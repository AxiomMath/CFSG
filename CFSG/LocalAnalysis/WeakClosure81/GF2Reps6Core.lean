module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Transport
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6OddTr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen
import CFSG.Quasithin.EmptyFaithful.SBd14Ind
import CFSG.GroupTheory.ConjKerCenter
import CFSG.GroupTheory.OddOrderClosurePResidual

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

private noncomputable def quotientCenterAut {G : Type*} [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rw [QuotientGroup.congr_mk]; rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      rfl

private theorem quotientCenterAut_mk {G : Type*} [Group G] (σ : MulAut G) (x : G) :
    quotientCenterAut σ (QuotientGroup.mk x : G ⧸ Subgroup.center G) =
      QuotientGroup.mk (σ x) :=
  QuotientGroup.congr_mk _ _ σ (Subgroup.map_center_eq σ) x

private noncomputable def restrictAut {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G)
    (hφH : H.map φ.toMonoidHom = H) : MulAut H :=
  (MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr hφH)

private theorem restrictAut_apply {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G)
    (hφH : H.map φ.toMonoidHom = H) (x : H) : (restrictAut φ H hφH x : G) = φ x :=
  rfl

private theorem center_eq_bot_of_simple_of_perfect {X : Type*} [Group X]
    [IsSimpleGroup X] (hperf : commutator X = ⊤) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer (⊤ : Set X) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hx' : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
      exact Subgroup.mem_center_iff.mp hx' y
    have hcomm : commutator X = ⊥ := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [hcomm] at hperf
    exact top_ne_bot hperf.symm

private theorem eq_one_of_quotientCenterAut_eq_one {L : Type*} [Group L]
    (hperf : Group.IsPerfect L) (ψ : MulAut L) (h : quotientCenterAut ψ = 1) : ψ = 1 := by
  apply CFSG.Quasithin.SBd14.eq_one_of_central_perfect hperf ψ
  intro x
  have h2 : (QuotientGroup.mk (ψ x) : L ⧸ Subgroup.center L) = QuotientGroup.mk x := by
    rw [← quotientCenterAut_mk ψ x, h, MulAut.one_apply]
  have hc0 : (ψ x)⁻¹ * x ∈ Subgroup.center L := QuotientGroup.eq.mp h2
  have hconj := (inferInstance : (Subgroup.center L).Normal).conj_mem
    ((ψ x)⁻¹ * x) hc0 (ψ x)
  have h' : ψ x * ((ψ x)⁻¹ * x) * (ψ x)⁻¹ = x * (ψ x)⁻¹ := by group
  rw [h'] at hconj
  simpa [mul_inv_rev] using (Subgroup.center L).inv_mem hconj

private theorem sq_eq_one_of_conj_mul_self_eq_one {X : Type*} [Group X]
    (hZ : Subgroup.center X = ⊥) {x : X} (h : MulAut.conj x * MulAut.conj x = 1) :
    x * x = 1 := by
  have hconj : MulAut.conj (x * x) = 1 := by
    rw [map_mul, h]
  have hcent : x * x ∈ Subgroup.center X := by
    rw [← CFSG.GroupTheory.ker_conj_eq_center, MonoidHom.mem_ker]
    exact hconj
  rw [hZ] at hcent
  exact Subgroup.mem_bot.mp hcent

private theorem eq_one_of_sq_eq_one_of_odd_center {X : Type*} [Group X]
    (hZ : Odd (Nat.card (Subgroup.center X))) {c : X}
    (hc : c ∈ Subgroup.center X) (hc2 : c * c = 1) : c = 1 := by
  have h1 : orderOf (⟨c, hc⟩ : Subgroup.center X) ∣ Nat.card ↥(Subgroup.center X) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨c, hc⟩ : Subgroup.center X) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hc2
  have h3 : Nat.gcd 2 (Nat.card ↥(Subgroup.center X)) = 1 :=
    Nat.coprime_two_left.mpr hZ
  have h4 : orderOf (⟨c, hc⟩ : Subgroup.center X) = 1 :=
    Nat.dvd_one.mp (h3 ▸ Nat.dvd_gcd h2 h1)
  have := orderOf_eq_one_iff.mp h4
  exact congrArg Subtype.val this

private theorem eq_of_mk_eq_of_sq_center {G : Type*} [Group G]
    (hodd : Odd (Nat.card (Subgroup.center G))) {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (QuotientGroup.mk a : G ⧸ Subgroup.center G) = QuotientGroup.mk b) : a = b := by
  have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.eq.mp hab
  set ζ := a⁻¹ * b with hζ
  have hbζ : b = a * ζ := by rw [hζ]; group
  have hcomm : a * ζ = ζ * a := Subgroup.mem_center_iff.mp hz a
  have hζ2 : ζ * ζ = 1 := by
    have hbb : b * b = (a * a) * (ζ * ζ) := by
      rw [hbζ]
      calc a * ζ * (a * ζ) = a * (ζ * a) * ζ := by group
        _ = a * (a * ζ) * ζ := by rw [hcomm]
        _ = (a * a) * (ζ * ζ) := by group
    rwa [hb, ha, one_mul, eq_comm] at hbb
  have hζ1 := eq_one_of_sq_eq_one_of_odd_center hodd hz hζ2
  rw [hbζ, hζ1, mul_one]

private theorem exists_sq_eq_one_lift_center {G : Type*} [Group G]
    (hodd : Odd (Nat.card (Subgroup.center G))) {y : G ⧸ Subgroup.center G}
    (hy : y * y = 1) : ∃ x : G, x * x = 1 ∧
      (QuotientGroup.mk x : G ⧸ Subgroup.center G) = y := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hx2 : x₀ * x₀ ∈ Subgroup.center G := by
    have h : ((x₀ * x₀ : G) : G ⧸ Subgroup.center G) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact hy
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨k, hk⟩ := hodd
  refine ⟨x₀ ^ Nat.card (Subgroup.center G), ?_, ?_⟩
  · have hc : (⟨x₀ * x₀, hx2⟩ : Subgroup.center G) ^ Nat.card (Subgroup.center G) = 1 :=
      pow_card_eq_one'
    have hc' : (x₀ * x₀) ^ Nat.card (Subgroup.center G) = 1 := congrArg Subtype.val hc
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two]
    exact hc'
  · rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, sq]
    have h : ((x₀ : G ⧸ Subgroup.center G) * (x₀ : G ⧸ Subgroup.center G)) = 1 := hy
    rw [h, one_pow, one_mul]

private theorem map_centralizer_singleton_aut {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    simpa using congrArg φ (hz x rfl)
  · intro h
    rw [Subgroup.mem_centralizer_iff] at h
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    have := congrArg φ.symm (h (φ x) rfl)
    simpa using this

private theorem mem_center_subgroup_iff {G : Type*} [Group G] {L : Subgroup G} (x : L) :
    x ∈ Subgroup.center L ↔ (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (h y y.2)

private theorem commutatorElement_mul_central_left {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hcy : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
  rw [commutatorElement_def]
  rw [show (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ by group]
  rw [hcy]
  group

private theorem commutatorElement_mul_central_right {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central_left hz, commutatorElement_inv]

private theorem commutator_sup_center_eq {G : Type*} [Group G] {Z X : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) [Z.Normal] : ⁅X ⊔ Z, X ⊔ Z⁆ = ⁅X, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨y, hy, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rw [commutatorElement_mul_central_left (hZ hz),
      commutatorElement_mul_central_right (hZ hz')]
    exact Subgroup.commutator_mem_commutator hx hy
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

private theorem le_of_perfect_le_sup_center {G : Type*} [Group G] {M Z : Subgroup G}
    (hperf : Group.IsPerfect G) (hZ : Z ≤ Subgroup.center G) [Z.Normal]
    (h : (⊤ : Subgroup G) ≤ M ⊔ Z) : (⊤ : Subgroup G) ≤ M := by
  have hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rw [← _root_.commutator_def (G := G)]
    exact hperf.commutator_eq_top
  calc (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := hG.symm
    _ ≤ ⁅M ⊔ Z, M ⊔ Z⁆ := Subgroup.commutator_mono h h
    _ = ⁅M, M⁆ := commutator_sup_center_eq hZ (X := M)
    _ ≤ M := Subgroup.commutator_le_self M

theorem odd_or_le_two_of_le_quadY_sup [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A M : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : IsQuadratic A) {a : MulAut V}
    (haA : a ∈ A) (ha : a ^ 2 = 1) (hM : fixV M = ⊥)
    (hgen : ∀ h ∈ G, h * a * h⁻¹ * a = a * (h * a * h⁻¹) → h * a * h⁻¹ ≠ a →
      M ≤ quadY G A a ⊔ (quadY G A a).map (MulAut.conj h).toMonoidHom)
    {g : MulAut V} (hg : g ∈ G) :
    Odd (orderOf (a * (g * a * g⁻¹))) ∨ orderOf (a * (g * a * g⁻¹)) ≤ 2 := by
  refine odd_or_le_two_of_inf_commV_eq_bot hV (hAG haA) ha ?_ hg
  intro h hhG hcomm hne
  refine commV_inf_commV_conj_eq_bot (Y := quadY G A a) (fixes_commV_quadY hA haA) ?_
  have hle : fixV (quadY G A a ⊔ (quadY G A a).map (MulAut.conj h).toMonoidHom) ≤
      fixV M := by
    intro v hv m hm
    exact hv m (hgen h hhG hcomm hne hm)
  simpa [hM, le_bot_iff] using hle

set_option maxHeartbeats 400000 in
theorem false_of_l3OddPointed [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    {t₀ : ↥L ⧸ center ↥L} (hX : L3OddPointed (↥L ⧸ center ↥L) t₀)
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) (hA4 : Nat.card A = 4)
    (hA2 : ∀ u ∈ A, u * u = 1) (hA : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥) : False := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite ↥L := Finite.of_injective ((↑) : ↥L → MulAut V) Subtype.coe_injective
  have : Finite ↥A := Finite.of_injective ((↑) : ↥A → MulAut V) Subtype.coe_injective
  let X := ↥L ⧸ center ↥L
  let π : ↥L →* X := QuotientGroup.mk' (center ↥L)
  have hAL' : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hAL u hu l hl, fun hl => by
      have h1 : u⁻¹ * (u * l * u⁻¹) * (u⁻¹)⁻¹ ∈ L := hAL u⁻¹ (A.inv_mem hu) _ hl
      have h2 : l = u⁻¹ * (u * l * u⁻¹) * (u⁻¹)⁻¹ := by group
      rw [h2]
      exact h1⟩
  let ψ : ↥A →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hAL')
  let φ : ↥A →* MulAut X := (quotientCenterAut (G := ↥L)).comp ψ
  have hφ_mk : ∀ (u : ↥A) (l : ↥L),
      φ u (π l) = π ⟨(u : MulAut V) * (l : MulAut V) * (u : MulAut V)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAL' u.2) (l : MulAut V)).mp l.2⟩ := by
    intro u l
    change quotientCenterAut (ψ u) (QuotientGroup.mk l) = _
    rw [quotientCenterAut_mk]
    rfl
  have hφker : ∀ u : ↥A, φ u = 1 →
      (u : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    intro u hu
    have hψu : ψ u = 1 := eq_one_of_quotientCenterAut_eq_one ⟨hL.1⟩ (ψ u) (by
      exact hu)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ((ψ u ⟨l, hl⟩ : ↥L) : MulAut V) = l := by
      have h := congrArg (fun α : MulAut ↥L => α ⟨l, hl⟩) hψu
      simpa using congrArg (fun y : ↥L => (y : MulAut V)) h
    have h2 : (u : MulAut V) * l * (u : MulAut V)⁻¹ = l := by
      simpa [ψ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
    calc l * (u : MulAut V) = ((u : MulAut V) * l * (u : MulAut V)⁻¹) * (u : MulAut V) := by
          rw [h2]
      _ = (u : MulAut V) * l := by group
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h1 : φ (u⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, huv]
      simp
    have h2 : ((u⁻¹ * v : ↥A) : MulAut V) ∈
        A ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
      ⟨(u⁻¹ * v).2, hφker (u⁻¹ * v) h1⟩
    rw [hAC] at h2
    have h3 : (u⁻¹ * v : ↥A) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp h2)
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  let B : Subgroup (MulAut X) := φ.range
  have hBcard : Nat.card B = 4 := by
    have h1 : Nat.card B = Nat.card ↥A := by
      rw [show B = φ.range from rfl, MonoidHom.range_eq_map]
      calc Nat.card ↥((⊤ : Subgroup ↥A).map φ) = Nat.card ↥(⊤ : Subgroup ↥A) :=
            Subgroup.card_map_of_injective (K := ⊤) hφinj
        _ = Nat.card ↥A := Subgroup.card_top
    rw [h1]
    simpa using hA4
  have hBsq : ∀ β ∈ B, β * β = 1 := by
    intro β hβ
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hβ
    have hu : u * u = 1 := Subtype.ext (hA2 (u : MulAut V) u.2)
    rw [← map_mul, hu, map_one]
  obtain ⟨β, hβB, hβ1, hβinner⟩ := hX.inner B hBcard hBsq
  obtain ⟨aA, hφa⟩ := MonoidHom.mem_range.mp hβB
  obtain ⟨x, hxconj⟩ := MonoidHom.mem_range.mp hβinner
  have hβconj : φ aA = MulAut.conj x := hφa.trans hxconj.symm
  have hneX : Nontrivial X := by
    refine ⟨t₀, 1, ?_⟩
    intro h
    have h1 : orderOf t₀ = 1 := by rw [h, orderOf_one]
    rw [hX.orderOf_eq] at h1
    omega
  have hperfL : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hsimpleX : IsSimpleGroup X := hL.2
  have hperfX : commutator X = ⊤ := by
    have h := Group.IsPerfect.ofSurjective (f := π)
      (QuotientGroup.mk'_surjective (center ↥L))
    exact h.commutator_eq_top
  have hZcenter : Subgroup.center X = ⊥ := center_eq_bot_of_simple_of_perfect hperfX
  have hφaB : φ aA ∈ B := by
    rw [hφa]
    exact hβB
  have hxx : x * x = 1 := by
    refine sq_eq_one_of_conj_mul_self_eq_one hZcenter ?_
    rw [← hβconj]
    exact hBsq (φ aA) hφaB
  have hx1 : x ≠ 1 := by
    intro hx
    apply hβ1
    rw [← hφa, hβconj, hx]
    simp
  have hxord : orderOf x = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  obtain ⟨t, ht2, htπ⟩ := exists_sq_eq_one_lift_center (G := ↥L) hZ (y := x) hxx
  have hπt : π t = x := htπ
  have hX' : L3OddPointed X x := hX.of_orderOf_eq_two (t := x) hxord
  let a : MulAut V := aA
  let c : MulAut V := (t : MulAut V)⁻¹ * a
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
    have htN : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
      Subgroup.le_normalizer t.2
    have haN : a ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL' aA.2
    have h := (Subgroup.normalizer (L : Set (MulAut V))).mul_mem
      ((Subgroup.normalizer (L : Set (MulAut V))).inv_mem htN) haN
    simpa [c] using h
  let ψc : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨c, hcN⟩
  have hmemc : ∀ l : ↥L, c * (l : MulAut V) * c⁻¹ ∈ L := by
    intro l
    have hal : a * (l : MulAut V) * a⁻¹ ∈ L := hAL a aA.2 (l : MulAut V) l.2
    have h1 : (t : MulAut V)⁻¹ * (a * (l : MulAut V) * a⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem t.2) hal
    have h2 : ((t : MulAut V)⁻¹ * (a * (l : MulAut V) * a⁻¹)) * (t : MulAut V) ∈ L :=
      L.mul_mem h1 t.2
    have h3 : c * (l : MulAut V) * c⁻¹ =
        ((t : MulAut V)⁻¹ * (a * (l : MulAut V) * a⁻¹)) * (t : MulAut V) := by
      simp only [c]
      group
    rw [h3]
    exact h2
  have hπc : ∀ l : ↥L, π ⟨c * (l : MulAut V) * c⁻¹, hmemc l⟩ = π l := by
    intro l
    have hal : a * (l : MulAut V) * a⁻¹ ∈ L := hAL a aA.2 (l : MulAut V) l.2
    have heq : (⟨c * (l : MulAut V) * c⁻¹, hmemc l⟩ : ↥L) =
        t⁻¹ * (⟨a * (l : MulAut V) * a⁻¹, hal⟩ : ↥L) * t := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [c]
      group
    rw [heq, map_mul, map_mul, map_inv]
    rw [hπt, ← hφ_mk aA l, hβconj, MulAut.conj_apply]
    group
  have hψc_cent : ∀ l : ↥L, ψc l * l⁻¹ ∈ Subgroup.center ↥L := by
    intro l
    rw [← QuotientGroup.eq_one_iff]
    change π (ψc l * l⁻¹) = 1
    have h1 : π (ψc l) = π ⟨c * (l : MulAut V) * c⁻¹, hmemc l⟩ :=
      congrArg π (Subtype.ext
        (Subgroup.normalizerMonoidHom_apply_apply_coe (H := L) ⟨c, hcN⟩ l))
    rw [map_mul, map_inv, h1, hπc l, mul_inv_cancel]
  have hψc_one : ψc = 1 :=
    CFSG.Quasithin.SBd14.eq_one_of_central_perfect ⟨hL.1⟩ ψc hψc_cent
  have hcC : ∀ l ∈ L, c * l * c⁻¹ = l := by
    intro l hl
    have h1 : ((ψc ⟨l, hl⟩ : ↥L) : MulAut V) = l := by
      have h := congrArg (fun α : MulAut ↥L => α ⟨l, hl⟩) hψc_one
      simpa using congrArg (fun y : ↥L => (y : MulAut V)) h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    exact h1
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    intro u hu v hv
    have hu2 : u * u = 1 := hA2 u hu
    have hv2 : v * v = 1 := hA2 v hv
    have huv2 : (u * v) * (u * v) = 1 := hA2 (u * v) (A.mul_mem hu hv)
    calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv2).symm
      _ = v⁻¹ * u⁻¹ := by rw [mul_inv_rev]
      _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv2,
          inv_eq_of_mul_eq_one_right hu2]
  have hacc : a * a = 1 := hA2 a aA.2
  have ht2' : (t : MulAut V) * (t : MulAut V) = 1 := by
    simpa using congrArg (fun x : ↥L => (x : MulAut V)) ht2
  have hti : (t : MulAut V)⁻¹ = (t : MulAut V) :=
    inv_eq_of_mul_eq_one_right ht2'
  have hcInv : ∀ l ∈ L, c⁻¹ * l * c = l := by
    intro l hl
    have h := hcC l hl
    have h' : c⁻¹ * (c * l * c⁻¹) * c = l := by group
    rwa [h] at h'
  have hut : ∀ u ∈ A, u * (t : MulAut V) * u⁻¹ = (t : MulAut V) := by
    intro u hu
    let U : MulAut V := u * (t : MulAut V) * u⁻¹
    have hUL : U ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL' hu) (t : MulAut V)).mp t.2
    have huci_cent : ∀ l ∈ L, (u * c⁻¹ * u⁻¹) * l * (u * c⁻¹ * u⁻¹)⁻¹ = l := by
      intro l hl
      have hul : u⁻¹ * l * u ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hAL' (A.inv_mem hu)) l).mp hl
      calc (u * c⁻¹ * u⁻¹) * l * (u * c⁻¹ * u⁻¹)⁻¹
          = u * (c⁻¹ * (u⁻¹ * l * u) * c) * u⁻¹ := by group
        _ = u * (u⁻¹ * l * u) * u⁻¹ := by rw [hcInv (u⁻¹ * l * u) hul]
        _ = l := by group
    have hz_eq : (t : MulAut V)⁻¹ * U = c * (u * c⁻¹ * u⁻¹) := by
      have huaeq : u * a * u⁻¹ = a := by
        have hau : u * a = a * u := hAcomm u hu a aA.2
        calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [hau]
          _ = a := by group
      have htca : (t : MulAut V) * c = a := by
        show (t : MulAut V) * ((t : MulAut V)⁻¹ * a) = a
        rw [hti, ← mul_assoc, ht2', one_mul]
      have htdef : (t : MulAut V) = a * c⁻¹ := by
        rw [← htca]
        group
      calc (t : MulAut V)⁻¹ * U
          = (a * c⁻¹)⁻¹ * (u * (a * c⁻¹) * u⁻¹) := by
            rw [show U = u * (t : MulAut V) * u⁻¹ from rfl, htdef]
        _ = (a * c⁻¹)⁻¹ * ((u * a * u⁻¹) * (u * c⁻¹ * u⁻¹)) := by group
        _ = (a * c⁻¹)⁻¹ * (a * (u * c⁻¹ * u⁻¹)) := by rw [huaeq]
        _ = c * (u * c⁻¹ * u⁻¹) := by group
    have hz_central : ∀ l ∈ L,
        ((t : MulAut V)⁻¹ * U) * l * ((t : MulAut V)⁻¹ * U)⁻¹ = l := by
      intro l hl
      rw [hz_eq]
      have h1 := huci_cent l hl
      calc (c * (u * c⁻¹ * u⁻¹)) * l * (c * (u * c⁻¹ * u⁻¹))⁻¹
          = c * ((u * c⁻¹ * u⁻¹) * l * (u * c⁻¹ * u⁻¹)⁻¹) * c⁻¹ := by group
        _ = c * l * c⁻¹ := by rw [h1]
        _ = l := hcC l hl
    let z : ↥L := ⟨(t : MulAut V)⁻¹ * U,
      L.mul_mem (L.inv_mem t.2) hUL⟩
    have hz_center : z ∈ Subgroup.center ↥L := by
      rw [mem_center_subgroup_iff]
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := hz_central l hl
      calc l * ((t : MulAut V)⁻¹ * U)
          = (((t : MulAut V)⁻¹ * U) * l * ((t : MulAut V)⁻¹ * U)⁻¹) *
              ((t : MulAut V)⁻¹ * U) := by rw [h]
        _ = ((t : MulAut V)⁻¹ * U) * l := by group
    have hU2 : U * U = 1 := by
      show (u * (t : MulAut V) * u⁻¹) * (u * (t : MulAut V) * u⁻¹) = 1
      calc (u * (t : MulAut V) * u⁻¹) * (u * (t : MulAut V) * u⁻¹)
          = u * ((t : MulAut V) * (t : MulAut V)) * u⁻¹ := by group
        _ = 1 := by rw [ht2']; simp
    have hzt_amb : ((t : MulAut V)⁻¹ * U) * (t : MulAut V) =
        (t : MulAut V) * ((t : MulAut V)⁻¹ * U) := by
      have h := Subgroup.mem_center_iff.mp hz_center ⟨t, t.2⟩
      exact (congrArg Subtype.val h).symm
    have hUt : U * (t : MulAut V) = (t : MulAut V) * U := by
      have h2 : (t : MulAut V) * U * (t : MulAut V) = U := by
        rw [hti] at hzt_amb
        calc (t : MulAut V) * U * (t : MulAut V)
            = (t : MulAut V) * ((t : MulAut V) * U) := hzt_amb
          _ = U := by rw [← mul_assoc, ht2', one_mul]
      calc U * (t : MulAut V) = ((t : MulAut V) * U * (t : MulAut V)) *
            (t : MulAut V) := by rw [h2]
        _ = (t : MulAut V) * U := by rw [mul_assoc, mul_assoc, ht2', mul_one]
    have hzsq_amb : ((t : MulAut V)⁻¹ * U) * ((t : MulAut V)⁻¹ * U) = 1 := by
      rw [hti]
      calc ((t : MulAut V) * U) * ((t : MulAut V) * U)
          = (t : MulAut V) * (U * (t : MulAut V)) * U := by group
        _ = (t : MulAut V) * ((t : MulAut V) * U) * U := by rw [hUt]
        _ = ((t : MulAut V) * (t : MulAut V)) * (U * U) := by group
        _ = 1 := by rw [ht2', hU2, one_mul]
    have hzsq : z * z = 1 := Subtype.ext (by simpa [z] using hzsq_amb)
    have hz1 : z = 1 := eq_one_of_sq_eq_one_of_odd_center hZ hz_center hzsq
    have hzamb : (t : MulAut V)⁻¹ * U = 1 := congrArg Subtype.val hz1
    have hUeq : U = (t : MulAut V) := by
      have h : (t : MulAut V) * U = 1 := by
        rwa [hti] at hzamb
      calc U = ((t : MulAut V) * (t : MulAut V)) * U := by rw [ht2', one_mul]
        _ = (t : MulAut V) * ((t : MulAut V) * U) := by group
        _ = (t : MulAut V) * 1 := by rw [h]
        _ = (t : MulAut V) := by simp
    exact hUeq
  have hcc : c * c = 1 := by
    have hat : a * (t : MulAut V) = (t : MulAut V) * a := by
      have h := hut a aA.2
      calc a * (t : MulAut V) = (a * (t : MulAut V) * a⁻¹) * a := by group
        _ = (t : MulAut V) * a := by rw [h]
    show ((t : MulAut V)⁻¹ * a) * ((t : MulAut V)⁻¹ * a) = 1
    rw [hti]
    calc (t * a) * (t * a) = (t : MulAut V) * (a * (t : MulAut V)) * a := by group
      _ = (t : MulAut V) * ((t : MulAut V) * a) * a := by rw [hat]
      _ = ((t : MulAut V) * (t : MulAut V)) * (a * a) := by group
      _ = 1 := by rw [ht2', hacc, one_mul]
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let CLt : Subgroup ↥L := Subgroup.centralizer ({t} : Set ↥L)
  have hCLt_map : CLt.map π = Subgroup.centralizer ({x} : Set X) := by
    ext y
    constructor
    · intro hy
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_iff] at hl ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      simpa [hπt, map_mul] using congrArg π (hl t rfl)
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) y
      rw [Subgroup.mem_map]
      refine ⟨l, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hcomm : x * π l = π l * x := hy x (by simp)
      have hcomm' : π t * π l = π l * π t := by
        rwa [← hπt] at hcomm
      have hu2 : (l * t * l⁻¹) * (l * t * l⁻¹) = 1 := by
        calc (l * t * l⁻¹) * (l * t * l⁻¹) = l * (t * t) * l⁻¹ := by group
          _ = 1 := by rw [ht2]; simp
      have huπ : π (l * t * l⁻¹) = x := by
        calc π (l * t * l⁻¹) = π l * π t * (π l)⁻¹ := by rw [map_mul, map_mul, map_inv]
          _ = π t * π l * (π l)⁻¹ := by rw [hcomm'.symm]
          _ = π t := by group
          _ = x := hπt
      have heq : l * t * l⁻¹ = t :=
        eq_of_mk_eq_of_sq_center hZ hu2 ht2 (huπ.trans hπt.symm)
      calc t * l = (l * t * l⁻¹) * l := by rw [heq]
        _ = l * t := by group
  let K0 : Subgroup ↥L := ⁅CLt, CLt⁆
  let K : Subgroup ↥L := ⁅K0, K0⁆
  have hK0map : K0.map π = derivedCent x := by
    rw [show K0 = ⁅CLt, CLt⁆ from rfl, Subgroup.map_commutator, hCLt_map]
    rfl
  have hKmap : K.map π = derivedCent x := by
    rw [show K = ⁅K0, K0⁆ from rfl, Subgroup.map_commutator, hK0map]
    exact Subgroup.isPerfect_iff.mp ⟨hX'.quasi.1⟩
  have hK0_le : K0 ≤ K ⊔ Z := by
    intro k0 hk0
    have hmem : π k0 ∈ derivedCent x := by
      rw [← hK0map]
      exact Subgroup.mem_map_of_mem π hk0
    have hmem' : π k0 ∈ K.map π := by
      rw [hKmap]
      exact hmem
    obtain ⟨k, hk, hπk⟩ := Subgroup.mem_map.mp hmem'
    have hz : k⁻¹ * k0 ∈ Z := QuotientGroup.eq.mp hπk
    have heq : k0 = k * (k⁻¹ * k0) := by group
    rw [heq]
    exact (K ⊔ Z).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hz)
  have hKperfect : Group.IsPerfect ↥K := by
    rw [Subgroup.isPerfect_iff]
    apply le_antisymm (Subgroup.commutator_le_self K)
    rw [show K = ⁅K0, K0⁆ from rfl]
    calc ⁅K0, K0⁆ ≤ ⁅K ⊔ Z, K ⊔ Z⁆ := Subgroup.commutator_mono hK0_le hK0_le
      _ = ⁅K, K⁆ := commutator_sup_center_eq (Z := Z) le_rfl (X := K)
  have htca : (t : MulAut V) * c = a := by
    show (t : MulAut V) * ((t : MulAut V)⁻¹ * a) = a
    rw [hti, ← mul_assoc, ht2', one_mul]
  have hct : c * (t : MulAut V) = (t : MulAut V) * c := by
    have h := hcC (t : MulAut V) t.2
    calc c * (t : MulAut V) = (c * (t : MulAut V) * c⁻¹) * c := by group
      _ = (t : MulAut V) * c := by rw [h]
  have hLU : ∀ g ∈ L, a * (g * a * g⁻¹) =
      (t : MulAut V) * (g * (t : MulAut V) * g⁻¹) := by
    intro g hg
    have hcg : c * g = g * c := by
      have h := hcC g hg
      calc c * g = (c * g * c⁻¹) * c := by group
        _ = g * c := by rw [h]
    have hcgi : c * g⁻¹ = g⁻¹ * c := by
      have h := hcC g⁻¹ (L.inv_mem hg)
      calc c * g⁻¹ = (c * g⁻¹ * c⁻¹) * c := by group
        _ = g⁻¹ * c := by rw [h]
    have hct : c * (t : MulAut V) = (t : MulAut V) * c := by
      have h := hcC (t : MulAut V) t.2
      calc c * (t : MulAut V) = (c * (t : MulAut V) * c⁻¹) * c := by group
        _ = (t : MulAut V) * c := by rw [h]
    calc a * (g * a * g⁻¹)
        = (t * c) * (g * (t * c) * g⁻¹) := by rw [htca]
      _ = t * (c * g) * t * (c * g⁻¹) := by group
      _ = t * (g * c) * t * (g⁻¹ * c) := by rw [hcg, hcgi]
      _ = t * g * (c * t) * (g⁻¹ * c) := by group
      _ = t * g * (t * c) * (g⁻¹ * c) := by rw [hct]
      _ = t * g * t * (c * g⁻¹) * c := by group
      _ = t * g * t * (g⁻¹ * c) * c := by rw [hcgi]
      _ = t * g * t * g⁻¹ * (c * c) := by group
      _ = (t : MulAut V) * (g * (t : MulAut V) * g⁻¹) := by rw [hcc]; group
  have haA1 : aA ≠ 1 := by
    intro h
    apply hβ1
    rw [← hφa, h]
    exact map_one φ
  have : Fintype ↥A := Fintype.ofFinite ↥A
  have hAcard : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hA4
  let sA : Finset ↥A := {1, aA}
  have hsAcard : sA.card = 2 := by
    have hne : (1 : ↥A) ≠ aA := fun h => haA1 h.symm
    simpa [sA] using Finset.card_pair hne
  obtain ⟨u, -, hu_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := sA)
    (t := Finset.univ) (by rw [Finset.card_univ, hAcard, hsAcard]; omega)
  have hu1 : u ≠ 1 := by
    intro h
    exact hu_notin (by simp [sA, h])
  have hua : u ≠ aA := by
    intro h
    exact hu_notin (by simp [sA, h])
  let uA : MulAut V := u
  have hu1' : uA ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hua' : uA ≠ a := fun h => hua (Subtype.ext h)
  let G : Subgroup (MulAut V) := A ⊔ L
  have hK_le_CLt : K ≤ CLt :=
    (Subgroup.commutator_le_self K0).trans (Subgroup.commutator_le_self CLt)
  have hK_cent_a : ∀ k ∈ K, (k : MulAut V) * a = a * (k : MulAut V) := by
    intro k hk
    have hkCLt : k ∈ CLt := hK_le_CLt hk
    rw [Subgroup.mem_centralizer_iff] at hkCLt
    have hkt : (k : MulAut V) * (t : MulAut V) = (t : MulAut V) * (k : MulAut V) :=
      congrArg (fun y : ↥L => (y : MulAut V)) (hkCLt t rfl).symm
    have hck : c * (k : MulAut V) = (k : MulAut V) * c := by
      have h := hcC (k : MulAut V) k.2
      calc c * (k : MulAut V) = (c * (k : MulAut V) * c⁻¹) * c := by group
        _ = (k : MulAut V) * c := by rw [h]
    calc (k : MulAut V) * a = (k : MulAut V) * ((t : MulAut V) * c) := by rw [htca]
      _ = ((k : MulAut V) * (t : MulAut V)) * c := by group
      _ = ((t : MulAut V) * (k : MulAut V)) * c := by rw [hkt]
      _ = (t : MulAut V) * ((k : MulAut V) * c) := by group
      _ = (t : MulAut V) * (c * (k : MulAut V)) := by rw [hck]
      _ = ((t : MulAut V) * c) * (k : MulAut V) := by group
      _ = a * (k : MulAut V) := by rw [htca]
  let ψu : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨uA, hAL' u.2⟩
  have hψu_t : ψu t = t := by
    apply Subtype.ext
    simpa [ψu, uA, Subgroup.normalizerMonoidHom_apply_apply_coe] using hut u u.2
  have hCLt_inv : CLt.map ψu.toMonoidHom = CLt := by
    rw [map_centralizer_singleton_aut ψu t, hψu_t]
  have hK0_inv : K0.map ψu.toMonoidHom = K0 := by
    rw [show K0 = ⁅CLt, CLt⁆ from rfl, Subgroup.map_commutator, hCLt_inv]
  have hK_inv : K.map ψu.toMonoidHom = K := by
    rw [show K = ⁅K0, K0⁆ from rfl, Subgroup.map_commutator, hK0_inv]
  let huKelem : ∀ x : ↥L, x ∈ K → ↥L := fun x hx =>
    ⟨uA * (x : MulAut V) * uA⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAL' u.2) (x : MulAut V)).mp x.2⟩
  have huKelem_mem : ∀ (x : ↥L) (hx : x ∈ K), huKelem x hx ∈ K := by
    intro x hx
    have h : ψu x ∈ K := by
      have hmem := Subgroup.mem_map_of_mem ψu.toMonoidHom hx
      rwa [hK_inv] at hmem
    have hval : ψu x = huKelem x hx := by
      apply Subtype.ext
      simp only [huKelem]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe (H := L) ⟨uA, hAL' u.2⟩ x
    rwa [hval] at h
  have mem_quadY_of_mem_G_comm : ∀ {x : MulAut V}, x ∈ G → x * a = a * x →
      ∀ y ∈ A, x * y * x⁻¹ ∈ quadY G A a := by
    intro x hxG hxa y hy
    refine Subgroup.mem_iSup_of_mem x ?_
    refine Subgroup.mem_iSup_of_mem hxG ?_
    refine Subgroup.mem_iSup_of_mem hxa ?_
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hy
  have hA_le_quadY : A ≤ quadY G A a := by
    intro y hy
    simpa using mem_quadY_of_mem_G_comm G.one_mem (by simp) y hy
  let gen : ↥K → ↥K := fun k =>
    ⟨(k : ↥L) * huKelem ((k : ↥L)⁻¹) (K.inv_mem k.2),
      K.mul_mem k.2 (huKelem_mem ((k : ↥L)⁻¹) (K.inv_mem k.2))⟩
  have hgen_mem_quadY : ∀ k : ↥K, ((gen k : ↥K) : MulAut V) ∈ quadY G A a := by
    intro k
    have hkG : (k : MulAut V) ∈ G := Subgroup.mem_sup_right (k : ↥L).2
    have hkcomm : (k : MulAut V) * a = a * (k : MulAut V) := hK_cent_a k k.2
    have hxu : (k : MulAut V) * uA * (k : MulAut V)⁻¹ ∈ quadY G A a :=
      mem_quadY_of_mem_G_comm hkG hkcomm uA u.2
    have hu_inv : uA⁻¹ ∈ quadY G A a := hA_le_quadY (A.inv_mem u.2)
    have hgen_eq : ((gen k : ↥K) : MulAut V) =
        ((k : MulAut V) * uA * (k : MulAut V)⁻¹) * uA⁻¹ := by
      dsimp only [gen, huKelem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hgen_eq]
    exact (quadY G A a).mul_mem hxu hu_inv
  let S : Set ↥K := {x | ∃ k1 : ↥K, ∃ k2 : ↥K, x = k1 * gen k2 * k1⁻¹}
  have hS_conj : ∀ g x : ↥K, x ∈ S → g * x * g⁻¹ ∈ S := by
    rintro g x ⟨k1, k2, rfl⟩
    refine ⟨g * k1, k2, ?_⟩
    group
  let N_K : Subgroup ↥K := Subgroup.closure S
  have hN_K_normal : N_K.Normal := by
    have hN_eq : N_K = Subgroup.normalClosure S := by
      rw [show N_K = Subgroup.closure S from rfl,
        ← CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant hS_conj]
    rw [hN_eq]
    exact Subgroup.normalClosure_normal
  let N : Subgroup ↥L := N_K.map K.subtype
  have hN_K_le_quadY : ∀ x ∈ N_K, ((x : ↥K) : MulAut V) ∈ quadY G A a := by
    let QK : Subgroup ↥K :=
      { carrier := {x : ↥K | ((x : ↥K) : MulAut V) ∈ quadY G A a}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          have hx' : ((x : ↥K) : MulAut V) ∈ quadY G A a := hx
          have hy' : ((y : ↥K) : MulAut V) ∈ quadY G A a := hy
          simpa [Subgroup.coe_mul] using (quadY G A a).mul_mem hx' hy'
        inv_mem' := by
          intro x hx
          have hx' : ((x : ↥K) : MulAut V) ∈ quadY G A a := hx
          simpa [Subgroup.coe_inv] using (quadY G A a).inv_mem hx' }
    have hS_le_QK : S ⊆ QK := by
      rintro x ⟨k1, k2, rfl⟩
      have hx1G : (k1 : MulAut V) ∈ G := Subgroup.mem_sup_right (k1 : ↥L).2
      have hx2K : ((k1 : ↥L) * (k2 : ↥L) * (k1 : ↥L)⁻¹) ∈ K :=
        K.mul_mem (K.mul_mem k1.2 k2.2) (K.inv_mem k1.2)
      have hx2G : ((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) ∈ G :=
        Subgroup.mem_sup_right (k1 * k2 * k1⁻¹ : ↥L).2
      have hx2comm : ((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) * a =
          a * ((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) := hK_cent_a _ hx2K
      have hB : (k1 : MulAut V) * uA * (k1 : MulAut V)⁻¹ ∈ quadY G A a :=
        mem_quadY_of_mem_G_comm hx1G (hK_cent_a k1 k1.2) uA u.2
      have hAB : ((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) *
          ((k1 : MulAut V) * uA * (k1 : MulAut V)⁻¹) *
          (((k1 * k2 * k1⁻¹ : ↥K) : MulAut V))⁻¹ ∈ quadY G A a := by
        have hprodG : ((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) * (k1 : MulAut V) ∈ G :=
          G.mul_mem hx2G hx1G
        have hprodcomm : (((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) * (k1 : MulAut V)) * a =
            a * (((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) * (k1 : MulAut V)) := by
          have h := hK_cent_a (k1 * k2) (K.mul_mem k1.2 k2.2)
          simpa [Subgroup.coe_mul, mul_assoc] using h
        have h := mem_quadY_of_mem_G_comm hprodG hprodcomm uA u.2
        simpa [Subgroup.coe_mul, mul_assoc] using h
      have hconj_eq : ((k1 * gen k2 * k1⁻¹ : ↥K) : MulAut V) =
          (((k1 * k2 * k1⁻¹ : ↥K) : MulAut V) *
            ((k1 : MulAut V) * uA * (k1 : MulAut V)⁻¹) *
            (((k1 * k2 * k1⁻¹ : ↥K) : MulAut V))⁻¹) *
            ((k1 : MulAut V) * uA * (k1 : MulAut V)⁻¹)⁻¹ := by
        dsimp only [gen, huKelem]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      show ((k1 * gen k2 * k1⁻¹ : ↥K) : MulAut V) ∈ quadY G A a
      rw [hconj_eq]
      exact (quadY G A a).mul_mem hAB ((quadY G A a).inv_mem hB)
    have hle : N_K ≤ QK := by
      rw [show N_K = Subgroup.closure S from rfl, Subgroup.closure_le]
      exact hS_le_QK
    intro x hx
    exact hle hx
  have hN_le_quadY : ∀ n ∈ N, (n : MulAut V) ∈ quadY G A a := by
    intro n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.mp hn
    exact hN_K_le_quadY n0 hn0
  have hN_le_K : N ≤ K := by
    intro n hn
    obtain ⟨n0, -, rfl⟩ := Subgroup.mem_map.mp hn
    exact n0.2
  have hNmap_le : N.map π ≤ derivedCent x := by
    rw [← hKmap]
    exact Subgroup.map_mono hN_le_K
  have hN_normal_K : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.mp hn
    have h : (⟨k, hk⟩ : ↥K) * n0 * (⟨k, hk⟩ : ↥K)⁻¹ ∈ N_K :=
      hN_K_normal.conj_mem n0 hn0 ⟨k, hk⟩
    exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩
  let Nbar : Subgroup ↥(derivedCent x) := (N.map π).subgroupOf (derivedCent x)
  have hNbar_normal : Nbar.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (show (g : X) ∈ K.map π by
      rw [hKmap]; exact g.2)
    obtain ⟨n0, hn0, hn0π⟩ := Subgroup.mem_map.mp hn
    have hmemN : k * n0 * k⁻¹ ∈ N := hN_normal_K k hk n0 hn0
    refine Subgroup.mem_map.mpr ⟨k * n0 * k⁻¹, hmemN, ?_⟩
    rw [map_mul, map_mul, map_inv, hkπ, hn0π]
    rfl
  have hφu_sq : φ u * φ u = 1 := by
    have hu2 : u * u = 1 := Subtype.ext (hA2 (u : MulAut V) u.2)
    rw [← map_mul, hu2, map_one]
  have hφu_x : φ u x = x := by
    rw [← hπt]
    have h : φ u (π t) = π ⟨(u : MulAut V) * (t : MulAut V) * (u : MulAut V)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAL' u.2) (t : MulAut V)).mp t.2⟩ := hφ_mk u t
    rw [h]
    congr 1
  have hKbar_map : (derivedCent x).map (φ u).toMonoidHom = derivedCent x := by
    rw [derivedCent_map, hφu_x]
  let α : MulAut ↥(derivedCent x) := restrictAut (φ u) (derivedCent x) hKbar_map
  have hα_apply : ∀ y : ↥(derivedCent x), ((α y : ↥(derivedCent x)) : X) = φ u y := fun y =>
    restrictAut_apply (φ u) (derivedCent x) hKbar_map y
  have hgen_inv_eq : ∀ k : ↥K, (gen k)⁻¹ =
      (⟨(u : MulAut V) * (k : MulAut V) * (u : MulAut V)⁻¹ * (k : MulAut V)⁻¹,
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL' u.2) (k : MulAut V)).mp
          (k : ↥L).2) (L.inv_mem (k : ↥L).2)⟩ : ↥L) := by
    intro k
    apply Subtype.ext
    dsimp only [gen, huKelem, uA]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hα_cent : Nbar ≤ Subgroup.center ↥(derivedCent x) → ∀ y : ↥(derivedCent x),
      α y * y⁻¹ ∈ Subgroup.center ↥(derivedCent x) := by
    intro hcentral y
    have hyK : (y : X) ∈ K.map π := by
      rw [hKmap]
      exact y.2
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hyK
    let kK : ↥K := ⟨k, hk⟩
    have hgen_memN : ((gen kK : ↥K) : ↥L) ∈ N :=
      Subgroup.mem_map.mpr ⟨gen kK, Subgroup.subset_closure ⟨1, kK, by simp⟩, rfl⟩
    have huk_mem_map : (π (gen kK : ↥L))⁻¹ ∈ N.map π := by
      have hinv : ((gen kK : ↥K) : ↥L)⁻¹ ∈ N := N.inv_mem hgen_memN
      have h := Subgroup.mem_map_of_mem π hinv
      rwa [map_inv] at h
    have hmemNbar : (⟨(π (gen kK : ↥L))⁻¹, hNmap_le huk_mem_map⟩ :
        ↥(derivedCent x)) ∈ Nbar :=
      Subgroup.mem_subgroupOf.mpr huk_mem_map
    have hcentral := hcentral hmemNbar
    have hEq : α y * y⁻¹ = (⟨(π (gen kK : ↥L))⁻¹, hNmap_le huk_mem_map⟩ :
        ↥(derivedCent x)) := by
      apply Subtype.ext
      change (α y : X) * (y : X)⁻¹ = (π (gen kK : ↥L))⁻¹
      let l1 : ↥L := ⟨(u : MulAut V) * (k : MulAut V) * (u : MulAut V)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAL' u.2) (k : MulAut V)).mp k.2⟩
      have hl1 : φ u (π k) = π l1 := hφ_mk u k
      calc (α y : X) * (y : X)⁻¹
          = (π l1) * (π k)⁻¹ := by rw [hα_apply, ← hkπ, hl1]
        _ = (π l1) * π k⁻¹ := by rw [map_inv]
        _ = π (l1 * k⁻¹) := by rw [← map_mul]
        _ = π ((gen kK : ↥L)⁻¹) := by rfl
        _ = (π (gen kK : ↥L))⁻¹ := by rw [map_inv]
    rwa [hEq]
  by_cases hcentral : Nbar ≤ Subgroup.center ↥(derivedCent x)
  · exfalso
    have hα_one : α = 1 :=
      CFSG.Quasithin.SBd14.eq_one_of_central_perfect ⟨hX'.quasi.1⟩ α (hα_cent hcentral)
    have hfixKbar : ∀ y ∈ derivedCent x, φ u y = y := by
      intro y hy
      have h := congrArg (fun β : MulAut ↥(derivedCent x) => β ⟨y, hy⟩) hα_one
      simp only [MulAut.one_apply] at h
      have h2 := congrArg (fun z : ↥(derivedCent x) => (z : X)) h
      rw [hα_apply] at h2
      exact h2
    have hcent := hX'.cent (φ u) hφu_sq hφu_x hfixKbar
    rcases hcent with h1 | h2
    · have hu_eq : u = 1 := hφinj (h1.trans (map_one φ).symm)
      exact hu1 hu_eq
    · have hu_eq : u = aA := hφinj (h2.trans hβconj.symm)
      exact hua hu_eq
  · have : IsSimpleGroup (↥(derivedCent x) ⧸ Subgroup.center ↥(derivedCent x)) :=
      hX'.quasi.2
    let ZK : Subgroup ↥(derivedCent x) := Subgroup.center ↥(derivedCent x)
    let q : ↥(derivedCent x) →* (↥(derivedCent x) ⧸ ZK) := QuotientGroup.mk' ZK
    have hq_normal : (Nbar.map q).Normal :=
      hNbar_normal.map q (QuotientGroup.mk'_surjective ZK)
    have hNbar_top : Nbar = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nbar.map q) with hbot | htop
      · exfalso
        apply hcentral
        intro y hy
        have hyq : q y = 1 := by
          have hmem : q y ∈ Nbar.map q := Subgroup.mem_map_of_mem q hy
          rw [hbot] at hmem
          exact Subgroup.mem_bot.mp hmem
        rw [QuotientGroup.mk'_apply] at hyq
        rw [QuotientGroup.eq_one_iff] at hyq
        exact hyq
      · have hsup : Nbar ⊔ ZK = ⊤ := by
          have h := Subgroup.comap_map_eq (f := q) (H := Nbar)
          rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
          exact h.symm
        have hperf : Group.IsPerfect ↥(derivedCent x) := ⟨hX'.quasi.1⟩
        exact le_antisymm le_top (le_of_perfect_le_sup_center hperf le_rfl hsup.symm.le)
    have hNmap_top : N.map π = derivedCent x := by
      apply le_antisymm hNmap_le
      intro y hy
      have hyNbar : (⟨y, hy⟩ : ↥(derivedCent x)) ∈ Nbar := by
        rw [hNbar_top]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hyNbar
    have hK_le_NZ : ∀ k ∈ K, ∃ n ∈ N, ∃ z ∈ Z, (k : ↥L) = n * z := by
      intro k hk
      have hmem : π k ∈ N.map π := by
        rw [hNmap_top, ← hKmap]
        exact Subgroup.mem_map_of_mem π hk
      obtain ⟨n, hnN, hnπ⟩ := Subgroup.mem_map.mp hmem
      refine ⟨n, hnN, n⁻¹ * k, ?_, by group⟩
      rw [show Z = Subgroup.center ↥L from rfl]
      exact QuotientGroup.eq.mp hnπ
    have hK_le_N : K ≤ N := by
      let M : Subgroup ↥K := N.subgroupOf K
      let ZK' : Subgroup ↥K := (Z ⊓ K).subgroupOf K
      have hZK'_cent : ZK' ≤ Subgroup.center ↥K := by
        intro z hz
        have hz' : ((z : ↥K) : ↥L) ∈ Z ⊓ K := Subgroup.mem_subgroupOf.mp hz
        rw [Subgroup.mem_center_iff]
        intro w
        have hcomm := Subgroup.mem_center_iff.mp hz'.1 ((w : ↥K) : ↥L)
        apply Subtype.ext
        exact hcomm
      have htop : (⊤ : Subgroup ↥K) ≤ M ⊔ ZK' := by
        intro x _
        obtain ⟨n, hnN, z, hzZ, hxz⟩ := hK_le_NZ x x.2
        have hzK : z ∈ K := by
          have hz_eq : z = n⁻¹ * (x : ↥L) := by
            rw [hxz]
            group
          rw [hz_eq]
          exact K.mul_mem (K.inv_mem (hN_le_K hnN)) x.2
        let nK : ↥K := ⟨n, hN_le_K hnN⟩
        let zK : ↥K := ⟨z, hzK⟩
        have hxeq : x = nK * zK := by
          apply Subtype.ext
          exact hxz
        rw [hxeq]
        exact (M ⊔ ZK').mul_mem
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hnN))
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ⟨hzZ, hzK⟩))
      have : ZK'.Normal := Subgroup.normal_of_le_center hZK'_cent
      have hle : (⊤ : Subgroup ↥K) ≤ M :=
        le_of_perfect_le_sup_center hKperfect hZK'_cent htop
      intro k hk
      exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top ⟨k, hk⟩))
    have hK_le_quadY : ∀ k ∈ K, (k : MulAut V) ∈ quadY G A a := by
      intro k hk
      exact hN_le_quadY k (hK_le_N hk)
    have hgen_step : ∀ h ∈ G, h * a * h⁻¹ * a = a * (h * a * h⁻¹) →
        h * a * h⁻¹ ≠ a →
        L ≤ quadY G A a ⊔ (quadY G A a).map (MulAut.conj h).toMonoidHom := by
      intro h hhG hcomm hne
      have hAG : A ≤ G := le_sup_left
      have hLG : L ≤ G := le_sup_right
      have hLnormal : (L.subgroupOf G).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLG]
        exact sup_le hAL' Subgroup.le_normalizer
      have hsupG : A.subgroupOf G ⊔ L.subgroupOf G = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hAG hLG, show A ⊔ L = G from rfl]
        exact Subgroup.subgroupOf_self G
      have hh' : (⟨h, hhG⟩ : ↥G) ∈ A.subgroupOf G ⊔ L.subgroupOf G := by
        rw [hsupG]
        exact Subgroup.mem_top _
      have := hLnormal
      obtain ⟨u, hu, l, hl, hul⟩ := Subgroup.mem_sup_of_normal_right.mp hh'
      have huA : (u : MulAut V) ∈ A := Subgroup.mem_subgroupOf.mp hu
      have hlL : (l : MulAut V) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have hh_eq : h = (u : MulAut V) * (l : MulAut V) := by
        simpa using (congrArg Subtype.val hul).symm
      have huaeq : (u : MulAut V) * a * (u : MulAut V)⁻¹ = a := by
        have hau : (u : MulAut V) * a = a * (u : MulAut V) := hAcomm u huA a aA.2
        calc (u : MulAut V) * a * (u : MulAut V)⁻¹ = (a * (u : MulAut V)) *
            (u : MulAut V)⁻¹ := by rw [hau]
          _ = a := by group
      let l' : ↥L := ⟨(u : MulAut V) * (l : MulAut V) * (u : MulAut V)⁻¹,
        hAL u huA (l : MulAut V) hlL⟩
      have hua_inv : (u : MulAut V)⁻¹ * a * (u : MulAut V) = a := by
        calc (u : MulAut V)⁻¹ * a * (u : MulAut V)
            = (u : MulAut V)⁻¹ * ((u : MulAut V) * a * (u : MulAut V)⁻¹) *
                (u : MulAut V) := by rw [huaeq]
          _ = a := by group
      have hah_eq : h * a * h⁻¹ = (l' : MulAut V) * a * (l' : MulAut V)⁻¹ := by
        calc h * a * h⁻¹
            = (u : MulAut V) * ((l : MulAut V) * a * (l : MulAut V)⁻¹) *
                (u : MulAut V)⁻¹ := by rw [hh_eq]; group
          _ = (u : MulAut V) * ((l : MulAut V) * ((u : MulAut V)⁻¹ * a * (u : MulAut V)) *
                (l : MulAut V)⁻¹) * (u : MulAut V)⁻¹ := by rw [hua_inv]
          _ = (l' : MulAut V) * a * (l' : MulAut V)⁻¹ := by
              dsimp only [l']
              group
      let tl : ↥L := l' * t * l'⁻¹
      have htl_sq : tl * tl = 1 := by
        show (l' * t * l'⁻¹) * (l' * t * l'⁻¹) = 1
        calc (l' * t * l'⁻¹) * (l' * t * l'⁻¹) = l' * (t * t) * l'⁻¹ := by group
          _ = 1 := by rw [ht2]; simp
      let y : X := π tl
      have hy_sq : y * y = 1 := by
        show π tl * π tl = 1
        rw [← map_mul, htl_sq, map_one]
      have hy_ne_one : y ≠ 1 := by
        intro hy1
        have htlc : tl ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff tl).mp hy1
        have htl1 : tl = 1 := eq_one_of_sq_eq_one_of_odd_center hZ htlc htl_sq
        have ht1 : t = 1 := by
          have h : l' * t * l'⁻¹ = 1 := htl1
          calc t = l'⁻¹ * (l' * t * l'⁻¹) * l' := by group
            _ = 1 := by rw [h]; simp
        exact hx1 (by rw [← hπt, ht1, map_one])
      have hy_ord : orderOf y = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hy_sq) hy_ne_one
      have hcl' : c * (l' : MulAut V) = (l' : MulAut V) * c := by
        have h := hcC (l' : MulAut V) l'.2
        calc c * (l' : MulAut V) = (c * (l' : MulAut V) * c⁻¹) * c := by group
          _ = (l' : MulAut V) * c := by rw [h]
      have ha_l' : (l' : MulAut V) * a * (l' : MulAut V)⁻¹ =
          (tl : MulAut V) * c := by
        rw [← htca]
        have hcl'c : (l' : MulAut V) * c * (l' : MulAut V)⁻¹ = c := by
          calc (l' : MulAut V) * c * (l' : MulAut V)⁻¹ =
              ((l' : MulAut V) * c) * (l' : MulAut V)⁻¹ := rfl
            _ = (c * (l' : MulAut V)) * (l' : MulAut V)⁻¹ := by rw [hcl']
            _ = c := by group
        calc (l' : MulAut V) * ((t : MulAut V) * c) * (l' : MulAut V)⁻¹ =
            ((l' : MulAut V) * (t : MulAut V) * (l' : MulAut V)⁻¹) *
              ((l' : MulAut V) * c * (l' : MulAut V)⁻¹) := by group
          _ = ((l' : MulAut V) * (t : MulAut V) * (l' : MulAut V)⁻¹) * c := by rw [hcl'c]
          _ = (tl : MulAut V) * c := by rfl
      have hcomm_l' : ((tl : MulAut V) * c) * ((t : MulAut V) * c) =
          ((t : MulAut V) * c) * ((tl : MulAut V) * c) := by
        rw [← ha_l', htca]
        rw [← hah_eq]
        exact hcomm
      have hctl : c * (tl : MulAut V) = (tl : MulAut V) * c := by
        have h := hcC (tl : MulAut V) tl.2
        calc c * (tl : MulAut V) = (c * (tl : MulAut V) * c⁻¹) * c := by group
          _ = (tl : MulAut V) * c := by rw [h]
      have hcomm_tl : (tl : MulAut V) * (t : MulAut V) =
          (t : MulAut V) * (tl : MulAut V) := by
        calc (tl : MulAut V) * (t : MulAut V)
            = ((tl : MulAut V) * c) * ((t : MulAut V) * c) := by
              rw [show ((tl : MulAut V) * c) * ((t : MulAut V) * c) =
                (tl : MulAut V) * (c * (t : MulAut V)) * c from by group]
              rw [hct]
              rw [show (tl : MulAut V) * ((t : MulAut V) * c) * c =
                (tl : MulAut V) * (t : MulAut V) * (c * c) from by group]
              rw [hcc]
              group
          _ = ((t : MulAut V) * c) * ((tl : MulAut V) * c) := hcomm_l'
          _ = (t : MulAut V) * (tl : MulAut V) := by
              rw [show ((t : MulAut V) * c) * ((tl : MulAut V) * c) =
                (t : MulAut V) * (c * (tl : MulAut V)) * c from by group]
              rw [hctl]
              rw [show (t : MulAut V) * ((tl : MulAut V) * c) * c =
                (t : MulAut V) * (tl : MulAut V) * (c * c) from by group]
              rw [hcc]
              group
      have hy_comm : y * x = x * y := by
        show y * x = x * y
        rw [show y = π tl from rfl, ← hπt]
        have hcomm_tl_sub : tl * t = t * tl := Subtype.ext hcomm_tl
        rw [← map_mul, ← map_mul, hcomm_tl_sub]
      have hy_ne_x : x ≠ y := by
        intro hxy
        apply hne
        rw [hah_eq, ha_l']
        have htl_eq : tl = t :=
          eq_of_mk_eq_of_sq_center hZ htl_sq ht2 (hxy.symm.trans hπt.symm)
        rw [show tl = t from htl_eq, ← htca]
      have hy_eq : y = (MulAut.conj (π l')) x := by
        show π tl = (MulAut.conj (π l')) x
        rw [show tl = l' * t * l'⁻¹ from rfl, map_mul, map_mul, map_inv, hπt,
          MulAut.conj_apply]
      have hgenX : derivedCent x ⊔ derivedCent y = ⊤ :=
        hX'.gen y hy_ord hy_comm.symm hy_ne_x
      have hA_quadY_le : ∀ z ∈ A,
          (quadY G A a).map (MulAut.conj z).toMonoidHom ≤ quadY G A a := by
        intro z hz
        simp only [quadY, Subgroup.map_iSup]
        refine iSup_le fun x => iSup_le fun hxG => iSup_le fun hxa => ?_
        rw [Subgroup.map_map]
        have e : (MulAut.conj z).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
            (MulAut.conj (z * x)).toMonoidHom := by
          rw [show MulAut.conj (z * x) = MulAut.conj z * MulAut.conj x from
            map_mul (MulAut.conj : MulAut V →* MulAut (MulAut V)) z x]
          rfl
        rw [e]
        refine le_iSup_of_le (z * x)
          (le_iSup_of_le (G.mul_mem (Subgroup.mem_sup_left hz) hxG)
            (le_iSup_of_le ?_ le_rfl))
        calc (z * x) * a = z * (x * a) := by group
          _ = z * (a * x) := by rw [hxa]
          _ = (z * a) * x := by group
          _ = (a * z) * x := by rw [hAcomm z hz a aA.2]
          _ = a * (z * x) := by group
      let ψl : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨l', Subgroup.le_normalizer l'.2⟩
      let Kl : Subgroup ↥L := K.map ψl.toMonoidHom
      have hKl_map : Kl.map π = derivedCent y := by
        rw [show Kl = K.map ψl.toMonoidHom from rfl, Subgroup.map_map]
        have hcomp : ∀ w : ↥L, (π.comp ψl.toMonoidHom) w =
            (MulAut.conj (π l')).toMonoidHom w := by
          intro w
          show π (ψl w) = (MulAut.conj (π l')) (π w)
          have hsub : ψl w = l' * w * l'⁻¹ :=
            Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe (H := L)
              ⟨l', Subgroup.le_normalizer l'.2⟩ w)
          rw [hsub, map_mul, map_mul, map_inv, MulAut.conj_apply]
        have hmap_eq : K.map (π.comp ψl.toMonoidHom) =
            (K.map π).map (MulAut.conj (π l')).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
        rw [hmap_eq, hKmap, derivedCent_map, ← hy_eq]
      have hKsupKl_map : (K ⊔ Kl).map π = ⊤ := by
        rw [Subgroup.map_sup, hKmap, hKl_map, hgenX]
      have hL_le_KsupKl : L ≤ (K ⊔ Kl).map L.subtype := by
        have htop : (⊤ : Subgroup ↥L) ≤ (K ⊔ Kl) ⊔ Z := by
          intro w _
          have hw : π w ∈ (K ⊔ Kl).map π := by
            rw [hKsupKl_map]
            exact Subgroup.mem_top _
          obtain ⟨m, hm, hmπ⟩ := Subgroup.mem_map.mp hw
          have hz : m⁻¹ * w ∈ Z := by
            rw [show Z = Subgroup.center ↥L from rfl]
            exact QuotientGroup.eq.mp hmπ
          have hxeq : w = m * (m⁻¹ * w) := by group
          rw [hxeq]
          exact ((K ⊔ Kl) ⊔ Z).mul_mem (Subgroup.mem_sup_left hm)
            (Subgroup.mem_sup_right hz)
        have hle : (⊤ : Subgroup ↥L) ≤ K ⊔ Kl :=
          le_of_perfect_le_sup_center ⟨hL.1⟩ le_rfl htop
        intro x hxL
        exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hle (Subgroup.mem_top _), rfl⟩
      have hK_quadY_amb : K.map L.subtype ≤ quadY G A a := by
        rintro w ⟨k, hk, rfl⟩
        exact hK_le_quadY k hk
      have h_l' : h * (u : MulAut V)⁻¹ = (l' : MulAut V) := by
        rw [hh_eq]
      have hKl_quadYh : Kl.map L.subtype ≤
          (quadY G A a).map (MulAut.conj h).toMonoidHom := by
        rintro w ⟨k, hk, rfl⟩
        obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.mp hk
        have hy0 : ((u : MulAut V)⁻¹ * (k0 : MulAut V) * (u : MulAut V)) ∈ quadY G A a := by
          have hmap := hA_quadY_le (u : MulAut V)⁻¹ (A.inv_mem huA)
          exact hmap (Subgroup.mem_map.mpr ⟨(k0 : MulAut V), hK_le_quadY k0 hk0, by
            simp⟩)
        refine Subgroup.mem_map.mpr ⟨(u : MulAut V)⁻¹ * (k0 : MulAut V) * (u : MulAut V), hy0, ?_⟩
        change h * ((u : MulAut V)⁻¹ * (k0 : MulAut V) * (u : MulAut V)) * h⁻¹ =
          ((ψl k0 : ↥L) : MulAut V)
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rw [← h_l']
        group
      have hquadY_sup : L ≤ quadY G A a ⊔ (quadY G A a).map (MulAut.conj h).toMonoidHom := by
        refine hL_le_KsupKl.trans ?_
        rw [Subgroup.map_sup]
        exact sup_le_sup hK_quadY_amb hKl_quadYh
      exact hquadY_sup
    have hMain : ∀ g : MulAut V, g ∈ G →
        Odd (orderOf (a * (g * a * g⁻¹))) ∨ orderOf (a * (g * a * g⁻¹)) ≤ 2 := by
      intro g hg
      exact odd_or_le_two_of_le_quadY_sup hV le_sup_left hA aA.2 (hA2 a aA.2) hfix
        hgen_step hg
    obtain ⟨gX, hgX⟩ := hX'.four
    obtain ⟨gL, hgL⟩ := QuotientGroup.mk'_surjective (center ↥L) gX
    have hgLG : (gL : MulAut V) ∈ G := Subgroup.mem_sup_right (gL : ↥L).2
    have hπg : π (t * (gL * t * gL⁻¹)) = x * (gX * x * gX⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, hπt, hgL]
    have hg_order : a * ((gL : MulAut V) * a * (gL : MulAut V)⁻¹) =
        (t : MulAut V) * ((gL : MulAut V) * (t : MulAut V) * (gL : MulAut V)⁻¹) :=
      hLU gL gL.2
    have h4 : 4 ∣ orderOf (a * ((gL : MulAut V) * a * (gL : MulAut V)⁻¹)) := by
      rw [hg_order]
      have hdiv := orderOf_map_dvd π (t * (gL * t * gL⁻¹))
      rw [hπg, hgX] at hdiv
      have hdiv_amb : 4 ∣ orderOf (((t * (gL * t * gL⁻¹) : ↥L) : MulAut V)) := by
        rw [Subgroup.orderOf_coe]
        exact hdiv
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hdiv_amb
    rcases hMain (gL : MulAut V) hgLG with hodd | hle
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4))
    · have hpos : 0 < orderOf (a * ((gL : MulAut V) * a * (gL : MulAut V)⁻¹)) :=
        orderOf_pos _
      omega

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
