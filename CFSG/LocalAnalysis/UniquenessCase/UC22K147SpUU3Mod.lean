module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.FFModules.RepMulAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Setup CFSG.RankThree.FFModules

theorem index_fixV_zpowers_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (a : MulAut (Multiplicative W)) (f : W →ₗ[ZMod 2] W)
    (h : ∀ w, a (Multiplicative.ofAdd w) = Multiplicative.ofAdd (f w)) :
    (CFSG.Quasithin.fixV (zpowers a)).index =
      2 ^ (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (LinearMap.ker (f - 1))) := by
  have hcard : Nat.card (CFSG.Quasithin.fixV (zpowers a)) = Nat.card (LinearMap.ker (f - 1)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun v => ?_)
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    constructor
    · intro hv
      exact congrArg Multiplicative.toAdd ((h (Multiplicative.toAdd v)).symm.trans hv)
    · intro hv
      calc a v = a (Multiplicative.ofAdd (Multiplicative.toAdd v)) := rfl
        _ = Multiplicative.ofAdd (f (Multiplicative.toAdd v)) := h _
        _ = v := by rw [hv]; rfl
  have hW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    rw [show Nat.card (Multiplicative W) = Nat.card W from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hK : Nat.card (LinearMap.ker (f - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (f - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : Module.finrank (ZMod 2) (LinearMap.ker (f - 1)) ≤ Module.finrank (ZMod 2) W :=
    Submodule.finrank_le _
  have hmul := (CFSG.Quasithin.fixV (zpowers a)).card_mul_index
  rw [hcard, hK, hW] at hmul
  refine Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (hmul.trans ?_)
  rw [← pow_add, Nat.add_sub_cancel' hle]

theorem repMulAut_range_facts {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {Y : Type} [Group Y]
    (β : X ⧸ center X ≃* Y) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ g, ρ g ≠ 1) :
    Group.IsPerfect (repMulAut ρ).range ∧
      (∀ U : Subgroup (Multiplicative W), (∀ g ∈ (repMulAut ρ).range, ∀ u ∈ U, g u ∈ U) →
        U = ⊥ ∨ U = ⊤) ∧
      Nonempty ((repMulAut ρ).range ⧸ center (repMulAut ρ).range ≃* Y) ∧
      (repMulAut ρ).ker ≤ center X := by
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have hnat : CFSG.IsQuasisimple X :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian X hq⟩
  have hψ : ∃ g, (repMulAut ρ).rangeRestrict g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h1 => hg (LinearMap.ext fun w => ?_)⟩
    have h2 : repMulAut ρ g = 1 := congrArg Subtype.val h1
    have := congrArg (fun F : MulAut (Multiplicative W) =>
      Multiplicative.toAdd (F (Multiplicative.ofAdd w))) h2
    exact this
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hnat hψ
  rw [MonoidHom.ker_rangeRestrict] at hker
  refine ⟨Group.IsPerfect.range _, fun U hU => ?_,
    ⟨(CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hnat
      (MonoidHom.rangeRestrict_surjective _) (by rw [MonoidHom.ker_rangeRestrict]; exact hker)).symm.trans β⟩,
    hker⟩
  let T : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup U)
  have hmem : ∀ w : W, w ∈ T ↔ Multiplicative.ofAdd w ∈ U := fun w => Iff.rfl
  have hT : ∀ g, ∀ u ∈ T, ρ g u ∈ T := fun g u hu => (hmem _).2 (hU _ ⟨g, rfl⟩ _ ((hmem u).1 hu))
  rcases hirr T hT with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have : Multiplicative.toAdd v ∈ T := (hmem _).2 hv
    rw [h, Submodule.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Multiplicative.toAdd.injective this
  · right
    rw [eq_top_iff]
    intro v _
    exact (hmem (Multiplicative.toAdd v)).1 (by rw [h]; exact Submodule.mem_top)

theorem exists_involution_unitarySU_three {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    (hU : UnitaryFieldData 2 n K) : ∃ s : unitarySU 2 n K 3, s * s = 1 ∧ s ≠ 1 := by
  obtain ⟨ℓ, hppd⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega) (by omega)
  have hℓ : ℓ.Prime := hppd.prime
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h2pow : (2 : ZMod ℓ) ^ (6 * n) = 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (6 * n)).mp hppd.dvd
  have hpos : 0 < orderOf (2 : ZMod ℓ) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨6 * n, by omega, h2pow⟩)
  have hge : 6 * n ≤ orderOf (2 : ZMod ℓ) :=
    Nat.le_of_dvd hpos ((hppd.dvd_sub_one_iff (by omega) _).mp
      ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mpr (pow_orderOf_eq_one _)))
  have hord : orderOf (2 : ZMod ℓ) = 6 * n :=
    le_antisymm (Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2pow)) hge
  obtain ⟨s, -, -, hs, hs1, -⟩ := X5.exists_three_involutions hn hU hℓ hord
  exact ⟨s, hs, hs1⟩

theorem not_mem_unitaryScalars_of_involution {n : ℕ} {K : Type} [Field K] {hU : UnitaryFieldData 2 n K}
    {s : unitarySU 2 n K 3} (hs : s * s = 1) (hs1 : s ≠ 1) : s ∉ unitaryScalars hU 3 := by
  intro hsc
  have h3 := X5.scalar_pow_three_matrix hsc
  apply hs1
  calc s = s ^ 3 * (s * s)⁻¹ := by group
    _ = 1 := by rw [h3, hs]; simp

theorem exists_orderOf_eq_two_of_unitary {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] (hU : UnitaryFieldData 2 n K) (β : X ⧸ center X ≃* unitaryPSU hU 3) :
    ∃ x : X, orderOf x = 2 := by
  obtain ⟨s, hs, hs1⟩ := exists_involution_unitarySU_three hn hU
  have hp2 : unitaryProj hU 3 s * unitaryProj hU 3 s = 1 := by rw [← map_mul, hs, map_one]
  have hp1 : unitaryProj hU 3 s ≠ 1 := fun h0 =>
    not_mem_unitaryScalars_of_involution hs hs1 (by rw [← ker_unitaryProj]; exact h0)
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β.symm (unitaryProj hU 3 s))
  have hxo : orderOf (QuotientGroup.mk' (center X) x) = 2 := by
    rw [QuotientGroup.mk'_apply, hx, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hp2) hp1
  have hdvd : 2 ∣ orderOf x := hxo ▸ orderOf_map_dvd (QuotientGroup.mk' (center X)) x
  exact ⟨x ^ (orderOf x / 2), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd⟩

section Bounds

set_option linter.unusedSectionVars false

theorem two_mul_le_finrank_of_irreducible {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] (hU : UnitaryFieldData 2 n K) (β : X ⧸ center X ≃* unitaryPSU hU 3)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ g, ρ g ≠ 1) : 2 * n ≤ Module.finrank (ZMod 2) W := by
  haveI : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    obtain ⟨g, hg⟩ := hnt
    exact hg (LinearMap.ext fun w => Subsingleton.elim _ _)
  obtain ⟨hperf, hirr', ⟨α⟩, -⟩ := repMulAut_range_facts hq β ρ hirr hnt
  obtain ⟨⟨φ, -, hφk, -, -⟩, -, h3, -⟩ :=
    X5.irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders hn hU
      (fun w => by simpa [sq] using multiplicative_sq w) _ hperf hirr' α
  obtain ⟨s, hs, hs1⟩ := exists_involution_unitarySU_three hn hU
  have hφs : (φ s : MulAut (Multiplicative W)) * φ s = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hs, map_one, Subgroup.coe_one]
  have hφs1 : (φ s : MulAut (Multiplicative W)) ≠ 1 := fun h0 =>
    not_mem_unitaryScalars_of_involution hs hs1 (hφk (MonoidHom.mem_ker.mpr (Subtype.ext h0)))
  obtain ⟨g, hg⟩ := (φ s).2
  have hidx := index_fixV_zpowers_eq (φ s : MulAut (Multiplicative W)) (ρ g) fun w => by
    rw [← hg]; rfl
  have h := h3 _ (φ s).2 hφs hφs1
  rw [hidx, Nat.pow_le_pow_iff_right (by norm_num)] at h
  omega

theorem two_mul_le_finrank {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] (hU : UnitaryFieldData 2 n K) (β : X ⧸ center X ≃* unitaryPSU hU 3)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (ρ : Representation (ZMod 2) X M) (hnt : ∃ g, ρ g ≠ 1) : 2 * n ≤ Module.finrank (ZMod 2) M := by
  have hperf : Group.IsPerfect X := ⟨hq.1⟩
  refine X7b.rep_induction (k := ZMod 2) (G := X)
    (fun {V} _ _ _ ρ => (∃ g, ρ g ≠ 1) → 2 * n ≤ Module.finrank (ZMod 2) V)
    (fun {V} _ _ _ ρ _ hex => ?_) (fun {V} _ _ _ ρ hirr hex => ?_)
    (fun {V} _ _ _ ρ W h1 h2 hex => ?_) (Module.finrank (ZMod 2) M) ρ rfl hnt
  · obtain ⟨g, hg⟩ := hex
    exact absurd (LinearMap.ext fun v => Subsingleton.elim _ _) hg
  · haveI : Finite V := Module.finite_of_finite (ZMod 2)
    refine two_mul_le_finrank_of_irreducible hq hn hU β ρ (fun U hU => ?_) hex
    rcases hirr.eq_bot_or_eq_top ⟨U, fun g v hv => hU g v hv⟩ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  · by_cases hW : ∃ g, W.toRepresentation g ≠ 1
    · have := h1 hW
      have := Submodule.finrank_le W.toSubmodule
      omega
    · by_cases hQ : ∃ g, W.quotient g ≠ 1
      · have := h2 hQ
        have := Submodule.finrank_quotient_le W.toSubmodule
        omega
      · push Not at hW hQ
        obtain ⟨g, hg⟩ := hex
        exact absurd (X7b.trivial_of_sub_quot hperf (MonoidHom.id X) ρ W hW hQ g) hg

theorem two_mul_le_of_gsIrreducible {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] (hU : UnitaryFieldData 2 n K) (β : X ⧸ center X ≃* unitaryPSU hU 3)
    (τ : X ≃* X) (hτ : ∃ g, τ g ≠ g) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (ρ : Representation (ZMod 2) X W) (s : W ≃ₗ[ZMod 2] W)
    (hss : ∀ w, s (s w) = w) (hs : ∀ g w, s (ρ g w) = ρ (τ g) (s w)) (hgs : X7b.GSIrreducible ρ s)
    (hW : Nontrivial W) (hnt : ∃ g, ρ g ≠ 1) :
    2 * n ≤ Module.finrank (ZMod 2) W -
      Module.finrank (ZMod 2) (LinearMap.ker (s.toLinearMap - 1)) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have hsg : ∀ g w, ρ g (s w) = s (ρ (τ.symm g) w) := fun g w => by
    rw [hs, MulEquiv.apply_symm_apply]
  by_cases hred : ∃ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ U ≠ ⊥ ∧ U ≠ ⊤
  ·
    obtain ⟨U, hUinv, hU0, hUtop⟩ := hred
    set S : Submodule (ZMod 2) W := U.map s.toLinearMap with hSdef
    have hSinv : ∀ g, ∀ v ∈ S, ρ g v ∈ S := by
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨ρ (τ.symm g) u, hUinv _ u hu, (hsg g u).symm⟩
    have hsU : ∀ u ∈ U, s u ∈ S := fun u hu => ⟨u, hu, rfl⟩
    have hsS : ∀ v ∈ S, s v ∈ U := by
      rintro _ ⟨u, hu, rfl⟩
      show s (s u) ∈ U
      rw [hss]
      exact hu
    have hinf : U ⊓ S = ⊥ := by
      rcases hgs (U ⊓ S) (fun g v hv => ⟨hUinv g v hv.1, hSinv g v hv.2⟩)
          (fun v hv => ⟨hsS v hv.2, hsU v hv.1⟩) with h | h
      · exact h
      · exact absurd (eq_top_iff.mpr (h ▸ inf_le_left)) hUtop
    have hker : U ⊓ LinearMap.ker (s.toLinearMap - 1) = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvU, hvk⟩
      have hsv : s v = v := by
        have hvk' : v ∈ LinearMap.ker (s.toLinearMap - 1) := hvk
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvk'
        exact hvk'
      have hv : v ∈ U ⊓ S := ⟨hvU, hsv ▸ hsU v hvU⟩
      rw [hinf] at hv
      exact hv
    let R : Subrepresentation ρ := ⟨U, fun g v hv => hUinv g v hv⟩
    have hmov : ∃ g, R.toRepresentation g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hfixU : ∀ g, ∀ u ∈ U, ρ g u = u := fun g u hu => by
        have := congrArg (fun T => ((T ⟨u, hu⟩ : U) : W)) (hcon g)
        exact this
      have hfixS : ∀ g, ∀ v ∈ S, ρ g v = v := by
        rintro g _ ⟨u, hu, rfl⟩
        show ρ g (s u) = s u
        rw [hsg, hfixU _ u hu]
      have hsup : U ⊔ S = ⊤ := by
        rcases hgs (U ⊔ S) (fun g v hv => by
            obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
            rw [map_add]
            exact Submodule.add_mem_sup (hUinv g u hu) (hSinv g w hw))
          (fun v hv => by
            obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
            rw [map_add, add_comm]
            exact Submodule.add_mem_sup (hsS w hw) (hsU u hu)) with h | h
        · exact absurd (eq_bot_iff.mpr (h ▸ le_sup_left)) hU0
        · exact h
      obtain ⟨g, hg⟩ := hnt
      apply hg
      refine LinearMap.ext fun w => ?_
      have hw : w ∈ U ⊔ S := hsup ▸ Submodule.mem_top
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, hfixU g u hu, hfixS g v hv]
      rfl
    have hdim : 2 * n ≤ Module.finrank (ZMod 2) U := two_mul_le_finrank hq hn hU β R.toRepresentation hmov
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker (s.toLinearMap - 1))
    rw [hker, finrank_bot] at h1
    have h2 := Submodule.finrank_le (U ⊔ LinearMap.ker (s.toLinearMap - 1))
    omega
  ·
    push Not at hred
    have hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      by_contra h
      push Not at h
      exact h.2 (hred U hU h.1)
    obtain ⟨hperf, hirr', ⟨α⟩, hkerc⟩ := repMulAut_range_facts hq β ρ hirr hnt
    have hsq : ∀ w : Multiplicative W, w * w = 1 := fun w => by simpa [sq] using multiplicative_sq w
    have hX5 := X5.irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders hn hU hsq _
      hperf hirr' α
    set L : Subgroup (MulAut (Multiplicative W)) := (repMulAut ρ).range with hLdef
    let a : MulAut (Multiplicative W) := AddEquiv.toMultiplicative s.toAddEquiv
    have haa : a * a = 1 := MulEquiv.ext fun v => by
      show Multiplicative.ofAdd (s (s (Multiplicative.toAdd v))) = v
      rw [hss]
      rfl
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have hconj : ∀ g, a * repMulAut ρ g * a⁻¹ = repMulAut ρ (τ g) := fun g => by
      rw [hainv]
      refine MulEquiv.ext fun v => ?_
      show Multiplicative.ofAdd (s (ρ g (s (Multiplicative.toAdd v)))) =
        Multiplicative.ofAdd (ρ (τ g) (Multiplicative.toAdd v))
      rw [hs, hss]
    have haN : a ∈ normalizer (L : Set (MulAut (Multiplicative W))) := by
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨τ g, (hconj g).symm⟩
      · rintro ⟨g, hg⟩
        refine ⟨τ g, ?_⟩
        rw [← hconj, hg, hainv]
        calc a * (a * h * a) * a = a * a * h * (a * a) := by group
          _ = h := by rw [haa, one_mul, mul_one]
    have hidx := index_fixV_zpowers_eq a s.toLinearMap fun w => rfl
    by_cases hinn : ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
        a * x * a⁻¹ = l * x * l⁻¹ * z
    ·
      haveI : Group.IsPerfect L := hperf
      have hodd := X5.centralizer_odd hsq L hirr'
      have haL : a ∈ L := by
        refine X5.mem_of_involution_inner L hodd haN haa ?_
        obtain ⟨l, hl, hlx⟩ := hinn
        refine ⟨QuotientGroup.mk ⟨l, hl⟩, MulEquiv.ext fun y => ?_⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨z, hz, hzc, hxz⟩ := hlx x x.2
        rw [MulAut.conj_apply, X5.normalizerAct_apply_mk, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hz' : (⟨l, hl⟩ * x * (⟨l, hl⟩ : L)⁻¹)⁻¹ * X5.conjOn L ⟨a, haN⟩ x = ⟨z, hz⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, X5.coe_conjOn]
          rw [hxz]
          group
        rw [hz', Subgroup.mem_center_iff]
        exact fun y => Subtype.ext (hzc y y.2)
      have ha1 : a ≠ 1 := by
        intro h1
        obtain ⟨g, hg⟩ := hτ
        have hcen : ∀ x : X, x⁻¹ * τ.toMonoidHom x ∈ center X := fun x => hkerc (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, ← hconj x, h1]
          group)
        have := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
          τ.toMonoidHom hcen
        exact hg (congrArg (fun f : X →* X => f g) this)
      have h3 := hX5.2.2.1 a haL haa ha1
      rw [hidx, Nat.pow_le_pow_iff_right (by norm_num)] at h3
      exact h3
    ·
      have h4 := hX5.2.2.2.1 a haN haa hinn
      rw [hidx, Nat.pow_le_pow_iff_right (by norm_num)] at h4
      omega

end Bounds

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU
