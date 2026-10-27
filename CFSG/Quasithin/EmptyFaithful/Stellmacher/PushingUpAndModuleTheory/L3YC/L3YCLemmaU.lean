module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Case4Orders
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCCommPhiCase4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7
open scoped commutatorElement

namespace Stellmacher.PU.L3YC

variable {G : Type} [Group G] [Finite G]

theorem card_section_c134Q {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) {D : Subgroup G} (hCD : c134CQ G₀ L ≤ D)
    (hDQ : D ≤ c134Q G₀ L) (hDL : L ≤ Subgroup.normalizer (D : Set G)) :
    ∃ j : ℕ, Nat.card ↥(c134Q G₀ L) = Nat.card ↥D * 8 ^ j := by
  classical
  have hT1 := comm_frattini_eq_CQ hLG hGL hq h
  have h' := h
  obtain ⟨⟨n, F, iF, fF, α, hFc, hα, hE2, hZ, hCU, hnatU, hnatΦ, hK, hnatQ⟩, -⟩ := h'
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  obtain ⟨hC4', -⟩ := isE2_card_sq hE2
  have hC4 : Nat.card ↥(c134CQ G₀ L) = 4 := by rw [hC4']; norm_num
  have h8 : Nat.card F ^ 3 = 8 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  set Q := c134Q G₀ L with hQdef
  set Φ := frattiniIn Q with hΦdef
  set Zq := centerOf Q with hZqdef
  set C := c134CQ G₀ L with hCdef
  set U : Subgroup G := ⁅Zq, L⁆ with hUdef
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hZΦ : Zq ≤ Φ := hnatΦ.2.1
  have hZQ : Zq ≤ Q := inf_le_left
  have hUZ : U ≤ Zq := by rw [hZ]; exact le_sup_right
  have hCZ : C ≤ Zq := by rw [hZ]; exact le_sup_left
  have hcom : ∀ z ∈ Zq, ∀ q ∈ Q, z * q = q * z := fun z hz q hq =>
    (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm
  have hcQ : ∀ q ∈ Q, ∀ z ∈ Zq, q * z * q⁻¹ = z := fun q hq z hz => by
    rw [← hcom z hz q hq]; group
  have hQZn : Q ≤ Subgroup.normalizer (Zq : Set G) := fun q hq => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; rw [hcQ q hq z hz]; exact hz
    · intro hz
      have := hcQ q⁻¹ (Q.inv_mem hq) _ hz
      have e : q⁻¹ * (q * z * q⁻¹) * q⁻¹⁻¹ = z := by group
      rw [e] at this
      rw [this]; exact hz
  have hΦnorm : Q ≤ Subgroup.normalizer (Φ : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hΦQ).mp ?_
    have he : Φ.subgroupOf Q = frattini ↥Q :=
      Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
    rw [he]
    infer_instance
  have hCΦ : C ≤ Φ := by
    rw [← hT1]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hΦnorm ha) b).mp hb
    have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Φ.mul_mem h1 (Φ.inv_mem hb)
  have hCL : ∀ l ∈ L, ∀ c ∈ C, l * c * l⁻¹ = c := fun l hl c hc => by
    have := Subgroup.mem_centralizer_iff.mp hc.2 l hl
    rw [this]; group
  have hCn : L ≤ Subgroup.normalizer (C : Set G) := fun l hl => by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc; rw [hCL l hl c hc]; exact hc
    · intro hc
      have := hCL l⁻¹ (L.inv_mem hl) _ hc
      have e : l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ = c := by group
      rw [e] at this
      rw [this]; exact hc
  have hUn : L ≤ Subgroup.normalizer (U : Set G) := hnatU.1
  have hZn : L ≤ Subgroup.normalizer (Zq : Set G) := by
    rw [hZ]
    exact fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hCn hg, hUn hg⟩
  have hZeq : Zq = C ⊔ U := hZ
  have hcenQ : ∀ A : Subgroup G, A ≤ Zq → ∀ K : Subgroup G, K ≤ Q →
      A ≤ Subgroup.normalizer (K : Set G) := fun A hA K hK a ha =>
    (Subgroup.centralizer_le_normalizer (K : Set G)) (Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (hcom a (hA ha) k (hK hk)).symm)
  have hUQ : U ≤ Q := hUZ.trans hZQ
  have hZcard : Nat.card ↥Zq = Nat.card ↥C * Nat.card ↥U := by
    have h1 := Stellmacher.CD.L3YC.card_sup_mul_card_inf (hcenQ C hCZ U hUQ)
    rw [← hZeq, hCU, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hdec : ∀ X : Subgroup G, C ≤ X → X ≤ Zq → X = C ⊔ (X ⊓ U) := by
    intro X hCX hXZ
    apply le_antisymm
    · intro x hx
      have hxZ : x ∈ C ⊔ U := by rw [← hZeq]; exact hXZ hx
      obtain ⟨c, hc, u, hu, rfl⟩ := mem_sup_of_commute
        (fun a ha b hb => hcom a (hCZ ha) b (hUQ hb)) hxZ
      have hu' : u ∈ X := by
        have := X.mul_mem (X.inv_mem (hCX hc)) hx
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ⟨hu', hu⟩)
    · exact sup_le hCX inf_le_left
  have hsecΦ : ∀ D' : Subgroup G, C ≤ D' → D' ≤ Φ → L ≤ Subgroup.normalizer (D' : Set G) →
      ∃ b : ℕ, Nat.card ↥Φ = Nat.card ↥D' * 8 ^ b := by
    intro D' hCD' hD'Φ hD'L
    have hD'Q : D' ≤ Q := hD'Φ.trans hΦQ
    have hX : D' ⊓ Zq ≤ Zq := inf_le_right
    have hCX : C ≤ D' ⊓ Zq := le_inf hCD' hCZ
    have hXdec := hdec (D' ⊓ Zq) hCX hX
    have hXU : L ≤ Subgroup.normalizer (((D' ⊓ Zq) ⊓ U : Subgroup G) : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hD'L hg, hZn hg⟩, hUn hg⟩
    obtain ⟨-, t, -, ht⟩ := Stellmacher.CD.L3YC.card_section_pow hα.1 hnatU (D := (D' ⊓ Zq) ⊓ U) inf_le_right bot_le hXU
    have hD''L : L ≤ Subgroup.normalizer ((D' ⊔ Zq : Subgroup G) : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hD'L hg, hZn hg⟩
    obtain ⟨-, s2, -, hs2⟩ := Stellmacher.CD.L3YC.card_section_pow hα.1 hnatΦ (D := D' ⊔ Zq) (sup_le hD'Φ hZΦ)
      le_sup_right hD''L
    have hiso := Stellmacher.CD.L3YC.card_sup_mul_card_inf (D := D') (K := Zq)
      (hD'Q.trans hQZn)
    have hXcard : Nat.card ↥(D' ⊓ Zq) = Nat.card ↥C * Nat.card ↥((D' ⊓ Zq) ⊓ U) := by
      have h1 := Stellmacher.CD.L3YC.card_sup_mul_card_inf (D := C) (K := (D' ⊓ Zq) ⊓ U)
        (hcenQ C hCZ _ (inf_le_right.trans hUQ))
      have hbot : C ⊓ ((D' ⊓ Zq) ⊓ U) = ⊥ :=
        eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans hCU.le)
      rw [hbot, Subgroup.card_bot, mul_one, ← hXdec] at h1
      exact h1
    rw [h8] at ht hs2
    have hposC : 0 < Nat.card ↥C := Nat.card_pos
    have hposX : 0 < Nat.card ↥((D' ⊓ Zq) ⊓ U) := Nat.card_pos
    have hsup : Nat.card ↥(D' ⊔ Zq) = Nat.card ↥D' * 8 ^ t := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposC hposX)
      have e1 : Nat.card ↥(D' ⊔ Zq) * (Nat.card ↥C * Nat.card ↥((D' ⊓ Zq) ⊓ U)) =
          Nat.card ↥D' * Nat.card ↥Zq := by rw [← hXcard]; exact hiso
      rw [hZcard] at e1
      rw [e1]
      have e2 : Nat.card ↥U = Nat.card ↥((D' ⊓ Zq) ⊓ U) * 8 ^ t := ht
      rw [e2]
      ring
    refine ⟨t + s2, ?_⟩
    rw [hs2, hsup, pow_add]
    ring
  have hΦL : L ≤ Subgroup.normalizer (Φ : Set G) := hnatΦ.1
  have hD₁L : L ≤ Subgroup.normalizer ((D ⊔ Φ : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hDL hg, hΦL hg⟩
  obtain ⟨j, hj⟩ := Stellmacher.CD.L3YC.card_quot_pow_eight h hC4 (D := D ⊔ Φ)
    (sup_le hDQ hΦQ) le_sup_right hD₁L
  have hiso := Stellmacher.CD.L3YC.card_sup_mul_card_inf (D := D) (K := Φ) (hDQ.trans hΦnorm)
  obtain ⟨b, hb⟩ := hsecΦ (D ⊓ Φ) (le_inf hCD hCΦ) inf_le_right
    (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hDL hg, hΦL hg⟩)
  have hpos : 0 < Nat.card ↥(D ⊓ Φ) := Nat.card_pos
  have hsup : Nat.card ↥(D ⊔ Φ) = Nat.card ↥D * 8 ^ b := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hiso, hb]
    ring
  refine ⟨b + j, ?_⟩
  rw [hj, hsup, pow_add]
  ring

section PiForm

theorem card_eq_card_inf_ker_mul_card_map {Λ B : Type} [Group Λ] [Finite Λ] [Group B]
    (π : Λ →* B) (X : Subgroup Λ) :
    Nat.card X = Nat.card ↥(π.ker ⊓ X) * Nat.card (X.map π) := by
  let φ : ↥X →* B := π.comp X.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hφk : φ.ker = π.ker.subgroupOf X := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hφr : φ.range = X.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hφk, hφr] at h1
  have hc : Nat.card ↥(π.ker.subgroupOf X) = Nat.card ↥(π.ker ⊓ X) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype]
  rw [hc] at h1
  exact h1.symm

omit [Finite G] in
theorem card_subgroupOf_of_le' {X L : Subgroup G} (h : X ≤ L) :
    Nat.card ↥(X.subgroupOf L) = Nat.card ↥X := by
  rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr h]

theorem card_c134CQ_eq_four {G₀ R L : Subgroup G} (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) : Nat.card ↥(c134CQ G₀ L) = 4 := by
  obtain ⟨⟨n, F, iF, fF, α, hFc, hα, hE2, -⟩, -⟩ := h
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  obtain ⟨hC4', -⟩ := isE2_card_sq hE2
  rw [hC4']; norm_num

theorem lemmaU_C_central {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) {B : Type} [Group B] (π : ↥L →* B) :
    ((c134CQ G₀ L).subgroupOf L).map π ≤ Subgroup.centralizer (π.range : Set B) ∧
      Nat.card ↥(((c134CQ G₀ L).subgroupOf L).map π) ≤ 4 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hc).2 l.1 l.2
    exact this
  · have h1 : Nat.card ↥(((c134CQ G₀ L).subgroupOf L).map π) ≤
        Nat.card ↥((c134CQ G₀ L).subgroupOf L) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective π _)
    have hCL : c134CQ G₀ L ≤ L :=
      inf_le_left.trans ((MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L))
    rw [card_subgroupOf_of_le' hCL, card_c134CQ_eq_four hq h] at h1
    exact h1

theorem lemmaU_comm_frattini_le {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) {B : Type} [Group B] [Finite B] (π : ↥L →* B) :
    ⁅((c134Q G₀ L).subgroupOf L).map π,
      (frattini ↥(((c134Q G₀ L).subgroupOf L).map π)).map
        (((c134Q G₀ L).subgroupOf L).map π).subtype⁆ ≤
      ((c134CQ G₀ L).subgroupOf L).map π := by
  classical
  have hT1 := comm_frattini_eq_CQ hLG hGL hq h
  set Q := c134Q G₀ L with hQdef
  set Φ := frattiniIn Q with hΦdef
  have hQO : Q ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLG hGL
  have hQL : Q ≤ L := hQO.trans (pCoreOf_le 2 L)
  have hQp : IsPGroup 2 ↥Q := (pCoreOf_isPGroup 2 L).to_le hQO
  have : Fact (IsPGroup 2 ↥Q) := ⟨hQp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set QL : Subgroup ↥L := Q.subgroupOf L with hQL'
  set ΦL : Subgroup ↥L := Φ.subgroupOf L with hΦL'
  set Qb : Subgroup B := QL.map π with hQb
  have hQN : QL ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := hQO hx
    unfold pCoreOf at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hQLp : IsPGroup 2 ↥QL := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)).to_le hQN
  have hQbp : IsPGroup 2 ↥Qb :=
    hQLp.of_surjective (π.subgroupMap QL) (MonoidHom.subgroupMap_surjective π QL)
  have : Fact (IsPGroup 2 ↥Qb) := ⟨hQbp⟩
  have hΦmem : ∀ a b : ↥L, a ∈ QL → b ∈ QL → ⁅a, b⁆ ∈ ΦL := by
    intro a b ha hb
    show ((⁅a, b⁆ : ↥L) : G) ∈ Φ
    let a' : ↥Q := ⟨a.1, ha⟩
    let b' : ↥Q := ⟨b.1, hb⟩
    have hc : ⁅a', b'⁆ ∈ frattini ↥Q := by
      refine commutator_le_frattini_of_isPGroup (p := 2) ?_
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b')
    refine ⟨⁅a', b'⁆, hc, ?_⟩
    simp [a', b', commutatorElement_def]
  have hΦsq : ∀ a : ↥L, a ∈ QL → a ^ 2 ∈ ΦL := by
    intro a ha
    show ((a ^ 2 : ↥L) : G) ∈ Φ
    let a' : ↥Q := ⟨a.1, ha⟩
    refine ⟨a' ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) a', ?_⟩
    simp [a']
  have hfr : frattini ↥Qb ≤ (ΦL.map π).subgroupOf Qb := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | ⟨x, rfl⟩)
    · have hc : _root_.commutator ↥Qb ≤ (ΦL.map π).subgroupOf Qb := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _ w _
        show ((⁅x, w⁆ : ↥Qb) : B) ∈ ΦL.map π
        obtain ⟨a, ha, hax⟩ := x.2
        obtain ⟨b, hb, hbw⟩ := w.2
        refine ⟨⁅a, b⁆, hΦmem a b ha hb, ?_⟩
        simp [commutatorElement_def, hax, hbw]
      exact hc hy
    · show ((x ^ 2 : ↥Qb) : B) ∈ ΦL.map π
      obtain ⟨a, ha, hax⟩ := x.2
      refine ⟨a ^ 2, hΦsq a ha, ?_⟩
      simp [hax]
  have hcomm : ⁅QL, ΦL⁆ ≤ (c134CQ G₀ L).subgroupOf L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf]
    have := Subgroup.commutator_mem_commutator (show (a : G) ∈ Q from ha)
      (show (b : G) ∈ Φ from hb)
    rw [hT1] at this
    simpa [commutatorElement_def] using this
  calc ⁅Qb, (frattini ↥Qb).map Qb.subtype⁆ ≤ ⁅Qb, ΦL.map π⁆ := by
        refine Subgroup.commutator_mono le_rfl ?_
        rintro _ ⟨y, hy, rfl⟩
        exact hfr hy
    _ = (⁅QL, ΦL⁆).map π := (Subgroup.map_commutator _ _ _).symm
    _ ≤ ((c134CQ G₀ L).subgroupOf L).map π := Subgroup.map_mono hcomm

theorem lemmaU_card_section {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) {B : Type} [Group B] [Finite B] (π : ↥L →* B)
    {D' : Subgroup B} (hDn : ∀ l : ↥L, ∀ y ∈ D', π l * y * (π l)⁻¹ ∈ D')
    (hCD : ((c134CQ G₀ L).subgroupOf L).map π ≤ D')
    (hDQ : D' ≤ ((c134Q G₀ L).subgroupOf L).map π) :
    ∃ j : ℕ, Nat.card ↥(((c134Q G₀ L).subgroupOf L).map π) = Nat.card ↥D' * 8 ^ j := by
  classical
  have h' := h
  obtain ⟨⟨n, F, iF, fF, α, hFc, hα, hE2, hZ, hCU, hnatU, hnatΦ, hK, hnatQ⟩, -⟩ := h'
  set Q := c134Q G₀ L with hQdef
  set C := c134CQ G₀ L with hCdef
  have hQO : Q ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLG hGL
  have hQL : Q ≤ L := hQO.trans (pCoreOf_le 2 L)
  have hCQ : C ≤ Q := inf_le_left
  have hCL : C ≤ L := hCQ.trans hQL
  set QL : Subgroup ↥L := Q.subgroupOf L with hQLdef
  let Dg : Subgroup G := (D'.comap π).map L.subtype
  have hmemDg : ∀ x : G, x ∈ Dg ↔ ∃ hx : x ∈ L, π ⟨x, hx⟩ ∈ D' := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, hy, rfl⟩
  have hDgconj : ∀ l ∈ L, ∀ x ∈ Dg, l * x * l⁻¹ ∈ Dg := by
    intro l hl x hx
    obtain ⟨hxL, hxD⟩ := (hmemDg x).mp hx
    refine (hmemDg _).mpr ⟨L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl), ?_⟩
    have : (⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩ : ↥L) =
        ⟨l, hl⟩ * ⟨x, hxL⟩ * ⟨l, hl⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact hDn _ _ hxD
  have hDgn : L ≤ Subgroup.normalizer (Dg : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hDgconj l hl x hx
    · intro hy
      have := hDgconj l⁻¹ (L.inv_mem hl) _ hy
      have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
      rwa [e] at this
  set D₁ : Subgroup G := Q ⊓ Dg with hD₁
  have hCD₁ : C ≤ D₁ := by
    intro c hc
    refine ⟨hCQ hc, (hmemDg c).mpr ⟨hCL hc, hCD ⟨⟨c, hCL hc⟩, ?_, rfl⟩⟩⟩
    exact hc
  have hD₁L : L ≤ Subgroup.normalizer (D₁ : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hnatQ.1 hg, hDgn hg⟩
  obtain ⟨j, hj⟩ := card_section_c134Q hLG hGL hq h hCD₁ inf_le_left hD₁L
  have hD₁L' : D₁ ≤ L := inf_le_left.trans hQL
  set D₁L : Subgroup ↥L := D₁.subgroupOf L with hD₁Ldef
  have h1 := card_eq_card_inf_ker_mul_card_map π QL
  have h2 := card_eq_card_inf_ker_mul_card_map π D₁L
  have hmap : D₁L.map π = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxL, hxD⟩ := (hmemDg x.1).mp hx.2
      exact hxD
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := hDQ hy
      refine ⟨a, ⟨ha, (hmemDg a.1).mpr ⟨a.2, hy⟩⟩, rfl⟩
  have hker : π.ker ⊓ D₁L = π.ker ⊓ QL := by
    apply le_antisymm
    · exact inf_le_inf_left _ (fun x hx => hx.1)
    · intro k hk
      refine ⟨hk.1, hk.2, (hmemDg k.1).mpr ⟨k.2, ?_⟩⟩
      have : π ⟨k.1, k.2⟩ = 1 := hk.1
      rw [this]; exact D'.one_mem
  rw [hmap, hker] at h2
  rw [← card_subgroupOf_of_le' hQL, ← card_subgroupOf_of_le' hD₁L'] at hj
  rw [h1, h2] at hj
  have hpos : 0 < Nat.card ↥(π.ker ⊓ QL) := Nat.card_pos
  refine ⟨j, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hj]
  ring

end PiForm

end Stellmacher.PU.L3YC

end CFSG.Quasithin
