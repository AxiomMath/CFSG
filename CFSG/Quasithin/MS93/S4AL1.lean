module

public import CFSG.Quasithin.MS93.S46Ker
public import CFSG.Quasithin.MS93.ML3AutBridge
public import CFSG.Quasithin.MS93.S4A431C

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Kind

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem exists_dual_of_isC1 (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ)
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) :
    ∃ dual : Bool, IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)
      (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ψ dual 1 := by
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  obtain ⟨F', _, _, ψ', hcard', hsurj, hnat, -, -, -, -⟩ := isC1_normal h hfull hb hα hc
  have hF'n : Nat.card F' = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard', hn]
  have : CharP F' 2 := FFC.charP_two_of_card_pow hF'n
  refine isSumOfNaturalModulesVia_of_surj hψs hsurj ?_ hnat
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have h1 : toSL3 ψ x = 1 := by
    simp [toSL3, hx]
  have hxQ := (S46.toSL3_eq_one_iff_mem_qv h hφ hα hψ x).mp h1
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)
  have hfix : ∀ v : Fin 3 → F', ((toSL3 ψ' x : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ v = v := by
    intro v
    obtain ⟨p, rfl⟩ := secVec_surjective hnat v
    have hsp : (x : (puAmalgam h.le).Universal) * p * (x : (puAmalgam h.le).Universal)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (hPn x.2) _).mp p.2
    rw [← secVec_conj hnat x p ⟨_, hsp⟩ rfl]
    have hK : (⟨_, hsp⟩ * p⁻¹ : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α)) ∈ (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α).subgroupOf _ := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_sup_left ?_
      have : ((⟨_, hsp⟩ * p⁻¹ : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
          ZM (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) =
          ⁅(p : (puAmalgam h.le).Universal), (x : (puAmalgam h.le).Universal)⁆⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (hPV p.2) hxQ)
    have h0 := (secVec_eq_zero_iff hnat _).mpr (Subgroup.mem_subgroupOf.mp hK)
    rw [secVec_mul, secVec_inv, add_neg_eq_zero] at h0
    exact h0
  have h2 : toSL3 ψ' x = 1 := eq_one_of_mulVec_eq_self hfix
  have := congrArg (specialLinearGroupEquivStatedSL 3 F') h2
  simpa [toSL3] using this

end Kind

section Lin

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_dloc_dichotomy {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {A B' : Subgroup (puAmalgam h.le).Universal} (hAs : A ≤ stab (puAmalgam h.le) α)
    (hAn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal))
    (hB'A : B' ≤ A)
    (hirr : ∀ N : Subgroup (puAmalgam h.le).Universal,
      stab (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) →
      B' ≤ N → N ≤ A → N = B' ∨ N = A)
    (hB'Q : ⁅B', Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α)
    (hAQ : ⁅A, Qv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α ⊔ Dloc h.le L α)
    (hAL : ⁅A, ⁅Qv (puAmalgam h.le) α, Ltil h.le L α⁆⁆ ≤ Dloc h.le L α)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ Qv (puAmalgam h.le) α) :
    (∀ a ∈ A, ⁅a, y⁆ ∈ Dloc h.le L α) ∨ (∀ a ∈ A, ⁅a, y⁆ ∈ Dloc h.le L α → a ∈ B') := by
  have h20 := h.hyp20
  have hDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hQs : Qv (puAmalgam h.le) α ≤ stab _ α := qv_le_stab _ α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hLs := ltil_le_stab h α
  have hEQ : ⁅ZM (puAmalgam h.le) α ⊔ Dloc h.le L α, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α := by
    refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (zm_le_centralizer_qv _ h20 hα)]
      exact bot_le
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hDn)
    · exact ((zm_le_qv_self _ hα h.critDist_pos).trans hQs).trans hDn
    · exact Subgroup.le_normalizer
  let N : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {a | a ∈ A ∧ ⁅a, y⁆ ∈ Dloc h.le L α}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hDn (hAs ha)) _).mp hb') ha'
      one_mem' := ⟨A.one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨A.inv_mem ha, ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hDn (hAs (A.inv_mem ha))) _).mp
          (Subgroup.inv_mem _ ha') }
  have hnorm : ∀ {S : Subgroup (puAmalgam h.le).Universal},
      (∀ s ∈ S, ∀ a ∈ N, s * a * s⁻¹ ∈ N) →
        S ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
    intro S hS s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hS s hs a
    · intro ha
      have := hS s⁻¹ (S.inv_mem hs) _ ha
      simpa [mul_assoc] using this
  have hNQ : Qv (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
    refine hnorm fun q hq a ha => ⟨(Subgroup.mem_normalizer_iff.mp (hAn (hQs hq)) a).mp ha.1, ?_⟩
    have he : ⁅a⁻¹, q⁆ ∈ ZM (puAmalgam h.le) α ⊔ Dloc h.le L α :=
      hAQ (Subgroup.commutator_mem_commutator (A.inv_mem ha.1) hq)
    have e1 : q * a * q⁻¹ = a * ⁅a⁻¹, q⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅a * ⁅a⁻¹, q⁆, y⁆ = a * ⁅⁅a⁻¹, q⁆, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1, e2]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hDn (hAs ha.1)) _).mp
      (hEQ (Subgroup.commutator_mem_commutator he hy))) ha.2
  have hNL : Ltil h.le L α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
    refine hnorm fun l hl a ha => ⟨(Subgroup.mem_normalizer_iff.mp (hAn (hLs hl)) a).mp ha.1, ?_⟩
    have hc : ⁅y⁻¹, l⁻¹⁆ ∈ ⁅Qv (puAmalgam h.le) α, Ltil h.le L α⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hy) (Subgroup.inv_mem _ hl)
    have e1 : ⁅l * a * l⁻¹, y⁆ = l * (⁅a, y⁆ * (y * ⁅a, ⁅y⁻¹, l⁻¹⁆⁆ * y⁻¹)) * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    refine (Subgroup.mem_normalizer_iff.mp (hDn (hLs hl)) _).mp (Subgroup.mul_mem _ ha.2 ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hDn (hQs hy)) _).mp
      (hAL (Subgroup.commutator_mem_commutator ha.1 hc))
  have hNn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set _) := by
    rw [stab_eq_ltil_sup_qv h hfull hα]
    exact sup_le hNL hNQ
  have hB'N : B' ≤ N := fun b hb => ⟨hB'A hb, hB'Q (Subgroup.commutator_mem_commutator hb hy)⟩
  have hNA : N ≤ A := fun a ha => ha.1
  rcases hirr N hNn hB'N hNA with hN | hN
  · right
    intro a ha hay
    have : a ∈ N := ⟨ha, hay⟩
    rwa [hN] at this
  · left
    intro a ha
    have : a ∈ N := hN ▸ ha
    exact this.2

end Lin

end CFSG.Quasithin.MS93.S4A
