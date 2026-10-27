module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4G0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaColl)

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem conjSubgroup_le_T_of_mem_perfectCore (h : Setting L T P₀ P₁ n w)
    {A P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) {g : Q} (hg : g ∈ perfectCore P) (hAT : A ≤ T)
    (hcomm : ⁅A, perfectCore P⁆ ≤ pCoreOf 2 (perfectCore P)) : conjSubgroup A g ≤ T := by
  intro x hx
  have hxA : g * x * g⁻¹ ∈ A := mem_conjSubgroup_iff.mp hx
  have hc : ⁅(g * x * g⁻¹)⁻¹, g⁻¹⁆ ∈ pCoreOf 2 (perfectCore P) :=
    hcomm (Subgroup.commutator_mem_commutator (A.inv_mem hxA) ((perfectCore P).inv_mem hg))
  have hrad : pCoreOf 2 (perfectCore P) ≤ T := (rad_le_inf h hP).trans inf_le_left
  have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hxeq, show g⁻¹ * (g * x * g⁻¹) * g = (g * x * g⁻¹) * ⁅(g * x * g⁻¹)⁻¹, g⁻¹⁆ by
    rw [commutatorElement_def]; group]
  exact T.mul_mem (hAT hxA) (hrad hc)

private theorem exists_mem_le_T (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) : ∃ A ∈ Ω, A ≤ T := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨h.sylow.le, h.sylow.isPGroup, h.sylow.not_dvd_relIndex⟩
  have hΩ' : CFSG.Quasithin.E1.IsInvColl (⊤ : Subgroup Q) Ω :=
    ⟨fun _ _ => le_top, hΩ.elemAbelian, fun A hA g _ => by
      have h1 := hΩ.conj A hA g⁻¹
      rwa [conjSubgroup_eq_conjSub, inv_inv] at h1⟩
  exact CFSG.LocalAnalysis.WeakClosure81.exists_mem_le_of_isSylowOf hT hΩ' hΩ.nonempty

private theorem le_stabilizer (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω)
    (hall : ∀ A ∈ Ω, A ≤ T → ⁅A, perfectCore P₀⁆ ≤ pCoreOf 2 (perfectCore P₀) ∧
      ⁅A, perfectCore P₁⁆ ≤ pCoreOf 2 (perfectCore P₁)) :
    ∀ g ∈ L, ∀ A ∈ Ω, A ≤ T → conjSubgroup A g ≤ T := by
  let P : Q → Prop := fun g => ∀ A ∈ Ω, A ≤ T → conjSubgroup A g ≤ T
  have h1 : P 1 := fun A _ hAT => by rwa [conjSubgroup_one]
  have hmul : ∀ a b : Q, P a → P b → P (a * b) := by
    intro a b ha hb A hA hAT
    rw [← conjSubgroup_conjSubgroup]
    exact hb (conjSubgroup A a) (hΩ.conj A hA a) (ha A hA hAT)
  have hinv : ∀ a : Q, P a → P (a⁻¹) := by
    intro a ha
    have hpow : ∀ m : ℕ, P (a ^ m) := by
      intro m
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ]; exact hmul _ _ ih ha
    have hord : a * a ^ (orderOf a - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
    rw [← (inv_eq_of_mul_eq_one_right hord).symm]
    exact hpow _
  have hgen : ∀ g ∈ (perfectCore P₀ : Set Q) ∪ (perfectCore P₁ : Set Q), P g := by
    intro g hg A hA hAT
    rcases hg with hg | hg
    · exact conjSubgroup_le_T_of_mem_perfectCore h (Or.inl rfl) hg hAT (hall A hA hAT).1
    · exact conjSubgroup_le_T_of_mem_perfectCore h (Or.inr rfl) hg hAT (hall A hA hAT).2
  have hclosure : ∀ g ∈ Subgroup.closure ((perfectCore P₀ : Set Q) ∪ (perfectCore P₁ : Set Q)),
      P g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact h1
    | mul a b _ _ iha ihb => exact hmul a b iha ihb
    | inv a _ iha => exact hinv a iha
  intro g hg
  rw [← perfectCore_sup_perfectCore h, Subgroup.sup_eq_closure] at hg
  exact hclosure g hg

private theorem le_normalizer_iSup_conjSubgroup {A D : Subgroup Q}
    (hD : D = ⨆ g : L, conjSubgroup A (g : Q)) : L ≤ Subgroup.normalizer (D : Set Q) := by
  have hmap : ∀ x : Q, conjSubgroup D x = ⨆ g : L, conjSubgroup A ((g : Q) * x) := by
    intro x
    rw [hD, conjSubgroup, Subgroup.map_iSup]
    exact iSup_congr fun g => conjSubgroup_conjSubgroup A (g : Q) x
  intro x hx
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hre : (⨆ g : L, conjSubgroup A ((g : Q) * x)) = ⨆ g : L, conjSubgroup A (g : Q) := by
    refine le_antisymm (iSup_le fun g => ?_) (iSup_le fun g => ?_)
    · exact le_iSup_of_le (g * ⟨x, hx⟩) le_rfl
    · have hgx : ((↑(g * ⟨x⁻¹, L.inv_mem hx⟩) : Q) * x) = (g : Q) := by
        change (g : Q) * x⁻¹ * x = (g : Q)
        group
      exact le_iSup_of_le (g * ⟨x⁻¹, L.inv_mem hx⟩) (le_of_eq (by rw [hgx]))
  exact (hmap x).trans (hre.trans hD.symm)

private theorem exists_supConj_le_T {Ω : Set (Subgroup Q)} {A : Subgroup Q}
    (hL : ∀ g ∈ L, ∀ B ∈ Ω, B ≤ T → conjSubgroup B g ≤ T)
    (hAΩ : A ∈ Ω) (hAT : A ≤ T) :
    ∃ D : Subgroup Q, A ≤ D ∧ D ≤ T ∧ L ≤ Subgroup.normalizer (D : Set Q) := by
  refine ⟨⨆ g : L, conjSubgroup A (g : Q), ?_, ?_, ?_⟩
  · have hle : conjSubgroup A ((1 : L) : Q) ≤ ⨆ g : L, conjSubgroup A (g : Q) :=
      le_iSup (fun g : L => conjSubgroup A (g : Q)) 1
    rwa [Subgroup.coe_one, conjSubgroup_one] at hle
  · exact iSup_le fun g => hL (g : Q) g.2 A hAΩ hAT
  · exact le_normalizer_iSup_conjSubgroup rfl

private theorem normal_subgroupOf_inf_of_le_normalizer {D : Subgroup Q}
    (hN : L ≤ Subgroup.normalizer (D : Set Q)) : ((D ⊓ L).subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  change (g : Q) * (n : Q) * (g : Q)⁻¹ ∈ D ⊓ L
  rw [Subgroup.mem_inf]
  constructor
  · have hg : (g : Q) ∈ Subgroup.normalizer (D : Set Q) := hN g.2
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg (n : Q)).mp hn.1
  · exact L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)

private theorem inf_eq_bot_or_eq_of_le_normalizer (h : Setting L T P₀ P₁ n w) {D : Subgroup Q}
    (hN : L ≤ Subgroup.normalizer (D : Set Q)) : D ⊓ L = ⊥ ∨ D ⊓ L = L := by
  haveI := h.simple
  haveI := normal_subgroupOf_inf_of_le_normalizer hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D ⊓ L).subgroupOf L) with hb | ht
  · left
    have hd : Disjoint (D ⊓ L) L := Subgroup.subgroupOf_eq_bot.mp hb
    rw [disjoint_iff_inf_le] at hd
    rw [inf_assoc, inf_idem] at hd
    exact eq_bot_iff.mpr hd
  · right
    exact le_antisymm inf_le_right (Subgroup.subgroupOf_eq_top.mp ht)

private theorem false_of_le_isPGroup (h : Setting L T P₀ P₁ n w) {D : Subgroup Q}
    (hDT : D ≤ T) (hLD : L ≤ D) : False := by
  have hLT : L ≤ T := hLD.trans hDT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 ↥L := IsPGroup.to_le h.sylow.isPGroup hLT
  haveI : Nontrivial ↥L := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨a, 1, fun ha => hab (by rw [ha]; simp)⟩
  have hlt := IsPGroup.bot_lt_center hL2
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hc | hc
  · rw [hc] at hlt
    exact lt_irrefl ⊥ hlt
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    exact hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp hc) a b)

private theorem false_of_inf_eq_bot (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) {A D : Subgroup Q} (hAΩ : A ∈ Ω) (hAD : A ≤ D)
    (hN : L ≤ Subgroup.normalizer (D : Set Q)) (hDinf : D ⊓ L = ⊥) : False := by
  haveI := h.normal
  have hDcomm : ⁅D, L⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro d hd l hl
    have hmem : l ∈ Subgroup.normalizer (D : Set Q) := hN hl
    rw [Subgroup.mem_normalizer_iff] at hmem
    have h1 : l * d⁻¹ * l⁻¹ ∈ D := (hmem d⁻¹).mp (D.inv_mem hd)
    have h2 : d * (l * d⁻¹ * l⁻¹) ∈ D := D.mul_mem hd h1
    rwa [show d * (l * d⁻¹ * l⁻¹) = ⁅d, l⁆ by rw [commutatorElement_def]; group] at h2
  have hcomm : ⁅D, L⁆ ≤ D ⊓ L := le_inf hDcomm (Subgroup.commutator_le_right D L)
  rw [hDinf] at hcomm
  have hDc : D ≤ Subgroup.centralizer (L : Set Q) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ⁅d, l⁆ = 1 := by
      have hmem := hcomm (Subgroup.commutator_mem_commutator hd hl)
      rwa [Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hDb : D ≤ ⊥ := by
    rw [← h.centralizer_eq]
    exact hDc
  exact hΩ.ne_bot A hAΩ (le_bot_iff.mp (hAD.trans hDb))

theorem false_of_forall_commutator_le (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω)
    (hall : ∀ A ∈ Ω, A ≤ T → ⁅A, perfectCore P₀⁆ ≤ pCoreOf 2 (perfectCore P₀) ∧
      ⁅A, perfectCore P₁⁆ ≤ pCoreOf 2 (perfectCore P₁)) : False := by
  obtain ⟨A, hAΩ, hAT⟩ := exists_mem_le_T h hΩ
  obtain ⟨D, hAD, hDT, hN⟩ := exists_supConj_le_T (le_stabilizer h hΩ hall) hAΩ hAT
  rcases inf_eq_bot_or_eq_of_le_normalizer h hN with hbot | htop
  · exact false_of_inf_eq_bot h hΩ hAΩ hAD hN hbot
  · exact false_of_le_isPGroup h hDT (htop ▸ inf_le_left)

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
