module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4G0
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalPerfect
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalPSLRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InCalEi ECaseII tA)
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem map_P₀_eq_of_mem_centralizer {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {c : Q} (hcT : c ∈ T) (hcC : c ∈ Subgroup.centralizer (A : Set Q)) :
    P₀.map (MulAut.conj c).toMonoidHom = P₀ :=
  hY c hcT fun a ha => (Subgroup.mem_centralizer_iff.mp hcC a ha).symm

private theorem map_P₁_eq_of_mem_centralizer (h : Setting L T P₀ P₁ n w) {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {c : Q} (hcT : c ∈ T) (hcC : c ∈ Subgroup.centralizer (A : Set Q)) :
    P₁.map (MulAut.conj c).toMonoidHom = P₁ := by
  rcases map_conj_eq_or h hcT with ⟨-, h1⟩ | ⟨h0, -⟩
  · exact h1
  · exact absurd ((map_P₀_eq_of_mem_centralizer hY hcT hcC).symm.trans h0) h.par_ne

private theorem map_perfectCore_eq_of_mem_centralizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) {c : Q} (hcT : c ∈ T)
    (hcC : c ∈ Subgroup.centralizer (A : Set Q)) :
    (perfectCore P).map (MulAut.conj c).toMonoidHom = perfectCore P := by
  rw [map_perfectCore]
  rcases hP with rfl | rfl
  · rw [map_P₀_eq_of_mem_centralizer hY hcT hcC]
  · rw [map_P₁_eq_of_mem_centralizer h hY hcT hcC]

private theorem centralizer_inf_le_normalizer_perfectCore (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    T ⊓ Subgroup.centralizer (A : Set Q) ≤ Subgroup.normalizer (perfectCore P : Set Q) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_perfectCore_eq_of_mem_centralizer h hY hP hc.1 hc.2

private theorem normal_perfectCore_sup_centralizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    ((perfectCore P).subgroupOf
      (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer (centralizer_inf_le_normalizer_perfectCore h hY hP)

private theorem exists_pow_mem_perfectCore_sup_centralizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) {x : Q}
    (hx : x ∈ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ perfectCore P := by
  have hT2 : IsPGroup 2 T := h.sylow.2.1
  have hCnorm := centralizer_inf_le_normalizer_perfectCore h hY hP
  have hx' : x ∈ ((perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :
      Subgroup Q) : Set Q) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (perfectCore P)
    (T ⊓ Subgroup.centralizer (A : Set Q)) hCnorm] at hx'
  obtain ⟨j, hj, c, hc, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hT2) ⟨c, hc.1⟩
  have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j', hj', hpow⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq hj (hCnorm hc) (2 ^ k)
  exact ⟨k, by rw [hpow, hk', mul_one]; exact hj'⟩

private theorem le_centralizer_inf_of_isElemAbelian {A : Subgroup Q} (hAT : A ≤ T)
    (hA2 : IsElemAbelian 2 A) : A ≤ T ⊓ Subgroup.centralizer (A : Set Q) :=
  le_inf hAT fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hA2.comm hb ha

private theorem pCoreOf_inf_perfectCore_le (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    pCoreOf 2 (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) ⊓ perfectCore P ≤
      pCoreOf 2 (perfectCore P) := by
  have hCnorm := centralizer_inf_le_normalizer_perfectCore h hY hP
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
  · intro j hj
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj j).injective]
    have h1 : Subgroup.map (↑(MulAut.conj j)) (pCoreOf 2 (perfectCore P ⊔
        (T ⊓ Subgroup.centralizer (A : Set Q)))) =
        pCoreOf 2 (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hj)
    have h2 : Subgroup.map (↑(MulAut.conj j)) (perfectCore P) = perfectCore P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hj)
    rw [h1, h2]
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left

private theorem not_le_pCoreOf_perfectCore_sup_centralizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) (hAT : A ≤ T) (hA2 : IsElemAbelian 2 A)
    (hcomm : ¬ ⁅A, perfectCore P⁆ ≤ pCoreOf 2 (perfectCore P)) :
    ¬ A ≤ pCoreOf 2 (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) := by
  intro hA
  apply hcomm
  have hAC := le_centralizer_inf_of_isElemAbelian hAT hA2
  have h1 : ⁅A, perfectCore P⁆ ≤
      pCoreOf 2 (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) := by
    refine le_trans (Subgroup.commutator_mono hA le_rfl)
      (CFSG.Quasithin.E1.commutator_le_of_le_normalizer ?_)
    exact (le_sup_left : perfectCore P ≤ _).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have h2 : ⁅A, perfectCore P⁆ ≤ perfectCore P := by
    rw [Subgroup.commutator_comm]
    exact CFSG.Quasithin.E1.commutator_le_of_le_normalizer
      (hAC.trans (centralizer_inf_le_normalizer_perfectCore h hY hP))
  exact le_trans (le_inf h1 h2) (pCoreOf_inf_perfectCore_le h hY hP)

private theorem le_perfectCore_inf_L (h : Setting L T P₀ P₁ n w) {P : Subgroup Q}
    (hP : P = P₀ ∨ P = P₁) : T ⊓ L ≤ perfectCore P := by
  rcases hP with h | h
  · subst P
    exact h.concl₀.S_le
  · subst P
    exact h.concl₁.S_le

private theorem le_sup_inf_centralizer_of_le_sylow (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) {P' : Subgroup Q}
    (hP'K : P' ≤ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)))
    (hP'2 : IsPGroup 2 P')
    (hUCP' : T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤ P') :
    P' ≤ T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) := by
  have hCnorm := centralizer_inf_le_normalizer_perfectCore h hY hP
  have hUJ := le_perfectCore_inf_L h hP
  have hUsylL : IsSylowTwoOf (T ⊓ L) L := by
    rcases hP with h | h
    · subst P
      exact h.concl₀.S_syl
    · subst P
      exact h.concl₁.S_syl
  have hPL : P ≤ L := by
    rcases hP with h | h
    · subst P
      exact h.par₀.1
    · subst P
      exact h.par₁.1
  have hUsylJ : IsSylowTwoOf (T ⊓ L) (perfectCore P) :=
    CFSG.Quasithin.A4.isSylowTwoOf_mono hUsylL hUJ ((perfectCore_le P).trans hPL)
  have hUmax := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hUsylJ).2.2
  intro p hp'
  have hp'K' : p ∈ ((perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :
      Subgroup Q) : Set Q) := hP'K hp'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (perfectCore P)
    (T ⊓ Subgroup.centralizer (A : Set Q)) hCnorm] at hp'K'
  obtain ⟨j, hj, c, hc, hjc⟩ := hp'K'
  have hcP : c ∈ P' := hUCP' (Subgroup.mem_sup_right hc)
  have hjP : j ∈ P' := by
    have hjc' : j = p * c⁻¹ := by rw [← hjc]; group
    rw [hjc']
    exact P'.mul_mem hp' (P'.inv_mem hcP)
  have hP'J : P' ⊓ perfectCore P = T ⊓ L := by
    have hULP' : T ⊓ L ≤ P' :=
      (le_sup_left : T ⊓ L ≤ T ⊓ L ⊔ T ⊓ Subgroup.centralizer (A : Set Q)).trans hUCP'
    refine le_antisymm (hUmax (P' ⊓ perfectCore P) inf_le_right hP'2.to_inf_left
      (le_inf hULP' hUJ)) (le_inf hULP' hUJ)
  have hjU : j ∈ T ⊓ L := hP'J ▸ ⟨hjP, hj⟩
  have hmem : j * c ∈ T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :=
    Subgroup.mul_mem_sup hjU hc
  have hjc'' : j * c = p := hjc
  rw [hjc''] at hmem
  exact hmem

private theorem isSylowTwoOf_perfectCore_sup_centralizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      (T ⊓ (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))))
      (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) := by
  have hT2 : IsPGroup 2 T := h.sylow.2.1
  have hUJ := le_perfectCore_inf_L h hP
  have hUC2 : IsPGroup 2 ↥(T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
    hT2.to_le (sup_le inf_le_left inf_le_left)
  have hUCK : T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤
      perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :=
    sup_le (hUJ.trans (le_sup_left : perfectCore P ≤ perfectCore P ⊔ _))
      (le_sup_right : T ⊓ Subgroup.centralizer (A : Set Q) ≤ _)
  have hUCmax : ∀ P' : Subgroup Q,
      P' ≤ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) → IsPGroup 2 P' →
      T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤ P' → P' ≤
        T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :=
    fun _ hP'K hP'2 hUCP' => le_sup_inf_centralizer_of_le_sylow h hY hP hP'K hP'2 hUCP'
  have hSylUC : IsSylowTwoOf
      (T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)))
      (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
    (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal).mpr ⟨hUCK, hUC2, hUCmax⟩
  have hle : T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤
      T ⊓ (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
    le_inf (sup_le (inf_le_left : T ⊓ L ≤ T)
      (inf_le_left : T ⊓ Subgroup.centralizer (A : Set Q) ≤ T)) hUCK
  have heq : T ⊓ (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) =
      T ⊓ L ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :=
    le_antisymm
      ((CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hSylUC).2.2
        (T ⊓ (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))))
        inf_le_right (hT2.to_le inf_le_left) hle) hle
  rw [heq]
  exact hSylUC

private theorem pCoreOf_perfectCore_eq_inf_of_le_normalizer (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁)
    (hKnorm : perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)) :
    pCoreOf 2 (perfectCore P) = T ⊓ L := by
  have hUJ : T ⊓ L ≤ perfectCore P := by
    rcases hP with h | h
    · subst P
      exact h.concl₀.S_le
    · subst P
      exact h.concl₁.S_le
  have hU2 : IsPGroup 2 ↥(T ⊓ L) := by
    rcases hP with h | h
    · subst P
      exact h.concl₀.S_syl.2.1
    · subst P
      exact h.concl₁.S_syl.2.1
  have hUnorm : ((T ⊓ L).subgroupOf (perfectCore P)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUJ]
    exact (le_sup_left : perfectCore P ≤ _).trans hKnorm
  exact le_antisymm (rad_le_inf h hP) (CFSG.LieType.BorelTits.le_pCoreOf 2 hUJ hUnorm hU2)

private theorem false_of_pCoreOf_eq_inf (h : Setting L T P₀ P₁ n w) {P : Subgroup Q}
    (hP : P = P₀ ∨ P = P₁) (hR : pCoreOf 2 (perfectCore P) = T ⊓ L) : False := by
  rcases hP with h | h
  · subst P
    have hUeq : T ⊓ L = pCoreOf 2 (perfectCore P₀) ⊔
        sp4Q₁ L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) := h.concl₀.S_eq
    rw [sp4Q₁_zero h] at hUeq
    have hRR : pCoreOf 2 (perfectCore P₀) =
        pCoreOf 2 (perfectCore P₀) ⊔ pCoreOf 2 (perfectCore P₁) := hR ▸ hUeq
    have hle : pCoreOf 2 (perfectCore P₁) ≤ pCoreOf 2 (perfectCore P₀) := hRR ▸ le_sup_right
    have hidx := h.concl₀.index_Q₁
    rw [sp4Q₁_zero h] at hidx
    rw [inf_eq_right.mpr hle, Subgroup.relIndex_self] at hidx
    have hn0 : n ≠ 0 := by
      have h0 : 0 < n := lt_of_lt_of_le (by norm_num) h.two_le
      exact Nat.pos_iff_ne_zero.mp h0
    exact absurd hidx.symm (Nat.one_lt_pow hn0 (by norm_num : 1 < 2)).ne'
  · subst P
    have hUeq : T ⊓ L = pCoreOf 2 (perfectCore P₁) ⊔
        sp4Q₁ L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) := h.concl₁.S_eq
    rw [sp4Q₁_one h] at hUeq
    have hRR : pCoreOf 2 (perfectCore P₁) =
        pCoreOf 2 (perfectCore P₁) ⊔ pCoreOf 2 (perfectCore P₀) := hR ▸ hUeq
    have hle : pCoreOf 2 (perfectCore P₀) ≤ pCoreOf 2 (perfectCore P₁) := hRR ▸ le_sup_right
    have hidx := h.concl₁.index_Q₁
    rw [sp4Q₁_one h] at hidx
    rw [inf_eq_right.mpr hle, Subgroup.relIndex_self] at hidx
    have hn0 : n ≠ 0 := by
      have h0 : 0 < n := lt_of_lt_of_le (by norm_num) h.two_le
      exact Nat.pos_iff_ne_zero.mp h0
    exact absurd hidx.symm (Nat.one_lt_pow hn0 (by norm_num : 1 < 2)).ne'

private theorem not_le_normalizer_inf_of_setting (h : Setting L T P₀ P₁ n w)
    {A : Subgroup Q}
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁) :
    ¬ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
  fun hKnorm =>
    false_of_pCoreOf_eq_inf h hP (pCoreOf_perfectCore_eq_inf_of_le_normalizer h hY hP hKnorm)

theorem exists_inCalEi_of_not_commutator_le (h : Setting L T P₀ P₁ n w) {A : Subgroup Q}
    (hAT : A ≤ T) (hA2 : IsElemAbelian 2 A)
    (hY : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀)
    {P : Subgroup Q} (hP : P = P₀ ∨ P = P₁)
    (hcomm : ¬ ⁅A, perfectCore P⁆ ≤ pCoreOf 2 (perfectCore P)) :
    ∃ K : Subgroup Q, InCalEi n T A K ∧ ¬ K ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  have hCn := normal_perfectCore_sup_centralizer h hY hP
  have hAC := le_centralizer_inf_of_isElemAbelian hAT hA2
  have hAK : A ≤ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)) :=
    hAC.trans le_sup_right
  have hK2 : ∀ x ∈ perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)),
      ∃ k : ℕ, x ^ 2 ^ k ∈ perfectCore P :=
    fun _ hx => exists_pow_mem_perfectCore_sup_centralizer h hY hP hx
  have hAJ : ∃ a ∈ A, ∃ x ∈ perfectCore P, ⁅a, x⁆ ∉ pCoreOf 2 (perfectCore P) := by
    by_contra hc
    refine hcomm (Subgroup.commutator_le.mpr ?_)
    intro a ha x hx
    by_contra h
    exact hc ⟨a, ha, x, hx, h⟩
  have hECaseII : ECaseII T A (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
    eCaseII_of_normal_perfect le_sup_left hCn (perfectCore_perfect P)
      (isSimpleGroup_modO2 h hP) hK2 hAK hAJ
  have hSyl := isSylowTwoOf_perfectCore_sup_centralizer h hY hP
  have htA : tA T A ≤ T ⊓ (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) := by
    rw [tA_eq h A]
    exact le_inf inf_le_left (le_sup_right : T ⊓ Subgroup.centralizer (A : Set Q) ≤
      perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)))
  have hnot : ¬ A ≤ pCoreOf 2 (perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q))) :=
    not_le_pCoreOf_perfectCore_sup_centralizer h hY hP hAT hA2 hcomm
  have hmQuot := mQuot_pCoreOf_le_of_normal_psl le_sup_left hCn
    (isSimpleGroup_modO2 h hP) (nonabelian_modO2 h hP) (isPSL_modO2 h hP) hK2 hAK hA2
  refine ⟨perfectCore P ⊔ (T ⊓ Subgroup.centralizer (A : Set Q)), ?_, ?_⟩
  · refine ⟨⟨htA, CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl, hnot, Or.inr hECaseII⟩, hmQuot⟩
  · exact not_le_normalizer_inf_of_setting h hY hP

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
