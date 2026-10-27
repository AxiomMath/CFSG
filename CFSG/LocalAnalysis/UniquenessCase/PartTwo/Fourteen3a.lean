module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section ThreeMembers

variable {M L₁ L₂ L₃ : Subgroup G}

theorem coe_sup_sup_eq_mul (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) :
    ((L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) : Set G) = (L₁ : Set G) * L₂ * L₃ := by
  have n12 : L₂ ≤ normalizer (L₁ : Set G) := calC_le_normalizer_of_ne h₁ h₂ h12
  have n13 : L₃ ≤ normalizer (L₁ : Set G) := calC_le_normalizer_of_ne h₁ h₃ h13
  have n23 : L₃ ≤ normalizer (L₂ : Set G) := calC_le_normalizer_of_ne h₂ h₃ h23
  have n3 : L₃ ≤ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
    intro g hg
    rw [UC6S846.mem_normalizer_iff_map_conj, Subgroup.map_sup,
      UC6S846.mem_normalizer_iff_map_conj.1 (n13 hg),
      UC6S846.mem_normalizer_iff_map_conj.1 (n23 hg)]
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (L₁ ⊔ L₂) L₃ n3,
    Subgroup.coe_mul_of_right_le_normalizer_left L₁ L₂ n12]

theorem isSubnormal_sup_sup (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M) :
    IsSubnormal (L₁ ⊔ L₂ ⊔ L₃) M := by
  have hle₁ : L₁ ≤ M := A3.subnormal_le h₁.1
  have hle₂ : L₂ ≤ M := A3.subnormal_le h₂.1
  have hle₃ : L₃ ≤ M := A3.subnormal_le h₃.1
  have hle : L₁ ⊔ L₂ ⊔ L₃ ≤ M := sup_le (sup_le hle₁ hle₂) hle₃
  rw [CFSG.Open.IsSubnormal.iff_subgroupOf hle,
    Subgroup.subgroupOf_sup (sup_le hle₁ hle₂) hle₃,
    Subgroup.subgroupOf_sup hle₁ hle₂]
  have hs₁ : (L₁.subgroupOf M).IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf h₁.1
  have hs₂ : (L₂.subgroupOf M).IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf h₂.1
  have hs₃ : (L₃.subgroupOf M).IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf h₃.1
  exact CFSG.GroupTheory.isSubnormal_sup (CFSG.GroupTheory.isSubnormal_sup hs₁ hs₂) hs₃

theorem commutator_sup_sup (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M) :
    ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ = L₁ ⊔ L₂ ⊔ L₃ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · apply sup_le (sup_le _ _) _
    · calc L₁ ≤ ⁅L₁, L₁⁆ := h₁.2.1.ge
        _ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ :=
          Subgroup.commutator_mono (le_sup_left.trans le_sup_left)
            (le_sup_left.trans le_sup_left)
    · calc L₂ ≤ ⁅L₂, L₂⁆ := h₂.2.1.ge
        _ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ :=
          Subgroup.commutator_mono (le_sup_right.trans le_sup_left)
            (le_sup_right.trans le_sup_left)
    · calc L₃ ≤ ⁅L₃, L₃⁆ := h₃.2.1.ge
        _ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ :=
          Subgroup.commutator_mono le_sup_right le_sup_right

theorem isElemAbelian_of_card_prime {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Y} [Finite E] (hE : Nat.card E = p) : IsElemAbelian p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic E := isCyclic_of_prime_card (p := p) hE
  refine ⟨inferInstance, fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : E) ^ p = 1 := by
    have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
    rwa [hE] at this
  simpa using congrArg Subtype.val hx'

theorem two_lt_pRank_sup_sup (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) (s₁ : IsL3 (Bar2 L₁) 1)
    (s₂ : IsL3 (Bar2 L₂) 1) (s₃ : IsL3 (Bar2 L₃) 1) :
    2 < Open.pRank 3 (L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L : Subgroup G := L₁ ⊔ L₂ ⊔ L₃ with hL
  let Lfam : Fin 3 → Subgroup G :=
    fun i => if (i : ℕ) = 0 then L₁ else if (i : ℕ) = 1 then L₂ else L₃
  have hshape : ∀ i, IsL3 (Bar2 (Lfam i)) 1 := by
    intro i
    fin_cases i
    · simpa [Lfam] using s₁
    · simpa [Lfam] using s₂
    · simpa [Lfam] using s₃
  have hLfam_le : ∀ i, Lfam i ≤ L := by
    intro i
    fin_cases i
    · rw [hL]; exact le_sup_left.trans le_sup_left
    · rw [hL]; exact le_sup_right.trans le_sup_left
    · rw [hL]; exact le_sup_right
  have hLfam_norm : ∀ i, L ≤ normalizer (Lfam i : Set G) := by
    intro i
    fin_cases i
    · rw [hL]
      exact sup_le (sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne h₁ h₂ h12))
        (calC_le_normalizer_of_ne h₁ h₃ h13)
    · rw [hL]
      exact sup_le (sup_le (calC_le_normalizer_of_ne h₂ h₁ h12.symm) Subgroup.le_normalizer)
        (calC_le_normalizer_of_ne h₂ h₃ h23)
    · rw [hL]
      exact sup_le (sup_le (calC_le_normalizer_of_ne h₃ h₁ h13.symm)
        (calC_le_normalizer_of_ne h₃ h₂ h23.symm)) Subgroup.le_normalizer
  have hcal : ∀ i, Lfam i ∈ calC L := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · exact A3.subnormal_of_normal (hLfam_le i)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hLfam_le i)).2 (hLfam_norm i))
    · fin_cases i
      · simpa [Lfam] using h₁.2.1
      · simpa [Lfam] using h₂.2.1
      · simpa [Lfam] using h₃.2.1
    · fin_cases i
      · simpa [Lfam] using h₁.2.2
      · simpa [Lfam] using h₂.2.2
      · simpa [Lfam] using h₃.2.2
  have hex : ∀ i, ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Lfam i) ∧ Nat.card P = 3 := by
    intro i
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Lfam i)
    exact ⟨P, hP, card_sylow_three_of_isL3_bar2 (hshape i) hP⟩
  choose P hPsyl hPcard using hex
  have hPle : ∀ i, P i ≤ Lfam i := fun i => (hPsyl i).le
  have hPLE : ∀ i, P i ≤ L := fun i => (hPle i).trans (hLfam_le i)
  let A : Fin 3 → Subgroup ↥L := fun i => (Lfam i).subgroupOf L
  let E : Fin 3 → Subgroup ↥L := fun i => (P i).subgroupOf L
  have hEA : ∀ i, E i ≤ A i := by
    intro i
    exact Subgroup.subgroupOf_mono L (hPle i)
  have hEc : ∀ i, Nat.card (E i) = 3 ^ (fun _ : Fin 3 => 1) i := by
    intro i
    rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPLE i)).toEquiv, hPcard i]
  have hEel : ∀ i, IsElemAbelian 3 (E i) := fun i =>
    isElemAbelian_of_card_prime Nat.prime_three (p := 3) (E := E i) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPLE i)).toEquiv, hPcard i])
  have hLfam_inj : Function.Injective Lfam := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Lfam]
  have hinj : Function.Injective A := by
    intro i j hij
    apply hLfam_inj
    have h := (Subgroup.subgroupOf_inj (K := L)).1 hij
    rwa [inf_eq_left.mpr (hLfam_le i), inf_eq_left.mpr (hLfam_le j)] at h
  have hZ : ∀ i, ¬ 3 ∣ Nat.card (center (↥(A i) ⧸ CFSG.pCore 2 ↥(A i))) := by
    intro i
    rw [(UC6S846.calC_subgroupOf (hcal i)).2.2.2, center_eq_bot_of_isL3 (hshape i),
      Subgroup.card_bot]
    norm_num
  obtain ⟨W, hWel, hWcard⟩ := UC6S898.rank_sum_of_family (Y := ↥L) (ι := Fin 3)
    (A := A) (E := E) (q := 3) (a := fun _ => 1) Nat.prime_three (by norm_num)
    (fun i => (UC6S846.calC_subgroupOf (hcal i)).1)
    (fun i => (UC6S846.calC_subgroupOf (hcal i)).2.1)
    (fun i => (UC6S846.calC_subgroupOf (hcal i)).2.2.1)
    hinj hZ hEA hEel hEc Finset.univ
  have hWcard' : Nat.card W = 3 ^ 3 := by simpa using hWcard
  have hcardW' : Nat.card (W.map L.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hWcard']
  have h3 := UC6S846.le_pRank' Nat.prime_three (H := L) (E := W.map L.subtype)
    (Subgroup.map_subtype_le W) (CFSG.Open.IsElemAbelian.map hWel L.subtype) hcardW'
  omega

theorem hyp81_of_three (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) (s₁ : IsL3 (Bar2 L₁) 1)
    (s₂ : IsL3 (Bar2 L₂) 1) (s₃ : IsL3 (Bar2 L₃) 1) : F08.Hyp81 M (L₁ ⊔ L₂ ⊔ L₃) := by
  unfold F08.Hyp81
  exact ⟨isSubnormal_sup_sup h₁ h₂ h₃, commutator_sup_sup h₁ h₂ h₃,
    two_lt_pRank_sup_sup h₁ h₂ h₃ h12 h13 h23 s₁ s₂ s₃,
    Or.inr ⟨L₁, L₂, L₃, h₁, h₂, h₃, pRank_three_of_isL3 s₁, pRank_three_of_isL3 s₂,
      pRank_three_of_isL3 s₃, le_sup_left.trans le_sup_left,
      le_sup_right.trans le_sup_left, le_sup_right,
      coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩

end ThreeMembers

@[expose] def PermutesPair (M L₁ L₂ : Subgroup G) : Prop :=
  ∀ m ∈ M,
    (L₁.map (MulAut.conj m).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj m).toMonoidHom = L₂) ∨
    (L₁.map (MulAut.conj m).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj m).toMonoidHom = L₁)

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem permutesPair (h : Hyp141 D L₁ L₂ X) (h82 : F08.R82 D)
    (hs : ¬ IsStronglyPEmbedded 3 D.M) : PermutesPair D.M L₁ L₂ := by
  intro m hm
  let f : MulAut G := MulAut.conj m
  have hM : D.M.map f.toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hm)
  have hL₁' : L₁.map f.toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M f hM h.mem₁
  have hL₂' : L₂.map f.toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M f hM h.mem₂
  have hs₁' : IsL3 (Bar2 (L₁.map f.toMonoidHom)) 1 := isL3_bar2_map_conj f h.shape₁
  have hs₂' : IsL3 (Bar2 (L₂.map f.toMonoidHom)) 1 := isL3_bar2_map_conj f h.shape₂
  have key : ∀ K : Subgroup G, K ∈ calC D.M → IsL3 (Bar2 K) 1 → K = L₁ ∨ K = L₂ := by
    intro K hK hKs
    by_contra hne
    push Not at hne
    obtain ⟨hK1, hK2⟩ := hne
    exact hs (h82 (L₁ ⊔ L₂ ⊔ K)
      (hyp81_of_three h.mem₁ h.mem₂ hK h.ne hK1.symm hK2.symm h.shape₁ h.shape₂ hKs))
  have hA := key _ hL₁' hs₁'
  have hB := key _ hL₂' hs₂'
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exfalso
    exact h.ne (Subgroup.map_injective f.injective (hA.trans hB.symm))
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exfalso
    exact h.ne (Subgroup.map_injective f.injective (hA.trans hB.symm))

theorem M_le_normalizer_sup (h : Hyp141 D L₁ L₂ X) (hperm : PermutesPair D.M L₁ L₂) :
    D.M ≤ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
  intro m hm
  rw [UC6S846.mem_normalizer_iff_map_conj, Subgroup.map_sup]
  rcases hperm m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact sup_comm _ _

theorem le_normalizer_of_isPGroup (h : Hyp141 D L₁ L₂ X) (hperm : PermutesPair D.M L₁ L₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) (hPM : P ≤ D.M) :
    P ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) := by
  intro x hx
  have hxM : x ∈ D.M := hPM hx
  rw [Subgroup.mem_inf, UC6S846.mem_normalizer_iff_map_conj,
    UC6S846.mem_normalizer_iff_map_conj]
  rcases hperm x hxM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · have hsq1 : x ^ 2 ∈ normalizer (L₁ : Set G) := by
      rw [pow_two, UC6S846.mem_normalizer_iff_map_conj]
      have hcomp : MulAut.conj (x * x) = MulAut.conj x * MulAut.conj x :=
        map_mul MulAut.conj x x
      have hto : (MulAut.conj x * MulAut.conj x).toMonoidHom =
          (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
        ext y
        simp [MulAut.mul_apply]
      rw [hcomp, hto, ← Subgroup.map_map, h1, h2]
    have hsq2 : x ^ 2 ∈ normalizer (L₂ : Set G) := by
      rw [pow_two, UC6S846.mem_normalizer_iff_map_conj]
      have hcomp : MulAut.conj (x * x) = MulAut.conj x * MulAut.conj x :=
        map_mul MulAut.conj x x
      have hto : (MulAut.conj x * MulAut.conj x).toMonoidHom =
          (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
        ext y
        simp [MulAut.mul_apply]
      rw [hcomp, hto, ← Subgroup.map_map, h2, h1]
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hk' : x ^ (p ^ k) = 1 := by simpa using hk
    have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨j, hj⟩ := hodd
    have hx_eq : x = ((x ^ 2) ^ j)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have h := hk'
      rw [hj, pow_succ, pow_mul] at h
      exact h
    have hxN1 : x ∈ normalizer (L₁ : Set G) := by
      rw [hx_eq]
      exact (Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem hsq1 j)
    have hxN2 : x ∈ normalizer (L₂ : Set G) := by
      rw [hx_eq]
      exact (Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem hsq2 j)
    exact ⟨UC6S846.mem_normalizer_iff_map_conj.1 hxN1,
      UC6S846.mem_normalizer_iff_map_conj.1 hxN2⟩

end Hyp141

theorem mem_centOverO2_iff {X L : Subgroup G} {x : G} :
    x ∈ F08.CentOverO2 X L ↔ x ∈ X ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  let Q := pCoreOf 2 L
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have norm_of_pred : ∀ y : G, (y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q) →
      y ∈ normalizer (L : Set G) := by
    intro y hy
    rw [UC6S846.mem_normalizer_iff_map_conj]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      intro l hl
      rw [Subgroup.mem_comap]
      have hmem : (MulAut.conj y).toMonoidHom l = (y * l * y⁻¹ * l⁻¹) * l := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [hmem]
      exact L.mul_mem (hQL (hy.2 l hl)) hl
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  unfold F08.CentOverO2
  constructor
  · intro hx
    change x ∈ Subgroup.closure {y : G | y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q} at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨X.one_mem, fun l _ => by simp⟩
    | mul a b _ _ ha hb =>
      refine ⟨X.mul_mem ha.1 hb.1, fun l hl => ?_⟩
      have haQ : a ∈ normalizer (Q : Set G) :=
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) (norm_of_pred a ha)
      have h1 : a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 haQ (b * l * b⁻¹ * l⁻¹)).1 (hb.2 l hl)
      have h2 : a * l * a⁻¹ * l⁻¹ ∈ Q := ha.2 l hl
      have hmem := Q.mul_mem h1 h2
      convert hmem using 1
      group
    | inv a _ ha =>
      refine ⟨X.inv_mem ha.1, fun l hl => ?_⟩
      have haQ : a ∈ normalizer (Q : Set G) :=
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) (norm_of_pred a ha)
      have hq : l * a * l⁻¹ * a⁻¹ ∈ Q := by
        rw [show l * a * l⁻¹ * a⁻¹ = (a * l * a⁻¹ * l⁻¹)⁻¹ by group]
        exact Q.inv_mem (ha.2 l hl)
      have hmem := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haQ)
        (l * a * l⁻¹ * a⁻¹)).1 hq
      convert hmem using 1
      group
  · rintro ⟨hxX, hxL⟩
    exact Subgroup.subset_closure ⟨hxX, hxL⟩

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem pCoreOf_sup_le_aux (h : Hyp141 D L₁ L₂ X) :
    pCoreOf 2 L₁ ⊔ pCoreOf 2 L₂ ≤ pCoreOf 2 (L₁ ⊔ L₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have n12 : L₂ ≤ normalizer (L₁ : Set G) := calC_le_normalizer_of_ne h.mem₁ h.mem₂ h.ne
  have n21 : L₁ ≤ normalizer (L₂ : Set G) :=
    calC_le_normalizer_of_ne h.mem₂ h.mem₁ h.ne.symm
  have hN : L₁ ⊔ L₂ ≤ normalizer (pCoreOf 2 L₁ ⊔ pCoreOf 2 L₂ : Subgroup G) := by
    have hL₁ : L₁ ≤ normalizer (pCoreOf 2 L₁ : Set G) ⊓
        normalizer (pCoreOf 2 L₂ : Set G) :=
      le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁)
        (n21.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₂))
    have hL₂ : L₂ ≤ normalizer (pCoreOf 2 L₁ : Set G) ⊓
        normalizer (pCoreOf 2 L₂ : Set G) :=
      le_inf (n12.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₂)
    exact (sup_le hL₁ hL₂).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hP : IsPGroup 2 (pCoreOf 2 L₁ ⊔ pCoreOf 2 L₂ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₂)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans
        (n21.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₂)))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans le_sup_left)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₂).trans le_sup_right)) hN hP

theorem acts_trivially_sup_iff (h : Hyp141 D L₁ L₂ X) {w : G} (hw₁ : w ∈ normalizer (L₁ : Set G))
    (hw₂ : w ∈ normalizer (L₂ : Set G)) :
    (∀ l ∈ L₁ ⊔ L₂, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂)) ↔
      ((∀ l ∈ L₁, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) ∧
        (∀ l ∈ L₂, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L₂)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCoreOf 2 (L₁ ⊔ L₂)
  have hQ₁ : pCoreOf 2 L₁ ≤ Q := le_sup_left.trans (Hyp141.pCoreOf_sup_le_aux h)
  have hQ₂ : pCoreOf 2 L₂ ≤ Q := le_sup_right.trans (Hyp141.pCoreOf_sup_le_aux h)
  have hLnormQ : L₁ ⊔ L₂ ≤ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ L₂)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ L₂)
  constructor
  · intro hw
    constructor
    · intro l hl
      have hcomm : w * l * w⁻¹ * l⁻¹ ∈ Q := hw l (Subgroup.mem_sup_left hl)
      have hcommL : w * l * w⁻¹ * l⁻¹ ∈ L₁ := by
        have h1 : w * l * w⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.1 hw₁ l).1 hl
        simpa [mul_assoc] using L₁.mul_mem h1 (L₁.inv_mem hl)
      have hmem : w * l * w⁻¹ * l⁻¹ ∈ L₁ ⊓ Q := Subgroup.mem_inf.mpr ⟨hcommL, hcomm⟩
      have hp : IsPGroup 2 (L₁ ⊓ Q : Subgroup G) := IsPGroup.to_le hQ2 (inf_le_right : L₁ ⊓ Q ≤ Q)
      have hnorm : L₁ ≤ normalizer ((L₁ ⊓ Q : Subgroup G) : Set G) := by
        have hLQ : L₁ ≤ normalizer (Q : Set G) := le_sup_left.trans hLnormQ
        exact (le_inf Subgroup.le_normalizer hLQ).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hp hmem
    · intro l hl
      have hcomm : w * l * w⁻¹ * l⁻¹ ∈ Q := hw l (Subgroup.mem_sup_right hl)
      have hcommL : w * l * w⁻¹ * l⁻¹ ∈ L₂ := by
        have h1 : w * l * w⁻¹ ∈ L₂ := (Subgroup.mem_normalizer_iff.1 hw₂ l).1 hl
        simpa [mul_assoc] using L₂.mul_mem h1 (L₂.inv_mem hl)
      have hmem : w * l * w⁻¹ * l⁻¹ ∈ L₂ ⊓ Q := Subgroup.mem_inf.mpr ⟨hcommL, hcomm⟩
      have hp : IsPGroup 2 (L₂ ⊓ Q : Subgroup G) := IsPGroup.to_le hQ2 (inf_le_right : L₂ ⊓ Q ≤ Q)
      have hnorm : L₂ ≤ normalizer ((L₂ ⊓ Q : Subgroup G) : Set G) := by
        have hLQ : L₂ ≤ normalizer (Q : Set G) := le_sup_right.trans hLnormQ
        exact (le_inf Subgroup.le_normalizer hLQ).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hp hmem
  · rintro ⟨h1, h2⟩ l hl
    have hl' : l ∈ (L₁ : Set G) * L₂ := by
      rw [← Hyp141.coe_sup h]
      exact hl
    obtain ⟨a, ha, b, hb, rfl⟩ := hl'
    have haQ : a ∈ normalizer (Q : Set G) := hLnormQ (Subgroup.mem_sup_left ha)
    have h1' : w * a * w⁻¹ * a⁻¹ ∈ Q := hQ₁ (h1 a ha)
    have h2' : a * (w * b * w⁻¹ * b⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 haQ (w * b * w⁻¹ * b⁻¹)).1 (hQ₂ (h2 b hb))
    have hmem := Q.mul_mem h1' h2'
    convert hmem using 1
    group

end Hyp141

theorem eq_sup_centralizer_of_acts_trivially {L W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hW : IsPGroup p W) (hWn : W ≤ normalizer (L : Set G))
    (hWc : ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    L = (L ⊓ centralizer (W : Set G)) ⊔ pCoreOf 2 L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCoreOf 2 L
  apply le_antisymm
  · intro l hl
    let L' : Subgroup G := L ⊔ W
    have hQL' : Q ≤ L' := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left
    have hLnormQ : L ≤ normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    have hWnormQ : W ≤ normalizer (Q : Set G) :=
      hWn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have hL'n : L' ≤ normalizer (Q : Set G) := sup_le hLnormQ hWnormQ
    have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    have hWL' : W ≤ L' := le_sup_right
    have hlL' : l ∈ L' := Subgroup.mem_sup_left hl
    have hnX : ∀ x ∈ W, l * x * l⁻¹ ∈ W ⊔ Q := by
      intro x hx
      have hcomm : l * x * l⁻¹ * x⁻¹ ∈ Q := by
        rw [show l * x * l⁻¹ * x⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ by group]
        exact Q.inv_mem (hWc x hx l hl)
      have hmem : (l * x * l⁻¹ * x⁻¹) * x ∈ Q ⊔ W :=
        Subgroup.mul_mem_sup hcomm hx
      rw [sup_comm] at hmem
      convert hmem using 1
      group
    obtain ⟨n, hn, hnq⟩ :=
      exists_mem_normalizer_of_mul_mem hp hp2 hQL' hL'n hQ2 hWL' hW hlL' hnX
    have hnL' : n ∈ L' := hn.1
    have hnN : n ∈ normalizer (W : Set G) := hn.2
    have hnl : l⁻¹ * n ∈ Q := by
      rw [show l⁻¹ * n = (n⁻¹ * l)⁻¹ by group]
      exact Q.inv_mem hnq
    have hnL : n ∈ L := by
      have hprod : l * (l⁻¹ * n) ∈ L :=
        L.mul_mem hl ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hnl)
      convert hprod using 1
      group
    have hncent : n ∈ centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcommW : n * x * n⁻¹ * x⁻¹ ∈ W := by
        have h1 : n * x * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hnN x).1 hx
        exact W.mul_mem h1 (W.inv_mem hx)
      have hcommQ : n * x * n⁻¹ * x⁻¹ ∈ Q := by
        rw [show n * x * n⁻¹ * x⁻¹ = (x * n * x⁻¹ * n⁻¹)⁻¹ by group]
        exact Q.inv_mem (hWc x hx n hnL)
      have hdisj : Disjoint W Q := IsPGroup.disjoint_of_ne p 2 hp2 W Q hW hQ2
      have hmem : n * x * n⁻¹ * x⁻¹ ∈ W ⊓ Q := Subgroup.mem_inf.mpr ⟨hcommW, hcommQ⟩
      rw [disjoint_iff.mp hdisj] at hmem
      have hbot : n * x * n⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hmem
      calc x * n = (n * x * n⁻¹ * x⁻¹) * (x * n) := by rw [hbot, one_mul]
        _ = n * x := by group
    have hnin : n ∈ L ⊓ centralizer (W : Set G) := Subgroup.mem_inf.mpr ⟨hnL, hncent⟩
    have hmem : n * (n⁻¹ * l) ∈ (L ⊓ centralizer (W : Set G)) ⊔ Q :=
      Subgroup.mul_mem_sup hnin hnq
    convert hmem using 1
    group
  · exact sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 L)

theorem acts_trivially_of_isPGroup {L W : Subgroup G} (hL : IsL3 (Bar2 L) 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7) (hW : IsPGroup p W)
    (hWn : W ≤ normalizer (L : Set G)) :
    ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  intro w hw l hl
  haveI : Fact p.Prime := ⟨hp⟩
  let N := normalizer (L : Set G)
  let m : ↥N := ⟨w, hWn hw⟩
  let ρ := UC6S846.rhoL L
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hk' : w ^ (p ^ k) = 1 := by simpa using hk
  have hmk : m ^ (p ^ k) = 1 := by
    apply Subtype.ext
    simpa [m] using hk'
  have hρk : (ρ m) ^ (p ^ k) = 1 := by
    rw [← map_pow, hmk, map_one]
  have hordp : orderOf (ρ m) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hρk
  have hord336 : orderOf (ρ m) ∣ 336 :=
    (orderOf_dvd_natCard (ρ m)).trans (card_mulAut_dvd_of_isL3 hL)
  have hdiv : ¬ p ∣ 336 := by
    intro hd
    have h336 : 2 ^ 4 * 3 * 7 = 336 := by norm_num
    rw [← h336] at hd
    rcases hp.dvd_mul.1 hd with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h)
  have hcop : Nat.Coprime (p ^ k) 336 :=
    Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).2 hdiv)
  have hord1 : orderOf (ρ m) = 1 := by
    apply Nat.dvd_one.mp
    have h := Nat.dvd_gcd hordp hord336
    rwa [hcop.gcd_eq_one] at h
  have hρ1 : ρ m = 1 := orderOf_eq_one_iff.mp hord1
  rw [← UC6S846.rhoL_fix_iff L m ⟨l, hl⟩]
  rw [hρ1]
  simp

theorem exists_mem_acts_eq {L A P : Subgroup G} (hL : IsL3 (Bar2 L) 1) (hP : IsPGroup 3 P)
    (hPn : P ≤ normalizer (L : Set G)) (hAP : A ≤ P) (hAL : A ≤ L) (hAc : Nat.card A = 3)
    {p : G} (hp : p ∈ P) :
    ∃ a ∈ A, ∀ l ∈ L, (a⁻¹ * p) * l * (a⁻¹ * p)⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normalizer (L : Set G)
  let ρ := UC6S846.rhoL L
  let P' : Subgroup ↥N := P.subgroupOf N
  let A' : Subgroup ↥N := A.subgroupOf N
  let R : Subgroup (MulAut (Bar2 L)) := P'.map ρ
  have hP' : IsPGroup 3 P' := hP.comap_subtype
  have hR : IsPGroup 3 R := hP'.map ρ
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcardR : Nat.card R = 3 ^ k := hk
  have hR336 : Nat.card R ∣ 336 :=
    R.card_subgroup_dvd_card.trans (card_mulAut_dvd_of_isL3 hL)
  have hdivR : Nat.card R ∣ 3 := by
    have hcop : Nat.Coprime (3 ^ k) 112 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 112)
    rw [hcardR] at hR336 ⊢
    have h336 : 336 = 3 * 112 := by norm_num
    rw [h336] at hR336
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hR336
  have hdisj : Disjoint A' ρ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxA' hxker
    have haA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hxA'
    have haL : (x : G) ∈ L := hAL haA
    have hρx : ρ x = 1 := MonoidHom.mem_ker.mp hxker
    have hxval : x = (⟨(x : G), Subgroup.le_normalizer haL⟩ : ↥N) := Subtype.ext rfl
    have hconj : MulAut.conj ((QuotientGroup.mk (⟨(x : G), haL⟩ : ↥L) : Bar2 L)) = 1 := by
      rw [hxval] at hρx
      rw [← UC6S846.rhoL_inner L (x : G) haL]
      exact hρx
    let z : Bar2 L := QuotientGroup.mk (⟨(x : G), haL⟩ : ↥L)
    have hcenter : z ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun f : MulAut (Bar2 L) => f y) hconj
      simp only [MulAut.one_apply] at hy
      have hzy : z * y * z⁻¹ = y := by simpa [MulAut.conj_apply] using hy
      have hzy' : z * y = y * z := by
        have := congrArg (· * z) hzy
        simpa [mul_assoc] using this
      exact hzy'.symm
    have hz1 : z = 1 := by
      have h := hcenter
      rw [center_eq_bot_of_isL3 hL] at h
      simpa using (Subgroup.mem_bot.mp h)
    have hxQ : (x : G) ∈ pCoreOf 2 L := by
      change (x : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype
      exact Subgroup.mem_map.mpr
        ⟨⟨(x : G), haL⟩, (QuotientGroup.eq_one_iff _).1 hz1, rfl⟩
    have hxA3 : IsPGroup 3 A := hP.to_le hAP
    have hx1 : (x : G) = 1 :=
      UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup Nat.prime_three (by norm_num)
        hxA3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) haA hxQ
    exact Subtype.ext (by simpa using hx1)
  have hA'N : A ≤ N := hAP.trans hPn
  have hdisjcard : Nat.card (A'.map ρ) = Nat.card A' :=
    UC6S846.card_map_of_disjoint_ker ρ A' hdisj
  have hcardA' : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'N).toEquiv
  have hcardAρ : Nat.card (A'.map ρ) = 3 := by
    rw [hdisjcard, hcardA', hAc]
  have hA'P' : A' ≤ P' := Subgroup.subgroupOf_mono N hAP
  have hmaple : A'.map ρ ≤ R := Subgroup.map_mono hA'P'
  have h3dvdR : 3 ∣ Nat.card R := by
    have h := Subgroup.card_dvd_of_le hmaple
    rwa [hcardAρ] at h
  have hR3 : Nat.card R = 3 := Nat.dvd_antisymm hdivR h3dvdR
  have hA'R : A'.map ρ = R := by
    apply Subgroup.eq_of_le_of_card_ge hmaple
    rw [hcardAρ, hR3]
  have hp' : (⟨p, hPn hp⟩ : ↥N) ∈ P' := Subgroup.mem_subgroupOf.mpr hp
  have hmemR : ρ ⟨p, hPn hp⟩ ∈ R := Subgroup.mem_map_of_mem ρ hp'
  rw [← hA'R] at hmemR
  obtain ⟨a'', ha'', hρa''⟩ := Subgroup.mem_map.1 hmemR
  refine ⟨(a'' : G), Subgroup.mem_subgroupOf.mp ha'', fun l hl => ?_⟩
  let m : ↥N := a''⁻¹ * ⟨p, hPn hp⟩
  have hmρ : ρ m = 1 := by
    simp [m, hρa'']
  have hmcoe : (m : G) = (a'' : G)⁻¹ * p := by
    simp [m]
  rw [← hmcoe]
  rw [← UC6S846.rhoL_fix_iff L m ⟨l, hl⟩]
  rw [hmρ]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
