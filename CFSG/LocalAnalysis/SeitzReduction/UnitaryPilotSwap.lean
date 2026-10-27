module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapFactors
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapGen
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Simple

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem isSimpleGroup_unitaryPSU_of_three_le (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    IsSimpleGroup (unitaryPSU h n) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f h.card_eq_sq n hn
    hnq
  exact (unitaryPSUEquiv h (by omega)).isSimpleGroup

end Simple

section Sunflower

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

omit [Field K] in
theorem card_insert_union_insert_le (A : Finset (Fin n)) (x y : Fin n) :
    (insert x A ∪ insert y A).card ≤ A.card + 2 := by
  have hsub : insert x A ∪ insert y A ⊆ insert x (insert y A) := by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    · exact Finset.mem_insert_of_mem hz
  calc (insert x A ∪ insert y A).card ≤ (insert x (insert y A)).card := Finset.card_le_card hsub
    _ ≤ (insert y A).card + 1 := Finset.card_insert_le _ _
    _ ≤ A.card + 2 := by have := Finset.card_insert_le y A; omega

theorem exists_swapFactors_of_sunflower [Finite G] {A : Finset (Fin n)} (hA2 : 2 ≤ A.card)
    (hAn : A.card + 4 ≤ n) (hAq : (A.card + 1, 2 ^ f) ≠ (3, 2))
    (hgen : ⨆ x : {x : Fin n // x ∉ A}, blockSU h (insert (x : Fin n) A) = ⊤)
    (e : L ≃* unitaryPSU h n) {t : G}
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ x : {x : Fin n // x ∉ A}, pieceCore e (insert (x : Fin n) A) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  classical
  set W : {x : Fin n // x ∉ A} → Finset (Fin n) := fun x => insert (x : Fin n) A with hWdef
  have hWcard : ∀ x, (W x).card = A.card + 1 := fun x => Finset.card_insert_of_notMem x.2
  have hW3 : ∀ x, 3 ≤ (W x).card := fun x => by rw [hWcard]; omega
  have hWq : ∀ x, ((W x).card, 2 ^ f) ≠ (3, 2) := fun x => by rw [hWcard]; exact hAq
  have hAW : ∀ x, A ⊆ W x := fun x => Finset.subset_insert _ _
  obtain ⟨x₀, -, hx₀⟩ : ∃ x ∈ (Finset.univ : Finset (Fin n)), x ∉ A :=
    Finset.exists_mem_notMem_of_card_lt_card
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  set o : {x : Fin n // x ∉ A} := ⟨x₀, hx₀⟩ with ho
  have hframe : ∀ x y : {x : Fin n // x ∉ A}, ∃ (a b : Fin n) (_ : a ≠ b),
      W x ∪ W y ⊆ ({a, b}ᶜ : Finset (Fin n)) := by
    intro x y
    obtain ⟨a, b, hab, ha, hb⟩ := LinearPilot.exists_two_index_notMem (S := W x ∪ W y)
      (by
        have := card_insert_union_insert_le A (x : Fin n) (y : Fin n)
        change (insert (x : Fin n) A ∪ insert (y : Fin n) A).card + 2 ≤ n
        omega)
    exact ⟨a, b, hab, subset_compl_pair_iff.2 ⟨ha, hb⟩⟩
  choose a b hab hsub using hframe
  let P : ∀ x y : {x : Fin n // x ∉ A}, SwapNeighbourParam e t
      (modelToG e (unitaryRootTorus h (hab x y))) ({a x y, b x y}ᶜ : Finset (Fin n)) :=
    fun x y => (hparam (a x y) (b x y) (hab x y)).some
  have hWN : ∀ x y, W x ⊆ ({a x y, b x y}ᶜ : Finset (Fin n)) := fun x y =>
    Finset.subset_union_left.trans (hsub x y)
  have hWN' : ∀ x y, W y ⊆ ({a x y, b x y}ᶜ : Finset (Fin n)) := fun x y =>
    Finset.subset_union_right.trans (hsub x y)
  have hc2 : ∀ x y {I : Finset (Fin n)}, I ⊆ ({a x y, b x y}ᶜ : Finset (Fin n)) →
      2 ≤ Iᶜ.card := fun x y _ hI => two_le_card_compl_of_subset_compl_pair (hab x y) hI
  have hXI : ∀ x y {I : Finset (Fin n)}, I ⊆ ({a x y, b x y}ᶜ : Finset (Fin n)) →
      modelToG e (unitaryRootTorus h (hab x y)) ≤ modelToG e (unitaryBlockTorus h I) :=
    fun x y _ hI => modelToG_unitaryRootTorus_le e (hab x y) hI
  have hperf : ∀ x, ⁅unitaryBlock h (W x), unitaryBlock h (W x)⁆ = unitaryBlock h (W x) :=
    fun x => commutator_unitaryBlock_eq_of_three_le h (hW3 x) (hWq x)
  have hpiece : ∀ x y, pieceCore e (W y) = (P x y).fst (W y) ⊔ (P x y).snd (W y) := fun x y =>
    (P x y).pieceCore_eq_fst_sup_snd (hWN' x y) (by have := hW3 y; omega) (hc2 x y (hWN' x y))
      (hperf y) (hXI x y (hWN' x y))
  set B := (P o o).fst (W o) with hB
  have hBside : ∀ x, B = (P o x).fst (W o) ∨ B = (P o x).snd (W o) := fun x =>
    (P o x).fst_eq_or_eq (P o o) (hWN o x) (hWN o o) (hW3 o) (hWq o) (hc2 o x (hWN o x))
      (hXI o x (hWN o x)) (hXI o o (hWN o o))
  let U : {x : Fin n // x ∉ A} → Subgroup G := fun x =>
    if B = (P o x).fst (W o) then (P o x).fst (W x) else (P o x).snd (W x)
  have hU : ∀ x, (U x = (P o x).fst (W x) ∧ B = (P o x).fst (W o)) ∨
      (U x = (P o x).snd (W x) ∧ B = (P o x).snd (W o)) := by
    intro x
    by_cases hx : B = (P o x).fst (W o)
    · exact Or.inl ⟨by simp only [U, hx, ite_true], hx⟩
    · exact Or.inr ⟨by simp only [U, hx, ite_false], (hBside x).resolve_left hx⟩
  have hUsup : ∀ x, U x ⊔ (U x).map (MulAut.conj t).toMonoidHom = pieceCore e (W x) := by
    intro x
    rw [hpiece o x]
    rcases hU x with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · rw [(P o x).map_conj_fst]
    · rw [(P o x).map_conj_snd, sup_comm]
  have hb1 : ∀ x, U x ≤ centralizer (B.map (MulAut.conj t).toMonoidHom : Set G) := by
    intro x
    rcases hU x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · rw [(P o x).map_conj_fst]
      exact (P o x).fst_le_centralizer_snd _ _
    · rw [(P o x).map_conj_snd]
      exact (P o x).snd_le_centralizer_fst _ _
  have hb2 : ∀ x, (U x).map (MulAut.conj t).toMonoidHom ≤ centralizer (B : Set G) := by
    intro x
    rcases hU x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · rw [(P o x).map_conj_fst]
      exact (P o x).snd_le_centralizer_fst _ _
    · rw [(P o x).map_conj_snd]
      exact (P o x).fst_le_centralizer_snd _ _
  obtain ⟨i, hiA, j, hjA, hij⟩ : ∃ i ∈ A, ∃ j ∈ A, i ≠ j := Finset.one_lt_card.1 (by omega)
  have hijW : ∀ x, ({i, j} : Finset (Fin n)) ⊆ W x := fun x =>
    SwapNeighbourParam.pair_subset_of_mem (hAW x hiA) (hAW x hjA)
  have hJ : modelToG e (blockSU h {i, j}) ≤ B ⊔ B.map (MulAut.conj t).toMonoidHom := by
    have hle : modelToG e (blockSU h (W o)) ≤ pieceCore e (W o) :=
      modelToG_blockSU_le_pieceCore e (W o) (by rw [blockSU, ← map_commutator, hperf o])
    rw [hB, (P o o).map_conj_fst, ← hpiece o o]
    exact (modelToG_mono e (blockSU_mono h (hijW o))).trans hle
  have hcomm : ∀ x y, (U y).map (MulAut.conj t).toMonoidHom ≤ centralizer (U x : Set G) := by
    intro x y
    have hx : U x = (P x y).fst (W x) ∨ U x = (P x y).snd (W x) := by
      rcases hU x with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact (P x y).fst_eq_or_eq (P o x) (hWN x y) (hWN' o x) (hW3 x) (hWq x)
          (hc2 x y (hWN x y)) (hXI x y (hWN x y)) (hXI o x (hWN' o x))
      · exact (P x y).snd_eq_or_eq (P o x) (hWN x y) (hWN' o x) (hW3 x) (hWq x)
          (hc2 x y (hWN x y)) (hXI x y (hWN x y)) (hXI o x (hWN' o x))
    have hy : U y = (P x y).fst (W y) ∨ U y = (P x y).snd (W y) := by
      rcases hU y with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact (P x y).fst_eq_or_eq (P o y) (hWN' x y) (hWN' o y) (hW3 y) (hWq y)
          (hc2 x y (hWN' x y)) (hXI x y (hWN' x y)) (hXI o y (hWN' o y))
      · exact (P x y).snd_eq_or_eq (P o y) (hWN' x y) (hWN' o y) (hW3 y) (hWq y)
          (hc2 x y (hWN' x y)) (hXI x y (hWN' x y)) (hXI o y (hWN' o y))
    have hiN : i ∈ ({a x y, b x y}ᶜ : Finset (Fin n)) := hWN x y (hAW x hiA)
    have hjN : j ∈ ({a x y, b x y}ᶜ : Finset (Fin n)) := hWN x y (hAW x hjA)
    obtain ⟨k, hkN, hkij⟩ : ∃ k ∈ ({a x y, b x y}ᶜ : Finset (Fin n)),
        k ∉ ({i, j} : Finset (Fin n)) := by
      refine Finset.exists_mem_notMem_of_card_lt_card ?_
      rw [Finset.card_pair hij, card_compl_pair (hab x y)]
      omega
    have hki : k ≠ i := fun hk => hkij (hk ▸ Finset.mem_insert_self _ _)
    have hkj : k ≠ j := fun hk => hkij (hk ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hB2 : ∀ Q : Subgroup G, Q ≤ U x → Q ≤ (U y).map (MulAut.conj t).toMonoidHom →
        Q ≤ centralizer (modelToG e (blockSU h {i, j}) : Set G) := by
      intro Q hQx hQy
      have h3 : Q ≤ centralizer
          ((B ⊔ B.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
        rw [le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [← le_centralizer_iff]
          exact hQy.trans (hb2 y)
        · rw [← le_centralizer_iff]
          exact hQx.trans (hb1 x)
      exact h3.trans (centralizer_le (SetLike.coe_subset_coe.2 hJ))
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy, (P x y).map_conj_fst]
      exact (P x y).snd_le_centralizer_fst _ _
    · exfalso
      refine (P x y).not_le_centralizer_fst_pair hij hki.symm hkj.symm hiN hjN hkN (hB2 _ ?_ ?_)
      · rw [hx]
        exact (P x y).fst_mono (hijW x)
      · rw [hy, (P x y).map_conj_snd]
        exact (P x y).fst_mono (hijW y)
    · exfalso
      refine (P x y).not_le_centralizer_snd_pair hij hki.symm hkj.symm hiN hjN hkN (hB2 _ ?_ ?_)
      · rw [hx]
        exact (P x y).snd_mono (hijW x)
      · rw [hy, (P x y).map_conj_fst]
        exact (P x y).snd_mono (hijW y)
    · rw [hx, hy, (P x y).map_conj_snd]
      exact (P x y).fst_le_centralizer_snd _ _
  have h₁₂ := LinearPilot.map_conj_iSup_le_centralizer (U := U) hcomm
  have hsup : (⨆ x, U x) ⊔ (⨆ x, U x).map (MulAut.conj t).toMonoidHom =
      ⨆ x : {x : Fin n // x ∉ A}, pieceCore e (insert (x : Fin n) A) := by
    rw [Subgroup.map_iSup, ← iSup_sup_eq]
    exact iSup_congr hUsup
  have hδ : ∀ z ∈ ⨆ x, U x, z * (t * z * t⁻¹) ∈ L := by
    refine LinearPilot.mul_conj_mem_of_mem_iSup h₁₂ fun x z hz => modelToG_le e (blockSU h (W x)) ?_
    rcases hU x with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (P o x).mul_conj_mem_modelToG_of_mem_fst (h1 ▸ hz)
    · exact (P o x).mul_conj_mem_modelToG_of_mem_snd (h1 ▸ hz)
  have hL : L = ⨆ x : {x : Fin n // x ∉ A}, modelToG e (blockSU h (W x)) := by
    rw [← modelToG_iSup, hgen, modelToG_top]
  have hsurj : ∀ y ∈ L, ∃ z ∈ ⨆ x, U x, z * (t * z * t⁻¹) = y := by
    intro y hy
    rw [hL] at hy
    refine LinearPilot.exists_mul_conj_eq_of_mem_iSup h₁₂ (fun x y hy => ?_) y hy
    rcases hU x with ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨z, hz, hzy⟩ := (P o x).exists_mem_fst_mul_conj_eq (hWN' o x) hy
      exact ⟨z, le_iSup U x (h1 ▸ hz), hzy⟩
    · obtain ⟨z, hz, hzy⟩ := (P o x).exists_mem_snd_mul_conj_eq (hWN' o x) hy
      exact ⟨z, le_iSup U x (h1 ▸ hz), hzy⟩
  have hperfU : ⁅⨆ x, U x, ⨆ x, U x⁆ = ⨆ x, U x :=
    LinearPilot.commutator_iSup_eq_of_forall U fun x => by
      rcases hU x with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact (P o x).commutator_fst (hWN' o x) (hW3 x) (hWq x)
      · exact (P o x).commutator_snd (hWN' o x) (hW3 x) (hWq x)
  have hLs : IsSimpleGroup L := by
    have := isSimpleGroup_unitaryPSU_of_three_le h (n := n) (by omega) (fun h' => by
      have := congrArg Prod.fst h'
      simp only at this
      omega)
    exact e.isSimpleGroup
  exact ⟨⨆ x, U x, LinearPilot.isQuasisimple_of_linearSwapDiag h₁₂ hperfU hLs hδ hsurj, h₁₂,
    hsup, hδ, hsurj⟩

end Sunflower

section Global

@[expose] def swapCoreSize (f : ℕ) : ℕ :=
  if 2 ≤ f then 2 else 3

@[expose] def swapCore (n f : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => (i : ℕ) < swapCoreSize f

theorem card_swapCore {n f : ℕ} (hn : swapCoreSize f ≤ n) :
    (swapCore n f).card = swapCoreSize f := by
  rw [swapCore, Fin.card_filter_val_lt]
  omega

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

@[expose] noncomputable def swapGlobal (e : L ≃* unitaryPSU h n) : Subgroup G :=
  ⨆ x : {x : Fin n // x ∉ swapCore n f}, pieceCore e (insert (x : Fin n) (swapCore n f))

theorem swapCore_hypotheses (h : UnitaryFieldData 2 f K) (hn : 6 ≤ n) (hnf : (n, f) ≠ (6, 1)) :
    2 ≤ (swapCore n f).card ∧ (swapCore n f).card + 4 ≤ n ∧
      ((swapCore n f).card + 1, 2 ^ f) ≠ (3, 2) ∧
      ⨆ x : {x : Fin n // x ∉ swapCore n f}, blockSU h (insert (x : Fin n) (swapCore n f)) =
        ⊤ := by
  have hf1 := h.one_le
  rcases Nat.lt_or_ge f 2 with hf | hf
  · have hs : swapCoreSize f = 3 := by simp [swapCoreSize, show ¬ 2 ≤ f by omega]
    have hn7 : 7 ≤ n := by
      rcases Nat.lt_or_ge n 7 with h7 | h7
      · exact absurd (Prod.ext (by simp only; omega) (by simp only; omega)) hnf
      · exact h7
    have hcard : (swapCore n f).card = 3 := by rw [card_swapCore (by omega), hs]
    refine ⟨by omega, by omega, fun h' => ?_, ?_⟩
    · have := congrArg Prod.fst h'
      simp only at this
      omega
    · exact iSup_blockSU_insert_eq_top h (by omega) (by omega) (Or.inl (by omega))
  · have hs : swapCoreSize f = 2 := by simp [swapCoreSize, hf]
    have hcard : (swapCore n f).card = 2 := by rw [card_swapCore (by omega), hs]
    refine ⟨by omega, by omega, fun h' => ?_, ?_⟩
    · have h2 := congrArg Prod.snd h'
      simp only at h2
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    · exact iSup_blockSU_insert_eq_top h (by omega) (by omega) (Or.inr hf)

theorem exists_swapFactors_unitaryRootTorus [Finite G] (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G}
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n)))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = swapGlobal e ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  obtain ⟨hA2, hAn, hAq, hgen⟩ := swapCore_hypotheses h hn hnf
  exact exists_swapFactors_of_sunflower hA2 hAn hAq hgen e hparam

end Global

end CFSG.SeitzReduction.UnitaryPilot
