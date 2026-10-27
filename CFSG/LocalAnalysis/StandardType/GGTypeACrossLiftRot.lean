module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeRel
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix
open scoped commutatorElement

section Entries

variable {F : Type} [Field F]

private theorem signedPerm_mul_apply {m : ℕ} (π : Equiv.Perm (Fin m))
    (M : Matrix (Fin m) (Fin m) F) (r s : Fin m) :
    (signedPerm π (1 : Fin m → F) * M) r s = M (π.symm r) s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm r)]
  · simp [signedPerm_apply]
  · intro u _ hu
    have h : ¬(r = π u) := fun e => hu (by rw [e, Equiv.symm_apply_apply])
    simp [signedPerm_apply, h]
  · intro h
    simp at h

private theorem mul_signedPerm_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) F)
    (π : Equiv.Perm (Fin m)) (r s : Fin m) :
    (M * signedPerm π (1 : Fin m → F)) r s = M r (π s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π s)]
  · simp [signedPerm_apply]
  · intro u _ hu
    simp [signedPerm_apply, hu]
  · intro h
    simp at h

end Entries

theorem finRotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  rw [show i.castSucc = (⟨i.val, i.isLt.trans_le n.le_succ⟩ : Fin (n + 1)) from rfl]
  rw [finRotate_of_lt i.isLt]
  rfl

theorem finRotate_finSumFinEquiv {n : ℕ} (p : Fin n ⊕ Fin 1) :
    finRotate (n + 1) (finSumFinEquiv p) =
      slLowerBlockEquiv n (Equiv.sumComm (Fin n) (Fin 1) p) := by
  rcases p with i | j
  · rw [finSumFinEquiv_apply_left,
      show Equiv.sumComm (Fin n) (Fin 1) (Sum.inl i) = Sum.inr i from rfl,
      slLowerBlockEquiv_inr]
    exact finRotate_castSucc i
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [finSumFinEquiv_apply_right,
      show Equiv.sumComm (Fin n) (Fin 1) (Sum.inr 0) = Sum.inl 0 from rfl,
      slLowerBlockEquiv_inl, slBlock_natAdd_zero_eq_last]
    exact finRotate_last

theorem slPerm_finRotate_conj_slUpperBlockHom {F : Type} [Field F] (h2 : (2 : F) = 0) {n : ℕ}
    (s : SpecialLinearGroup (Fin n) F) :
    slPerm h2 (finRotate (n + 1)) * slUpperBlockHom n F s *
        (slPerm h2 (finRotate (n + 1)))⁻¹ =
      slLowerBlockHom n F s := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show signedPerm (finRotate (n + 1)) (1 : Fin (n + 1) → F) * slUpperBlockMat n F ↑s =
    slLowerBlockMat n F ↑s * signedPerm (finRotate (n + 1)) (1 : Fin (n + 1) → F)
  ext r t
  rw [signedPerm_mul_apply, mul_signedPerm_apply]
  obtain ⟨a, rfl⟩ : ∃ a, finRotate (n + 1) a = r :=
    ⟨(finRotate (n + 1)).symm r, (finRotate (n + 1)).apply_symm_apply r⟩
  rw [Equiv.symm_apply_apply]
  obtain ⟨p, rfl⟩ : ∃ p, finSumFinEquiv p = a :=
    ⟨finSumFinEquiv.symm a, finSumFinEquiv.apply_symm_apply a⟩
  obtain ⟨q, rfl⟩ : ∃ q, finSumFinEquiv q = t :=
    ⟨finSumFinEquiv.symm t, finSumFinEquiv.apply_symm_apply t⟩
  rw [finRotate_finSumFinEquiv p, finRotate_finSumFinEquiv q, slUpperBlockMat_apply,
    slLowerBlockMat_apply]
  rcases p with i | i <;> rcases q with j | j
  · simp [Matrix.fromBlocks_apply₁₁]
  · simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁]
  · simp [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₂]
  · obtain rfl : i = j := Subsingleton.elim i j
    simp [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁]

section RotLift

variable {F : Type} [Field F] {X : Type*} [Group X] {n : ℕ}

@[expose] noncomputable def ggRotLift (h2 : (2 : F) = 0)
    (φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    SpecialLinearGroup (Fin (n + 1)) F →* X :=
  (MulAut.conj (φ₂ (slPerm h2 (finRotate (n + 1))))).toMonoidHom.comp φ₃

theorem ggRotLift_apply (h2 : (2 : F) = 0)
    (φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X)
    (s : SpecialLinearGroup (Fin (n + 1)) F) :
    ggRotLift h2 φ₂ φ₃ s =
      φ₂ (slPerm h2 (finRotate (n + 1))) * φ₃ s *
        (φ₂ (slPerm h2 (finRotate (n + 1))))⁻¹ :=
  rfl

theorem ggRotLift_range (h2 : (2 : F) = 0)
    (φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    (ggRotLift h2 φ₂ φ₃).range =
      φ₃.range.map (MulAut.conj (φ₂ (slPerm h2 (finRotate (n + 1))))).toMonoidHom :=
  MonoidHom.range_comp _ _

theorem ggRotLift_ker (h2 : (2 : F) = 0)
    (φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    (ggRotLift h2 φ₂ φ₃).ker = φ₃.ker :=
  MonoidHom.ker_comp_of_injective φ₃ _ (MulAut.conj _).injective

theorem ggRotLift_compat (h2 : (2 : F) = 0)
    {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hc₂ : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hc₃ : φ₁.comp (slLowerBlockHom n F) = φ₃.comp (slUpperBlockHom n F)) :
    φ₂.comp (slLowerBlockHom n F) = (ggRotLift h2 φ₂ φ₃).comp (slUpperBlockHom n F) := by
  ext s
  simp only [MonoidHom.comp_apply, ggRotLift_apply]
  have h23 : φ₃ (slUpperBlockHom n F s) = φ₂ (slUpperBlockHom n F s) :=
    ((DFunLike.congr_fun hc₃ s).symm).trans (DFunLike.congr_fun hc₂ s)
  rw [h23, ← map_mul, ← map_inv, ← map_mul, slPerm_finRotate_conj_slUpperBlockHom h2 s]

end RotLift

section PermUp

variable {F : Type} [Field F]

theorem exists_slUpperBlockHom_eq_slPerm (h2 : (2 : F) = 0) {n : ℕ}
    {π : Equiv.Perm (Fin (n + 1))} (hπ : π (Fin.last n) = Fin.last n) :
    ∃ s : SpecialLinearGroup (Fin n) F, slUpperBlockHom n F s = slPerm h2 π := by
  let p : Fin (n + 1) → Prop := fun x => x ≠ Fin.last n
  have hp : ∀ x, p (π x) ↔ p x := by
    intro x
    exact ⟨fun hx e => hx (by rw [e, hπ]), fun hx e => hx (π.injective (e.trans hπ.symm))⟩
  have hfix : ∀ x, π x ≠ x → p x := by
    intro x hx
    by_contra h
    exact hx (by rw [h, hπ])
  have hmem : ∀ σ : Equiv.Perm {x : Fin (n + 1) // p x},
      Equiv.Perm.ofSubtype σ ∈ (slUpperBlockHom n F).range.comap (slPerm h2) := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ (by simpa only [map_one] using Subgroup.one_mem _) ?_
    intro f x y hxy hf
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    refine mul_mem ?_ hf
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr x.2
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr y.2
    rw [← hi, ← hj, Subgroup.mem_comap, ← slUpperBlockHom_slPerm_swap h2 i j]
    exact ⟨_, rfl⟩
  have hπ' := hmem (π.subtypePerm hp)
  rw [Equiv.Perm.ofSubtype_subtypePerm hp hfix, Subgroup.mem_comap] at hπ'
  obtain ⟨s, hs⟩ := hπ'
  exact ⟨s, hs⟩

end PermUp

section UpperCommute

variable {F : Type} [Field F] {X : Type*} [Group X] {n : ℕ}

theorem commute_slUpperBlockHom_of_transvection (hn : 2 ≤ n)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
    (h : ∀ (a b : Fin (n + 1)) (hab : a ≠ b), a.val < n → b.val < n → ∀ c : F,
      Commute T (φ (SpecialLinearGroup.transvection hab c)))
    (s : SpecialLinearGroup (Fin n) F) : Commute T (φ (slUpperBlockHom n F s)) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have htop : (Subgroup.centralizer ({T} : Set X)).comap (φ.comp (slUpperBlockHom n F)) = ⊤ := by
    refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem _ ?_
    intro i j hij c
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, slUpperBlockHom_transvection hij c]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h i.castSucc j.castSucc ((Fin.castSucc_injective n).ne hij) (by simp) (by simp) c
  have hs : s ∈ (Subgroup.centralizer ({T} : Set X)).comap (φ.comp (slUpperBlockHom n F)) := by
    rw [htop]
    exact Subgroup.mem_top s
  rw [Subgroup.mem_comap] at hs
  exact hs T (by simp)

end UpperCommute

section Generation

variable {F : Type} [Field F]

theorem eq_top_of_slLowerBlockHom_le (h2 : (2 : F) = 0) {n : ℕ} (hn : 2 ≤ n)
    (H : Subgroup (SpecialLinearGroup (Fin (n + 1)) F))
    (hlow : ∀ s, slLowerBlockHom n F s ∈ H) {i : Fin n} (hi : i.val = 0)
    (hw : weylRep n F i ∈ H) : H = ⊤ := by
  haveI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hz : i.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simpa using hi)
  have hone : i.succ = (1 : Fin (n + 1)) := by
    ext
    rw [Fin.val_succ, hi, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have h10 : (1 : Fin (n + 1)) ≠ 0 := by
    intro e
    have h := congrArg Fin.val e
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega), Fin.val_zero] at h
    omega
  have hinner : ∀ {a b : Fin (n + 1)} (hab : a ≠ b), a ≠ 0 → b ≠ 0 → ∀ c : F,
      SpecialLinearGroup.transvection hab c ∈ H := by
    intro a b hab ha0 hb0 c
    obtain ⟨a', rfl⟩ := Fin.exists_succ_eq.mpr ha0
    obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.mpr hb0
    have hab' : a' ≠ b' := fun e => hab (by rw [e])
    have h := hlow (SpecialLinearGroup.transvection hab' c)
    rwa [slLowerBlockHom_transvection hab' c] at h
  have hrow : ∀ (b : Fin (n + 1)) (h0b : (0 : Fin (n + 1)) ≠ b), b ≠ 0 → b ≠ 1 →
      ∀ c : F, SpecialLinearGroup.transvection h0b c ∈ H := by
    intro b h0b hb0 hb1 c
    have h1b : (1 : Fin (n + 1)) ≠ b := fun e => hb1 e.symm
    have hidx1 : (Equiv.swap i.castSucc i.succ) (1 : Fin (n + 1)) = 0 := by
      rw [hone, hz, Equiv.swap_apply_right]
    have hidxb : (Equiv.swap i.castSucc i.succ) b = b := by
      rw [hz, hone]
      exact Equiv.swap_apply_of_ne_of_ne hb0 hb1
    have key := weylRep_conj_transvection_of_two h2 i h1b c
    rw [transvection_eq_of_eq ((Equiv.swap i.castSucc i.succ).injective.ne h1b) h0b hidx1
      hidxb c] at key
    have hm : weylRep n F i * SpecialLinearGroup.transvection h1b c *
        (weylRep n F i)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hw (hinner h1b h10 hb0 c)) (H.inv_mem hw)
    exact key ▸ hm
  have hcol : ∀ (b : Fin (n + 1)) (hb0 : b ≠ 0), b ≠ 1 →
      ∀ c : F, SpecialLinearGroup.transvection hb0 c ∈ H := by
    intro b hb0 hb1 c
    have hidxb : (Equiv.swap i.castSucc i.succ) b = b := by
      rw [hz, hone]
      exact Equiv.swap_apply_of_ne_of_ne hb0 hb1
    have hidx1 : (Equiv.swap i.castSucc i.succ) (1 : Fin (n + 1)) = 0 := by
      rw [hone, hz, Equiv.swap_apply_right]
    have key := weylRep_conj_transvection_of_two h2 i hb1 c
    rw [transvection_eq_of_eq ((Equiv.swap i.castSucc i.succ).injective.ne hb1) hb0 hidxb
      hidx1 c] at key
    have hm : weylRep n F i * SpecialLinearGroup.transvection hb1 c *
        (weylRep n F i)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hw (hinner hb1 hb0 h10 c)) (H.inv_mem hw)
    exact key ▸ hm
  let k2 : Fin (n + 1) := ⟨2, by omega⟩
  have hk2 : (k2 : ℕ) = 2 := rfl
  have h02 : (0 : Fin (n + 1)) ≠ k2 := by
    intro e
    have h := congrArg Fin.val e
    rw [Fin.val_zero, hk2] at h
    omega
  have h20 : k2 ≠ 0 := fun e => h02 e.symm
  have h21 : k2 ≠ (1 : Fin (n + 1)) := by
    intro e
    have h := congrArg Fin.val e
    rw [hk2, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h
    omega
  have h12 : (1 : Fin (n + 1)) ≠ k2 := fun e => h21 e.symm
  have h01ne : (0 : Fin (n + 1)) ≠ (1 : Fin (n + 1)) := by
    intro e
    have h := congrArg Fin.val e
    rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h
    omega
  have h01 : ∀ c : F, SpecialLinearGroup.transvection h01ne c ∈ H := by
    intro c
    have e := Matrix.SpecialLinearGroup.commutatorElement_transvection h02 h21 h01ne c (1 : F)
    rw [mul_one] at e
    have hx : SpecialLinearGroup.transvection h02 c ∈ H := hrow k2 h02 h20 h21 c
    have hy : SpecialLinearGroup.transvection h21 (1 : F) ∈ H := hinner h21 h20 h10 1
    have hm : SpecialLinearGroup.transvection h01ne c ∈ H := by
      rw [← e, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
    exact hm
  have h10ne : (1 : Fin (n + 1)) ≠ (0 : Fin (n + 1)) := h10
  have h10t : ∀ c : F, SpecialLinearGroup.transvection h10ne c ∈ H := by
    intro c
    have e := Matrix.SpecialLinearGroup.commutatorElement_transvection h12 h20 h10ne c (1 : F)
    rw [mul_one] at e
    have hx : SpecialLinearGroup.transvection h12 c ∈ H := hinner h12 h10 h20 c
    have hy : SpecialLinearGroup.transvection h20 (1 : F) ∈ H := hcol k2 h20 h21 1
    have hm : SpecialLinearGroup.transvection h10ne c ∈ H := by
      rw [← e, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
    exact hm
  refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem H ?_
  intro a b hab c
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · exact absurd (by rw [ha0, hb0]) hab
    by_cases hb1 : b = 1
    · exact transvection_eq_of_eq h01ne hab ha0.symm hb1.symm c ▸ h01 c
    · have h0b : (0 : Fin (n + 1)) ≠ b := fun e => hb0 e.symm
      exact transvection_eq_of_eq h0b hab ha0.symm rfl c ▸ hrow b h0b hb0 hb1 c
  · by_cases hb0 : b = 0
    · by_cases ha1 : a = 1
      · exact transvection_eq_of_eq h10ne hab ha1.symm hb0.symm c ▸ h10t c
      · exact transvection_eq_of_eq ha0 hab rfl hb0.symm c ▸ hcol a ha0 ha1 c
    · exact hinner hab ha0 hb0 c

end Generation

end CFSG.StandardType
