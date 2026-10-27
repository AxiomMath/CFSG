module

public import CFSG.RankThree.PartOne.KLR.TorusGeneric
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KE.F4Regular

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Psi

variable {L : Type} [Field L]

@[expose] def reePsi (a : ℕ) (v : Fin ReeTag.F4.tag.rank → ℤ) : Fin ReeTag.F4.tag.rank → ℤ :=
  fun j => (ReeTag.F4.relationExponent a j : ℤ) * v (ReeTag.F4.perm j)

theorem rootChar_reeTuple (a : ℕ) (b : Fin ReeTag.F4.tag.rank → Lˣ)
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (reeTuple a b) v = rootChar b (reePsi a v) := by
  unfold rootChar reeTuple reePsi
  rw [← Equiv.prod_comp (ReeTag.F4.perm)
    (fun j => b j ^ ((ReeTag.F4.relationExponent a j : ℤ) * v (ReeTag.F4.perm j)))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ReeTag.perm_perm, zpow_mul, zpow_natCast]

theorem scale_vec (j : Fin ReeTag.F4.tag.rank) :
    (ReeTag.F4.scale j : ℤ) = (![2, 2, 1, 1] : Fin 4 → ℤ) j := by
  fin_cases j <;> rfl

theorem relExp_eq_aux (a : ℕ) (j : Fin 4) :
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j =
      2 ^ a * (![2, 2, 1, 1] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) j) := by
  fin_cases j <;> simp [pow_succ]

theorem relExp_eq_two_pow_mul_scale (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    ((ReeTag.F4.relationExponent a j : ℕ) : ℤ) =
      2 ^ a * (ReeTag.F4.scale (ReeTag.F4.perm j) : ℤ) := by
  rw [relExp_vec, scale_vec, perm_vec]
  exact relExp_eq_aux a j

theorem reePsi_root (a : ℕ) {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    ∃ k : ℕ, reePsi a α = ((2 ^ k : ℕ) : ℤ) • ReeTag.F4.dualRoot α := by
  obtain ⟨hQ, hdiv, -⟩ := ReeTag.rootDualityCheck_spec hα
  have key : ∀ j, ReeTag.F4.quadForm α * ReeTag.F4.dualRoot α j =
      2 * (ReeTag.F4.scale (ReeTag.F4.perm j) : ℤ) * α (ReeTag.F4.perm j) := by
    intro j
    have h := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (hdiv j))
    have hsymm : ReeTag.F4.perm.symm j = ReeTag.F4.perm j :=
      (Equiv.symm_apply_eq ReeTag.F4.perm).2 (ReeTag.perm_perm _ _).symm
    rw [ReeTag.dualRoot]
    simp only [ReeTag.dualMapInt, hsymm] at h ⊢
    rw [h]
    ring
  rcases hQ with hQ | hQ
  · refine ⟨a, funext fun j => ?_⟩
    have h := key j
    rw [hQ] at h
    have h2 : ReeTag.F4.dualRoot α j =
        (ReeTag.F4.scale (ReeTag.F4.perm j) : ℤ) * α (ReeTag.F4.perm j) := by linarith
    simp only [reePsi, Pi.smul_apply, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [relExp_eq_two_pow_mul_scale, h2]
    ring
  · refine ⟨a + 1, funext fun j => ?_⟩
    have h := key j
    have hp : (2 * ReeTag.F4.prime : ℤ) = 4 := by simp [ReeTag.prime]
    rw [hQ, hp] at h
    have h2 : 2 * ReeTag.F4.dualRoot α j =
        (ReeTag.F4.scale (ReeTag.F4.perm j) : ℤ) * α (ReeTag.F4.perm j) := by linarith
    simp only [reePsi, Pi.smul_apply, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [relExp_eq_two_pow_mul_scale, pow_succ]
    linear_combination (-(2 : ℤ) ^ a) * h2

theorem rootChar_pow_prime_eq_one {p : ℕ} {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hbp : ∀ i, b i ^ p = 1) (v : Fin ReeTag.F4.tag.rank → ℤ) : rootChar b v ^ p = 1 := by
  unfold rootChar
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp i, one_zpow]

theorem eq_one_of_pow_two_pow_eq_one {x : Lˣ} {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxp : x ^ p = 1) (hxk : x ^ (2 ^ k) = 1) : x = 1 := by
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h := pow_gcd_eq_one.2 ⟨hxp, hxk⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

theorem rootChar_smul_root_eq_one_iff {a : ℕ} {b : Fin ReeTag.F4.tag.rank → Lˣ} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hbp : ∀ i, b i ^ p = 1) {w : WeylGroup ReeTag.F4.tag}
    (hw : ∀ v, rootChar b (w • v) = rootChar (reeTuple a b) v)
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    rootChar b (w • α) = 1 ↔ rootChar b (ReeTag.F4.dualRoot α) = 1 := by
  obtain ⟨k, hk⟩ := reePsi_root a hα
  rw [hw, rootChar_reeTuple, hk, rootChar_zsmul, zpow_natCast]
  constructor
  · intro h
    exact eq_one_of_pow_two_pow_eq_one hp hp2 (rootChar_pow_prime_eq_one hbp _) h
  · intro h
    rw [h, one_pow]

theorem mem_kernel_iff_smul_dualRoot {a : ℕ} {b : Fin ReeTag.F4.tag.rank → Lˣ} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hbp : ∀ i, b i ^ p = 1) {w : WeylGroup ReeTag.F4.tag}
    (hw : ∀ v, rootChar b (w • v) = rootChar (reeTuple a b) v)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) :
    w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b := by
  have hd : IsRoot ReeTag.F4.tag (ReeTag.F4.dualRoot β) := ReeTag.isRoot_dualRoot hβ
  have hdd : ReeTag.F4.dualRoot (ReeTag.F4.dualRoot β) = β := ReeTag.dualRoot_dualRoot hβ
  show IsRoot ReeTag.F4.tag _ ∧ _ ↔ IsRoot ReeTag.F4.tag _ ∧ _
  rw [rootChar_smul_root_eq_one_iff hp hp2 hbp hw hd, hdd]
  exact ⟨fun h => ⟨hβ, h.2⟩, fun h => ⟨IsRoot.smul hd w, h.2⟩⟩

theorem quadForm_smul (w : WeylGroup ReeTag.F4.tag) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    ReeTag.F4.quadForm (w • v) = ReeTag.F4.quadForm v := by
  rw [ReeTag.quadForm_eq_iform, ReeTag.quadForm_eq_iform]
  exact iform_smul w v v

theorem lengthParam_smul (w : WeylGroup ReeTag.F4.tag) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    ReeTag.F4.lengthParam (w • v) = ReeTag.F4.lengthParam v := by
  simp only [ReeTag.lengthParam, quadForm_smul]

theorem smul_mem_longRoots (w : WeylGroup ReeTag.F4.tag) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ ReeTag.F4.longRoots) : w • α ∈ ReeTag.F4.longRoots :=
  ⟨IsRoot.smul hα.1 w, by rw [lengthParam_smul]; exact hα.2⟩

theorem smul_mem_shortRoots (w : WeylGroup ReeTag.F4.tag) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ ReeTag.F4.shortRoots) : w • α ∈ ReeTag.F4.shortRoots :=
  ⟨IsRoot.smul hα.1 w, by rw [lengthParam_smul]; exact hα.2⟩

theorem dualRoot_mem_longRoots {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ ∈ ReeTag.F4.shortRoots) :
    ReeTag.F4.dualRoot γ ∈ ReeTag.F4.longRoots := by
  obtain ⟨δ, hδ, rfl⟩ := (ReeTag.bijOn_dualRoot ReeTag.F4).surjOn hγ
  rwa [ReeTag.dualRoot_dualRoot hδ.1]

theorem ncard_long_eq_ncard_short {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (w : WeylGroup ReeTag.F4.tag)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S)) :
    (S ∩ ReeTag.F4.longRoots).ncard = (S ∩ ReeTag.F4.shortRoots).ncard := by
  have hinj : ∀ β₁ β₂ : Fin ReeTag.F4.tag.rank → ℤ, IsRoot ReeTag.F4.tag β₁ →
      IsRoot ReeTag.F4.tag β₂ →
      w • ReeTag.F4.dualRoot β₁ = w • ReeTag.F4.dualRoot β₂ → β₁ = β₂ := by
    intro β₁ β₂ h₁ h₂ h
    have h' := MulAction.injective w h
    rw [← ReeTag.dualRoot_dualRoot h₁, h', ReeTag.dualRoot_dualRoot h₂]
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn (fun β => w • ReeTag.F4.dualRoot β)
      (fun β hβ => ⟨(hst β hβ.2.1).2 hβ.1,
        smul_mem_shortRoots w ((ReeTag.bijOn_dualRoot ReeTag.F4).mapsTo hβ.2)⟩)
      (fun β₁ h₁ β₂ h₂ h => hinj _ _ h₁.2.1 h₂.2.1 h)
      ((finite_setOf_isRoot ReeTag.F4.tag).subset fun v hv => hv.2.1)
  · refine Set.ncard_le_ncard_of_injOn (fun β => w • ReeTag.F4.dualRoot β)
      (fun β hβ => ⟨(hst β hβ.2.1).2 hβ.1,
        smul_mem_longRoots w (dualRoot_mem_longRoots hβ.2)⟩)
      (fun β₁ h₁ β₂ h₂ h => hinj _ _ h₁.2.1 h₂.2.1 h)
      ((finite_setOf_isRoot ReeTag.F4.tag).subset fun v hv => hv.2.1)

end Psi

section Count

@[expose] def kernelCount (J : Finset (Fin ReeTag.F4.tag.rank)) (q : ℤ) : ℕ :=
  ((rootFinset ReeTag.F4.tag).filter fun α : Fin ReeTag.F4.tag.rank → ℤ =>
    (∀ i, i ∉ J → α i = 0) ∧ ReeTag.F4.quadForm α = q).card

@[expose] def BalancedSupport (J : Finset (Fin ReeTag.F4.tag.rank)) : Prop :=
  J = ∅ ∨ (∀ i, i ∈ J ↔ i.val = 0 ∨ i.val = 2) ∨ (∀ i, i ∈ J ↔ i.val = 0 ∨ i.val = 3) ∨
    (∀ i, i ∈ J ↔ i.val = 1 ∨ i.val = 3) ∨ (∀ i, i ∈ J ↔ i.val = 1 ∨ i.val = 2)

instance (J : Finset (Fin ReeTag.F4.tag.rank)) : Decidable (BalancedSupport J) := by
  unfold BalancedSupport
  infer_instance

theorem balanced_cases : ∀ J : Finset (Fin ReeTag.F4.tag.rank), J ≠ Finset.univ →
    kernelCount J 4 = kernelCount J 2 → BalancedSupport J := by
  decide +kernel


theorem ncard_parabolic_inter_long (J : Finset (Fin ReeTag.F4.tag.rank)) :
    (parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩
      ReeTag.F4.longRoots).ncard = kernelCount J 4 := by
  have h : parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩
      ReeTag.F4.longRoots = ↑((rootFinset ReeTag.F4.tag).filter
        fun α : Fin ReeTag.F4.tag.rank → ℤ => (∀ i, i ∉ J → α i = 0) ∧
          ReeTag.F4.quadForm α = 4) := by
    rw [ReeTag.longRoots_eq]
    ext α
    simp only [parabolicRoots, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter,
      mem_rootFinset, Finset.mem_coe]
    have h4 : (2 * (ReeTag.F4.prime : ℤ)) = 4 := by simp [ReeTag.prime]
    rw [h4]
    tauto
  rw [h, Set.ncard_coe_finset]
  rfl

theorem ncard_parabolic_inter_short (J : Finset (Fin ReeTag.F4.tag.rank)) :
    (parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩
      ReeTag.F4.shortRoots).ncard = kernelCount J 2 := by
  have h : parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩
      ReeTag.F4.shortRoots = ↑((rootFinset ReeTag.F4.tag).filter
        fun α : Fin ReeTag.F4.tag.rank → ℤ => (∀ i, i ∉ J → α i = 0) ∧
          ReeTag.F4.quadForm α = 2) := by
    rw [ReeTag.shortRoots_eq]
    ext α
    simp only [parabolicRoots, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter,
      mem_rootFinset, Finset.mem_coe]
    tauto
  rw [h, Set.ncard_coe_finset]
  rfl

theorem balancedSupport_of_stable {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w u : WeylGroup ReeTag.F4.tag)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    {J : Finset (Fin ReeTag.F4.tag.rank)}
    (hu : (fun α => u • α) '' S =
      parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    (hJ : J ≠ Finset.univ) : BalancedSupport J := by
  have himg : ∀ T : Set (Fin ReeTag.F4.tag.rank → ℤ), (T = ReeTag.F4.longRoots ∨
      T = ReeTag.F4.shortRoots) →
      (parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩ T).ncard =
        (S ∩ T).ncard := by
    intro T hT
    rw [← hu]
    have himg : (fun α => u • α) '' S ∩ T = (fun α => u • α) '' (S ∩ T) := by
      ext β
      constructor
      · rintro ⟨⟨α, hα, rfl⟩, hβ⟩
        refine ⟨α, ⟨hα, ?_⟩, rfl⟩
        rcases hT with rfl | rfl
        · exact ⟨hS α hα, by rw [← lengthParam_smul u α]; exact hβ.2⟩
        · exact ⟨hS α hα, by rw [← lengthParam_smul u α]; exact hβ.2⟩
      · rintro ⟨α, ⟨hα, hαT⟩, rfl⟩
        refine ⟨⟨α, hα, rfl⟩, ?_⟩
        rcases hT with rfl | rfl
        · exact smul_mem_longRoots u hαT
        · exact smul_mem_shortRoots u hαT
    rw [himg]
    exact Set.ncard_image_of_injective _ (MulAction.injective u)
  have h1 := himg _ (Or.inl rfl)
  have h2 := himg _ (Or.inr rfl)
  have h3 := ncard_long_eq_ncard_short (S := S) w hst
  rw [ncard_parabolic_inter_long] at h1
  rw [ncard_parabolic_inter_short] at h2
  exact balanced_cases J hJ (by rw [h1, h2, h3])

end Count

section Bridge

variable {L : Type} [Field L]

theorem rootChar_zetaPow_eq_one_iff_charVal {τ : Tag} {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (z : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ζ ^ (z i).val) v = 1 ↔ CFSG.RankThree.E6.charVal z v = 0 := by
  have h : rootChar (fun i => ζ ^ (z i).val) v = ζ ^ (∑ i, v i * ((z i).val : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum ζ Finset.univ (fun i => v i * ((z i).val : ℤ))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, CFSG.RankThree.E6.charVal]
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem rootCharKernel_zetaPow_eq {τ : Tag} {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (z : Fin τ.rank → ZMod p) :
    rootCharKernel (fun i => ζ ^ (z i).val) = rootKernel z := by
  ext α
  exact and_congr_right fun _ => rootChar_zetaPow_eq_one_iff_charVal hζ z α

theorem exists_balanced_conj {a : ℕ} [CharP L 2] [IsAlgClosed L] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {b : Fin ReeTag.F4.tag.rank → Lˣ} (hbp : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1)
    {w : WeylGroup ReeTag.F4.tag}
    (hw : ∀ v, rootChar b (w • v) = rootChar (reeTuple a b) v) :
    ∃ (u : WeylGroup ReeTag.F4.tag) (J : Finset (Fin ReeTag.F4.tag.rank)), BalancedSupport J ∧
      (fun α => u • α) '' rootCharKernel b =
        parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : L) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff L 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hp0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  lift ζ₀ to Lˣ using hζ₀.isUnit hp.ne_zero
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  have hk : ∀ i, ∃ k < p, ζ₀ ^ k = b i := fun i =>
    hζ₀.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).2 (hbp i))
  choose k hkp hkb using hk
  set z : Fin ReeTag.F4.tag.rank → ZMod p := fun i => (k i : ZMod p) with hz
  have hzval : ∀ i, (z i).val = k i := fun i => ZMod.val_natCast_of_lt (hkp i)
  have hbz : b = fun i => ζ₀ ^ (z i).val := by
    funext i
    rw [hzval, hkb]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hb1
    rw [hbz]
    funext i
    have : z i = 0 := congrFun h0 i
    simp [this]
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  obtain ⟨u, J, hΦ, hJ⟩ := KF4.exists_smul_rootKernel_eq_parabolicRoots hordW z
  have hker : rootCharKernel b = rootKernel z := by
    rw [hbz]
    exact rootCharKernel_zetaPow_eq hζ₀ z
  have hJfin : J.Finite := Set.toFinite J
  have hJc : (↑hJfin.toFinset : Set (Fin ReeTag.F4.tag.rank)) = J := hJfin.coe_toFinset
  have hΦ' : (fun α => u • α) '' rootCharKernel b =
      parabolicRoots ReeTag.F4.tag (↑hJfin.toFinset : Set (Fin ReeTag.F4.tag.rank)) := by
    rw [hker, hJc]
    exact hΦ
  refine ⟨u, hJfin.toFinset, ?_, hΦ'⟩
  refine balancedSupport_of_stable (S := rootCharKernel b) (fun α hα => hα.1) w u
    (fun β hβ => mem_kernel_iff_smul_dualRoot hp hp2 hbp hw hβ) hΦ' ?_
  intro h
  apply hJ hz0
  rw [← hJc, h, Finset.coe_univ]

end Bridge

end CFSG.RankThree.PartOne.KLR
