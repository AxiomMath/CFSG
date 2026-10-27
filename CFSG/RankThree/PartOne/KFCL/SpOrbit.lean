module

public import CFSG.RankThree.PartOne.KFCL.SpBlocks
public import CFSG.RankThree.PartOne.KFCL.OrbitRoot
public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Transport

variable [CharP K 2]

theorem mem_centralizer_map_conj_iff {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n)
    {S : Subgroup (StatedSp n K)} {x : StatedSp n K} :
    x ∈ Subgroup.centralizer ((S.map (MulAut.conj (permSp τ hτ)).toMonoidHom : Subgroup (StatedSp n K)) :
      Set (StatedSp n K)) ↔ cj hτ x ∈ Subgroup.centralizer (S : Set (StatedSp n K)) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have := h _ (Subgroup.mem_map.2 ⟨s, hs, rfl⟩)
    show s * ((permSp τ hτ)⁻¹ * x * permSp τ hτ) = ((permSp τ hτ)⁻¹ * x * permSp τ hτ) * s
    have h2 : permSp τ hτ * s * (permSp τ hτ)⁻¹ * x = x * (permSp τ hτ * s * (permSp τ hτ)⁻¹) := this
    calc s * ((permSp τ hτ)⁻¹ * x * permSp τ hτ)
        = (permSp τ hτ)⁻¹ * ((permSp τ hτ * s * (permSp τ hτ)⁻¹) * x) * permSp τ hτ := by group
      _ = (permSp τ hτ)⁻¹ * (x * (permSp τ hτ * s * (permSp τ hτ)⁻¹)) * permSp τ hτ := by rw [h2]
      _ = ((permSp τ hτ)⁻¹ * x * permSp τ hτ) * s := by group
  · intro h b hb
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
    have := h s hs
    have h2 : s * ((permSp τ hτ)⁻¹ * x * permSp τ hτ) = ((permSp τ hτ)⁻¹ * x * permSp τ hτ) * s := this
    show permSp τ hτ * s * (permSp τ hτ)⁻¹ * x = x * (permSp τ hτ * s * (permSp τ hτ)⁻¹)
    calc permSp τ hτ * s * (permSp τ hτ)⁻¹ * x
        = permSp τ hτ * (s * ((permSp τ hτ)⁻¹ * x * permSp τ hτ)) * (permSp τ hτ)⁻¹ := by group
      _ = permSp τ hτ * (((permSp τ hτ)⁻¹ * x * permSp τ hτ) * s) * (permSp τ hτ)⁻¹ := by rw [h2]
      _ = x * (permSp τ hτ * s * (permSp τ hτ)⁻¹) := by group

theorem map_conj_suppGroup {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (S : Set (Fin n ⊕ Fin n)) :
    (suppGroup (K := K) S).map (MulAut.conj (permSp τ hτ)).toMonoidHom = suppGroup (τ '' S) := by
  ext x
  rw [mem_map_conj_permSp_iff, mem_suppGroup, mem_suppGroup]
  constructor
  · intro h a' b' hab'
    obtain ⟨a, rfl⟩ := τ.surjective a'
    obtain ⟨b, rfl⟩ := τ.surjective b'
    have := h a b (fun hh => hab' ⟨⟨a, hh.1, rfl⟩, ⟨b, hh.2, rfl⟩⟩)
    rw [mat_cj_apply] at this
    rw [this]
    simp [Matrix.one_apply]
  · intro h a b hab
    rw [mat_cj_apply]
    have := h (τ a) (τ b) (fun hh => hab ⟨by
      obtain ⟨a₀, ha₀, he⟩ := hh.1
      rwa [← τ.injective he], by
      obtain ⟨b₀, hb₀, he⟩ := hh.2
      rwa [← τ.injective he]⟩)
    rw [this]
    simp [Matrix.one_apply]

end Transport

section TorZ

variable {p : ℕ}

@[expose] def tv (u : Fin 3 → ℤ) : Fin 3 ⊕ Fin 3 → ℤ := Sum.elim u (fun i => - u i)

variable (ζ : Kˣ) (u : Fin 3 → ℤ)

@[expose] noncomputable def torZ : StatedSp 3 K :=
  CFSG.LieType.Universal.Symplectic.equivStatedSp 3 K (TauCeti.GLSymplecticFin.diagonal (fun i => ζ ^ u i))

theorem mat_torZ_apply (c : Fin 3 ⊕ Fin 3) :
    mat 3 K (torZ ζ u) c c = (ζ : K) ^ tv u c := by
  unfold torZ
  rw [mat_equiv_diagonal, Matrix.diagonal_apply_eq]
  rcases c with i | i
  · simp [tv]
  · simp [tv, _root_.zpow_neg]

theorem mat_torZ_ne {a b : Fin 3 ⊕ Fin 3} (hab : a ≠ b) : mat 3 K (torZ ζ u) a b = 0 := by
  unfold torZ
  rw [mat_equiv_diagonal, Matrix.diagonal_apply_ne _ hab]

theorem torZ_mem (hζ : ζ ^ p = 1) : torZ ζ u ∈ spTorus p 3 K := by
  refine ⟨fun i => ((ζ ^ u i : Kˣ) : K), fun i => ?_, ?_⟩
  · have : (ζ ^ u i) ^ p = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hζ, _root_.one_zpow]
    simpa using congrArg (fun x : Kˣ => (x : K)) this
  · unfold torZ
    rw [mat_equiv_diagonal]
    congr 1
    funext c
    rcases c with i | i <;> simp [Units.val_inv_eq_inv_val]

end TorZ

@[expose] def u₁ : Fin 3 → ℤ := ![0, 1, 2]

@[expose] def u₂ : Fin 3 → ℤ := ![1, 1, 2]

theorem tv_u₁_eq_zero (a : Fin 3 ⊕ Fin 3) : tv u₁ a = 0 ↔ a = Sum.inl 0 ∨ a = Sum.inr 0 := by
  revert a
  decide

theorem tv_u₁_ne (a b : Fin 3 ⊕ Fin 3) (hab : a ≠ b) (hb : b ≠ par a) : tv u₁ a ≠ tv u₁ b := by
  revert a b
  decide

theorem tv_u₂_ne_zero (a : Fin 3 ⊕ Fin 3) : tv u₂ a ≠ 0 := by
  revert a
  decide

theorem tv_u₂_eq (a b : Fin 3 ⊕ Fin 3) (hab : a ≠ b) (hb : b ≠ par a) (h : tv u₂ a = tv u₂ b) :
    (a = Sum.inl 0 ∧ b = Sum.inl 1) ∨ (a = Sum.inl 1 ∧ b = Sum.inl 0) ∨
      (a = Sum.inr 0 ∧ b = Sum.inr 1) ∨ (a = Sum.inr 1 ∧ b = Sum.inr 0) := by
  revert a b
  decide

theorem tv_u₁_abs_le (a : Fin 3 ⊕ Fin 3) : |tv u₁ a| ≤ 2 := by
  revert a
  decide

theorem tv_u₂_abs_le (a : Fin 3 ⊕ Fin 3) : |tv u₂ a| ≤ 2 := by
  revert a
  decide

section ConjElt

variable [CharP K 2]

theorem mat_conj_perm {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x : StatedSp n K) :
    mat n K (permSp τ hτ * x * (permSp τ hτ)⁻¹) = (mat n K x).submatrix τ.symm τ.symm := by
  have h1 : permSp (K := K) τ hτ * x * (permSp τ hτ)⁻¹ = cj ((Hp n).inv_mem hτ) x := by
    unfold cj
    rw [← permSp_inv hτ, inv_inv]
  rw [h1]
  ext a b
  rw [mat_cj_apply]
  simp [Equiv.Perm.inv_def]

theorem mat_conj_elt {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3) (c : K) :
    mat 3 K (permSp τ hτ * elt r c * (permSp τ hτ)⁻¹) =
      1 + c • (E K r).submatrix τ.symm τ.symm := by
  rw [mat_conj_perm, mat_elt]
  ext a b
  simp [Matrix.one_apply]

theorem mat_conj_elt_diff {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (i j : Fin 3) (hij : i ≠ j)
    (c : K) :
    mat 3 K (permSp τ hτ * elt (.difference i j hij) c * (permSp τ hτ)⁻¹) =
      1 + c • (Matrix.single (τ (Sum.inl i)) (τ (Sum.inl j)) 1 -
        Matrix.single (par (τ (Sum.inl j))) (par (τ (Sum.inl i))) 1) := by
  rw [mat_conj_elt]
  have h1 : τ (Sum.inr j) = par (τ (Sum.inl j)) := by rw [← hτ]; rfl
  have h2 : τ (Sum.inr i) = par (τ (Sum.inl i)) := by rw [← hτ]; rfl
  congr 2
  ext a b
  simp only [E, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.single_apply, Equiv.eq_symm_apply,
    h1.symm, h2.symm]

@[expose] def FourCases (τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) : Prop :=
  (τ (Sum.inl 0) = Sum.inl 0 ∧ τ (Sum.inl 1) = Sum.inl 1) ∨
  (τ (Sum.inl 0) = Sum.inl 1 ∧ τ (Sum.inl 1) = Sum.inl 0) ∨
  (τ (Sum.inl 0) = Sum.inr 0 ∧ τ (Sum.inl 1) = Sum.inr 1) ∨
  (τ (Sum.inl 0) = Sum.inr 1 ∧ τ (Sum.inl 1) = Sum.inr 0)

theorem conj_elt_diff_mem_Ss {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (h : FourCases τ) (c : K) :
    permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ ∈ Ss K ∧
    permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ ∈ Ss K := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · constructor
    · have : permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ = elt (.difference 0 1 h01) c := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact ⟨sl2Upper c, shortBlock_sl2Upper h01 c⟩
    · have : permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ =
          elt (.difference 1 0 h01.symm) c := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact ⟨sl2Lower c, shortBlock_sl2Lower h01 c⟩
  · constructor
    · have : permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ = elt (.difference 1 0 h01.symm) c := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact ⟨sl2Lower c, shortBlock_sl2Lower h01 c⟩
    · have : permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ =
          elt (.difference 0 1 h01) c := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact ⟨sl2Upper c, shortBlock_sl2Upper h01 c⟩
  · constructor
    · have : permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ =
          elt (.difference 1 0 h01.symm) (-c) := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
        module
      rw [this]
      exact ⟨sl2Lower (-c), shortBlock_sl2Lower h01 (-c)⟩
    · have : permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ =
          elt (.difference 0 1 h01) (-c) := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
        module
      rw [this]
      exact ⟨sl2Upper (-c), shortBlock_sl2Upper h01 (-c)⟩
  · constructor
    · have : permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ =
          elt (.difference 0 1 h01) (-c) := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
        module
      rw [this]
      exact ⟨sl2Upper (-c), shortBlock_sl2Upper h01 (-c)⟩
    · have : permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ =
          elt (.difference 1 0 h01.symm) (-c) := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
        module
      rw [this]
      exact ⟨sl2Lower (-c), shortBlock_sl2Lower h01 (-c)⟩

theorem conj_shortBlock_mem_Ss {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (h : FourCases τ)
    (A : SL(2, K)) : permSp τ hτ * shortBlock K h01 A * (permSp τ hτ)⁻¹ ∈ Ss K := by
  refine Subgroup.closure_induction
    (p := fun A _ => permSp τ hτ * shortBlock K h01 A * (permSp τ hτ)⁻¹ ∈ Ss K) ?_ ?_ ?_ ?_
    (mem_closure_sl2 A)
  · rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [shortBlock_sl2Upper]
      exact (conj_elt_diff_mem_Ss hτ h c).1
    · rw [shortBlock_sl2Lower]
      exact (conj_elt_diff_mem_Ss hτ h c).2
  · simp
  · intro x y _ _ hx hy
    have : permSp τ hτ * shortBlock K h01 (x * y) * (permSp τ hτ)⁻¹ =
        (permSp τ hτ * shortBlock K h01 x * (permSp τ hτ)⁻¹) *
          (permSp τ hτ * shortBlock K h01 y * (permSp τ hτ)⁻¹) := by
      rw [map_mul]
      group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : permSp τ hτ * shortBlock K h01 x⁻¹ * (permSp τ hτ)⁻¹ =
        (permSp τ hτ * shortBlock K h01 x * (permSp τ hτ)⁻¹)⁻¹ := by
      rw [map_inv]
      group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem Ss_map_conj_eq [Finite K] {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (h : FourCases τ) :
    (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom = Ss K := by
  have hle : (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom ≤ Ss K := by
    rintro _ ⟨s, ⟨A, rfl⟩, rfl⟩
    exact conj_shortBlock_mem_Ss hτ h A
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj (permSp τ hτ)).injective]

theorem Sl_map_conj_eq {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3)
    (h : τ (Sum.inl 0) = Sum.inl 0 ∨ τ (Sum.inl 0) = Sum.inr 0) :
    (Sl K).map (MulAut.conj (permSp τ hτ)).toMonoidHom = Sl K := by
  rw [Sl, range_longBlock, map_conj_suppGroup]
  congr 1
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases mem_coords.1 hd with rfl | rfl
    · rcases h with h | h <;> rw [h] <;> simp [coords]
    · have : τ (Sum.inr 0) = par (τ (Sum.inl 0)) := by rw [← hτ]; rfl
      rcases h with h | h <;> rw [this, h] <;> simp [coords, par]
  · intro hc
    rcases mem_coords.1 hc with rfl | rfl
    · rcases h with h | h
      · exact ⟨Sum.inl 0, inl_mem_coords 0, h⟩
      · exact ⟨Sum.inr 0, inr_mem_coords 0, by rw [show τ (Sum.inr 0) = par (τ (Sum.inl 0)) by rw [← hτ]; rfl, h]; rfl⟩
    · rcases h with h | h
      · exact ⟨Sum.inr 0, inr_mem_coords 0, by rw [show τ (Sum.inr 0) = par (τ (Sum.inl 0)) by rw [← hτ]; rfl, h]; rfl⟩
      · exact ⟨Sum.inl 0, inl_mem_coords 0, h⟩

end ConjElt

section Hyper

variable {p : ℕ}

theorem zpow_eq_one_iff_of_small {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℤ} (hm : |m| < p) :
    ζ ^ m = 1 ↔ m = 0 := by
  rw [hζ.zpow_eq_one_iff_dvd]
  constructor
  · intro h
    exact Int.eq_zero_of_abs_lt_dvd h hm
  · rintro rfl
    exact dvd_zero _

theorem zpow_eq_zpow_iff_of_small {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0) {m m' : ℤ}
    (hm : |m - m'| < p) : ζ ^ m = ζ ^ m' ↔ m = m' := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp
  constructor
  · intro h
    have h1 : ζ ^ (m - m') = 1 := by
      rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)]
    have := (zpow_eq_one_iff_of_small hζ hm).1 h1
    omega
  · rintro rfl
    rfl

variable [CharP K 2]

theorem abs_tv_sub_lt (hp5 : 5 ≤ p) {u v : Fin 3 → ℤ} (hu : ∀ a, |tv u a| ≤ 2) (hv : ∀ a, |tv v a| ≤ 2)
    (a b : Fin 3 ⊕ Fin 3) : |tv u a - tv v b| < p := by
  have h1 := hu a
  have h2 := hv b
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> omega

variable (K) in
theorem isSimpleGroup_Sl (h4 : 4 ≤ Nat.card K) : IsSimpleGroup ↥(Sl K) := by
  have := L4.sl2_isSimpleGroup (K := K) h4
  exact (MonoidHom.ofInjective (longBlock_injective (K := K) (n := 3) 0)).symm.isSimpleGroup

variable (K) in
theorem isSimpleGroup_Ss (h4 : 4 ≤ Nat.card K) : IsSimpleGroup ↥(Ss K) := by
  have := L4.sl2_isSimpleGroup (K := K) h4
  exact (MonoidHom.ofInjective (shortBlock_injective (K := K) (n := 3) h01)).symm.isSimpleGroup

@[expose] def SpStd (K : Type) [Field K] : Set (Subgroup (StatedSp 3 K)) := {Sl K, Ss K}

theorem hsimple_Sp (h4 : 4 ≤ Nat.card K) :
    ∀ S ∈ SpStd K, ∀ N : Subgroup (StatedSp 3 K), N ≤ S → (N.subgroupOf S).Normal → N = ⊥ ∨ N = S := by
  intro S hS N hN hnorm
  rcases hS with rfl | rfl
  · have := isSimpleGroup_Sl K h4
    exact L4.eq_bot_or_eq_of_normal_subgroupOf _ N hN hnorm
  · have := isSimpleGroup_Ss K h4
    exact L4.eq_bot_or_eq_of_normal_subgroupOf _ N hN hnorm

variable {ζ : Kˣ}

omit [CharP K 2] in
theorem units_pow_eq_one (hζ : IsPrimitiveRoot (ζ : K) p) : ζ ^ p = 1 :=
  Units.ext (by simpa using hζ.pow_eq_one)

@[expose] def u₀ : Fin 3 → ℤ := ![1, 0, 0]

omit [CharP K 2] in
theorem hne_std (hp : p.Prime) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∀ S ∈ SpStd K, ¬ spTorus p 3 K ≤ Subgroup.centralizer (S : Set (StatedSp 3 K)) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmem : torZ ζ u₀ ∈ spTorus p 3 K := torZ_mem ζ u₀ (units_pow_eq_one hζ)
  have h00 : mat 3 K (torZ ζ u₀) (Sum.inl 0) (Sum.inl 0) = (ζ : K) := by
    rw [mat_torZ_apply]
    simp [tv, u₀]
  have h11 : mat 3 K (torZ ζ u₀) (Sum.inl 1) (Sum.inl 1) = 1 := by
    rw [mat_torZ_apply]
    simp [tv, u₀]
  have hne1 : (ζ : K) ≠ 1 := hζ.ne_one (by omega)
  rintro S (rfl | rfl) hle
  · have := (mem_centralizer_Sl_iff hodd hmem).1 (hle hmem)
    rw [h00] at this
    exact hne1 this
  · have := (mem_centralizer_Ss_iff hmem).1 (hle hmem)
    rw [h00, h11] at this
    exact hne1 this

theorem tau_pair_ne {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    τ (Sum.inl 0) ≠ τ (Sum.inl 1) ∧ τ (Sum.inl 1) ≠ par (τ (Sum.inl 0)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := τ.injective h
    exact absurd (Sum.inl_injective this) (by decide)
  · rw [← hτ] at h
    have := τ.injective h
    exact absurd this (by decide)

omit [CharP K 2] in
theorem torZ_eq_one_iff (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p) {u : Fin 3 → ℤ}
    (hu : ∀ a, |tv u a| ≤ 2) (a : Fin 3 ⊕ Fin 3) : mat 3 K (torZ ζ u) a a = 1 ↔ tv u a = 0 := by
  rw [mat_torZ_apply]
  refine zpow_eq_one_iff_of_small hζ ?_
  have h := hu a
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> omega

omit [CharP K 2] in
theorem torZ_eq_iff (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p) {u : Fin 3 → ℤ}
    (hu : ∀ a, |tv u a| ≤ 2) (a b : Fin 3 ⊕ Fin 3) :
    mat 3 K (torZ ζ u) a a = mat 3 K (torZ ζ u) b b ↔ tv u a = tv u b := by
  rw [mat_torZ_apply, mat_torZ_apply]
  refine zpow_eq_zpow_iff_of_small hζ (by omega) ?_
  have h1 := hu a
  have h2 := hu b
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> omega

theorem hred_Sp [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∀ S ∈ SpStd K, ∀ B' ∈ blockOrbit (spWeyl 3 K) (SpStd K),
      spTorus p 3 K ⊓ Subgroup.centralizer (S : Set (StatedSp 3 K)) =
        spTorus p 3 K ⊓ Subgroup.centralizer (B' : Set (StatedSp 3 K)) → B' = S := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpz := units_pow_eq_one hζ
  intro S hS B' hB' hD
  obtain ⟨w, hw, S', hS', rfl⟩ := hB'
  obtain ⟨τ, hτ, rfl⟩ := mem_spWeyl_iff.1 hw
  obtain ⟨hab, hbpar⟩ := tau_pair_ne hτ
  have key : ∀ t, t ∈ spTorus p 3 K → t ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) →
      cj hτ t ∈ Subgroup.centralizer (S' : Set (StatedSp 3 K)) := by
    intro t ht htS
    have : t ∈ spTorus p 3 K ⊓ Subgroup.centralizer ((S'.map (MulAut.conj (permSp τ hτ)).toMonoidHom :
        Subgroup (StatedSp 3 K)) : Set (StatedSp 3 K)) := by
      rw [← hD]
      exact ⟨ht, htS⟩
    exact (mem_centralizer_map_conj_iff hτ).1 this.2
  have hcjT : ∀ t, t ∈ spTorus p 3 K → cj hτ t ∈ spTorus p 3 K := fun t ht => cj_mem_spTorus hτ ht
  have ht1 : torZ ζ u₁ ∈ spTorus p 3 K := torZ_mem ζ u₁ hpz
  have ht2 : torZ ζ u₂ ∈ spTorus p 3 K := torZ_mem ζ u₂ hpz
  have hc1 : torZ ζ u₁ ∈ Subgroup.centralizer (Sl K : Set (StatedSp 3 K)) :=
    (mem_centralizer_Sl_iff hodd ht1).2
      ((torZ_eq_one_iff hp5 hζ tv_u₁_abs_le _).2 ((tv_u₁_eq_zero _).2 (Or.inl rfl)))
  have hc2 : torZ ζ u₂ ∈ Subgroup.centralizer (Ss K : Set (StatedSp 3 K)) :=
    (mem_centralizer_Ss_iff ht2).2 ((torZ_eq_iff hp5 hζ tv_u₂_abs_le _ _).2 (by simp [tv, u₂]))
  rcases hS with rfl | rfl <;> rcases hS' with rfl | rfl
  ·
    have h1 := (mem_centralizer_Sl_iff hodd (hcjT _ ht1)).1 (key _ ht1 hc1)
    rw [mat_cj_apply] at h1
    exact Sl_map_conj_eq hτ ((tv_u₁_eq_zero _).1 ((torZ_eq_one_iff hp5 hζ tv_u₁_abs_le _).1 h1))
  ·
    have h1 := (mem_centralizer_Ss_iff (hcjT _ ht1)).1 (key _ ht1 hc1)
    rw [mat_cj_apply, mat_cj_apply] at h1
    exact absurd ((torZ_eq_iff hp5 hζ tv_u₁_abs_le _ _).1 h1) (tv_u₁_ne _ _ hab hbpar)
  ·
    have h1 := (mem_centralizer_Sl_iff hodd (hcjT _ ht2)).1 (key _ ht2 hc2)
    rw [mat_cj_apply] at h1
    exact absurd ((torZ_eq_one_iff hp5 hζ tv_u₂_abs_le _).1 h1) (tv_u₂_ne_zero _)
  ·
    have h1 := (mem_centralizer_Ss_iff (hcjT _ ht2)).1 (key _ ht2 hc2)
    rw [mat_cj_apply, mat_cj_apply] at h1
    exact Ss_map_conj_eq hτ
      (tv_u₂_eq _ _ hab hbpar ((torZ_eq_iff hp5 hζ tv_u₂_abs_le _ _).1 h1))

end Hyper

end CFSG.RankThree.PartOne.KFCL.Sp
