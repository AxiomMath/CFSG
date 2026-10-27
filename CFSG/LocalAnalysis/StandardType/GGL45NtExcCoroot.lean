module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcPSatData

public section

namespace CFSG.HardMathSupport.C14Coroot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.C14Idx
open scoped Matrix

@[expose] def phi (τ : Tag) : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun x j := 2 * iform x (Pi.single j 1)
  map_zero' := by
    funext j
    simp [iform]
  map_add' x y := by
    funext j
    show 2 * iform (x + y) (Pi.single j 1) = 2 * iform x (Pi.single j 1) + 2 * iform y (Pi.single j 1)
    simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring

theorem phi_eq_mulVec {τ : Tag}
    (x : Fin τ.rank → ℤ) :
    phi τ x = (Matrix.of fun j k => 2 * τ.symmetrizer j j * τ.cartan j k) *ᵥ x := by
  funext j
  change 2 * iform x (Pi.single j 1) = _
  rw [iform_single_right]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem phi_root {τ : Tag}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : phi τ β = iform β β • corootVec β := by
  funext j
  change 2 * iform β (Pi.single j 1) = iform β β * corootPair β (Pi.single j 1)
  rw [← corootPair_mul hβ, mul_comm]

theorem iform_self_of_isRoot {τ : Tag}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ i, iform β β = 2 * τ.symmetrizer i i := by
  induction hβ with
  | basis j => exact ⟨j, iform_single_single j⟩
  | reflect i _ ih => rwa [iform_reflect]

theorem corootPSat_of_rootPSat {τ : Tag}
    {p : ℕ} (hp : p.Prime) (Ψ : Set (Fin τ.rank → ℤ))
    (hΨ : ∀ β ∈ Ψ, IsRoot τ β) (C : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (N : ℕ)
    (hR : ∀ y, phi τ (C *ᵥ y) = (N : ℤ) • y) (hL : ∀ x, C *ᵥ phi τ x = (N : ℤ) • x)
    (m : ℕ) (hm : ∀ β ∈ Ψ, iform β β ∣ m)
    (hroot : ∀ v, p • v ∈ AddSubgroup.closure Ψ → v ∈ AddSubgroup.closure Ψ)
    (hpm : ¬ p ∣ m * N) : CorootPSaturated p Ψ := by
  intro y hy
  set Λ := AddSubgroup.closure Ψ
  set Λc := AddSubgroup.closure (corootVec '' Ψ)
  have hN : (N : ℤ) ≠ 0 := by
    rintro h
    exact hpm (by rw [Int.natCast_eq_zero.1 h, mul_zero]; exact dvd_zero p)
  have hinj : Function.Injective (phi τ) := by
    intro u v huv
    have := congrArg (C *ᵥ ·) huv
    simp only [hL] at this
    exact smul_right_injective _ hN this
  have h1 : Λ ≤ Λc.comap (phi τ) := by
    rw [AddSubgroup.closure_le]
    intro β hβ
    change phi τ β ∈ Λc
    rw [phi_root (hΨ β hβ)]
    exact zsmul_mem (AddSubgroup.subset_closure (Set.mem_image_of_mem corootVec hβ)) _
  have h2 : ∀ w ∈ Λc, (m : ℤ) • w ∈ Λ.map (phi τ) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, rfl⟩ := hw
      obtain ⟨k, hk⟩ := hm β hβ
      refine ⟨k • β, zsmul_mem (AddSubgroup.subset_closure hβ) _, ?_⟩
      rw [map_zsmul, phi_root (hΨ β hβ), smul_smul, mul_comm, ← hk]
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  have hy' : (p : ℤ) • y ∈ Λc := by rwa [natCast_zsmul]
  obtain ⟨z, hz, hzy⟩ := h2 _ hy'
  change phi τ z = (m : ℤ) • (p : ℤ) • y at hzy
  set x := C *ᵥ y
  have hx : phi τ ((p : ℤ) • (m : ℤ) • x) = phi τ ((N : ℤ) • z) := by
    rw [map_zsmul, map_zsmul, map_zsmul, hR, hzy, smul_comm (N : ℤ) (m : ℤ), smul_comm (p : ℤ),
      smul_comm (N : ℤ) (p : ℤ)]
  have hmx : (m : ℤ) • x ∈ Λ := by
    refine hroot _ ?_
    rw [← natCast_zsmul, hinj hx]
    exact zsmul_mem hz _
  have hmN : ((m * N : ℕ) : ℤ) • y ∈ Λc := by
    have := h1 hmx
    change phi τ ((m : ℤ) • x) ∈ Λc at this
    rwa [map_zsmul, hR, smul_smul, ← Nat.cast_mul] at this
  exact CFSG.HardMathSupport.C14PSat.mem_of_zsmul_mem hp (by exact_mod_cast hpm) hy hmN

@[expose] def cinv : (τ : Tag) → Matrix (Fin τ.rank) (Fin τ.rank) ℤ
  | .G2 => !![2, 3; 3, 6]
  | .F4 => !![2, 3, 4, 2; 3, 6, 8, 4; 4, 8, 12, 6; 2, 4, 6, 4]
  | .D4 => !![2, 1, 2, 1; 1, 2, 2, 1; 2, 2, 4, 2; 1, 1, 2, 2]
  | .E6 => !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
      4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]
  | .E7 => !![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
      8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4; 2, 3, 4, 6, 5, 4, 3]
  | .E8 => !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
      10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
      4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def cden : Tag → ℕ
  | .G2 => 6 | .F4 => 4 | .D4 => 4 | .E6 => 6 | .E7 => 4 | .E8 => 2

@[expose] def cnorm : Tag → ℕ
  | .G2 => 6 | .F4 => 4 | _ => 2

theorem phiMat_mul_cinv (τ : Tag) :
    (Matrix.of fun j k => 2 * τ.symmetrizer j j * τ.cartan j k) * cinv τ =
      ((cden τ : ℕ) : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by
  cases τ <;> decide

theorem cinv_mul_phiMat (τ : Tag) :
    cinv τ * (Matrix.of fun j k => 2 * τ.symmetrizer j j * τ.cartan j k) =
      ((cden τ : ℕ) : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by
  cases τ <;> decide

theorem symmetrizer_dvd_cnorm
    (τ : Tag) (i : Fin τ.rank) :
    2 * τ.symmetrizer i i ∣ (cnorm τ : ℤ) := by
  cases τ <;> revert i <;> decide

theorem corootPSat_of_transfer {τ : Tag}
    {p : ℕ} (hp : p.Prime) (Ψ : Set (Fin τ.rank → ℤ))
    (hΨ : ∀ β ∈ Ψ, IsRoot τ β)
    (hroot : ∀ v, p • v ∈ AddSubgroup.closure Ψ → v ∈ AddSubgroup.closure Ψ)
    (hpm : ¬ p ∣ cnorm τ * cden τ) : CorootPSaturated p Ψ :=
  corootPSat_of_rootPSat hp Ψ hΨ (cinv τ) (cden τ)
    (fun y => by rw [phi_eq_mulVec, Matrix.mulVec_mulVec, phiMat_mul_cinv, Matrix.smul_mulVec,
      Matrix.one_mulVec])
    (fun x => by rw [phi_eq_mulVec, Matrix.mulVec_mulVec, cinv_mul_phiMat, Matrix.smul_mulVec,
      Matrix.one_mulVec])
    (cnorm τ) (fun β hβ => by
      obtain ⟨i, hi⟩ := iform_self_of_isRoot (hΨ β hβ)
      rw [hi]; exact symmetrizer_dvd_cnorm τ i) hroot hpm

@[expose] def g2Roots : List (Fin 2 → ℤ) :=
  [![-2, -3], ![-1, -3], ![-1, -2], ![-1, -1], ![-1, 0], ![0, -1], ![0, 1], ![1, 0], ![1, 1],
    ![1, 2], ![1, 3], ![2, 3]]

theorem reflect_all_g2Roots :
    g2Roots.all (fun v => g2Roots.contains (reflect Tag.G2 0 v) &&
    g2Roots.contains (reflect Tag.G2 1 v)) = true := by
  decide

theorem reflect_mem_g2Roots'
    (v : Fin 2 → ℤ) (hv : v ∈ g2Roots) :
    reflect Tag.G2 0 v ∈ g2Roots ∧ reflect Tag.G2 1 v ∈ g2Roots := by
  have h := List.all_eq_true.1 reflect_all_g2Roots v hv
  rw [Bool.and_eq_true] at h
  have h' : ∀ w : Fin 2 → ℤ, g2Roots.contains w = true → w ∈ g2Roots :=
    fun w hw => List.mem_of_elem_eq_true hw
  exact ⟨h' _ h.1, h' _ h.2⟩

theorem reflect_mem_g2Roots
    (i : Fin Tag.G2.rank) (v : Fin Tag.G2.rank → ℤ) (hv : v ∈ g2Roots) :
    reflect Tag.G2 i v ∈ g2Roots := by
  have h := reflect_mem_g2Roots' v hv
  match i with
  | 0 => exact h.1
  | 1 => exact h.2

theorem mem_g2Roots
    {v : Fin Tag.G2.rank → ℤ} (hv : IsRoot Tag.G2 v) : v ∈ g2Roots := by
  induction hv with
  | basis j =>
    have key : ∀ j : Fin 2, (Pi.single j 1 : Fin 2 → ℤ) ∈ g2Roots := by decide
    exact key j
  | reflect i _ ih => exact reflect_mem_g2Roots i _ ih

@[expose] def det2 (u v : Fin 2 → ℤ) : ℤ := u 0 * v 1 - u 1 * v 0

@[expose] def cs : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

theorem g2_pairs :
    ∀ β ∈ g2Roots, ∀ γ ∈ g2Roots, det2 β γ ≠ 0 →
    (det2 (corootVec (τ := .G2) β) (corootVec (τ := .G2) γ) ∈ [1, -1, 2, -2]) ∨
    ((∃ k ∈ cs, ∃ l ∈ cs, (Pi.single 0 1 : Fin 2 → ℤ) = k • β + l • γ) ∧
      (∃ k ∈ cs, ∃ l ∈ cs, (Pi.single 1 1 : Fin 2 → ℤ) = k • β + l • γ)) := by
  decide

theorem g2_dep :
    ∀ β ∈ g2Roots, ∀ γ ∈ g2Roots, det2 β γ = 0 → γ = β ∨ γ = -β := by
  decide

theorem g2_primitive :
    ∀ β ∈ g2Roots, ∃ s ∈ cs, ∃ t ∈ cs,
    s * corootVec (τ := .G2) β 0 + t * corootVec (τ := .G2) β 1 = 1 := by
  decide

theorem g2_neg :
    ∀ β ∈ g2Roots, corootVec (τ := .G2) (-β) = -corootVec (τ := .G2) β := by
  decide

theorem g2_simple_det :
    det2 (corootVec (τ := .G2) (Pi.single 0 1)) (corootVec (τ := .G2) (Pi.single 1 1)) = 1 := by
  decide

theorem det2_smul_mem
    {Λ : AddSubgroup (Fin 2 → ℤ)} {u v : Fin 2 → ℤ} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (y : Fin 2 → ℤ) : det2 u v • y ∈ Λ := by
  have : det2 u v • y = (y 0 * v 1 - y 1 * v 0) • u + (u 0 * y 1 - u 1 * y 0) • v := by
    funext i
    fin_cases i <;> simp [det2] <;> ring
  rw [this]
  exact add_mem (zsmul_mem hu _) (zsmul_mem hv _)

theorem mem_familyKernel_comb {τ : Tag}
    {K : Type} [Field K] {ι : Type} {a : ι → Fin τ.rank → Kˣ}
    {β γ δ : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) (hγ : γ ∈ familyKernel a) (hδ : IsRoot τ δ)
    {k l : ℤ} (h : δ = k • β + l • γ) : δ ∈ familyKernel a := by
  refine ⟨hδ, fun i => ?_⟩
  rw [h, rootChar_add, rootChar_zsmul, rootChar_zsmul, hβ.2 i, hγ.2 i, one_zpow, one_zpow, mul_one]

theorem corootPSat_G2_three
    {K : Type} [Field K] {ι : Type} (a : ι → Fin Tag.G2.rank → Kˣ) :
    CorootPSaturated 3 (familyKernel a) := by
  intro y hy
  set Ψ := familyKernel a
  set Λc := AddSubgroup.closure (corootVec (τ := .G2) '' Ψ)
  have hy' : (3 : ℤ) • y ∈ Λc := by rwa [show (3 : ℤ) • y = 3 • y from natCast_zsmul _ _]
  have hmemc : ∀ β ∈ Ψ, corootVec (τ := .G2) β ∈ Λc := fun β hβ =>
    AddSubgroup.subset_closure ⟨β, hβ, rfl⟩
  have finish : ∀ u v : Fin 2 → ℤ, u ∈ Λc → v ∈ Λc → det2 u v ∈ [1, -1, 2, -2] → y ∈ Λc := by
    intro u v hu hv hd
    refine CFSG.HardMathSupport.C14PSat.mem_of_zsmul_mem Nat.prime_three ?_ hy'
      (det2_smul_mem hu hv y)
    revert hd
    generalize det2 u v = d
    intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> decide
  by_cases hrank : ∃ β ∈ Ψ, ∃ γ ∈ Ψ, det2 β γ ≠ 0
  · obtain ⟨β, hβ, γ, hγ, hdet⟩ := hrank
    rcases g2_pairs β (mem_g2Roots hβ.1) γ (mem_g2Roots hγ.1) hdet with hd | ⟨⟨k, -, l, -, h0⟩,
        ⟨k', -, l', -, h1⟩⟩
    · exact finish _ _ (hmemc β hβ) (hmemc γ hγ) hd
    · have h0' := mem_familyKernel_comb hβ hγ (IsRoot.basis 0) h0
      have h1' := mem_familyKernel_comb hβ hγ (IsRoot.basis 1) h1
      exact finish _ _ (hmemc _ h0') (hmemc _ h1') (by rw [g2_simple_det]; decide)
  · push Not at hrank
    by_cases hne : ∃ β, β ∈ Ψ
    · obtain ⟨β, hβ⟩ := hne
      set c := corootVec (τ := .G2) β
      have hle : Λc ≤ AddSubgroup.zmultiples c := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨γ, hγ, rfl⟩
        rcases g2_dep β (mem_g2Roots hβ.1) γ (mem_g2Roots hγ.1) (hrank β hβ γ hγ) with rfl | rfl
        · exact AddSubgroup.mem_zmultiples _
        · rw [g2_neg β (mem_g2Roots hβ.1)]
          exact neg_mem (AddSubgroup.mem_zmultiples _)
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (hle hy')
      obtain ⟨s, -, t, -, hst⟩ := g2_primitive β (mem_g2Roots hβ.1)
      have h3k : k = 3 * (s * y 0 + t * y 1) := by
        have e0 := congrFun hk 0
        have e1 := congrFun hk 1
        simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
        calc k = k * (s * c 0 + t * c 1) := by rw [hst, mul_one]
          _ = s * (k * c 0) + t * (k * c 1) := by ring
          _ = 3 * (s * y 0 + t * y 1) := by rw [e0, e1]; ring
      have hyc : y = (s * y 0 + t * y 1) • c := by
        funext i
        have ei := congrFun hk i
        simp only [Pi.smul_apply, smul_eq_mul] at ei ⊢
        refine mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide) ?_
        rw [← ei, h3k]
        ring
      rw [hyc]
      exact zsmul_mem (hmemc β hβ) _
    · push Not at hne
      have hΛ : Λc = ⊥ := by
        rw [eq_bot_iff, AddSubgroup.closure_le]
        rintro _ ⟨γ, hγ, rfl⟩
        exact (hne γ hγ).elim
      rw [hΛ, AddSubgroup.mem_bot] at hy'
      have : y = 0 := by
        funext i
        have hi := congrFun hy' i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        omega
      rw [this]
      exact zero_mem _

theorem not_dvd_two_pow_mul_three_pow
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))

theorem corootPSaturated_of_nonTorsion
    {τ : Tag} {K : Type} [Field K] {ι : Type} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) (a : ι → Fin τ.rank → Kˣ) : CorootPSaturated p (familyKernel a) := by
  by_cases hG : τ = .G2 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := hG
    exact corootPSat_G2_three a
  · have hG2 : τ = .G2 → p ≠ 3 := fun h h' => hG ⟨h, h'⟩
    refine corootPSat_of_transfer hp _ (fun _ hβ => hβ.1)
      (CFSG.HardMathSupport.C14PSat.familyKernel_pSaturated hp hp2 h3 h5 hG2 a) ?_
    cases τ
    · exact not_dvd_two_pow_mul_three_pow hp hp2 (hG2 rfl) 2 2
    · exact not_dvd_two_pow_mul_three_pow hp hp2 (h3 (Or.inl rfl)) 4 0
    · intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (n := 3) (by simpa [cnorm, cden] using h)))
    · exact not_dvd_two_pow_mul_three_pow hp hp2 (h3 (Or.inr (Or.inl rfl))) 2 1
    · exact not_dvd_two_pow_mul_three_pow hp hp2 (h3 (Or.inr (Or.inr (Or.inl rfl)))) 3 0
    · exact not_dvd_two_pow_mul_three_pow hp hp2 (h3 (Or.inr (Or.inr (Or.inr rfl)))) 2 0

end CFSG.HardMathSupport.C14Coroot
