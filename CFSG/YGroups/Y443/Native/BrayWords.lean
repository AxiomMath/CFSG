module

public import CFSG.YGroups.Y443.Native.Align

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups.Y443Native

@[expose] def xWord : List Native.Gen := [.rho (true, 0, 0)]

@[expose] def eWord : List Native.Gen := Lw 4

@[expose] def kWord : List Native.Gen :=
  [.tau, .tau, .rho (false, 2556, 1067), .tau, .rho (false, 961, 3315), .rho (false, 0, 1481),
   .rho (false, 0, 6),
   .perm #[1, 16, 4, 5, 22, 12, 6, 10, 3, 14, 19, 13, 17, 21, 20, 0, 2, 18, 9, 11, 23, 15, 8, 7],
   .xi, .rho (false, 0, 36),
   .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
   .xi, .rho (false, 0, 60),
   .perm #[4, 5, 12, 23, 13, 20, 16, 18, 14, 21, 2, 1, 9, 11, 22, 15, 3, 8, 6, 19, 17, 7, 0, 10],
   .tau, .tau, .xi, .rho (false, 0, 0),
   .perm #[16, 17, 2, 3, 0, 1, 18, 19, 4, 5, 22, 23, 20, 21, 6, 7, 15, 12, 9, 11, 10, 8, 14, 13],
   .tau, .xi, .xi, .rho (false, 0, 8),
   .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
   .xi, .rho (false, 0, 42),
   .perm #[8, 10, 12, 21, 14, 19, 17, 23, 6, 16, 3, 11, 15, 5, 20, 4, 1, 13, 2, 22, 18, 0, 9, 7],
   .tau, .tau, .xi, .rho (false, 0, 24),
   .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
   .xi, .rho (false, 0, 2),
   .perm #[9, 10, 13, 21, 14, 18, 17, 22, 1, 20, 0, 15, 11, 7, 16, 2, 3, 8, 5, 19, 23, 6, 12, 4]]

@[expose] def gWord : List Native.Gen :=
  [.tau, .tau, .rho (false, 198, 0), .tau, .rho (false, 2576, 2870), .rho (false, 0, 854),
   .rho (false, 0, 34),
   .perm #[23, 7, 12, 19, 0, 2, 8, 1, 18, 21, 15, 4, 5, 16, 14, 22, 13, 17, 20, 6, 3, 11, 10, 9],
   .xi, .xi, .rho (false, 0, 6),
   .perm #[0, 2, 3, 5, 1, 4, 6, 7, 8, 21, 12, 17, 18, 15, 22, 11, 13, 16, 9, 20, 23, 10, 19, 14],
   .xi, .xi, .rho (false, 0, 36),
   .perm #[1, 4, 5, 7, 11, 12, 20, 19, 0, 2, 6, 3, 22, 17, 9, 14, 13, 21, 10, 18, 16, 15, 8, 23]]

@[expose] def eqWords3 (w₁ w₂ : List Native.Gen) : Bool :=
  eqWords w₁ w₂ (aV ()) && eqWords w₁ w₂ (bV ()) && eqWords w₁ w₂ (wV ())

theorem eq_of_eqWords3
    {w₁ w₂ : List Native.Gen} (h : eqWords3 w₁ w₂ = true) :
    wordLin w₁ = wordLin w₂ := by
  unfold eqWords3 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact eq_of_eqWords h.1.1 h.1.2 h.2

@[expose] def coordX (r : Native.DVec) (p E : ℕ) : ℤ := r.D.getD (300 + p) 0 * 2 ^ (E - r.e)

@[expose] def diffX (r₁ r₂ : Native.DVec) (p : ℕ) : Bool :=
  coordX r₁ p (max r₁.e r₂.e) != coordX r₂ p (max r₁.e r₂.e)

theorem diffX_sound {r₁ r₂ : Native.DVec} {p : ℕ} (hp : p < 98280)
    (h : diffX r₁ r₂ p = true) : interp r₁ ≠ interp r₂ := by
  intro heq
  have hX : interpX r₁ = interpX r₂ := congrArg (fun z : SpaceB => z.2.1) heq
  have h1 := congrFun hX (shortOf ⟨p, hp⟩)
  simp only [interpX, posOf_shortOf] at h1
  unfold diffX coordX at h
  rw [bne_iff_ne] at h
  refine h ?_
  have hE1 : (2 : ℚ) ^ (max r₁.e r₂.e) = 2 ^ r₁.e * 2 ^ (max r₁.e r₂.e - r₁.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_left _ _)]
  have hE2 : (2 : ℚ) ^ (max r₁.e r₂.e) = 2 ^ r₂.e * 2 ^ (max r₁.e r₂.e - r₂.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right _ _)]
  have h2 : (((r₁.D.getD (300 + p) 0 * 2 ^ (max r₁.e r₂.e - r₁.e) : ℤ)) : ℚ) =
      (((r₂.D.getD (300 + p) 0 * 2 ^ (max r₁.e r₂.e - r₂.e) : ℤ)) : ℚ) := by
    push_cast
    calc (r₁.D.getD (300 + p) 0 : ℚ) * 2 ^ (max r₁.e r₂.e - r₁.e)
        = ((r₁.D.getD (300 + p) 0 : ℚ) / 2 ^ r₁.e) * 2 ^ (max r₁.e r₂.e) := by
          rw [hE1]; field_simp
      _ = ((r₂.D.getD (300 + p) 0 : ℚ) / 2 ^ r₂.e) * 2 ^ (max r₁.e r₂.e) := by rw [h1]
      _ = (r₂.D.getD (300 + p) 0 : ℚ) * 2 ^ (max r₁.e r₂.e - r₂.e) := by
          rw [hE2]; field_simp
  exact_mod_cast h2

@[expose] def neX (w₁ w₂ : List Native.Gen) (v : Native.DVec) (p : ℕ) : Bool :=
  w₁.all Native.Gen.validB && w₂.all Native.Gen.validB &&
    diffX (Native.evalWordC (Native.mkCtx ()) w₁ v) (Native.evalWordC (Native.mkCtx ()) w₂ v) p

theorem ne_of_neX
    {w₁ w₂ : List Native.Gen} {v : Native.DVec} {p : ℕ} (hp : p < 98280)
    (h : neX w₁ w₂ v p = true) : wordLin w₁ (interp v) ≠ wordLin w₂ (interp v) := by
  unfold neX at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv₁, hv₂⟩, hd⟩ := h
  have hw₁ : ∀ g ∈ w₁, g.validB = true := fun g hg => List.all_eq_true.1 hv₁ g hg
  have hw₂ : ∀ g ∈ w₂, g.validB = true := fun g hg => List.all_eq_true.1 hv₂ g hg
  have := diffX_sound hp hd
  rwa [evalWordC_sound w₁ hw₁ v, evalWordC_sound w₂ hw₂ v] at this

end CFSG.YGroups.Y443
