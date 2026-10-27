module

public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Ree.LargeReeB2FixedCoordinates
public import CFSG.LieType.Ree.RootBruhatEquivariance
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwistedF4Diag

section RootChar

variable {K : Type} [Field K]

theorem rootChar_largeReeRoot_zero (b : Fin Tag.F4.rank → Kˣ) :
    rootChar b (largeReeRoot 0) = b ⟨2, by decide⟩ := by
  change ∏ i : Fin 4, b i ^ largeReeRoot 0 i = _
  rw [Fin.prod_univ_four]
  simp [largeReeRoot]
  rfl

theorem rootChar_largeReeRoot_one (b : Fin Tag.F4.rank → Kˣ) :
    rootChar b (largeReeRoot 1) = b ⟨1, by decide⟩ := by
  change ∏ i : Fin 4, b i ^ largeReeRoot 1 i = _
  rw [Fin.prod_univ_four]
  simp [largeReeRoot]
  rfl

end RootChar


section Conj

variable {K : Type} [Field K]

theorem rootDiagUnit_conj_largeReeP (b : Fin Tag.F4.rank → Kˣ) (A B C D : K) :
    rootDiagUnit Tag.F4 b * largeReeP K A B C D * (rootDiagUnit Tag.F4 b)⁻¹ =
      largeReeP K ((rootChar b (largeReeRoot 0) : K) * A) ((rootChar b (largeReeRoot 1) : K) * B)
        ((rootChar b (largeReeRoot 2) : K) * C) ((rootChar b (largeReeRoot 3) : K) * D) := by
  have e : ∀ x y z w : ModGL Tag.F4 K, rootDiagUnit Tag.F4 b * (x * y * z * w) *
      (rootDiagUnit Tag.F4 b)⁻¹ = (rootDiagUnit Tag.F4 b * x * (rootDiagUnit Tag.F4 b)⁻¹) *
        (rootDiagUnit Tag.F4 b * y * (rootDiagUnit Tag.F4 b)⁻¹) *
        (rootDiagUnit Tag.F4 b * z * (rootDiagUnit Tag.F4 b)⁻¹) *
        (rootDiagUnit Tag.F4 b * w * (rootDiagUnit Tag.F4 b)⁻¹) := fun _ _ _ _ => by group
  simp only [largeReeP, largeReeX]
  rw [e, rootDiagUnit_conj_pinnedX (τ := Tag.F4) b (largeReeRoot_pos 0).1,
    rootDiagUnit_conj_pinnedX (τ := Tag.F4) b (largeReeRoot_pos 1).1,
    rootDiagUnit_conj_pinnedX (τ := Tag.F4) b (largeReeRoot_pos 2).1,
    rootDiagUnit_conj_pinnedX (τ := Tag.F4) b (largeReeRoot_pos 3).1]

end Conj

section Compat

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem compat_one_four (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : Fin ReeTag.F4.tag.rank → Kˣ}
    (h : ∀ g ∈ ReeTag.F4.reeGamma K a, rootDiagUnit ReeTag.F4.tag b * g *
      (rootDiagUnit ReeTag.F4.tag b)⁻¹ ∈ ReeTag.F4.reeGamma K a) :
    b ReeTag.largeReeI4 = b ReeTag.largeReeI1 ^ 2 ^ a := by
  have hset := ReeTag.coe_reeFixedOrbitUnipotent_zero (a := a) hK
  have hg : xUnit ReeTag.F4.tag K ReeTag.largeReeI1 1 * xUnit ReeTag.F4.tag K ReeTag.largeReeI4 1 ∈
      (ReeTag.F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL ReeTag.F4.tag K)) := by
    rw [hset]
    exact ⟨1, by simp only [one_pow]⟩
  have hc := h _ (Subgroup.mem_inf.1 hg).2
  have hx := (root_diagonal_conjugation ReeTag.F4.tag K b).1
  have e : rootDiagUnit ReeTag.F4.tag b * (xUnit ReeTag.F4.tag K ReeTag.largeReeI1 1 *
      xUnit ReeTag.F4.tag K ReeTag.largeReeI4 1) * (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
      xUnit ReeTag.F4.tag K ReeTag.largeReeI1 (b ReeTag.largeReeI1) *
        xUnit ReeTag.F4.tag K ReeTag.largeReeI4 (b ReeTag.largeReeI4) := by
    calc _ = (rootDiagUnit ReeTag.F4.tag b * xUnit ReeTag.F4.tag K ReeTag.largeReeI1 1 *
          (rootDiagUnit ReeTag.F4.tag b)⁻¹) * (rootDiagUnit ReeTag.F4.tag b *
          xUnit ReeTag.F4.tag K ReeTag.largeReeI4 1 * (rootDiagUnit ReeTag.F4.tag b)⁻¹) := by
          group
      _ = _ := by rw [hx, hx, mul_one, mul_one]
  have hU : xUnit ReeTag.F4.tag K ReeTag.largeReeI1 (b ReeTag.largeReeI1) *
      xUnit ReeTag.F4.tag K ReeTag.largeReeI4 (b ReeTag.largeReeI4) ∈
        ReeTag.F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, e ▸ hc⟩
    rw [ReeTag.F4_fixedOrbitRoots_zero]
    refine mul_mem ?_ ?_ <;> rw [← pinnedX_single] <;> exact pinnedX_mem_rootSpan (by simp) _
  have hU' : _ ∈ (ReeTag.F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ :
      Set (ModGL ReeTag.F4.tag K)) := hU
  rw [hset] at hU'
  obtain ⟨c, hc'⟩ := hU'
  obtain ⟨h1, h2⟩ := ReeTag.largeRee_x_inj hc'
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h2, h1])

theorem compat_two_three (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : Fin Tag.F4.rank → Kˣ}
    (h : ∀ g : ModGL Tag.F4 K, g ∈ ReeTag.F4.reeGamma K a →
      rootDiagUnit Tag.F4 b * g * (rootDiagUnit Tag.F4 b)⁻¹ ∈ ReeTag.F4.reeGamma K a) :
    b ⟨1, by decide⟩ = b ⟨2, by decide⟩ ^ (2 * 2 ^ a) := by
  obtain ⟨hmaps, -, hsurj⟩ := ReeTag.bijOn_largeReeCoord (a := a) hK
  have hc := h (ReeTag.largeReeCoord a K 1 0)
    (Subgroup.mem_inf.1 (hmaps (Set.mem_univ ((1 : K), (0 : K))))).2
  rw [ReeTag.largeReeCoord, rootDiagUnit_conj_largeReeP] at hc
  have hU := (Subgroup.mem_inf (p := rootSpan ReeTag.F4.tag K
      (ReeTag.F4.fixedOrbitRoots ⟨1, by decide⟩)) (p' := ReeTag.F4.reeGamma K a)).2
    ⟨by rw [ReeTag.F4_fixedOrbitRoots_one]; exact largeReeP_mem_rootSpan _ _ _ _, hc⟩
  obtain ⟨⟨t, v⟩, -, htv⟩ := hsurj hU
  obtain ⟨e1, e2, -, -⟩ := ReeTag.largeReeP_injective htv
  rw [rootChar_largeReeRoot_zero, mul_one] at e1
  rw [rootChar_largeReeRoot_one, ReeTag.largeReeSigma, ReeTag.largeReeSigma, one_pow, mul_one,
    e1] at e2
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact e2.symm)

end Compat

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem rootDiagUnit_mem_reeGamma_of_compat (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : Fin ReeTag.F4.tag.rank → Kˣ} (h4 : b ReeTag.largeReeI4 = b ReeTag.largeReeI1 ^ 2 ^ a)
    (h2 : b ⟨1, by decide⟩ = b ⟨2, by decide⟩ ^ (2 * 2 ^ a)) :
    rootDiagUnit ReeTag.F4.tag b ∈ ReeTag.F4.reeGamma K a := by
  have hu : ∀ u : Kˣ, u ^ 2 ^ (2 * a + 1) = u := fun u => by
    rw [← hK]
    have h1 : u ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    calc u ^ Nat.card K = u ^ (Nat.card K - 1 + 1) := by rw [Nat.sub_add_cancel Nat.card_pos]
      _ = u := by rw [pow_succ, h1, one_mul]
  have hchar : ringChar K = 2 := ringChar.eq K ReeTag.F4.prime
  have hT : rootDiagUnit ReeTag.F4.tag b ∈ torusGroup ReeTag.F4.tag K :=
    (even_power_two_Cartan_root_diagonals_inner Tag.F4 (Or.inr (Or.inl rfl)) K hchar).1 b
  have hle : torusGroup ReeTag.F4.tag K ≤ adjointGroup ReeTag.F4.tag K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  have hadj : rootDiagUnit ReeTag.F4.tag b ∈ adjointGroup ReeTag.F4.tag K := hle hT
  have hFT : ((ReeTag.F4.finiteReeAut K a ⟨_, hadj⟩ : adjointGroup ReeTag.F4.tag K) :
      ModGL ReeTag.F4.tag K) ∈ torusGroup ReeTag.F4.tag K := by
    have h1 : (⟨_, hadj⟩ : adjointGroup ReeTag.F4.tag K) ∈
        (torusGroup ReeTag.F4.tag K).subgroupOf (adjointGroup ReeTag.F4.tag K) :=
      Subgroup.mem_subgroupOf.2 hT
    have h1' := Subgroup.mem_map_of_mem (ReeTag.F4.finiteReeAut K a).toMonoidHom h1
    rw [ReeTag.map_finiteReeAut_torusSub] at h1'
    exact Subgroup.mem_subgroupOf.1 h1'
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hFT
  have key : ∀ i, b' (ReeTag.F4.perm i) = b i ^ ReeTag.F4.relationExponent a i := by
    intro i
    have e1 : (⟨_, hadj⟩ : adjointGroup ReeTag.F4.tag K) * xElement i 1 *
        (⟨_, hadj⟩ : adjointGroup ReeTag.F4.tag K)⁻¹ = xElement i (b i : K) := by
      apply Subtype.ext
      change rootDiagUnit ReeTag.F4.tag b * xUnit ReeTag.F4.tag K i 1 *
        (rootDiagUnit ReeTag.F4.tag b)⁻¹ = xUnit ReeTag.F4.tag K i (b i : K)
      rw [(root_diagonal_conjugation ReeTag.F4.tag K b).1, mul_one]
    have e2 := congrArg (fun x => ((ReeTag.F4.finiteReeAut K a x : adjointGroup ReeTag.F4.tag K) :
      ModGL ReeTag.F4.tag K)) e1
    simp only [map_mul, map_inv, ReeTag.finiteReeAut_xElement, one_pow, Subgroup.coe_mul,
      Subgroup.coe_inv] at e2
    rw [hb'] at e2
    change rootDiagUnit ReeTag.F4.tag b' * xUnit ReeTag.F4.tag K (ReeTag.F4.perm i) 1 *
      (rootDiagUnit ReeTag.F4.tag b')⁻¹ = xUnit ReeTag.F4.tag K (ReeTag.F4.perm i)
        ((b i : K) ^ ReeTag.F4.relationExponent a i) at e2
    rw [(root_diagonal_conjugation ReeTag.F4.tag K b').1, mul_one] at e2
    have e3 := xOp_injective _ (congrArg Units.val e2)
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact e3)
  obtain ⟨p1, p4, -, -, -⟩ := ReeTag.largeRee_A1_data
  obtain ⟨r1, r4⟩ := ReeTag.largeRee_relationExponent a
  have p2 : ReeTag.F4.perm ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have p3 : ReeTag.F4.perm ⟨2, by decide⟩ = ⟨1, by decide⟩ := by decide
  have r2 : ReeTag.F4.relationExponent a ⟨1, by decide⟩ = 2 ^ a := by
    rw [ReeTag.relationExponent, ite_eq_left (by decide)]
    rfl
  have r3 : ReeTag.F4.relationExponent a ⟨2, by decide⟩ = 2 * 2 ^ a := by
    rw [ReeTag.relationExponent, ite_eq_right (by decide), pow_succ, mul_comm]
    rfl
  have k1 := key ReeTag.largeReeI1
  have k2 := key ⟨1, by decide⟩
  have k3 := key ⟨2, by decide⟩
  have k4 := key ReeTag.largeReeI4
  rw [p1, r1] at k1
  rw [p2, r2] at k2
  rw [p3, r3] at k3
  rw [p4, r4] at k4
  have hexp : 2 ^ a * (2 * 2 ^ a) = 2 ^ (2 * a + 1) := by ring
  have hbb : b' = b := by
    funext j
    obtain ⟨n, hn⟩ := j
    have hn4 : n < 4 := hn
    interval_cases n
    · calc b' ⟨0, hn⟩ = b ReeTag.largeReeI4 ^ (2 * 2 ^ a) := k4
        _ = b ReeTag.largeReeI1 ^ (2 ^ a * (2 * 2 ^ a)) := by rw [h4, ← pow_mul]
        _ = b ⟨0, hn⟩ := by rw [hexp, hu]
    · exact k3.trans h2.symm
    · calc b' ⟨2, hn⟩ = b ⟨1, by decide⟩ ^ 2 ^ a := k2
        _ = b ⟨2, by decide⟩ ^ (2 ^ a * (2 * 2 ^ a)) := by rw [h2, ← pow_mul, mul_comm]
        _ = b ⟨2, hn⟩ := by rw [hexp, hu]
    · exact k1.trans h4.symm
  exact ReeTag.mem_reeGamma_of_fixed hadj (by rw [hb', hbb])

theorem rootDiagUnit_mem_reeGamma_of_forall_conj_mem (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : Fin ReeTag.F4.tag.rank → Kˣ}
    (h : ∀ g ∈ ReeTag.F4.reeGamma K a, rootDiagUnit ReeTag.F4.tag b * g *
      (rootDiagUnit ReeTag.F4.tag b)⁻¹ ∈ ReeTag.F4.reeGamma K a) :
    rootDiagUnit ReeTag.F4.tag b ∈ ReeTag.F4.reeGamma K a :=
  rootDiagUnit_mem_reeGamma_of_compat hK (compat_one_four hK h) (compat_two_three hK h)

end Fixed

end TwistedF4Diag

end CFSG.StandardType
