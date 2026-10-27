module

public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.Quasithin.Background.FFC4G2
public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinZorn)

@[expose] def HasNoncentralThree (X : Type*) [Group X] : Prop :=
  ∃ c : X, c ^ 3 = 1 ∧ c ∉ Subgroup.center X

theorem HasNoncentralThree.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : HasNoncentralThree X) : HasNoncentralThree Y := by
  obtain ⟨c, hc3, hcn⟩ := h
  refine ⟨e c, by rw [← map_pow, hc3, map_one], fun hz => hcn ?_⟩
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact hz (e g)

section Rot

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem rotGL_not_mem_center {Γ : Subgroup (GL ι K)} (hΓ : CFSG.Quasithin.H.HasScalarCommutant Γ)
    {i j : ι} (hij : i ≠ j) (hmem : rotGL (K := K) i j ∈ Γ) :
    (⟨rotGL i j, hmem⟩ : ↥Γ) ∉ Subgroup.center ↥Γ := by
  intro hc
  rw [Subgroup.mem_center_iff] at hc
  have hcomm : ∀ γ ∈ Γ, (γ : Matrix ι ι K) * rotMatrix i j = rotMatrix i j * (γ : Matrix ι ι K) := by
    intro γ hγ
    have h := congrArg (fun x : ↥Γ => (((x : GL ι K) : Matrix ι ι K))) (hc ⟨γ, hγ⟩)
    simpa [coe_rotGL] using h
  obtain ⟨c, hc'⟩ := hΓ (AddMonoidHom.mk' (fun v => rotMatrix (K := K) i j *ᵥ v)
    (fun a b => Matrix.mulVec_add _ _ _)) (fun γ hγ v => by
      simp only [AddMonoidHom.mk'_apply, Matrix.mulVec_mulVec, ← hcomm γ hγ])
  have h1 := hc' (Pi.single i 1)
  simp only [AddMonoidHom.mk'_apply, rotMatrix_mulVec_left] at h1
  have h2 := congrFun h1 j
  simp [hij.symm] at h2

theorem hasNoncentralThree_of_rot {Γ : Subgroup (GL ι K)} (hΓ : CFSG.Quasithin.H.HasScalarCommutant Γ)
    {i j : ι} (hij : i ≠ j) (hmem : rotGL (K := K) i j ∈ Γ) : HasNoncentralThree ↥Γ :=
  ⟨⟨rotGL i j, hmem⟩, Subtype.ext (rotGL_pow_three _ _), rotGL_not_mem_center hΓ hij hmem⟩

theorem hasNoncentralThree_statedSL {d : ℕ} (hd : 2 ≤ d) : HasNoncentralThree ↥(StatedSL d K) := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact hasNoncentralThree_of_rot (CFSG.Quasithin.H.hasScalarCommutant_statedSL hd) h01
    (Subgroup.subset_closure (det_rotMatrix _ _))

theorem hasNoncentralThree_statedSp : HasNoncentralThree ↥(StatedSp 2 K) :=
  hasNoncentralThree_of_rot (CFSG.Quasithin.H.Sp4.hasScalarCommutant_statedSp (K := K))
    (i := Sum.inl 0) (j := Sum.inr 0) (by decide)
    (Subgroup.subset_closure (rotMatrix_symplectic 0))

end Rot

theorem hasNoncentralThree_alt {n : ℕ} (hn : 5 ≤ n) :
    HasNoncentralThree ↥(alternatingGroup (Fin n)) := by
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have h3 : (Equiv.swap a b * Equiv.swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hmem : Equiv.swap a b * Equiv.swap a c ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 h3.sign
  have hord := h3.orderOf
  refine ⟨⟨_, hmem⟩, Subtype.ext (by simpa [hord] using pow_orderOf_eq_one (Equiv.swap a b * Equiv.swap a c)), ?_⟩
  rw [alternatingGroup.center_eq_bot (by simp; omega), Subgroup.mem_bot]
  intro h
  have h1 : Equiv.swap a b * Equiv.swap a c = 1 := congrArg Subtype.val h
  rw [h1, orderOf_one] at hord
  omega

theorem hasNoncentralThree_hat {X : Type} [Group X] [Finite X]
    (h : IsHat X ↥(alternatingGroup (Fin 6))) : HasNoncentralThree X := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := threeRank2_hat h
  by_cases hxc : x ∈ Subgroup.center X
  · refine ⟨y, hy3, fun hyc => hyx ?_⟩
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hle : Subgroup.zpowers x ≤ Subgroup.center X := (Subgroup.zpowers_le).2 hxc
    have heq : Subgroup.zpowers x = Subgroup.center X :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h.2.1, Nat.card_zpowers, hord])
    rw [heq]
    exact hyc
  · exact ⟨x, hx3, hxc⟩

section G2

variable (K : Type) [Field K] [CharP K 2]

theorem matA2_matB2_ne : matA2 * matB2 ≠ matB2 * matA2 := by decide +kernel

theorem aK_bK_ne : aK (K := K) * bK ≠ bK * aK := by
  intro h
  have h1 := congrArg cmat h
  rw [map_mul, map_mul, cmat_aK, cmat_bK, ← map_mul, ← map_mul] at h1
  exact matA2_matB2_ne (bcM_injective h1)

theorem hasNoncentralThree_cayley :
    HasNoncentralThree ↥(cayleyGroup K) := by
  refine ⟨aK, aK_pow3, fun hz => aK_bK_ne K ?_⟩
  rw [Subgroup.mem_center_iff] at hz
  exact (hz bK).symm

theorem hasNoncentralThree_derived :
    HasNoncentralThree ↥⁅cayleyGroup K, cayleyGroup K⁆ := by
  refine ⟨⟨(aK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K), aK_mem⟩,
    Subtype.ext (by simpa using congrArg Subtype.val (aK_pow3 (K := K))), fun hz => aK_bK_ne K ?_⟩
  rw [Subgroup.mem_center_iff] at hz
  exact Subtype.ext (congrArg Subtype.val (hz ⟨(bK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K),
    bK_mem⟩)).symm

end G2

theorem hasNoncentralThree_g2 (K : Type) [Field K] [CharP K 2] :
    HasNoncentralThree ↥(CFSG.Open.quasithinG2 K) := by
  rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact hasNoncentralThree_cayley K

theorem hasNoncentralThree_g2_derived (K : Type) [Field K] [CharP K 2] :
    HasNoncentralThree ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
  rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact hasNoncentralThree_derived K

theorem hasNoncentralThree_of_realizes {W : Type*} [CommGroup W] {D : FFModel} (hD : D.Faithful)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π)
    (hX : HasNoncentralThree D.Gam) : HasNoncentralThree ↥L :=
  hX.of_mulEquiv (MulEquiv.ofBijective π ⟨injective_of_faithful_sec hD h, h.1⟩)

theorem hasNoncentralThree_of_pair {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hB : B42ModulePair L U Z) :
    HasNoncentralThree ↥L := by
  rcases hB with ⟨n, K, hK, hf, hc, π, hπ⟩ | ⟨n, K, hK, hf, hc, π, hπ⟩ | ⟨n, K, hK, hf, hc, π, hπ⟩ |
    ⟨n, K, hK, hf, hc, π, hπ⟩ | ⟨K, hK, hf, hc, π, hπ⟩ | h5 | h6 | h7 | h74 | h3a | h4 | h5' | hx4 | hx5
  · exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ
      (hasNoncentralThree_statedSL (d := 2) (by norm_num))
  · exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ
      (hasNoncentralThree_statedSL (d := 3) (by norm_num))
  · exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ hasNoncentralThree_statedSp
  · have := charP_two_of_card_pow hc
    exact hasNoncentralThree_of_realizes (zornQ_faithful _ le_rfl) hπ (hasNoncentralThree_g2 K)
  · have hc' : Nat.card K = 2 ^ 1 := hc
    have := charP_two_of_card_pow hc'
    exact hasNoncentralThree_of_realizes (zornQ_faithful _ (commutator_le_self_aux _)) hπ
      (hasNoncentralThree_g2_derived K)
  · obtain ⟨π, hπ⟩ := h5
    exact hasNoncentralThree_of_realizes (altDn_faithful (by norm_num)) hπ
      (hasNoncentralThree_alt (by norm_num))
  · obtain ⟨π, hπ⟩ := h6
    exact hasNoncentralThree_of_realizes (altDn_faithful (by norm_num)) hπ
      (hasNoncentralThree_alt (by norm_num))
  · obtain ⟨π, hπ⟩ := h7
    exact hasNoncentralThree_of_realizes (altDn_faithful (by norm_num)) hπ
      (hasNoncentralThree_alt (by norm_num))
  · obtain ⟨α, π, hπ⟩ := h74
    exact hasNoncentralThree_of_realizes (a7Four_faithful α) hπ
      (hasNoncentralThree_alt (n := 7) (by norm_num))
  · obtain ⟨K, hK, hf, Γ₀, hc, -, hhat, -, π, hπ⟩ := h3a
    have hE : HasNoncentralThree ↥Γ₀ := hasNoncentralThree_hat hhat
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ hE
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := h4
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ
      (hasNoncentralThree_statedSL (d := 4) (by norm_num))
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := h5'
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) hπ
      (hasNoncentralThree_statedSL (d := 5) (by norm_num))
  · obtain ⟨π, hπ⟩ := hx4
    exact hasNoncentralThree_of_realizes (b58Inputs.ext 4 (by norm_num)) hπ
      (hasNoncentralThree_statedSL (d := 4) (by norm_num))
  · obtain ⟨π, hπ⟩ := hx5
    exact hasNoncentralThree_of_realizes (b58Inputs.ext 5 (by norm_num)) hπ
      (hasNoncentralThree_statedSL (d := 5) (by norm_num))

theorem hasNoncentralThree_of_case1 {W : Type} [CommGroup W] [Finite W]
    {G L : Subgroup (MulAut W)}
    (h : B51Case1i G L ∨ B51Case1ii G L ∨ (∃ n, B51Case1iii G L n) ∨ B51Case1iv G L) :
    HasNoncentralThree ↥L := by
  rcases h with hi | hii | ⟨n, hiii⟩ | hiv
  · exact hasNoncentralThree_of_pair hi.2.1
  · obtain ⟨-, n, K, hK, hf, hc, I, π, -, -, hreal, -, -⟩ := hii
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) (hreal 0)
      (hasNoncentralThree_statedSL (d := 3) (by norm_num))
  · obtain ⟨-, hn, π, U₁, U₂, -, h₁, -⟩ := hiii
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) h₁
      (hasNoncentralThree_statedSL (d := n) (by omega))
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact hasNoncentralThree_of_realizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩)
      (hasNoncentralThree_statedSL (d := n) (by omega))

end FFC

end CFSG.Quasithin
