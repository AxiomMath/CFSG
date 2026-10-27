module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityPair
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis

public section

namespace CFSG.RankThree.PartOne.KCUnitaryOne

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.RankThree.PartOne.KCUnitaryPlane

section Char

variable {K : Type} [Field K] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_charHom (ρ : G →* LinearMap.GeneralLinearGroup K V) {v : V} (hv : v ≠ 0)
    (hev : ∀ g, ∃ c : K, (ρ g : Module.End K V) v = c • v) :
    ∃ χ : G →* Kˣ, ∀ g, (ρ g : Module.End K V) v = (χ g : K) • v := by
  choose c hc using hev
  have hc0 : ∀ g, c g ≠ 0 := by
    intro g h0
    have h1 := hc g
    rw [h0, zero_smul] at h1
    have h2 : (((ρ g)⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        ((ρ g : Module.End K V) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
      rfl
    rw [h1, map_zero] at h2
    exact hv h2.symm
  refine ⟨{ toFun := fun g => Units.mk0 (c g) (hc0 g), map_one' := ?_, map_mul' := ?_ },
    fun g => hc g⟩
  · have h1 := hc 1
    rw [map_one, Units.val_one, Module.End.one_apply] at h1
    apply Units.ext
    exact smul_left_injective K hv (show c 1 • v = (1 : K) • v by rw [one_smul]; exact h1.symm)
  · intro g g'
    have h1 := hc (g * g')
    rw [map_mul, Units.val_mul, Module.End.mul_apply, hc g', map_smul, hc g, smul_smul] at h1
    apply Units.ext
    exact smul_left_injective K hv
      (show c (g * g') • v = (c g * c g') • v by rw [← h1, mul_comm])

theorem exists_ne_one_of_pow_eq_one [Finite G] {p : ℕ} (hp : p.Prime) (hcard : Nat.card G = p ^ 2)
    (r : G →* Kˣ) (hr : ∀ x, r x ^ p = 1) : ∃ x : G, x ≠ 1 ∧ r x = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra h1
    exact hcon x h1 hx
  have hle : Nat.card G ≤ Nat.card (rootsOfUnity p K) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨r x, ?_⟩) ?_
    · rw [mem_rootsOfUnity]
      exact hr x
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
  have h2 := card_rootsOfUnity K p
  rw [hcard] at hle
  have := hp.two_le
  nlinarith

end Char

section Plane

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem exists_pair_eigenvalue (S : PlaneSetup h n p Ahat) {b : Fin n → Fin n → K}
    (hb0 : ∀ i, b i ≠ 0) (hbeig : ∀ x ∈ Ahat, ∀ i, ∃ c : K, xlin h n x (b i) = c • b i)
    (i j : Fin n) :
    ∃ x ∈ Ahat, x ≠ 1 ∧ ∃ μ : K, μ ^ p = 1 ∧ xlin h n x (b i) = μ • b i ∧
      xlin h n x (b j) = μ • b j := by
  classical
  have : Finite K := h.finite
  have : Finite ↥Ahat := inferInstance
  have hρ : ∀ x : ↥Ahat, ((planeRep h n Ahat x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = xlin h n x.1 := fun x => rfl
  obtain ⟨χi, hχi⟩ := exists_charHom (planeRep h n Ahat) (hb0 i)
    (fun x => by rw [hρ]; exact hbeig x.1 x.2 i)
  obtain ⟨χj, hχj⟩ := exists_charHom (planeRep h n Ahat) (hb0 j)
    (fun x => by rw [hρ]; exact hbeig x.1 x.2 j)
  have hpow : ∀ x : ↥Ahat, x ^ p = 1 := fun x => Subtype.ext (S.pow_eq_one x.2)
  obtain ⟨x₀, hx₀1, hx₀⟩ := exists_ne_one_of_pow_eq_one S.prime (by rw [S.card])
    (χi * χj⁻¹) (fun x => by
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, ← map_pow, hpow x,
        map_one, inv_one, mul_one])
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at hx₀
  refine ⟨x₀.1, x₀.2, fun h1 => hx₀1 (Subtype.ext h1), (χi x₀ : K), ?_, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow x₀, map_one, Units.val_one]
  · rw [← hρ, hχi]
  · rw [← hρ, hχj, hx₀]

theorem rigidity_of_orthonormal_eigenbasis (S : PlaneSetup h n p Ahat) (hpq : p ∣ ℓ ^ f + 1)
    (hq : 3 < ℓ ^ f) (b : Module.Basis (Fin n) K (Fin n → K))
    (hbON : IsOrthonormalFamily h b)
    (hbeig : ∀ x ∈ Ahat, ∀ i, ∃ c : K, xlin h n x (b i) = c • b i)
    (β : MulAut (primeFormP h (idGram K n)))
    (hcent : ∀ x ∈ Ahat, β * primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) * β)
    (hblock : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      β * primeFormConjHom h (idGram K n) g = primeFormConjHom h (idGram K n) g * β) :
    β = 1 := by
  classical
  have hn := S.three_le
  have hne := S.ne
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne β
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hpair := fun i j => exists_pair_eigenvalue S hb0 hbeig i j
  have hMunit : IsUnit ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (M : GL (Fin n) K).isUnit
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := fun h' => by simpa [i0, i1] using congrArg Fin.val h'
  have h02 : i0 ≠ i2 := fun h' => by simpa [i0, i2] using congrArg Fin.val h'
  have h12 : i1 ≠ i2 := fun h' => by simpa [i1, i2] using congrArg Fin.val h'
  have htorus : ∀ i j : Fin n, i ≠ j → ∀ c : Kˣ, h.norm (c : K) = 1 →
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h (b i) (b j) c).map τ =
        torusMat h (b i) (b j) c * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    obtain ⟨x, hx, hx1, μ, hμ, hei, hej⟩ := hpair i j
    exact torus_comm_of_good_eigenpair S hx (bar_eq_inv_of_pow_eq_one h hpq hμ) (hbON.pair hij)
      hei hej (not_exceptional_of_three_lt hq) M τ (fun i g hg => hblock x hx hx1 i g hg)
  have hτ : τ = RingEquiv.refl K :=
    tau_eq_one_of_torus h hMunit (hbON.pair h01) (hbON.pair h02)
      (hbON.linearIndependent_triple h01 h02 h12) (htorus i0 i1 h01) (htorus i0 i2 h02)
  subst hτ
  have hmat1 : ∀ g : GL (Fin n) K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
      (RingEquiv.refl K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun g => by
    ext
    rfl
  have hscal : ∀ i j : Fin n, i ≠ j → ∃ c : K,
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = c • b i ∧
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b j = c • b j := by
    intro i j hij
    obtain ⟨x, hx, hx1, μ, hμ, hei, hej⟩ := hpair i j
    have hev : Module.End.HasEigenvalue (xlin h n x) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hei, hb0 i⟩
    have hmem := X_sub_C_mem_primaryFactors hev
    have hm : 2 ≤ Module.finrank K (primaryComponent (xlin h n x) (X - C μ)) :=
      two_le_finrank_of_pair (mem_primaryComponent_X_sub_C.mpr hei)
        (mem_primaryComponent_X_sub_C.mpr hej) (hbON.pair hij).linearIndependent
    have hgood := isGoodBlock_X_sub_C (hK := h) hmem hm (not_exceptional_of_three_lt hq)
    have hF := isPerfect_idSpecialBlock S hx ⟨⟨X - C μ, hmem⟩, hgood⟩
    have hMx : M * liftUnitary x = liftUnitary x * M := by
      have := matrix_comm_of_plane S hx M (RingEquiv.refl K) (hcent x hx)
      rw [hmat1] at this
      exact Subtype.ext (Units.ext this)
    have hblock' : ∀ g ∈ idSpecialBlock h x (X - C μ), M * g = g * M := by
      intro g hg
      have := matrix_comm_of_perfect S.three_le S.ne hF M (RingEquiv.refl K)
        (hblock x hx hx1 ⟨⟨X - C μ, hmem⟩, hgood⟩) g hg
      rw [hmat1] at this
      exact Subtype.ext (Units.ext this)
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_block_X_sub_C S hx hmem hgood M hMx hblock'
    exact ⟨c, hc _ hei, hc _ hej⟩
  obtain ⟨d, hd0, -⟩ := hscal i0 i1 h01
  have hall : ∀ j, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b j = d • b j := by
    intro j
    by_cases hj : j = i0
    · rw [hj]
      exact hd0
    · obtain ⟨c, hc0, hcj⟩ := hscal i0 j (Ne.symm hj)
      have hcd : c = d := smul_left_injective K (hb0 i0) (hc0.symm.trans hd0)
      rw [hcj, hcd]
  have hMeq : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      d • (1 : Matrix (Fin n) (Fin n) K) := by
    apply Matrix.toLin'.injective
    apply b.ext
    intro j
    simp only [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact hall j
  have hself : idForm h n (b i0) (b i0) = 1 := by rw [hbON i0 i0, ite_eq_left rfl]
  have hdn : h.bar d * d = 1 := by
    have h1 := (mem_sesqUnitaryGroup.mp (toLinU_mem M)) (b i0) (b i0)
    rw [toLinU_apply_eq, hall i0, hself] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hself, mul_one,
      RingHom.id_apply] at h1
    rw [mul_comm]
    exact h1
  have hd_ne : d ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hdn
    exact zero_ne_one hdn
  have hcn : h.norm ((Units.mk0 d hd_ne : Kˣ) : K) = 1 := by
    change d * h.bar d = 1
    rw [mul_comm]
    exact hdn
  have hker : primeFormConjHom h (idGram K n) M = 1 := by
    refine (primeFormConjHom_eq_one_iff_of_ne hn hne M).mpr
      ⟨Units.mk0 d hd_ne, (pow_succ_eq_one_iff_norm h _).mpr hcn, ?_⟩
    apply Units.ext
    rw [hMeq]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [primeFormPsi_apply, hker, one_mul]
  exact map_one _

end Plane

end CFSG.RankThree.PartOne.KCUnitaryOne
