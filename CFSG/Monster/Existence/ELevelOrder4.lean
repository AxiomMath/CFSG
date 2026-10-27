module

public import CFSG.Monster.Existence.ELevelDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

theorem exists_triple_of_mem_FE {f : MGriess} (hf : f ∈ FE) (hf1 : f ≠ 1) :
    ∃ a b c : Q, IsShortCoord (coordOf a) ∧ IsShortCoord (coordOf b) ∧ IsShortCoord (coordOf c) ∧
      f = rhoGriess a ∧ rhoGriess b ∈ FE ∧ rhoGriess c = f * rhoGriess b := by
  have htu : tGriess * uGriess = rhoGriess rOneTwo := Subtype.ext tStar_mul_uStar
  have hut : uGriess * tGriess = rhoGriess rOneTwo := Subtype.ext uStar_mul_tStar
  have ht : tGriess ∈ FE := mem_FE.2 (Or.inr (Or.inl rfl))
  have hu : uGriess ∈ FE := mem_FE.2 (Or.inr (Or.inr (Or.inl rfl)))
  rcases mem_FE.1 hf with rfl | rfl | rfl | rfl
  · exact absurd rfl hf1
  · refine ⟨rStar, rTwo, rOneTwo, isShortCoord_rStar, isShortCoord_rTwo, isShortCoord_rOneTwo,
      rhoGriess_rStar.symm, by rw [rhoGriess_rTwo]; exact hu, ?_⟩
    rw [rhoGriess_rTwo]
    exact htu.symm
  · refine ⟨rTwo, rStar, rOneTwo, isShortCoord_rTwo, isShortCoord_rStar, isShortCoord_rOneTwo,
      rhoGriess_rTwo.symm, by rw [rhoGriess_rStar]; exact ht, ?_⟩
    rw [rhoGriess_rStar]
    exact hut.symm
  · refine ⟨rOneTwo, rStar, rTwo, isShortCoord_rOneTwo, isShortCoord_rStar, isShortCoord_rTwo,
      htu, by rw [rhoGriess_rStar]; exact ht, ?_⟩
    rw [rhoGriess_rTwo, rhoGriess_rStar, mul_assoc, ← tGriess_mul_uGriess, ← mul_assoc,
      tGriess_mul_self, one_mul]

theorem mul_self_mem_of_piVis_eq_one {k : MGriess}
    (hkG : (k : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis) (h : piVis ⟨k, hkG⟩ = 1) :
    k * k = 1 ∨ k * k = xGriess := by
  obtain ⟨r, hr⟩ := (piVis_eq_one_iff _).1 h
  have hk : k = rhoGriess r := Subtype.ext hr.symm
  rw [hk, ← rhoGriess_mul]
  rcases eq_one_or_zQ_of_coordOf_eq_zero
      ((mem_zpowers_zQ_iff _).1 (mul_self_mem_zpowers_zQ r)) with h1 | h1
  · exact Or.inl (by rw [h1, rhoGriess_one])
  · exact Or.inr (by rw [h1, rhoGriess_zQ])

theorem exists_conj_mem_cosetR
    {K : SpaceB ≃ₗ[ℚ] SpaceB} (hK : K ∈ Gvis)
    (hπ : piVis ⟨K, hK⟩ ≠ 1) {a : Q} (hKK : K * K = rhoEquiv a) :
    ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 6) ∧ ∃ (δ : Pvis) (q : Q),
      thetaEquiv δ * K * (thetaEquiv δ)⁻¹ =
        (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q := by
  obtain ⟨pk, rfl⟩ := mem_Gvis.1 hK
  have hψ1 : modTwoUnit pk.1.2 ≠ 1 := fun h => hπ (by
    rw [piVis_thetaEquiv, MulOpposite.op_eq_one_iff, QuotientGroup.eq_one_iff,
      mem_zpowers_negOneO_iff]
    exact (modTwoUnit_eq_one_iff _).1 h)
  have hψ2 : modTwoUnit pk.1.2 * modTwoUnit pk.1.2 = 1 := by
    have h1 : thetaEquiv (pk * pk) = thetaEquiv (rhoPair a) := by
      rw [thetaEquiv_mul]
      exact hKK
    have h2 := mk_eq_of_thetaEquiv_eq h1
    have h3 : (QuotientGroup.mk (pk.1.2 * pk.1.2) :
        latticeO ⧸ Subgroup.zpowers negOneO) = 1 := h2
    rw [QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff, ← modTwoUnit_eq_one_iff,
      modTwoUnit_mul] at h3
    exact h3
  obtain ⟨i, hi, g, hg, hgψ⟩ := exists_conj_three (mem_OLvis.2 ⟨_, rfl⟩) hψ2 hψ1
  obtain ⟨g₀, rfl⟩ := mem_OLvis.1 hg
  obtain ⟨s, hs⟩ := exists_mem_Pvis g₀
  let pγ : Pvis := ⟨(s, g₀), hs⟩
  have hP : thetaEquiv (pγ * pk * pγ⁻¹) =
      thetaEquiv pγ⁻¹ * thetaEquiv pk * (thetaEquiv pγ⁻¹)⁻¹ := by
    rw [thetaEquiv_mul, thetaEquiv_mul, thetaEquiv_inv, inv_inv, mul_assoc]
  have hmod : modTwoUnit (pγ * pk * pγ⁻¹).1.2 = monoN i := by
    change modTwoUnit (g₀ * pk.1.2 * g₀⁻¹) = monoN i
    rw [modTwoUnit_mul, modTwoUnit_mul, modTwoUnit_inv, ← hgψ]
    group
  have hmk : (QuotientGroup.mk (pγ * pk * pγ⁻¹).1.2 :
      latticeO ⧸ Subgroup.zpowers negOneO) = QuotientGroup.mk (monoAO i) := by
    rw [QuotientGroup.eq, mem_zpowers_negOneO_iff, ← modTwoUnit_eq_one_iff, modTwoUnit_mul,
      modTwoUnit_inv, hmod]
    exact mul_inv_cancel _
  have hi' : i = 1 ∨ i = 2 ∨ i = 6 := by simpa using hi
  have hmem : (⟨thetaEquiv (pγ * pk * pγ⁻¹), thetaEquiv_mem_Gvis _⟩ : Gvis) ∈ cosetR i := by
    rw [mem_cosetR_iff, piVis_thetaEquiv, piVis_cosetRep, hmk]
  obtain ⟨q, hq⟩ := (mem_cosetR_iff_exists i _).1 hmem
  exact ⟨i, hi', pγ⁻¹, q, hP ▸ hq⟩

theorem rhoEquiv_conjQ_cosetPair
    (i : ℕ) (x : Q) :
    rhoEquiv (conjQ (cosetPair i) x) =
      (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv x * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ :=
  (Visible.thetaEquiv_conj_rhoEquiv (cosetPair i) x).symm

theorem rhoEquiv_inv_mul_mul (q q' : Q) :
    rhoEquiv (q⁻¹ * q' * q) = rhoEquiv q * (rhoEquiv q' * (rhoEquiv q)⁻¹) := by
  rw [rhoEquiv_mul (q⁻¹ * q') q, rhoEquiv_mul q⁻¹ q', Short.rhoEquiv_inv q]

theorem conj_eq_of_mul_comm {G : Type*} [Group G] {h r r' : G} (H : h * r * r' = r' * (h * r)) :
    h * (r * (r' * r⁻¹)) * h⁻¹ = r' :=
  calc h * (r * (r' * r⁻¹)) * h⁻¹ = h * r * r' * r⁻¹ * h⁻¹ := by group
    _ = r' * (h * r) * r⁻¹ * h⁻¹ := by rw [H]
    _ = r' := by group

theorem noConfig_apply
    {i : ℕ} (hno : NoConfig i) {q s q' : Q}
    (hs : q * cosetW i * conjQ (cosetPair i) q = s) (h1 : IsShortCoord (coordOf s))
    (h2 : IsShortCoord (coordOf q')) (h3 : IsShortCoord (coordOf (q' * s))) (h4 : q' * s = s * q')
    (h5 : conjQ (cosetPair i) (q⁻¹ * q' * q) = q') : False := by
  subst hs
  exact hno q q' h1 h2 h3 h4 h5

theorem false_of_conj_mem_cosetR
    {i : ℕ} (hno : NoConfig i) (hi : i = 1 ∨ i = 2 ∨ i = 6)
    {K : SpaceB ≃ₗ[ℚ] SpaceB} {δ : Pvis} {q a b : Q}
    (hK : thetaEquiv δ * K * (thetaEquiv δ)⁻¹ =
      (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q)
    (hKK : K * K = rhoEquiv a) (hKb : K * rhoEquiv b = rhoEquiv b * K)
    (ha : IsShortCoord (coordOf a)) (hb : IsShortCoord (coordOf b))
    (hba : IsShortCoord (coordOf (b * a))) (hab : b * a = a * b) : False := by
  have hconj : ∀ r : Q, thetaEquiv δ * rhoEquiv r * (thetaEquiv δ)⁻¹ = rhoEquiv (conjQ δ r) :=
    fun r => Visible.thetaEquiv_conj_rhoEquiv δ r
  have hs : q * cosetW i * conjQ (cosetPair i) q = conjQ δ a := by
    have h1 : ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) *
        ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) =
        rhoEquiv (q * cosetW i * conjQ (cosetPair i) q) :=
      congrArg Subtype.val (mul_rho_sq hi q)
    have h2 : ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) *
        ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) = rhoEquiv (conjQ δ a) := by
      rw [← hK, ← hconj a, ← hKK]
      group
    exact rhoEquiv_injective (h1.symm.trans h2)
  have hcomm : ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) * rhoEquiv (conjQ δ b) =
      rhoEquiv (conjQ δ b) * ((cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q) := by
    rw [← hK, ← hconj b]
    calc thetaEquiv δ * K * (thetaEquiv δ)⁻¹ *
          (thetaEquiv δ * rhoEquiv b * (thetaEquiv δ)⁻¹) =
        thetaEquiv δ * (K * rhoEquiv b) * (thetaEquiv δ)⁻¹ := by group
      _ = thetaEquiv δ * (rhoEquiv b * K) * (thetaEquiv δ)⁻¹ := by rw [hKb]
      _ = _ := by group
  have hc : conjQ (cosetPair i) (q⁻¹ * conjQ δ b * q) = conjQ δ b := by
    apply rhoEquiv_injective
    rw [rhoEquiv_conjQ_cosetPair, rhoEquiv_inv_mul_mul]
    exact conj_eq_of_mul_comm hcomm
  have h3 : IsShortCoord (coordOf (conjQ δ b * conjQ δ a)) :=
    (congrArg (fun x : Q => IsShortCoord (coordOf x)) (map_mul (conjQ δ) b a)).mp
      (isShortCoord_conjQ δ hba)
  have h4 : conjQ δ b * conjQ δ a = conjQ δ a * conjQ δ b :=
    (map_mul (conjQ δ) b a).symm.trans ((congrArg (conjQ δ) hab).trans (map_mul (conjQ δ) a b))
  exact noConfig_apply hno hs (isShortCoord_conjQ δ ha) (isShortCoord_conjQ δ hb) h3 h4 hc

theorem no_sq_in_FE
    (hno : ∀ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 6) → NoConfig i) {k : MGriess}
    (hkF : k ∈ Subgroup.centralizer (FE : Set MGriess))
    (hkx : k ∈ Subgroup.centralizer ({xGriess} : Set MGriess))
    (hk2 : k * k ∈ FE) (hk2' : k * k ≠ 1) : False := by
  have hkG := mem_Gvis_of_mem_cent_xGriess hkx
  by_cases hπ : piVis ⟨(k : SpaceB ≃ₗ[ℚ] SpaceB), hkG⟩ = 1
  · rcases mul_self_mem_of_piVis_eq_one hkG hπ with h | h
    · exact hk2' h
    · exact xGriess_not_mem_FE (h ▸ hk2)
  · obtain ⟨a, b, c, ha, hb, hc, hfa, hbF, hcf⟩ := exists_triple_of_mem_FE hk2 hk2'
    have hKK : (k : SpaceB ≃ₗ[ℚ] SpaceB) * k = rhoEquiv a := congrArg Subtype.val hfa
    obtain ⟨i, hi, δ, q, hK⟩ := exists_conj_mem_cosetR hkG hπ hKK
    have hKb : (k : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv b = rhoEquiv b * k :=
      (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hkF _ hbF)).symm
    have hcba : c = b * a :=
      rhoGriess_injective (by rw [hcf, hfa, rhoGriess_mul])
    have haF : rhoGriess a ∈ FE := hfa ▸ hk2
    have hab : b * a = a * b :=
      rhoGriess_injective (by rw [rhoGriess_mul, rhoGriess_mul]; exact FE_comm _ haF _ hbF)
    exact false_of_conj_mem_cosetR (hno i hi) hi hK hKK hKb ha hb (hcba ▸ hc) hab

end CFSG.Monster.Existence
