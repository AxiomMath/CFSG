module

public import CFSG.RankThree.PartOne.K159G.BlockIdent
public import CFSG.RankThree.PartOne.S15K.AutBlock
public import CFSG.RankThree.PartOne.CTP.StdBlocks

public section

namespace CFSG.RankThree.PartOne.K159G

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
  CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryBlock

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem unitarySU_le_idSU {w : GL (Fin 5) K} (hw : w ∈ unitarySU 2 f K 5) : w ∈ idSU h := by
  rw [mem_unitarySU_iff h] at hw
  rw [mem_gramSU_iff_unitary]
  refine ⟨?_, hw.1⟩
  rw [mem_primeFormUnitary]
  simpa [idGram] using hw.2

theorem blk_le_idSU {i j : Fin 5} (hij : i ≠ j) : blk h hij ≤ idSU h :=
  fun _ hw => unitarySU_le_idSU h (blk_le_unitarySU hij hw)

@[expose] noncomputable def planeSU (i j : Fin 5) (hij : i ≠ j) : Subgroup ↥(idSU h) :=
  (blk h hij).subgroupOf (idSU h)

@[expose] noncomputable def planeP (i j : Fin 5) (hij : i ≠ j) :
    Subgroup (primeFormP h (idGram K 5)) :=
  (planeSU h i j hij).map (idPi h)

theorem planeP_swap {i j : Fin 5} (hij : i ≠ j) : planeP h j i hij.symm = planeP h i j hij := by
  unfold planeP planeSU
  rw [(CTP.blk_swap h hij).symm]

theorem mem_iSup_planeSU_of_mem_planeGen (B : Finset (Fin 5)) {w : ↥(idSU h)}
    (hw : (w : GL (Fin 5) K) ∈ planeGen h B) :
    w ∈ ⨆ q : {q : Fin 5 × Fin 5 // q.1 ∈ B ∧ q.2 ∈ B ∧ q.1 ≠ q.2},
      planeSU h q.1.1 q.1.2 q.2.2.2 := by
  have key : ∀ x : GL (Fin 5) K, x ∈ planeGen h B → ∃ hx : x ∈ idSU h,
      (⟨x, hx⟩ : ↥(idSU h)) ∈ ⨆ q : {q : Fin 5 × Fin 5 // q.1 ∈ B ∧ q.2 ∈ B ∧ q.1 ≠ q.2},
        planeSU h q.1.1 q.1.2 q.2.2.2 := by
    intro x hx
    refine planeGen_induction (C := fun x => ∃ hx : x ∈ idSU h,
      (⟨x, hx⟩ : ↥(idSU h)) ∈ ⨆ q : {q : Fin 5 × Fin 5 // q.1 ∈ B ∧ q.2 ∈ B ∧ q.1 ≠ q.2},
        planeSU h q.1.1 q.1.2 q.2.2.2) ?_ ⟨one_mem _, one_mem _⟩ ?_ hx
    · intro i hi j hj hij g hg
      refine ⟨blk_le_idSU h hij hg, ?_⟩
      exact Subgroup.mem_iSup_of_mem (⟨(i, j), hi, hj, hij⟩ :
        {q : Fin 5 × Fin 5 // q.1 ∈ B ∧ q.2 ∈ B ∧ q.1 ≠ q.2}) (show _ ∈ planeSU h i j hij from hg)
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨mul_mem ha hb, mul_mem ha' hb'⟩
  obtain ⟨hx, hmem⟩ := key _ hw
  exact hmem

theorem blockSU_map_le_planes (hq : 4 ≤ 2 ^ f) {d : Fin 5 → Kˣ} {g : ↥(idU h)}
    (hg : (g : GL (Fin 5) K) = diagU d) (a : BlockIdx (toLinU h 5 g)) {μ : K}
    (hax : (a.1 : K[X]) = X - C μ) (hμ : h.bar μ * μ = 1) :
    (blockSU h g a).map (idPi h) ≤
      ⨆ q : {q : Fin 5 × Fin 5 // q.1 ≠ q.2 ∧ d q.1 = d q.2}, planeP h q.1.1 q.1.2 q.2.1 := by
  rintro _ ⟨w, hw, rfl⟩
  have h1 := mem_iSup_planeSU_of_mem_planeGen h (eigIdx d μ)
    (blockSU_le_planeGen h hq hg a hax hμ w hw)
  have h2 := Subgroup.mem_map_of_mem (idPi h) h1
  rw [Subgroup.map_iSup] at h2
  refine (iSup_le (fun q => ?_) : (⨆ q : {q : Fin 5 × Fin 5 // q.1 ∈ eigIdx d μ ∧ q.2 ∈ eigIdx d μ ∧
      q.1 ≠ q.2}, (planeSU h q.1.1 q.1.2 q.2.2.2).map (idPi h)) ≤ _) h2
  have hd : d q.1.1 = d q.1.2 := by
    apply Units.ext
    rw [mem_eigIdx.1 q.2.1, mem_eigIdx.1 q.2.2.1]
  exact le_iSup (fun q : {q : Fin 5 × Fin 5 // q.1 ≠ q.2 ∧ d q.1 = d q.2} =>
    planeP h q.1.1 q.1.2 q.2.1) ⟨q.1, q.2.2.2, hd⟩

theorem perfect_le_planes {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {d : Fin 5 → Kˣ} {g : ↥(idU h)} (hg : (g : GL (Fin 5) K) = diagU d) (hgp : g ^ p = 1)
    {Y : Subgroup (primeFormP h (idGram K 5))}
    (hY : Y ≤ fixedSub (primeFormConjHom h (idGram K 5) g)) (hYp : ⁅Y, Y⁆ = Y) :
    Y ≤ ⨆ q : {q : Fin 5 × Fin 5 // q.1 ≠ q.2 ∧ d q.1 = d q.2}, planeP h q.1.1 q.1.2 q.2.1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) hpq
    omega
  have hgp' : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) 1 := by
    rw [← Subgroup.coe_pow, hgp]
    ext
    simp
  have HU := unitaryPrimaryData_of_pow_scalar h hp hp2 g hgp'
  have hle := le_iSup_map_of_isPerfect (idPi_surjective h) (ker_idPi_le_center h)
    (fun w => idPi_idConj h g w) (idConj_fix_ker h g) (blockSU h g)
    (derived_fixed_le_iSup HU hq4) hY hYp
  refine hle.trans (iSup_le fun a => ?_)
  obtain ⟨μ, hax, -, hμ⟩ := linear_of_mult_two h hp hp5 hpq g (c := 1) (by simp) hgp' _ rfl a.1 a.2
  exact blockSU_map_le_planes h hq4 hg a hax hμ

theorem eq_one_of_mem_blk_of_scalar {i j : Fin 5} (hij : i ≠ j) {w : GL (Fin 5) K} (hw : w ∈ blk h hij)
    {c : Kˣ} (hc : w = GeneralLinearGroup.scalar (Fin 5) c) : w = 1 := by
  classical
  have hex : ∀ i j : Fin 5, ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hex i j
  have hfix := blk_le_fixOut (h := h) (B := {i, j}) (by simp) (by simp) hij hw k (by simp [hki, hkj])
  have hck : c = 1 := by
    have := congrFun hfix k
    rw [hc, GeneralLinearGroup.coe_scalar] at this
    simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using this
  rw [hc, hck]
  ext
  simp

theorem idPi_injective_planeSU {i j : Fin 5} (hij : i ≠ j) :
    Function.Injective ((idPi h).domRestrict (planeSU h i j hij)) := by
  intro x y hxy
  have hxy' : ((x : ↥(idSU h)) : ↥(idSU h) ⧸ normOneScalars h (idSU h) 5) =
      ((y : ↥(idSU h)) : _) := hxy
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.1 hxy'
  have hmem : (((x : ↥(idSU h))⁻¹ * (y : ↥(idSU h)) : ↥(idSU h)) : GL (Fin 5) K) ∈ blk h hij :=
    mul_mem (inv_mem x.2) y.2
  have h1 := eq_one_of_mem_blk_of_scalar h hij hmem hc
  have h2 : (x : ↥(idSU h))⁻¹ * (y : ↥(idSU h)) = 1 := Subtype.ext h1
  exact Subtype.ext (inv_mul_eq_one.1 h2)

theorem card_planeP {i j : Fin 5} (hij : i ≠ j) : Nat.card (planeP h i j hij) = Nat.card (blk h hij) := by
  have h1 : planeP h i j hij = ((idPi h).domRestrict (planeSU h i j hij)).range :=
    (MonoidHom.domRestrict_range (planeSU h i j hij) (idPi h)).symm
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective (idPi_injective_planeSU h hij)).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blk_le_idSU h hij)).toEquiv

end CFSG.RankThree.PartOne.K159G
