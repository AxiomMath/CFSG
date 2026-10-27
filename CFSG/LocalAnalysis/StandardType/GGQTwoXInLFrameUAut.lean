module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUAutLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Phan
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private noncomputable def ggQTUa_extendPerm {N : ℕ} (S : Finset (Fin N))
    (τ : Equiv.Perm (Fin S.card)) : Equiv.Perm (Fin N) :=
  Equiv.Perm.subtypeCongrHom (fun i : Fin N => i ∈ S)
    (S.equivFin.trans (τ.trans S.equivFin.symm), 1)

private lemma ggQTUa_extendPerm_apply_mem {N : ℕ} {S : Finset (Fin N)}
    (τ : Equiv.Perm (Fin S.card)) {i : Fin N} (hi : i ∈ S) :
    ggQTUa_extendPerm S τ i =
      (S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩)) : Fin N) := by
  simp only [ggQTUa_extendPerm, Equiv.Perm.subtypeCongrHom_apply,
    Equiv.Perm.subtypeCongr.apply, dif_pos hi]
  rfl

private lemma ggQTUa_extendPerm_apply_notMem {N : ℕ} {S : Finset (Fin N)}
    (τ : Equiv.Perm (Fin S.card)) {i : Fin N} (hi : i ∉ S) :
    ggQTUa_extendPerm S τ i = i := by
  simp only [ggQTUa_extendPerm, Equiv.Perm.subtypeCongrHom_apply,
    Equiv.Perm.subtypeCongr.apply, dif_neg hi]
  rfl

private lemma ggQTUa_blockExt_permMatrix {N : ℕ} {K : Type} [Field K]
    (S : Finset (Fin N)) (τ : Equiv.Perm (Fin S.card)) :
    TableBUE.blockExt S (τ.permMatrix K) = (ggQTUa_extendPerm S τ).permMatrix K := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [TableBUE.blockExt, dif_pos hi, dif_pos hj]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, ggQTUa_extendPerm_apply_mem τ hi]
      by_cases h : τ (S.equivFin ⟨i, hi⟩) = S.equivFin ⟨j, hj⟩
      · have h' : (S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩)) : Fin N) = j := by
          rw [h]
          exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨j, hj⟩)
        rw [if_pos h, if_pos h']
      · have h' : (S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩)) : Fin N) ≠ j := by
          intro hh
          apply h
          have hh' : S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩)) = ⟨j, hj⟩ := Subtype.ext hh
          have := congrArg S.equivFin hh'
          simpa using this
        rw [if_neg h, if_neg h']
    · rw [TableBUE.blockExt, dif_pos hi, dif_neg hj]
      have hmem : (ggQTUa_extendPerm S τ i : Fin N) ∈ S := by
        rw [ggQTUa_extendPerm_apply_mem τ hi]
        exact (S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩))).2
      have hne : ggQTUa_extendPerm S τ i ≠ j := fun h => hj (h ▸ hmem)
      have hne' : (S.equivFin.symm (τ (S.equivFin ⟨i, hi⟩)) : Fin N) ≠ j := by
        intro h
        exact hne (by rw [ggQTUa_extendPerm_apply_mem τ hi]; exact h)
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, ggQTUa_extendPerm_apply_mem τ hi, if_neg hne']
  · rw [TableBUE.blockExt, dif_neg hi]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, ggQTUa_extendPerm_apply_notMem τ hi, Matrix.one_apply]

private lemma ggQTUa_permMatrix_conj_diag {N : ℕ} {K : Type} [Field K]
    (σ : Equiv.Perm (Fin N)) (ω : Kˣ) (v : Fin N → ZMod 3) :
    σ.permMatrix K * Matrix.diagonal (fun i => ((ω ^ (v i).val : Kˣ) : K)) *
        (σ.permMatrix K)⁻¹ =
      Matrix.diagonal (fun i => ((ω ^ (v (σ i)).val : Kˣ) : K)) := by
  have hσinv : (σ.permMatrix K)⁻¹ = (σ⁻¹).permMatrix K := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  rw [hσinv, TypeANbrDvd.permMatrix_mul_diagonal_mul_inv]
  rfl

private lemma ggQTUa_sumZero {n : ℕ} {v : ↥(GGQTwoXInLAug n)} :
    ∑ i, (v : Fin (n + 1) → ZMod 3) i = 0 := by
  have h := LinearMap.mem_ker.mp v.2
  rw [LinearMap.sum_apply] at h
  simpa using h

private noncomputable def ggQTUa_permLin {n : ℕ} (ρ : Equiv.Perm (Fin (n + 1))) :
    ↥(GGQTwoXInLAug n) ≃ₗ[ZMod 3] ↥(GGQTwoXInLAug n) :=
  LinearEquiv.mk
    { toFun := fun v => ⟨fun i => (v : Fin (n + 1) → ZMod 3) (ρ i), by
        rw [LinearMap.mem_ker, LinearMap.sum_apply]
        change ∑ i, (v : Fin (n + 1) → ZMod 3) (ρ i) = 0
        rw [Equiv.sum_comp ρ]
        exact ggQTUa_sumZero⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c v
        apply Subtype.ext
        rfl }
    (fun v => ⟨fun i => (v : Fin (n + 1) → ZMod 3) (ρ⁻¹ i), by
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      change ∑ i, (v : Fin (n + 1) → ZMod 3) (ρ⁻¹ i) = 0
      rw [Equiv.sum_comp ρ⁻¹]
      exact ggQTUa_sumZero⟩)
    (by intro v; apply Subtype.ext; funext i; simp)
    (by intro v; apply Subtype.ext; funext i; simp)

private lemma ggQTUa_lin_apply {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1))
    (ε : Equiv.Perm (Fin (Finset.univ.erase c).card) ≃*
      ↥(ggAutomizer (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)).range Bs))
    (hε : ∀ (σ : Equiv.Perm (Fin (Finset.univ.erase c).card)) (s : ↥Bs),
      ((((ε σ : ↥(ggAutomizer (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)).range Bs)) :
          MulAut ↥Bs) s : ↥Bs) : G) =
        (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)) (ggPermSU (K := K) (f := 1) σ⁻¹) * (s : G) *
          ((ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c))
            (ggPermSU (K := K) (f := 1) σ⁻¹))⁻¹)
    (τ : Equiv.Perm (Fin (Finset.univ.erase c).card)) :
    ggLin (p := 3) C.ι (ε τ) =
      ggQTUa_permLin (ggQTUa_extendPerm (Finset.univ.erase c) τ⁻¹) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.erase c
  let ρ : Equiv.Perm (Fin (n + 1)) := ggQTUa_extendPerm S τ⁻¹
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, x = C.ι (Additive.ofMul b) := by
    refine ⟨Additive.toMul (C.ι.symm x), ?_⟩
    simpa using (AddEquiv.apply_symm_apply C.ι x).symm
  rw [ggLin_apply_ofMul]
  let v : Fin (n + 1) → ZMod 3 := fun i => (C.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i
  let w : Fin (n + 1) → ZMod 3 := fun i => v (ρ i)
  have hw : w ∈ GGQTwoXInLAug n := by
    rw [LinearMap.mem_ker, LinearMap.sum_apply]
    change ∑ i, v (ρ i) = 0
    rw [Equiv.sum_comp ρ]
    exact ggQTUa_sumZero
  let b' : ↥Bs := Additive.toMul (C.ι.symm ⟨w, hw⟩)
  have hιb' : (C.ι (Additive.ofMul b') : Fin (n + 1) → ZMod 3) = w := by
    simp [b']
  obtain ⟨s, hsmat, hsφ⟩ := C.diag b
  obtain ⟨s', hs'mat, hs'φ⟩ := C.diag b'
  let xτ : ↥(unitarySU 2 1 K S.card) := ggQTwoXInLU_suEquiv C S (ggPermSU (K := K) (f := 1) τ⁻¹)
  let P : ↥(unitarySU 2 1 K (n + 1)) := TableBUE.blockExtSU S C.field xτ
  have hxτ : ((xτ : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
      (τ⁻¹).permMatrix K := rfl
  have hPmat : ((P : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      ρ.permMatrix K := by
    rw [TableBUE.coe_blockExtSU, hxτ]
    change TableBUE.blockExt S ((τ⁻¹).permMatrix K) = ρ.permMatrix K
    rw [show ρ = ggQTUa_extendPerm S τ⁻¹ from rfl, ggQTUa_blockExt_permMatrix]
  have hψP : (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)) (ggPermSU (K := K) (f := 1) τ⁻¹) =
      C.φ P := rfl
  have hPinvMat : ((((P⁻¹ : ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K) = (ρ.permMatrix K)⁻¹ := by
    rw [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv, hPmat]
  have hconj : (C.φ P) * (b : G) * (C.φ P)⁻¹ = (b' : G) := by
    rw [← hsφ, ← hs'φ]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      hPmat, hsmat, coe_diagHom, hs'mat, coe_diagHom, hPinvMat]
    rw [hιb']
    change (ρ.permMatrix K * Matrix.diagonal (fun i => ((C.ω ^ (v i).val : Kˣ) : K))) *
      (ρ.permMatrix K)⁻¹ =
      Matrix.diagonal (fun i => ((C.ω ^ (v (ρ i)).val : Kˣ) : K))
    exact ggQTUa_permMatrix_conj_diag ρ C.ω v
  let eτ : MulAut ↥Bs := (ε τ : ↥(ggAutomizer (ggQTwoXInLU_blockCoverSU C S).range Bs))
  have hεb : ((eτ b : ↥Bs) : G) = C.φ P * (b : G) * (C.φ P)⁻¹ := by
    rw [show ((eτ b : ↥Bs) : G) = (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c))
        (ggPermSU (K := K) (f := 1) τ⁻¹) * (b : G) *
        ((ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c))
          (ggPermSU (K := K) (f := 1) τ⁻¹))⁻¹ from hε τ b]
    rw [show (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)) (ggPermSU (K := K) (f := 1) τ⁻¹) =
      C.φ P from hψP]
  have hb'b : ((eτ b : ↥Bs) : G) = (b' : G) := hεb.trans hconj
  have hb' : eτ b = b' := Subtype.ext hb'b
  rw [hb']
  apply Subtype.ext
  funext i
  change (C.ι (Additive.ofMul b') : Fin (n + 1) → ZMod 3) i = v (ρ i)
  rw [hιb']

private noncomputable def ggQTUa_eSUFull {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) :
    Su K 2 1 (n + 1) ≃* ↥(unitarySU 2 1 K (n + 1)) :=
  letI : Fact (Nat.Prime 2) := ⟨C.field.prime⟩
  letI : CharP K 2 := C.field.charP
  MulEquiv.subgroupCongr
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1)
      (by rw [C.field.card]; norm_num) (n + 1))

private lemma ggQTUa_permSU_mem_blockSU {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ c = c) :
    ggQTUa_eSUFull C (ggPermSU (K := K) (f := 1) σ) ∈
      TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase c) := by
  classical
  rw [TableBUE.mem_blockSU]
  change TableBUE.IsBlockOn (Finset.univ.erase c) (σ.permMatrix K)
  intro i j hij
  simp only [TableBUE.IsBlockOn, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Matrix.one_apply]
  rcases hij with hi | hj
  · have hic : i = c := by
      by_contra h
      exact hi (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)
    subst hic
    rw [hσ]
  · have hjc : j = c := by
      by_contra h
      exact hj (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
    subst j
    by_cases h : i = c
    · subst h
      rw [hσ]
    · have hσi : σ i ≠ c := by
        intro hh
        apply h
        exact σ.injective (by rw [hh, hσ])
      rw [if_neg hσi, if_neg h]

private lemma ggQTUa_conj_perm_element {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K)
    (σ : Equiv.Perm (Fin (n + 1))) (P : ↥(unitarySU 2 1 K (n + 1)))
    (hPmat : ((P : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      σ.permMatrix K) (b : ↥Bs) :
    ∃ b' : ↥Bs, ((C.ι (Additive.ofMul b') : Fin (n + 1) → ZMod 3) =
        fun i => (C.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) (σ i)) ∧
      C.φ P * (b : G) * (C.φ P)⁻¹ = (b' : G) := by
  classical
  let v : Fin (n + 1) → ZMod 3 := fun i => (C.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i
  let w : Fin (n + 1) → ZMod 3 := fun i => v (σ i)
  have hw : w ∈ GGQTwoXInLAug n := by
    rw [LinearMap.mem_ker, LinearMap.sum_apply]
    change ∑ i, v (σ i) = 0
    rw [Equiv.sum_comp σ]
    exact ggQTUa_sumZero
  let b' : ↥Bs := Additive.toMul (C.ι.symm ⟨w, hw⟩)
  have hιb' : (C.ι (Additive.ofMul b') : Fin (n + 1) → ZMod 3) = w := by
    simp [b']
  obtain ⟨s, hsmat, hsφ⟩ := C.diag b
  obtain ⟨s', hs'mat, hs'φ⟩ := C.diag b'
  have hPinvMat : ((((P⁻¹ : ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K) = (σ.permMatrix K)⁻¹ := by
    rw [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv, hPmat]
  refine ⟨b', hιb', ?_⟩
  rw [← hsφ, ← hs'φ, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    hPmat, hsmat, coe_diagHom, hs'mat, coe_diagHom, hPinvMat]
  rw [hιb']
  change (σ.permMatrix K * Matrix.diagonal (fun i => ((C.ω ^ (v i).val : Kˣ) : K))) *
    (σ.permMatrix K)⁻¹ =
    Matrix.diagonal (fun i => ((C.ω ^ (v (σ i)).val : Kˣ) : K))
  exact ggQTUa_permMatrix_conj_diag σ C.ω v

theorem ggQTwoXInLU_automizer {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hn6 : 6 ≤ n)
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1))
    (hcent : Nat.card ↥(B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase c)).map C.φ : Subgroup G) :
        Set G)) = 3) :
    (ggAutomizer ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase c)).map C.φ) Bs).map
        (ggLin (p := 3) C.ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ c = c ∧
        ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
          ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
            (v : Fin (n + 1) → ZMod 3) (σ i)} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨C.field.prime⟩
  haveI : CharP K 2 := C.field.charP
  set S : Finset (Fin (n + 1)) := Finset.univ.erase c with hS_def
  have hrange : (ggQTwoXInLU_blockCoverSU C S).range =
      (TableBUE.blockSU (K := K) (n := 1) S).map C.φ := ggQTwoXInLU_blockCoverSU_range C S
  rw [← hrange]
  obtain ⟨ε, hε, -⟩ := ggNSDiag_automizer_perm
    (p := 3) (f := 1) (ggQTwoXInLU_blockCover_localHyp hS C c hcent hn6) (ggQTwoXInLU_blockCover_actsDiag C S)
  apply le_antisymm
  · rintro y ⟨f, hf, rfl⟩
    obtain ⟨σ, hσ⟩ := ε.surjective ⟨f, hf⟩
    have hσ' : (ε σ : MulAut ↥Bs) = f := congrArg Subtype.val hσ
    rw [← hσ', ggQTUa_lin_apply C c ε hε σ]
    apply Subgroup.subset_closure
    refine ⟨ggQTUa_extendPerm S σ⁻¹, ?_, ?_⟩
    · exact ggQTUa_extendPerm_apply_notMem σ⁻¹ (by simp)
    · intro v i
      rfl
  · rw [Subgroup.closure_le]
    rintro T ⟨σ, hσ, hT⟩
    have hT' : T = ggQTUa_permLin σ := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      funext i
      exact hT v i
    rw [hT']
    let P : ↥(unitarySU 2 1 K (n + 1)) := ggQTUa_eSUFull C (ggPermSU (K := K) (f := 1) σ)
    have hPblock : P ∈ TableBUE.blockSU (K := K) (n := 1) S :=
      ggQTUa_permSU_mem_blockSU C c σ hσ
    have hPmat : ((P : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        σ.permMatrix K := rfl
    let g : G := C.φ P
    have hgX : g ∈ (ggQTwoXInLU_blockCoverSU C S).range := by
      rw [ggQTwoXInLU_blockCoverSU_range]
      exact ⟨P, hPblock, rfl⟩
    have hN : g ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        obtain ⟨b', -, hb'g⟩ := ggQTUa_conj_perm_element C σ P hPmat ⟨b, hb⟩
        rw [hb'g]
        exact b'.2
      · intro hbconj
        let b'' : ↥Bs := ⟨g * b * g⁻¹, hbconj⟩
        have hσinv : σ⁻¹ c = c := by
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact hσ.symm
        let P' : ↥(unitarySU 2 1 K (n + 1)) :=
          ggQTUa_eSUFull C (ggPermSU (K := K) (f := 1) σ⁻¹)
        have hP'mat : ((P' : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
            (σ⁻¹).permMatrix K := rfl
        have hperm_inv : ggPermSU (K := K) (f := 1) σ⁻¹ =
            (ggPermSU (K := K) (f := 1) σ)⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          rw [← ggNSPosPA_permSU_mul_anti' (σ := σ⁻¹) (τ := σ)]
          rw [inv_mul_cancel]
          apply Subtype.ext
          simp only [ggPermSU, Matrix.permMatrix_one]
          exact map_one (Matrix.SpecialLinearGroup.toGL (n := Fin (n + 1)) (R := K))
        have hP'inv : P' = P⁻¹ := by
          simp only [P', P]
          rw [hperm_inv, map_inv]
        have hg' : C.φ P' = g⁻¹ := by
          rw [hP'inv]
          change C.φ (P⁻¹) = (C.φ P)⁻¹
          rw [map_inv]
        obtain ⟨b''', -, hb'''g⟩ := ggQTUa_conj_perm_element C σ⁻¹ P' hP'mat b''
        have hb_eq : b = b''' := by
          rw [← hb'''g, hg']
          change b = g⁻¹ * (g * b * g⁻¹) * (g⁻¹)⁻¹
          group
        rw [hb_eq]
        exact b'''.2
    let f : MulAut ↥Bs := Subgroup.normalizerMonoidHom Bs ⟨g, hN⟩
    have hf_ind : f ∈ ggInduced (ggQTwoXInLU_blockCoverSU C S).range Bs :=
      ⟨g, hgX, hN, fun b => by
        exact Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨g, hN⟩ b⟩
    have hf_aut : f ∈ ggAutomizer (ggQTwoXInLU_blockCoverSU C S).range Bs := Subgroup.subset_closure hf_ind
    have hLin : ggLin (p := 3) C.ι f = ggQTUa_permLin σ := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, v = C.ι (Additive.ofMul b) := by
        refine ⟨Additive.toMul (C.ι.symm v), ?_⟩
        simp
      rw [ggLin_apply_ofMul]
      apply Subtype.ext
      funext i
      obtain ⟨b', hb'ι, hb'g⟩ := ggQTUa_conj_perm_element C σ P hPmat b
      have hfb : f b = b' := Subtype.ext (by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact hb'g)
      rw [hfb]
      exact congrFun hb'ι i
    exact ⟨f, hf_aut, hLin⟩

end CFSG.StandardType

end

