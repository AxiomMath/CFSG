module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316O2
public import CFSG.Quasithin.Vol2.Ch11SecS12T
public import CFSG.Quasithin.Vol2.Ch11SecB414PB
public import CFSG.Quasithin.Vol2.Ch11SecB414PA
public import CFSG.Quasithin.Vol2.Ch11SecS12O
public import CFSG.Quasithin.Vol2.Ch11SecS12Q

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.LieType.SteinbergBR.BlockPar
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL uSL_mul uSL_inv uSL_zero
  uSL_injective)
open scoped MatrixGroups Matrix Pointwise

namespace L4316

theorem card_sup_mul_inf {G : Type} [Group G] [Finite G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(X ⊔ N) * Nat.card ↥(X ⊓ N) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (_root_.sup_le hXN Subgroup.le_normalizer)
  have : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
    fun x hx => mem_normalizer_inf (hXN hx) (Subgroup.le_normalizer hx)
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card ↥(X ⊓ N) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

variable {F : Type} [Field F]

@[expose] noncomputable def slPGL (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 3) F →* PGL3 F :=
  Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL

theorem slPGL_apply (x : Matrix.SpecialLinearGroup (Fin 3) F) :
    slPGL F x = Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL x) := rfl

theorem eq_uSL_of_mem_radU {r : Matrix.SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ radU F (flagSpace 3 F 1)) :
    r = uSL ((r : Matrix (Fin 3) (Fin 3) F) 0 1) ((r : Matrix (Fin 3) (Fin 3) F) 0 2) 0 := by
  have hd := S12.radU_diag hr
  have hrow : ∀ i : Fin 3, 1 ≤ (i : ℕ) → ∀ k : Fin 3,
      (r : Matrix (Fin 3) (Fin 3) F) i k = if i = k then 1 else 0 := fun i hi k =>
    S12.radU_row hr hi k
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_uSL]
  fin_cases i
  · fin_cases j
    · simp [uMat, hd 0]
    · simp [uMat]
    · simp [uMat]
  · have := hrow 1 (by simp)
    fin_cases j <;> simp [uMat, this]
  · have := hrow 2 (by simp)
    fin_cases j <;> simp [uMat, this]

theorem blkSL_mem_stabilizer (g : SL(2, F)) : SL3Pt.blkSL g ∈ stabilizer (flagSpace 3 F 1) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, mem_flagSpace] at hw
  rw [mem_flagSpace]
  have h1 := hw 1 (by simp)
  have h2 := hw 2 (by simp)
  intro j hj
  change (SL3Pt.blk (g : Matrix (Fin 2) (Fin 2) F) *ᵥ w) j = 0
  rw [SL3Pt.blk_mulVec]
  fin_cases j
  · simp at hj
  · simp [h1, h2]
  · simp [h1, h2]

variable [Finite F] [CharP F 2]

theorem pCoreOf_Ptheta_zero_le (hF : Nat.card F = 4) {N : Subgroup (PGL3 F)}
    (hN : N ≤ pCoreOf 2 (Ptheta F 0)) (hBN : Ptheta F 0 ≤ Subgroup.normalizer (N : Set (PGL3 F)))
    (hne : N ≠ ⊥) : pCoreOf 2 (Ptheta F 0) ≤ N := by
  have hlevi : ∀ g : SL(2, F), slPGL F (SL3Pt.blkSL g) ∈ Ptheta F 0 := fun g =>
    S12.mk_mem_Ptheta (j := 0) (blkSL_mem_stabilizer g)
  have hconj : ∀ g : SL(2, F), ∀ x ∈ N,
      slPGL F (SL3Pt.blkSL g) * x * (slPGL F (SL3Pt.blkSL g))⁻¹ ∈ N := fun g x hx =>
    (Subgroup.mem_normalizer_iff.mp (hBN (hlevi g)) x).mp hx
  obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨r, hr, rfl⟩ := (S12.mem_pCoreOf_Ptheta hF (j := 0)).mp (hN hxN)
  have hr' := eq_uSL_of_mem_radU hr
  set a := (r : Matrix (Fin 3) (Fin 3) F) 0 1
  set b := (r : Matrix (Fin 3) (Fin 3) F) 0 2
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hx1'
    rw [hr', h.1, h.2, uSL_zero, map_one, map_one]
  obtain ⟨g₁, hg₁⟩ := SL3Pt.exists_blkSL_conj hab
  have h1 : slPGL F (uSL 1 0 0) ∈ N := by
    have := hconj g₁ _ hxN
    rw [← slPGL_apply, hr', ← map_inv, ← map_mul, ← map_mul, hg₁] at this
    exact this
  intro y hy
  obtain ⟨r', hr'', rfl⟩ := (S12.mem_pCoreOf_Ptheta hF (j := 0)).mp hy
  rw [← slPGL_apply, eq_uSL_of_mem_radU hr'']
  set c := (r' : Matrix (Fin 3) (Fin 3) F) 0 1
  set d := (r' : Matrix (Fin 3) (Fin 3) F) 0 2
  by_cases hcd : c = 0 ∧ d = 0
  · rw [hcd.1, hcd.2, uSL_zero, map_one]
    exact N.one_mem
  have hcd' : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    exact hcd h
  obtain ⟨g₂, hg₂⟩ := SL3Pt.exists_blkSL_conj hcd'
  have e : uSL c d 0 = (SL3Pt.blkSL g₂)⁻¹ * uSL 1 0 0 * SL3Pt.blkSL g₂ := by
    rw [← hg₂]
    group
  have hz : (slPGL F (SL3Pt.blkSL g₂))⁻¹ ∈ Ptheta F 0 := (Ptheta F 0).inv_mem (hlevi g₂)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hBN hz) _).mp h1
  rw [inv_inv] at h2
  rw [e, map_mul, map_mul, map_inv]
  exact h2

theorem pCoreOf_Ptheta_zero_comm (hF : Nat.card F = 4) {x y : PGL3 F}
    (hx : x ∈ pCoreOf 2 (Ptheta F 0)) (hy : y ∈ pCoreOf 2 (Ptheta F 0)) : x * y = y * x := by
  obtain ⟨r, hr, rfl⟩ := (S12.mem_pCoreOf_Ptheta hF (j := 0)).mp hx
  obtain ⟨r', hr', rfl⟩ := (S12.mem_pCoreOf_Ptheta hF (j := 0)).mp hy
  rw [← slPGL_apply, ← slPGL_apply, ← map_mul, ← map_mul, eq_uSL_of_mem_radU hr,
    eq_uSL_of_mem_radU hr', uSL_mul, uSL_mul]
  congr 2 <;> ring

theorem card_Ptheta (hF : Nat.card F = 4) (j : Fin 2) :
    Nat.card ↥(Ptheta F j) = 960 ∧ Nat.card ↥(pCoreOf 2 (Ptheta F j)) = 16 := by
  obtain ⟨h1, h2, -⟩ := parab34_structure hF j
  rw [dInf_parab34 hF j] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [Ptheta, Subgroup.card_map_of_injective thetaP_injective, h1]
  · rw [Ptheta, C11P9A.pCoreOf_map_of_injective (thetaP F) thetaP_injective,
      Subgroup.card_map_of_injective thetaP_injective, pCoreOf,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h2]

theorem eq_Ptheta_zero_of_le (hF : Nat.card F = 4) {H : Subgroup (PGL3 F)} (hHB : H ≤ Ptheta F 0)
    (hcard : Nat.card H = 60 * Nat.card ↥(pCoreOf 2 H)) (hne : pCoreOf 2 H ≠ ⊥) :
    H = Ptheta F 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := Ptheta F 0 with hB
  set O := pCoreOf 2 B with hO
  obtain ⟨hcB, hcO⟩ := card_Ptheta hF 0
  have hBO : B ≤ Subgroup.normalizer (O : Set (PGL3 F)) := le_normalizer_pCoreOf 2 B
  have hHO : H ≤ Subgroup.normalizer (O : Set (PGL3 F)) := hHB.trans hBO
  have hinf : H ⊓ O ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun h hh => mem_normalizer_inf (Subgroup.le_normalizer hh) (hHO hh))
      ((pCoreOf_isPGroup 2 B).to_le inf_le_right)
  have hprod := card_sup_mul_inf hHO
  have hsupB : H ⊔ O ≤ B := _root_.sup_le hHB (pCoreOf_le 2 B)
  have h1 : Nat.card ↥(H ⊔ O) ≤ 960 := hcB ▸ Subgroup.card_le_of_le hsupB
  have h2 : Nat.card ↥(H ⊓ O) ≤ Nat.card ↥(pCoreOf 2 H) := Subgroup.card_le_of_le hinf
  have hpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
  rw [hcard, hcO] at hprod
  have h3 : Nat.card ↥(H ⊔ O) = 960 := by
    by_contra hne'
    have h4 : Nat.card ↥(H ⊔ O) < 960 := lt_of_le_of_ne h1 hne'
    have h5 : Nat.card ↥(H ⊔ O) * Nat.card ↥(H ⊓ O) < 960 * Nat.card ↥(pCoreOf 2 H) :=
      calc Nat.card ↥(H ⊔ O) * Nat.card ↥(H ⊓ O) ≤ Nat.card ↥(H ⊔ O) * Nat.card ↥(pCoreOf 2 H) :=
            Nat.mul_le_mul_left _ h2
        _ < 960 * Nat.card ↥(pCoreOf 2 H) := Nat.mul_lt_mul_of_pos_right h4 hpos
    rw [hprod] at h5
    linarith
  have hsup : H ⊔ O = B := Subgroup.eq_of_le_of_card_ge hsupB (by rw [h3, hcB])
  have h6 : Nat.card ↥(H ⊓ O) = Nat.card ↥(pCoreOf 2 H) := by
    rw [h3] at hprod
    have : 960 * Nat.card ↥(H ⊓ O) = 960 * Nat.card ↥(pCoreOf 2 H) := by rw [hprod]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hinfeq : H ⊓ O = pCoreOf 2 H := Subgroup.eq_of_le_of_card_ge hinf h6.ge
  have hnorm : B ≤ Subgroup.normalizer ((H ⊓ O : Subgroup (PGL3 F)) : Set (PGL3 F)) := by
    rw [← hsup]
    refine _root_.sup_le (fun h hh => mem_normalizer_inf (Subgroup.le_normalizer hh) (hHO hh))
      fun o ho => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have e : o * z * o⁻¹ = z := by
        rw [pCoreOf_Ptheta_zero_comm hF ho hz.2, mul_inv_cancel_right]
      rw [e]
      exact hz
    · intro hz
      have hz' : z = o⁻¹ * (o * z * o⁻¹) * o := by group
      have hzO : z ∈ O := by
        rw [hz']
        exact O.mul_mem (O.mul_mem (O.inv_mem ho) hz.2) ho
      have e : o * z * o⁻¹ = z := by
        rw [pCoreOf_Ptheta_zero_comm hF ho hzO, mul_inv_cancel_right]
      rw [e] at hz
      exact hz
  have hle := pCoreOf_Ptheta_zero_le hF inf_le_right hnorm (hinfeq ▸ hne)
  have hOH : O ≤ H := hle.trans inf_le_left
  rw [← hsup, sup_eq_left.mpr hOH]

theorem exists_aut_map_le (hF : Nat.card F = 4) {H : Subgroup (PGL3 F)} (hp : ⁅H, H⁆ = H)
    (hne : pCoreOf 2 H ≠ ⊥) : ∃ φ : PGL3 F ≃* PGL3 F, H.map φ.toMonoidHom ≤ Ptheta F 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHR : H ≤ (thetaP F).range := by
    rw [range_thetaP_eq hF, ← hp]
    exact Subgroup.commutator_mono le_top le_top
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup (projectiveSL 3 F), H' = H.comap (thetaP F) := ⟨_, rfl⟩
  have hH'm : H'.map (thetaP F) = H := hH' ▸ Subgroup.map_comap_eq_self hHR
  obtain ⟨U, hU⟩ : ∃ U : Subgroup (projectiveSL 3 F), U = (pCoreOf 2 H).comap (thetaP F) :=
    ⟨_, rfl⟩
  have hUm : U.map (thetaP F) = pCoreOf 2 H :=
    hU ▸ Subgroup.map_comap_eq_self ((pCoreOf_le 2 H).trans hHR)
  have hU1 : U ≠ ⊥ := by
    intro h
    apply hne
    rw [← hUm, h, Subgroup.map_bot]
  have hU2 : IsPGroup 2 ↥U :=
    hU ▸ (pCoreOf_isPGroup 2 H).comap_of_injective (thetaP F) thetaP_injective
  have hH'N : H' ≤ Subgroup.normalizer (U : Set (projectiveSL 3 F)) := by
    intro x hx
    have h1 : thetaP F x ∈ H := by rw [hH'] at hx; exact hx
    have h2 := le_normalizer_pCoreOf 2 H h1
    rw [← hUm] at h2
    exact (C11P9A.map_mem_normalizer_iff (thetaP F) thetaP_injective).mp h2
  have hH'p : ⁅H', H'⁆ = H' := by
    apply Subgroup.map_injective thetaP_injective
    rw [Subgroup.map_commutator, hH'm, hp]
  have hH'1 : H' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, ← hH'm, h, Subgroup.map_bot]
    exact pCoreOf_le 2 _
  have hBT : CFSG.LieType.BorelTits.Holds (projectiveSL 3 F) 2 :=
    (CFSG.LieType.BorelTits.holds_statedProj_statedSL 3 F 2).of_mulEquiv
      (Id2519.projectiveSLEquivStatedProj 3 F).symm
  obtain ⟨S, P, hPt, hNP, -, -, hSP⟩ := hBT U hU1 hU2
  have hH'P : H' ≤ P := hH'N.trans hNP
  have hŪ := isSylowTwoOf_projU (K := F)
  have hidx : ¬ 2 ∣ (projUnitriangular 3 F).index := by
    have := hŪ.2.2
    rwa [show ((projUnitriangular 3 F).subgroupOf ⊤).index = (projUnitriangular 3 F).index from
      Subgroup.relIndex_top_right _] at this
  let Ū : Sylow 2 (projectiveSL 3 F) := hŪ.2.1.toSylow hidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) S Ū
  have hmem : ∀ x, x ∈ projUnitriangular 3 F ↔ c⁻¹ * x * c ∈ (S : Subgroup (projectiveSL 3 F)) := by
    intro x
    have h1 : (Ū : Subgroup (projectiveSL 3 F)) = projUnitriangular 3 F := rfl
    rw [← h1, ← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  have hconjP : ∀ x, x ∈ P' ↔ c⁻¹ * x * c ∈ P := by
    intro x
    constructor
    · rintro ⟨p, hp', rfl⟩
      have e : c⁻¹ * ((MulAut.conj c).toMonoidHom p) * c = p := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hp'
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hNP' : Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) ≤ P' := by
    intro n hn
    rw [hconjP]
    refine hSP (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    have e1 : c⁻¹ * n * c * x * (c⁻¹ * n * c)⁻¹ = c⁻¹ * (n * (c * x * c⁻¹) * n⁻¹) * c := by group
    have e2 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [e1, ← hmem, ← (Subgroup.mem_normalizer_iff.mp hn) (c * x * c⁻¹), hmem, e2]
  have hP't : P' ≠ ⊤ := by
    intro h
    apply hPt
    rw [eq_top_iff]
    intro x _
    have : c * x * c⁻¹ ∈ P' := h ▸ Subgroup.mem_top _
    rw [hconjP] at this
    simpa [mul_assoc] using this
  set X := perfectCore P' with hX
  have hH'X : H'.map (MulAut.conj c).toMonoidHom ≤ X := by
    refine le_perfectCore_of_perfect (Subgroup.map_mono hH'P) ?_
    rw [← Subgroup.map_commutator, hH'p]
  have hX1 : X ≠ ⊥ := by
    intro h
    apply hH'1
    rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective] at hH'X
    exact hH'X
  have hSX : projUnitriangular 3 F ≤ Subgroup.normalizer (X : Set (projectiveSL 3 F)) :=
    (Subgroup.le_normalizer.trans hNP').trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P'))
  have hjX : ∃ j : Fin 2, H'.map (MulAut.conj c).toMonoidHom ≤ parab34 F j := by
    rcases classify_std hF X hX1 (perfectCore_perfect P') hSX with h | h | h
    · exact ⟨0, h ▸ hH'X⟩
    · exact ⟨1, h ▸ hH'X⟩
    · exact absurd (eq_top_iff.mpr (h ▸ perfectCore_le P')) hP't
  obtain ⟨j, hj⟩ := hjX
  have hθ : ∀ x : projectiveSL 3 F, thetaP F (c * x * c⁻¹) =
      thetaP F c * thetaP F x * (thetaP F c)⁻¹ := fun x => by
    rw [map_mul, map_mul, map_inv]
  have hmap : H.map (MulAut.conj (thetaP F c)).toMonoidHom ≤ Ptheta F j := by
    rintro _ ⟨h, hh, rfl⟩
    rw [← hH'm] at hh
    obtain ⟨x, hx, rfl⟩ := hh
    refine ⟨c * x * c⁻¹, hj ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hθ x
  fin_cases j
  · exact ⟨MulAut.conj (thetaP F c), hmap⟩
  · refine ⟨(MulAut.conj (thetaP F c)).trans (B414.M.graphAut F), ?_⟩
    rw [← B414.M.map_graphAut_Ptheta_one]
    intro z hz
    obtain ⟨h, hh, rfl⟩ := hz
    exact ⟨_, hmap ⟨h, hh, rfl⟩, rfl⟩

theorem exists_aut_map_eq_Ptheta_zero (hF : Nat.card F = 4) {H : Subgroup (PGL3 F)}
    (hp : ⁅H, H⁆ = H) (hne : pCoreOf 2 H ≠ ⊥)
    (hcard : Nat.card H = 60 * Nat.card ↥(pCoreOf 2 H)) :
    ∃ φ : PGL3 F ≃* PGL3 F, H.map φ.toMonoidHom = Ptheta F 0 := by
  obtain ⟨φ, hφ⟩ := exists_aut_map_le hF hp hne
  refine ⟨φ, eq_Ptheta_zero_of_le hF hφ ?_ ?_⟩
  · rw [pCoreOf_map_mulEquiv, Subgroup.card_map_of_injective φ.injective,
      Subgroup.card_map_of_injective φ.injective, hcard]
  · rw [pCoreOf_map_mulEquiv]
    intro h
    apply hne
    rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at h

theorem exists_isMaxParabolic2 (hF : Nat.card F = 4) {H : Subgroup (PGL3 F)}
    (hp : ⁅H, H⁆ = H) (hne : pCoreOf 2 H ≠ ⊥)
    (hcard : Nat.card H = 60 * Nat.card ↥(pCoreOf 2 H)) :
    IsMaxParabolic2 ⊤ (Subgroup.normalizer (H : Set (PGL3 F))) ∧
      perfectCore (Subgroup.normalizer (H : Set (PGL3 F))) = H := by
  obtain ⟨φ, hφ⟩ := exists_aut_map_eq_Ptheta_zero hF hp hne hcard
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PGL3 F)))
  have hS := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨c, hc⟩ := exists_conj_S0P hF hS
  have hS0 : CFSG.QuasithinUnique.IsSylowTwoOf (S0P F) ⊤ := by
    have h1 := C11P9A.isSylowTwoOf_map (MulAut.conj c⁻¹) hS
    rwa [hc, Subgroup.map_map, show (MulAut.conj c⁻¹).toMonoidHom.comp
      (MulAut.conj c).toMonoidHom = MonoidHom.id _ by ext x; simp [MulAut.conj_apply, mul_assoc],
      Subgroup.map_id] at h1
  have hN : Subgroup.normalizer (H : Set (PGL3 F)) =
      (Subgroup.normalizer (Ptheta F 0 : Set (PGL3 F))).map φ.symm.toMonoidHom := by
    rw [← hφ, ← Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [this, Subgroup.map_id]
  have hHφ : (Ptheta F 0).map φ.symm.toMonoidHom = H := by
    rw [← hφ, Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [this, Subgroup.map_id]
  refine ⟨?_, ?_⟩
  · rw [hN]
    exact B414.M.isMaxParabolic2_map φ.symm (S12.isMaxParabolic2_normalizer_Ptheta hS0 hF 0)
  · rw [hN, ← map_perfectCore, S12.perfectCore_normalizer_Ptheta hS0 hF 0, hHφ]

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem comm_mem_pCoreOf_K (hm : m = 2) {w : G} (hw : w ∈ Subgroup.zpowers y) {k : G}
    (hk : k ∈ K) : w * k * w⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hμ3 : μ ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, s.μ_order, hm]
    norm_num
  have hwK : w ∈ K := (Subgroup.zpowers_le.mpr s.y_mem) hw
  have htor : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, SL3Pt.tor μ * g = g * SL3Pt.tor μ := by
    intro g
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have hμ' : ((μ⁻¹ : Fˣ) : F) ^ 2 = μ := by
      have : (μ⁻¹ : Fˣ) ^ 2 = μ := by
        calc (μ⁻¹ : Fˣ) ^ 2 = μ⁻¹ ^ 2 * μ ^ 3 := by rw [hμ3, mul_one]
          _ = μ := by group
      rw [← Units.val_pow_eq_pow_val, this]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, SL3Pt.coe_tor,
      SL3Pt.torMat, hμ']
    have hd : Matrix.diagonal ![(μ : F), (μ : F), (μ : F)] = Matrix.scalar (Fin 3) (μ : F) := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    rw [hd, (Matrix.scalar_commute (μ : F) (fun r => Commute.all _ r) _).eq]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hαw : α ⟨y ^ j, hwK⟩ = specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor μ ^ j) := by
    have e : (⟨y ^ j, hwK⟩ : ↥K) = (⟨y, s.y_mem⟩ : ↥K) ^ j := rfl
    rw [e, map_zpow, s.α_y, ← map_zpow]
  have hmem : y ^ j * k * (y ^ j)⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hwK hk) (K.inv_mem hwK)) (K.inv_mem hk)
  have h1 : α ⟨y ^ j * k * (y ^ j)⁻¹ * k⁻¹, hmem⟩ = 1 := by
    have e : (⟨y ^ j * k * (y ^ j)⁻¹ * k⁻¹, hmem⟩ : ↥K) =
        ⟨y ^ j, hwK⟩ * ⟨k, hk⟩ * (⟨y ^ j, hwK⟩ : ↥K)⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hαw]
    obtain ⟨g, hg⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective (α ⟨k, hk⟩)
    rw [← hg, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    have hc : SL3Pt.tor μ ^ j * g = g * SL3Pt.tor μ ^ j := (Commute.zpow_left (htor g) j).eq
    rw [hc, mul_inv_cancel_right, mul_inv_cancel, map_one]
  have h2 : (⟨y ^ j * k * (y ^ j)⁻¹ * k⁻¹, hmem⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← s.modO2.2]
    exact h1
  exact (mem_pCoreOf_iff' _).mpr h2

theorem comm_mem_pCoreOf_K₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    {w : G} (hw : w ∈ Subgroup.zpowers y) {l : G} (hl : l ∈ K₂) :
    w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 K₂ := by
  have h1 := s.comm_mem_pCoreOf_K hm hw (s.K₂_le_K hl)
  rw [s.pCoreOf_K_eq h135 hR hC h37 h38 h39] at h1
  refine s.R₂_inf_K₂_le ⟨s.q4311_le_R₂ h135 hR hC h37 h38 h39 h1, ?_⟩
  have h2 : w * l * w⁻¹ ∈ K₂ :=
    (Subgroup.mem_normalizer_iff.mp (s.Y_le_normalizer_K₂ hw) l).mp hl
  exact K₂.mul_mem h2 (K₂.inv_mem hl)

theorem KZ_inf_zpowers : KZ ⊓ Subgroup.zpowers y = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwY⟩
  rw [Subgroup.mem_bot]
  exact s.Y_faithful hwY fun z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp (s.KZ_cent hwK) z hz).symm, mul_inv_cancel_right]

variable {α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}

theorem card_map_K₂ (hm : m = 2) (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) :
    Nat.card ↥((K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α') =
      60 * Nat.card ↥(pCoreOf 2 ((K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α')) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, s.card_F, hm]; norm_num
  have hK₂Γ : K₂ ≤ KZ ⊔ Subgroup.zpowers y := s.K₂_le_KZ.trans le_sup_left
  have hOΓ : pCoreOf 2 K₂ ≤ KZ ⊔ Subgroup.zpowers y := (pCoreOf_le 2 K₂).trans hK₂Γ
  set H := (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' with hH
  have hperf : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, L4316.subgroupOf_perfect hK₂Γ s.K₂_perfect]
  have hne : H ≠ ⊥ := by
    intro h
    apply s.not_K₂_le_pCoreOf_KZ
    intro k hk
    have h1 : α' ⟨k, hK₂Γ hk⟩ ∈ H := ⟨⟨k, hK₂Γ hk⟩, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (hα'k _).mp h1
  set α₀ : ↥K₂ →* ↥(StatedSL 2 F) :=
    (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp s.levi with hα₀
  have hα₀s : Function.Surjective α₀ :=
    (specialLinearGroupEquivStatedSL 2 F).surjective.comp s.levi_surjective
  have hα₀k : α₀.ker = (pCoreOf 2 K₂).subgroupOf K₂ := by
    ext k
    rw [MonoidHom.mem_ker, hα₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, s.ker_levi, Subgroup.mem_subgroupOf,
      mem_pCoreOf_iff']
  have hO : pCoreOf 2 H = ((pCoreOf 2 K₂).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' :=
    le_antisymm (S12.pCoreOf_le_map hF hK₂Γ α' hperf hne α₀ hα₀s hα₀k)
      (S12.map_pCoreOf_le α' hK₂Γ)
  set f := α'.comp (Subgroup.inclusion hK₂Γ) with hf
  set g := α'.comp (Subgroup.inclusion hOΓ) with hg
  have hfr : f.range = H := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hgr : g.range = pCoreOf 2 H := by
    rw [hg, MonoidHom.range_comp, Subgroup.inclusion_range, hO]
  have hinter : K₂ ⊓ pCoreOf 2 KZ ≤ pCoreOf 2 K₂ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => mem_normalizer_inf (Subgroup.le_normalizer hk)
        (normalizer_le_normalizer_pCoreOf 2 KZ (Subgroup.le_normalizer (s.K₂_le_KZ hk))))
      ((pCoreOf_isPGroup 2 KZ).to_le inf_le_right)
  have hfk : f.ker.map K₂.subtype = K₂ ⊓ pCoreOf 2 KZ := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, (hα'k _).mp hk⟩
    · rintro ⟨hxK, hxO⟩
      exact ⟨⟨x, hxK⟩, (hα'k ⟨x, hK₂Γ hxK⟩).mpr hxO, rfl⟩
  have hgk : g.ker.map (pCoreOf 2 K₂).subtype = K₂ ⊓ pCoreOf 2 KZ := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨pCoreOf_le 2 K₂ k.2, (hα'k _).mp hk⟩
    · rintro ⟨hxK, hxO⟩
      exact ⟨⟨x, hinter ⟨hxK, hxO⟩⟩, (hα'k ⟨x, hK₂Γ hxK⟩).mpr hxO, rfl⟩
  have hkk : Nat.card f.ker = Nat.card g.ker := by
    rw [← Subgroup.card_map_of_injective K₂.subtype_injective, hfk,
      ← Subgroup.card_map_of_injective (pCoreOf 2 K₂).subtype_injective, hgk]
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 := Subgroup.card_ker_mul_card_range g
  have h3 := Subgroup.card_ker_mul_card_range α₀
  rw [hfr] at h1
  rw [hgr] at h2
  rw [MonoidHom.range_eq_top.mpr hα₀s, Subgroup.card_top,
    Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv.symm, card_SL2_four hF,
    hα₀k, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 K₂)).toEquiv] at h3
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have h4 : Nat.card f.ker * Nat.card H = Nat.card f.ker * (60 * Nat.card ↥(pCoreOf 2 H)) := by
    rw [h1, ← h3, ← h2, hkk]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h4

theorem exists_P (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) (hQL : IsPSL 3 2 2 (ModO2 KZ))
    (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) :
    ∃ P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)), IsMaxParabolic2 ⊤ P ∧
      (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' = perfectCore P ∧
      ((Subgroup.zpowers y).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' ≤ P ∧
      Nat.card ↥(((Subgroup.zpowers y).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α') = 3 ∧
      ∀ x ∈ ((Subgroup.zpowers y).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α',
        ∀ l ∈ (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α',
          x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 ((K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α') := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, s.card_F, hm]; norm_num
  have hK₂Γ : K₂ ≤ KZ ⊔ Subgroup.zpowers y := s.K₂_le_KZ.trans le_sup_left
  have hXΓ : Subgroup.zpowers y ≤ KZ ⊔ Subgroup.zpowers y := le_sup_right
  set H := (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' with hH
  have hperf : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, L4316.subgroupOf_perfect hK₂Γ s.K₂_perfect]
  have hneO : pCoreOf 2 H ≠ ⊥ := by
    obtain ⟨k, hk, hkO⟩ := IsConcreteLE.not_le_iff_exists.mp
      (s.pCoreOf_K₂_not_le h135 hR hC h36 h37 h38 h39 hm hZ hQL hα'k)
    intro h
    have h1 : α' ⟨k, hK₂Γ (pCoreOf_le 2 K₂ hk)⟩ ∈ pCoreOf 2 H :=
      S12.map_pCoreOf_le α' hK₂Γ ⟨_, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hkO ((hα'k _).mp h1)
  have hcard := s.card_map_K₂ hm hα'k
  obtain ⟨hmax, hcore⟩ := L4316.exists_isMaxParabolic2 hF hperf hneO hcard
  refine ⟨Subgroup.normalizer (H : Set (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))), hmax,
    hcore.symm, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact S12.map_mem_normalizer α' K₂ (s.Y_le_normalizer_K₂ (Subgroup.mem_subgroupOf.mp hw))
  ·
    set φ := α'.comp (Subgroup.inclusion hXΓ) with hφ
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro w hw
      have h1 : ((Subgroup.inclusion hXΓ w : ↥(KZ ⊔ Subgroup.zpowers y)) : G) ∈ pCoreOf 2 KZ :=
        (hα'k _).mp hw
      have h2 : (w : G) ∈ KZ ⊓ Subgroup.zpowers y := ⟨pCoreOf_le 2 KZ h1, w.2⟩
      rw [s.KZ_inf_zpowers, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have hr : φ.range = ((Subgroup.zpowers y).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' := by
      rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, s.card_Y, hm]
    norm_num
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨γ, hγ, rfl⟩
    have hwX := Subgroup.mem_subgroupOf.mp hw
    have hγK := Subgroup.mem_subgroupOf.mp hγ
    have h1 := s.comm_mem_pCoreOf_K₂ h135 hR hC h37 h38 h39 hm hwX hγK
    have h2 : w * γ * w⁻¹ * γ⁻¹ ∈ (pCoreOf 2 K₂).subgroupOf (KZ ⊔ Subgroup.zpowers y) := by
      rw [Subgroup.mem_subgroupOf]
      simpa using h1
    have h3 := S12.map_pCoreOf_le α' hK₂Γ ⟨_, h2, rfl⟩
    simpa only [map_mul, map_inv] using h3

end Setting4315

end CFSG.Quasithin.H13.Ch4
