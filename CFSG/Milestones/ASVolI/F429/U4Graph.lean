module

public import CFSG.Milestones.ASVolI.F429.Sp4Mark
public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Quasithin.H13.U4ParSp
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open Matrix CFSG.Open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

section Rank

variable {K : Type} [Field K]

theorem burnsideF429_rank_sandwich {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m n K) (Q : Matrix n m K) (hQP : Q * P = 1) (N : Matrix n n K) :
    Matrix.rank (P * N * Q) = Matrix.rank N := by
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) ?_
  have e : N = Q * (P * N * Q) * P := by
    rw [show Q * (P * N * Q) * P = (Q * P) * N * (Q * P) by simp only [Matrix.mul_assoc], hQP,
      Matrix.one_mul, Matrix.mul_one]
  calc Matrix.rank N = Matrix.rank (Q * (P * N * Q) * P) := by rw [← e]
    _ ≤ Matrix.rank (Q * (P * N * Q)) := Matrix.rank_mul_le_left _ _
    _ ≤ Matrix.rank (P * N * Q) := Matrix.rank_mul_le_right _ _

theorem burnsideF429_rank_eq_one_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (N : Matrix m n K) :
    Matrix.rank N = 1 ↔ N ≠ 0 ∧ ∀ i j k l, N i k * N j l = N i l * N j k := by
  have hzero : Matrix.rank N = 0 → N = 0 := by
    intro h0
    rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    ext i j
    have := congrFun (congrArg (fun φ => φ (Pi.single j 1)) h0) i
    simpa [Matrix.mulVecLin_apply, mulVec_single_one] using this
  constructor
  · intro hr
    refine ⟨fun hN => by rw [hN, Matrix.rank_zero] at hr; exact absurd hr (by norm_num), ?_⟩
    obtain ⟨⟨v, hvR⟩, -, hvspan⟩ := (finrank_eq_one_iff' (K := K)
      (V := LinearMap.range N.mulVecLin)).mp hr
    have hcol : ∀ k, ∃ c : K, ∀ i, N i k = c * v i := by
      intro k
      obtain ⟨c, hc⟩ := hvspan ⟨N *ᵥ Pi.single k 1, Pi.single k 1, rfl⟩
      refine ⟨c, fun i => ?_⟩
      have e1 : (N *ᵥ Pi.single k 1) i = N i k := by simp [mulVec_single_one]
      have e2 := congrFun (congrArg Subtype.val hc) i
      rw [← e1]
      exact e2.symm
    intro i j k l
    obtain ⟨c, hc⟩ := hcol k
    obtain ⟨d, hd⟩ := hcol l
    rw [hc i, hd j, hd i, hc j]
    ring
  · rintro ⟨hN, hmin⟩
    obtain ⟨i₀, j₀, h0⟩ : ∃ i j, N i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hN (Matrix.ext hcon)
    have hN' : N = Matrix.vecMulVec (fun i => N i j₀) (fun j => N i₀ j / N i₀ j₀) := by
      ext i j
      rw [vecMulVec_apply, mul_div_assoc', eq_div_iff h0]
      linear_combination hmin i i₀ j j₀
    refine le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr fun h => hN (hzero h))
    rw [hN']
    exact Matrix.rank_vecMulVec_le _ _

theorem burnsideF429_rank_map_eq_one_iff {F : Type} [Field F] {m n : Type} [Fintype m]
    [Fintype n] [DecidableEq n] (φ : F →+* K) (N : Matrix m n F) :
    Matrix.rank (N.map φ) = 1 ↔ Matrix.rank N = 1 := by
  rw [burnsideF429_rank_eq_one_iff, burnsideF429_rank_eq_one_iff]
  refine and_congr (not_congr ⟨fun hN => ?_, fun hN => by rw [hN, Matrix.map_zero _ (map_zero φ)]⟩)
    (forall_congr' fun i => forall_congr' fun j => forall_congr' fun k => forall_congr' fun l => ?_)
  · ext i j
    have := congrFun (congrFun hN i) j
    simpa using this
  · simp only [Matrix.map_apply, ← map_mul]
    exact φ.injective.eq_iff

end Rank

section U4

open CFSG.Quasithin.H13.U4Par CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF429_U4_cen_equiv {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (Φ : hypSU h 2 0 ≃* ↥Gp) {t : E} (a : hypSU h 2 0)
    (ha : ∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) =
      t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) :
    ∃ ι : StatedSp 2 h.fixedField ≃* cenIn Gp t,
      ∀ x, ((ι x : cenIn Gp t) : E) = ((Φ (a * spIncl h x * a⁻¹) : ↥Gp) : E) := by
  have hcomm : ∀ y : hypSU h 2 0, frobElt h y = y →
      ((Φ (a * y * a⁻¹) : ↥Gp) : E) ∈ cenIn Gp t := by
    intro y hy
    have hc : ((Φ (a * y * a⁻¹) : ↥Gp) : E) ∈ Subgroup.centralizer ({t} : Set E) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e := ha y
      rw [hy] at e
      calc ((Φ (a * y * a⁻¹) : ↥Gp) : E) * t =
          (t * ((Φ (a * y * a⁻¹) : ↥Gp) : E) * t⁻¹) * t := by rw [← e]
        _ = t * ((Φ (a * y * a⁻¹) : ↥Gp) : E) := by group
    exact Subgroup.mem_inf.mpr ⟨(Φ (a * y * a⁻¹)).2, hc⟩
  let φ₀ : StatedSp 2 h.fixedField →* E :=
    Gp.subtype.comp (Φ.toMonoidHom.comp ((MulAut.conj a).toMonoidHom.comp (spIncl h)))
  have hφ₀ : ∀ x, φ₀ x = ((Φ (a * spIncl h x * a⁻¹) : ↥Gp) : E) := fun x => rfl
  have hfix : ∀ x, frobElt h (spIncl h x) = spIncl h x := fun x =>
    (mem_frobFix h).mp (by rw [← range_spIncl h]; exact ⟨x, rfl⟩)
  have hmem : ∀ x, φ₀ x ∈ cenIn Gp t := fun x => by rw [hφ₀]; exact hcomm _ (hfix x)
  let ψ : StatedSp 2 h.fixedField →* cenIn Gp t := φ₀.codRestrict (cenIn Gp t) hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y hxy => ?_, fun e => ?_⟩
    · have h1 : φ₀ x = φ₀ y := congrArg (fun z : cenIn Gp t => (z : E)) hxy
      rw [hφ₀, hφ₀] at h1
      have h2 : a * spIncl h x * a⁻¹ = a * spIncl h y * a⁻¹ := Φ.injective (Subtype.ext h1)
      exact spIncl_injective h (by simpa using h2)
    · obtain ⟨e, he⟩ := e
      obtain ⟨heG, het⟩ := Subgroup.mem_inf.mp he
      obtain ⟨w, hwe⟩ : ∃ w : hypSU h 2 0, ((Φ w : ↥Gp) : E) = e :=
        ⟨Φ.symm ⟨e, heG⟩, by rw [MulEquiv.apply_symm_apply]⟩
      obtain ⟨y, hyw⟩ : ∃ y : hypSU h 2 0, a * y * a⁻¹ = w := ⟨a⁻¹ * w * a, by group⟩
      have het' : t * e * t⁻¹ = e := by
        rw [Subgroup.mem_centralizer_singleton_iff] at het
        rw [← het]
        group
      have hyfix : frobElt h y = y := by
        have e1 := ha y
        rw [hyw, hwe, het', ← hwe, ← hyw] at e1
        have e2 := Φ.injective (Subtype.ext e1)
        simpa using e2
      obtain ⟨x, hx⟩ : y ∈ (spIncl h).range := by
        rw [range_spIncl h]
        exact (mem_frobFix h).mpr hyfix
      refine ⟨x, Subtype.ext ?_⟩
      show φ₀ x = e
      rw [hφ₀, hx, hyw, hwe]
  exact ⟨MulEquiv.ofBijective ψ hψ, fun x => rfl⟩

theorem burnsideF429_U4_isGenLie {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (Φ : hypSU h 2 0 ≃* ↥Gp) {t : E} (a : hypSU h 2 0)
    (ha : ∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) =
      t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) :
    IsGenLie ↥(cenIn Gp t) .Sp4 2 m := by
  obtain ⟨ι, -⟩ := burnsideF429_U4_cen_equiv h Φ a ha
  haveI := charP_fixedField h
  haveI : Finite K := h.finite
  exact ⟨Nat.prime_two, h.one_le, h.fixedField, inferInstance, inferInstance,
    h.card_fixedField, ⟨ι.symm.trans (CFSG.QuasithinUnique.Lin2.Five.projEquiv _)⟩⟩

theorem burnsideF429_U4_rank_conj {m : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : UnitaryFieldData 2 m K) (a g : hypSU h 2 0) :
    Matrix.rank ((((a * g * a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1) =
      Matrix.rank ((((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1) := by
  have e : (((a * g * a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1 =
      ((a : GL Ix K) : Matrix Ix Ix K) * (((g : GL Ix K) : Matrix Ix Ix K) - 1) *
        (((a : GL Ix K)⁻¹ : GL Ix K) : Matrix Ix Ix K) :=
    burnsideF429_conj_sub_one (a : GL Ix K) (g : GL Ix K)
  rw [e, burnsideF429_rank_conj]

theorem burnsideF429_U4_rank_spIncl {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (x : StatedSp 2 h.fixedField) :
    Matrix.rank ((((spIncl h x : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1) = 1 ↔
      Matrix.rank (((x : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) - 1) = 1 := by
  have e : (((spIncl h x : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1 =
      ((((x : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) - 1).map
          h.fixedField.subtype).submatrix ixEF ixEF := by
    rw [coe_spIncl]
    ext i j
    simp only [inclMat_apply, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.map_apply,
      Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp
  rw [e, Matrix.rank_submatrix, burnsideF429_rank_map_eq_one_iff]

theorem burnsideF429_U4_rank_T {f : ℕ} {H : Type} [Group H] (mk : Marking .U4 2 f H)
    (g : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    Matrix.rank ((((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) :
        GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) - 1) =
      Matrix.rank (((g : GL (HypIndex 2 0) mk.field) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) - 1) := by
  have hR := burnsideF4gU4_marking_isHypTransport mk
  have e : (((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) :
        GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) - 1 =
      burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
        (((g : GL (HypIndex 2 0) mk.field) : Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) - 1) *
        transportInv (burnsideF4gU4_fieldData mk)
          (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)) := by
    rw [burnsideF4gU4_coe_T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_transportInv hR]
  rw [e, burnsideF429_rank_sandwich _ _ (transportInv_mul hR)]

theorem burnsideF429_U4_graphFixed {f : ℕ} (chart : NativeChart .U4 2 f Gp)
    (mk : Marking .U4 2 f ↥Gp)
    (hcp : chart.coordinatePayload = NativeCoordinates.classical .U4 rfl mk) {t : E}
    (a : hypSU (burnsideF4gU4_fieldData mk) 2 0)
    (ha : ∀ x, ((burnsideF4gU4_Phi mk (a * frobElt (burnsideF4gU4_fieldData mk) x * a⁻¹) :
      ↥Gp) : E) = t * ((burnsideF4gU4_Phi mk (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) :
    chart.GraphFixedMarkingGoal t := by
  intro _
  have hfd := burnsideF4gU4_fieldData mk
  haveI : CharP mk.field 2 := hfd.charP
  haveI := charP_fixedField (burnsideF4gU4_fieldData mk)
  obtain ⟨ι, hι⟩ := burnsideF429_U4_cen_equiv (burnsideF4gU4_fieldData mk)
    (burnsideF4gU4_Phi mk) a ha
  refine burnsideF429_sp4_marking_exists mk.exponent_pos
    (burnsideF4gU4_fieldData mk).card_fixedField ι (chart.coordinatePayload.RankInvolution 1)
    ?_ ?_
  · intro e he
    rw [hcp] at he
    exact ⟨he.2.1, he.2.2.1⟩
  · intro x hx1 hx2
    rw [hcp]
    have hPhi : ∀ g, burnsideF4gU4_Phi mk g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
      congrArg (fun φ : hypSU (burnsideF4gU4_fieldData mk) 2 0 →* ↥Gp => φ g)
        (burnsideF4gU4_Phi_toMonoidHom mk)
    set g := a * spIncl (burnsideF4gU4_fieldData mk) x * a⁻¹ with hg
    have hιx : ((ι x : cenIn Gp t) : E) = ((burnsideF4gU4_Phi mk g : ↥Gp) : E) := hι x
    have hrep : ∀ rep : nativeGroup .U4 (2 ^ f) mk.field,
        ((mk.transport rep : ↥Gp) : E) = ((ι x : cenIn Gp t) : E) ↔
          rep = burnsideF4gU4_T mk g := by
      intro rep
      rw [hιx, hPhi]
      constructor
      · intro h1
        exact burnsideF4gU4_transport_injective mk (Subtype.ext h1)
      · rintro rfl
        rfl
    have hrank : Matrix.rank ((((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) :
        GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) - 1) = 1 ↔
        Matrix.rank (((x : GL (Fin 2 ⊕ Fin 2) (burnsideF4gU4_fieldData mk).fixedField) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (burnsideF4gU4_fieldData mk).fixedField) - 1) =
          1 := by
      rw [burnsideF429_U4_rank_T, hg, burnsideF429_U4_rank_conj, burnsideF429_U4_rank_spIncl]
    simp only [NativeCoordinates.RankInvolution]
    constructor
    · rintro ⟨-, -, -, rep, h1, -, h3⟩
      rw [(hrep rep).mp h1] at h3
      exact hrank.mp h3
    · intro hr
      refine ⟨(ι x).2.1, hx1, hx2, burnsideF4gU4_T mk g, (hrep _).mpr rfl, ?_, hrank.mpr hr⟩
      apply burnsideF4gU4_transport_injective mk
      rw [map_mul, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← hPhi, ← hιx]
      exact hx2

end U4

end CFSG.ASVolI
