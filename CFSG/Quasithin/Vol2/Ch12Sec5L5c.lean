module

public import CFSG.Quasithin.Vol2.Ch12Sec5F
public import CFSG.Quasithin.Vol2.Ch12Sec5L5b
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125Tr3 S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar
open CFSG.ComponentClassification.PresentationLocal (antidiagGram sympFour omegaPerm
  omegaPerm_injective omegaPerm_surjective)

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "M4" => Matrix (Fin 4) (Fin 4) (ZMod 2)
local notation "SL41" => Matrix.SpecialLinearGroup (Fin 4 ⊕ Fin 1) (ZMod 2)

namespace S125L5c

@[expose] def Q (g : M5) (i j : Fin 5) : ZMod 2 :=
  g i 0 * g j 3 - g i 3 * g j 0 + (g i 1 * g j 2 - g i 2 * g j 1)

theorem wedge_y1 (g : M5) (k : Fin 10) :
    (JonesParshall.wedgeMat g *ᵥ S125L5b.y1) k =
      Q g (JonesParshall.pr5 k).1 (JonesParshall.pr5 k).2 := by
  rw [S125L5b.y1, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    Pi.add_apply, Matrix.col_apply, Matrix.col_apply]
  simp only [JonesParshall.wedgeMat, Matrix.of_apply,
    show JonesParshall.pr5 2 = (0, 3) from rfl, show JonesParshall.pr5 4 = (1, 2) from rfl, Q]

@[expose] def idx5 : Fin 5 → Fin 5 → Fin 10 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 4, 5, 6], ![1, 4, 0, 7, 8], ![2, 5, 7, 0, 9], ![3, 6, 8, 9, 0]]

theorem pr5_idx5 : ∀ i j : Fin 5, i < j → JonesParshall.pr5 (idx5 i j) = (i, j) := by decide

theorem Q_of_fix {g : M5} (h : JonesParshall.wedgeMat g *ᵥ S125L5b.y1 = S125L5b.y1) (i j : Fin 5)
    (hij : i < j) : Q g i j = S125L5b.y1 (idx5 i j) := by
  have := wedge_y1 g (idx5 i j)
  rw [h, pr5_idx5 i j hij] at this
  exact this.symm

@[expose] def G4 (g : M5) : M4 := Matrix.of fun i j => g (Fin.castSucc i) (Fin.castSucc j)

@[expose] def r4 (g : M5) : Fin 4 → ZMod 2 := fun j => g 4 (Fin.castSucc j)

theorem mul_antidiag_transpose (M N : M4) (i j : Fin 4) :
    (M * antidiagGram * Nᵀ) i j =
      M i 0 * N j 3 + M i 1 * N j 2 + M i 2 * N j 1 + M i 3 * N j 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, antidiagGram, Matrix.of_apply,
    Matrix.transpose_apply]
  simp
  ring

theorem antidiag_mulVec (M : M4) (r : Fin 4 → ZMod 2) (i : Fin 4) :
    (M *ᵥ (antidiagGram *ᵥ r)) i = M i 0 * r 3 + M i 1 * r 2 + M i 2 * r 1 + M i 3 * r 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, antidiagGram, Matrix.of_apply]
  simp

theorem id_lt : ∀ a b c d e f g h : ZMod 2,
    a * b + e * f + g * h + c * d = a * b - c * d + (e * f - g * h) := by decide

theorem id_gt : ∀ a b c d e f g h : ZMod 2,
    a * b + e * f + g * h + c * d = d * c - b * a + (h * g - f * e) := by decide

theorem id_eq : ∀ a b e f : ZMod 2, a * b + e * f + f * e + b * a = 0 := by decide

@[expose] def adg (i j : Fin 4) : ZMod 2 := if (i : ℕ) + j = 3 then 1 else 0

theorem antidiag_apply (i j : Fin 4) : antidiagGram i j = adg i j := rfl

theorem y1_adg : ∀ i j : Fin 4, i < j →
    S125L5b.y1 (idx5 (Fin.castSucc i) (Fin.castSucc j)) = adg i j := by decide

theorem y1_antidiag (i j : Fin 4) (hij : i < j) :
    S125L5b.y1 (idx5 (Fin.castSucc i) (Fin.castSucc j)) = antidiagGram i j := by
  rw [antidiag_apply]
  exact y1_adg i j hij

theorem adg_symm : ∀ i j : Fin 4, adg i j = adg j i := by decide

theorem antidiag_symm (i j : Fin 4) : antidiagGram i j = antidiagGram j i := by
  rw [antidiag_apply, antidiag_apply]
  exact adg_symm i j

theorem adg_diag : ∀ i : Fin 4, adg i i = 0 := by decide

theorem antidiag_diag (i : Fin 4) : antidiagGram i i = 0 := by
  rw [antidiag_apply]
  exact adg_diag i

theorem y1_last : ∀ i : Fin 4, S125L5b.y1 (idx5 (Fin.castSucc i) 4) = 0 := by decide

theorem castSucc_lt_four : ∀ i : Fin 4, Fin.castSucc i < (4 : Fin 5) := by decide

theorem G4_sp {g : M5} (h : JonesParshall.wedgeMat g *ᵥ S125L5b.y1 = S125L5b.y1) :
    G4 g * antidiagGram * (G4 g)ᵀ = antidiagGram := by
  ext i j
  rw [mul_antidiag_transpose]
  simp only [G4, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hQ := Q_of_fix h _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
    rw [y1_antidiag i j hij] at hQ
    rw [← hQ, Q, id_lt]
    rfl
  · rw [antidiag_diag]
    exact id_eq _ _ _ _
  · have hQ := Q_of_fix h _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
    rw [y1_antidiag j i hij, ← antidiag_symm] at hQ
    rw [← hQ, Q, id_gt]
    rfl

theorem G4_r {g : M5} (h : JonesParshall.wedgeMat g *ᵥ S125L5b.y1 = S125L5b.y1) :
    G4 g *ᵥ (antidiagGram *ᵥ r4 g) = 0 := by
  funext i
  rw [antidiag_mulVec]
  have hQ := Q_of_fix h _ _ (castSucc_lt_four i)
  rw [y1_last] at hQ
  simp only [G4, r4, Matrix.of_apply, Pi.zero_apply]
  rw [← hQ, Q, id_lt]
  rfl

theorem det_antidiag : antidiagGram.det = 1 := by
  have : antidiagGram = (Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2).permMatrix (ZMod 2) := by
    decide
  rw [this, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2)) with
    h | h <;> rw [h] <;> decide

theorem stabGam_of_fix {g : M5} (h : JonesParshall.wedgeMat g *ᵥ S125L5b.y1 = S125L5b.y1) :
    ∀ j : Fin 4, g 4 (Fin.castSucc j) = 0 := by
  have hsp := G4_sp h
  have hdet : (G4 g).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsp
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      det_antidiag] at this
    exact zero_ne_one this
  have hunit : IsUnit (G4 g * antidiagGram) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, det_antidiag, mul_one]
    exact isUnit_iff_ne_zero.2 hdet
  have h1 : (G4 g * antidiagGram) *ᵥ r4 g = 0 := by
    rw [← Matrix.mulVec_mulVec]
    exact G4_r h
  have h2 : r4 g = 0 := by
    have := congrArg ((G4 g * antidiagGram)⁻¹ *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
      hunit), Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  intro j
  exact congrFun h2 j

@[expose] def invT : GL (Fin 4) (ZMod 2) →* GL (Fin 4) (ZMod 2) where
  toFun u := ⟨u.invᵀ, u.valᵀ, by rw [← Matrix.transpose_mul, u.val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, u.inv_val, Matrix.transpose_one]⟩
  map_one' := Units.ext (by
    change ((1 : GL (Fin 4) (ZMod 2)).inv)ᵀ = 1
    rw [show (1 : GL (Fin 4) (ZMod 2)).inv = 1 from rfl, Matrix.transpose_one])
  map_mul' u v := Units.ext (by
    change ((u * v).inv)ᵀ = (u.inv)ᵀ * (v.inv)ᵀ
    rw [show (u * v).inv = v.inv * u.inv from rfl, Matrix.transpose_mul])

theorem invT_invT (u : GL (Fin 4) (ZMod 2)) : invT (invT u) = u := by
  apply Units.ext
  change ((u.valᵀ)ᵀ) = u.val
  rw [Matrix.transpose_transpose]

theorem invT_val (u : GL (Fin 4) (ZMod 2)) :
    ((invT u : GL (Fin 4) (ZMod 2)) : M4) = (u⁻¹ : GL (Fin 4) (ZMod 2)).valᵀ := rfl

theorem mem_sympFour_invT (u : GL (Fin 4) (ZMod 2)) :
    invT u ∈ sympFour ↔ (u : M4) * antidiagGram * (u : M4)ᵀ = antidiagGram := by
  change ((invT u : M4))ᵀ * antidiagGram * (invT u : M4) = antidiagGram ↔ _
  rw [invT_val, Matrix.transpose_transpose]
  have h1 : ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * (u : M4) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (u : M4) * ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    calc (u : M4) * antidiagGram * (u : M4)ᵀ =
        (u : M4) * (((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * antidiagGram *
          ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4)ᵀ) * (u : M4)ᵀ := by rw [h]
      _ = ((u : M4) * ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4)) * antidiagGram *
          (((u : M4) * ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4)))ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = antidiagGram := by rw [h2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  · intro h
    calc ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * antidiagGram * ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4)ᵀ =
        ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * ((u : M4) * antidiagGram * (u : M4)ᵀ) *
          ((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4)ᵀ := by rw [h]
      _ = (((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * (u : M4)) * antidiagGram *
          ((((u⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * (u : M4)))ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = antidiagGram := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def Q0 : Subgroup ↥(parQ : Subgroup SL41) :=
  sympFour.comap (invT.comp (chiL (ZMod 2) (Fin 4) (Fin 1)))

theorem mem_Q0 (q : ↥(parQ : Subgroup SL41)) :
    q ∈ Q0 ↔ (q : SL41).val.toBlocks₁₁ * antidiagGram * ((q : SL41).val.toBlocks₁₁)ᵀ =
      antidiagGram := by
  change invT (chiL (ZMod 2) (Fin 4) (Fin 1) q) ∈ sympFour ↔ _
  rw [mem_sympFour_invT]
  rfl

@[expose] noncomputable def psi0 : ↥Q0 →* ↥sympFour :=
  (invT.comp (chiL (ZMod 2) (Fin 4) (Fin 1))).subgroupComap sympFour

theorem det_eq_one_GL4 (u : GL (Fin 4) (ZMod 2)) : (u : M4).det = 1 := by
  have hu : ∀ x : (ZMod 2)ˣ, (x : ZMod 2) = 1 := by decide
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact hu _

theorem psi0_surjective : Function.Surjective psi0 := by
  rintro ⟨h, hh⟩
  set A : GL (Fin 4) (ZMod 2) := invT h with hA
  set A' : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨A, det_eq_one_GL4 A⟩
  have hg : levL (ZMod 2) (Fin 1) A' ∈ (parQ : Subgroup SL41) :=
    parJL_le_parQ (levL_mem_parJL A')
  have hchi : chiL (ZMod 2) (Fin 4) (Fin 1) ⟨_, hg⟩ = A := by
    apply Units.ext
    change (levL (ZMod 2) (Fin 1) A').val.toBlocks₁₁ = (A : M4)
    rw [levL_val, Matrix.toBlocks_fromBlocks₁₁]
  have hq : (⟨_, hg⟩ : ↥(parQ : Subgroup SL41)) ∈ Q0 := by
    change invT (chiL (ZMod 2) (Fin 4) (Fin 1) ⟨_, hg⟩) ∈ sympFour
    rw [hchi, hA, invT_invT]
    exact hh
  refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
  change invT (chiL (ZMod 2) (Fin 4) (Fin 1) ⟨_, hg⟩) = h
  rw [hchi, hA, invT_invT]

theorem toBlocks22_eq_one {g : SL41} (hg : g ∈ (parQ : Subgroup SL41)) :
    g.val.toBlocks₂₂ = 1 := by
  rw [← S125Pb.parJL_eq_parQ_of_fin_one] at hg
  exact (mem_parJL.1 hg).2

theorem psi0_eq_one_iff (q : ↥Q0) :
    psi0 q = 1 ↔ ((q : ↥(parQ : Subgroup SL41)) : SL41) ∈ S125Pb.uniRad (Fin 4) (Fin 1) := by
  set qq : ↥(parQ : Subgroup SL41) := (q : ↥(parQ : Subgroup SL41)) with hqq
  have hq : (qq : SL41) ∈ (parQ : Subgroup SL41) := qq.property
  have h22 := toBlocks22_eq_one hq
  rw [S125Pb.mem_uniRad]
  have hpsi : ((psi0 q : ↥sympFour) : GL (Fin 4) (ZMod 2)) =
      invT (chiL (ZMod 2) (Fin 4) (Fin 1) qq) := rfl
  constructor
  · intro h
    have h1 : invT (chiL (ZMod 2) (Fin 4) (Fin 1) qq) = 1 := by
      rw [← hpsi, h]
      rfl
    have h2 : chiL (ZMod 2) (Fin 4) (Fin 1) qq = 1 := by
      rw [← invT_invT (chiL (ZMod 2) (Fin 4) (Fin 1) qq), h1, map_one]
    exact ⟨hq, congrArg Units.val h2, h22⟩
  · rintro ⟨-, h11, -⟩
    apply Subtype.ext
    rw [hpsi]
    have : chiL (ZMod 2) (Fin 4) (Fin 1) qq = 1 := Units.ext h11
    rw [this, map_one]
    rfl

theorem idx5_pr5 : ∀ k : Fin 10, idx5 (JonesParshall.pr5 k).1 (JonesParshall.pr5 k).2 = k := by
  decide

theorem fix_iff_parQ {q : SL41} (hq : q ∈ (parQ : Subgroup SL41)) :
    JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5) q : SL5) : M5) *ᵥ
        S125L5b.y1 = S125L5b.y1 ↔
      q.val.toBlocks₁₁ * antidiagGram * (q.val.toBlocks₁₁)ᵀ = antidiagGram := by
  set M : M5 := ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5) q : SL5) : M5) with hM
  have hG : G4 M = q.val.toBlocks₁₁ := by
    ext i j
    exact S125Nat.reindex_castLE _ (by norm_num) q i j
  constructor
  · intro h
    rw [← hG]
    exact G4_sp h
  · intro h
    rw [← hG] at h
    have hrow : ∀ c : Fin 5, c.val < 4 → M 4 c = 0 := fun c hc => by
      rw [hM, S125F.reindex_row4 hq c, ite_eq_right]
      intro h4
      rw [h4] at hc
      exact absurd hc (by decide)
    funext k
    rw [wedge_y1]
    conv_rhs => rw [← idx5_pr5 k]
    have hk := pr5_lt k
    generalize (JonesParshall.pr5 k).1 = i at hk ⊢
    generalize (JonesParshall.pr5 k).2 = j at hk ⊢
    by_cases hj : j.val < 4
    · obtain ⟨i', rfl⟩ : ∃ i' : Fin 4, Fin.castSucc i' = i :=
        ⟨⟨i.val, lt_trans (show i.val < j.val from hk) hj⟩, Fin.ext rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin 4, Fin.castSucc j' = j := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      have hij : i' < j' := Fin.castSucc_lt_castSucc_iff.1 hk
      have he := congrFun₂ h i' j'
      rw [mul_antidiag_transpose] at he
      rw [y1_antidiag i' j' hij, ← he, Q, id_lt]
      rfl
    · have hj4 : j = 4 := Fin.ext (by have := j.2; omega)
      subst hj4
      obtain ⟨i', rfl⟩ : ∃ i' : Fin 4, Fin.castSucc i' = i := ⟨⟨i.val, hk⟩, Fin.ext rfl⟩
      rw [y1_last, Q, hrow 3 (by decide), hrow 0 (by decide), hrow 2 (by decide),
        hrow 1 (by decide)]
      ring

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem part3 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (ri T L F.V6) V ≤ autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1' ∧
      ∃ _ : ((autOn (ri T L F.V6) V).subgroupOf
          (autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1')).Normal,
        Nonempty (↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1') ⧸
          (autOn (ri T L F.V6) V).subgroupOf
            (autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1') ≃* Equiv.Perm (Fin 6)) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V6 F hf.normalizes hf.T_le
  have hTW := (S125L2G.T_le_V F hf.T_le).2.2.2
  have hres := S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ41
  have hde : 4 + 1 = 5 := by norm_num
  have hRL : autOn (ri T L F.V6) V ⊓ autOn (li L F.V6) V =
      (S125Pb.uniRad (Fin 4) (Fin 1)).map (theta F hde) :=
    rbar_inf_lbar F hH hf hde hst hTW hres S125Pb.uniRad_le_parJL
      (fun N hN hn hp => S125Pb.le_uniRad_of_parJL (S125Pb.noO2_GL 4 S125Pb.noO2_SL4) hN hn hp)
  have hML := (S125L2G.part4_groups h1222 F hH).1
  have hRle : autOn (ri T L F.V6) V ≤ autOn (li L F.V6) V := by
    rw [← hML]
    exact A4.autOn_mono ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_mi hTW))
  have hR : autOn (ri T L F.V6) V = (S125Pb.uniRad (Fin 4) (Fin 1)).map (theta F hde) := by
    rw [← hRL, inf_of_le_left hRle]
  let Θq : ↥(parQ : Subgroup SL41) →* MulAut ↥V := (theta F hde).comp parQ.subtype
  have hΘq : Function.Injective Θq := (theta_injective F hde).comp Subtype.val_injective
  have hΘL : ∀ q, Θq q ∈ autOn L V := fun q =>
    (F.γ.symm (reindexSL (ZMod 2) hde (q : SL41))).2
  have hfixq : ∀ q : ↥(parQ : Subgroup SL41),
      Θq q ∈ MulAction.stabilizer (MulAut ↥V) F.w1' ↔ q ∈ Q0 := by
    intro q
    rw [MulAction.mem_stabilizer_iff, mem_Q0, ← fix_iff_parQ q.2]
    change theta F hde (q : SL41) F.w1' = F.w1' ↔ _
    rw [← F.e.injective.eq_iff, e_theta_apply, Frame125.w1', MulEquiv.apply_symm_apply,
      toAdd_ofAdd, ← Multiplicative.toAdd.injective.eq_iff, toAdd_ofAdd]
    rfl
  set C := autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) F.w1' with hC
  have hCeq : C = Q0.map Θq := by
    ext c
    constructor
    · rintro ⟨hcL, hcw⟩
      set g5 : SL5 := F.γ ⟨c, hcL⟩ with hg5
      have hc5 : ((F.γ.symm g5 : ↥(autOn L V)) : MulAut ↥V) = c := by
        rw [hg5, MulEquiv.symm_apply_apply]
      have hfix5 : JonesParshall.wedgeMat (g5 : M5) *ᵥ S125L5b.y1 = S125L5b.y1 := by
        have h1 : c F.w1' = F.w1' := hcw
        rw [← hc5, S125L5a.fix_iff, Frame125.w1', MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
        exact h1
      have hstab : g5 ∈ stabK 4 := by
        rw [mem_stabK]
        intro i j hj hi
        have hi4 : i = 4 := Fin.ext (by have := i.2; omega)
        rw [hi4]
        have := stabGam_of_fix hfix5 ⟨j.val, hj⟩
        exact this
      rw [← map_parQ_eq_stabK hde] at hstab
      obtain ⟨q, hq, hqg⟩ := hstab
      have hcq : Θq ⟨q, hq⟩ = c := by
        rw [← hc5]
        change psi F (reindexSL (ZMod 2) hde q) = _
        rw [show reindexSL (ZMod 2) hde q = g5 from hqg]
        rfl
      refine ⟨⟨q, hq⟩, (hfixq _).1 (hcq ▸ hcw), hcq⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hΘL q, (hfixq q).2 hq⟩
  have hRC : autOn (ri T L F.V6) V ≤ C := by
    rw [hR, hCeq]
    rintro _ ⟨u, hu, rfl⟩
    have huQ : u ∈ (parQ : Subgroup SL41) := S125Pb.uniRad_le_parQ hu
    refine ⟨⟨u, huQ⟩, (mem_Q0 _).2 ?_, rfl⟩
    rw [(S125Pb.mem_uniRad.1 hu).2.1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  let eC : ↥Q0 ≃* ↥C :=
    (Q0.equivMapOfInjective Θq hΘq).trans (MulEquiv.subgroupCongr hCeq.symm)
  have heC : ∀ q : ↥Q0, ((eC q : ↥C) : MulAut ↥V) = Θq q := fun _ => rfl
  let Ψ : ↥C →* ↥sympFour := psi0.comp eC.symm.toMonoidHom
  have hΨ : Function.Surjective Ψ := psi0_surjective.comp eC.symm.surjective
  have hker : Ψ.ker = (autOn (ri T L F.V6) V).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨q, rfl⟩ := eC.surjective c
    change psi0 (eC.symm (eC q)) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, psi0_eq_one_iff, heC, hR]
    constructor
    · intro hu
      exact ⟨_, hu, rfl⟩
    · rintro ⟨u, hu, hue⟩
      have : u = ((q : ↥(parQ : Subgroup SL41)) : SL41) := theta_injective F hde hue
      rw [← this]
      exact hu
  have hnorm : ((autOn (ri T L F.V6) V).subgroupOf C).Normal := by
    rw [← hker]
    exact MonoidHom.normal_ker Ψ
  refine ⟨hRC, hnorm, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ).trans
      (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩))

end S125L5c

end CFSG.Quasithin.H13
