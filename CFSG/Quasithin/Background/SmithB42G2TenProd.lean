module

public import CFSG.Quasithin.Background.SmithB42G2TenBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7a
open scoped Kronecker

variable (F : Type) [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

abbrev TIdx (lab : Fin f → G2L) : Type := ∀ j, (lab j).idx

@[expose] def tRep (lab : Fin f → G2L) :
    ↥(cayleyGroup F) →* Matrix (TIdx lab) (TIdx lab) k :=
  kronRep fun j => matMap (frK k (j : ℕ)) ((lab j).rep (F := F))

@[expose] def tHw (lab : Fin f → G2L) : TIdx lab → k :=
  fun x => ∏ j : Fin f, frK k (j : ℕ) ((lab j).hw (F := F) (x j))

@[expose] def tLow (lab : Fin f → G2L) : TIdx lab → k :=
  fun x => ∏ j : Fin f, frK k (j : ℕ) ((lab j).low (F := F) (x j))

theorem matMap_mulVec_map {F k : Type} [Field F] [Field k] {ι : Type} [Fintype ι] (θ : F →+* k)
    (M : Matrix ι ι F) (v : ι → F) :
    (M.map θ).mulVec (fun x => θ (v x)) = fun x => θ (M.mulVec v x) := by
  funext x
  exact (RingHom.map_mulVec θ M v x).symm

theorem tRep_mulVec_prod (lab : Fin f → G2L) (g : ↥(cayleyGroup F))
    (v : ∀ j, (lab j).idx → F) :
    (tRep F k lab g).mulVec (fun x => ∏ j : Fin f, frK k (j : ℕ) (v j (x j))) =
      fun x => ∏ j : Fin f, frK k (j : ℕ) (((lab j).rep g).mulVec (v j) (x j)) := by
  rw [tRep, kronRep_apply, kron_mulVec_prod (v := fun (j : Fin f) y => frK k (j : ℕ) (v j y))]
  funext x
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [matMap_apply, matMap_mulVec_map]

theorem tRep_U0_hw (lab : Fin f → G2L) {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    (tRep F k lab u).mulVec (tHw F k lab) = tHw F k lab := by
  unfold tHw
  rw [tRep_mulVec_prod]
  funext x
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [G2L.rep_U0_hw hu]

theorem tRep_g2Sw_hw (lab : Fin f → G2L) :
    (tRep F k lab g2Sw).mulVec (tHw F k lab) = tLow F k lab := by
  unfold tHw
  rw [tRep_mulVec_prod]
  funext x
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [G2L.rep_g2Sw_hw]

omit [CharP F 2] in
theorem tHw_ne_zero (lab : Fin f → G2L) : tHw F k lab ≠ 0 := by
  have h : ∀ j, ∃ x : (lab j).idx, (lab j).hw (F := F) x ≠ 0 := fun j => by
    by_contra hc
    push Not at hc
    exact G2L.hw_ne_zero (F := F) (lab j) (funext hc)
  choose x hx using h
  intro h0
  have := congrFun h0 x
  unfold tHw at this
  rw [Pi.zero_apply, Finset.prod_eq_zero_iff] at this
  obtain ⟨j, -, hj⟩ := this
  exact hx j ((map_eq_zero _).mp hj)

@[expose] def stLab (f : ℕ) : Fin f → G2L := fun _ => .st

@[expose] def embT (lab : Fin f → G2L) (x : TIdx lab) : TIdx (stLab f) :=
  fun j => (lab j).emb (x j)

theorem embT_injective (lab : Fin f → G2L) : Function.Injective (embT lab) := by
  intro x y h
  funext j
  exact G2L.emb_injective (lab j) (congrFun h j)

theorem tRep_U0_low (lab : Fin f → G2L) {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) (x : TIdx lab) :
    (tRep F k lab u).mulVec (tLow F k lab) x =
      (tRep F k (stLab f) u).mulVec (tLow F k (stLab f)) (embT lab x) := by
  unfold tLow
  rw [tRep_mulVec_prod, tRep_mulVec_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [G2L.rep_U0_low hu]
  rfl

omit [CharP F 2] in
theorem card_TIdx_st : Fintype.card (TIdx (stLab f)) = 64 ^ f := by
  rw [Fintype.card_pi]
  have h : ∀ j : Fin f, Fintype.card ((stLab f j).idx) = 64 := fun j => by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_eq_fintype_card (α := SIdx)).trans card_SIdx
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

@[expose] def hwStq (f : ℕ) : TIdx (stLab f) := fun _ => hwS

theorem st_coord_hwS {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    (repSt u).mulVec (Pi.single lowS 1) hwS = cQ u * cG u := by
  rw [repSt_lowS]
  change repQ u (.inl 0) (.inr 0) * (repLie u).mulVec (Pi.single lowL 1) hwL = _
  rw [(repLie_U0_low hu).2]
  rfl

theorem st_norm_coord [Fintype F] [Fintype ↥(U0 F)] (hF : Fintype.card F = 2 ^ f) :
    ∑ u : ↥(U0 F), (tRep F k (stLab f) u).mulVec (tLow F k (stLab f)) (hwStq f) = 1 := by
  classical
  have hn : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have e : ∀ u : ↥(U0 F), (tRep F k (stLab f) u).mulVec (tLow F k (stLab f)) (hwStq f) =
      frK k 0 ((cQ (u : ↥(cayleyGroup F)) * cG (u : ↥(cayleyGroup F))) ^
        (Fintype.card F - 1)) := fun u => by
    unfold tLow
    rw [tRep_mulVec_prod, ← prod_frK_eq k hF]
    refine Finset.prod_congr rfl fun j _ => ?_
    change frK k (j : ℕ) ((repSt (u : ↥(cayleyGroup F))).mulVec (Pi.single lowS 1) hwS) = _
    rw [st_coord_hwS F u.2]
  simp_rw [e]
  rw [← map_sum, sum_U0_cQ_cG hn, map_one]

theorem st_coords_li [Fintype F] (hF : Fintype.card F = 2 ^ f) :
    LinearIndependent k (fun x : TIdx (stLab f) => fun u : ↥(U0 F) =>
      (tRep F k (stLab f) u).mulVec (tLow F k (stLab f)) x) := by
  classical
  have := finite_cayleyGroup (F := F)
  let _ : Fintype ↥(U0 F) := Fintype.ofFinite _
  have hn : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  let ρ : ↥(U0 F) →* ((TIdx (stLab f) → k) →ₗ[k] (TIdx (stLab f) → k)) :=
    { toFun := fun u => Matrix.mulVecLin (tRep F k (stLab f) (u : ↥(cayleyGroup F)))
      map_one' := by
        rw [Subgroup.coe_one, map_one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun u v => by
        simp only [Subgroup.coe_mul, map_mul, Matrix.mulVecLin_mul]
        rfl }
  have hv : ∑ u, ρ u (tLow F k (stLab f)) ≠ 0 := by
    intro h
    have h1 : (∑ u, ρ u (tLow F k (stLab f))) (hwStq f) = 0 := by rw [h]; rfl
    rw [Finset.sum_apply] at h1
    change ∑ u : ↥(U0 F), (tRep F k (stLab f) u).mulVec (tLow F k (stLab f)) (hwStq f) = 0
      at h1
    rw [st_norm_coord F k hF] at h1
    exact one_ne_zero h1
  have hdim : Module.finrank k (TIdx (stLab f) → k) = Fintype.card ↥(U0 F) := by
    rw [Module.finrank_fintype_fun_eq_card, card_TIdx_st, Fintype.card_eq_nat_card, card_U0 hn,
      hn, ← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, mul_comm]
  obtain ⟨b, hb, -, -⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two isPGroup_U0 ρ _ hv hdim
  have hspan : Submodule.span k (Set.range fun u : ↥(U0 F) =>
      matRep (tRep F k (stLab f)) (u : ↥(cayleyGroup F)) (tLow F k (stLab f))) = ⊤ := by
    have e : (fun u : ↥(U0 F) => matRep (tRep F k (stLab f)) (u : ↥(cayleyGroup F))
        (tLow F k (stLab f))) = ⇑b := funext fun u => (hb u).symm
    rw [e]
    exact b.span_eq
  exact coords_linearIndependent_of_span _ _ _ hspan

omit [CharP F 2] in
theorem transpose_mul_mul_apply {κ ν : Type} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (S : Matrix κ ν F) (A : Matrix κ κ F) (i j : ν) :
    (Sᵀ * A * S) i j = S.mulVec (Pi.single i 1) ⬝ᵥ A.mulVec (S.mulVec (Pi.single j 1)) := by
  have e : ∀ M : Matrix ν ν F, M i j = Pi.single i 1 ⬝ᵥ M.mulVec (Pi.single j 1) :=
    fun M => by simp
  rw [e (Sᵀ * A * S), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem gramSt_lowS_hwS : gramSt F lowS hwS = 1 := by
  rw [gramSt, transpose_mul_mul_apply, secSt_lowS, secSt_hwS]
  simp only [dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.mulVec, mul_ite, mul_one, mul_zero]
  change (formQ F ⊗ₖ gramL F) (.inr 0, lowL) (.inl 0, hwL) = 1
  rw [Matrix.kroneckerMap_apply, formQ_apply, gramL]
  simp [dualL, hwL, lowL]

@[expose] def rhoSt : ↥(U0 F) →* ((SIdx → F) →ₗ[F] (SIdx → F)) where
  toFun u := Matrix.mulVecLin (repSt (u : ↥(cayleyGroup F)))
  map_one' := by
    rw [Subgroup.coe_one, map_one, Matrix.mulVecLin_one]
    rfl
  map_mul' u v := by
    simp only [Subgroup.coe_mul, map_mul, Matrix.mulVecLin_mul]
    rfl

theorem det_gramSt_ne_zero_of_card_two [Fintype F] (hF : Fintype.card F = 2) :
    (gramSt F).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := finite_cayleyGroup (F := F)
  let _ : Fintype ↥(U0 F) := Fintype.ofFinite _
  let W : Submodule F (SIdx → F) := LinearMap.ker (gramSt F).mulVecLin
  have hW : ∀ u : ↥(U0 F), ∀ w ∈ W, rhoSt F u w ∈ W := by
    intro u w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    change (gramSt F).mulVec ((repSt (u : ↥(cayleyGroup F))).mulVec w) = 0
    rw [Matrix.mulVec_mulVec, gramSt_mul_repSt, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have hne : W ≠ ⊥ := by
    intro h
    apply hx0
    have : x ∈ W := by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hx]
    rw [h] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨w, hwW, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup F Nat.prime_two isPGroup_U0
    (rhoSt F) W hW hne
  have hn : Nat.card F = 2 ^ 1 := by rw [Nat.card_eq_fintype_card, hF, pow_one]
  have hv : ∑ u, rhoSt F u (Pi.single lowS 1) ≠ 0 := by
    intro h
    have h1 := congrFun h hwS
    rw [Finset.sum_apply, Pi.zero_apply] at h1
    change ∑ u : ↥(U0 F), (repSt (u : ↥(cayleyGroup F))).mulVec (Pi.single lowS 1) hwS = 0 at h1
    have h2 : ∑ u : ↥(U0 F), cQ (u : ↥(cayleyGroup F)) * cG (u : ↥(cayleyGroup F)) = 1 := by
      simpa [hF] using sum_U0_cQ_cG (F := F) hn
    rw [Finset.sum_congr rfl fun u _ => st_coord_hwS F u.2, h2] at h1
    exact one_ne_zero h1
  have hdim : Module.finrank F (SIdx → F) = Fintype.card ↥(U0 F) := by
    rw [Module.finrank_fintype_fun_eq_card, card_SIdx, Fintype.card_eq_nat_card, card_U0 hn, hn]
    norm_num
  obtain ⟨-, -, -, hfix⟩ := orbit_regular_of_norm_ne_zero F Nat.prime_two isPGroup_U0 (rhoSt F) _
    hv hdim
  have hwmem : w ∈ fixedSub (rhoSt F) ⊤ := fun u _ => hwfix u
  have hhw : (Pi.single hwS 1 : SIdx → F) ∈ fixedSub (rhoSt F) ⊤ := fun u _ => repSt_U0_hw u.2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwmem⟩ : fixedSub (rhoSt F) ⊤)
    (fun h => hw0 (congrArg Subtype.val h))).mp hfix ⟨_, hhw⟩
  have hc' : c • w = Pi.single hwS 1 := congrArg Subtype.val hc
  have hzero : (gramSt F).mulVec (Pi.single hwS 1) = 0 := by
    rw [← hc', Matrix.mulVec_smul]
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hwW
    rw [hwW, smul_zero]
  have h3 := congrFun hzero lowS
  rw [Matrix.mulVec_single_one, Pi.zero_apply] at h3
  change gramSt F lowS hwS = 0 at h3
  rw [gramSt_lowS_hwS] at h3
  exact one_ne_zero h3

theorem det_gramSt_two : (gramSt (ZMod 2)).det ≠ 0 :=
  det_gramSt_ne_zero_of_card_two (ZMod 2) (ZMod.card 2)

theorem tLow_coords_li [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    LinearIndependent k (fun x : TIdx lab => fun u : ↥(U0 F) =>
      (tRep F k lab u).mulVec (tLow F k lab) x) := by
  have h := (st_coords_li F k hF).comp (embT lab) (embT_injective lab)
  convert h using 1
  funext x u
  exact tRep_U0_low F k lab u.2 x

theorem tLow_span [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    Submodule.span k (Set.range fun u : ↥(U0 F) =>
      matRep (tRep F k lab) (u : ↥(cayleyGroup F)) (tLow F k lab)) = ⊤ :=
  span_orbit_eq_top_of_coords _ _ _ (tLow_coords_li F k hF lab)

@[expose] def tGram (lab : Fin f → G2L) : Matrix (TIdx lab) (TIdx lab) k :=
  kron fun j => ((lab j).gram (F := F)).map (frK k (j : ℕ))

@[expose] def tGramInv (lab : Fin f → G2L) : Matrix (TIdx lab) (TIdx lab) k :=
  kron fun j => ((lab j).gramInv (F := F)).map (frK k (j : ℕ))

theorem tGram_mul_tRep (lab : Fin f → G2L) (g : ↥(cayleyGroup F)) :
    tGram F k lab * tRep F k lab g = (tRep F k lab g⁻¹)ᵀ * tGram F k lab := by
  rw [tGram, tRep, kronRep_apply, kronRep_apply, ← kron_mul, kron_transpose, ← kron_mul]
  congr 1
  funext j
  rw [matMap_apply, matMap_apply, ← Matrix.map_mul, G2L.gram_mul_rep, Matrix.map_mul,
    Matrix.transpose_map]

theorem tGram_mul_tGramInv (lab : Fin f → G2L) :
    tGram F k lab * tGramInv F k lab = 1 := by
  rw [tGram, tGramInv, ← kron_mul]
  have e : (fun j : Fin f => ((lab j).gram (F := F)).map (frK k (j : ℕ)) *
      ((lab j).gramInv (F := F)).map (frK k (j : ℕ))) = fun j => 1 := by
    funext j
    rw [← Matrix.map_mul, G2L.gram_mul_gramInv det_gramSt_two,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e, kron_one]

theorem tRep_hline [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    ∃ n ∈ fixedSub (matRep (tRep F k lab)) (U0 F),
      ∀ w ∈ fixedSub (matRep (tRep F k lab)) (U0 F), ∃ c : k, w = c • n := by
  refine hline_of_cocyclic (tRep F k lab) (U0 F) ((tGram F k lab).mulVec (tLow F k lab)) ?_
  have e : (Set.range fun u : ↥(U0 F) =>
      (tRep F k lab ((u : ↥(cayleyGroup F))⁻¹))ᵀ.mulVec ((tGram F k lab).mulVec (tLow F k lab))) =
      (tGram F k lab).mulVecLin '' Set.range fun u : ↥(U0 F) =>
        matRep (tRep F k lab) (u : ↥(cayleyGroup F)) (tLow F k lab) := by
    rw [← Set.range_comp]
    congr 1
    funext u
    simp only [Function.comp_apply, Matrix.mulVecLin_apply, matRep_apply, Matrix.mulVec_mulVec,
      tGram_mul_tRep]
  rw [e, Submodule.span_image, tLow_span F k hF, Submodule.map_top, eq_top_iff]
  intro z _
  refine ⟨(tGramInv F k lab).mulVec z, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, tGram_mul_tGramInv, Matrix.one_mulVec]

theorem tRep_fixed_irreducible [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    fixedSub (matRep (tRep F k lab)) (U0 F) = Submodule.span k {tHw F k lab} ∧
      (matRep (tRep F k lab)).IsIrreducible := by
  have := finite_cayleyGroup (F := F)
  refine fixed_line_and_irreducible Nat.prime_two (matRep (tRep F k lab)) (U0 F) isPGroup_U0
    (tHw F k lab) (tHw_ne_zero F k lab) (fun u hu => tRep_U0_hw F k lab hu) g2Sw ?_
    (tRep_hline F k hF lab)
  have e : matRep (tRep F k lab) (g2Sw : ↥(cayleyGroup F)) (tHw F k lab) = tLow F k lab :=
    tRep_g2Sw_hw F k lab
  rw [e]
  exact tLow_span F k hF lab

end CFSG.Quasithin.B42G2Ten
