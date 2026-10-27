module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Sp
public import CFSG.Milestones.ASVolI.F431.RU4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngLift
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.LieType.BorelTits Module Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Descent

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def semiMap (σ : K ≃+* K) (A : Matrix ι ι K) (v : ι → K) : ι → K :=
  A *ᵥ fun i => σ (v i)

theorem semiMap_add (σ : K ≃+* K) (A : Matrix ι ι K) (u v : ι → K) :
    semiMap σ A (u + v) = semiMap σ A u + semiMap σ A v := by
  unfold semiMap
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem semiMap_smul (σ : K ≃+* K) (A : Matrix ι ι K) (c : K) (v : ι → K) :
    semiMap σ A (c • v) = σ c • semiMap σ A v := by
  unfold semiMap
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem semiMap_semiMap (σ : K ≃+* K) (hσ2 : ∀ c, σ (σ c) = c) {A : Matrix ι ι K}
    (hA : A * A.map σ = 1) (v : ι → K) : semiMap σ A (semiMap σ A v) = v := by
  unfold semiMap
  have h1 : (fun i => σ ((A *ᵥ fun j => σ (v j)) i)) = A.map σ *ᵥ fun j => σ (σ (v j)) := by
    funext i
    exact RingHom.map_mulVec (σ : K →+* K) A (fun j => σ (v j)) i
  rw [h1, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  funext i
  exact hσ2 _

@[expose] def semiFix (σ : K ≃+* K) (A : Matrix ι ι K) : AddSubgroup (ι → K) where
  carrier := {v | semiMap σ A v = v}
  add_mem' := by
    intro u v hu hv
    change semiMap σ A (u + v) = u + v
    rw [semiMap_add]
    rw [show semiMap σ A u = u from hu, show semiMap σ A v = v from hv]
  zero_mem' := by
    change semiMap σ A 0 = 0
    have h := semiMap_smul σ A 0 0
    simpa using h
  neg_mem' := by
    intro v hv
    change semiMap σ A (-v) = -v
    have h := semiMap_smul σ A (-1) v
    rw [show semiMap σ A v = v from hv, map_neg, map_one, neg_one_smul] at h
    exact h

theorem mem_semiFix {σ : K ≃+* K} {A : Matrix ι ι K} {v : ι → K} :
    v ∈ semiFix σ A ↔ semiMap σ A v = v :=
  Iff.rfl

theorem semiMap_eq_of_fix (σ : K ≃+* K) (hσ2 : ∀ c, σ (σ c) = c) {A : Matrix ι ι K}
    (hA : A * A.map σ = 1) {ω : K} (hω : σ ω ≠ ω) (v : ι → K) :
    ∃ u₁ ∈ semiFix σ A, ∃ u₂ ∈ semiFix σ A, semiMap σ A v = (ω + σ ω)⁻¹ • (ω • u₁ + u₂) := by
  have hτ2 := semiMap_semiMap σ hσ2 hA
  have hc : ω + σ ω ≠ 0 := by
    intro h0
    apply hω
    have : σ ω = -ω := eq_neg_of_add_eq_zero_right h0
    rw [this, CharTwo.neg_eq]
  refine ⟨v + semiMap σ A v, ?_, ω • v + semiMap σ A (ω • v), ?_, ?_⟩
  · rw [mem_semiFix, semiMap_add, hτ2, add_comm]
  · rw [mem_semiFix, semiMap_add, hτ2, add_comm]
  · rw [semiMap_smul]
    have hvv : ω • v + ω • v = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hin : ω • (v + semiMap σ A v) + (ω • v + σ ω • semiMap σ A v) =
        (ω + σ ω) • semiMap σ A v := by
      calc ω • (v + semiMap σ A v) + (ω • v + σ ω • semiMap σ A v)
          = (ω • v + ω • v) + (ω • semiMap σ A v + σ ω • semiMap σ A v) := by rw [smul_add]; abel
        _ = (ω + σ ω) • semiMap σ A v := by rw [hvv, zero_add, add_smul]
    rw [hin, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_card_dvd_of_semilinear (hK : Fintype.card K = 4) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hσ2 : ∀ c, σ (σ c) = c) {A : Matrix ι ι K} (hA : A * A.map σ = 1) {R : Subgroup (GL ι K)}
    (hR : ∀ g ∈ R, A * (g : Matrix ι ι K).map σ = (g : Matrix ι ι K) * A) :
    ∃ d ≤ Fintype.card ι, Nat.card R ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω : K, σ ω ≠ ω := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  set V₀ := semiFix σ A with hV₀
  letI : Module (ZMod 2) V₀ := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, two_nsmul, AddSubgroup.coe_zero]
    funext i
    exact CharTwo.add_self_eq_zero _
  have hRV : ∀ g ∈ R, ∀ v ∈ V₀, (g : Matrix ι ι K) *ᵥ v ∈ V₀ := by
    intro g hg v hv
    rw [mem_semiFix] at hv ⊢
    unfold semiMap at hv ⊢
    have h1 : (fun i => σ (((g : Matrix ι ι K) *ᵥ v) i)) =
        (g : Matrix ι ι K).map σ *ᵥ fun j => σ (v j) := by
      funext i
      exact RingHom.map_mulVec (σ : K →+* K) (g : Matrix ι ι K) v i
    rw [h1, Matrix.mulVec_mulVec, hR g hg, ← Matrix.mulVec_mulVec, hv]
  let act : ↥R →* Module.End (ZMod 2) V₀ :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2
        { toFun := fun v => ⟨((g : GL ι K) : Matrix ι ι K) *ᵥ v, hRV g g.2 v v.2⟩
          map_zero' := Subtype.ext (Matrix.mulVec_zero _)
          map_add' := fun u v => Subtype.ext (Matrix.mulVec_add _ _ _) }
      map_one' := by
        ext v
        simp
      map_mul' := fun g g' => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  have hinj : Function.Injective act.toHomUnits := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ v ∈ V₀, ((g : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
      intro v hv
      have := congrArg (fun f : (Module.End (ZMod 2) V₀)ˣ => ((f : Module.End (ZMod 2) V₀) ⟨v, hv⟩ : ι → K)) hg
      simpa [act] using this
    have hall : ∀ w : ι → K, ((g : GL ι K) : Matrix ι ι K) *ᵥ w = w := by
      intro w
      have hτ2 := semiMap_semiMap σ hσ2 hA
      obtain ⟨u₁, hu₁, u₂, hu₂, he⟩ := semiMap_eq_of_fix σ hσ2 hA hω (semiMap σ A w)
      rw [hτ2] at he
      rw [he, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hfix u₁ hu₁, hfix u₂ hu₂]
    have hmat : ((g : GL ι K) : Matrix ι ι K) = 1 := by
      ext i j
      have h2 := congrFun (hall (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
      rw [h2, Matrix.one_apply, Pi.single_apply]
    exact Subtype.ext (Units.ext hmat)
  haveI : Fintype V₀ := Fintype.ofFinite _
  have hcard := Subgroup.card_dvd_of_injective act.toHomUnits hinj
  have hGL := card_generalLinearGroup (K := ZMod 2) (M := V₀) (n := finrank (ZMod 2) V₀) rfl
  rw [ZMod.card] at hGL
  refine ⟨finrank (ZMod 2) V₀, ?_, ?_⟩
  ·
    have hinj2 : Function.Injective fun xy : V₀ × V₀ => ((xy.1 : ι → K) + ω • (xy.2 : ι → K)) := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      simp only at hxy
      have hz : (x : ι → K) - x' = ω • ((y' : ι → K) - y) := by
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, hxy, add_comm]
      have ht : ((y' : ι → K) - y) ∈ V₀ := V₀.sub_mem y'.2 y.2
      have hzV : ((x : ι → K) - x') ∈ V₀ := V₀.sub_mem x.2 x'.2
      have h1 : semiMap σ A ((x : ι → K) - x') = (x : ι → K) - x' := hzV
      rw [hz, semiMap_smul, show semiMap σ A ((y' : ι → K) - y) = (y' : ι → K) - y from ht] at h1
      have h2 : (σ ω - ω) • ((y' : ι → K) - y) = 0 := by rw [sub_smul, h1, sub_self]
      have hne : σ ω - ω ≠ 0 := sub_ne_zero.2 hω
      have h3 : (y' : ι → K) - y = 0 := (smul_eq_zero.1 h2).resolve_left hne
      have hyy : y = y' := Subtype.ext (sub_eq_zero.1 h3).symm
      subst hyy
      have hxx : (x : ι → K) = x' := by simpa using hxy
      exact Prod.ext (Subtype.ext hxx) rfl
    have hle := Fintype.card_le_of_injective _ hinj2
    rw [Fintype.card_prod, Fintype.card_fun, hK, ← sq] at hle
    have hV : Fintype.card V₀ = 2 ^ finrank (ZMod 2) V₀ := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V₀), ZMod.card]
    rw [hV, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
    omega
  · have h1 : Nat.card (Module.End (ZMod 2) V₀)ˣ =
        ∏ i : Fin (finrank (ZMod 2) V₀), (2 ^ finrank (ZMod 2) V₀ - 2 ^ (i : ℕ)) := hGL
    rw [← h1]
    exact hcard

end Descent

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut X => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  rw [hZ] at hxZ
  exact Subgroup.mem_bot.1 hxZ

section U4

open CFSG.Quasithin.H13.U4Par CFSG.ASVolI

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem card_hypSU_two : Nat.card (hypSU h 2 0) = 3 ^ 4 * 320 := by
  rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_hypSU_four h]
  norm_num

theorem isSimpleGroup_hypSU_two : IsSimpleGroup (hypSU h 2 0) := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_hypSU_equiv_statedProj h
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [h.card]; norm_num
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK 4 (by norm_num)
    (by decide)
  exact e.isSimpleGroup

theorem center_hypSU_two_eq_bot : Subgroup.center (hypSU h 2 0) = ⊥ := by
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI := isSimpleGroup_hypSU_two h
  exact center_eq_bot_of_isSimpleGroup (by rw [card_hypSU_two h]; norm_num)
    (by rw [card_hypSU_two h]; norm_num)

theorem false_of_normalizes_hypSU_two {U R : Subgroup (hypSU h 2 0)} (hU : IsPGroup 2 U) (hUne : U ≠ ⊥)
    (hR : Nat.card R = 81) (hRU : R ≤ normalizer (U : Set (hypSU h 2 0))) : False := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [h.card]; norm_num
  obtain ⟨T, hT⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  let e := hypTransport h hT
  let U' : Subgroup (StatedSU (2 * 2 + 0) (2 ^ 1) K) := U.map e.toMonoidHom
  let R' : Subgroup (StatedSU (2 * 2 + 0) (2 ^ 1) K) := R.map e.toMonoidHom
  have hmem : ∀ (X : Subgroup (hypSU h 2 0)) (x : hypSU h 2 0), e x ∈ X.map e.toMonoidHom ↔ x ∈ X :=
    fun X x => by rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hU' : IsPGroup 2 U' := hU.map _
  have hU'ne : U' ≠ ⊥ := by
    intro hb
    apply hUne
    rw [eq_bot_iff]
    intro u hu
    have h1 : e u ∈ U' := (hmem U u).2 hu
    rw [hb, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (e.injective (by rw [h1, map_one]))
  have hR'card : Nat.card R' = 81 := by
    rw [Subgroup.card_map_of_injective e.injective, hR]
  have hR'U' : R' ≤ normalizer (U' : Set (StatedSU (2 * 2 + 0) (2 ^ 1) K)) := by
    intro x hx
    obtain ⟨g, rfl⟩ := e.surjective x
    have hg : g ∈ R := (hmem R g).1 hx
    rw [mem_normalizer_iff]
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [show e g * e u * (e g)⁻¹ = e (g * u * g⁻¹) by rw [map_mul, map_mul, map_inv], hmem, hmem]
    exact Subgroup.mem_normalizer_iff.1 (hRU hg) u
  have hρ := isIsometric_natRep_statedSU hK (2 * 2 + 0)
  have hinj := natRep_injective (StatedSU (2 * 2 + 0) (2 ^ 1) K)
  set F := unitaryForm 2 1 hK (2 * 2 + 0) with hF
  set ρ := natRep (StatedSU (2 * 2 + 0) (2 ^ 1) K) with hρdef
  set W₀ := isoSeq F ρ U' 1 with hW₀
  have hWne : W₀ ≠ ⊥ := isoSeq_one_ne_bot F ρ 2 hρ hinj U' hU' hU'ne
  have hWt : F.IsTotallyIsotropic W₀ := isoSeq_isTotallyIsotropic F ρ U' 1
  have hRW : ∀ g ∈ R', ∀ w ∈ W₀, ρ g w ∈ W₀ := fun g hg w hw =>
    apply_mem_isoSeq F ρ hρ U' 1 (hR'U' hg) hw
  have hn : finrank K (Fin (2 * 2 + 0) → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨a, ha⟩ : ∃ a, finrank K W₀ = a := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [← ha, Nat.one_le_iff_ne_zero]
    intro h0
    exact hWne (Submodule.finrank_eq_zero.1 h0)
  have ha2 : a ≤ 2 := by
    have hp := F.finrank_perp W₀
    have hle := Submodule.finrank_mono hWt
    omega
  have hodd : Odd (Nat.card R') := by rw [hR'card]; decide
  have hdvd := card_dvd_prod_of_stabilizes hρ hinj hWt (R := R') hodd hRW hn ha
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
  rw [hq, hR'card] at hdvd
  interval_cases a <;> revert hdvd <;> decide

theorem false_of_fieldAut_hypSU_two {R : Subgroup (hypSU h 2 0)} (hR : Nat.card R = 81) (a : hypSU h 2 0)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (ha : a * burnsideF4m_U4_fieldElt h σ a = 1)
    (hfix : ∀ s ∈ R, a * burnsideF4m_U4_fieldElt h σ s * a⁻¹ = s) : False := by
  classical
  haveI := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := h.charP
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
  have hσ2 : ∀ c, σ (σ c) = c := by
    rw [burnsideF4r_ringEquiv_eq_bar h σ hσ]
    exact fun c => h.bar_bar c
  have hcoe : ∀ g : hypSU h 2 0, ((burnsideF4m_U4_fieldElt h σ g : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = ((g : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K).map σ := fun g => rfl
  set A : Matrix (HypIndex 2 0) (HypIndex 2 0) K := ((a : GL (HypIndex 2 0) K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hAdef
  have hA : A * A.map σ = 1 := by
    have h1 := congrArg (fun x : hypSU h 2 0 => ((x : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) ha
    simp only [Subgroup.coe_mul, Units.val_mul, hcoe, Subgroup.coe_one, Units.val_one] at h1
    exact h1
  set R' : Subgroup (GL (HypIndex 2 0) K) := R.map (hypSU h 2 0).subtype with hR'def
  have hR' : ∀ g ∈ R', A * (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map σ =
      (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A := by
    rintro _ ⟨s, hs, rfl⟩
    have h2 : a * burnsideF4m_U4_fieldElt h σ s = s * a := by
      calc a * burnsideF4m_U4_fieldElt h σ s = a * burnsideF4m_U4_fieldElt h σ s * a⁻¹ * a := by group
        _ = s * a := by rw [hfix s hs]
    have h3 := congrArg (fun x : hypSU h 2 0 => ((x : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) h2
    simp only [Subgroup.coe_mul, Units.val_mul, hcoe] at h3
    exact h3
  obtain ⟨d, hd, hdvd⟩ := exists_card_dvd_of_semilinear hq σ hσ hσ2 hA hR'
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hR] at hdvd
  have hι : Fintype.card (HypIndex 2 0) = 4 := card_hypIndex
  rw [hι] at hd
  interval_cases d <;> revert hdvd <;> decide

theorem twoSigTriv_hypSU_two : TwoSigTriv 3 (hypSU h 2 0) := by
  classical
  intro S W hW hnorm
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card (S : Subgroup (hypSU h 2 0)) = 81 := by
    rw [card_sylow_eq S (card_hypSU_two h) (by norm_num)]
    norm_num
  have hconj := conj_injective_of_center_eq_bot (center_hypSU_two_eq_bot h)
  have hinn : ∀ x : hypSU h 2 0, MulAut.conj x ∈ W → x = 1 := by
    intro x hx
    by_contra hx1
    set U : Subgroup (hypSU h 2 0) := W.comap (MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)) with hU
    have hU2 : IsPGroup 2 U := hW.comap_of_injective _ hconj
    have hUne : U ≠ ⊥ := by
      intro hb
      have hxU : x ∈ U := hx
      rw [hb, Subgroup.mem_bot] at hxU
      exact hx1 hxU
    have hSU : (S : Subgroup (hypSU h 2 0)) ≤ normalizer (U : Set (hypSU h 2 0)) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro u
      have hc : MulAut.conj (g * u * g⁻¹) = MulAut.conj g * MulAut.conj u * (MulAut.conj g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      change MulAut.conj u ∈ W ↔ MulAut.conj (g * u * g⁻¹) ∈ W
      rw [hc]
      exact Subgroup.mem_normalizer_iff.1 (hnorm g hg) _
    exact false_of_normalizes_hypSU_two h hU2 hUne hS hSU
  by_contra hWne
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWne
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  obtain ⟨a, σ, hwa⟩ := burnsideF4m_U4_normalForm h w
  have hσ : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hwa
    rw [hwa] at hwW hw1'
    exact hw1' (by rw [hinn a hwW, map_one])
  have hσσ : σ * σ = 1 := by
    have hσ2 : ∀ c, σ (σ c) = c := by
      rw [burnsideF4r_ringEquiv_eq_bar h σ hσ]
      exact fun c => h.bar_bar c
    exact RingEquiv.ext hσ2
  set φ := burnsideF4m_U4_fieldAut h σ with hφ
  have hφφ : φ * φ = 1 := by rw [hφ, ← map_mul, hσσ, map_one]
  have hφa : φ a = burnsideF4m_U4_fieldElt h σ a := rfl
  have hw2 : w * w = MulAut.conj (a * burnsideF4m_U4_fieldElt h σ a) := by
    rw [hwa, ← hφa]
    calc MulAut.conj a * φ * (MulAut.conj a * φ) = MulAut.conj a * (φ * MulAut.conj a * φ⁻¹) * (φ * φ) := by
          group
      _ = MulAut.conj (a * φ a) := by rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hφφ, mul_one, map_mul]
  have haa : a * burnsideF4m_U4_fieldElt h σ a = 1 := hinn _ (by rw [← hw2]; exact W.mul_mem hwW hwW)
  have hfixS : ∀ s ∈ (S : Subgroup (hypSU h 2 0)), w s = s := by
    intro s hs
    have h1 : MulAut.conj s * w * (MulAut.conj s)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hnorm s hs) w).1 hwW
    have h2 : MulAut.conj s * w * (MulAut.conj s)⁻¹ * w⁻¹ ∈ W := W.mul_mem h1 (W.inv_mem hwW)
    have h3 : MulAut.conj s * w * (MulAut.conj s)⁻¹ * w⁻¹ = MulAut.conj (s * (w s)⁻¹) := by
      rw [map_mul, map_inv, ← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv w s]
      group
    rw [h3] at h2
    exact (mul_inv_eq_one.1 (hinn _ h2)).symm
  refine false_of_fieldAut_hypSU_two h hS a hσ haa fun s hs => ?_
  have h4 := hfixS s hs
  rw [hwa] at h4
  exact h4

theorem twoSigTriv_u42 {L : Type} [Group L] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 3 q)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq2, hq1, hd⟩ := hd
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  rw [hq2, hq1] at hF eF
  have hF' : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨e₀⟩ := nonempty_hypSU_equiv_statedProj hF'
  haveI : Finite (hypSU hF' 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU hF'
  exact (twoSigTriv_hypSU_two hF').of_mulEquiv (e₀.trans eF.symm)

end U4

end CFSG.LocalAnalysis.UniquenessCase.UCK
