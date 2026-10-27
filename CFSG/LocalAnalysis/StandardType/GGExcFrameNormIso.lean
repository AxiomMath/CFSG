module

public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTvE7E8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo
  TableBExcTwoFusion TableBExcTwoTB Matrix

namespace ExcFrameIso

section NormIso

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem frameCoordHom_form (hsym : ∀ i, τ.symmetrizer i i = 1) (F : OrthFrame τ d)
    (x y : Fin (d + 1) → ZMod 3) :
    frameCoordHom F x ⬝ᵥ (NoTvAut.cartanMod τ 3 *ᵥ frameCoordHom F y) = 2 * (x ⬝ᵥ y) := by
  have hΛ : ∀ z : Fin (d + 1) → ZMod 3,
      frameCoordHom F z = ∑ i, z i • redMod τ 3 (F.root i) := by
    intro z
    funext k
    simp [frameCoordHom, Finset.sum_apply, redMod]
  have hform : ∀ i j, redMod τ 3 (F.root i) ⬝ᵥ
      (NoTvAut.cartanMod τ 3 *ᵥ redMod τ 3 (F.root j)) = if i = j then 2 else 0 := by
    intro i j
    rw [NoTvAut.redMod_form, dotProduct_mulVec_eq_iform]
    by_cases hij : i = j
    · subst hij
      rw [iform_self_eq_two_of_isRoot hsym (F.isRoot i)]
      simp
    · rw [F.orth i j hij]
      simp [hij]
  have key : frameCoordHom F x ⬝ᵥ (NoTvAut.cartanMod τ 3 *ᵥ frameCoordHom F y) =
      ∑ j, ∑ i, x i * y j * (redMod τ 3 (F.root i) ⬝ᵥ
        (NoTvAut.cartanMod τ 3 *ᵥ redMod τ 3 (F.root j))) := by
    rw [hΛ x, hΛ y]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  simp only [hform, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem normIsometry_of_frame (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hd : d + 1 = τ.rank) (hK : Nat.card K = 2) (φ : MulAut (adjointGroup τ K))
    (hφ : ∀ x ∈ (tE K F).range, φ x ∈ (tE K F).range) :
    ∃ M : (Fin (d + 1) → ZMod 3) →+ (Fin (d + 1) → ZMod 3),
      (∀ v, φ (tE K F (Multiplicative.ofAdd v)) = tE K F (Multiplicative.ofAdd (M v))) ∧
        ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have h3 : 3 ∣ Nat.card L - 1 := three_dvd_natCard_ext_sub_one hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hsym := F.symm_one
  have hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L :=
    TableBExc.full_of_E7_E8 hτ
  have hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod 3) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) (by norm_num)
  have hV : Nat.card (TableBExc.torusPow τ L 3) = 3 ^ τ.rank := by
    rcases hτ with rfl | rfl
    · exact TableBExc.card_torusPow_E7 Nat.prime_three h3
    · exact TableBExc.card_torusPow_E8 Nat.prime_three h3
  have hfinL : Finite (adjointGroup τ L) := generated_group_finite τ L
  have hfinK : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨g, rfl⟩ := mem_range_conj_adjoint hτ hK φ
  set G := langElt F hωo with hG
  set ι := adjointMap τ (algebraMap K L) with hι
  have hιinj : Function.Injective ι := adjointMap_injective _
  set D : (Fin τ.rank → ZMod 3) → adjointGroup τ L := fun s =>
    ⟨ExcFrames.frameDiag ω hω3 s, ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 s⟩ with hD
  have hKI : ∀ v, ι (tE K F (Multiplicative.ofAdd v)) = G * D (frameCoordHom F v) * G⁻¹ :=
    fun v => adjointMap_tE_eq hsym F hωo hω3 hfull v
  set T := (tE K F).range with hT
  have hle : T.map (MulAut.conj g).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφ x hx
  have hTeq : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hgT : ∀ x, x ∈ T ↔ g * x * g⁻¹ ∈ T := by
    intro x
    constructor
    · intro hx
      exact hle ⟨x, hx, rfl⟩
    · intro hx
      rw [← hTeq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxy : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        exact mul_right_cancel (mul_left_cancel h1)
      exact hxy ▸ hy
  have hTcard : Nat.card T = 3 ^ τ.rank := by
    have e : Multiplicative (Fin (d + 1) → ZMod 3) ≃ T :=
      (MonoidHom.ofInjective (tE_injective F)).toEquiv
    rw [← hd, ← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  set T' : Subgroup (adjointGroup τ L) := (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom with hT'
  have hT'le : T' ≤ TableBExc.torusPow τ L 3 := by
    rintro _ ⟨_, ⟨y, ⟨u, rfl⟩, rfl⟩, rfl⟩
    have hu : ι (tE K F u) = G * D (frameCoordHom F (Multiplicative.toAdd u)) * G⁻¹ := by
      have := hKI (Multiplicative.toAdd u)
      rwa [ofAdd_toAdd] at this
    have e : (MulAut.conj G⁻¹).toMonoidHom (ι (tE K F u)) =
        D (frameCoordHom F (Multiplicative.toAdd u)) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
      group
    rw [e]
    exact ExcFrames.mem_torusPow_iff_coe.mpr (ExcFrames.frameDiag_mem hfull ω hω3 _)
  have hT'eq : T' = TableBExc.torusPow τ L 3 :=
    Subgroup.eq_of_le_of_card_ge hT'le (by
      rw [hV, hT', Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective,
        Subgroup.card_map_of_injective hιinj, hTcard])
  set a : adjointGroup τ L := G⁻¹ * ι g * G with ha
  have hmemV : ∀ x : adjointGroup τ L,
      x ∈ TableBExc.torusPow τ L 3 ↔ ∃ y ∈ T, x = G⁻¹ * ι y * G := by
    intro x
    rw [← hT'eq]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
  have hnorm : ∀ x : adjointGroup τ L,
      x ∈ TableBExc.torusPow τ L 3 ↔ a * x * a⁻¹ ∈ TableBExc.torusPow τ L 3 := by
    intro x
    rw [hmemV, hmemV]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, (hgT y).mp hy, ?_⟩
      simp only [ha, map_mul, map_inv]
      group
    · rintro ⟨z, hz, hzx⟩
      have hgz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      refine ⟨g⁻¹ * z * g, (hgT _).mpr (by rw [hgz]; exact hz), ?_⟩
      have h1 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [h1, hzx]
      simp only [ha, map_mul, map_inv]
      group
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes hnorm
  have hex : ∀ v : Fin (d + 1) → ZMod 3, ∃ v' : Fin (d + 1) → ZMod 3,
      tE K F (Multiplicative.ofAdd v') = g * tE K F (Multiplicative.ofAdd v) * g⁻¹ := by
    intro v
    obtain ⟨u, hu⟩ := hφ _ ⟨Multiplicative.ofAdd v, rfl⟩
    refine ⟨Multiplicative.toAdd u, ?_⟩
    rw [ofAdd_toAdd, hu]
    rfl
  choose M0 hM0 using hex
  have hM0add : ∀ v v', M0 (v + v') = M0 v + M0 v' := by
    intro v v'
    apply Multiplicative.ofAdd.injective
    apply tE_injective (K := K) F
    rw [hM0, ofAdd_add, map_mul, ofAdd_add, map_mul, hM0, hM0]
    group
  have hΛ : ∀ v, frameCoordHom F (M0 v) = TableBExc.torusAct τ 3 w (frameCoordHom F v) := by
    intro v
    refine ExcFrames.frameDiag_injective hωo hω3 hdet ?_
    have e1 : D (frameCoordHom F (M0 v)) = G⁻¹ * ι (tE K F (Multiplicative.ofAdd (M0 v))) * G := by
      rw [hKI]
      group
    have e2 : G⁻¹ * ι (tE K F (Multiplicative.ofAdd (M0 v))) * G =
        a * D (frameCoordHom F v) * a⁻¹ := by
      rw [hM0 v, map_mul, map_mul, map_inv, hKI v]
      simp only [ha]
      group
    have e3 := congrArg (Subtype.val : adjointGroup τ L → ModGL τ L) (e1.trans e2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
    refine e3.trans ?_
    show (a : ModGL τ L) * ExcFrames.frameDiag ω hω3 (frameCoordHom F v) * (a : ModGL τ L)⁻¹ = _
    rw [hw _ (ExcFrames.frameDiag_mem hfull ω hω3 _), ExcFrames.canonicalRep_conj_frameDiag]
  refine ⟨AddMonoidHom.mk' M0 hM0add, fun v => ?_, fun v v' => ?_⟩
  · show g * tE K F (Multiplicative.ofAdd v) * g⁻¹ = tE K F (Multiplicative.ofAdd (M0 v))
    exact (hM0 v).symm
  · show M0 v ⬝ᵥ M0 v' = v ⬝ᵥ v'
    have h2 : (2 : ZMod 3) * (M0 v ⬝ᵥ M0 v') = 2 * (v ⬝ᵥ v') := by
      rw [← frameCoordHom_form hsym F, ← frameCoordHom_form hsym F, hΛ v, hΛ v',
        NoTvAut.torusAct_form]
    exact (mul_right_inj' zmod3_two_ne_zero).mp h2

theorem ggE7TwoNormIsometry_holds {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : GGE7TwoNormIsometry K :=
  fun φ hφ => normIsometry_of_frame (Or.inl rfl) frameE7 rfl hK φ hφ

theorem ggE8TwoNormIsometry_holds {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : GGE8TwoNormIsometry K :=
  fun φ hφ => normIsometry_of_frame (Or.inr rfl) frameE8 rfl hK φ hφ

theorem ggE7TwoNormIsometryInput_holds : GGE7TwoNormIsometryInput :=
  fun _ _ _ _ hK => ggE7TwoNormIsometry_holds hK

theorem ggE8TwoNormIsometryInput_holds : GGE8TwoNormIsometryInput :=
  fun _ _ _ _ hK => ggE8TwoNormIsometry_holds hK

end NormIso

end ExcFrameIso

end CFSG.StandardType

end
