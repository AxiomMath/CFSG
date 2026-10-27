module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaCent
public import CFSG.RankThree.GF2n.Stroth80.Sec53aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_Vt_inf_QB_plus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 3 ≤ m)
    (hom : OmegaPlusNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := hom
  letI := fK
  letI := finK
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
  have hQ := nondegenerate_polarBilin_quadPlus m K
  have hX := addCommutantScalar_statedOmegaPlus (K := K) (m := m) hm
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm) hQ h3
    hX φ hφ ψ hψ
  obtain ⟨u, -, hu0, -, hW, -, -⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK
    (ElemMatrixIso.plus hm) hQ h3 hX φ hφ hker ψ hψ hsing
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B :=
    le_inf (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hc.Z_le_QB.1
  have hW0card : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
      Nat.card Z * Nat.card K ^ (Fintype.card (Fin m ⊕ Fin m) - 1) := by
    have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left
      {x | polar (quadPlus m K) u x = 0} (fun x => hW x)
    rw [h1]
    congr 1
    exact card_polar_perp (quadPlus m K) hQ hu0
  have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  have hpow : Nat.card Z * Nat.card Z ^ (2 * m - 1) = Nat.card Z ^ (2 * m) := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
  rw [hW0card, hι, hK, hpow]

theorem card_Vt_inf_QB_minus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (hom : OmegaMinusNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := hom
  letI := fK
  letI := finK
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hX := addCommutantScalar_statedOmegaMinus (m := m) (b := b) (c := c) hm hirr
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr) hQ h3
    hX φ hφ ψ hψ
  obtain ⟨u, -, hu0, -, hW, -, -⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK
    (ElemMatrixIso.minus hm hirr) hQ h3 hX φ hφ hker ψ hψ hsing
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B :=
    le_inf (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hc.Z_le_QB.1
  have hW0card : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
      Nat.card Z * Nat.card K ^ (Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) - 1) := by
    have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left
      {x | polar (quadMinus m K b c) u x = 0} (fun x => hW x)
    rw [h1]
    congr 1
    exact card_polar_perp (quadMinus m K b c) hQ hu0
  have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  have hpow : Nat.card Z * Nat.card Z ^ (2 * m - 1) = Nat.card Z ^ (2 * m) := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
  rw [hW0card, hι, hK, hpow]

theorem card_Vt_of_omegaPlus (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hm : 3 ≤ m)
    (hom : OmegaPlusNat hc t m) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := hom
  have := card_V_of_naturalRep (Z := Z) (V := Vt M (LB M Q B) B Z t)
    (R := Rt M (LB M Q B) t) (N := hc.CN t) sec39_Z_le_Vt hK hnat
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using this

theorem card_Vt_of_omegaMinus (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hm : 2 ≤ m)
    (hom : OmegaMinusNat hc t m) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := hom
  have := card_V_of_naturalRep (Z := Z) (V := Vt M (LB M Q B) B Z t)
    (R := Rt M (LB M Q B) t) (N := hc.CN t) sec39_Z_le_Vt hK hnat
  rw [this]
  congr 1
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem Ctx.card_Vt_inf_QB_of_omegaNat (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) :
    ∃ m : ℕ, 2 ≤ m ∧ Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) ∧
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  rcases hom with ⟨K, fK, finK, hK, hplus | hminus⟩
  · obtain ⟨m, hm, hnat⟩ := hplus
    exact ⟨m, by omega, card_Vt_of_omegaPlus hc hm ⟨K, fK, finK, hK, hnat⟩,
      card_Vt_inf_QB_plus h34 hRoot hc hs hm ⟨K, fK, finK, hK, hnat⟩⟩
  · obtain ⟨m, b, c, hm, hirr, hnat⟩ := hminus
    exact ⟨m, hm, card_Vt_of_omegaMinus hc hm ⟨K, fK, finK, hK, b, c, hirr, hnat⟩,
      card_Vt_inf_QB_minus h34 hRoot hc hs hm ⟨K, fK, finK, hK, b, c, hirr, hnat⟩⟩
theorem bilin_orthogonal_sup_eq_inf {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (U W : Submodule K E) :
    B.orthogonal (U ⊔ W) = B.orthogonal U ⊓ B.orthogonal W := by
  ext e
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.add_apply, h1 y hy, h2 z hz, add_zero]

theorem card_QB_inf_Wt (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) :
    Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm
  have hn_gt : 2 < n := hs.n_gt
  obtain ⟨m, hm, hVcard, hVQB⟩ := Ctx.card_Vt_inf_QB_of_omegaNat h34 hRoot hc hs hom
  obtain ⟨K, hKf, hKfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := hKf
  letI := hKfin
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hK2 : 1 < Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hcard33 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (hc.card_of_3_3 hs.width (by omega) hs.noA2 (stroth_3_3 hc hs.width (by omega))).2
  have hE : Module.finrank K M₀.E = 2 * n := hD.finrank_E hs.width hK2
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := LinearMap.IsAlt.isRefl (fun e => M₀.alt e)
  obtain ⟨U, hUmem⟩ := hc.exists_submodule_inf_QB hs.width hcard33 hD
  let Vsub : Submodule K M₀.E := imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  let Wsub : Submodule K M₀.E :=
    imgSub M₀ (Wt Q (Vt M (LB M Q B) B Z t))
      (fun c e he => smul_mem_img_Wt M₀ hD.reg hVQ c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun e => mem_imgSub
  have hWsub_mem : ∀ e, e ∈ Wsub ↔ e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
    fun e => mem_imgSub
  have hUorth : ∀ e ∈ U, ∀ f ∈ U, M₀.B e f = 0 := by
    intro e he f hf
    obtain ⟨x, hx, hxe⟩ := (hUmem e).mp he
    obtain ⟨y, hy, hyf⟩ := (hUmem f).mp hf
    have hxy : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      have hc1 := hc.inf_QB_elemAbelian.1.is_comm
      exact congrArg Subtype.val (hc1.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have h1 := M₀.comm_eq x hx.1 y hy.1
    rw [hxy, hD.reg.one] at h1
    simpa [hxe, hyf] using h1.symm
  have hUle : U ≤ M₀.B.orthogonal U := by
    intro e he f hf
    rw [M₀.B_comm, hUorth e he f hf, neg_zero]
  have hUdim : Module.finrank K U = n := by
    have hUcardImg : Nat.card ↥U = Nat.card (M₀.img (Q ⊓ QB B)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => hUmem e)
    have hQcard : Nat.card ↥(Q ⊓ QB B) =
        Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) :=
      M₀.card_eq inf_le_left (le_inf hc.Z_le_Q hc.Z_le_QB.1)
    have hUcard : Nat.card ↥U = Nat.card Z ^ n := by
      rw [hUcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hcard33, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K U = Nat.card K ^ n := by
      rw [← Module.natCard_eq_pow_finrank, hUcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hUlag : M₀.B.orthogonal U = U := by
    refine (Submodule.eq_of_le_of_finrank_eq hUle ?_).symm
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB U
    omega
  have hVdim : Module.finrank K Vsub = 2 * m := by
    have hVcardImg : Nat.card ↥Vsub = Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => (hVsub_mem e).symm)
    have hQcard : Nat.card ↥(Vt M (LB M Q B) B Z t) =
        Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) :=
      M₀.card_eq hVQ sec39_Z_le_Vt
    have hVcard : Nat.card ↥Vsub = Nat.card Z ^ (2 * m) := by
      rw [hVcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hVcard, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ (2 * m) := by
      rw [← Module.natCard_eq_pow_finrank, hVcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hWorth : Wsub = M₀.B.orthogonal Vsub := by
    ext e
    rw [hWsub_mem, mem_img_Wt_iff M₀ hD.reg hVQ]
    constructor
    · intro h f hf
      rw [M₀.B_comm, h f ((hVsub_mem f).mpr hf), neg_zero]
    · intro h f hf
      have := h f ((hVsub_mem f).mpr hf)
      rwa [M₀.B_comm, neg_eq_zero] at this
  have hUVdim : Module.finrank K ↥(U ⊓ Vsub) = 2 * m - 1 := by
    have hsetV : Vt M (LB M Q B) B Z t ⊓ QB B =
        (Q ⊓ QB B) ⊓ Vt M (LB M Q B) B Z t := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        exact ⟨⟨hVQ hx, hxB⟩, hx⟩
      · rintro ⟨⟨-, hxB⟩, hx⟩
        exact ⟨hx, hxB⟩
    have hinfimg : M₀.img ((Q ⊓ QB B) ⊓ Vt M (LB M Q B) B Z t) =
        M₀.img (Q ⊓ QB B) ⊓ M₀.img (Vt M (LB M Q B) B Z t) :=
      quadModel_img_inf M₀ (le_inf hc.Z_le_Q hc.Z_le_QB.1) sec39_Z_le_Vt inf_le_left hVQ
    have hset : ∀ e, e ∈ U ⊓ Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B) := by
      intro e
      rw [Submodule.mem_inf, hUmem, hVsub_mem, hsetV]
      constructor
      · rintro ⟨he1, he2⟩
        rw [hinfimg]
        exact ⟨he1, he2⟩
      · intro he
        rw [hinfimg] at he
        exact ⟨he.1, he.2⟩
    have hcardImg : Nat.card (M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B)) =
        Nat.card Z ^ (2 * m - 1) := by
      have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
          Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B)) :=
        M₀.card_eq ((inf_le_left : Vt M (LB M Q B) B Z t ⊓ QB B ≤ _).trans hVQ)
          (le_inf sec39_Z_le_Vt hc.Z_le_QB.1)
      rw [hVQB] at h1
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← h1, ← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
    have hUVcard : Nat.card ↥(U ⊓ Vsub) = Nat.card Z ^ (2 * m - 1) :=
      (Nat.card_congr (Equiv.subtypeEquivRight fun e => hset e)).trans hcardImg
    have h2 : Nat.card ↥(U ⊓ Vsub) = Nat.card K ^ (2 * m - 1) := by
      rw [hUVcard, hKZ]
    have h1 : Nat.card K ^ Module.finrank K ↥(U ⊓ Vsub) = Nat.card K ^ (2 * m - 1) := by
      conv_lhs => rw [← Module.natCard_eq_pow_finrank]
      exact h2
    exact Nat.pow_right_injective hK2 h1
  have hWdim : Module.finrank K Wsub = 2 * n - 2 * m := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB Vsub
    rw [← hWorth] at h1
    omega
  have horthsup : M₀.B.orthogonal (U ⊔ Wsub) = U ⊓ Vsub := by
    rw [bilin_orthogonal_sup_eq_inf, hUlag, hWorth,
      LinearMap.BilinForm.orthogonal_orthogonal hB hrefl Vsub]
  have hUWdim : Module.finrank K ↥(U ⊓ Wsub) = n - 1 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq U Wsub
    have e2 := LinearMap.BilinForm.finrank_orthogonal hB (U ⊔ Wsub)
    rw [horthsup, hUVdim] at e2
    have e3 : Module.finrank K ↥(U ⊔ Wsub) ≤ Module.finrank K M₀.E := Submodule.finrank_le _
    omega
  have hUWcard : Nat.card ↥(U ⊓ Wsub) = Nat.card Z ^ (n - 1) := by
    have h2 : Nat.card ↥(U ⊓ Wsub) = Nat.card K ^ (n - 1) := by
      conv_lhs => rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(U ⊓ Wsub))]
      rw [hUWdim]
    rwa [hKZ] at h2
  have hImgEq : M₀.img (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      (U ⊓ Wsub).toAddSubgroup := by
    have hinfimg := quadModel_img_inf M₀
      (S := Q ⊓ QB B) (T := Wt Q (Vt M (LB M Q B) B Z t))
      (le_inf hc.Z_le_Q hc.Z_le_QB.1) hZW inf_le_left inf_le_left
    have hset : (Q ⊓ QB B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) =
        QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
      ext x
      constructor
      · rintro ⟨⟨-, hx⟩, hw⟩
        exact ⟨hx, hw⟩
      · rintro ⟨hx, hw⟩
        exact ⟨⟨(inf_le_left : Wt Q _ ≤ Q) hw, hx⟩, hw⟩
    rw [hset] at hinfimg
    rw [hinfimg]
    ext e
    constructor
    · rintro ⟨he1, he2⟩
      exact ⟨(hUmem e).mpr he1, (hWsub_mem e).mpr he2⟩
    · rintro ⟨he1, he2⟩
      exact ⟨(hUmem e).mp he1, (hWsub_mem e).mp he2⟩
  have hWcard : Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card ↥(U ⊓ Wsub) := by
    have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
    have h1 := M₀.card_eq (S := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))
      (inf_le_right.trans hWQ) (le_inf hc.Z_le_QB.1 hZW)
    rw [h1, hImgEq]
    rfl
  have hn1 : 1 ≤ n := by have := hs.n_gt; omega
  rw [hWcard, hUWcard]
  rw [← pow_succ', show n - 1 + 1 = n by omega]

end CFSG.RankThree.GF2n.Stroth80
