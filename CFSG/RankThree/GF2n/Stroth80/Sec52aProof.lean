module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec53cShared
public import CFSG.RankThree.GF2n.Stroth80.Sec53aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec52a_card_Vt_inf_QB_plus (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 3 ≤ m) (hom : OmegaPlusNat hc t m) :
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

theorem sec52a_card_Vt_inf_QB_minus (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m) (hom : OmegaMinusNat hc t m) :
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

theorem Ctx.sec52a_card_Vt_inf_QB_of_omegaNat (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) :
    ∃ m : ℕ, 2 ≤ m ∧ Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) ∧
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  rcases hom with ⟨K, fK, finK, hK, hplus | hminus⟩
  · obtain ⟨m, hm, hnat⟩ := hplus
    exact ⟨m, by omega, card_Vt_of_plus (hc := hc) (t := t) ⟨K, fK, finK, hK, hnat⟩,
      sec52a_card_Vt_inf_QB_plus h34 hRoot hc hs hm ⟨K, fK, finK, hK, hnat⟩⟩
  · obtain ⟨m, b, c, hm, hirr, hnat⟩ := hminus
    exact ⟨m, hm, card_Vt_of_minus (hc := hc) (t := t) (by omega)
        ⟨K, fK, finK, hK, b, c, hirr, hnat⟩,
      sec52a_card_Vt_inf_QB_minus h34 hRoot hc hs hm ⟨K, fK, finK, hK, b, c, hirr, hnat⟩⟩

theorem sec52a_card_QB_inf_Wt (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) :
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
  obtain ⟨m, hm, hVcard, hVQB⟩ := Ctx.sec52a_card_Vt_inf_QB_of_omegaNat h34 hRoot hc hs hom
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
    have hVcard' : Nat.card ↥Vsub = Nat.card Z ^ (2 * m) := by
      rw [hVcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hVcard, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ (2 * m) := by
      rw [← Module.natCard_eq_pow_finrank, hVcard', hKZ]
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
    have hsup : M₀.B.orthogonal (U ⊔ Wsub) = M₀.B.orthogonal U ⊓ M₀.B.orthogonal Wsub := by
      ext w
      simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
      constructor
      · intro h
        exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
          fun u hu => h u (Submodule.mem_sup_right hu)⟩
      · rintro ⟨h, h'⟩ u hu
        obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hu
        rw [map_add, LinearMap.add_apply, h a ha, h' a' ha', add_zero]
    rw [hsup, hUlag, hWorth, LinearMap.BilinForm.orthogonal_orthogonal hB hrefl Vsub]
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

theorem sec52a_B_inf_QB_conj_eq_bot (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    B ⊓ QB (conjSubgroup r B) = ⊥ := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  obtain ⟨g, hg⟩ := hc.conj
  have hCQ : conjSubgroup r B ≤ QB B :=
    hc.hyp.le_QB_of_mem_QB (X := conjSubgroup r B) (Y := B)
      ⟨r * g, by rw [hg, conjSubgroup_mul]⟩ ⟨g, hg⟩ hb.1 hb1 hb.2
  obtain ⟨ĉ, hĉQ, hĉC, b', hb'B, hb'ne⟩ := hplane
  have hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inr hom)
  have hvV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.mem hr) hĉC
  have hvQB : ⁅ĉ, t⁆ ∈ QB B := (sup_le hCQ hc.Z_le_QB.1) hĉC
  have hperp := (stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnot ⁅ĉ, t⁆ hvV).mp hvQB
    b' hb'B ĉ hĉQ (by rw [show ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ = 1 by group]; exact Z.one_mem)
  exact hb'ne hperp

theorem sec52a_conj_sup_Z_of_mem_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {l : G}
    (hl : l ∈ hc.CN t) :
    conjSubgroup l (conjSubgroup r B) ⊔ Z = conjSubgroup r B ⊔ Z := by
  have hlR : l ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hl).1
  have hlM : l ∈ M := hc.Rt_le_M t hlR
  have hrM : r ∈ M := hc.Rt_le_M t hr
  set C : Subgroup G := conjSubgroup r B with hC
  have hCV : C ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup r B ≤ conjSubgroup r B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.mem hr)
  have hconj_le : conjSubgroup l C ≤ C ⊔ Z := by
    intro x hx
    have hxC : l⁻¹ * x * l ∈ C := mem_conjSubgroup.mp hx
    have hz : ⁅l, l⁻¹ * x * l⁆ ∈ Z := (Ctx.mem_CN.mp hl).2 _ (hCV hxC)
    have e : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
    have e2 : l * (l⁻¹ * x * l) * l⁻¹ = ⁅l, l⁻¹ * x * l⁆ * (l⁻¹ * x * l) := by
      rw [commutatorElement_def]; group
    rw [e, e2]
    exact (C ⊔ Z).mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hxC)
  have hle : conjSubgroup l C ⊔ Z ≤ C ⊔ Z := sup_le hconj_le le_sup_right
  have hcC : Ctx M Q Z C := hc.conj_of_mem hrM
  have hcCl : Ctx M Q Z (conjSubgroup l C) := hcC.conj_of_mem hlM
  have hCcard : Nat.card ↥C = Nat.card Z := by
    obtain ⟨g, hg⟩ := hcC.conj
    rw [hg, card_conjSubgroup]
  have hcardC : Nat.card ↥(C ⊔ Z) = Nat.card Z * Nat.card Z := by
    rw [hcC.card_sup_Z, hCcard]
  have hcardCl : Nat.card ↥(conjSubgroup l C ⊔ Z) = Nat.card Z * Nat.card Z := by
    rw [hcCl.card_sup_Z, card_conjSubgroup, hCcard]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardCl, hcardC])

theorem sec52a_QB_inf_normalizes_of_mem_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {l : G}
    (hl : l ∈ hc.CN t) :
    l ∈ Subgroup.normalizer ((Q ⊓ QB (conjSubgroup r B) : Subgroup G) : Set G) := by
  have hlR : l ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hl).1
  have hlM : l ∈ M := hc.Rt_le_M t hlR
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hcCl : Ctx M Q Z (conjSubgroup l (conjSubgroup r B)) := hcC.conj_of_mem hlM
  have hCeq := sec52a_conj_sup_Z_of_mem_CN hc hs hr hl
  have h1 : Q ⊓ QB (conjSubgroup l (conjSubgroup r B)) = Q ⊓ QB (conjSubgroup r B) :=
    sec8_inf_QB_eq_of_sup_eq hcCl hcC hCeq
  have h2 : conjSubgroup l (Q ⊓ QB (conjSubgroup r B)) = Q ⊓ QB (conjSubgroup r B) := by
    rw [conjSubgroup_inf, hc.conj_Q_eq hlM, ← QB_conj, h1]
  exact conjSubgroup_eq_self_iff.mp h2

theorem sec52a_comm_mem_Z_of_mem_CN (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {l : G} (hl : l ∈ (QB B ⊓ M) ⊓ hc.CN t) {d : G}
    (hdB : d ∈ QB B) (hdC : d ∈ QB (conjSubgroup r B)) (hdQ : d ∈ Q) :
    ⁅l, d⁆ ∈ Z := by
  have hlL : l ∈ LB M Q B := le_sup_right (a := Q) ⟨hl.1.1, hl.1.2⟩
  have hlN : l ∈ hc.CN t := hl.2
  have hlM : l ∈ M := hl.1.2
  have hZB : ⁅l, d⁆ ∈ (Z ⊔ B : Subgroup G) :=
    hc.comm_LB_inf_QB_mem_sup hlL ⟨hdQ, hdB⟩
  have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hlN
  have hldQ : l * d * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) d).mp hdQ
  have hldQC : l * d * l⁻¹ ∈ QB (conjSubgroup r B) :=
    ((Subgroup.mem_normalizer_iff.mp hnorm d).mp ⟨hdQ, hdC⟩).2
  have hcommQC : ⁅l, d⁆ ∈ Q ⊓ QB (conjSubgroup r B) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [commutatorElement_def]
      exact Q.mul_mem hldQ (Q.inv_mem hdQ)
    · simp only [commutatorElement_def]
      exact (QB (conjSubgroup r B)).mul_mem hldQC ((QB (conjSubgroup r B)).inv_mem hdC)
  have hBinf : B ⊓ QB (conjSubgroup r B) = ⊥ :=
    sec52a_B_inf_QB_conj_eq_bot h34 hRoot hc hs hom hr hplane
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem (hc.Rt_le_M t hr)
  have hZQC : Z ≤ QB (conjSubgroup r B) := hcC.Z_le_QB.1
  have hZBnorm : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb))
  have hZint : ((Z ⊔ B : Subgroup G) ⊓ QB (conjSubgroup r B)) = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hZQC)
    intro x hx
    obtain ⟨hxZB, hxQC⟩ := hx
    obtain ⟨b, hb, z, hz, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := B) (K := Z) hZBnorm
        (by rwa [sup_comm] at hxZB)
    have hzQC : z ∈ QB (conjSubgroup r B) := hZQC hz
    have hbQC : b ∈ QB (conjSubgroup r B) := by
      have e : b = (b * z) * z⁻¹ := by group
      rw [e]
      exact (QB (conjSubgroup r B)).mul_mem hxQC ((QB (conjSubgroup r B)).inv_mem hzQC)
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hb, hbQC⟩
    rw [Subgroup.mem_bot] at hbBot
    simpa [hbBot] using hz
  exact hZint.le ⟨hZB, hcommQC.2⟩

theorem Ctx.sec52a_centLam_omega_of_omegaNat (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vt M (LB M Q B) B Z t := by
  rcases hom with ⟨K, fK, finK, hK, hplus | hminus⟩
  · obtain ⟨m, hm, hnat⟩ := hplus
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
    exact hc.centLam_omega h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm)
      (nondegenerate_polarBilin_quadPlus m K) h3
      (addCommutantScalar_statedOmegaPlus (K := K) (m := m) hm) hnat
  · obtain ⟨m, b, c, hm, hirr, hnat⟩ := hminus
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
    exact hc.centLam_omega h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus (m := m) (b := b) (c := c) hm hirr) hnat

theorem sec52a_prod_decomp (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {m : ℕ} (hm : 2 ≤ m)
    (hVcard : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1))
    (hVQB : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m)) :
    ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
        x = a * b := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hq2 : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  have hqpos : 0 < Nat.card Z := by omega
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set C : Subgroup G := conjSubgroup r B with hCdef
  set X₁ : Subgroup G := QB B ⊓ W with hX₁def
  set X₂ : Subgroup G := QB C ⊓ W with hX₂def
  set A : Subgroup G := V ⊓ QB B with hAdef
  set D : Subgroup G := V ⊓ QB C with hDdef
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hZW : Z ≤ W := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs.notQ
  have hmn : m ≤ n := by
    have hle : Nat.card V ≤ Nat.card Q := Subgroup.card_le_of_le hVQ
    rw [hVcard, hs.width] at hle
    have := (Nat.pow_le_pow_iff_right hq2).mp hle
    omega
  have hBinf : B ⊓ QB C = ⊥ :=
    sec52a_B_inf_QB_conj_eq_bot h34 hRoot hc hs hom hr hplane
  have hIle : X₁ ⊓ X₂ ≤ A ⊓ D := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxB : x ∈ QB B := hx1.1
    have hxW : x ∈ W := hx1.2
    have hxC : x ∈ QB C := hx2.1
    have hxQ : x ∈ Q := hWQ hxW
    have hxV : x ∈ V :=
      Ctx.sec52a_centLam_omega_of_omegaNat h34 hRoot hc hs hom x ⟨hxQ, hxB⟩
        (fun l hl => sec52a_comm_mem_Z_of_mem_CN h34 hRoot hc hs hom hr hplane hl hxB hxC hxQ)
    exact ⟨⟨hxV, hxB⟩, ⟨hxV, hxC⟩⟩
  have hAV : A ≤ V := inf_le_left
  have hDV : D ≤ V := inf_le_left
  have hVconj : conjSubgroup r V = V :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr)
  have hDconj : D = conjSubgroup r A := by
    rw [hDdef, hAdef, hCdef, QB_conj, conjSubgroup_inf, hVconj]
  have hDcard : Nat.card ↥D = Nat.card Z ^ (2 * m) := by
    rw [hDconj, card_conjSubgroup, hVQB]
  have hAcard : Nat.card ↥A = Nat.card Z ^ (2 * m) := hVQB
  have hDrelV : D.relIndex V = Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := V)
    have hDVint : D ⊓ V = D := inf_of_le_left hDV
    rw [hDVint, hDcard, hVcard] at h1
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hqpos (2 * m)) ?_
    rw [h1, pow_succ']
  have hDrelVne : D.relIndex V ≠ 0 := by rw [hDrelV]; omega
  have hrel_le : D.relIndex A ≤ Nat.card Z := by
    rw [← hDrelV]
    exact Subgroup.relIndex_le_of_le_right hAV hDrelVne
  have hBA : B ≤ A := le_inf (hc.B_le_Vt ht) hc.B_le_QB
  have hB_inf_D : B ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbC : b ∈ QB C := (inf_le_right : D ≤ QB C) hb.2
    have hmem : b ∈ B ⊓ QB C := ⟨hb.1, hbC⟩
    rw [hBinf] at hmem
    exact hmem
  have hBcard : Nat.card ↥B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  haveI : IsMulCommutative ↥A :=
    ⟨⟨fun x y => Subtype.ext (hVcomm x.1 (hAV x.2) y.1 (hAV y.2))⟩⟩
  let f : ↥B → ↥A ⧸ (D.subgroupOf A) := fun b =>
    QuotientGroup.mk (s := D.subgroupOf A) (⟨(b : G), hBA b.2⟩ : ↥A)
  have hf_inj : Function.Injective f := by
    intro b1 b2 h
    have hmem : (⟨(b1 : G), hBA b1.2⟩ : ↥A) / ⟨(b2 : G), hBA b2.2⟩ ∈ D.subgroupOf A :=
      (QuotientGroup.eq_iff_div_mem).mp h
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmemB : (b1 : G) * (b2 : G)⁻¹ ∈ B := B.mul_mem b1.2 (B.inv_mem b2.2)
    have hmemD : (b1 : G) * (b2 : G)⁻¹ ∈ D := by
      simpa only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    have hbot : (b1 : G) * (b2 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hB_inf_D]
      exact ⟨hmemB, hmemD⟩
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  have hrel_ge : Nat.card Z ≤ D.relIndex A := by
    have h1 := Nat.card_le_card_of_injective f hf_inj
    have h2 : Nat.card (↥A ⧸ (D.subgroupOf A)) = D.relIndex A := rfl
    rwa [hBcard, h2] at h1
  have hrel_eq : D.relIndex A = Nat.card Z := le_antisymm hrel_le hrel_ge
  have hADcard : Nat.card ↥(A ⊓ D) = Nat.card Z ^ (2 * m - 1) := by
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := A)
    rw [hrel_eq, hAcard] at h1
    have h2 : Nat.card Z * Nat.card ↥(A ⊓ D) = Nat.card Z * Nat.card Z ^ (2 * m - 1) := by
      rw [inf_comm] at h1
      rw [h1, ← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
    exact Nat.eq_of_mul_eq_mul_left hqpos h2
  have hIupper : Nat.card ↥(X₁ ⊓ X₂) ≤ Nat.card Z ^ (2 * m - 1) :=
    (Subgroup.card_le_of_le hIle).trans_eq hADcard
  have hX₁c : Nat.card ↥X₁ = Nat.card Z ^ n := sec52a_card_QB_inf_Wt h34 hRoot hc hs hom
  have hrQ : r ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hrM
  have hrV : r ∈ Subgroup.normalizer (V : Set G) := hc.Rt_normalizes_Vt ht hr
  have hWconj : conjSubgroup r W = W := by
    rw [conjSubgroup_eq_self_iff]
    refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · exact conj_mem_Wt hrQ hrV hw
    · have h1 := conj_mem_Wt (V := V) (l := r⁻¹) (Subgroup.inv_mem _ hrQ)
        (Subgroup.inv_mem _ hrV) hw
      have e : r⁻¹ * (r * w * r⁻¹) * r⁻¹⁻¹ = w := by group
      rwa [e] at h1
  have hX₂eq : X₂ = conjSubgroup r X₁ := by
    show QB C ⊓ W = conjSubgroup r (QB B ⊓ W)
    rw [hCdef, QB_conj, conjSubgroup_inf, hWconj]
  have hX₂c : Nat.card ↥X₂ = Nat.card Z ^ n := by
    rw [hX₂eq, card_conjSubgroup, hX₁c]
  have hnorm : X₂ ≤ Subgroup.normalizer (X₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine Subgroup.commutator_le.mpr fun b hb a ha => ?_
    have hbQ : b ∈ Q := hWQ hb.2
    have haQ : a ∈ Q := hWQ ha.2
    have hcZ : ⁅b, a⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hbQ haQ
    exact Subgroup.mem_inf.mpr ⟨hc.Z_le_QB.1 hcZ, hZW hcZ⟩
  have hWmul := hc.card_Wt_mul_card_Vt t
  rw [hVcard, hs.width] at hWmul
  have hWc : Nat.card ↥W = Nat.card Z ^ (2 * n - 2 * m + 1) := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := Z)) (2 * m + 1)) ?_
    calc Nat.card ↥W * Nat.card Z ^ (2 * m + 1)
        = Nat.card Z ^ (2 * n + 2) := hWmul
      _ = Nat.card Z ^ (2 * n - 2 * m + 1) * Nat.card Z ^ (2 * m + 1) := by
          rw [← pow_add]; congr 1; omega
  have hsupmul := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hX₁c, hX₂c] at hsupmul
  have hge : Nat.card Z ^ (2 * n - 2 * m + 1) ≤ Nat.card ↥(X₁ ⊔ X₂) := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hqpos (2 * m - 1))
    have hpow : Nat.card Z ^ (2 * n - 2 * m + 1) * Nat.card Z ^ (2 * m - 1) =
        Nat.card Z ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have hmid : Nat.card Z ^ n * Nat.card Z ^ n =
        Nat.card ↥(X₁ ⊔ X₂) * Nat.card ↥(X₁ ⊓ X₂) := hsupmul.symm
    calc Nat.card Z ^ (2 * n) = Nat.card Z ^ n * Nat.card Z ^ n := by
          rw [← pow_add]; congr 1; omega
      _ = Nat.card ↥(X₁ ⊔ X₂) * Nat.card ↥(X₁ ⊓ X₂) := hmid
      _ ≤ Nat.card ↥(X₁ ⊔ X₂) * Nat.card Z ^ (2 * m - 1) :=
          Nat.mul_le_mul_left _ hIupper
  have hjoinW : X₁ ⊔ X₂ = W := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_right inf_le_right) ?_
    rw [hWc]
    exact hge
  intro x hx
  have hxL : x ∈ X₂ ⊔ X₁ := by
    rw [sup_comm]
    exact hjoinW.symm ▸ hx
  obtain ⟨b, hb, a, ha, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hxL
  refine ⟨b * a * b⁻¹, ?_, b, hb, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hnorm hb) a).mp ha
  · rw [← hab]; group

theorem sec52a_mem_V_of_mem_QB_QB (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {x : G} (hxB : x ∈ QB B) (hxC : x ∈ QB (conjSubgroup r B)) (hxQ : x ∈ Q) :
    x ∈ Vt M (LB M Q B) B Z t :=
  Ctx.sec52a_centLam_omega_of_omegaNat h34 hRoot hc hs hom x ⟨hxQ, hxB⟩
    (fun l hl => sec52a_comm_mem_Z_of_mem_CN h34 hRoot hc hs hom hr hplane hl hxB hxC hxQ)

theorem sec52a_hboxB (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ⁅QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q B ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
  have ht : t ∈ LB M Q B := hs.mem
  have hxQ : x ∈ Q := (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hx.2
  have hlM : l ∈ M := hc.LB_le_M hl.1
  have hlxB : ⁅l, x⁆ ∈ QB B :=
    comm_LB_Wt_mem_QB hc (hc.B_le_Vt ht) hl.1 hx.2
  have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hl.2
  have hldQC : l * x * l⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
    (Subgroup.mem_normalizer_iff.mp hnorm x).mp ⟨hxQ, hx.1⟩
  have hlxQC : ⁅l, x⁆ ∈ QB (conjSubgroup r B) := by
    simpa only [commutatorElement_def] using
      (QB (conjSubgroup r B)).mul_mem hldQC.2 ((QB (conjSubgroup r B)).inv_mem hx.1)
  have hlxQ : ⁅l, x⁆ ∈ Q := by
    have h1 : l * x * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hxQ
    simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hxQ)
  have hlxV : ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t :=
    sec52a_mem_V_of_mem_QB_QB h34 hRoot hc hs hom hr hplane hlxB hlxQC hlxQ
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem hlxV

theorem sec52a_hboxC (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hom : OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ⁅QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup r B ≤ conjSubgroup r B ⊔ Z).trans
      (hc.conj_Rt_le_Vt ht hr)
  have hxQ : x ∈ Q := (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hx.2
  have hlxC : ⁅l, x⁆ ∈ QB (conjSubgroup r B) :=
    comm_LB_Wt_mem_QB hcC hCV hl.1 hx.2
  have hnormB := sec52a_QB_inf_normalizes_of_mem_CN hc hs (r := 1)
    (Subgroup.one_mem (Rt M (LB M Q B) t)) hl.2
  have hnormB' : l ∈ Subgroup.normalizer ((Q ⊓ QB B : Subgroup G) : Set G) := by
    simpa [conjSubgroup_one] using hnormB
  have hldQB : l * x * l⁻¹ ∈ Q ⊓ QB B :=
    (Subgroup.mem_normalizer_iff.mp hnormB' x).mp ⟨hxQ, hx.1⟩
  have hlxB : ⁅l, x⁆ ∈ QB B := by
    simpa only [commutatorElement_def] using
      (QB B).mul_mem hldQB.2 ((QB B).inv_mem hx.1)
  have hlxQ : ⁅l, x⁆ ∈ Q := by
    have hlM : l ∈ M := hcC.LB_le_M hl.1
    have h1 : l * x * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hxQ
    simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hxQ)
  have hlxV : ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t :=
    sec52a_mem_V_of_mem_QB_QB h34 hRoot hc hs hom hr hplane hlxB hlxC hlxQ
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem hlxV

theorem stroth52a_of_inputs (h51 : Stroth51Statement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) : Stroth52aStatement := by
  intro G _ _ M Q Z B hc n t hs hom r hr hplane C N V W hC hN hV hW
  subst hC hN hV hW
  obtain ⟨m, hm, hVcard, hVQB⟩ :=
    Ctx.sec52a_card_Vt_inf_QB_of_omegaNat h34 hRoot hc hs hom
  have hprod := sec52a_prod_decomp h34 hRoot hc hs hom hr hplane hm hVcard hVQB
  refine ⟨hprod, ?_⟩
  have hcomm := sec52a_comm_of_51 h51 hc hs hom hr hplane hprod
    (sec52a_hboxB h34 hRoot hc hs hom hr hplane)
    (sec52a_hboxC h34 hRoot hc hs hom hr hplane)
  intro s hsN x hxW
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem
    ((Subgroup.commutator_le.mp hcomm) x hxW s hsN)

section Certs

theorem stroth52aStatement_holds : Stroth52aStatement :=
  stroth52a_of_inputs stroth51Statement_unconditional stroth34Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional)

end Certs

end CFSG.RankThree.GF2n.Stroth80
