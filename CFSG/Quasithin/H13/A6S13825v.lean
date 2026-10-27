module

public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Quasithin.H13.A6S1372L76
public import CFSG.Quasithin.H13.A6S13825p
public import CFSG.Quasithin.H13.A6S13825u

public section

namespace CFSG.Quasithin.H13.A6.L13825

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

theorem nonempty_map_mulEquiv {A B₁ B₂ : Type*} [Group A] [Group B₁] [Group B₂] (φ₁ : A →* B₁)
    (φ₂ : A →* B₂) (h : ∀ x, φ₁ x = 1 ↔ φ₂ x = 1) (X : Subgroup A) :
    Nonempty (↥(X.map φ₁) ≃* ↥(X.map φ₂)) := by
  set ψ₁ := φ₁.comp X.subtype
  set ψ₂ := φ₂.comp X.subtype
  have hker : ψ₁.ker = ψ₂.ker := by
    ext x
    simp only [MonoidHom.mem_ker, ψ₁, ψ₂, MonoidHom.comp_apply]
    exact h _
  have hr₁ : ψ₁.range = X.map φ₁ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hr₂ : ψ₂.range = X.map φ₂ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hr₁).symm.trans
    ((QuotientGroup.quotientKerEquivRange ψ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.quotientKerEquivRange ψ₂).trans (MulEquiv.subgroupCongr hr₂))))⟩

theorem fixV_eq_bot_of_natSL {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}
    (hn : 2 ≤ n) (h : BinaryNaturalSL H ⊤ ⊥ n 1) : fixV H = ⊥ := by
  classical
  obtain ⟨F, _, _, π, E, -, -, hE⟩ := G64.BinaryNaturalSL.exists_equiv_vec h
  refine eq_bot_iff.mpr fun v hv => ?_
  have hx : Multiplicative.toAdd (E v) = 0 := by
    funext j
    obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ j := by
      by_cases hj : (j : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hj; simp at hj⟩
      · exact ⟨⟨0, by omega⟩, fun h => hj (by rw [← h])⟩
    let γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) :=
      specialLinearGroupEquivStatedSL n F (Matrix.SpecialLinearGroup.transvection hij 1)
    have h1 := hE γ v
    rw [hv _ (π γ).2] at h1
    have h2 := congrFun h1 i
    rw [show ((γ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (1 : Matrix (Fin n) (Fin n) F) + Matrix.single i j 1 from rfl, Matrix.add_mulVec,
      Matrix.one_mulVec] at h2
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.single_apply, true_and,
      one_mul, ite_mul, zero_mul] at h2
    simpa using h2
  have : E v = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hx]
    rfl
  rw [Subgroup.mem_bot]
  exact E.injective (this.trans (map_one E).symm)

theorem span_eq_top_of_commV {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)} {a : MulAut W}
    (h : commV (conjClosure (Subgroup.zpowers a) X) = ⊤) :
    (⨆ (g : MulAut W) (_ : g ∈ X), (commV (Subgroup.zpowers a)).map g.toMonoidHom) = ⊤ := by
  set M := ⨆ (g : MulAut W) (_ : g ∈ X), (commV (Subgroup.zpowers a)).map g.toMonoidHom with hM
  let Y : Subgroup (MulAut W) :=
    { carrier := {x | ∀ v, x v * v⁻¹ ∈ M}
      one_mem' := fun v => by
        rw [MulAut.one_apply, mul_inv_cancel]
        exact M.one_mem
      mul_mem' := fun {x y} hx hy v => by
        have e : (x * y) v * v⁻¹ = (x (y v) * (y v)⁻¹) * (y v * v⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact M.mul_mem (hx _) (hy v)
      inv_mem' := fun {x} hx v => by
        have e : x⁻¹ v * v⁻¹ = (x (x⁻¹ v) * (x⁻¹ v)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [e]
        exact M.inv_mem (hx _) }
  have hle : conjClosure (Subgroup.zpowers a) X ≤ Y := by
    refine conjClosure_le fun g hg z hz => ?_
    intro v
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have e : (g * a ^ k * g⁻¹) v * v⁻¹ = g ((a ^ k) (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [e]
    exact (le_iSup₂ (f := fun (g : MulAut W) (_ : g ∈ X) =>
      (commV (Subgroup.zpowers a)).map g.toMonoidHom) g hg)
      ⟨_, G6.mem_commV_of_mem (Subgroup.zpow_mem_zpowers a k) _, rfl⟩
  rw [eq_top_iff, ← h]
  exact G6.commV_le_iff.2 fun x hx v => hle hx v

theorem sec_sq_eq_one {G : Type} [Group G] {U C : Subgroup G} [IsMulCommutative ↥U]
    (hU : ∀ u ∈ U, u ^ 2 = 1) (w : Sec (⊤ : Subgroup ↥U) (C.subgroupOf U)) : w ^ 2 = 1 := by
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (C.subgroupOf U) w
  rw [← map_pow]
  have hu : u ^ 2 = 1 := Subtype.ext (by simpa using hU u u.2)
  rw [hu, map_one]

section Act

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem commV_eq_top_of_commutator {K : Subgroup G} (hKH : K ≤ H)
    (h : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H) :
    commV ((K.subgroupOf H).map (sigmaH hH)) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  obtain ⟨⟨u, hu⟩, rfl⟩ :=
    InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) w
  set X : Subgroup G := ((commV ((K.subgroupOf H).map (sigmaH hH))).comap
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).map
      (conjClosure S.V3 H).subtype with hX
  have hle : ⁅conjClosure S.V3 H, K⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx k hk
    have hxk : ⁅x, k⁆ ∈ conjClosure S.V3 H := h ▸ Subgroup.commutator_mem_commutator hx hk
    refine ⟨⟨⁅x, k⁆, hxk⟩, ?_, rfl⟩
    have e : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨⁅x, k⁆, hxk⟩ =
        (sigmaH hH ⟨k, hKH hk⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨x, hx⟩) *
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨x, hx⟩)⁻¹)⁻¹ := by
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, Setup.rho_apply_coe, commutatorElement_def]
      group
    rw [SetLike.mem_coe, Subgroup.mem_comap, e]
    exact (commV _).inv_mem (G6.mem_commV_of_mem
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)) _)
  rw [h] at hle
  obtain ⟨y, hy, hyu⟩ := hle hu
  have : y = ⟨u, hu⟩ := Subtype.ext hyu
  rw [← this]
  exact hy

theorem hyp61_sigmaH (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    (hsq : CFSG.SectionRank.IsSQTKCat ↥H)
    (hW2 : ∀ w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), w ^ 2 = 1)
    {a : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))} (haH : a ∈ (sigmaH hH).range)
    (ha1 : a ≠ 1)
    {w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))}
    (hw : IsTransvectionWith a w)
    (hspan : commV (conjClosure (Subgroup.zpowers a) (sigmaH hH).range) = ⊤) :
    G64.Hyp61 (sigmaH hH).range a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, haH, ha1, ?_, ?_, span_eq_top_of_commV hspan⟩
  ·
    refine A6Tv.range_o2_eq_bot hF _ (sigmaH_eq_one_iff hH hF) _
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).2 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  ·
    exact ⟨↥H, inferInstance, inferInstance, (sigmaH hH).ker, inferInstance, hsq,
      ⟨(QuotientGroup.quotientKerEquivRange (sigmaH hH)).symm⟩⟩
  · rw [sq]
    exact B1.tv_sq hW2 hw ha1
  · rw [card_commV_of_transvectionWith hW2 hw ha1]
    norm_num

include hH in
theorem natL4_of (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    (h : BinaryNaturalSL (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ 4 1) : S.NatL4 H := by
  have hGH : autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) = (sigmaH hH).range := by
    rw [autSec_eq_map hH le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [hGH] at h
  obtain ⟨π, hπ⟩ := G64.BinaryNaturalSL.exists_zmod h
  have hinj := G64.natSL_injective hπ
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.exists_natMap hπ
  set ψ := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm with hψ
  have hπψ : ∀ y, π (ψ y) = y := fun y =>
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).apply_symm_apply y
  have hψπ : ∀ γ, ψ (π γ) = γ := fun γ =>
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm_apply_apply γ
  refine ⟨(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)).subtype.comp
    (ψ.toMonoidHom.comp (sigmaH hH).rangeRestrict), fun g => ?_, fun x => ?_,
    f.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))), fun y => ?_,
    fun u => ?_, fun x u v huv => ?_⟩
  ·
    obtain ⟨x, hx⟩ := (sigmaH hH).rangeRestrict_surjective (π ⟨g, G64.mem_statedSL_zmod g⟩)
    refine ⟨x, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx, hψπ, Subgroup.coe_subtype]
  ·
    rw [← sigmaH_eq_one_iff hH hF]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]
    rw [Subtype.ext_iff, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
  ·
    obtain ⟨⟨w, -⟩, rfl⟩ := hfs y
    obtain ⟨u, rfl⟩ :=
      InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) w
    exact ⟨u, rfl⟩
  ·
    rw [← A6Mod.secMk_eq_one_iff u]
    show f ⟨_, trivial⟩ = 1 ↔ _
    rw [hfk]
    exact Subgroup.mem_bot
  ·
    set γ := ψ ((sigmaH hH).rangeRestrict x) with hγ
    have hπγ : ((π γ : ↥(sigmaH hH).range) : MulAut _) = sigmaH hH x := by
      rw [hγ, hπψ]
      rfl
    have hsec : ((π γ : ↥(sigmaH hH).range) : MulAut _)
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) v := by
      rw [hπγ, A6Mod.secAct_secMk]
      congr 1
      exact Subtype.ext (by rw [Setup.rho_apply_coe, huv, Subgroup.coe_inv])
    have h1 := hfe γ ⟨InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u,
      trivial⟩ trivial
    show Multiplicative.toAdd
      (f ⟨InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) v, trivial⟩) = _
    have h2 : (⟨InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) v, trivial⟩ :
        ↥(⊤ : Subgroup _)) = ⟨((π γ : ↥(sigmaH hH).range) : MulAut _)
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u), trivial⟩ :=
      Subtype.ext hsec.symm
    rw [h2, h1]
    rfl

end Act

end CFSG.Quasithin.H13.A6.L13825

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

open L13825 in
theorem lem13825One_of (h21 : Lem13821) (h16 : Lem13816) (h1376 : Lem1376Full)
    (h64 : G64.LemmaG64) : Lem13825One := by
  intro G _ _ T L V S hS H hH K hK n hn3 hn5 hn htr
  obtain ⟨h, hh, htr⟩ := htr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hab := isElemAbelian_UH hS hH
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hab.1
  obtain ⟨h1, -, h3, -, -, -, -, -⟩ := h1376 G T L V S hS.hNS hS.hNU H hH hab K hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have h21' := h21 G T L V S hS H hH K hK
  have hKT : K ⊔ T = H := h21'.2.2.1.1
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hker : ∀ x : ↥H, sigmaH hH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := sigmaH_eq_one_iff hH hF
  have hGKeq : autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) = (K.subgroupOf H).map (sigmaH hH) :=
    autSec_eq_map hH hKH
  rw [hGKeq] at h1 h3
  set σ := sigmaH hH with hσ
  set GK := (K.subgroupOf H).map σ with hGK
  set GT := (T.subgroupOf H).map σ with hGT
  obtain ⟨e₀⟩ := FLc.nonempty_equiv_SLt_of_isPSL hn
  obtain ⟨e₁⟩ := nonempty_map_mulEquiv (S1549C.starHom hF) σ
    (fun x => by rw [S1549C.starHom_eq_one_iff hF, hker]) (K.subgroupOf H)
  let e : ↥GK ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    e₁.symm.trans ((MulEquiv.subgroupCongr (S.kst_eq hF hKH)).symm.trans e₀)
  have hKH' : GK ≤ σ.range := Subgroup.map_le_range σ _
  have hKn : σ.range ≤ Subgroup.normalizer (GK : Set _) := by
    have h0 := L32Case.map_le_normalizer_map hKnH σ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h0
  have hHKT : σ.range ≤ GK ⊔ GT := by
    have e1 : (⊤ : Subgroup ↥H) = K.subgroupOf H ⊔ T.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, hKT, Subgroup.subgroupOf_self]
    rw [MonoidHom.range_eq_map, e1, Subgroup.map_sup]
  have hTH' : GT ≤ σ.range := Subgroup.map_le_range σ _
  have hT2 : IsPGroup 2 ↥T := (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH).2.1
  have hTp : IsPGroup 2 ↥GT := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  have hZ : ∀ k ∈ GK, (∀ k' ∈ GK, k * k' = k' * k) → k = 1 := by
    intro k hk hcomm
    have hc : e ⟨k, hk⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨⟨y', hy'⟩, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm y' hy').symm
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      G11.P4GL.scalars_trivial, Subgroup.mem_bot] at hc
    have := congrArg Subtype.val (e.injective (hc.trans (map_one e).symm))
    simpa using this
  have hC := inf_centralizer_eq_bot hKn hHKT hTH' hTp hZ (A6Tv.range_o2_eq_bot hF σ hker)
  obtain ⟨ha1, w, hw⟩ := exists_transvectionWith_sigmaH hH hh htr
  have hW2 := sec_sq_eq_one (C := fsuV1 T V) hab.2
  have htr2 := card_commV_of_transvectionWith hW2 hw ha1
  have haH : σ ⟨h, hh⟩ ∈ σ.range := ⟨_, rfl⟩
  have haK : ∃ k ∈ GK, σ ⟨h, hh⟩ * k ≠ k * σ ⟨h, hh⟩ := by
    by_contra hcon
    push Not at hcon
    apply ha1
    have hmem : σ ⟨h, hh⟩ ∈ σ.range ⊓ Subgroup.centralizer (GK : Set _) :=
      ⟨haH, Subgroup.mem_centralizer_iff.mpr fun k hk => (hcon k hk).symm⟩
    rw [hC] at hmem
    exact hmem
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hn3
  have hcomm : commV GK = ⊤ := commV_eq_top_of_commutator hH hKH h21'.2.2.2
  have hspan : commV (conjClosure (Subgroup.zpowers (σ ⟨h, hh⟩)) σ.range) = ⊤ :=
    eq_top_iff.mpr (hcomm ▸ G6.commV_mono
      (le_classClosure_of_simple haH hKH' hKn e.isSimpleGroup haK))
  have hsq : CFSG.SectionRank.IsSQTKCat ↥H := by
    have : IsSimpleGroup G := S.h13.simple
    exact (QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1 H hH.1.2
  have hyp := hyp61_sigmaH hH hF hsq hW2 haH ha1 hw hspan
  rcases g64_cases h64 hW2 hyp htr2 hKH' hKn hn3 hn5 e hcomm haK with ⟨-, hnat⟩ | ⟨rfl, hsym⟩
  ·
    have hfix : fixV GK = ⊥ := fixV_eq_bot_of_natSL (by omega) hnat
    rw [hcomm, hfix, bot_inf_eq] at h1
    obtain ⟨hn4, hhat, hnatH⟩ := h1 n (by omega) hnat
    exact ⟨hn4, hhat, natL4_of hH hF hnatH⟩
  ·
    exfalso
    rw [hcomm, inf_top_eq] at h3
    obtain ⟨-, -, -, h6 | h7⟩ := h3 8 (alternatingNatural_of_sym8 hKH' hsym)
    · exact absurd h6.1 (by norm_num)
    · exact absurd h7.1 (by norm_num)

end CFSG.Quasithin.H13.A6
