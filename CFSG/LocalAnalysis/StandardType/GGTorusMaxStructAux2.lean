module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStructAux

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.CentralCover CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo TableBExcTwoFusion
  TableBExcTwoTB Multiplicative

theorem tmStruct_concrete
    {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (F : TableBExcTwo.OrthFrame τ d) (hd : d + 1 = τ.rank)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hK : Nat.card K = 2)
    (hcent : Subgroup.centralizer ((TableBExcTwoTB.tE K F).range :
        Set (CFSG.Blueprint.Chevalley.adjointGroup τ K)) =
      (TableBExcTwoTB.tE K F).range) :
    ∃ (π : (Subgroup.normalizer ((TableBExcTwoTB.tE K F).range :
          Set (CFSG.Blueprint.Chevalley.adjointGroup τ K))) →* WeylGroup τ)
      (φ : (TableBExcTwoTB.tE K F).range ≃* Multiplicative (Fin τ.rank → ZMod 3)),
      Function.Surjective π ∧
      π.ker = (TableBExcTwoTB.tE K F).range.subgroupOf
        (Subgroup.normalizer ((TableBExcTwoTB.tE K F).range :
          Set (CFSG.Blueprint.Chevalley.adjointGroup τ K))) ∧
      ∀ (g : Subgroup.normalizer ((TableBExcTwoTB.tE K F).range :
            Set (CFSG.Blueprint.Chevalley.adjointGroup τ K)))
        (e : (TableBExcTwoTB.tE K F).range),
        φ ((TableBExcTwoTB.tE K F).range.normalizerMonoidHom g e) =
          ExcWeylOuter.torusMulAut τ 3 (π g) (φ e) := by
  classical
  set T : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ K) := (TableBExcTwoTB.tE K F).range with hT
  set N : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ K) :=
    Subgroup.normalizer (T : Set (CFSG.Blueprint.Chevalley.adjointGroup τ K)) with hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := FiniteField.Extension K 2 2 with hL
  have h3dvd : 3 ∣ Nat.card L - 1 := TableBExcTwoFusion.three_dvd_natCard_ext_sub_one hK
  have hV : Nat.card (torusPow τ L 3) = 3 ^ τ.rank :=
    tmStruct_card_torusPow_of_E7_E8 hτ hK
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3dvd
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  set G : CFSG.Blueprint.Chevalley.adjointGroup τ L := TableBExcTwoFusion.langElt F hωo with hG
  set ι : CFSG.Blueprint.Chevalley.adjointGroup τ K →*
      CFSG.Blueprint.Chevalley.adjointGroup τ L :=
    TableBExcTwo.adjointMap τ (algebraMap K L) with hι
  have hιinj : Function.Injective ι := TableBExcTwo.adjointMap_injective _
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow τ L 3 := by
    rw [hT]
    exact TableBExcTwoTB.langElt_conj_frame_eq_torusPow hτ F hd hV hωo
  let Ψ : T →* CFSG.Blueprint.Chevalley.adjointGroup τ L :=
    (MulAut.conj G⁻¹).toMonoidHom.comp (ι.comp T.subtype)
  have hΨ_coe : ∀ y : T, Ψ y = G⁻¹ * ι (y : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G := by
    intro y
    simp [Ψ, MulAut.conj_apply]
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hιinj
    have h : G⁻¹ * ι (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G =
        G⁻¹ * ι (y : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G := by
      rw [← hΨ_coe x, ← hΨ_coe y]
      exact hxy
    calc ι (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) =
          G * (G⁻¹ * ι (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G) * G⁻¹ := by group
      _ = G * (G⁻¹ * ι (y : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G) * G⁻¹ := by rw [h]
      _ = ι (y : CFSG.Blueprint.Chevalley.adjointGroup τ K) := by group
  have hΨrange : Ψ.range = torusPow τ L 3 := by
    rw [← hTV]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι (y : CFSG.Blueprint.Chevalley.adjointGroup τ K), ⟨(y : CFSG.Blueprint.Chevalley.adjointGroup τ K), y.2, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eΨ : T ≃* torusPow τ L 3 :=
    (MonoidHom.ofInjective hΨinj).trans (MulEquiv.subgroupCongr hΨrange)
  have hΨ_apply : ∀ y : T, ((eΨ y : torusPow τ L 3) :
      CFSG.Blueprint.Chevalley.adjointGroup τ L) = Ψ y := by
    intro y
    simp only [eΨ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  have hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L := full_of_E7_E8 hτ
  let eMhom : Multiplicative (Fin τ.rank → ZMod 3) →*
      CFSG.Blueprint.Chevalley.adjointGroup τ L :=
    ExcFrames.frameHom hfull ω hω3 (1 : CFSG.Blueprint.Chevalley.adjointGroup τ L)
  have heMhom_coe : ∀ s : Fin τ.rank → ZMod 3,
      (eMhom (Multiplicative.ofAdd s) : ModGL τ L) = ExcFrames.frameDiag ω hω3 s := by
    intro s
    rw [ExcFrames.coe_frameHom]
    simp
  have heMhom_inj : Function.Injective eMhom := by
    intro x y hxy
    have h1 : ExcFrames.frameDiag ω hω3 (Multiplicative.toAdd x) =
        ExcFrames.frameDiag ω hω3 (Multiplicative.toAdd y) := by
      rw [← heMhom_coe (Multiplicative.toAdd x), ← heMhom_coe (Multiplicative.toAdd y)]
      exact congrArg (fun z : CFSG.Blueprint.Chevalley.adjointGroup τ L => (z : ModGL τ L)) hxy
    exact Multiplicative.toAdd.injective
      (ExcFrames.frameDiag_injective (τ := τ) (ζ := ω) hωo hω3
        (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) (by norm_num)) h1)
  have heMhom_range : eMhom.range = torusPow τ L 3 := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      rw [show eMhom x = eMhom (Multiplicative.ofAdd (Multiplicative.toAdd x)) from by
        rw [ofAdd_toAdd]]
      exact ExcFrames.mem_torusPow_iff_coe.mpr (by
        rw [heMhom_coe]
        exact ExcFrames.frameDiag_mem hfull ω hω3 _)
    · intro hv
      have hsp : (v : ModGL τ L) ∈ ExcFrames.splitPow τ L 3 :=
        ExcFrames.mem_torusPow_iff_coe.mp hv
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem (τ := τ) hωo hω3
        (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) (by norm_num)) hsp
      exact ⟨Multiplicative.ofAdd s, by apply Subtype.ext; rw [heMhom_coe]; exact hs⟩
  let eM : Multiplicative (Fin τ.rank → ZMod 3) ≃* torusPow τ L 3 :=
    (MonoidHom.ofInjective heMhom_inj).trans (MulEquiv.subgroupCongr heMhom_range)
  have eM_coe : ∀ s : Fin τ.rank → ZMod 3,
      ((eM (Multiplicative.ofAdd s) : torusPow τ L 3) : ModGL τ L) =
        ExcFrames.frameDiag ω hω3 s := by
    intro s
    simp only [eM, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    exact heMhom_coe s
  let φ : T ≃* Multiplicative (Fin τ.rank → ZMod 3) := eΨ.trans eM.symm
  let Θ : WeylGroup τ →* MulAut T :=
    (MulAut.congr φ.symm).toMonoidHom.comp (ExcWeylOuter.torusMulAut τ 3)
  have hΘ_apply : ∀ (w : WeylGroup τ) (x : T),
      φ (Θ w x) = ExcWeylOuter.torusMulAut τ 3 w (φ x) := by
    intro w x
    simp only [Θ, MonoidHom.comp_apply, MulAut.congr_apply]
    simp
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h2 : MulAut.congr φ (Θ w) = ExcWeylOuter.torusMulAut τ 3 w := by
      simp only [Θ, MonoidHom.comp_apply]
      exact tmStruct_congr_symm φ.symm (ExcWeylOuter.torusMulAut τ 3 w)
    rw [hw, map_one] at h2
    have h3 : ExcWeylOuter.torusMulAut τ 3 w = 1 := h2.symm
    exact ExcWeylOuter.torusMulAut_injective (τ := τ) (p := 3) (by norm_num)
      (by simpa using h3)
  have hcanon : ∀ w : WeylGroup τ,
      (⟨canonicalRep (coxeterSystem τ) L w,
        CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
          CFSG.Blueprint.Chevalley.adjointGroup τ L) ∈
        Subgroup.normalizer ((torusPow τ L 3 : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ L)) :
          Set (CFSG.Blueprint.Chevalley.adjointGroup τ L)) :=
    fun w => tmStruct_canonicalRep_mem_normalizer_torusPow (L := L) w
  let θ' : WeylGroup τ → MulAut (torusPow τ L 3) := fun w =>
    (torusPow τ L 3).normalizerMonoidHom
      ⟨⟨canonicalRep (coxeterSystem τ) L w,
        CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩, hcanon w⟩
  have hθ'_apply : ∀ (w : WeylGroup τ) (v : torusPow τ L 3),
      ((θ' w v : torusPow τ L 3) : CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L) *
          (v : CFSG.Blueprint.Chevalley.adjointGroup τ L) *
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L)⁻¹ :=
    fun w v => CFSG.StandardType.normalizerMonoidHom_apply_coe (hcanon w) v
  have hkey2 : ∀ (w : WeylGroup τ) (v : torusPow τ L 3),
      eM (ExcWeylOuter.torusMulAut τ 3 w (eM.symm v)) = θ' w v := by
    intro w v
    set s : Fin τ.rank → ZMod 3 := Multiplicative.toAdd (eM.symm v) with hs
    have hof : eM.symm v = Multiplicative.ofAdd s := (ofAdd_toAdd _).symm
    have hv : v = eM (Multiplicative.ofAdd s) := by
      rw [← hof]
      exact (MulEquiv.apply_symm_apply eM v).symm
    have hcoe : (v : ModGL τ L) = ExcFrames.frameDiag ω hω3 s := by
      rw [hv, eM_coe]
    apply Subtype.ext
    apply Subtype.ext
    rw [hof, ExcWeylOuter.torusMulAut_apply, eM_coe]
    rw [show ((θ' w v : torusPow τ L 3) : ModGL τ L) =
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L) *
          (v : CFSG.Blueprint.Chevalley.adjointGroup τ L) *
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L)⁻¹ from
      congrArg (fun z : CFSG.Blueprint.Chevalley.adjointGroup τ L => (z : ModGL τ L))
        (hθ'_apply w v)]
    rw [hcoe]
    exact (ExcFrames.canonicalRep_conj_frameDiag (τ := τ) ω hω3 w s).symm
  have hΘeΨ : ∀ (w : WeylGroup τ) (x : T), eΨ (Θ w x) = θ' w (eΨ x) := by
    intro w x
    change eΨ ((MulAut.congr φ.symm (ExcWeylOuter.torusMulAut τ 3 w)) x) = _
    rw [MulAut.congr_apply]
    have hφsymm : ∀ z : Multiplicative (Fin τ.rank → ZMod 3),
        eΨ (φ.symm z) = eM z := by
      intro z
      change eΨ ((eM.trans eΨ.symm) z) = eM z
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm, hφsymm]
    rw [show φ x = eM.symm (eΨ x) from rfl]
    exact hkey2 w (eΨ x)
  have hmemT : ∀ x : CFSG.Blueprint.Chevalley.adjointGroup τ K,
      x ∈ T ↔ G⁻¹ * ι x * G ∈ torusPow τ L 3 := by
    intro x
    constructor
    · intro hx
      rw [← hTV]
      exact ⟨ι x, ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply]⟩
    · intro hx
      rw [← hTV] at hx
      obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hx
      have h1 : G⁻¹ * ι y * G = G⁻¹ * ι x * G := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyx
        exact hyx
      have h2 : ι y = ι x := mul_left_cancel (mul_right_cancel h1)
      have h3 : y = x := hιinj h2
      exact h3 ▸ hy
  have hint : ∀ (g : N) (y : T),
      ((eΨ (⟨(g : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
          (y : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
          (g : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹,
          (Subgroup.mem_normalizer_iff.mp g.2 (y : CFSG.Blueprint.Chevalley.adjointGroup τ K)).mp y.2⟩ : T) :
        CFSG.Blueprint.Chevalley.adjointGroup τ L)) =
        (G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G) * (eΨ y) *
          (G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G)⁻¹ := by
    intro g y
    simp only [hΨ_apply, hΨ_coe, map_mul, map_inv]
    group
  have hdescent : ∀ w : WeylGroup τ, ∃ g : N, T.normalizerMonoidHom g = Θ w := by
    intro w
    set n : CFSG.Blueprint.Chevalley.adjointGroup τ L :=
      ⟨canonicalRep (coxeterSystem τ) L w,
        CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩
      with hn
    have hmono : (n : ModGL τ L) ∈ monomialSubgroup τ L :=
      CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup L w
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : CFSG.Blueprint.Chevalley.adjointGroup τ K, ι m₀ = G * n * G⁻¹ :=
      exists_adjointMap_eq_of_frob hτ
        (adjointMap_frob_conj_langElt hK F hw hsymm hdet hV hωo hmono)
    have hconj : ∀ x : CFSG.Blueprint.Chevalley.adjointGroup τ K,
        G⁻¹ * ι (m₀ * x * m₀⁻¹) * G = n * (G⁻¹ * ι x * G) * n⁻¹ := by
      intro x
      rw [map_mul, map_mul, map_inv, hm₀]
      group
    have hm₀N : m₀ ∈ N := by
      rw [hN, Subgroup.mem_normalizer_iff]
      intro x
      rw [hmemT x, hmemT (m₀ * x * m₀⁻¹), hconj x]
      exact Subgroup.mem_normalizer_iff.mp (hcanon w) _
    obtain ⟨g, hg⟩ : ∃ g : N, (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) = m₀ :=
      ⟨⟨m₀, hm₀N⟩, rfl⟩
    refine ⟨g, ?_⟩
    apply MulEquiv.ext
    intro x
    apply eΨ.injective
    apply Subtype.ext
    have hx_eq : (T.normalizerMonoidHom g) x =
        ⟨(g : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (g : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹,
          (Subgroup.mem_normalizer_iff.mp g.2
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K)).mp x.2⟩ :=
      Subtype.ext (CFSG.StandardType.normalizerMonoidHom_apply_coe g.2 x)
    have hL : ((eΨ ((T.normalizerMonoidHom g) x) : torusPow τ L 3) :
        CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        (G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G) * (eΨ x) *
          (G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G)⁻¹ := by
      rw [hx_eq]
      exact hint g x
    have ha : G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G = n := by
      rw [hg, hm₀]
      group
    rw [hL, ha, hΘeΨ w x]
    exact (hθ'_apply w (eΨ x)).symm
  have key : ∀ g : N, ∃ w : WeylGroup τ, T.normalizerMonoidHom g = Θ w := by
    intro g
    set a : CFSG.Blueprint.Chevalley.adjointGroup τ L :=
      G⁻¹ * ι (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G with ha_def
    have ha : ∀ x : CFSG.Blueprint.Chevalley.adjointGroup τ L,
        x ∈ torusPow τ L 3 ↔ a * x * a⁻¹ ∈ torusPow τ L 3 := by
      intro x
      constructor
      · intro hx
        have h := hint g (eΨ.symm ⟨x, hx⟩)
        have hx' : (eΨ (eΨ.symm ⟨x, hx⟩) : CFSG.Blueprint.Chevalley.adjointGroup τ L) = x := by
          rw [MulEquiv.apply_symm_apply]
        rw [hx'] at h
        rw [← h]
        exact (eΨ _).2
      · intro hx
        have h := hint g⁻¹ (eΨ.symm ⟨a * x * a⁻¹, hx⟩)
        have hcoef : G⁻¹ * ι ((g⁻¹ : N) : CFSG.Blueprint.Chevalley.adjointGroup τ K) * G = a⁻¹ := by
          rw [ha_def]
          simp only [Subgroup.coe_inv, map_inv]
          group
        rw [hcoef, MulEquiv.apply_symm_apply] at h
        have hx_eq : x = (eΨ (⟨((g⁻¹ : N) : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (eΨ.symm ⟨a * x * a⁻¹, hx⟩) *
            ((g⁻¹ : N) : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (g⁻¹).2
              (eΨ.symm ⟨a * x * a⁻¹, hx⟩)).mp
              (eΨ.symm ⟨a * x * a⁻¹, hx⟩).2⟩ : T) :
          CFSG.Blueprint.Chevalley.adjointGroup τ L) := by
          rw [h]; group
        rw [hx_eq]
        exact (eΨ _).2
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes (p := 3) ha
    refine ⟨w, ?_⟩
    apply MulEquiv.ext
    intro x
    apply eΨ.injective
    apply Subtype.ext
    have hL : ((eΨ ((T.normalizerMonoidHom g) x) : torusPow τ L 3) :
        CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        a * (eΨ x) * a⁻¹ := by
      have hx_eq : (T.normalizerMonoidHom g) x =
          ⟨(g : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
              (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
              (g : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹,
            (Subgroup.mem_normalizer_iff.mp g.2
              (x : CFSG.Blueprint.Chevalley.adjointGroup τ K)).mp x.2⟩ :=
        Subtype.ext (CFSG.StandardType.normalizerMonoidHom_apply_coe g.2 x)
      rw [hx_eq]
      exact hint g x
    rw [hL]
    have h3 : eΨ (Θ w x) = θ' w (eΨ x) := hΘeΨ w x
    rw [h3]
    have hconj : a * (eΨ x) * a⁻¹ =
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L) * (eΨ x) *
          (⟨canonicalRep (coxeterSystem τ) L w,
            CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
              CFSG.Blueprint.Chevalley.adjointGroup τ L)⁻¹ := by
      apply Subtype.ext
      exact hw (eΨ x) (ExcFrames.mem_torusPow_iff_coe.mp (eΨ x).2)
    rw [show ((θ' w (eΨ x) : torusPow τ L 3) :
        CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
            CFSG.Blueprint.Chevalley.adjointGroup τ L) * (eΨ x) *
          (⟨canonicalRep (coxeterSystem τ) L w,
            CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
              CFSG.Blueprint.Chevalley.adjointGroup τ L)⁻¹ from by
      rw [hθ'_apply]]
    exact hconj
  have key_mem : ∀ g : N, T.normalizerMonoidHom g ∈ Θ.range := by
    intro g
    obtain ⟨w, hw⟩ := key g
    exact ⟨w, hw.symm⟩
  let π : N →* WeylGroup τ :=
    (MonoidHom.ofInjective hΘinj).symm.toMonoidHom.comp
      (T.normalizerMonoidHom.codRestrict Θ.range key_mem)
  have hπ : ∀ g : N, T.normalizerMonoidHom g = Θ (π g) := by
    intro g
    have hx := congrArg Subtype.val (MulEquiv.apply_symm_apply (MonoidHom.ofInjective hΘinj)
      (T.normalizerMonoidHom.codRestrict Θ.range key_mem g))
    rw [MonoidHom.ofInjective_apply] at hx
    exact hx.symm
  have hπsurj : Function.Surjective π := by
    intro w
    obtain ⟨g, hg⟩ := hdescent w
    exact ⟨g, hΘinj (by rw [← hπ g, hg])⟩
  have hπker : π.ker = T.subgroupOf N := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have h1 : T.normalizerMonoidHom g = 1 := by rw [hπ g, hg, map_one]
      have h2 : (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) ∈
          Subgroup.centralizer (T : Set (CFSG.Blueprint.Chevalley.adjointGroup τ K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hxy : ((T.normalizerMonoidHom g) ⟨h, hh⟩ : T) = ⟨h, hh⟩ := by
          have := congrArg (fun f : MulAut T => f ⟨h, hh⟩) h1
          simpa using this
        have hcoe := CFSG.StandardType.normalizerMonoidHom_apply_coe g.2 ⟨h, hh⟩
        rw [hxy] at hcoe
        have hgh : (h : CFSG.Blueprint.Chevalley.adjointGroup τ K) =
            (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * h *
              (g : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹ := by
          simpa using hcoe
        have hcomm : (h : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) =
            (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) * h := by
          nth_rewrite 1 [hgh]
          group
        first
          | exact hcomm
          | exact hcomm.symm
      rwa [hcent] at h2
    · intro hg
      have hmem : (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) ∈
          Subgroup.centralizer (T : Set (CFSG.Blueprint.Chevalley.adjointGroup τ K)) := hcent.symm ▸ hg
      have h1 : T.normalizerMonoidHom g = 1 := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        show ((g : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (g : CFSG.Blueprint.Chevalley.adjointGroup τ K)⁻¹) =
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K)
        have hc := (Subgroup.mem_centralizer_iff.mp hmem)
          (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) x.2
        have hcomm : (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) =
            (x : CFSG.Blueprint.Chevalley.adjointGroup τ K) *
              (g : CFSG.Blueprint.Chevalley.adjointGroup τ K) := by
          first
            | exact hc
            | exact hc.symm
        rw [hcomm]
        group
      apply hΘinj
      rw [← hπ g, h1, map_one]
  refine Exists.intro (π : (Subgroup.normalizer ((TableBExcTwoTB.tE K F).range :
      Set (CFSG.Blueprint.Chevalley.adjointGroup τ K))) →* WeylGroup τ) ?_
  refine Exists.intro (φ : (TableBExcTwoTB.tE K F).range ≃*
      Multiplicative (Fin τ.rank → ZMod 3)) ?_
  refine ⟨hπsurj, hπker, ?_⟩
  intro g e
  rw [hπ g]
  exact hΘ_apply (π g) e

end CFSG.StandardType.FrameRoute

end
