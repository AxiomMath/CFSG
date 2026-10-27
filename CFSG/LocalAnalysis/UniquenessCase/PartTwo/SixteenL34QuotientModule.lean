module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardTrans
public import CFSG.Quasithin.Background.Harris.L3.Classify
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.HModelType
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.Quasithin.Vol2.Ch5Sec1L34E54
public import CFSG.RankThree.FFModules.BinaryTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.L3Nine CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix
open scoped Matrix

theorem binaryNineTensor_of_l34_quotient_rank_nine
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsLn ↥H 3 2)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 9) :
    BinaryNineTensor H ⊤ (fixV H) 1 := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥H := by
    have h1 := CFSG.Quasithin.H13.E54.isQuasisimple_of_lieModel (L := ↥H) hH
    exact ⟨Group.isPerfect_def.mp h1.1, h1.2.1⟩
  obtain ⟨Q, hQcomm, hQfin, q, ρ, hqsurj, hqker, hρinj, hqeq, hQsq, hQcard, hQirr⟩ :=
    s16k_qm_quotMap (W := W) (H := H) hq hcomm hW
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨eHF⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) (p := 2) (f := 2) hH
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : Fintype F := Fintype.ofFinite F
  haveI hFchar : CharP F 2 := CFSG.Quasithin.G11.Harris.L3.charP_two_of_card (f := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hFint : Fintype.card F = 2 ^ 2 := by
    simpa using hFcard
  let π₀ : SpecialLinearGroup (Fin 3) F →* ↥H :=
    eHF.symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
  have hπ₀ : Function.Surjective π₀ :=
    eHF.symm.surjective.comp
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F)
  letI : Module (ZMod 2) (Additive Q) := CFSG.RankThree.FFModules.moduleOfSq hQsq
  let σ : Representation (ZMod 2) (SpecialLinearGroup (Fin 3) F) (Additive Q) :=
    (CFSG.RankThree.FFModules.autRep Q).comp (ρ.comp π₀)
  have hσirr : σ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
    refine ⟨?_, ?_⟩
    ·
      haveI : IsSimpleGroup ↥H :=
        CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel (L := ↥H) hH
      have hHnt : Nontrivial ↥H := inferInstance
      have hMulAutnt : Nontrivial (MulAut Q) := by
        obtain ⟨h, hh⟩ := exists_ne (1 : ↥H)
        refine ⟨1, ρ h, fun hcon => hh (hρinj (hcon.symm.trans (map_one ρ).symm))⟩
      obtain ⟨a, b, hab⟩ := hMulAutnt
      obtain ⟨x, hx⟩ : ∃ x : Q, a x ≠ b x := by
        by_contra hcon
        push Not at hcon
        exact hab (MulEquiv.ext hcon)
      exact ⟨Additive.ofMul (a x), Additive.ofMul (b x), fun hcon =>
        hx (Additive.ofMul.injective hcon)⟩
    · intro U hU
      let B : Subgroup Q :=
        { carrier := {b | Additive.ofMul b ∈ U}
          mul_mem' := fun {a b} ha hb => by
            show Additive.ofMul (a * b) ∈ U
            exact U.add_mem ha hb
          one_mem' := by simpa using U.zero_mem
          inv_mem' := fun {a} ha => by
            show Additive.ofMul a⁻¹ ∈ U
            exact U.neg_mem ha }
      have hB : ∀ l : ↥H, ∀ b ∈ B, (ρ l : MulAut Q) b ∈ B := by
        intro l b hb
        obtain ⟨g, hg⟩ := hπ₀ l
        have h := hU g (Additive.ofMul b) hb
        change Additive.ofMul ((ρ l : MulAut Q) b) ∈ U
        simpa [σ, CFSG.RankThree.FFModules.autRep_apply, MonoidHom.comp_apply, hg] using h
      rcases hQirr hirr B hB with hB | hB
      · left
        rw [Submodule.eq_bot_iff]
        intro a ha
        have h1 : Additive.toMul a ∈ B := ha
        rw [hB, Subgroup.mem_bot] at h1
        exact Additive.toMul.injective h1
      · right
        rw [Submodule.eq_top_iff']
        intro a
        have h1 : Additive.toMul a ∈ B := by rw [hB]; trivial
        exact h1
  have hntσ : ∃ g : SpecialLinearGroup (Fin 3) F, σ g ≠ 1 := by
    haveI : IsSimpleGroup ↥H :=
      CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel (L := ↥H) hH
    have hHnt : Nontrivial ↥H := inferInstance
    obtain ⟨h, hh⟩ := exists_ne (1 : ↥H)
    obtain ⟨g, hg⟩ := hπ₀ h
    refine ⟨g, ?_⟩
    intro hσ
    have hfun : ∀ x : Q, (ρ (π₀ g)) x = x := by
      intro x
      have h := congrArg (fun f : Module.End (ZMod 2) (Additive Q) =>
        f (Additive.ofMul x)) hσ
      have h' : Additive.ofMul ((ρ (π₀ g)) x) = Additive.ofMul x := by
        simpa [σ, CFSG.RankThree.FFModules.autRep_apply, MonoidHom.comp_apply] using h
      exact Additive.ofMul.injective h'
    have hρ1 : ρ (π₀ g) = 1 := MulEquiv.ext hfun
    exact hh (by rw [← hg]; exact hρinj (hρ1.trans (map_one ρ).symm))
  have hdimQ : Module.finrank (ZMod 2) (Additive Q) = 9 := by
    apply CFSG.Quasithin.G11.Harris.L3.finrank_eq_of_natCard (d := 9)
    show Nat.card Q = 2 ^ 9
    rw [hQcard, hdim]
  have hdim_le : Module.finrank (ZMod 2) (Additive Q) ≤ 4 * 2 + 2 := by
    rw [hdimQ]; norm_num
  rcases CFSG.Quasithin.G11.Harris.L3.sl3_small_classification'
      (f := 2) (F := F) (W := Additive Q) (by norm_num) hFint σ hσirr hntσ hdim_le with
    ⟨⟨ψ, hψ, E, hE⟩, hdim6⟩ | ⟨k, hf2, hk12, hdim9, hK, ψ, hψ, E, hE⟩
  · rw [hdimQ] at hdim6
    omega
  ·
    have hk1 : k = 1 := by
      rw [hdimQ] at hdim9
      omega
    subst k
    let D : FFModel := FFModel.twistTensor 1 (StatedSL 3 F)
    have hK' : Nat.card F = 2 ^ (2 * 1) := by simpa using hK
    have hD : D.IsActionModel :=
      CFSG.Quasithin.FFModel.twistTensor_isActionModel (F := F) (ι := Fin 3) (a := 1)
        (Γ := StatedSL 3 F) hK'
    have hkerD : D.ker = ⊥ := rfl
    let gmap : ↥(StatedSL 3 F) →* SpecialLinearGroup (Fin 3) F :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom
    let π : ↥(StatedSL 3 F) →* ↥(ρ.range) :=
      ρ.rangeRestrict.comp (π₀.comp (ψ.comp gmap))
    have hψsurj : Function.Surjective ψ := fun g => ⟨ψ g, hψ g⟩
    have hπ : Function.Surjective π :=
      ρ.rangeRestrict_surjective.comp
        (hπ₀.comp (hψsurj.comp
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.surjective))
    let φ : Q ≃* Multiplicative (Additive Q) :=
      { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
        invFun := fun x => Additive.toMul (Multiplicative.toAdd x)
        left_inv := fun x => rfl
        right_inv := fun x => rfl
        map_mul' := fun a b => rfl }
    let β : Q ≃* HMod 1 F := φ.trans E
    have hact_eq : ∀ (γ : ↥(StatedSL 3 F)) (X : HMod 1 F),
        (FFModel.twistTensor 1 (StatedSL 3 F)).act γ
            ((X : HMod 1 F) : Multiplicative (Matrix (Fin 3) (Fin 3) F)) =
          ((CFSG.Quasithin.H.L3Nine.rhoT hK (γ : GL (Fin 3) F) X : HMod 1 F) :
            Multiplicative (Matrix (Fin 3) (Fin 3) F)) := by
      intro γ X
      change Multiplicative.ofAdd
          ((((γ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *
            CFSG.Quasithin.H.L3Nine.mat X *
            (CFSG.Quasithin.frobPow 1 (((γ : GL (Fin 3) F)) :
              Matrix (Fin 3) (Fin 3) F))ᵀ) =
        Multiplicative.ofAdd
          (CFSG.Quasithin.H.L3Nine.tw 1 (((γ : GL (Fin 3) F)) :
            Matrix (Fin 3) (Fin 3) F) (CFSG.Quasithin.H.L3Nine.mat X))
      rw [CFSG.Quasithin.H.L3Nine.frobPow_eq_conjM]
      rfl
    have hβact : ∀ (γ : ↥(StatedSL 3 F)) (v : Q),
        ((β (((π γ : ↥(ρ.range)) : MulAut Q) v) : HMod 1 F) :
            Multiplicative (Matrix (Fin 3) (Fin 3) F)) =
          (FFModel.twistTensor 1 (StatedSL 3 F)).act γ
            ((β v : HMod 1 F) : Multiplicative (Matrix (Fin 3) (Fin 3) F)) := by
      intro γ v
      have hstep : β (((π γ : ↥(ρ.range)) : MulAut Q) v) =
          CFSG.Quasithin.H.L3Nine.rhoT hK (γ : GL (Fin 3) F) (β v) := by
        calc β (((π γ : ↥(ρ.range)) : MulAut Q) v)
            = E (Multiplicative.ofAdd (σ (ψ (gmap γ)) (Additive.ofMul v))) := rfl
          _ = CFSG.Quasithin.H.L3Nine.rho hK (ψ (ψ (gmap γ)))
                (E (Multiplicative.ofAdd (Additive.ofMul v))) :=
                hE (ψ (gmap γ)) (Additive.ofMul v)
          _ = CFSG.Quasithin.H.L3Nine.rho hK (gmap γ) (β v) := by
                rw [hψ (gmap γ)]
                rfl
          _ = CFSG.Quasithin.H.L3Nine.rhoT hK (γ : GL (Fin 3) F) (β v) := by
                apply CFSG.Quasithin.H.L3Nine.mat_injective
                rw [CFSG.Quasithin.H.L3Nine.mat_rho,
                  CFSG.Quasithin.H.L3Nine.mat_rhoT]
                have hmat : ((↑(gmap γ) : Matrix (Fin 3) (Fin 3) F)) =
                    ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
                  have h1 := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe
                    3 F (gmap γ)).symm
                  simpa [gmap, MulEquiv.apply_symm_apply] using h1
                rw [hmat]
      rw [hstep]
      exact (hact_eq γ (β v)).symm
    have hRvia : D.RealizesVia (ρ.range) ⊤ ⊥ π :=
      CFSG.Quasithin.B42L2.realizesVia_of_secEquiv (D := D) hD hkerD π hπ β hβact
    have hinj : Function.Injective ρ.rangeRestrict := fun a b hab =>
      hρinj (by simpa using congrArg Subtype.val hab)
    let eHB : ↥H ≃* ↥(ρ.range) :=
      MulEquiv.ofBijective ρ.rangeRestrict ⟨hinj, ρ.rangeRestrict_surjective⟩
    let e : ↥(ρ.range) →* ↥H := eHB.symm.toMonoidHom
    let s : ↥(⊤ : Subgroup W) →* ↥(⊤ : Subgroup Q) :=
      MonoidHom.codRestrict (q.comp (⊤ : Subgroup W).subtype) ⊤
        (fun _ => Subgroup.mem_top _)
    have hs : Function.Surjective s := by
      intro y
      obtain ⟨x, hx⟩ := hqsurj (y : Q)
      exact ⟨⟨x, Subgroup.mem_top x⟩, Subtype.ext hx⟩
    have heq : ∀ (b : ↥(ρ.range)) (u : ↥(⊤ : Subgroup W)),
        ((s ⟨((e b : ↥H) : MulAut W) (u : W), Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup Q)) : Q) = (b : MulAut Q) ((s u : ↥(⊤ : Subgroup Q)) : Q) := by
      intro b u
      have hb : ρ (e b) = (b : MulAut Q) := by
        have hcoe : ∀ x : ↥H, ((eHB x : ↥(ρ.range)) : MulAut Q) = ρ x := fun x => rfl
        calc ρ (e b) = ((eHB (e b) : ↥(ρ.range)) : MulAut Q) := (hcoe (e b)).symm
          _ = (b : MulAut Q) := congrArg Subtype.val (eHB.apply_symm_apply b)
      show q (((e b : ↥H) : MulAut W) (u : W)) = (b : MulAut Q) (q (u : W))
      rw [hqeq, hb]
    have hZ : Subgroup.map (⊤ : Subgroup W).subtype s.ker = fixV H := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
        have h2 : s u = 1 := MonoidHom.mem_ker.mp hu
        have h3 : q (u : W) = 1 := by simpa [s] using congrArg Subtype.val h2
        exact (hqker (u : W)).1 h3
      · intro hx
        exact Subgroup.mem_map.2 ⟨⟨x, Subgroup.mem_top x⟩, by
          apply Subtype.ext
          show q x = 1
          exact (hqker x).2 hx, rfl⟩
    have hRealH : D.Realizes H ⊤ (fixV H) := by
      have h := s16c11_v1_realizes_comp (W := W) (W' := Q) (A := H) (B := ρ.range)
        (U := ⊤) (I := ⊤) e eHB.symm.surjective (fun _ _ _ _ => Subgroup.mem_top _)
        s hs heq (show D.Realizes (ρ.range) ⊤ ⊥ from ⟨π, hRvia⟩)
      rwa [hZ] at h
    exact ⟨F, hFfield, hFfin, hFchar, hK', hRealH⟩

theorem centralizer_eq_bot_of_binaryNineTensor_of_commSub_eq_top
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (hmodel : BinaryNineTensor H ⊤ (fixV H) 1)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤) :
    Subgroup.centralizer (H : Set (MulAut W)) = ⊥ := by
  classical
  obtain ⟨F, hFfield, hFfin, hFchar, hFcard, hReal⟩ := hmodel
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  obtain ⟨π, hR⟩ := hReal
  let D : FFModel := FFModel.twistTensor 1 (StatedSL 3 F)
  let Z : Subgroup W := fixV H
  have hHstab : H ≤ stabSub Z :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer (X := H) (K := H)
      Subgroup.le_normalizer
  let θ : ↥H →* ↥(autQuot H Z) :=
    MonoidHom.codRestrict ((quotHom Z).comp (Subgroup.inclusion hHstab)) (autQuot H Z) (by
      intro h
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hHstab h, by
        rw [Subgroup.mem_subgroupOf]
        exact h.2, rfl⟩)
  have hθ : Function.Surjective θ := by
    intro φ
    obtain ⟨g, hgH, hgφ⟩ := Subgroup.mem_map.1 φ.2
    refine ⟨⟨(g : MulAut W), hgH⟩, ?_⟩
    apply Subtype.ext
    exact hgφ
  have hRealQ : D.Realizes (autQuot H Z) ⊤ ⊥ := by
    have h := s16k_realizes_map (W := W) (W' := W ⧸ Z) (D := D) ⟨π, hR⟩
      (QuotientGroup.mk' Z) (by rw [QuotientGroup.ker_mk' Z]) θ hθ (by
        intro h w
        have h1 : (θ h : MulAut (W ⧸ Z)) (QuotientGroup.mk' Z w) =
            QuotientGroup.mk' Z ((h : MulAut W) w) := rfl
        rw [h1])
    have htop : Subgroup.map (QuotientGroup.mk' Z) (⊤ : Subgroup W) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)
    have hbot : Subgroup.map (QuotientGroup.mk' Z) Z = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro z hz
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    rw [htop, hbot] at h
    exact h
  have hmodelQ : BinaryNineTensor (autQuot H Z) ⊤ ⊥ 1 :=
    ⟨F, hFfield, hFfin, hFchar, hFcard, hRealQ⟩
  have hcentQ : Subgroup.centralizer (autQuot H Z : Set (MulAut (W ⧸ Z))) = ⊥ :=
    CFSG.Quasithin.H.ModelType.centralizer_eq_bot_of_binaryNine hmodelQ
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have hac : ∀ h ∈ H, a * h = h * a := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp ha h hh).symm
  have haN : a ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer _ ha
  have haStab : a ∈ stabSub Z :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer (X := Subgroup.centralizer
      (H : Set (MulAut W))) (K := H)
      (Subgroup.centralizer_le_normalizer (H : Set (MulAut W))) ha
  have hcent_a : quotHom Z ⟨a, haStab⟩ ∈
      Subgroup.centralizer (autQuot H Z : Set (MulAut (W ⧸ Z))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro φ hφ
    obtain ⟨g, hgmem, hgφ⟩ := Subgroup.mem_map.1 hφ
    have hgH : (g : MulAut W) ∈ H := Subgroup.mem_subgroupOf.mp hgmem
    rw [← hgφ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (g : MulAut W) * a = a * (g : MulAut W)
    exact (hac (g : MulAut W) hgH).symm
  have hqa : quotHom Z ⟨a, haStab⟩ = 1 := by
    rw [hcentQ, Subgroup.mem_bot] at hcent_a
    exact hcent_a
  have hdisp : ∀ w : W, a w * w⁻¹ ∈ fixV H := by
    have hmem : ⟨a, haStab⟩ ∈ (quotHom Z).ker := MonoidHom.mem_ker.2 hqa
    rw [CFSG.Quasithin.ker_quotHom Z, Subgroup.mem_subgroupOf] at hmem
    exact CFSG.Quasithin.mem_centQuot.1 hmem
  exact s16g_eq_one_of_commSub hcomm hac hdisp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
