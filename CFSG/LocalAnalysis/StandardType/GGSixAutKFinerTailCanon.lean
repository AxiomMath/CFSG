module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerRest
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

open scoped Pointwise

variable {G : Type} [Group G]

theorem ggAKFT_centralizer_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {M E₀ K : Subgroup G}
    (hfus : GGControlsStrongFusion M E₀) (hE : IsElemAbelian p E₀) (hEcard : Nat.card E₀ = p ^ 2)
    (hEK : E₀ ≤ Subgroup.normalizer (K : Set G)) :
    (E₀ ⊔ K) ⊓ Subgroup.centralizer (K : Set G) ≤ M := by
  classical
  set W := E₀ ⊔ K with hW
  set Y := W ⊓ Subgroup.centralizer (K : Set G) with hY
  have hKW : K ≤ W := le_sup_right
  have hKn : (K.subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  have hEp : ∀ e ∈ E₀, e ^ p = 1 := hE.2
  have hsurj : ∀ q : ↥W ⧸ K.subgroupOf W, ∃ e ∈ E₀, ∃ he : e ∈ W,
      QuotientGroup.mk' (K.subgroupOf W) ⟨e, he⟩ = q := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hw : (w : G) ∈ (E₀ : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E₀ K hEK]
      exact w.2
    obtain ⟨e, he, k, hk, hek⟩ := Set.mem_mul.mp hw
    refine ⟨e, he, le_sup_left (a := E₀) he, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 : ((⟨e, le_sup_left (a := E₀) he⟩ : ↥W)⁻¹ * w : ↥W) = (e⁻¹ * w : G) := rfl
    rw [h1, ← hek, inv_mul_cancel_left]
    exact hk
  have hQp : IsPGroup p (↥W ⧸ K.subgroupOf W) := by
    intro q
    obtain ⟨e, he, heW, rfl⟩ := hsurj q
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    have h1 : (⟨e, heW⟩ : ↥W) ^ p = 1 := Subtype.ext (by simpa using hEp e he)
    rw [h1, map_one]
  have : Group.IsNilpotent (↥W ⧸ K.subgroupOf W) := hQp.isNilpotent
  let φ : ↥Y →* ↥W ⧸ K.subgroupOf W :=
    (QuotientGroup.mk' (K.subgroupOf W)).comp (Subgroup.inclusion (inf_le_left : Y ≤ W))
  have hφ : φ.ker ≤ Subgroup.center ↥Y := by
    intro y hy
    have h1 : QuotientGroup.mk' (K.subgroupOf W) (Subgroup.inclusion inf_le_left y) = 1 := hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    rw [Subgroup.mem_center_iff]
    intro y'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp y'.2.2 (y : G) h1).symm
  have hYnil : Group.IsNilpotent ↥Y := Subgroup.isNilpotent_of_ker_le_center φ hφ
  have hYN : E₀ ≤ Subgroup.normalizer (Y : Set G) := fun e he =>
    ggMem_normalizer_inf (Subgroup.le_normalizer (le_sup_left (a := E₀) he))
      (ggMem_normalizer_centralizer (hEK he))
  have hO : (CFSG.pPrimeCore p ↥Y).map Y.subtype ≤ M := by
    refine hfus.le_of_coprime hp.out hE hEcard ?_ ?_
    · rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact (hp.out.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
    · exact hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hP : (CFSG.pCore p ↥Y).map Y.subtype ≤ M := by
    obtain ⟨e, he, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
    have hEpg : IsPGroup p E₀ := fun g => ⟨1, Subtype.ext (by simpa using hEp g g.2)⟩
    have hPp : IsPGroup p ((CFSG.pCore p ↥Y).map Y.subtype) := CFSG.pCore_isPGroup.map _
    have hEN : E₀ ≤ Subgroup.normalizer
        (((CFSG.pCore p ↥Y).map Y.subtype : Subgroup G) : Set G) :=
      hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
    have hR : IsPGroup p ↥(E₀ ⊔ (CFSG.pCore p ↥Y).map Y.subtype) :=
      IsPGroup.to_sup_of_normal_right' hEpg hPp hEN
    exact le_sup_right.trans (hfus.le_of_isPGroup he he1 hR (le_sup_left (a := E₀) he))
  intro y hy
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (p := p) hYnil
    (Subgroup.mem_top (⟨y, hy⟩ : ↥Y))
  have hmap := Subgroup.mem_map_of_mem Y.subtype htop
  rw [Subgroup.map_sup] at hmap
  exact sup_le hP hO hmap

theorem ggAKFT_sup_inf_le {M E₀ K : Subgroup G} (hEM : E₀ ≤ M)
    (hEK : E₀ ≤ Subgroup.normalizer (K : Set G)) : (E₀ ⊔ K) ⊓ M ≤ E₀ ⊔ (K ⊓ M) := by
  intro w hw
  obtain ⟨hwW, hwM⟩ := Subgroup.mem_inf.mp hw
  have hw' : w ∈ (E₀ : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E₀ K hEK]
    exact hwW
  obtain ⟨e, he, k, hk, rfl⟩ := Set.mem_mul.mp hw'
  have hkM : k ∈ M := by
    have h := M.mul_mem (M.inv_mem (hEM he)) hwM
    rwa [inv_mul_cancel_left] at h
  exact Subgroup.mul_mem _ (le_sup_left (a := E₀) he)
    (le_sup_right (a := E₀) (Subgroup.mem_inf.mpr ⟨hk, hkM⟩))

theorem ggAKFT_generalizedFitting_eq {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : CFSG.IsComponent N) (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    CFSG.generalizedFitting X = N :=
  CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot N hN hC

end General

section Canon

theorem ggAutKCanonIIInput_holds : GGAutKCanonIIInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg _
  obtain ⟨-, hb1, -, hK, -, hKM, hm, hEC⟩ := hcfg
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hEK : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hYV : ggAutKW D K m ⊓ Subgroup.centralizer (K : Set G) ≤
      ggAutKV D K (ggM p B x L D J) m := by
    intro w hw
    have hwM : w ∈ ggM p B x L D J := ggAKFT_centralizer_le hfusE hE0el hE0card hEK hw
    exact Subgroup.mem_inf.mpr
      ⟨ggAKFT_sup_inf_le hfusE.1 hEK (Subgroup.mem_inf.mpr ⟨hw.1, hwM⟩), hw.2⟩
  set W₀ := ggAutKW D K m with hW₀
  set V := ggAutKV D K (ggM p B x L D J) m with hV
  set π : ↥W₀ →* ↥W₀ ⧸ V.subgroupOf W₀ := QuotientGroup.mk' (V.subgroupOf W₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ1 : ∀ w : ↥W₀, π w = 1 ↔ (w : G) ∈ V := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hVC : V ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hKW : K ≤ W₀ := le_sup_right
  have hKn : (K.subgroupOf W₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  have hKnat := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
    hK.2.2
  set Kbar : Subgroup (↥W₀ ⧸ V.subgroupOf W₀) := (K.subgroupOf W₀).map π with hKbar
  let φ : ↥K →* ↥Kbar := (π.comp (Subgroup.inclusion hKW)).codRestrict Kbar
    (fun k => ⟨Subgroup.inclusion hKW k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext rfl⟩
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hk g
      have h1 : π (Subgroup.inclusion hKW k) = 1 := congrArg Subtype.val hk
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hVC ((hπ1 _).mp h1)) g g.2)
    · intro hk
      apply Subtype.ext
      change π (Subgroup.inclusion hKW k) = 1
      rw [hπ1]
      refine hYV (Subgroup.mem_inf.mpr ⟨hKW k.2, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (hk ⟨g, hg⟩)
  let eK : ↥Kbar ≃* ↥K ⧸ Subgroup.center ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).symm
  have hKnotker : ¬ K.subgroupOf W₀ ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hK fun a ha c hc => ?_
    have haV : a ∈ V := (hπ1 ⟨a, hKW ha⟩).mp (hle (Subgroup.mem_subgroupOf.mpr ha))
    exact (Subgroup.mem_centralizer_iff.mp (hVC haV) c hc).symm
  have hKcW : IsComponentOf K W₀ := ⟨hKW, ggIsSubnormal_of_normal hKW hKn, hK.2.2⟩
  have hKcomp : CFSG.IsComponent (K.subgroupOf W₀) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKW).mp hKcW
  have hKbarC : CFSG.IsComponent Kbar :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKcomp.1 π hKnotker, (hKn.map π hπs).isSubnormal⟩
  have hCbar : Subgroup.centralizer (Kbar : Set (↥W₀ ⧸ V.subgroupOf W₀)) = ⊥ := by
    rw [eq_bot_iff]
    intro wbar hwbar
    obtain ⟨w, rfl⟩ := hπs wbar
    rw [Subgroup.mem_bot, hπ1]
    refine hYV (Subgroup.mem_inf.mpr ⟨w.2, ?_⟩)
    have hconj : ∀ k : ↥K, (w : G) * k * (w : G)⁻¹ ∈ K := fun k => by
      have h := hKn.conj_mem (Subgroup.inclusion hKW k) (Subgroup.mem_subgroupOf.mpr k.2) w
      exact Subgroup.mem_subgroupOf.mp h
    let α : ↥K →* ↥K := MonoidHom.mk' (fun k => ⟨(w : G) * k * (w : G)⁻¹, hconj k⟩)
      (fun a c => Subtype.ext (by simp [mul_assoc]))
    have hα : ∀ k : ↥K, k⁻¹ * α k ∈ Subgroup.center ↥K := by
      intro k
      have hcomm := Subgroup.mem_centralizer_iff.mp hwbar (π (Subgroup.inclusion hKW k))
        ⟨_, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
      have h1 : π ((Subgroup.inclusion hKW k)⁻¹ * (w * Subgroup.inclusion hKW k * w⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      have h2 := hVC ((hπ1 _).mp h1)
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h3 := Subgroup.mem_centralizer_iff.mp h2 (g : G) g.2
      simpa [α, mul_assoc] using h3
    have hαid := ggAKF_eq_of_mem_center hK.2.2.1 α hα
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 : (w : G) * k * (w : G)⁻¹ = k := congrArg Subtype.val (hαid ⟨k, hk⟩)
    calc k * (w : G) = ((w : G) * k * (w : G)⁻¹) * w := by rw [h2]
      _ = w * k := by group
  have hF : CFSG.generalizedFitting (↥W₀ ⧸ V.subgroupOf W₀) = Kbar :=
    ggAKFT_generalizedFitting_eq hKbarC hCbar
  have hKtop : K ≠ ⊤ := fun h =>
    ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1 (top_le_iff.mp (h ▸ hK.1))
  have hcat : InCatalog (↥K ⧸ Subgroup.center ↥K) := by
    set Z : Subgroup G := (Subgroup.center ↥K).map K.subtype with hZ
    have hZK : Z ≤ K := Subgroup.map_subtype_le _
    have hZeq : Z.subgroupOf K = Subgroup.center ↥K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    have : (Z.subgroupOf K).Normal := by
      rw [hZeq]
      infer_instance
    let eZ : ↥K ⧸ Z.subgroupOf K ≃* ↥K ⧸ Subgroup.center ↥K :=
      QuotientGroup.quotientMulEquivOfEq hZeq
    have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKnat.2.1
    have : Nontrivial (↥K ⧸ Z.subgroupOf K) := eZ.toEquiv.nontrivial
    have hsZ : IsSimpleGroup (↥K ⧸ Z.subgroupOf K) :=
      IsSimpleGroup.isSimpleGroup_of_surjective eZ.symm.toMonoidHom eZ.symm.surjective
    obtain ⟨a, c, hac⟩ := hKnat.2.2
    have hnZ : ∃ a c : ↥K ⧸ Z.subgroupOf K, a * c ≠ c * a :=
      ⟨eZ.symm a, eZ.symm c, fun h => hac (eZ.symm.injective (by rw [map_mul, map_mul, h]))⟩
    exact inCatalog_of_mulEquiv eZ.symm (hctx.1.2.2.1 K Z hKtop hZK hsZ hnZ)
  unfold GGHypRestII
  rw [hF]
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKnat.2.1
  have : Nontrivial ↥Kbar := eK.toEquiv.nontrivial
  obtain ⟨a, c, hac⟩ := hKnat.2.2
  exact ⟨IsSimpleGroup.isSimpleGroup_of_surjective eK.symm.toMonoidHom eK.symm.surjective,
    ⟨eK.symm a, eK.symm c, fun h => hac (eK.symm.injective (by rw [map_mul, map_mul, h]))⟩,
    inCatalog_of_mulEquiv eK hcat⟩

end Canon

end CFSG.StandardType
