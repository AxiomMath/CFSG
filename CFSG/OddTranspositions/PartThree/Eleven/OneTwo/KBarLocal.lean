module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KBar
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.LocalHypC
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section KBarLocal

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem localTwoA5_map_of_injective {Y₀ Y : Type} [Group Y₀] [Group Y]
    (φ : Y₀ →* Y) (hφ : Function.Injective φ) {Λ₀ : Set Y₀} {Λ : Set Y} {d : Y₀}
    (himg : φ '' commSet Λ₀ d = commSet Λ (φ d))
    (hL : LocalTwoA5 Λ₀ d) : LocalTwoA5 Λ (φ d) := by
  have hmap : Subgroup.map φ (Subgroup.closure (commSet Λ₀ d)) =
      Subgroup.closure (commSet Λ (φ d)) := by
    rw [MonoidHom.map_closure, himg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ commSet Λ₀ d, φ x₀ = x := by
      have : x ∈ φ '' commSet Λ₀ d := by rw [himg]; exact hx
      exact this
    obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ commSet Λ₀ d, φ y₀ = y := by
      have : y ∈ φ '' commSet Λ₀ d := by rw [himg]; exact hy
      exact this
    obtain ⟨g, hg, hgxy⟩ := hL.transitive x₀ hx₀ y₀ hy₀
    exact ⟨φ g, by rw [← hmap]; exact Subgroup.mem_map_of_mem φ hg,
      by simpa only [map_mul, map_inv] using congrArg φ hgxy⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem φ hL.mem
  · intro x hx hxcomm
    have hxmap : x ∈ Subgroup.map φ (Subgroup.closure (commSet Λ₀ d)) := by
      rw [hmap]; exact hx
    obtain ⟨x₀, hx₀, rfl⟩ := hxmap
    have hcomm : ∀ y ∈ Subgroup.closure (commSet Λ₀ d), Commute x₀ y := by
      intro y hy
      have hyB : φ y ∈ Subgroup.closure (commSet Λ (φ d)) := by
        rw [← hmap]; exact Subgroup.mem_map_of_mem φ hy
      have hcy := hxcomm (φ y) hyB
      apply hφ
      rw [map_mul, map_mul]
      exact hcy.eq
    rcases hL.center x₀ hx₀ hcomm with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1]
  · have eAB : Subgroup.closure (commSet Λ₀ d) ≃*
        Subgroup.closure (commSet Λ (φ d)) :=
      (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
    have eC : Subgroup.closure (commSet Λ₀ d) ⧸
          Subgroup.center (Subgroup.closure (commSet Λ₀ d)) ≃*
        Subgroup.closure (commSet Λ (φ d)) ⧸
          Subgroup.center (Subgroup.closure (commSet Λ (φ d))) :=
      QuotientGroup.congr _ _ eAB (Subgroup.map_center_eq eAB)
    obtain ⟨e2⟩ := hL.bender
    exact ⟨eC.symm.trans e2⟩

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

theorem localTwoA5_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (hu : hC.d ∈ centSet D (frameE hC r)) :
    LocalTwoA5 (centSetBar D (frameE hC r)) (mkCentSet D (frameE hC r) hC.d hu) := by
  classical
  set z : G := frameE hC r with hz
  let H := Halpha D hC.alpha
  let Θ : Set H := DstarH hC
  let Γu : Set H := centSet Θ (r 0 * r 1 * r 2)
  let L : Subgroup H := localGroup Θ (r 0 * r 1 * r 2)
  let K := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  let π := QuotientGroup.mk' R
  have hzp : z = hC.d * frameT hC r := by
    rw [hz, frameE]
  have hz2 : orderOf z = 2 := by simpa [hz] using orderOf_frameE h hF
  have hzH : z ∉ H := by
    intro hzH
    have htH : frameT hC r ∈ H := (r 0 * r 1 * r 2 : H).2
    have hprod : hC.d * frameT hC r ∈ H := hzp ▸ hzH
    have huH : hC.d ∈ H := by
      have := H.mul_mem hprod (H.inv_mem htH)
      simpa [mul_assoc] using this
    exact h.d_not_mem_Halpha huH
  have hRmap : R.map (Subgroup.subtype K) = Subgroup.zpowers z := by
    simpa [R, K, hz] using solvableRadical_localGroup h hF
  have hriΘ : ∀ i : Fin 3, r i ∈ Θ := by
    intro i
    have : r i ∈ ((T : Subgroup H) : Set H) ∩ DstarH hC := by
      rw [hF.frame.inter_eq]
      exact ⟨i, rfl⟩
    exact this.2
  have hri_cent : ∀ i : Fin 3, r i ∈ Γu := by
    intro i
    refine ⟨hriΘ i, ?_⟩
    exact ((hF.frame.commute i 0).mul_right (hF.frame.commute i 1)).mul_right
      (hF.frame.commute i 2)
  have hpL : r 0 * r 1 * r 2 ∈ L := by
    have h0 := Subgroup.subset_closure (hri_cent 0)
    have h1 := Subgroup.subset_closure (hri_cent 1)
    have h2 := Subgroup.subset_closure (hri_cent 2)
    exact L.mul_mem (L.mul_mem h0 h1) h2
  have hcommSetΘ : commSet Θ (r 0 * r 1 * r 2) = centSet Θ (r 0 * r 1 * r 2) := by
    ext x
    refine ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, ?_⟩⟩
    intro h
    have hx' : r 0 * r 1 * r 2 ∈ Θ := by simpa [h] using hx.1
    exact hF.frame.not_mem hx'
  have hFrame : LocalTwoA5 Θ (r 0 * r 1 * r 2) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [hcommSetΘ] at hx hy ⊢
      exact hF.frame.transitive x hx y hy
    · rw [hcommSetΘ]
      exact hpL
    · intro x _ hxc
      exact hF.frame.centralizer x fun y hy =>
        hxc y (Subgroup.subset_closure (hcommSetΘ.symm ▸ hy))
    · rw [hcommSetΘ]
      show Nonempty (localGroup Θ (r 0 * r 1 * r 2) ⧸
        Subgroup.center (localGroup Θ (r 0 * r 1 * r 2)) ≃* CFSG.Theory.Comparator.PSL2Model 2)
      exact hF.frame.bender
  let Λ₀ : Set L := {x : L | (x : H) ∈ Θ}
  have himg1 : L.subtype '' commSet Λ₀ ⟨r 0 * r 1 * r 2, hpL⟩ =
      commSet Θ (r 0 * r 1 * r 2) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hcy : Commute (y : H) (r 0 * r 1 * r 2) := by
        simpa using (hy.2.1).map L.subtype
      exact ⟨hy.1, hcy, fun h => hy.2.2 (Subtype.ext h)⟩
    · intro hx
      refine ⟨⟨x, Subgroup.subset_closure ⟨hx.1, hx.2.1⟩⟩, ⟨hx.1, ?_, ?_⟩, rfl⟩
      · exact (commute_iff_eq _ _).mpr (Subtype.ext hx.2.1.eq)
      · intro h
        exact hx.2.2 (congrArg (fun w : L => (w : H)) h)
  have hL : LocalTwoA5 Λ₀ ⟨r 0 * r 1 * r 2, hpL⟩ :=
    LocalTwoA5.of_injective L.subtype L.subtype_injective himg1 hFrame
  have hsub : ∀ x ∈ Γu, ((x : H) : G) ∈ K := by
    intro x hx
    have hxDstar : ((x : H) : G) ∈ DalphaStar D hC.alpha := hx.1
    have hxCS : ((x : H) : G) ∈ commSet D hC.d := by
      rwa [h.DalphaStar_eq] at hxDstar
    have hxD : ((x : H) : G) ∈ D := hxCS.1
    have hxu : Commute ((x : H) : G) hC.d := hxCS.2.1
    have hxt : Commute ((x : H) : G) (frameT hC r) := by
      have := hx.2.map H.subtype
      simpa [frameT] using this
    have hxe : Commute ((x : H) : G) z := by
      rw [hzp]
      exact hxu.mul_right hxt
    exact mem_localGroup_of_mem ⟨hxD, hxe⟩
  have hLK : L.map H.subtype ≤ K := by
    change (localGroup Θ (r 0 * r 1 * r 2)).map H.subtype ≤ localGroup D z
    rw [localGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact hsub x hx
  let fLK : L →* K :=
    { toFun := fun x => ⟨((x : H) : G), hLK (Subgroup.mem_map_of_mem H.subtype x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  let ψ : L →* K ⧸ R := π.comp fLK
  have hcomm_zpow : ∀ {a b : K}, Commute (π a) (π b) →
      (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ Subgroup.zpowers z := by
    intro a b hab
    have hmemR : a * b * a⁻¹ * b⁻¹ ∈ R := by
      have h1 : π (a * b * a⁻¹ * b⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab.eq]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    have h2 := Subgroup.mem_map_of_mem (Subgroup.subtype K) hmemR
    rw [hRmap] at h2
    simpa [Subgroup.coe_subtype] using h2
  have hdiff_zpow : ∀ {a b : K}, π a = π b →
      (a : G) * (b : G)⁻¹ ∈ Subgroup.zpowers z := by
    intro a b hab
    have hmemR : a * b⁻¹ ∈ R := by
      have h1 : π (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have h2 := Subgroup.mem_map_of_mem (Subgroup.subtype K) hmemR
    rw [hRmap] at h2
    simpa [Subgroup.coe_subtype] using h2
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hmem : (fLK x : G) * ((fLK y : G))⁻¹ ∈ Subgroup.zpowers z := hdiff_zpow hxy
    have hzmem : ((x : H) : G) * (((y : H) : G))⁻¹ ∈ Subgroup.zpowers z := hmem
    have hHz : ((x : H) : G) * (((y : H) : G))⁻¹ ∈ H :=
      H.mul_mem (x : H).2 (H.inv_mem (y : H).2)
    have hzpH : Subgroup.zpowers z ⊓ H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      rw [Subgroup.mem_inf] at hw
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hw.1 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hw.2) hzH
    have hbot : ((x : H) : G) * (((y : H) : G))⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hzpH]
      exact ⟨hzmem, hHz⟩
    have hxy' : ((x : H) : G) = ((y : H) : G) :=
      mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
    exact Subtype.ext (Subtype.ext hxy')
  have ht_comm : Commute (frameT hC r) hC.d := by
    have h := ((mem_commSet h hF 0).2.1.mul_left (mem_commSet h hF 1).2.1).mul_left
      (mem_commSet h hF 2).2.1
    simpa [frameT, mul_assoc] using h
  have hzt : z * hC.d = frameT hC r := by
    rw [hzp]
    rw [mul_assoc, ht_comm.eq, ← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul]
  let Sset : Set K := {w : K | (w : G) ∈ H.subtype '' Γu}
  have himg : ψ '' commSet Λ₀ ⟨r 0 * r 1 * r 2, hpL⟩ =
      commSet (centSetBar D z) (mkCentSet D z hC.d hu) := by
    have hLcomm : commSet Λ₀ ⟨r 0 * r 1 * r 2, hpL⟩ = {y : L | (y : H) ∈ Γu} := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, (hy.2.1).map L.subtype⟩
      · intro hy
        refine ⟨hy.1, (commute_iff_eq _ _).mpr (Subtype.ext hy.2.eq), ?_⟩
        intro h
        have h' : (y : H) = r 0 * r 1 * r 2 := congrArg (fun w : L => (w : H)) h
        simp only [Set.mem_setOf_eq] at hy
        rw [h'] at hy
        exact hF.frame.not_mem hy.1
    have hfLK : fLK '' {y : L | (y : H) ∈ Γu} = Sset := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : H), hy, rfl⟩
      · rintro ⟨x, hx, hw⟩
        refine ⟨⟨x, Subgroup.subset_closure hx⟩, hx, ?_⟩
        exact Subtype.ext hw
    have hRcomm : commSet (centSetBar D z) (mkCentSet D z hC.d hu) = π '' Sset := by
      ext v
      constructor
      · intro hv
        obtain ⟨w, hwLocal, rfl⟩ : ∃ w ∈ localSet D z, π w = v := hv.1
        have hwΓ : (w : G) ∈ centSet D z := hwLocal
        have hc : Commute (π w) (mkCentSet D z hC.d hu) := hv.2.1
        have hne : π w ≠ mkCentSet D z hC.d hu := hv.2.2
        have hwu : Commute (w : G) hC.d := by
          rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp (hcomm_zpow hc) with h1 | h1
          · rw [commute_iff_eq]
            have h1' : (w : G) * hC.d * (w : G)⁻¹ = hC.d := by
              have := congrArg (fun t => t * hC.d) h1
              simpa [mul_assoc] using this
            calc (w : G) * hC.d = (w : G) * hC.d * (w : G)⁻¹ * (w : G) := by group
              _ = hC.d * (w : G) := by rw [h1']
          · exfalso
            have h1' : (w : G) * hC.d * (w : G)⁻¹ = z * hC.d := by
              have := congrArg (fun t => t * hC.d) h1
              simpa [mul_assoc] using this
            have htD : frameT hC r ∈ D := by
              have hconj : (w : G) * hC.d * (w : G)⁻¹ ∈ D :=
                hC.setup.normal (w : G) hC.d hC.hd
              rw [h1', hzt] at hconj
              exact hconj
            exact frameT_not_mem h hF htD
        have hstar : (w : G) ∈ DalphaStar D hC.alpha := by
          have hwc : (w : G) ∈ commSet D hC.d := by
            refine ⟨hwΓ.1, hwu, ?_⟩
            intro h
            exact hne (by
              rw [show w = ⟨hC.d, mem_localGroup_of_mem hu⟩ from Subtype.ext h]
              rfl)
          rwa [h.DalphaStar_eq]
        have hwhH : (w : G) ∈ H := Subgroup.subset_closure hstar
        have hwt : Commute (w : G) (frameT hC r) := by
          have hwe'' : Commute (w : G) (hC.d * frameT hC r) := hwΓ.2
          have h := hwu.mul_right hwe''
          rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul] at h
          exact h
        refine ⟨w, ⟨⟨(w : G), hwhH⟩, ⟨hstar, ?_⟩, rfl⟩, rfl⟩
        exact (commute_iff_eq _ _).mpr (Subtype.ext hwt.eq)
      · rintro ⟨w, hwS, rfl⟩
        obtain ⟨x, hxΓu, hhw⟩ := hwS
        have hhΘ : x ∈ Θ := hxΓu.1
        have hcs : (x : G) ∈ commSet D hC.d := by
          have hd : (x : G) ∈ DalphaStar D hC.alpha := hhΘ
          rwa [h.DalphaStar_eq] at hd
        have hhD : (x : G) ∈ D := hcs.1
        have hhu : Commute (x : G) hC.d := hcs.2.1
        have hhne : (x : G) ≠ hC.d := hcs.2.2
        have hwu : Commute (w : G) hC.d := by rw [← hhw]; exact hhu
        have hhD' : (w : G) ∈ D := hhw ▸ hhD
        have hhz : Commute (x : G) z := by
          rw [hzp]
          exact hhu.mul_right (hxΓu.2.map H.subtype)
        have hwe : Commute (w : G) z := by rw [← hhw]; exact hhz
        have hwΓ : (w : G) ∈ centSet D z := ⟨hhD', hwe⟩
        have hvΛ : π w ∈ centSetBar D z := ⟨w, hwΓ, rfl⟩
        have hvcomm : Commute (π w) (mkCentSet D z hC.d hu) := by
          have : Commute w ⟨hC.d, mem_localGroup_of_mem hu⟩ :=
            (commute_iff_eq _ _).mpr (Subtype.ext hwu.eq)
          exact this.map π
        have hvne : π w ≠ mkCentSet D z hC.d hu := by
          intro hEq
          have hker : (w : G) * hC.d ∈ Subgroup.zpowers z := by
            have h := hdiff_zpow (a := w) (b := ⟨hC.d, mem_localGroup_of_mem hu⟩) hEq
            simpa [hC.setup.oddT.inv_eq hC.hd] using h
          rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hker with h1 | h1
          · have h1' : (w : G) = hC.d := by
              have := mul_eq_one_iff_eq_inv.mp h1
              rwa [hC.setup.oddT.inv_eq hC.hd] at this
            have hhw' : (x : G) = (w : G) := hhw
            exact hhne (by rw [hhw']; exact h1')
          · have h1' : (w : G) = frameT hC r := by
              have h2 : (w : G) = z * hC.d := by
                have h3 := congrArg (fun t => t * hC.d) h1
                rw [mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, mul_one] at h3
                exact h3
              rw [h2, hzt]
            exact frameT_not_mem h hF (h1' ▸ hhD')
        exact ⟨hvΛ, hvcomm, hvne⟩
    rw [hLcomm, hRcomm, ← hfLK]
    ext v
    exact ⟨fun ⟨y, hy, hvy⟩ => ⟨fLK y, ⟨y, hy, rfl⟩, hvy⟩,
      fun ⟨y, hy, hvy⟩ => by
        obtain ⟨z₀, hz₀, rfl⟩ := hy
        exact ⟨z₀, hz₀, hvy⟩⟩
  have htK : frameT hC r ∈ K := hLK (Subgroup.mem_map_of_mem H.subtype hpL)
  have hzK : z ∈ K := by
    have := K.mul_mem (mem_localGroup_of_mem hu) htK
    rw [hzp]
    exact this
  have hzR : (⟨z, hzK⟩ : K) ∈ R := by
    have hmem : z ∈ R.map (Subgroup.subtype K) := by
      rw [hRmap]
      exact Subgroup.mem_zpowers z
    obtain ⟨r', hr, hrz⟩ := hmem
    have hr' : r' = ⟨z, hzK⟩ := Subtype.ext hrz
    rwa [hr'] at hr
  have hπz : π ⟨z, hzK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hzR
  have hzprod : (⟨z, hzK⟩ : K) = ⟨hC.d, mem_localGroup_of_mem hu⟩ * ⟨frameT hC r, htK⟩ :=
    Subtype.ext hzp
  have hπt : π ⟨frameT hC r, htK⟩ = π ⟨hC.d, mem_localGroup_of_mem hu⟩ := by
    have h1 : π ⟨hC.d, mem_localGroup_of_mem hu⟩ * π ⟨frameT hC r, htK⟩ = 1 := by
      rw [← map_mul, ← hzprod, hπz]
    have h2 : π ⟨frameT hC r, htK⟩ = (π ⟨hC.d, mem_localGroup_of_mem hu⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    have h3 : (π ⟨hC.d, mem_localGroup_of_mem hu⟩)⁻¹ = π ⟨hC.d, mem_localGroup_of_mem hu⟩ :=
      inv_eq_of_mul_eq_one_right (by
        rw [← map_mul,
          show (⟨hC.d, mem_localGroup_of_mem hu⟩ * ⟨hC.d, mem_localGroup_of_mem hu⟩ : K) = 1
            from Subtype.ext (hC.setup.oddT.mul_self_eq_one hC.hd),
          map_one])
    exact h2.trans h3
  have hψp : ψ ⟨r 0 * r 1 * r 2, hpL⟩ = mkCentSet D z hC.d hu := by
    change π (fLK ⟨r 0 * r 1 * r 2, hpL⟩) = mkCentSet D z hC.d hu
    have hfLKp : fLK ⟨r 0 * r 1 * r 2, hpL⟩ = ⟨frameT hC r, htK⟩ := Subtype.ext rfl
    rw [hfLKp]
    exact hπt
  have himg' : ψ '' commSet Λ₀ ⟨r 0 * r 1 * r 2, hpL⟩ =
      commSet (centSetBar D z) (ψ ⟨r 0 * r 1 * r 2, hpL⟩) := by
    rw [hψp]
    exact himg
  have hmain : LocalTwoA5 (centSetBar D z) (ψ ⟨r 0 * r 1 * r 2, hpL⟩) :=
    localTwoA5_map_of_injective ψ hψinj himg' hL
  rw [← hψp]
  exact hmain

end ElevenTwoFrame

end KBarLocal

end CFSG.OddTranspositions.PartThree
