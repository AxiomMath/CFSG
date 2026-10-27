module

public import CFSG.RankThree.GF2n.Tim79a34QEOutResidual
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.RankThree.S4Free.StellmacherEmbed

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_of_centerIn_le [Finite G] {V S : Subgroup G}
    (hZleV : centerIn S ≤ V) (hZne : centerIn S ≠ ⊥) (hTI : IsTI V) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  have hconjInvZ : conjSubgroup g⁻¹ (centerIn S) ≤ centerIn S := by
    intro x hx
    have hxZ : g * x * g⁻¹ ∈ centerIn S := by simpa using mem_conjSubgroup.mp hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mpr hxZ.1, ?_⟩
    show x ∈ Subgroup.centralizer (S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hgsg : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have hcent : (g * s * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * s * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hxZ.2) (g * s * g⁻¹) hgsg
    calc s * x = g⁻¹ * (g * s * g⁻¹) * g * (g⁻¹ * (g * x * g⁻¹) * g) := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * s * g⁻¹)) * g := by rw [hcent]
      _ = g⁻¹ * (g * x * g⁻¹) * g * (g⁻¹ * (g * s * g⁻¹) * g) := by group
      _ = x * s := by group
  have hZleconjV : centerIn S ≤ conjSubgroup g V := by
    intro z hz
    rw [mem_conjSubgroup]
    refine hZleV (hconjInvZ ?_)
    rw [mem_conjSubgroup, inv_inv]
    have h : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rwa [h]
  have hne : V ⊓ conjSubgroup g V ≠ ⊥ := by
    intro hbot
    exact hZne (le_bot_iff.mp (hbot ▸ le_inf hZleV hZleconjV))
  exact mem_normalizer_iff_conjSubgroup_eq.mpr (conjSubgroup_eq_of_isTI hTI hne)

theorem exists_sylow_le_of_twoEnd [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  let T₂ : Sylow 2 ↥M := Classical.arbitrary _
  let S : Subgroup G := (T₂ : Subgroup ↥M).map M.subtype
  have hSylM : IsSylowOf 2 S M := ⟨T₂, rfl⟩
  have hQT : inSubgroup (pCore 2) M ≤ S :=
    Subgroup.map_mono (f := M.subtype)
      (IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := ↥M)) T₂)
  have hPcore : P ≤ inSubgroup (pCore 2) M := by
    rw [← hc.hQ]
    exact hc.P_le_Q
  have hPS : P ≤ S := hPcore.trans hQT
  have hPne : P ≠ ⊥ := fun hbot => hc.V_ne_bot (le_bot_iff.mp (hbot ▸ hc.V_le_P))
  have hSne : S ≠ ⊥ := fun hbot => hPne (le_bot_iff.mp (hbot ▸ hPS))
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have hSp : IsPGroup 2 S := (Sylow.isPGroup' T₂).map M.subtype
  have hZne : centerIn S ≠ ⊥ := by
    rw [centerIn_eq_map_center]
    intro hbot
    have hcenter : Subgroup.center ↥S = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥S) S.subtype_injective).mp hbot
    exact (ne_of_gt (IsPGroup.bot_lt_center (p := 2) hSp)) hcenter
  have hZleV : centerIn S ≤ V := by
    calc centerIn S ≤ Subgroup.centralizer (S : Set G) := inf_le_right
      _ ≤ Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le fun x hx => hPS hx
      _ = V := hc.centralizer_P_eq
  have hNM : Subgroup.normalizer (S : Set G) ≤ M := by
    rw [← hc.normalizer_eq]
    exact normalizer_le_normalizer_of_centerIn_le hZleV hZne hc.ti
  have hSylTop : IsSylowOf 2 S ⊤ :=
    isSylowOf_of_normalizer_inf_le (T := S) (H := M) (M := ⊤)
      (by simpa using hSylM) (by simpa using hNM)
  rw [isSylowOf_iff] at hSylTop
  obtain ⟨-, hSp', hidx⟩ := hSylTop
  have hidx' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hidx
  refine ⟨hSp'.toSylow hidx', ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subtype_le _

theorem pResidual_sup_eq_top_of_twoEnd [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) :
    pResidual 2 G ⊔ M = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTM⟩ := exists_sylow_le_of_twoEnd hH
  have hsup : (T : Subgroup G) ⊔ pResidual 2 G = ⊤ :=
    CFSG.RankThree.S4Free.sylow_sup_pResidual_eq_top T
  have hRle : pResidual 2 G ≤ pResidual 2 G ⊔ M := le_sup_left
  have hMle : M ≤ pResidual 2 G ⊔ M := le_sup_right
  have hTle : (T : Subgroup G) ≤ pResidual 2 G ⊔ M := hTM.trans hMle
  rw [eq_top_iff, ← hsup]
  exact sup_le hTle hRle

theorem not_weaklyClosedIn_subgroupOf_residual [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    ¬ WeaklyClosedIn (V.subgroupOf (pResidual 2 G)) (M.subgroupOf (pResidual 2 G)) := by
  let G₀ : Subgroup G := pResidual 2 G
  haveI : G₀.Normal := G6.pResidual_normal_aux 2
  intro hwc
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hV : V ≤ G₀ := V_le_pResidual_of_twoEnd hH hZ hn
  have hnot : ¬ ∀ g : G, conjSubgroup g V ≤ M → conjSubgroup g V = V := by
    intro h
    exact hc.notWC ⟨hc.maxAb.prop.1, h⟩
  push Not at hnot
  obtain ⟨g, hgM, hgne⟩ := hnot
  have hsup : G₀ ⊔ M = ⊤ := pResidual_sup_eq_top_of_twoEnd hH
  obtain ⟨g₀, hg₀, m, hm, hgm⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := G₀) (t := M)).mp (by rw [hsup]; exact Subgroup.mem_top g)
  have hmV : conjSubgroup m V = V :=
    mem_normalizer_iff_conjSubgroup_eq.mp (hc.maxAb.prop.2.1 hm)
  have hVg : conjSubgroup g V = conjSubgroup g₀ V := by
    rw [← hgm, conjSubgroup_mul, hmV]
  have hVgM : conjSubgroup g₀ V ≤ M := hVg ▸ hgM
  have hVgG : conjSubgroup g₀ V ≤ G₀ := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact Subgroup.Normal.conj_mem ‹G₀.Normal› v (hV hv) g₀
  let V₀ : Subgroup ↥G₀ := V.subgroupOf G₀
  let M₀ : Subgroup ↥G₀ := M.subgroupOf G₀
  let g₀' : ↥G₀ := ⟨g₀, hg₀⟩
  have hconj : conjSubgroup g₀' V₀ = (conjSubgroup g₀ V).subgroupOf G₀ :=
    conjSubgroup_subgroupOf G₀ V g₀'
  have hconjM : conjSubgroup g₀' V₀ ≤ M₀ := by
    rw [hconj]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hVgM (Subgroup.mem_subgroupOf.mp hx))
  have hmapconj : (conjSubgroup g₀' V₀).map G₀.subtype = conjSubgroup g₀ V := by
    rw [hconj, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hVgG
  have hmapV : V₀.map G₀.subtype = V := by
    rw [show V₀ = V.subgroupOf G₀ from rfl]
    exact Subgroup.map_subgroupOf_eq_of_le hV
  have hmap := congrArg (Subgroup.map G₀.subtype) (hwc.2 g₀' hconjM)
  rw [hmapconj, hmapV] at hmap
  exact hgne (hVg.trans hmap)

theorem generalizedFitting_subgroupOf_residual [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hrel : P.relIndex Q = 2)
    (hOut : ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) :
    generalizedFitting ↥(M.subgroupOf (pResidual 2 G)) =
      pCore 2 ↥(M.subgroupOf (pResidual 2 G)) := by
  let G₀ : Subgroup G := pResidual 2 G
  let M₀ : Subgroup ↥G₀ := M.subgroupOf G₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcore : P.subgroupOf G₀ = inSubgroup (pCore 2) M₀ :=
    pCore_subgroupOf_residual_eq hH hZ hn hrel hOut
  have hPM : P ≤ M := hc.P_le_Q.trans (hc.hQ ▸ (inSubgroup_pCore_two M).2.1)
  have hPG : P ≤ G₀ := P_le_pResidual hH hZ hn
  have hchar : IsCharacteristicP 2 ↥M₀ := by
    intro x hx
    have hxV : (((x : ↥M₀) : ↥G₀) : G) ∈ V := by
      rw [← hc.centralizer_P_eq, Subgroup.mem_centralizer_iff]
      intro p hp
      have hpG : p ∈ G₀ := hPG hp
      have hpM : p ∈ M := hPM hp
      let p₀ : ↥G₀ := ⟨p, hpG⟩
      let pm : ↥M₀ := ⟨p₀, Subgroup.mem_subgroupOf.mpr hpM⟩
      have hp₀map : p₀ ∈ (pCore 2 ↥M₀).map M₀.subtype := by
        have h : p₀ ∈ P.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr hp
        rw [hcore] at h
        exact h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hp₀map
      have hpm : pm ∈ pCore 2 ↥M₀ := by
        have hy_eq : y = pm := M₀.subtype_injective (by simpa [pm, p₀] using hyx)
        rwa [hy_eq] at hy
      have hxy : pm * x = x * pm := (Subgroup.mem_centralizer_iff.mp hx) pm hpm
      have := congrArg (fun z : ↥M₀ => (((z : ↥G₀) : G))) hxy
      simpa [pm, p₀] using this
    have hxP : (((x : ↥M₀) : ↥G₀) : G) ∈ P := hc.V_le_P hxV
    have hxmap : ((x : ↥M₀) : ↥G₀) ∈ (pCore 2 ↥M₀).map M₀.subtype := by
      have h : ((x : ↥M₀) : ↥G₀) ∈ P.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr hxP
      rw [hcore] at h
      exact h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hyx' : y = x := M₀.subtype_injective hyx
    rwa [hyx'] at hy
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M₀ 2).mp hchar

theorem residualFitNotWC [Finite G] {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hrel : P.relIndex Q = 2)
    (hOut : ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) :
    generalizedFitting (M.subgroupOf (pResidual 2 G)) =
      pCore 2 (M.subgroupOf (pResidual 2 G)) ∧
    ¬ WeaklyClosedIn (V.subgroupOf (pResidual 2 G)) (M.subgroupOf (pResidual 2 G)) :=
  ⟨generalizedFitting_subgroupOf_residual hH hZ hn hrel hOut,
    not_weaklyClosedIn_subgroupOf_residual hH hZ hn⟩

end CFSG.RankThree.GF2n.Tim79a
