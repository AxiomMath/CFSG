module

public import CFSG.RankThree.GF2n.Tim79a34QEOutRed
public import CFSG.RankThree.GF2n.Tim79a34ResidualBasic
public import CFSG.RankThree.GF2n.Tim79a34ResidualMaxLocal
public import CFSG.GroupTheory.PCoreOfSubnormal

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem V_le_pResidual_of_twoEnd {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    V ≤ pResidual 2 G :=
  hH.setup.mc.toMinCex.V_le_P.trans (P_le_pResidual hH hZ hn)

theorem H_le_pResidual_of_twoEnd {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    H ≤ pResidual 2 G := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  exact le_pResidual_of_twoEnd hIW hH hZ hn

theorem centralizer_subgroupOf_residual_eq {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hV : V ≤ pResidual 2 G) :
    P.subgroupOf (pResidual 2 G) =
      P.subgroupOf (pResidual 2 G) ⊓
        Subgroup.centralizer ((V.subgroupOf (pResidual 2 G) : Subgroup ↥(pResidual 2 G)) :
          Set ↥(pResidual 2 G)) := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hPcent : P ≤ Subgroup.centralizer (V : Set G) := by
    rw [hc.hP]
    exact inf_le_right
  refine le_antisymm (fun x hx => ⟨hx, ?_⟩) inf_le_left
  change x ∈ Subgroup.centralizer ((V.subgroupOf (pResidual 2 G) : Subgroup ↥(pResidual 2 G)) :
    Set ↥(pResidual 2 G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hxG : (x : G) ∈ Subgroup.centralizer (V : Set G) :=
    hPcent (Subgroup.mem_subgroupOf.mp hx)
  have hyV : (y : G) ∈ V := Subgroup.mem_subgroupOf.mp hy
  exact Subgroup.mem_centralizer_iff.mp hxG (y : G) hyV

theorem weaklyClosedIn_subgroupOf_residual {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hV : V ≤ pResidual 2 G) :
    WeaklyClosedIn (V.subgroupOf (pResidual 2 G)) (P.subgroupOf (pResidual 2 G)) := by
  set G₀ : Subgroup G := pResidual 2 G with hG₀
  set V₀ : Subgroup ↥G₀ := V.subgroupOf G₀ with hV₀
  set P₀ : Subgroup ↥G₀ := P.subgroupOf G₀ with hP₀
  haveI : G₀.Normal := G6.pResidual_normal_aux 2
  have hc : MinCexWCQ M V Q P H := hH.setup.mc
  refine ⟨Subgroup.subgroupOf_mono G₀ hc.toMinCex.V_le_P, fun g hg => ?_⟩
  have hconj : conjSubgroup g V₀ = (conjSubgroup (g : G) V).subgroupOf G₀ :=
    CFSG.CGT.Timmesfeld75.conjSubgroup_subgroupOf G₀ V g
  have hconjG : conjSubgroup (g : G) V ≤ G₀ := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact Subgroup.Normal.conj_mem ‹G₀.Normal› v (hV hv) (g : G)
  have hleP : conjSubgroup (g : G) V ≤ P := by
    have h := Subgroup.map_mono (f := G₀.subtype) hg
    rw [hconj, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h
    rw [inf_eq_left.mpr hconjG] at h
    exact h.trans inf_le_left
  have heqG : conjSubgroup (g : G) V = V := hc.wcQ.2 (g : G) (hleP.trans hc.toMinCex.P_le_Q)
  rw [hconj, heqG]

theorem PleH_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H) :
    P.subgroupOf (pResidual 2 G) ≤ H.subgroupOf (pResidual 2 G) :=
  Subgroup.subgroupOf_mono (pResidual 2 G) hH.setup.mc.toMinCex.PleH

theorem four_le_card_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hV : V ≤ pResidual 2 G) : 4 ≤ Nat.card ↥(V.subgroupOf (pResidual 2 G)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv]
  exact hH.setup.mc.toMinCex.four

theorem isElemAbelian_subgroupOf_residual {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hV : V ≤ pResidual 2 G) :
    Assembly.IsElemAbelian 2 (V.subgroupOf (pResidual 2 G)) := by
  let e : ↥(V.subgroupOf (pResidual 2 G)) ≃* ↥V :=
    Subgroup.subgroupOfEquivOfLe hV
  refine ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => ?_⟩
  · apply e.injective
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (hH.setup.mc.toMinCex.elemAb.1.is_comm.comm (e x) (e y))
  · apply Subtype.ext
    exact hH.setup.mc.toMinCex.elemAb.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)

theorem isTI_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hV : V ≤ pResidual 2 G) : IsTI (V.subgroupOf (pResidual 2 G)) := by
  set G₀ : Subgroup G := pResidual 2 G with hG₀
  set V₀ : Subgroup ↥G₀ := V.subgroupOf G₀ with hV₀
  haveI : G₀.Normal := G6.pResidual_normal_aux 2
  have hmapconj : ∀ g : ↥G₀,
      (conjSubgroup g V₀).map G₀.subtype = conjSubgroup (g : G) V := by
    intro g
    rw [hV₀, conjSubgroup_subgroupOf, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (conjSubgroup_le_of_le_of_mem hV g.2)
  intro g
  have h := hH.setup.mc.toMinCex.ti (g : G)
  have hmap : (V₀ ⊓ conjSubgroup g V₀).map G₀.subtype =
      V ⊓ conjSubgroup (g : G) V := by
    rw [Subgroup.map_inf_eq _ _ _ G₀.subtype_injective, hV₀, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hV, hmapconj g]
  rcases h with hbot | htop
  · left
    apply Subgroup.map_injective G₀.subtype_injective
    rw [hmap, hbot, Subgroup.map_bot]
  · right
    apply Subgroup.map_injective G₀.subtype_injective
    rw [hmap, htop, hV₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV]

theorem map_inSubgroup_pCore_subgroupOf {H : Subgroup G} (hH : H ≤ pResidual 2 G) :
    (inSubgroup (pCore 2) (H.subgroupOf (pResidual 2 G))).map (pResidual 2 G).subtype =
      inSubgroup (pCore 2) H := by
  let G₀ : Subgroup G := pResidual 2 G
  let e : ↥(H.subgroupOf G₀) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hH
  let φ : ↥(H.subgroupOf G₀) →* G := G₀.subtype.comp (H.subgroupOf G₀).subtype
  have hcomp : φ = H.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [inSubgroup, Subgroup.map_map]
  change (pCore 2 ↥(H.subgroupOf G₀)).map φ = inSubgroup (pCore 2) H
  rw [hcomp, ← Subgroup.map_map, pCore_map_iso]
  rfl

theorem o2H_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hHle : H ≤ pResidual 2 G) :
    inSubgroup (pCore 2) (H.subgroupOf (pResidual 2 G)) ≠ ⊥ := by
  intro hbot
  apply hH.setup.mc.toMinCex.o2H
  have := congrArg (Subgroup.map (pResidual 2 G).subtype) hbot
  rw [map_inSubgroup_pCore_subgroupOf hHle, Subgroup.map_bot] at this
  exact this

theorem notLe_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hV : V ≤ pResidual 2 G) (hHle : H ≤ pResidual 2 G) :
    ¬ V.subgroupOf (pResidual 2 G) ≤
      inSubgroup (pCore 2) (H.subgroupOf (pResidual 2 G)) := by
  intro hle
  apply hH.setup.mc.toMinCex.notLe
  have hmap := Subgroup.map_mono (f := (pResidual 2 G).subtype) hle
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV,
    map_inSubgroup_pCore_subgroupOf hHle] at hmap
  exact hmap

theorem map_inSubgroup_pCore_subgroupOf' (H : Subgroup G) :
    (inSubgroup (pCore 2) (H.subgroupOf (pResidual 2 G))).map (pResidual 2 G).subtype =
      pCoreOf 2 (H ⊓ pResidual 2 G) := by
  let G₀ : Subgroup G := pResidual 2 G
  have hdom : H.subgroupOf G₀ = (H ⊓ G₀).subgroupOf G₀ :=
    (Subgroup.inf_subgroupOf_right H G₀).symm
  rw [hdom]
  let e : ↥((H ⊓ G₀).subgroupOf G₀) ≃* ↥(H ⊓ G₀) :=
    Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ G₀ ≤ G₀)
  let φ : ↥((H ⊓ G₀).subgroupOf G₀) →* G :=
    G₀.subtype.comp ((H ⊓ G₀).subgroupOf G₀).subtype
  have hcomp : φ = (H ⊓ G₀).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [inSubgroup, Subgroup.map_map]
  change (pCore 2 ↥((H ⊓ G₀).subgroupOf G₀)).map φ = pCoreOf 2 (H ⊓ G₀)
  rw [hcomp, ← Subgroup.map_map, pCore_map_iso]
  rfl

theorem pCore_subgroupOf_residual_eq {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hrel : P.relIndex Q = 2)
    (hOut : ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) :
    P.subgroupOf (pResidual 2 G) =
      inSubgroup (pCore 2) (M.subgroupOf (pResidual 2 G)) := by
  let G₀ : Subgroup G := pResidual 2 G
  haveI : G₀.Normal := G6.pResidual_normal_aux 2
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hPG : P ≤ G₀ := P_le_pResidual hH hZ hn
  apply Subgroup.map_injective G₀.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPG,
    map_inSubgroup_pCore_subgroupOf' M]
  have hnormal : ∀ m ∈ M, conjSubgroup m (M ⊓ G₀) = M ⊓ G₀ := by
    intro m hm
    ext x
    constructor
    · rintro ⟨y, ⟨hyM, hyG⟩, rfl⟩
      exact ⟨M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm),
        Subgroup.Normal.conj_mem ‹G₀.Normal› y hyG m⟩
    · intro hx
      refine ⟨m⁻¹ * x * m, ⟨?_, ?_⟩, ?_⟩
      · exact M.mul_mem (M.mul_mem (M.inv_mem hm) hx.1) hm
      · simpa using Subgroup.Normal.conj_mem ‹G₀.Normal› x hx.2 m⁻¹
      · show m * (m⁻¹ * x * m) * m⁻¹ = x
        group
  have hMnorm : ((M ⊓ G₀).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro m hm
    exact mem_normalizer_iff_conjSubgroup_eq.mpr (hnormal m hm)
  have hsub : CFSG.Open.IsSubnormal (M ⊓ G₀) M :=
    CFSG.Open.IsSubnormal.step inf_le_left hMnorm (CFSG.Open.IsSubnormal.refl M)
  have hcore := CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub
  rw [hcore]
  have hQ' : pCoreOf 2 M = Q := by
    simpa [pCoreOf, inSubgroup] using hc.hQ.symm
  rw [hQ']
  rw [inf_assoc, inf_comm G₀ Q, inf_pResidual_eq_P hH hZ hn hrel hOut,
    inf_eq_right.mpr hPM]

theorem min_subgroupOf_residual {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hV : V ≤ pResidual 2 G) (hHle : H ≤ pResidual 2 G) (hPG : P ≤ pResidual 2 G) :
    ∀ K : Subgroup ↥(pResidual 2 G),
      P.subgroupOf (pResidual 2 G) ≤ K →
      inSubgroup (pCore 2) K ≠ ⊥ → K < H.subgroupOf (pResidual 2 G) →
      V.subgroupOf (pResidual 2 G) ≤ inSubgroup (pCore 2) K := by
  let G₀ : Subgroup G := pResidual 2 G
  let V₀ : Subgroup ↥G₀ := V.subgroupOf G₀
  let H₀ : Subgroup ↥G₀ := H.subgroupOf G₀
  let P₀ : Subgroup ↥G₀ := P.subgroupOf G₀
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  intro K hPK hOK hKH
  have hKle : K ≤ H₀ := hKH.le
  let K' : Subgroup G := K.map G₀.subtype
  have hK'G : K' ≤ G₀ := Subgroup.map_subtype_le K
  have hK'sub : K'.subgroupOf G₀ = K := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK'G]
  have hHmap : H₀.map G₀.subtype = H := by
    rw [show H₀ = H.subgroupOf G₀ from rfl, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHle]
  have hPmap : P₀.map G₀.subtype = P := by
    rw [show P₀ = P.subgroupOf G₀ from rfl, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPG]
  have hK'le : K' ≤ H := by
    have h := Subgroup.map_mono (f := G₀.subtype) hKle
    rwa [hHmap] at h
  have hPK' : P ≤ K' := by
    have h := Subgroup.map_mono (f := G₀.subtype) hPK
    rwa [hPmap] at h
  have hOK' : inSubgroup (pCore 2) K' ≠ ⊥ := by
    intro hbot
    apply hOK
    have hmap : (inSubgroup (pCore 2) K).map G₀.subtype = ⊥ := by
      rw [← hK'sub, map_inSubgroup_pCore_subgroupOf hK'G, hbot]
    exact (Subgroup.map_eq_bot_iff_of_injective (H := inSubgroup (pCore 2) K)
      (f := G₀.subtype) G₀.subtype_injective).mp hmap
  have hlt : K' < H := by
    refine lt_of_le_of_ne hK'le ?_
    intro hEq
    have hmap : K.map G₀.subtype = H₀.map G₀.subtype := by
      change K' = H₀.map G₀.subtype
      rw [hEq, hHmap]
    have hKH' : K = H₀ := Subgroup.map_injective G₀.subtype_injective hmap
    exact (not_le_of_gt hKH) (le_of_eq hKH'.symm)
  have hVK := hc.min K' hPK' hOK' hlt
  rw [← Subgroup.map_le_map_iff_of_injective G₀.subtype_injective]
  have hVmap : V₀.map G₀.subtype = V := by
    rw [show V₀ = V.subgroupOf G₀ from rfl, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hV]
  have hKmap : (inSubgroup (pCore 2) K).map G₀.subtype = inSubgroup (pCore 2) K' := by
    rw [← hK'sub]
    exact map_inSubgroup_pCore_subgroupOf hK'G
  rw [hVmap, hKmap]
  exact hVK

theorem le_commutator_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B ≤ commutator B) : Subgroup.center A ≤ commutator A := by
  intro x hx
  have hx' : e x ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa using congrArg e (hx z)
  have hxcomm : e x ∈ commutator B := h hx'
  have hmap : commutator B = (commutator A).map e.toMonoidHom := by
    rw [_root_.commutator_def, _root_.commutator_def]
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup A)) (H₂ := (⊤ : Subgroup A))
      e.toMonoidHom
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
    exact h.symm
  rw [hmap, Subgroup.mem_map] at hxcomm
  obtain ⟨y, hy, hyx⟩ := hxcomm
  have hyx' : y = x := e.injective hyx
  rwa [hyx'] at hy

theorem ntQEOutResidualStatement_of_max
    (hFields : ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G),
      TwoEndHyp M V Q P H →
      Subgroup.center (Xbar V H) = ⊥ →
      (∃ n : ℕ, 3 ≤ n ∧
        Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
      P.relIndex Q = 2 →
      (∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) →
      generalizedFitting (M.subgroupOf (pResidual 2 G)) =
        pCore 2 (M.subgroupOf (pResidual 2 G)) ∧
      ¬ WeaklyClosedIn (V.subgroupOf (pResidual 2 G))
          (M.subgroupOf (pResidual 2 G)) ∧
      Sec23Data (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      (∀ d ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
        ∀ e ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
          orderOf (d * e) ≠ 4) ∧
      qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) = 2 ∧
      Sec23Three (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      Sec24bTilde (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
        (P.subgroupOf (pResidual 2 G)) ∧
      Sec25Concl (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
        (P.subgroupOf (pResidual 2 G)) ∧
      Nat.card ↥(V.subgroupOf (pResidual 2 G) ⊓
          wOf (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))) =
        qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      Nonempty (Xbar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ≃*
        Xbar V H)) :
    NTQEOutResidualStatement := by
  have hMaxLocal := residualMaxLocalStatement_holds
  have hMaxAb := residualMaxAbStatement_holds
  intro G _ _ M V Q P H hH hZ hn hrel hOut
  obtain ⟨hFit, hNotWC, hData, hDeg, hQtwo, hThree, hTilde,
    hConcl, hModule, hXbar⟩ := hFields G M V Q P H hH hZ hn hrel hOut
  have hV : V ≤ pResidual 2 G := V_le_pResidual_of_twoEnd hH hZ hn
  have hHle : H ≤ pResidual 2 G := H_le_pResidual_of_twoEnd hH hZ hn
  obtain ⟨eX⟩ := hXbar
  have hCenter : Subgroup.center (Xbar (V.subgroupOf (pResidual 2 G))
      (H.subgroupOf (pResidual 2 G))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : eX x ∈ Subgroup.center (Xbar V H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := eX.surjective y
      simpa using congrArg eX (Subgroup.mem_center_iff.mp hx z)
    rw [hZ, Subgroup.mem_bot] at hx'
    exact eX.injective (by simpa using hx')
  have hnKeep := hn
  obtain ⟨n, hn3, ⟨eSp⟩⟩ := hn
  let eZ : XbarZ (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ≃*
      XbarZ V H := QuotientGroup.congr _ _ eX (by simpa using Subgroup.map_center_eq (f := eX))
  have hRank : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃*
        XbarZ (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))) :=
    ⟨n, hn3, ⟨eSp.trans eZ.symm⟩⟩
  refine ⟨M.subgroupOf (pResidual 2 G), V.subgroupOf (pResidual 2 G),
    H.subgroupOf (pResidual 2 G), ?_, hCenter, hRank⟩
  exact
    { setup :=
        { mc :=
            { toMinCex :=
                { o2 := pCore_two_residual_eq_bot hH.setup.mc.toMinCex.o2
                  maxLocal := hMaxLocal G M V Q P H hH hZ hnKeep hrel hOut
                  fitting := hFit
                  maxAb := hMaxAb G M V Q P H hH hZ hnKeep hrel hOut
                  elemAb := isElemAbelian_subgroupOf_residual hH hV
                  ti := isTI_subgroupOf_residual hH hV
                  four := four_le_card_subgroupOf_residual hH hV
                  hQ := pCore_subgroupOf_residual_eq hH hZ hnKeep hrel hOut
                  hP := centralizer_subgroupOf_residual_eq hH hV
                  notWC := hNotWC
                  PleH := PleH_subgroupOf_residual hH
                  o2H := o2H_subgroupOf_residual hH hHle
                  notLe := notLe_subgroupOf_residual hH hV hHle
                  min := min_subgroupOf_residual hH hV hHle
                    (P_le_pResidual hH hZ hnKeep) }
              wcQ := weaklyClosedIn_subgroupOf_residual hH hV }
          data := hData
          degenerate := hDeg }
      q_two := hQtwo
      three := hThree
      centre := le_commutator_of_mulEquiv eX hH.centre
      tilde := hTilde
      concl := hConcl
      module := hModule }

theorem ntQEOutResidualStatement_of_fields
    (hFields : ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G),
      TwoEndHyp M V Q P H →
      Subgroup.center (Xbar V H) = ⊥ →
      (∃ n : ℕ, 3 ≤ n ∧
        Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
      P.relIndex Q = 2 →
      (∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) →
      generalizedFitting (M.subgroupOf (pResidual 2 G)) =
        pCore 2 (M.subgroupOf (pResidual 2 G)) ∧
      ¬ WeaklyClosedIn (V.subgroupOf (pResidual 2 G))
          (M.subgroupOf (pResidual 2 G)) ∧
      Sec23Data (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      (∀ d ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
        ∀ e ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
          orderOf (d * e) ≠ 4) ∧
      qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) = 2 ∧
      Sec23Three (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      Sec24bTilde (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
        (P.subgroupOf (pResidual 2 G)) ∧
      Sec25Concl (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
        (P.subgroupOf (pResidual 2 G)) ∧
      Nat.card ↥(V.subgroupOf (pResidual 2 G) ⊓
          wOf (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))) =
        qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
      Nonempty (Xbar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ≃*
        Xbar V H)) :
    NTQEOutResidualStatement :=
  ntQEOutResidualStatement_of_max hFields

end CFSG.RankThree.GF2n.Tim79a
