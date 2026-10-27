module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarImageCalC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.Quasithin.EmptyFaithful.S151S5A
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.WeakClosure81.InFMulEquiv
public import CFSG.LocalAnalysis.WeakClosure81.InFSqSymThree
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable def barSubActHom {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hXS : X ≤ stabTil V₀ V) : ↥X →* ↥(barSub V₀ V hV X) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hXS)).codRestrict
    (barSub V₀ V hV X) (fun x => actTil_mem_barSub V₀ V hV x.2 (hXS x.2))

theorem barSubActHom_surjective {V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXS : X ≤ stabTil V₀ V) : Function.Surjective (barSubActHom hV hXS) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨a, haX, rfl⟩ := (mem_barSub V₀ V hV X ψ).1 hψ
  exact ⟨⟨a, haX⟩, rfl⟩

theorem inFSq_one_barSub_of_bar2_perm_three {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {H : Subgroup G} (hHM : H ≤ D.M)
    (h : Nonempty (UC22.Bar2 H ≃* Equiv.Perm (Fin 3))) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (barSub V₀ V hV.isElemAbelian H) := by
  classical
  obtain ⟨e⟩ := h
  have hV' := hV.isElemAbelian
  have hHS : H ≤ stabTil V₀ V :=
    hHM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  let φ : ↥H →* ↥(barSub V₀ V hV' H) := barSubActHom hV' hHS
  have hφ : Function.Surjective φ := barSubActHom_surjective hV' hHS
  let ψ : ↥H →* Bar2 (barSub V₀ V hV' H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(barSub V₀ V hV' H))).comp φ
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp hφ
  have hcore : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H := by
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hIle : ((pCoreOf 2 H).subgroupOf H).map φ ≤
      CFSG.pCore 2 ↥(barSub V₀ V hV' H) := by
    refine CFSG.LieType.BorelTits.le_pCore 2 ?_ ?_
    · rw [hcore]
      exact (CFSG.pCore_normal (p := 2) (G := ↥H)).map φ hφ
    · rw [hcore]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map φ
  have hO2H : CFSG.pCore 2 ↥H ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxsub : x ∈ (pCoreOf 2 H).subgroupOf H := by
      rw [hcore]
      exact hx
    have hxI : φ x ∈ ((pCoreOf 2 H).subgroupOf H).map φ :=
      Subgroup.mem_map_of_mem φ hxsub
    exact (QuotientGroup.eq_one_iff (φ x)).mpr (hIle hxI)
  let θ : Bar2 H →* Bar2 (barSub V₀ V hV' H) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥H) ψ hO2H
  have hθ : Function.Surjective θ := by
    intro q
    obtain ⟨x, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hcardH : Nat.card (Bar2 H) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    norm_num
  by_cases hKp : IsPGroup 2 θ.ker
  · have hKbot : θ.ker = ⊥ := by
      have hle := CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker θ) hKp
      rw [pCore_two_bar2_eq_bot H] at hle
      exact bot_unique hle
    let eθ : Bar2 H ≃* Bar2 (barSub V₀ V hV' H) :=
      MulEquiv.ofBijective θ ⟨(MonoidHom.ker_eq_bot_iff θ).mp hKbot, hθ⟩
    exact inFSq_one_of_bar2_perm_three (barSub V₀ V hV' H)
      ⟨eθ.symm.trans e⟩
  · have hdvd : Nat.card θ.ker ∣ 6 := by
      rw [← hcardH]
      exact Subgroup.card_subgroup_dvd_card θ.ker
    have hcardrel : Nat.card (Bar2 (barSub V₀ V hV' H)) * Nat.card θ.ker = 6 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
      rw [hcardH, Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv] at h1
      exact h1.symm
    have hKle : Nat.card θ.ker ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hKpos : 0 < Nat.card θ.ker := Nat.card_pos
    interval_cases hK : Nat.card θ.ker
    · exact absurd (IsPGroup.of_card (n := 0) (by rw [hK]; norm_num)) hKp
    · exact absurd (IsPGroup.of_card (n := 1) (by rw [hK]; norm_num)) hKp
    · have hQ2 : Nat.card (Bar2 (barSub V₀ V hV' H)) = 2 := by omega
      have hQp : IsPGroup 2 (Bar2 (barSub V₀ V hV' H)) :=
        IsPGroup.of_card (n := 1) (by rw [hQ2]; norm_num)
      have htop : CFSG.pCore 2 (Bar2 (barSub V₀ V hV' H)) = ⊤ :=
        le_antisymm le_top (CFSG.LieType.BorelTits.le_pCore 2 inferInstance
          (hQp.to_subgroup ⊤))
      have hbot := pCore_two_bar2_eq_bot (barSub V₀ V hV' H)
      rw [htop] at hbot
      have hcard1 : Nat.card (Bar2 (barSub V₀ V hV' H)) = 1 := by
        have := congrArg (fun S : Subgroup (Bar2 (barSub V₀ V hV' H)) => Nat.card S) hbot
        simpa using this
      omega
    · norm_num at hdvd
    · norm_num at hdvd
    · have hQ1 : Nat.card (Bar2 (barSub V₀ V hV' H)) = 1 := by omega
      exact inFSq_of_odd_card_bar2 1 (barSub V₀ V hV' H) (by rw [hQ1]; norm_num)

theorem fIndexSum_le_ncard_of_inFSq_one {Γ : Type} [Group Γ] [Finite Γ]
    {Δ : Set (Subgroup Γ)} (hfin : Δ.Finite)
    (h : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H) :
    fIndexSum Δ ≤ (Δ.ncard : ℕ∞) := by
  classical
  rw [fIndexSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ H ∈ hfin.toFinset, fIndex H
      ≤ ∑ H ∈ hfin.toFinset, (1 : ℕ∞) := by
        refine Finset.sum_le_sum fun H hH => ?_
        exact fIndex_le_iff.mpr (h H ((Set.Finite.mem_toFinset hfin).mp hH))
    _ = (hfin.toFinset.card : ℕ∞) := by simp
    _ = (Δ.ncard : ℕ∞) := by rw [Set.ncard_eq_toFinset_card Δ hfin]

theorem nonempty_bar2_barSub_equiv_of_le_sup_T {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hZ : Subgroup.center (UC22.Bar2 L) = ⊥) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    {H : Subgroup G} (hH : H ≤ L ⊔ D.T) :
    Nonempty (UC22.Bar2 H ≃* UC22.Bar2 (barSub V₀ V hV.isElemAbelian H)) := by
  classical
  have hV' := hV.isElemAbelian
  let N : Subgroup G := L ⊔ D.T
  have hLN : L ≤ N := le_sup_left
  have hTN : D.T ≤ N := le_sup_right
  have hNM : N ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hNS : N ≤ stabTil V₀ V :=
    hNM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hHS : H ≤ stabTil V₀ V := hH.trans hNS
  have hsub : CFSG.Open.IsSubnormal L N :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hNM
  let J : Subgroup (Bar2 N) := UC22.barImage N L
  let S : Subgroup (Bar2 N) := UC22.barImage N D.T
  have hJcomp : CFSG.IsComponent J := by
    simpa [J, N] using barImage_component_of_calC hL
  have hJz : ∀ x ∈ J, (∀ y ∈ J, y * x = x * y) → x = 1 := by
    intro x hx hxc
    obtain ⟨eJ, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_bar2Equiv
      (L := N) (K := L) le_sup_left hsub
    obtain ⟨a, ha⟩ := eJ.surjective ⟨x, hx⟩
    have hxcomm : ∀ y ∈ J, y * (eJ a : Bar2 N) = (eJ a : Bar2 N) * y := by
      intro y hy
      simpa [ha] using hxc y hy
    have hca : a ∈ Subgroup.center (UC22.Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply eJ.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (hxcomm (eJ b) (eJ b).2)
    rw [hZ, Subgroup.mem_bot] at hca
    have hxA : x = (eJ a : Bar2 N) := (congrArg Subtype.val ha).symm
    rw [hxA]
    simp [hca]
  have hS : IsPGroup 2 ↥(UC22.barImage N D.T) := by
    change IsPGroup 2 ↥((D.T.subgroupOf N).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥N)))
    exact (D.sylowM.isPGroup.comap_subtype).map _
  have hgen : J ⊔ S = ⊤ := by
    have h := PartTwo.s13_barImage_sup (M := N) (A := L) (B := D.T)
      le_sup_left le_sup_right
    rw [show L ⊔ D.T = N from rfl, PartTwo.s13_barImage_self] at h
    simpa [J, S, UC22.barImage] using h.symm
  have hO : CFSG.pCore 2 (Bar2 N) = ⊥ := pCore_two_bar2_eq_bot N
  let CK : Subgroup G := (actTil V₀ V hV').ker.map (stabTil V₀ V).subtype
  have hCKle : CK ≤ stabTil V₀ V := Subgroup.map_subtype_le _
  have hCKsub : CK.subgroupOf (stabTil V₀ V) = (actTil V₀ V hV').ker := by
    rw [show CK = (actTil V₀ V hV').ker.map (stabTil V₀ V).subtype from rfl]
    exact Subgroup.comap_map_eq_self_of_injective (stabTil V₀ V).subtype_injective _
  have hCKnorm : (CK.subgroupOf (stabTil V₀ V)).Normal := by
    rw [hCKsub]
    exact MonoidHom.normal_ker _
  have hstabCK : stabTil V₀ V ≤ Subgroup.normalizer (CK : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCKle).mp hCKnorm
  have hNCK : N ≤ Subgroup.normalizer (CK : Set G) := hNS.trans hstabCK
  let K : Subgroup G := N ⊓ CK
  have hKnormal : (K.subgroupOf N).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact N.mul_mem (N.mul_mem m.2 hn.1) (N.inv_mem m.2)
    · have hconj := (Subgroup.mem_normalizer_iff.mp (hNCK m.2) (n : G)).mp hn.2
      simpa using hconj
  let Nimg : Subgroup (Bar2 N) :=
    (K.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))
  have hNimgNormal : Nimg.Normal :=
    hKnormal.map _ (QuotientGroup.mk'_surjective _)
  have hcases : J ≤ Nimg ∨ Nimg = ⊥ :=
    CFSG.Quasithin.S151S5.component_le_or_normal_eq_bot hJcomp hJz hS hgen hO hNimgNormal
  have hnot : ¬ J ≤ Nimg := by
    intro hJN
    have hbarLe : barSub V₀ V hV' L ≤ barSub V₀ V hV' (pCoreOf 2 N) := by
      rintro φ hφ
      obtain ⟨l, hlL, rfl⟩ := (mem_barSub V₀ V hV' L φ).1 hφ
      have hlN : (l : G) ∈ N := hLN hlL
      let lN : ↥N := ⟨l, hlN⟩
      have hqJ : (QuotientGroup.mk lN : Bar2 N) ∈ J :=
        Subgroup.mem_map.mpr ⟨lN, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩
      have hqN : (QuotientGroup.mk lN : Bar2 N) ∈ Nimg := hJN hqJ
      obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hqN
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hkCK : (k : G) ∈ CK := hkK.2
      obtain ⟨y, hyker, hyval⟩ := Subgroup.mem_map.mp hkCK
      have hkact : actTil V₀ V hV' ⟨(k : G), hNS k.2⟩ = 1 := by
        have hy : (⟨(k : G), hNS k.2⟩ : ↥(stabTil V₀ V)) = y :=
          Subtype.ext (by simpa using hyval.symm)
        rw [hy]
        exact MonoidHom.mem_ker.mp hyker
      have hkq' : (QuotientGroup.mk k : Bar2 N) = QuotientGroup.mk lN := hkq
      have hq1 : (QuotientGroup.mk (k⁻¹ * lN) : Bar2 N) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hkq']
        group
      have hkP : ((k : G)⁻¹ * (l : G)) ∈ pCoreOf 2 N := by
        have hmem : (k⁻¹ * lN : ↥N) ∈ CFSG.pCore 2 ↥N :=
          (QuotientGroup.eq_one_iff _).mp hq1
        exact ⟨_, hmem, rfl⟩
      let kS : ↥(stabTil V₀ V) := ⟨(k : G), hNS k.2⟩
      have hmemS : ((kS⁻¹ * l : ↥(stabTil V₀ V)) : G) ∈ pCoreOf 2 N := by
        simpa [kS] using hkP
      have htarget : actTil V₀ V hV' l = actTil V₀ V hV' (kS⁻¹ * l) := by
        have hl : l = kS * (kS⁻¹ * l) := by group
        conv_lhs => rw [hl]
        rw [map_mul, hkact, one_mul]
      rw [htarget]
      exact actTil_mem_barSub V₀ V hV' hmemS (kS⁻¹ * l).2
    have h2O2 : IsPGroup 2 ↥(barSub V₀ V hV' (pCoreOf 2 N)) := by
      change IsPGroup 2 ↥(((pCoreOf 2 N).subgroupOf (stabTil V₀ V)).map
        (actTil V₀ V hV'))
      exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).comap_subtype).map
        (actTil V₀ V hV')
    have h2L : IsPGroup 2 ↥(barSub V₀ V hV' L) := by
      have hle : barSub V₀ V hV' L ≤ barSub V₀ V hV' (pCoreOf 2 N) := hbarLe
      have hsub2 : IsPGroup 2 ↥((barSub V₀ V hV' L).subgroupOf
          (barSub V₀ V hV' (pCoreOf 2 N))) :=
        h2O2.to_subgroup _
      exact hsub2.of_equiv (Subgroup.subgroupOfEquivOfLe hle)
    have hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV' L) :=
      (barSub_mem_compBar_of_ne_bot hV hL hL1).2.2
    have : Nontrivial ↥(barSub V₀ V hV' L) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hL1
    have : Group.IsPerfect ↥(barSub V₀ V hV' L) := ⟨hq.1⟩
    exact Group.IsPerfect.not_isNilpotent _ h2L.isNilpotent
  have hNimg_bot : Nimg = ⊥ := by
    rcases hcases with hle | hbot
    · exact absurd hle hnot
    · exact hbot
  have hKleO : K ≤ pCoreOf 2 N := by
    intro k hk
    have hkN : k ∈ N := hk.1
    have hksub : (⟨k, hkN⟩ : ↥N) ∈ K.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have hkmem : (QuotientGroup.mk ⟨k, hkN⟩ : Bar2 N) ∈ Nimg :=
      Subgroup.mem_map_of_mem _ hksub
    rw [hNimg_bot, Subgroup.mem_bot] at hkmem
    have hpk : (⟨k, hkN⟩ : ↥N) ∈ CFSG.pCore 2 ↥N :=
      (QuotientGroup.eq_one_iff _).mp hkmem
    exact ⟨_, hpk, rfl⟩
  have hK2 : IsPGroup 2 K := by
    intro x
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      ⟨(x : G), hKleO x.2⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  let φH : ↥H →* ↥(barSub V₀ V hV' H) := barSubActHom hV' hHS
  have hφH : Function.Surjective φH := barSubActHom_surjective hV' hHS
  have hCleK : (φH.ker).map H.subtype ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    have hy1 : φH y = 1 := by simpa using hy
    refine ⟨hH y.2, ?_⟩
    refine Subgroup.mem_map.mpr ⟨⟨(y : G), hHS y.2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hyval : ((φH y : ↥(barSub V₀ V hV' H)) : MulAut (Vtil V₀ V hV')) = 1 :=
      congrArg Subtype.val hy1
    change ((φH y : ↥(barSub V₀ V hV' H)) : MulAut (Vtil V₀ V hV')) = 1
    exact hyval
  have hker2 : IsPGroup 2 φH.ker := by
    intro x
    have hxmap : ((x : ↥H) : G) ∈ (φH.ker).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype x.2
    obtain ⟨n, hn⟩ := hK2 ⟨((x : ↥H) : G), hCleK hxmap⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker φH hφH hker2

theorem inFSq_barSub_of_le_sup_T {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hZ : Subgroup.center (UC22.Bar2 L) = ⊥) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    {H : Subgroup G} (hH : H ≤ L ⊔ D.T) {j : ℕ}
    (h : CFSG.LocalAnalysis.WeakClosure81.InFSq j H) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq j (barSub V₀ V hV.isElemAbelian H) := by
  obtain ⟨e⟩ := nonempty_bar2_barSub_equiv_of_le_sup_T hV hL hZ hL1 hH
  exact (inFSq_iff_bar2_inF_mulEquiv e j).mp h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
