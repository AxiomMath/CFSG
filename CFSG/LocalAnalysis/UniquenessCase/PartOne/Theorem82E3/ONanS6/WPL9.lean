module

public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K3)
variable {G : Type} [Group G] [Finite G] {D : Data G}

noncomputable abbrev thetaCen_wPL9 (e : G) : Subgroup G :=
  Subgroup.centralizer ({e} : Set G)

noncomputable abbrev thetaCore_wPL9 (e : G) : Subgroup (thetaCen_wPL9 e) :=
  aschbacherSolvableCore 3 ↥(thetaCen_wPL9 e)

noncomputable abbrev thetaQuot_wPL9 (e : G) : Type :=
  ↥(thetaCen_wPL9 e) ⧸ thetaCore_wPL9 e

noncomputable abbrev thetaMap_wPL9 (e : G) : thetaCen_wPL9 e →* thetaQuot_wPL9 e :=
  QuotientGroup.mk' (thetaCore_wPL9 e)

theorem thetaComponent_le_cen_wPL9 {e : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 e) : L ≤ thetaCen_wPL9 e := by
  obtain ⟨L₀, -, rfl⟩ := hL
  exact Subgroup.map_subtype_le L₀

theorem thetaComponent_isSubnormal_wPL9 {e : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 e) : (L.subgroupOf (thetaCen_wPL9 e)).IsSubnormal := by
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  have hEq : (L₀.map (thetaCen_wPL9 e).subtype).subgroupOf (thetaCen_wPL9 e) = L₀ := by
    apply Subgroup.map_injective (thetaCen_wPL9 e).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact Subgroup.map_subtype_le L₀
  rw [hEq]
  exact hL₀.2.1

theorem zSub_le_thetaCen_wPL9 (c : Ctx82E3 D) {P : Subgroup G} {e : G}
    (he : e ∈ P ⊓ c.L) : zSub P c.L ≤ thetaCen_wPL9 e := by
  intro z hz
  rw [thetaCen_wPL9, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm

theorem inSubgroup_core_le_core_wPL9 {e : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 e) :
    inSubgroup (aschbacherSolvableCore 3) L ≤
      (thetaCore_wPL9 e).map (thetaCen_wPL9 e).subtype := by
  rw [CFSG.RankThree.GroupTheory.inSubgroup_core_eq_inf_of_subgroupOf_isSubnormal Nat.prime_three
    (thetaComponent_le_cen_wPL9 hL) (thetaComponent_isSubnormal_wPL9 hL)]
  exact inf_le_right

theorem thetaMap_conj_eq_of_autThetaQuot_bot_wPL9
    (c : Ctx82E3 D) {P : Subgroup G} {e : G} (he : e ∈ P ⊓ c.L)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 e)
    {z : G} (hzZ : z ∈ zSub P c.L)
    (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (haut : autThetaQuot (zSub P c.L) L = ⊥) (l : L) :
    thetaMap_wPL9 e (Subgroup.inclusion (thetaComponent_le_cen_wPL9 hL)
        ((L.normalizerMonoidHom ⟨z, hzN⟩) l)) =
      thetaMap_wPL9 e (Subgroup.inclusion (thetaComponent_le_cen_wPL9 hL) l) := by
  classical
  have hLK : L ≤ thetaCen_wPL9 e := thetaComponent_le_cen_wPL9 hL
  let σ : MulAut L := L.normalizerMonoidHom ⟨z, hzN⟩
  have hmem : thetaQuotMulAut L σ ∈ autThetaQuot (zSub P c.L) L :=
    mem_autThetaQuot_iff.mpr ⟨z, hzN, hzZ, rfl⟩
  have hτ : thetaQuotMulAut L σ = 1 := by
    have hbot : thetaQuotMulAut L σ ∈ (⊥ : Subgroup (MulAut (L ⧸
        aschbacherSolvableCore 3 L))) := by simpa [haut] using hmem
    simpa using (Subgroup.mem_bot.mp hbot)
  have hq : (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (σ l) =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) l := by
    have h := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
      τ ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)) l)) hτ
    simpa [thetaQuotMulAut_mk] using h
  have hmemθL : σ l * l⁻¹ ∈ aschbacherSolvableCore 3 L := by
    have h1 : (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (σ l * l⁻¹) = 1 := by
      rw [map_mul, map_inv, hq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 L)
      (σ l * l⁻¹)).mp h1
  have hmemθK : ((σ l * l⁻¹ : L) : G) ∈
      (thetaCore_wPL9 e).map (thetaCen_wPL9 e).subtype :=
    inSubgroup_core_le_core_wPL9 hL (Subgroup.mem_map_of_mem L.subtype hmemθL)
  have hx : thetaMap_wPL9 e (Subgroup.inclusion hLK (σ l * l⁻¹)) = 1 := by
    rw [thetaMap_wPL9, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hmemK : ((Subgroup.inclusion hLK (σ l * l⁻¹) : thetaCen_wPL9 e) : G) ∈
        (thetaCore_wPL9 e).map (thetaCen_wPL9 e).subtype := by
      simpa [Subgroup.inclusion] using hmemθK
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmemK
    have hy_eq : y = Subgroup.inclusion hLK (σ l * l⁻¹) := Subtype.ext hyx
    simpa [hy_eq] using hy
  rw [map_mul, map_inv] at hx
  exact eq_of_mul_inv_eq_one hx

theorem centralizer_zSub_le_normalizer_twoCore_wPL9
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (he : e ∈ P ⊓ c.L) :
    Subgroup.centralizer (((zSub P c.L).subgroupOf (thetaCen_wPL9 e)) : Set (thetaCen_wPL9 e)) ≤
      Subgroup.normalizer (((thetaCen_wPL9 e ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
        (thetaCen_wPL9 e)) : Set (thetaCen_wPL9 e)) := by
  classical
  let K : Subgroup G := thetaCen_wPL9 e
  let Z : Subgroup G := zSub P c.L
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let W : Subgroup G := K ⊓ O
  have hZK : Z ≤ K := zSub_le_thetaCen_wPL9 c he
  have hZcard : Nat.card Z = 3 := by
    simpa [Z] using c.card_inf_centralizer_of_onan hON hP
  have hZne : Z ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZcard
    norm_num at hZcard
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥Z)
  have hzZ : (z : G) ∈ Z := z.2
  have hzK : (z : G) ∈ K := hZK hzZ
  have hzne : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzord : orderOf (z : G) = 3 := by
    have hdvd : orderOf (z : G) ∣ 3 := by
      simpa [hZcard] using Subgroup.orderOf_dvd_natCard Z hzZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hzne
    · exact h3
  have hzgen : Subgroup.zpowers (z : G) = Z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) (by
      rw [Nat.card_zpowers, hzord, hZcard])
  have hkey : ∀ y : ↥(thetaCen_wPL9 e), y ∈
      Subgroup.centralizer (((zSub P c.L).subgroupOf (thetaCen_wPL9 e)) : Set (thetaCen_wPL9 e)) →
      ∀ w : ↥(thetaCen_wPL9 e), w ∈ ((thetaCen_wPL9 e ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
        (thetaCen_wPL9 e)) → y * w * y⁻¹ ∈ ((thetaCen_wPL9 e ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
          (thetaCen_wPL9 e)) := by
    intro y hy w hw
    have hyM : (y : G) ∈ D.M := by
      have hycent : (y : G) ∈ Subgroup.centralizer (Z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have htK : t ∈ K := hZK ht
        have hcomm := (Subgroup.mem_centralizer_iff.mp hy) ⟨t, htK⟩
          (Subgroup.mem_subgroupOf.mpr ht)
        exact congrArg Subtype.val hcomm
      have hycent' : (y : G) ∈
          Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have htZ : t ∈ Z := Subgroup.zpowers_le.mpr hzZ ht
        exact (Subgroup.mem_centralizer_iff.mp hycent) t htZ
      have hyN : (y : G) ∈ Subgroup.normalizer (Z : Set G) := by
        have h := Subgroup.centralizer_le_normalizer
          (Subgroup.zpowers (z : G) : Set G) hycent'
        simpa [hzgen] using h
      exact hNZ hyN
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
    rw [Subgroup.mem_subgroupOf]
    refine ⟨K.mul_mem (K.mul_mem y.2 (hwW.1)) (K.inv_mem y.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M hyM) (w : G)).mp hwW.2
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr ?_
  intro w
  constructor
  · intro hw
    exact hkey x hx w hw
  · intro hxw
    have hinv : x⁻¹ ∈ Subgroup.centralizer
        (((zSub P c.L).subgroupOf (thetaCen_wPL9 e)) : Set (thetaCen_wPL9 e)) :=
      (Subgroup.centralizer _).inv_mem hx
    have h := hkey x⁻¹ hinv (x * w * x⁻¹) hxw
    rw [inv_inv, show x⁻¹ * (x * w * x⁻¹) * x = w by group] at h
    exact h

theorem exists_E27_frame_at_wPL9
    (hK3 : K3) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      e ∈ A ∧ A ≤ P ⊓ c.L ∧ zSub P c.L ≤ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := P ⊓ c.L
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let QL : Subgroup ↥c.L := Q.subgroupOf c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective O)
  have hScoe : (S : Subgroup c.Lbar) = QL.map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  obtain ⟨hScard, hSexp, hScenter, hScomm⟩ := hK3 c.Lbar hON S
  let f : ↥QL →* c.Lbar := π.comp QL.subtype
  have hdisj : QL ⊓ O = ⊥ := by
    have hQ3 : IsPGroup 3 QL := hQsyl.isPGroup.comap_subtype
    have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) QL O hQ3 hO2).eq_bot
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : QuotientGroup.mk' O (x : ↥c.L) = 1 := hx
    have hxO : (x : ↥c.L) ∈ O := (QuotientGroup.eq_one_iff (N := O) (x : ↥c.L)).mp hx'
    have hxbot : (x : ↥c.L) ∈ (⊥ : Subgroup ↥c.L) := by
      rw [← hdisj]
      exact ⟨x.2, hxO⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  let eQL₀ : ↥QL ≃* ↥f.range := MonoidHom.ofInjective hf_inj
  have hrange : f.range = (S : Subgroup c.Lbar) := by
    rw [hScoe]
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eQL : ↥QL ≃* ↥S := eQL₀.trans (MulEquiv.subgroupCongr hrange)
  let eQ : ↥Q ≃* ↥S :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ≤ c.L)).symm.trans eQL
  have hcardQ : Nat.card ↥Q = 3 ^ 5 := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hScard
  have hexpQ : ∀ x : ↥Q, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    exact c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (x : G) x.2
  have hZS : Nat.card (Subgroup.center ↥S) = 3 := by
    have hmap := CFSG.center_map_subtype_eq_inf_centralizer (S : Subgroup c.Lbar)
    calc Nat.card (Subgroup.center ↥S)
        = Nat.card ↥((Subgroup.center ↥(S : Subgroup c.Lbar)).map
            (S : Subgroup c.Lbar).subtype) :=
          (Subgroup.card_map_of_injective (S : Subgroup c.Lbar).subtype_injective).symm
      _ = Nat.card ↥((S : Subgroup c.Lbar) ⊓
            Subgroup.centralizer ((S : Subgroup c.Lbar) : Set c.Lbar)) := by rw [hmap]
      _ = 3 := hScenter
  have hcommS_eq : commutator ↥S = Subgroup.center ↥S := by
    apply Subgroup.map_injective (S : Subgroup c.Lbar).subtype_injective
    calc Subgroup.map (S : Subgroup c.Lbar).subtype (commutator ↥S)
        = ⁅(S : Subgroup c.Lbar), (S : Subgroup c.Lbar)⁆ := by
          exact Subgroup.map_subtype_commutator (S : Subgroup c.Lbar)
      _ = (S : Subgroup c.Lbar) ⊓
            Subgroup.centralizer ((S : Subgroup c.Lbar) : Set c.Lbar) := hScomm
      _ = Subgroup.map (S : Subgroup c.Lbar).subtype (Subgroup.center ↥S) :=
          (CFSG.center_map_subtype_eq_inf_centralizer (S : Subgroup c.Lbar)).symm
  have hZQ : Nat.card (Subgroup.center ↥Q) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eQ).toEquiv, hZS]
  have hcommQ : commutator ↥Q ≤ Subgroup.center ↥Q := by
    have hcenter_map : (Subgroup.center ↥Q).map eQ.toMonoidHom = Subgroup.center ↥S := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr eQ ⟨y, hy⟩).2
      · intro x hx
        refine ⟨eQ.symm x, ?_, eQ.apply_symm_apply x⟩
        exact ((Subgroup.centerCongr eQ).symm ⟨x, hx⟩).2
    have hmapcomm : (commutator ↥Q).map eQ.toMonoidHom = commutator ↥S := by
      rw [show commutator ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ from rfl, Subgroup.map_commutator]
      rw [show commutator ↥S = ⁅(⊤ : Subgroup ↥S), ⊤⁆ from rfl]
      simp
    have hle : (commutator ↥Q).map eQ.toMonoidHom ≤
        (Subgroup.center ↥Q).map eQ.toMonoidHom := by
      rw [hmapcomm, hcenter_map, hcommS_eq]
    exact (Subgroup.map_le_map_iff_of_injective eQ.injective).mp hle
  have haZ : (⟨e, he⟩ : ↥Q) ∉ Subgroup.center ↥Q := by
    intro hcen
    have hmem : e ∈ (Subgroup.center ↥Q).map Q.subtype :=
      Subgroup.mem_map.mpr ⟨⟨e, he⟩, hcen, rfl⟩
    rw [CFSG.center_map_subtype_eq_inf_centralizer Q] at hmem
    exact heZ (by simpa [Q, zSub] using hmem)
  obtain ⟨E, -, haE, hEea, hE27⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_of_index_le_three
      (R := ↥Q) hcardQ hexpQ hZQ hcommQ (H := ⊤) (by simp) (a := ⟨e, he⟩)
      (Subgroup.mem_top _) haZ
  let A : Subgroup G := E.map Q.subtype
  have hAea : CFSG.Open.IsElemAbelian 3 A := hEea.map Q.subtype
  have hA27 : Nat.card A = 27 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hE27]
  have heA : e ∈ A := Subgroup.mem_map.mpr ⟨⟨e, he⟩, haE, rfl⟩
  have hAPL : A ≤ P ⊓ c.L := by
    simpa [A, Q] using Subgroup.map_subtype_le (H := Q) E
  have hZcard : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hZcent : zSub P c.L ≤ Subgroup.centralizer ((zSub P c.L : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (⟨x, hx⟩ : ↥(zSub P c.L)).2.2 (y : G) hy.1
  have hZcomm : IsMulCommutative ↥(zSub P c.L) :=
    (Subgroup.le_centralizer_iff_isMulCommutative).mp hZcent
  have hZea : CFSG.Open.IsElemAbelian 3 (zSub P c.L) :=
    ⟨hZcomm, fun x hx =>
      c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP x hx.1⟩
  have hcommAZ : ∀ x ∈ A, ∀ y ∈ zSub P c.L, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (⟨y, hy⟩ : ↥(zSub P c.L)).2.2 (x : G) (hAPL hx)
  have hZA : zSub P c.L ≤ A := by
    by_contra hnot
    have hinf : A ⊓ zSub P c.L = ⊥ := by
      have hdvd : Nat.card ↥(A ⊓ zSub P c.L) ∣ 3 := by
        rw [← hZcard]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hnot
        have heq : A ⊓ zSub P c.L = zSub P c.L :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
        exact heq ▸ inf_le_left
    have hsupEa : CFSG.Open.IsElemAbelian 3 (A ⊔ zSub P c.L) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hAea hZea hcommAZ
    have hcardSup : Nat.card ↥(A ⊔ zSub P c.L) = 81 := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A (zSub P c.L)
        hcommAZ).1
      rw [hinf, Subgroup.card_bot, hA27, hZcard] at h
      simpa using h
    have hsupM : (A ⊔ zSub P c.L) ≤ D.M := by
      have hAcent : A ≤ Subgroup.centralizer ((zSub P c.L : Subgroup G) : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (⟨y, hy⟩ : ↥(zSub P c.L)).2.2
          (x : G) (hAPL hx)).symm
      exact (sup_le hAcent hZcent).trans
        ((Subgroup.centralizer_le_normalizer ((zSub P c.L : Subgroup G) : Set G)).trans hNZ)
    obtain ⟨k, hk⟩ := hsupEa.isPGroup.exists_card_eq
    have hk_le : k ≤ CFSG.Open.pRank 3 D.M :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hsupM hsupEa hk
    rw [c.pRank_three_M] at hk_le
    have hk4 : k = 4 := by
      have h34 : 3 ^ k = 3 ^ 4 := by
        rw [← hk, hcardSup]
        norm_num
      exact Nat.pow_right_injective (by norm_num : 1 < 3) h34
    omega
  exact ⟨A, hAea, hA27, heA, hAPL, hZA⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
