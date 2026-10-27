module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129SPAbs
public import CFSG.RankThree.PartTwo.Sec12.Hering129SPSpor
public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec12.Hering129SP
open scoped commutatorElement

theorem not_three_dvd_of_isSLThreePiAt' {X : Type} [Group X] {m : ℕ}
    (h : Sec4.IsSLThreePiAt X m) : ¬ 3 ∣ m := by
  obtain ⟨K, _, _, h⟩ := h
  rcases h with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;> omega

theorem gap129YSporadic_of
    (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus) : Gap129YSporadic := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb Y hY hXY X' _ hX' ⟨eT⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime hx3 hx1) h hb1 (Subgroup.mem_zpowers b))
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hYperf : Group.IsPerfect ↥Y := Sec6.isPerfect_of_mem_thetaComponentsAt hYx
  have hW : SporLocal X' := sporLocal_of_equiv hX'
  have e0 : (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) ≃* X' :=
    equivOfCommutatorTop hW.simple hW.nonabelian eT
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) := hAN hbA
  let β : MulAut ↥Y := Y.normalizerMonoidHom ⟨b, hbN⟩
  have hβ : ∀ y : ↥Y, ((β y : ↥Y) : G) = b * (y : G) * b⁻¹ := fun y => rfl
  have hβ3 : β ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hβnt : ∃ y : ↥Y, y⁻¹ * β y ∉ aschbacherSolvableCore 3 ↥Y := by
    by_contra hcon
    push_neg at hcon
    have hbQ : b ∈ Sec4.thetaQuotCentralizer Y := by
      rw [Sec6.mem_thetaQuotCentralizer_iff]
      refine ⟨hbN, fun l hl => ?_⟩
      exact ⟨_, hcon ⟨l, hl⟩, by simp [hβ]⟩
    have hbAQ : b ∈ A ⊓ Sec4.thetaQuotCentralizer Y := ⟨hbA, hbQ⟩
    rw [hAC] at hbAQ
    exact hbx hbAQ
  set UG : Subgroup G := inSubgroup (aschbacherSolvableCore 3) Y with hUG
  have hUGle : UG ≤ Y := by rintro _ ⟨u, -, rfl⟩; exact u.2
  have hUGθ : UG ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G)) := by
    rw [hUG, Sec6.theta_eq_inf_of_mem_thetaComponentsAt hYx]
    exact inf_le_right
  have hAU : ∀ g ∈ A, ∀ u ∈ UG, g * u * g⁻¹ ∈ UG := by
    intro g hg u hu
    obtain ⟨u', hu', rfl⟩ := hu
    have hgN : g ∈ Subgroup.normalizer (Y : Set G) := hAN hg
    let γ : MulAut ↥Y := Y.normalizerMonoidHom ⟨g, hgN⟩
    exact ⟨γ u', (mem_theta_iff γ u').2 hu', rfl⟩
  have hRle : ⁅UG, A⁆ ≤ UG := by
    rw [Subgroup.commutator_le]
    intro u hu g hg
    have : ⁅u, g⁆ = u * (g * u⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact UG.mul_mem hu (hAU g hg u⁻¹ (UG.inv_mem hu))
  have hRodd_G : Odd (Nat.card (⁅UG, A⁆ : Subgroup G)) :=
    (cfg.mem_S.2.1 x hxA hx1).of_dvd_nat
      (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hUGθ le_rfl))
  have hconj : ∀ u ∈ UG, ∀ r ∈ ⁅UG, A⁆, u * r * u⁻¹ ∈ ⁅UG, A⁆ := by
    intro u hu
    have hle : ⁅UG, A⁆ ≤ (⁅UG, A⁆).comap (MulAut.conj u).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro v hv a ha
      rw [Subgroup.mem_comap]
      have h1 : (MulAut.conj u).toMonoidHom ⁅v, a⁆ = ⁅u * v, a⁆ * ⁅u, a⁆⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]; group
      rw [h1]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hu hv) ha)
        (inv_mem (Subgroup.commutator_mem_commutator hu ha))
    intro r hr
    exact hle hr
  let R : Subgroup ↥Y := (⁅UG, A⁆).subgroupOf Y
  have hRle' : ⁅UG, A⁆ ≤ Y := hRle.trans hUGle
  have hRU : R ≤ aschbacherSolvableCore 3 ↥Y := by
    intro r hr
    have hr' : (r : G) ∈ ⁅UG, A⁆ := hr
    obtain ⟨t, ht, hte⟩ := hRle hr'
    have : t = r := Subtype.ext hte
    rwa [← this]
  have hRn : ∀ u ∈ aschbacherSolvableCore 3 ↥Y, ∀ r ∈ R, u * r * u⁻¹ ∈ R := by
    intro u hu r hr
    have hu' : (u : G) ∈ UG := ⟨u, hu, rfl⟩
    have hr' : (r : G) ∈ ⁅UG, A⁆ := hr
    show ((u * r * u⁻¹ : ↥Y) : G) ∈ ⁅UG, A⁆
    simpa using hconj _ hu' _ hr'
  have hRodd : Odd (Nat.card R) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle').toEquiv]
    exact hRodd_G
  have hR : ∀ u ∈ aschbacherSolvableCore 3 ↥Y, u⁻¹ * β u ∈ R := by
    intro u hu
    have hu' : (u : G) ∈ UG := ⟨u, hu, rfl⟩
    have h : ((u⁻¹ * β u : ↥Y) : G) = ⁅(u : G)⁻¹, b⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ, commutatorElement_def]; group
    show ((u⁻¹ * β u : ↥Y) : G) ∈ ⁅UG, A⁆
    rw [h]
    exact Subgroup.commutator_mem_commutator (UG.inv_mem hu') hbA
  let Mfix : Subgroup ↥Y := (Y ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf Y
  have hMfix : ∀ y : ↥Y, y ∈ Mfix ↔ β y = y := by
    intro y
    show (y : G) ∈ Y ⊓ Subgroup.centralizer ({b} : Set G) ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hβ, ← h]
      group
    · intro h
      refine ⟨y.2, ?_⟩
      have h' := congrArg Subtype.val h
      rw [hβ] at h'
      calc (y : G) * b = (b * (y : G) * b⁻¹) * b := by rw [h']
        _ = b * y := by group
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXK : resCent K x ≤ K := (resCent_le K x).trans inf_le_left
  let XY : Subgroup ↥Y := (resCent K x).subgroupOf Y
  let eXY : ↥XY ≃* ↥(resCent K x) := Subgroup.subgroupOfEquivOfLe hXY
  have hXM : XY ≤ Mfix := by
    intro y hy
    rw [hMfix]
    apply Subtype.ext
    have hyK : (y : G) ∈ K := hXK hy
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hKb hyK)
    rw [hβ, ← h]
    group
  haveI : Group.IsPerfect ↥(resCent K x) := isPerfect_resCent K x
  have hXp : Group.IsPerfect ↥XY :=
    Group.IsPerfect.ofSurjective (f := eXY.symm.toMonoidHom) eXY.symm.surjective
  have hXM' : resCent K x ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hXY (hXK.trans hKb)
  have hXsubG := resCent_isSubnormal cfg.hK inf_le_right (inf_le_left.trans hYle) hXM'
  let ιM : ↥Mfix →* ↥(Y ⊓ Subgroup.centralizer ({b} : Set G)) :=
    (Y.subtype.comp Mfix.subtype).codRestrict _ (fun z => z.2)
  have hXsub : (XY.subgroupOf Mfix).IsSubnormal := by
    have h := hXsubG.comap ιM
    have heq : ((resCent K x).subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set G))).comap ιM =
        XY.subgroupOf Mfix := by
      ext z
      exact Iff.rfl
    rwa [heq] at h
  obtain ⟨-, -, δ, hGK, hδ13, F, hFf, hFfin, hFcard, φK, hφK, hkerK⟩ :=
    exists_sl2_quotient_of_fix hTL hCen G A c L b a K S cfg q hq x hxD hxb
  obtain ⟨hq4, hq2, -⟩ := hCen.2 G A c L b a K S cfg q hq
  haveI : Finite F := Finite.of_fintype F
  have hq3card : ¬ 3 ∣ q.card := not_three_dvd_of_isSLThreePiAt' hq.1
  have hF3 : ¬ 3 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    exact fun h => hq3card (Nat.prime_three.dvd_of_dvd_pow h)
  have hδpos : 1 ≤ δ := by rcases hδ13 with rfl | rfl <;> norm_num
  have hF4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    exact hq4.trans (Nat.le_self_pow (by omega) _)
  let φK' : ↥XY →* Matrix.SpecialLinearGroup (Fin 2) F := φK.comp eXY.toMonoidHom
  have hφK' : Function.Surjective φK' := hφK.comp eXY.surjective
  have hkerK' : φK'.ker ≤ aschbacherSolvableCore 3 ↥XY := by
    intro z hz
    have h1 : eXY z ∈ φK.ker := hz
    have h2 := hkerK h1
    have h3 := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eXY
    rw [← h3] at h2
    obtain ⟨z', hz', hz'e⟩ := h2
    have : z' = z := eXY.injective hz'e
    rwa [← this]
  exact no_sporadic_cover hYperf hW e0 β hβ3 hβnt R hRU hRn hRodd hR Mfix hMfix XY hXp hXM
    hXsub hF4 hF3 φK' hφK' hkerK'

end CFSG.RankThree.PartTwo.Sec12
