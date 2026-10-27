module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepBOne
public import CFSG.LocalAnalysis.StandardType.GGSporKStepZero
public import CFSG.LocalAnalysis.StandardType.GGSporKLayer
import CFSG.Walter.AStar.Subnormal
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem gkbf_isComponent_subgroupOf {W : Type} [Group W] {H : Subgroup W}
    {K : Subgroup W} (hK : IsComponentOf K H) : CFSG.IsComponent (K.subgroupOf H) := by
  have hsub : CFSG.Assembly.IsSubnormal (K.subgroupOf H) (⊤ : Subgroup ↥H) :=
    CFSG.Assembly.IsSubnormal.of_mathlib
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hK.1).mp hK.2.1)
  have hqs : CFSG.Assembly.IsQuasisimple ↥(K.subgroupOf H) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1) hK.2.2
  have hcomp : IsComponentOf (K.subgroupOf H) (⊤ : Subgroup ↥H) := ⟨le_top, hsub, hqs⟩
  exact (CFSG.isComponent_iff_open _).mpr (CFSG.Assembly.isComponentOf_iff_open.mp hcomp)

private theorem gkbf_eq_of_ne_one_of_card_two {M : Type*} [Group M] (hM : Nat.card M = 2)
    {a b : M} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  have hgen : b ∈ Submonoid.powers a := mem_powers_of_prime_card hM ha
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff b a).mp hgen
  have horder : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := by
      rw [← hM]
      exact orderOf_dvd_natCard a
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha
    · exact h
  have ha2 : a ^ 2 = 1 := by
    simpa [horder] using pow_orderOf_eq_one a
  have hmod : a ^ n = a ^ (n % 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    rw [pow_add, pow_mul, ha2, one_pow, one_mul]
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [hmod, h0, pow_zero] at hn
    exact absurd hn.symm hb
  · rw [hmod, h1] at hn
    simpa using hn

private theorem gkbf_normal_card_two_le_center {W : Type} [Group W] {C M : Subgroup W}
    (hCM : M ≤ C) (hMn : (M.subgroupOf C).Normal) (hMcard : Nat.card M = 2) :
    M ≤ Subgroup.centralizer (C : Set W) := by
  haveI : Nonempty M := ⟨⟨1, M.one_mem⟩⟩
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hconj : c * m * c⁻¹ ∈ M := by
    have h := hMn.conj_mem (⟨m, hCM hm⟩ : ↥C) (Subgroup.mem_subgroupOf.mpr hm) (⟨c, hc⟩ : ↥C)
    exact Subgroup.mem_subgroupOf.mp h
  have hcm : c * m * c⁻¹ = m := by
    by_cases hm1 : m = 1
    · rw [hm1, mul_one, mul_inv_cancel]
    · have hconj1 : c * m * c⁻¹ ≠ 1 := by
        intro h
        apply hm1
        have h' := congrArg (fun z => c⁻¹ * z * c) h
        simpa [mul_assoc] using h'
      have hEq := gkbf_eq_of_ne_one_of_card_two (M := ↥M) hMcard
          (a := (⟨c * m * c⁻¹, hconj⟩ : ↥M)) (b := (⟨m, hm⟩ : ↥M))
          (fun h => hconj1 (congrArg Subtype.val h)) (fun h => hm1 (congrArg Subtype.val h))
      exact congrArg Subtype.val hEq
  exact mul_inv_eq_iff_eq_mul.mp hcm

private theorem gkbf_isComponent_conj {W : Type} [Group W] {H : Subgroup W} {L : Subgroup W}
    (hL : IsComponentOf L H) {x : W} (hx : x ∈ H) :
    IsComponentOf (L.map (MulAut.conj x).toMonoidHom) H := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hxl : x * l * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx (hL.1 hl)) (H.inv_mem hx)
    simpa [MulAut.conj_apply] using hxl
  · have hmap := hL.2.1.map (MulAut.conj x).toMonoidHom
    have hfix : H.map (MulAut.conj x).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
    rwa [hfix] at hmap
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).symm hL.2.2

private theorem gkbf_center_card {W : Type} [Group W] {J : Subgroup W}
    (hJ : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set W)) = 2) :
    Nat.card (Subgroup.center ↥J) = 2 := by
  have hcenter : Subgroup.center ↥J =
      (J ⊓ Subgroup.centralizer (J : Set W)).subgroupOf J := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := (Subgroup.mem_center_iff.mp hx) ⟨y, hy⟩
      simpa using congrArg Subtype.val h1
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨-, hxZ⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := Subgroup.mem_centralizer_iff.mp hxZ (y : W) y.2
      apply Subtype.ext
      simpa using h1
  rw [hcenter]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact hJ

private theorem gkbf_inf_centralizer_le {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat 7 H E)
    {L : Subgroup W} (hL : IsComponentOf L H) (h7 : ¬ 7 ∣ Nat.card L) {a : W} (haE : a ∈ E)
    (ha1 : a ≠ 1) :
    L ⊓ Subgroup.centralizer {a} ≤ Subgroup.centralizer (E : Set W) := by
  haveI : Fact (Nat.Prime 7) := ⟨hyp.1.1⟩
  have hord : orderOf a = 7 := orderOf_eq_prime (hyp.1.2.2.1.2 a haE) ha1
  set C : Subgroup W := Subgroup.centralizer {a} with hCdef
  have hCH : C ≤ H := hyp.1.2.2.2.2.centralizer_le haE ha1
  have hsub : CFSG.Assembly.IsSubnormal (L ⊓ C) C := hL.2.1.inf_of_le hCH
  have hcop : ¬ 7 ∣ Nat.card ↥(L ⊓ C) := fun hd =>
    h7 (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hleO : ((L ⊓ C).subgroupOf C) ≤ CFSG.pPrimeCore 7 ↥C := by
    refine CFSG.StandardType.ggLe_pPrimeCore_of_isSubnormal ?_ ?_
    · exact hsub.subgroupOf
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hcop
  obtain ⟨J, hJcomp, -, hJcard, hJcore⟩ := ha a hord
  have hJcore' : CFSG.pPrimeCore 7 ↥C =
      (J ⊓ Subgroup.centralizer (J : Set W)).subgroupOf C := by
    simpa only [LargeEvenPPrimeCore] using hJcore
  have hleJ : L ⊓ C ≤ J ⊓ Subgroup.centralizer (J : Set W) := by
    intro x hx
    have hxC : (⟨x, hx.2⟩ : ↥C) ∈ (L ⊓ C).subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
    have hxJ := hleO hxC
    rw [hJcore'] at hxJ
    exact Subgroup.mem_subgroupOf.mp hxJ
  have hMleC : J ⊓ Subgroup.centralizer (J : Set W) ≤ C := inf_le_left.trans hJcomp.1
  have hMn : ((J ⊓ Subgroup.centralizer (J : Set W)).subgroupOf C).Normal := by
    rw [← hJcore']
    infer_instance
  have hMcent := gkbf_normal_card_two_le_center hMleC hMn hJcard
  have hEC : E ≤ C := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    haveI : IsMulCommutative E := hyp.1.2.2.1.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he⟩ : E) (⟨a, haE⟩ : E))
  exact hleJ.trans (hMcent.trans (Subgroup.centralizer_le hEC))

private theorem gkbf_component_le_centralizer {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat 7 H E)
    (h2 : CFSG.pCore 2 ↥H = ⊥) {L : Subgroup W} (hL : IsComponentOf L H)
    (h7 : ¬ 7 ∣ Nat.card L) : L ≤ Subgroup.centralizer (E : Set W) := by
  haveI : Fact (Nat.Prime 7) := ⟨hyp.1.1⟩
  have hEnormData : ∀ e ∈ E, ∀ x ∈ L, e * x * e⁻¹ ∈ L :=
    (ggSporK_component_data hyp h2 hL).1
  have hEnorm : E ≤ Subgroup.normalizer (L : Set W) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff'']
    intro r
    constructor
    · intro hr
      simpa using hEnormData e⁻¹ (E.inv_mem he) r hr
    · intro hr
      have h := hEnormData e he (e⁻¹ * r * e) hr
      have heq : e * (e⁻¹ * r * e) * e⁻¹ = r := by group
      rwa [heq] at h
  haveI : IsElementaryAbelian 7 E :=
    { toIsMulCommutative := hyp.1.2.2.1.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        simpa using hyp.1.2.2.1.2 (x : W) x.2 }
  letI : MulDistribMulAction E ↥L :=
    MulDistribMulAction.compHom L (L.normalizerMonoidHom.comp (Subgroup.inclusion hEnorm))
  have hact : ∀ (a : E) (x : ↥L), ((a • x : ↥L) : W) = (a : W) * (x : W) * (a : W)⁻¹ :=
    fun _ _ => rfl
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 7) (A := E) (H := ↥L)
    (by rw [hyp.1.2.2.2.1]) h7
  have htop : (Subgroup.centralizer (E : Set W)).comap L.subtype = ⊤ := by
    rw [eq_top_iff]
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun hne => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have h2' : (a : W) * (x : W) * (a : W)⁻¹ = (x : W) := by
      simpa [hact a x] using congrArg (fun z : ↥L => (z : W)) h1
    have hax : (a : W) * (x : W) = (x : W) * (a : W) := mul_inv_eq_iff_eq_mul.mp h2'
    have hmem : (x : W) ∈ L ⊓ Subgroup.centralizer ({(a : W)} : Set W) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hax.symm⟩
    exact gkbf_inf_centralizer_le ha hb hyp hL h7 a.2 (fun h => hne (Subtype.ext h)) hmem
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥L) ∈ (Subgroup.centralizer (E : Set W)).comap L.subtype := by
    rw [htop]
    trivial
  simpa using Subgroup.mem_comap.mp hx'

private theorem gkbf_seven_dvd_card {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat 7 H E)
    (h2 : CFSG.pCore 2 ↥H = ⊥) (hP' : LargeEvenPPrimeCore 7 ↥H = ⊥)
    (hP : CFSG.pCore 7 ↥H = ⊥) {L : Subgroup W} (hL : IsComponentOf L H) :
    7 ∣ Nat.card L := by
  by_contra h7
  have hle := gkbf_component_le_centralizer ha hb hyp h2 hL h7
  obtain ⟨-, hnonab⟩ := ggSporK_components_simple hP' hP hL
  obtain ⟨a, b, hab⟩ := hnonab
  have hEcard : Nat.card E = 49 := by rw [hyp.1.2.2.2.1]; norm_num
  refine hab ?_
  apply Subtype.ext
  exact hb E hyp.1.2.2.1 hEcard (a : W) (hle a.2) (b : W) (hle b.2)

private theorem gkbf_factorization_seven_eq_two {W : Type} [Group W] [Finite W]
    {H E : Subgroup W} (hEH : E ≤ H) (hEcard : Nat.card E = 49)
    (h49 : (Nat.card W).factorization 7 = 2) : (Nat.card H).factorization 7 = 2 := by
  have h7p : Nat.Prime 7 := by norm_num
  haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
  haveI : Nonempty W := ⟨1⟩
  have hHne : Nat.card H ≠ 0 := (Nat.card_pos (α := ↥H)).ne'
  have hWne : Nat.card W ≠ 0 := (Nat.card_pos (α := W)).ne'
  have hge : 2 ≤ (Nat.card H).factorization 7 := by
    have hdvdE : Nat.card E ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
    have hdvd : 7 ^ 2 ∣ Nat.card H := by
      rwa [show (7 : ℕ) ^ 2 = Nat.card E by rw [hEcard]; norm_num]
    exact (h7p.pow_dvd_iff_le_factorization hHne).mp hdvd
  have hle : (Nat.card H).factorization 7 ≤ 2 := by
    have hdvd : Nat.card H ∣ Nat.card W := by
      simpa using Subgroup.card_dvd_of_le (le_top : H ≤ (⊤ : Subgroup W))
    have hle' : (Nat.card H).factorization 7 ≤ (Nat.card W).factorization 7 :=
      (Nat.factorization_le_iff_dvd hHne hWne).mpr hdvd 7
    omega
  omega

private theorem gkbf_components_unique {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (h49 : (Nat.card W).factorization 7 = 2) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 7 H E) (hP' : LargeEvenPPrimeCore 7 ↥H = ⊥)
    (hP : CFSG.pCore 7 ↥H = ⊥) (h2 : CFSG.pCore 2 ↥H = ⊥) {L : Subgroup W}
    (hL : IsComponentOf L H) (h7L : 7 ∣ Nat.card L) :
    ∀ C : Subgroup W, IsComponentOf C H → C = L := by
  haveI : Fact (Nat.Prime 7) := ⟨hyp.1.1⟩
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  have hfac : (Nat.card ↥H).factorization 7 = 2 :=
    gkbf_factorization_seven_eq_two hEH (by rw [hyp.1.2.2.2.1]; norm_num) h49
  have hcard' : Nat.card (E.subgroupOf H) = 7 ^ (Nat.card ↥H).factorization 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hfac, hyp.1.2.2.2.1]
  let E' : Sylow 7 ↥H := Sylow.ofCard (E.subgroupOf H) hcard'
  have hE'map : (E' : Subgroup ↥H).map H.subtype = E := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.map_subgroupOf_eq_of_le hEH
  intro C hC
  rcases CFSG.LocalCores.distinct_components_commute (gkbf_isComponent_subgroupOf hC)
      (gkbf_isComponent_subgroupOf hL) with heq | hcomm
  · have hinf := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hC.1, inf_eq_left.mpr hL.1] at hinf
  · exfalso
    have hLsub : (L.subgroupOf H).IsSubnormal := hL.2.1.subgroupOf
    have h7L' : 7 ∣ Nat.card (L.subgroupOf H) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.1).toEquiv]
      exact h7L
    have hne : (E' : Subgroup ↥H) ⊓ L.subgroupOf H ≠ ⊥ :=
      CFSG.Walter.sylow_inf_ne_bot_of_isSubnormal E' hLsub h7L'
    obtain ⟨w, hw, hw1⟩ :
        ∃ w : ↥H, w ∈ (E' : Subgroup ↥H) ⊓ L.subgroupOf H ∧ w ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one ((E' : Subgroup ↥H) ⊓ L.subgroupOf H) with hb | hex
      · exact absurd hb hne
      · exact hex
    set z : W := (w : W) with hzdef
    have hzE : z ∈ E := by
      have hwE' : w ∈ (E' : Subgroup ↥H) := (Subgroup.mem_inf.mp hw).1
      have hmem : (w : W) ∈ (E' : Subgroup ↥H).map H.subtype := Subgroup.mem_map_of_mem _ hwE'
      rw [hE'map] at hmem
      simpa [z] using hmem
    have hzL : z ∈ L := by
      have hwL : w ∈ L.subgroupOf H := (Subgroup.mem_inf.mp hw).2
      have hmem : (w : W) ∈ L := Subgroup.mem_subgroupOf.mp hwL
      simpa [z] using hmem
    have hz1 : z ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hzord : orderOf z = 7 := orderOf_eq_prime (hyp.1.2.2.1.2 z hzE) hz1
    have hcle : C.subgroupOf H ≤
        Subgroup.centralizer (L.subgroupOf H : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hCw : C ≤ Subgroup.centralizer ({z} : Set W) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcH : (⟨c, hC.1 hc⟩ : ↥H) ∈ C.subgroupOf H := Subgroup.mem_subgroupOf.mpr hc
      have hzH : (⟨z, hL.1 hzL⟩ : ↥H) ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.mpr hzL
      have h1 := Subgroup.mem_centralizer_iff.mp (hcle hcH) (⟨z, hL.1 hzL⟩ : ↥H) hzH
      exact (congrArg Subtype.val h1).symm
    have hCcomp : IsComponentOf C (Subgroup.centralizer {z}) :=
      hC.of_le_of_le hCw (hyp.1.2.2.2.2.centralizer_le hzE hz1)
    obtain ⟨J, hJcomp, hJuniq, hJcard, -⟩ := ha z hzord
    have hCJ : C = J := hJuniq C hCcomp
    obtain ⟨hCsimple, hnonab⟩ := ggSporK_components_simple hP' hP hC
    rw [hCJ] at hCsimple hnonab
    have hcentercard : Nat.card (Subgroup.center ↥J) = 2 := gkbf_center_card hJcard
    have hcenterne : Subgroup.center ↥J ≠ ⊥ := by
      intro hbot
      rw [hbot] at hcentercard
      have : (1 : ℕ) = 2 := by simpa using hcentercard
      omega
    have hcentertop : Subgroup.center ↥J = ⊤ :=
      (hCsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J)).resolve_left hcenterne
    obtain ⟨a, b, hab⟩ := hnonab
    have hmem : a ∈ Subgroup.center ↥J := by rw [hcentertop]; trivial
    exact hab (Subgroup.mem_center_iff.mp hmem b).symm

theorem ggSporK_layer_simple_B {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) (h49 : (Nat.card W).factorization 7 = 2) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 7 H E) (hP' : LargeEvenPPrimeCore 7 ↥H = ⊥)
    (hP : CFSG.pCore 7 ↥H = ⊥) (hJ : ∃ J : Subgroup W, IsComponentOf J H) :
    ∃ L : Subgroup W, IsComponentOf L H ∧ IsSimpleGroup ↥L ∧
      (∀ C : Subgroup W, IsComponentOf C H → C = L) ∧ H ⊓ Subgroup.centralizer (L : Set W) = ⊥ ∧
      H ≤ Subgroup.normalizer (L : Set W) := by
  obtain ⟨L, hL⟩ := hJ
  have h2 : CFSG.pCore 2 ↥H = ⊥ := ggSporK_pCore_two_eq_bot hyp.1.1 hyp.1.2.1 hP'
  have hsimple : IsSimpleGroup ↥L := (ggSporK_components_simple hP' hP hL).1
  have hseven : 7 ∣ Nat.card L := gkbf_seven_dvd_card ha hb hyp h2 hP' hP hL
  have huniq : ∀ C : Subgroup W, IsComponentOf C H → C = L :=
    gkbf_components_unique ha h49 hyp hP' hP h2 hL hseven
  refine ⟨L, hL, hsimple, huniq, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx1 : x = 1 :=
      ggSporK_eq_one_of_centralizes_components hP' hP hxH fun J hJ y hy => by
        have hJL : J = L := huniq J hJ
        rw [hJL] at hy
        exact (Subgroup.mem_centralizer_iff.mp hxC y hy).symm
    rwa [Subgroup.mem_bot]
  · intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact huniq (L.map (MulAut.conj x).toMonoidHom) (gkbf_isComponent_conj hL hx)

end CFSG.StandardType.SporadicShape
