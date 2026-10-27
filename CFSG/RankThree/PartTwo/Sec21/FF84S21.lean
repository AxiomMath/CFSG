module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
import CFSG.RankThree.PartTwo.Sec21.HeringFFLRank
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.RankThree.PartTwo.Sec21.HeringFFLInner
import CFSG.RankThree.PartTwo.Sec21.HeringFFLTransfer
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
import CFSG.RankThree.GF2n.Tim81.Sec4.ListBridges
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Walter.W67.W1Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

@[expose] def FF79TheoremA_simpleK4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G),
    IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
      FF79Hyp 4 b J → ConjInto b J

end CFSG.RankThree.PartTwo.Sec21.FF79

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian IsTwoLocal)
open CFSG.RankThree.PartTwo.Sec21.FF79 (FF79Hyp FF79_1_3 FF79TheoremA_simpleK FF79TheoremA_simpleK4)

variable {G : Type} [Group G]

private theorem comm_of_isPGroup_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hS : ∀ P : Sylow 3 H, IsCyclic ↥(P : Subgroup H)) {R : Subgroup H} (hR : IsPGroup 3 R)
    {r s : H} (hr : r ∈ R) (hs : s ∈ R) : r * s = s * r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  haveI := hS P
  exact congrArg Subtype.val
    ((inferInstance : IsMulCommutative ↥(P : Subgroup H)).is_comm.comm ⟨r, hRP hr⟩ ⟨s, hRP hs⟩)

private theorem mem_zpowers_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hS : ∀ P : Sylow 3 H, IsCyclic ↥(P : Subgroup H)) {u v : H} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (huv : Commute u v) :
    u ∈ Subgroup.zpowers v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hov : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hzu : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  have hzv : IsPGroup 3 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hov, pow_one])
  have hle : Subgroup.zpowers u ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup H) : Set H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact huv.symm.zpow_left k
  obtain ⟨P, hP⟩ := (IsPGroup.to_sup_of_normal_right' hzu hzv hle).exists_le_sylow
  haveI := hS P
  have hmu : u ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hmv : v ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hu' : orderOf (⟨u, hmu⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hou]
  have hv' : orderOf (⟨v, hmv⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hov]
  have heq : Subgroup.zpowers (⟨u, hmu⟩ : (P : Subgroup H)) =
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hu', hv'])
  have hmem : (⟨u, hmu⟩ : (P : Subgroup H)) ∈
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem ffStandardJ_of_cyc [Finite G] {b : G} {L : Subgroup G} (hord : orderOf b = 3)
    (hLC : L ≤ Cen b) (hLN : Cen b ≤ Nor L) (hLq : CFSG.IsQuasisimple L)
    (hcyc : FFCentCyclicSylow L) : FFStandardJ b L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : b ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one b
  have ha1 : b ≠ 1 := fun h => by simp [h] at hord
  have hXC : L ≤ Subgroup.centralizer ({b} : Set G) := hLC
  have hcyc' : ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)),
      IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (L : Set G))) := hcyc
  have hXnorm : (L.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).mpr hLN
  have hXcomp : CFSG.IsComponent (L.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXC) hLq,
      hXnorm.isSubnormal⟩
  unfold FFStandardJ
  set Cc : Subgroup G := Subgroup.centralizer ({b} : Set G)
  set D : Subgroup G := Subgroup.centralizer (L : Set G)
  refine ⟨hXC, hXcomp, fun K hK h3K => ?_⟩
  rcases CFSG.LocalCores.distinct_components_commute hK hXcomp with h | hcomm
  · exact h
  exfalso
  have hcomm' : ∀ k ∈ K, ∀ y ∈ L.subgroupOf Cc, y * k = k * y := fun k hk y hy =>
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk) y hy
  have hKD : ∀ k ∈ K, ((k : ↥Cc) : G) ∈ D := by
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    have hy' : (⟨y, hXC hy⟩ : ↥Cc) ∈ L.subgroupOf Cc := Subgroup.mem_subgroupOf.mpr hy
    exact congrArg Subtype.val (hcomm' k hk ⟨y, hXC hy⟩ hy')
  obtain ⟨xK, hxK⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  set x : G := ((xK : ↥Cc) : G) with hxdef
  have hxD : x ∈ D := hKD xK.1 xK.2
  have hxa : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp xK.1.2
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one xK
    rw [hxK] at h
    simpa [hxdef] using congrArg (fun z : ↥K => ((z : ↥Cc) : G)) h
  have hx1 : x ≠ 1 := by
    intro h
    have h' : xK = 1 := Subtype.ext (Subtype.ext (by simpa [hxdef] using h))
    rw [h', orderOf_one] at hxK
    norm_num at hxK
  have haCc : b ∈ Cc := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haD : b ∈ D := by
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXC hy)
  have hcommA : Commute (⟨b, haD⟩ : ↥D) (⟨x, hxD⟩ : ↥D) := by
    show (⟨b, haD⟩ : ↥D) * ⟨x, hxD⟩ = ⟨x, hxD⟩ * ⟨b, haD⟩
    exact Subtype.ext hxa.symm
  have hu3 : (⟨b, haD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hu1 : (⟨b, haD⟩ : ↥D) ≠ 1 := fun h => ha1 (by simpa using congrArg Subtype.val h)
  have hv3 : (⟨x, hxD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hv1 : (⟨x, hxD⟩ : ↥D) ≠ 1 := fun h => hx1 (by simpa using congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_cyclic_sylow hcyc' hu3 hu1 hv3 hv1 hcommA)
  have hxk : x ^ k = b := by simpa using congrArg Subtype.val hk
  have haK : (⟨b, haCc⟩ : ↥Cc) ∈ K := by
    have he : (⟨b, haCc⟩ : ↥Cc) = (xK : ↥Cc) ^ k :=
      Subtype.ext (by simpa [hxdef] using hxk.symm)
    rw [he]
    exact zpow_mem xK.2 k
  have haK3 : (⟨⟨b, haCc⟩, haK⟩ : ↥K) ^ 3 = 1 :=
    Subtype.ext (Subtype.ext (by simpa using ha3))
  have haK1 : (⟨⟨b, haCc⟩, haK⟩ : ↥K) ≠ 1 := fun h =>
    ha1 (by simpa using congrArg (fun z : ↥K => ((z : ↥Cc) : G)) h)
  have haKc : (⟨⟨b, haCc⟩, haK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.1.2
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  have hPab : ∀ y ∈ (P : Subgroup ↥K), ∀ z ∈ (P : Subgroup ↥K), y * z = z * y := by
    let φ : ↥K →* ↥D := (Cc.subtype.comp K.subtype).codRestrict D (fun k => hKD k.1 k.2)
    have hφ : Function.Injective φ := fun u v huv =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥D => (z : G)) huv))
    have hR : IsPGroup 3 ((P : Subgroup ↥K).map φ) := P.isPGroup'.map φ
    intro y hy z hz
    apply hφ
    rw [map_mul, map_mul]
    exact comm_of_isPGroup_of_cyclic_sylow hcyc' hR (Subgroup.mem_map_of_mem φ hy)
      (Subgroup.mem_map_of_mem φ hz)
  have hz1 := eq_one_of_mem_center_of_abelian_sylow hK.1.1 P hPab haKc haK3
  exact haK1 hz1

private theorem ker_conj_eq_center' {X : Type*} [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := congrArg (fun φ : MulAut X => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]

private theorem card_le_three_of_cyclic_sylow {Y : Type} [Group Y] [Finite Y]
    (hcyc : ∀ S : Sylow 3 Y, IsCyclic ↥(S : Subgroup Y)) {A : Subgroup Y}
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨S, hS⟩ := hAp.exists_le_sylow
  haveI := hcyc S
  haveI : IsCyclic A := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hS).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
  exact Subtype.ext (by simpa using hA.2 g g.2)

private theorem card_le_27 [Finite G] {L : Subgroup G} (hq : CFSG.IsQuasisimple L)
    (hmod : IsTypeLnq 4 2 1 L) (hcyc : FFCentCyclicSylow L) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hEN : E ≤ Nor L) : Nat.card E ≤ 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.RankThree.GF2n.Tim81.nonempty_mulEquiv_alternating_eight_of_psl4_model hmod
  have hInn : Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range = 20160 := by
    have h1 := Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : ↥L →* MulAut ↥L)).toEquiv
    rw [ker_conj_eq_center'] at h1
    rw [← h1, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  set ρ : ↥E →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hρ
  have hρapp : ∀ (g : ↥E) (y : ↥L), ((ρ g y : ↥L) : G) = (g : G) * y * (g : G)⁻¹ := fun g y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hEN g) y
  have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hle : ρ.range ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨x, hx, hc⟩ := exists_mem_inv_mul_mem_centralizer_of_odd hq (Or.inl rfl) hmod
      (hEN g.2) (m := 3) (by decide) (by simpa using hE.2 g g.2)
    refine ⟨⟨x, hx⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
    rw [MulAut.conj_apply, hρapp]
    have hcy : (x : G)⁻¹ * g * y = y * ((x : G)⁻¹ * g) :=
      (Subgroup.mem_centralizer_iff.mp hc y y.2).symm
    have : (g : G) = x * ((x : G)⁻¹ * g) := by group
    show (x : G) * y * (x : G)⁻¹ = (g : G) * y * (g : G)⁻¹
    calc (x : G) * y * (x : G)⁻¹ = x * (y * ((x : G)⁻¹ * g)) * (g : G)⁻¹ := by group
      _ = x * ((x : G)⁻¹ * g * y) * (g : G)⁻¹ := by rw [hcy]
      _ = g * y * (g : G)⁻¹ := by group
  have hrange : Nat.card ρ.range ≤ 9 := by
    have hp : IsPGroup 3 ρ.range := hE3.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card ρ.range ∣ 20160 := hInn ▸ Subgroup.card_dvd_of_le hle
    rw [hn] at hdvd ⊢
    by_contra hlt
    have h3n : 3 ≤ n := by
      by_contra h
      have : n ≤ 2 := by omega
      have h9 : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      exact hlt (by simpa using h9)
    have : 3 ^ 3 ∣ 20160 := (pow_dvd_pow 3 h3n).trans hdvd
    norm_num at this
  have hker : Nat.card ρ.ker ≤ 3 := by
    set kerE : Subgroup G := ρ.ker.map E.subtype with hkerE
    have hkE : kerE ≤ E := Subgroup.map_subtype_le _
    have hkD : kerE ≤ Subgroup.centralizer (L : Set G) := by
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have := hρapp g ⟨y, hy⟩
      rw [(MonoidHom.mem_ker.mp hg : ρ g = 1)] at this
      simp only [MulAut.one_apply] at this
      show y * (g : G) = (g : G) * y
      calc y * (g : G) = (g * y * (g : G)⁻¹) * g := by rw [← this]
        _ = g * y := by group
    have hcard : Nat.card ρ.ker = Nat.card kerE := by
      rw [hkerE, Subgroup.card_map_of_injective E.subtype_injective]
    have hT : IsElemAbelian 3 (kerE.subgroupOf (Subgroup.centralizer (L : Set G))) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨x, hx⟩ := x
        obtain ⟨y, hy⟩ := y
        have hx' : (x : G) ∈ kerE := hx
        have hy' : (y : G) ∈ kerE := hy
        have := hE.1.is_comm.comm ⟨(x : G), hkE hx'⟩ ⟨(y : G), hkE hy'⟩
        exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥E => (z : G)) this))
      · exact Subtype.ext (by simpa using hE.2 x (hkE hx))
    have hcT : Nat.card (kerE.subgroupOf (Subgroup.centralizer (L : Set G))) = Nat.card kerE :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkD).toEquiv
    rw [hcard, ← hcT]
    exact card_le_three_of_cyclic_sylow hcyc hT
  have hcardE := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at hcardE
  rw [hcardE]
  calc Nat.card ρ.range * Nat.card ρ.ker ≤ 9 * 3 := Nat.mul_le_mul hrange hker
    _ = 27 := by norm_num

private theorem false_of_central_three {X : Type} [Group X] [Finite X]
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center X)) (e : X) (he : e ∈ Subgroup.center X)
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let z : ↥(Subgroup.center X) := ⟨e, he⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext he3
  have hz1 : z ≠ 1 := fun h => he1 (congrArg (fun w : ↥(Subgroup.center X) => (w : X)) h)
  exact hZ3 ((orderOf_eq_prime hz3 hz1) ▸ orderOf_dvd_natCard z)

private theorem exists_e27 [Finite G] {b : G} {L : Subgroup G} (hord : orderOf b = 3)
    (hLC : L ≤ Cen b) (hq : CFSG.IsQuasisimple L) (hmod : IsTypeLnq 4 2 1 L)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    ∃ K V : Subgroup ↥(Cen b), IsElemAbelian 3 K ∧ Nat.card K = 27 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      K ≤ Subgroup.normalizer (V : Set ↥(Cen b)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, V₀, hE₀, hE₀9, hV₀, hV₀2, hE₀V₀⟩ := fFKE9_holds ↥L hq hZ3 (Or.inl hmod)
  have ha3 : b ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one b
  have ha1 : b ≠ 1 := fun h => by simp [h] at hord
  have haC : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set a' : ↥(Cen b) := ⟨b, haC⟩ with ha'def
  have ha'C : a' ∈ Subgroup.center ↥(Cen b) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hZc : Subgroup.zpowers a' ≤ Subgroup.center ↥(Cen b) := Subgroup.zpowers_le.mpr ha'C
  have ha'3 : a' ^ 3 = 1 := Subtype.ext ha3
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hZcard : Nat.card (Subgroup.zpowers a') = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha'3 ha'1]
  have hZab : IsElemAbelian 3 (Subgroup.zpowers a') := CFSG.Open.isElemAbelian_zpowers ha'3
  set ι : ↥L →* ↥(Cen b) := Subgroup.inclusion hLC with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective hLC
  set E : Subgroup ↥(Cen b) := E₀.map ι with hE
  set V : Subgroup ↥(Cen b) := V₀.map ι with hV
  have hEab : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hE₀ ι
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective hιinj]
    exact hE₀9
  have hVne : V ≠ ⊥ := fun h => hV₀ ((Subgroup.map_eq_bot_iff_of_injective V₀ hιinj).mp h)
  have hV2 : IsPGroup 2 V := hV₀2.map ι
  have hEN : E ≤ Subgroup.normalizer (V : Set ↥(Cen b)) :=
    (Subgroup.map_mono hE₀V₀).trans (Subgroup.le_normalizer_map ι)
  have hZN : Subgroup.zpowers a' ≤ Subgroup.normalizer (V : Set ↥(Cen b)) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp ha'C h))
  have hdisj : ∀ x ∈ E, x ∈ Subgroup.zpowers a' → x = 1 := by
    rintro x hxE hxZ
    obtain ⟨e, he, rfl⟩ := hxE
    by_contra hne
    have hec : e ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hZc hxZ) (ι k))
      exact h
    exact false_of_central_three hZ3 e hec (hE₀.2 e he)
      (fun h => hne (by rw [h, map_one]))
  have hcomm : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers a', x * y = y * x :=
    fun x _ y hy => Subgroup.mem_center_iff.mp (hZc hy) x
  obtain ⟨K, hKN, hKab, hKcard⟩ :=
    exists_elemAbelian_card_mul (N := Subgroup.normalizer (V : Set ↥(Cen b))) hEab hZab hEN hZN
      hcomm hdisj
  exact ⟨K, V, hKab, by rw [hKcard, hE9, hZcard], hVne, hV2, hKN⟩

private theorem localRank_eq_pRank [Finite G] {b : G} {L : Subgroup G} (hord : orderOf b = 3)
    (hLC : L ≤ Cen b) (hLN : Cen b ≤ Nor L) (hq : CFSG.IsQuasisimple L)
    (hmod : IsTypeLnq 4 2 1 L) (hcyc : FFCentCyclicSylow L)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    localRank 3 ↥(Cen b) = CFSG.Open.pRank 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, V, hKab, hK27, hVne, hV2, hKN⟩ := exists_e27 hord hLC hq hmod hZ3
  have hbd : ∀ E : Subgroup ↥(Cen b), IsElemAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have h := card_le_27 hq hmod hcyc (E := E.map (Cen b).subtype)
      (CFSG.Open.IsElemAbelian.map hE _)
      (by
        rintro _ ⟨y, _, rfl⟩
        exact hLN y.2)
    rwa [Subgroup.card_map_of_injective (Cen b).subtype_injective] at h
  have hle3 : ∀ E : Subgroup ↥(Cen b), IsElemAbelian 3 E → ∀ k, Nat.card E = 3 ^ k → k ≤ 3 := by
    intro E hE k hk
    have := hbd E hE
    rw [hk] at this
    by_contra hlt
    have h4 : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbddG := CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
    (Cen b)
  have hK' : IsElemAbelian 3 (K.map (Cen b).subtype) := CFSG.Open.IsElemAbelian.map hKab _
  have hK'card : Nat.card (K.map (Cen b).subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (Cen b).subtype_injective, hK27]; norm_num
  have hp1 : CFSG.Open.pRank 3 (Cen b) ≤ 3 := by
    refine csSup_le' ?_
    rintro k ⟨E, hEC, hE, hk⟩
    exact hle3 (E.subgroupOf (Cen b)) (CFSG.Open.IsElemAbelian.subgroupOf hE (Cen b)) k
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]; exact hk)
  have hp2 : 3 ≤ CFSG.Open.pRank 3 (Cen b) :=
    le_csSup hbddG ⟨_, Subgroup.map_subtype_le K, hK', hK'card⟩
  have hl1 : localRank 3 ↥(Cen b) ≤ 3 := by
    refine csSup_le' ?_
    rintro k ⟨H, -, rfl⟩
    refine csSup_le' ?_
    rintro j ⟨E, -, hE, hj⟩
    exact hle3 E hE j hj
  have hl2 : 3 ≤ localRank 3 ↥(Cen b) := by
    have hH2 : IsTwoLocal (Subgroup.normalizer (V : Set ↥(Cen b))) := ⟨V, hVne, hV2, rfl⟩
    have hp3 : 3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (V : Set ↥(Cen b))) :=
      le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
        (Subgroup.normalizer (V : Set ↥(Cen b)))) ⟨K, hKN, hKab, by rw [hK27]; norm_num⟩
    have hbdd : BddAbove {k | ∃ H : Subgroup ↥(Cen b), IsTwoLocal H ∧
        CFSG.Open.pRank 3 H = k} := by
      refine ⟨3, ?_⟩
      rintro _ ⟨H, -, rfl⟩
      refine csSup_le' ?_
      rintro j ⟨E, -, hE, hj⟩
      exact hle3 E hE j hj
    exact hp3.trans (le_csSup hbdd ⟨_, hH2, rfl⟩)
  omega

theorem ff79Hyp_four_of_ff84Hyp [Finite G] {b : G} {L : Subgroup G}
    (h : FF84Hyp b L) : FF79Hyp 4 b L := by
  obtain ⟨e⟩ := CFSG.RankThree.GF2n.Tim81.nonempty_mulEquiv_alternating_eight_of_psl4_model h.model
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := fun h3 => by
    have := h3.trans (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_two_of_eight
      h.quasi e)
    omega
  exact
    { ord := h.ord
      std := ffStandardJ_of_cyc h.ord h.hLC h.hLN h.quasi h.cyc
      model := h.model
      cyc := h.cyc
      nsc := h.nsc
      rank := h.rank.trans (localRank_eq_pRank h.ord h.hLC h.hLN h.quasi h.model h.cyc hZ3) }

theorem ff84_2_1_of4
    (h13 : FF79_1_3) (hA : FF79TheoremA_simpleK4) : FF84_2_1 := by
  intro G _ _ b L hyp B hB
  have hF := ff79Hyp_four_of_ff84Hyp hyp
  have hconj := hA G b L hyp.simple hyp.nonab hyp.iii hF
  obtain ⟨hE27, hE9, hsup, hcase⟩ := h13 G 4 (Or.inl rfl) b L hF B hB
  rcases hcase with ⟨hnc, -⟩ | ⟨-, hfus, b₁, hb₁, b₂, hb₂, hmono⟩
  · exact absurd hconj hnc
  refine ⟨b₁, hb₁, b₂, hb₂, ?_, hmono, hfus⟩
  have hMle : Subgroup.closure ({b₁, b₂} : Set G) ≤ B ⊓ L :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hb₁, Set.singleton_subset_iff.mpr hb₂⟩)
  have hBcl : B = Subgroup.closure {b, b₁, b₂} := hmono.2.1
  have hbB : b ∈ B := hBcl ▸ Subgroup.subset_closure (by simp)
  have hord : orderOf b = 3 := hyp.ord
  have hB' : B ≤ Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂} : Set G) := by
    rw [hBcl, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  haveI := hE27.1
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set G),
      x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative ↥B).is_comm.comm
      ⟨x, Subgroup.zpowers_le.mpr hbB hx⟩ ⟨y, (hMle.trans inf_le_left) hy⟩)
  obtain ⟨hcs, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm
  have h27 : Nat.card B = 27 := by rw [hE27.2]; norm_num
  have h9 : Nat.card ↥(B ⊓ L) = 9 := by rw [hE9.2]; norm_num
  have h3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hord]
  have hBle : 27 ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂} : Set G)) :=
    h27 ▸ Subgroup.card_le_of_le hB'
  have hM : 9 ≤ Nat.card ↥(Subgroup.closure ({b₁, b₂} : Set G)) := by
    rw [h3] at hcs
    have hpos : 1 ≤ Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.closure ({b₁, b₂} : Set G)) :=
      Nat.card_pos
    have := Nat.mul_le_mul hBle hpos
    omega
  exact (Subgroup.eq_of_le_of_card_ge hMle (by rw [h9]; exact hM)).symm

end CFSG.RankThree.PartTwo.Sec21.FF84
