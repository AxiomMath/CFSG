module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
import CFSG.Adapters.StatedPSLTwo
import CFSG.Quasithin.EmptyFaithful.SBd14Ind
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem a1413Adapt_mem_center_subgroup_iff {G : Type*} [Group G] {L : Subgroup G}
    (x : L) : x ∈ Subgroup.center L ↔ (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (h y y.2)

private theorem a1413Adapt_mem_fixV_zpowers_iff {V : Type*} [CommGroup V] {g : MulAut V}
    {v : V} : v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h x hx => ?_⟩
  have hg : g ∈ MulAction.stabilizer (MulAut V) v := MulAction.mem_stabilizer_iff.mpr h
  exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hg) hx)

private theorem a1413Adapt_zpow_eq_one_or_self {G : Type*} [Group G] {g : G}
    (hg : g * g = 1) (m : ℤ) : g ^ m = 1 ∨ g ^ m = g := by
  have hg2 : g ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]; exact hg
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, show k + k = 2 * k by ring, zpow_mul, hg2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hg2, one_zpow, one_mul, zpow_one]

private theorem a1413Adapt_mem_centralizer_of_conj_mem_centralizer {G : Type*} [Group G]
    {X : Subgroup G} [X.Normal] (hperf : Group.IsPerfect ↥X) {y : G}
    (hyN : y ∈ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (X : Set G)) :
    y ∈ Subgroup.centralizer (X : Set G) := by
  have hψ : conjAct X ⟨y, hyN⟩ = 1 := by
    apply CFSG.Quasithin.SBd14.eq_one_of_central_perfect hperf
    intro x
    rw [a1413Adapt_mem_center_subgroup_iff, Subgroup.coe_mul, Subgroup.coe_inv,
      CFSG.Quasithin.AutOn.coe_conjAct_apply]
    exact hcomm x x.2
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : G)) hψ
  simp only [MulAut.one_apply] at this
  rw [CFSG.Quasithin.AutOn.coe_conjAct_apply] at this
  have h1 : y * x = x * y := by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [this]
  exact h1.symm

private theorem a1413Adapt_commutatorElement_mul_central_left {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hcy : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
  rw [commutatorElement_def]
  rw [show (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ by group]
  rw [hcy]
  group

private theorem a1413Adapt_commutatorElement_mul_central_right {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, a1413Adapt_commutatorElement_mul_central_left hz,
    commutatorElement_inv]

private theorem a1413Adapt_commutator_sup_center_eq {G : Type*} [Group G] {Z X : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) [Z.Normal] : ⁅X ⊔ Z, X ⊔ Z⁆ = ⁅X, X⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨y, hy, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rw [a1413Adapt_commutatorElement_mul_central_left (hZ hz),
      a1413Adapt_commutatorElement_mul_central_right (hZ hz')]
    exact Subgroup.commutator_mem_commutator hx hy
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

private theorem a1413Adapt_le_of_perfect_le_sup_center {G : Type*} [Group G] {M Z : Subgroup G}
    (hperf : Group.IsPerfect G) (hZ : Z ≤ Subgroup.center G) [Z.Normal]
    (h : (⊤ : Subgroup G) ≤ M ⊔ Z) : (⊤ : Subgroup G) ≤ M := by
  have hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rw [← _root_.commutator_def (G := G)]; exact hperf.commutator_eq_top
  calc (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := hG.symm
    _ ≤ ⁅M ⊔ Z, M ⊔ Z⁆ := Subgroup.commutator_mono h h
    _ = ⁅M, M⁆ := a1413Adapt_commutator_sup_center_eq hZ (X := M)
    _ ≤ M := Subgroup.commutator_le_self M

private noncomputable def a1413Adapt_restrictAut {V : Type*} [CommGroup V] {U : Subgroup V}
    (g : stabSub U) : MulAut ↥U :=
  (MulEquiv.subgroupMap (g.1 : V ≃* V) U).trans
    (MulEquiv.subgroupCongr (map_eq_of_mem_stabSub g.2))

private theorem a1413Adapt_restrictAut_apply {V : Type*} [CommGroup V] {U : Subgroup V}
    (g : stabSub U) (u : ↥U) : (a1413Adapt_restrictAut g u : V) = g.1 u := rfl

private noncomputable def a1413Adapt_restrictHom {V : Type*} [CommGroup V] {U : Subgroup V}
    {M : Type*} [Group M] (f : M →* MulAut V) (h : ∀ m : M, f m ∈ stabSub U) :
    M →* MulAut ↥U where
  toFun m := a1413Adapt_restrictAut ⟨f m, h m⟩
  map_one' := by
    refine MulEquiv.ext (fun u => ?_)
    apply Subtype.ext
    rw [a1413Adapt_restrictAut_apply]
    simp
  map_mul' a b := by
    refine MulEquiv.ext (fun u => ?_)
    apply Subtype.ext
    show (f (a * b)) (u : V) = (f a) ((f b) (u : V))
    rw [map_mul, MulAut.mul_apply]

private theorem a1413Adapt_commV_zpowers_le_fixV {V : Type*} [CommGroup V]
    (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} (hg : g * g = 1) :
    commV (Subgroup.zpowers g) ≤ fixV (Subgroup.zpowers g) := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨h, hh, v, rfl⟩
  change h v * v⁻¹ ∈ fixV (Subgroup.zpowers g)
  rw [a1413Adapt_mem_fixV_zpowers_iff]
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rcases a1413Adapt_zpow_eq_one_or_self hg m with hm | hm
  · rw [hm]; simp
  · rw [hm]
    have hv1 : v * v = 1 := by simpa [pow_two] using hV v
    have hgv1 : g v * g v = 1 := by
      have := map_mul g v v
      rw [hv1, map_one] at this
      exact this.symm
    have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv1
    have hgvi : (g v)⁻¹ = g v := inv_eq_of_mul_eq_one_left hgv1
    calc g (g v * v⁻¹) = g (g v) * g (v⁻¹) := map_mul g _ _
      _ = v * (g v)⁻¹ := by
            rw [show g (g v) = v by rw [← MulAut.mul_apply, hg, MulAut.one_apply], map_inv]
      _ = v * g v := by rw [hgvi]
      _ = g v * v := mul_comm _ _
      _ = g v * v⁻¹ := by rw [hv]

private theorem a1413Adapt_apply (h64o : Asch6_4Odd) (h64s : Asch6_4Seven)
    {Q : Type} [Group Q] [Finite Q] {X A G : Subgroup Q} {z : Q}
    (hXG : X ≤ G) (hAG : A ≤ G) (hsup : G ≤ X ⊔ A)
    (hz2 : orderOf z = 2) (hzX : z ∈ X) (hXperf : ⁅X, X⁆ = X)
    (hZX : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) ↔ x ∈ zpowers z)
    (hzA : ∀ a ∈ A, a * z = z * a)
    (hXnormal : G ≤ Subgroup.normalizer (X : Set Q))
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hAC : ∀ a ∈ A, (∀ x ∈ X, a * x = x * a) → a = 1)
    {V'' : Type} [CommGroup V''] [Finite V'']
    (hV'' : ∀ v : V'', v ^ 2 = 1)
    {ρ'' : ↥G →* MulAut V''}
    (hz'' : ρ'' ⟨z, hXG hzX⟩ = 1)
    (hXnt : ∃ x : ↥G, (x : Q) ∈ X ∧ ρ'' x ≠ 1)
    (hq'' : IsQuadraticOn ρ'' (A.subgroupOf G))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hmod : F6.IsL2 p 1 (↥X ⧸ Subgroup.center ↥X)) :
    p = 7 ∧ ∀ a ∈ A, ∃ x ∈ X, ∃ c ∈ centralizer (X : Set Q), a = x * c := by
  classical
  let K : Subgroup ↥G := ρ''.ker
  haveI hKnormal : K.Normal := inferInstance
  let π : ↥G →* (↥G ⧸ K) := QuotientGroup.mk' K
  let ρ' : (↥G ⧸ K) →* MulAut V'' := QuotientGroup.kerLift ρ''
  have hρ'inj : Function.Injective ρ' := QuotientGroup.kerLift_injective ρ''
  have hρ'π : ∀ g : ↥G, ρ' (π g) = ρ'' g := fun g => QuotientGroup.kerLift_mk ρ'' g
  let XG : Subgroup ↥G := X.subgroupOf G
  let AG : Subgroup ↥G := A.subgroupOf G
  let L' : Subgroup (↥G ⧸ K) := XG.map π
  let A' : Subgroup (↥G ⧸ K) := AG.map π
  haveI hXGnormal : XG.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXG).mpr hXnormal
  have hL'normal : L'.Normal := hXGnormal.map π (QuotientGroup.mk'_surjective K)
  have hzG : z ∈ G := hXG hzX
  have hzK : (⟨z, hzG⟩ : ↥G) ∈ K := by
    rw [MonoidHom.mem_ker]; exact hz''
  let ZX : Subgroup ↥G := Subgroup.zpowers (⟨z, hzG⟩ : ↥G)
  have hZXleK : ZX ≤ K := Subgroup.zpowers_le.mpr hzK
  have hZXleX : ZX ≤ XG := by
    rw [Subgroup.zpowers_le]; exact Subgroup.mem_subgroupOf.mpr hzX
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    simpa [pow_two] using this
  have hz_centX : ∀ y ∈ X, z * y = y * z :=
    (hZX z hzX).mpr (Subgroup.mem_zpowers z)
  have hcenterXG : Subgroup.center ↥XG = ZX.subgroupOf XG := by
    apply le_antisymm
    · intro c hc
      rw [Subgroup.mem_subgroupOf]
      have hcent : ∀ y ∈ X, (c : Q) * y = y * (c : Q) := by
        intro y hy
        have hcy := Subgroup.mem_center_iff.mp hc
          (⟨⟨y, hXG hy⟩, Subgroup.mem_subgroupOf.mpr hy⟩ : ↥XG)
        exact (congrArg (fun t : ↥XG => ((t : ↥G) : Q)) hcy).symm
      have hmem := (hZX (c : Q) (Subgroup.mem_subgroupOf.mp c.2)).mp hcent
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro c hc
      rw [Subgroup.mem_subgroupOf] at hc
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hcQ : (c : Q) = z ^ k := by
        have := congrArg (fun t : ↥G => (t : Q)) hk
        simpa using this.symm
      have hzc : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X :=
        Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hz_centX (g : Q) g.2).symm)
      have hzpowc : (⟨z, hzX⟩ : ↥X) ^ k ∈ Subgroup.center ↥X :=
        (Subgroup.center ↥X).zpow_mem hzc k
      have hcomm := Subgroup.mem_center_iff.mp hzpowc
        (⟨((y : ↥G) : Q), Subgroup.mem_subgroupOf.mp y.2⟩ : ↥X)
      apply Subtype.ext
      apply Subtype.ext
      change ((y : Q) * (c : Q)) = ((c : Q) * (y : Q))
      rw [hcQ]
      simpa using congrArg Subtype.val hcomm
  have hXGperf : Group.IsPerfect ↥XG := by
    haveI : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hXG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXG).symm.surjective
  have hsimpleXG : IsSimpleGroup (↥XG ⧸ Subgroup.center ↥XG) := by
    let eXGX := Subgroup.subgroupOfEquivOfLe hXG
    have h1 : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) :=
      CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hmod
    exact (QuotientGroup.congr (Subgroup.center ↥XG) (Subgroup.center ↥X) eXGX
      (Subgroup.map_center_eq eXGX)).isSimpleGroup
  have hKinfX_le_ZX : XG ⊓ K ≤ ZX := by
    intro n hn
    let M : Subgroup ↥XG := (XG ⊓ K).subgroupOf XG
    have hMnormal : M.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (by rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (XG ⊓ K).Normal)];
            exact le_top)
    let q : ↥XG →* (↥XG ⧸ Subgroup.center ↥XG) := QuotientGroup.mk' (Subgroup.center ↥XG)
    have hMq : (M.map q).Normal := hMnormal.map q (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map q) with hbot | htop
    · have hMle : M ≤ Subgroup.center ↥XG := by
        have := (Subgroup.map_eq_bot_iff (f := q) M).mp hbot
        rwa [QuotientGroup.ker_mk'] at this
      have hnM : (⟨n, hn.1⟩ : ↥XG) ∈ M := Subgroup.mem_subgroupOf.mpr hn
      have hnZ : (⟨n, hn.1⟩ : ↥XG) ∈ Subgroup.center ↥XG := hMle hnM
      exact Subgroup.mem_subgroupOf.mp (hcenterXG ▸ hnZ)
    · exfalso
      have htop' : M ⊔ Subgroup.center ↥XG = ⊤ := by
        have h := Subgroup.comap_map_eq (f := q) M
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
        exact h.symm
      have hMtop : M = ⊤ :=
        le_antisymm le_top (a1413Adapt_le_of_perfect_le_sup_center hXGperf le_rfl htop'.symm.le)
      have hXGleK : XG ≤ K := by
        intro x hx
        have hxM : (⟨x, hx⟩ : ↥XG) ∈ M := by rw [hMtop]; trivial
        exact (Subgroup.mem_subgroupOf.mp hxM).2
      obtain ⟨x, hxX, hxnt⟩ := hXnt
      exact hxnt (MonoidHom.mem_ker.mp (hXGleK (Subgroup.mem_subgroupOf.mpr hxX)))
  have hKinfX : XG ⊓ K = ZX := le_antisymm hKinfX_le_ZX (le_inf hZXleX hZXleK)
  have hAGinfK : AG ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have haA : (a : Q) ∈ A := Subgroup.mem_subgroupOf.mp ha.1
    have haK : a ∈ K := ha.2
    have hcomm : ∀ x ∈ XG, a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (XG : Set ↥G) := by
      intro x hx
      have hmemK : a * x * a⁻¹ * x⁻¹ ∈ K := by
        have hπa : π a = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact haK
        have h : π (a * x * a⁻¹ * x⁻¹) = 1 := by
          calc π (a * x * a⁻¹ * x⁻¹)
              = π a * π x * (π a)⁻¹ * (π x)⁻¹ := by simp only [map_mul, map_inv]
            _ = 1 := by rw [hπa]; group
        exact QuotientGroup.eq_one_iff _ |>.mp h
      have hmemX : a * x * a⁻¹ * x⁻¹ ∈ XG := by
        have h1 : a * x * a⁻¹ ∈ XG := hXGnormal.conj_mem x hx a
        exact XG.mul_mem h1 (XG.inv_mem hx)
      have hmem : a * x * a⁻¹ * x⁻¹ ∈ ZX := by
        rw [← hKinfX]; exact ⟨hmemX, hmemK⟩
      have hz : (⟨a * x * a⁻¹ * x⁻¹, hmemX⟩ : ↥XG) ∈ Subgroup.center ↥XG := by
        rw [hcenterXG, Subgroup.mem_subgroupOf]
        exact hmem
      have := (a1413Adapt_mem_center_subgroup_iff
        (⟨a * x * a⁻¹ * x⁻¹, hmemX⟩ : ↥XG)).mp hz
      simpa using this
    have haN : a ∈ Subgroup.normalizer (XG : Set ↥G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hXGnormal]; exact Subgroup.mem_top a
    have hacent : a ∈ Subgroup.centralizer (XG : Set ↥G) :=
      a1413Adapt_mem_centralizer_of_conj_mem_centralizer hXGperf haN hcomm
    have hacentQ : (a : Q) ∈ Subgroup.centralizer (X : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp hacent ⟨x, hXG hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
      exact congrArg Subtype.val this
    have ha1 : (a : Q) = 1 := hAC (a : Q) haA
      (fun x hx => (Subgroup.mem_centralizer_iff.mp hacentQ x hx).symm)
    exact Subgroup.mem_bot.mpr (Subtype.ext ha1)
  let eA : ↥AG →* ↥A' := (π.comp AG.subtype).codRestrict A'
    (fun x => Subgroup.mem_map_of_mem π x.2)
  have heAinj : Function.Injective eA := by
    intro x y hxy
    have hxy' : π (x : ↥G) = π (y : ↥G) := congrArg Subtype.val hxy
    have hmem : (x : ↥G) * (y : ↥G)⁻¹ ∈ AG ⊓ K := by
      refine ⟨AG.mul_mem x.2 (AG.inv_mem y.2), ?_⟩
      have hπ : π ((x : ↥G) * (y : ↥G)⁻¹) = 1 := by
        have := congrArg (fun z => z * (π y)⁻¹) hxy'
        simpa [map_mul, map_inv] using this
      exact (QuotientGroup.eq_one_iff (N := K) ((x : ↥G) * (y : ↥G)⁻¹)).mp hπ
    have hbot : (x : ↥G) * (y : ↥G)⁻¹ = 1 := by
      have := hAGinfK ▸ hmem
      simpa using this
    have hG : (x : ↥G) = (y : ↥G) := by
      calc (x : ↥G) = (x : ↥G) * (y : ↥G)⁻¹ * (y : ↥G) := by group
        _ = (y : ↥G) := by rw [hbot, one_mul]
    exact Subtype.ext hG
  have heAsurj : Function.Surjective eA := by
    intro y
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  have hA'card : Nat.card A' = 4 := by
    have hcard : Nat.card A' = Nat.card ↥AG :=
      (Nat.card_congr (MulEquiv.ofBijective eA ⟨heAinj, heAsurj⟩).toEquiv).symm
    rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv, hA]
  have hAe' : IsElemAbelian 2 A' :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hAe G) π
  have hAC' : A' ⊓ Subgroup.centralizer (L' : Set (↥G ⧸ K)) = ⊥ := by
    rw [eq_bot_iff]
    intro a' ha'
    obtain ⟨a, haAG, rfl⟩ := Subgroup.mem_map.mp ha'.1
    have haA : (a : Q) ∈ A := Subgroup.mem_subgroupOf.mp haAG
    have hcentL : ∀ l ∈ L', l * π a = π a * l :=
      Subgroup.mem_centralizer_iff.mp ha'.2
    have hcomm : ∀ x ∈ XG, a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (XG : Set ↥G) := by
      intro x hx
      have hxL : π x ∈ L' := Subgroup.mem_map_of_mem π hx
      have hπ : π (a * x * a⁻¹ * x⁻¹) = 1 := by
        have h1 := hcentL (π x) hxL
        calc π (a * x * a⁻¹ * x⁻¹)
            = π a * π x * (π a)⁻¹ * (π x)⁻¹ := by simp only [map_mul, map_inv]
          _ = 1 := by rw [← h1]; group
      have hmemK : a * x * a⁻¹ * x⁻¹ ∈ K := QuotientGroup.eq_one_iff _ |>.mp hπ
      have hmemX : a * x * a⁻¹ * x⁻¹ ∈ XG := by
        have h1 : a * x * a⁻¹ ∈ XG := hXGnormal.conj_mem x hx a
        exact XG.mul_mem h1 (XG.inv_mem hx)
      have hmem : a * x * a⁻¹ * x⁻¹ ∈ ZX := by
        rw [← hKinfX]; exact ⟨hmemX, hmemK⟩
      have hz : (⟨a * x * a⁻¹ * x⁻¹, hmemX⟩ : ↥XG) ∈ Subgroup.center ↥XG := by
        rw [hcenterXG, Subgroup.mem_subgroupOf]
        exact hmem
      have := (a1413Adapt_mem_center_subgroup_iff
        (⟨a * x * a⁻¹ * x⁻¹, hmemX⟩ : ↥XG)).mp hz
      simpa using this
    have haN : a ∈ Subgroup.normalizer (XG : Set ↥G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hXGnormal]; exact Subgroup.mem_top a
    have hacent : a ∈ Subgroup.centralizer (XG : Set ↥G) :=
      a1413Adapt_mem_centralizer_of_conj_mem_centralizer hXGperf haN hcomm
    have hacentQ : (a : Q) ∈ Subgroup.centralizer (X : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp hacent ⟨x, hXG hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
      exact congrArg Subtype.val this
    have ha1 : (a : Q) = 1 := hAC (a : Q) haA
      (fun x hx => (Subgroup.mem_centralizer_iff.mp hacentQ x hx).symm)
    have ha1' : a = 1 := Subtype.ext ha1
    exact Subgroup.mem_bot.mpr (by rw [ha1', map_one])
  have hAnorm' : A' ≤ Subgroup.normalizer (L' : Set (↥G ⧸ K)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL'normal]; exact le_top
  have hq' : IsQuadraticOn ρ' A' := by
    intro a' ha' b' hb' v
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    rw [hρ'π a, hρ'π b]
    exact hq'' a ha b hb v
  let πX : ↥XG →* ↥L' := (π.comp XG.subtype).codRestrict L'
    (fun x => Subgroup.mem_map_of_mem π x.2)
  have hπXsurj : Function.Surjective πX := by
    intro y
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  have hπXker : πX.ker = Subgroup.center ↥XG := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π (x : ↥G) = 1 := congrArg Subtype.val hx
      have hxK : (x : ↥G) ∈ K := (QuotientGroup.eq_one_iff (N := K) (x : ↥G)).mp h1
      have hmemZX : (x : ↥G) ∈ ZX := by
        rw [← hKinfX]; exact ⟨x.2, hxK⟩
      have hz : (⟨(x : ↥G), x.2⟩ : ↥XG) ∈ Subgroup.center ↥XG := by
        rw [hcenterXG, Subgroup.mem_subgroupOf]
        exact hmemZX
      simpa using hz
    · intro hx
      have hmemZX : (x : ↥G) ∈ ZX :=
        Subgroup.mem_subgroupOf.mp (hcenterXG ▸ hx)
      have h1 : π (x : ↥G) = 1 :=
        (QuotientGroup.eq_one_iff (N := K) (x : ↥G)).mpr (hZXleK hmemZX)
      exact Subtype.ext h1
  let e1 : ↥L' ≃* (↥XG ⧸ Subgroup.center ↥XG) :=
    (QuotientGroup.quotientKerEquivOfSurjective πX hπXsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hπXker)
  let e2 : (↥XG ⧸ Subgroup.center ↥XG) ≃* (↥X ⧸ Subgroup.center ↥X) :=
    QuotientGroup.congr (Subgroup.center ↥XG) (Subgroup.center ↥X)
      (Subgroup.subgroupOfEquivOfLe hXG)
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hXG))
  let eL : ↥L' ≃* (↥X ⧸ Subgroup.center ↥X) := e1.trans e2
  have hL2' : F6.IsL2 p 1 ↥L' :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eL.symm hmod
  have hL2p : F6.IsL2 p 1 ↥L' := hL2'
  haveI hL'simple : IsSimpleGroup ↥L' :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hL2'
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hL2'
  have hFne2 : Nat.card F ≠ 2 := by rw [hF, pow_one]; omega
  have hFne3 : Nat.card F ≠ 3 := by rw [hF, pow_one]; omega
  obtain ⟨x, y, hxy⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
      F hFne2 hFne3
  let e' := eF.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hnab : ∃ a b : ↥L', a * b ≠ b * a :=
    ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  have hL'perf : Group.IsPerfect ↥L' :=
    Group.isPerfect_def.mpr (CFSG.ComponentClassification.Helpers.commutator_eq_top ↥L' hnab)
  have hL'center : Subgroup.center ↥L' = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot ↥L' hnab
  have hL'quasi : CFSG.Open.IsQuasisimple ↥L' := by
    refine ⟨Group.isPerfect_def.mp hL'perf, ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hL'center).trans
      (QuotientGroup.quotientBot (G := ↥L'))).isSimpleGroup
  have hcomp : CFSG.Open.IsComponentOf L' ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top (hL'normal.subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤), hL'quasi⟩
  have hpne2 : p ≠ 2 := by omega
  have hp7 : p = 7 := by
    by_contra hpne
    have hp11 : 11 ≤ p := by
      by_contra h
      have hp_le : p ≤ 10 := by omega
      interval_cases p
      · norm_num at hp
      · exact hpne rfl
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
    have h9 : 9 < p ^ 1 := by rw [pow_one]; omega
    exact h64o (↥G ⧸ K) V'' hV'' ρ' hρ'inj L' A' hcomp hAnorm' hA'card hAe' hq' hAC'
      p 1 hp hpne2 h9 hL2p
  refine ⟨hp7, ?_⟩
  have hL2'7 : F6.IsL2 7 1 ↥L' := hp7 ▸ hL2p
  have hinner := h64s (↥G ⧸ K) V'' hV'' ρ' hρ'inj L' A' hcomp hAnorm' hA'card hAe' hq' hAC'
    hL2'7
  intro a ha
  have ha' : π ⟨a, hAG ha⟩ ∈ A' :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  obtain ⟨l, hl, hcent⟩ := hinner (π ⟨a, hAG ha⟩) ha'
  obtain ⟨x0, hx0G, hx0π⟩ := Subgroup.mem_map.mp hl
  let y : ↥G := ⟨a, hAG ha⟩ * x0⁻¹
  have hyCentL : π y ∈ Subgroup.centralizer (L' : Set (↥G ⧸ K)) := by
    have hyeq : π y = π ⟨a, hAG ha⟩ * (π x0)⁻¹ := by
      dsimp [y]; rw [map_mul, map_inv]
    rw [hyeq]
    rwa [← hx0π] at hcent
  have hcommY : ∀ x ∈ XG, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (XG : Set ↥G) := by
    intro x hx
    have hxL : π x ∈ L' := Subgroup.mem_map_of_mem π hx
    have hcommxy := Subgroup.mem_centralizer_iff.mp hyCentL (π x) hxL
    have hmemK : y * x * y⁻¹ * x⁻¹ ∈ K := by
      have h : π (y * x * y⁻¹ * x⁻¹) = 1 := by
        calc π (y * x * y⁻¹ * x⁻¹)
            = π y * π x * (π y)⁻¹ * (π x)⁻¹ := by simp only [map_mul, map_inv]
          _ = 1 := by rw [← hcommxy]; group
      exact QuotientGroup.eq_one_iff _ |>.mp h
    have hmemX : y * x * y⁻¹ * x⁻¹ ∈ XG := by
      have h1 : y * x * y⁻¹ ∈ XG := hXGnormal.conj_mem x hx y
      exact XG.mul_mem h1 (XG.inv_mem hx)
    have hmem : y * x * y⁻¹ * x⁻¹ ∈ ZX := by
      rw [← hKinfX]; exact ⟨hmemX, hmemK⟩
    have hz : (⟨y * x * y⁻¹ * x⁻¹, hmemX⟩ : ↥XG) ∈ Subgroup.center ↥XG := by
      rw [hcenterXG, Subgroup.mem_subgroupOf]
      exact hmem
    have := (a1413Adapt_mem_center_subgroup_iff
      (⟨y * x * y⁻¹ * x⁻¹, hmemX⟩ : ↥XG)).mp hz
    simpa using this
  have hyN : y ∈ Subgroup.normalizer (XG : Set ↥G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hXGnormal]; exact Subgroup.mem_top y
  have hyCentXG : y ∈ Subgroup.centralizer (XG : Set ↥G) :=
    a1413Adapt_mem_centralizer_of_conj_mem_centralizer hXGperf hyN hcommY
  have hyCentQ : (y : Q) ∈ Subgroup.centralizer (X : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.mp hyCentXG ⟨x, hXG hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact congrArg Subtype.val this
  refine ⟨(x0 : Q), Subgroup.mem_subgroupOf.mp hx0G,
    (x0 : Q)⁻¹ * (y : Q) * (x0 : Q), ?_, ?_⟩
  · have hx0X : (x0 : Q) ∈ X := Subgroup.mem_subgroupOf.mp hx0G
    have hcommxy : (y : Q) * (x0 : Q) = (x0 : Q) * (y : Q) :=
      (Subgroup.mem_centralizer_iff.mp hyCentQ (x0 : Q) hx0X).symm
    have hcEq : (x0 : Q)⁻¹ * (y : Q) * (x0 : Q) = (y : Q) := by
      calc (x0 : Q)⁻¹ * (y : Q) * (x0 : Q)
          = (x0 : Q)⁻¹ * ((y : Q) * (x0 : Q)) := by group
        _ = (x0 : Q)⁻¹ * ((x0 : Q) * (y : Q)) := by rw [hcommxy]
        _ = (y : Q) := by group
    rwa [hcEq]
  · have hyQ : (y : Q) = a * (x0 : Q)⁻¹ := rfl
    rw [hyQ]; group

theorem asch1413_adapt64 (h64o : Asch6_4Odd) (h64s : Asch6_4Seven) {Q : Type} [Group Q]
    [Finite Q] {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {X A : Subgroup Q} {z : Q} (hz2 : orderOf z = 2) (hzX : z ∈ X) (hXperf : ⁅X, X⁆ = X)
    (hZX : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) ↔ x ∈ zpowers z)
    (hzA : ∀ a ∈ A, a * z = z * a) (hAN : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    (hAC : ∀ a ∈ A, (∀ x ∈ X, a * x = x * a) → a = 1)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hmod : F6.IsL2 p 1 (↥X ⧸ Subgroup.center ↥X)) :
    p = 7 ∧ ∀ a ∈ A, ∃ x ∈ X, ∃ c ∈ centralizer (X : Set Q), a = x * c := by
  classical
  let G : Subgroup Q := X ⊔ A
  have hXG : X ≤ G := le_sup_left
  have hAG : A ≤ G := le_sup_right
  have hsup : G ≤ X ⊔ A := le_of_eq rfl
  have hzG : z ∈ G := hXG hzX
  have hXnormal : G ≤ Subgroup.normalizer (X : Set Q) := by
    rw [show G = X ⊔ A from rfl]
    apply sup_le
    · exact Subgroup.le_normalizer
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; exact hAN a ha x hx
      · intro hx
        have h1 : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ ∈ X := hAN a⁻¹ (A.inv_mem ha) _ hx
        convert h1 using 1
        group
  have hGcent : G ≤ Subgroup.centralizer ({z} : Set Q) := by
    have hGcl : G = Subgroup.closure ((X : Set Q) ∪ (A : Set Q)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hGcl, Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hZX z hzX).mpr (Subgroup.mem_zpowers z) y hy)
    · exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hzA y hy).symm)
  have hz_cent : ∀ g ∈ G, g * z = z * g := by
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hGcent hg) z (Set.mem_singleton z)).symm
  let ρG : ↥G →* MulAut V := ρ.comp G.subtype
  let U : Subgroup V := commV (Subgroup.zpowers (ρ z))
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    simpa [pow_two] using this
  have hzρ : ρ z * ρ z = 1 := by rw [← map_mul, hzsq, map_one]
  have hUfix : U ≤ fixV (Subgroup.zpowers (ρ z)) :=
    a1413Adapt_commV_zpowers_le_fixV hV hzρ
  have hUcent : ρ z ∈ centQuot U :=
    mem_centQuot.mpr
      (fun v => Subgroup.subset_closure ⟨ρ z, Subgroup.mem_zpowers (ρ z), v, rfl⟩)
  have hconjZ : ∀ g : ↥G, ρG g * ρ z * (ρG g)⁻¹ = ρ z := by
    intro g
    have h : ρG g * ρ z = ρ z * ρG g := by
      have := congrArg (fun t : Q => ρ t) (hz_cent (g : Q) g.2)
      simpa [ρG, map_mul] using this
    rw [h]; group
  have hUstab : ∀ g : ↥G, ρG g ∈ stabSub U := by
    intro g
    have hmap : U.map (ρG g).toMonoidHom = U := by
      rw [show U = commV (Subgroup.zpowers (ρ z)) from rfl, ← commV_map_conj_eq]
      congr 1
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers (hconjZ g)
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      rw [← hmap] at hu
      obtain ⟨u', hu', heq⟩ := Subgroup.mem_map.mp hu
      have : u' = u := (ρG g).injective heq
      rwa [this] at hu'
    · intro hu
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hu
  by_cases hcase : ∃ x ∈ X, ∃ v : V, ρ x v * v⁻¹ ∉ U
  · let ρI : ↥G →* MulAut (V ⧸ U) :=
      (quotHom U).comp (ρG.codRestrict (stabSub U) hUstab)
    have hzI : ρI ⟨z, hzG⟩ = 1 := by
      have hmem : (⟨ρG ⟨z, hzG⟩, hUstab ⟨z, hzG⟩⟩ : stabSub U) ∈ (quotHom U).ker := by
        rw [ker_quotHom, Subgroup.mem_subgroupOf]
        exact hUcent
      exact MonoidHom.mem_ker.mp hmem
    have hXntI : ∃ x : ↥G, (x : Q) ∈ X ∧ ρI x ≠ 1 := by
      obtain ⟨x, hxX, v, hv⟩ := hcase
      refine ⟨⟨x, hXG hxX⟩, hxX, ?_⟩
      intro hx1
      apply hv
      have h := congrArg (fun φ : MulAut (V ⧸ U) => φ (QuotientGroup.mk v)) hx1
      have hL : ρI ⟨x, hXG hxX⟩ (QuotientGroup.mk v) = QuotientGroup.mk (ρ x v) := by
        rw [show ρI ⟨x, hXG hxX⟩ =
          quotHom U ⟨ρG ⟨x, hXG hxX⟩, hUstab _⟩ from rfl, quotHom_mk]
        rfl
      rw [hL, MulAut.one_apply] at h
      exact (mk_eq_mk_iff (ρ x v) v).mp h
    have hVquot : ∀ w : V ⧸ U, w ^ 2 = 1 := by
      intro w
      induction w using QuotientGroup.induction_on with
      | H v => rw [pow_two, ← QuotientGroup.mk_mul,
          show v * v = 1 from by simpa [pow_two] using hV v, QuotientGroup.mk_one]
    have hqI : IsQuadraticOn ρI (A.subgroupOf G) := by
      intro a ha b hb w
      induction w using QuotientGroup.induction_on with
      | H v =>
        have haA : (a : Q) ∈ A := Subgroup.mem_subgroupOf.mp ha
        have hbA : (b : Q) ∈ A := Subgroup.mem_subgroupOf.mp hb
        have h1 : ρI a (QuotientGroup.mk v) = QuotientGroup.mk (ρ (a : Q) v) := by
          rw [show ρI a = quotHom U ⟨ρG a, hUstab a⟩ from rfl, quotHom_mk]; rfl
        have h2 : ρI b (QuotientGroup.mk (ρ (a : Q) v * v⁻¹)) =
            QuotientGroup.mk (ρ (b : Q) (ρ (a : Q) v * v⁻¹)) := by
          rw [show ρI b = quotHom U ⟨ρG b, hUstab b⟩ from rfl, quotHom_mk]; rfl
        calc ρI b (ρI a (QuotientGroup.mk v) * (QuotientGroup.mk v)⁻¹)
            = ρI b (QuotientGroup.mk (ρ (a : Q) v * v⁻¹)) := by
              rw [h1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          _ = QuotientGroup.mk (ρ (b : Q) (ρ (a : Q) v * v⁻¹)) := h2
          _ = QuotientGroup.mk (ρ (a : Q) v * v⁻¹) := by rw [hq (a : Q) haA (b : Q) hbA v]
          _ = ρI a (QuotientGroup.mk v) * (QuotientGroup.mk v)⁻¹ := by
              rw [h1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact a1413Adapt_apply h64o h64s hXG hAG hsup hz2 hzX hXperf hZX hzA hXnormal hA hAe hAC
      hVquot hzI hXntI hqI hp hp5 hmod
  · have hncase : ∀ x ∈ X, ∀ v : V, ρ x v * v⁻¹ ∈ U := by
      intro x hx v
      by_contra hnot
      exact hcase ⟨x, hx, v, hnot⟩
    let ρII : ↥G →* MulAut ↥U := a1413Adapt_restrictHom ρG hUstab
    have hzII : ρII ⟨z, hzG⟩ = 1 := by
      refine MulEquiv.ext (fun u => ?_)
      apply Subtype.ext
      change ρ z (u : V) = (u : V)
      exact (a1413Adapt_mem_fixV_zpowers_iff (g := ρ z)).mp (hUfix u.2)
    have hXntII : ∃ x : ↥G, (x : Q) ∈ X ∧ ρII x ≠ 1 := by
      by_contra h
      have htriv : ∀ x : ↥G, (x : Q) ∈ X → ρII x = 1 := by
        intro x hx
        by_contra hx1
        exact h ⟨x, hx, hx1⟩
      have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
        intro x hx y hy
        apply hρ
        ext v
        simp only [map_mul, MulAut.mul_apply]
        have hxG : x ∈ G := hXG hx
        have hyG : y ∈ G := hXG hy
        have hxU : ρ x v * v⁻¹ ∈ U := hncase x hx v
        have hyU : ρ y v * v⁻¹ ∈ U := hncase y hy v
        have hxfixv : ρ x (ρ y v * v⁻¹) = ρ y v * v⁻¹ := by
          have h := congrArg (fun φ : MulAut ↥U => ((φ ⟨ρ y v * v⁻¹, hyU⟩ : ↥U) : V))
            (htriv ⟨x, hxG⟩ hx)
          change ((a1413Adapt_restrictAut ⟨ρG ⟨x, hxG⟩, hUstab ⟨x, hxG⟩⟩
            ⟨ρ y v * v⁻¹, hyU⟩ : ↥U) : V) = ρ y v * v⁻¹ at h
          rw [a1413Adapt_restrictAut_apply] at h
          exact h
        have hyfixv : ρ y (ρ x v * v⁻¹) = ρ x v * v⁻¹ := by
          have h := congrArg (fun φ : MulAut ↥U => ((φ ⟨ρ x v * v⁻¹, hxU⟩ : ↥U) : V))
            (htriv ⟨y, hyG⟩ hy)
          change ((a1413Adapt_restrictAut ⟨ρG ⟨y, hyG⟩, hUstab ⟨y, hyG⟩⟩
            ⟨ρ x v * v⁻¹, hxU⟩ : ↥U) : V) = ρ x v * v⁻¹ at h
          rw [a1413Adapt_restrictAut_apply] at h
          exact h
        have h1 : ρ x (ρ y v) = (ρ y v * v⁻¹) * ρ x v := by
          calc ρ x (ρ y v) = ρ x ((ρ y v * v⁻¹) * v) := by
                rw [show (ρ y v * v⁻¹) * v = ρ y v by group]
            _ = ρ x (ρ y v * v⁻¹) * ρ x v := by rw [map_mul]
            _ = (ρ y v * v⁻¹) * ρ x v := by rw [hxfixv]
        have h2 : ρ y (ρ x v) = (ρ x v * v⁻¹) * ρ y v := by
          calc ρ y (ρ x v) = ρ y ((ρ x v * v⁻¹) * v) := by
                rw [show (ρ x v * v⁻¹) * v = ρ x v by group]
            _ = ρ y (ρ x v * v⁻¹) * ρ y v := by rw [map_mul]
            _ = (ρ x v * v⁻¹) * ρ y v := by rw [hyfixv]
        rw [h1, h2]; ac_rfl
      have hXleZ : X ≤ Subgroup.zpowers z := fun x hx => (hZX x hx).mp (hXab x hx)
      have hXeqZ : X = Subgroup.zpowers z := le_antisymm hXleZ (Subgroup.zpowers_le.mpr hzX)
      have hcommbot : ⁅X, X⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hXab x hx y hy).symm
      have hXbot : X = ⊥ := by rw [← hXperf, hcommbot]
      have hz1 : z = 1 := by
        have : z ∈ (⊥ : Subgroup Q) := hXbot ▸ hzX
        simpa using this
      have : (1 : ℕ) = 2 := by rw [hz1, orderOf_one] at hz2; exact hz2
      exact absurd this (by norm_num)
    have hVU : ∀ w : ↥U, w ^ 2 = 1 := by
      intro w
      apply Subtype.ext
      simpa using hV (w : V)
    have hqII : IsQuadraticOn ρII (A.subgroupOf G) := by
      intro a ha b hb u
      apply Subtype.ext
      have haA : (a : Q) ∈ A := Subgroup.mem_subgroupOf.mp ha
      have hbA : (b : Q) ∈ A := Subgroup.mem_subgroupOf.mp hb
      have hcoee : ∀ (c : ↥G) (w : ↥U), ((ρII c w : ↥U) : V) = ρ (c : Q) (w : V) :=
        fun c w => rfl
      have h1 : ((ρII a u * u⁻¹ : ↥U) : V) = ρ (a : Q) (u : V) * (u : V)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoee a u]
      have h2 : ((ρII b (ρII a u * u⁻¹) : ↥U) : V) =
          ρ (b : Q) (ρ (a : Q) (u : V) * (u : V)⁻¹) := by
        rw [hcoee b (ρII a u * u⁻¹), h1]
      rw [h2, h1]
      exact hq (a : Q) haA (b : Q) hbA (u : V)
    exact a1413Adapt_apply h64o h64s hXG hAG hsup hz2 hzX hXperf hZX hzA hXnormal hA hAe hAC
      hVU hzII hXntII hqII hp hp5 hmod

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
