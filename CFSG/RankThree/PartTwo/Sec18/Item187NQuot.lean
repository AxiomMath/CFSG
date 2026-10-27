module

public import CFSG.RankThree.PartTwo.Sec18.Item187NAut
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
import CFSG.LieType.BorelTits.Basic
import CFSG.GF2Type.Smith1980Orth.S4Fixed

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Quot

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

abbrev NSolY (X : Subgroup G) : Type := ↥X ⧸ CFSG.pCore 2 ↥X

def nsolMk (X : Subgroup G) : ↥X →* NSolY X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)

theorem pCoreOf_eq_map_pCore (X : Subgroup G) :
    CFSG.Open.pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := rfl

theorem nsolMk_eq_one_iff {X : Subgroup G} (x : ↥X) :
    nsolMk X x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 X := by
  rw [nsolMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pCoreOf_eq_map_pCore]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

noncomputable def cAct (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G)) :
    MulAut (NSolY X) :=
  Sec16.Crit167.quotPCoreAut ↥X (X.normalizerMonoidHom ⟨c, hc⟩)

theorem cAct_mk (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G)) (x : ↥X)
    (hx : c * (x : G) * c⁻¹ ∈ X) :
    cAct X hc (nsolMk X x) = nsolMk X ⟨c * (x : G) * c⁻¹, hx⟩ := by
  have : (X.normalizerMonoidHom ⟨c, hc⟩ : MulAut ↥X) x = ⟨c * (x : G) * c⁻¹, hx⟩ :=
    Subtype.ext (by simp)
  show Sec16.Crit167.quotPCoreAut ↥X (X.normalizerMonoidHom ⟨c, hc⟩) (QuotientGroup.mk x) = _
  rw [Sec16.Crit167.quotPCoreAut_apply_mk, this]
  rfl

theorem cAct_pow_three (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G))
    (hc3 : c ^ 3 = 1) : cAct X hc ^ 3 = 1 := by
  unfold cAct
  rw [← map_pow, ← map_pow]
  have : (⟨c, hc⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  rw [this, map_one, map_one]

theorem cAct_ne_one (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G))
    (hnot : ¬ ⁅X, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X) : cAct X hc ≠ 1 := by
  intro h1
  apply hnot
  have hkey : ∀ k : ℤ, ∀ y : ↥X, ∃ hy : c ^ k * (y : G) * (c ^ k)⁻¹ ∈ X,
      nsolMk X ⟨c ^ k * (y : G) * (c ^ k)⁻¹, hy⟩ = nsolMk X y := by
    intro k y
    have hk : c ^ k ∈ Subgroup.normalizer (X : Set G) := Subgroup.zpow_mem _ hc k
    have hy : c ^ k * (y : G) * (c ^ k)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hk (y : G)).mp y.2
    refine ⟨hy, ?_⟩
    have hw : cAct X hk = 1 := by
      have e : (⟨c ^ k, hk⟩ : Subgroup.normalizer (X : Set G)) =
          (⟨c, hc⟩ : Subgroup.normalizer (X : Set G)) ^ k := Subtype.ext (by simp)
      have h2 : Sec16.Crit167.quotPCoreAut ↥X (X.normalizerMonoidHom ⟨c, hc⟩) = 1 := h1
      show Sec16.Crit167.quotPCoreAut ↥X (X.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1
      rw [e, map_zpow, map_zpow, h2, one_zpow]
    have h3 := cAct_mk X hk y hy
    rw [hw, MulAut.one_apply] at h3
    exact h3.symm
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
  obtain ⟨a, rfl⟩ : ∃ a : ↥X, (a : G) = g₁ := ⟨⟨g₁, hg₁⟩, rfl⟩
  obtain ⟨hy, hyeq⟩ := hkey k a⁻¹
  have hprod : nsolMk X (a * (⟨c ^ k * ((a⁻¹ : ↥X) : G) * (c ^ k)⁻¹, hy⟩ : ↥X)) = 1 := by
    rw [map_mul, hyeq, map_inv, mul_inv_cancel]
  have hmem := (nsolMk_eq_one_iff _).mp hprod
  have e : ((a * (⟨c ^ k * ((a⁻¹ : ↥X) : G) * (c ^ k)⁻¹, hy⟩ : ↥X) : ↥X) : G) =
      ⁅(a : G), c ^ k⁆ := by
    simp [commutatorElement_def, mul_assoc]
  rw [← e]
  exact hmem

theorem exists_fixed_lift (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G))
    (hc3 : c ^ 3 = 1) {yb : NSolY X} (hyb : cAct X hc yb = yb) :
    ∃ y : ↥X, nsolMk X y = yb ∧ c * (y : G) = (y : G) * c := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) yb
  have hcx : c * (x₀ : G) * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hc x₀).mp x₀.2
  have h1 : cAct X hc (nsolMk X x₀) = nsolMk X ⟨c * (x₀ : G) * c⁻¹, hcx⟩ := cAct_mk X hc x₀ hcx
  have h2 : nsolMk X ⟨c * (x₀ : G) * c⁻¹, hcx⟩ = nsolMk X x₀ := h1.symm.trans hyb
  have hmem : (x₀ : G)⁻¹ * (c * (x₀ : G) * c⁻¹) ∈ CFSG.Open.pCoreOf 2 X := by
    have := (nsolMk_eq_one_iff (X := X) (x₀⁻¹ * ⟨c * (x₀ : G) * c⁻¹, hcx⟩)).mp (by
      rw [map_mul, map_inv, h2, inv_mul_cancel])
    simpa using this
  have hpc : IsPGroup 2 (CFSG.Open.pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hθH : ∀ h ∈ CFSG.Open.pCoreOf 2 X, c * h * c⁻¹ ∈ CFSG.Open.pCoreOf 2 X := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hc) h).mp hh
  obtain ⟨h, hh, hfix⟩ := CFSG.GF2Type.Smith1980Orth.exists_fixed_mem_coset hpc hc3 hθH hmem
  have hhX : h ∈ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hh
  refine ⟨⟨(x₀ : G) * h, X.mul_mem x₀.2 hhX⟩, ?_, ?_⟩
  · have h3 : nsolMk X ⟨h, hhX⟩ = 1 := (nsolMk_eq_one_iff _).mpr hh
    show nsolMk X (x₀ * ⟨h, hhX⟩) = nsolMk X x₀
    rw [map_mul, h3, mul_one]
  · show c * ((x₀ : G) * h) = ((x₀ : G) * h) * c
    calc c * ((x₀ : G) * h) = (c * ((x₀ : G) * h) * c⁻¹) * c := by group
      _ = ((x₀ : G) * h) * c := by rw [hfix]

theorem exists_order_five_preimage (X : Subgroup G) {yb : NSolY X} (hyb5 : orderOf yb = 5) :
    ∃ y : ↥X, orderOf (y : G) = 5 ∧ nsolMk X y ∈ Subgroup.zpowers yb := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) yb
  have hy₀' : nsolMk X y₀ = yb := hy₀
  have h5 : 5 ∣ orderOf y₀ := by
    have := orderOf_map_dvd (nsolMk X) y₀
    rwa [hy₀', hyb5] at this
  have hker : y₀ ^ 5 ∈ CFSG.pCore 2 ↥X := by
    have h1 : nsolMk X (y₀ ^ 5) = 1 := by
      rw [map_pow, hy₀', ← hyb5]
      exact pow_orderOf_eq_one yb
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h2 : ∃ k, orderOf (y₀ ^ 5) = 2 ^ k := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨y₀ ^ 5, hker⟩
    have : (y₀ ^ 5) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one this)
    exact ⟨j, hj⟩
  obtain ⟨k, hk⟩ := h2
  have hord : orderOf y₀ = 5 * 2 ^ k := by
    have := orderOf_pow_of_dvd (x := y₀) (n := 5) (by norm_num) h5
    rw [hk] at this
    omega
  refine ⟨y₀ ^ (2 ^ k), ?_, ?_⟩
  · have hd : 2 ^ k ∣ orderOf y₀ := ⟨5, by rw [hord]; ring⟩
    have := orderOf_pow_of_dvd (x := y₀) (n := 2 ^ k) (by positivity) hd
    rw [Subgroup.orderOf_coe, this, hord]
    exact Nat.mul_div_cancel _ (by positivity)
  · rw [map_pow, hy₀']
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers yb) _

def nsolPre (X : Subgroup G) (V : Subgroup (NSolY X)) : Subgroup G :=
  (V.comap (nsolMk X)).map X.subtype

theorem mem_nsolPre {X : Subgroup G} {V : Subgroup (NSolY X)} {g : G} :
    g ∈ nsolPre X V ↔ ∃ hg : g ∈ X, nsolMk X ⟨g, hg⟩ ∈ V := by
  unfold nsolPre
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem nsolPre_le (X : Subgroup G) (V : Subgroup (NSolY X)) : nsolPre X V ≤ X :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_nsolPre (X : Subgroup G) (V : Subgroup (NSolY X)) :
    CFSG.Open.pCoreOf 2 X ≤ nsolPre X V := by
  refine Subgroup.map_mono (fun x hx => ?_)
  rw [Subgroup.mem_comap]
  have : nsolMk X x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [this]
  exact V.one_mem

theorem le_normalizer_nsolPre (X : Subgroup G) (V : Subgroup (NSolY X)) [V.Normal] :
    X ≤ Subgroup.normalizer (nsolPre X V : Set G) := by
  have key : ∀ y : G, y ∈ X → ∀ h ∈ nsolPre X V, y * h * y⁻¹ ∈ nsolPre X V := by
    intro y hy h hh
    obtain ⟨hhX, hhV⟩ := mem_nsolPre.mp hh
    have hyhX : y * h * y⁻¹ ∈ X := X.mul_mem (X.mul_mem hy hhX) (X.inv_mem hy)
    refine mem_nsolPre.mpr ⟨hyhX, ?_⟩
    have hconj := Subgroup.Normal.conj_mem inferInstance _ hhV (nsolMk X ⟨y, hy⟩)
    have e : nsolMk X ⟨y * h * y⁻¹, hyhX⟩ =
        nsolMk X ⟨y, hy⟩ * nsolMk X ⟨h, hhX⟩ * (nsolMk X ⟨y, hy⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [e]
    exact hconj
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key y hy h
  · intro hh
    have h' := key y⁻¹ (X.inv_mem hy) _ hh
    have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem mem_normalizer_nsolPre {X : Subgroup G} (hc : c ∈ Subgroup.normalizer (X : Set G))
    {V : Subgroup (NSolY X)} (hV : V.map (cAct X hc).toMonoidHom = V) :
    c ∈ Subgroup.normalizer (nsolPre X V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨hgX, hgV⟩ := mem_nsolPre.mp hg
    have hcg : c * g * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hc g).mp hgX
    refine mem_nsolPre.mpr ⟨hcg, ?_⟩
    have h1 : (cAct X hc).toMonoidHom (nsolMk X ⟨g, hgX⟩) ∈ V.map (cAct X hc).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hgV
    rw [hV] at h1
    have h2 := cAct_mk X hc ⟨g, hgX⟩ hcg
    exact h2 ▸ h1
  · intro hg
    obtain ⟨hcg, hcgV⟩ := mem_nsolPre.mp hg
    have hgX : g ∈ X := (Subgroup.mem_normalizer_iff.mp hc g).mpr hcg
    refine mem_nsolPre.mpr ⟨hgX, ?_⟩
    have h2 := cAct_mk X hc ⟨g, hgX⟩ hcg
    have h1 : (cAct X hc).toMonoidHom (nsolMk X ⟨g, hgX⟩) ∈ V := h2 ▸ hcgV
    rw [← hV] at h1
    obtain ⟨v, hv, hve⟩ := h1
    have : v = nsolMk X ⟨g, hgX⟩ := (cAct X hc).injective hve
    rwa [← this]

theorem le_normalizer_nsolPre_of_characteristic (X : Subgroup G) (V : Subgroup (NSolY X))
    [V.Characteristic] {B : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (nsolPre X V : Set G) := fun b hb =>
  mem_normalizer_nsolPre (hBX hb) (Subgroup.characteristic_iff_map_eq.mp inferInstance _)

def sylowImage (X S : Subgroup G) : Subgroup (NSolY X) := (S.subgroupOf X).map (nsolMk X)

theorem mem_sylowImage {X S : Subgroup G} {z : NSolY X} :
    z ∈ sylowImage X S ↔ ∃ s : ↥X, (s : G) ∈ S ∧ nsolMk X s = z := by
  unfold sylowImage
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

theorem isSylowOf_sylowImage {X S : Subgroup G} (hS : IsSylowOf 2 S X) :
    IsSylowOf 2 (sylowImage X S) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hSp, hSdvd⟩ := hS
  have hP : IsPGroup 2 (sylowImage X S) := (hSp.comap_subtype (K := X)).map (nsolMk X)
  refine ⟨le_top, hP, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have hsurj : Function.Surjective (nsolMk X) := QuotientGroup.mk'_surjective _
  have hdiv : (sylowImage X S).index ∣ S.relIndex X :=
    (S.subgroupOf X).index_map_dvd hsurj
  exact fun hdvd => hSdvd (hdvd.trans hdiv)

theorem isPGroup_sylowImage {X S : Subgroup G} (hS : IsPGroup 2 S) :
    IsPGroup 2 (sylowImage X S) :=
  (hS.comap_subtype (K := X)).map (nsolMk X)

theorem pCore_NSolY (X : Subgroup G) : CFSG.pCore 2 (NSolY X) = ⊥ :=
  CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot

theorem not_isSolvable_nsolY (X : Subgroup G) (hns : ¬ Group.IsSolvable ↥X) :
    ¬ Group.IsSolvable (NSolY X) := fun h => hns (by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (CFSG.pCore 2 ↥X) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).isNilpotent
  haveI : Group.IsSolvable (CFSG.pCore 2 ↥X) := inferInstance
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥X).subtype
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (by simp [QuotientGroup.ker_mk']))

theorem le_sup_centralizer_of_fixedSubgroupOf_sup (X S : Subgroup G)
    (hc : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1) (hSX : S ≤ X)
    (hQS : CFSG.Open.pCoreOf 2 X ≤ S)
    (hY : fixedSubgroupOf (cAct X hc) ⊔ sylowImage X S = ⊤) :
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ S := by
  set J : Subgroup G := (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ S with hJ
  have hfix : fixedSubgroupOf (cAct X hc) ≤ (J.subgroupOf X).map (nsolMk X) := by
    intro f hf
    obtain ⟨y, hyf, hyc⟩ :=
      exists_fixed_lift X hc hc3 ((CFSG.RankThree.PartTwo.mem_fixedSubgroupOf _ _).mp hf)
    have hyJ : (y : G) ∈ J :=
      Subgroup.mem_sup_left (show (y : G) ∈ X ⊓ Subgroup.centralizer ({c} : Set G) from
        ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm⟩)
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyJ, hyf⟩
  have hsyl : sylowImage X S ≤ (J.subgroupOf X).map (nsolMk X) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono X le_sup_right)
  have htop : (⊤ : Subgroup (NSolY X)) ≤ (J.subgroupOf X).map (nsolMk X) := by
    rw [← hY]
    exact sup_le hfix hsyl
  intro x hx
  have hxtop : nsolMk X ⟨x, hx⟩ ∈ (J.subgroupOf X).map (nsolMk X) :=
    htop (Subgroup.mem_top _)
  obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp hxtop
  have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hk1 : nsolMk X (j⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hjx, inv_mul_cancel]
  have hk2 : ((j⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ CFSG.Open.pCoreOf 2 X := (nsolMk_eq_one_iff _).mp hk1
  have hk3 : ((j⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ J := Subgroup.mem_sup_right (hQS hk2)
  have hxj : x = (j : G) * ((j⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
  rw [hxj]
  exact J.mul_mem hjJ hk3

theorem exists_restrict_hom (X : Subgroup G) (hc : c ∈ Subgroup.normalizer (X : Set G))
    (K : Subgroup (NSolY X)) (hK : K.map (cAct X hc).toMonoidHom = K) :
    ∃ π : ↥(nsolPre X K) →* ↥K, Function.Surjective π ∧
      π.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf (nsolPre X K) ∧
      (∀ x : ↥(nsolPre X K), ((π x : ↥K) : NSolY X) = nsolMk X ⟨(x : G), nsolPre_le X K x.2⟩) ∧
      (∀ x : ↥(nsolPre X K), ∃ x' : ↥(nsolPre X K),
        (x' : G) = c * x * c⁻¹ ∧ π x' = restrictAut (cAct X hc) K hK (π x)) := by
  have hmem : ∀ x : ↥(nsolPre X K), nsolMk X ⟨(x : G), nsolPre_le X K x.2⟩ ∈ K :=
    fun x => (mem_nsolPre.mp x.2).2
  refine ⟨((nsolMk X).comp (Subgroup.inclusion (nsolPre_le X K))).codRestrict K hmem,
    ?_, ?_, ?_, ?_⟩
  · intro k
    have hsurj : Function.Surjective (nsolMk X) := QuotientGroup.mk'_surjective _
    obtain ⟨y, hy⟩ := hsurj (k : NSolY X)
    have hyK : nsolMk X y ∈ K := by
      rw [hy]
      exact k.2
    exact ⟨⟨(y : G), mem_nsolPre.mpr ⟨y.2, hyK⟩⟩, Subtype.ext hy⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : nsolMk X ⟨(x : G), nsolPre_le X K x.2⟩ = 1 := congrArg Subtype.val h
      exact (nsolMk_eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      exact (nsolMk_eq_one_iff ⟨(x : G), nsolPre_le X K x.2⟩).mpr h
  · intro x
    rfl
  · intro x
    have hx' : c * (x : G) * c⁻¹ ∈ nsolPre X K :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_nsolPre hc hK) (x : G)).mp x.2
    refine ⟨⟨c * (x : G) * c⁻¹, hx'⟩, rfl, ?_⟩
    apply Subtype.ext
    rw [coe_restrictAut]
    exact (cAct_mk X hc ⟨(x : G), nsolPre_le X K x.2⟩ (nsolPre_le X K hx')).symm

end Quot

section Misc

variable {G : Type} [Group G]

theorem centralizer_singleton_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro g hg
  have hgc : Commute g c := (Subgroup.mem_centralizer_iff.mp hg c rfl).symm
  have e : ∀ k : ℤ, g * c ^ k * g⁻¹ = c ^ k := fun k => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_right hgc k).eq
  have e' : ∀ k : ℤ, g⁻¹ * c ^ k * g = c ^ k := fun k => by
    rw [(Commute.zpow_right hgc.inv_left k).eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [e k]
    exact hh
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : h = c ^ k := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g⁻¹ * c ^ k * g := by rw [hk]
        _ = c ^ k := e' k
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k

end Misc

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
