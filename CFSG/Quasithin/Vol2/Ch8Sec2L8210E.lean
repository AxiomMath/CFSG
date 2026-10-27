module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.Background.AutOnCard
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8210E

variable {G : Type} [Group G] {V : Subgroup G}

omit [Group G] in
theorem finite_mulAut_82 {W : Type*} [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => f.toEquiv) fun _ _ h =>
    MulEquiv.ext fun x => congrArg (· x) h

theorem autOn_perfectCore_82 [Finite G] {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore X) V = perfectCore (autOn X V) :=
  CFSG.Quasithin.AutOn.autOn_perfectCore_eq hX

theorem autOn_inf_normalizer_82 [hc : IsMulCommutative ↥V] {L U : Subgroup G} (hUV : U ≤ V) :
    autOn (L ⊓ Subgroup.normalizer (U : Set G)) V = autOn L V ⊓ stabSub (U.subgroupOf V) := by
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ L ⊓ Subgroup.normalizer (U : Set G) := hg
    refine ⟨⟨g, hg'.1, rfl⟩, fun u => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg'.2 u).symm
  · rintro ⟨⟨g, hgL, rfl⟩, hg⟩
    have hgL' : (g : G) ∈ L := hgL
    refine ⟨g, ⟨hgL', ?_⟩, rfl⟩
    show (g : G) ∈ Subgroup.normalizer (U : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (hg ⟨x, hUV hx⟩).mpr hx
      rw [Subgroup.mem_subgroupOf, CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h1
      exact h1
    · intro hx
      have hxV : x ∈ V := by
        have h2 : (g : G) * x * (g : G)⁻¹ ∈ V := hUV hx
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2) _).mp h2
        simpa [mul_assoc] using this
      have h1 := hg ⟨x, hxV⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h1
      exact h1.mp hx

theorem fixV_autOn_82 [hc : IsMulCommutative ↥V] {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn X V) = (V ⊓ Subgroup.centralizer (X : Set G)).subgroupOf V := by
  ext v
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hv
    refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have h1 := hv (conjAct V ⟨a, hX ha⟩) ⟨⟨a, hX ha⟩, ha, rfl⟩
    have h2 := congrArg Subtype.val h1
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
    calc a * (v : G) = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h2]
  · rintro ⟨-, hvC⟩
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ X := hg
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_iff.mp hvC g hg', mul_inv_cancel_right]

theorem card_autOn_mul_82 [Finite G] {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autOn X V) * Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) = Nat.card ↥X :=
  CFSG.Quasithin.AutOn.card_autOn_mul hX

theorem card_autOn_82 [Finite G] {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hXp : IsPGroup 2 ↥X) :
    Nat.card ↥(autOn X V) = 2 ^ mQuot X (X ⊓ Subgroup.centralizer (V : Set G)) := by
  have h1 := card_autOn_mul_82 hX
  have h2 : Nat.card ↥((X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X) *
      (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X = Nat.card ↥X :=
    Subgroup.card_mul_index _
  have h3 : Nat.card ↥((X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h4 : Nat.card ↥(autOn X V) = (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X := by
    have h5 : Nat.card ↥(autOn X V) * Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) =
        (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X *
          Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h5
  have hdvd : Nat.card ↥(autOn X V) ∣ Nat.card ↥X := ⟨_, h1.symm⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hXp
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  unfold mQuot
  rw [← h4, hm, padicValNat.prime_pow]

theorem autOn_commutator_82 {X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    autOn ⁅X, Y⁆ V = ⁅autOn X V, autOn Y V⁆ := by
  have hXY : ⁅X, Y⁆ ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.commutator_mono hX hY).trans (A3.commutator_self_le _)
  have h1 : ⁅X, Y⁆.subgroupOf (Subgroup.normalizer (V : Set G)) =
      ⁅X.subgroupOf (Subgroup.normalizer (V : Set G)),
        Y.subgroupOf (Subgroup.normalizer (V : Set G))⁆ := by
    apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_subgroupOf_eq_of_le hXY]
  unfold autOn
  rw [h1, Subgroup.map_commutator]

theorem autOn_le_normalizer_82 {X L : Subgroup G} (hXL : X ≤ Subgroup.normalizer (L : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXL

theorem isElemAbelian_autOn_82 {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    IsElemAbelian 2 (autOn X V) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
    have ha' : (a : G) ∈ X := ha
    have hb' : (b : G) ∈ X := hb
    have hab : a * b = b * a := by
      apply Subtype.ext
      have h1 := hX.1.1.1 ⟨a, ha'⟩ ⟨b, hb'⟩
      have h2 : ((⟨a, ha'⟩ * ⟨b, hb'⟩ : ↥X) : G) = ((⟨b, hb'⟩ * ⟨a, ha'⟩ : ↥X) : G) := by
        rw [h1]
      exact h2
    apply Subtype.ext
    change conjAct V a * conjAct V b = conjAct V b * conjAct V a
    rw [← map_mul, ← map_mul, hab]
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ X := ha
    have h1 : a ^ 2 = 1 := Subtype.ext (by simpa using hX.2 a ha')
    rw [← map_pow, h1, map_one]

end L8210E

end CFSG.Quasithin.H13
