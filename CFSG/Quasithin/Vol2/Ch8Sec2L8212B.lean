module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210B
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212B

variable {G : Type} [Group G] {V : Subgroup G}

theorem autOn_inf_centralizer_82 [hc : IsMulCommutative ↥V] {X : Subgroup G} (z : ↥V) :
    autOn (X ⊓ Subgroup.centralizer ({(z : G)} : Set G)) V =
      autOn X V ⊓ centSub (Subgroup.zpowers z) := by
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ X ⊓ Subgroup.centralizer ({(z : G)} : Set G) := hg
    refine ⟨⟨g, hg'.1, rfl⟩, ?_⟩
    show conjAct V g ∈ centSub (Subgroup.zpowers z)
    rw [mem_centSub]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow]
    congr 1
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_singleton_iff.mp hg'.2, mul_inv_cancel_right]
  · rintro ⟨⟨g, hgX, rfl⟩, hg⟩
    have hgX' : (g : G) ∈ X := hgX
    refine ⟨g, ⟨hgX', ?_⟩, rfl⟩
    show (g : G) ∈ Subgroup.centralizer ({(z : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := (mem_centSub.mp hg) z (Subgroup.mem_zpowers z)
    have h2 := congrArg Subtype.val h1
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
    calc (g : G) * z = g * z * (g : G)⁻¹ * g := by group
      _ = z * g := by rw [h2]

theorem autOn_pCoreOf_82 [Finite G] {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hXC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    autOn (pCoreOf 2 X) V = pCoreOf 2 (autOn X V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_82 (W := ↥V)
  have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono fun x hx => hQX hx)
      (autOn_le_normalizer_82 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) ?_
    have h1 : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe (hQX.trans hX)).symm
    exact h1.map _
  · set P := pCoreOf 2 (autOn X V) with hP
    have hPX : P ≤ autOn X V := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hPN : autOn X V ≤ Subgroup.normalizer (P : Set (MulAut ↥V)) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hPp : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    let D : Subgroup G :=
      (P.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype ⊓ X
    have hmemD : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ X →
        conjAct V g ∈ P → (g : G) ∈ D := fun g hgX hgP => ⟨⟨g, hgP, rfl⟩, hgX⟩
    have hD : ∀ g ∈ D, ∃ n : ↥(Subgroup.normalizer (V : Set G)),
        (n : G) = g ∧ (n : G) ∈ X ∧ conjAct V n ∈ P := by
      rintro g ⟨⟨n, hn, rfl⟩, hgX⟩
      exact ⟨n, rfl, hgX, hn⟩
    have hDN : X ≤ Subgroup.normalizer (D : Set G) := by
      intro k hk
      have hkN : k ∈ Subgroup.normalizer (V : Set G) := hX hk
      have hconj : ∀ a ∈ X, ∀ g ∈ D, a * g * a⁻¹ ∈ D := by
        intro a ha g hg
        obtain ⟨n, rfl, hnX, hnP⟩ := hD g hg
        have haN : a ∈ Subgroup.normalizer (V : Set G) := hX ha
        refine hmemD (⟨a, haN⟩ * n * ⟨a, haN⟩⁻¹) (X.mul_mem (X.mul_mem ha hnX) (X.inv_mem ha)) ?_
        have haH : conjAct V ⟨a, haN⟩ ∈ autOn X V := ⟨⟨a, haN⟩, ha, rfl⟩
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hPN haH) _).mp hnP
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨hconj k hk g, fun hg => ?_⟩
      have := hconj k⁻¹ (X.inv_mem hk) _ hg
      simpa [mul_assoc] using this
    have hDp : IsPGroup 2 ↥D := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl, hnX, hnP⟩ := hD g hg
      obtain ⟨a, ha⟩ := hPp ⟨conjAct V n, hnP⟩
      have ha' : conjAct V (n ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha
      have hC : ((n ^ 2 ^ a : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
          X ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨X.pow_mem hnX _, (conjAct_eq_one_iff_82 _).mp ha'⟩
      obtain ⟨b, hb⟩ := hXC ⟨_, hC⟩
      refine ⟨a + b, Subtype.ext ?_⟩
      have hb' : ((n : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
        have := congrArg Subtype.val hb
        simpa using this
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_add, pow_mul, hb']
    have hDQ : D ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hDN hDp
    intro φ hφ
    obtain ⟨n, hnX, rfl⟩ := hPX hφ
    exact ⟨n, hDQ (hmemD n hnX hφ), rfl⟩

theorem commV_autOn_82 [hc : IsMulCommutative ↥V] {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    commV (autOn X V) = (⁅V, X⁆).subgroupOf V :=
  CFSG.Quasithin.AutOn.commV_autOn_eq hX

theorem autOn_ch8Lz_82 [Finite G] [hc : IsMulCommutative ↥V] {L : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (z : ↥V) :
    autOn (ch8Lz L z) V = parz82 (autOn L V) z := by
  unfold ch8Lz parz82
  rw [autOn_perfectCore_82 (inf_le_left.trans hLN), autOn_inf_centralizer_82]

end L8212B

end CFSG.Quasithin.H13
