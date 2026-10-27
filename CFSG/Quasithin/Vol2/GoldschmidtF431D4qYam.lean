module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYamLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYamLat
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.Yam CFSG.Quasithin.H13.Sec53F.TriD4


variable {K : Type} [Field K] (σ : K ≃+* K)

theorem d4_fixed_isSimpleGroup [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 K σ
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf K hK σ.toRingHom hσ).1).1

theorem d4_fixed_no_normal [Finite K]
    (hs : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (R : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hR : R.Normal)
    (hp : IsPGroup 2 ↥R) : R = ⊥ := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
  · exact h
  · subst h
    have hD : IsPGroup 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      intro g
      obtain ⟨n, hn⟩ := hp ⟨g, Subgroup.mem_top g⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    have hnt := hD.center_nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)))
    have hx' : (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
        (⊥ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← exceptional_fixed_center_trivial TwistTag.D4 K σ]
      exact x.2
    exact absurd (Subtype.ext (Subgroup.mem_bot.1 hx')) hx

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "𝒰" => Subgroup.subgroupOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) C₀
local notation "P₀" =>
  graphFixedParabolic TwistTag.D4 K σ.toRingHom {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}
local notation "P₁" =>
  graphFixedParabolic TwistTag.D4 K σ.toRingHom {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}

theorem d4_yamStd [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    YamStd ↥C₀ 𝒰 (Subgroup.subgroupOf P₀ C₀) (Subgroup.subgroupOf P₁ C₀) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hs := d4_fixed_isSimpleGroup σ hf hK hσ
  have hlat := d4_overgroups_normalizer σ
  have hN := d4_normalizer_eq σ
  have hBP0 : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ P₀ :=
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
  have hBP1 : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ P₁ :=
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
  have hP0C : P₀ ≤ C₀ := graphFixedParabolic_le _ _ _ _
  have hP1C : P₁ ≤ C₀ := graphFixedParabolic_le _ _ _ _
  have hn01 : ¬ P₀ ≤ P₁ := fun h =>
    absurd (congrArg Fin.val ((graphFixedParabolic_le_iff σ.surjective).1 h (Set.mem_singleton _)))
      (by decide)
  have hn10 : ¬ P₁ ≤ P₀ := fun h =>
    absurd (congrArg Fin.val ((graphFixedParabolic_le_iff σ.surjective).1 h (Set.mem_singleton _)))
      (by decide)
  have hn01' : ¬ Subgroup.subgroupOf P₀ C₀ ≤ Subgroup.subgroupOf P₁ C₀ :=
    fun h => hn01 fun x hx => h (show (⟨x, hP0C hx⟩ : ↥C₀) ∈ _ from hx)
  have hn10' : ¬ Subgroup.subgroupOf P₁ C₀ ≤ Subgroup.subgroupOf P₀ C₀ :=
    fun h => hn10 fun x hx => h (show (⟨x, hP1C hx⟩ : ↥C₀) ∈ _ from hx)
  have hle0 : Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀) ≤ Subgroup.subgroupOf P₀ C₀ :=
    hN.trans_le fun x hx => hBP0 hx
  have hle1 : Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀) ≤ Subgroup.subgroupOf P₁ C₀ :=
    hN.trans_le fun x hx => hBP1 hx
  refine ⟨d4_sylow σ, d4_fixed_no_normal σ hs, fun h => hn01' h.le, hle0, hle1,
    isCoatom_of_overgroups_four hle0 hn10' hlat hn01',
    isCoatom_of_overgroups_four hle1 hn01' (fun A hA => ?_) hn10', fun A hNA hAt => ?_,
    d4_twoLocal_parabolic σ _, d4_twoLocal_parabolic σ _⟩
  · rcases hlat A hA with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h))]
  · rcases hlat A hNA with h | h | h | h
    exacts [Or.inl (h ▸ hle0), Or.inl h.le, Or.inr h.le, absurd h hAt]

end CFSG.Quasithin.H13.F431.D4q.Hex
