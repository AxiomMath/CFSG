module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3OddU35K
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem eq_one_of_two_elem_of_u35 (h : Sec15R G A c L) [Fact (Nat.Prime 5)]
    (φU : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1)
    (hsimp : IsSimpleGroup ↥L)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G))))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {x : G} (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxA : x ∈ Subgroup.centralizer (A : Set G)) : x = 1 := by
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA) hxA
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L
      (centralizer_singleton_le_normalizer_zpowers c hxc)
  have hθ := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hsimp
  have φL : ↥L ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1 :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).symm.trans φU
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩ with hσ
  obtain ⟨k, hk⟩ := hx
  have hσ2 : ∃ n : ℕ, σ ^ 2 ^ n = 1 := by
    refine ⟨k, ?_⟩
    have hk' : (⟨x, hxL⟩ : Subgroup.normalizer (L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [hσ, ← map_pow, hk', map_one]
  have hE : Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hfix : ∀ y ∈ (A ⊓ L).subgroupOf L, σ y = y := by
    intro y hy
    apply Subtype.ext
    have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hy).1
    have hc' := Subgroup.mem_centralizer_iff.mp hxA (y : G) hyA
    simp only [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [← hc', mul_inv_cancel_right]
  have hσ1 := eq_one_of_pow_two_pow_of_fix_card_nine φL σ hσ2 hE hfix
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    have hker : (⟨x, hxL⟩ : Subgroup.normalizer (L : Set G)) ∈ L.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.mpr hσ1
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hmem : x ∈ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hxc, hxCL⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (Subgroup.orderOf_dvd_natCard _ hmem))

theorem false_of_u35_of_field (h : Sec15R G A c L) [Fact (Nat.Prime 5)]
    (φU : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1)
    (hsimp : IsSimpleGroup ↥L)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G))))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {Y : Subgroup G} {Yc : Subgroup (Res1Q A L)}
    (hfield : ∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) : False := by
  obtain ⟨x, ⟨hxO, hxA⟩, y, -, hne⟩ := hfield
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y ⟨x, hxO⟩
  have hx1 : (x : G) = 1 :=
    eq_one_of_two_elem_of_u35 h φU hsimp hodd h9 ⟨k, by simpa using congrArg Subtype.val hk⟩ hxA
  have hx : x = 1 := Subtype.ext hx1
  subst hx
  simp at hne

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd
