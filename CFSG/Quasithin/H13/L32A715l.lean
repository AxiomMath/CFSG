module

public import CFSG.Quasithin.H13.L32A715k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem prime_dvd_card {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) : p = 2 ∨ p = 3 := by
  by_contra hne
  push Not at hne
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have : Fact p.Prime := ⟨hp⟩
  have := E.kdot_normal
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hxp : x ^ p ^ 1 = 1 := by rw [pow_one, ← hx, pow_orderOf_eq_one]
  have hxC := comm_of_pow_prime E.isPOnePlusTwo_kdot hp hp5 hxp
  have hxCen : x ∈ Subgroup.centralizer
      ((modO2Image (hz T V) (oTwoUpper H) : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    calc k * x = x * k * x⁻¹ * x := by rw [hxC k hk]
      _ = x * k := by group
  obtain ⟨b, hb⟩ := E.isPGroup_centralizer ⟨x, hxCen⟩
  have hb' : x ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 := orderOf_dvd_of_pow_eq_one hb'
  rw [hx] at h1
  exact hne.2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h1))

theorem not_two_dvd_index_tdot : ¬ 2 ∣ (modO2Image (hz T V) T).index := by
  have hT := E.S.hyp.fsu.sylow
  have hidx : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index E.t_le_hz]
    exact Dvd.dvd.mul_right hd _
  intro h2
  exact hidx (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

theorem sup_eq_top :
    modO2Image (hz T V) (oTwoUpper H) ⊔ modO2Image (hz T V) T = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := modO2Image (hz T V) (oTwoUpper H) ⊔ modO2Image (hz T V) T with hX
  by_contra hne
  have hidx1 : X.index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hidx1
  rcases E.prime_dvd_card hp (hpd.trans X.index_dvd_card) with rfl | rfl
  · exact E.not_two_dvd_index_tdot (hpd.trans (Subgroup.index_dvd_of_le le_sup_right))
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    have hPK : (P : Subgroup _) ≤ modO2Image (hz T V) (oTwoUpper H) := by
      intro x hx
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      exact E.mem_kdot_of_pow hF (m := k) (by simpa using congrArg Subtype.val hk)
    exact P.not_dvd_index (hpd.trans (Subgroup.index_dvd_of_le (hPK.trans le_sup_left)))

theorem lemma14_7_15_three_of : H = hz T V ∧ H = oTwoUpper H ⊔ T := by
  have hKT : hz T V ≤ oTwoUpper H ⊔ T := by
    intro g hg
    have hmem : QuotientGroup.mk (⟨g, hg⟩ : ↥(hz T V)) ∈
        modO2Image (hz T V) (oTwoUpper H) ⊔ modO2Image (hz T V) T := by
      rw [E.sup_eq_top hF]
      exact Subgroup.mem_top _
    have := E.kdot_normal
    obtain ⟨x, hx, t, ht, hxt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    obtain ⟨k, hkK, rfl⟩ := mem_modO2Image_iff.mp hx
    obtain ⟨t', htT, rfl⟩ := mem_modO2Image_iff.mp ht
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxt
    have hq : ((k * t')⁻¹ * ⟨g, hg⟩ : ↥(hz T V)).1 ∈ pCoreOf 2 (hz T V) := ⟨_, hxt, rfl⟩
    have hqT : ((k * t')⁻¹ * ⟨g, hg⟩ : ↥(hz T V)).1 ∈ T :=
      pCoreOf_le_of_le E.S.hyp E.t_le_hz hq
    have e : g = (k : G) * t' * ((k * t')⁻¹ * ⟨g, hg⟩ : ↥(hz T V)).1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hkK)
      (Subgroup.mem_sup_right htT)) (Subgroup.mem_sup_right hqT)
  have hKTH : oTwoUpper H ⊔ T ≤ H := sup_le (oTwoUpper_le H) (le_sup_right.trans E.S.hz.1.1)
  have h1 : H = hz T V := le_antisymm E.le_hz (hKT.trans hKTH)
  exact ⟨h1, le_antisymm (h1 ▸ hKT) hKTH⟩

end Ctx7153

end CFSG.Quasithin.H13.L32A
