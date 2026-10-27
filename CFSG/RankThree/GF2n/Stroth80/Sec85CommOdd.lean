module

public import CFSG.RankThree.GF2n.Stroth80.Sec8SpTransvectionPair
public import CFSG.RankThree.GF2n.Stroth80.Sec85F2
public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec83SpFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.F2Fixed (fixedSub mem_fixedSub comm comm_apply ker_comm fixedSub_anti
  card_eq_card_fixedSub_mul_card_range)
open scoped commutatorElement Matrix

section Fixed

variable {X : Type*} [Group X] {M : Type*} [AddCommGroup M] [DistribMulAction X M]

theorem fixedSub_mul_eq_bot_of_smul_sq (h2 : ∀ m : M, m + m = 0) {x y : X}
    (hx : ∀ n : M, x • x • n = n) (hy : ∀ n : M, y • y • n = n)
    (h : fixedSub M {x} ⊓ fixedSub M {y} = ⊥) :
    fixedSub M {x * y} = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  have hxy : x • y • m = m := by rw [← mul_smul]; exact hm _ rfl
  have hym : y • m = x • m := by
    have := congrArg (fun n => x • n) hxy
    simp only [hx] at this
    exact this
  have hyx : y • x • m = m := by
    rw [← hym, hy]
  have hn : m + x • m ∈ fixedSub M {x} ⊓ fixedSub M {y} := by
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg, smul_add, hx, add_comm]
    · rw [Set.mem_singleton_iff.mp hg, smul_add, hym, hyx, add_comm]
  rw [h, AddSubgroup.mem_bot] at hn
  have hxm : x • m = m := by
    have : x • m = -m := eq_neg_of_add_eq_zero_right hn
    rw [this, neg_eq_of_add_eq_zero_right (h2 m)]
  have : m ∈ fixedSub M {x} ⊓ fixedSub M {y} := by
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg]; exact hxm
    · rw [Set.mem_singleton_iff.mp hg, hym, hxm]
  rw [h] at this
  exact this

theorem fixedSub_singleton_eq_of_range [Finite M] {x : X} {F : AddSubgroup M}
    (hr : (comm M x).range = F) (hc : Nat.card M = Nat.card F ^ 2)
    (hle : F ≤ fixedSub M {x}) : fixedSub M {x} = F := by
  have h1 := card_eq_card_fixedSub_mul_card_range (M := M) x
  rw [hr, hc, sq] at h1
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h2 : Nat.card (fixedSub M {x}) = Nat.card F := (Nat.eq_of_mul_eq_mul_right hpos h1.symm)
  exact (AddSubgroup.eq_of_le_of_card_ge hle h2.le).symm

end Fixed

section Odd

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec85_exists_fpf (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ y ∈ Rt M (LB M Q B) t, y ^ 3 = 1 ∧ ∀ c ∈ hc.CN t, ⁅y, c⁆ ∈ Z0 → c ∈ Z0 := by
  classical
  have hRoot := stroth310Root_of_34 h34
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  obtain ⟨r, hr, -, hopp, -⟩ := sec8_Z0_data h51 hA hc hs hZ0
  obtain ⟨m, hm2, hmSp⟩ := hs.sp
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hRM := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hρ)) y).mp hy
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ c ∈ hc.CN t, ρ * c * ρ⁻¹ ∈ hc.CN t :=
    fun ρ hρ c hc' => hc.CN_conj_mem ht hρ hc'
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, ρ * z * ρ⁻¹ ∈ Z0 := fun ρ hρ z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormQ hρ) z).mp hz
  have hsec : SecHyp (Rt M (LB M Q B) t) (hc.CN t) Z0 := SecHyp.of_isOppDecomp hopp hP hI
  have hN : ∀ c ∈ hc.CN t, ∀ d ∈ hc.CN t, ⁅c, d⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  obtain ⟨Mo, iMo, iAct, κ, hκ, hkerAct⟩ := exists_sectionModule_ker hpts.ker hsec hN
  haveI : Finite Mo := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hopp hLR hLCR
  obtain ⟨a, ha, b, hb, hna, hnb, hab3⟩ := exists_transvection_pair_order_three (K := K) hpts.uu'
  have ha' : a ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ := by
    rw [hpts.hL]
    exact ha
  have hb' : b ∈ ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ := by
    rw [hL2]
    exact hb
  obtain ⟨la, hla, hlaφ⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨lb, hlb, hlbφ⟩ := Subgroup.mem_map.mp hb'
  have hsym : spForm m K u' u = spForm m K u u' := by
    rw [← (spForm_isAlt (m := m) (K := K)).neg_eq, CharTwo.neg_eq]
  have hFa := stroth_2_1_fixed_of_hom φ hpts.range (by omega) hκ.two hkerAct hpts.uu' hpts.hL hL2
    hdec (x := la) (by rw [hlaφ]; exact ha) (by rw [hlaφ]; exact hna)
  have hFb := stroth_2_1_fixed_of_hom φ hpts.range (by omega) hκ.two hkerAct
    (by rw [hsym]; exact hpts.uu') hL2 hpts.hL hdec.symm (x := lb) (by rw [hlbφ]; exact hb)
    (by rw [hlbφ]; exact hnb)
  have hka : fixedSub Mo {la} =
      fixedSub Mo (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) : Subgroup ↥(Rt M (LB M Q B) t)) :
        Set ↥(Rt M (LB M Q B) t)) :=
    fixedSub_singleton_eq_of_range hFa.1 hFa.2 (fixedSub_anti (Set.singleton_subset_iff.mpr hla))
  have hkb : fixedSub Mo {lb} =
      fixedSub Mo (((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) :=
    fixedSub_singleton_eq_of_range hFb.1 hFb.2 (fixedSub_anti (Set.singleton_subset_iff.mpr hlb))
  have hinf : fixedSub Mo {la} ⊓ fixedSub Mo {lb} = ⊥ := by
    rw [hka, hkb]
    exact hdec.inf_eq_bot
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hker_mem : ∀ g : ↥(Rt M (LB M Q B) t), (g : G) ∈ hc.CN t → ∀ a' : Mo, g • a' = a' :=
    fun g hg a' => hkerAct g (by rw [hpts.ker]; exact Subgroup.mem_subgroupOf.mpr hg) a'
  have hlaa : ∀ a' : Mo, la • la • a' = a' := by
    intro a'
    rw [← mul_smul]
    refine hker_mem _ (hQN ?_) a'
    have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp hla)
    rwa [sq] at this
  have hlbb : ∀ a' : Mo, lb • lb • a' = a' := by
    intro a'
    rw [← mul_smul]
    refine hker_mem _ (hQN ?_) a'
    have := (hc.conj_of_mem hrM).sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp hlb)
    rwa [sq] at this
  have hgfix : fixedSub Mo {la * lb} = ⊥ := fixedSub_mul_eq_bot_of_smul_sq hκ.two hlaa hlbb hinf
  have hN2 : IsPGroup 2 ↥(hc.CN t) := sec8_isPGroup_CN h34 h51 hA hc hs hZ0
  set g : ↥(Rt M (LB M Q B) t) := la * lb with hg
  have hgφ : φ (g ^ 3) = 1 := by
    rw [map_pow, hg, map_mul, hlaφ, hlbφ]
    exact hab3
  have hg3ker : g ^ 3 ∈ φ.ker := hgφ
  have hg3 : ((g ^ 3 : ↥(Rt M (LB M Q B) t)) : G) ∈ hc.CN t := by
    have h1 := hg3ker
    rw [hpts.ker] at h1
    exact h1
  obtain ⟨k, hk⟩ := hN2 ⟨((g ^ 3 : ↥(Rt M (LB M Q B) t)) : G), hg3⟩
  have hk' : (((g ^ 3 : ↥(Rt M (LB M Q B) t)) : G)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hn3 : (g ^ 3) ^ (2 ^ k) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk')
  have hy3 : (g ^ (4 ^ k)) ^ 3 = 1 := by
    have e1 : (g ^ (4 ^ k)) ^ 3 = (g ^ 3) ^ (4 ^ k) := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have e2 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    rw [e1, e2, pow_mul, hn3, one_pow]
  obtain ⟨c, hc4⟩ : ∃ c : ℕ, 4 ^ k = 3 * c + 1 := ⟨4 ^ k / 3, by
    have : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega⟩
  have hacty : ∀ a : Mo, (g ^ (4 ^ k)) • a = g • a := by
    intro a
    rw [hc4, pow_add, pow_mul, mul_smul, pow_one]
    exact hkerAct _ (Subgroup.pow_mem _ hg3ker c) _
  have hfy : fixedSub Mo {g ^ (4 ^ k)} = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : (g ^ (4 ^ k)) • a = a := mem_fixedSub.mp ha _ rfl
    rw [hacty] at h1
    have h2 : a ∈ fixedSub Mo {g} := mem_fixedSub.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h1
    rw [hgfix] at h2
    exact h2
  refine ⟨((g ^ (4 ^ k) : ↥(Rt M (LB M Q B) t)) : G), (g ^ (4 ^ k)).2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hy3]
    rfl
  · intro c' hcN hcomm
    set y : ↥(Rt M (LB M Q B) t) := g ^ (4 ^ k) with hy
    have hcP : (y : G) * c' * (y : G)⁻¹ ∈ hc.CN t := hP (y : G) y.2 c' hcN
    have hact := hκ.act y ⟨c', hcN⟩ ⟨(y : G) * c' * (y : G)⁻¹, hcP⟩ rfl
    have heq : κ ⟨(y : G) * c' * (y : G)⁻¹, hcP⟩ = κ ⟨c', hcN⟩ := by
      rw [hκ.eq_iff]
      have e : (y : G) * c' * (y : G)⁻¹ * c'⁻¹ = ⁅(y : G), c'⁆ := by
        simp [commutatorElement_def]
      show (y : G) * c' * (y : G)⁻¹ * c'⁻¹ ∈ Z0
      rw [e]
      exact hcomm
    rw [heq] at hact
    have hfix : Multiplicative.toAdd (κ ⟨c', hcN⟩) ∈ fixedSub Mo {y} := by
      refine mem_fixedSub.mpr fun x hx => ?_
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h1 := congrArg Multiplicative.toAdd hact
      rw [toAdd_ofAdd] at h1
      exact h1.symm
    rw [hfy] at hfix
    have h0 : κ ⟨c', hcN⟩ = 1 :=
      Multiplicative.toAdd.injective (show Multiplicative.toAdd (κ ⟨c', hcN⟩) = 0 from hfix)
    exact (hκ.ker ⟨c', hcN⟩).mp h0

end Odd

end CFSG.RankThree.GF2n.Stroth80
