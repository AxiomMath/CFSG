module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Common
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.J3
public import CFSG.Sporadic.SmallOddCore.J3

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem localRank_three_le_two_of_centralizer {H : Type} [Group H] [Finite H]
    (h : ∀ t : H, orderOf t = 2 → ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set H))) :
    localRank 3 H ≤ 2 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three H (by change 0 < localRank 3 H; omega)
  change Assembly.pRank 3 L = localRank 3 H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3
    Nat.prime_three L
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  set k := Assembly.pRank 3 (Subgroup.normalizer (P : Set H)) with hk
  have hk3 : 3 ≤ k := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer E P hEL
  have : IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (hE.2 g g.2) }
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hEc]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3)
  have hp : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := E) (H := P) hp
  obtain ⟨B, hB, hBne⟩ : ∃ B : Subgroup E, B.index = 3 ∧
      CFSG.fixedPointSubgroup B P ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hP1 : (⊤ : Subgroup P) = ⊥ := by
      rw [← hgen]
      exact iSup_eq_bot.mpr fun B => iSup_eq_bot.mpr fun hB => hno B hB
    apply hP
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : P) ∈ (⊥ : Subgroup P) := hP1 ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)
  set Q := CFSG.fixedPointSubgroup B P
  have hQ2 : IsPGroup 2 Q := hP2.to_subgroup Q
  have hdvd : 2 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rcases n with _ | n
    · exact (hBne ((Subgroup.eq_bot_iff_card Q).mpr (by simpa using hn))).elim
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set t' : H := ((t : P) : H)
  have ht' : orderOf t' = 2 := by
    rw [show t' = ((t : P) : H) from rfl, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hfix : ∀ b : B, (b : H) * t' * (b : H)⁻¹ = t' := fun b => by
    have h1 : (b : E) • (t : P) = t := t.2 b
    exact congrArg Subtype.val h1
  set B' := B.map E.subtype
  have hB'C : B' ≤ Subgroup.centralizer ({t'} : Set H) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix ⟨b, hb⟩
    exact (eq_mul_inv_iff_mul_eq.mp this.symm).symm
  have hBc : Nat.card B' * 3 = 3 ^ k := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    have h1 := Subgroup.card_mul_index B
    rw [hB, hEc] at h1
    exact h1
  have h9 : 9 ∣ Nat.card B' := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have : Nat.card B' = 3 ^ (m + 2) := by
      have h := hBc
      rw [hm, pow_succ] at h
      omega
    rw [this, pow_add]
    exact Dvd.intro_left _ rfl
  exact h t' ht' (h9.trans (Subgroup.card_dvd_of_le hB'C))

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native in
theorem card_centralizer_j3P {t : j3P} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set j3P)) = 1920 := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have htR : (t : Equiv.Perm (Fin 6156)) ∈ j3R := (le_sup_left : j3P ≤ j3P ⊔ _) t.2
  have ht2 : orderOf (t : Equiv.Perm (Fin 6156)) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨r, hr, g, hg, hrep⟩ := hcover _ htR ht2
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrepP : tp 6156 r.rep ∈ j3P := by
    have h1 := j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) t.2) hg
    rwa [hrep, show g⁻¹ * (g * tp 6156 r.rep * g⁻¹) * g = tp 6156 r.rep by group] at h1
  have hrout : r.outer = false := by
    cases h : r.outer
    · rfl
    · exact absurd hrepP (hout.1 h)
  have hr1920 : r.centOrder = 1920 := by
    have hm := List.mem_map_of_mem (f := fun r => (r.outer, r.classSize, r.centOrder)) hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · rw [hrout] at h
      exact absurd h (by decide)
  rw [card_centralizer_subgroup, hrep, inf_centralizer_conj j3P hg,
    Subgroup.card_map_of_injective (MulAut.conj g).injective, hcent, hr1920]

open CFSG.Blueprint CFSG.Sporadic.Schreier TauCeti in
theorem excluded433_J3 : Excluded433 (.sporadic .J3) :=
  excluded433_sporadic_of_equiv (T := j3P)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_J3.map fun e =>
      e.trans j3PermEquiv)
    fun _ _ _ hG eT => false_of_localRank_three_le_two_of_equiv hG eT
      (localRank_three_le_two_of_centralizer fun t ht h9 => by
        rw [card_centralizer_j3P ht] at h9
        exact absurd h9 (by norm_num))

end CFSG.RankThree.PartTwo.Census
