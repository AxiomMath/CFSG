module

public import CFSG.Quasithin.Vol2.KGFactC31Act
public import Certificates.Certificate7199
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native

theorem prime_dvd_j2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 604800) : p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)

theorem rep_genTab {j : ℕ} (hj : j < 7) :
    Rep 315 (J2.genTab j) (j2StrongPerm j) := by
  have h := rep_j2StrongPerm hj
  intro i hi
  rw [J2.genTab, ap_ofFn _ hi, idx_of_lt _ hi, UInt32.toNat_ofNat', h ⟨i, hi⟩,
    Nat.mod_eq_of_lt (lt_trans (Fin.isLt _) (by norm_num))]
  rfl

theorem noOddAct_j2P :
    NoOddAct ↥j2P := by
  obtain ⟨h5a, h5b, h7, hcomm, hinj, hc5, hc7⟩ := Certificates.certificate7199
  have hQ : ValidSchreier j2Chain := j2Chain_valid.1
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hcard : Nat.card j2P = 604800 := card_j2P
  have hgens : ∀ l, J2.gensG l ∈ j2P := fun l => by
    unfold J2.gensG
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrep : ∀ l, Rep 315 (J2.gensT l) (J2.gensG l) := fun l => by
    unfold J2.gensT J2.gensG
    split_ifs
    · exact rep_genTab (by norm_num)
    · exact rep_genTab (by norm_num)
  have htabs : orderTables j2Chain 2 = J2.invTabs := by
    unfold orderTables J2.invTabs
    rw [CFSG.ComponentClassification.J2Cover.levelTables_eq j2ChainArrays
      (chainCheckFacts PairJ2.chain_check.1)]
  have hinvs : ∀ t : j2P, orderOf t = 2 →
      ∃ T ∈ J2.invTabs, Rep 315 T (t : Equiv.Perm (Fin 315)) := fun t ht => by
    rw [← htabs]
    exact exists_orderTables hn _ hQ (by rw [← j2P_eq_original]; exact t.2)
      (by rw [Subgroup.orderOf_coe]; exact ht)
  have hword : ∀ w : List ℤ, ∃ x : j2P, (x : Equiv.Perm (Fin 315)) = wordG J2.gensG w ∧
      Rep 315 (wordT 315 J2.gensT w) (x : Equiv.Perm (Fin 315)) := fun w =>
    ⟨⟨wordG J2.gensG w, wordG_mem_of _ hgens w⟩, rfl, Rep.wordT hn w fun l _ => hrep l⟩
  have hord : ∀ {q : ℕ} {w : List ℤ} {x : j2P}, 0 < q →
      Rep 315 (wordT 315 J2.gensT w) (x : Equiv.Perm (Fin 315)) →
      ordTest 315 q (wordT 315 J2.gensT w) = true → orderOf x = q := fun hq hx h => by
    rw [← Subgroup.orderOf_coe]
    exact (ordTest_iff perm_faithful hx hq).1 h
  intro p hp hp5 y hy W hW hyW t ht
  by_cases hpd : p ∣ 604800
  · rcases prime_dvd_j2 hp hp5 hpd with rfl | rfl
    ·
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨x, -, hx⟩ := hword J2.w5a
      obtain ⟨z, -, hz⟩ := hword J2.w5b
      have hox := hord (by norm_num) hx h5a
      have hoz := hord (by norm_num) hz h5b
      have hxz : Commute x z := by
        apply Subtype.ext
        have h1 := Rep.compT hx hz
        have h2 := Rep.compT hz hx
        exact rep_unique (rep_of_tblEq h2 hcomm) h1 |>.symm
      have hx5 : x ^ 5 = 1 := by rw [← hox]; exact pow_orderOf_eq_one x
      have hz5 : z ^ 5 = 1 := by rw [← hoz]; exact pow_orderOf_eq_one z
      have hgrid : ∀ a b : ℕ, Rep 315 (compT 315 (powT 315 a (wordT 315 J2.gensT J2.w5a))
          (powT 315 b (wordT 315 J2.gensT J2.w5b)))
            ((x ^ a * z ^ b : j2P) : Equiv.Perm (Fin 315)) :=
        fun a b => by
          rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
          exact Rep.compT (Rep.powT hn hx a) (Rep.powT hn hz b)
      have hinj' : ∀ a < 5, ∀ b < 5, ∀ c < 5, ∀ d < 5, x ^ a * z ^ b = x ^ c * z ^ d →
          a = c ∧ b = d := by
        intro a ha b hb c hc d hd he
        unfold gridInj at hinj
        simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq, Bool.not_eq_true'] at hinj
        rcases hinj a ha b hb c hc d hd with h | h
        · exact h
        · exfalso
          have h1 := hgrid a b
          rw [he] at h1
          have heq : tblEq 315 (compT 315 (powT 315 a J2.x5aT) (powT 315 b J2.x5bT))
              (compT 315 (powT 315 c J2.x5aT) (powT 315 d J2.x5bT)) = true :=
            (tblEq_iff (n := 315)).2 fun i hi => (h1 i hi).trans (hgrid c d i hi).symm
          rw [heq] at h
          exact absurd h (by decide)
      set P := gridSubgroup (by norm_num) hx5 hz5 hxz
      have hcardP : Nat.card P = 5 ^ 2 := card_gridSubgroup _ hx5 hz5 hxz hinj'
      have hP : IsPGroup 5 P := IsPGroup.of_card hcardP
      have hPi : ¬ 5 ∣ P.index := by
        have h := P.card_mul_index
        rw [hcardP, hcard] at h
        omega
      refine forall_act_of_sylow hn hP hPi (fun u hu => ?_) hinvs hc5 hy hW hyW ht
      obtain ⟨a, ha, b, hb, rfl⟩ := hu
      refine ⟨_, ?_, hgrid a b⟩
      exact List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb,
        rfl⟩⟩
    ·
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨x, -, hx⟩ := hword J2.w7
      have hox := hord (by norm_num) hx h7
      have hcardx : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hox]
      have hP : IsPGroup 7 (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one])
      have hPi : ¬ 7 ∣ (Subgroup.zpowers x).index := by
        have h := (Subgroup.zpowers x).card_mul_index
        rw [hcardx, hcard] at h
        omega
      refine forall_act_of_sylow hn hP hPi (fun u hu => ?_) hinvs hc7 hy hW hyW ht
      have := exists_powTabs hn hx hu
      rwa [hox] at this
  · rw [eq_one_of_pow_of_not_dvd hp (by rwa [hcard]) hy]
    group

theorem noOddAct_j2 :
    NoOddAct NativeSporadic.J2 :=
  noOddAct_of_mulEquiv j2PermEquiv noOddAct_j2P

theorem inspC31SporadicAt_j2 :
    CFSG.Quasithin.InspC31SporadicAt .J2 :=
  inspC31SporadicAt_of_noOddAct noOddAct_j2

end CFSG.Quasithin.KGC31

end
