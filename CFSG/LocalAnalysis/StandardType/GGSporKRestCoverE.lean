module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpec
public import CFSG.LocalAnalysis.StandardType.GGSporKRestIdx

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRestECond_spec {n p : ℕ} {mul : List (List ℕ)} {good : List Bool}
    (h : sporKRestECond n p mul good = true) :
    ∀ a < n, ∀ b < n, a ≠ 0 → b ≠ 0 → sporKRestMulIdx mul a b = sporKRestMulIdx mul b a →
      sporKRestPowIdx mul a p = 0 → sporKRestPowIdx mul b p = 0 →
      (∀ i < p, sporKRestPowIdx mul a i ≠ b) →
      ∃ i < p, ∃ j < p,
        good.getD (sporKRestMulIdx mul (sporKRestPowIdx mul a i) (sporKRestPowIdx mul b j)) false =
          true := by
  intro a ha b hb ha0 hb0 hmulIdx hpa hpb hbnotpow
  unfold sporKRestECond at h
  rw [List.all_eq_true] at h
  have hb' :=
    (List.all_eq_true.mp (h a (List.mem_range.mpr ha))) b (List.mem_range.mpr hb)
  rw [Bool.or_eq_true] at hb'
  rcases hb' with hbad | hgood
  · exfalso
    rw [Bool.not_eq_true'] at hbad
    have hchain : (decide (a ≠ 0) && decide (b ≠ 0) &&
        decide (sporKRestMulIdx mul a b = sporKRestMulIdx mul b a) &&
        decide (sporKRestPowIdx mul a p = 0) && decide (sporKRestPowIdx mul b p = 0) &&
        (List.range p).all fun i => decide (sporKRestPowIdx mul a i ≠ b)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨⟨⟨⟨ha0, hb0⟩, hmulIdx⟩, hpa⟩, hpb⟩,
        fun i hi => hbnotpow i (List.mem_range.mp hi)⟩
    rw [hchain] at hbad
    exact Bool.noConfusion hbad
  · obtain ⟨i, hi, hgood⟩ := List.any_eq_true.mp hgood
    obtain ⟨j, hj, hgood⟩ := List.any_eq_true.mp hgood
    exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, hgood⟩

theorem sporKRestPowIdx_spec {K : Type} [Group K] (T : List K) (h0 : T.getD 0 1 = 1)
    (mul : List (List ℕ))
    (hmul : ∀ i j, i < T.length → j < T.length →
      sporKRestMulIdx mul i j < T.length ∧
        T.getD i 1 * T.getD j 1 = T.getD (sporKRestMulIdx mul i j) 1)
    (hlen : 0 < T.length) {a : ℕ} (ha : a < T.length) (k : ℕ) :
    sporKRestPowIdx mul a k < T.length ∧
      T.getD (sporKRestPowIdx mul a k) 1 = (T.getD a 1) ^ k := by
  induction k with
  | zero =>
      simp only [sporKRestPowIdx, pow_zero]
      exact ⟨hlen, h0⟩
  | succ k ih =>
      obtain ⟨ihlt, iheq⟩ := ih
      have hm := hmul (sporKRestPowIdx mul a k) a ihlt ha
      refine ⟨hm.1, ?_⟩
      show T.getD (sporKRestMulIdx mul (sporKRestPowIdx mul a k) a) 1 = (T.getD a 1) ^ (k + 1)
      rw [← hm.2, iheq, pow_succ]

theorem sporKRest_exists_independent_pair {K : Type} [Group K] {p : ℕ} (hp : p.Prime)
    (E : Subgroup K) (hE2 : Nat.card E = p ^ 2) (hEp : ∀ x ∈ E, x ^ p = 1) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ ∀ i : ℕ, a ^ i ≠ b := by
  classical
  have hfin : Finite ↥E :=
    Nat.finite_of_card_ne_zero (by rw [hE2]; exact pow_ne_zero 2 hp.ne_zero)
  haveI := hfin
  letI : Fintype ↥E := Fintype.ofFinite ↥E
  have hcardE : 1 < Nat.card ↥E := by rw [hE2]; nlinarith [hp.two_le]
  have hbot : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hcardE
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hbot
  obtain ⟨a, haE, ha1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hex : ∃ b ∈ E, ∀ i : ℕ, a ^ i ≠ b := by
    by_contra hno
    simp only [not_exists, not_and, not_forall, not_ne_iff] at hno
    have hle : Nat.card ↥E ≤ p := by
      let s : Finset ↥E := (Finset.range p).image fun i => (⟨a ^ i, E.pow_mem haE i⟩ : ↥E)
      have hs_card : s.card ≤ p := by
        calc s.card ≤ (Finset.range p).card := Finset.card_image_le
          _ = p := Finset.card_range p
      have huniv : (Finset.univ : Finset ↥E) ⊆ s := by
        intro x _
        obtain ⟨i, hi⟩ := hno (x : K) x.2
        refine Finset.mem_image.mpr ⟨i % p, Finset.mem_range.mpr (Nat.mod_lt i hp.pos), ?_⟩
        refine Subtype.ext ?_
        change a ^ (i % p) = (x : K)
        rw [show a ^ (i % p) = a ^ i from
          (pow_eq_pow_mod (a := a) (n := p) i (hEp a haE)).symm]
        exact hi
      calc Nat.card ↥E = Fintype.card ↥E := Nat.card_eq_fintype_card
        _ = (Finset.univ : Finset ↥E).card := (Finset.card_univ).symm
        _ ≤ s.card := Finset.card_le_card huniv
        _ ≤ p := hs_card
    have hle' : p ^ 2 ≤ p := by rw [← hE2]; exact hle
    nlinarith [hp.two_le, hle']
  obtain ⟨b, hbE, hb⟩ := hex
  exact ⟨a, haE, b, hbE, ha1, hb⟩

theorem sporKRest_cover_of_data_E {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (S : Sylow p K) (T : List K) (hnd : T.Nodup) (h0 : T.getD 0 1 = 1)
    (hT : ∀ x ∈ (S : Subgroup K), x ∈ T) (hTS : ∀ t ∈ T, t ∈ (S : Subgroup K))
    (mul : List (List ℕ))
    (hmul : ∀ i j, i < T.length → j < T.length →
      sporKRestMulIdx mul i j < T.length ∧
        T.getD i 1 * T.getD j 1 = T.getD (sporKRestMulIdx mul i j) 1)
    (reps : List K) (hreps : ∀ r ∈ reps, ∀ x : K, IsConj r x → SporKRestGenerating p x)
    (good : List Bool) (hgood0 : good.getD 0 false = false)
    (hgood : ∀ i, i < T.length → good.getD i false = true →
      ∃ r ∈ reps, ∃ g : K, g⁻¹ * r * g = T.getD i 1)
    (hcond : sporKRestECond T.length p mul good = true) : SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hST : ∀ x : K, x ∈ (S : Subgroup K) ↔ x ∈ T := fun x => ⟨hT x, hTS x⟩
  intro E hE hE2
  obtain ⟨a, haE, b, hbE, ha1, hb⟩ :=
    sporKRest_exists_independent_pair hp E hE2 hE.2
  have hEpgroup : IsPGroup p ↥E := IsPGroup.of_card hE2
  obtain ⟨Q, hEQ⟩ := hEpgroup.exists_le_sylow
  letI : MulAction.IsPretransitive K (Sylow p K) :=
    Sylow.isPretransitive_of_finite (p := p) (G := K)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := K) S Q
  have hconjS : ∀ y ∈ E, g⁻¹ * y * g ∈ (S : Subgroup K) := by
    intro y hy
    have hyQ : y ∈ ((g • S : Sylow p K) : Subgroup K) := by
      rw [hg]; exact hEQ hy
    rw [Sylow.coe_subgroup_smul] at hyQ
    refine (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj g)
      (S := (S : Subgroup K)) (x := g⁻¹ * y * g)).mp ?_
    have hax : (MulAut.conj g) • (g⁻¹ * y * g) = y := by
      change (MulAut.conj g) (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group
    rw [hax]
    exact hyQ
  have haT : g⁻¹ * a * g ∈ T := (hST _).mp (hconjS a haE)
  have hbT : g⁻¹ * b * g ∈ T := (hST _).mp (hconjS b hbE)
  obtain ⟨ia, hia, hiaEq⟩ := List.mem_iff_getElem.mp haT
  obtain ⟨ib, hib, hibEq⟩ := List.mem_iff_getElem.mp hbT
  have hiaD : T.getD ia 1 = g⁻¹ * a * g := by
    rw [List.getD_eq_getElem T 1 hia, hiaEq]
  have hibD : T.getD ib 1 = g⁻¹ * b * g := by
    rw [List.getD_eq_getElem T 1 hib, hibEq]
  have hlen : 0 < T.length := lt_of_le_of_lt (Nat.zero_le ia) hia
  have hget_inj : ∀ i j (hi : i < T.length) (hj : j < T.length),
      T.getD i 1 = T.getD j 1 → i = j := by
    intro i j hi hj h
    rw [List.getD_eq_getElem T 1 hi, List.getD_eq_getElem T 1 hj] at h
    exact (List.Nodup.getElem_inj_iff hnd).mp h
  have ha'p : (g⁻¹ * a * g) ^ p = 1 := by
    have h1 : (g⁻¹ * a * g) = (g⁻¹ * a * (g⁻¹)⁻¹) := by rw [inv_inv]
    rw [h1, conj_pow, hE.2 a haE]
    group
  have hb'p : (g⁻¹ * b * g) ^ p = 1 := by
    have h1 : (g⁻¹ * b * g) = (g⁻¹ * b * (g⁻¹)⁻¹) := by rw [inv_inv]
    rw [h1, conj_pow, hE.2 b hbE]
    group
  have ha'1 : g⁻¹ * a * g ≠ 1 := by
    intro h
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hb1 : b ≠ 1 := by
    intro h
    exact hb 0 (by rw [h, pow_zero])
  have hb'1 : g⁻¹ * b * g ≠ 1 := by
    intro h
    apply hb1
    calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hab_comm : a * b = b * a := by
    have h := hE.1.is_comm.comm (⟨a, haE⟩ : ↥E) (⟨b, hbE⟩ : ↥E)
    simpa using congrArg Subtype.val h
  have ha'b'_comm : (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
    calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hab_comm]
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group
  have hconj : ∀ i j : ℕ,
      g⁻¹ * (a ^ i * b ^ j) * g = (g⁻¹ * a * g) ^ i * (g⁻¹ * b * g) ^ j := by
    intro i j
    have h1 : (g⁻¹ * a * g) ^ i = g⁻¹ * a ^ i * g := by
      have hc := conj_pow (a := g⁻¹) (b := a) (i := i)
      simpa using hc
    have h2 : (g⁻¹ * b * g) ^ j = g⁻¹ * b ^ j * g := by
      have hc := conj_pow (a := g⁻¹) (b := b) (i := j)
      simpa using hc
    rw [h1, h2]; group
  have ha'b'_pow : ∀ i : ℕ, (g⁻¹ * a * g) ^ i ≠ g⁻¹ * b * g := by
    intro i h
    apply hb i
    calc a ^ i = (g * (g⁻¹ * a * g) * g⁻¹) ^ i := by
          rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
      _ = g * (g⁻¹ * a * g) ^ i * g⁻¹ := conj_pow
      _ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h]
      _ = b := by group
  have hia0 : ia ≠ 0 := by
    intro h
    apply ha'1
    rw [← hiaD, h, h0]
  have hib0 : ib ≠ 0 := by
    intro h
    apply hb'1
    rw [← hibD, h, h0]
  have hmulIdx_comm : sporKRestMulIdx mul ia ib = sporKRestMulIdx mul ib ia := by
    have h1 := hmul ia ib hia hib
    have h2 := hmul ib ia hib hia
    apply hget_inj _ _ h1.1 h2.1
    rw [← h1.2, ← h2.2, hiaD, hibD, ha'b'_comm]
  have hpowIa : sporKRestPowIdx mul ia p = 0 := by
    have hspec := sporKRestPowIdx_spec T h0 mul hmul hlen hia p
    apply hget_inj _ _ hspec.1 hlen
    rw [hspec.2, hiaD, ha'p, h0]
  have hpowIb : sporKRestPowIdx mul ib p = 0 := by
    have hspec := sporKRestPowIdx_spec T h0 mul hmul hlen hib p
    apply hget_inj _ _ hspec.1 hlen
    rw [hspec.2, hibD, hb'p, h0]
  have hbnotpow : ∀ i < p, sporKRestPowIdx mul ia i ≠ ib := by
    intro i _hip h
    apply ha'b'_pow i
    have hspec := sporKRestPowIdx_spec T h0 mul hmul hlen hia i
    calc (g⁻¹ * a * g) ^ i = (T.getD ia 1) ^ i := by rw [hiaD]
      _ = T.getD (sporKRestPowIdx mul ia i) 1 := hspec.2.symm
      _ = T.getD ib 1 := by rw [h]
      _ = g⁻¹ * b * g := hibD
  obtain ⟨i, _hip, j, _hjp, hgoodij⟩ :=
    sporKRestECond_spec hcond ia hia ib hib hia0 hib0 hmulIdx_comm hpowIa hpowIb hbnotpow
  have hia_i : sporKRestPowIdx mul ia i < T.length :=
    (sporKRestPowIdx_spec T h0 mul hmul hlen hia i).1
  have hib_j : sporKRestPowIdx mul ib j < T.length :=
    (sporKRestPowIdx_spec T h0 mul hmul hlen hib j).1
  have hk : sporKRestMulIdx mul (sporKRestPowIdx mul ia i) (sporKRestPowIdx mul ib j) <
      T.length := (hmul _ _ hia_i hib_j).1
  have hk_val : T.getD (sporKRestMulIdx mul (sporKRestPowIdx mul ia i)
        (sporKRestPowIdx mul ib j)) 1 = (g⁻¹ * a * g) ^ i * (g⁻¹ * b * g) ^ j := by
    rw [← (hmul _ _ hia_i hib_j).2,
        (sporKRestPowIdx_spec T h0 mul hmul hlen hia i).2,
        (sporKRestPowIdx_spec T h0 mul hmul hlen hib j).2, hiaD, hibD]
  have hk0 : sporKRestMulIdx mul (sporKRestPowIdx mul ia i) (sporKRestPowIdx mul ib j) ≠ 0 := by
    intro h0k
    rw [h0k, hgood0] at hgoodij
    rw [Bool.false_eq_true] at hgoodij
    exact hgoodij
  obtain ⟨r, hr, g', hg'⟩ :=
    hgood (sporKRestMulIdx mul (sporKRestPowIdx mul ia i) (sporKRestPowIdx mul ib j)) hk hgoodij
  refine ⟨a ^ i * b ^ j, E.mul_mem (E.pow_mem haE i) (E.pow_mem hbE j), ?_, ?_⟩
  · intro hx1
    apply hk0
    apply hget_inj _ _ hk hlen
    calc T.getD (sporKRestMulIdx mul (sporKRestPowIdx mul ia i)
            (sporKRestPowIdx mul ib j)) 1
        = (g⁻¹ * a * g) ^ i * (g⁻¹ * b * g) ^ j := hk_val
      _ = g⁻¹ * (a ^ i * b ^ j) * g := (hconj i j).symm
      _ = 1 := by rw [hx1]; group
      _ = T.getD 0 1 := h0.symm
  · have hconj_r_t : IsConj r
        (T.getD (sporKRestMulIdx mul (sporKRestPowIdx mul ia i)
          (sporKRestPowIdx mul ib j)) 1) := by
      rw [isConj_iff]
      exact ⟨g'⁻¹, by rw [inv_inv]; exact hg'⟩
    have hconj_t_x : IsConj
        (T.getD (sporKRestMulIdx mul (sporKRestPowIdx mul ia i)
          (sporKRestPowIdx mul ib j)) 1) (a ^ i * b ^ j) := by
      rw [isConj_iff]
      refine ⟨g, ?_⟩
      rw [hk_val, ← hconj i j]
      group
    exact hreps r hr (a ^ i * b ^ j) (hconj_r_t.trans hconj_t_x)

end CFSG.StandardType.SporadicShape
