module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne
import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofW
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Three

variable {H : Type} [Group H]

theorem zpow_eq_zpow_of_emod_eq {a : H} (ha : a ^ 3 = 1) {k l : ℤ} (h : k % 3 = l % 3) :
    a ^ k = a ^ l := by
  have h1 := zpow_eq_zpow_emod' k ha
  have h2 := zpow_eq_zpow_emod' l ha
  push_cast at h1 h2
  rw [h1, h2, h]

theorem exists_nat_mul_emod_three {i : ℤ} (hi : i % 3 = 1 ∨ i % 3 = 2) (r : ℤ) :
    ∃ n : ℕ, ((n : ℤ) * i) % 3 = r % 3 := by
  rcases hi with hi | hi <;>
  rcases (show r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 by omega) with hr | hr | hr
  · exact ⟨0, by push_cast; omega⟩
  · exact ⟨1, by push_cast; omega⟩
  · exact ⟨2, by push_cast; omega⟩
  · exact ⟨0, by push_cast; omega⟩
  · exact ⟨2, by push_cast; omega⟩
  · exact ⟨1, by push_cast; omega⟩

theorem conj_eq_of_sq_conj_eq {x d : H} {m : ℕ} (hx : x ^ 3 ^ m = 1)
    (h2 : x ^ 2 * d * (x ^ 2)⁻¹ = d) : x * d * x⁻¹ = d := by
  have hC : x ^ 2 ∈ Subgroup.centralizer ({d} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 2 * d = x ^ 2 * d * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = d * x ^ 2 := by rw [h2]
  have hodd : (3 ^ m) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hpow : x = (x ^ 2) ^ ((3 ^ m + 1) / 2) := by
    rw [← pow_mul, show 2 * ((3 ^ m + 1) / 2) = 3 ^ m + 1 by omega, pow_succ, hx, one_mul]
  have hxC : x ∈ Subgroup.centralizer ({d} : Set H) := by
    rw [hpow]
    exact Subgroup.pow_mem _ hC _
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC
  rw [hxC]
  group

theorem conj_eq_of_mem_zpowers {x d : H} {m : ℕ} (hx : x ^ 3 ^ m = 1) (hd : d ^ 3 = 1)
    (hxd : x * d * x⁻¹ ∈ Subgroup.zpowers d) : x * d * x⁻¹ = d := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxd
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · have hd1 : x * d * x⁻¹ = 1 := by
      rw [← hk, zpow_eq_zpow_of_emod_eq hd (l := 0) (by omega), zpow_zero]
    have : d = 1 := by
      calc d = x⁻¹ * (x * d * x⁻¹) * x := by group
        _ = 1 := by rw [hd1]; group
    rw [hd1, this]
  · rw [← hk, zpow_eq_zpow_of_emod_eq hd (l := 1) (by omega), zpow_one]
  · have hinv : x * d * x⁻¹ = d⁻¹ := by
      rw [← hk, zpow_eq_zpow_of_emod_eq hd (l := -1) (by omega), zpow_neg_one]
    apply conj_eq_of_sq_conj_eq hx
    calc x ^ 2 * d * (x ^ 2)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = d := by
        rw [hinv]
        have : x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ := by group
        rw [this, hinv, inv_inv]

theorem exists_pow_conj_of_conj_eq_mul {a d b y : H} (ha : a ^ 3 = 1) (hd : d ^ 3 = 1)
    (had : a * d = d * a) (hb : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d)
    (hba : b ∉ Subgroup.zpowers a) (hya : y * a * y⁻¹ = a) {i : ℤ} (hi : i % 3 = 1 ∨ i % 3 = 2)
    (h1 : y * d * y⁻¹ = a ^ i * d) :
    ∃ n : ℕ, y ^ n * d * (y ^ n)⁻¹ = b ∨ y ^ n * d * (y ^ n)⁻¹ = b⁻¹ := by
  obtain ⟨s, t, hst⟩ := Sec4.exists_zpow_mul_of_mem_sup had hb
  have hyai : ∀ k : ℤ, y * a ^ k * y⁻¹ = a ^ k := by
    intro k
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hya]
  have hcomm : ∀ k l : ℤ, d ^ l * a ^ k = a ^ k * d ^ l := fun k l =>
    (Commute.zpow_zpow had k l).eq.symm
  have hn : ∀ n : ℕ, y ^ n * d * (y ^ n)⁻¹ = a ^ ((n : ℤ) * i) * d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * d * (y ^ (n + 1))⁻¹ = y * (y ^ n * d * (y ^ n)⁻¹) * y⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = y * a ^ ((n : ℤ) * i) * y⁻¹ * (y * d * y⁻¹) := by rw [ih]; group
        _ = a ^ ((n : ℤ) * i) * (a ^ i * d) := by rw [hyai, h1]
        _ = a ^ (((n + 1 : ℕ) : ℤ) * i) * d := by
          rw [← mul_assoc, ← zpow_add]
          congr 2
          push_cast
          ring
  rcases (show t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 by omega) with ht | ht | ht
  · exfalso
    apply hba
    rw [hst, zpow_eq_zpow_of_emod_eq hd (l := 0) (by omega), zpow_zero, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) s
  · obtain ⟨n, hn'⟩ := exists_nat_mul_emod_three hi s
    refine ⟨n, Or.inl ?_⟩
    rw [hn n, hst, zpow_eq_zpow_of_emod_eq ha hn', zpow_eq_zpow_of_emod_eq hd (k := t) (l := 1)
      (by omega), zpow_one]
  · obtain ⟨n, hn'⟩ := exists_nat_mul_emod_three hi (-s)
    refine ⟨n, Or.inr ?_⟩
    rw [hn n, hst, zpow_eq_zpow_of_emod_eq ha hn', mul_inv_rev, ← zpow_neg, ← zpow_neg,
      hcomm, zpow_eq_zpow_of_emod_eq hd (k := -t) (l := 1) (by omega), zpow_one]

theorem conj_eq_or_exists_pow_conj {a d b y : H} {m : ℕ} (hy : y ^ 3 ^ m = 1)
    (ha : a ^ 3 = 1) (hd : d ^ 3 = 1) (had : a * d = d * a) (hda : d ∉ Subgroup.zpowers a)
    (hb : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d) (hba : b ∉ Subgroup.zpowers a)
    (hya : y * a * y⁻¹ = a) (hyd : y * d * y⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d) :
    y * d * y⁻¹ = d ∨ ∃ n : ℕ, y ^ n * d * (y ^ n)⁻¹ = b ∨ y ^ n * d * (y ^ n)⁻¹ = b⁻¹ := by
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup had hyd
  have hyai : ∀ k : ℤ, y * a ^ k * y⁻¹ = a ^ k := by
    intro k
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hya]
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with hj | hj | hj
  · exfalso
    apply hda
    have h1 : y * d * y⁻¹ = a ^ i := by
      rw [hij, zpow_eq_zpow_of_emod_eq hd (l := 0) (by omega), zpow_zero, mul_one]
    have h2 : d = a ^ i := by
      calc d = y⁻¹ * (y * d * y⁻¹) * y := by group
        _ = y⁻¹ * (y * a ^ i * y⁻¹) * y := by rw [h1, hyai]
        _ = a ^ i := by group
    rw [h2]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i
  · have h1 : y * d * y⁻¹ = a ^ i * d := by
      rw [hij, zpow_eq_zpow_of_emod_eq hd (l := 1) (by omega), zpow_one]
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with hi | hi | hi
    · left
      rw [h1, zpow_eq_zpow_of_emod_eq ha (l := 0) (by omega), zpow_zero, one_mul]
    · exact Or.inr (exists_pow_conj_of_conj_eq_mul ha hd had hb hba hya (Or.inl hi) h1)
    · exact Or.inr (exists_pow_conj_of_conj_eq_mul ha hd had hb hba hya (Or.inr hi) h1)
  · left
    have h1 : y * d * y⁻¹ = a ^ i * d⁻¹ := by
      rw [hij, zpow_eq_zpow_of_emod_eq hd (l := -1) (by omega), zpow_neg_one]
    apply conj_eq_of_sq_conj_eq hy
    calc y ^ 2 * d * (y ^ 2)⁻¹ = y * (y * d * y⁻¹) * y⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = y * (a ^ i * d⁻¹) * y⁻¹ := by rw [h1]
      _ = (y * a ^ i * y⁻¹) * (y * d * y⁻¹)⁻¹ := by group
      _ = a ^ i * (a ^ i * d⁻¹)⁻¹ := by rw [hyai, h1]
      _ = d := by
        rw [mul_inv_rev, inv_inv, ← mul_assoc, (Commute.zpow_left had i).eq]
        group

end Three

omit [Finite G] in
theorem thetaComponentsAt_congr {p : ℕ} {x y : G}
    (h : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G)) :
    thetaComponentsAt p x = thetaComponentsAt p y := by
  unfold thetaComponentsAt
  rw [h]

theorem mem_normalizer_of_conj_mem {S : Subgroup G} {x : G}
    (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  rintro _ ⟨s, hs, rfl⟩
  exact hx s hs

theorem exists_isSylowOf_ge {R K : Subgroup G} (hRK : R ≤ K) (hR : IsPGroup 3 R) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P K ∧ R ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR' : IsPGroup 3 (R.subgroupOf K) := hR.comap_subtype
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun r hr => ?_⟩
  exact ⟨⟨r, hRK hr⟩, hS (Subgroup.mem_subgroupOf.mpr hr), rfl⟩

omit [Finite G] in
theorem isElemAbelian_subgroupOf {E N : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (E.subgroupOf N) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · have h := congrArg Subtype.val
      (hE.1.is_comm.comm ⟨((x : ↥N) : G), x.2⟩ ⟨((y : ↥N) : G), y.2⟩)
    simpa using h
  · simpa using hE.2 _ hx

omit [Finite G] in
theorem closure_pair_eq_sup (u v : G) :
    Subgroup.closure {u, v} = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
    (Set.mem_insert u _))) (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
      (Set.mem_insert_of_mem u rfl))))
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

section RankB


theorem centralizer_le_normalizer_lb {A L B Lb : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Lb : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27'
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have huniq := (h.chosen136.2 b hc.2.1 Lb hLb).2
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hc.2.1).1
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨hdL, -⟩ := hc.2.2.2.2
  have h3 : 3 ∣ Nat.card Lb := by
    have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
    rw [← hod, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdL)
  intro g hg
  have hgb : g * b * g⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [hg]
    group
  have hmem := Sec11.map_conj_mem_thetaComponentsAt hb3 hLb.1 (w := g)
    (by rw [hgb]; exact Subgroup.mem_zpowers b)
  have hcard : 3 ∣ Nat.card (Lb.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hmem hcard)

theorem card_le_of_le_centralizer_b {A L B Lb Q E : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q) (hQb : Q ≤ Subgroup.centralizer ({b} : Set G))
    (hEQ : E ≤ Q) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  obtain ⟨φJ⟩ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, -, hAb⟩ := j2_point_facts hS.toSec13Data ⟨φJ⟩
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLb.1
  have hb3card : Nat.card (Subgroup.zpowers b) = 3 := (zpowers_mem_omegaA_iff.mp hc.2.1).2.1
  have hCN := centralizer_le_normalizer_lb h hB hc
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hZ : Subgroup.center (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  set N := Subgroup.normalizer (Lb : Set G) with hNdef
  set θ := aschbacherSolvableCore 3 ↥Lb with hθdef
  set φ : ↥N →* MulAut (↥Lb ⧸ θ) := (Sec4.thetaQuotMulAut ↥Lb).comp Lb.normalizerMonoidHom
    with hφdef
  have hEN : E ≤ N := hEQ.trans (hQb.trans hCN)
  set E' := E.subgroupOf N with hE'def
  set f : ↥E' →* MulAut (↥Lb ⧸ θ) := φ.comp E'.subtype with hfdef
  have hrange : CFSG.Open.IsElemAbelian 3 f.range := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ _ (isElemAbelian_subgroupOf hE)
  have h9 : Nat.card f.range ≤ 9 :=
    Sec10.Item1015Proof.card_le_nine_of_mulAut_J2 φJ f.range hrange
  have hφ : ∀ (n : ↥N) (l : ↥Lb), φ n (l : ↥Lb ⧸ θ) =
      ((Lb.normalizerMonoidHom n l : ↥Lb) : ↥Lb ⧸ θ) := fun n l => rfl
  have hker : ∀ x : ↥E', f x = 1 → ((x : ↥N) : G) ∈ Subgroup.zpowers b := by
    intro x hx
    set g : G := ((x : ↥N) : G) with hgdef
    have hgE : g ∈ E := x.2
    have hgQ : g ∈ Q := hEQ hgE
    have hg3 : g ^ 3 = 1 := hE.2 g hgE
    have hφx : φ (x : ↥N) = 1 := hx
    have htriv : ∀ l : ↥Lb, ((Lb.normalizerMonoidHom (x : ↥N) l : ↥Lb) : ↥Lb ⧸ θ) =
        (l : ↥Lb ⧸ θ) := by
      intro l
      rw [← hφ, hφx, MulAut.one_apply]
    have hcf : ∀ f0 ∈ A ⊓ Lb, f0 * g = g * f0 := by
      intro f0 hf0
      set l : ↥Lb := ⟨f0, hf0.2⟩ with hl
      have h1 := htriv l
      rw [QuotientGroup.eq] at h1
      set w : ↥Lb := (Lb.normalizerMonoidHom (x : ↥N) l)⁻¹ * l with hw
      have hwG : (w : G) = (g * f0 * g⁻¹)⁻¹ * f0 := rfl
      have hwQ : (w : G) ∈ Q := by
        rw [hwG]
        exact Q.mul_mem (Q.inv_mem (Q.mul_mem (Q.mul_mem hgQ (hAQ hf0.1)) (Q.inv_mem hgQ)))
          (hAQ hf0.1)
      obtain ⟨k, hk⟩ := hQ ⟨(w : G), hwQ⟩
      have hk' : w ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      have hw1 : w = 1 := eq_one_of_mem_of_pow_three_pow hθ3 h1 hk'
      have hw1' : (g * f0 * g⁻¹)⁻¹ * f0 = 1 := by rw [← hwG, hw1]; rfl
      have h2 : g * f0 * g⁻¹ = f0 := inv_mul_eq_one.mp hw1'
      calc f0 * g = g * f0 * g⁻¹ * g := by rw [h2]
        _ = g * f0 := by group
    have hgb : b * g = g * b := (Subgroup.mem_centralizer_singleton_iff.mp (hQb hgQ)).symm
    have hle : Subgroup.zpowers b ⊔ (A ⊓ Lb) ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgb))
        fun f0 hf0 => Subgroup.mem_centralizer_singleton_iff.mpr (hcf f0 hf0)
    have hgA : g ∈ A := by
      refine Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian hg3 fun α hα => ?_
      have hα' : α ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAb ▸ hα
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hα')
    have hbC : b ∈ Subgroup.centralizer ((A ⊓ Lb : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC hy.2)
    have hgsup : g ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAb ▸ hgA
    obtain ⟨k, ℓ, hℓ, hgk⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hbC hgsup
    set lℓ : ↥Lb := ⟨ℓ, hℓ.2⟩ with hlℓ
    have hcentral : ∀ l : ↥Lb, ((lℓ * l * lℓ⁻¹ : ↥Lb) : ↥Lb ⧸ θ) = (l : ↥Lb ⧸ θ) := by
      intro l
      have h1 := htriv l
      have heq : lℓ * l * lℓ⁻¹ = Lb.normalizerMonoidHom (x : ↥N) l := by
        apply Subtype.ext
        show ℓ * (l : G) * ℓ⁻¹ = g * (l : G) * g⁻¹
        have hℓg : ℓ = (b ^ k)⁻¹ * g := by rw [hgk]; group
        have hbk : (b ^ k)⁻¹ ∈ Subgroup.centralizer ((Lb : Subgroup G) : Set G) := by
          refine Subgroup.inv_mem _ (Subgroup.zpow_mem _ ?_ k)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC hy)
        have hgl : g * (l : G) * g⁻¹ ∈ Lb :=
          (Subgroup.mem_normalizer_iff.mp (x : ↥N).2 (l : G)).mp l.2
        have hc1 := Subgroup.mem_centralizer_iff.mp hbk _ hgl
        rw [hℓg]
        calc (b ^ k)⁻¹ * g * (l : G) * ((b ^ k)⁻¹ * g)⁻¹
            = (b ^ k)⁻¹ * (g * (l : G) * g⁻¹) * ((b ^ k)⁻¹)⁻¹ := by group
          _ = (g * (l : G) * g⁻¹) * (b ^ k)⁻¹ * ((b ^ k)⁻¹)⁻¹ := by rw [← hc1]
          _ = g * (l : G) * g⁻¹ := by group
      rw [heq]
      exact h1
    have hmem : (lℓ : ↥Lb ⧸ θ) ∈ Subgroup.center (↥Lb ⧸ θ) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 := hcentral l
      have h2 : ((lℓ * l * lℓ⁻¹ : ↥Lb) : ↥Lb ⧸ θ) =
          (lℓ : ↥Lb ⧸ θ) * (l : ↥Lb ⧸ θ) * (lℓ : ↥Lb ⧸ θ)⁻¹ := rfl
      rw [h2] at h1
      calc (l : ↥Lb ⧸ θ) * (lℓ : ↥Lb ⧸ θ)
          = (lℓ : ↥Lb ⧸ θ) * (l : ↥Lb ⧸ θ) * (lℓ : ↥Lb ⧸ θ)⁻¹ * (lℓ : ↥Lb ⧸ θ) := by rw [h1]
        _ = (lℓ : ↥Lb ⧸ θ) * (l : ↥Lb ⧸ θ) := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    have hℓ3 : lℓ ^ 3 = 1 := Subtype.ext (by simpa using h.isE27'.1.2 ℓ hℓ.1)
    have hℓ1 : lℓ = 1 := eq_one_of_mem_aschbacherSolvableCore hmem hℓ3
    have hℓ1' : ℓ = 1 := congrArg Subtype.val hℓ1
    rw [hgk, hℓ1', mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  have hker3 : Nat.card f.ker ≤ 3 := by
    refine (Nat.card_le_card_of_injective
      (fun (x : ↥f.ker) => (⟨(((x : ↥E') : ↥N) : G), hker x (MonoidHom.mem_ker.mp x.2)⟩ :
        Subgroup.zpowers b)) ?_).trans hb3card.le
    intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    simp only at hxy'
    exact Subtype.ext (Subtype.ext (Subtype.ext hxy'))
  have hcard := Subgroup.card_ker_mul_card_range f
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := by rw [hcard, hE'card]
    _ ≤ 3 * 9 := Nat.mul_le_mul hker3 h9
    _ = 27 := by norm_num

theorem false_of_conj_eq_b (h48 : Sec4.Item4_8) {A L B Lb : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {g : G}
    (hg : g * d * g⁻¹ = b ∨ g * d * g⁻¹ = b⁻¹) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27'
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hbL, -, -⟩ := j2_point_facts hS.toSec13Data hJ
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have huniq := (h.chosen136.2 b hc.2.1 Lb hLb).2
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨hdL, -⟩ := hc.2.2.2.2
  have hob : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b (hB.1 hbB)) hb1
  have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hdb : d ∉ Subgroup.zpowers b := by
    intro hd
    apply hbL
    have heq := Desc143X.zpowers_eq_of_mem hod hob hd
    have : b ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.mpr hdL) this
  obtain ⟨K, hK, hJK⟩ := Desc143X.exists_mem_le_residual h48 h hB hc hdB hd1 hdb
  have hdK : d ∈ K := hJK (Item148HJ.inf_le_residual h hB hc ⟨hdA, hdL⟩)
  have hKg := Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hK g
  have hgdb : Subgroup.centralizer ({g * d * g⁻¹} : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg]
      exact centralizer_singleton_eq_of_zpowers_eq Subgroup.zpowers_inv
  rw [thetaComponentsAt_congr hgdb] at hKg
  have h3 : 3 ∣ Nat.card (K.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hod, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdK)
  have heq := huniq _ hKg h3
  have hmem : g * d * g⁻¹ ∈ Lb := heq ▸ (⟨d, hdK, rfl⟩ : g * d * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom)
  rcases hg with hg | hg
  · rw [hg] at hmem
    exact hbL hmem
  · rw [hg] at hmem
    exact hbL (by simpa using Lb.inv_mem hmem)

theorem exists_isSylowOf_le_centralizer_d (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L B Lb : Subgroup G} {c a b d : G} (h : Desc143X.One A c L a b d B Lb)
    {H : Subgroup G} (hAH : A ≤ H) (hHa : H ≤ Subgroup.centralizer ({a} : Set G)) :
    ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 Q H ∧ A ≤ Q ∧
      Q ≤ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.std.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  obtain ⟨hb1, hd1⟩ := h.config.ne_one h.hyp hA
  have hbB : b ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := h.hyp.1 hdB
  have hbA : b ∈ A := h.hyp.1 hbB
  have hd3 := hA3 d hdA
  have ha3 := hA3 a h.mem
  have had : a * d = d * a := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, h.mem⟩ ⟨d, hdA⟩)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 h.ne_one
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hob : orderOf b = 3 := orderOf_eq_prime (hA3 b hbA) hb1
  have hda : d ∉ Subgroup.zpowers a := fun hd =>
    h.ne_d (Desc143X.zpowers_eq_of_mem hod hoa hd).symm
  have hba : b ∉ Subgroup.zpowers a := fun hb =>
    h.not_mem_zpowers_b ((Desc143X.zpowers_eq_of_mem hob hoa hb) ▸ Subgroup.mem_zpowers a)
  have hBad : B = Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    rw [← h.closure_d_a, closure_pair_eq_sup, sup_comm]
  have hB9 : Nat.card B = 9 := by have := h.hyp.2; rw [hA.2] at this; omega
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  have hACd : A ≤ Cd := Desc143X.le_centralizer_of_isE27 hA hdA
  obtain ⟨Q, hQsyl, hAQ⟩ := exists_isSylowOf_ge (le_inf hAH hACd) hAp
  have hQH : Q ≤ H := hQsyl.le.trans inf_le_left
  have hQd : Q ≤ Cd := hQsyl.le.trans inf_le_right
  refine ⟨Q, ?_, hAQ, hQd⟩
  obtain ⟨P, hPsyl, hQP⟩ := exists_isSylowOf_ge hQH hQsyl.isPGroup
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP (fun heq => hne (heq ▸ hPsyl))
  obtain ⟨y, hyP, hyQ, hyN⟩ := Sec3.exists_conj_mem_of_lt hPsyl.isPGroup hlt
  have hyH : y ∈ H := hPsyl.le hyP
  have hya : y * a * y⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hHa hyH)
    rw [this]
    group
  obtain ⟨m, hm⟩ := hPsyl.isPGroup ⟨y, hyP⟩
  have hym : y ^ 3 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hyNQ : y ∈ Subgroup.normalizer (Q : Set G) := mem_normalizer_of_conj_mem hyN
  set Z₁ := A ⊓ Subgroup.centralizer (Q : Set G) with hZ₁
  have hcent : ∀ z ∈ Subgroup.centralizer (Q : Set G),
      y * z * y⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro q hq
    have hq' : y⁻¹ * q * y ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyNQ) q).mp hq
      simpa using this
    have h1 := hz _ hq'
    calc q * (y * z * y⁻¹) = y * ((y⁻¹ * q * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * q * y)) * y⁻¹ := by rw [h1]
      _ = y * z * y⁻¹ * q := by group
  have hZ : ∀ z ∈ Z₁, y * z * y⁻¹ ∈ Z₁ := by
    rintro z ⟨hzA, hzC⟩
    have hc := hcent z hzC
    refine ⟨?_, hc⟩
    refine Sec4.mem_of_maximal_of_commute h.std.maximal_isElemAbelian ?_ fun α hα => ?_
    · rw [conj_pow, hA3 z hzA, mul_one, mul_inv_cancel]
    · exact Subgroup.mem_centralizer_iff.mp hc α (hAQ hα)
  have haZ : a ∈ Z₁ := ⟨h.mem, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hHa (hQH hq))⟩
  have hdZ : d ∈ Z₁ := ⟨hdA, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQd hq)⟩
  have hBZ : B ≤ Z₁ := by
    rw [hBad]
    exact sup_le (Subgroup.zpowers_le.mpr haZ) (Subgroup.zpowers_le.mpr hdZ)
  have hZA : Z₁ ≤ A := inf_le_left
  have hZcard : Nat.card Z₁ = 9 ∨ Nat.card Z₁ = 27 := by
    have h1 : Nat.card Z₁ ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hZA
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have h2 : 9 ∣ Nat.card Z₁ := hB9 ▸ Subgroup.card_dvd_of_le hBZ
    rw [hik] at h2 ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · norm_num at h2
    · norm_num at h2
    · left; norm_num
    · right; norm_num
  have hyd : y * d * y⁻¹ = d := by
    rcases hZcard with h9 | h27
    · have hZB : Z₁ = B := (Subgroup.eq_of_le_of_card_ge hBZ (by rw [h9, hB9])).symm
      have hydB : y * d * y⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
        rw [← hBad, ← hZB]
        exact hZ d hdZ
      have hbad : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d := hBad ▸ hbB
      rcases conj_eq_or_exists_pow_conj hym ha3 hd3 had hda hbad hba hya hydB with h1 | ⟨n, hn⟩
      · exact h1
      · exact (false_of_conj_eq_b h48 h.std h.hyp h.config hn).elim
    · have hZA' : Z₁ = A := Subgroup.eq_of_le_of_card_ge hZA (by rw [h27, hA.2])
      have hyA : y ∈ Subgroup.normalizer (A : Set G) := by
        refine mem_normalizer_of_conj_mem fun z hz => ?_
        have h1 := hZ z (hZA' ▸ hz)
        rwa [hZA'] at h1
      have hyNd := HJRes148.normalizer_le_normalizer_zpowers_d h134 h48 h.std h.hyp h.config hyA
      exact conj_eq_of_mem_zpowers hym hd3
        ((Subgroup.mem_normalizer_iff.mp hyNd d).mp (Subgroup.mem_zpowers d))
  have hyCd : y ∈ Cd := by
    rw [hCd, Subgroup.mem_centralizer_singleton_iff]
    calc y * d = y * d * y⁻¹ * y := by group
      _ = d * y := by rw [hyd]
  have hR : Q ⊔ Subgroup.zpowers y ≤ H ⊓ Cd :=
    sup_le hQsyl.le (Subgroup.zpowers_le.mpr ⟨hyH, hyCd⟩)
  have heq := hQsyl.eq_of_le le_sup_left hR
    (hPsyl.isPGroup.to_le (sup_le hQP (Subgroup.zpowers_le.mpr hyP)))
  exact hyQ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

theorem pRank_le_three (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L B Lb : Subgroup G} {c a b d : G} (h : Desc143X.One A c L a b d B Lb)
    {H : Subgroup G} (hAH : A ≤ H) (hHa : H ≤ Subgroup.centralizer ({a} : Set G)) :
    CFSG.Open.pRank 3 H ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQsyl, hAQ, hQd⟩ := exists_isSylowOf_le_centralizer_d h134 h48 h hAH hHa
  obtain ⟨E, hEH, hE, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three H
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨P', hP'syl, hEP'⟩ := exists_isSylowOf_ge hEH hEp
  obtain ⟨k, -, hk⟩ := hP'syl.exists_mem_conj hQsyl
  set E' := E.map (MulAut.conj k).toMonoidHom with hE'
  have hE'Q : E' ≤ Q := by
    rintro _ ⟨e, he, rfl⟩
    apply (hk _).mpr
    show k⁻¹ * (k * e * k⁻¹) * k ∈ P'
    rw [show k⁻¹ * (k * e * k⁻¹) * k = e by group]
    exact hEP' he
  have hE'ab : CFSG.Open.IsElemAbelian 3 E' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hbB : b ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) := fun q hq =>
    Desc143X.mem_centralizer_of_mem_closure_pair (hQd hq) (hHa (hQsyl.le hq))
      (h.closure_d_a ▸ hbB)
  have h27 := card_le_of_le_centralizer_b h.std h.hyp h.config hQsyl.isPGroup hAQ hQb hE'Q hE'ab
  rw [hE'card, hEcard] at h27
  by_contra hlt
  have : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 H := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem step143HJCompRank_of (h134 : Item134) (h48 : Sec4.Item4_8) : Step143HJCompRank := by
  intro G _ _ A c L hS a ha ha1 hΩ B b d Lb hB haB hc hne X hX hJX
  have hOne : Desc143X.One A c L a b d B Lb := ⟨hS, ha, ha1, hΩ, hB, haB, hc, hne⟩
  exact pRank_le_three h134 h48 hOne le_sup_right
    (sup_le (le_centralizer_of_mem_thetaComponentsAt hX)
      (Desc143X.le_centralizer_of_isE27 hS.isE27' ha))

end RankB

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
