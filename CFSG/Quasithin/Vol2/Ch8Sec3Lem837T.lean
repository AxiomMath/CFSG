module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837F
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8312B
public import CFSG.Quasithin.Vol2.Ch7Lem734WrLie
public import CFSG.Quasithin.Background.C124Perf
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative commutatorElement

namespace Ch837

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ p ≠ 2 ∧ p ≠ 3 := by
  have h8 : 8 ∣ 2 ^ n := by
    have : 2 ^ 3 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
    simpa using this
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hm7 : (2 ^ n - 1) % 8 = 7 := by omega
  by_contra hcon
  push Not at hcon
  have hm0 : 2 ^ n - 1 ≠ 0 := by omega
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
    intro d hd hdm
    refine hcon d hd hdm ?_
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd hdm
    omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hall
  have h3 : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  rcases h3 (2 ^ n - 1).primeFactorsList.length with h | h <;> rw [← heq] at h <;> omega

theorem mul_sq_sub_one_ne {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    p * (p ^ 2 - 1) ≠ 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  intro h
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have : 1 ≤ 2 ^ n := by omega
    zify [this, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring
  have hdvd : p ∣ 2 * (2 ^ n * ((2 ^ n - 1) * (2 ^ n + 1))) := by
    rw [← hfac, ← h]
    exact dvd_mul_right p _
  have hp2n : ¬ p ∣ 2 ^ n := fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h'))
  have hp2' : ¬ p ∣ 2 := fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hd2 : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h' | h'
    · exact absurd h' hp2'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact absurd h'' hp2n
      · exact h''
  have hle : p ≤ 2 ^ n + 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hd2 with h' | h'
    · exact (Nat.le_of_dvd (by omega) h').trans (by omega)
    · exact Nat.le_of_dvd (by omega) h'
  have hne : p ≠ 2 ^ n := fun h' => hp2n (h' ▸ dvd_refl p)
  have hZ : (p : ℤ) * ((p : ℤ) ^ 2 - 1) = 2 * ((2 ^ n : ℕ) * (((2 ^ n : ℕ) : ℤ) ^ 2 - 1)) := by
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have hq1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hq1] at this
    exact_mod_cast this
  set q : ℕ := 2 ^ n with hqdef
  have hqZ : (8 : ℤ) ≤ q := by exact_mod_cast hq8
  rcases (by omega : p + 1 ≤ q ∨ p = q + 1) with h1 | h1
  · have hpq : (p : ℤ) ≤ (q : ℤ) - 1 := by
      have : ((p + 1 : ℕ) : ℤ) ≤ q := by exact_mod_cast h1
      push_cast at this
      linarith
    have hp0 : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have hcube : (p : ℤ) ^ 3 ≤ ((q : ℤ) - 1) ^ 3 := pow_le_pow_left₀ (by linarith) hpq 3
    nlinarith
  · have hpZ : (p : ℤ) = (q : ℤ) + 1 := by exact_mod_cast h1
    rw [hpZ] at hZ
    nlinarith

theorem card_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two h

theorem two_mul_card_of_isPSL_two_prime {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : 2 * Nat.card X = p * (p ^ 2 - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      K).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg]
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton]
  have h2 : 2 ∣ p * (p ^ 2 - 1) :=
    dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
  exact Nat.mul_div_cancel' h2

omit [Finite G] in
theorem mem_centralizer_of_orderOf_prime {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (e : IntMod V hV ≃* WMod) (g : Subgroup.normalizer (V : Set G))
    (hg : congrHom e (convI hV g) ∈ stabE) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hgo : orderOf (g : G) = p) : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : orderOf (congrHom e (convI hV g)) ∣ p := by
    rw [← hgo, Subgroup.orderOf_coe]
    exact orderOf_map_dvd ((congrHom e).comp (convI hV)) g
  have h2 : orderOf (congrHom e (convI hV g)) ∣ 2 ^ 7 * 3 ^ 2 := by
    rw [← card_stabE]
    exact Subgroup.orderOf_dvd_natCard stabE hg
  have h3 : orderOf (congrHom e (convI hV g)) = 1 := by
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h' | h'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h'))
  have hc1 : congrHom e (convI hV g) = 1 := orderOf_eq_one_iff.mp h3
  have hconv : convI hV g = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hc1
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hval := convI_apply_val hV g (IntMod.mk hV ⟨v, hv⟩)
  rw [hconv] at hval
  change v = (g : G) * v * (g : G)⁻¹ at hval
  calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [← hval]
    _ = (g : G) * v := by group

theorem false_of_mem_inf_of_orderOf_prime (h326 : Stmt3_2_6C) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {H : Subgroup G}
    (hloc : H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L))
    {x : G} (hxH : x ∈ H) (hxM : x ∈ fsuM T L) (hxz : x ∈ Subgroup.centralizer ({z} : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hxo : orderOf x = p) : False := by
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨e, he, -, -, hz, hez⟩ := exists_model_eW00_T hyp hV hrow hz1 hzV
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVVM]
    exact le_normalizer_conjClosure _ _
  have hst := Ch8312.act_mem_stabE e he hz hez (hMV hxM) hxM hxz
  have hxC := mem_centralizer_of_orderOf_prime e ⟨x, hMV hxM⟩ hst hp hp2 hp3 hxo
  have hxO : x ∈ pCoreOf 2 (H ⊓ fsuM T L) := hloc ⟨⟨hxH, hxM⟩, hxC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ fsuM T L) ⟨x, hxO⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : p ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

omit [Finite G] in
theorem isSylowTwoOf_subgroupOf_top {S Y : Subgroup G} (hS : IsSylowTwoOf S Y) :
    IsSylowTwoOf (S.subgroupOf Y) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [show ((S.subgroupOf Y).subgroupOf (⊤ : Subgroup ↥Y)).index = S.relIndex Y from
    Subgroup.relIndex_top_right (S.subgroupOf Y)]
  exact hS.2.2

theorem exists_orderOf_eq_of_isBorelIn {M H K : Subgroup G} {n p : ℕ} (hn : 2 ≤ n)
    (hX : E2.IsBenderOf n ↥(E2.star M H K) ∨ IsPSL 3 2 n ↥(E2.star M H K) ∨
      IsPSp4 2 n ↥(E2.star M H K))
    (hB : IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) (hp : p.Prime)
    (hpd : p ∣ 2 ^ n - 1) : ∃ x ∈ M ⊓ K, orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hBeq⟩ := hB
  set Y := E2.star M H K with hYdef
  have hS' : IsSylowTwoOf (S.subgroupOf Y) ⊤ := isSylowTwoOf_subgroupOf_top hS
  obtain ⟨Yt, -, -, hYtN, -, -, -, -, hcard, -⟩ :=
    e22TorusFacts_holds ↥Y n hn hX (S.subgroupOf Y) hS'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Yt) p (by rw [hcard]; exact hpd)
  have hyN : ((y : ↥Y) : E2.StarQuot M H) ∈ Subgroup.normalizer (S : Set (E2.StarQuot M H)) := by
    have hyS := hYtN y.2
    rw [Subgroup.mem_normalizer_iff] at hyS ⊢
    intro s
    by_cases hsY : s ∈ Y
    · have := hyS ⟨s, hsY⟩
      simp only [Subgroup.mem_subgroupOf] at this
      exact this
    · have hS1 : s ∉ S := fun h => hsY (hS.1 h)
      have hS2 : ((y : ↥Y) : E2.StarQuot M H) * s * ((y : ↥Y) : E2.StarQuot M H)⁻¹ ∉ S := by
        intro h
        apply hsY
        have h1 := Y.mul_mem (Y.mul_mem (Y.inv_mem (y : ↥Y).2) (hS.1 h)) (y : ↥Y).2
        simpa [mul_assoc] using h1
      exact ⟨fun h => absurd h hS1, fun h => absurd h hS2⟩
  have hyB : ((y : ↥Y) : E2.StarQuot M H) ∈ E2.star M H (M ⊓ K) := by
    rw [hBeq]
    exact ⟨(y : ↥Y).2, hyN⟩
  obtain ⟨h, hh, hhy⟩ := hyB
  have hoy : orderOf (QuotientGroup.mk' ((kerIn M H).subgroupOf H) h) = p := by
    rw [hhy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hdvd : p ∣ orderOf h := hoy ▸ orderOf_map_dvd _ h
  have ho : orderOf h ≠ 0 := (orderOf_pos h).ne'
  refine ⟨((h ^ (orderOf h / p) : ↥H) : G), ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact (M ⊓ K).pow_mem (Subgroup.mem_subgroupOf.mp hh) _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div ho hdvd

omit [Finite G] in
theorem commutator_sup_le_of {K' K K₂ N : Subgroup G}
    (hN : K ⊔ K₂ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅K', K⁆ ≤ N) (h2 : ⁅K', K₂⁆ ≤ N) :
    ⁅K', K ⊔ K₂⁆ ≤ N := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set G) ∧ ∀ a ∈ K', ⁅a, y⁆ ∈ N}
      mul_mem' := fun {y₁ y₂} hy₁ hy₂ => ⟨Subgroup.mul_mem _ hy₁.1 hy₂.1, fun a ha => by
        have e : ⁅a, y₁ * y₂⁆ = ⁅a, y₁⁆ * (y₁ * ⁅a, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem (hy₁.2 a ha) ((Subgroup.mem_normalizer_iff.mp hy₁.1 _).mp (hy₂.2 a ha))⟩
      one_mem' := ⟨Subgroup.one_mem _, fun a _ => by
        simp only [commutatorElement_def, mul_one, inv_one, mul_inv_cancel]
        exact N.one_mem⟩
      inv_mem' := fun {y} hy => ⟨Subgroup.inv_mem _ hy.1, fun a ha => by
        have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy.1) _).mp
          (N.inv_mem (hy.2 a ha))⟩ }
  have hS : K ⊔ K₂ ≤ S := sup_le
    (fun y hy => ⟨hN (Subgroup.mem_sup_left hy), fun a ha =>
      h1 (Subgroup.commutator_mem_commutator ha hy)⟩)
    (fun y hy => ⟨hN (Subgroup.mem_sup_right hy), fun a ha =>
      h2 (Subgroup.commutator_mem_commutator ha hy)⟩)
  rw [Subgroup.commutator_le]
  intro a ha y hy
  exact (hS hy).2 a ha

theorem eq_or_eq_of_mem_cComp_of_le_sup (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {H K K₂ K' : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hKc : K ∈ cComp H) (hK₂c : K₂ ∈ cComp H)
    (hK'c : K' ∈ cComp H) (hle : K' ≤ K ⊔ K₂) : K' = K ∨ K' = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have c1 := (Vol2Native.lemma_1_2_1_two hK h37 hH hK'c hKc h1).1
  have c2 := (Vol2Native.lemma_1_2_1_two hK h37 hH hK'c hK₂c h2).1
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_commutator_le (c1.trans (inf_le_left.trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K')))
  have hK₂N : K₂ ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_commutator_le (c2.trans (inf_le_left.trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K')))
  have hNO : K ⊔ K₂ ≤ Subgroup.normalizer (pCoreOf 2 K' : Set G) :=
    (sup_le hKN hK₂N).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')
  have hc := commutator_sup_le_of hNO (c1.trans inf_le_left) (c2.trans inf_le_left)
  have hK'O : K' ≤ pCoreOf 2 K' :=
    calc K' = ⁅K', K'⁆ := (perfect_of_mem_cComp hK'c).symm
      _ ≤ ⁅K', K ⊔ K₂⁆ := Subgroup.commutator_mono le_rfl hle
      _ ≤ pCoreOf 2 K' := hc
  have h2g : IsPGroup 2 K' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K').to_le hK'O
  have : Group.IsNilpotent ↥K' := h2g.isNilpotent
  exact not_isSolvable_of_mem_cComp hK'c inferInstance

theorem exists_lieCases_of_l2 (hNoN : E2.E22StatementNoN) (hKl : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {T M₀ H₀ K : Subgroup G} {t : G} {n : ℕ}
    (hmin : MinParabolic H₀ T M₀) (hSQ : SQTKGroup ↥H₀) (hPH₀ : pCoreOf 2 H₀ ≠ ⊥)
    (hKc : K ∈ cComp H₀) (htT : t ∈ T) (htN : t ∉ Subgroup.normalizer (K : Set G))
    (hTK : conjClosure K T = K ⊔ conjByElt t K) (hH₀ : H₀ = K ⊔ conjByElt t K ⊔ T)
    (hn4 : 4 ≤ n) (hmod : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ K' ∈ cComp H₀, H₀ = K' ⊔ T ∧ E2.E22LieCases H₀ T M₀ K' ∧
      IsPSL 2 2 n ↥(E2.star M₀ H₀ K') ∧ IsBorelIn (E2.star M₀ H₀ K') (E2.star M₀ H₀ (M₀ ⊓ K')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kz := K ⊔ conjByElt t K with hKzdef
  have hTH₀ : T ≤ H₀ := hH₀ ▸ le_sup_right
  have hKzH₀ : Kz ≤ H₀ := hH₀ ▸ le_sup_left
  have hns : ¬ Group.IsSolvable ↥H₀ := fun hs => not_isSolvable_of_mem_cComp hKc
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_of_mem_cComp hKc)))
  obtain ⟨⟨K', hK'c, hH₀K', -, hcases⟩, -⟩ := hNoN G H₀ T M₀ hmin hSQ hns
  have hK₂c : conjByElt t K ∈ cComp H₀ := conjSub_mem_cComp_of_mem hKc (hTH₀ htT)
  have hKzN : H₀ ≤ Subgroup.normalizer (Kz : Set G) := by
    rw [hH₀]
    refine sup_le Subgroup.le_normalizer ?_
    rw [← hTK]
    exact le_normalizer_conjClosure K T
  have h2q : ∀ y ∈ H₀, ∃ k : ℕ, y ^ 2 ^ k ∈ Kz :=
    B6.isTwoQuotient_of_sup_eq hmin.isSylow.2.1 hKzN (by rw [hH₀, sup_comm])
  have hK'H₀ : K' ≤ H₀ := le_of_mem_cComp hK'c
  have hK'le : K' ≤ Kz := by
    have hnorm : K' ≤ Subgroup.normalizer ((K' ⊓ Kz : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hKzN (hK'H₀ hx)⟩
    have h2 : ∀ y ∈ K', ∃ k : ℕ, y ^ 2 ^ k ∈ K' ⊓ Kz := fun y hy => by
      obtain ⟨k, hk⟩ := h2q y (hK'H₀ hy)
      exact ⟨k, K'.pow_mem hy _, hk⟩
    have h3 := twoResidual_le_of_isTwoQuotient inf_le_left hnorm h2
    rw [C124.twoResidual_eq_self_of_perfect' (perfect_of_mem_cComp hK'c)] at h3
    exact fun x hx => (h3 hx).2
  have hK'eq := eq_or_eq_of_mem_cComp_of_le_sup hKl h37 hPH₀ hKc hK₂c hK'c hK'le
  have hmod' : IsPSL 2 2 n (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    rcases hK'eq with rfl | rfl
    · exact hmod
    · obtain ⟨eK⟩ := nonempty_quot_conjugate_equiv K t⁻¹
      rw [conjByElt_eq_conjugate]
      exact IsPSL.of_mulEquiv eK hmod
  have htN' : ¬ T ≤ Subgroup.normalizer (K' : Set G) := by
    intro hTN
    rcases hK'eq with rfl | rfl
    · exact htN (hTN htT)
    · apply htN
      have hX := Subgroup.mem_normalizer_iff.mp (hTN htT)
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have h := hX (t * k * t⁻¹)
      rw [mem_conjByElt, mem_conjByElt] at h
      have e1 : t⁻¹ * (t * k * t⁻¹) * t = k := by group
      have e2 : t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) * t = t * k * t⁻¹ := by group
      rw [e1, e2] at h
      exact h
  dsimp only [E2.E22CasesNoN] at hcases
  rcases hcases with ⟨hJ, t', ht', hne, hM, hcase1⟩ | ⟨hTK', -⟩
  swap
  · exact absurd hTK' htN'
  have hinf : K' ⊓ pCoreOf 2 H₀ = pCoreOf 2 K' := by
    refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K')
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK'c)))
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀).to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀ (hK'H₀ hx)⟩
  set ψ : ↥K' →* E2.StarQuot M₀ H₀ :=
    (QuotientGroup.mk' ((kerIn M₀ H₀).subgroupOf H₀)).comp (Subgroup.inclusion hK'H₀) with hψ
  have hrange : ψ.range = E2.star M₀ H₀ K' := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ψ.ker = CFSG.pCore 2 ↥K' := by
    rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf, ← hinf]
    ext k
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hJ]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have e1 : ↥K' ⧸ CFSG.pCore 2 ↥K' ≃* ↥(E2.star M₀ H₀ K') :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hrange)
  have hstar : IsPSL 2 2 n ↥(E2.star M₀ H₀ K') := IsPSL.of_mulEquiv e1 hmod'
  rcases hcase1 with ⟨m, hm2, hty, hB⟩ | ⟨p, hp, hp8, hK, -, -⟩
  · exact ⟨K', hK'c, hH₀K', Or.inl ⟨hJ, t', ht', hne, hM, m, hm2, hty, hB⟩, hstar, hB⟩
  · exfalso
    have hp2 : p ≠ 2 := by rintro rfl; omega
    have h1 := card_of_isPSL_two_two hstar
    have h2 := two_mul_card_of_isPSL_two_prime hp hp2 hK
    rw [h1] at h2
    exact mul_sq_sub_one_ne hp hp2 (by omega) h2.symm

theorem not_isHStar_of_l2_four
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    {K : Subgroup G} {t : G} (htT : t ∈ T) (htN : t ∉ Subgroup.normalizer (K : Set G))
    (hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)))
    (hKz : ch83Kz T L z = K ⊔ conjByElt t K) (hTK : conjClosure K T = K ⊔ conjByElt t K)
    {n : ℕ} (hn4 : 4 ≤ n) (hmod : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ¬ IsHStar T (fsuM T L) (ch83Kz T L z ⊔ T) := by
  intro hstar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have h37' := a37ForSQTK_of_cat h37
  have h38' := a38ForSQTK_of_cat h38
  have h39' := a39ForSQTK_of_cat h39
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  set H₀ := ch83Kz T L z ⊔ T with hH₀def
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hH₀Gz : H₀ ≤ Subgroup.centralizer ({z} : Set G) := sup_le hKzGz hTz
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 H₀ :=
    zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) hH₀Gz
  have hPH₀ : pCoreOf 2 H₀ ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hSQ : IsSQTKIn H₀ :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPH₀
  have hTH₀ : IsSylowTwoOf T H₀ := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
  have hKH₀ : K ≤ H₀ := by
    rw [hH₀def, hKz]
    exact le_sup_left.trans le_sup_left
  have hKcH₀ : K ∈ cComp H₀ := cComp_mem_of_le hKc hKH₀ hH₀Gz
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hU : IsUniqueMaxOver H₀ T (H₀ ⊓ fsuM T L) := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.fsu.sylow
    have := IsHStar.isUniqueMaxOver S (hS ▸ hstar) (hS ▸ hTM)
    rwa [hS] at this
  have hmin : MinParabolic H₀ T (H₀ ⊓ fsuM T L) := KG4413.minParabolic_of_cComp hTH₀ hU hKcH₀
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  obtain ⟨K', hK'c, hH₀K', hlie, hstarK', hB⟩ := exists_lieCases_of_l2 hNoN hKl h37 hmin hSQ hPH₀
    hKcH₀ htT htN hTK (by rw [hH₀def, hKz]) hn4 hmod
  have hloc := (local_structure_wreath_lie_of h326
    (Ch4.stmt4_4_14Lie_of_steps h443 hC58 h317 h37' h38' h39') hC58 h317 h37' h38' h39' h3228 hyp
    hrow H₀ hstar ⟨K', hK'c, hH₀K', hlie⟩).2
  obtain ⟨p, hp, hpd, hp2, hp3⟩ := exists_prime_dvd_two_pow_sub_one (n := n) (by omega)
  obtain ⟨x, ⟨hxM₀, -⟩, hxo⟩ :=
    exists_orderOf_eq_of_isBorelIn (by omega) (Or.inl ⟨by omega, Or.inl hstarK'⟩) hB hp hpd
  exact false_of_mem_inf_of_orderOf_prime h326 hyp hrow hV hz2 hzV hloc hxM₀.1 hxM₀.2
    (hH₀Gz hxM₀.1) hp hp2 hp3 hxo

theorem false_of_l2_four_lie
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h836 : Stmt8_3_6)
    (hKG : KGRankOneOvergroups) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    (φ : OTwoQuot (ch83X T L z ⊔ T) ≃* S152N.W3)
    (hrel : (pCoreOf 2 (ch83X T L z)).relIndex (ch83X T L z) = 9)
    {K : Subgroup G} {t : G} (htT : t ∈ T) (htN : t ∉ Subgroup.normalizer (K : Set G))
    (hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)))
    (hKz : ch83Kz T L z = K ⊔ conjByElt t K) (hTK : conjClosure K T = K ⊔ conjByElt t K)
    {n : ℕ} (hn4 : 4 ≤ n) (hmod : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) : False :=
  false_of_l2_four_of_not_hstar h37 h38 h326 h836 hKG hyp h731 hrow hV hN hz2 hzV φ hrel hKc hKz
    hTK hn4 hmod (not_isHStar_of_l2_four hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 hyp hrow hV
      hN hz2 hzV htT htN hKc hKz hTK hn4 hmod)

end Ch837

open Ch837 in
theorem claim837L2N_of_lie
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h836 : Stmt8_3_6)
    (hKG : KGRankOneOvergroups) : Claim837L2N := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV K s n hsT hsN hKc hKz hn hn4 hmod
  exfalso
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  obtain ⟨φ, -, -, hrel, -⟩ := xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have htT : s⁻¹ ∈ T := T.inv_mem hsT
  have htN : s⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hsN (by simpa using Subgroup.inv_mem _ h)
  have hconj : CFSG.conjugate K s = conjByElt s⁻¹ K := by
    rw [conjByElt_eq_conjugate, inv_inv]
  rw [hconj] at hKz
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hKKz : K ≤ ch83Kz T L z := by rw [hKz]; exact le_sup_left
  have hTK : conjClosure K T = K ⊔ conjByElt s⁻¹ K := by
    refine le_antisymm ?_ (sup_le (le_conjClosure _ _) ?_)
    · rw [← hKz]
      refine conjClosure_le fun h hh x hx => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hGzKz (hTz hh)) x).mp (hKKz hx)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨s⁻¹, htT, k, hk, rfl⟩
  exact false_of_l2_four_lie hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h836 hKG hyp h731 hrow hV
    hN hz2 hzV φ hrel htT htN hKc hKz hTK hn4 hmod

theorem stmt8_3_7_of_lie
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (h734 : Stmt7_3_4) (h836 : Stmt8_3_6)
    (hOut : KG838Out) (hKG : KGRankOneOvergroups) (hNoN : E2.E22StatementNoN)
    (h443 : Stmt4_4_3Orbit') (hYns : Claim837YNonsolv) : Stmt8_3_7 :=
  stmt8_3_7_of h37 h38 h39 h3228 hC58 h317 h332 h326 h3108 h134 h734 h836 hOut hKG
    (claim837L2N_of_lie hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h836 hKG) hYns

end CFSG.Quasithin.H13
