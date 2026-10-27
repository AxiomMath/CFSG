module

public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace CommMod

theorem mem_of_pow_mem {N : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ N) (hb : x ^ b = 1) : x ∈ N := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e, hb, one_zpow, mul_one]
  exact N.zpow_mem ha _

theorem exists_pow_eq_mul {C : Subgroup G} {c t : G} (hc : c ∈ C)
    (ht : t ∈ Subgroup.normalizer (C : Set G)) (k : ℕ) : ∃ c' ∈ C, (c * t) ^ k = c' * t ^ k := by
  induction k with
  | zero => exact ⟨1, C.one_mem, by rw [pow_zero, pow_zero, mul_one]⟩
  | succ k ih =>
    obtain ⟨c', hc', e⟩ := ih
    refine ⟨c' * (t ^ k * c * (t ^ k)⁻¹), C.mul_mem hc'
      ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht k) c).mp hc), ?_⟩
    rw [pow_succ, e, pow_succ]
    group

end CommMod

theorem mem_of_mem_sup_of_pow_eq_one {C T : Subgroup G}
    (hTC : T ≤ Subgroup.normalizer (C : Set G)) (hT : IsPGroup 2 T) {x : G} (hx : x ∈ C ⊔ T)
    {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) : x ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C T hTC] at hx
  obtain ⟨c, hc, t, ht, rfl⟩ := hx
  obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  obtain ⟨c', hc', e⟩ := CommMod.exists_pow_eq_mul hc (hTC ht) (2 ^ m)
  refine CommMod.mem_of_pow_mem (a := 2 ^ m) (b := n)
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)) ?_ hxn
  rw [e, htm, mul_one]
  exact hc'

variable [Finite G]

theorem exists_elemAbelian_of_commute_mod {p : ℕ} [hp : Fact p.Prime] {Q E F : Subgroup G}
    {a b : ℕ} (hQ : ¬ p ∣ Nat.card Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hFQ : F ≤ Subgroup.normalizer (Q : Set G))
    (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEc : Nat.card E = p ^ a) (hFc : Nat.card F = p ^ b)
    (hcomm : ⁅E, F⁆ ≤ Q) (hint : (E ⊔ Q) ⊓ (F ⊔ Q) ≤ Q) :
    ∃ R : Subgroup G, R ≤ E ⊔ F ⊔ Q ∧ IsElemAbelian p R ∧ Nat.card R = p ^ (a + b) := by
  set W := E ⊔ F ⊔ Q with hW
  have hEW : E ≤ W := le_sup_left.trans le_sup_left
  have hFW : F ≤ W := le_sup_right.trans le_sup_left
  have hQW : Q ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (sup_le hEQ hFQ) Subgroup.le_normalizer
  set Q' : Subgroup ↥W := Q.subgroupOf W with hQ'
  have : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQW).mpr hWN
  set π := QuotientGroup.mk' Q' with hπ
  have hpQ : Nat.Coprime p (Nat.card Q) := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQ
  have hEQ1 : E ⊓ Q = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hEc]; exact hpQ.pow_left a)).eq_bot
  have hFQ1 : F ⊓ Q = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hFc]; exact hpQ.pow_left b)).eq_bot
  have hc : ∀ (e : ↥E) (f : ↥F), Commute ((π.comp (Subgroup.inclusion hEW)) e)
      ((π.comp (Subgroup.inclusion hFW)) f) := by
    intro e f
    have h1 : ⁅(f : G)⁻¹, (e : G)⁻¹⁆ ∈ Q := by
      apply hcomm
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (F.inv_mem f.2) (E.inv_mem e.2)
    show π _ * π _ = π _ * π _
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev]
    rw [commutatorElement_def, inv_inv, inv_inv] at h1
    simpa only [mul_assoc] using h1
  set ψ := (π.comp (Subgroup.inclusion hEW)).noncommCoprod (π.comp (Subgroup.inclusion hFW)) hc
    with hψdef
  have hψ : ∀ x : ↥E × ↥F,
      ψ x = π (Subgroup.inclusion hEW x.1) * π (Subgroup.inclusion hFW x.2) := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, f⟩ h
    rw [hψ, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h
    have heQ : (e : G) ∈ Q := by
      refine hint ⟨Subgroup.mem_sup_left e.2, ?_⟩
      have e1 : (e : G) = (e : G) * f * (f : G)⁻¹ := by group
      rw [e1]
      exact (F ⊔ Q).mul_mem (Subgroup.mem_sup_right h) (Subgroup.mem_sup_left (F.inv_mem f.2))
    have he1 : (e : G) = 1 := by
      have : (e : G) ∈ E ⊓ Q := ⟨e.2, heQ⟩
      rwa [hEQ1, Subgroup.mem_bot] at this
    have hfQ : (f : G) ∈ Q := by
      have e1 : (f : G) = (e : G)⁻¹ * ((e : G) * f) := by group
      rw [e1]
      exact Q.mul_mem (Q.inv_mem heQ) h
    have hf1 : (f : G) = 1 := by
      have : (f : G) ∈ F ⊓ Q := ⟨f.2, hfQ⟩
      rwa [hFQ1, Subgroup.mem_bot] at this
    exact Prod.ext (Subtype.ext he1) (Subtype.ext hf1)
  have hR₀c : Nat.card ψ.range = p ^ (a + b) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hEc, hFc, pow_add]
  have hR₀ : CFSG.Assembly.IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (hE.1.is_comm.comm _ _) (hF.1.is_comm.comm _ _)
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have hu : u ^ p = 1 := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · rw [Prod.pow_fst, Subgroup.coe_pow, Prod.fst_one, Subgroup.coe_one]
          exact hE.2 _ u.1.2
        · rw [Prod.pow_snd, Subgroup.coe_pow, Prod.snd_one, Subgroup.coe_one]
          exact hF.2 _ u.2.2
      rw [hu, map_one]
  have hQ'c : ¬ p ∣ Nat.card Q' := by
    rwa [hQ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW).toEquiv]
  obtain ⟨S, -, hS, hSc⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift Q' hQ'c hR₀
  refine ⟨S.map W.subtype, Subgroup.map_subtype_le S, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨x', hx', hxx⟩ := x.2
    obtain ⟨y', hy', hyy⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxx, ← hyy]
    have h1 := hS.1.is_comm.comm (⟨x', hx'⟩ : ↥S) ⟨y', hy'⟩
    have h2 := congrArg (fun s : ↥S => ((s : ↥W) : G)) h1
    simpa using h2
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow, hS.2 x' hx', map_one]
  · rw [Subgroup.card_map_of_injective W.subtype_injective, hSc, hR₀c]

theorem add_le_pRank_of_commute_mod {p : ℕ} [hp : Fact p.Prime] {X Q E F : Subgroup G}
    {a b : ℕ} (hQ : ¬ p ∣ Nat.card Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hFQ : F ≤ Subgroup.normalizer (Q : Set G))
    (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEc : Nat.card E = p ^ a) (hFc : Nat.card F = p ^ b)
    (hcomm : ⁅E, F⁆ ≤ Q) (hint : (E ⊔ Q) ⊓ (F ⊔ Q) ≤ Q) (hEX : E ≤ X) (hFX : F ≤ X)
    (hQX : Q ≤ X) : a + b ≤ pRank p X := by
  obtain ⟨R, hRW, hR, hRc⟩ :=
    exists_elemAbelian_of_commute_mod hQ hEQ hFQ hE hF hEc hFc hcomm hint
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨E', -, -, hE'⟩ := hk
    have h1 : p ^ k ≤ Nat.card G := hE' ▸ Subgroup.card_le_card_group E'
    have h2 : k < p ^ k := Nat.lt_pow_self hp.out.one_lt
    omega
  exact le_csSup hbdd ⟨R, hRW.trans (sup_le (sup_le hEX hFX) hQX), hR, hRc⟩

theorem succ_le_pRank_of_commute_mod {p : ℕ} [hp : Fact p.Prime] {X Q E : Subgroup G} {a : ℕ}
    {f : G} (hQ : ¬ p ∣ Nat.card Q) (hEQ : E ≤ Subgroup.normalizer (Q : Set G))
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ a) (hfp : f ^ p = 1) (hcomm : ⁅E, Subgroup.zpowers f⁆ ≤ Q)
    (hfE : f ∉ E ⊔ Q) (hEX : E ≤ X) (hfX : f ∈ X) (hQX : Q ≤ X) : a + 1 ≤ pRank p X := by
  set F := Subgroup.zpowers f with hFdef
  have hf1 : f ≠ 1 := fun h => hfE (h ▸ Subgroup.one_mem _)
  have hfo : orderOf f = p := orderOf_eq_prime hfp hf1
  have hFc : Nat.card F = p ^ 1 := by rw [pow_one, Nat.card_zpowers, hfo]
  have hFN : F ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hfQ
  have hF : IsElemAbelian p F := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := x.2
      obtain ⟨j, hj⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self f i j).eq
    · obtain ⟨i, rfl⟩ := hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfp, one_zpow]
  have hint : (E ⊔ Q) ⊓ (F ⊔ Q) ≤ Q := by
    rintro x ⟨hxE, hxF⟩
    have hxE : x ∈ E ⊔ Q := hxE
    have hxF : x ∈ F ⊔ Q := hxF
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F Q hFN] at hxF
    obtain ⟨y, hy, q, hq, rfl⟩ := hxF
    have hyE : y ∈ E ⊔ Q := by
      have e1 : y = y * q * q⁻¹ := by group
      rw [e1]
      exact (E ⊔ Q).mul_mem hxE (Subgroup.mem_sup_right (Q.inv_mem hq))
    by_cases hy1 : y = 1
    · simpa [hy1] using hq
    · exfalso
      have hne : (⟨y, hy⟩ : ↥F) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
      have htop := zpowers_eq_top_of_prime_card (G := ↥F) (by rw [hFc, pow_one]) hne
      have hfmem : (⟨f, Subgroup.mem_zpowers f⟩ : ↥F) ∈ Subgroup.zpowers ⟨y, hy⟩ :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm⟩ := hfmem
      apply hfE
      have : y ^ m = f := congrArg Subtype.val hm
      rw [← this]
      exact zpow_mem hyE m
  have h := add_le_pRank_of_commute_mod hQ hEQ hFN hE hF hEc hFc hcomm hint hEX
    (Subgroup.zpowers_le.mpr hfX) hQX
  simpa using h

end CFSG.Quasithin
