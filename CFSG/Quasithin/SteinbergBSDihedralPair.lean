module

public import CFSG.GroupTheory.BaerConjugatePairPCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.Quasithin.SteinbergBSNoncentralHyperplane
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.ABGLocalTools DihedralGroup

section Dihedral

variable {X : Type*} [Group X]

theorem pow_val_add {y : X} {n : ℕ} [NeZero n] (hy : y ^ n = 1) (a b : ZMod n) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hy, pow_add]

theorem pow_val_sub {y : X} {n : ℕ} [NeZero n] (hy : y ^ n = 1) (a b : ZMod n) :
    y ^ (b - a).val = (y ^ a.val)⁻¹ * y ^ b.val := by
  have h1 := pow_val_add hy (b - a) a
  rw [sub_add_cancel] at h1
  rw [h1]
  have hc : y ^ (b - a).val * y ^ a.val = y ^ a.val * y ^ (b - a).val := by
    rw [← pow_add, ← pow_add, add_comm]
  rw [hc]
  group

@[expose] noncomputable def dihedralHom (n : ℕ) [NeZero n] {v y : X} (hv : v * v = 1)
    (hvy : v * y * v = y⁻¹) (hy : y ^ n = 1) : DihedralGroup n →* X where
  toFun g := match g with
    | r i => y ^ i.val
    | sr i => v * y ^ i.val
  map_one' := by
    rw [one_def]
    simp
  map_mul' g h := by
    have hk : ∀ k : ℕ, v * y ^ k * v = (y ^ k)⁻¹ := fun k => by
      have h1 : v * y ^ k * v⁻¹ = (v * y * v⁻¹) ^ k := (conj_pow).symm
      have hvinv : v⁻¹ = v := (eq_inv_of_mul_eq_one_left hv).symm
      rw [hvinv, hvy, inv_pow] at h1
      exact h1
    have hk' : ∀ k : ℕ, y ^ k * v = v * (y ^ k)⁻¹ := fun k => by
      rw [← hk k]
      calc y ^ k * v = (v * v) * y ^ k * v := by rw [hv, one_mul]
        _ = v * (v * y ^ k * v) := by group
    rcases g with i | i <;> rcases h with j | j
    · rw [r_mul_r]
      exact pow_val_add hy i j
    · rw [r_mul_sr]
      show v * y ^ (j - i).val = y ^ i.val * (v * y ^ j.val)
      rw [pow_val_sub hy, ← mul_assoc (y ^ i.val), hk' i.val, mul_assoc]
    · rw [sr_mul_r]
      show v * y ^ (i + j).val = v * y ^ i.val * y ^ j.val
      rw [pow_val_add hy, mul_assoc]
    · rw [sr_mul_sr]
      show y ^ (j - i).val = v * y ^ i.val * (v * y ^ j.val)
      rw [pow_val_sub hy, ← mul_assoc, hk i.val]

theorem dihedralHom_r (n : ℕ) [NeZero n] {v y : X} (hv : v * v = 1) (hvy : v * y * v = y⁻¹)
    (hy : y ^ n = 1) (i : ZMod n) : dihedralHom n hv hvy hy (r i) = y ^ i.val :=
  rfl

theorem dihedralHom_sr (n : ℕ) [NeZero n] {v y : X} (hv : v * v = 1) (hvy : v * y * v = y⁻¹)
    (hy : y ^ n = 1) (i : ZMod n) : dihedralHom n hv hvy hy (sr i) = v * y ^ i.val :=
  rfl

theorem dihedralHom_injective (n : ℕ) [NeZero n] {v y : X} (hv : v * v = 1)
    (hvy : v * y * v = y⁻¹) (hy : y ^ n = 1) (hn : orderOf y = n) (hvz : v ∉ zpowers y) :
    Function.Injective (dihedralHom n hv hvy hy) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [dihedralHom_r] at h
    have h1 : orderOf y ∣ i.val := orderOf_dvd_of_pow_eq_one h
    rw [hn] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [one_def, (ZMod.val_eq_zero i).1 h2]
  · rw [dihedralHom_sr] at h
    exfalso
    apply hvz
    have h1 : v = (y ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_mem (pow_mem (mem_zpowers y) _)

theorem range_dihedralHom (n : ℕ) [NeZero n] {v y : X} (hv : v * v = 1)
    (hvy : v * y * v = y⁻¹) (hy : y ^ n = 1) :
    (dihedralHom n hv hvy hy).range = closure {v, y} := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rcases g with i | i
    · rw [dihedralHom_r]
      exact pow_mem (subset_closure (by simp)) _
    · rw [dihedralHom_sr]
      exact mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _)
  · rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨sr 0, ?_⟩
      rw [dihedralHom_sr, ZMod.val_zero, pow_zero, mul_one]
    · refine ⟨r 1, ?_⟩
      rw [dihedralHom_r]
      rcases Nat.lt_or_ge 1 n with h | h
      · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h, pow_one]
      · have hn1 : n = 1 := le_antisymm h (Nat.pos_of_ne_zero (NeZero.ne n))
        subst hn1
        rw [pow_one] at hy
        rw [hy]
        simp

theorem dihedral_closure_facts [Finite X] {v y : X} {n : ℕ} [NeZero n] (hv : v * v = 1)
    (hv1 : v ≠ 1) (hvy : v * y * v = y⁻¹) (hn : orderOf y = n) (hodd : Odd n) (hn3 : 3 ≤ n) :
    Nonempty (closure {v, y} ≃* DihedralGroup n) ∧
    Nat.card (closure {v, y}) = 2 * n ∧
    (∀ x ∈ closure {v, y}, ∃ k : ℕ, x = y ^ k ∨ x = v * y ^ k) ∧
    (∀ P : Subgroup X, P ≤ closure {v, y} → IsPGroup 2 P → Nat.card P ≤ 2) ∧
    (∀ N : Subgroup X, N ≤ closure {v, y} → closure {v, y} ≤ normalizer (N : Set X) →
      IsPGroup 2 N → N = ⊥) ∧
    (∀ x ∈ closure {v, y}, x * v = v * x → x = 1 ∨ x = v) := by
  classical
  have hy : y ^ n = 1 := hn ▸ pow_orderOf_eq_one y
  have hvz : v ∉ zpowers y := by
    intro h
    have h1 : orderOf v ∣ n := hn ▸ orderOf_dvd_of_mem_zpowers h
    have h2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv) hv1
    rw [h2] at h1
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)
  set φ := dihedralHom n hv hvy hy with hφ
  have hinj := dihedralHom_injective n hv hvy hy hn hvz
  have hrange := range_dihedralHom n hv hvy hy
  have e : DihedralGroup n ≃* closure {v, y} :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hcard : Nat.card (closure {v, y}) = 2 * n := by
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have helem : ∀ x ∈ closure {v, y}, ∃ k : ℕ, x = y ^ k ∨ x = v * y ^ k := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨g, rfl⟩ := hx
    rcases g with i | i
    · exact ⟨i.val, Or.inl rfl⟩
    · exact ⟨i.val, Or.inr rfl⟩
  have hy2 : ∀ k : ℕ, y ^ k * y ^ k = 1 → y ^ k = 1 := by
    intro k hk
    rw [← pow_add, ← two_mul] at hk
    have h1 : n ∣ 2 * k := hn ▸ orderOf_dvd_of_pow_eq_one hk
    have h2 : n ∣ k := (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hodd)) h1)
    rw [← hn] at h2
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  have hk' : ∀ k : ℕ, y ^ k * v = v * (y ^ k)⁻¹ := fun k => by
    have h1 : v * y ^ k * v⁻¹ = (v * y * v⁻¹) ^ k := (conj_pow).symm
    have hvinv : v⁻¹ = v := (eq_inv_of_mul_eq_one_left hv).symm
    rw [hvinv, hvy, inv_pow] at h1
    calc y ^ k * v = (v * v) * y ^ k * v := by rw [hv, one_mul]
      _ = v * (v * y ^ k * v) := by group
      _ = v * (y ^ k)⁻¹ := by rw [h1]
  have hyodd : ∀ k j : ℕ, (y ^ k) ^ 2 ^ j = 1 → y ^ k = 1 := by
    intro k j hkj
    have h1 : orderOf (y ^ k) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hkj
    have h2 : orderOf (y ^ k) ∣ n := hn ▸ orderOf_dvd_of_mem_zpowers (pow_mem (mem_zpowers y) k)
    have hcop : Nat.Coprime (2 ^ j) n := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
    have h3 : orderOf (y ^ k) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.1 h3
  have h2sub : ∀ P : Subgroup X, P ≤ closure {v, y} → IsPGroup 2 P → Nat.card P ≤ 2 := by
    intro P hPD hP
    obtain ⟨j, hj⟩ := hP.exists_card_eq
    have h1 : Nat.card P ∣ 2 * n := hcard ▸ card_dvd_of_le hPD
    rw [hj] at h1 ⊢
    rcases j with _ | j
    · norm_num
    · rw [pow_succ, mul_comm] at h1
      have h2 : 2 ^ j ∣ n := Nat.dvd_of_mul_dvd_mul_left two_pos h1
      have h3 : 2 ^ j = 1 := Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)) dvd_rfl h2
      rw [pow_succ, h3]
      norm_num
  refine ⟨⟨e.symm⟩, hcard, helem, h2sub, ?_, ?_⟩
  ·
    intro N hND hDN hN
    by_contra hN1
    obtain ⟨⟨t, htN⟩, ht1⟩ := (ne_bot_iff_exists_ne_one).1 hN1
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hN2 := h2sub N hND hN
    obtain ⟨k, hk | hk⟩ := helem t (hND htN)
    · obtain ⟨j, hj⟩ := hN ⟨t, htN⟩
      have h1 : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      rw [hk] at h1 ht1'
      exact ht1' (hyodd k j h1)
    · have hyD : y ∈ closure ({v, y} : Set X) := subset_closure (by simp)
      have h1 : y * t * y⁻¹ ∈ N := (mem_normalizer_iff.mp (hDN hyD) t).mp htN
      have h2 : y * t * y⁻¹ ≠ 1 := fun h => ht1' (by
        have h5 : t = y⁻¹ * (y * t * y⁻¹) * y := by group
        rw [h5, h]
        group)
      have h3 := eq_of_card_le_two hN2 h1 htN h2 ht1'
      rw [hk] at h3
      have h4 : y * y = 1 := by
        have h5 : y * (v * y ^ k) = v * y ^ k * y := by
          calc y * (v * y ^ k) = y * (v * y ^ k) * y⁻¹ * y := by group
            _ = v * y ^ k * y := by rw [h3]
        have h6 : y * v = v * y⁻¹ := by simpa using hk' 1
        rw [← mul_assoc, h6] at h5
        have h7 : y⁻¹ * y ^ k = y ^ k * y := by
          have := congrArg (fun z => v⁻¹ * z) h5
          simpa [mul_assoc] using this
        have h8 : y ^ k * y = y * y ^ k := pow_mul_comm' y k
        rw [h8] at h7
        have h9 := congrArg (fun z => z * (y ^ k)⁻¹) h7
        simp only [mul_assoc, mul_inv_cancel, mul_one] at h9
        have h10 := congrArg (fun z => y * z) h9
        simpa using h10.symm
      have h11 := hy2 1 (by simpa using h4)
      rw [pow_one] at h11
      rw [h11] at hn
      rw [orderOf_one] at hn
      omega
  ·
    intro x hx hxv
    obtain ⟨k, hk | hk⟩ := helem x hx
    · left
      rw [hk] at hxv ⊢
      apply hy2 k
      have h1 : (y ^ k)⁻¹ = y ^ k := by
        have h2 : y ^ k * v = v * y ^ k := hxv
        rw [hk' k] at h2
        exact mul_left_cancel h2
      calc y ^ k * y ^ k = y ^ k * (y ^ k)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    · right
      rw [hk] at hxv ⊢
      have h1 : (y ^ k)⁻¹ = y ^ k := by
        have h2 : v * y ^ k * v = v * (v * y ^ k) := hxv
        rw [mul_assoc, hk' k, ← mul_assoc, ← mul_assoc, hv, one_mul, one_mul] at h2
        exact h2
      have h2 : y ^ k = 1 := hy2 k (by
        calc y ^ k * y ^ k = y ^ k * (y ^ k)⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel _)
      rw [h2, mul_one]

end Dihedral

section DihedralPair

variable {G : Type*} [Group G]

theorem pCore_quotient_pCore_eq_bot (p : ℕ) : pCore p (G ⧸ pCore p G) = ⊥ := by
  set N : Subgroup G := pCore p G with hN
  set K : Subgroup G := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (pCore_isPGroup (G := G ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (pCore_isPGroup (G := G) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKn : K.Normal := (pCore_normal (G := G ⧸ N) (p := p)).comap _
  have hKN : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem map_conjugate {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) (g : G) :
    (conjugate A g).map f = conjugate (A.map f) (f g) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g⁻¹ * a * g, ⟨a, ha, by simp⟩, by simp⟩

theorem conjugate_sup (A B : Subgroup G) (g : G) :
    conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g :=
  map_sup A B _

theorem card_inf_ker_mul_card_map {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) :
    Nat.card (A ⊓ f.ker : Subgroup G) * Nat.card (A.map f) = Nat.card A := by
  have hrange : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : (f.comp A.subtype).ker = f.ker.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply, MonoidHom.mem_ker]
    rfl
  have h1 := card_ker_mul_card_range (f.comp A.subtype)
  rw [hker, hrange, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm] at h1
  exact h1

theorem qrc_order_two_original_core_image_produces_dihedral_pair {H : Type*} [Group H]
    [Finite H] (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H) {M : Subgroup H}
    (hTM : (T : Subgroup H) ≤ M) {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : (V ⊓ pCore 2 H).relIndex V = 2) :
    ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧ ∃ g : H, ∃ I : Subgroup H, I = V ⊔ conjugate V g ∧
      V < I ∧ g ∈ I ∧ pCore 2 H ≤ normalizer (I : Set H) ∧
      (I.subgroupOf (pCore 2 H ⊔ I)).Normal ∧ IsCharacteristicP 2 I ∧
      IsSylowOf 2 ((T : Subgroup H) ⊓ I) I ∧ M ⊓ I = (T : Subgroup H) ⊓ I ∧
      normalizer (V : Set H) ⊓ I = (T : Subgroup H) ⊓ I ∧
      V ≤ inSubgroup (pCore 2) (M ⊓ I) ∧
      (⨅ i ∈ I, conjugate (M ⊓ I) i) = inSubgroup (pCore 2) I ∧
      inSubgroup (pCore 2) I = I ⊓ pCore 2 H ∧
      Nonempty (I ⧸ pCore 2 I ≃* DihedralGroup (p ^ a)) ∧
      Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 2 := by
  classical
  set Q := pCore 2 H with hQdef
  set π := QuotientGroup.mk' Q with hπ
  have hQT : Q ≤ T := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal T
  have hQV : Q ≤ normalizer (V : Set H) := hQT.trans hTV
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hπker : ∀ x : H, π x = 1 ↔ x ∈ Q := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hVb2 : Nat.card (V.map π) = 2 := by
    set f := π.comp V.subtype with hf
    have hrange : f.range = V.map π := by rw [hf, MonoidHom.range_comp, range_subtype]
    have hker : f.ker = Q.subgroupOf V := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, hπker]
      rfl
    have h1 := card_ker_mul_card_range f
    rw [hker, hrange, ← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    have h2 := relIndex_mul_card (V ⊓ Q) V
    rw [hVQ, inf_eq_left.2 inf_le_left] at h2
    rw [inf_comm] at h1
    have hpos : 0 < Nat.card (V ⊓ Q : Subgroup H) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (h2.symm.trans (mul_comm _ _)))
  obtain ⟨v, hvV, hvb1⟩ : ∃ v ∈ V, π v ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : V.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact mem_bot.2 (h x hx)
    rw [h1, card_bot] at hVb2
    omega
  set vb := π v with hvbdef
  have hvb2 : vb * vb = 1 := by rw [hvbdef, ← map_mul, hV2 v hvV, map_one]
  have hvbinv : vb⁻¹ = vb := (eq_inv_of_mul_eq_one_left hvb2).symm
  have hordv : orderOf vb = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvb2) hvb1
  have hVbz : V.map π = zpowers vb := by
    have hle : zpowers vb ≤ V.map π := zpowers_le.2 (mem_map_of_mem _ hvV)
    have hcz : Nat.card (zpowers vb) = 2 := by rw [Nat.card_zpowers, hordv]
    exact (eq_of_le_of_card_ge hle (by rw [hcz, hVb2])).symm
  have hO2 : pCore 2 (H ⧸ Q) = ⊥ := pCore_quotient_pCore_eq_bot 2
  obtain ⟨ub, hub⟩ : ∃ ub : H ⧸ Q, ¬ IsPGroup 2 ↥(V.map π ⊔ conjugate (V.map π) ub) := by
    by_contra h
    push Not at h
    have h1 := (CFSG.GroupTheory.baer_conjugate_pair_p_core 2).1 (V.map π) h
    rw [hO2] at h1
    exact hvb1 (mem_bot.1 (h1 (mem_map_of_mem _ hvV)))
  set wb := ub⁻¹ * vb * ub with hwb
  set rb := vb * wb with hrb
  have hwb2 : wb * wb = 1 := by
    rw [hwb]
    calc ub⁻¹ * vb * ub * (ub⁻¹ * vb * ub) = ub⁻¹ * (vb * vb) * ub := by group
      _ = 1 := by rw [hvb2]; group
  have hwbinv : wb⁻¹ = wb := (eq_inv_of_mul_eq_one_left hwb2).symm
  have hvrv : vb * rb * vb = rb⁻¹ := by
    rw [hrb, mul_inv_rev, hvbinv, hwbinv]
    calc vb * (vb * wb) * vb = (vb * vb) * wb * vb := by group
      _ = wb * vb := by rw [hvb2, one_mul]
  have hvb_norm : vb ∈ normalizer (zpowers rb : Set (H ⧸ Q)) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show zpowers (MulAut.conj vb rb) = zpowers rb
    rw [MulAut.conj_apply, hvbinv, hvrv, zpowers_inv]
  have hrb_not : ¬ IsPGroup 2 (zpowers rb) := by
    intro hrp
    apply hub
    have hle : V.map π ⊔ conjugate (V.map π) ub ≤ zpowers vb ⊔ zpowers rb := by
      rw [hVbz]
      refine sup_le le_sup_left ?_
      rw [conjugate, MonoidHom.map_zpowers, zpowers_le]
      have h1 : (MulAut.conj ub⁻¹).toMonoidHom vb = vb * rb := by
        show ub⁻¹ * vb * ub⁻¹⁻¹ = vb * rb
        rw [inv_inv, hrb, ← mul_assoc, hvb2, one_mul]
      rw [h1]
      exact mul_mem (mem_sup_left (mem_zpowers vb)) (mem_sup_right (mem_zpowers rb))
    have hvp : IsPGroup 2 (zpowers vb) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordv, pow_one])
    exact (IsPGroup.to_sup_of_normal_right' hvp hrp (zpowers_le.2 hvb_norm)).to_le hle
  set N := orderOf rb with hN
  have hN0 : N ≠ 0 := (orderOf_pos rb).ne'
  obtain ⟨p, hp, hp2, hpN⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ N := by
    by_contra h
    push Not at h
    apply hrb_not
    apply IsPGroup.of_card (n := N.primeFactorsList.length)
    rw [Nat.card_zpowers]
    exact Nat.eq_prime_pow_of_unique_prime_dvd hN0 fun {d} hd hdN => by
      by_contra hd2
      exact h d hd hd2 hdN
  set a := N.factorization p with ha
  have ha1 : 1 ≤ a := hp.factorization_pos_of_dvd hN0 hpN
  have hpa_dvd : p ^ a ∣ N := Nat.ordProj_dvd N p
  set yb := rb ^ (N / p ^ a) with hyb
  have hordy : orderOf yb = p ^ a := orderOf_pow_orderOf_div hN0 hpa_dvd
  have hvyv : vb * yb * vb = yb⁻¹ := by
    rw [hyb]
    have h1 : vb * rb ^ (N / p ^ a) * vb⁻¹ = (vb * rb * vb⁻¹) ^ (N / p ^ a) := (conj_pow).symm
    rw [hvbinv, hvrv, inv_pow] at h1
    exact h1
  have hodd : Odd (p ^ a) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p ^ a := by
    have h1 : 3 ≤ p := by have := hp.two_le; omega
    calc 3 ≤ p := h1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha1
  have : NeZero (p ^ a) := ⟨by positivity⟩
  obtain ⟨⟨eD⟩, hcardD, helemD, h2subD, hO2D, hcentD⟩ :=
    dihedral_closure_facts hvb2 hvb1 hvyv hordy hodd hp3
  set Db := closure ({vb, yb} : Set (H ⧸ Q)) with hDb
  have hconjV : ∀ g : H, π g = yb → (V ⊔ conjugate V g).map π = Db := by
    intro g hg
    rw [Subgroup.map_sup, map_conjugate, hg, hVbz, CFSG.GroupTheory.zpowers_sup_conjugate]
    have hyvy : yb⁻¹ * vb * yb = vb * (yb * yb) := by
      have h1 : yb⁻¹ = vb * yb * vb := hvyv.symm
      rw [h1]
      calc vb * yb * vb * vb * yb = vb * yb * (vb * vb) * yb := by group
        _ = vb * (yb * yb) := by rw [hvb2]; group
    rw [hyvy]
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp))
          (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    · rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact subset_closure (by simp)
      · have h1 : yb * yb ∈ closure ({vb, vb * (yb * yb)} : Set (H ⧸ Q)) := by
          have h3 := mul_mem (inv_mem (subset_closure (by simp) :
            vb ∈ closure ({vb, vb * (yb * yb)} : Set (H ⧸ Q))))
            (subset_closure (by simp) : vb * (yb * yb) ∈ closure ({vb, vb * (yb * yb)} : Set _))
          simpa using h3
        have h2 : yb = (yb * yb) ^ ((p ^ a + 1) / 2) := by
          rw [← pow_two, ← pow_mul]
          obtain ⟨k, hk⟩ := hodd
          have h4 : 2 * ((p ^ a + 1) / 2) = p ^ a + 1 := by omega
          rw [h4, pow_succ, ← hordy, pow_orderOf_eq_one, one_mul]
        have h5 := pow_mem h1 ((p ^ a + 1) / 2)
        rw [← h2] at h5
        exact h5
  obtain ⟨g₀, hg₀, hmin⟩ := Set.exists_min_image {g : H | π g = yb}
    (fun g => Nat.card ↥(V ⊔ conjugate V g)) (Set.toFinite _) (QuotientGroup.mk'_surjective Q yb)
  set I₀ := V ⊔ conjugate V g₀ with hI₀
  have hI₀D : I₀.map π = Db := hconjV g₀ hg₀
  obtain ⟨g, hgI₀, hgy⟩ : ∃ g ∈ I₀, π g = yb := by
    have h1 : yb ∈ I₀.map π := hI₀D ▸ subset_closure (by simp)
    obtain ⟨g, hg, hgy⟩ := h1
    exact ⟨g, hg, hgy⟩
  have hVI₀ : V ≤ I₀ := le_sup_left
  have hconjle : conjugate V g ≤ I₀ := fun x hx => by
    have h1 := hVI₀ (mem_conjugate_iff.1 hx)
    have h2 := mul_mem (mul_mem (inv_mem hgI₀) h1) hgI₀
    simpa [mul_assoc] using h2
  set I := V ⊔ conjugate V g with hIdef
  have hII₀ : I ≤ I₀ := sup_le hVI₀ hconjle
  have hIeq : I = I₀ := eq_of_le_of_card_ge hII₀ (hmin g hgy)
  have hgI : g ∈ I := hIeq ▸ hgI₀
  have hID : I.map π = Db := hconjV g hgy
  have hVI : V ≤ I := le_sup_left
  have hVltI : V < I := by
    refine lt_of_le_of_ne hVI fun h => ?_
    have h1 : Nat.card (V.map π) = Nat.card Db := by rw [h, hID]
    rw [hVb2, hcardD] at h1
    omega
  have hcz2 : Nat.card (zpowers vb) = 2 := by rw [Nat.card_zpowers, hordv]
  have hzp : ∀ z ∈ zpowers vb, z ≠ 1 → z = vb := fun z hz hz1 =>
    eq_of_card_le_two hcz2.le hz (mem_zpowers vb) hz1 hvb1
  have hkey : ∀ x ∈ I, π x * vb * (π x)⁻¹ ∈ zpowers vb → π x ∈ zpowers vb := by
    intro x hxI hx
    have h1 : π x * vb * (π x)⁻¹ ≠ 1 := by
      intro h
      apply hvb1
      calc vb = (π x)⁻¹ * (π x * vb * (π x)⁻¹) * π x := by group
        _ = 1 := by rw [h]; group
    have h3 : π x * vb = vb * π x := by
      calc π x * vb = π x * vb * (π x)⁻¹ * π x := by group
        _ = vb * π x := by rw [hzp _ hx h1]
    have hxD : π x ∈ Db := by
      rw [← hID]
      exact mem_map_of_mem π hxI
    rcases hcentD (π x) hxD h3 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers vb
  have hT_of : ∀ x : H, π x ∈ zpowers vb → x ∈ (T : Subgroup H) := by
    intro x hx
    rw [← hVbz] at hx
    obtain ⟨v', hv', hv'x⟩ := hx
    have hq : v'⁻¹ * x ∈ Q := (hπker _).1 (by rw [map_mul, map_inv, hv'x, inv_mul_cancel])
    have h1 := mul_mem (hVT hv') (hQT hq)
    rwa [mul_inv_cancel_left] at h1
  have hMO : M ≤ normalizer (inSubgroup (pCore 2) M : Set H) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic M (pCore 2 M))
  have hP : (inSubgroup (pCore 2) M ⊓ I).map π = zpowers vb := by
    have hle1 : zpowers vb ≤ (inSubgroup (pCore 2) M ⊓ I).map π :=
      zpowers_le.2 (mem_map_of_mem _ (mem_inf.2 ⟨hVM hvV, hVI hvV⟩))
    have hle2 : (inSubgroup (pCore 2) M ⊓ I).map π ≤ Db := by
      rw [← hID]
      exact map_mono inf_le_right
    have hp2 : IsPGroup 2 ((inSubgroup (pCore 2) M ⊓ I).map π) :=
      (((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le inf_le_left).map π
    exact (eq_of_le_of_card_ge hle1 (by rw [hcz2]; exact h2subD _ hle2 hp2)).symm
  have hMIπ : ∀ x ∈ M ⊓ I, π x ∈ zpowers vb := by
    intro x hx
    obtain ⟨hxM, hxI⟩ := mem_inf.1 hx
    apply hkey x hxI
    have h1 : x * v * x⁻¹ ∈ inSubgroup (pCore 2) M ⊓ I :=
      mem_inf.2 ⟨(mem_normalizer_iff.mp (hMO hxM) v).mp (hVM hvV),
        mul_mem (mul_mem hxI (hVI hvV)) (inv_mem hxI)⟩
    have h2 := mem_map_of_mem π h1
    rw [hP, map_mul, map_mul, map_inv] at h2
    exact h2
  set S := (T : Subgroup H) ⊓ I with hSdef
  have hMI : M ⊓ I = S := by
    apply le_antisymm
    · intro x hx
      exact mem_inf.2 ⟨hT_of x (hMIπ x hx), (mem_inf.1 hx).2⟩
    · exact inf_le_inf_right I hTM
  have hNV : normalizer (V : Set H) ⊓ I = S := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxN, hxI⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨hT_of x (hkey x hxI ?_), hxI⟩
      have h1 : x * v * x⁻¹ ∈ V := (mem_normalizer_iff.mp hxN v).mp hvV
      have h2 := mem_map_of_mem π h1
      rw [hVbz, map_mul, map_mul, map_inv] at h2
      exact h2
    · exact inf_le_inf_right I hTV
  have hVO2MI : V ≤ inSubgroup (pCore 2) (M ⊓ I) := by
    refine le_inSubgroup_pCore (le_inf (hVT.trans hTM) hVI) ?_ ((T.isPGroup').to_le hVT)
    rw [hMI]
    exact inf_le_left.trans hTV
  have hQnormI : Q ≤ normalizer (I : Set H) := by
    intro q hq
    apply mem_normalizer_of_conjugate_eq
    have hgq : g * q * g⁻¹ ∈ normalizer (V : Set H) :=
      hQV ((pCore_normal (p := 2) (G := H)).conj_mem q hq g)
    have h1 : conjugate (conjugate V g) q = conjugate V g := by
      rw [← conjugate_mul, show g * q = (g * q * g⁻¹) * g by group, conjugate_mul,
        conjugate_of_mem_normalizer hgq]
    rw [hIdef, conjugate_sup, conjugate_of_mem_normalizer (hQV hq), h1]
  have hInorm : (I.subgroupOf (Q ⊔ I)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 (sup_le hQnormI le_normalizer)
  have : Q.Normal := pCore_normal
  set πI := π.comp I.subtype with hπI
  have hπIrange : πI.range = Db := by rw [hπI, MonoidHom.range_comp, range_subtype, hID]
  have hπIker : πI.ker = Q.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hπI, MonoidHom.comp_apply, hπker]
    rfl
  have hO2I : pCore 2 I = πI.ker := by
    apply le_antisymm
    · have hbot : (pCore 2 I).map πI = ⊥ := by
        apply hO2D
        · rw [← hπIrange]
          exact map_le_range _ _
        · intro d hd
          rw [← hπIrange] at hd
          obtain ⟨i, rfl⟩ := hd
          rw [mem_normalizer_iff]
          intro z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨i * y * i⁻¹, (pCore_normal (p := 2) (G := I)).conj_mem y hy i, by
              rw [map_mul, map_mul, map_inv]⟩
          · rintro ⟨y, hy, hyz⟩
            refine ⟨i⁻¹ * y * i, ?_, ?_⟩
            · have h1 := (pCore_normal (p := 2) (G := I)).conj_mem y hy i⁻¹
              simpa using h1
            · rw [map_mul, map_mul, map_inv, hyz]
              group
        · exact (pCore_isPGroup (p := 2) (G := I)).map πI
      intro x hx
      have h1 : πI x ∈ (pCore 2 I).map πI := mem_map_of_mem _ hx
      rw [hbot, mem_bot] at h1
      exact h1
    · rw [hπIker]
      exact le_pCore_of_normal (pCore_isPGroup (p := 2) (G := H)).comap_subtype
  have hO2Iamb : inSubgroup (pCore 2) I = I ⊓ Q := by
    rw [inSubgroup, hO2I, hπIker, subgroupOf_map_subtype, inf_comm]
  have hDih : Nonempty (I ⧸ pCore 2 I ≃* DihedralGroup (p ^ a)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hO2I).trans ((QuotientGroup.quotientKerEquivRange πI).trans
      ((MulEquiv.subgroupCongr hπIrange).trans eD))⟩
  have hchar' : centralizer (Q : Set H) ≤ Q := hchar
  have hcharL : centralizer (CFSG.Open.pCore 2 ↥(Q ⊔ I) : Set ↥(Q ⊔ I)) ≤
      CFSG.Open.pCore 2 ↥(Q ⊔ I) := by
    have hQL : Q.subgroupOf (Q ⊔ I) ≤ pCore 2 ↥(Q ⊔ I) :=
      le_pCore_of_normal (pCore_isPGroup (p := 2) (G := H)).comap_subtype
    intro c hc
    have hcQ : (c : H) ∈ centralizer (Q : Set H) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hqL : (⟨q, mem_sup_left hq⟩ : ↥(Q ⊔ I)) ∈ pCore 2 ↥(Q ⊔ I) := hQL hq
      exact congrArg Subtype.val (mem_centralizer_iff.1 hc _ hqL)
    exact hQL (show c ∈ Q.subgroupOf (Q ⊔ I) from hchar' hcQ)
  have hcharI : IsCharacteristicP 2 I := by
    change centralizer (pCore 2 I : Set I) ≤ pCore 2 I
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroupOf_self_centralizing_pCore 2
      Nat.prime_two I (Q ⊔ I) le_sup_right hInorm hcharL
  have hπker' : π.ker = Q := QuotientGroup.ker_mk' Q
  have hcardI : Nat.card I = 2 * p ^ a * Nat.card (I ⊓ Q : Subgroup H) := by
    have h1 := card_inf_ker_mul_card_map π I
    rw [hπker', hID, hcardD] at h1
    rw [← h1, mul_comm]
  have hVS : V ≤ S := le_inf hVT hVI
  have hSQ : S ⊓ Q = I ⊓ Q := by
    ext x
    simp only [hSdef, mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hQT h.2, h.1⟩, h.2⟩⟩
  have hSmap : Nat.card (S.map π) = 2 := by
    have hle : S.map π ≤ Db := by
      rw [← hID]
      exact map_mono inf_le_right
    have hp2 : IsPGroup 2 (S.map π) := ((T.isPGroup').to_le inf_le_left).map π
    have hc := h2subD _ hle hp2
    have hc2 : Nat.card (V.map π) ≤ Nat.card (S.map π) := card_le_of_le (map_mono hVS)
    omega
  have hcardS : Nat.card S = 2 * Nat.card (I ⊓ Q : Subgroup H) := by
    have h1 := card_inf_ker_mul_card_map π S
    rw [hπker', hSQ, hSmap] at h1
    rw [← h1, mul_comm]
  have hSsyl : IsSylowOf 2 S I := by
    rw [isSylowOf_iff]
    refine ⟨inf_le_right, (T.isPGroup').to_le inf_le_left, ?_⟩
    have h1 := relIndex_mul_card S I
    rw [inf_eq_left.2 (inf_le_right : S ≤ I), hcardS, hcardI] at h1
    have hc : 0 < 2 * Nat.card (I ⊓ Q : Subgroup H) := Nat.mul_pos two_pos Nat.card_pos
    have h2 : S.relIndex I = p ^ a := Nat.eq_of_mul_eq_mul_right hc (h1.trans (by ring))
    rw [h2]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hJ : (⨅ i ∈ I, conjugate (M ⊓ I) i) = I ⊓ Q := by
    apply le_antisymm
    · intro x hx
      rw [mem_iInf] at hx
      have hx1 : x ∈ M ⊓ I := by
        have h1 := mem_iInf.1 (hx 1) (one_mem I)
        rwa [conjugate_one] at h1
      have hxg : g * x * g⁻¹ ∈ M ⊓ I := mem_conjugate_iff.1 (mem_iInf.1 (hx g) hgI)
      have hπx := hMIπ x hx1
      have hπgx := hMIπ _ hxg
      refine mem_inf.2 ⟨(mem_inf.1 hx1).2, (hπker x).1 ?_⟩
      by_contra hne
      have h1 : π x = vb := hzp _ hπx hne
      rw [map_mul, map_mul, map_inv, hgy, h1] at hπgx
      have h3 : π g * vb * (π g)⁻¹ ∈ zpowers vb := by
        rw [hgy]
        exact hπgx
      have h4 := hkey g hgI h3
      rw [hgy] at h4
      have h5 : orderOf yb ∣ orderOf vb := orderOf_dvd_of_mem_zpowers h4
      rw [hordy, hordv] at h5
      have h6 := Nat.le_of_dvd two_pos h5
      omega
    · refine le_iInf₂ fun i hi => ?_
      intro x hx
      rw [mem_conjugate_iff]
      obtain ⟨hxI, hxQ⟩ := mem_inf.1 hx
      have h1 : i * x * i⁻¹ ∈ Q := (pCore_normal (p := 2) (G := H)).conj_mem x hxQ i
      exact mem_inf.2 ⟨hTM (hQT h1), mul_mem (mul_mem hi hxI) (inv_mem hi)⟩
  have hVimg : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 2 := by
    have h1 := card_inf_ker_mul_card_map (QuotientGroup.mk' (pCore 2 I)) (V.subgroupOf I)
    have hk : V.subgroupOf I ⊓ (QuotientGroup.mk' (pCore 2 I)).ker = (V ⊓ Q).subgroupOf I := by
      rw [QuotientGroup.ker_mk', hO2I, hπIker]
      ext x
      simp only [mem_inf, mem_subgroupOf]
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe ((inf_le_left : V ⊓ Q ≤ V).trans hVI)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hVI).toEquiv] at h1
    have h2 := relIndex_mul_card (V ⊓ Q) V
    rw [hVQ, inf_eq_left.2 inf_le_left] at h2
    have hpos : 0 < Nat.card (V ⊓ Q : Subgroup H) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1, ← h2, mul_comm]
  exact ⟨p, a, hp, hp2, ha1, g, I, rfl, hVltI, hgI, hQnormI, hInorm, hcharI, hSsyl, hMI, hNV,
    hVO2MI, hJ.trans hO2Iamb.symm, hO2Iamb, hDih, hVimg⟩

end DihedralPair

end CFSG.Quasithin.SteinbergBS
