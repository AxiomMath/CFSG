module

public import CFSG.Quasithin.H13.NQCatT513L24
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Quasithin.Background.P3GL24A5Dec

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open CFSG.GorensteinWalter
open scoped Pointwise

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

section Perm

variable {G : Type*} [Group G]

theorem coe_sup_of_perm {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, ∃ x' ∈ H, ∃ k' ∈ K, k * x = x' * k') :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  let M : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        obtain ⟨c', hc', b', hb', hbc⟩ := h b hb c hc
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hbc]
          _ = a * b * (c * d) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        obtain ⟨a', ha', b', hb', hab⟩ := h b⁻¹ (K.inv_mem hb) a⁻¹ (H.inv_mem ha)
        exact ⟨a', ha', b', hb', by rw [mul_inv_rev, hab]⟩ }
  refine le_antisymm ?_ ?_
  · have : H ⊔ K ≤ M := sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
    exact this
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem card_sup_of_perm [Finite G] {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, ∃ x' ∈ H, ∃ k' ∈ K, k * x = x' * k')
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hd : H ⊓ K = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hs := coe_sup_of_perm h
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun x => ⟨x.1 * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ hab
      have h1 : (a : G) * b = c * d := congrArg Subtype.val hab
      have h2 : (c : G)⁻¹ * a = d * (b : G)⁻¹ := by
        calc (c : G)⁻¹ * a = (c : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (c : G)⁻¹ * (c * d) * (b : G)⁻¹ := by rw [h1]
          _ = d * (b : G)⁻¹ := by group
      have hmem : (c : G)⁻¹ * a ∈ H ⊓ K :=
        ⟨H.mul_mem (H.inv_mem c.2) a.2, h2 ▸ K.mul_mem d.2 (K.inv_mem b.2)⟩
      rw [hd, Subgroup.mem_bot] at hmem
      have hac : (a : G) = c := by
        calc (a : G) = c * ((c : G)⁻¹ * a) := by group
          _ = c := by rw [hmem, mul_one]
      have hbd : (b : G) = d := by
        rw [hac] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (H : Set G) * (K : Set G) := hs ▸ hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end Perm

section Dihedral

theorem dihedral_r_comm (m : ℕ) (g : DihedralGroup (2 * m)) :
    DihedralGroup.r ((m : ZMod (2 * m))) * g = g * DihedralGroup.r (m : ZMod (2 * m)) := by
  rcases g with i | i
  · simp only [DihedralGroup.r_mul_r, add_comm]
  · simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    have h : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
    push_cast at h
    linear_combination -h

theorem dihedral_r_sq (m : ℕ) :
    DihedralGroup.r ((m : ZMod (2 * m))) * DihedralGroup.r (m : ZMod (2 * m)) = 1 := by
  rw [DihedralGroup.r_mul_r, DihedralGroup.one_def]
  congr 1
  have h : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

theorem dihedral_r_ne_one {m : ℕ} (hm : 1 ≤ m) :
    DihedralGroup.r ((m : ZMod (2 * m))) ≠ 1 := by
  rw [DihedralGroup.one_def]
  intro h
  have h1 := DihedralGroup.r.inj h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by omega) h1
  omega

theorem dihedral_center_eq {m : ℕ} (hm : 2 ≤ m) {c : DihedralGroup (2 * m)}
    (hc : ∀ g, c * g = g * c) (hc1 : c ≠ 1) : c = DihedralGroup.r (m : ZMod (2 * m)) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rcases c with i | i
  · have h1 := hc (DihedralGroup.sr 0)
    simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add] at h1
    have h2 : -i = i := DihedralGroup.sr.inj h1
    have h3 : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination -h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have hlt := ZMod.val_lt i
    have h4 : m ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
    obtain ⟨k, hk⟩ := h4
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : m * 2 ≤ m * k := Nat.mul_le_mul_left m hk2
      omega
    interval_cases k
    · exfalso
      apply hc1
      have : i = 0 := by rw [← ZMod.natCast_zmod_val i, hk]; simp
      rw [this, DihedralGroup.one_def]
    · congr 1
      rw [← ZMod.natCast_zmod_val i, hk, mul_one]
  · exfalso
    have h1 := hc (DihedralGroup.r 1)
    simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at h1
    have h2 : i + 1 = i - 1 := DihedralGroup.sr.inj h1
    have h3 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
      push_cast
      linear_combination h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega

end Dihedral

section Cases

variable {G : Type*} [Group G] [Finite G]

theorem isKleinFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) [IsKleinFour X] :
    IsKleinFour Y where
  card_four := by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four
  exponent_two := by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two

theorem false_of_dihedral {H R : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    (eH : ↥H ≃* DihedralGroup (2 * m)) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (eR : ↥R ≃* L24) (hTR : (T : Subgroup G) ≤ R) {b : G} (hbR : b ∈ R) (hb3 : orderOf b = 3)
    (hbH : b ∈ Subgroup.normalizer (H : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : ↥H := eH.symm (DihedralGroup.r (m : ZMod (2 * m))) with hcdef
  have hcen : ∀ x : ↥H, c * x = x * c := by
    intro x
    apply eH.injective
    rw [map_mul, map_mul, hcdef, MulEquiv.apply_symm_apply]
    exact dihedral_r_comm m (eH x)
  have hc1 : c ≠ 1 := by
    intro h
    apply dihedral_r_ne_one (m := m) (by omega)
    rw [← eH.apply_symm_apply (DihedralGroup.r _), ← hcdef, h, map_one]
  have hc2 : c * c = 1 := by
    apply eH.injective
    rw [map_mul, hcdef, MulEquiv.apply_symm_apply, map_one]
    exact dihedral_r_sq m
  have hbc : b * (c : G) * b⁻¹ = c := by
    have hmem : b * (c : G) * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hbH _).mp c.2
    set c' : ↥H := ⟨b * (c : G) * b⁻¹, hmem⟩
    have hcen' : ∀ x : ↥H, c' * x = x * c' := by
      intro x
      have hx' : b⁻¹ * (x : G) * b ∈ H := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hbH) (x : G)).mp x.2
        simpa using this
      have h1 := congrArg Subtype.val (hcen ⟨b⁻¹ * (x : G) * b, hx'⟩)
      simp only [Subgroup.coe_mul] at h1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, c']
      calc b * (c : G) * b⁻¹ * x = b * ((c : G) * (b⁻¹ * x * b)) * b⁻¹ := by group
        _ = b * ((b⁻¹ * x * b) * c) * b⁻¹ := by rw [h1]
        _ = x * (b * c * b⁻¹) := by group
    have hc'1 : c' ≠ 1 := by
      intro h
      apply hc1
      have h1 := congrArg Subtype.val h
      simp only [c', Subgroup.coe_one] at h1
      apply Subtype.ext
      rw [Subgroup.coe_one]
      calc (c : G) = b⁻¹ * (b * c * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    have hcen'' : ∀ g, eH c' * g = g * eH c' := by
      intro g
      obtain ⟨x, rfl⟩ := eH.surjective g
      rw [← map_mul, ← map_mul, hcen' x]
    have h1 := dihedral_center_eq (by omega) hcen'' (by
      intro h
      apply hc'1
      rw [← map_one eH] at h
      exact eH.injective h)
    have h2 : c' = c := by
      apply eH.injective
      rw [h1, hcdef, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hcT : (c : G) ∈ (T : Subgroup G) := by
    have hz : IsPGroup 2 (Subgroup.zpowers (c : G)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one]
      apply orderOf_eq_prime
      · rw [sq, ← Subgroup.coe_mul, hc2, Subgroup.coe_one]
      · intro h
        exact hc1 (Subtype.ext h)
    have hle : (T : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers (c : G) : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have htc : t * (c : G) * t⁻¹ = c := by
        have := congrArg Subtype.val (hcen ⟨t, hTH ht⟩)
        simp only [Subgroup.coe_mul] at this
        calc t * (c : G) * t⁻¹ = (c : G) * t * t⁻¹ := by rw [this]
          _ = c := by group
      have hconj : ∀ k : ℤ, t * (c : G) ^ k * t⁻¹ = (c : G) ^ k := by
        intro k
        rw [← conj_zpow, htc]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (hconj k).symm⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have : t * y * t⁻¹ = t * (c : G) ^ k * t⁻¹ := by rw [hconj k]; exact hk.symm
        simpa using this.symm
    have h1 := T.is_maximal' (IsPGroup.to_sup_of_normal_right' T.isPGroup' hz hle) le_sup_left
    rw [← h1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hbo : orderOf (⟨b, hbR⟩ : ↥R) = 3 := by rw [Subgroup.orderOf_mk, hb3]
  have hco : orderOf (⟨(c : G), hTR hcT⟩ : ↥R) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    apply orderOf_eq_prime
    · rw [sq, hc2]
    · exact hc1
  have hcomm : (⟨b, hbR⟩ : ↥R) * ⟨(c : G), hTR hcT⟩ = ⟨(c : G), hTR hcT⟩ * ⟨b, hbR⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc b * (c : G) = (b * c * b⁻¹) * b := by group
      _ = c * b := by rw [hbc]
  have := CFSG.Walter.JT.eq_one_of_commute_of_psl24 eR (by rw [hbo]; decide) hco hcomm
  rw [this, orderOf_one] at hbo
  omega

end Cases

section Arith

theorem dvd_twelve_of_dvd {n u : ℕ} (hu : Odd u) (h96 : n ∣ 96) (hu4 : n ∣ 4 * u) : n ∣ 12 := by
  obtain ⟨k, rfl⟩ := hu
  have hn : n ≤ 96 := Nat.le_of_dvd (by norm_num) h96
  interval_cases n <;> omega

theorem psl2_card_four_mul {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    ∃ u, Odd u ∧ Nat.card (PSL2 K) = 4 * u ∧ Nat.card (PSL2 K) = p * (p ^ 2 - 1) / 2 := by
  have hp2 : p ≠ 2 := by omega
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [hK, pow_one]⟩
  have hc := psl2_card_formula K hodd
  rw [hK] at hc
  have hk : p = 8 * (p / 8) + p % 8 := (Nat.div_add_mod p 8).symm
  set k := p / 8
  rcases hp8 with h3 | h5
  · rw [h3] at hk
    have e1 : p ^ 2 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by
      have : p ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by rw [hk]; ring
      omega
    refine ⟨p * (8 * k ^ 2 + 6 * k + 1), (hp.odd_of_ne_two hp2).mul ⟨4 * k ^ 2 + 3 * k, by ring⟩,
      ?_, hc⟩
    rw [hc, e1]
    have : p * (8 * (8 * k ^ 2 + 6 * k + 1)) = 2 * (4 * (p * (8 * k ^ 2 + 6 * k + 1))) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  · rw [h5] at hk
    have e1 : p ^ 2 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by
      have : p ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by rw [hk]; ring
      omega
    refine ⟨p * (8 * k ^ 2 + 10 * k + 3),
      (hp.odd_of_ne_two hp2).mul ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩, ?_, hc⟩
    rw [hc, e1]
    have : p * (8 * (8 * k ^ 2 + 10 * k + 3)) = 2 * (4 * (p * (8 * k ^ 2 + 10 * k + 3))) := by
      ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

end Arith

theorem core_psl2_prime_le
    {K : Type} [Field K] [Finite K] {p : ℕ} [hpf : Fact p.Prime]
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p)
    {D₁ R₁ : Subgroup (PSL2 K)} (T : Sylow 2 (PSL2 K)) (hDc : IsCyclic D₁)
    (hDo : Odd (Nat.card D₁))
    (hperm : ∀ t ∈ (T : Subgroup (PSL2 K)), ∀ x ∈ D₁, ∃ x' ∈ D₁,
      ∃ t' ∈ (T : Subgroup (PSL2 K)), t * x = x' * t')
    (eR : ↥R₁ ≃* L24) (hTR : (T : Subgroup (PSL2 K)) ≤ R₁) {b : PSL2 K} (hbR : b ∈ R₁)
    (hb3 : orderOf b = 3) (hbD : b ∈ Subgroup.normalizer (D₁ : Set (PSL2 K)))
    (hbT : b ∈ Subgroup.normalizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K))) :
    D₁ ≤ R₁ ⊓ Subgroup.normalizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
  have hp := hpf.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨u, hu, hPu, hPc⟩ := psl2_card_four_mul hp hK hp8
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hu) (Nat.even_iff.mpr rfl)
  have hT4 : Nat.card (T : Subgroup (PSL2 K)) = 4 := by
    rw [Sylow.card_eq_multiplicity, hPu, show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) hu0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hu)
        (even_iff_two_dvd.mpr h))]
    simp
  have hR60 : Nat.card R₁ = 60 := CFSG.Walter.JT.card_of_psl24 eR
  have hTR4 : Nat.card ↥((T : Subgroup (PSL2 K)).subgroupOf R₁) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv, hT4]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTRi : ¬ 2 ∣ ((T : Subgroup (PSL2 K)).subgroupOf R₁).index := by
    have h := Subgroup.card_mul_index ((T : Subgroup (PSL2 K)).subgroupOf R₁)
    rw [hTR4, hR60] at h
    omega
  have hTR2 : IsPGroup 2 ↥((T : Subgroup (PSL2 K)).subgroupOf R₁) :=
    IsPGroup.of_card (n := 2) (by rw [hTR4]; norm_num)
  have hKl : IsKleinFour ↥((T : Subgroup (PSL2 K)).subgroupOf R₁) :=
    CFSG.Walter.JT.isKleinFour_sylow_of_psl24 eR (hTR2.toSylow hTRi)
  have hKl' : IsKleinFour ↥(T : Subgroup (PSL2 K)) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTR)
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [hK, pow_one]⟩
  have hCT : Subgroup.centralizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K)) = T :=
    psl2_kleinFour_centralizer_eq_self K hodd _ hKl'
  set m := Nat.card D₁ with hmdef
  have hcop : Nat.Coprime (Nat.card D₁) (Nat.card (T : Subgroup (PSL2 K))) := by
    rw [hT4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hDo)
  have hH : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = m * 4 := by
    rw [card_sup_of_perm hperm hcop, hT4]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D₁)
  have hgo : orderOf (g : PSL2 K) = m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hgH : (g : PSL2 K) ∈ D₁ ⊔ (T : Subgroup (PSL2 K)) := Subgroup.mem_sup_left g.2
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (by omega)
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hK1 (D₁ ⊔ (T : Subgroup (PSL2 K))) with
    ⟨m₀, -, hc, -⟩ | ⟨z, hz, hc, -⟩ | ⟨z, -, -, ⟨eH⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m₀, t, -, -, -, ht, E, C, -, -, hEc, -, hCc, -, -, -, φ, -, ⟨eSD⟩⟩ |
      ⟨m₀, hm₀, ⟨eL⟩⟩ | ⟨m₀, hm₀, -⟩
  ·
    exfalso
    rw [hH] at hc
    have h2 : 2 ∣ p ^ m₀ := by rw [← hc]; exact Dvd.intro (m * 2) (by ring)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  ·
    exfalso
    rw [hgcd, pow_one] at hz
    rw [hH] at hc
    have h4 : 4 ∣ z := hc ▸ Dvd.intro_left _ rfl
    rcases hz with hz | hz <;> have := h4.trans hz <;> omega
  ·
    have hz : 2 * z = m * 4 := by
      rw [← hH, Nat.card_congr eH.toEquiv, DihedralGroup.nat_card]
    obtain ⟨n, hn⟩ := hDo
    rcases Nat.lt_or_ge m 3 with hm | hm
    ·
      have hm1 : m = 1 := by omega
      have hD : D₁ = ⊥ := Subgroup.eq_bot_of_card_eq D₁ hm1
      rw [hD]
      exact bot_le
    · exfalso
      obtain rfl : z = 2 * m := by omega
      exact false_of_dihedral hm eH T le_sup_right eR hTR hbR hb3
        (Subgroup.inf_normalizer_le_normalizer_sup D₁ _ ⟨hbD, hbT⟩)
  ·
    have h12 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 12 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    set H := D₁ ⊔ (T : Subgroup (PSL2 K)) with hHdef
    have hTH4 : Nat.card ↥((T : Subgroup (PSL2 K)).subgroupOf H) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hT4]
    have hTHi : ¬ 2 ∣ ((T : Subgroup (PSL2 K)).subgroupOf H).index := by
      have h := Subgroup.card_mul_index ((T : Subgroup (PSL2 K)).subgroupOf H)
      rw [hTH4, h12] at h
      omega
    have hTH2 : IsPGroup 2 ↥((T : Subgroup (PSL2 K)).subgroupOf H) :=
      IsPGroup.of_card (n := 2) (by rw [hTH4]; norm_num)
    set V : Subgroup ↥H := (alternatingGroup.kleinFour (Fin 4)).map eA.symm.toMonoidHom
    have hV : V.Normal := by
      have := alternatingGroup.normal_kleinFour (α := Fin 4) (by simp)
      exact this.map _ eA.symm.surjective
    have hV4 : Nat.card V = 4 := by
      rw [Subgroup.card_map_of_injective eA.symm.injective,
        alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
    have hVT : V ≤ (T : Subgroup (PSL2 K)).subgroupOf H :=
      hV2.le_sylow_of_normal (hTH2.toSylow hTHi)
    have hVeq : V = (T : Subgroup (PSL2 K)).subgroupOf H :=
      Subgroup.eq_of_le_of_card_ge hVT (by rw [hV4, hTH4])
    have hTn : ((T : Subgroup (PSL2 K)).subgroupOf H).Normal := hVeq ▸ hV
    have hDN : D₁ ≤ Subgroup.normalizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
      intro x hx
      apply mem_normalizer_of_conj_mem
      intro t ht
      have := hTn.conj_mem ⟨t, Subgroup.mem_sup_right ht⟩ ht ⟨x, Subgroup.mem_sup_left hx⟩
      exact this
    set N := Subgroup.normalizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K))
    have hN96 := card_normalizer_dvd_of_centralizer_le (T := (T : Subgroup (PSL2 K))) hCT.le
    rw [hT4] at hN96
    have hN12 : Nat.card N ∣ 12 := by
      refine dvd_twelve_of_dvd hu (hN96.trans (by decide)) ?_
      rw [← hPu]
      exact Subgroup.card_subgroup_dvd_card _
    have hM4 : 4 ∣ Nat.card ↥(N ⊓ R₁) := by
      rw [← hT4]
      exact Subgroup.card_dvd_of_le (le_inf Subgroup.le_normalizer hTR)
    have hM3 : 3 ∣ Nat.card ↥(N ⊓ R₁) := by
      rw [← hb3]
      exact Subgroup.orderOf_dvd_natCard _ ⟨hbT, hbR⟩
    have hM12 : 12 ∣ Nat.card ↥(N ⊓ R₁) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hM4 hM3
    have hMN : N ⊓ R₁ = N := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      exact (Nat.le_of_dvd (by norm_num) hN12).trans (Nat.le_of_dvd Nat.card_pos hM12)
    intro x hx
    have hxR : x ∈ R₁ := by
      have := hDN hx
      rw [← hMN] at this
      exact this.2
    exact Subgroup.mem_inf.mpr ⟨hxR, hDN hx⟩
  ·
    exfalso
    have h24 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 24 := by
      rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := hDo
    omega
  ·
    exfalso
    have h60 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hm15 : m = 15 := by omega
    set σ := eA5 ⟨g, hgH⟩
    have hσ : orderOf σ = 15 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hgo, hm15]
    have hσ' : orderOf (σ : Equiv.Perm (Fin 5)) = 15 := by rw [Subgroup.orderOf_coe, hσ]
    rcases CFSG.Quasithin.G11.G118.gl24_ord_alt5 σ σ.2 with h | h | h <;>
      have := orderOf_dvd_of_pow_eq_one h <;> rw [hσ'] at this <;> norm_num at this
  ·
    exfalso
    have hcard : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = Nat.card E * Nat.card C := by
      rw [Nat.card_congr eSD.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hH, hEc, hCc] at hcard
    rw [hgcd, pow_one] at ht
    have h4 : 4 ∣ p ^ m₀ * t := hcard ▸ Dvd.intro_left _ rfl
    have hcop4 : Nat.Coprime 4 (p ^ m₀) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow 2 m₀ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have := (hcop4.dvd_of_dvd_mul_left h4).trans ht
    omega
  ·
    exfalso
    have hm1 : m₀ = 1 := Nat.eq_one_of_dvd_one hm₀
    subst hm1
    have hGF : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 (by norm_num), pow_one]
    have hcard : m * 4 = p * (p ^ 2 - 1) / 2 := by
      rw [← hH, Nat.card_congr eL.toEquiv]
      have := psl2_card_formula (GaloisField p 1)
        ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [hGF, pow_one]⟩
      rw [hGF] at this
      exact this
    have hp121 : 121 ≤ p ^ 2 := by nlinarith
    have hbig : 60 * p ≤ p * (p ^ 2 - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : p * 120 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul_left p (by omega)
      linarith
    have hmbig : 15 * p ≤ m := by omega
    rcases CFSG.Glauberman.Dickson.psl2_orderOf_dvd hK1 (g : PSL2 K) with h | h | h <;>
      rw [hgo] at h
    · have := Nat.le_of_dvd hp.pos h
      omega
    · rw [hK] at h
      have hpos : 0 < (p - 1) / (p - 1).gcd 2 := by
        have : (p - 1).gcd 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
        exact Nat.div_pos (by omega) (Nat.gcd_pos_of_pos_right _ (by norm_num))
      have := Nat.le_of_dvd hpos h
      have : (p - 1) / (p - 1).gcd 2 ≤ p - 1 := Nat.div_le_self _ _
      omega
    · rw [hK] at h
      have hpos : 0 < (p + 1) / (p - 1).gcd 2 := by
        have : (p - 1).gcd 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
        exact Nat.div_pos (by omega) (Nat.gcd_pos_of_pos_right _ (by norm_num))
      have := Nat.le_of_dvd hpos h
      have : (p + 1) / (p - 1).gcd 2 ≤ p + 1 := Nat.div_le_self _ _
      omega
  ·
    exfalso
    have := Nat.eq_one_of_dvd_one hm₀
    omega

theorem core_psl2_prime
    {K : Type} [Field K] [Finite K] {p : ℕ} [hpf : Fact p.Prime]
    (hK : Nat.card K = p) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp11 : 11 ≤ p)
    {D₁ R₁ : Subgroup (PSL2 K)} (T : Sylow 2 (PSL2 K)) (hDc : IsCyclic D₁)
    (hDo : Odd (Nat.card D₁))
    (hperm : ∀ t ∈ (T : Subgroup (PSL2 K)), ∀ x ∈ D₁, ∃ x' ∈ D₁,
      ∃ t' ∈ (T : Subgroup (PSL2 K)), t * x = x' * t')
    (eR : ↥R₁ ≃* L24) (hTR : (T : Subgroup (PSL2 K)) ≤ R₁) {b : PSL2 K} (hbR : b ∈ R₁)
    (hb3 : orderOf b = 3) (hbD : b ∈ Subgroup.normalizer (D₁ : Set (PSL2 K)))
    (hbT : b ∈ Subgroup.normalizer ((T : Subgroup (PSL2 K)) : Set (PSL2 K))) :
    D₁ ≤ Subgroup.normalizer (R₁ : Set (PSL2 K)) :=
  fun _ hx => Subgroup.le_normalizer (Subgroup.mem_inf.mp
    (core_psl2_prime_le hK hp8 hp11 T hDc hDo hperm eR hTR hbR hb3 hbD hbT hx)).1

end CFSG.Quasithin.H13.NQCat.T513
