module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25P
public import CFSG.LocalAnalysis.AGLEmbeddingD2.E9TwoGroup

public section

namespace CFSG.Quasithin.H13

namespace Lem25

open Equiv Equiv.Perm CFSG.AGLEmbeddingD2
open scoped Pointwise

abbrev A7 : Type := alternatingGroup (Fin 7)

@[expose] def a7a : A7 := ⟨c[0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7b : A7 := ⟨c[3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7g₁ : A7 := ⟨c[0, 3] * c[1, 4, 2, 5], by
  rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7g₂ : A7 := ⟨c[0, 3] * c[1, 5, 2, 4], by
  rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem a7a_mul_a7b : a7a * a7b = a7b * a7a := Subtype.ext (by decide)

theorem a7a_cube : a7a ^ 3 = 1 := Subtype.ext (by decide)

theorem a7b_cube : a7b ^ 3 = 1 := Subtype.ext (by decide)

theorem a7g₁_conj : a7g₁ * a7a * a7g₁⁻¹ = a7b := Subtype.ext (by decide)

theorem a7g₂_conj : a7g₂ * (a7a * a7b) * a7g₂⁻¹ = a7a * a7b⁻¹ := Subtype.ext (by decide)

theorem pairMap_a7_injective : Function.Injective (pairMap a7a a7b) := by
  intro q r h
  have h' := congrArg Subtype.val h
  revert q r
  simp only [pairMap, Subgroup.coe_mul, Subgroup.coe_pow]
  decide

@[expose] def a7E : Subgroup A7 := pairSubgroup a7a a7b a7a_mul_a7b a7a_cube a7b_cube

theorem card_a7E : Nat.card a7E = 9 := card_pairSubgroup _ _ _ pairMap_a7_injective

theorem a7a_mem : a7a ∈ a7E := mem_pairSubgroup_left _ _ _

theorem a7b_mem : a7b ∈ a7E := ⟨(0, 1), by simp [pairMap]⟩

theorem card_a7 : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem a7_isSimpleGroup : IsSimpleGroup A7 :=
  alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))

theorem exists_conj_mem_a7E (x : A7) (hx : x ^ 3 = 1) : ∃ g : A7, g * x * g⁻¹ ∈ a7E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hE3 : IsPGroup 3 a7E := IsPGroup.of_card (n := 2) (by rw [card_a7E]; norm_num)
  have hEi : ¬ 3 ∣ a7E.index := by
    have h := a7E.card_mul_index
    rw [card_a7E, card_a7] at h
    have : a7E.index = 280 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 Q (hE3.toSylow hEi)
  refine ⟨g, ?_⟩
  have hxQ : x ∈ (Q : Subgroup A7) := hPQ (Subgroup.mem_zpowers x)
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (Q : Subgroup A7) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply] using h1

theorem eq_top_of_index_le_six (H : Subgroup A7) (hH : H.index ≤ 6) : H = ⊤ := by
  have hs := a7_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hbot | htop
  · exfalso
    have h1 := H.index_normalCore_dvd_factorial_index
    rw [hbot, Subgroup.index_bot, card_a7] at h1
    have h2 : Nat.factorial H.index ≤ Nat.factorial 6 := Nat.factorial_le hH
    have h3 := Nat.le_of_dvd (Nat.factorial_pos _) h1
    have h4 : Nat.factorial 6 = 720 := by decide
    omega
  · exact eq_top_iff.mpr (htop ▸ H.normalCore_le)

theorem mem_of_mem_normalizer_a7 {B : Subgroup A7} (hB : Nat.card B = 168) {z : A7}
    (hz : z ∈ Subgroup.normalizer (B : Set A7)) : z ∈ B := by
  by_contra hzB
  set N := Subgroup.normalizer (B : Set A7) with hN
  have hBN : B ≤ N := Subgroup.le_normalizer
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBN
  have hNB : N ≠ B := fun h => hzB (h ▸ hz)
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hNB (Subgroup.eq_of_le_of_card_ge hBN (by rw [hm])).symm
  have hidx := N.card_mul_index
  rw [hm, hB, card_a7] at hidx
  have hidx6 : N.index ≤ 6 := by
    have h15 : m * N.index = 15 := by nlinarith
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have : N.index ∣ 15 := Dvd.intro_left m h15
    have hle : N.index ≤ 15 := Nat.le_of_dvd (by norm_num) this
    interval_cases hc : N.index <;> omega
  have htop := eq_top_of_index_le_six N hidx6
  have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hs := a7_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
  · rw [h, Subgroup.card_bot] at hB
    omega
  · rw [h, Subgroup.card_top, card_a7] at hB
    omega

theorem a7b_not_mem : a7b ∉ Subgroup.zpowers a7a := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [zpow_eq_zpow_emod' k a7a_cube] at hk
  simp only [Nat.cast_ofNat] at hk
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at hk <;> revert hk <;> decide

theorem a7a_ne_one : a7a ≠ 1 := by decide

theorem a7b_ne_one : a7b ≠ 1 := by decide

theorem two_pow_mod_three (x : ℕ) : 2 ^ x % 3 = if x % 2 = 0 then 1 else 2 := by
  induction x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

theorem mod_two_eq_of_modEq {x y : ℕ} (h : 2 ^ x ≡ 2 ^ y [MOD 3]) : x % 2 = y % 2 := by
  unfold Nat.ModEq at h
  rw [two_pow_mod_three, two_pow_mod_three] at h
  split_ifs at h <;> omega

variable {G : Type} [Group G]

theorem false_of_alt_seven [Finite G] {K R Y : Subgroup G}
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hYK : Y ≤ K) (hR2 : IsPGroup 2 R)
    (hRc : Nat.card R = 2 ^ 6 ∨ Nat.card R = 2 ^ 7)
    (χ : ↥K →* A7) (hχ : Function.Surjective χ) (hker : IsPGroup 2 χ.ker)
    (hYc : Nat.card ((Y.subgroupOf K).map χ) = 168)
    (hY16 : ∀ y ∈ Y, orderOf y = 3 →
      Nat.card ↥(R ⊓ Subgroup.centralizer ({y} : Set G)) * 16 = Nat.card R)
    (hNY : ∀ c ∈ K, orderOf c = 3 →
      Nat.card ↥(R ⊓ Subgroup.centralizer ({c} : Set G)) * 4 = Nat.card R →
      c ∈ Subgroup.normalizer (Y : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ : ∃ f : G → ℕ, ∀ x, f x = Nat.card ↥(R ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ⟨_, fun _ => rfl⟩
  have hfconj : ∀ g ∈ K, ∀ x : G, f (g * x * g⁻¹) = f x := fun g hg x => by
    rw [hf, hf]
    exact E9TwoGroup.card_inf_centralizer_conj R (hKR hg) x
  have hflift : ∀ k₁ k₂ : ↥K, k₁ ^ 3 = 1 → k₂ ^ 3 = 1 → χ k₁ = χ k₂ →
      f (k₁ : G) = f (k₂ : G) := by
    intro k₁ k₂ h₁ h₂ h12
    obtain ⟨g, hg⟩ := exists_conj_of_map_eq χ hker h₁ h₂ h12
    rw [← hg]
    exact (hfconj g g.2 k₁).symm
  have hcent : ∀ z : G, Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun z => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hfz : ∀ x x' : G, Subgroup.zpowers x = Subgroup.zpowers x' → f x = f x' := by
    intro x x' h
    rw [hf, hf, hcent x, hcent x', h]
  have hpow : ∀ S : Subgroup G, S ≤ R → ∃ k, Nat.card S = 2 ^ k := fun S hS =>
    (hR2.to_le hS).exists_card_eq
  have h3Y : 3 ∣ Nat.card Y := by
    have h1 : Nat.card ((Y.subgroupOf K).map χ) ∣ Nat.card (Y.subgroupOf K) :=
      Subgroup.card_map_dvd _ _
    rw [hYc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv] at h1
    exact dvd_trans (by norm_num) h1
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 3 h3Y
  have hyY : (y₀ : G) ∈ Y := y₀.2
  have hyo : orderOf (y₀ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hfy : f y₀ * 16 = Nat.card R := by rw [hf]; exact hY16 _ hyY hyo
  set yk : ↥K := ⟨y₀, hYK hyY⟩ with hyk
  have hyk3 : yk ^ 3 = 1 := Subtype.ext (hyo ▸ pow_orderOf_eq_one (y₀ : G))
  obtain ⟨g, hg⟩ := exists_conj_mem_a7E (χ yk) (by rw [← map_pow, hyk3, map_one])
  obtain ⟨gk, hgk⟩ := hχ g
  set y' : ↥K := gk * yk * gk⁻¹ with hy'
  have hy'3 : y' ^ 3 = 1 := by rw [hy', conj_pow, hyk3]; group
  have hfy' : f y' = f y₀ := hfconj gk gk.2 _
  have hχy' : χ y' ∈ a7E := by rw [hy', map_mul, map_mul, map_inv, hgk]; exact hg
  have hχy'1 : χ y' ≠ 1 := by
    intro h1
    have h2 := eq_one_of_mem_ker χ hker h1 hy'3
    have h3 : yk = 1 := by
      calc yk = gk⁻¹ * y' * gk := by rw [hy']; group
        _ = 1 := by rw [h2]; group
    have h4 : (y₀ : G) = 1 := congrArg Subtype.val h3
    rw [h4, orderOf_one] at hyo
    omega
  obtain ⟨S, hSK, hScard, hSab, hSmap, hSinj⟩ := exists_elemAbelian_lift χ hker (E := a7E)
    (by rw [MonoidHom.range_eq_top.mpr hχ]; exact le_top) (pairSubgroup_elem _ _ _) (k := 2)
    (by rw [card_a7E]; norm_num)
  have hS9 : Nat.card S = 9 := by rw [hScard]; norm_num
  let F : ↥S → ↥a7E := fun s => ⟨χ ⟨s, hSK s.2⟩, hSmap _ s.2⟩
  have hFinj : Function.Injective F := by
    intro s s' h
    have h1 : χ (⟨s, hSK s.2⟩ * (⟨s', hSK s'.2⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (congrArg Subtype.val h)
    have h2 := hSinj _ (S.mul_mem s.2 (S.inv_mem s'.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp (congrArg Subtype.val h2))
  have hFsurj : Function.Surjective F :=
    (hFinj.bijective_of_nat_card_le (by rw [card_a7E, hS9])).2
  have hS3 : ∀ s : ↥S, s ^ 3 = 1 := fun s => Subtype.ext (hSab.2 _ s.2)
  have hk3 : ∀ s : ↥S, (⟨s, hSK s.2⟩ : ↥K) ^ 3 = 1 := fun s =>
    Subtype.ext (show (s : G) ^ 3 = 1 from hSab.2 _ s.2)
  obtain ⟨sa, hsa⟩ := hFsurj ⟨a7a, a7a_mem⟩
  obtain ⟨sb, hsb⟩ := hFsurj ⟨a7b, a7b_mem⟩
  have hχa : χ ⟨sa, hSK sa.2⟩ = a7a := congrArg Subtype.val hsa
  have hχb : χ ⟨sb, hSK sb.2⟩ = a7b := congrArg Subtype.val hsb
  have hsa1 : sa ≠ 1 := by
    rintro rfl
    apply a7a_ne_one
    rw [← hχa]
    exact map_one χ
  have hsao : orderOf sa = 3 := orderOf_eq_prime (hS3 sa) hsa1
  have hsb1 : sb ≠ 1 := by
    rintro rfl
    have : a7b = 1 := by rw [← hχb]; exact map_one χ
    exact a7b_ne_one this
  have hsbo : orderOf sb = 3 := orderOf_eq_prime (hS3 sb) hsb1
  have hab : sb ∉ Subgroup.zpowers sa := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply a7b_not_mem
    rw [← hχb, ← hχa]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using congrArg (fun z : ↥S => (z : G)) hk)
  have hcS : Commute sa sb := hSab.1.is_comm.comm sa sb
  have hcop : Nat.Coprime (Nat.card R) 3 := by
    rcases hRc with h | h <;> rw [h] <;> norm_num
  have hsolv : Group.IsSolvable R := by
    have := hR2.isNilpotent
    infer_instance
  have habG : (sb : G) ∉ Subgroup.zpowers (sa : G) := by
    intro h
    apply hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
  have hW := E9TwoGroup.card_mul_card_inf_centralizer_pow_three R S (hSK.trans hKR) hcop hsolv
    hS9 sa.2 sb.2 (by rw [Subgroup.orderOf_coe]; exact hsao)
    (by rw [Subgroup.orderOf_coe]; exact hsbo) habG
  have hfab : f sa = f sb := by
    obtain ⟨g₁, hg₁⟩ := hχ a7g₁
    have h1 := hflift (g₁ * ⟨sa, hSK sa.2⟩ * g₁⁻¹) ⟨sb, hSK sb.2⟩
      (by rw [conj_pow, hk3 sa]; group) (hk3 sb)
      (by simp only [map_mul, map_inv, hg₁, hχa, hχb]; exact a7g₁_conj)
    calc f sa = f ((g₁ : G) * sa * (g₁ : G)⁻¹) := (hfconj g₁ g₁.2 _).symm
      _ = f sb := h1
  have hkab3 : (⟨sa, hSK sa.2⟩ * ⟨sb, hSK sb.2⟩ : ↥K) ^ 3 = 1 := by
    have := hk3 (sa * sb)
    exact this
  have hkabi3 : (⟨sa, hSK sa.2⟩ * (⟨sb, hSK sb.2⟩ : ↥K)⁻¹) ^ 3 = 1 := by
    have := hk3 (sa * sb⁻¹)
    exact this
  have hfd : f ((sa : G) * sb) = f ((sa : G) * (sb : G)⁻¹) := by
    obtain ⟨g₂, hg₂⟩ := hχ a7g₂
    have h1 := hflift (g₂ * (⟨sa, hSK sa.2⟩ * ⟨sb, hSK sb.2⟩) * g₂⁻¹)
      (⟨sa, hSK sa.2⟩ * (⟨sb, hSK sb.2⟩ : ↥K)⁻¹)
      (by rw [conj_pow, hkab3]; group) hkabi3
      (by simp only [map_mul, map_inv, hg₂, hχa, hχb]; exact a7g₂_conj)
    calc f ((sa : G) * sb) = f ((g₂ : G) * ((sa : G) * sb) * (g₂ : G)⁻¹) :=
          (hfconj g₂ g₂.2 _).symm
      _ = f ((sa : G) * (sb : G)⁻¹) := h1
  obtain ⟨sy, hsy⟩ := hFsurj ⟨χ y', hχy'⟩
  have hχsy : χ ⟨sy, hSK sy.2⟩ = χ y' := congrArg Subtype.val hsy
  have hsy1 : sy ≠ 1 := by
    rintro rfl
    apply hχy'1
    rw [← hχsy]
    exact map_one χ
  have hfsy : f y' = f sy := hflift y' ⟨sy, hSK sy.2⟩ hy'3 (hk3 sy) hχsy.symm
  have hsyo : orderOf sy = 3 := orderOf_eq_prime (hS3 sy) hsy1
  have hline : ∀ x : ↥S, orderOf x = 3 → sy ∈ Subgroup.zpowers x → f sy = f x := by
    intro x hx hmem
    have h1 := E9TwoGroup.zpowers_eq_of_mem_of_mem hsyo hx hsy1 (Subgroup.mem_zpowers sy) hmem
    apply hfz
    have h2 := congrArg (Subgroup.map S.subtype) h1
    rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
  have hsabo : orderOf (sa * sb) = 3 :=
    orderOf_eq_prime (hS3 _) (fun h => hab (by
      rw [eq_inv_of_mul_eq_one_right h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers sa)))
  have hsabio : orderOf (sa * sb⁻¹) = 3 :=
    orderOf_eq_prime (hS3 _) (fun h => hab (by
      rw [inv_injective (eq_inv_of_mul_eq_one_right h)]; exact Subgroup.mem_zpowers sa))
  have hfy'2 : f y' = f sa ∨ f y' = f ((sa : G) * sb) := by
    rw [hfsy]
    rcases E9TwoGroup.mem_lines hsao hsbo hab hcS hS9 hsy1 with h | h | h | h
    · exact Or.inl (hline sa hsao h)
    · exact Or.inl ((hline sb hsbo h).trans hfab.symm)
    · refine Or.inr ?_
      rw [hline (sa * sb) hsabo h, Subgroup.coe_mul]
    · refine Or.inr ?_
      rw [hline (sa * sb⁻¹) hsabio h, Subgroup.coe_mul, Subgroup.coe_inv, ← hfd]
  obtain ⟨r, hr⟩ := hpow R le_rfl
  have hr67 : r = 6 ∨ r = 7 := by
    rcases hRc with h | h <;> rw [hr] at h
    · exact Or.inl (Nat.pow_right_injective le_rfl h)
    · exact Or.inr (Nat.pow_right_injective le_rfl h)
  obtain ⟨s, hs⟩ := hpow _ (inf_le_left : R ⊓ Subgroup.centralizer ({(sa : G)} : Set G) ≤ R)
  obtain ⟨t, ht⟩ := hpow _ (inf_le_left :
    R ⊓ Subgroup.centralizer ({(sa : G) * sb} : Set G) ≤ R)
  obtain ⟨e, he⟩ := hpow _ (inf_le_left : R ⊓ Subgroup.centralizer (S : Set G) ≤ R)
  have hfa : f sa = 2 ^ s := by rw [hf]; exact hs
  have hfab' : f ((sa : G) * sb) = 2 ^ t := by rw [hf]; exact ht
  have hW' : Nat.card R * Nat.card ↥(R ⊓ Subgroup.centralizer (S : Set G)) ^ 3 =
      f sa * f sb * f ((sa : G) * sb) * f ((sa : G) * (sb : G)⁻¹) := by
    rw [hf, hf, hf, hf]
    exact hW
  rw [← hfab, ← hfd, hr, he, hfa, hfab'] at hW'
  have hexp : r + 3 * e = 2 * s + 2 * t := by
    apply Nat.pow_right_injective (le_refl 2)
    show 2 ^ (r + 3 * e) = 2 ^ (2 * s + 2 * t)
    rw [pow_add, pow_add, pow_mul', pow_mul', pow_mul', hW']
    ring
  have hR3 : ∀ x ∈ K, x ^ 3 = 1 → f x ≡ 2 ^ r [MOD 3] := fun x hx hx3 => by
    rw [hf, ← hr]
    exact card_inf_centralizer_elem_modEq hx3 (hKR hx)
  have hsr : s % 2 = r % 2 := mod_two_eq_of_modEq (hfa ▸ hR3 _ (hSK sa.2) (hSab.2 _ sa.2))
  have htr : t % 2 = r % 2 := mod_two_eq_of_modEq
    (hfab' ▸ hR3 _ (hSK (S.mul_mem sa.2 sb.2)) (hSab.2 _ (S.mul_mem sa.2 sb.2)))
  have her : e % 2 = r % 2 := by
    have h1 : IsPGroup 3 S := IsPGroup.of_card (n := 2) hScard
    have h2 := card_inf_centralizer_modEq h1 (hSK.trans hKR)
    rw [he, hr] at h2
    exact mod_two_eq_of_modEq h2
  have hdvd : ∀ x ∈ S, Nat.card ↥(R ⊓ Subgroup.centralizer (S : Set G)) ∣ f x := fun x hx => by
    rw [hf]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hx)))
  have hes : e ≤ s := by
    have := hdvd _ sa.2
    rw [he, hfa] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have het : e ≤ t := by
    have := hdvd _ (S.mul_mem sa.2 sb.2)
    rw [he, hfab'] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hst : s + 4 = r ∨ t + 4 = r := by
    have h16 : f y' * 16 = 2 ^ r := by rw [hfy', hfy, hr]
    rcases hfy'2 with h | h
    · left
      rw [h, hfa, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add] at h16
      exact Nat.pow_right_injective le_rfl h16
    · right
      rw [h, hfab', show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add] at h16
      exact Nat.pow_right_injective le_rfl h16
  obtain ⟨c, hcS, hco, hc4⟩ : ∃ c ∈ S, orderOf c = 3 ∧ f c * 4 = Nat.card R := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    have : (t + 2 = r) ∨ (s + 2 = r) := by omega
    rcases this with h | h
    · refine ⟨_, S.mul_mem sa.2 sb.2, (Subgroup.orderOf_coe (sa * sb)).trans hsabo, ?_⟩
      rw [hfab', hr, h4, ← pow_add, h]
    · refine ⟨_, sa.2, by rw [Subgroup.orderOf_coe]; exact hsao, ?_⟩
      rw [hfa, hr, h4, ← pow_add, h]
  have hcK : c ∈ K := hSK hcS
  have hcY := hNY c hcK hco (by rw [← hf]; exact hc4)
  set ck : ↥K := ⟨c, hcK⟩ with hck
  have hck3 : ck ^ 3 = 1 := Subtype.ext (hco ▸ pow_orderOf_eq_one c)
  set Yb : Subgroup A7 := (Y.subgroupOf K).map χ with hYb
  have hcYb : χ ck ∉ Yb := by
    intro hmem
    have hχc1 : χ ck ≠ 1 := by
      intro h1
      have := eq_one_of_mem_ker χ hker h1 hck3
      have h2 : c = 1 := congrArg Subtype.val this
      rw [h2, orderOf_one] at hco
      omega
    have hoχ : orderOf (χ ck) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hck3, map_one]) hχc1
    let ψ : ↥Y →* ↥Yb := (χ.comp (Subgroup.inclusion hYK)).codRestrict Yb fun y =>
      ⟨Subgroup.inclusion hYK y, y.2, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, ⟨y₁, hy₁, rfl⟩⟩
      exact ⟨⟨y₁, hy₁⟩, rfl⟩
    obtain ⟨x, hxo, hx⟩ := exists_odd_lift ψ hψ (g := ⟨χ ck, hmem⟩)
      (by rw [Subgroup.orderOf_mk, hoχ]; decide)
    set xk : ↥K := Subgroup.inclusion hYK x with hxk
    have hχx : χ xk = χ ck := congrArg Subtype.val hx
    have hxk3 : xk ^ 3 = 1 := by
      have h1 : χ (xk ^ 3) = 1 := by rw [map_pow, hχx, ← map_pow, hck3, map_one]
      obtain ⟨i, hi⟩ := hker ⟨_, h1⟩
      have h2 : (xk ^ 3) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
      have hodd : Odd (orderOf (xk ^ 3)) := by
        have h3 : orderOf (xk ^ 3) ∣ orderOf xk := orderOf_pow_dvd _
        have h4 : orderOf xk = orderOf (x : G) := by
          rw [hxk, ← Subgroup.orderOf_coe]
          rfl
        exact Odd.of_dvd_nat (h4 ▸ hxo) h3
      have hcop : Nat.Coprime (orderOf (xk ^ 3)) (2 ^ i) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2))
    have hxk1 : xk ≠ 1 := by
      intro h1
      apply hχc1
      rw [← hχx, h1, map_one]
    have hxo3 : orderOf (xk : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hxk3 hxk1
    have h16 : f xk * 16 = Nat.card R := by rw [hf]; exact hY16 (xk : G) x.2 hxo3
    have hfe : f c = f xk := hflift ck xk hck3 hxk3 hχx.symm
    have hpos : 0 < f c := by rw [hf]; exact Nat.card_pos
    rw [← hfe] at h16
    omega
  have hcN : χ ck ∈ Subgroup.normalizer (Yb : Set A7) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨y₁, hy₁, rfl⟩ := hz
    refine ⟨ck * y₁ * ck⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show c * (y₁ : G) * c⁻¹ ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp hcY _).mp hy₁
  exact hcYb (mem_of_mem_normalizer_a7 hYc hcN)

end Lem25

end CFSG.Quasithin.H13
