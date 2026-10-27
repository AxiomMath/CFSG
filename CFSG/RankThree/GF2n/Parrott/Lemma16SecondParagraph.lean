module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FixedCount
public import CFSG.LocalAnalysis.EvenBN.Tits.S56PermFive

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {z : G}

theorem conj_eq_of_mem_normalizer_of_fusion {K A : Subgroup G} {x : G}
    (hK : IsElemAbelian 2 K) (hxK : x ∈ K) (hAK : A ≤ K) (hzA : z ∈ A) (hxA : x ∉ A)
    (hA : 2 < Nat.card A) (hS : ∀ k ∈ K, IsConj z k ↔ (k = z ∨ x⁻¹ * k ∈ A)) :
    ∀ n ∈ Subgroup.normalizer (K : Set G), n * z * n⁻¹ = z := by
  classical
  have hzK : z ∈ K := hAK hzA
  obtain ⟨a₀, ha₀A, ha₀1, ha₀z⟩ : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ a₀ ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (A : Set G) ⊆ {1, z} := fun a ha => by
      by_cases h1 : a = 1
      · exact Or.inl h1
      · exact Or.inr (hcon a ha h1)
    have hle : Nat.card A ≤ 2 := by
      change Nat.card ↥(A : Set G) ≤ 2
      rw [Nat.card_coe_set_eq]
      calc (A : Set G).ncard ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({z} : Set G).ncard + 1 := Set.ncard_insert_le 1 {z}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  let P : G → Prop := fun s => ∀ s' ∈ K, IsConj z s' → s * s' ≠ 1 → IsConj z (s * s')
  have hPz : P z := by
    intro s' hs'K hs'z hne
    rcases (hS s' hs'K).mp hs'z with rfl | hs'A
    · exact absurd (hK.mul_self_eq_one hzK) hne
    · refine (hS (z * s') (K.mul_mem hzK hs'K)).mpr (Or.inr ?_)
      have heq : x⁻¹ * (z * s') = z * (x⁻¹ * s') := by
        rw [← mul_assoc, hK.comm (K.inv_mem hxK) hzK, mul_assoc]
      rw [heq]
      exact A.mul_mem hzA hs'A
  have hnotP : ∀ s ∈ K, IsConj z s → s ≠ z → ¬ P s := by
    intro s hsK hsz hsne hP
    have hb : x⁻¹ * s ∈ A := ((hS s hsK).mp hsz).resolve_left hsne
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left (hK.mul_self_eq_one hxK)
    have hs'K : s⁻¹ * a₀ ∈ K := K.mul_mem (K.inv_mem hsK) (hAK ha₀A)
    have hs'z : IsConj z (s⁻¹ * a₀) := by
      refine (hS _ hs'K).mpr (Or.inr ?_)
      have heq : x⁻¹ * (s⁻¹ * a₀) = (x⁻¹ * s)⁻¹ * a₀ := by
        calc x⁻¹ * (s⁻¹ * a₀) = (s * x)⁻¹ * a₀ := by group
          _ = (x * s)⁻¹ * a₀ := by rw [hK.comm hsK hxK]
          _ = (x⁻¹ * s)⁻¹ * a₀ := by rw [hxinv]
      rw [heq]
      exact A.mul_mem (A.inv_mem hb) ha₀A
    have h1 : s * (s⁻¹ * a₀) = a₀ := by group
    have h2 := hP (s⁻¹ * a₀) hs'K hs'z (by rw [h1]; exact ha₀1)
    rw [h1] at h2
    rcases (hS a₀ (hAK ha₀A)).mp h2 with h | h
    · exact ha₀z h
    · apply hxA
      have heq : x = a₀ * (x⁻¹ * a₀)⁻¹ := by group
      rw [heq]
      exact A.mul_mem ha₀A (A.inv_mem h)
  intro n hn
  have hnK : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hzK
  have hninv : ∀ k ∈ K, n⁻¹ * k * n ∈ K := fun k hk => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) k).mp hk
    simpa using h
  have hPn : P (n * z * n⁻¹) := by
    intro s' hs'K hs'z hne
    have hs''K : n⁻¹ * s' * n ∈ K := hninv s' hs'K
    have hs''z : IsConj z (n⁻¹ * s' * n) :=
      hs'z.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩)
    have heq : n * z * n⁻¹ * s' = n * (z * (n⁻¹ * s' * n)) * n⁻¹ := by group
    have hne' : z * (n⁻¹ * s' * n) ≠ 1 := by
      intro h1
      apply hne
      rw [heq, h1]
      group
    rw [heq]
    exact (hPz _ hs''K hs''z hne').trans (isConj_iff.mpr ⟨n, rfl⟩)
  by_contra hne
  exact hnotP (n * z * n⁻¹) hnK (isConj_iff.mpr ⟨n, rfl⟩) hne hPn

theorem eq_of_ne_one_of_card_eq_two {S : Subgroup G} (hS : Nat.card S = 2) {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have ha2 : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := hS ▸ Subgroup.orderOf_dvd_natCard S ha
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hzp : Subgroup.zpowers a = S := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
    rw [hS, Nat.card_zpowers, ha2]
  have hbz : b ∈ Subgroup.zpowers a := hzp ▸ hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    apply hb1
    rw [← zpow_mod_orderOf, ha2]
    exact_mod_cast (by rw [h0, zpow_zero] : a ^ (k % 2) = 1)
  · rw [← zpow_mod_orderOf, ha2]
    exact_mod_cast (by rw [h1, zpow_one] : a ^ (k % 2) = a).symm

theorem false_of_commute_on_elemAbelian_thirtyTwo {K : Subgroup G} (hK : IsElemAbelian 2 K)
    (hK32 : Nat.card K = 2 ^ 5) {y e : G} (hy5 : IsPGroup 5 (Subgroup.zpowers y))
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (heN : e ∈ Subgroup.normalizer (K : Set G))
    (hy : y ∉ Subgroup.centralizer (K : Set G)) (he : e ∉ Subgroup.centralizer (K : Set G))
    (he2 : e * e ∈ Subgroup.centralizer (K : Set G))
    (hc : e * y * e⁻¹ * y⁻¹ ∈ Subgroup.centralizer (K : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
  have heK : ∀ k ∈ K, e * k * e⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp heN k).mp hk
  have hcK : ∀ k ∈ K, k * (e * y * e⁻¹ * y⁻¹) = (e * y * e⁻¹ * y⁻¹) * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have he2K : ∀ k ∈ K, k * (e * e) = (e * e) * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp he2 k hk
  have hswap : ∀ k ∈ K, e * (y * k * y⁻¹) * e⁻¹ = y * (e * k * e⁻¹) * y⁻¹ := by
    intro k hk
    have hm : y * (e * k * e⁻¹) * y⁻¹ ∈ K := hyK _ (heK k hk)
    calc e * (y * k * y⁻¹) * e⁻¹
        = (e * y * e⁻¹ * y⁻¹) * (y * (e * k * e⁻¹) * y⁻¹) * (e * y * e⁻¹ * y⁻¹)⁻¹ := by group
      _ = (y * (e * k * e⁻¹) * y⁻¹) * (e * y * e⁻¹ * y⁻¹) * (e * y * e⁻¹ * y⁻¹)⁻¹ := by
          rw [← hcK _ hm]
      _ = y * (e * k * e⁻¹) * y⁻¹ := by group
  have hPK : ∀ w ∈ Subgroup.zpowers y, ∀ k ∈ K, w * k * w⁻¹ ∈ K := fun w hw k hk =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hyN) hw) k).mp hk
  set CKy : Subgroup G := K ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)
    with hCKy
  have h1 := CFSG.LocalAnalysis.EvenBN.Tits.card_modEq_card_inf_centralizer hy5 hPK
  have hCKy2 : Nat.card CKy = 2 := by
    have hdvd : Nat.card CKy ∣ 32 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : CKy ≤ K)
      have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
      rw [hK32, h32] at h
      exact h
    have hne : Nat.card CKy ≠ 32 := by
      intro h32
      have heq : CKy = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h32, hK32]; norm_num)
      apply hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : k ∈ CKy := heq ▸ hk
      exact (CFSG.LocalAnalysis.EvenBN.Tits.mem_centralizer_zpowers_iff.1
        (Subgroup.mem_inf.1 hk').2).symm
    rw [hK32] at h1
    have hle : Nat.card CKy ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card CKy <;> omega
  set F : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hF
  have hmemF : ∀ {k : G}, k ∈ F ↔ k ∈ K ∧ e * k * e⁻¹ = k := by
    intro k
    rw [hF, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hk, hke⟩
      exact ⟨hk, by rw [← hke]; group⟩
    · rintro ⟨hk, hke⟩
      refine ⟨hk, ?_⟩
      calc k * e = (e * k * e⁻¹) * e := by rw [hke]
        _ = e * k := by group
  have hyNF : y ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨hkK, hke⟩ := hmemF.mp hk
      refine hmemF.mpr ⟨hyK k hkK, ?_⟩
      rw [hswap k hkK, hke]
    · intro hk
      obtain ⟨hkK, hke⟩ := hmemF.mp hk
      have hkK' : k ∈ K := (Subgroup.mem_normalizer_iff.mp hyN k).mpr hkK
      refine hmemF.mpr ⟨hkK', ?_⟩
      have h := hswap k hkK'
      rw [hke] at h
      have h' : k = e * k * e⁻¹ := by
        have := congrArg (fun w => y⁻¹ * w * y) h
        simpa [mul_assoc] using this
      exact h'.symm
  have hPF : ∀ w ∈ Subgroup.zpowers y, ∀ k ∈ F, w * k * w⁻¹ ∈ F := fun w hw k hk =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hyNF) hw) k).mp hk
  have h2 := CFSG.LocalAnalysis.EvenBN.Tits.card_modEq_card_inf_centralizer hy5 hPF
  have hCKyF : CKy ≤ F := by
    obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c₀ ∈ CKy, c₀ ≠ 1 := by
      have : Nontrivial CKy := by
        rw [← Finite.one_lt_card_iff_nontrivial, hCKy2]
        norm_num
      obtain ⟨c, hc⟩ := exists_ne (1 : CKy)
      exact ⟨c, c.2, fun h => hc (Subtype.ext h)⟩
    intro k hk
    by_cases hk1 : k = 1
    · rw [hk1]
      exact F.one_mem
    have hkK : k ∈ K := (Subgroup.mem_inf.1 hk).1
    have hky : y * k = k * y :=
      CFSG.LocalAnalysis.EvenBN.Tits.mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
    have hek : e * k * e⁻¹ ∈ CKy := by
      refine Subgroup.mem_inf.2 ⟨heK k hkK, ?_⟩
      apply CFSG.LocalAnalysis.EvenBN.Tits.mem_centralizer_zpowers_iff.2
      have h := hswap k hkK
      have hyk : y * k * y⁻¹ = k := by rw [hky]; group
      rw [hyk] at h
      calc y * (e * k * e⁻¹) = (y * (e * k * e⁻¹) * y⁻¹) * y := by group
        _ = (e * k * e⁻¹) * y := by rw [← h]
    have hek1 : e * k * e⁻¹ ≠ 1 := by
      intro h1
      apply hk1
      have := congrArg (fun w => e⁻¹ * w * e) h1
      simpa [mul_assoc] using this
    have heq : e * k * e⁻¹ = k :=
      (eq_of_ne_one_of_card_eq_two hCKy2 hek hc₀ hek1 hc₀1).trans
        (eq_of_ne_one_of_card_eq_two hCKy2 hk hc₀ hk1 hc₀1).symm
    exact hmemF.mpr ⟨hkK, heq⟩
  have hFy : F ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) = CKy := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf hCKyF inf_le_right
  rw [hFy, hCKy2] at h2
  let φ : ↥K →* ↥K :=
    { toFun := fun k => ⟨e * (k : G) * e⁻¹ * (k : G)⁻¹, K.mul_mem (heK k k.2) (K.inv_mem k.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k₁ k₂ => Subtype.ext (by
        change e * ((k₁ : G) * (k₂ : G)) * e⁻¹ * ((k₁ : G) * (k₂ : G))⁻¹ =
          (e * (k₁ : G) * e⁻¹ * (k₁ : G)⁻¹) * (e * (k₂ : G) * e⁻¹ * (k₂ : G)⁻¹)
        have hcomm := hK.comm (K.inv_mem k₁.2)
          (K.mul_mem (heK k₂ k₂.2) (K.inv_mem k₂.2))
        calc e * ((k₁ : G) * (k₂ : G)) * e⁻¹ * ((k₁ : G) * (k₂ : G))⁻¹
            = e * (k₁ : G) * e⁻¹ * ((e * (k₂ : G) * e⁻¹ * (k₂ : G)⁻¹) * (k₁ : G)⁻¹) := by group
          _ = e * (k₁ : G) * e⁻¹ * ((k₁ : G)⁻¹ * (e * (k₂ : G) * e⁻¹ * (k₂ : G)⁻¹)) := by
              rw [hcomm]
          _ = (e * (k₁ : G) * e⁻¹ * (k₁ : G)⁻¹) * (e * (k₂ : G) * e⁻¹ * (k₂ : G)⁻¹) := by
              group) }
  have hker : ∀ k : ↥K, k ∈ φ.ker ↔ (k : G) ∈ F := by
    intro k
    rw [MonoidHom.mem_ker, hmemF]
    constructor
    · intro h1
      have h1' : e * (k : G) * e⁻¹ * (k : G)⁻¹ = 1 := congrArg Subtype.val h1
      exact ⟨k.2, mul_inv_eq_one.mp h1'⟩
    · rintro ⟨-, h1⟩
      exact Subtype.ext (show e * (k : G) * e⁻¹ * (k : G)⁻¹ = 1 by rw [h1, mul_inv_cancel])
  have hrange : ∀ k : ↥K, ((φ k : ↥K) : G) ∈ F := by
    intro k
    have hk := k.2
    have hek := heK k hk
    refine hmemF.mpr ⟨(φ k).2, ?_⟩
    change e * (e * (k : G) * e⁻¹ * (k : G)⁻¹) * e⁻¹ = e * (k : G) * e⁻¹ * (k : G)⁻¹
    have h1 : e * (e * (k : G) * e⁻¹ * (k : G)⁻¹) * e⁻¹ =
        (e * e) * (k : G) * (e * e)⁻¹ * (e * (k : G) * e⁻¹)⁻¹ := by group
    rw [h1, ← he2K _ hk]
    have hinv1 : (e * (k : G) * e⁻¹)⁻¹ = e * (k : G) * e⁻¹ :=
      inv_eq_of_mul_eq_one_left (hK.mul_self_eq_one hek)
    have hinv2 : (k : G)⁻¹ = (k : G) := inv_eq_of_mul_eq_one_left (hK.mul_self_eq_one hk)
    rw [hinv1, hinv2, mul_inv_cancel_right, hK.comm hk hek]
  have hcardK : Nat.card K ≤ Nat.card F * Nat.card F := by
    have h3 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h3
    have hkerF : Nat.card φ.ker = Nat.card F := by
      have hle : F ≤ K := inf_le_left
      have heq : φ.ker = F.subgroupOf K := by
        ext k
        rw [Subgroup.mem_subgroupOf, hker]
      rw [heq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hrangeF : Nat.card φ.range ≤ Nat.card F := by
      have hle : φ.range ≤ F.subgroupOf K := by
        rintro _ ⟨k, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr (hrange k)
      calc Nat.card φ.range ≤ Nat.card (F.subgroupOf K) := Subgroup.card_le_of_le hle
        _ = Nat.card F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← h3, hkerF]
    exact Nat.mul_le_mul_left _ hrangeF
  have hFdvd : Nat.card F ∣ 32 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : F ≤ K)
    have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [hK32, h32] at h
    exact h
  have hF32 : Nat.card F = 32 := by
    rw [hK32] at hcardK
    have hle : Nat.card F ≤ 32 := Nat.le_of_dvd (by norm_num) hFdvd
    unfold Nat.ModEq at h2
    interval_cases h : Nat.card F <;> omega
  have hFK : F = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hF32, hK32]; norm_num)
  apply he
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : k ∈ F := hFK ▸ hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hk').2)

theorem exists_five_element_commute_mod {N C E : Subgroup G}
    (hnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (h20 : C.relIndex N = 20)
    (hEN : E ≤ N) (h4 : C.relIndex E = 4) (hE2 : ∀ e ∈ E, e * e ∈ C) :
    ∃ y ∈ N, IsPGroup 5 (Subgroup.zpowers y) ∧ y ∉ C ∧
      ∃ e ∈ E, e ∉ C ∧ e * y * e⁻¹ * y⁻¹ ∈ C := by
  classical
  obtain ⟨e₁, he₁E, he₁C, e₂, he₂E, he₂C, he₁₂C⟩ :
      ∃ e₁ ∈ E, e₁ ∉ C ∧ ∃ e₂ ∈ E, e₂ ∉ C ∧ e₁ * e₂ ∉ C := by
    have hR : Nat.card (↥E ⧸ C.subgroupOf E) = 4 := by
      rw [← Subgroup.index_eq_card]
      exact h4
    have : Fintype (↥E ⧸ C.subgroupOf E) := Fintype.ofFinite _
    have hcard : Fintype.card (↥E ⧸ C.subgroupOf E) = 4 := by
      rw [← Nat.card_eq_fintype_card, hR]
    let o : ↥E ⧸ C.subgroupOf E := QuotientGroup.mk 1
    obtain ⟨r₁, hr₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) o
    obtain ⟨r₂, hr₂o, hr₂r₁⟩ : ∃ r₂ : ↥E ⧸ C.subgroupOf E, r₂ ≠ o ∧ r₂ ≠ r₁ := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (↥E ⧸ C.subgroupOf E)) ⊆ {o, r₁} := by
        intro r _
        by_cases h : r = o
        · simp [h]
        · simp [hcon r h]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, hcard] at h1
      have h2 : ({o, r₁} : Finset (↥E ⧸ C.subgroupOf E)).card ≤ 2 := by
        calc ({o, r₁} : Finset (↥E ⧸ C.subgroupOf E)).card
            ≤ ({r₁} : Finset (↥E ⧸ C.subgroupOf E)).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by rw [Finset.card_singleton]
      omega
    obtain ⟨⟨a, haE⟩, rfl⟩ := QuotientGroup.mk_surjective r₁
    obtain ⟨⟨b, hbE⟩, rfl⟩ := QuotientGroup.mk_surjective r₂
    have hmk : ∀ {u v : ↥E}, (QuotientGroup.mk u : ↥E ⧸ C.subgroupOf E) = QuotientGroup.mk v ↔
        ((u : G)⁻¹ * (v : G)) ∈ C := by
      intro u v
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp
    have haC : a ∉ C := by
      intro h
      apply hr₁
      exact hmk.mpr (by simpa using C.inv_mem h)
    have hbC : b ∉ C := by
      intro h
      apply hr₂o
      exact hmk.mpr (by simpa using C.inv_mem h)
    refine ⟨a, haE, haC, b, hbE, hbC, fun hab => hr₂r₁ (hmk.mpr ?_)⟩
    change b⁻¹ * a ∈ C
    have h2 : b⁻¹ * a = ((a * a)⁻¹ * (a * b))⁻¹ := by group
    rw [h2]
    exact C.inv_mem (C.mul_mem (C.inv_mem (hE2 a haE)) hab)
  let C' : Subgroup ↥N := C.subgroupOf N
  have hC'n : C'.Normal := ⟨fun c hc n => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using hnorm n n.2 c hc⟩
  have hQ : Nat.card (↥N ⧸ C') = 20 := by
    rw [← Subgroup.index_eq_card]
    exact h20
  obtain ⟨q, hq5, hqn⟩ :=
    CFSG.LocalAnalysis.EvenBN.Tits.S56.exists_orderOf_five_normal (P := ↥N ⧸ C') (Or.inl hQ)
  have hmk1 : ∀ u : ↥N, (QuotientGroup.mk u : ↥N ⧸ C') = 1 ↔ (u : G) ∈ C := by
    intro u
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hpm : ∀ u : ↥N, (u : G) * u ∈ C →
      (QuotientGroup.mk u : ↥N ⧸ C') * q * (QuotientGroup.mk u)⁻¹ = q ∨
        (QuotientGroup.mk u : ↥N ⧸ C') * q * (QuotientGroup.mk u)⁻¹ = q⁻¹ := by
    intro u hu
    set ū : ↥N ⧸ C' := QuotientGroup.mk u
    have hū2 : ū * ū = 1 := by
      rw [← QuotientGroup.mk_mul, hmk1]
      exact hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hqn ū)
    have hconjpow : ∀ j : ℤ, ū * q ^ j * ū⁻¹ = (ū * q * ū⁻¹) ^ j := fun j => by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    have hkk : q ^ (k * k) = q := by
      have h1 : ū * (ū * q * ū⁻¹) * ū⁻¹ = q := by
        calc ū * (ū * q * ū⁻¹) * ū⁻¹ = (ū * ū) * q * (ū * ū)⁻¹ := by group
          _ = q := by rw [hū2]; group
      rw [← hk, hconjpow, ← hk, ← zpow_mul] at h1
      exact h1
    have hdvd : (5 : ℤ) ∣ k * k - 1 := by
      have h1 : q ^ (k * k - 1) = 1 := by
        rw [zpow_sub, zpow_one, hkk, mul_inv_cancel]
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hq5] at this
      exact_mod_cast this
    have hk5 : (k : ZMod 5) = 1 ∨ (k : ZMod 5) = -1 := by
      have h0 : ((k * k - 1 : ℤ) : ZMod 5) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hdvd
      push_cast at h0
      generalize (k : ZMod 5) = r at h0 ⊢
      revert r
      decide
    rcases hk5 with h1 | h1
    · left
      rw [← hk]
      have : (5 : ℤ) ∣ k - 1 := by
        have h0 : ((k - 1 : ℤ) : ZMod 5) = 0 := by
          rw [Int.cast_sub, Int.cast_one, h1]
          decide
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 5).mp h0
        simpa using this
      obtain ⟨m, hm⟩ := this
      calc q ^ k = q ^ (k - 1) * q := by rw [zpow_sub_one, inv_mul_cancel_right]
        _ = q := by
          rw [hm, zpow_mul]
          have h5 : q ^ (5 : ℕ) = 1 := hq5 ▸ pow_orderOf_eq_one q
          have : q ^ (5 : ℤ) = 1 := by exact_mod_cast h5
          rw [this, one_zpow, one_mul]
    · right
      rw [← hk]
      have : (5 : ℤ) ∣ k + 1 := by
        have h0 : ((k + 1 : ℤ) : ZMod 5) = 0 := by
          rw [Int.cast_add, Int.cast_one, h1]
          decide
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k + 1) 5).mp h0
        simpa using this
      obtain ⟨m, hm⟩ := this
      calc q ^ k = q ^ (k + 1) * q⁻¹ := by rw [zpow_add_one, mul_inv_cancel_right]
        _ = q⁻¹ := by
          rw [hm, zpow_mul]
          have h5 : q ^ (5 : ℕ) = 1 := hq5 ▸ pow_orderOf_eq_one q
          have : q ^ (5 : ℤ) = 1 := by exact_mod_cast h5
          rw [this, one_zpow, one_mul]
  obtain ⟨e, heE, heC, heq⟩ : ∃ e, ∃ heE : e ∈ E, e ∉ C ∧
      (QuotientGroup.mk ⟨e, hEN heE⟩ : ↥N ⧸ C') * q * (QuotientGroup.mk ⟨e, hEN heE⟩)⁻¹ = q := by
    rcases hpm ⟨e₁, hEN he₁E⟩ (hE2 e₁ he₁E) with h1 | h1
    · exact ⟨e₁, he₁E, he₁C, h1⟩
    rcases hpm ⟨e₂, hEN he₂E⟩ (hE2 e₂ he₂E) with h2 | h2
    · exact ⟨e₂, he₂E, he₂C, h2⟩
    refine ⟨e₁ * e₂, E.mul_mem he₁E he₂E, he₁₂C, ?_⟩
    have hmul : (QuotientGroup.mk ⟨e₁ * e₂, hEN (E.mul_mem he₁E he₂E)⟩ : ↥N ⧸ C') =
        QuotientGroup.mk ⟨e₁, hEN he₁E⟩ * QuotientGroup.mk ⟨e₂, hEN he₂E⟩ := rfl
    rw [hmul]
    calc QuotientGroup.mk ⟨e₁, hEN he₁E⟩ * QuotientGroup.mk ⟨e₂, hEN he₂E⟩ * q *
          (QuotientGroup.mk ⟨e₁, hEN he₁E⟩ * QuotientGroup.mk ⟨e₂, hEN he₂E⟩ : ↥N ⧸ C')⁻¹
        = QuotientGroup.mk ⟨e₁, hEN he₁E⟩ *
            ((QuotientGroup.mk ⟨e₂, hEN he₂E⟩ : ↥N ⧸ C') * q *
              (QuotientGroup.mk ⟨e₂, hEN he₂E⟩)⁻¹) * (QuotientGroup.mk ⟨e₁, hEN he₁E⟩)⁻¹ := by
          group
      _ = ((QuotientGroup.mk ⟨e₁, hEN he₁E⟩ : ↥N ⧸ C') * q *
            (QuotientGroup.mk ⟨e₁, hEN he₁E⟩)⁻¹)⁻¹ := by rw [h2]; group
      _ = q := by rw [h1, inv_inv]
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hg₀ : orderOf g₀ ≠ 0 := (orderOf_pos g₀).ne'
  obtain ⟨a, m, hm5, hgm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg₀ 5 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgm
    exact hg₀ hgm
  let y₀ : ↥N := g₀ ^ m
  have hy₀ord : orderOf y₀ = 5 ^ a := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hgm]; exact Dvd.intro_left _ rfl), hgm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hqm : (QuotientGroup.mk g₀ : ↥N ⧸ C') ^ m ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hq5] at this
    exact hm5 this
  refine ⟨(y₀ : G), y₀.2, ?_, ?_, e, heE, heC, ?_⟩
  · refine IsPGroup.of_card (n := a) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy₀ord]
  · intro hy
    apply hqm
    rw [← QuotientGroup.mk_pow]
    exact (hmk1 y₀).mpr hy
  ·
    have hcomm : (QuotientGroup.mk ⟨e, hEN heE⟩ : ↥N ⧸ C') * (QuotientGroup.mk g₀) ^ m *
        (QuotientGroup.mk ⟨e, hEN heE⟩)⁻¹ = (QuotientGroup.mk g₀) ^ m := by
      rw [← conj_pow, heq]
    have h1 : (QuotientGroup.mk (⟨e, hEN heE⟩ * y₀ * ⟨e, hEN heE⟩⁻¹ * y₀⁻¹) : ↥N ⧸ C') = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, y₀, QuotientGroup.mk_pow]
      rw [hcomm, mul_inv_cancel]
    exact (hmk1 _).mp h1

theorem false_of_conj_of_isElemAbelian
    {L X K A : Subgroup G} {x : G}
    (hXS : IsSylowOf 2 X (L ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G)))
    (_hKX : K ≤ X)
    (hNXK : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : IsElemAbelian 2 K) (hxK : x ∈ K)
    (hAK : A ≤ K) (hzA : z ∈ A) (hxA : x ∉ A) (hA : 2 < Nat.card A)
    (hfus : ∀ k ∈ K, IsConj z k → k = z ∨ x⁻¹ * k ∈ A)
    (_hdvd : 2 ∣ (L ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (L ⊓ H z))
    (hcase2 : (∃ a ∈ A, ¬ IsConj z (x * a)) →
      Nat.card K = 2 ^ 5 ∧
      (L ⊓ Subgroup.centralizer (K : Set G)).relIndex (L ⊓ Subgroup.normalizer (K : Set G)) = 20 ∧
      ∃ E : Subgroup G, L ⊓ Subgroup.centralizer (K : Set G) ≤ E ∧
        E ≤ L ⊓ Subgroup.normalizer (K : Set G) ∧
        (L ⊓ Subgroup.centralizer (K : Set G)).relIndex E = 4 ∧
        ∀ e ∈ E, e * e ∈ Subgroup.centralizer (K : Set G))
    (hconj : ∃ c ∈ L, c * z * c⁻¹ = x) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hc1 : ∀ a ∈ A, IsConj z (x * a)
  ·
    have hS : ∀ k ∈ K, IsConj z k ↔ (k = z ∨ x⁻¹ * k ∈ A) := by
      intro k hk
      refine ⟨hfus k hk, ?_⟩
      rintro (rfl | hkA)
      · exact IsConj.refl _
      · have h := hc1 _ hkA
        rwa [mul_inv_cancel_left] at h
    have hNz := conj_eq_of_mem_normalizer_of_fusion hK hxK hAK hzA hxA hA hS
    have hX' : IsSylowOf 2 X (H z ⊓ (L ⊓ Subgroup.centralizer ({x} : Set G))) := by
      have heq : L ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G) =
          H z ⊓ (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
        rw [inf_comm L (H z), inf_assoc]
      rw [← heq]
      exact hXS
    have hXM : IsSylowOf 2 X (L ⊓ Subgroup.centralizer ({x} : Set G)) :=
      isSylowOf_of_forall_pElement_normalizer_le hX' fun g _ hgN _ => by
        have hg := hNz g (hNXK hgN)
        rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [hg]
    obtain ⟨c, hcL, hcz⟩ := hconj
    have hXH : X ≤ H z := hXS.le.trans (inf_le_left.trans inf_le_right)
    have hXL : X ≤ L := hXS.le.trans (inf_le_left.trans inf_le_left)
    let Xc : Subgroup G := X.map (MulAut.conj c).toMonoidHom
    have hmemXc : ∀ w : G, c * w * c⁻¹ ∈ Xc ↔ w ∈ X := by
      intro w
      constructor
      · intro hw
        obtain ⟨w', hw', hw'eq⟩ := Subgroup.mem_map.mp hw
        have h1 : c * w' * c⁻¹ = c * w * c⁻¹ := by simpa [MulAut.conj_apply] using hw'eq
        have h2 : w' = w := mul_left_cancel (mul_right_cancel h1)
        exact h2 ▸ hw'
      · intro hw
        exact Subgroup.mem_map.mpr ⟨w, hw, by simp [MulAut.conj_apply]⟩
    have hXcM : Xc ≤ L ⊓ Subgroup.centralizer ({x} : Set G) := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hcL (hXL hw)) (L.inv_mem hcL), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hwz : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp (hXH hw)
      rw [← hcz]
      calc c * w * c⁻¹ * (c * z * c⁻¹) = c * (w * z) * c⁻¹ := by group
        _ = c * (z * w) * c⁻¹ := by rw [hwz]
        _ = c * z * c⁻¹ * (c * w * c⁻¹) := by group
    have hXc : IsSylowOf 2 Xc (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
      apply isSylowOf_of_card hXcM
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact hXM.card_eq
    obtain ⟨d, hdM, hd⟩ := hXM.exists_mem_conj hXc
    have hdx : d * x = x * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdM).2
    have hnN : d⁻¹ * c ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have heq : d⁻¹ * c * w * (d⁻¹ * c)⁻¹ = d⁻¹ * (c * w * c⁻¹) * d := by group
      rw [heq, ← hd, hmemXc]
    have hnz : d⁻¹ * c * z * (d⁻¹ * c)⁻¹ = x := by
      calc d⁻¹ * c * z * (d⁻¹ * c)⁻¹ = d⁻¹ * (c * z * c⁻¹) * d := by group
        _ = d⁻¹ * (x * d) := by rw [hcz, mul_assoc]
        _ = x := by rw [← hdx]; group
    have h := hNz _ (hNXK hnN)
    rw [hnz] at h
    exact hxA (h ▸ hzA)
  ·
    push Not at hc1
    obtain ⟨hK32, h20, E, -, hEN, h4, hE2⟩ := hcase2 hc1
    have hnorm : ∀ n ∈ L ⊓ Subgroup.normalizer (K : Set G),
        ∀ c ∈ L ⊓ Subgroup.centralizer (K : Set G),
          n * c * n⁻¹ ∈ L ⊓ Subgroup.centralizer (K : Set G) := by
      intro n hn c hc
      obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.mp hn
      obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hnL hcL) (L.inv_mem hnL), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : n⁻¹ * k * n ∈ K := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) k).mp hk
        simpa using h
      have hck : (n⁻¹ * k * n) * c = c * (n⁻¹ * k * n) := Subgroup.mem_centralizer_iff.mp hcC _ hk'
      calc k * (n * c * n⁻¹) = n * ((n⁻¹ * k * n) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * k * n)) * n⁻¹ := by rw [hck]
        _ = n * c * n⁻¹ * k := by group
    have hE2' : ∀ e ∈ E, e * e ∈ L ⊓ Subgroup.centralizer (K : Set G) := fun e he =>
      Subgroup.mem_inf.mpr ⟨L.mul_mem (Subgroup.mem_inf.mp (hEN he)).1
        (Subgroup.mem_inf.mp (hEN he)).1, hE2 e he⟩
    obtain ⟨y, hyN, hy5, hyC, e, heE, heC, hcomm⟩ :=
      exists_five_element_commute_mod hnorm h20 hEN h4 hE2'
    obtain ⟨hyL, hyNK⟩ := Subgroup.mem_inf.mp hyN
    obtain ⟨heL, heNK⟩ := Subgroup.mem_inf.mp (hEN heE)
    exact false_of_commute_on_elemAbelian_thirtyTwo hK hK32 hy5 hyNK heNK
      (fun h => hyC (Subgroup.mem_inf.mpr ⟨hyL, h⟩))
      (fun h => heC (Subgroup.mem_inf.mpr ⟨heL, h⟩)) (hE2 e heE)
      (Subgroup.mem_inf.mp hcomm).2

end CFSG.RankThree.GF2n.Parrott
