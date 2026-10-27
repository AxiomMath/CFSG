module

public import CFSG.RankThree.Co2.Lemma210Cert
public import CFSG.RankThree.Co2.Dist
public import CFSG.RankThree.Co2.Fusion2

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem exists_omega_five :
    ∃ l : List Cr, l.length = 5 ∧ (∀ t ∈ l, t ∈ subW jWords ∧ InOmega t) ∧ l.prod = 1 := by
  obtain ⟨t₁, h₁, t₂, h₂, t₃, h₃, t₄, h₄, t₅, h₅, a₁, a₂, a₃, a₄, a₅, hp⟩ :=
    jHypFacts_cert.five
  rw [← map_subW_eq jWords_lt42] at h₁ h₂ h₃ h₄ h₅
  obtain ⟨y₁, (hy₁ : y₁ ∈ subW jWords), rfl⟩ := h₁
  obtain ⟨y₂, (hy₂ : y₂ ∈ subW jWords), rfl⟩ := h₂
  obtain ⟨y₃, (hy₃ : y₃ ∈ subW jWords), rfl⟩ := h₃
  obtain ⟨y₄, (hy₄ : y₄ ∈ subW jWords), rfl⟩ := h₄
  obtain ⟨y₅, (hy₅ : y₅ ∈ subW jWords), rfl⟩ := h₅
  have b₁ := (inOmega_iff_clsA y₁).2 a₁
  have b₂ := (inOmega_iff_clsA y₂).2 a₂
  have b₃ := (inOmega_iff_clsA y₃).2 a₃
  have b₄ := (inOmega_iff_clsA y₄).2 a₄
  have b₅ := (inOmega_iff_clsA y₅).2 a₅
  refine ⟨[y₁, y₂, y₃, y₄, y₅], rfl, by simp [hy₁, hy₂, hy₃, hy₄, hy₅, b₁, b₂, b₃, b₄, b₅], ?_⟩
  apply crMat_injective
  rw [map_one, ← hp]
  simp [map_mul, mul_assoc]

theorem exists_four_three :
    ∃ l : List Cr, l.length = 3 ∧ (∀ t ∈ l, t ∈ subW jWords ∧ IsConj (rep 4) t) ∧
      (l.prod = 1 ∨ l.prod = rCr) := by
  obtain ⟨u₁, h₁, u₂, h₂, u₃, h₃, a₁, a₂, a₃, hp⟩ := jHypFacts_cert.three
  rw [← map_subW_eq jWords_lt42] at h₁ h₂ h₃
  obtain ⟨y₁, (hy₁ : y₁ ∈ subW jWords), rfl⟩ := h₁
  obtain ⟨y₂, (hy₂ : y₂ ∈ subW jWords), rfl⟩ := h₂
  obtain ⟨y₃, (hy₃ : y₃ ∈ subW jWords), rfl⟩ := h₃
  have b₁ := (isConj_iff_crConj (c := 4) (y := y₁) (by norm_num)).2 a₁
  have b₂ := (isConj_iff_crConj (c := 4) (y := y₂) (by norm_num)).2 a₂
  have b₃ := (isConj_iff_crConj (c := 4) (y := y₃) (by norm_num)).2 a₃
  refine ⟨[y₁, y₂, y₃], rfl, fun t ht => ?_, ?_⟩
  · rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨hy₁, b₁⟩
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨hy₂, b₂⟩
    rcases List.mem_singleton.1 ht with rfl
    exact ⟨hy₃, b₃⟩
  rcases hp with hp | hp
  · left
    apply crMat_injective
    rw [map_one, ← hp]
    simp [map_mul, mul_assoc]
  · right
    apply crMat_injective
    rw [crMat_rCr, ← hp]
    simp [map_mul, mul_assoc]

theorem prod_mem_iff {K : Type*} [Group K] {A T : Subgroup K}
    (hTA : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ T ↔ (a ∈ T ↔ b ∈ T)) :
    ∀ l : List K, (∀ x ∈ l, x ∈ A ∧ x ∉ T) → (l.prod ∈ T ↔ Even l.length)
  | [], _ => by simp [T.one_mem]
  | x :: l, hl => by
    have hx := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, y ∈ A ∧ y ∉ T := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, hTA x hx.1 _ (A.list_prod_mem fun y hy => (hl' y hy).1),
      prod_mem_iff hTA l hl', List.length_cons, Nat.even_add_one]
    have := hx.2
    tauto

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem prod_map_φ_symm (l : List Cr) :
    (l.map fun y => ((h.φ.symm y : h.H) : G)).prod = ((h.φ.symm l.prod : h.H) : G) :=
  (map_list_prod (h.H.subtype.comp h.φ.symm.toMonoidHom) l).symm

theorem mul_mem_iff_of_half {S : Subgroup G} (hS : S ≤ h.JG) (hcard : Nat.card S = 2 ^ 9)
    {a b : G} (ha : a ∈ h.JG) (hb : b ∈ h.JG) : a * b ∈ S ↔ (a ∈ S ↔ b ∈ S) := by
  have hidx : (S.subgroupOf h.JG).index = 2 := by
    have h1 := (S.subgroupOf h.JG).card_mul_index
    rw [card_subgroupOf_eq hS, hcard, h.card_JG] at h1
    norm_num at h1
    omega
  have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this

theorem exists_mem_Ω_of_half {S : Subgroup G} (hS : S ≤ h.JG) (hcard : Nat.card S = 2 ^ 9) :
    ∃ ω ∈ S, ω ∈ h.Ω := by
  by_contra hno
  push Not at hno
  obtain ⟨l, hlen, hl, hprod⟩ := exists_omega_five
  have hnot : ∀ x ∈ l.map fun y => ((h.φ.symm y : h.H) : G), x ∈ h.JG ∧ x ∉ S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨h.φ_symm_mem_JG (hl y hy).1,
      fun hS => hno _ hS ((h.mem_Ω_iff (hl y hy).1).2 (hl y hy).2)⟩
  have key := prod_mem_iff (fun a ha b hb => h.mul_mem_iff_of_half hS hcard ha hb) _ hnot
  rw [h.prod_map_φ_symm, hprod, map_one, List.length_map, hlen] at key
  exact absurd (key.1 S.one_mem) (by decide)

theorem exists_four_of_half {S : Subgroup G} (hS : S ≤ h.JG) (hcard : Nat.card S = 2 ^ 9)
    (hzS : h.z ∈ S) :
    ∃ y ∈ subW jWords, ((h.φ.symm y : h.H) : G) ∈ S ∧ IsConj (rep 4) y := by
  by_contra hno
  push Not at hno
  obtain ⟨l, hlen, hl, hprod⟩ := exists_four_three
  have hnot : ∀ x ∈ l.map fun y => ((h.φ.symm y : h.H) : G), x ∈ h.JG ∧ x ∉ S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨h.φ_symm_mem_JG (hl y hy).1, fun hmem => hno y (hl y hy).1 hmem (hl y hy).2⟩
  have key := prod_mem_iff (fun a ha b hb => h.mul_mem_iff_of_half hS hcard ha hb) _ hnot
  have hmem : (l.map fun y => ((h.φ.symm y : h.H) : G)).prod ∈ S := by
    rw [h.prod_map_φ_symm]
    rcases hprod with hp | hp
    · rw [hp, map_one]
      exact S.one_mem
    · rw [hp, h.φ_symm_rCr]
      exact hzS
  rw [List.length_map, hlen] at key
  exact absurd (key.1 hmem) (by decide)

theorem card_inf_centralizer (x : Cr) :
    Nat.card ↥(Subgroup.centralizer {h.z} ⊓
      Subgroup.centralizer {((h.φ.symm x : h.H) : G)}) =
      Nat.card (Subgroup.centralizer ({x} : Set Cr)) := by
  rw [h.inf_centralizer x, card_liftG]

theorem card_centralizer_of_isConj {x y : Cr} (hxy : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set Cr)) =
      Nat.card (Subgroup.centralizer ({y} : Set Cr)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  exact Nat.card_congr (centralizerConjEquiv c x).toEquiv

theorem eq_bot_of_odd_normalized {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hJY : h.JG ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ := by
  haveI := h.finite
  have hel : CFSG.Open.IsElemAbelian 2 h.JG :=
    ⟨⟨⟨fun a b => Subtype.ext (h.elemTwo_JG.2 _ a.2 _ b.2)⟩⟩,
      fun x hx => by rw [sq]; exact h.elemTwo_JG.1 x hx⟩
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 9
    Nat.prime_two h.JG Y hel (by rw [h.card_JG]; norm_num) hJY (Nat.coprime_two_left.2 hY)
  rw [← hgen, iSup₂_eq_bot]
  rintro S ⟨hSJ, hScard⟩
  obtain ⟨ω, hωS, hωΩ⟩ := h.exists_mem_Ω_of_half hSJ hScard
  obtain ⟨n, hn, hnω⟩ := exists_normalizer_conj_of_class h.elemTwo_JG h.one_class hωΩ.1 hωΩ.2
  have hnJ : ∀ x ∈ h.JG, n⁻¹ * x * n ∈ h.JG := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x).1 hx
    simpa using this
  set S' : Subgroup G := S.map (MulAut.conj n⁻¹).toMonoidHom
  have hS'J : S' ≤ h.JG := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hnJ x (hSJ hx)
  have hS'card : Nat.card S' = 2 ^ 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hScard]
  have hzS' : h.z ∈ S' := ⟨ω, hωS, by simp [← hnω, mul_assoc]⟩
  obtain ⟨y, -, hjS', hj4⟩ := h.exists_four_of_half hS'J hS'card hzS'
  set K : Subgroup G := Y ⊓ Subgroup.centralizer (S : Set G)
  set K' : Subgroup G := K.map (MulAut.conj n⁻¹).toMonoidHom
  have hK'le : K' ≤ Subgroup.centralizer {h.z} ⊓
      Subgroup.centralizer {((h.φ.symm y : h.H) : G)} := by
    rintro _ ⟨k, hk, rfl⟩
    have hkC := (Subgroup.mem_inf.1 hk).2
    have hc : ∀ s ∈ S',
        (MulAut.conj n⁻¹).toMonoidHom k * s = s * (MulAut.conj n⁻¹).toMonoidHom k := by
      rintro _ ⟨s, hs, rfl⟩
      have hks : s * k = k * s := Subgroup.mem_centralizer_iff.1 hkC s hs
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc n⁻¹ * k * n * (n⁻¹ * s * n) = n⁻¹ * (k * s) * n := by group
        _ = n⁻¹ * (s * k) * n := by rw [hks]
        _ = n⁻¹ * s * n * (n⁻¹ * k * n) := by group
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact hc _ hzS'
    · exact hc _ hjS'
  have hcard2 : Nat.card ↥(Subgroup.centralizer {h.z} ⊓
      Subgroup.centralizer {((h.φ.symm y : h.H) : G)}) =
      32768 := by
    rw [h.card_inf_centralizer, ← card_centralizer_of_isConj hj4,
      card_C 4 (by norm_num) (m := 32768) (by decide) (classSizes_pos (by norm_num))]
  have hdvd2 : Nat.card K' ∣ 2 ^ 15 := by
    rw [show (2 : ℕ) ^ 15 = 32768 by norm_num, ← hcard2]
    exact Subgroup.card_dvd_of_le hK'le
  have hoddK' : Odd (Nat.card K') := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
    exact Odd.of_dvd_nat hY (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : Nat.card K' = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 15 (Nat.coprime_two_right.2 hoddK'))
      hdvd2
  rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective] at h1
  exact Subgroup.card_eq_one.1 h1

end Co2CentHyp

end CFSG.RankThree.Co2
