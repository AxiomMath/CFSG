module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Basic
public import CFSG.GroupTheory.OddCoreCentralizerDecomposition
public import CFSG.GroupTheory.BurnsideNormalComplement

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.mem_oddCore_of_isolated (h : FS79Hyp b t b₁ b₂ J)
    (hiso : ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    b ∈ CFSG.oddCore H := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    have := h.ord_t
    simp at this
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    rw [← h.ord_t]
    exact pow_orderOf_eq_one t
  have hdec := CFSG.eq_oddCore_mul_centralizer_of_isolated ht1 ht2 hiso
  have hbmem : b ∈ (⊤ : Set H) := Set.mem_univ b
  rw [hdec] at hbmem
  obtain ⟨o, ho, c, hc, hbc⟩ := Set.mem_mul.mp hbmem
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hOn : (CFSG.oddCore H).Normal := CFSG.oddCore_normal H
  set o' : H := t * o * t⁻¹ with ho'
  have ho'O : o' ∈ CFSG.oddCore H := hOn.conj_mem o ho t
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hct' : c * t⁻¹ = t⁻¹ * c := by
    calc c * t⁻¹ = t⁻¹ * (t * c) * t⁻¹ := by group
      _ = t⁻¹ * (c * t) * t⁻¹ := by rw [← hct]
      _ = t⁻¹ * c := by group
  have h1 : b⁻¹ = o' * c := by
    rw [← h.inv_b, ← hbc, ho']
    calc t * (o * c) * t⁻¹ = t * o * (c * t⁻¹) := by group
      _ = t * o * (t⁻¹ * c) := by rw [hct']
      _ = t * o * t⁻¹ * c := by group
  have h2 : b⁻¹ * b⁻¹ = o' * o⁻¹ := by
    have hc' : c = o⁻¹ * b := by rw [← hbc]; group
    calc b⁻¹ * b⁻¹ = (o' * c) * b⁻¹ := by rw [← h1]
      _ = o' * (o⁻¹ * b) * b⁻¹ := by rw [hc']
      _ = o' * o⁻¹ := by group
  have h3 : b⁻¹ ∈ CFSG.oddCore H := by
    have hmem : o' * o⁻¹ ∈ CFSG.oddCore H :=
      (CFSG.oddCore H).mul_mem ho'O ((CFSG.oddCore H).inv_mem ho)
    have e : b⁻¹ = (b⁻¹ * b⁻¹) * (b⁻¹ * b⁻¹) := by
      calc b⁻¹ = b⁻¹ * (b ^ 3)⁻¹ := by rw [hb3]; group
        _ = (b⁻¹ * b⁻¹) * (b⁻¹ * b⁻¹) := by
          have : (b ^ 3)⁻¹ = b⁻¹ * b⁻¹ * b⁻¹ := by group
          rw [this]; group
    rw [e, h2]
    exact (CFSG.oddCore H).mul_mem hmem hmem
  simpa using (CFSG.oddCore H).inv_mem h3

theorem FS79Hyp.eq_oddCore_mul_nor (h : FS79Hyp b t b₁ b₂ J) (hb : b ∈ CFSG.oddCore H) :
    ∀ g : H, ∃ o ∈ CFSG.oddCore H, ∃ n ∈ Nor (Subgroup.zpowers b), g = o * n := by
  intro g
  set O : Subgroup H := CFSG.oddCore H with hO
  have hsyl := h.isSylowOf_zpowers_oddCore hb
  have hOn : O.Normal := CFSG.oddCore_normal H
  have hconj : conjBy g (Subgroup.zpowers b) ≤ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hOn.conj_mem x ((Subgroup.zpowers_le.mpr hb) hx) g
  have hp : IsPGroup 3 (conjBy g (Subgroup.zpowers b)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [conjBy, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers,
      h.ord_b]
    simp
  obtain ⟨k, hkO, hk⟩ := L14.exists_conj_le_sylowOf hsyl hconj hp
  refine ⟨k⁻¹, O.inv_mem hkO, k * g, ?_, by group⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' : g * x * g⁻¹ ∈ conjBy g (Subgroup.zpowers b) := ⟨x, hx, rfl⟩
  have := hk _ hx'
  have e : k * g * x * (k * g)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ := by group
  rw [e]
  exact this

theorem FS79Hyp.exists_normal_three_complement (h : FS79Hyp b t b₁ b₂ J)
    (hb : b ∈ CFSG.oddCore H) :
    ∃ X : Subgroup H, X ≤ CFSG.oddCore H ∧ (∀ g : H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧
      Nat.Coprime 3 (Nat.card X) ∧
      ∀ o ∈ CFSG.oddCore H, ∃ x ∈ X, ∃ m : ℤ, o = x * b ^ m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup H := CFSG.oddCore H with hO
  have hOn : O.Normal := CFSG.oddCore_normal H
  have hOodd : Odd (Nat.card O) := odd_card_oddCore' H
  have hsyl := h.isSylowOf_zpowers_oddCore hb
  have hbO : Subgroup.zpowers b ≤ O := Subgroup.zpowers_le.mpr hb
  set A : Subgroup ↥O := (Subgroup.zpowers b).subgroupOf O with hA
  have hAp : IsPGroup 3 A := hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hbO).symm
  have hAi : ¬ 3 ∣ A.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hsyl.2.2
  let P : Sylow 3 ↥O := hAp.toSylow hAi
  have hPA : (P : Subgroup ↥O) = A := rfl
  have hNC : Subgroup.normalizer (P : Set ↥O) ≤ Subgroup.centralizer (P : Set ↥O) := by
    intro x hx
    have hxb : (x : H) * b * (x : H)⁻¹ ∈ Subgroup.zpowers b := by
      have hbP : (⟨b, hb⟩ : ↥O) ∈ (P : Set ↥O) := by
        change (⟨b, hb⟩ : ↥O) ∈ A
        exact Subgroup.mem_zpowers b
      have := (Subgroup.mem_normalizer_iff.mp hx ⟨b, hb⟩).mp hbP
      have h2 : x * ⟨b, hb⟩ * x⁻¹ ∈ A := this
      exact h2
    have hxodd : Odd (orderOf (x : H)) := by
      have h1 : orderOf (x : H) ∣ Nat.card O := by
        rw [Subgroup.orderOf_coe x]
        exact orderOf_dvd_natCard x
      exact hOodd.of_dvd_nat h1
    have hfix := conj_eq_self_of_odd_of_mem_zpowers h.ord_b hxodd hxb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (show (y : H) ∈ Subgroup.zpowers b from hy)
    apply Subtype.ext
    have hxc : (x : H) * b = b * (x : H) := by
      calc (x : H) * b = ((x : H) * b * (x : H)⁻¹) * (x : H) := by group
        _ = b * (x : H) := by rw [hfix]
    have hxcm : (x : H) * b ^ m = b ^ m * (x : H) :=
      ((Commute.zpow_right (show Commute (x : H) b from hxc) m)).eq
    change (y : H) * (x : H) = (x : H) * (y : H)
    rw [← hm, hxcm]
  obtain ⟨K, hKn, hK3, -, -, hKc, -, hsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hNC
  refine ⟨K.map O.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro g _ ⟨x, hx, rfl⟩
    refine ⟨MulAut.conjNormal g x, ?_, ?_⟩
    · have := hKc.fixed (MulAut.conjNormal g)
      have hx' : x ∈ K.comap (MulAut.conjNormal g).toMonoidHom := by rw [this]; exact hx
      exact hx'
    · simp [MulAut.conjNormal_apply]
  · rw [Subgroup.card_map_of_injective O.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3
  · intro o ho
    have hmem : (⟨o, ho⟩ : ↥O) ∈ K ⊔ (P : Subgroup ↥O) := by
      rw [hsup]
      trivial
    obtain ⟨k, hk, p, hp, hkp⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hpA : p ∈ A := by
      rw [← hPA]
      exact hp
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (show (p : H) ∈ Subgroup.zpowers b from hpA)
    refine ⟨(k : H), ⟨k, hk, rfl⟩, m, ?_⟩
    have := congrArg Subtype.val hkp
    change (k : H) * (p : H) = o at this
    rw [← this, ← hm]

theorem FS79Hyp.conclusion_of_isolated (h : FS79Hyp b t b₁ b₂ J)
    (hiso : ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    setMul (Opp 3 (⊤ : Subgroup H)) (Nor (Subgroup.zpowers b)) = Set.univ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb := h.mem_oddCore_of_isolated hiso
  obtain ⟨X, hXO, hXn, hXc, hXdec⟩ := h.exists_normal_three_complement hb
  have hXopp : X ≤ Opp 3 (⊤ : Subgroup H) :=
    L14.le_Opp_of_normalized le_top (fun g _ x hx => hXn g x hx) hXc
  ext g
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨o, ho, n, hn, hg⟩ := h.eq_oddCore_mul_nor hb g
    obtain ⟨x, hx, m, hxm⟩ := hXdec o ho
    refine ⟨x, hXopp hx, b ^ m * n, ?_, ?_⟩
    · exact (Nor (Subgroup.zpowers b)).mul_mem
        ((Nor (Subgroup.zpowers b)).zpow_mem (Subgroup.le_normalizer (Subgroup.mem_zpowers b)) m) hn
    · rw [hg, hxm, mul_assoc]

end CFSG.RankThree.PartTwo.Sec21.FF81
