module

public import CFSG.Quasithin.H13.NQCoreP134Group
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.QuasithinUnique

section Config

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem OddConfig.isSylowTwoOf_inf [Finite A] (h : OddConfig p L P T) :
    IsSylowTwoOf (T ⊓ L) L := by
  have := h.normal
  exact CFSG.Quasithin.A4.isSylowTwoOf_inf_normal h.sylow le_top
    (by rw [Subgroup.normalizer_eq_top])

theorem OddConfig.mul_inf (h : OddConfig p L P T) :
    ∀ t ∈ T ⊓ L, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T ⊓ L, t * x = y * s := by
  intro t ht x hx
  obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht.1 x hx
  refine ⟨y, hy, s, ⟨hs, ?_⟩, he⟩
  have hs' : s = y⁻¹ * (t * x) := by rw [he]; group
  rw [hs']
  exact L.mul_mem (L.inv_mem (h.le hy)) (L.mul_mem ht.2 (h.le hx))

theorem OddConfig.card_sup_inf [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h : OddConfig p L P T) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = Nat.card P * Nat.card (T ⊓ L : Subgroup A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (h.sylow.2.1.to_le (inf_le_left : T ⊓ L ≤ T))
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (T ⊓ L : Subgroup A)) := by
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr (by omega)
    rw [hk]
    rcases h.card with h1 | h1 <;> rw [h1]
    · exact Nat.Coprime.pow _ _ h2
    · exact Nat.Coprime.pow _ _ h2
  exact card_sup_eq_of_mul' hcop h.mul_inf

theorem OddConfig.sup_inf_le (h : OddConfig p L P T) : P ⊔ (T ⊓ L) ≤ L :=
  sup_le h.le inf_le_right

end Config

theorem card_map_of_injOn {G G' : Type*} [Group G] [Group G'] (f : G →* G') (K : Subgroup G)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x = y) : Nat.card (K.map f) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : K.map f))
    ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)), ?_⟩)).symm
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem OddConfig.exists_model [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h : OddConfig p L P T)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) :
    ∃ a : ℕ, (a = 2 ∨ a = 3) ∧ ∃ H S : Subgroup (↥L ⧸ Subgroup.center ↥L),
      IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ S ≤ H ∧ Nat.card H = p ^ a * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.isSylowTwoOf_inf
  obtain ⟨a, ha, hPa⟩ : ∃ a, (a = 2 ∨ a = 3) ∧ Nat.card P = p ^ a := by
    rcases h.card with h2 | h3
    · exact ⟨2, Or.inl rfl, h2⟩
    · exact ⟨3, Or.inr rfl, h3⟩
  refine ⟨a, ha, ?_⟩
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  let π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  set S₁ : Subgroup ↥L := (T ⊓ L).subgroupOf L with hS₁def
  set H₁ : Subgroup ↥L := (P ⊔ (T ⊓ L)).subgroupOf L with hH₁def
  have hS₁H₁ : S₁ ≤ H₁ := Subgroup.subgroupOf_mono L le_sup_right
  have hS₁p : IsPGroup 2 S₁ :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS₁p
  have hcardS₁ : Nat.card S₁ = Nat.card (T ⊓ L : Subgroup A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have hcardH₁ : Nat.card H₁ = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sup_inf_le).toEquiv
  have hH₁ : Nat.card H₁ = p ^ a * Nat.card S₁ := by
    rw [hcardH₁, hcardS₁, h.card_sup_inf hp5, hPa]
  have hcop : Nat.Coprime 3 (Nat.card H₁) := by
    have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega)
    rw [hH₁, hk]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a h3p)
      (Nat.Coprime.pow_right k (by norm_num))
  have hinj : ∀ x ∈ H₁, ∀ y ∈ H₁, π x = π y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
    have hzH : x⁻¹ * y ∈ H₁ := H₁.mul_mem (H₁.inv_mem hx) hy
    have hd3 : orderOf (x⁻¹ * y) ∣ 3 := by
      have h1 : orderOf (x⁻¹ * y) ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hz
      rcases hZ with hZ1 | hZ3
      · rw [hZ1] at h1; exact h1.trans (one_dvd _)
      · rwa [hZ3] at h1
    have hdH : orderOf (x⁻¹ * y) ∣ Nat.card H₁ := Subgroup.orderOf_dvd_natCard H₁ hzH
    have h1 : orderOf (x⁻¹ * y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd3 hdH
    have h2 : x⁻¹ * y = 1 := orderOf_eq_one_iff.mp h1
    exact inv_mul_eq_one.mp h2
  have hinjS : ∀ x ∈ S₁, ∀ y ∈ S₁, π x = π y → x = y :=
    fun x hx y hy => hinj x (hS₁H₁ hx) y (hS₁H₁ hy)
  have hcardŜ : Nat.card (S₁.map π) = Nat.card S₁ := card_map_of_injOn π S₁ hinjS
  have hcardĤ : Nat.card (H₁.map π) = Nat.card H₁ := card_map_of_injOn π H₁ hinj
  refine ⟨H₁.map π, S₁.map π, hS₁p.map π, ?_, Subgroup.map_mono hS₁H₁, ?_⟩
  ·
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have h1 := S₁.card_mul_index
    have h2 := (S₁.map π).card_mul_index
    have hpos : 0 < Nat.card S₁ := Nat.card_pos
    have h3 : S₁.index = (S₁.map π).index * Nat.card Z := by
      rw [hcardŜ] at h2
      have : Nat.card S₁ * S₁.index = Nat.card S₁ * ((S₁.map π).index * Nat.card Z) := by
        rw [h1, hq, ← h2]
        ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    exact fun h2 => hS.2.2 ((Dvd.dvd.trans h2 (Dvd.intro _ h3.symm)))
  · rw [hcardĤ, hcardŜ, hH₁]

theorem noOddConfigSpor_of_noPowerOvergroup {s : TauCeti.SporadicName}
    (h : NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) : NoOddConfigSpor s := by
  intro A _ _ p hp L P T hp5 hcfg hZ e
  obtain ⟨a, ha, H, S, hS2, hSi, hSH, hH⟩ := hcfg.exists_model hp5 hZ
  exact h (↥L ⧸ Subgroup.center ↥L) e p a hp.out hp5 ha H S hS2 hSi hSH hH

end CFSG.Quasithin.H13.NQCore
