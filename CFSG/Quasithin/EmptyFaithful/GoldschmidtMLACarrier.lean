module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLABender
public import CFSG.Quasithin.Background.C2Six

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

structure IsCarrier (B P : Subgroup G) : Prop where
  le : P ≤ B
  pGroup : IsPGroup 2 ↥P
  norm : B ≤ Subgroup.normalizer (P : Set G)
  hall : ∀ x ∈ B, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ P
  cent : ∀ x ∈ B, (∀ p ∈ P, x * p = p * x) → x ∈ P

theorem mem_normalizer_of_map_le {X : Subgroup G} {g : G}
    (h1 : X.map (MulAut.conj g).toMonoidHom ≤ X) (h2 : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 ⟨h, hh, rfl⟩, fun hh => ?_⟩
  have h3 : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) ∈ X := h2 ⟨g * h * g⁻¹, hh, rfl⟩
  have e : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) = h := by simp [mul_assoc]
  rwa [e] at h3

theorem mem_normalizer_of_commute {P : Subgroup G} {x : G} (h : ∀ p ∈ P, x * p = p * x) :
    x ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have e : ∀ q ∈ P, x * q * x⁻¹ = q := fun q hq => by rw [h q hq]; group
  refine ⟨fun hp => by rw [e p hp]; exact hp, fun hp => ?_⟩
  have h1 := e _ hp
  have h3 : x * (x * p * x⁻¹) = x * p := mul_right_cancel (b := x⁻¹) (by simpa [mul_assoc] using h1)
  have h4 : x * p * x⁻¹ = p := mul_left_cancel h3
  rwa [h4] at hp

theorem le_normalizer_sup_of_commute {B₁ P₁ P₂ : Subgroup G}
    (h1 : B₁ ≤ Subgroup.normalizer (P₁ : Set G)) (hc : ∀ a ∈ B₁, ∀ b ∈ P₂, a * b = b * a) :
    B₁ ≤ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by
  intro a ha
  have key : ∀ g : G, g ∈ Subgroup.normalizer (P₁ : Set G) → (∀ b ∈ P₂, g * b = b * g) →
      (P₁ ⊔ P₂).map (MulAut.conj g).toMonoidHom ≤ P₁ ⊔ P₂ := by
    intro g hg hgc
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
      simpa using this
    · rintro _ ⟨x, hx, rfl⟩
      have : g * x * g⁻¹ = x := by rw [hgc x hx]; group
      simpa [this] using hx
  have hainv : a⁻¹ ∈ B₁ := B₁.inv_mem ha
  exact mem_normalizer_of_map_le (key a (h1 ha) (hc a ha)) (key a⁻¹ (h1 hainv) (hc a⁻¹ hainv))

section Finite

variable [Finite G]

theorem IsCarrier.pCoreOf_eq {B P : Subgroup G} (h : IsCarrier B P) : pCoreOf 2 B = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    have hxB : x ∈ B := pCoreOf_le 2 B hx
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 B) ⟨x, hx⟩
    exact h.hall x hxB k (by simpa using congrArg Subtype.val hk)
  · exact le_pCoreOf_of_le_normalizer 2 h.le h.norm h.pGroup

theorem IsCarrier.charTwo_odd {B P : Subgroup G} (h : IsCarrier B P) :
    CharTwo B ∧ Odd (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) := by
  have hpc := h.pCoreOf_eq
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hpc]
    refine h.cent x hx.1 (fun p hp => ?_)
    have := Subgroup.mem_centralizer_iff.mp hx.2 p (by rw [hpc]; exact hp)
    exact this.symm
  · have hsyl : IsSylowTwoOf P B := by
      refine CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mpr ⟨h.le, h.pGroup, fun R hRB hR hPR => ?_⟩
      intro r hr
      obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
      exact h.hall r (hRB hr) k (by simpa using congrArg Subtype.val hk)
    have hcore : CFSG.pCore 2 ↥B = P.subgroupOf B := by
      ext y
      rw [CFSG.Quasithin.C2Six.mem_pCore_two_iff, hpc, Subgroup.mem_subgroupOf]
    show Odd (CFSG.pCore 2 ↥B).index
    rw [hcore]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hsyl.2.2)

end Finite

theorem IsCarrier.conj {B P : Subgroup G} (h : IsCarrier B P) (t : G) :
    IsCarrier (CFSG.Quasithin.conjByElt t B) (CFSG.Quasithin.conjByElt t P) := by
  have hm : ∀ {x : G} {K : Subgroup G}, x ∈ CFSG.Quasithin.conjByElt t K ↔ t⁻¹ * x * t ∈ K :=
    fun {x K} => CFSG.Quasithin.mem_conjByElt
  refine ⟨fun x hx => hm.mpr (h.le (hm.mp hx)), ?_, fun x hx => ?_, fun x hx k hk => ?_,
    fun x hx hc => ?_⟩
  · exact h.pGroup.of_equiv (Subgroup.equivMapOfInjective P (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := h.norm (hm.mp hx)
    have e : t⁻¹ * (x * y * x⁻¹) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) * (t⁻¹ * x * t)⁻¹ := by group
    rw [hm, hm, e]
    exact Subgroup.mem_normalizer_iff.mp hx' _
  · refine hm.mpr (h.hall _ (hm.mp hx) k ?_)
    have : (t⁻¹ * x * t) ^ 2 ^ k = t⁻¹ * x ^ 2 ^ k * t := by
      rw [← MulAut.conj_symm_apply, ← MulAut.conj_symm_apply]
      simp [map_pow]
    rw [this, hk]
    group
  · refine hm.mpr (h.cent _ (hm.mp hx) (fun p hp => ?_))
    have e0 : t⁻¹ * (t * p * t⁻¹) * t = p := by group
    have h1 := hc (t * p * t⁻¹) (hm.mpr (by rw [e0]; exact hp))
    have h2 : x * (t * p * t⁻¹) = (t * p * t⁻¹) * x := h1
    calc t⁻¹ * x * t * p = t⁻¹ * (x * (t * p * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * p * t⁻¹) * x) * t := by rw [h2]
      _ = p * (t⁻¹ * x * t) := by group

theorem IsCarrier.sup {B₁ B₂ P₁ P₂ : Subgroup G} (h₁ : IsCarrier B₁ P₁) (h₂ : IsCarrier B₂ P₂)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hint : B₁ ⊓ B₂ ≤ P₁) :
    IsCarrier (B₁ ⊔ B₂) (P₁ ⊔ P₂) := by
  have hN12 : B₂ ≤ Subgroup.normalizer (B₁ : Set G) := fun b hb =>
    mem_normalizer_of_commute (fun a ha => (hcomm a ha b hb).symm)
  have hP₂N₁ : P₂ ≤ Subgroup.normalizer (P₁ : Set G) := fun b hb =>
    mem_normalizer_of_commute (fun a ha => (hcomm a (h₁.le ha) b (h₂.le hb)).symm)
  refine ⟨sup_le_sup h₁.le h₂.le, ?_, ?_, ?_, ?_⟩
  · rw [sup_comm]
    exact h₂.pGroup.to_sup_of_normal_right' h₁.pGroup hP₂N₁
  · refine sup_le (le_normalizer_sup_of_commute h₁.norm
      (fun a ha b hb => hcomm a ha b (h₂.le hb))) ?_
    rw [sup_comm P₁ P₂]
    exact le_normalizer_sup_of_commute h₂.norm (fun b hb a ha => (hcomm a (h₁.le ha) b hb).symm)
  · intro x hx k hk
    have hx' : x ∈ ((B₁ ⊔ B₂ : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN12] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hab : Commute a b := hcomm a ha b hb
    have hpow : a ^ 2 ^ k * b ^ 2 ^ k = 1 := by rw [← hab.mul_pow]; exact hk
    have hae : a ^ 2 ^ k = (b ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have hbe : b ^ 2 ^ k = (a ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    have hmem : a ^ 2 ^ k ∈ B₁ ⊓ B₂ :=
      ⟨pow_mem ha _, by rw [hae]; exact B₂.inv_mem (pow_mem hb _)⟩
    have hP1 : a ^ 2 ^ k ∈ P₁ := hint hmem
    obtain ⟨j, hj⟩ := h₁.pGroup ⟨a ^ 2 ^ k, hP1⟩
    have haj : a ^ 2 ^ (k + j) = 1 := by
      have := congrArg Subtype.val hj
      simpa [pow_add, pow_mul] using this
    have ha1 : a ∈ P₁ := h₁.hall a ha (k + j) haj
    have hbP : b ^ 2 ^ k ∈ P₁ := by rw [hbe]; exact P₁.inv_mem hP1
    obtain ⟨j', hj'⟩ := h₁.pGroup ⟨b ^ 2 ^ k, hbP⟩
    have hbj : b ^ 2 ^ (k + j') = 1 := by
      have := congrArg Subtype.val hj'
      simpa [pow_add, pow_mul] using this
    exact Subgroup.mul_mem_sup ha1 (h₂.hall b hb (k + j') hbj)
  · intro x hx hc
    have hx' : x ∈ ((B₁ ⊔ B₂ : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN12] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hcP₁ : ∀ p ∈ P₁, a * p = p * a := fun p hp => by
      have h1 := hc p (Subgroup.mem_sup_left hp)
      have h2 : b * p = p * b := (hcomm p (h₁.le hp) b hb).symm
      have h3 : (a * p) * b = (p * a) * b := by
        calc (a * p) * b = a * (p * b) := by rw [mul_assoc]
          _ = a * (b * p) := by rw [h2]
          _ = (a * b) * p := by rw [mul_assoc]
          _ = p * (a * b) := h1
          _ = (p * a) * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hcP₂ : ∀ q ∈ P₂, b * q = q * b := fun q hq => by
      have h1 := hc q (Subgroup.mem_sup_right hq)
      have h2 : a * q = q * a := hcomm a ha q (h₂.le hq)
      have h3 : a * (b * q) = a * (q * b) := by
        calc a * (b * q) = (a * b) * q := by rw [mul_assoc]
          _ = q * (a * b) := h1
          _ = (q * a) * b := by rw [mul_assoc]
          _ = (a * q) * b := by rw [h2]
          _ = a * (q * b) := by rw [mul_assoc]
      exact mul_left_cancel h3
    exact Subgroup.mul_mem_sup (h₁.cent a ha hcP₁) (h₂.cent b hb hcP₂)

theorem isCarrier_borel [Finite G] {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsCarrier (L ⊓ Subgroup.normalizer (P : Set G)) P := by
  refine ⟨le_inf hP.1 Subgroup.le_normalizer, hP.2.1, inf_le_right, fun x hx k hk => ?_,
    fun x hx hc => mem_of_centralizes hP hB hx.1 hx.2 hc⟩
  have hp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hz : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le).mpr hx.2
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ P) := hp.to_sup_of_normal_right' hP.2.1 hz
  have hle : Subgroup.zpowers x ⊔ P ≤ L := sup_le ((Subgroup.zpowers_le).mpr hx.1) hP.1
  have := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hP).2.2 _ hle hsup le_sup_right
  exact this (le_sup_left (a := Subgroup.zpowers x) (b := P) (Subgroup.mem_zpowers x))

end CFSG.Quasithin.GoldMLA
