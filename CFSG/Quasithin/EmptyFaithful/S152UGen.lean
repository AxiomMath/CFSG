module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_or_eq_of_relIndex_two {S J T : Subgroup G} (hSJ : S ≤ J) (hJT : J ≤ T)
    (h : S.relIndex T = 2) : J = S ∨ J = T := by
  have hmul := Subgroup.relIndex_mul_relIndex S J T hSJ hJT
  rw [h] at hmul
  have hdvd : J.relIndex T ∣ 2 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Or.inr (le_antisymm hJT (Subgroup.relIndex_eq_one.mp h1))
  · left
    rw [h2] at hmul
    have h3 : S.relIndex J = 1 := by omega
    exact (le_antisymm hSJ (Subgroup.relIndex_eq_one.mp h3)).symm

theorem isSylowTwoOf_restrict {S N I : Subgroup G} (hS : IsSylowTwoOf S I) (hSN : S ≤ N)
    (hNI : N ≤ I) : IsSylowTwoOf S N := by
  refine ⟨hSN, hS.2.1, fun h => hS.2.2 ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex S N I hSN hNI
  have h' : 2 ∣ S.relIndex N := h
  have h'' : 2 ∣ S.relIndex I := hmul ▸ Dvd.dvd.mul_right h' _
  exact h''

theorem exists_mem_normalizer_not_mem_of_lt [Finite G] {P S : Subgroup G} (hP : IsPGroup 2 P)
    (hSP : S < P) : ∃ x ∈ P, x ∉ S ∧ x ∈ Subgroup.normalizer (S : Set G) := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hIP : S.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    have hPS : P ≤ S := Subgroup.subgroupOf_eq_top.mp htop
    exact absurd hSP (not_lt_of_ge hPS)
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hlt := hnc (S.subgroupOf P) hIP
  obtain ⟨x, hxN, hxS⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxS (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hSP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem isSylowTwoOf_of_forall_normalizer [Finite G] {S I : Subgroup G} (hSI : S ≤ I)
    (hS : IsPGroup 2 S)
    (h : ∀ x ∈ I, x ∈ Subgroup.normalizer (S : Set G) → IsPGroup 2 (Subgroup.zpowers x) →
      x ∈ S) : IsSylowTwoOf S I := by
  obtain ⟨P, hP, hSP⟩ := EscapingLocal.exists_isSylowTwoOf_ge hSI hS
  have hSP' : S = P := by
    by_contra hne
    obtain ⟨x, hxP, hxS, hxN⟩ :=
      exists_mem_normalizer_not_mem_of_lt hP.2.1 (lt_of_le_of_ne hSP hne)
    exact hxS (h x (hP.1 hxP) hxN (hP.2.1.to_le (Subgroup.zpowers_le.mpr hxP)))
  rwa [hSP']

theorem normalizer_eq_of_le_normalizer {M C : Subgroup G} (hM : quasithinIsMaxTwoLocal M)
    (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hMC : M ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) = M :=
  hM.2 _ ⟨C, hC1, hC2, rfl⟩ hMC

theorem mem_sup_iff_of_le_normalizer {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G))
    {x : G} : x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  constructor
  · intro hx
    let Q : Subgroup G :=
      { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
          refine ⟨h₁ * (k₁ * h₂ * k₁⁻¹), H.mul_mem hh₁ ?_, k₁ * k₂, K.mul_mem hk₁ hk₂, by group⟩
          exact (Subgroup.mem_normalizer_iff.mp (hK hk₁) h₂).mp hh₂
        inv_mem' := by
          rintro _ ⟨h, hh, k, hk, rfl⟩
          refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (hK (K.inv_mem hk)) h⁻¹).mp (H.inv_mem hh)
          simpa [mul_assoc] using this }
    have hle : H ⊔ K ≤ Q :=
      sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
        (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
    exact hle hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

theorem oTwoUpper_idem (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  apply le_antisymm (oTwoUpper_le _)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem le_oddCoreIn_of_odd {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem oddCoreIn_eq_oTwoUpper [Finite G] {H : Subgroup G}
    (hodd : Odd (Nat.card (oTwoUpper H))) : oddCoreIn H = oTwoUpper H := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H := oddCoreIn_le H hx
    have hord : Odd (orderOf x) :=
      (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn H) hx)
    exact mem_oTwoUpper_of_odd hxH hord
  · exact le_oddCoreIn_of_odd (oTwoUpper_le H) (le_normalizer_oTwoUpper H) hodd

theorem inverts_of_commutator_eq_of_comm {E B : Subgroup G} {b : G} (hb2 : b ^ 2 = 1)
    (hbE : b ∈ Subgroup.normalizer (E : Set G)) (hBb : ∀ x ∈ B, x = 1 ∨ x = b)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcomm : ⁅E, B⁆ = E) :
    ∀ e ∈ E, b * e * b⁻¹ = e⁻¹ := by
  have hbinv : b⁻¹ = b := by
    have h1 : b * b = 1 := by rw [← sq]; exact hb2
    exact inv_eq_of_mul_eq_one_right h1
  let I : Subgroup G :=
    { carrier := {e | e ∈ E ∧ b * e * b⁻¹ = e⁻¹}
      one_mem' := ⟨E.one_mem, by simp⟩
      mul_mem' := by
        rintro a c ⟨ha, ha'⟩ ⟨hc, hc'⟩
        refine ⟨E.mul_mem ha hc, ?_⟩
        have e1 : b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) := by group
        rw [e1, ha', hc', mul_inv_rev, hab _ (E.inv_mem ha) _ (E.inv_mem hc)]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨E.inv_mem ha, ?_⟩
        have e1 : b * a⁻¹ * b⁻¹ = (b * a * b⁻¹)⁻¹ := by group
        rw [e1, ha'] }
  have hle : ⁅E, B⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    have hxE : x * e⁻¹ * x⁻¹ ∈ E := by
      rcases hBb x hx with rfl | rfl
      · simpa using E.inv_mem he
      · exact (Subgroup.mem_normalizer_iff.mp hbE e⁻¹).mp (E.inv_mem he)
    refine ⟨?_, ?_⟩
    · have : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact E.mul_mem he hxE
    · rcases hBb x hx with rfl | rfl
      · simp
      · simp only [commutatorElement_def]
        rw [hbinv]
        have e2 : x * (e * x * e⁻¹ * x) * x = x * e * x * e⁻¹ * (x * x) := by group
        have e3 : x * x = 1 := by rw [← sq]; exact hb2
        have e4 : (e * x * e⁻¹ * x)⁻¹ = x⁻¹ * e * x⁻¹ * e⁻¹ := by group
        rw [e2, e3, e4, hbinv]
        group
  rw [hcomm] at hle
  exact fun e he => (hle he).2

theorem eq_one_of_commutator_eq_of_comm {E B : Subgroup G} {b : G} (hb2 : b ^ 2 = 1)
    (hbE : b ∈ Subgroup.normalizer (E : Set G)) (hBb : ∀ x ∈ B, x = 1 ∨ x = b)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcomm : ⁅E, B⁆ = E) (hodd : Odd (Nat.card E)) :
    ∀ e ∈ E, b * e = e * b → e = 1 := by
  intro e he hbe
  have hinv := inverts_of_commutator_eq_of_comm hb2 hbE hBb hab hcomm e he
  have hc : b * e * b⁻¹ = e := by rw [hbe]; group
  have he2 : e ^ 2 = 1 := by
    have : e = e⁻¹ := hc.symm.trans hinv
    calc e ^ 2 = e * e := sq e
      _ = e * e⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel e
  have h1 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
  have h2 : orderOf e ∣ Nat.card E :=
    Subgroup.orderOf_dvd_natCard E he
  have h3 : Odd (orderOf e) := hodd.of_dvd_nat h2
  have h4 : orderOf e = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h3; exact absurd h3 (by decide)
  exact orderOf_eq_one_iff.mp h4

end CFSG.Quasithin
