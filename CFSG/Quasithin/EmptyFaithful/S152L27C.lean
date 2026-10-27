module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

section Subnormal

variable {X : Type*} [Group X] [Finite X]

private def pPrimeCoreIn152 (p : ℕ) (K : Subgroup X) : Subgroup X :=
  (CFSG.pPrimeCore p ↥K).map K.subtype

private theorem pPrimeCoreIn152_le_of_normal (p : ℕ) [Fact p.Prime] {H K : Subgroup X} (hle : H ≤ K)
    (hN : (H.subgroupOf K).Normal) : pPrimeCoreIn152 p H ≤ pPrimeCoreIn152 p K := by
  set H' : Subgroup ↥K := H.subgroupOf K with hH'
  have : H'.Normal := hN
  let e : ↥H' ≃* ↥H := Subgroup.subgroupOfEquivOfLe hle
  have hA : ((CFSG.pPrimeCore p ↥H').map H'.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hAcop : Nat.Coprime p (Nat.card ↥((CFSG.pPrimeCore p ↥H').map H'.subtype)) := by
    rw [Subgroup.card_map_of_injective H'.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hAle : (CFSG.pPrimeCore p ↥H').map H'.subtype ≤ CFSG.pPrimeCore p ↥K := le_sSup ⟨hA, hAcop⟩
  have hid : pPrimeCoreIn152 p H = ((CFSG.pPrimeCore p ↥H').map H'.subtype).map K.subtype := by
    unfold pPrimeCoreIn152
    rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso p e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono hAle

private theorem pPrimeCoreIn152_le_of_subnormal (p : ℕ) [Fact p.Prime] {H : Subgroup X}
    (hH : H.IsSubnormal) : pPrimeCoreIn152 p H ≤ CFSG.pPrimeCore p X := by
  induction hH with
  | top =>
    have h := CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
    unfold pPrimeCoreIn152
    exact h.le
  | step H K hle hK hN ih =>
    exact (pPrimeCoreIn152_le_of_normal p hle hN).trans ih

theorem le_pPrimeCore_of_isSubnormal_of_coprime152 (p : ℕ) [Fact p.Prime] {A : Subgroup X}
    (hA : A.IsSubnormal) (hcop : Nat.Coprime p (Nat.card A)) : A ≤ CFSG.pPrimeCore p X := by
  refine le_trans ?_ (pPrimeCoreIn152_le_of_subnormal p hA)
  have h : (⊤ : Subgroup ↥A) ≤ CFSG.pPrimeCore p ↥A := by
    refine le_sSup ⟨inferInstance, ?_⟩
    simpa using hcop
  intro a ha
  exact ⟨⟨a, ha⟩, h (Subgroup.mem_top _), rfl⟩

end Subnormal

section Components

open scoped Pointwise commutatorElement

private theorem le_center_of_normal_of_ne_top152 {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q)) {D : Subgroup Q} (hD : D.Normal)
    (hne : D ≠ ⊤) : D ≤ Subgroup.center Q := by
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' _
  have hDn : (D.map π).Normal := hD.map π (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (D.map π) with h | h
  · intro d hd
    have : π d ∈ D.map π := ⟨d, hd, rfl⟩
    rw [h] at this
    exact (QuotientGroup.eq_one_iff d).mp (Subgroup.mem_bot.mp this)
  · exfalso
    apply hne
    have hsup : D ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq π D
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ D := by
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      have ha : a ∈ (D : Set Q) * (Subgroup.center Q : Set Q) := by
        rw [← Subgroup.mul_normal]; exact hsup ▸ Subgroup.mem_top a
      have hb : b ∈ (D : Set Q) * (Subgroup.center Q : Set Q) := by
        rw [← Subgroup.mul_normal]; exact hsup ▸ Subgroup.mem_top b
      obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := ha
      obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hb
      have hc1 := Subgroup.mem_center_iff.mp hz₁
      have hc2 := Subgroup.mem_center_iff.mp hz₂
      have e : ⁅d₁ * z₁, d₂ * z₂⁆ = ⁅d₁, d₂⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        have s1 : z₁ * d₂ * z₂ * z₁⁻¹ = d₂ * z₂ := by
          have h := hc1 (d₂ * z₂)
          calc z₁ * d₂ * z₂ * z₁⁻¹ = z₁ * (d₂ * z₂) * z₁⁻¹ := by group
            _ = (d₂ * z₂) * z₁ * z₁⁻¹ := by rw [h]
            _ = d₂ * z₂ := by group
        have s2 : z₂ * d₁⁻¹ * z₂⁻¹ = d₁⁻¹ := by
          have h := hc2 d₁⁻¹
          calc z₂ * d₁⁻¹ * z₂⁻¹ = (d₁⁻¹ * z₂) * z₂⁻¹ := by rw [h]
            _ = d₁⁻¹ := by group
        calc d₁ * z₁ * (d₂ * z₂) * (d₁ * z₁)⁻¹ * (d₂ * z₂)⁻¹
            = d₁ * (z₁ * d₂ * z₂ * z₁⁻¹) * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by group
          _ = d₁ * (d₂ * z₂) * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by rw [s1]
          _ = d₁ * d₂ * (z₂ * d₁⁻¹ * z₂⁻¹) * d₂⁻¹ := by group
          _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by rw [s2]
      rw [e]
      exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact hcomm

private theorem not_dvd_card_of_perfect_of_central152 {C : Type*} [Group C] [Finite C]
    (hperf : Group.IsPerfect C) (p : ℕ) [hp : Fact p.Prime]
    (hcen : ∀ y : C, (∃ k : ℕ, orderOf y = p ^ k) → y ∈ Subgroup.center C) :
    ¬ p ∣ Nat.card C := by
  intro hdvd
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  have hPc : (P : Subgroup C) ≤ Subgroup.center C := by
    intro y hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨y, hy⟩
    exact hcen y ⟨k, by rw [← Subgroup.orderOf_coe] at hk; simpa using hk⟩
  have hP : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤ Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro x _ y hy
    exact (Subgroup.mem_center_iff.mp (hPc hy) x).symm
  let f : C →* (P : Subgroup C) := MonoidHom.transferSylow P hP
  have hcommP : ∀ a b : (P : Subgroup C), a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hPc b.2) a)
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcommP (f a) (f b)]
    group
  have hPcard : p ∣ Nat.card (P : Subgroup C) := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self p (by
      intro h0
      have := (Nat.factorization_eq_zero_iff _ _).mp h0
      rcases this with h | h | h
      · exact h hp.out
      · exact h hdvd
      · exact (Nat.card_pos (α := C)).ne' h)
  have : Fintype (P : Subgroup C) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := (P : Subgroup C)) p (by
    simpa [Nat.card_eq_fintype_card] using hPcard)
  have h1 : f.domRestrict (P : Subgroup C) y = y ^ (P : Subgroup C).index := by
    have := MonoidHom.transferSylow_domRestrict_eq_pow P hP
    exact congrFun this y
  have h2 : f.domRestrict (P : Subgroup C) y = 1 := by
    simpa using (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top ((y : C))))
  rw [h2] at h1
  have h3 : orderOf y ∣ (P : Subgroup C).index := orderOf_dvd_of_pow_eq_one h1.symm
  rw [hy] at h3
  exact P.not_dvd_index h3

variable {Y : Type*} [Group Y] [Finite Y]

theorem isComponent_le_sup152 {K A C : Subgroup Y} (hK : K.Normal)
    (h3 : ∀ x : Y, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ K)
    (hA : ∀ W : Subgroup Y, W.Normal → ¬ 3 ∣ Nat.card W → W ≤ A)
    (hC : CFSG.IsComponent C) : C ≤ K ⊔ A := by
  by_cases hCK : C ≤ K
  · exact hCK.trans le_sup_left
  · obtain ⟨⟨hperf, hsimple, -⟩, hsub⟩ := hC
    have hD : (K.subgroupOf C).Normal := hK.subgroupOf C
    have hDne : K.subgroupOf C ≠ ⊤ := fun h => hCK (Subgroup.subgroupOf_eq_top.mp h)
    have hDc := le_center_of_normal_of_ne_top152 hperf hsimple hD hDne
    have hcen : ∀ y : C, (∃ k : ℕ, orderOf y = 3 ^ k) → y ∈ Subgroup.center C := by
      rintro y ⟨k, hk⟩
      have hyK : (y : Y) ∈ K := h3 y ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
      exact hDc (Subgroup.mem_subgroupOf.mpr hyK)
    have hnd : ¬ 3 ∣ Nat.card C := not_dvd_card_of_perfect_of_central152 hperf 3 hcen
    have hcop : Nat.Coprime 3 (Nat.card C) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
    have hle := le_pPrimeCore_of_isSubnormal_of_coprime152 3 hsub hcop
    have hWnd : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
    exact le_sup_of_le_right (hle.trans (hA _ inferInstance hWnd))

theorem eq_bot_of_normalizes_of_centralizes152
    (hY2 : ∀ W : Subgroup Y, W.Normal → IsPGroup 2 W → W = ⊥)
    {K A V : Subgroup Y} (hK : K.Normal)
    (h3 : ∀ x : Y, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ K)
    (hA : ∀ W : Subgroup Y, W.Normal → ¬ 3 ∣ Nat.card W → W ≤ A)
    (hV2 : IsPGroup 2 V) (hVA : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (hKV : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k) : V = ⊥ := by
  set F : Subgroup Y := CFSG.generalizedFitting Y with hF
  have hFn : F.Normal := by
    rw [hF, CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal Y
  have hFKA : F ≤ K ⊔ A := by
    refine sup_le ?_ ?_
    · rw [CFSG.fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      have hq : Nat.Prime q.1.1 := Nat.prime_of_mem_primeFactors q.1.2
      have : Fact (Nat.Prime q.1.1) := ⟨hq⟩
      by_cases h2 : q.1.1 = 2
      · have hpg : IsPGroup 2 (CFSG.pCore q.1.1 Y) := by
          rw [← h2]; exact CFSG.pCore_isPGroup
        have hbot : CFSG.pCore q.1.1 Y = ⊥ := hY2 _ CFSG.pCore_normal hpg
        rw [hbot]; exact bot_le
      · by_cases h3' : q.1.1 = 3
        · intro x hx
          obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := q.1.1) (G := Y))) ⟨x, hx⟩
          have e : orderOf x = orderOf (⟨x, hx⟩ : ↥(CFSG.pCore q.1.1 Y)) := Subgroup.orderOf_coe ⟨x, hx⟩
          exact Subgroup.mem_sup_left (h3 x ⟨k, by rw [e, hk, h3']⟩)
        · intro x hx
          obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := q.1.1) (G := Y)).exists_card_eq
          have hnd : ¬ 3 ∣ Nat.card (CFSG.pCore q.1.1 Y) := by
            rw [hn]
            intro hd
            exact h3' (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
              (Nat.prime_three.dvd_of_dvd_pow hd)).symm)
          exact Subgroup.mem_sup_right (hA _ CFSG.pCore_normal hnd hx)
    · exact sSup_le fun C hC => isComponent_le_sup152 hK h3 hA hC
  have hKA : K ⊔ A ≤ Subgroup.normalizer (V : Set Y) := by
    refine sup_le (fun k hk => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        have := hKV k hk v hv
        rw [show k * v * k⁻¹ = v by rw [this]; group]
        exact hv
      · intro hw
        have hc := hKV k⁻¹ (K.inv_mem hk) _ hw
        have e : v = k * v * k⁻¹ := by
          calc v = k⁻¹ * (k * v * k⁻¹) * k := by group
            _ = ((k * v * k⁻¹) * k⁻¹) * k := by rw [hc]
            _ = k * v * k⁻¹ := by group
        convert hw using 1
    · rw [Subgroup.mem_normalizer_iff]
      intro v
      refine ⟨fun hv => hVA a ha v hv, fun hw => ?_⟩
      have := hVA a⁻¹ (A.inv_mem ha) _ hw
      simpa [mul_assoc] using this
  have hFN : F ≤ Subgroup.normalizer (V : Set Y) := hFKA.trans hKA
  set D : Subgroup Y := V ⊓ F with hD
  have hD2 : IsPGroup 2 D := hV2.to_le inf_le_left
  have hDn : F ≤ Subgroup.normalizer (D : Set Y) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfV := Subgroup.mem_normalizer_iff.mp (hFN hf) x
    have hfF : x ∈ F ↔ f * x * f⁻¹ ∈ F := by
      constructor
      · intro hx; exact F.mul_mem (F.mul_mem hf hx) (F.inv_mem hf)
      · intro hx
        have := F.mul_mem (F.mul_mem (F.inv_mem hf) hx) hf
        simpa [mul_assoc] using this
    exact ⟨fun hx => ⟨hfV.mp hx.1, hfF.mp hx.2⟩, fun hx => ⟨hfV.mpr hx.1, hfF.mpr hx.2⟩⟩
  have hDW : D ≤ CFSG.Open.pCoreOf 2 F :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hDn hD2
  have hWn : (CFSG.Open.pCoreOf 2 F).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    calc (⊤ : Subgroup Y) = Subgroup.normalizer (F : Set Y) :=
          (Subgroup.normalizer_eq_top_iff.mpr hFn).symm
      _ ≤ _ := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 F
  have hW0 : CFSG.Open.pCoreOf 2 F = ⊥ := hY2 _ hWn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 F)
  have hD0 : D = ⊥ := le_bot_iff.mp (hW0 ▸ hDW)
  rw [eq_bot_iff]
  intro v hv
  have hvc : v ∈ Subgroup.centralizer (F : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hmem : v * f * v⁻¹ * f⁻¹ ∈ D := by
      refine ⟨?_, ?_⟩
      · have h1 : f * v⁻¹ * f⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hFN hf) v⁻¹).mp (V.inv_mem hv)
        have := V.mul_mem hv h1
        simpa [mul_assoc] using this
      · exact F.mul_mem (hFn.conj_mem f hf v) (F.inv_mem hf)
    have h1 : v * f * v⁻¹ * f⁻¹ = 1 := Subgroup.mem_bot.mp (hD0 ▸ hmem)
    calc f * v = (v * f * v⁻¹ * f⁻¹) * (f * v) := by rw [h1]; simp
      _ = v * f := by group
  have hvF : v ∈ F := CFSG.centralizer_generalizedFitting_le Y hvc
  have : v ∈ D := ⟨hv, hvF⟩
  rw [hD0] at this
  exact this

end Components

end CFSG.Quasithin
