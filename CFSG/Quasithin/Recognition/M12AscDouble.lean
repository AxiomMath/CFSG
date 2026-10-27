module

public import CFSG.Quasithin.Recognition.M12AscGen

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

theorem double_transfer [Finite G] {t : G} (ht2 : t * t = 1) {S D V : Subgroup G} {r : G}
    (hSI : S ≤ Subgroup.centralizer ({t} : Set G)) (hSp : IsPGroup 2 S)
    (hSmax : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({t} : Set G) → IsPGroup 2 R → S ≤ R →
      R = S)
    (htS : t ∈ S) (hDS : D ≤ S) (hS16 : Nat.card S = 16) (hSD : Nat.card S = 2 * Nat.card D)
    (htD : t ∉ D) (hVD : V ≤ D) (hVcard : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (hrS : r ∈ S) (hr2 : r * r = 1)
    (hVcl : ∀ v ∈ V, ∀ a ∈ Subgroup.centralizer ({t} : Set G), a⁻¹ * v * a ∈ S → a⁻¹ * v * a ∈ V)
    (hrV : ∀ a : G, a⁻¹ * r * a ∉ V ∧ a⁻¹ * (r * t) * a ∉ V) :
    ∃ I0 K : Subgroup G, I0 ≤ Subgroup.centralizer ({t} : Set G) ∧ K ≤ I0 ∧
      (∀ x ∈ Subgroup.centralizer ({t} : Set G), ∀ w ∈ I0, x * w * x⁻¹ ∈ I0) ∧
      (∀ x ∈ Subgroup.centralizer ({t} : Set G), ∀ w ∈ K, x * w * x⁻¹ ∈ K) ∧
      Nat.card (Subgroup.centralizer ({t} : Set G)) = 4 * Nat.card K ∧ t ∉ I0 ∧
      (∀ a ∈ Subgroup.centralizer ({t} : Set G), a * a ∈ K) ∧ V ≤ K ∧
      (∀ k ∈ K, k ∈ S → k ∈ V) := by
  classical
  set I : Subgroup G := Subgroup.centralizer ({t} : Set G) with hI
  have hmemI : ∀ a, a ∈ I ↔ a * t = t * a := fun a => Subgroup.mem_centralizer_singleton_iff
  have htcomm : ∀ a ∈ I, t * a = a * t := fun a ha => ((hmemI a).1 ha).symm
  have htI : t ∈ I := (hmemI t).2 rfl
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hidx : D.relIndex S = 2 := relIndex_eq_two_of_card hDS hSD
  have hQu : ∀ a ∈ I, a⁻¹ * t * a ∉ D := by
    intro a ha
    have : a⁻¹ * t * a = t := by
      calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
        _ = a⁻¹ * (a * t) := by rw [htcomm a ha]
        _ = t := by group
    rw [this]
    exact htD
  obtain ⟨I0, hI0I, hI0n, hI0card, htI0, htr1, hcrit1⟩ :=
    thompson_transfer_index_two_sub I S D hSI hSp hSmax hidx ht2 htS hQu
  have hVS : V ≤ S := hVD.trans hDS
  have hVI0 : ∀ v ∈ V, v ∈ I0 := by
    intro v hv
    have hcond : ∀ a ∈ I, a⁻¹ * v * a ∈ S → (a⁻¹ * v * a ∈ D ↔ v ∈ D) := fun a ha haS =>
      ⟨fun _ => hVD hv, fun _ => hVD (hVcl v hv a ha haS)⟩
    exact (hcrit1 v (hVS hv) (hVsq v hv) hcond).2 (hVD hv)
  obtain ⟨r0, hr0I0, hr0S, hr02, hr0V⟩ : ∃ r0 : G, r0 ∈ I0 ∧ r0 ∈ S ∧ r0 * r0 = 1 ∧
      ∀ a : G, a⁻¹ * r0 * a ∉ V := by
    rcases htr1 r (hSI hrS) with h | h
    · exact ⟨r, h, hrS, hr2, fun a => (hrV a).1⟩
    · refine ⟨r * t, h, S.mul_mem hrS htS, ?_, fun a => (hrV a).2⟩
      have hrt : t * r = r * t := htcomm r (hSI hrS)
      calc r * t * (r * t) = r * (t * r) * t := by group
        _ = r * (r * t) * t := by rw [hrt]
        _ = (r * r) * (t * t) := by group
        _ = 1 := by rw [hr2, ht2, one_mul]
  have hS0card : Nat.card S = 2 * Nat.card (S ⊓ I0 : Subgroup G) :=
    card_inf_of_transversal htS htI0 (fun a ha => htr1 a (hSI ha))
  have hS0card8 : Nat.card (S ⊓ I0 : Subgroup G) = 8 := by omega
  obtain ⟨m, hmodd, hIm⟩ := exists_odd_card_of_maximal I S hSI hSp hSmax
  have hIcard : Nat.card I = 16 * m := by rw [hIm, hS16]
  have hI0m : Nat.card I0 = 2 ^ 3 * m := by
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [this]
    omega
  have hS0max : ∀ R : Subgroup G, R ≤ I0 → IsPGroup 2 R → (S ⊓ I0) ≤ R → R = S ⊓ I0 := by
    intro R hRI0 hRp hSR
    have hle := card_le_of_isPGroup_of_odd hI0m hmodd hRp hRI0
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hSR (by rw [hS0card8]; omega)).symm
  have hVS0 : V ≤ S ⊓ I0 := fun v hv => ⟨hVS hv, hVI0 v hv⟩
  have hidx2 : V.relIndex (S ⊓ I0) = 2 :=
    relIndex_eq_two_of_card hVS0 (by rw [hS0card8, hVcard])
  have hQu2 : ∀ a ∈ I0, a⁻¹ * r0 * a ∉ V := fun a _ => hr0V a
  obtain ⟨K, hKI0, hKn, hKcard, hr0K, htr2, hcrit2⟩ :=
    thompson_transfer_index_two_sub I0 (S ⊓ I0) V inf_le_right (hSp.to_le inf_le_left) hS0max
      hidx2 hr02 ⟨hr0S, hr0I0⟩ hQu2
  have hVK : ∀ v ∈ V, v ∈ K := by
    intro v hv
    have hcond : ∀ a ∈ I0, a⁻¹ * v * a ∈ (S ⊓ I0 : Subgroup G) → (a⁻¹ * v * a ∈ V ↔ v ∈ V) :=
      fun a ha haS => ⟨fun _ => hv, fun _ => hVcl v hv a (hI0I ha) haS.1⟩
    exact (hcrit2 v (hVS0 hv) (hVsq v hv) hcond).2 hv
  have hS0K : Nat.card (S ⊓ I0 : Subgroup G) = 2 * Nat.card ((S ⊓ I0) ⊓ K : Subgroup G) :=
    card_inf_of_transversal ⟨hr0S, hr0I0⟩ hr0K (fun a ha => htr2 a ha.2)
  have hVeq : V = (S ⊓ I0) ⊓ K :=
    Subgroup.eq_of_le_of_card_ge (fun v hv => ⟨hVS0 hv, hVK v hv⟩) (by omega)
  have hsqI0 : ∀ b ∈ I0, b * b ∈ K := fun b hb => sq_mem_of_transversal hKn hr02 hr0I0 htr2 hb
  have hsqI : ∀ a ∈ I, a * a ∈ K := by
    intro a ha
    rcases htr1 a ha with h | h
    · exact hsqI0 a h
    · have e : (a * t) * (a * t) = a * a := by
        calc a * t * (a * t) = a * (t * a) * t := by group
          _ = a * (a * t) * t := by rw [htcomm a ha]
          _ = (a * a) * (t * t) := by group
          _ = a * a := by rw [ht2, mul_one]
      rw [← e]
      exact hsqI0 _ h
  have hnormK : ∀ x ∈ I, ∀ w ∈ K, x * w * x⁻¹ ∈ K := by
    intro x hx w hw
    rcases htr1 x hx with h | h
    · exact hKn x h w hw
    · have hwI : w ∈ I := hI0I (hKI0 hw)
      have hcomm' : t * w * t⁻¹ = w := by
        rw [htcomm w hwI, hti, mul_assoc, ht2, mul_one]
      have e : x * w * x⁻¹ = (x * t) * w * (x * t)⁻¹ := by
        calc x * w * x⁻¹ = x * (t * w * t⁻¹) * x⁻¹ := by rw [hcomm']
          _ = (x * t) * w * (x * t)⁻¹ := by group
      rw [e]
      exact hKn (x * t) h w hw
  refine ⟨I0, K, hI0I, hKI0, hI0n, hnormK, by omega, htI0, hsqI, fun v hv => hVK v hv, ?_⟩
  intro k hk hkS
  rw [hVeq]
  exact ⟨⟨hkS, hKI0 hk⟩, hk⟩

end CFSG.Quasithin
