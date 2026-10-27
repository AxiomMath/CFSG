module

public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.Quasithin.Background.RonanF13Transfer

public section

namespace CFSG.Quasithin.RonanF13

universe u

open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type u} [Group G]

theorem commute_of_sup {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 := hAB a ha b hb
      have : b * a * b⁻¹ = a := by rw [← h1]; group
      rw [this]
      exact ha
    · intro hba
      have h1 := hAB _ hba b⁻¹ (B.inv_mem hb)
      have h2 : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← h1]
          _ = b * a * b⁻¹ := by group
      rw [h2]
      exact hba
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBA).mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBA).mp hy
  have e1 := hA a ha a' ha'
  have e2 := hB b hb b' hb'
  have e3 := hAB a' ha' b hb
  have e4 := hAB a ha b' hb'
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [e3]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1, e2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e4]
    _ = a' * b' * (a * b) := by group

theorem mem_normalizer_inf {D N : Subgroup G} {g : G} (hgD : g ∈ D)
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    g ∈ Subgroup.normalizer ((D ⊓ N : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact ⟨D.mul_mem (D.mul_mem hgD hz.1) (D.inv_mem hgD),
      (Subgroup.mem_normalizer_iff.mp hgN z).mp hz.2⟩
  · intro hz
    have h1 : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hgN z).mpr hz.2⟩
    rw [h1]
    exact D.mul_mem (D.mul_mem (D.inv_mem hgD) hz.1) hgD

theorem core5 {L1 L2 S : Subgroup G} (h : F13Setup L1 L2 S)
    (hT1 : RankOneTwist (oTwoQuot ↥L1)) (hT2 : RankOneTwist (oTwoQuot ↥L2)) :
    ∃ D1 D2 : Subgroup G, HallTwoPrime D1 (borelOf L1 S) ∧ HallTwoPrime D2 (borelOf L2 S) ∧
      borelOf L1 S = (S ⊓ L1) ⊔ D1 ∧ borelOf L2 S = (S ⊓ L2) ⊔ D2 ∧
      (∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x) ∧
      borelOf L1 S ⊔ borelOf L2 S ⊔ S = S ⊔ D1 ⊔ D2 ∧
      HallTwoPrime (D1 ⊔ D2) (borelOf L1 S ⊔ borelOf L2 S ⊔ S) ∧
      (∀ x ∈ D1 ⊔ D2, ∀ y ∈ D1 ⊔ D2, x * y = y * x) := by
  classical
  obtain ⟨D, hD, hD1, hD2, hE1, hE2, hDE, hBE⟩ := hall_setup h
  have hB1B : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S := le_sup_right.trans le_sup_left
  have hBN1 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer (borelOf L1 S : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h.b2_le_nb1) h.s_le_nb1
  have hBN2 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer (borelOf L2 S : Set G) :=
    sup_le (sup_le h.b1_le_nb2 Subgroup.le_normalizer) h.s_le_nb2
  have hSD : S ⊓ D = ⊥ := inf_eq_bot_of_odd h.pS hD.2.1
  have hab1 : ∀ x ∈ D ⊓ borelOf L1 S, ∀ y ∈ D ⊓ borelOf L1 S, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ S ⊓ D :=
      ⟨(h.comm1 x hx.2 y hy.2).1,
        D.mul_mem (D.mul_mem (D.mul_mem hx.1 hy.1) (D.inv_mem hx.1)) (D.inv_mem hy.1)⟩
    rw [hSD, Subgroup.mem_bot] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hab2 : ∀ x ∈ D ⊓ borelOf L2 S, ∀ y ∈ D ⊓ borelOf L2 S, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ S ⊓ D :=
      ⟨(h.comm2 x hx.2 y hy.2).1,
        D.mul_mem (D.mul_mem (D.mul_mem hx.1 hy.1) (D.inv_mem hx.1)) (D.inv_mem hy.1)⟩
    rw [hSD, Subgroup.mem_bot] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hcomm : ∀ x ∈ D ⊓ borelOf L1 S, ∀ y ∈ D ⊓ borelOf L2 S, x * y = y * x := by
    intro x hx d hd
    have hdD : d ∈ D := hd.1
    have hdB : d ∈ borelOf L1 S ⊔ borelOf L2 S ⊔ S := hB2B hd.2
    have hdodd : Odd (orderOf d) := by
      have h1 : orderOf d ∣ Nat.card ↥(D ⊓ borelOf L2 S) := by
        have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥(D ⊓ borelOf L2 S))
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hD2.2.1 h1
    have key := twist_commute (L := L1) (T := S ⊓ L1) (B := borelOf L1 S) (Di := D ⊓ borelOf L1 S)
      inf_le_right h.syl1.2.1 h.syl1.2.2 rfl hE1 hD1.2.1 hT1 h.pcore1
      (d := d) (h.b2_le_nL1 hd.2) (h.bigB_le_ns1 hdB)
      (mem_normalizer_inf hdD (hBN1 hdB)) (F7.le_normalizer_pCoreOf_of_le_normalizer h.b2_le_nL1 hd.2)
      hdodd ?_ x hx
    · have : x * d = d * x := by
        have h2 : d * x * d⁻¹ = x := key
        calc x * d = (d * x * d⁻¹) * d := by rw [h2]
          _ = d * x := by group
      exact this
    · intro z hz
      have hzD : z ∈ D := hz.1
      have hzN : z⁻¹ ∈ Subgroup.normalizer (borelOf L2 S : Set G) := Subgroup.inv_mem _ (hBN2 (hB1B hz.2))
      have hy : z⁻¹ * (d * z * d⁻¹) ∈ D ⊓ borelOf L2 S := by
        have h1 : z⁻¹ * (d * z * d⁻¹) = (z⁻¹ * d * z) * d⁻¹ := by group
        rw [h1]
        refine ⟨D.mul_mem (D.mul_mem (D.mul_mem (D.inv_mem hzD) hdD) hzD) (D.inv_mem hdD),
          (borelOf L2 S).mul_mem ?_ ((borelOf L2 S).inv_mem hd.2)⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBN2 (hB1B hz.2))) d).mp hd.2
        simpa [mul_assoc] using this
      have hcd := hab2 d hd _ hy
      calc d * (z⁻¹ * (d * z * d⁻¹)) * d⁻¹ = (d * (z⁻¹ * (d * z * d⁻¹))) * d⁻¹ := rfl
        _ = ((z⁻¹ * (d * z * d⁻¹)) * d) * d⁻¹ := by rw [hcd]
        _ = z⁻¹ * (d * z * d⁻¹) := by group
  refine ⟨D ⊓ borelOf L1 S, D ⊓ borelOf L2 S, hD1, hD2, hE1, hE2, hcomm, hBE, ?_, ?_⟩
  · rw [← hDE]
    exact hD
  · exact commute_of_sup hab1 hab2 hcomm


end CFSG.Quasithin.RonanF13
