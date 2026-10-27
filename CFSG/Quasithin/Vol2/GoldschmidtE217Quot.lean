module

public import CFSG.Quasithin.Vol2.GoldschmidtE217TwoInv
public import CFSG.Quasithin.Vol2.GoldschmidtE217Bridge
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F B6 E2

namespace E217R1

section Quotient

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem no_central_involution_quotient (h : E2.Pair X T M V g) {w : E2.StarQuot M X}
    (hw2 : w * w = 1) (hw1 : w ≠ 1) : ∃ q : E2.StarQuot M X, q * w ≠ w * q := by
  have hJX : kerIn M X ≤ X := kerIn_le.trans h.le_X
  have hJn : ((kerIn M X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (le_normalizer_kerIn M X)
  by_contra hcon
  push Not at hcon
  set φ := QuotientGroup.mk' ((kerIn M X).subgroupOf X) with hφ
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective w
  have hwc : (QuotientGroup.mk w₀ : E2.StarQuot M X) ∈
      Subgroup.center (E2.StarQuot M X) :=
    Subgroup.mem_center_iff.2 hcon
  have hzn : (Subgroup.zpowers (QuotientGroup.mk w₀ : E2.StarQuot M X)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hwc)
  set D' : Subgroup ↥X := (Subgroup.zpowers (QuotientGroup.mk w₀ : ↥X ⧸
    (kerIn M X).subgroupOf X)).comap φ with hD'
  have hD'n : D'.Normal := hzn.comap φ
  set D : Subgroup G := D'.map X.subtype with hD
  have hDX : D ≤ X := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf X = D' :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective D'
  have hXD : X ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).1 (hDsub ▸ hD'n)
  have hJD : kerIn M X ≤ D := by
    intro j hj
    refine ⟨⟨j, hJX hj⟩, ?_, rfl⟩
    show φ ⟨j, hJX hj⟩ ∈ Subgroup.zpowers _
    have : φ ⟨j, hJX hj⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hj
    rw [this]
    exact Subgroup.one_mem _
  have h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ kerIn M X := by
    rintro _ ⟨d', hd', rfl⟩
    refine ⟨1, ?_⟩
    have hd'' : φ d' ∈ Subgroup.zpowers (QuotientGroup.mk w₀ : ↥X ⧸
      (kerIn M X).subgroupOf X) := hd'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hd''
    have hsq : φ (d' ^ 2) = 1 := by
      have hw2' : (QuotientGroup.mk w₀ : E2.StarQuot M X) ^ (2 : ℤ) = 1 := by
        rw [zpow_two]
        exact hw2
      have e : (φ d') ^ 2 = (φ d') ^ (2 : ℤ) := by rw [zpow_two, pow_two]
      rw [map_pow, e, ← hi, ← zpow_mul, mul_comm, zpow_mul, hw2', one_zpow]
    have := (QuotientGroup.eq_one_iff _).1 hsq
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hDJ := h.le_kerIn_of_isTwoQuotient hDX hXD hJD h2
  have hw0D : (w₀ : G) ∈ D := ⟨w₀, Subgroup.mem_zpowers _, rfl⟩
  have hw0J : (w₀ : G) ∈ kerIn M X := hDJ hw0D
  apply hw1
  exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hw0J)

theorem not_four_dvd_relIndex_of_relIndex_eq_two (h : E2.Pair X T M V g)
    (h2 : (kerIn M X ⊓ V).relIndex V = 2) : ¬ 4 ∣ (kerIn M X).relIndex X := by
  have hJX : kerIn M X ≤ X := kerIn_le.trans h.le_X
  have hJn : ((kerIn M X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (le_normalizer_kerIn M X)
  obtain ⟨x, hxV, hxJ⟩ : ∃ x ∈ V, x ∉ kerIn M X := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ kerIn M X := hcon
    rw [inf_eq_right.2 hle, Subgroup.relIndex_self] at h2
    omega
  have hV2 := E2.forall_mem_or_mul_mem_of_relIndex_eq_two h.elem (by rwa [inf_comm] at h2) hxV hxJ
  set φ := QuotientGroup.mk' ((kerIn M X).subgroupOf X) with hφ
  have hxX : x ∈ X := h.V_le hxV
  have hgX : g ∈ X := h.mem
  have hx2 : x * x = 1 := by simpa [pow_two] using h.elem.2 x hxV
  have hyX : g * x * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hgX hxX) (X.inv_mem hgX)
  have hyconj : g * x * g⁻¹ ∈ conjSub g V := B6.mem_conjSub.2 (by simpa [mul_assoc] using hxV)
  set a : E2.StarQuot M X := φ ⟨x, hxX⟩ with ha
  set b : E2.StarQuot M X := φ ⟨g * x * g⁻¹, hyX⟩ with hb
  set gq : E2.StarQuot M X := φ ⟨g, hgX⟩ with hgq
  have haa : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨x, hxX⟩ * ⟨x, hxX⟩ : ↥X) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hbb : b * b = 1 := by
    rw [hb, ← map_mul]
    have : (⟨g * x * g⁻¹, hyX⟩ * ⟨g * x * g⁻¹, hyX⟩ : ↥X) = 1 := by
      apply Subtype.ext
      show g * x * g⁻¹ * (g * x * g⁻¹) = 1
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    rw [this, map_one]
  have hbconj : b = gq * a * gq⁻¹ := by
    rw [hb, ha, hgq, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hVimg : ∀ v : ↥X, (v : G) ∈ V → φ v = 1 ∨ φ v = a := by
    intro v hv
    rcases hV2 v hv with hvJ | hvJ
    · left
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hvJ.2)
    · right
      have h1 : φ (⟨x, hxX⟩ * v) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hvJ.2)
      rw [map_mul, ← ha] at h1
      have := eq_inv_of_mul_eq_one_right h1
      rw [this, hai]
  have hgen : Subgroup.closure ({a, b} : Set (E2.StarQuot M X)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    induction q using QuotientGroup.induction_on with
    | H z =>
      have hz : (z : G) ∈ V ⊔ conjSub g V := h.gen ▸ z.2
      rw [Subgroup.sup_eq_closure] at hz
      have key : ∀ y : G, ∀ hy : y ∈ Subgroup.closure ((V : Set G) ∪ (conjSub g V : Set G)),
          ∀ hyX : y ∈ X, φ ⟨y, hyX⟩ ∈ Subgroup.closure ({a, b} :
            Set (E2.StarQuot M X)) := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem y hy' =>
          intro hyX
          rcases hy' with hy' | hy'
          · rcases hVimg ⟨y, hyX⟩ hy' with h1 | h1
            · rw [h1]
              exact Subgroup.one_mem _
            · rw [h1]
              exact Subgroup.subset_closure (Set.mem_insert _ _)
          · have hvV : g⁻¹ * y * g ∈ V := B6.mem_conjSub.1 hy'
            have hvX : g⁻¹ * y * g ∈ X := h.V_le hvV
            have hyeq : (⟨y, hyX⟩ : ↥X) = ⟨g, hgX⟩ * ⟨g⁻¹ * y * g, hvX⟩ * ⟨g, hgX⟩⁻¹ := by
              apply Subtype.ext
              show y = g * (g⁻¹ * y * g) * g⁻¹
              group
            rw [hyeq, map_mul, map_mul, map_inv, ← hgq]
            rcases hVimg ⟨g⁻¹ * y * g, hvX⟩ hvV with h1 | h1
            · rw [h1]
              simp
            · rw [h1, ← hbconj]
              exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        | one =>
          intro hyX
          have : (⟨1, hyX⟩ : ↥X) = 1 := rfl
          rw [this, map_one]
          exact Subgroup.one_mem _
        | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
          intro hyX
          have hy₁X : y₁ ∈ X := by
            have := Subgroup.sup_eq_closure V (conjSub g V) ▸ hy₁
            exact (h.gen ▸ this)
          have hy₂X : y₂ ∈ X := by
            have := Subgroup.sup_eq_closure V (conjSub g V) ▸ hy₂
            exact (h.gen ▸ this)
          have := (Subgroup.closure _).mul_mem (ih₁ hy₁X) (ih₂ hy₂X)
          rwa [← map_mul] at this
        | inv y₁ hy₁ ih =>
          intro hyX
          have hy₁X : y₁ ∈ X := by
            have := Subgroup.sup_eq_closure V (conjSub g V) ▸ hy₁
            exact (h.gen ▸ this)
          have := (Subgroup.closure _).inv_mem (ih hy₁X)
          rwa [← map_inv] at this
      exact key z hz z.2
  exact not_four_dvd_card_of_two_involutions haa hbb hgen
    (fun w hw2 hw1 => no_central_involution_quotient h hw2 hw1)

end Quotient

end E217R1

end CFSG.Quasithin
