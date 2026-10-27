module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Count
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab2

variable {D : Type*} [Group D]

theorem normalizer_of_le_conjSub [Finite D] {R : Subgroup D} {g : D} (hle : R ≤ conjSub g R) :
    g ∈ Subgroup.normalizer (R : Set D) := by
  have heq : R = conjSub g R :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSub g R))
  refine Subgroup.mem_normalizer_iff''.mpr fun u => ?_
  constructor
  · intro hu
    have : u ∈ conjSub g R := heq ▸ hu
    exact mem_conjSub.mp this
  · intro hu
    have : u ∈ conjSub g R := mem_conjSub.mpr hu
    exact heq ▸ this

theorem two_mul_card_le_of_lt [Finite D] {K R : Subgroup D} (h : K < R) :
    2 * Nat.card K ≤ Nat.card R := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le h.le
  have hK : 0 < Nat.card K := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hm.le)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card R := Nat.card_pos
    omega
  rw [hm]
  have : 2 ≤ m := by omega
  nlinarith

theorem c_facts {x z : D} (hx3 : x * x * x = 1) (hmove : x * z * x⁻¹ ≠ z) (hz1 : z ≠ 1) :
    x * z * x⁻¹ ≠ 1 ∧ x * x * z * (x * x)⁻¹ ≠ 1 ∧ z ≠ x * z * x⁻¹ ∧
      z ≠ x * x * z * (x * x)⁻¹ ∧ x * z * x⁻¹ ≠ x * x * z * (x * x)⁻¹ := by
  refine ⟨fun e => hz1 ?_, fun e => hz1 ?_, fun e => hmove e.symm, fun e => hmove ?_,
    fun e => hmove ?_⟩
  · calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  · calc z = (x * x)⁻¹ * (x * x * z * (x * x)⁻¹) * (x * x) := by group
      _ = 1 := by rw [e]; group
  · calc x * z * x⁻¹ = x * (x * x * z * (x * x)⁻¹) * x⁻¹ := by rw [← e]
      _ = (x * x * x) * z * (x * x * x)⁻¹ := by group
      _ = z := by rw [hx3]; group
  · calc x * z * x⁻¹ = x⁻¹ * (x * x * z * (x * x)⁻¹) * x := by group
      _ = x⁻¹ * (x * z * x⁻¹) * x := by rw [e]
      _ = z := by group

theorem conj_mem_conjClosure {B V : Subgroup D} {g v : D} (hg : g ∈ B) (hv : v ∈ V) :
    g * v * g⁻¹ ∈ conjClosure V B :=
  mem_conjClosure hg hv

theorem conj_mem_conjClosure_self {B V : Subgroup D} {g u : D} (hg : g ∈ B)
    (hu : u ∈ conjClosure V B) : g * u * g⁻¹ ∈ conjClosure V B :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hg) u).mp hu

theorem conj_inv_mem_pCoreOf {B : Subgroup D} {x q : D} (hxB : x ∈ B) (hq : q ∈ pCoreOf 2 B) :
    x⁻¹ * q * x ∈ pCoreOf 2 B := by
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B (B.inv_mem hxB)) q).mp hq
  simpa using this

section Tests

variable [Finite D]

theorem exists_test_a {A B : Subgroup D} {x : D} (hxB : x ∈ B)
    (hnorm : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    ∃ q ∈ pCoreOf 2 B, q ∈ pCoreOf 2 A ∧ x⁻¹ * q * x ∉ pCoreOf 2 A := by
  by_contra hcon
  push Not at hcon
  apply hnorm
  apply normalizer_of_le_conjSub
  intro q hq
  exact mem_conjSub.mpr ⟨hcon q hq.2 hq.1, conj_inv_mem_pCoreOf hxB hq.2⟩

theorem exists_test_b {A B : Subgroup D} {x : D} (hxB : x ∈ B)
    (hnorm : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    ∃ q ∈ pCoreOf 2 B, q ∉ pCoreOf 2 A ∧ x⁻¹ * q * x ∈ pCoreOf 2 A := by
  by_contra hcon
  push Not at hcon
  apply hnorm
  have hle : conjSub x (pCoreOf 2 A ⊓ pCoreOf 2 B) ≤ pCoreOf 2 A ⊓ pCoreOf 2 B := by
    intro u hu
    have hu' := mem_conjSub.mp hu
    have huB : u ∈ pCoreOf 2 B := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hxB) _).mp hu'.2
      simpa [mul_assoc] using this
    refine ⟨?_, huB⟩
    by_contra huA
    exact hcon u huB huA hu'.1
  have heq : conjSub x (pCoreOf 2 A ⊓ pCoreOf 2 B) = pCoreOf 2 A ⊓ pCoreOf 2 B :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSub x _).symm)
  exact normalizer_of_le_conjSub heq.symm.le

theorem exists_test_c {A B : Subgroup D} {x : D} (hxB : x ∈ B) (hx3 : x * x * x = 1)
    (hnorm : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    ∃ q ∈ pCoreOf 2 B, q ∈ pCoreOf 2 A ∧ (x * x)⁻¹ * q * (x * x) ∉ pCoreOf 2 A := by
  by_contra hcon
  push Not at hcon
  apply hnorm
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hxx : x * x ∈ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
    apply normalizer_of_le_conjSub
    intro q hq
    exact mem_conjSub.mpr ⟨hcon q hq.2 hq.1, conj_inv_mem_pCoreOf hxxB hq.2⟩
  have hx : x = (x * x) * (x * x) := by
    calc x = (x * x * x) * x := by rw [hx3, one_mul]
      _ = (x * x) * (x * x) := by group
  rw [hx]
  exact Subgroup.mul_mem _ hxx hxx

end Tests

theorem not_mem_conj {A B : Subgroup D} {g q : D} (hgB : g ∈ B)
    (hgN : g ∈ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
    (hq : q ∈ pCoreOf 2 B) (hqA : q ∉ pCoreOf 2 A) : g⁻¹ * q * g ∉ pCoreOf 2 A := by
  intro hmem
  have hR : g⁻¹ * q * g ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := ⟨hmem, conj_inv_mem_pCoreOf hgB hq⟩
  have := (Subgroup.mem_normalizer_iff.mp hgN _).mp hR
  have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
  rw [e] at this
  exact hqA this.1

structure OneSide (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  gold : GoldHyp A B
  nat : IsNaturalAt A (A ⊓ B) z V
  hVQ : V ≤ pCoreOf 2 B
  abel : IsElemAbelian 2 (conjClosure V B)

namespace OneSide

variable [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D} (h : OneSide A B z V)

include h

omit [Finite D] in
theorem U_le_Q_B : conjClosure V B ≤ pCoreOf 2 B :=
  conjClosure_le fun _ hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hg) v).mp (h.hVQ hv)

theorem U_le_T : conjClosure V B ≤ A ⊓ B :=
  (h.U_le_Q_B.trans (h.gold.pCoreOf_right_le)).trans le_rfl

theorem U_le_Q_A : conjClosure V B ≤ pCoreOf 2 A := by
  intro u hu
  rw [← h.nat.centralizer_eq]
  refine ⟨(h.U_le_T hu).1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact (isElemAbelian_comm h.abel (le_conjClosure V B hv) hu)

theorem U_le_R : conjClosure V B ≤ pCoreOf 2 A ⊓ pCoreOf 2 B :=
  le_inf h.U_le_Q_A h.U_le_Q_B

theorem z_mem_center : z ∈ centerOf (pCoreOf 2 B) :=
  ⟨h.gold.centerOf_le_pCoreOf_right h.nat.z_mem,
    Subgroup.centralizer_le h.gold.pCoreOf_right_le h.nat.z_mem.2⟩

theorem conj_conj_z {p q : D} (hp : p ∈ B) (hq : q ∈ pCoreOf 2 B) :
    q * (p * z * p⁻¹) * q⁻¹ = p * z * p⁻¹ := by
  have hc := conj_mem_centerOf' (le_normalizer_pCoreOf 2 B hp) h.z_mem_center
  have := Subgroup.mem_centralizer_iff.mp hc.2 q hq
  calc q * (p * z * p⁻¹) * q⁻¹ = (q * (p * z * p⁻¹)) * q⁻¹ := rfl
    _ = ((p * z * p⁻¹) * q) * q⁻¹ := by rw [this]
    _ = p * z * p⁻¹ := by group

theorem conj_a {q a : D} (hq : q ∈ pCoreOf 2 B) (ha : a ∈ V) (ha1 : a ≠ 1) (haz : a ≠ z) :
    (q ∈ pCoreOf 2 A → q * a * q⁻¹ = a) ∧ (q ∉ pCoreOf 2 A → q * a * q⁻¹ = a * z) := by
  refine ⟨fun hqA => ?_, fun hqA => ?_⟩
  · have := Subgroup.mem_centralizer_iff.mp (h.nat.le_center ha).2 q hqA
    calc q * a * q⁻¹ = (a * q) * q⁻¹ := by rw [this]
      _ = a := by group
  · exact h.nat.conj_eq_mul inf_le_left (h.gold.pCoreOf_right_le hq) hqA ha ha1 haz

theorem conj_d {p q a : D} (hp : p ∈ B) (hq : q ∈ pCoreOf 2 B) (ha : a ∈ V) (ha1 : a ≠ 1)
    (haz : a ≠ z) :
    (p⁻¹ * q * p ∈ pCoreOf 2 A → q * (p * a * p⁻¹) * q⁻¹ = p * a * p⁻¹) ∧
      (p⁻¹ * q * p ∉ pCoreOf 2 A →
        q * (p * a * p⁻¹) * q⁻¹ = (p * a * p⁻¹) * (p * z * p⁻¹)) := by
  have hq' : p⁻¹ * q * p ∈ pCoreOf 2 B := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B (B.inv_mem hp)) q).mp hq
    simpa using this
  have e : q * (p * a * p⁻¹) * q⁻¹ = p * ((p⁻¹ * q * p) * a * (p⁻¹ * q * p)⁻¹) * p⁻¹ := by group
  obtain ⟨h1, h2⟩ := h.conj_a hq' ha ha1 haz
  refine ⟨fun hqA => ?_, fun hqA => ?_⟩
  · rw [e, h1 hqA]
  · rw [e, h2 hqA]; group

theorem card_U_ge_32 {x a : D} (hxB : x ∈ B) (hx3 : x * x * x = 1)
    (hmove : x * z * x⁻¹ ≠ z) (ha : a ∈ V) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hnorm : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    2 ^ 5 ≤ Nat.card ↥(conjClosure V B) := by
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hzV : z ∈ V := h.nat.z_mem_V
  have hcomm : ∀ u u' : ↥(conjClosure V B), u * u' = u' * u := fun u u' =>
    Subtype.ext (isElemAbelian_comm h.abel u.2 u'.2)
  have hsq : ∀ u : ↥(conjClosure V B), u * u = 1 := fun u => by
    apply Subtype.ext
    have := isElemAbelian_pow_eq_one h.abel u.2
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := h.nat.z_ne
  have hcz : ∀ q ∈ pCoreOf 2 B, q * z * q⁻¹ = z := fun q hq => by
    simpa using h.conj_conj_z B.one_mem hq
  have hcx1 : ∀ q ∈ pCoreOf 2 B, q * (x * z * x⁻¹) * q⁻¹ = x * z * x⁻¹ :=
    fun q hq => h.conj_conj_z hxB hq
  have hcx2 : ∀ q ∈ pCoreOf 2 B, q * (x * x * z * (x * x)⁻¹) * q⁻¹ = x * x * z * (x * x)⁻¹ :=
    fun q hq => h.conj_conj_z hxxB hq
  let c₀ : ↥(conjClosure V B) := ⟨z, le_conjClosure V B hzV⟩
  let c₁ : ↥(conjClosure V B) := ⟨x * z * x⁻¹, conj_mem_conjClosure hxB hzV⟩
  let c₂ : ↥(conjClosure V B) := ⟨x * x * z * (x * x)⁻¹, conj_mem_conjClosure hxxB hzV⟩
  let d₀ : ↥(conjClosure V B) := ⟨a, le_conjClosure V B ha⟩
  let d₁ : ↥(conjClosure V B) := ⟨x * a * x⁻¹, conj_mem_conjClosure hxB ha⟩
  let d₂ : ↥(conjClosure V B) := ⟨x * x * a * (x * x)⁻¹, conj_mem_conjClosure hxxB ha⟩
  let τ : (q : D) → q ∈ B → (↥(conjClosure V B) →* ↥(conjClosure V B)) := fun q hq =>
    MonoidHom.mk' (fun u => ⟨q * u * q⁻¹, conj_mem_conjClosure_self hq u.2⟩) (by
      intro u u'
      apply Subtype.ext
      simp [mul_assoc])
  have hτ : ∀ (q : D) (hq : q ∈ B) (u : ↥(conjClosure V B)),
      ((τ q hq u : ↥(conjClosure V B)) : D) = q * u * q⁻¹ := fun _ _ _ => rfl
  have hQB : ∀ q ∈ pCoreOf 2 B, q ∈ B := fun q hq => (h.gold.pCoreOf_right_le hq).2
  obtain ⟨k1, k2, k01, k02, k12⟩ := c_facts hx3 hmove hz1
  have hc0 : c₀ ≠ 1 := fun e => hz1 (congrArg Subtype.val e)
  have hc1 : c₁ ≠ 1 := fun e => k1 (congrArg Subtype.val e)
  have hc2 : c₂ ≠ 1 := fun e => k2 (congrArg Subtype.val e)
  have hc01 : c₀ ≠ c₁ := fun e => k01 (congrArg Subtype.val e)
  have hc02 : c₀ ≠ c₂ := fun e => k02 (congrArg Subtype.val e)
  have hc12 : c₁ ≠ c₂ := fun e => k12 (congrArg Subtype.val e)
  obtain ⟨q₁, hq₁B, hq₁A, hq₁x⟩ := exists_test_b hxB hnorm
  obtain ⟨q₂, hq₂B, hq₂A, hq₂x⟩ := exists_test_a hxB hnorm
  obtain ⟨q₃, hq₃B, hq₃A, hq₃x⟩ := exists_test_c hxB hx3 hnorm
  have da := fun q (hq : q ∈ pCoreOf 2 B) => h.conj_a hq ha ha1 haz
  have db := fun q (hq : q ∈ pCoreOf 2 B) => h.conj_d hxB hq ha ha1 haz
  have dc := fun q (hq : q ∈ pCoreOf 2 B) => h.conj_d hxxB hq ha ha1 haz
  refine card_ge_32_grp hcomm hsq c₀ c₁ c₂ d₀ d₁ d₂ hc0 hc1 hc2 hc02 hc12 hc01
    (τ q₁ (hQB q₁ hq₁B)) (τ q₂ (hQB q₂ hq₂B)) (τ q₃ (hQB q₃ hq₃B)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · exact Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact hcz q₁ hq₁B)
  · exact Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact hcx1 q₁ hq₁B)
  · exact Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact (da q₁ hq₁B).2 hq₁A)
  · exact Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact (db q₁ hq₁B).1 hq₁x)
  · by_cases hm : (x * x)⁻¹ * q₁ * (x * x) ∈ pCoreOf 2 A
    · exact Or.inl (Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact (dc q₁ hq₁B).1 hm))
    · exact Or.inr (Subtype.ext (by rw [hτ q₁ (hQB q₁ hq₁B)]; exact (dc q₁ hq₁B).2 hm))
  · exact Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact hcz q₂ hq₂B)
  · exact Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact hcx1 q₂ hq₂B)
  · exact Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact (da q₂ hq₂B).1 hq₂A)
  · exact Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact (db q₂ hq₂B).2 hq₂x)
  · by_cases hm : (x * x)⁻¹ * q₂ * (x * x) ∈ pCoreOf 2 A
    · exact Or.inl (Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact (dc q₂ hq₂B).1 hm))
    · exact Or.inr (Subtype.ext (by rw [hτ q₂ (hQB q₂ hq₂B)]; exact (dc q₂ hq₂B).2 hm))
  · exact Subtype.ext (by rw [hτ q₃ (hQB q₃ hq₃B)]; exact hcz q₃ hq₃B)
  · exact Subtype.ext (by rw [hτ q₃ (hQB q₃ hq₃B)]; exact hcx1 q₃ hq₃B)
  · exact Subtype.ext (by rw [hτ q₃ (hQB q₃ hq₃B)]; exact (da q₃ hq₃B).1 hq₃A)
  · exact Subtype.ext (by rw [hτ q₃ (hQB q₃ hq₃B)]; exact (dc q₃ hq₃B).2 hq₃x)

theorem card_U_ge_64 {x a : D} (hxB : x ∈ B) (hx3 : x * x * x = 1)
    (hmove : x * z * x⁻¹ ≠ z) (ha : a ∈ V) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hε : z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ≠ 1) {q : D} (hqB : q ∈ pCoreOf 2 B)
    (hq0 : q ∉ pCoreOf 2 A) (hq1 : x⁻¹ * q * x ∉ pCoreOf 2 A)
    (hq2 : (x * x)⁻¹ * q * (x * x) ∉ pCoreOf 2 A) :
    2 ^ 6 ≤ Nat.card ↥(conjClosure V B) := by
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hzV : z ∈ V := h.nat.z_mem_V
  have hcomm : ∀ u u' : ↥(conjClosure V B), u * u' = u' * u := fun u u' =>
    Subtype.ext (isElemAbelian_comm h.abel u.2 u'.2)
  have hsq : ∀ u : ↥(conjClosure V B), u * u = 1 := fun u => by
    apply Subtype.ext
    have := isElemAbelian_pow_eq_one h.abel u.2
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := h.nat.z_ne
  have hcz : q * z * q⁻¹ = z := by simpa using h.conj_conj_z B.one_mem hqB
  have hcx1 : q * (x * z * x⁻¹) * q⁻¹ = x * z * x⁻¹ := h.conj_conj_z hxB hqB
  have hcx2 : q * (x * x * z * (x * x)⁻¹) * q⁻¹ = x * x * z * (x * x)⁻¹ :=
    h.conj_conj_z hxxB hqB
  let c₀ : ↥(conjClosure V B) := ⟨z, le_conjClosure V B hzV⟩
  let c₁ : ↥(conjClosure V B) := ⟨x * z * x⁻¹, conj_mem_conjClosure hxB hzV⟩
  let c₂ : ↥(conjClosure V B) := ⟨x * x * z * (x * x)⁻¹, conj_mem_conjClosure hxxB hzV⟩
  let d₀ : ↥(conjClosure V B) := ⟨a, le_conjClosure V B ha⟩
  let d₁ : ↥(conjClosure V B) := ⟨x * a * x⁻¹, conj_mem_conjClosure hxB ha⟩
  let d₂ : ↥(conjClosure V B) := ⟨x * x * a * (x * x)⁻¹, conj_mem_conjClosure hxxB ha⟩
  have hqB' : q ∈ B := (h.gold.pCoreOf_right_le hqB).2
  let τ : ↥(conjClosure V B) →* ↥(conjClosure V B) :=
    MonoidHom.mk' (fun u => ⟨q * u * q⁻¹, conj_mem_conjClosure_self hqB' u.2⟩) (by
      intro u u'
      apply Subtype.ext
      simp [mul_assoc])
  have hτ : ∀ u : ↥(conjClosure V B), ((τ u : ↥(conjClosure V B)) : D) = q * u * q⁻¹ :=
    fun _ => rfl
  obtain ⟨k1, k2, k01, k02, k12⟩ := c_facts hx3 hmove hz1
  have da := h.conj_a hqB ha ha1 haz
  have db := h.conj_d hxB hqB ha ha1 haz
  have dc := h.conj_d hxxB hqB ha ha1 haz
  refine card_ge_64_grp hcomm hsq c₀ c₁ c₂ d₀ d₁ d₂ (fun e => hz1 (congrArg Subtype.val e))
    (fun e => k1 (congrArg Subtype.val e)) (fun e => k2 (congrArg Subtype.val e))
    (fun e => k01 (congrArg Subtype.val e)) (fun e => k02 (congrArg Subtype.val e))
    (fun e => k12 (congrArg Subtype.val e)) (fun e => hε (congrArg Subtype.val e)) τ ?_ ?_ ?_
    ?_ ?_ ?_
  · exact Subtype.ext (by rw [hτ]; exact hcz)
  · exact Subtype.ext (by rw [hτ]; exact hcx1)
  · exact Subtype.ext (by rw [hτ]; exact hcx2)
  · exact Subtype.ext (by rw [hτ]; exact da.2 hq0)
  · exact Subtype.ext (by rw [hτ]; exact db.2 hq1)
  · exact Subtype.ext (by rw [hτ]; exact dc.2 hq2)

theorem card_T_eq : Nat.card ↥(A ⊓ B) = 4 * Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) := by
  have h4 := h.gold.relIndex_inf_pCoreOf (h.nat.pCoreOf_ne h.gold)
  have hle : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ A ⊓ B := inf_le_left.trans h.gold.pCoreOf_left_le
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 A ⊓ pCoreOf 2 B) (A ⊓ B)
  rw [inf_eq_left.mpr hle, h4] at h1
  exact h1.symm

theorem card_R_ge {x a : D} (hxB : x ∈ B) (hx3 : x * x * x = 1)
    (hmove : x * z * x⁻¹ ≠ z) (ha : a ∈ V) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hcase : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) ∨
      z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ≠ 1) :
    2 ^ 6 ≤ Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) := by
  by_cases hnorm : x ∈ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)
  ·
    have hε : z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ≠ 1 := by
      rcases hcase with h1 | h1
      · exact absurd hnorm h1
      · exact h1
    have hxxB : x * x ∈ B := B.mul_mem hxB hxB
    have hxxN : x * x ∈ Subgroup.normalizer
        ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := Subgroup.mul_mem _ hnorm hnorm
    obtain ⟨q, hqB, hqA⟩ : ∃ q ∈ pCoreOf 2 B, q ∉ pCoreOf 2 A := by
      by_contra hcon
      push Not at hcon
      exact h.gold.not_pCoreOf_right_le_left (h.nat.pCoreOf_ne h.gold) (fun q hq => hcon q hq)
    have hU := h.card_U_ge_64 hxB hx3 hmove ha ha1 haz hε hqB hqA
      (not_mem_conj hxB hnorm hqB hqA) (not_mem_conj hxxB hxxN hqB hqA)
    exact hU.trans (Subgroup.card_le_of_le h.U_le_R)
  · have hU := h.card_U_ge_32 hxB hx3 hmove ha ha1 haz hnorm
    have hUx : conjClosure V B ≤ conjSub x (pCoreOf 2 A ⊓ pCoreOf 2 B) := by
      intro u hu
      refine mem_conjSub.mpr (h.U_le_R ?_)
      have := conj_mem_conjClosure_self (B.inv_mem hxB) hu
      simpa using this
    have hlt : pCoreOf 2 A ⊓ pCoreOf 2 B ⊓ conjSub x (pCoreOf 2 A ⊓ pCoreOf 2 B) <
        pCoreOf 2 A ⊓ pCoreOf 2 B := by
      refine lt_of_le_of_ne inf_le_left fun heq => hnorm ?_
      apply normalizer_of_le_conjSub
      intro r hr
      have : r ∈ pCoreOf 2 A ⊓ pCoreOf 2 B ⊓ conjSub x (pCoreOf 2 A ⊓ pCoreOf 2 B) := by
        rw [heq]; exact hr
      exact this.2
    have h2 := two_mul_card_le_of_lt hlt
    have h3 := Subgroup.card_le_of_le (le_inf h.U_le_R hUx)
    omega

theorem card_T_ge {x a : D} (hxB : x ∈ B) (hx3 : x * x * x = 1)
    (hmove : x * z * x⁻¹ ≠ z) (ha : a ∈ V) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hcase : x ∉ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) ∨
      z * (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ≠ 1) :
    256 ≤ Nat.card ↥(A ⊓ B) := by
  have := h.card_R_ge hxB hx3 hmove ha ha1 haz hcase
  have h4 := h.card_T_eq
  omega

end OneSide


end GoldAmLab2

end F6

end CFSG.Quasithin
