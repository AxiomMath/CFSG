module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WInt
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Red
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WBase

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem two_mul_card_le_of_lt {H K : Subgroup D} (hle : H ≤ K) {k : D} (hk : k ∈ K)
    (hkH : k ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hposK : 0 < Nat.card K := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    have : H = K := Subgroup.eq_of_le_of_card_ge hle (by omega)
    exact hkH (this ▸ hk)
  have : 2 ≤ m := by omega
  nlinarith

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem noACentral_vertex (hA : NoACentral A B) {u : CosetGeom (A ⊔ B) A B}
    (hu : vtype u = false) {c : D} (hcZ : c ∈ centerOf (ballStab 1 u)) (hc2 : c ^ 2 = 1)
    (hfix : ∀ g ∈ stab u, g * c * g⁻¹ = c) : c = 1 := by
  obtain ⟨k, rfl⟩ := exists_smul_eq_γ₀ hu
  rw [ballStab_smul, h.ballStab_one_γ₀_eq] at hcZ
  rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at hfix
  have hcZ1 := Subgroup.mem_inf.mp hcZ
  have hQ : (k : D)⁻¹ * c * k ∈ pCoreOf 2 A := mem_conjSub.mp hcZ1.1
  have hfixA : ∀ a ∈ A, a * ((k : D)⁻¹ * c * k) * a⁻¹ = (k : D)⁻¹ * c * k := by
    intro a ha
    have e : (k : D)⁻¹ * ((k : D) * a * (k : D)⁻¹) * k = a := by group
    have h1 := hfix ((k : D) * a * (k : D)⁻¹) (by rw [mem_conjSub, e]; exact ha)
    calc a * ((k : D)⁻¹ * c * k) * a⁻¹
        = (k : D)⁻¹ * (((k : D) * a * (k : D)⁻¹) * c * ((k : D) * a * (k : D)⁻¹)⁻¹) * k := by
          group
      _ = (k : D)⁻¹ * c * k := by rw [h1]
  have hT : (k : D)⁻¹ * c * k ∈ A ⊓ B := h.gold.pCoreOf_left_le hQ
  have hcen : (k : D)⁻¹ * c * k ∈ centerOf (A ⊓ B) :=
    Subgroup.mem_inf.mpr ⟨hT, Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (mul_inv_eq_iff_eq_mul.mp (hfixA t ht.1))⟩
  have hc2' : ((k : D)⁻¹ * c * k) ^ 2 = 1 := by
    have hcc : c * c = 1 := by rwa [← pow_two]
    rw [pow_two]
    calc (k : D)⁻¹ * c * k * ((k : D)⁻¹ * c * k) = (k : D)⁻¹ * (c * c) * k := by group
      _ = 1 := by rw [hcc]; group
  have h0 := hA _ hcen hc2' hfixA
  have : c = (k : D) * ((k : D)⁻¹ * c * k) * (k : D)⁻¹ := by group
  rw [this, h0]
  group

theorem smul_dichotomy {u a b c : CosetGeom (A ⊔ B) A B} (h1 : (graph (A ⊔ B) A B).Adj u a)
    (h2 : (graph (A ⊔ B) A B).Adj u b) (h3 : (graph (A ⊔ B) A B).Adj u c) (nab : a ≠ b)
    (nac : a ≠ c) (nbc : b ≠ c) {k : ↥(A ⊔ B)} (hk : k • u = u) (hka : k • a = b) :
    (k • b = c ∧ k • c = a) ∨ (k • b = a ∧ k • c = c) := by
  have hadj : ∀ w, (graph (A ⊔ B) A B).Adj u w → (graph (A ⊔ B) A B).Adj u (k • w) := fun w hw => by
    have := (smul_adj k).mpr hw
    rwa [hk] at this
  have hb : (graph (A ⊔ B) A B).Adj u (k • b) := hadj b h2
  have hc : (graph (A ⊔ B) A B).Adj u (k • c) := hadj c h3
  have hinj : ∀ w w' : CosetGeom (A ⊔ B) A B, k • w = k • w' → w = w' := fun w w' e =>
    smul_left_cancel k e
  rcases h.eq_or_eq_of_adj h1 h2 h3 hb nab nac nbc with e | e | e
  ·
    right
    refine ⟨e, ?_⟩
    rcases h.eq_or_eq_of_adj h1 h2 h3 hc nab nac nbc with e' | e' | e'
    · exact absurd (hinj _ _ (e'.trans e.symm)) (Ne.symm nbc)
    · exact absurd (hinj _ _ (e'.trans hka.symm)) (Ne.symm nac)
    · exact e'
  · exact absurd (hinj _ _ (e.trans hka.symm)) (Ne.symm nab)
  · left
    refine ⟨e, ?_⟩
    rcases h.eq_or_eq_of_adj h1 h2 h3 hc nab nac nbc with e' | e' | e'
    · exact e'
    · exact absurd (hinj _ _ (e'.trans hka.symm)) (Ne.symm nac)
    · exact absurd (hinj _ _ (e'.trans e.symm)) (Ne.symm nbc)

omit h [Finite D] in
theorem mem_centralizer_singleton_iff' {g c : D} :
    g ∈ Subgroup.centralizer ({c} : Set D) ↔ g * c * g⁻¹ = c := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem exists_transposition {u β₁ β₂ β₃ : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (h1 : (graph (A ⊔ B) A B).Adj u β₁) (h2 : (graph (A ⊔ B) A B).Adj u β₂)
    (h3 : (graph (A ⊔ B) A B).Adj u β₃) (n12 : β₁ ≠ β₂) (n13 : β₁ ≠ β₃) (n23 : β₂ ≠ β₃) :
    ∃ t : ↥(A ⊔ B), t • u = u ∧ t • β₁ = β₁ ∧ (t : D) ∉ ballStab 1 u ∧ t • β₂ = β₃ ∧
      t • β₃ = β₂ := by
  obtain ⟨t0, ht0, ht0Q⟩ := IsConcreteLE.not_le_iff_exists.1
    (h.not_stab_inf_le_ballStab_one h1 hu)
  let kt : ↥(A ⊔ B) := ⟨t0, stab_le u ht0.1⟩
  have hku : kt • u = u := smul_eq_of_mem_stab ht0.1
  have hk1 : kt • β₁ = β₁ := smul_eq_of_mem_stab ht0.2
  obtain ⟨hne, hadj, hn1⟩ := h.smul_nbr_ne h1 h2 n12 hku hk1 ht0Q
  have h23 : kt • β₂ = β₃ := by
    rcases h.eq_or_eq_of_adj h1 h2 h3 hadj n12 n13 n23 with e | e | e
    · exact absurd e hn1
    · exact absurd e hne
    · exact e
  refine ⟨kt, hku, hk1, ht0Q, h23, ?_⟩
  rcases h.smul_dichotomy h2 h3 h1 n23 n12.symm n13.symm hku h23 with ⟨-, e⟩ | ⟨e, -⟩
  · exact absurd (e.symm.trans hk1) n12.symm
  · exact e

theorem exists_cycle {u β₁ β₂ β₃ : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (h1 : (graph (A ⊔ B) A B).Adj u β₁) (h2 : (graph (A ⊔ B) A B).Adj u β₂)
    (h3 : (graph (A ⊔ B) A B).Adj u β₃) (n12 : β₁ ≠ β₂) (n13 : β₁ ≠ β₃) (n23 : β₂ ≠ β₃) :
    ∃ x : ↥(A ⊔ B), x • u = u ∧ x • β₁ = β₂ ∧ x • β₂ = β₃ ∧ x • β₃ = β₁ := by
  obtain ⟨x0, hx0u, hx0⟩ := exists_stab_smul_eq h1 h2
  rcases h.smul_dichotomy h1 h2 h3 n12 n13 n23 hx0u hx0 with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · exact ⟨x0, hx0u, hx0, e2, e3⟩
  · obtain ⟨t, htu, ht1, -, ht2, ht3⟩ := h.exists_transposition hu h1 h2 h3 n12 n13 n23
    refine ⟨x0 * t, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul, htu, hx0u]
    · rw [mul_smul, ht1, hx0]
    · rw [mul_smul, ht2, e3]
    · rw [mul_smul, ht3, e2]

theorem fix_of_fix_cycle {u β₁ β₂ β₃ : CosetGeom (A ⊔ B) A B}
    (h1 : (graph (A ⊔ B) A B).Adj u β₁) (h2 : (graph (A ⊔ B) A B).Adj u β₂)
    (h3 : (graph (A ⊔ B) A B).Adj u β₃) (n12 : β₁ ≠ β₂) (n13 : β₁ ≠ β₃) (n23 : β₂ ≠ β₃)
    {x t : ↥(A ⊔ B)} (hxu : x • u = u) (hx1 : x • β₁ = β₂) (hx2 : x • β₂ = β₃)
    (htu : t • u = u) (ht1 : t • β₁ = β₁) (htQ : (t : D) ∉ ballStab 1 u) {c : D}
    (hcZ : c ∈ centerOf (ballStab 1 u)) (hxc : (x : D) * c * (x : D)⁻¹ = c)
    (htc : (t : D) * c * (t : D)⁻¹ = c) : ∀ g ∈ stab u, g * c * g⁻¹ = c := by
  have hcQ : ∀ q ∈ ballStab 1 u, q * c * q⁻¹ = c := fun q hq =>
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2 q hq)
  set F := Subgroup.centralizer ({c} : Set D) with hF
  have hQF : ∀ q ∈ ballStab 1 u, q ∈ F := fun q hq =>
    mem_centralizer_singleton_iff'.mpr (hcQ q hq)
  have hxF : (x : D) ∈ F := mem_centralizer_singleton_iff'.mpr hxc
  have htF : (t : D) ∈ F := mem_centralizer_singleton_iff'.mpr htc
  have hT1 : ∀ g ∈ stab u ⊓ stab β₁, g ∈ F := by
    intro g hg
    by_cases hgQ : g ∈ ballStab 1 u
    · exact hQF g hgQ
    · have htmem : (t : D) ∈ stab u ⊓ stab β₁ :=
        ⟨mem_stab_of_smul_eq htu, mem_stab_of_smul_eq ht1⟩
      have hm := h.mul_inv_mem_ballStab_one h1 hg htmem hgQ htQ
      have e : g = (g * (t : D)⁻¹) * t := by group
      rw [e]
      exact F.mul_mem (hQF _ hm) htF
  intro g hg
  rw [← mem_centralizer_singleton_iff']
  let kg : ↥(A ⊔ B) := ⟨g, stab_le u hg⟩
  have hkgu : kg • u = u := smul_eq_of_mem_stab hg
  have hadj : (graph (A ⊔ B) A B).Adj u (kg • β₁) := by
    have := (smul_adj kg).mpr h1
    rwa [hkgu] at this
  have hx3 : x • β₃ = β₁ := by
    rcases h.smul_dichotomy h1 h2 h3 n12 n13 n23 hxu hx1 with ⟨-, e⟩ | ⟨e, -⟩
    · exact e
    · exact absurd (e.symm.trans hx2) n13
  have hxinv : (x : D)⁻¹ ∈ F := F.inv_mem hxF
  rcases h.eq_or_eq_of_adj h1 h2 h3 hadj n12 n13 n23 with e | e | e
  · exact hT1 g ⟨hg, mem_stab_of_smul_eq e⟩
  · have hmem : (((x⁻¹ * kg : ↥(A ⊔ B))) : D) ∈ stab u ⊓ stab β₁ := by
      refine ⟨mem_stab_of_smul_eq ?_, mem_stab_of_smul_eq ?_⟩
      · rw [mul_smul, hkgu, inv_smul_eq_iff.mpr hxu.symm]
      · rw [mul_smul, e, inv_smul_eq_iff.mpr hx1.symm]
    have := hT1 _ hmem
    have e2 : g = (x : D) * (((x⁻¹ * kg : ↥(A ⊔ B))) : D) := by
      show (kg : D) = (x : D) * ((x : D)⁻¹ * (kg : D))
      group
    rw [e2]
    exact F.mul_mem hxF this
  · have hxx : (x * x) • β₁ = β₃ := by rw [mul_smul, hx1, hx2]
    have hmem : ((((x * x)⁻¹ * kg : ↥(A ⊔ B))) : D) ∈ stab u ⊓ stab β₁ := by
      refine ⟨mem_stab_of_smul_eq ?_, mem_stab_of_smul_eq ?_⟩
      · rw [mul_smul, hkgu, inv_smul_eq_iff.mpr (by rw [mul_smul, hxu, hxu])]
      · rw [mul_smul, e, inv_smul_eq_iff.mpr hxx.symm]
    have := hT1 _ hmem
    have e2 : g = ((x : D) * (x : D)) * ((((x * x)⁻¹ * kg : ↥(A ⊔ B))) : D) := by
      show (kg : D) = ((x : D) * (x : D)) * (((x : D) * (x : D))⁻¹ * (kg : D))
      group
    rw [e2]
    exact F.mul_mem (F.mul_mem hxF hxF) this

theorem eq_one_of_cycle (hA : NoACentral A B) {u β₁ β₂ β₃ : CosetGeom (A ⊔ B) A B}
    (hu : vtype u = false) (h1 : (graph (A ⊔ B) A B).Adj u β₁)
    (h2 : (graph (A ⊔ B) A B).Adj u β₂) (h3 : (graph (A ⊔ B) A B).Adj u β₃) (n12 : β₁ ≠ β₂)
    (n13 : β₁ ≠ β₃) (n23 : β₂ ≠ β₃) {x : ↥(A ⊔ B)} (hxu : x • u = u) (hx1 : x • β₁ = β₂)
    (hx2 : x • β₂ = β₃) (hx3 : x • β₃ = β₁) {c : D} (hcZ : c ∈ centerOf (ballStab 1 u))
    (hc2 : c ^ 2 = 1) (hxc : (x : D) * c * (x : D)⁻¹ = c) : c = 1 := by
  obtain ⟨t, htu, ht1, htQ, ht2, ht3⟩ := h.exists_transposition hu h1 h2 h3 n12 n13 n23
  have htu' : (t : D) ∈ stab u := mem_stab_of_smul_eq htu
  have ht1' : (t : D) ∈ stab β₁ := mem_stab_of_smul_eq ht1
  have hwQ : (t : D)⁻¹ * (x : D) * (t : D) * (x : D) ∈ ballStab 1 u := by
    have hti1 : t⁻¹ • β₁ = β₁ := inv_smul_eq_iff.mpr ht1.symm
    have hti3 : t⁻¹ • β₃ = β₂ := inv_smul_eq_iff.mpr ht2.symm
    have hwu : (t⁻¹ * x * t * x) • u = u := by
      rw [mul_smul, mul_smul, mul_smul, hxu, htu, hxu, inv_smul_eq_iff.mpr htu.symm]
    have hw1 : (t⁻¹ * x * t * x) • β₁ = β₁ := by
      rw [mul_smul, mul_smul, mul_smul, hx1, ht2, hx3, hti1]
    have hw2 : (t⁻¹ * x * t * x) • β₂ = β₂ := by
      rw [mul_smul, mul_smul, mul_smul, hx2, ht3, hx2, hti3]
    exact h.mem_ballStab_one_of_fix_two' h1 h2 n12 (mem_stab_of_smul_eq hwu)
      (mem_stab_of_smul_eq hw1) (mem_stab_of_smul_eq hw2)
  have hT2 : (t : D) * t ∈ ballStab 1 u := h.sq_mem_ballStab_one_of_adj h1 htu' ht1'
  have hcQ : ∀ q ∈ ballStab 1 u, q * c * q⁻¹ = c := fun q hq =>
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2 q hq)
  have hcomm : ∀ a ∈ centerOf (ballStab 1 u), ∀ b ∈ centerOf (ballStab 1 u), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 b
      (Subgroup.mem_inf.mp hb).1).symm
  have hXc : (x : D)⁻¹ * c * (x : D) = c := by
    have e : c = (x : D)⁻¹ * ((x : D) * c * (x : D)⁻¹) * x := by group
    rw [hxc] at e
    exact e.symm
  have hdZ : (t : D) * c * (t : D)⁻¹ ∈ centerOf (ballStab 1 u) :=
    conj_mem_centerOf' (le_normalizer_ballStab 1 u htu') hcZ
  have hxd : (x : D) * ((t : D) * c * (t : D)⁻¹) * (x : D)⁻¹ = (t : D) * c * (t : D)⁻¹ := by
    have hWc := hcQ _ hwQ
    calc (x : D) * ((t : D) * c * (t : D)⁻¹) * (x : D)⁻¹
        = (t : D) * (((t : D)⁻¹ * x * t) * c * ((t : D)⁻¹ * x * t)⁻¹) * (t : D)⁻¹ := by group
      _ = (t : D) * ((((t : D)⁻¹ * x * t * x) * (x : D)⁻¹) * c *
            (((t : D)⁻¹ * x * t * x) * (x : D)⁻¹)⁻¹) * (t : D)⁻¹ := by group
      _ = (t : D) * (((t : D)⁻¹ * x * t * x) * ((x : D)⁻¹ * c * x) *
            ((t : D)⁻¹ * x * t * x)⁻¹) * (t : D)⁻¹ := by group
      _ = (t : D) * (((t : D)⁻¹ * x * t * x) * c * ((t : D)⁻¹ * x * t * x)⁻¹) * (t : D)⁻¹ := by
          rw [hXc]
      _ = (t : D) * c * (t : D)⁻¹ := by rw [hWc]
  have hc'Z : c * ((t : D) * c * (t : D)⁻¹) ∈ centerOf (ballStab 1 u) :=
    (centerOf (ballStab 1 u)).mul_mem hcZ hdZ
  have hcc : c * c = 1 := by rwa [← pow_two]
  have hdd : ((t : D) * c * (t : D)⁻¹) * ((t : D) * c * (t : D)⁻¹) = 1 := by
    calc ((t : D) * c * (t : D)⁻¹) * ((t : D) * c * (t : D)⁻¹) = (t : D) * (c * c) * (t : D)⁻¹ := by
          group
      _ = 1 := by rw [hcc]; group
  have hcd : c * ((t : D) * c * (t : D)⁻¹) = ((t : D) * c * (t : D)⁻¹) * c := hcomm _ hcZ _ hdZ
  have hc'2 : (c * ((t : D) * c * (t : D)⁻¹)) ^ 2 = 1 := by
    rw [pow_two]
    calc c * ((t : D) * c * (t : D)⁻¹) * (c * ((t : D) * c * (t : D)⁻¹))
        = c * (((t : D) * c * (t : D)⁻¹) * c) * ((t : D) * c * (t : D)⁻¹) := by group
      _ = c * (c * ((t : D) * c * (t : D)⁻¹)) * ((t : D) * c * (t : D)⁻¹) := by rw [hcd]
      _ = (c * c) * (((t : D) * c * (t : D)⁻¹) * ((t : D) * c * (t : D)⁻¹)) := by group
      _ = 1 := by rw [hcc, hdd]; group
  have hxc' : (x : D) * (c * ((t : D) * c * (t : D)⁻¹)) * (x : D)⁻¹ =
      c * ((t : D) * c * (t : D)⁻¹) := by
    calc (x : D) * (c * ((t : D) * c * (t : D)⁻¹)) * (x : D)⁻¹
        = ((x : D) * c * (x : D)⁻¹) * ((x : D) * ((t : D) * c * (t : D)⁻¹) * (x : D)⁻¹) := by
          group
      _ = c * ((t : D) * c * (t : D)⁻¹) := by rw [hxc, hxd]
  have htc' : (t : D) * (c * ((t : D) * c * (t : D)⁻¹)) * (t : D)⁻¹ =
      c * ((t : D) * c * (t : D)⁻¹) := by
    have hTT : (t : D) * (t : D) * c * ((t : D) * (t : D))⁻¹ = c := hcQ _ hT2
    calc (t : D) * (c * ((t : D) * c * (t : D)⁻¹)) * (t : D)⁻¹
        = ((t : D) * c * (t : D)⁻¹) * ((t : D) * (t : D) * c * ((t : D) * (t : D))⁻¹) := by group
      _ = ((t : D) * c * (t : D)⁻¹) * c := by rw [hTT]
      _ = c * ((t : D) * c * (t : D)⁻¹) := hcd.symm
  have hfix' := h.fix_of_fix_cycle h1 h2 h3 n12 n13 n23 hxu hx1 hx2 htu ht1 htQ hc'Z hxc' htc'
  have h0 := h.noACentral_vertex hA hu hc'Z hc'2 hfix'
  have hdc : (t : D) * c * (t : D)⁻¹ = c := by
    have e1 : (t : D) * c * (t : D)⁻¹ = c⁻¹ := eq_inv_of_mul_eq_one_right h0
    rw [e1]
    exact inv_eq_of_mul_eq_one_right hcc
  have hfix := h.fix_of_fix_cycle h1 h2 h3 n12 n13 n23 hxu hx1 hx2 htu ht1 htQ hcZ hxc hdc
  exact h.noACentral_vertex hA hu hcZ hc2 hfix

omit [Finite D] in
theorem conj_mem_Vv (k : ↥(A ⊔ B)) {w b : CosetGeom (A ⊔ B) A B} {a : D} (ha : a ∈ Vv V w)
    (hkw : k • w = b) : (k : D) * a * (k : D)⁻¹ ∈ Vv V b := by
  rw [← hkw, h.Vv_smul' k w]
  exact mul_mem_conjSub ha

theorem Vv_ne_of_adj {u β₁ β₂ : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (h1 : (graph (A ⊔ B) A B).Adj u β₁) (h2 : (graph (A ⊔ B) A B).Adj u β₂) (n12 : β₁ ≠ β₂) :
    Vv V β₁ ≠ Vv V β₂ := by
  intro hVV
  apply h.not_stab_le_normalizer_Vv h1 hu
  rw [← h.sup_stab_inf_eq hu h1 h2 n12]
  refine sup_le ?_ ?_
  · exact inf_le_right.trans (stab_le_normalizer_Vv h.natural.reduced.2.1 β₁)
  · refine inf_le_right.trans ?_
    have := stab_le_normalizer_Vv h.natural.reduced.2.1 β₂ (V := V)
    rwa [← hVV] at this

theorem mem_Vv_of_mem_inf (hA : NoACentral A B) (hU16 : Nat.card (conjClosure V B) = 16)
    {u β₁ β₂ : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (h1 : (graph (A ⊔ B) A B).Adj u β₁) (h2 : (graph (A ⊔ B) A B).Adj u β₂) (n12 : β₁ ≠ β₂)
    {y : D} (hyZ : y ∈ centerOf (ballStab 1 u)) (hy1 : y ∈ Vv V β₁) (hy2 : y ∈ Vv V β₂) :
    y ∈ Vv V u := by
  by_contra hyV
  obtain ⟨β₃, h3, n31, n32⟩ := h.exists_third (w := u) n12
  have n13 : β₁ ≠ β₃ := n31.symm
  have n23 : β₂ ≠ β₃ := n32.symm
  obtain ⟨x, hxu, hx1, hx2, hx3⟩ := h.exists_cycle hu h1 h2 h3 n12 n13 n23
  have hxD : (x : D) ∈ stab u := mem_stab_of_smul_eq hxu
  have hxN : (x : D) ∈ Subgroup.normalizer (ballStab 1 u : Set D) :=
    le_normalizer_ballStab 1 u hxD
  have t1 : vtype β₁ = true := vtype_eq_true_of_adj h1 hu
  have t2 : vtype β₂ = true := vtype_eq_true_of_adj h2 hu
  have t3 : vtype β₃ = true := vtype_eq_true_of_adj h3 hu
  set y₂ : D := (x : D) * y * (x : D)⁻¹ with hy₂
  set y₃ : D := (x : D) * y₂ * (x : D)⁻¹ with hy₃
  have hy₂Z : y₂ ∈ centerOf (ballStab 1 u) := conj_mem_centerOf' hxN hyZ
  have hy₃Z : y₃ ∈ centerOf (ballStab 1 u) := conj_mem_centerOf' hxN hy₂Z
  have hy₂2 : y₂ ∈ Vv V β₂ := h.conj_mem_Vv x hy1 hx1
  have hy₂3 : y₂ ∈ Vv V β₃ := h.conj_mem_Vv x hy2 hx2
  have hy₃3 : y₃ ∈ Vv V β₃ := h.conj_mem_Vv x hy₂2 hx2
  have hy₃1 : y₃ ∈ Vv V β₁ := h.conj_mem_Vv x hy₂3 hx3
  have hab1 := h.elemAbelian_Vv_B (V := V) t1
  have hyy : y * y = 1 := by rw [← pow_two]; exact hab1.2 y hy1
  have hy₂y₂ : y₂ * y₂ = 1 := by
    calc y₂ * y₂ = (x : D) * (y * y) * (x : D)⁻¹ := by rw [hy₂]; group
      _ = 1 := by rw [hyy]; group
  have hy₃y₃ : y₃ * y₃ = 1 := by
    calc y₃ * y₃ = (x : D) * (y₂ * y₂) * (x : D)⁻¹ := by rw [hy₃]; group
      _ = 1 := by rw [hy₂y₂]; group
  have hcomm : ∀ a ∈ centerOf (ballStab 1 u), ∀ b ∈ centerOf (ballStab 1 u), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 b
      (Subgroup.mem_inf.mp hb).1).symm
  have hx3Q : (x : D) * (x : D) * (x : D) ∈ ballStab 1 u := by
    have hu3 : (x * x * x) • u = u := by rw [mul_smul, mul_smul, hxu, hxu, hxu]
    have h31 : (x * x * x) • β₁ = β₁ := by rw [mul_smul, mul_smul, hx1, hx2, hx3]
    have h32 : (x * x * x) • β₂ = β₂ := by
      rw [mul_smul, mul_smul, hx2, hx3, hx1]
    exact h.mem_ballStab_one_of_fix_two' h1 h2 n12 (mem_stab_of_smul_eq hu3)
      (mem_stab_of_smul_eq h31) (mem_stab_of_smul_eq h32)
  have hyx3 : (x : D) * y₃ * (x : D)⁻¹ = y := by
    have hcen := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyZ).2 _ hx3Q
    calc (x : D) * y₃ * (x : D)⁻¹
        = ((x : D) * (x : D) * (x : D)) * y * ((x : D) * (x : D) * (x : D))⁻¹ := by
          rw [hy₃, hy₂]; group
      _ = y := mul_inv_eq_iff_eq_mul.mpr hcen
  have he₀Z : y * y₂ * y₃ ∈ centerOf (ballStab 1 u) :=
    (centerOf (ballStab 1 u)).mul_mem ((centerOf (ballStab 1 u)).mul_mem hyZ hy₂Z) hy₃Z
  have h23 : y₂ * y₃ = y₃ * y₂ := hcomm _ hy₂Z _ hy₃Z
  have h12 : y * y₂ = y₂ * y := hcomm _ hyZ _ hy₂Z
  have h13 : y * y₃ = y₃ * y := hcomm _ hyZ _ hy₃Z
  have he₀2 : (y * y₂ * y₃) ^ 2 = 1 := by
    rw [pow_two]
    calc y * y₂ * y₃ * (y * y₂ * y₃) = y * y₂ * (y₃ * y) * y₂ * y₃ := by group
      _ = y * y₂ * (y * y₃) * y₂ * y₃ := by rw [h13]
      _ = y * (y₂ * y) * y₃ * y₂ * y₃ := by group
      _ = y * (y * y₂) * y₃ * y₂ * y₃ := by rw [h12]
      _ = (y * y) * (y₂ * (y₃ * y₂) * y₃) := by group
      _ = (y * y) * (y₂ * (y₂ * y₃) * y₃) := by rw [h23]
      _ = (y * y) * ((y₂ * y₂) * (y₃ * y₃)) := by group
      _ = 1 := by rw [hyy, hy₂y₂, hy₃y₃]; group
  have hxe₀ : (x : D) * (y * y₂ * y₃) * (x : D)⁻¹ = y * y₂ * y₃ := by
    calc (x : D) * (y * y₂ * y₃) * (x : D)⁻¹
        = ((x : D) * y * (x : D)⁻¹) * ((x : D) * y₂ * (x : D)⁻¹) * ((x : D) * y₃ * (x : D)⁻¹) := by
          group
      _ = y₂ * y₃ * y := by rw [← hy₂, ← hy₃, hyx3]
      _ = y * y₂ * y₃ := by
          calc y₂ * y₃ * y = y₂ * (y₃ * y) := by group
            _ = y₂ * (y * y₃) := by rw [h13]
            _ = (y₂ * y) * y₃ := by group
            _ = (y * y₂) * y₃ := by rw [h12]
  have he₀ : y * y₂ * y₃ = 1 :=
    h.eq_one_of_cycle hA hu h1 h2 h3 n12 n13 n23 hxu hx1 hx2 hx3 he₀Z he₀2 hxe₀
  have hya : y * y₂ = y₃ := by
    calc y * y₂ = y * y₂ * (y₃ * y₃) := by rw [hy₃y₃, mul_one]
      _ = (y * y₂ * y₃) * y₃ := by group
      _ = y₃ := by rw [he₀, one_mul]
  have hyb : y * y₃ = y₂ := by
    calc y * y₃ = y * (y * y₂) := by rw [hya]
      _ = (y * y) * y₂ := by group
      _ = y₂ := by rw [hyy, one_mul]
  have hy₂1 : y₂ ∈ Vv V β₁ := by rw [← hyb]; exact (Vv V β₁).mul_mem hy1 hy₃1
  have hy₃2 : y₃ ∈ Vv V β₂ := by rw [← hya]; exact (Vv V β₂).mul_mem hy2 hy₂2
  have hNV : (x : D) ∈ Subgroup.normalizer (Vv V u : Set D) :=
    stab_le_normalizer_Vv h.natural.reduced.2.1 u hxD
  have hy₂V : y₂ ∉ Vv V u := fun hm => hyV ((Subgroup.mem_normalizer_iff.mp hNV y).mpr hm)
  have hy₃V : y₃ ∉ Vv V u := fun hm => hy₂V ((Subgroup.mem_normalizer_iff.mp hNV y₂).mpr hm)
  have hVu1 : Vv V u ≤ Vv V β₁ := Vv_le_Vv_of_adj h1 hu
  have hVu2 : Vv V u ≤ Vv V β₂ := Vv_le_Vv_of_adj h2 hu
  have hnorm : Vv V u ≤ Subgroup.normalizer (Subgroup.zpowers y : Set D) := fun v hv =>
    mem_normalizer_zpowers_of_mul_comm (isElemAbelian_comm hab1 (hVu1 hv) hy1)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Vv V u) (Subgroup.zpowers y) hnorm
  have hy₂P : y₂ ∉ Vv V u ⊔ Subgroup.zpowers y := by
    intro hm
    have hm' : y₂ ∈ ((Vv V u ⊔ Subgroup.zpowers y : Subgroup D) : Set D) := hm
    rw [hset] at hm'
    obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_mul.mp hm'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases zpow_eq_one_or_self (hab1.2 y hy1) k with hk | hk
    · rw [hk, mul_one] at hvw
      exact hy₂V (hvw ▸ hv)
    · rw [hk] at hvw
      have hvy : v * y = y * v := isElemAbelian_comm hab1 (hVu1 hv) hy1
      have e : y₃ = v := by
        calc y₃ = y * y₂ := hya.symm
          _ = y * (v * y) := by rw [hvw]
          _ = y * (y * v) := by rw [hvy]
          _ = (y * y) * v := by group
          _ = v := by rw [hyy, one_mul]
      exact hy₃V (e ▸ hv)
  have hy1P : y ∈ Vv V u ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hy₂Q : y₂ ∈ Vv V u ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers y₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  have hc1 := two_mul_card_le_of_lt (le_sup_left : Vv V u ≤ Vv V u ⊔ Subgroup.zpowers y) hy1P hyV
  have hc2 := two_mul_card_le_of_lt
    (le_sup_left : Vv V u ⊔ Subgroup.zpowers y ≤ Vv V u ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers y₂)
    hy₂Q hy₂P
  rw [h.card_Vv_A hu] at hc1
  have hQ1 : Vv V u ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers y₂ ≤ Vv V β₁ :=
    sup_le (sup_le hVu1 (Subgroup.zpowers_le.mpr hy1)) (Subgroup.zpowers_le.mpr hy₂1)
  have hQ2 : Vv V u ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers y₂ ≤ Vv V β₂ :=
    sup_le (sup_le hVu2 (Subgroup.zpowers_le.mpr hy2)) (Subgroup.zpowers_le.mpr hy₂2)
  have hcard1 := h.card_Vv_B_of hU16 t1
  have hcard2 := h.card_Vv_B_of hU16 t2
  have e1 := Subgroup.eq_of_le_of_card_ge hQ1 (by omega)
  have e2 := Subgroup.eq_of_le_of_card_ge hQ2 (by omega)
  exact h.Vv_ne_of_adj hu h1 h2 n12 (e1.symm.trans e2)

theorem inf_Vv_le_Vv_of_adj_of_noACentral (hA : NoACentral A B)
    (hU16 : Nat.card (conjClosure V B) = 16) {u β β' : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hβ : (graph (A ⊔ B) A B).Adj u β) (hβ' : (graph (A ⊔ B) A B).Adj u β') (hne : β ≠ β') :
    Vv V β ⊓ Vv V β' ≤ Vv V u := by
  intro x hx
  by_contra hxu
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hu
  have hβ't : vtype β' = true := vtype_eq_true_of_adj hβ' hu
  have hUβ : Nat.card (Vv V β) = 16 := h.card_Vv_B_of_card hU16 hβt
  have hUβ' : Nat.card (Vv V β') = 16 := h.card_Vv_B_of_card hU16 hβ't
  obtain ⟨n, hn⟩ : ∃ n, critDist (A ⊔ B) A B V = n + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by have := h.three_le_critDist; omega⟩
  have hn2 : 2 ≤ n := by have := h.three_le_critDist; omega
  have hd1 : CosetGeom.dist β u + 1 ≤ n := by
    rw [dist_eq_one_iff_adj.mpr hβ.symm]
    omega
  have hd1' : CosetGeom.dist β' u + 1 ≤ n := by
    rw [dist_eq_one_iff_adj.mpr hβ'.symm]
    omega
  have hUQ : Vv V β ≤ ballStab 1 u := h.VvB_le_ballStab_one_of_dist hn hβt hd1
  have hUQ' : Vv V β' ≤ ballStab 1 u := h.VvB_le_ballStab_one_of_dist hn hβ't hd1'
  have hQβ : ∀ q ∈ ballStab 1 u, q ∈ stab u ⊓ stab β := fun q hq =>
    ⟨ballStab_le_stab 1 u hq, ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr hβ).le hq⟩
  have hQβ' : ∀ q ∈ ballStab 1 u, q ∈ stab u ⊓ stab β' := fun q hq =>
    ⟨ballStab_le_stab 1 u hq, ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr hβ').le hq⟩
  have hab := h.isElemAbelian_Vv_B (V := V) hβt
  have hx2 : x ^ 2 = 1 := hab.2 x hx.1
  by_cases hc : ∀ q ∈ ballStab 1 u, q * x * q⁻¹ = x
  · have hxZ : x ∈ centerOf (ballStab 1 u) :=
      Subgroup.mem_inf.mpr ⟨hUQ hx.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
        mul_inv_eq_iff_eq_mul.mp (hc q hq)⟩
    exact hxu (h.mem_Vv_of_mem_inf hA hU16 hu hβ hβ' hne hxZ hx.1 hx.2)
  · push Not at hc
    obtain ⟨q, hq, hqx⟩ := hc
    set f := q * x * q⁻¹ * x⁻¹ with hf
    have hf1 : f ≠ 1 := fun e => hqx (mul_inv_eq_one.mp e)
    have hfβ : f ∈ Theta z V u β := comm_mem_Theta (hQβ q hq) hx.1 z
    have hfβ' : f ∈ Theta z V u β' := comm_mem_Theta (hQβ' q hq) hx.2 z
    have hbot := h.inf_Zv_eq_bot hu hβ hβ' hne
    have hfc : ∀ q' ∈ ballStab 1 u, q' * f * q'⁻¹ = f := fun q' hq' => by
      have h1 := h.comm_Theta_le_Zv hu hβ (hQβ q' hq') hfβ
      have h2 := h.comm_Theta_le_Zv hu hβ' (hQβ' q' hq') hfβ'
      have h3 : q' * f * q'⁻¹ * f⁻¹ ∈ Zv z β ⊓ Zv z β' := ⟨h1, h2⟩
      rw [hbot] at h3
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
    have hfU : f ∈ Vv V β := h.Theta_le_Vv hu hβ hfβ
    have hfU' : f ∈ Vv V β' := h.Theta_le_Vv hu hβ' hfβ'
    have hfZ : f ∈ centerOf (ballStab 1 u) :=
      Subgroup.mem_inf.mpr ⟨hUQ hfU, Subgroup.mem_centralizer_iff.mpr fun q' hq' =>
        mul_inv_eq_iff_eq_mul.mp (hfc q' hq')⟩
    have hfV : f ∈ Vv V u := h.mem_Vv_of_mem_inf hA hU16 hu hβ hβ' hne hfZ hfU hfU'
    have hm1 : f ∈ Zv z β := by
      have hmem : f ∈ Theta z V u β ⊓ Vv V u := ⟨hfβ, hfV⟩
      rwa [h.Theta_inf_Vv hu hβ hUβ] at hmem
    have hm2 : f ∈ Zv z β' := by
      have hmem : f ∈ Theta z V u β' ⊓ Vv V u := ⟨hfβ', hfV⟩
      rwa [h.Theta_inf_Vv hu hβ' hUβ'] at hmem
    have h3 : f ∈ Zv z β ⊓ Zv z β' := ⟨hm1, hm2⟩
    rw [hbot] at h3
    exact hf1 (Subgroup.mem_bot.mp h3)

theorem I1_of_noACentral (hA : NoACentral A B) (hU16 : Nat.card (conjClosure V B) = 16) :
    ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false → (graph (A ⊔ B) A B).Adj u β →
      (graph (A ⊔ B) A B).Adj u β' → β ≠ β' → Vv V β ⊓ Vv V β' ≤ Vv V u :=
  fun _ _ _ hu hβ hβ' hne => h.inf_Vv_le_Vv_of_adj_of_noACentral hA hU16 hu hβ hβ' hne

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
