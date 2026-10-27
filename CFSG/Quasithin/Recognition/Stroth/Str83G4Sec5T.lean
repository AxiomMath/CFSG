module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Fpf
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_trivial_on_sup_right
    (hfr : Str83G4Frame L1 L2 S a) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hk : ∀ l ∈ L2, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) :
    ∀ x ∈ L2 ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ Q2 L1 L2 S := by
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [bigB_comm]
    exact bigB_le_normalizer_of_hyp111 hF.1.symm
  have hQ2NL2 : Q2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (pCoreOf_le 2 (P2 L1 L2 S)).trans (sup_le Subgroup.le_normalizer hBL2)
  have hBNQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hL2NQ2 : L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hO2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm
    rw [show pCoreOf 2 (L2 ⊔ bigB L2 L1 S) = Q1 L2 L1 S from rfl, hQ] at h
    exact h
  intro x hx
  have hx' : x ∈ L2 ⊔ Q2 L1 L2 S := by rwa [sup_eq_of_S_eq_right hS2] at hx
  obtain ⟨l, hl, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2NL2).mp hx'
  have hkl : k * l * k⁻¹ * l⁻¹ ∈ Q2 L1 L2 S := hO2 (hk l hl)
  have hkq : k * q * k⁻¹ * q⁻¹ ∈ Q2 L1 L2 S :=
    (Q2 L1 L2 S).mul_mem ((Subgroup.mem_normalizer_iff.mp (hBNQ2 hkB) q).mp hq)
      ((Q2 L1 L2 S).inv_mem hq)
  have hconj : l * (k * q * k⁻¹ * q⁻¹) * l⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hL2NQ2 hl) _).mp hkq
  have e : k * (l * q) * k⁻¹ * (l * q)⁻¹ =
      (k * l * k⁻¹ * l⁻¹) * (l * (k * q * k⁻¹ * q⁻¹) * l⁻¹) := by
    group
  rw [e]
  exact (Q2 L1 L2 S).mul_mem hkl hconj

theorem str83G4Data_sup_le_bigB (d : Str83G4Data L1 L2 S) : d.D1 ⊔ d.D2 ≤ bigB L1 L2 S := by
  rw [d.hBsplit, sup_assoc]
  exact le_sup_right

theorem str83G4_eq_one_of_fix_z2
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hstep : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    {x δ : G} (hx : x ∈ d.D1) (hδ : δ ∈ d.D2) (hδ1 : δ ≠ 1)
    (hxδ : ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2)
    {v : G} (hv : v ∈ Z2 L1 L2 S) (hfix : (x * δ⁻¹) * v * (x * δ⁻¹)⁻¹ = v) : v = 1 := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  set h : G := x * δ⁻¹ with hhdef
  have hhB : h ∈ bigB L1 L2 S :=
    str83G4Data_sup_le_bigB d ((d.D1 ⊔ d.D2).mul_mem (Subgroup.mem_sup_left hx)
      ((d.D1 ⊔ d.D2).inv_mem (Subgroup.mem_sup_right hδ)))
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hHZ2 : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have htriv := str83G4_trivial_on_sup_right hfr' hhB hxδ
  have hCn : IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S)
      (Z2 L1 L2 S ⊓ Subgroup.centralizer ({h} : Set G)) := by
    refine ⟨inf_le_left, fun g hg y hy => ?_⟩
    obtain ⟨hyZ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hgy : g * y * g⁻¹ ∈ Z2 L1 L2 S := (Subgroup.mem_normalizer_iff.mp (hHZ2 hg) y).mp hyZ
    refine Subgroup.mem_inf.mpr ⟨hgy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyh : y * h = h * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hc : h * g * h⁻¹ * g⁻¹ ∈ Q2 L1 L2 S := htriv g hg
    have hcz : (h * g * h⁻¹ * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (h * g * h⁻¹ * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hQ2C hc) _ hgy).symm
    have hy' : h⁻¹ * y * h = y := by rw [mul_assoc, hyh]; group
    have e : h * (g * y * g⁻¹) * h⁻¹ = g * y * g⁻¹ := by
      calc h * (g * y * g⁻¹) * h⁻¹ = h * g * (h⁻¹ * y * h) * g⁻¹ * h⁻¹ := by rw [hy']; group
        _ = (h * g * h⁻¹ * g⁻¹) * (g * y * g⁻¹) * (h * g * h⁻¹ * g⁻¹)⁻¹ := by group
        _ = g * y * g⁻¹ := by rw [hcz]; group
    calc g * y * g⁻¹ * h = (h * (g * y * g⁻¹) * h⁻¹) * h := by rw [e]
      _ = h * (g * y * g⁻¹) := by group
  rcases hstep.2.2.2 _ hCn bot_le inf_le_left with hC | hC
  ·
    have hvC : v ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer ({h} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc v * h = (h * v * h⁻¹) * h := by rw [hfix]
        _ = h * v := by group
    rw [hC] at hvC
    exact Subgroup.mem_bot.mp hvC
  ·
    exfalso
    refine hδ1 (str83G4_torusFaithful hfr' δ (d.hD2hall.1 hδ)
      (Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hδ)) fun z hz => ?_)
    rw [← hZ1eq] at hz
    have hzC : z ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer ({h} : Set G) := by
      rw [hC]
      exact hZ1Z2 hz
    have hzh : Commute z h :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hzC).2
    have hxL1 : x ∈ L1 ⊔ Q1 L1 L2 S :=
      Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 hx))
    have hzx : Commute z x := Subgroup.mem_centralizer_iff.mp (hZI hxL1) z hz
    have hδeq : δ = h⁻¹ * x := by rw [hhdef]; group
    rw [hδeq]
    exact ((hzh.inv_right).mul_right hzx).symm.eq

theorem str83G4_exists_fpf_x
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hD1I : ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1) :
    ∃ k ∈ d.D1 ⊔ d.D2, (∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) ∧
      ∀ y ∈ str83X L1 L2 S, k * y * k⁻¹ * y⁻¹ ∈ Z1 L1 L2 S → y ∈ Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨d₂, hd₂, hd₂1⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D2).resolve_left (str83G4Data_D2_ne_bot hfr d)
  obtain ⟨δ, hδ, hδL⟩ := d.hdelta d₂ hd₂
  have hkH : d₂ * δ⁻¹ ∈ d.D1 ⊔ d.D2 :=
    (d.D1 ⊔ d.D2).mul_mem (Subgroup.mem_sup_right hd₂)
      ((d.D1 ⊔ d.D2).inv_mem (Subgroup.mem_sup_left hδ))
  refine ⟨d₂ * δ⁻¹, hkH, hδL, ?_⟩
  intro y₀ hy₀X hy₀k
  by_contra hy₀Z
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  set k : G := d₂ * δ⁻¹ with hkdef
  have hkB : k ∈ bigB L1 L2 S := str83G4Data_sup_le_bigB d hkH
  have hkP1 : k ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hkB
  have hNX : P1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    le_normalizer_str83X L1 L2 S
  have hNZ1 : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr'
  have hXP1 : str83X L1 L2 S ≤ P1 L1 L2 S := hXQ1.trans (pCoreOf_le 2 (P1 L1 L2 S))
  have hZ1X : Z1 L1 L2 S ≤ str83X L1 L2 S := hZ1Z2.trans (z2_le_str83X L1 L2 S)
  have hcommXQ1 := str83G4_commutator_x_q1_le hfr'
  have hkX : ∀ y, y ∈ str83X L1 L2 S → k * y * k⁻¹ ∈ str83X L1 L2 S := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNX hkP1) y).mp hy
  have hconjZ1 : ∀ g ∈ P1 L1 L2 S, ∀ z ∈ Z1 L1 L2 S, g * z * g⁻¹ ∈ Z1 L1 L2 S :=
    fun g hg z hz => (Subgroup.mem_normalizer_iff.mp (hNZ1 hg) z).mp hz
  let F : Subgroup G :=
    { carrier := {y | y ∈ str83X L1 L2 S ∧ k * y * k⁻¹ * y⁻¹ ∈ Z1 L1 L2 S}
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁X, h₁⟩ ⟨h₂X, h₂⟩
        refine ⟨(str83X L1 L2 S).mul_mem h₁X h₂X, ?_⟩
        have e : k * (y₁ * y₂) * k⁻¹ * (y₁ * y₂)⁻¹ =
            (k * y₁ * k⁻¹ * y₁⁻¹) * (y₁ * (k * y₂ * k⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact (Z1 L1 L2 S).mul_mem h₁ (hconjZ1 _ (hXP1 h₁X) _ h₂)
      one_mem' := ⟨(str83X L1 L2 S).one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hyX, hy⟩
        refine ⟨(str83X L1 L2 S).inv_mem hyX, ?_⟩
        have e : k * y⁻¹ * k⁻¹ * y⁻¹⁻¹ = y⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hconjZ1 _ (hXP1 ((str83X L1 L2 S).inv_mem hyX)) _ ((Z1 L1 L2 S).inv_mem hy) }
  have hmemF : ∀ y, y ∈ F ↔ y ∈ str83X L1 L2 S ∧ k * y * k⁻¹ * y⁻¹ ∈ Z1 L1 L2 S :=
    fun _ => Iff.rfl
  have hFn : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) F := by
    refine ⟨fun y hy => ((hmemF y).mp hy).1, fun g hg y hy => ?_⟩
    obtain ⟨hyX, hy⟩ := (hmemF y).mp hy
    have hgP1 : g ∈ P1 L1 L2 S := sup_left_le_p1 L1 L2 S hg
    have hgy : g * y * g⁻¹ ∈ str83X L1 L2 S := (Subgroup.mem_normalizer_iff.mp (hNX hgP1) y).mp hyX
    refine (hmemF _).mpr ⟨hgy, ?_⟩
    have hc : k * g * k⁻¹ * g⁻¹ ∈ Q1 L1 L2 S := str83G4_trivial_on_sup hfr' hkB hδL g hg
    have hcP1 : k * g * k⁻¹ * g⁻¹ ∈ P1 L1 L2 S := pCoreOf_le 2 (P1 L1 L2 S) hc
    have hcomm : k * g * k⁻¹ * g⁻¹ * (g * y * g⁻¹) * (k * g * k⁻¹ * g⁻¹)⁻¹ *
        (g * y * g⁻¹)⁻¹ ∈ Z1 L1 L2 S := by
      refine hcommXQ1 ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hc hgy
    have e : k * (g * y * g⁻¹) * k⁻¹ * (g * y * g⁻¹)⁻¹ =
        ((k * g * k⁻¹ * g⁻¹) * (g * (k * y * k⁻¹ * y⁻¹) * g⁻¹) * (k * g * k⁻¹ * g⁻¹)⁻¹) *
          (k * g * k⁻¹ * g⁻¹ * (g * y * g⁻¹) * (k * g * k⁻¹ * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) := by
      group
    rw [e]
    exact (Z1 L1 L2 S).mul_mem (hconjZ1 _ hcP1 _ (hconjZ1 _ hgP1 _ hy)) hcomm
  have hZ1F : Z1 L1 L2 S ≤ F := fun z hz =>
    (hmemF z).mpr ⟨hZ1X hz, (Z1 L1 L2 S).mul_mem (hconjZ1 _ hkP1 _ hz) ((Z1 L1 L2 S).inv_mem hz)⟩
  rcases hXstep.2.2.2 F hFn hZ1F (fun y hy => ((hmemF y).mp hy).1) with hFZ | hFX
  · exact hy₀Z (hFZ ▸ (hmemF y₀).mpr ⟨hy₀X, hy₀k⟩)
  have hkall : ∀ y ∈ str83X L1 L2 S, k * y * k⁻¹ * y⁻¹ ∈ Z1 L1 L2 S := fun y hy => by
    rw [← hFX] at hy
    exact ((hmemF y).mp hy).2
  have hd₂H : d₂ ∈ L2 ⊔ S := Subgroup.mem_sup_left ((F1.borelOf_le L2 S) (d.hD2hall.1 hd₂))
  have hkZ2 : k⁻¹ ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (Subgroup.normalizer _).inv_mem (bigB_le_normalizer_z2 L1 L2 S hkB)
  have hδ1 : δ = 1 := by
    refine hD1I δ hδ fun y hy => ?_
    have hyX : y ∈ str83X L1 L2 S := (Subgroup.mem_inf.mp hy).1
    have h1 : k⁻¹ * (d₂ * y * d₂⁻¹ * y⁻¹) * k⁻¹⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp hkZ2 _).mp (hIL2 d₂ hd₂H y hy)
    have h2 : k⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ * k⁻¹⁻¹ ∈ Z1 L1 L2 S :=
      hconjZ1 _ ((P1 L1 L2 S).inv_mem hkP1) _ ((Z1 L1 L2 S).inv_mem (hkall y hyX))
    have e : δ * y * δ⁻¹ * y⁻¹ = (k⁻¹ * (d₂ * y * d₂⁻¹ * y⁻¹) * k⁻¹⁻¹) *
        (k⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ * k⁻¹⁻¹) := by
      rw [hkdef]
      group
    rw [e]
    exact (Z2 L1 L2 S).mul_mem h1 (hZ1Z2 h2)
  have hk : k = d₂ := by rw [hkdef, hδ1, inv_one, mul_one]
  rw [hk] at hkall
  have hw' : d.w * d₂⁻¹ * d.w⁻¹ = d₂ := by
    rw [show d.w * d₂⁻¹ * d.w⁻¹ = (d.w * d₂ * d.w⁻¹)⁻¹ by group, d.hwInv d₂ hd₂, inv_inv]
  have hHZ2 : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hd₂P1 : d₂ ∈ P1 L1 L2 S := hk ▸ hkP1
  have hcent : ∀ v ∈ Z2 L1 L2 S, d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹ = 1 := by
    intro v hv
    have hm1 : d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹ ∈ Z1 L1 L2 S := by
      have e : d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹ = d₂⁻¹ * (d₂ * v * d₂⁻¹ * v⁻¹)⁻¹ * d₂⁻¹⁻¹ := by group
      rw [e]
      exact hconjZ1 _ ((P1 L1 L2 S).inv_mem hd₂P1) _
        ((Z1 L1 L2 S).inv_mem (hkall v (z2_le_str83X L1 L2 S hv)))
    have hwv : d.w * v * d.w⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hHZ2 d.hwH2) v).mp hv
    have hm2 : d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹ ∈ CFSG.conjugate (Z1 L1 L2 S) d.w := by
      rw [CFSG.mem_conjugate_iff]
      have e : d.w * (d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹) * d.w⁻¹ =
          d₂ * (d.w * v * d.w⁻¹) * d₂⁻¹ * (d.w * v * d.w⁻¹)⁻¹ := by
        calc d.w * (d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹) * d.w⁻¹ = (d.w * d₂⁻¹ * d.w⁻¹) * (d.w * v * d.w⁻¹) *
              (d.w * d₂⁻¹ * d.w⁻¹)⁻¹ * (d.w * v * d.w⁻¹)⁻¹ := by group
          _ = d₂ * (d.w * v * d.w⁻¹) * d₂⁻¹ * (d.w * v * d.w⁻¹)⁻¹ := by rw [hw']
      rw [e]
      exact hkall _ (z2_le_str83X L1 L2 S hwv)
    have hbot := str83G4_z1_inf_conjugate_w hfr' d
    have hm : d₂⁻¹ * v * d₂⁻¹⁻¹ * v⁻¹ ∈ Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w :=
      Subgroup.mem_inf.mpr ⟨hm1, hm2⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  refine hd₂1 (str83G4_torusFaithful hfr' d₂ (d.hD2hall.1 hd₂)
    (Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hd₂)) fun z hz => ?_)
  rw [← hZ1eq] at hz
  have h1 : d₂⁻¹ * z * d₂ = z := by
    simpa using mul_inv_eq_one.mp (hcent z (hZ1Z2 hz))
  calc d₂ * z = d₂ * (d₂⁻¹ * z * d₂) := by rw [h1]
    _ = z * d₂ := by group

end CFSG.Quasithin.Stroth

end
