module

public import CFSG.Quasithin.H13.NQS134EI
public import CFSG.Quasithin.H13.NQS134EF

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem swap_D_cases : ∀ i j : Fin 6, i ≠ j → InD6 (swap i j) →
    swap i j = swap 0 1 ∨ swap i j = swap 2 3 ∨ swap i j = swap 4 5 := by
  decide +kernel

theorem not_InD6_comm_c3 : ¬ InD6 (swap (0 : Fin 6) 1 * swap 1 2 * swap 0 1 *
    (swap (0 : Fin 6) 1 * swap 1 2)⁻¹ * (swap (0 : Fin 6) 1)⁻¹) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem exists_conj_swap01 (hCMT : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T)
    {g : G} (hAT : conjSub g V ≤ T) {i j : Fin 6} (hij : i ≠ j)
    (hρ : ∀ (a : G) (ha : a ∈ conjSub g V), S.frame.ρ ⟨a, S.frame.T_le (hAT ha)⟩ = 1 ∨
      S.frame.ρ ⟨a, S.frame.T_le (hAT ha)⟩ = swap i j)
    (hAC : ¬ conjSub g V ≤ centralizer (V : Set G)) :
    ∃ (y : G) (hyT : conjSub y V ≤ T),
      (∀ (a : G) (ha : a ∈ conjSub y V), S.frame.ρ ⟨a, S.frame.T_le (hyT ha)⟩ = 1 ∨
        S.frame.ρ ⟨a, S.frame.T_le (hyT ha)⟩ = swap 0 1) ∧
      ∃ (a₁ : G) (ha₁ : a₁ ∈ conjSub y V), S.frame.ρ ⟨a₁, S.frame.T_le (hyT ha₁)⟩ = swap 0 1 := by
  obtain ⟨a₀, ha₀, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hAC
  have ha₀N := S.frame.T_le (hAT ha₀)
  have hρ₀ : S.frame.ρ ⟨a₀, ha₀N⟩ = swap i j :=
    (hρ a₀ ha₀).resolve_left fun h => ha₀C ((frame5_ker_iff S.frame _).1 h)
  have hD : InD6 (swap i j) := hρ₀ ▸ S.frame.T_D _ (hAT ha₀)
  obtain ⟨σ, hσA, hσ, t₀₁, ht₀₁T, ht₀₁⟩ : ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      σ * swap i j * σ⁻¹ = swap 0 1 ∧ ∃ (t : G) (ht : t ∈ T),
        S.frame.ρ ⟨t, S.frame.T_le ht⟩ = swap 0 1 := by
    rcases swap_D_cases i j hij hD with h | h | h
    · exact ⟨1, one_mem _, by rw [h]; group, a₀, hAT ha₀, hρ₀.trans h⟩
    · obtain ⟨⟨t, htN⟩, htT, hρt⟩ := S.frame.DA_T (swap 0 2 * swap 1 3) (by decide)
        (Perm.mem_alternatingGroup.2 (by decide))
      refine ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.2 (by decide), by rw [h]; decide,
        t * a₀ * t⁻¹,
        mul_mem (mul_mem htT (hAT ha₀)) (inv_mem htT), ?_⟩
      have e : (⟨t * a₀ * t⁻¹, S.frame.T_le (mul_mem (mul_mem htT (hAT ha₀)) (inv_mem htT))⟩ :
          ↥(normalizer (V : Set G))) = ⟨t, htN⟩ * ⟨a₀, ha₀N⟩ * (⟨t, htN⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hρt, hρ₀, h]
      decide
    · obtain ⟨⟨t, htN⟩, htT, hρt⟩ := S.frame.DA_T (swap 0 1 * swap 4 5) (by decide)
        (Perm.mem_alternatingGroup.2 (by decide))
      refine ⟨swap 0 4 * swap 1 5, Perm.mem_alternatingGroup.2 (by decide), by rw [h]; decide,
        t * a₀,
        mul_mem htT (hAT ha₀), ?_⟩
      have e : (⟨t * a₀, S.frame.T_le (mul_mem htT (hAT ha₀))⟩ : ↥(normalizer (V : Set G))) =
          ⟨t, htN⟩ * ⟨a₀, ha₀N⟩ := rfl
      rw [e, map_mul, hρt, hρ₀, h]
      decide
  obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσA
  have hmem : ∀ a' : G, a' ∈ conjSub (l * g) V ↔ l⁻¹ * a' * l ∈ conjSub g V := fun a' => by
    rw [conjSub_mul, mem_conjSub]
  have hA'N : ∀ a' ∈ conjSub (l * g) V, a' ∈ normalizer (V : Set G) := by
    intro a' ha'
    have h1 := S.frame.T_le (hAT ((hmem a').1 ha'))
    have e : a' = l * (l⁻¹ * a' * l) * l⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hlN h1) (inv_mem hlN)
  have hρ' : ∀ (a' : G) (ha' : a' ∈ conjSub (l * g) V), S.frame.ρ ⟨a', hA'N a' ha'⟩ = 1 ∨
      S.frame.ρ ⟨a', hA'N a' ha'⟩ = swap 0 1 := by
    intro a' ha'
    have ha := (hmem a').1 ha'
    have e : (⟨a', hA'N a' ha'⟩ : ↥(normalizer (V : Set G))) =
        ⟨l, hlN⟩ * ⟨l⁻¹ * a' * l, S.frame.T_le (hAT ha)⟩ * (⟨l, hlN⟩)⁻¹ :=
      Subtype.ext (by simp only [coe_mul, InvMemClass.coe_inv]; group)
    rw [e, map_mul, map_mul, map_inv, hlσ]
    rcases hρ _ ha with h | h
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [h, hσ]
  have hT : conjSub (l * g) V ≤ T := by
    intro a' ha'
    have hNL := S.normalizer_V_le (hA'N a' ha')
    rcases hρ' a' ha' with h | h
    · exact hCMT (mem_inf.2 ⟨hNL, (frame5_ker_iff S.frame _).1 h⟩)
    · have ht₀₁N := S.frame.T_le ht₀₁T
      have h1 : a' * t₀₁⁻¹ ∈ T := by
        refine hCMT (mem_inf.2 ⟨mul_mem hNL (inv_mem (S.normalizer_V_le ht₀₁N)), ?_⟩)
        refine (frame5_ker_iff S.frame ⟨a' * t₀₁⁻¹, mul_mem (hA'N a' ha') (inv_mem ht₀₁N)⟩).1 ?_
        have e : (⟨a' * t₀₁⁻¹, mul_mem (hA'N a' ha') (inv_mem ht₀₁N)⟩ :
            ↥(normalizer (V : Set G))) = ⟨a', hA'N a' ha'⟩ * (⟨t₀₁, ht₀₁N⟩)⁻¹ := rfl
        rw [e, map_mul, map_inv, h, ht₀₁, mul_inv_cancel]
      have e : a' = a' * t₀₁⁻¹ * t₀₁ := by group
      rw [e]
      exact mul_mem h1 ht₀₁T
  refine ⟨l * g, hT, fun a' ha' => hρ' a' ha', l * a₀ * l⁻¹, ?_, ?_⟩
  · rw [hmem]
    simpa [mul_assoc] using ha₀
  · have ha₀' : l * a₀ * l⁻¹ ∈ conjSub (l * g) V := by
      rw [hmem]
      simpa [mul_assoc] using ha₀
    rcases hρ' _ ha₀' with h | h
    · exfalso
      have e : (⟨l * a₀ * l⁻¹, hA'N _ ha₀'⟩ : ↥(normalizer (V : Set G))) =
          ⟨l, hlN⟩ * ⟨a₀, ha₀N⟩ * (⟨l, hlN⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hlσ, hρ₀, hσ] at h
      exact absurd h (by decide)
    · exact h

theorem not_le_centralizer_of_swap01 {K W : Subgroup G} (hL1K : L₁Of L (fsuV1 T V) ≤ K)
    (hKW : K ≤ normalizer (W : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hCKT : K ⊓ centralizer (W : Set G) ≤ T) {A : Subgroup G} (hAT : A ≤ T) {a₁ : G}
    (ha₁ : a₁ ∈ A) (hρ₁ : S.frame.ρ ⟨a₁, S.frame.T_le (hAT ha₁)⟩ = swap 0 1) :
    ¬ A ≤ centralizer (W : Set G) := by
  intro hAW
  obtain ⟨⟨y, hyN⟩, hyL1, hρy⟩ := U3.s134_L1_three S (swap 0 1 * swap 1 2) (by decide)
  have hyK := hL1K hyL1
  have ha₁T := hAT ha₁
  have hcK : y * a₁ * y⁻¹ * a₁⁻¹ ∈ K := by
    have h1 : a₁ * y⁻¹ * a₁⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK ha₁T) _).mp (inv_mem hyK)
    have e : y * a₁ * y⁻¹ * a₁⁻¹ = y * (a₁ * y⁻¹ * a₁⁻¹) := by group
    rw [e]
    exact mul_mem hyK h1
  have hcW : y * a₁ * y⁻¹ * a₁⁻¹ ∈ centralizer (W : Set G) := by
    refine mul_mem ?_ (inv_mem (hAW ha₁))
    exact (mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer W (hKW hyK)) a₁).mp
      (hAW ha₁)
  have hcT := hCKT (mem_inf.2 ⟨hcK, hcW⟩)
  have hD := S.frame.T_D ⟨_, S.frame.T_le hcT⟩ hcT
  have e : (⟨y * a₁ * y⁻¹ * a₁⁻¹, S.frame.T_le hcT⟩ : ↥(normalizer (V : Set G))) =
      ⟨y, hyN⟩ * ⟨a₁, S.frame.T_le ha₁T⟩ * (⟨y, hyN⟩)⁻¹ * (⟨a₁, S.frame.T_le ha₁T⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hρy, hρ₁] at hD
  exact not_InD6_comm_c3 hD

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
include hz hzL

theorem wtP_ne_of_zV :
    wtP (S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) ∧
      wtP (S.frame.ψ ⟨z * S.zV, mul_mem hz.1 S.zV_mem_V⟩ : P6) ≠
        wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
  rw [wtP_mul_zV S hz hzL, S.psi_zV]
  show wtP (G6.allOnes 6) ≠ _ ∧ _
  rw [wtP_allOnes]
  rcases psi_z_cases' S hz hzL with h | h
  · rw [h, wtP_e0123]
    decide
  · rw [h, wtP_e45]
    decide

omit hz in
theorem mul_zV_ne_one : z * S.zV ≠ 1 := by
  intro h1
  have : z = S.zV⁻¹ := eq_inv_of_mul_eq_one_left h1
  apply hzL
  rw [this]
  exact inv_mem (S.mem_ZV_iff.2 (Or.inr rfl)).2

variable (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
    ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z)
include huniq

theorem false_of_comm_ne (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {W : Subgroup G}
    (hTW : T ≤ normalizer (W : Set G)) (hWC : W ≤ centralizer (V : Set G))
    (horb : ∀ c ∈ W, c ≠ 1 → c ≠ z →
      ∃ g ∈ normalizer (W : Set G), g * c * g⁻¹ = S.zV ∨ g * c * g⁻¹ = z * S.zV)
    (hnz : ∀ x ∈ T, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ≠ z)
    {y : G} (hyT : conjSub y V ≤ T) {a u : G} (ha : a ∈ conjSub y V) (hu : u ∈ W)
    (huN : u ∈ normalizer (conjSub y V : Set G)) (hau : a * u ≠ u * a) : False := by
  have haT := hyT ha
  have hc1 : a * u * a⁻¹ * u⁻¹ ≠ 1 := by
    intro h
    apply hau
    calc a * u = a * u * a⁻¹ * u⁻¹ * (u * a) := by group
      _ = u * a := by rw [h, one_mul]
  have hcW : a * u * a⁻¹ * u⁻¹ ∈ W :=
    mul_mem ((mem_normalizer_iff.mp (hTW haT) u).mp hu) (inv_mem hu)
  have hcA : a * u * a⁻¹ * u⁻¹ ∈ conjSub y V := by
    have h1 : u * a⁻¹ * u⁻¹ ∈ conjSub y V := (mem_normalizer_iff.mp huN _).mp (inv_mem ha)
    have e : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem ha h1
  obtain ⟨g, hgW, hg⟩ := horb _ hcW hc1 (hnz a haT u hu)
  obtain ⟨w, hwV, hw1, hww, hgw⟩ : ∃ w : G, ∃ hwV : w ∈ V, w ≠ 1 ∧
      wtP (S.frame.ψ ⟨w, hwV⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) ∧
        g * (a * u * a⁻¹ * u⁻¹) * g⁻¹ = w := by
    obtain ⟨h6, h4⟩ := wtP_ne_of_zV S hz hzL
    rcases hg with hg | hg
    · exact ⟨_, S.zV_mem_V, S.zV_ne_one, h6, hg⟩
    · exact ⟨_, mul_mem hz.1 S.zV_mem_V, mul_zV_ne_one S hzL, h4, hg⟩
  have hwg : w ∈ V.map (MulAut.conj (g * y)).toMonoidHom := by
    show w ∈ conjSub (g * y) V
    rw [conjSub_mul, ← hgw]
    exact mul_mem_conjSub hcA
  have hgy : conjSub (g * y) V = V := eq_of_mem_conj S hz hzL huniq h331 h1222 hwV hw1 hww hwg
  have hga : g * a * g⁻¹ ∈ V := by
    rw [← hgy, conjSub_mul]
    exact mul_mem_conjSub ha
  have hgu : g * u * g⁻¹ ∈ W := (mem_normalizer_iff.mp hgW u).mp hu
  have hcomm := mem_centralizer_iff.1 (hWC hgu) _ hga
  apply hau
  have e : g * a * g⁻¹ * (g * u * g⁻¹) = g * (a * u) * g⁻¹ := by group
  have e' : g * u * g⁻¹ * (g * a * g⁻¹) = g * (u * a) * g⁻¹ := by group
  rw [e, e'] at hcomm
  simpa using hcomm

theorem false_of_comm_eq (h1222 : Stmt12_2_2) {W : Subgroup G} {y : G}
    (hWA : ¬ conjSub y V ≤ centralizer (W : Set G))
    (hU : ∀ a ∈ conjSub y V, ∀ u ∈ W, u ∈ normalizer (conjSub y V : Set G) → a * u = u * a)
    (hE1 : Nat.card (conjSub y V) ≤ 8 * Nat.card ↥(conjSub y V ⊓ centralizer (W : Set G)))
    (hE2 : Nat.card (conjSub y V) = 8 * Nat.card ↥(conjSub y V ⊓ centralizer (W : Set G)) →
      ∃ a₁ ∈ conjSub y V, a₁ ∉ centralizer (W : Set G) ∧ ∃ a₂ ∈ conjSub y V, ∃ w ∈ W,
        a₁ * w = w * a₁ ∧ a₂ * w ≠ w * a₂) : False := by
  set A := conjSub y V with hAdef
  set C := A ⊓ centralizer (W : Set G) with hCdef
  have hC4 : Nat.card C ≤ 4 := by
    by_contra h
    push Not at h
    apply hWA
    have hN := centralizer_le_normalizer_conj S hz hzL huniq h1222 (g := y)
      (inf_le_left : C ≤ A) h
    intro a ha
    rw [mem_centralizer_iff]
    intro u hu
    have huC : u ∈ centralizer (C : Set G) := mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (mem_inf.1 hx).2 u hu).symm
    exact (hU a ha u hu (hN huC)).symm
  have hA32 := card_conj S y
  rw [← hAdef] at hA32
  have h4 : Nat.card C = 4 := by omega
  obtain ⟨a₁, ha₁, ha₁C, a₂, ha₂, w, hw, hw₁, hw₂⟩ := hE2 (by rw [hA32, h4])
  set B := C ⊔ zpowers a₁ with hBdef
  have hBA : B ≤ A := sup_le inf_le_left (zpowers_le.2 ha₁)
  have hCB : C ≤ B := le_sup_left
  have ha₁B : a₁ ∈ B := mem_sup_right (mem_zpowers a₁)
  have hB4 : 4 < Nat.card B := by
    obtain ⟨k, hk⟩ := card_dvd_of_le hCB
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      have hCBeq := eq_of_le_of_card_ge hCB hk.le
      exact ha₁C (mem_inf.1 (hCBeq ▸ ha₁B)).2
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact (Nat.card_pos (α := ↥B)).ne' hk
    have : 2 * Nat.card C ≤ Nat.card B := by
      rw [hk, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hN := centralizer_le_normalizer_conj S hz hzL huniq h1222 (g := y) hBA hB4
  have hwB : w ∈ centralizer (B : Set G) := by
    have hle : B ≤ centralizer ({w} : Set G) := by
      refine sup_le ?_ (zpowers_le.2 (mem_centralizer_singleton_iff.2 hw₁))
      intro x hx
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hx).2 w hw).symm
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.1 (hle hx)
  exact hw₂ (hU a₂ ha₂ w hw (hN hwB))

end End134

end CFSG.Quasithin.H13.NQS134
