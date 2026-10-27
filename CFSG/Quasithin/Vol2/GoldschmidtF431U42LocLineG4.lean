module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G) [Finite G]

theorem local_line {g : G} (hcomm : (g * C.z * g⁻¹) * C.tG = C.tG * (g * C.z * g⁻¹)) :
    ∃ a m : Y, a ∈ P1 ∧ m ∈ P1 ∧ C.Φ1 a = g⁻¹ * C.tG * g ∧ a ∈ Vconj m ∧ a * a = 1 ∧ a ≠ 1 ∧
      ¬ IsConj xY a ∧ ∀ W : Subgroup G, C.IsLn W → g * C.z * g⁻¹ ∈ W → C.tG ∈ W →
        W = C.V2.map (MulAut.conj (g * C.Φ1 m)).toMonoidHom := by
  obtain ⟨a, haP, haΦ, ha2, ha1⟩ := C.exists_pull hcomm C.tG_sq C.tG_ne_one
  have hnc : ¬ IsConj xY a := by
    intro hc
    obtain ⟨k, hk⟩ := C.isPt_of_isConj haP hc haΦ
    exact C.not_conj_z tPrime_mem_Vsub not_isConj_tPrime k hk
  obtain ⟨m, hmP, hV⟩ := exists_P1_conj_of_involution haP ha2 ha1 hnc
  have hfix := fixSet_eq_of_mem_Vconj hV ha2 ha1 hnc
  refine ⟨a, m, haP, hmP, haΦ, hV, ha2, ha1, hnc, ?_⟩
  intro W hW hu ht
  obtain ⟨k, hk⟩ := hW
  have hWmem : ∀ x, x ∈ W ↔ k⁻¹ * x * k ∈ C.V2 := fun x => by rw [hk]; exact mem_map_conj
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have := C.V2_comm ((hWmem x).1 hx) ((hWmem y).1 hy)
    calc x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by rw [this]
      _ = y * x := by group
  have hWsq : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    have := C.V2_sq ((hWmem x).1 hx)
    calc x * x = k * ((k⁻¹ * x * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = 1 := by rw [this]; group
  obtain ⟨hEab, hEsq, hEcard⟩ := C.pre1_props hWab hWsq hu
  have hAmem : ∀ x, x ∈ W.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ W := by
    intro x
    rw [mem_map_conj]
    simp
  have hcardW : Nat.card W = Nat.card C.V2 := by
    rw [hk, Subgroup.card_map_of_injective (MulAut.conj k).injective]
  obtain ⟨m', hm'P, hEm'⟩ := exists_P1_conj_of_elemAbelian C.pre1_le hEab hEsq
    (by rw [hEcard, hcardW, C.card_V2])
  have haE : a ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom) := by
    refine C.mem_pre1.2 ⟨haP, (hAmem _).2 ?_⟩
    rw [haΦ]
    simpa [mul_assoc] using ht
  rw [hEm'] at haE
  have hfix' := fixSet_eq_of_mem_Vconj haE ha2 ha1 hnc
  have hVeq : Vconj m = Vconj m' := Vconj_eq_of_image_eq (hfix.symm.trans hfix')
  have hE : C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom) = Vconj m := by rw [hEm', hVeq]
  have hRHS : ∀ x, x ∈ C.V2.map (MulAut.conj (g * C.Φ1 m)).toMonoidHom ↔
      (g * C.Φ1 m)⁻¹ * x * (g * C.Φ1 m) ∈ C.V2 := fun x => mem_map_conj
  ext x
  rw [hRHS]
  have hΦm : ∀ y ∈ P1, C.Φ1 (m⁻¹ * y * m) = (C.Φ1 m)⁻¹ * C.Φ1 y * C.Φ1 m := by
    intro y hy
    rw [C.Φ1_mul (P1.mul_mem (P1.inv_mem hmP) hy) hmP, C.Φ1_mul (P1.inv_mem hmP) hy,
      C.Φ1_inv hmP]
  constructor
  · intro hx
    obtain ⟨y, hyP, hy⟩ := C.exists_Φ1_of_mem_conj hWab hu (x := g⁻¹ * x * g)
      (by simpa [mul_assoc] using hx)
    have hyE : y ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom) := by
      refine C.mem_pre1.2 ⟨hyP, (hAmem _).2 ?_⟩
      rw [hy]
      simpa [mul_assoc] using hx
    rw [hE] at hyE
    have h1 := C.Φ1_mem_V2 (mem_Vconj.1 hyE)
    rw [hΦm y hyP, hy] at h1
    have : (C.Φ1 m)⁻¹ * (g⁻¹ * x * g) * C.Φ1 m = (g * C.Φ1 m)⁻¹ * x * (g * C.Φ1 m) := by group
    rwa [this] at h1
  · intro hx
    obtain ⟨v, hv, hvx⟩ := C.mem_V2.1 hx
    have hvP : v ∈ P1 := Vsub_le_P1 hv
    have hyE : m * v * m⁻¹ ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom) := by
      rw [hE, mem_Vconj]
      simpa [mul_assoc] using hv
    obtain ⟨hyP, hyA⟩ := C.mem_pre1.1 hyE
    have h1 : C.Φ1 (m * v * m⁻¹) = g⁻¹ * x * g := by
      rw [C.Φ1_conj hmP hvP, C.Φ1_eq_Φ2 (T_le_B0 (Vsub_le_T hv)), hvx]
      group
    rw [h1, hAmem] at hyA
    simpa [mul_assoc] using hyA

end Ctx

end CFSG.Quasithin.H13.F431.U42
