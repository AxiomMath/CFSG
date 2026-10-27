module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagBase
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMain

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {Y : Type} [Group Y]

structure BorelAutDiag (U H : Subgroup Y) (F E : Subgroup (MulAut Y)) : Prop
    extends BorelBase U H where
  F_U : ∀ σ ∈ F, ∀ x : Y, σ x ∈ U ↔ x ∈ U
  F_H : ∀ σ ∈ F, ∀ h ∈ H, σ h ∈ H
  F_solv : Group.IsSolvable ↥F
  F_faithful : ∀ σ ∈ F, (∀ h ∈ H, σ h = h) → σ = 1
  E_U : ∀ e ∈ E, ∀ x : Y, e x ∈ U ↔ x ∈ U
  E_solv : Group.IsSolvable ↥E
  E_triv : ∀ e ∈ E, ∀ b ∈ Subgroup.normalizer (U : Set Y), b⁻¹ * e b ∈ U
  E_two : ∀ e ∈ E, ∀ k : ℕ, e ^ 2 ^ k = 1 → ∃ u ∈ U, e = MulAut.conj u
  F_E : ∀ σ ∈ F, ∀ e ∈ E, σ * e * σ⁻¹ ∈ E
  normal_form : ∀ α : MulAut Y, (∀ x : Y, α x ∈ U ↔ x ∈ U) →
    ∃ e ∈ E, ∃ σ ∈ F, α = e * σ

theorem aut_mul_conj_mul_inv (β : MulAut Y) (h : Y) :
    β * MulAut.conj h * β⁻¹ = MulAut.conj (β h) := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem comm_conj_aut_gen (β : MulAut Y) (h : Y) :
    MulAut.conj h * β * (MulAut.conj h)⁻¹ * β⁻¹ = MulAut.conj (h * (β h)⁻¹) := by
  have e2 : β * (MulAut.conj h)⁻¹ * β⁻¹ = MulAut.conj (β h)⁻¹ := by
    rw [← map_inv (MulAut.conj : Y →* MulAut Y) h, aut_mul_conj_mul_inv, map_inv β h]
  rw [mul_assoc, mul_assoc, ← mul_assoc β, e2, ← map_mul]

theorem lieAut_of_borelAutDiag [Finite Y] {U H : Subgroup Y} {F E : Subgroup (MulAut Y)}
    (D : BorelAutDiag U H F E) (A : LieAmalgamExt Y) (hTD : A.TD = U)
    (hP : A.P1 ⊓ A.P2 ≤ Subgroup.normalizer (U : Set Y)) (hUP : U ≤ perfectCore A.P1) :
    Group.IsSolvable ↥(A.N1 ⊓ A.N2) ∧ pCoreOf 2 (A.N1 ⊓ A.N2) ≤ perfectCore A.N1 := by
  have hBP1 : Subgroup.normalizer (U : Set Y) ≤ A.P1 := by
    rw [← hTD]
    exact ((A.yam.2.2 A.P1).mpr (Or.inl rfl)).2
  have hBP2 : Subgroup.normalizer (U : Set Y) ≤ A.P2 := by
    rw [← hTD]
    exact ((A.yam.2.2 A.P2).mpr (Or.inr rfl)).2
  have hB : A.P1 ⊓ A.P2 = Subgroup.normalizer (U : Set Y) :=
    le_antisymm hP (le_inf hBP1 hBP2)
  have hBβ : ∀ β ∈ A.N1 ⊓ A.N2, ∀ x, β x ∈ Subgroup.normalizer (U : Set Y) ↔
      x ∈ Subgroup.normalizer (U : Set Y) := by
    intro β hβ x
    rw [← hB, Subgroup.mem_inf, Subgroup.mem_inf]
    have h1 := hβ.1.2 x
    have h2 := hβ.2.2 x
    constructor
    · rintro ⟨a, b⟩
      exact ⟨h1.mpr a, h2.mpr b⟩
    · rintro ⟨a, b⟩
      exact ⟨h1.mp a, h2.mp b⟩
  have hUp : IsPGroup 2 ↥U := D.sylow.2.1
  have hstab : ∀ β ∈ A.N1 ⊓ A.N2, ∀ x, β x ∈ U ↔ x ∈ U := by
    intro β hβ x
    constructor
    · intro hx
      have hxB' : x ∈ Subgroup.normalizer (U : Set Y) :=
        (hBβ β hβ x).mp (Subgroup.le_normalizer hx)
      obtain ⟨a, ha⟩ := hUp ⟨β x, hx⟩
      have h1 : (β x) ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have h2 : x ^ 2 ^ a = 1 := by
        apply β.injective
        rw [map_pow, map_one]
        exact h1
      exact D.mem_U_of_pow x hxB' h2
    · intro hx
      have hxB := (hBβ β hβ x).mpr (Subgroup.le_normalizer hx)
      obtain ⟨a, ha⟩ := hUp ⟨x, hx⟩
      have h1 : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have h2 : (β x) ^ 2 ^ a = 1 := by rw [← map_pow, h1, map_one]
      exact D.mem_U_of_pow (β x) hxB h2
  have hnf : ∀ β ∈ A.N1 ⊓ A.N2, ∃ e ∈ E, ∃ σ ∈ F, β = e * σ := fun β hβ =>
    D.normal_form β (hstab β hβ)
  have hinj := D.conj_injective
  have hEs : Group.IsSolvable ↥E := D.E_solv
  have hFs : Group.IsSolvable ↥F := D.F_solv
  have hFn : F ≤ Subgroup.normalizer (E : Set (MulAut Y)) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => D.F_E σ hσ a ha, fun ha => ?_⟩
    have := D.F_E σ⁻¹ (F.inv_mem hσ) _ ha
    simpa [mul_assoc] using this
  have hW : Group.IsSolvable ↥(E ⊔ F) := A3.isSolvable_sup_of_le_normalizer hFn
  have hle : A.N1 ⊓ A.N2 ≤ E ⊔ F := by
    intro β hβ
    obtain ⟨e, he, σ, hσ, rfl⟩ := hnf β hβ
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hσ)
  refine ⟨Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle), ?_⟩
  have hRn : A.N1 ⊓ A.N2 ≤ Subgroup.normalizer (pCoreOf 2 (A.N1 ⊓ A.N2) : Set (MulAut Y)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hR2 : IsPGroup 2 (pCoreOf 2 (A.N1 ⊓ A.N2)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  intro β hβR
  have hβN : β ∈ A.N1 ⊓ A.N2 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hβR
  obtain ⟨e, he, σ, hσ, hβσ⟩ := hnf β hβN
  obtain ⟨b, hb⟩ := hR2 ⟨β, hβR⟩
  have hβb : β ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hσ1 : σ = 1 := by
    apply D.F_faithful σ hσ
    intro h hh
    have hhB : h ∈ Subgroup.normalizer (U : Set Y) := D.H_le hh
    have hc : (MulAut.conj h : MulAut Y) ∈ A.N1 ⊓ A.N2 :=
      ⟨⟨A.inn_le ⟨h, rfl⟩, conj_mem_autStab (hBP1 hhB)⟩,
        ⟨A.inn_le ⟨h, rfl⟩, conj_mem_autStab (hBP2 hhB)⟩⟩
    have hγ : MulAut.conj h * β * (MulAut.conj h)⁻¹ * β⁻¹ ∈ pCoreOf 2 (A.N1 ⊓ A.N2) := by
      have := (Subgroup.mem_normalizer_iff.mp (hRn hc) β).mp hβR
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hβR)
    rw [comm_conj_aut_gen] at hγ
    obtain ⟨a, ha⟩ := hR2 ⟨_, hγ⟩
    have hxa : (h * (β h)⁻¹) ^ 2 ^ a = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact congrArg Subtype.val ha
    have hβhB : β h ∈ Subgroup.normalizer (U : Set Y) := (hBβ β hβN h).mpr hhB
    have hx : h * (β h)⁻¹ ∈ Subgroup.normalizer (U : Set Y) :=
      Subgroup.mul_mem _ hhB (Subgroup.inv_mem _ hβhB)
    have hxU : h * (β h)⁻¹ ∈ U := D.mem_U_of_pow _ hx hxa
    have hσh : σ h ∈ H := D.F_H σ hσ h hh
    have hu₂ := D.E_triv e he (σ h) (D.H_le hσh)
    have hβh : β h = e (σ h) := by rw [hβσ]; rfl
    rw [hβh] at hxU
    have hconj : h * (σ h)⁻¹ ∈ U := by
      have h2 : h * (σ h)⁻¹ = (h * ((σ h)⁻¹ * e (σ h)) * h⁻¹) * (h * (e (σ h))⁻¹) := by group
      rw [h2]
      exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp hhB _).mp hu₂) hxU
    have := D.U_inf_H _ hconj (H.mul_mem hh (H.inv_mem hσh))
    exact (mul_inv_eq_one.mp this).symm
  rw [hσ1, mul_one] at hβσ
  obtain ⟨u, hu, hue⟩ := D.E_two e he b (by rw [← hβσ]; exact hβb)
  have hmem : β ∈ (perfectCore A.P1).map (MulAut.conj : Y →* MulAut Y) :=
    ⟨u, hUP hu, (hβσ.trans hue).symm⟩
  rw [← perfectCore_map_inj (MulAut.conj : Y →* MulAut Y) hinj A.P1] at hmem
  exact perfectCore_mono (map_conj_le_N1 A) hmem

end CFSG.Quasithin.H13.Sec53F.BA
