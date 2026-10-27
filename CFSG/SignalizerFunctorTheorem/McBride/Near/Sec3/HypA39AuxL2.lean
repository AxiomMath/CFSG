module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxL

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

namespace Red

theorem cen_le_normalizer_M₀ [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K : Subgroup Γ}
    (hK : Admits (H ⊔ A) K) (hLK : L ≤ K) (hKR : K ≤ R) {e : Γ} (he : e ∈ E)
    (hne : K ⊔ (H ⊓ Subgroup.centralizer {e}) ⊔ A ≠ H ⊔ A) :
    H ⊓ Subgroup.centralizer {e} ≤
      Subgroup.normalizer ((⁅K, A⁆ ⊔ (K ⊓ D₂) : Subgroup Γ) : Set Γ) := by
  obtain ⟨U, hUR, hUadm, hUD, hRU⟩ := c.hasB_cen hK hLK hKR he hne
  have heA : e ∈ A := c.hEA he
  have hDC := c.D_le_centralizer_singleton heA
  have hD₂U : D₂ ≤ U := by
    rw [← hUD]
    exact inf_le_left
  have hUR' : U ≤ R := hUR.trans (sup_le hKR inf_le_left)
  have hUL : U ≤ Subgroup.normalizer (L : Set Γ) :=
    admits_of_centralizes (fun g hg x hx => c.R_cen g (hUR' hg) x hx)
  have hKU : K ≤ U ⊔ L := by
    calc K ≤ K ⊔ (R ⊓ Subgroup.centralizer {e}) := le_sup_left
      _ = U ⊔ D₁ := hRU
      _ = U ⊔ L := by rw [c.hD₁, ← sup_assoc, sup_eq_left.mpr hD₂U]
  have hAU : Admits A U := le_sup_right.trans hUadm
  have hAK : A ≤ Subgroup.normalizer (K : Set Γ) := le_sup_right.trans hK
  have hcomm : ⁅K, A⁆ ≤ U := by
    refine Subgroup.commutator_le.mpr fun k hk a ha => ?_
    obtain ⟨u, hu, l, hl, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hUL).mp (hKU hk)
    have hla : l * a = a * l := (c.A_cen a ha l hl).symm
    have h1 : ⁅u * l, a⁆ = ⁅u, a⁆ := by
      calc ⁅u * l, a⁆ = u * (l * a * l⁻¹) * u⁻¹ * a⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅u, a⁆ := by
            rw [hla]
            simp only [commutatorElement_def, mul_inv_cancel_right]
    rw [h1, commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hu (by simpa [mul_assoc] using hAU.conj_mem ha (inv_mem hu))
  have hAp : IsPGroup p A := HypAAux.isPGroup_of_isElemAbelian c.h15.a1_elemAbelian
  have hcopK : Nat.Coprime p (Nat.card K) :=
    c.h15.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (hKR.trans c.R_le_H))
  have hfact := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p
    c.h15.prime A K hAp hAK hcopK
  have hKAle : ⁅K, A⁆ ≤ K := Thm210.commutator_le_of_normalizes hAK
  have hM₀ : ⁅K, A⁆ ⊔ (K ⊓ D₂) = K ⊓ U := by
    apply le_antisymm
    · exact sup_le (le_inf hKAle hcomm) (le_inf inf_le_left (inf_le_right.trans hD₂U))
    · intro x hx
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
      have hX : K ⊓ Subgroup.centralizer (A : Set Γ) ≤
          Subgroup.normalizer ((⁅K, A⁆ : Subgroup Γ) : Set Γ) :=
        inf_le_left.trans (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes
          A K hAK)
      rw [← hfact] at hxK
      obtain ⟨w, hw, z, hz, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hX).mp hxK
      obtain ⟨hzK, hzC⟩ := Subgroup.mem_inf.mp hz
      have hzU : z ∈ U := by
        have := mul_mem (inv_mem (hcomm hw)) hxU
        simpa using this
      have hzD : z ∈ D := c.h15.mem_D (c.R_le_H (hKR hzK)) hzC
      have hzD₂ : z ∈ D₂ := by
        rw [← hUD]
        exact Subgroup.mem_inf.mpr ⟨hzU, hzD⟩
      exact mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right
        (Subgroup.mem_inf.mpr ⟨hzK, hzD₂⟩))
  intro g hg
  rw [hM₀]
  refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hK (Subgroup.mem_sup_left
    (Subgroup.mem_inf.mp hg).1), ?_⟩
  obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
  rw [c.hHR] at hgH
  obtain ⟨r, hr, d, hd, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer'
    (le_sup_left.trans c.admits_R)).mp hgH
  have hrC : r ∈ Subgroup.centralizer {e} := by
    have := mul_mem hgC (inv_mem (hDC hd))
    simpa using this
  have hrU : r ∈ Subgroup.normalizer (U : Set Γ) :=
    hUadm (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_inf.mpr ⟨hr, hrC⟩))))
  have hdU : d ∈ Subgroup.normalizer (U : Set Γ) :=
    hUadm (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd))
  exact mul_mem hrU hdU

theorem eq_L_of_ne [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K : Subgroup Γ}
    (hK : Admits (H ⊔ A) K) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hLK : L ≤ K)
    (hKR : K ≤ R)
    (hF2 : ∀ e ∈ E, e ≠ 1 → K ⊔ (H ⊓ Subgroup.centralizer {e}) ⊔ A ≠ H ⊔ A) : K = L := by
  have hAK : A ≤ Subgroup.normalizer (K : Set Γ) := le_sup_right.trans hK
  have hAp : IsPGroup p A := HypAAux.isPGroup_of_isElemAbelian c.h15.a1_elemAbelian
  have hKH : K ≤ H := hKR.trans c.R_le_H
  have hcopK : Nat.Coprime p (Nat.card K) :=
    c.h15.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKH)
  have hKAle : ⁅K, A⁆ ≤ K := Thm210.commutator_le_of_normalizes hAK
  have : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext (hKab a a.2 b b.2)⟩⟩
  have hAM₀ : Admits A (⁅K, A⁆ ⊔ (K ⊓ D₂)) := by
    refine Admits.sup (fun a ha => Thm210.mem_normalizer_commutator (hAK ha)
      (Subgroup.le_normalizer ha)) (Admits.inf hAK ?_)
    exact admits_of_centralizes (fun a ha x hx => Subgroup.mem_centralizer_iff.mp
      (c.h15.D_le_centralizer (c.D₂_le_D hx)) a ha)
  have hEab : IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (commute_of_mem c.h15.a1_elemAbelian.1 (c.hEA a.2)
      (c.hEA b.2)).eq⟩⟩, fun x hx => c.h15.a1_elemAbelian.2 x (c.hEA hx)⟩
  have hgen := McBride.iSup_centralizer_nonidentity c.h15.prime hEab c.hE.ge
    (c.hEA.trans c.h15.a1_admits) c.h15.coprime
  have hHM₀ : H ≤ Subgroup.normalizer ((⁅K, A⁆ ⊔ (K ⊓ D₂) : Subgroup Γ) : Set Γ) := by
    refine le_of_eq_of_le hgen.symm ?_
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    exact c.cen_le_normalizer_M₀ hK hLK hKR ha (hF2 a ha ha1)
  have hM₀adm : Admits (H ⊔ A) (⁅K, A⁆ ⊔ (K ⊓ D₂)) := sup_le hHM₀ hAM₀
  have hM₀H : ⁅K, A⁆ ⊔ (K ⊓ D₂) ≤ H := sup_le (hKAle.trans hKH) (inf_le_left.trans hKH)
  have hM₀D : (⁅K, A⁆ ⊔ (K ⊓ D₂)) ⊓ D ≤ D₂ := by
    intro x hx
    obtain ⟨hxM, hxD⟩ := Subgroup.mem_inf.mp hx
    have hX : K ⊓ D₂ ≤ Subgroup.normalizer ((⁅K, A⁆ : Subgroup Γ) : Set Γ) :=
      inf_le_left.trans (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes
        A K hAK)
    obtain ⟨w, hw, z, hz, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hX).mp hxM
    have hzD : z ∈ D := c.D₂_le_D (Subgroup.mem_inf.mp hz).2
    have hwD : w ∈ D := by simpa using mul_mem hxD (inv_mem hzD)
    have hFit := Thm210.commutator_inf_centralizer_eq_bot (R := K) (A := A) c.h15.prime hAK hAp
      hcopK
    have hw1 : w ∈ ⁅K, A⁆ ⊓ Subgroup.centralizer (A : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨hw, c.h15.D_le_centralizer hwD⟩
    rw [hFit, Subgroup.mem_bot] at hw1
    rw [hw1, one_mul]
    exact (Subgroup.mem_inf.mp hz).2
  have hM₀0 := c.eq_bot_of_normal hM₀H hM₀adm hM₀D
  have hKA0 : ⁅K, A⁆ = ⊥ := le_bot_iff.mp (hM₀0 ▸ le_sup_left)
  have hKD₂0 : K ⊓ D₂ = ⊥ := le_bot_iff.mp (hM₀0 ▸ le_sup_right)
  have hKD : K ≤ D := fun x hx => c.h15.mem_D (hKH hx)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKA0 hx)
  have hKD₁ : K ≤ D₁ := by
    rw [← c.hRD]
    exact le_inf hKR hKD
  have hLN : L ≤ Subgroup.normalizer (D₂ : Set Γ) := fun l hl => c.h15.a4_chief.1.2 (c.L_le_D hl)
  have hKLD₂ : K ≤ L ⊔ D₂ := by
    rw [sup_comm, ← c.hD₁]
    exact hKD₁
  have h1 : K ≤ L ⊔ (K ⊓ D₂) :=
    (le_inf le_rfl hKLD₂).trans (HypAAux.inf_sup_le_sup_inf hLK hLN)
  rw [hKD₂0, sup_bot_eq] at h1
  exact le_antisymm h1 hLK

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
