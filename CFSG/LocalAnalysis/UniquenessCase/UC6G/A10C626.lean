module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B11
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.P6a
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10C626

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10Gen (O1 O2)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} {m : Mz614 Dat}

theorem exists_E_comp (h620 : m.C620) {e : G} (he : e ∈ m.A ⊓ m.L) (he1 : e ≠ 1) :
    ∃ e₀ ∈ m.E, e₀ ≠ 1 ∧ ∀ x ∈ m.L, x * e = e * x → x * e₀ = e₀ * x := by
  have heA : e ∈ m.Z ⊔ m.E := he.1
  obtain ⟨z, hz, e₀, he₀, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (fun z hz e he => m.Z_comm_E hz he) heA
  have hZL : m.Z ⊓ m.L = ⊥ := inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2
  refine ⟨e₀, he₀, ?_, ?_⟩
  · rintro rfl
    apply he1
    have hzL : z ∈ m.Z ⊓ m.L := ⟨hz, by simpa using he.2⟩
    rw [hZL, Subgroup.mem_bot] at hzL
    rw [hzL, mul_one]
  · intro x hx hc
    have hxz : x * z = z * x := (m.Z_comm_L hz hx).symm
    have : z * (x * e₀) = z * (e₀ * x) := by
      calc z * (x * e₀) = (z * x) * e₀ := by rw [mul_assoc]
        _ = (x * z) * e₀ := by rw [hxz]
        _ = x * (z * e₀) := by rw [mul_assoc]
        _ = (z * e₀) * x := hc
        _ = z * (e₀ * x) := by rw [mul_assoc]
    exact mul_left_cancel this

theorem mem_gammaL_E (h620 : m.C620) {e : G} (he : e ∈ m.A ⊓ m.L) (he1 : e ≠ 1) {x : G}
    (hx : x ∈ m.L) (hc : x * e = e * x) : x ∈ gammaL m.L m.r m.E := by
  obtain ⟨e₀, he₀, he₀1, hcomm⟩ := exists_E_comp h620 he he1
  exact mem_gammaL_of_commute m.hr m.d.E_el.isPGroup he₀ he₀1 hx (hcomm x hx hc)

namespace A10Setup

variable (D : A10Setup m)

theorem ι_alt2_mem (h620 : m.C620) {x : A10}
    (hx : ∀ i, i ∉ O2 → (x : Equiv.Perm (Fin 10)) i = i) : D.ι x ∈ gammaL m.L m.r m.E := by
  refine mem_gammaL_E h620 ((D.ι_mem_B_iff a₁).2 a₁_mem)
    (fun h => a₁_ne (D.ι_injective (by rw [h, map_one]))) (D.ι_mem_L x) ?_
  rw [← map_mul, ← map_mul, A10Aut.commute_a₁_of_fix hx]

theorem ι_alt1_mem (h620 : m.C620) {x : A10}
    (hx : ∀ i, i ∉ O1 → (x : Equiv.Perm (Fin 10)) i = i) : D.ι x ∈ gammaL m.L m.r m.E := by
  refine mem_gammaL_E h620 ((D.ι_mem_B_iff a₂).2 a₂_mem)
    (fun h => a₂_ne (D.ι_injective (by rw [h, map_one]))) (D.ι_mem_L x) ?_
  rw [← map_mul, ← map_mul, A10Aut.commute_a₂_of_fix hx]

include D in
theorem c626gen_A10 (h620 : m.C620) (hr : m.r = 5) : m.C626gen := by
  intro p hp P hP hPne
  have hpp : p.Prime := (Dat.sig_prime _ hp).1
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  have hp5 : p ≠ 5 := fun h => m.hrσ (hr ▸ h ▸ hp)
  have hPN : P ≤ normalizer (m.L : Set G) := fun q hq =>
    m.normalizer_Z_le_normalizer_L (hP.le hq).2
  have hPp : IsPGroup p P := hP.isPGroup
  let f : ↥P →* Equiv.Perm (Fin 10) := D.permOf.comp (Subgroup.inclusion hPN)
  by_cases hall : ∀ q : ↥P, f q = 1
  ·
    obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    have hqC : q ∈ centralizer (m.L : Set G) := D.mem_centralizer_of_permOf_eq_one (hall ⟨q, hq⟩)
    exact le_sup_of_le_left fun y hy => mem_gammaL_of_commute hpp hPp hq
      (fun h => hq1 (Subtype.ext h)) hy (mem_centralizer_iff.1 hqC y hy)
  · push Not at hall
    obtain ⟨q, hq1⟩ := hall
    obtain ⟨q', hq'⟩ := A10Gen.exists_orderOf_map_eq_prime hpp hPp f hq1
    set σ : Equiv.Perm (Fin 10) := f q' with hσ
    have hσp : σ ^ p = 1 := by rw [← hq']; exact pow_orderOf_eq_one σ
    have hp37 := A10Gen.eq_three_or_seven hpp hp2 hp5 (hq' ▸ orderOf_dvd_natCard σ)
    have hσ37 : σ ^ 3 = 1 ∨ σ ^ 7 = 1 := by
      rcases hp37 with rfl | rfl
      · exact Or.inl hσp
      · exact Or.inr hσp
    have hσeven : Equiv.Perm.sign σ = 1 := A10Gen.sign_eq_one_of_pow σ hσ37
    let σA : A10 := ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσeven⟩
    have hσA : σA ^ 3 = 1 ∨ σA ^ 7 = 1 := by
      rcases hσ37 with h | h
      · left; apply Subtype.ext; simpa [σA] using h
      · right; apply Subtype.ext; simpa [σA] using h
    have hq'1 : (q' : G) ≠ 1 := fun h => by
      have h1 : σ = 1 := by rw [hσ, show q' = 1 from Subtype.ext h, map_one]
      rw [h1, orderOf_one] at hq'
      exact hpp.ne_one hq'.symm
    have act_eq : ∀ u : A10,
        (q' : G) * D.ι u * (q' : G)⁻¹ = D.ι σA * D.ι u * (D.ι σA)⁻¹ := fun u =>
      D.conj_eq_of_permOf (n := ⟨q', hPN q'.2⟩) (a := σA) rfl (D.ι_mem_L u)
    set Γ := gammaL m.L p P ⊔ gammaL m.L m.r m.E with hΓ
    have hT := A10Gen.core_A10 (D.img Γ)
      (fun x hfix => D.mem_img.2 (Subgroup.mem_sup_right (D.ι_alt1_mem h620 hfix)))
      (fun x hfix => D.mem_img.2 (Subgroup.mem_sup_right (D.ι_alt2_mem h620 hfix)))
      hσA (fun x hx => by
        apply D.mem_img.2
        refine Subgroup.mem_sup_left (mem_gammaL_of_commute hpp hPp q'.2 hq'1 (D.ι_mem_L x) ?_)
        have h2 : σA * x * σA⁻¹ = x := mul_inv_eq_iff_eq_mul.2 hx.symm
        have h1 : (q' : G) * D.ι x * (q' : G)⁻¹ = D.ι x := by
          rw [act_eq x, ← map_inv, ← map_mul, ← map_mul, h2]
        calc D.ι x * (q' : G) = ((q' : G) * D.ι x * (q' : G)⁻¹) * (q' : G) := by rw [h1]
          _ = (q' : G) * D.ι x := by group)
    intro l hl
    obtain ⟨u, rfl⟩ := D.exists_ι hl
    have : u ∈ D.img Γ := by rw [hT]; exact Subgroup.mem_top u
    exact D.mem_img.1 this

end A10Setup

theorem exists_A10Setup_of_Lbar (h620 : m.C620) (hr : m.r = 5)
    (hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥) (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt m.Lbar 10) :
    Nonempty (Mz614.A10Setup m) := by
  obtain ⟨e⟩ := hA
  exact Mz614.exists_A10Setup m h620 hr ⟨(m.equivLbar hOL).trans e⟩

theorem c626gen_of_A10 (m : Mz614 Dat) (hL : m.L620) (hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥)
    (hr : m.r = 5) (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt m.Lbar 10) : m.C626gen := by
  obtain ⟨D⟩ := exists_A10Setup_of_Lbar hL.1 hr hOL hA
  exact D.c626gen_A10 hL.1 hr

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
