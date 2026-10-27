module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrAN

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

theorem wrT_mul_self : wrT * wrT = 1 :=
  RegularWreathProduct.ext
    (funext fun q => by rw [left_mul_apply, wrT_left, wrT_left, mul_one]; rfl)
    (by rw [right_mul, wrT_right, zs_mul_zs]; rfl)

theorem hypFix_Ncl_wrT {A : Subgroup SymFiveWrTwo} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a * a = 1) (hT : wrT ∈ A) : HypFix Ncl A := by
  have hcoord : ∀ g ∈ A, g.left 1 = g.left zs := fun g hg =>
    left_one_eq_of_comm (hc g hg wrT hT)
  let D : Subgroup (Perm (Fin 5)) :=
    { carrier := {σ | ∃ g ∈ A, g.left zs = σ}
      one_mem' := ⟨1, A.one_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
        exact ⟨g * h, A.mul_mem hg hh, left_zs_mul (hcoord h hh)⟩
      inv_mem' := by
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨g⁻¹, A.inv_mem hg, left_zs_inv (hcoord g hg)⟩ }
  have hDc : ∀ σ ∈ D, ∀ τ ∈ D, σ * τ = τ * σ := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← left_zs_mul (hcoord h hh), ← left_zs_mul (hcoord g hg), hc g hg h hh]
  have hD2 : ∀ σ ∈ D, σ * σ = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← left_zs_mul (hcoord g hg), h2 g hg]
    rfl
  have hgP : ∀ g ∈ A, ∀ u, gP g (tens u u) = tens (pv (g.left zs) u) (pv (g.left zs) u) := by
    intro g hg u
    rcases zmod2_cases g.right with hr | hr
    · rw [gP_tens_base hr, hcoord g hg]
    · rw [gP_tens_swap hr, hcoord g hg]
  by_cases hD : D = ⊥
  · have hA1 : ∀ g ∈ A, g.left = 1 := fun g hg => by
      have hz : g.left zs = 1 := by
        have h1 : g.left zs ∈ D := ⟨g, hg, rfl⟩
        rw [hD, Subgroup.mem_bot] at h1
        exact h1
      funext q
      rcases zmod2_cases q with rfl | rfl
      · rw [hcoord g hg, hz]
        rfl
      · exact hz
    refine ⟨⊥, bot_le, ⟨wrT, hT, fun h => ?_, fun g hg => ?_⟩, tens (wv 4) (wv 3),
      tens_mem_Ncl (isO_wv 4) (isO_wv 3), fun b hb => ?_, wrT, hT, gP_wrT_tens_ne⟩
    · rw [Subgroup.mem_bot] at h
      exact zs_ne_one (congrArg RegularWreathProduct.right h)
    · rcases zmod2_cases g.right with hr | hr
      · exact Or.inl (Subgroup.mem_bot.mpr (RegularWreathProduct.ext (hA1 g hg) hr))
      · right
        rw [show g = wrT from RegularWreathProduct.ext (hA1 g hg) hr, wrT_mul_self]
        exact Subgroup.one_mem _
    · rw [Subgroup.mem_bot] at hb
      rw [hb, gP_one]
  · obtain ⟨D', -, ⟨x1, hx1, hx1D, hcov⟩, u, hu, hufix, d, hd, hdu⟩ :=
      exists_hyperplane_fix hDc hD2 hD
    let B : Subgroup SymFiveWrTwo :=
      { carrier := {g | g ∈ A ∧ g.left zs ∈ D'}
        one_mem' := ⟨A.one_mem, D'.one_mem⟩
        mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
          rw [left_zs_mul (hcoord b hb.1)]
          exact D'.mul_mem ha.2 hb.2⟩
        inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
          rw [left_zs_inv (hcoord a ha.1)]
          exact D'.inv_mem ha.2⟩ }
    obtain ⟨x, hxA, rfl⟩ := hx1
    obtain ⟨gd, hgdA, rfl⟩ := hd
    refine ⟨B, fun _ h => h.1, ⟨x, hxA, fun h => hx1D h.2, fun g hg => ?_⟩, tens u u,
      tens_mem_Ncl hu hu, fun b hb => ?_, gd, hgdA, fun h => hdu ?_⟩
    · rcases hcov _ ⟨g, hg, rfl⟩ with h | h
      · exact Or.inl ⟨hg, h⟩
      · exact Or.inr ⟨A.mul_mem hg hxA, by rw [left_zs_mul (hcoord x hxA)]; exact h⟩
    · rw [hgP b hb.1, hufix _ hb.2]
    · rw [hgP gd hgdA] at h
      exact eq_of_tens_diag h

theorem exists_conj_wrT {t : SymFiveWrTwo} (htz : t.right = zs) (ht2 : t * t = 1) :
    ∃ c : SymFiveWrTwo, c * t * c⁻¹ = wrT := by
  have hf : t.left 1 * t.left zs = 1 := by
    have h1 : (t * t).left 1 = (1 : SymFiveWrTwo).left 1 := by rw [ht2]
    rw [left_mul_apply, htz, zs_inv_mul_one] at h1
    exact h1
  let k : Multiplicative (ZMod 2) → Perm (Fin 5) := fun q => if q = 1 then 1 else t.left 1
  have hcr : (wrBaseHom k).right = 1 := wrBaseHom_right k
  have hr : (wrBaseHom k * t).right = zs := by
    rw [right_mul, hcr, htz]
    decide
  have key : ∀ q, (wrBaseHom k * t * (wrBaseHom k)⁻¹).left q =
      k q * t.left q * (k (zs⁻¹ * q))⁻¹ := by
    intro q
    rw [left_mul_apply, left_mul_base hcr, inv_left_base hcr, hr]
    rfl
  refine ⟨wrBaseHom k, RegularWreathProduct.ext (funext fun q => ?_) ?_⟩
  · rw [key, wrT_left]
    rcases zmod2_cases q with rfl | rfl
    · rw [zs_inv_mul_one]
      simp [k]
    · rw [zs_inv_mul_zs]
      simp [k, hf]
  · rw [right_mul, hr, inv_right_base hcr]
    decide

theorem hypFix_Ncl {A : Subgroup SymFiveWrTwo} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a * a = 1) (hA : A ≠ ⊥) : HypFix Ncl A := by
  by_cases hbase : ∀ g ∈ A, g.right = 1
  · exact hypFix_Ncl_base hc h2 hA hbase
  · push Not at hbase
    obtain ⟨t, htA, ht⟩ := hbase
    have htz : t.right = zs := (zmod2_cases t.right).resolve_left ht
    obtain ⟨c, hct⟩ := exists_conj_wrT htz (h2 t htA)
    apply hypFix_of_conj (fun g v hv => gP_mem_Ncl g hv) c
    apply hypFix_Ncl_wrT
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, h2 a ha, map_one]
    · exact ⟨t, htA, hct⟩

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
