module

public import CFSG.Quasithin.Background.HL3WrModel
public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix

@[expose] def decPair (a b : Fin 3) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if a = b then
    (if a = 0 then (!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 1, 0; 1, 0, 0; 0, 0, 1])
      else if a = 1 then (!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 1, 1; 0, 1, 0])
      else (!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 1]))
  else (1 + single a b 1, 1)

theorem decPair_spec (a b : Fin 3) : (decPair a b).1 + (decPair a b).2 = single a b 1 ∧
    (decPair a b).1.det ≠ 0 ∧ (decPair a b).2.det ≠ 0 := by
  fin_cases a <;> fin_cases b <;>
    exact ⟨by decide, by rw [det_fin_three]; decide, by rw [det_fin_three]; decide⟩

@[expose] noncomputable def ofMat (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det ≠ 0) : ↥SL32 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, mem_SL32 _⟩

theorem mat_ofMat (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : A.det ≠ 0) : mat (ofMat A h) = A :=
  rfl

theorem exists_sum_single (a b : Fin 3) : ∃ g₁ g₂ : ↥SL32, mat g₁ + mat g₂ = single a b 1 := by
  obtain ⟨hs, h₁, h₂⟩ := decPair_spec a b
  exact ⟨ofMat _ h₁, ofMat _ h₂, by rw [mat_ofMat, mat_ofMat, hs]⟩

theorem eq_top_of_invariant {J : Subgroup WMod} (hJ : ∀ γ, ∀ x ∈ J, rho γ x ∈ J)
    (hne : J ≠ ⊥) : J = ⊤ := by
  have hadd : ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), Multiplicative.ofAdd A ∈ J →
      Multiplicative.ofAdd B ∈ J → Multiplicative.ofAdd (A + B) ∈ J := fun A B hA hB => by
    rw [ofAdd_add]
    exact J.mul_mem hA hB
  have hleft : ∀ (g : ↥SL32) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      Multiplicative.ofAdd A ∈ J → Multiplicative.ofAdd (mat g * A) ∈ J := by
    intro g A hA
    have h1 := hJ (g, 1) _ hA
    have e : rho (g, 1) (Multiplicative.ofAdd A) = Multiplicative.ofAdd (mat g * A) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      show mat g * A * (mat 1)ᵀ = mat g * A
      rw [mat_one, transpose_one, Matrix.mul_one]
    rwa [e] at h1
  have hright : ∀ (g : ↥SL32) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      Multiplicative.ofAdd A ∈ J → Multiplicative.ofAdd (A * (mat g)ᵀ) ∈ J := by
    intro g A hA
    have h1 := hJ (1, g) _ hA
    have e : rho (1, g) (Multiplicative.ofAdd A) = Multiplicative.ofAdd (A * (mat g)ᵀ) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      show mat 1 * A * (mat g)ᵀ = A * (mat g)ᵀ
      rw [mat_one, Matrix.one_mul]
    rwa [e] at h1
  have hEl : ∀ (a b : Fin 3) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      Multiplicative.ofAdd A ∈ J → Multiplicative.ofAdd (single a b 1 * A) ∈ J := by
    intro a b A hA
    obtain ⟨g₁, g₂, e⟩ := exists_sum_single a b
    rw [← e, Matrix.add_mul]
    exact hadd _ _ (hleft g₁ A hA) (hleft g₂ A hA)
  have hEr : ∀ (a b : Fin 3) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      Multiplicative.ofAdd A ∈ J → Multiplicative.ofAdd (A * single a b 1) ∈ J := by
    intro a b A hA
    obtain ⟨g₁, g₂, e⟩ := exists_sum_single b a
    have e' : single a b (1 : ZMod 2) = (mat g₁)ᵀ + (mat g₂)ᵀ := by
      rw [← transpose_add, e, transpose_single]
    rw [e', Matrix.mul_add]
    exact hadd _ _ (hright g₁ A hA) (hright g₂ A hA)
  obtain ⟨⟨x, hxJ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hX : Multiplicative.ofAdd (Multiplicative.toAdd (x : WMod)) ∈ J := hxJ
  obtain ⟨i, j, hij⟩ : ∃ i j, Multiplicative.toAdd (x : WMod) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    ext a b
    exact hcon a b
  have hXij : Multiplicative.toAdd (x : WMod) i j = 1 := by
    revert hij
    generalize Multiplicative.toAdd (x : WMod) i j = c
    decide +revert
  have hall : ∀ k l : Fin 3, Multiplicative.ofAdd (single k l (1 : ZMod 2)) ∈ J := by
    intro k l
    have h1 := hEr j l _ (hEl k i _ hX)
    rwa [single_mul_mul_single, hXij, one_mul, mul_one] at h1
  rw [eq_top_iff]
  intro y _
  have hy : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := rfl
  rw [hy, matrix_eq_sum_single (Multiplicative.toAdd y)]
  refine Finset.sum_induction _ (fun A => Multiplicative.ofAdd A ∈ J) hadd J.one_mem
    fun a _ => Finset.sum_induction _ (fun A => Multiplicative.ofAdd A ∈ J) hadd J.one_mem
      fun b _ => ?_
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd y a b) with h | h
  · rw [h, single_zero]
    exact J.one_mem
  · rw [h]
    exact hall a b

@[expose] def fixW : Subgroup WMod where
  carrier := {X | ∀ γ, rho γ X = X}
  mul_mem' := fun {X Y} hX hY γ => by rw [map_mul, hX γ, hY γ]
  one_mem' := fun γ => map_one (rho γ)
  inv_mem' := fun {X} hX γ => (map_inv (rho γ) X).trans (congrArg (·⁻¹) (hX γ))

theorem fixW_eq_bot : fixW = ⊥ := by
  by_contra hne
  have htop := eq_top_of_invariant (J := fixW) (fun γ X hX => by rw [hX γ]; exact hX) hne
  have h1 : ∀ γ, rho γ = 1 := fun γ => MulEquiv.ext fun X => by
    have : X ∈ fixW := by rw [htop]; exact Subgroup.mem_top X
    exact this γ
  obtain ⟨hs, h₁, -⟩ := decPair_spec 0 1
  have h2 := rho_injective ((h1 (ofMat _ h₁, 1)).trans (h1 1).symm)
  have h3 : mat (ofMat _ h₁) = mat 1 := congrArg (fun g => mat g.1) h2
  rw [mat_ofMat, mat_one] at h3
  revert h3
  decide

end L3Wr

end H

end CFSG.Quasithin

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative


namespace Wr326

theorem mem_conjugate_iff {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem card_conjugate {G : Type} [Group G] (H : Subgroup G) (g : G) :
    Nat.card ↥(CFSG.conjugate H g) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

end Wr326

theorem eq_fsuV_of_row711L3Wreath {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) :
    I = fsuV T I := by
  obtain ⟨e, he⟩ := exists_model hrow.2
  have hIV : I ≤ fsuV T I := le_conjClosure I T
  have hL0I : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hfsu.irrPlus.2.2.1
  have hI1 : I ≠ ⊥ := hfsu.irrPlus.2.1
  set J := (I.subgroupOf (fsuV T I)).map e.toMonoidHom with hJdef
  have hJ : ∀ γ, ∀ x ∈ J, rho γ x ∈ J := by
    intro γ x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hγ : rho γ ∈ (autOn (fsuL0 T L) (fsuV T I)).map (H.congrHom e) := by
      rw [he]
      exact rho_mem_img γ
    obtain ⟨φ, hφ, hφe⟩ := hγ
    obtain ⟨g, hg, rfl⟩ := hφ
    have hgL : (g : G) ∈ fsuL0 T L := Subgroup.mem_subgroupOf.mp hg
    refine ⟨conjAct (fsuV T I) g u, ?_, ?_⟩
    · show conjAct (fsuV T I) g u ∈ I.subgroupOf (fsuV T I)
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((conjAct (fsuV T I) g u : ↥(fsuV T I)) : G) = (g : G) * u * (g : G)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe _ (Subgroup.inclusion le_rfl g) u
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp (hL0I hgL) u).mp (Subgroup.mem_subgroupOf.mp hu)
    · rw [← hφe]
      show e (conjAct (fsuV T I) g u) = e ((conjAct (fsuV T I) g) (e.symm (e u)))
      rw [MulEquiv.symm_apply_apply]
  have hne : J ≠ ⊥ := by
    intro hbot
    apply hI1
    rw [eq_bot_iff]
    intro x hx
    have h1 : e.toMonoidHom ⟨x, hIV hx⟩ ∈ J := ⟨⟨x, hIV hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hIV hx⟩ : ↥(fsuV T I)) = 1 := e.injective (h1.trans (map_one e).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hJtop := eq_top_of_invariant hJ hne
  refine le_antisymm hIV fun v hv => ?_
  have h1 : e ⟨v, hv⟩ ∈ J := by
    rw [hJtop]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, hue⟩ := h1
  have h2 : u = ⟨v, hv⟩ := e.injective hue
  have h3 := Subgroup.mem_subgroupOf.mp hu
  rw [h2] at h3
  exact h3

theorem fsuV_inf_centralizer_eq_bot_of_row711L3Wreath {G : Type} [Group G]
    {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) :
    fsuV T I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
  obtain ⟨e, he⟩ := exists_model hrow.2
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvC⟩
  have hfix : e ⟨v, hvV⟩ ∈ fixW := by
    intro γ
    have hγ : rho γ ∈ (autOn (fsuL0 T L) (fsuV T I)).map (H.congrHom e) := by
      rw [he]
      exact rho_mem_img γ
    obtain ⟨φ, ⟨g, hg, rfl⟩, hφe⟩ := hγ
    have hgL : (g : G) ∈ fsuL0 T L := Subgroup.mem_subgroupOf.mp hg
    rw [← hφe]
    show e (conjAct (fsuV T I) g (e.symm (e ⟨v, hvV⟩))) = e ⟨v, hvV⟩
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    have h1 : ((conjAct (fsuV T I) g ⟨v, hvV⟩ : ↥(fsuV T I)) : G) = (g : G) * v * (g : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe _ (Subgroup.inclusion le_rfl g) ⟨v, hvV⟩
    rw [h1, Subgroup.mem_centralizer_iff.mp hvC _ hgL, mul_inv_cancel_right]
  rw [fixW_eq_bot, Subgroup.mem_bot] at hfix
  have h2 : (⟨v, hvV⟩ : ↥(fsuV T I)) = 1 := e.injective (hfix.trans (map_one e).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h2

theorem isTISetUnder_of_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G]
    {T L I : Subgroup G} (hfsu : FSU G T L I)
    (hC : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) : IsTISetUnder I (fsuM T L) := by
  intro g hg hgn
  have hL0I : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hfsu.irrPlus.2.2.1
  have hirr := hfsu.irrPlus.2.2.2.2.2.1
  rw [hC] at hirr
  set J := I ⊓ CFSG.conjugate I g with hJ
  have hJL : fsuL0 T L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    have hgl : g * l * g⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
    have key : ∀ l' ∈ fsuL0 T L, ∀ x ∈ J, l' * x * l'⁻¹ ∈ J := by
      intro l' hl' x hx
      have hgl' : g * l' * g⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp hg l').mp hl'
      have hx1 : x ∈ I := hx.1
      have hx2 : g * x * g⁻¹ ∈ I := Wr326.mem_conjugate_iff.mp hx.2
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hL0I hl') x).mp hx1,
        Wr326.mem_conjugate_iff.mpr ?_⟩
      have e : g * (l' * x * l'⁻¹) * g⁻¹ =
          (g * l' * g⁻¹) * (g * x * g⁻¹) * (g * l' * g⁻¹)⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hL0I hgl') _).mp hx2
    intro x
    refine ⟨key l hl x, fun hx => ?_⟩
    have h1 := key l⁻¹ (inv_mem hl) _ hx
    have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hJI : J ≤ I := inf_le_left
  rcases hirr J bot_le hJI hJL with h1 | h1
  · exact h1
  · exfalso
    apply hgn
    have hJc : J ≤ CFSG.conjugate I g := inf_le_right
    have hle : I ≤ CFSG.conjugate I g := h1 ▸ hJc
    have heq : CFSG.conjugate I g = I :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [Wr326.card_conjugate])).symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← Wr326.mem_conjugate_iff (H := I) (g := g), heq]

theorem isTISetUnder_fsuV_of_row711L3Wreath {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) :
    I = fsuV T I ∧ IsTISetUnder (fsuV T I) (fsuM T L) := by
  have hIV := eq_fsuV_of_row711L3Wreath hfsu hrow
  have hC := fsuV_inf_centralizer_eq_bot_of_row711L3Wreath hrow
  refine ⟨hIV, ?_⟩
  have h1 := isTISetUnder_of_inf_centralizer_eq_bot hfsu (hIV ▸ hC)
  rwa [← hIV]

end CFSG.Quasithin.H13
