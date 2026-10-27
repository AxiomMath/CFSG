module

public import CFSG.Quasithin.Vol2.Ch10SecA1011C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def quotBotEquiv (X : Subgroup G) [((⊥ : Subgroup G).subgroupOf X).Normal] :
    ↥X ⧸ (⊥ : Subgroup G).subgroupOf X ≃* ↥X :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf X)).trans QuotientGroup.quotientBot

theorem quotBotEquiv_mk (X : Subgroup G) [((⊥ : Subgroup G).subgroupOf X).Normal] (x : ↥X) :
    quotBotEquiv X (x : ↥X ⧸ (⊥ : Subgroup G).subgroupOf X) = x :=
  rfl

theorem quotBotEquiv_symm_apply (X : Subgroup G) [((⊥ : Subgroup G).subgroupOf X).Normal]
    (x : ↥X) : (quotBotEquiv X).symm x = (x : ↥X ⧸ (⊥ : Subgroup G).subgroupOf X) := by
  rw [MulEquiv.symm_apply_eq, quotBotEquiv_mk]

@[expose] def conjugateEquiv (W : Subgroup G) (s : G) : ↥(CFSG.conjugate W s) ≃* ↥W where
  toFun y := ⟨s * y * s⁻¹, mem_conjugate_iff.mp y.2⟩
  invFun w := ⟨s⁻¹ * w * s, mem_conjugate_iff.mpr (by simp [mul_assoc])⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjugateEquiv_apply (W : Subgroup G) (s : G) (y : ↥(CFSG.conjugate W s)) :
    ((conjugateEquiv W s y : ↥W) : G) = s * y * s⁻¹ :=
  rfl

variable [Finite G] {T L I : Subgroup G}

theorem not_isXSectionIso_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {W : Subgroup G} {s : G} (hsT : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hsO : s ∉ L ⊔ pCoreOf 2 (L ⊔ T ⊓ Subgroup.normalizer (L : Set G)))
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (htop : autOn L W = ⊤)
    (hC : L ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 L) :
    ¬ IsXSectionIso L ⊥ W (CFSG.conjugate W s) := by
  rintro ⟨hJ, hK, e, he⟩
  set f : ↥W ≃* ↥(CFSG.conjugate W s) :=
    ((quotBotEquiv W).symm.trans e).trans (quotBotEquiv _) with hfdef
  have hfe : ∀ x : ↥W, e (x : ↥W ⧸ (⊥ : Subgroup G).subgroupOf W) =
      ((f x : ↥(CFSG.conjugate W s)) : ↥(CFSG.conjugate W s) ⧸
        (⊥ : Subgroup G).subgroupOf (CFSG.conjugate W s)) := by
    intro x
    have h1 : (quotBotEquiv (CFSG.conjugate W s)).symm (f x) = e ((quotBotEquiv W).symm x) := by
      simp [hfdef]
    rw [quotBotEquiv_symm_apply, quotBotEquiv_symm_apply] at h1
    exact h1.symm
  have hLWs : L ≤ Subgroup.normalizer (CFSG.conjugate W s : Set G) := by
    intro l hl
    have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have hw : CFSG.conjugate W (s * l * s⁻¹) = W := conjugate_eq_self_iff.mpr (hLW hsl)
    rw [← conjugate_eq_self_iff, conjugate_conjugate,
      show s * l = (s * l * s⁻¹) * s by group, ← conjugate_conjugate, hw]
  have hf : ∀ (l : G) (hl : l ∈ L) (x : ↥W),
      ((f ⟨l * x * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hLW hl) _).mp x.2⟩ :
        ↥(CFSG.conjugate W s)) : G) = l * (f x : G) * l⁻¹ := by
    intro l hl x
    have h1 := he l hl x (f x) ((Subgroup.mem_normalizer_iff.mp (hLW hl) _).mp x.2)
      ((Subgroup.mem_normalizer_iff.mp (hLWs hl) _).mp (f x).2) (hfe x)
    rw [hfe] at h1
    have h2 := congrArg (quotBotEquiv _) h1
    rw [quotBotEquiv_mk, quotBotEquiv_mk] at h2
    exact congrArg Subtype.val h2
  set g : MulAut ↥W := f.trans (conjugateEquiv W s) with hgdef
  have hgmem : g ∈ autOn L W := htop ▸ Subgroup.mem_top g
  obtain ⟨x0, hx0L, hx0g⟩ := Subgroup.mem_map.mp hgmem
  have hl0L : (x0 : G) ∈ L := hx0L
  have hg : ∀ w : ↥W, ((g w : ↥W) : G) = (x0 : G) * w * (x0 : G)⁻¹ := by
    intro w
    rw [← hx0g]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl x0) w
  have hgf : ∀ y : ↥W, ((g y : ↥W) : G) = s * (f y : G) * s⁻¹ := fun _ => rfl
  have hkey : ∀ l ∈ L, ∀ w ∈ W, ((x0 : G) * l) * w * ((x0 : G) * l)⁻¹ =
      (s * l * s⁻¹ * x0) * w * (s * l * s⁻¹ * x0)⁻¹ := by
    intro l hl w hw
    have hlw : l * w * l⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW hl) _).mp hw
    have e1 := hg ⟨l * w * l⁻¹, hlw⟩
    have e2 := hg ⟨w, hw⟩
    rw [hgf, hf l hl ⟨w, hw⟩] at e1
    rw [hgf] at e2
    have hfw : (f ⟨w, hw⟩ : G) = s⁻¹ * ((x0 : G) * w * (x0 : G)⁻¹) * s := by
      rw [← e2]
      group
    rw [hfw] at e1
    calc ((x0 : G) * l) * w * ((x0 : G) * l)⁻¹ = (x0 : G) * (l * w * l⁻¹) * (x0 : G)⁻¹ := by
          group
      _ = s * (l * (s⁻¹ * ((x0 : G) * w * (x0 : G)⁻¹) * s) * l⁻¹) * s⁻¹ := e1.symm
      _ = _ := by group
  have hcq : (x0 : G)⁻¹ * s ∈ centQuot T L := by
    refine ⟨(L ⊔ T1 T L).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl0L))
      (Subgroup.mem_sup_right ⟨hsT, hsN⟩), fun l hl => ?_⟩
    have hv : (s * l⁻¹ * s⁻¹ * x0)⁻¹ * ((x0 : G) * l⁻¹) ∈
        L ⊓ Subgroup.centralizer (W : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hsl : s * l⁻¹ * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN _).mp (L.inv_mem hl)
        exact L.mul_mem (L.inv_mem (L.mul_mem hsl hl0L)) (L.mul_mem hl0L (L.inv_mem hl))
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 := hkey l⁻¹ (L.inv_mem hl) w hw
        calc w * ((s * l⁻¹ * s⁻¹ * x0)⁻¹ * ((x0 : G) * l⁻¹))
            = (s * l⁻¹ * s⁻¹ * x0)⁻¹ * ((s * l⁻¹ * s⁻¹ * x0) * w * (s * l⁻¹ * s⁻¹ * x0)⁻¹) *
              ((x0 : G) * l⁻¹) := by group
          _ = (s * l⁻¹ * s⁻¹ * x0)⁻¹ * (((x0 : G) * l⁻¹) * w * ((x0 : G) * l⁻¹)⁻¹) *
              ((x0 : G) * l⁻¹) := by rw [h1]
          _ = _ := by group
    have heq : ⁅(x0 : G)⁻¹ * s, l⁆ = (s * l⁻¹ * s⁻¹ * x0)⁻¹ * ((x0 : G) * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact hC hv
  have hx := centQuot_le_pCoreOf h37 h38 hyp hcq
  apply hsO
  have hs : s = (x0 : G) * ((x0 : G)⁻¹ * s) := by group
  rw [hs]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl0L) (Subgroup.mem_sup_right hx)

end CFSG.Quasithin.Vol2.Ch10.SecA
