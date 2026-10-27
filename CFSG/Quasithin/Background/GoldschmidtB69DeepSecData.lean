module

public import CFSG.Quasithin.Background.FFC11D

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionFittingData (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hH : CompHyp X T M A L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    ∃ ℓ : ↥L →* ↥(autSec L W (W ⊓ fixV L)), Function.Surjective ℓ ∧
      ℓ.ker ≤ Subgroup.center ↥L ∧ CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) ∧
      XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ ∧
      quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) ∧
      (∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
        g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L)) ∧
      ∀ (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub (W ⊓ fixV L)) (l : ↥L),
        ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) =
          B5.secHom L hLW hLU l := by
  obtain ⟨-, -, -, -, -, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hsupn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hy
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq2 : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  obtain ⟨ℓ, hℓs, hℓa⟩ : ∃ ℓ : ↥L →* ↥(autSec L W (W ⊓ fixV L)), Function.Surjective ℓ ∧
      ∀ l : ↥L, ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) =
        B5.secHom L hLW hLZ l := by
    refine ⟨(B5.secHom L hLW hLZ).codRestrict (autSec L W (W ⊓ fixV L)) (fun l => ?_), ?_,
      fun l => rfl⟩
    · rw [← B5.range_secHom L hLW hLZ]
      exact ⟨l, rfl⟩
    · intro y
      have hy : (y : MulAut (Sec W (W ⊓ fixV L))) ∈ (B5.secHom L hLW hLZ).range := by
        rw [B5.range_secHom L hLW hLZ]
        exact y.2
      obtain ⟨l, hl⟩ := hy
      exact ⟨l, Subtype.ext hl⟩
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_left : L ≤ L ⊔ A)
  have hrange := B5.range_secHom (L ⊔ A) hMW hMZ
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) :=
    autSec_mono le_sup_left W _
  have hLbn : ∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
      g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L) := by
    intro g hg l hl
    rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [← hmapL] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨m * l' * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    exact hsupn m m.2 l' hl'
  have hHb2 : ∀ y ∈ autSec (L ⊔ A) W (W ⊓ fixV L), y ^ 2 ∈ autSec L W (W ⊓ fixV L) := by
    intro y hy
    rw [← hrange] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [← hmapL]
    refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp [map_pow]⟩
    rw [Subgroup.mem_subgroupOf]
    exact hsq2 m m.2
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq ℓ.ker hne
  have hLbq : CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective (B1Red.isQuasisimple_of_open hLq) ℓ hℓs hcent
  obtain ⟨-, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have hIrr : XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ :=
    B5.isIrrSec_autSec hlt hirr hLW hLZ
  have hO2G : pCoreOf 2 (autSec (L ⊔ A) W (W ⊓ fixV L)) = ⊥ := n1_pCoreOf_eq_bot hS2 hLG hIrr
  have hFstar : quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hLbn (B1Red.isQuasisimple_to_open hLbq) hHb2 hO2G
  exact ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, fun _ _ l => hℓa l⟩

end B69

end CFSG.Quasithin
