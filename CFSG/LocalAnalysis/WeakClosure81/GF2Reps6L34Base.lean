module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourWith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Aut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Model
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Wit
import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open Subgroup CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.GH74.Uniqueness.Bender

private def g₁S : S := ⟨g₁, g₁_mem_S⟩

private def g₂S : S := ⟨g₂, g₂_mem_S⟩

private def g₃S : S := ⟨g₃, g₃_mem_S⟩

private def h₃S : S := ⟨h₃, wordPerm_mem _⟩

private def x₂S : S := ⟨x₂, wordPerm_mem _⟩

private def k₂S : S := ⟨k₂, wordPerm_mem _⟩

private def k₂S' : S := ⟨k₂', wordPerm_mem _⟩

private def x₃S : S := ⟨x₃, wordPerm_mem _⟩

private def k₃S : S := ⟨k₃, wordPerm_mem _⟩

private theorem map_autFixed (r : R) :
    (autFixed (conjAutS r)).map S.subtype =
      Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S := by
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simpa using (mem_autFixed_conjAutS (r := r) (s := y)).mp hy
  · intro hs
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsC, hsS⟩ := hs
    refine ⟨⟨s, hsS⟩, ?_, rfl⟩
    rw [mem_autFixed_conjAutS]
    exact Subgroup.mem_centralizer_iff.mp hsC r (by simp)

private theorem isSimple_autFixed (r : R)
    (h : IsSimpleGroup
      (Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S : Subgroup (Equiv.Perm (Fin 42)))) :
    IsSimpleGroup (autFixed (conjAutS r)) := by
  haveI := h
  exact MulEquiv.isSimpleGroup
    ((Subgroup.equivMapOfInjective (autFixed (conjAutS r)) S.subtype
      S.subtype_injective).trans (MulEquiv.subgroupCongr (map_autFixed r)))

private theorem centralizer_autFixed (r : R)
    (h : ∀ s : Equiv.Perm (Fin 42), s ∈ R → s * s = 1 →
      s * (r : Equiv.Perm (Fin 42)) = (r : Equiv.Perm (Fin 42)) * s →
      (∀ c ∈ Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S, s * c = c * s) →
      s = 1 ∨ s = (r : Equiv.Perm (Fin 42)))
    {B : Subgroup (MulAut S)} (hB2 : ∀ b ∈ B, b * b = 1) (hβ : conjAutS r ∈ B) :
    ∀ b ∈ B, (∀ y ∈ autFixed (conjAutS r), b y = y) → b = 1 ∨ b = conjAutS r := by
  intro b hb hfix
  obtain ⟨s, rfl⟩ := conjAutS_surjective b
  have hs2 : (s : Equiv.Perm (Fin 42)) * s = 1 := mul_self_of_mem hB2 hb
  have hcomm : (s : Equiv.Perm (Fin 42)) * r = r * s := commute_of_mem hB2 hb hβ
  have hC : ∀ c ∈ Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S,
      (s : Equiv.Perm (Fin 42)) * c = c * s := by
    intro c hc
    obtain ⟨hcC, hcS⟩ := Subgroup.mem_inf.mp hc
    have hmem : (⟨c, hcS⟩ : S) ∈ autFixed (conjAutS r) := by
      rw [mem_autFixed_conjAutS]
      exact Subgroup.mem_centralizer_iff.mp hcC r (by simp)
    have hval : (s : Equiv.Perm (Fin 42)) * c * (s : Equiv.Perm (Fin 42))⁻¹ = c := by
      have := congrArg (fun t : S => (t : Equiv.Perm (Fin 42))) (hfix ⟨c, hcS⟩ hmem)
      simpa [conjAutS_apply] using this
    calc (s : Equiv.Perm (Fin 42)) * c
        = ((s : Equiv.Perm (Fin 42)) * c * (s : Equiv.Perm (Fin 42))⁻¹) *
            (s : Equiv.Perm (Fin 42)) := by group
      _ = c * s := by rw [hval]
  rcases h (s : Equiv.Perm (Fin 42)) s.2 hs2 hcomm hC with h1 | h2
  · left
    rw [show s = 1 from Subtype.ext h1, map_one]
  · right
    rw [show s = r from Subtype.ext h2]

private theorem fourGen_of_aux {B : Subgroup (MulAut S)}
    {r : R} {x k : S} (hle : autFixed (conjAutS r) ≤ commY B (conjAutS r))
    (hβ2 : conjAutS r * conjAutS r = 1)
    (hord : orderOf ((conjAutS r) x * x⁻¹) = 4)
    (hk : k * ((conjAutS r) k)⁻¹ =
      (conjAutS r) (((conjAutS r) x * x⁻¹) ^
        (orderOf ((conjAutS r) x * x⁻¹) / 2)))
    (hgen : autFixed (conjAutS r) ⊔
      (autFixed (conjAutS r)).map (MulAut.conj k).toMonoidHom = ⊤) :
    orderOf (conjAutS r * (MulAut.conj x * conjAutS r * (MulAut.conj x)⁻¹)) = 4 ∧
      FourGen B (conjAutS r) x := by
  have hker : (MulAut.conj : S →* MulAut S).ker = ⊥ := by
    rw [CFSG.GroupTheory.ker_conj_eq_center, center_eq_bot]
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hββ : conjAutS r * (MulAut.conj x * conjAutS r * (MulAut.conj x)⁻¹) =
      MulAut.conj ((conjAutS r) x * x⁻¹) := mul_conj_mul_conj_inv hβ2 x
  refine ⟨?_, ?_⟩
  · rw [hββ, orderOf_injective (MulAut.conj : S →* MulAut S) hinj]
    exact hord
  · exact FourGenWith.fourGen hle (fourGenWith_of center_eq_bot hβ2 hk hgen)

private theorem orderOf_w_r₂ :
    orderOf ((conjAutS r₂R) x₂S * x₂S⁻¹) = 4 := by
  have hcoe : (((conjAutS r₂R) x₂S * x₂S⁻¹ : S) : Equiv.Perm (Fin 42)) =
      r₂ * x₂ * r₂⁻¹ * x₂⁻¹ := by
    simp [x₂S, r₂R, conjAutS_apply]
  rw [← Subgroup.orderOf_coe ((conjAutS r₂R) x₂S * x₂S⁻¹), hcoe, orderOf_r₂_x₂]

private theorem orderOf_w_r₂' :
    orderOf ((conjAutS r₂R) x₂S⁻¹ * x₂S) = 4 := by
  have hcoe : (((conjAutS r₂R) x₂S⁻¹ * x₂S : S) : Equiv.Perm (Fin 42)) =
      r₂ * x₂⁻¹ * r₂⁻¹ * x₂ := by
    simp [x₂S, r₂R, conjAutS_apply]
    group
  rw [← Subgroup.orderOf_coe ((conjAutS r₂R) x₂S⁻¹ * x₂S), hcoe, orderOf_r₂_x₂_inv]

private theorem hk_r₂ :
    k₂S * ((conjAutS r₂R) k₂S)⁻¹ =
      (conjAutS r₂R) (((conjAutS r₂R) x₂S * x₂S⁻¹) ^
        (orderOf ((conjAutS r₂R) x₂S * x₂S⁻¹) / 2)) := by
  apply Subtype.ext
  rw [orderOf_w_r₂, show (4 / 2 : ℕ) = 2 by norm_num]
  change k₂ * (r₂ * k₂ * r₂⁻¹)⁻¹ = r₂ * (r₂ * x₂ * r₂⁻¹ * x₂⁻¹) ^ 2 * r₂⁻¹
  exact k₂_mul_inv

private theorem hk_r₂' :
    k₂S' * ((conjAutS r₂R) k₂S')⁻¹ =
      (conjAutS r₂R) (((conjAutS r₂R) x₂S⁻¹ * x₂S) ^
        (orderOf ((conjAutS r₂R) x₂S⁻¹ * x₂S) / 2)) := by
  apply Subtype.ext
  rw [orderOf_w_r₂', show (4 / 2 : ℕ) = 2 by norm_num]
  change k₂' * (r₂ * k₂' * r₂⁻¹)⁻¹ = r₂ * (r₂ * x₂⁻¹ * r₂⁻¹ * x₂) ^ 2 * r₂⁻¹
  exact k₂'_mul_inv

private theorem hgen_r₂ :
    autFixed (conjAutS r₂R) ⊔
      (autFixed (conjAutS r₂R)).map (MulAut.conj k₂S).toMonoidHom = ⊤ := by
  let H : Subgroup S := autFixed (conjAutS r₂R) ⊔
    (autFixed (conjAutS r₂R)).map (MulAut.conj k₂S).toMonoidHom
  have h₁ : g₁S ∈ autFixed (conjAutS r₂R) := by
    rw [mem_autFixed_conjAutS]
    simpa [g₁S, r₂R] using g₁_mul_r₂.symm
  have h₂ : g₂S ∈ autFixed (conjAutS r₂R) := by
    rw [mem_autFixed_conjAutS]
    simpa [g₂S, r₂R] using g₂_mul_r₂.symm
  have h₁H : g₁S ∈ H := Subgroup.mem_sup_left h₁
  have h₂H : g₂S ∈ H := Subgroup.mem_sup_left h₂
  have hk₁ : MulAut.conj k₂S g₁S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ h₁)
  have hk₂ : MulAut.conj k₂S g₂S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ h₂)
  change H = ⊤
  have h₃eq : g₃S = MulAut.conj k₂S g₂S * g₁S⁻¹ * (MulAut.conj k₂S g₁S) * g₂S *
      (MulAut.conj k₂S g₁S)⁻¹ * g₁S := by
    apply Subtype.ext
    simpa [g₁S, g₂S, g₃S, k₂S, MulAut.conj_apply] using g₃_eq_of_k₂
  refine eq_top_of_mem h₁H h₂H ?_
  change g₃S ∈ H
  rw [h₃eq]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hk₂ (Subgroup.inv_mem H h₁H)) hk₁) h₂H)
    (Subgroup.inv_mem H hk₁)) h₁H

private theorem hgen_r₂' :
    autFixed (conjAutS r₂R) ⊔
      (autFixed (conjAutS r₂R)).map (MulAut.conj k₂S').toMonoidHom = ⊤ := by
  let H : Subgroup S := autFixed (conjAutS r₂R) ⊔
    (autFixed (conjAutS r₂R)).map (MulAut.conj k₂S').toMonoidHom
  have h₁ : g₁S ∈ autFixed (conjAutS r₂R) := by
    rw [mem_autFixed_conjAutS]
    simpa [g₁S, r₂R] using g₁_mul_r₂.symm
  have h₂ : g₂S ∈ autFixed (conjAutS r₂R) := by
    rw [mem_autFixed_conjAutS]
    simpa [g₂S, r₂R] using g₂_mul_r₂.symm
  have h₁H : g₁S ∈ H := Subgroup.mem_sup_left h₁
  have h₂H : g₂S ∈ H := Subgroup.mem_sup_left h₂
  have hk₁ : MulAut.conj k₂S' g₁S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ h₁)
  have hk₂ : MulAut.conj k₂S' g₂S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ h₂)
  change H = ⊤
  have h₃eq : g₃S = g₁S * (MulAut.conj k₂S' g₁S)⁻¹ * g₂S * (MulAut.conj k₂S' g₁S) *
      g₁S⁻¹ * (MulAut.conj k₂S' g₂S) := by
    apply Subtype.ext
    simpa [g₁S, g₂S, g₃S, k₂S', MulAut.conj_apply] using g₃_eq_of_k₂'
  refine eq_top_of_mem h₁H h₂H ?_
  change g₃S ∈ H
  rw [h₃eq]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h₁H (Subgroup.inv_mem H hk₁)) h₂H) hk₁)
    (Subgroup.inv_mem H h₁H)) hk₂

private theorem orderOf_w_r₃ :
    orderOf ((conjAutS r₃R) x₃S * x₃S⁻¹) = 4 := by
  have hcoe : (((conjAutS r₃R) x₃S * x₃S⁻¹ : S) : Equiv.Perm (Fin 42)) =
      r₃ * x₃ * r₃⁻¹ * x₃⁻¹ := by
    simp [x₃S, r₃R, conjAutS_apply]
  rw [← Subgroup.orderOf_coe ((conjAutS r₃R) x₃S * x₃S⁻¹), hcoe, orderOf_r₃_x₃]

private theorem hk_r₃ :
    k₃S * ((conjAutS r₃R) k₃S)⁻¹ =
      (conjAutS r₃R) (((conjAutS r₃R) x₃S * x₃S⁻¹) ^
        (orderOf ((conjAutS r₃R) x₃S * x₃S⁻¹) / 2)) := by
  apply Subtype.ext
  rw [orderOf_w_r₃, show (4 / 2 : ℕ) = 2 by norm_num]
  change k₃ * (r₃ * k₃ * r₃⁻¹)⁻¹ = r₃ * (r₃ * x₃ * r₃⁻¹ * x₃⁻¹) ^ 2 * r₃⁻¹
  exact k₃_mul_inv

private theorem hgen_r₃ :
    autFixed (conjAutS r₃R) ⊔
      (autFixed (conjAutS r₃R)).map (MulAut.conj k₃S).toMonoidHom = ⊤ := by
  let H : Subgroup S := autFixed (conjAutS r₃R) ⊔
    (autFixed (conjAutS r₃R)).map (MulAut.conj k₃S).toMonoidHom
  have h₁ : g₁S ∈ autFixed (conjAutS r₃R) := by
    rw [mem_autFixed_conjAutS]
    simpa [g₁S, r₃R] using g₁_mul_r₃.symm
  have hh : h₃S ∈ autFixed (conjAutS r₃R) := by
    rw [mem_autFixed_conjAutS]
    simpa [h₃S, r₃R] using h₃_mul_r₃.symm
  have h₁H : g₁S ∈ H := Subgroup.mem_sup_left h₁
  have hhH : h₃S ∈ H := Subgroup.mem_sup_left hh
  have hk₁ : MulAut.conj k₃S g₁S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ h₁)
  have hkh : MulAut.conj k₃S h₃S ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hh)
  change H = ⊤
  have h₂eq : g₂S = h₃S * g₁S⁻¹ * h₃S⁻¹ * g₁S * h₃S * (MulAut.conj k₃S g₁S) := by
    apply Subtype.ext
    simpa [g₁S, g₂S, h₃S, k₃S, MulAut.conj_apply] using g₂_eq_of_k₃
  have h₂ : g₂S ∈ H := by
    rw [h₂eq]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hhH (Subgroup.inv_mem H h₁H))
      (Subgroup.inv_mem H hhH)) h₁H) hhH) hk₁
  have h₃eq : g₃S = MulAut.conj k₃S g₁S * (MulAut.conj k₃S h₃S)⁻¹ *
      (MulAut.conj k₃S h₃S)⁻¹ * (MulAut.conj k₃S g₁S) := by
    apply Subtype.ext
    simpa [g₁S, g₃S, h₃S, k₃S, MulAut.conj_apply] using g₃_eq_of_k₃
  refine eq_top_of_mem h₁H h₂ ?_
  change g₃S ∈ H
  rw [h₃eq]
  exact mul_mem (mul_mem (mul_mem hk₁ (Subgroup.inv_mem H hkh)) (Subgroup.inv_mem H hkh)) hk₁

theorem fourGen_r₂
    {B : Subgroup (MulAut S)} (hB4 : Nat.card B = 4) (hB2 : ∀ b ∈ B, b * b = 1)
    (hβ : conjAutS r₂R ∈ B) :
    ∃ x : S, orderOf (conjAutS r₂R * (MulAut.conj x * conjAutS r₂R * (MulAut.conj x)⁻¹)) = 4 ∧
      FourGen B (conjAutS r₂R) x ∧ FourGen B (conjAutS r₂R) x⁻¹ := by
  have hβ2 : conjAutS r₂R * conjAutS r₂R = 1 := hB2 _ hβ
  have hs : IsSimpleGroup (autFixed (conjAutS r₂R)) :=
    isSimple_autFixed r₂R isSimpleGroup_C₂
  have hc := centralizer_autFixed r₂R
    (fun s hsR hs2 hcomm hC => eq_one_or_eq_r₂ hsR hs2 hcomm (by simpa [C₂, r₂R] using hC))
    hB2 hβ
  have hle : autFixed (conjAutS r₂R) ≤ commY B (conjAutS r₂R) :=
    autFixed_le_commY hB4 hB2 hβ hs hc
  obtain ⟨hord, hx⟩ := fourGen_of_aux hle hβ2 orderOf_w_r₂ hk_r₂ hgen_r₂
  have hx' : FourGen B (conjAutS r₂R) x₂S⁻¹ :=
    (fourGen_of_aux (x := x₂S⁻¹) (k := k₂S') hle hβ2 orderOf_w_r₂' hk_r₂' hgen_r₂').2
  exact ⟨x₂S, hord, hx, hx'⟩

theorem fourGen_r₃
    {B : Subgroup (MulAut S)} (hB4 : Nat.card B = 4) (hB2 : ∀ b ∈ B, b * b = 1)
    (hβ : conjAutS r₃R ∈ B) :
    ∃ x : S, orderOf (conjAutS r₃R * (MulAut.conj x * conjAutS r₃R * (MulAut.conj x)⁻¹)) = 4 ∧
      FourGen B (conjAutS r₃R) x ∧ FourGen B (conjAutS r₃R) x⁻¹ := by
  have hβ2 : conjAutS r₃R * conjAutS r₃R = 1 := hB2 _ hβ
  have hs : IsSimpleGroup (autFixed (conjAutS r₃R)) :=
    isSimple_autFixed r₃R isSimpleGroup_C₃
  have hc := centralizer_autFixed r₃R
    (fun s hsR hs2 hcomm hC => eq_one_or_eq_r₃ hsR hs2 hcomm (by simpa [C₃, r₃R] using hC))
    hB2 hβ
  have hle : autFixed (conjAutS r₃R) ≤ commY B (conjAutS r₃R) :=
    autFixed_le_commY hB4 hB2 hβ hs hc
  obtain ⟨hord, hx⟩ := fourGen_of_aux hle hβ2 orderOf_w_r₃ hk_r₃ hgen_r₃
  have hxinv : x₃S⁻¹ = x₃S := mul_eq_one_iff_inv_eq.mp (Subtype.ext x₃_mul_self)
  exact ⟨x₃S, hord, hx, by simpa [hxinv] using hx⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
