module

public import Certificates.Kernel.AE6Tri.FactsM
public import Certificates.Kernel.AE6Tri.Gamma
public import Certificates.Kernel.AE6Tri.Q

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT omegaT_eq gen)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

theorem coe_prod_map {α : Type} (f : α → AE6Om) : ∀ w : List α,
    (((w.map f).prod : AE6Om) : Equiv.Perm (Fin 360)) = (w.map fun j => (f j : Equiv.Perm (Fin 360))).prod
  | [] => rfl
  | a :: w => by simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, coe_prod_map f w]

theorem coe_ae6Word (w : List (Fin 8)) :
    ((ae6Word w : AE6Om) : Equiv.Perm (Fin 360)) = wv gP (w.map Fin.val) := by
  rw [ae6Word, coe_prod_map, wv, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => coe_curtisGen j

theorem word_mem {A : Set (Fin 8)} : ∀ w : List (Fin 8), (∀ j ∈ w, j ∈ A) →
    ae6Word w ∈ Subgroup.closure (A6.curtisGen '' A)
  | [], _ => Subgroup.one_mem _
  | a :: w, h => by
    rw [ae6Word, List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, h a (by simp), rfl⟩)
      (word_mem w fun j hj => h j (by simp [hj]))

theorem diag_get : ∀ c : Fin 2, (diag.getD c.val []).length = 8 ∧
    ∀ i : Fin 8, (diag.getD c.val []).getD i.val 0 = (ae6Diag c i).val := by decide

theorem gam_perm (c : Fin 2) :
    ∃ x : Equiv.Perm (Fin 360), ∀ i : Fin 8, x * gP i * x⁻¹ = gP (ae6Diag c i) := by
  have hk : gamOK RG (diag.getD c.val []) (xc.getD c.val 0) (xci.getD c.val 0) = true := by
    fin_cases c
    exacts [kGam0, kGam1]
  obtain ⟨x, -, hx⟩ := gamOK_sound gRep hk
  refine ⟨x, fun i => ?_⟩
  rw [hx i (by rw [(diag_get c).1]; exact i.isLt), (diag_get c).2 i]

theorem conj_mem {x : Equiv.Perm (Fin 360)} {d : Fin 8 → Fin 8}
    (hx : ∀ i : Fin 8, x * gP i * x⁻¹ = gP (d i)) {y : Equiv.Perm (Fin 360)} (hy : y ∈ omegaT) :
    x * y * x⁻¹ ∈ omegaT := by
  rw [omegaT_eq] at hy ⊢
  have hle : (Subgroup.closure {g | ∃ i < 8, gen i = g}).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.closure {g | ∃ i < 8, gen i = g} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨i, hi, rfl⟩, rfl⟩
    have e := hx ⟨i, hi⟩
    simp only [gP, if_pos hi, if_pos (d ⟨i, hi⟩).isLt] at e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨_, (d ⟨i, hi⟩).isLt, rfl⟩
  exact hle ⟨y, hy, rfl⟩

@[expose] noncomputable def conjHom (x : Equiv.Perm (Fin 360)) (d : Fin 8 → Fin 8)
    (hx : ∀ i : Fin 8, x * gP i * x⁻¹ = gP (d i)) : AE6Om →* AE6Om where
  toFun y := ⟨x * y * x⁻¹, conj_mem hx y.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjHom_injective (x : Equiv.Perm (Fin 360)) (d : Fin 8 → Fin 8)
    (hx : ∀ i : Fin 8, x * gP i * x⁻¹ = gP (d i)) : Function.Injective (conjHom x d hx) := by
  intro a b h
  apply Subtype.ext
  have e := congrArg Subtype.val h
  simpa [conjHom] using e

theorem gamma (c : Fin 2) :
    ∃ e : MulAut AE6Om, ∀ i, e (A6.curtisGen i) = A6.curtisGen (ae6Diag c i) := by
  obtain ⟨x, hx⟩ := gam_perm c
  have hi := conjHom_injective x _ hx
  refine ⟨MulEquiv.ofBijective (conjHom x _ hx) ⟨hi, Finite.surjective_of_injective hi⟩,
    fun i => ?_⟩
  apply Subtype.ext
  change x * (A6.curtisGen i : Equiv.Perm (Fin 360)) * x⁻¹ = _
  rw [coe_curtisGen, coe_curtisGen, hx i]

theorem delta_get : (dg.getD 0 []).length = 8 ∧ (delta.getD 0 []).length = 8 ∧
    ∀ i : Fin 8, (delta.getD 0 []).getD i.val [] = (ae6Delta 0 i).map Fin.val := by decide

@[expose] noncomputable def dP (c : Nat) : Equiv.Perm (Fin 360) := wv gP ((delta.getD 0 []).getD c [])

theorem dRep : GRep (dg.getD 0 []) dP := by
  intro c
  by_cases hc : c < 8
  · have h := pinOK_sound gRep kPinD 0 (by rw [shapes.2.2.1]; norm_num) c
      (by rw [delta_get.2.1]; exact hc)
    exact h
  · have e1 : gl (dg.getD 0 []) c = pidn 360 9 := by
      unfold gl
      rw [List.getD_eq_default _ _ (by rw [delta_get.1]; omega)]
    have e2 : dP c = 1 := by
      rw [dP, List.getD_eq_default _ _ (by rw [delta_get.2.1]; omega)]
      rfl
    rw [e1, e2]
    exact Orb.prep_pidn (by norm_num) (by norm_num)

theorem vl0_iff : ∀ i : Fin 8, i ∈ ae6VertexLetters 0 ↔ i.val ∈ vl.getD 0 [] := fun i => vl_iff 0 i

theorem delta0_inv : ∀ i ∈ ae6VertexLetters 0,
    ((ae6Delta 0 i).map fun j => ae6Word (ae6Delta 0 j)).prod = A6.curtisGen i := by
  intro i hi
  have h := invDOK_sound gRep dRep kInvD i.val ((vl0_iff i).1 hi)
  apply Subtype.ext
  rw [coe_prod_map, coe_curtisGen, ← h, delta_get.2.2 i, wv, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [Function.comp_apply, coe_ae6Word, dP, delta_get.2.2 j]

theorem delta0_letters : ∀ i : Fin 8, ∀ j ∈ ae6Delta 0 i, j ∈ ae6VertexLetters 0 := by decide

theorem vertexV0 : ae6ModelV 0 = Subgroup.closure (A6.curtisGen '' ↑(ae6VertexLetters 0)) := by
  rw [ae6ModelV]
  congr 2
  ext i
  simp [ae6VertexLetters]

theorem v0_images : Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) =>
    ae6Word (ae6Delta 0 i)) = ae6ModelV 0 := by
  rw [vertexV0]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact word_mem _ (delta0_letters i)
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [← delta0_inv i hi]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact Subgroup.subset_closure ⟨⟨j, delta0_letters i j hj⟩, rfl⟩

theorem trigen0_eq : ∀ i : Fin 6, ae6TriGen 0 i = ae6TriGen₀ i := by decide

theorem trigen0_letters : ∀ i : Fin 6, ∀ j ∈ ae6TriGen₀ i, j ∈ ae6EdgeLetters 0 1 := by decide

theorem tg0_get : ∀ i : Fin 6, tg0.getD i.val [] = (ae6TriGen₀ i).map Fin.val := by decide

theorem tg0_len : tg0.length = 6 := by decide

theorem el_of : ∀ c : Fin 8, c.val ∈ el → ∃ t < 6, el.getD t 0 = c.val := by decide

@[expose] noncomputable def tgA (i : Nat) : AE6Om := if h : i < 6 then ae6Word (ae6TriGen₀ ⟨i, h⟩) else 1

theorem coe_tgA (i : Nat) : (tgA i : Equiv.Perm (Fin 360)) = wv gP (tg0.getD i []) := by
  by_cases h : i < 6
  · rw [tgA, dif_pos h, coe_ae6Word, ← tg0_get ⟨i, h⟩]
  · rw [tgA, dif_neg h, List.getD_eq_default _ _ (by rw [tg0_len]; omega)]
    rfl

theorem tgen0 : Subgroup.closure (Set.range fun i => ae6Word (ae6TriGen 0 i)) =
    ae6LetterSub ↑(ae6EdgeLetters 0 1) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    simp only [trigen0_eq]
    exact word_mem _ (trigen0_letters i)
  · rw [ae6LetterSub, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨t, ht, he⟩ := el_of c ((el_iff c).1 hc)
    have h := tgOK_sound gRep kTGen t (by rw [shapes.2.2.2.2.2.1]; exact ht)
    have e : A6.curtisGen c = ((tgW.getD t []).map tgA).prod := by
      apply Subtype.ext
      rw [coe_prod_map, coe_curtisGen, ← he, ← h]
      congr 1
      exact List.map_congr_left fun i _ => (coe_tgA i).symm
    rw [e]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    by_cases hi : i < 6
    · rw [tgA, dif_pos hi]
      exact Subgroup.subset_closure ⟨⟨i, hi⟩, by simp only [trigen0_eq]⟩
    · rw [tgA, dif_neg hi]
      exact Subgroup.one_mem _

end CertificateChecks.KernelAE6Tri

end
