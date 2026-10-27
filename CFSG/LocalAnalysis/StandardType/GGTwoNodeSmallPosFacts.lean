module

public import Certificates.Data.CFSGNative.TwoNodeSmall.VerifyPos
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Pt.AlphaFixed (P : Pt) : Prop := P.dot (P.vec P.lastRefl.f) (P.vec P.x) = 0

@[expose] def Pt.CycleAt (P : Pt) (s : ℕ) : Prop :=
  5 ≤ P.p ∧ ∃ (ψ rj rj' : P.V ≃ₗ[ZMod P.p] P.V) (j j' : ℕ), ψ ∈ P.group ∧ s ≤ j ∧ j < s + (P.nFrame - 2) ∧ s ≤ j' ∧
    j' < s + (P.nFrame - 2) ∧ j ≠ j' ∧
    (∀ w, rj w = w - P.dot (P.vec (P.gens.getD j ⟨[], []⟩).f) w • P.vec (P.gens.getD j ⟨[], []⟩).h) ∧
    (∀ w, rj' w = w - P.dot (P.vec (P.gens.getD j' ⟨[], []⟩).f) w • P.vec (P.gens.getD j' ⟨[], []⟩).h) ∧
    ∃ (ht : P.V) (αt : Module.Dual (ZMod P.p) P.V),
      (∀ w, (ψ * rj * ψ⁻¹) w = w - αt w • ht) ∧ αt ht = 2 ∧
      ψ * rj * ψ⁻¹ * rj' ≠ rj' * (ψ * rj * ψ⁻¹) ∧
      P.dot (P.vec (P.gens.getD j ⟨[], []⟩).f) (P.vec (P.gens.getD j' ⟨[], []⟩).h) *
          P.dot (P.vec (P.gens.getD j' ⟨[], []⟩).f) ht * αt (P.vec (P.gens.getD j ⟨[], []⟩).h) ≠
        P.dot (P.vec (P.gens.getD j' ⟨[], []⟩).f) (P.vec (P.gens.getD j ⟨[], []⟩).h) *
          αt (P.vec (P.gens.getD j' ⟨[], []⟩).h) * P.dot (P.vec (P.gens.getD j ⟨[], []⟩).f) ht

private lemma pff_foldl_range_map (p D : ℕ) (F : ℕ → ℕ) :
    ((((List.range D).map F).foldl (· + ·) 0 : ℕ) : ZMod p)
      = ∑ i : Fin D, (F i.val : ZMod p) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Nat.cast_add, ih, Fin.sum_univ_castSucc]
      simp

private lemma pff_dotv_cast (P : Pt) (f v : Vec) :
    ((P.dotv f v : ℕ) : ZMod P.p) = P.dot (P.vec f) (P.vec v) := by
  simp only [Pt.dotv]
  rw [ZMod.natCast_mod, pff_foldl_range_map]
  simp only [Pt.dot, Pt.vec, Nat.cast_mul]

theorem verifyF_sound {P : Pt} (h : verifyF P = true) : P.AlphaFixed := by
  unfold Pt.AlphaFixed
  have h0 : P.dotv P.lastRefl.f P.x = 0 := by
    simpa [verifyF] using h
  rw [← pff_dotv_cast P P.lastRefl.f P.x, h0]
  simp

theorem verifyS_sound {P : Pt} (h : verifyS P = true) : ¬ P.WF := by
  intro hwf
  have hfalse : wfCheck P = false := by
    simpa [verifyS] using h
  have htrue : wfCheck P = true := by
    rw [wfCheck, List.all_eq_true]
    intro r hr
    have hmod : P.dotv r.f r.h = 2 % P.p := by
      have hcast : ((P.dotv r.f r.h : ℕ) : ZMod P.p) = ((2 : ℕ) : ZMod P.p) := by
        rw [pff_dotv_cast, hwf r hr]
        simp
      have hred : P.dotv r.f r.h % P.p = 2 % P.p :=
        (ZMod.natCast_eq_natCast_iff (P.dotv r.f r.h) 2 P.p).mp hcast
      simpa [Pt.dotv] using hred
    simp [hmod]
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem alphaFixed_models {P : Pt} {V : Type} [AddCommGroup V] [Module (ZMod P.p) V] {n : ℕ}
    {e : V ≃ₗ[ZMod P.p] P.V} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod P.p) V} {x ha : V}
    {αa : Module.Dual (ZMod P.p) V} (hM : P.Models e h α x ha αa) (hfix : P.AlphaFixed) : αa x = 0 := by
  obtain ⟨hn, -, hx, -, -, hαa⟩ := hM
  rw [hαa x, hx]
  unfold Pt.AlphaFixed Pt.lastRefl at hfix
  rw [hn] at hfix
  exact hfix

theorem wf_of_models {P : Pt} {V : Type} [AddCommGroup V] [Module (ZMod P.p) V] {n : ℕ}
    {e : V ≃ₗ[ZMod P.p] P.V} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod P.p) V} {x ha : V}
    {αa : Module.Dual (ZMod P.p) V} (hM : P.Models e h α x ha αa) (hpair : ∀ i, α i (h i) = 2)
    (hha : αa ha = 2) : P.WF := by
  obtain ⟨hn, hlen, -, hframe, hlast, hαa⟩ := hM
  intro r hr
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hr
  have hklt : k < n + 1 := by rw [← hlen]; exact hk
  have hgetD : P.gens.getD k ⟨[], []⟩ = r := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hklt), hkr]
  rw [← hgetD]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with hkn | hkn
  · have he : e (h ⟨k, hkn⟩) = P.vec (P.gens.getD k ⟨[], []⟩).h := (hframe ⟨k, hkn⟩).1
    have hfun : α ⟨k, hkn⟩ (h ⟨k, hkn⟩)
        = P.dot (P.vec (P.gens.getD k ⟨[], []⟩).f) (e (h ⟨k, hkn⟩)) := (hframe ⟨k, hkn⟩).2 _
    rw [← he, ← hfun]
    exact hpair ⟨k, hkn⟩
  · rw [hkn]
    have he : e ha = P.vec (P.gens.getD n ⟨[], []⟩).h := hlast
    have hfun : αa ha = P.dot (P.vec (P.gens.getD n ⟨[], []⟩).f) (e ha) := hαa _
    rw [← he, ← hfun]
    exact hha

end CFSG.TwoNodeSmall
