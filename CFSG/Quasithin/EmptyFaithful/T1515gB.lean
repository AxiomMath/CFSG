module

public import CFSG.Quasithin.EmptyFaithful.T1515gA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def a7PairVec (i j : Fin 7) : ↥(evenWeight 7) :=
  ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0), by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Finset.sum_add_distrib]
    simp
    try decide⟩

theorem a7_nodup_six_iff {a b c d e f : Fin 7} (hnd : [a, b, c, d, e, f].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧
      c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp [List.nodup_cons] at hnd
  tauto

theorem a7_three_swaps_inv {a b c d e f : Fin 7} (hnd : [a, b, c, d, e, f].Nodup) :
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ a = b ∧
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ b = a ∧
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ c = d ∧
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ d = c ∧
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ e = f ∧
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)⁻¹ f = e := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ :=
    a7_nodup_six_iff hnd
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hea := hae.symm
  have hfa := haf.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have heb := hbe.symm
  have hfb := hbf.symm
  have hdc := hcd.symm
  have hec := hce.symm
  have hfc := hcf.symm
  have hed := hde.symm
  have hfd := hdf.symm
  have hfe := hef.symm
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul, Function.comp_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Equiv.swap_apply_def, *]

theorem a7_perm_nonconst {a b c d e f : Fin 7} (hnd : [a, b, c, d, e, f].Nodup)
    (σ : Equiv.Perm (Fin 7)) (ha : σ.symm a = b) (_hb : σ.symm b = a) (hc : σ.symm c = d)
    (_hd : σ.symm d = c) (he : σ.symm e = f) (_hf : σ.symm f = e) (z : ↥(evenWeight 7))
    (hz : z = a7PairVec a c ∨ z = a7PairVec a e ∨ z = -a7PairVec a c + a7PairVec a e) :
    -(permWeight 7 σ z) + z ∉ constWeight 7 := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ :=
    a7_nodup_six_iff hnd
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hea := hae.symm
  have hfa := haf.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have heb := hbe.symm
  have hfb := hbf.symm
  have hdc := hcd.symm
  have hec := hce.symm
  have hfc := hcf.symm
  have hed := hde.symm
  have hfd := hdf.symm
  have hfe := hef.symm
  intro hconst
  have hcst : ∀ i j : Fin 7, (-(permWeight 7 σ z) + z : ↥(evenWeight 7)).1 i =
      (-(permWeight 7 σ z) + z : ↥(evenWeight 7)).1 j := hconst
  rcases hz with h | h | h <;> subst h
  · have h1 := hcst a e
    simp [permWeight, a7PairVec, *] at h1
  · have h1 := hcst a c
    simp [permWeight, a7PairVec, *] at h1
  · have h1 := hcst c a
    simp [permWeight, a7PairVec, *] at h1

theorem a7_exists_mem_or_of_index_two {K : Type*} [Group K] {H : Subgroup K} (h2 : H.index = 2)
    (x y : K) : x ∈ H ∨ y ∈ H ∨ x⁻¹ * y ∈ H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy, hxy⟩ := hcon
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
  have hn : H.Normal := Subgroup.normal_of_index_eq_two h2
  have hxa : x * a ∈ H := by
    rcases ha x with h | h
    · exact h.1
    · exact absurd h.1 hx
  have hya : y * a ∈ H := by
    rcases ha y with h | h
    · exact h.1
    · exact absurd h.1 hy
  have h1 : (x * a)⁻¹ * (y * a) ∈ H := H.mul_mem (H.inv_mem hxa) hya
  have h2' : a * ((x * a)⁻¹ * (y * a)) * a⁻¹ ∈ H := hn.conj_mem _ h1 a
  apply hxy
  have : a * ((x * a)⁻¹ * (y * a)) * a⁻¹ = x⁻¹ * y := by group
  rwa [this] at h2'

theorem a7ModuleStepB : A7ModuleStepB := by
  intro G _ _ L S V₁ α β hshort hstr hSL hUS u hV1S hidx s hs σ hact hσ hV
  by_contra hnot
  obtain ⟨v, hvV, hvB⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨b, hbB, hvb⟩ : ∃ b ∈ a7BSub S L (u : G), v = b * s := (hV v hvV).resolve_left hvB
  have hUab : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := fun x hx y hy =>
    C1.blockU_comm hshort x hx y (C1.blockU_le_blockQ hshort hy)
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le L)
  have hBU : ∀ x ∈ blockU L, x * b = b * x := by
    have hle : a7BSub S L (u : G) ≤ Subgroup.centralizer (blockU L : Set G) := by
      refine sup_le (fun c hc => ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_iff.mp hc.2 x (hUL hx)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro x hx
        exact hUab x hx u u.2
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hbB) x hx
  have key : ∀ x : ↥(blockU L), (x : G) ∈ Subgroup.centralizer (V₁ : Set G) →
      ∀ z : ↥(evenWeight 7), (QuotientAddGroup.mk z : AltHeart 7) = Multiplicative.toAdd (β x) →
        -(permWeight 7 σ z) + z ∈ constWeight 7 := by
    intro x hxC z hz
    have hcomm : v * (x : G) = (x : G) * v := Subgroup.mem_centralizer_iff.mp hxC v hvV
    have hxb : (x : G) * b = b * (x : G) := hBU x x.2
    have hsx : s * (x : G) = (x : G) * s := by
      have h1 : b * (s * (x : G)) = b * ((x : G) * s) := by
        calc b * (s * (x : G)) = (b * s) * (x : G) := by group
          _ = (x : G) * (b * s) := by rw [← hvb]; exact hcomm
          _ = ((x : G) * b) * s := by group
          _ = (b * (x : G)) * s := by rw [hxb]
          _ = b * ((x : G) * s) := by group
      exact mul_left_cancel h1
    have hy : (x : G) = s * (x : G) * s⁻¹ := by rw [hsx]; group
    have h2 := hact x x hy z hz
    rw [← hz] at h2
    exact QuotientAddGroup.eq.mp h2
  obtain ⟨a, b', c, d, e, f, hnd, rfl⟩ := hσ
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := a7_three_swaps_inv hnd
  have hβsurj : Function.Surjective β := hstr.2.2.1
  obtain ⟨x₁, hx₁⟩ := hβsurj (Multiplicative.ofAdd (QuotientAddGroup.mk (a7PairVec a c)))
  obtain ⟨x₂, hx₂⟩ := hβsurj (Multiplicative.ofAdd (QuotientAddGroup.mk (a7PairVec a e)))
  have hx₁' : (QuotientAddGroup.mk (a7PairVec a c) : AltHeart 7) = Multiplicative.toAdd (β x₁) := by
    rw [hx₁]; rfl
  have hx₂' : (QuotientAddGroup.mk (a7PairVec a e) : AltHeart 7) = Multiplicative.toAdd (β x₂) := by
    rw [hx₂]; rfl
  have hx₃' : (QuotientAddGroup.mk (-a7PairVec a c + a7PairVec a e) : AltHeart 7) =
      Multiplicative.toAdd (β (x₁⁻¹ * x₂)) := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← hx₁', ← hx₂', QuotientAddGroup.mk_add,
      QuotientAddGroup.mk_neg]
  have hS2 : ((Subgroup.centralizer (V₁ : Set G) ⊓ S).subgroupOf S).index = 2 := hidx
  let X₁ : ↥S := ⟨(x₁ : G), hUS x₁.2⟩
  let X₂ : ↥S := ⟨(x₂ : G), hUS x₂.2⟩
  rcases a7_exists_mem_or_of_index_two hS2 X₁ X₂ with h1 | h2 | h3
  · exact a7_perm_nonconst hnd _ ha hb hc hd he hf _ (Or.inl rfl)
      (key x₁ (Subgroup.mem_subgroupOf.mp h1).1 _ hx₁')
  · exact a7_perm_nonconst hnd _ ha hb hc hd he hf _ (Or.inr (Or.inl rfl))
      (key x₂ (Subgroup.mem_subgroupOf.mp h2).1 _ hx₂')
  · exact a7_perm_nonconst hnd _ ha hb hc hd he hf _ (Or.inr (Or.inr rfl))
      (key (x₁⁻¹ * x₂) (Subgroup.mem_subgroupOf.mp h3).1 _ hx₃')

end CFSG.Quasithin
