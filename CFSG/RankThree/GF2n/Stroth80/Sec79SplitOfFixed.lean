module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem splitOfFixed_surj_of_inj {P : Type} [AddCommGroup P] [Finite P] (S : AddSubgroup P)
    (T : P → P) (hmaps : ∀ c ∈ S, T c ∈ S) (hinj : ∀ c ∈ S, ∀ c' ∈ S, T c = T c' → c = c') :
    ∀ c ∈ S, ∃ c' ∈ S, T c' = c := by
  intro c hc
  obtain ⟨phi, hphi⟩ : ∃ phi : S → S, ∀ x : S, (phi x : P) = T x.1 :=
    ⟨fun x => ⟨T x.1, hmaps x.1 x.2⟩, fun x => rfl⟩
  have hphiinj : Function.Injective phi := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.1 x.2 y.1 y.2
    rw [← hphi x, ← hphi y, hxy]
  obtain ⟨c', hc'⟩ := Finite.surjective_of_injective hphiinj ⟨c, hc⟩
  exact ⟨c'.1, c'.2, (hphi c').symm.trans (congrArg Subtype.val hc')⟩

theorem splitOfFixed_holds :
    ∀ (P : Type) [AddCommGroup P] [Finite P] (C₁ C₂ A : AddSubgroup P), IsCompl C₁ C₂ →
      ∀ (f g : P →+ P), f.ker = C₁ → f.range = C₁ → g.ker = C₂ → g.range = C₂ →
        (∀ a ∈ A, f a ∈ A ∧ g a ∈ A) → A = (A ⊓ C₁) ⊔ (A ⊓ C₂) := by
  intro P _ _ C₁ C₂ A hC f g hfk hfr hgk hgr hA
  have hfC : ∀ x, f x ∈ C₁ := by
    intro x
    rw [← hfr]
    exact AddMonoidHom.mem_range.2 ⟨x, rfl⟩
  have hgC : ∀ x, g x ∈ C₂ := by
    intro x
    rw [← hgr]
    exact AddMonoidHom.mem_range.2 ⟨x, rfl⟩
  have hgC₂ : ∀ x ∈ C₂, g x = 0 := by
    intro x hx
    rw [← hgk] at hx
    exact AddMonoidHom.mem_ker.1 hx
  have hT0 : ∀ c ∈ C₁, f (g c) = 0 → c = 0 := by
    intro c hc h
    have h1 : g c ∈ C₁ := by
      rw [← hfk]
      exact AddMonoidHom.mem_ker.2 h
    have h2 : g c ∈ C₁ ⊓ C₂ := AddSubgroup.mem_inf.2 ⟨h1, hgC c⟩
    rw [hC.inf_eq_bot, AddSubgroup.mem_bot] at h2
    have h3 : c ∈ C₂ := by
      rw [← hgk]
      exact AddMonoidHom.mem_ker.2 h2
    have h4 : c ∈ C₁ ⊓ C₂ := AddSubgroup.mem_inf.2 ⟨hc, h3⟩
    rw [hC.inf_eq_bot, AddSubgroup.mem_bot] at h4
    exact h4
  have hTA : ∀ c ∈ C₁ ⊓ (A ⊔ C₂), f (g c) ∈ A := by
    intro c hc
    obtain ⟨a, ha, d, hd, hcad⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_inf.1 hc).2
    have hgc : g c = g a := by
      rw [← hcad, map_add, hgC₂ d hd, add_zero]
    rw [hgc]
    exact (hA (g a) (hA a ha).2).1
  have hS_sub : C₁ ⊓ (A ⊔ C₂) ≤ A ⊓ C₁ := by
    have hmaps : ∀ c ∈ C₁ ⊓ (A ⊔ C₂), f (g c) ∈ C₁ ⊓ (A ⊔ C₂) := by
      intro c hc
      exact AddSubgroup.mem_inf.2 ⟨hfC (g c), AddSubgroup.mem_sup_left (hTA c hc)⟩
    have hinj : ∀ c ∈ C₁ ⊓ (A ⊔ C₂), ∀ c' ∈ C₁ ⊓ (A ⊔ C₂),
        f (g c) = f (g c') → c = c' := by
      intro c hc c' hc' h
      have h0 : f (g (c - c')) = 0 := by
        rw [map_sub, map_sub, h, sub_self]
      have h1 : c - c' = 0 :=
        hT0 (c - c') (sub_mem (AddSubgroup.mem_inf.1 hc).1 (AddSubgroup.mem_inf.1 hc').1) h0
      exact sub_eq_zero.1 h1
    intro c hc
    obtain ⟨c', hc', hcc'⟩ :=
      splitOfFixed_surj_of_inj (C₁ ⊓ (A ⊔ C₂)) (fun c => f (g c)) hmaps hinj c hc
    have hcA : c ∈ A := by
      rw [← hcc']
      exact hTA c' hc'
    exact AddSubgroup.mem_inf.2 ⟨hcA, (AddSubgroup.mem_inf.1 hc).1⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro a ha
  have hsup : a ∈ C₁ ⊔ C₂ := by
    rw [hC.sup_eq_top]
    exact AddSubgroup.mem_top a
  obtain ⟨c, hc, d, hd, hcd⟩ := AddSubgroup.mem_sup.1 hsup
  have hcS : c ∈ C₁ ⊓ (A ⊔ C₂) := by
    refine AddSubgroup.mem_inf.2 ⟨hc, AddSubgroup.mem_sup.2 ⟨a, ha, -d, neg_mem hd, ?_⟩⟩
    rw [← hcd, add_neg_cancel_right]
  have hcA : c ∈ A := (AddSubgroup.mem_inf.1 (hS_sub hcS)).1
  have hdA : d ∈ A := by
    have hd' : d = a + -c := by
      rw [← hcd, add_right_comm, add_neg_cancel, zero_add]
    rw [hd']
    exact add_mem ha (neg_mem hcA)
  exact AddSubgroup.mem_sup.2
    ⟨c, AddSubgroup.mem_inf.2 ⟨hcA, hc⟩, d, AddSubgroup.mem_inf.2 ⟨hdA, hd⟩, hcd⟩

end CFSG.RankThree.GF2n.Stroth80
