module

public import CFSG.Timmesfeld.Bridge.RootSetsBasic
public import CFSG.Timmesfeld.Opposite.Basic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {D : Set G}

@[expose] def MoufangPair (D : Set G) (d c : G) : Prop :=
  (∀ a ∈ rootSet D d, ∃ b ∈ rootSet D c, orderOf (a * b) = 3) ∧
    ∀ b ∈ rootSet D c, ∃ a ∈ rootSet D d, orderOf (a * b) = 3

@[expose] def RankOneTransitive (D : Set G) (d c : G) : Prop :=
  ∀ x ∈ rootGroup D d ⊔ rootGroup D c,
    (rootGroup D d).map (MulAut.conj x).toMonoidHom ≠ rootGroup D c →
      ∃ g ∈ rootGroup D c, (rootGroup D d).map (MulAut.conj x).toMonoidHom =
        (rootGroup D d).map (MulAut.conj g).toMonoidHom

theorem rootGroup_ne_of_opposite [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {d c : G} (hd : d ∈ D) (hc : c ∈ D) (hdc : ¬ Commute d c) : rootGroup D d ≠ rootGroup D c := by
  intro h
  have hcT : c ∈ rootSet D d :=
    mem_rootSet_of_mem_rootGroup hclass hd hc (h ▸ rootSet_subset_rootGroup D c
      (mem_rootSet_self hc))
  exact hdc (commute_of_mem_rootSet hd (mem_rootSet_self hd) hcT)

theorem mem_rootSet_of_mem_rootGroup_of_ne_one (hD : IsRootInvolutionSet D) (hrc : RootClosure D)
    {d g : G} (hd : d ∈ D) (hg : g ∈ rootGroup D d) (hg1 : g ≠ 1) : g ∈ rootSet D d :=
  ((mem_rootGroup_iff_of_rootClosure hD hrc hd).1 hg).resolve_left hg1

theorem map_conj_rootGroup_ne_of_opposite [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {c a : G} (hc : c ∈ D) (ha : a ∈ D) (hac : ¬ Commute a c) :
    (rootGroup D c).map (MulAut.conj a).toMonoidHom ≠ rootGroup D c := by
  intro h
  exact hac (commute_of_mem_normalizer_rootGroup hclass hD hc ha
    (map_conj_eq_self_iff.1 h)).symm

theorem map_conj_rootGroup_injOn [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) {g g' : G} (hg : g ∈ rootGroup D c)
    (hg' : g' ∈ rootGroup D c)
    (h : (rootGroup D d).map (MulAut.conj g).toMonoidHom =
      (rootGroup D d).map (MulAut.conj g').toMonoidHom) : g = g' := by
  by_contra hne
  have hk : g'⁻¹ * g ∈ rootGroup D c := (rootGroup D c).mul_mem ((rootGroup D c).inv_mem hg') hg
  have hk1 : g'⁻¹ * g ≠ 1 := fun h1 => hne (inv_mul_eq_one.1 h1).symm
  have hkT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hc hk hk1
  have hfix : (rootGroup D d).map (MulAut.conj (g'⁻¹ * g)).toMonoidHom = rootGroup D d := by
    rw [map_conj_mul, h, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  have hcomm := commute_of_mem_normalizer_rootGroup hclass hD hd hkT.1
    (map_conj_eq_self_iff.1 hfix)
  obtain ⟨-, hnc⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc (mem_rootSet_self hd) hkT hodd hdc
  exact hnc hcomm

theorem map_conj_rootGroup_eq_iff_of_mem [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c a b : G} (hd : d ∈ D) (hc : c ∈ D) (hdc : ¬ Commute d c)
    (hodd : Odd (orderOf (d * c))) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D c) :
    (rootGroup D d).map (MulAut.conj b).toMonoidHom =
        (rootGroup D c).map (MulAut.conj a).toMonoidHom ↔ orderOf (a * b) = 3 := by
  obtain ⟨hab, hnc⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc ha hb hodd hdc
  rw [← rootGroup_eq_of_mem ha, ← rootGroup_eq_of_mem hb]
  exact map_conj_rootGroup_eq_iff hclass hD ha.1 hb.1 hnc hab

theorem map_conj_dihedralSwap (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hodd : Odd (orderOf (d * c))) :
    (rootGroup D d).map (MulAut.conj (dihedralSwap d c)).toMonoidHom = rootGroup D c := by
  rw [← rootGroup_conj hclass, dihedralSwap_conj (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hc)
    hodd]

theorem dihedralSwap_mem_sup {d c : G} (hd : d ∈ D) (hc : c ∈ D) :
    dihedralSwap d c ∈ rootGroup D d ⊔ rootGroup D c := by
  have hdX : d ∈ rootGroup D d ⊔ rootGroup D c :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hcX : c ∈ rootGroup D d ⊔ rootGroup D c :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D c (mem_rootSet_self hc))
  exact Subgroup.mul_mem _ hdX (Subgroup.pow_mem _ (Subgroup.mul_mem _ hdX hcX) _)

@[expose] def rankOneOrbit (D : Set G) (d c : G) : Set (Subgroup G) :=
  insert (rootGroup D c)
    {Y | ∃ g ∈ rootGroup D c, Y = (rootGroup D d).map (MulAut.conj g).toMonoidHom}

theorem map_conj_mem_rankOneOrbit [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hM : MoufangPair D d c) {x : G}
    (hx : x ∈ rootGroup D d ⊔ rootGroup D c) :
    ∀ Y : Subgroup G, Y ∈ rankOneOrbit D d c ↔
      Y.map (MulAut.conj x).toMonoidHom ∈ rankOneOrbit D d c := by
  set A := rootGroup D d
  set B := rootGroup D c
  set S := rankOneOrbit D d c
  have hgen : ∀ t ∈ rootSet D d ∪ rootSet D c, ∀ Y ∈ S, Y.map (MulAut.conj t).toMonoidHom ∈ S := by
    rintro t (ht | ht) Y (rfl | ⟨g, hg, rfl⟩)
    ·
      obtain ⟨b, hb, h3⟩ := hM.1 t ht
      exact Or.inr ⟨b, rootSet_subset_rootGroup D c hb,
        ((map_conj_rootGroup_eq_iff_of_mem hclass hD hd hc hdc hodd ht hb).2 h3).symm⟩
    · by_cases hg1 : g = 1
      · subst hg1
        refine Or.inr ⟨1, B.one_mem, ?_⟩
        simp only [map_conj_one]
        exact map_conj_of_mem (rootSet_subset_rootGroup D d ht)
      · have hgT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hc hg hg1
        obtain ⟨a', ha', h3⟩ := hM.2 g hgT
        rw [(map_conj_rootGroup_eq_iff_of_mem hclass hD hd hc hdc hodd ha' hgT).2 h3,
          ← map_conj_mul]
        have hta : t * a' ∈ A := A.mul_mem (rootSet_subset_rootGroup D d ht)
          (rootSet_subset_rootGroup D d ha')
        by_cases h1 : t * a' = 1
        · rw [h1, map_conj_one]
          exact Or.inl rfl
        · obtain ⟨b', hb', h3'⟩ := hM.1 _ (mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hd hta h1)
          exact Or.inr ⟨b', rootSet_subset_rootGroup D c hb', ((map_conj_rootGroup_eq_iff_of_mem
            hclass hD hd hc hdc hodd (mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hd hta h1)
            hb').2 h3').symm⟩
    · rw [map_conj_of_mem (rootSet_subset_rootGroup D c ht)]
      exact Or.inl rfl
    · exact Or.inr ⟨t * g, B.mul_mem (rootSet_subset_rootGroup D c ht) hg,
        (map_conj_mul _ _ _).symm⟩
  have hX : A ⊔ B = Subgroup.closure (rootSet D d ∪ rootSet D c) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hX] at hx
  induction hx using Subgroup.closure_induction with
  | mem t ht =>
    intro Y
    refine ⟨hgen t ht Y, fun hY => ?_⟩
    have ht2 : t * t = 1 := by
      rcases ht with ht | ht
      · exact hD.mul_self_eq_one ht.1
      · exact hD.mul_self_eq_one ht.1
    have := hgen t ht _ hY
    rwa [← map_conj_mul, ht2, map_conj_one] at this
  | one => intro Y; rw [map_conj_one]
  | mul x y _ _ ihx ihy =>
    intro Y
    rw [ihy Y, ihx, ← map_conj_mul]
  | inv x _ ih =>
    intro Y
    have := ih (Y.map (MulAut.conj x⁻¹).toMonoidHom)
    rw [map_conj_map_conj_inv] at this
    exact this.symm

theorem moufangPair_iff_rankOneTransitive [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) :
    MoufangPair D d c ↔ RankOneTransitive D d c := by
  set A := rootGroup D d
  set B := rootGroup D c
  set σ := dihedralSwap d c
  have hσ2 : σ * σ = 1 := dihedralSwap_mul_self (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hc)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσA : A.map (MulAut.conj σ).toMonoidHom = B := map_conj_dihedralSwap hclass hD hd hc hodd
  have hσB : B.map (MulAut.conj σ).toMonoidHom = A := by
    rw [← hσA, ← map_conj_mul, hσ2, map_conj_one]
  have hσX : σ ∈ A ⊔ B := dihedralSwap_mem_sup hd hc
  have hAB : A ≠ B := rootGroup_ne_of_opposite hclass hd hc hdc
  constructor
  · intro hM x hx hne
    have hmem := (map_conj_mem_rankOneOrbit hclass hD hrc hd hc hdc hodd hM hx A).1
      (Or.inr ⟨1, B.one_mem, (map_conj_one A).symm⟩)
    rcases hmem with h | ⟨g, hg, h⟩
    · exact absurd h hne
    · exact ⟨g, hg, h⟩
  · intro hT
    have hmove : ∀ a ∈ rootSet D d, B.map (MulAut.conj a).toMonoidHom ≠ B := by
      intro a ha
      obtain ⟨-, hnc⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc ha (mem_rootSet_self hc) hodd hdc
      exact map_conj_rootGroup_ne_of_opposite hclass hD hc ha.1 hnc
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have haX : a ∈ A ⊔ B := Subgroup.mem_sup_left (rootSet_subset_rootGroup D d ha)
      have hx : A.map (MulAut.conj (a * σ)).toMonoidHom = B.map (MulAut.conj a).toMonoidHom := by
        rw [map_conj_mul, hσA]
      obtain ⟨g, hg, hgeq⟩ := hT (a * σ) (Subgroup.mul_mem _ haX hσX) (hx ▸ hmove a ha)
      rw [hx] at hgeq
      have hg1 : g ≠ 1 := by
        rintro rfl
        rw [map_conj_one, map_conj_eq_iff,
          map_conj_of_mem (A.inv_mem (rootSet_subset_rootGroup D d ha))] at hgeq
        exact hAB hgeq.symm
      have hgT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hc hg hg1
      exact ⟨g, hgT, (map_conj_rootGroup_eq_iff_of_mem hclass hD hd hc hdc hodd ha hgT).1
        hgeq.symm⟩
    · have hbX : b ∈ A ⊔ B := Subgroup.mem_sup_right (rootSet_subset_rootGroup D c hb)
      have hbA : A.map (MulAut.conj b).toMonoidHom ≠ A := by
        obtain ⟨-, hnc⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc (mem_rootSet_self hd) hb hodd
          hdc
        exact map_conj_rootGroup_ne_of_opposite hclass hD hd hb.1 (fun h => hnc h.symm)
      have hne : A.map (MulAut.conj (σ * b)).toMonoidHom ≠ B := by
        rw [map_conj_mul]
        intro h
        apply hbA
        rw [map_conj_eq_iff, hσinv, hσB] at h
        exact h
      obtain ⟨g, hg, hgeq⟩ := hT (σ * b) (Subgroup.mul_mem _ hσX hbX) hne
      set a := σ * g * σ⁻¹ with ha_def
      have haA : a ∈ A := by
        rw [← hσB]
        exact conj_mem_map_conj σ hg
      have heq : A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom := by
        have h1 : (A.map (MulAut.conj (σ * b)).toMonoidHom).map (MulAut.conj σ⁻¹).toMonoidHom =
            (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj σ⁻¹).toMonoidHom := by
          rw [hgeq]
        rw [map_conj_mul A σ b, map_conj_inv_map_conj, ← map_conj_mul] at h1
        rw [h1, ha_def, map_conj_mul B (σ * g) σ⁻¹, hσinv, hσB]
      have ha1 : a ≠ 1 := by
        intro h1
        rw [h1, map_conj_one, map_conj_eq_iff,
          map_conj_of_mem (B.inv_mem (rootSet_subset_rootGroup D c hb))] at heq
        exact hAB heq
      have haT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hd haA ha1
      exact ⟨a, haT, (map_conj_rootGroup_eq_iff_of_mem hclass hD hd hc hdc hodd haT hb).1 heq⟩

end CFSG.Timmesfeld.Bridge
