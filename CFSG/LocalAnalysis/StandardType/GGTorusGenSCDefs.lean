module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusCentSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∀ c : R, (∀ e ∈ E, c * e = e * c) → (∃ k : ℕ, c ^ p ^ k = 1) → c ∈ E

@[expose] def GGTorusCompMeetSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∀ x ∈ E, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
      ∃ w ∈ J, w ∈ E ∧ w ≠ 1

@[expose] def GGTorusCompGenSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∀ x ∈ E, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
      E ≤ Subgroup.closure (⋃ n ∈ Subgroup.normalizer (E : Set R),
        (fun s => n * s * n⁻¹) '' ((J ⊓ E : Subgroup R) : Set R))

private theorem map_hypotheses {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R} (hE : IsElemAbelian p E) (h3 : p ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    IsElemAbelian p (E.map e.toMonoidHom) ∧ p ^ 3 ≤ Nat.card (E.map e.toMonoidHom) ∧
      ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
        g ∈ E.map e.toMonoidHom := by
  refine ⟨CFSG.SectionRank.isElemAbelian_map hE _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h3
  · intro g hg hgp
    obtain ⟨y, hy⟩ := e.surjective g
    have hy' : e.toMonoidHom y = g := hy
    rw [← hy'] at hg hgp ⊢
    rw [Subgroup.mem_map_iff_mem (K := E) (x := y) e.injective]
    refine hsc y (fun x hx => ?_) ?_
    · apply e.injective
      rw [map_mul, map_mul]
      exact hg (e.toMonoidHom x) ((Subgroup.mem_map_iff_mem (K := E) (x := x) e.injective).mpr hx)
    · apply e.injective
      rw [map_pow, map_one]
      exact hgp

theorem ggTorusCentSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusCentSC p R') : GGTorusCentSC p R := by
  intro E hE h3 hsc c hc hcp
  obtain ⟨hE', h3', hsc'⟩ := map_hypotheses e hE h3 hsc
  have hcm : ∀ x ∈ E.map e.toMonoidHom, e.toMonoidHom c * x = x * e.toMonoidHom c := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg e.toMonoidHom (hc y hy)
  have hcpe : ∃ k : ℕ, e.toMonoidHom c ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, by simpa only [map_pow, map_one] using congrArg e.toMonoidHom hk⟩
  exact (Subgroup.mem_map_iff_mem (K := E) (x := c) e.injective).mp
    (h (E.map e.toMonoidHom) hE' h3' hsc' (e.toMonoidHom c) hcm hcpe)

theorem ggTorusCompMeetSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusCompMeetSC p R') : GGTorusCompMeetSC p R := by
  intro E hE h3 hsc x hx hx1 J hJ
  obtain ⟨hE', h3', hsc'⟩ := map_hypotheses e hE h3 hsc
  have hcent : (Subgroup.centralizer ({x} : Set R)).map e.toMonoidHom =
      Subgroup.centralizer ({e.toMonoidHom x} : Set R') := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      simpa only [map_mul] using congrArg e.toMonoidHom hz
    · intro hy
      obtain ⟨z, hz⟩ := e.surjective y
      have hz' : e.toMonoidHom z = y := hz
      refine Subgroup.mem_map.mpr ⟨z, ?_, hz'⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hz'] at hy
      apply e.injective
      rw [map_mul, map_mul]
      exact hy
  have hJ' : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e.toMonoidHom x} : Set R')) := by
    refine ⟨(Subgroup.map_mono hJ.1).trans (le_of_eq hcent), ?_, ?_⟩
    · rw [← hcent]
      exact hJ.2.1.map e.toMonoidHom
    · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (J.equivMapOfInjective e.toMonoidHom e.injective).symm hJ.2.2
  have hx1' : e.toMonoidHom x ≠ 1 := fun h1 => hx1 (e.map_eq_one_iff.mp h1)
  obtain ⟨w', hw'J, hw'E, hw'1⟩ :=
    h (E.map e.toMonoidHom) hE' h3' hsc'
      (e.toMonoidHom x) ((Subgroup.mem_map_iff_mem (K := E) (x := x) e.injective).mpr hx)
      hx1' (J.map e.toMonoidHom) hJ'
  obtain ⟨w, hwJ, rfl⟩ := hw'J
  exact ⟨w, hwJ, (Subgroup.mem_map_iff_mem (K := E) (x := w) e.injective).mp hw'E,
    fun h1 => hw'1 (by rw [h1, map_one])⟩

end CFSG.StandardType
