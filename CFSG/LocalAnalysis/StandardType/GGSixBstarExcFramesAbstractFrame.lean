module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAutTrivial

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.LieType.SeitzGeneration CFSG.Open
open scoped Pointwise

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ] {p m k : ℕ} [Fact p.Prime]

theorem trivial_on_stable_of_fixedSubgroup (C Dg : Subgroup Γ)
    (hDg : Dg ≤ Subgroup.normalizer (C : Set Γ)) (hk : ¬ p ∣ k) (hkDg : ∀ d ∈ Dg, d ^ k ∈ C)
    (hSyl : SylowTorus C p m) (s : Γ →* Γ) {E : Subgroup Γ} (hEC : E ≤ C)
    (hE : IsElemAbelian p E) (hEcard : p ^ m ≤ Nat.card E) (hEs : ∀ e ∈ E, s e = e) {x : Γ}
    (hx : x ∈ C ⊔ Dg) {α : MulAut C} (hαp : α ^ p = 1)
    (hα : ∀ h : C, (α h : Γ) = x * s h * x⁻¹) {Bs : Subgroup C} (hBs : IsElemAbelian p Bs)
    (hBsc : p ^ m ≤ Nat.card Bs) (hstable : ∀ b ∈ Bs, α b ∈ Bs) : ∀ b ∈ Bs, α b = b := by
  classical
  have hxN : x ∈ Subgroup.normalizer (C : Set Γ) :=
    (sup_le Subgroup.le_normalizer hDg :
      C ⊔ Dg ≤ Subgroup.normalizer (C : Set Γ)) hx
  have hsC : ∀ h ∈ C, s h ∈ C := by
    intro h hh
    have h1 := hα ⟨h, hh⟩
    have h2 : s h = x⁻¹ * ((α ⟨h, hh⟩ : C) : Γ) * x := by
      rw [h1]
      group
    rw [h2]
    have hαC : ((α ⟨h, hh⟩ : C) : Γ) ∈ C := (α ⟨h, hh⟩).2
    have h3 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) _).1 hαC
    rwa [inv_inv] at h3
  have hBmap : IsElemAbelian p (Bs.map C.subtype) := isElemAbelian_map_frame C.subtype hBs
  have hBcard : p ^ m ≤ Nat.card (Bs.map C.subtype) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hBsc
  have hnorm : ∀ b ∈ Bs.map C.subtype, x * s b * x⁻¹ ∈ Bs.map C.subtype := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨α b, hstable b hb, hα b⟩
  have hit : ∀ j : ℕ, ∀ b : C, (fun h => x * s h * x⁻¹)^[j] (b : Γ) =
      (((α ^ j) b : C) : Γ) := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [Function.iterate_succ_apply', ih b]
      show x * s (((α ^ j) b : C) : Γ) * x⁻¹ = _
      rw [← hα, pow_succ', MulAut.mul_apply]
  have hord : ∀ b ∈ Bs.map C.subtype, (fun h => x * s h * x⁻¹)^[p] b = b := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := hit p b
    rw [hαp] at h1
    exact h1
  have key := fixes_of_sylowTorus_of_fixedSubgroup (C := C) (Dg := Dg) hDg hk hkDg hSyl s hsC hEC
    hE hEcard hEs (Subgroup.map_subtype_le Bs) hBmap hBcard hx hnorm hord
  intro b hb
  have h1 := key b ⟨b, hb, rfl⟩
  refine Subtype.ext ?_
  rw [hα b]
  exact h1

theorem centralizes_of_induced_abstract {G : Type} [Group G] (hk : ¬ p ∣ k) (C : Subgroup Γ)
    (hSyl : SylowTorus C p m)
    (hNF : ∀ α : MulAut C, α ^ p = 1 →
      ∃ (Dg : Subgroup Γ) (x : Γ) (s : Γ →* Γ) (E : Subgroup Γ),
        Dg ≤ Subgroup.normalizer (C : Set Γ) ∧ (∀ d ∈ Dg, d ^ k ∈ C) ∧ x ∈ C ⊔ Dg ∧ E ≤ C ∧
          IsElemAbelian p E ∧ p ^ m ≤ Nat.card E ∧ (∀ e ∈ E, s e = e) ∧
          ∀ h : C, (α h : Γ) = x * s h * x⁻¹)
    (ψ : C →* G) (hψ : Function.Injective ψ) {Bs : Subgroup G} (hBsR : Bs ≤ ψ.range)
    (hBs : IsElemAbelian p Bs) (hBsc : p ^ m ≤ Nat.card Bs) {g : G}
    (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) (hgp : g ^ p = 1) :
    g ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  haveI : Finite C := inferInstance
  obtain ⟨α, hα⟩ := exists_inducedAut ψ hψ hgN
  have hαp : α ^ p = 1 := inducedAut_pow_eq_one ψ hψ hα hgp
  obtain ⟨Dg, x, s, E, hDg, hkDg, hx, hEC, hE, hEc, hEs, hαx⟩ := hNF α hαp
  have hBs' : IsElemAbelian p (Bs.comap ψ) := isElemAbelian_comap_frame ψ hψ hBs
  have hcard : p ^ m ≤ Nat.card (Bs.comap ψ) := by
    rw [card_comap_of_le_range ψ hψ hBsR]
    exact hBsc
  have hstable : ∀ b ∈ Bs.comap ψ, α b ∈ Bs.comap ψ := by
    intro b hb
    have hb' : ψ b ∈ Bs := hb
    show ψ (α b) ∈ Bs
    rw [hα b]
    exact (Subgroup.mem_normalizer_iff.1 hgB (ψ b)).1 hb'
  have hfix := trivial_on_stable_of_fixedSubgroup C Dg hDg hk hkDg hSyl s hEC hE hEc hEs hx hαp
    hαx hBs' hcard hstable
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨b, rfl⟩ := hBsR hy
  have h1 := hα b
  rw [hfix b hy] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm

end Abstract

section SelfCentralizing

variable {C : Type*} [Group C] [Finite C] {p m : ℕ} [Fact p.Prime]

theorem le_card_of_sylowTorus_of_sc (h : SylowTorus C p m) {A : Subgroup C}
    (hA : IsElemAbelian p A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set C), c ^ p = 1 → c ∈ A) : p ^ m ≤ Nat.card A := by
  obtain ⟨T, E, hT, hconj, hET, hE, hEel, hcard⟩ := h.exists_torus
  obtain ⟨g, hg⟩ := hconj A (isPGroup_of_isElemAbelian hA)
  have hAE : A ≤ E.map (MulAut.conj g).toMonoidHom := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := hg ha
    refine ⟨t, hE t ht ?_, hta⟩
    have h1 : a ^ p = 1 := hA.2 a ha
    rw [← hta, ← map_pow] at h1
    exact (MulAut.conj g).injective (h1.trans (map_one (MulAut.conj g)).symm)
  have hE'A : E.map (MulAut.conj g).toMonoidHom ≤ A := by
    intro y hy
    refine hSC y ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨e, he, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hg ha
      have := hT
      rw [← map_mul, ← map_mul, setLike_mul_comm ht (hET he)]
    · obtain ⟨e, he, rfl⟩ := hy
      rw [← map_pow, hEel.2 e he, map_one]
  have hEA : A = E.map (MulAut.conj g).toMonoidHom := le_antisymm hAE hE'A
  rw [hEA, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

end SelfCentralizing

end ExcFrames

end CFSG.StandardType
