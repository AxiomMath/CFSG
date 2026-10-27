module

public import CFSG.Monster.GMS.CoTwoFacts
public import CFSG.Monster.GMS.CoTwoLemma
public import CFSG.Monster.GMS.Leech.Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace LeechSystem

variable {G : Type*} [Group G] {w : G} (L : LeechSystem w)

include L

theorem image_centralizer_inf_one
    {t : G} (ht : t ∈ leechQ w) (hv : L.vec t ≠ 0) :
    L.image (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)) =
      co1Stab (L.vec t) := by
  have hind : LinearIndependent (ZMod 2) fun _ : Unit => L.vec t :=
    linearIndependent_unique_iff.2 hv
  have h := L.image_inf_iInf_centralizer (fun _ : Unit => t) (fun _ => ht) hind
  have h1 : Subgroup.centralizer ({w} : Set G) ⊓ ⨅ _ : Unit, Subgroup.centralizer ({t} : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) := by
    rw [iInf_const, inf_comm]
  rw [h1, iInf_const] at h
  exact h

theorem image_centralizer_inf_two
    {p q : G} (hp : p ∈ leechQ w) (hq : q ∈ leechQ w)
    (hind : LinearIndependent (ZMod 2) ![L.vec p, L.vec q])
    (hle : Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.centralizer ({w} : Set G)) :
    L.image (Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G)) =
      co1Stab (L.vec p) ⊓ co1Stab (L.vec q) := by
  have hind' : LinearIndependent (ZMod 2) fun i : Fin 2 => L.vec (![p, q] i) := by
    have : (fun i : Fin 2 => L.vec (![p, q] i)) = ![L.vec p, L.vec q] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    exact hind
  have h := L.image_inf_iInf_centralizer ![p, q] (fun i => by fin_cases i <;> assumption) hind'
  have h1 : Subgroup.centralizer ({w} : Set G) ⊓
      ⨅ i : Fin 2, Subgroup.centralizer ({![p, q] i} : Set G) =
      Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · rintro ⟨-, h₁, h₂⟩
      exact ⟨h₁, h₂⟩
    · intro h'
      exact ⟨hle (Subgroup.mem_inf.2 h'), h'.1, h'.2⟩
  have h2 : (⨅ i : Fin 2, co1Stab (L.vec (![p, q] i))) = co1Stab (L.vec p) ⊓ co1Stab (L.vec q) := by
    ext x
    simp [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_two]
  rw [h1, h2] at h
  exact h

theorem commutator_centralizer_inf_one
    (hF : Co2McLFacts) {t : G} (htL : t ∈ L.typeSet 0) :
    ⁅Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G),
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)⁆ =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) := by
  have htQ : t ∈ leechQ w := htL.1
  have hu : L.vec t ∈ co1Orbit 0 := htL.2
  have hS : ∀ y : Fin 24 → ZMod 2, y ∈ {y | bil₀ y (L.vec t) = 0} ↔
      y ∈ L.vecSpace (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)) := by
    intro y
    have h := L.mem_vecSpace_centralizer_inf (fun _ : Unit => t) (fun _ => htQ) y
    rw [inf_comm, show (⨅ _ : Unit, Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({t} : Set G) from iInf_const] at h
    simpa using h.symm
  refine L.commutator_eq_of_comm_span inf_le_right (L.image_centralizer_inf_one htQ
    (L.vec_ne_zero_of_mem_typeSet htL)) hS (hF.perfect_co2 _ hu) ?_ ?_
  · intro X h1 h2 h3 y hy
    exact hF.comm_span_co2 _ hu X h1 h2 h3 y hy
  · obtain ⟨y₁, y₂, h1, h2, h3⟩ := hF.nondeg_co2 _ hu
    exact ⟨y₁, h1, y₂, h2, h3⟩

theorem irreducible_centralizer_inf_one
    (hF : Co2McLFacts) {t : G} (htL : t ∈ L.typeSet 0)
    (N : Subgroup G) (htN : t ∈ N) (hwN : w ∈ N)
    (hNle : N ≤ leechQ w ⊓ Subgroup.centralizer ({t} : Set G))
    (hinv : ∀ g ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G),
      ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    (∀ n ∈ N, n = 1 ∨ n = t ∨ n = w ∨ n = t * w) ∨
      N = leechQ w ⊓ Subgroup.centralizer ({t} : Set G) := by
  have htQ : t ∈ leechQ w := htL.1
  have hu : L.vec t ∈ co1Orbit 0 := htL.2
  have hperp : ∀ q ∈ leechQ w ⊓ Subgroup.centralizer ({t} : Set G), bil₀ (L.vec q) (L.vec t) = 0 :=
    fun q hq => (L.comm_eq_one_iff hq.1 htQ).1
      (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 hq.2))
  have hIN : ∀ n ∈ N, n ∈ leechQ w ∧ n ∈ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_inf.1 (hNle hn)
  have hmain := hF.irred_co2 _ hu (L.vecSpace N) (L.mem_vecSpace.2 ⟨t, ⟨htQ, htN⟩, rfl⟩)
    (by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := L.mem_vecSpace.1 hy
      exact hperp n (hNle hn.2))
    (by
      intro A hA y hy
      obtain ⟨c, hc, rfl⟩ := L.mem_image.1
        ((L.image_centralizer_inf_one htQ (L.vec_ne_zero_of_mem_typeSet htL)).symm ▸ hA)
      obtain ⟨n, hn, rfl⟩ := L.mem_vecSpace.1 hy
      exact L.mem_vecSpace.2 ⟨(c : G) * n * (c : G)⁻¹, ⟨L.conj_mem c hn.1, hinv _ hc _ hn.2⟩,
        L.vec_conj c n hn.1⟩)
  rcases hmain with h | h
  · left
    intro n hn
    have hmem : L.vec n ∈ Submodule.span (ZMod 2) {L.vec t} :=
      h ▸ L.mem_vecSpace.2 ⟨n, ⟨(hIN n hn).1, hn⟩, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      rcases (L.vec_eq_zero n (hIN n hn).1).1 hc.symm with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
    · rw [one_smul] at hc
      rcases L.eq_or_eq_mul_z (hIN n hn).1 htQ hc.symm with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr h1))
  · right
    refine le_antisymm hNle fun q hq => ?_
    obtain ⟨n, hn, hnq⟩ := L.mem_vecSpace.1 (h (L.vec q) (hperp q hq))
    rcases L.eq_or_eq_mul_z hq.1 hn.1 hnq.symm with h1 | h1
    · rw [h1]
      exact hn.2
    · rw [h1]
      exact mul_mem hn.2 hwN

theorem commutator_centralizer_inf_two
    (hF : Co2McLFacts) {p q : G} (hp : p ∈ L.typeSet 0)
    (hq : q ∈ L.typeSet 0) (hsum : L.vec p + L.vec q ∈ co1Orbit 1)
    (hle : Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.centralizer ({w} : Set G)) :
    ⁅Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G),
        Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G)⁆ =
      Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) := by
  have hind : LinearIndependent (ZMod 2) ![L.vec p, L.vec q] :=
    Leech.linearIndependent_pair_of_add_mem (L.vec_ne_zero_of_mem_typeSet hp)
      (L.vec_ne_zero_of_mem_typeSet hq) hsum
  have hS : ∀ y : Fin 24 → ZMod 2, y ∈ {y | bil₀ y (L.vec p) = 0 ∧ bil₀ y (L.vec q) = 0} ↔
      y ∈ L.vecSpace (Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G)) := by
    intro y
    have h := L.mem_vecSpace_centralizer_inf ![p, q] (fun i => by fin_cases i <;> simp [hp.1, hq.1])
      y
    have h1 : Subgroup.centralizer ({w} : Set G) ⊓
        ⨅ i : Fin 2, Subgroup.centralizer ({![p, q] i} : Set G) =
        Subgroup.centralizer ({p} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      constructor
      · rintro ⟨-, h₁, h₂⟩
        exact ⟨h₁, h₂⟩
      · intro h'
        exact ⟨hle (Subgroup.mem_inf.2 h'), h'.1, h'.2⟩
    rw [h1] at h
    simpa [Fin.forall_fin_two] using h.symm
  refine L.commutator_eq_of_comm_span hle (L.image_centralizer_inf_two hp.1 hq.1 hind hle) hS
    (hF.perfect_mcl _ hp.2 _ hq.2 hsum) ?_ ?_
  · intro X h1 h2 h3 y hy
    exact hF.comm_span_mcl _ hp.2 _ hq.2 hsum X h1 h2 (fun A hA y h₁ h₂ => h3 A hA y ⟨h₁, h₂⟩) y
      hy.1 hy.2
  · obtain ⟨y₁, y₂, h1, h2, h3, h4, h5⟩ := hF.nondeg_mcl _ hp.2 _ hq.2 hsum
    exact ⟨y₁, ⟨h1, h2⟩, y₂, ⟨h3, h4⟩, h5⟩

end LeechSystem

end CFSG.Monster.GMS
