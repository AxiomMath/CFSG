module

public import CFSG.Quasithin.EmptyFaithful.SzN19B56
public import CFSG.Quasithin.EmptyFaithful.S153LNs

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace SzN19

section Pair

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem not_isSolvable_of_mem_cComp {J K : Subgroup Ω} (hK : K ∈ cComp J) :
    ¬ Group.IsSolvable ↥K := fun hs => by
  have h1 := (isSolvable_iff_perfectCore_eq_bot K).mp hs
  rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)] at h1
  exact ne_bot_of_mem_cComp hK h1

end Pair

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem normalizes_component {Hs Js Ms Ys Ts K : Subgroup (MulAut V)}
    (hcases : B56Case1 Js ∨ B56Case2 Js ∨ B56Case3 Js ∨ B56Case4 Js ∨ B56Case5 Js)
    (hJH : Js ≤ Hs) (hJn : ∀ h ∈ Hs, ∀ j ∈ Js, h * j * h⁻¹ ∈ Js)
    (hTH : Ts ≤ Hs) (hT2 : IsPGroup 2 Ts)
    (hTY : Ts ≤ Subgroup.normalizer (Ys : Set (MulAut V))) (hYs : Group.IsSolvable ↥Ys)
    (hmin : ∀ K' : Subgroup (MulAut V), Ys ⊔ Ts ≤ K' → K' ≤ Hs → K' ≠ Hs → K' ≤ Ms)
    (hθ : ∀ x ∈ Ms, orderOf x = 3 → x ∈ Ys)
    (hY3 : ∀ E : Subgroup (MulAut V), E ≤ Ys → IsPGroup 3 E → Nat.card E ≤ 3)
    (hex : ∃ y ∈ Ys, orderOf y = 3)
    (hK : K ∈ cComp Js) (hYK : Ys ≤ conjClosure K Ts) :
    Ts ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  intro t ht
  by_contra hnt
  have hJnorm : ∀ y ∈ Hs, ∀ x, x ∈ Js ↔ y * x * y⁻¹ ∈ Js := fun y hy x =>
    ⟨hJn y hy x, fun hx => by simpa [mul_assoc] using hJn y⁻¹ (Hs.inv_mem hy) _ hx⟩
  have hcomp : ∀ s ∈ Ts, ∀ K' ∈ cComp Js, cj s K' ∈ cComp Js := fun s hs K' hK' =>
    S153L.comp_conj_mem_cComp (hJnorm s (hTH hs)) hK'
  have hK' : cj t K ∈ cComp Js := hcomp t ht K hK
  have hne : K ≠ cj t K := fun h => hnt (mem_normalizer_of_cj_eq h.symm)
  obtain ⟨hinf, hc, hall⟩ := b56_pair hcases hK hK' hne
  have hinj : ∀ s : MulAut V, ∀ A B : Subgroup (MulAut V), cj s A = cj s B → A = B := fun s A B h =>
    Subgroup.map_injective (MulAut.conj s).injective h
  have hperm : ∀ s ∈ Ts, (cj s K = K ∧ cj s (cj t K) = cj t K) ∨
      (cj s K = cj t K ∧ cj s (cj t K) = K) := by
    intro s hs
    have h1 := hall _ (hcomp s hs K hK)
    have h2 := hall _ (hcomp s hs _ hK')
    have hsne : cj s K ≠ cj s (cj t K) := fun h => hne (hinj s _ _ h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hsne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hsne
  have hKH : K ≤ Hs := (le_of_mem_cComp hK).trans hJH
  have hK'H : cj t K ≤ Hs := (le_of_mem_cComp hK').trans hJH
  have hYX : Ys ≤ K ⊔ cj t K := by
    refine hYK.trans (conjClosure_le fun g hg b hb => ?_)
    have hmem : g * b * g⁻¹ ∈ cj g K := conj_mem_cj hb
    rcases hall _ (hcomp g hg K hK) with h | h
    · rw [h] at hmem
      exact Subgroup.mem_sup_left hmem
    · rw [h] at hmem
      exact Subgroup.mem_sup_right hmem
  have key := not_swap (N₁ := K) (N₂ := cj t K) (Y := Ys) (M := Ms) (T := Ts) (H := Hs) hc hinf
    (not_isSolvable_of_mem_cComp hK) hKH hK'H hTH hperm hT2 hTY hYs hYX
    (fun K'' h1 h2 h3 => hmin K'' h1 h2 (fun heq => h3 (heq ▸ hKH))) hθ hY3 hex t ht
  exact hne key.symm

end Main

end SzN19

end CFSG.Quasithin
