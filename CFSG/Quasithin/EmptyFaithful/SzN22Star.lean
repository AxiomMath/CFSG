module

public import CFSG.Quasithin.EmptyFaithful.SzN22Core
public import CFSG.Quasithin.EmptyFaithful.SzN22Rig
public import CFSG.Quasithin.EmptyFaithful.SzN19Star

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace SzN22

section Star

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_C {Hs As Ts K : Subgroup (MulAut V)}
    (hcases : B56Case1 As ∨ B56Case2 As ∨ B56Case3 As ∨ B56Case4 As ∨ B56Case5 As)
    (hAH : As ≤ Hs) (hAn : ∀ g ∈ Hs, ∀ a ∈ As, g * a * g⁻¹ ∈ As) (hTH : Ts ≤ Hs)
    (hK : K ∈ cComp As) :
    ∃ C : Subgroup (MulAut V), conjClosure K Ts = K ⊔ C ∧ K ⊓ C = ⊥ ∧
      (∀ a ∈ K, ∀ b ∈ C, a * b = b * a) ∧ C ≤ Hs := by
  have hAnorm : ∀ y ∈ Hs, ∀ x, x ∈ As ↔ y * x * y⁻¹ ∈ As := fun y hy x =>
    ⟨hAn y hy x, fun hx => by simpa [mul_assoc] using hAn y⁻¹ (Hs.inv_mem hy) _ hx⟩
  by_cases hN : Ts ≤ Subgroup.normalizer (K : Set (MulAut V))
  · refine ⟨⊥, ?_, inf_bot_eq _, fun a _ b hb => ?_, bot_le⟩
    · rw [sup_bot_eq]
      refine le_antisymm (conjClosure_le fun g hg b hb => ?_) (le_conjClosure K Ts)
      exact (Subgroup.mem_normalizer_iff.mp (hN hg) b).mp hb
    · rw [Subgroup.mem_bot] at hb
      simp [hb]
  · obtain ⟨t, ht, hnt⟩ := IsConcreteLE.not_le_iff_exists.mp hN
    have hK' : SzN19.cj t K ∈ cComp As := S153L.comp_conj_mem_cComp (hAnorm t (hTH ht)) hK
    have hne : K ≠ SzN19.cj t K := fun h => hnt (SzN19.mem_normalizer_of_cj_eq h.symm)
    obtain ⟨hinf, hc, hall⟩ := SzN19.b56_pair hcases hK hK' hne
    refine ⟨SzN19.cj t K, ?_, hinf, hc, (le_of_mem_cComp hK').trans hAH⟩
    apply le_antisymm
    · refine conjClosure_le fun g hg b hb => ?_
      have hmem : g * b * g⁻¹ ∈ SzN19.cj g K := SzN19.conj_mem_cj hb
      have hKg : SzN19.cj g K ∈ cComp As := S153L.comp_conj_mem_cComp (hAnorm g (hTH hg)) hK
      rcases hall _ hKg with h | h
      · rw [h] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [h] at hmem
        exact Subgroup.mem_sup_right hmem
    · refine sup_le (le_conjClosure K Ts) ?_
      intro x hx
      have hx' := SzN19.mem_cj.mp hx
      have := mem_conjClosure ht hx'
      simpa [mul_assoc] using this

theorem k_star {Hs As Ms Ys Ts L₀s K : Subgroup (MulAut V)}
    (hcases : B56Case1 As ∨ B56Case2 As ∨ B56Case3 As ∨ B56Case4 As ∨ B56Case5 As)
    (hAH : As ≤ Hs) (hAn : ∀ g ∈ Hs, ∀ a ∈ As, g * a * g⁻¹ ∈ As) (hK : K ∈ cComp As)
    (hmain : ∀ K' ∈ cComp As, Ys ≤ Subgroup.normalizer (K' : Set (MulAut V)) ∧ ⁅K', Ys⁆ = K')
    (hO2 : pCoreOf 2 Hs = ⊥) (hTs : IsSylowTwoOf Ts Hs) (hYM : Ys ≤ Ms) (hMH : Ms ≤ Hs)
    (hTY : Ts ≤ Subgroup.normalizer (Ys : Set (MulAut V)))
    (hord : ∀ y ∈ Ys, ∃ k : ℕ, y ^ (2 ^ k * 3) = 1) (hex : ∃ y ∈ Ys, orderOf y = 3)
    (hY3 : ∀ E : Subgroup (MulAut V), E ≤ Ys → IsPGroup 3 E → Nat.card E ≤ 3)
    (hYgen : Ys = Subgroup.closure {y | y ∈ Ys ∧ orderOf y = 3})
    (hθ : ∀ x ∈ Ms, orderOf x = 3 → x ∈ Ys)
    (hmin : ∀ K' : Subgroup (MulAut V), Ys ⊔ Ts ≤ K' → K' ≤ Hs → K' ≠ Hs → K' ≤ Ms)
    (hHeq : Hs = L₀s ⊔ Ys ⊔ Ts) (hL₀ : L₀s ≤ conjClosure K Ts) (hRig : KRig K) :
    Ys ≤ conjClosure K Ts := by
  have hTH : Ts ≤ Hs := hTs.1
  have hAnorm : ∀ y ∈ Hs, ∀ x, x ∈ As ↔ y * x * y⁻¹ ∈ As := fun y hy x =>
    ⟨hAn y hy x, fun hx => by simpa [mul_assoc] using hAn y⁻¹ (Hs.inv_mem hy) _ hx⟩
  obtain ⟨C, hP, hinf, hKC, hCH⟩ := exists_C hcases hAH hAn hTH hK
  have hKH : K ≤ Hs := (le_of_mem_cComp hK).trans hAH
  have hYN : Ys ≤ Subgroup.normalizer ((conjClosure K Ts : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have key : ∀ y ∈ Ys, ∀ p ∈ conjClosure K Ts, y * p * y⁻¹ ∈ conjClosure K Ts := by
      intro y hy p hp
      let X : Subgroup (MulAut V) := (conjClosure K Ts).comap (MulAut.conj y).toMonoidHom
      have hX : conjClosure K Ts ≤ X := by
        refine conjClosure_le fun g hg b hb => ?_
        show y * (g * b * g⁻¹) * y⁻¹ ∈ conjClosure K Ts
        have hKg : SzN19.cj g K ∈ cComp As := S153L.comp_conj_mem_cComp (hAnorm g (hTH hg)) hK
        have hyKg := (hmain _ hKg).1 hy
        have h1 : g * b * g⁻¹ ∈ SzN19.cj g K := SzN19.conj_mem_cj hb
        have h2 : y * (g * b * g⁻¹) * y⁻¹ ∈ SzN19.cj g K :=
          (Subgroup.mem_normalizer_iff.mp hyKg _).mp h1
        have h3 := SzN19.mem_cj.mp h2
        have := mem_conjClosure hg h3
        simpa [mul_assoc] using this
      exact hX hp
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key y hy x, fun hx => by simpa [mul_assoc] using key y⁻¹ (Ys.inv_mem hy) _ hx⟩
  have hHL : Hs ≤ Subgroup.normalizer ((K ⊔ C : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← hP, hHeq]
    exact sup_le (sup_le (hL₀.trans Subgroup.le_normalizer) hYN) (le_normalizer_conjClosure K Ts)
  rw [hP]
  exact k_core hKC hinf (SzN19.not_isSolvable_of_mem_cComp hK) hKH hCH hHL hO2 hTs hYM hMH hTY hord
    hex hY3 hYgen hθ hmin (hmain K hK).1 (hmain K hK).2 hRig

end Star

end SzN22

end CFSG.Quasithin
