module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineSub
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Seven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Tree
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4CentMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Fan48Def

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Track.eq_valence_parity (T : Track Γ G) (F : FanTree Γ G) {i j : ℤ}
    (h : valence Γ (T.line.vert i) = valence Γ (T.line.vert j)) : (i - j) % 2 = 0 := by
  by_contra hodd
  obtain ⟨k, hk⟩ : ∃ k : ℤ, i = (j + 1) + 2 * k := ⟨(i - (j + 1)) / 2, by omega⟩
  have h1 : valence Γ (T.line.vert i) = valence Γ (T.line.vert (j + 1)) := by
    rw [hk]
    exact T.valence_vert_zpow F (j + 1) k
  have h2 : valence Γ (T.line.vert j) ≠ valence Γ (T.line.vert (j + 1)) :=
    F.alternating _ _ (T.line.adj j)
  omega

theorem exists_long_tarc (T : Track Γ G) (F : FanTree Γ G) (h40 : Fan40 F) (hPi : TrackInPi T)
    {a : ℤ} (h3 : valence Γ (T.line.vert a) = 3) : ∃ b' : ℤ, IsTArc T a b' ∧ 6 ≤ b' - a := by
  obtain ⟨a₀, b₀, hmax⟩ := fan42_2a_max T F h40
  have h3₀ : valence Γ (T.line.vert a₀) = 3 := fan47 T F h40 hPi hmax.1 (Or.inl rfl)
  have hpar := T.eq_valence_parity F (h3.trans h3₀.symm)
  have hev := fan_4_3_2 T F hPi hmax.1
  have h6 := fan40_lineSingLe h40 (fan44_3 T F h40 hPi.1 hPi.2 hmax)
  have hab := hmax.1.1
  refine ⟨b₀ + 2 * ((a - a₀) / 2), ?_, by omega⟩
  have := hmax.1.translate T ((a - a₀) / 2)
  rwa [show a₀ + 2 * ((a - a₀) / 2) = a by omega] at this

theorem fan48_concl (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h211 : Tutte.TutteTree)
    (T : Track Γ G) (hPiS : InPiStar T) {a b : ℤ} (hθ : IsTArc T a b) : Fan48Concl T a b := by
  obtain ⟨hPi, d, f, hd3, hfN, hfR⟩ := hPiS
  have h3 : valence Γ (T.line.vert a) = 3 := fan47 T F h40 hPi hθ (Or.inl rfl)
  have hpar := T.eq_valence_parity F (h3.trans hd3.symm)
  have hfa : IsLenTwoReflection T.line a (T.τ ^ ((a - d) / 2) * f * (T.τ ^ ((a - d) / 2))⁻¹) := by
    have := hfR.conj_zpow T ((a - d) / 2)
    rwa [show d + 2 * ((a - d) / 2) = a by omega] at this
  have hfL : T.τ ^ ((a - d) / 2) * f * (T.τ ^ ((a - d) / 2))⁻¹ ∈
      Subgroup.normalizer (omega1 T.fixer : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem (T.zpow_mem_normalizer _) hfN)
      ((Subgroup.normalizer _).inv_mem (T.zpow_mem_normalizer _))
  have hS := subgraph48 F hPi hθ hfL hfa
  obtain ⟨hinfα, hinfβ⟩ := H48_inf F hPi hθ
  obtain ⟨hfix, hlen⟩ := fan46_three hS F hPi h211 h3
  refine ⟨hS, hinfα, hinfβ, fun h hh z hz => ?_, hlen, ?_,
    ⟨_, (swap_mem hfL hfa).1, (swap_mem hfL hfa).2⟩⟩
  · rw [← hfix] at hz ⊢
    exact fixSet_orbit_conj hh hz
  · obtain ⟨b', hθ', hlong⟩ := exists_long_tarc T F h40 hPi h3
    have hS' := subgraph48 F hPi hθ' hfL hfa
    obtain ⟨hfix', -⟩ := fan46_three hS' F hPi h211 h3
    obtain ⟨m', hm'⟩ : ∃ m' : ℤ, b' - a = 2 * m' :=
      ⟨(b' - a) / 2, by have := fan_4_3_2 T F hPi hθ'; omega⟩
    intro x hx hx3 z hz
    exact fan46_central hS' F hm' hlong h28 h3 x ⟨inf_le_H48 T a hx, hx.2⟩ hx3 z
      (by rw [hfix']; exact hz)

theorem fan48_two (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h211 : Tutte.TutteTree) :
    Fan48Two F := fun T hPiS a _ hθ => by
  have h := fan48_concl F h40 h28 h211 T hPiS hθ
  exact ⟨H48 T a, h.subgraph, h.normal, h.central⟩

end CFSG.Quasithin.Fan86
