module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F7
public import CFSG.Quasithin.Vol2.Ch10SecGFact
public import CFSG.Quasithin.Vol2.Ch10SecQ4F3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem g64CommTransvFact_holds : G64CommTransvFact := by
  intro V _ _ hV2 G a h61 hcard hconc P hP v₁ hc g hg hcomm hmove
  obtain ⟨s, Ks, -, hsupK, hind, hcommK, hsupV, hfixV, ⟨hs0, haK⟩, hperm, -, hmod, h3, -⟩ :=
    hconc
  have hv₁1 : v₁ ≠ 1 := by
    intro h
    rw [hc, h, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    omega
  rcases C10E4.fix_three_or_lin_two (hmod ⟨0, hs0⟩) with ⟨F, instF, instFF, hF2, π, hπ⟩ | h3fix
  · right
    exact C10E4.lin_two_case hV2 h61 hc hv₁1 hsupK hind hcommK hsupV hfixV haK hperm h3
      (by simpa using hF2) hπ hg hcomm hmove
  · left
    have hKG : conjClosure (Subgroup.zpowers a) G ≤ G := conjClosure_le fun h hh z hz =>
      G.mul_mem (G.mul_mem hh ((Subgroup.zpowers_le.mpr h61.mem) hz)) (G.inv_mem hh)
    have hK0G : Ks ⟨0, hs0⟩ ≤ G := (hsupK ▸ le_iSup Ks ⟨0, hs0⟩).trans hKG
    have hW'fix : (⨆ (i : Fin s) (_ : i ≠ ⟨0, hs0⟩), commV (Ks i)) ≤ fixV (Ks ⟨0, hs0⟩) :=
      iSup₂_le fun i hi => hfixV _ i (Ne.symm hi)
    have hVsup := C10E4.sup_commV_eq_top hsupV ⟨0, hs0⟩
    refine C10E4.exists_proper_of_fix_three hV2 h61 hc hP.1 hP.2.1 fun u => ?_
    have hu : u ∈ commV (Ks ⟨0, hs0⟩) ⊔ (⨆ (i : Fin s) (_ : i ≠ ⟨0, hs0⟩), commV (Ks i)) :=
      hVsup ▸ Subgroup.mem_top u
    obtain ⟨u₀, hu₀, u', hu', rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨x, hxK, hx3, hxu₀⟩ := h3fix u₀ hu₀
    exact ⟨x, hK0G hxK, hx3, by rw [map_mul, hxu₀, hW'fix hu' x hxK]⟩

end CFSG.Quasithin.Vol2.Ch10.SecG
