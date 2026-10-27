module

public import CFSG.Quasithin.MS93.S45Q4PC
public import CFSG.Quasithin.MS93.S45Q4

public section

namespace CFSG.Quasithin.MS93.S45Q4

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.Quasithin.Fan86.Univ
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : S45.Ctx M T L φ)
include c

theorem hQ4 : c.HQ4 := by
  intro p N hp a ha h24 haN g hg
  have h := c.hyp
  have hq : IsNBPath (puAmalgam h.le) (fun i => p (a + i)) 4 :=
    (isNBPath_shift hp.toIsNBPath a).mono (by omega)
  have hpa : IsMVtx (puAmalgam h.le) (p a) := by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := a) (by omega) hp.mvtx ha
    rwa [zero_add] at this
  have ha2 : Even (a - 2) := by obtain ⟨k, hk⟩ := ha; exact ⟨k - 1, by omega⟩
  have ha4 : Even (a - 4) := by obtain ⟨k, hk⟩ := ha; exact ⟨k - 2, by omega⟩
  have ha6 : Even (a - 6) := by obtain ⟨k, hk⟩ := ha; exact ⟨k - 3, by omega⟩
  have hs : ∃ k ∈ stab (puAmalgam h.le) (p (a + 2)), k • p (a + 4) = p (a + 0) :=
    c.straight_of_isGoodPath hp ha (by omega)
  have hVV := (c.commutator_vv_vv hp ha (by omega) (by omega)).1
  have hc : IsCritical (puAmalgam h.le) (p (a - 2)) (p (a + 6)) := by
    have := c.isCritical_of_isGoodPath hp ha2 (by omega)
    rwa [show a - 2 + 8 = a + 6 by omega] at this
  have hgeo : geo (puAmalgam h.le) (p (a - 2)) (p (a + 6)) 2 = p a := by
    rw [hp.eq_geo (i := a - 2) (j := a + 6) (k := a) (by omega) (by omega) (by omega),
      show a - (a - 2) = 2 by omega]
  have hK1 : ⁅Vv (puAmalgam h.le) (p (a + 0)), Vv _ (p (a + 4))⁆ ≤ Zloc h.le L (p (a + 0)) := by
    rw [add_zero, hVV, ← hgeo]
    exact c.critR_le_zloc hc
  have hK2 : ⁅Vv (puAmalgam h.le) (p (a + 0)), Vv _ (p (a + 4))⁆ ≤
      Usup _ (p (a + 2)) (p (a + 3)) := by
    rw [add_zero, hVV]
    have := c.critR_eq_usup_inf hp (x := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 + 8 = a + 6 by omega, show a - 2 + 4 = a + 2 by omega,
      show a - 2 + 5 = a + 3 by omega] at this
    rw [this]
    exact inf_le_right
  have hH2 : Hloc h.le L (p (a + 2)) = Usup (puAmalgam h.le) (p (a + 0)) (p (a + 1)) := by
    have := c.hloc_eq_usup hp (x := a - 4) ha4 (by omega) (by omega)
    rwa [show a - 4 + 6 = a + 2 by omega, show a - 4 + 4 = a + 0 by omega,
      show a - 4 + 5 = a + 1 by omega] at this
  have hH4 : Hloc h.le L (p (a + 4)) = Usup (puAmalgam h.le) (p (a + 2)) (p (a + 3)) := by
    have := c.hloc_eq_usup hp (x := a - 2) ha2 (by omega) (by omega)
    rwa [show a - 2 + 6 = a + 4 by omega, show a - 2 + 4 = a + 2 by omega,
      show a - 2 + 5 = a + 3 by omega] at this
  have hN2 : stab (puAmalgam h.le) (p (a + 0)) ⊓
      Subgroup.normalizer (Qv (puAmalgam h.le) (p (a + 1)) : Set (puAmalgam h.le).Universal) ≤
        Subgroup.normalizer (ZM (puAmalgam h.le) (p (a + 2)) : Set (puAmalgam h.le).Universal) := by
    have := c.normalizer_zm_right hp (x := a - 6) ha6 (by omega) (by omega)
    rwa [show a - 6 + 6 = a + 0 by omega, show a - 6 + 7 = a + 1 by omega,
      show a - 6 + 8 = a + 2 by omega] at this
  have hN4 : stab (puAmalgam h.le) (p (a + 2)) ⊓
      Subgroup.normalizer (Qv (puAmalgam h.le) (p (a + 3)) : Set (puAmalgam h.le).Universal) ≤
        Subgroup.normalizer (ZM (puAmalgam h.le) (p (a + 4)) : Set (puAmalgam h.le).Universal) := by
    have := c.normalizer_zm_right hp (x := a - 4) ha4 (by omega) (by omega)
    rwa [show a - 4 + 6 = a + 2 by omega, show a - 4 + 7 = a + 3 by omega,
      show a - 4 + 8 = a + 4 by omega] at this
  have hZ13 : ZH (puAmalgam h.le) (p (a + 1)) ≠ ZH _ (p (a + 3)) := by
    have := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
    rwa [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at this
  exact zm_smul_le_qv_of c (q := fun i => p (a + i)) hq (by rwa [add_zero]) hs hK1 hK2 hH2 hH4
    hN2 hN4 hZ13 (by rwa [add_zero])

end CFSG.Quasithin.MS93.S45Q4

