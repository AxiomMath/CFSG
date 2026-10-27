module

public import CFSG.Quasithin.EmptyFaithful.S151S9TM24
public import CFSG.Quasithin.EmptyFaithful.S151S9UTr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1c
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
  CFSG.QuasithinUnique.K1.SporadicPerm

theorem m24_actionDataG_of_hom {X : Type} [Group X] {m : ℕ} (hm : 5 ≤ m)
    (φ : X →* Equiv.Perm (Fin m)) (hker : IsPGroup 2 ↥φ.ker)
    (hrange : alternatingGroup (Fin m) ≤ φ.range) : ActionDataG X := by
  refine ⟨⊤, m, φ.comp (⊤ : Subgroup X).subtype, inferInstance, ⟨0, by simp⟩, hm, ?_, ?_⟩
  · rw [← MonoidHom.comap_ker]
    exact hker.comap_of_injective _ (Subgroup.subtype_injective _)
  · intro x hx
    obtain ⟨y, rfl⟩ := hrange hx
    exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩

theorem m24_actionData_octad :
    ActionData A312M24.Z1 := by
  refine m24_actionDataG_of_hom (m := A312M24.LO.length) (by decide) A312M24.rho1 ?_ ?_
  · rw [A312M24.rho1_ker.2]
    refine IsPGroup.of_card (n := 4) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A312M24.V1_le_Z1).toEquiv,
      A312M24.card_V1]
    norm_num
  · exact (A312M24.rho1_range).ge

theorem m24_mldAtSylow :
    MLDAtSylow A312M24.m24CtxE.S := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := CFSG.Quasithin.S151S9T.m24_centre
  have hZ' : centerOf A312M24.m24CtxE.S = Subgroup.zpowers z₀ := hZ
  have h4 : m24Ctx.Y 4 ≤ Subgroup.centralizer ({z₀} : Set A312M24.G24) :=
    m24_Y4_le_centralizer hzT
  refine ⟨by rw [hZ', Nat.card_zpowers, hz2], ?_⟩
  intro W hWS hW0 Y hSY hY hlt
  have hWz : W = Subgroup.zpowers z₀ := by
    refine le_antisymm (hZ' ▸ hWS) ?_
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW0
    have hwz : (w : A312M24.G24) ∈ Subgroup.zpowers z₀ := hZ' ▸ hWS w.2
    rcases CFSG.Quasithin.S151S9T.LatAux.eq_one_or_eq_of_mem_zpowers hz2 hwz with h1 | h1
    · exact absurd (Subtype.ext h1) hw1
    · rw [Subgroup.zpowers_le, ← h1]
      exact w.2
  have hcW : m24Ctx.Y 4 ≤ Subgroup.centralizer (W : Set A312M24.G24) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hWz] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hyz : z₀ * y = y * z₀ :=
      CFSG.Quasithin.S151S9T.LatAux.mem_centralizer_single_iff.mp (h4 hy)
    exact (Commute.zpow_left hyz k).eq
  obtain ⟨j, hj, hYj, -⟩ := A312M24.overgroup_member hSY hY
  have hY4j : m24Ctx.Y 4 ≤ m24Ctx.Y j := by
    have := hcW.trans hlt.le
    rw [hYj] at this
    exact this
  have hmem : j ∈ CFSG.Quasithin.S151S9T.m24Incl[4]! :=
    ((m24_Y_le_iff (by norm_num) hj).mp hY4j)
  have hrow : CFSG.Quasithin.S151S9T.m24Incl[4]! = [1, 4] := rfl
  rw [hrow] at hmem
  have hj14 : j = 1 ∨ j = 4 := by simpa using hmem
  rcases hj14 with rfl | rfl
  · rw [hYj, ← A312M24.Z1_eq_Y1.2]
    exact m24_actionData_octad
  · exfalso
    rw [hYj] at hlt
    exact lt_irrefl _ (lt_of_le_of_lt hcW hlt)

theorem mldAt_m24 :
    MLDAt .M24 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  exact mldOver_of_sylow (Γ := A312M24.G24) e A312M24.m24_S_sylow' m24_mldAtSylow

end CFSG.Quasithin.S151S9U
