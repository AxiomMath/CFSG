module

public import CFSG.Quasithin.EmptyFaithful.S151S9UTr
public import CFSG.Quasithin.EmptyFaithful.S151S9UM23Blocks
public import CFSG.Quasithin.EmptyFaithful.S151S9UM23Lat

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat

theorem centralizer_singleton_le_of_le_zpowers {G : Type} [Group G] {z : G} {W : Subgroup G}
    (hW : W ≤ Subgroup.zpowers z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (W : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hW hw)
  have hzg : Commute z g := hg z rfl
  exact (hzg.zpow_left k).eq

theorem m23_mldAtSylow
    (h : S151S9T.m23CheckD) : MLDAtSylow m23CtxB.S := by
  obtain ⟨z₀, hz2, hZ, hczv⟩ := m23_centre_czv h
  refine ⟨?_, fun W hW _ Y hSY hY hlt => ?_⟩
  · rw [hZ, Nat.card_zpowers, hz2]
  · have hcen := centralizer_singleton_le_of_le_zpowers (hW.trans hZ.le)
    rcases m23_lat_cases hSY with ⟨j, hj16, rfl⟩ | htop
    · have h4 : m23CtxB.Y 4 ≤ Subgroup.centralizer {z₀} :=
        (hczv 4 (by norm_num)).mp (by decide)
      have hmem : j ∈ m23Incl[4]! :=
        (m23_Y_le_iff (by norm_num) hj16).mp (h4.trans (hcen.trans hlt.le))
      have hj45 : j = 4 ∨ j = 5 := by
        have key : ∀ i < 16, i ∈ m23Incl[4]! → i = 4 ∨ i = 5 := by decide
        exact key j hj16 hmem
      rcases hj45 with rfl | rfl
      · exact absurd (lt_of_le_of_lt (h4.trans hcen) hlt) (lt_irrefl _)
      · exact m23_actionData_y5
    · exact absurd htop hY

theorem mldAt_m23
    (h : S151S9T.m23CheckD) : MLDAt .M23 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  exact mldOver_of_sylow (Γ := ↥CFSG.Blueprint.NativeSporadic.M23) e S151S9T.m23B_S_sylow
    (m23_mldAtSylow h)

end CFSG.Quasithin.S151S9U
