module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalT2b
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPUd
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem t2_dist_ne_five_full (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    {α α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hbad : ¬ Zv α ≤ Qv α')
    (hd : dist α α' = bAt α) (h5 : bAt α = 5) : False := by
  have hA := Amal.of_frame F
  set g0 := γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) with hg0
  have hb0 : bAt g0 = 5 := by
    rw [← h5]; exact bAt_eq_of_vtype_eq (by rw [hα, hg0, vtype_γ₀])
  have hcen : ∀ u' ∈ nbrs g0, Zv u' ≤ Zv g0 := by
    intro u' hu'
    have hty : vtype u' = true := by
      have := vtype_ne_of_adj (show (graph _ _ _).Adj g0 u' from hu')
      cases hv : vtype u' <;> simp_all [vtype_γ₀]
    have hc : ZCentral u' := by
      intro T hT
      refine Zv_eq_omega_of_central F u' (fun x hx => ?_) hT
      intro z hz
      exact ((hZ u' hty hz).2 x hx).symm
    exact hA.Zv_le_Zv_of_ZCentral (show g0 ∈ nbrs u' from
      (show (graph _ _ _).Adj g0 u' from hu').symm) hc
  have hZQδ : ∀ u' ∈ nbrs g0, Zv u' ≤ Qv g0 := fun u' hu' => (hcen u' hu').trans (hA.Zv_le_Qv g0)
  have hZQ : ∀ u' ∈ nbrs g0, ∀ u'' ∈ nbrs g0, Zv u' ≤ Qv u'' := by
    intro u' hu' u'' hu''
    refine (hcen u' hu').trans (Zv_le_Qv_of_dist_lt ?_)
    rw [hb0, dist_eq_one_iff_adj.mpr (show (graph _ _ _).Adj g0 u'' from hu'')]
    norm_num
  exact t2_dist_ne_five F hZ (pu_d F hZQδ hZQ) hα hbad hd h5

theorem t2_dist_ne_le_five (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    {α α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hbad : ¬ Zv α ≤ Qv α')
    (hd : dist α α' = bAt α) (hb : bAt α = 1 ∨ bAt α = 3 ∨ bAt α = 5) : False := by
  rcases hb with h | h | h
  · exact t2_dist_ne F hZ hα hbad hd (Or.inl h)
  · exact t2_dist_ne F hZ hα hbad hd (Or.inr h)
  · exact t2_dist_ne_five_full F hZ hα hbad hd h

end CFSG.Quasithin.Kleidman.F204
