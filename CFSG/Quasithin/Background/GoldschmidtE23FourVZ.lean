module

public import CFSG.Quasithin.Background.C1GNC128
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace E2

variable {G : Type} [Group G]

theorem le_normalizer_centralizer {H Z : Subgroup G} (hH : H ≤ Subgroup.normalizer (Z : Set G)) :
    H ≤ Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) := by
  have key : ∀ g ∈ H, ∀ c ∈ Subgroup.centralizer (Z : Set G), g * c * g⁻¹ ∈
      Subgroup.centralizer (Z : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro z hz
    have hz' : g⁻¹ * z * g ∈ Z := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hg)) z).mp hz
    have h1 := hc _ hz'
    calc z * (g * c * g⁻¹) = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * z := by group
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (fun x hx => key g hg x hx)
    (fun x hx => by simpa using key g⁻¹ (H.inv_mem hg) x hx)

variable [Finite G]

theorem le_centralizer_VZ_of_thompsonJ_le {H T M V : Subgroup G} (hmin : MinParabolic H T M)
    (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (h : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) :
    H ≤ Subgroup.centralizer (VZ T H : Set G) := by
  have hT := hmin.isSylow
  have hTH : T ≤ H := hT.1
  have hredZ : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hF hT
  set K := H ⊓ Subgroup.centralizer (VZ T H : Set G) with hK
  have hKH : K ≤ H := inf_le_left
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer hredZ.2.1 hg⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have hJTH : thompsonJ T ≤ H := (B6.thompsonJ_le T).trans hTH
  have hJX : thompsonJ T ≤ T ⊓ K := le_inf (B6.thompsonJ_le T) (le_inf hJTH h)
  have hJeq : thompsonJ (T ⊓ K) = thompsonJ T := B6.thompsonJ_eq_of_le hJX inf_le_left
  have hFrat := B6.frattini_two hKH hHK hTK
  have hNJ : H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      H ⊓ Subgroup.normalizer (thompsonJ T : Set G) := by
    refine inf_le_inf_left _ ?_
    have := normalizer_le_normalizer_thompsonJ (T ⊓ K)
    rwa [hJeq] at this
  have hlt : H ⊓ Subgroup.normalizer (thompsonJ T : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left fun he => hJ ?_
    have hHN : H ≤ Subgroup.normalizer (thompsonJ T : Set G) := he ▸ inf_le_right
    exact (le_pCoreOf_of_le_normalizer 2 hJTH hHN (hT.2.1.to_le (B6.thompsonJ_le T))).trans
      (MinParabolic.pCoreOf_le_centralizer hred)
  have hNM : H ⊓ Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
    hmin.le_of_lt (le_inf hTH (B6.le_normalizer_thompsonJ T)) hlt
  have hKM : ¬ K ≤ M := fun hKM => by
    have hHM : H ≤ M := hFrat.trans (sup_le hKM (hNJ.trans hNM))
    exact lt_irrefl H (lt_of_le_of_lt hHM hmin.maximal.1)
  have hHeq : T ⊔ K = H := by
    rw [sup_comm]
    exact hmin.eq_of_not_le le_sup_right (sup_le hKH hTH) fun h' => hKM (le_sup_left.trans h')
  have h2 := B6.isTwoQuotient_of_sup_eq hT.2.1 hHK hHeq
  exact hredZ.2.2.2 H le_rfl Subgroup.le_normalizer fun d hd =>
    (h2 d hd).imp fun k hk => (Subgroup.mem_inf.mp hk).2

end E2

end CFSG.Quasithin
