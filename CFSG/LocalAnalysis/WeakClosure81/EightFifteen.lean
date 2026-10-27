module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteen
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFiveMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_of_relIndex_two_of_le {V₁ V D : Subgroup G} (hV₁V : V₁ ≤ V) (hV₁D : V₁ ≤ D)
    (h2 : V₁.relIndex V = 2) {g : G} (hgV : g ∈ normalizer (V : Set G))
    (hgD : g ∈ normalizer (D : Set G)) {x : G} (hx : x ∈ V) : g * x * g⁻¹ * x⁻¹ ∈ D := by
  have hP : V₁ ≤ V ⊓ D := le_inf hV₁V hV₁D
  have hdvd : (V ⊓ D).relIndex V ∣ 2 := h2 ▸ Subgroup.relIndex_dvd_of_le_left V hP
  have hpos : 0 < (V ⊓ D).relIndex V := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : (V ⊓ D).relIndex V ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h12 : (V ⊓ D).relIndex V = 1 ∨ (V ⊓ D).relIndex V = 2 := by omega
  rcases h12 with h1 | h2'
  · have hVD : V ≤ V ⊓ D := Subgroup.relIndex_eq_one.mp h1
    have hxD : x ∈ D := (Subgroup.mem_inf.mp (hVD hx)).2
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp hgD x).1 hxD) (D.inv_mem hxD)
  · have hgP : g ∈ normalizer ((V ⊓ D : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyV, hyD⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgV y).1 hyV,
          (Subgroup.mem_normalizer_iff.mp hgD y).1 hyD⟩
      · rintro ⟨hyV, hyD⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgV y).2 hyV,
          (Subgroup.mem_normalizer_iff.mp hgD y).2 hyD⟩
    exact (Subgroup.mem_inf.mp (comm_mem_of_relIndex_two h2' hgP hgV hx)).2

theorem Sit813.comm_K_V_mem_u1Grp (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∀ x ∈ V, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ u1Grp V H T A K := by
  obtain ⟨-, -, h4⟩ := h.eight_fourteen hin
  have h2 : (v1Grp V H T A K).relIndex V = 2 := h.relIndex_v1Grp h4
  have hcomm : ∀ g, g ∈ normalizer (V : Set G) → g ∈ normalizer (u1Grp V H T A K : Set G) →
      ∀ x ∈ V, g * x * g⁻¹ * x⁻¹ ∈ u1Grp V H T A K := fun g hgV hgD x hx =>
    comm_mem_of_relIndex_two_of_le Sit813.v1Grp_le_V Sit813.v1Grp_le_u1Grp h2 hgV hgD hx
  have hDA : A ≤ normalizer (u1Grp V H T A K : Set G) := fun a ha =>
    h.sGrp_le_normalizer_u1Grp (Sit813.a_le_sGrp ha)
  have hswap : ∀ u ∈ uGrp V K, ∀ w ∈ uGrp V K, w * u⁻¹ = u⁻¹ * w := fun u hu w hw =>
    h.fiveData.u_comm w hw u⁻¹ ((uGrp V K).inv_mem hu)
  intro x hx k hk
  have hxU : x ∈ uGrp V K := Sit813.V_le_uGrp hx
  have key := Five.five_conjugates_mod h.fiveData (Z := u1Grp V H T A K)
    Sit813.k_le_normalizer_u1Grp hDA hx
    (fun k hk => by
      rw [← hswap x hxU _ (mem_conjClosure (Subgroup.mem_inf.mp hk).1 hx)]
      exact hcomm k (Subgroup.mem_inf.mp hk).2
        (Sit813.k_le_normalizer_u1Grp (Subgroup.mem_inf.mp hk).1) x hx)
    (fun a ha => by
      rw [← hswap x hxU _ ((Subgroup.mem_normalizer_iff.mp (h.fiveData.u_normA ha) x).1 hxU)]
      exact hcomm a (h.a_le_normalizer_V ha) (hDA ha) x hx) k hk
  rwa [← hswap x hxU _ (mem_conjClosure hk hx)] at key

theorem Sit813.eight_fifteen (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : uGrp V K = u1Grp V H T A K ⊔ V := by
  have hmod := h.comm_K_V_mem_u1Grp hin
  refine le_antisymm ?_ (sup_le Sit813.u1Grp_le_uGrp Sit813.V_le_uGrp)
  refine conjClosure_le fun k hk x hx => ?_
  have hmem : k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
  rw [hmem]
  exact Subgroup.mul_mem_sup (hmod x hx k hk) hx

end CFSG.LocalAnalysis.WeakClosure81

end
