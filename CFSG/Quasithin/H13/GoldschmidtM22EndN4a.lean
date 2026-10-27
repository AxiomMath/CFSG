module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem exists_gen_Z (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧
      quasithinOmegaOneCenter T = Subgroup.zpowers z := by
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : quasithinOmegaOneCenter T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this] at hZ
    simp at hZ
  have hle : Subgroup.zpowers z ≤ quasithinOmegaOneCenter T := Subgroup.zpowers_le.mpr hzZ
  have hdvd : orderOf z ∣ 2 := by
    have h1 : orderOf (⟨z, hzZ⟩ : ↥(quasithinOmegaOneCenter T)) ∣
        Nat.card ↥(quasithinOmegaOneCenter T) := orderOf_dvd_natCard _
    rw [hZ, Subgroup.orderOf_mk] at h1
    exact h1
  have hne : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have h2 : orderOf z = 2 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne
  refine ⟨z, hzZ, hz1, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [Nat.card_zpowers, h2, hZ]

omit [Finite G] in
theorem HH_eq_centralizer_of_gen {z : G} (hz : quasithinOmegaOneCenter T = Subgroup.zpowers z) :
    HH T = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx z (hz ▸ Subgroup.mem_zpowers z)
  · intro hx y hy
    rw [hz] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have := hx z rfl
    exact ((Commute.zpow_left (show Commute z x from this) k)).eq

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in
theorem normalizer_eq_sup (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) :
    Subgroup.normalizer (V : Set G) = L ⊔ T := by
  refine le_antisymm ?_ (sup_le h.toHyp611.L_le_normalizer h.toHyp611.T_le_normalizer)
  intro n hn
  obtain ⟨z, hzZ, hz1, hZz⟩ := exists_gen_Z hZ
  have hzV : z ∈ V := Z_le_V h hZ hzZ
  have hnM : n ∈ M := (h621 G T M L V h).2 hn
  have hnzV : n * z * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hn z).mp hzV
  have hnz1 : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg (fun y => n⁻¹ * y * n) h1
    simpa [mul_assoc] using this
  obtain ⟨l, hlL, hl⟩ := h.natural.exists_conj_eq hzV hnzV hz1 hnz1
  have hcomm : (l⁻¹ * n) * z = z * (l⁻¹ * n) := by
    have e : l⁻¹ * (n * z * n⁻¹) * l = z := by rw [← hl]; group
    calc (l⁻¹ * n) * z = (l⁻¹ * (n * z * n⁻¹) * l) * (l⁻¹ * n) := by group
      _ = z * (l⁻¹ * n) := by rw [e]
  have ht : l⁻¹ * n ∈ HH T := by
    rw [HH_eq_centralizer_of_gen hZz, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have htM : l⁻¹ * n ∈ M := M.mul_mem (M.inv_mem (h.L_le hlL)) hnM
  have htT : l⁻¹ * n ∈ T := by
    have : l⁻¹ * n ∈ HH T ⊓ M := ⟨ht, htM⟩
    rwa [P.HH_inf_M_eq_T h hZ h629 h6210 h6212] at this
  have e : n = l * (l⁻¹ * n) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hlL htT

include P h in
theorem centralizer_le_T (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) :
    Subgroup.centralizer (V : Set G) ≤ T := by
  intro x hx
  have hxH : x ∈ HH T := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact Subgroup.mem_centralizer_iff.mp hx z (Z_le_V h hZ hz)
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hx
  have : x ∈ HH T ⊓ M := ⟨hxH, (h621 G T M L V h).2 hxN⟩
  rwa [P.HH_inf_M_eq_T h hZ h629 h6210 h6212] at this

end PsiData

end CFSG.Quasithin.H13.GM22
