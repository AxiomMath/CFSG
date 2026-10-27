module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Cs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At16A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' : Geo H M}

theorem comm_Qv_eq_one (hS : Sit H M S) (hp : S34.PD β α') (hZβ : Zv β ⊓ Vn α' = ⊥) :
    ∀ a ∈ Vn β, ∀ y ∈ Vn α' ⊓ Qv β, ⁅a, y⁆ = 1 := by
  intro a ha y hy
  have h2 : ⁅a, y⁆ ∈ ⁅Vn β, Qv β⁆ := Subgroup.commutator_mem_commutator ha hy.2
  rw [comm_Vn_Qv hS hp.vδ] at h2
  have h3 : ⁅a, y⁆ ∈ Vn α' := (PD_comm_le hS hp (Subgroup.commutator_mem_commutator ha hy.1)).2
  have : ⁅a, y⁆ ∈ Zv β ⊓ Vn α' := ⟨h2, h3⟩
  rw [hZβ] at this
  exact Subgroup.mem_bot.mp this

theorem comm_eq_of_theta_eq (hS : Sit H M S) (hp : S34.PD β α') (hZβ : Zv β ⊓ Vn α' = ⊥)
    (cb : Chart2 β) {a u w : G} (ha : a ∈ Vn β) (hu : u ∈ Vn α') (hw : w ∈ Vn α')
    (hθ : cb.θ ⟨u, (PD_Vn_le_stab hS hp).2 hu⟩ = cb.θ ⟨w, (PD_Vn_le_stab hS hp).2 hw⟩) :
    a * u * a⁻¹ * u⁻¹ = a * w * a⁻¹ * w⁻¹ := by
  have hle := (PD_Vn_le_stab hS hp).2
  have hy : w⁻¹ * u ∈ Vn α' ⊓ Qv β := by
    refine ⟨(Vn α').mul_mem ((Vn α').inv_mem hw) hu, ?_⟩
    have hys : w⁻¹ * u ∈ stab β := (stab β).mul_mem ((stab β).inv_mem (hle hw)) (hle hu)
    refine (cb.ker_iff hS hp.vδ ⟨_, hys⟩).mp ?_
    have e : (⟨w⁻¹ * u, hys⟩ : ↥(stab β)) = ⟨w, hle hw⟩⁻¹ * ⟨u, hle hu⟩ := rfl
    rw [e, map_mul, map_inv, hθ, inv_mul_cancel]
  have hc := comm_Qv_eq_one hS hp hZβ a ha _ hy
  have hc' := commutatorElement_eq_one_iff_mul_comm.mp hc
  have hy2 : (w⁻¹ * u) * a⁻¹ * (w⁻¹ * u)⁻¹ = a⁻¹ := by
    calc _ = a⁻¹ * (a * (w⁻¹ * u)) * a⁻¹ * (w⁻¹ * u)⁻¹ := by group
      _ = a⁻¹ * ((w⁻¹ * u) * a) * a⁻¹ * (w⁻¹ * u)⁻¹ := by rw [hc']
      _ = a⁻¹ := by group
  calc a * u * a⁻¹ * u⁻¹ = a * w * ((w⁻¹ * u) * a⁻¹ * (w⁻¹ * u)⁻¹) * w⁻¹ := by group
    _ = a * w * a⁻¹ * w⁻¹ := by rw [hy2]

theorem card_cI_of_swap (hS : Sit H M S) (hRk : S35.II.RkZvEq H M) (hp : S34.PD β α')
    (hZβ : Zv β ⊓ Vn α' = ⊥) (cb : Chart2 β) {u : G} (hu : u ∈ Vn α')
    (hsw : (cb.θ ⟨u, (PD_Vn_le_stab hS hp).2 hu⟩).IsSwap) :
    cI hS β ((PD_Vn_le_stab hS hp).2 hu) ≤ Vn α' ∧
      Nat.card (cI hS β ((PD_Vn_le_stab hS hp).2 hu)) = 2 := by
  have hle := (PD_Vn_le_stab hS hp).2
  have hq := hle hu
  have hT : cI hS β hq ≤ Vn α' := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_cI.mp hx
    have h1 : ⁅b, u⁆ ∈ ⁅Vn β, Vn α'⁆ := Subgroup.commutator_mem_commutator hb hu
    have h2 := (PD_comm_le hS hp h1).2
    have : u * b * u⁻¹ * b⁻¹ = ⁅b, u⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [this]
    exact (Vn α').inv_mem h2
  refine ⟨hT, ?_⟩
  have h1 := relIndex_cI_Zv hS hp.vδ hq
  rw [secIdx_Zv_eq_idx hRk cb hp.vδ hq, (idx_orth_eq_two_iff _).mpr hsw] at h1
  have hbot : cI hS β hq ⊓ Zv β = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hT).trans (by rw [inf_comm]; exact hZβ.le))
  rw [hbot, Subgroup.relIndex_bot_left] at h1
  exact h1

theorem card_R_le_four (hS : Sit H M S) (hRk : S35.II.RkZvEq H M) (hp : S34.PD β α')
    (hZβ : Zv β ⊓ Vn α' = ⊥) (cb : Chart2 β) {s t : Perm (Fin 5)} (hs2 : s * s = 1)
    (ht2 : t * t = 1) (hc : s * t = t * s) (hsw : s.IsSwap) (htw : t.IsSwap)
    (hbar : cb.bar (Vn α') = Subgroup.closure ({s, t} : Set (Perm (Fin 5)))) :
    Nat.card ↥⁅Vn β, Vn α'⁆ ≤ 4 := by
  have hle := (PD_Vn_le_stab hS hp).2
  have hle2 := (PD_Vn_le_stab hS hp).1
  have hVα : IsMulCommutative (Vn α') := (Vn_isElemAbelian hS α').1
  have hmem : ∀ x ∈ ({s, t} : Set (Perm (Fin 5))), x ∈ cb.bar (Vn α') := fun x hx =>
    hbar ▸ Subgroup.subset_closure hx
  obtain ⟨U1, hU1, hθ1⟩ := cb.mem_bar_iff.mp (hmem s (by simp))
  obtain ⟨U2, hU2, hθ2⟩ := cb.mem_bar_iff.mp (hmem t (by simp))
  have e1 : (⟨(U1 : G), hle hU1⟩ : ↥(stab β)) = U1 := rfl
  have e2 : (⟨(U2 : G), hle hU2⟩ : ↥(stab β)) = U2 := rfl
  have hsw1 : (cb.θ ⟨(U1 : G), hle hU1⟩).IsSwap := by rw [e1, hθ1]; exact hsw
  have hsw2 : (cb.θ ⟨(U2 : G), hle hU2⟩).IsSwap := by rw [e2, hθ2]; exact htw
  obtain ⟨hT1le, hT1c⟩ := card_cI_of_swap hS hRk hp hZβ cb hU1 hsw1
  obtain ⟨hT2le, hT2c⟩ := card_cI_of_swap hS hRk hp hZβ cb hU2 hsw2
  set T1 := cI hS β (hle hU1) with hT1
  set T2 := cI hS β (hle hU2) with hT2
  have hΦ1 : ∀ a ∈ Vn β, a * (U1 : G) * a⁻¹ * (U1 : G)⁻¹ ∈ T1 := fun a ha => by
    have := T1.inv_mem (comm_mem_cI hS β (hle hU1) ha)
    convert this using 1
    group
  have hΦ2 : ∀ a ∈ Vn β, a * (U2 : G) * a⁻¹ * (U2 : G)⁻¹ ∈ T2 := fun a ha => by
    have := T2.inv_mem (comm_mem_cI hS β (hle hU2) ha)
    convert this using 1
    group
  have key : ∀ a ∈ Vn β, ∀ u ∈ Vn α', a * u * a⁻¹ * u⁻¹ ∈ T1 ⊔ T2 := by
    intro a ha u hu
    have hus : u ∈ stab β := hle hu
    have hθu : cb.θ ⟨u, hus⟩ ∈ Subgroup.closure ({s, t} : Set (Perm (Fin 5))) :=
      hbar ▸ cb.mem_bar_of_mem hu hus
    have hk := (mem_closure_pair hs2 ht2 hc _).mp hθu
    simp only [kl, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h
    · rw [comm_eq_of_theta_eq hS hp hZβ cb ha hu (Vn α').one_mem
        (by rw [h]; exact (map_one cb.θ).symm)]
      simp
    · rw [comm_eq_of_theta_eq hS hp hZβ cb ha hu hU1 (by rw [h, ← hθ1])]
      exact Subgroup.mem_sup_left (hΦ1 a ha)
    · rw [comm_eq_of_theta_eq hS hp hZβ cb ha hu hU2 (by rw [h, ← hθ2])]
      exact Subgroup.mem_sup_right (hΦ2 a ha)
    · have hw : (U1 : G) * (U2 : G) ∈ Vn α' := (Vn α').mul_mem hU1 hU2
      have e12 : (⟨(U1 : G) * (U2 : G), hle hw⟩ : ↥(stab β)) = U1 * U2 := rfl
      rw [comm_eq_of_theta_eq hS hp hZβ cb ha hu hw (by
        rw [h, e12, map_mul, hθ1, hθ2])]
      have hn : a ∈ Subgroup.normalizer (Vn α' : Set G) := Vn_normal α' (hle2 ha)
      have hm := congrArg Subtype.val (map_mul (S34.yCommHom hVα hn) ⟨(U1 : G), hU1⟩
        ⟨(U2 : G), hU2⟩)
      simp only [S34.coe_yCommHom] at hm
      have hm' : a * ((U1 : G) * (U2 : G)) * a⁻¹ * ((U1 : G) * (U2 : G))⁻¹ =
          (a * (U1 : G) * a⁻¹ * (U1 : G)⁻¹) * (a * (U2 : G) * a⁻¹ * (U2 : G)⁻¹) := hm
      rw [hm']
      exact (T1 ⊔ T2).mul_mem (Subgroup.mem_sup_left (hΦ1 a ha))
        (Subgroup.mem_sup_right (hΦ2 a ha))
  have hR : ⁅Vn β, Vn α'⁆ ≤ T1 ⊔ T2 := by
    rw [Subgroup.commutator_le]
    intro a ha u hu
    rw [commutatorElement_def]
    exact key a ha u hu
  refine (Subgroup.card_le_of_le hR).trans ?_
  have h1 := relIndex_sup_eq_of_comm hVα hT1le hT2le
  have h2 := relIndex_le_card' T2 T1
  have h3 := Subgroup.relIndex_mul_card (H := T2) (K := T1 ⊔ T2)
  rw [inf_eq_left.mpr le_sup_right, h1] at h3
  rw [hT1c] at h2
  rw [← h3, hT2c]
  omega

theorem inf_comm_eq_bot (hS : Sit H M S) (hRk : S35.II.RkZvEq H M) (hp : S34.PD β α')
    (ca : Chart2 α') {v : G} (hv : v ∈ Vn β) (hvs : v ∈ stab α')
    (h4 : idx orth (ca.θ ⟨v, hvs⟩) = 4) (hR : Nat.card ↥⁅Vn β, Vn α'⁆ ≤ 4) :
    Zv α' ⊓ ⁅Vn β, Vn α'⁆ = ⊥ := by
  set X := cI hS α' hvs with hX
  have hXR : X ≤ ⁅Vn β, Vn α'⁆ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_cI.mp hx
    exact Subgroup.commutator_mem_commutator hv ha
  have h1 := relIndex_cI_Zv hS hp.vδ' hvs
  rw [secIdx_Zv_eq_idx hRk ca hp.vδ' hvs, h4] at h1
  have h3 := Subgroup.relIndex_mul_card (H := X ⊓ Zv α') (K := X)
  rw [inf_eq_left.mpr (inf_le_left : X ⊓ Zv α' ≤ X)] at h3
  have hXc : Nat.card X ≤ 4 := (Subgroup.card_le_of_le hXR).trans hR
  have hpos : 0 < Nat.card ↥(X ⊓ Zv α') := Nat.card_pos
  rw [h1] at h3
  have hbot : X ⊓ Zv α' = ⊥ := by
    rw [← Subgroup.card_eq_one]
    omega
  have hXeq : X = ⁅Vn β, Vn α'⁆ := by
    refine Subgroup.eq_of_le_of_card_ge hXR ?_
    omega
  rw [← hXeq, inf_comm]
  exact hbot

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
