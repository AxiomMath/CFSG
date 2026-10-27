module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem dih_transport (F : FanTree Γ G) {v p : V}
    (hD : ∀ g ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G p,
      g * g ∈ nbrStab Γ G v) (k : G) :
    ∀ g ∈ MulAction.stabilizer G (k • v) ⊓ MulAction.stabilizer G (k • p),
      g * g ∈ nbrStab Γ G (k • v) := by
  intro g hg
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hmem : k⁻¹ * g * k ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G p := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hg1,
        inv_smul_smul]
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hg2,
        inv_smul_smul]
  have h1 := F.conj_mem_nbrStab_smul k (hD _ hmem)
  have e : k * ((k⁻¹ * g * k) * (k⁻¹ * g * k)) * k⁻¹ = g * g := by group
  rwa [e] at h1

theorem cen_edgeStab_five (ℓ : Line Γ) {i : ℤ} (h5 : valence Γ (ℓ.vert i) = 5)
    (hsq : ∀ g ∈ MulAction.stabilizer G (ℓ.vert i) ⊓ MulAction.stabilizer G (ℓ.vert (i + 1)),
      g * g ∈ nbrStab Γ G (ℓ.vert i)) {u : G} (hu : u ∈ Cen (ℓ.edgeCirc (G := G) i)) :
    u ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := by
  rw [ℓ.edgeCirc_of_five h5] at hu
  obtain ⟨⟨hu1, -⟩, hu2⟩ := hu
  exact ⟨hu1, fun h hh => hu2 h ⟨hh, hsq h hh⟩⟩

theorem cen_edgeStab_ne_five (ℓ : Line Γ) {i : ℤ} (h5 : valence Γ (ℓ.vert i) ≠ 5)
    (hsq : ∀ g ∈ MulAction.stabilizer G (ℓ.vert (i + 1)) ⊓ MulAction.stabilizer G (ℓ.vert i),
      g * g ∈ nbrStab Γ G (ℓ.vert (i + 1))) {u : G} (hu : u ∈ Cen (ℓ.edgeCirc (G := G) i)) :
    u ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := by
  rw [ℓ.edgeCirc_of_ne_five h5] at hu
  obtain ⟨⟨hu1, -⟩, hu2⟩ := hu
  refine ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hu1).2, (Subgroup.mem_inf.1 hu1).1⟩,
    fun h hh => hu2 h ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hh).2, (Subgroup.mem_inf.1 hh).1⟩,
      hsq h (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hh).2, (Subgroup.mem_inf.1 hh).1⟩)⟩⟩

theorem cen_mul {H : Subgroup G} {x y : G} (hx : x ∈ Cen (H : Set G)) (hy : y ∈ Cen (H : Set G)) :
    x * y ∈ Cen (H : Set G) := by
  refine ⟨mul_mem hx.1 hy.1, fun h hh => ?_⟩
  calc h * (x * y) = (h * x) * y := by rw [mul_assoc]
    _ = (x * h) * y := by rw [hx.2 h hh]
    _ = x * (h * y) := by rw [mul_assoc]
    _ = x * (y * h) := by rw [hy.2 h hh]
    _ = (x * y) * h := by rw [mul_assoc]

theorem fcomm_inv (a b : G) : (fcomm a b)⁻¹ = fcomm b a := by
  simp only [fcomm]
  group

theorem prod3_ne_one (F : FanTree Γ G) {z : G} {α o : V} (C : LblCtx Γ z α o) {p q s : V}
    (hp : Γ.Adj o p) (hq : Γ.Adj o q) (hs : Γ.Adj o s) (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) : Lb z α p * Lb z α q * Lb z α s ≠ 1 := by
  classical
  obtain ⟨b, c, hb, hc, hnd⟩ := exists_five_nbrs C.v5 hpq hps hqs
  have hprod := C.prod5 [p, q, s, b, c] hnd rfl (by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hprod
  intro h3
  have hbc : b ≠ c := by
    have := List.nodup_cons.1 hnd
    simp [List.nodup_cons] at this
    tauto
  have h2 : Lb z α b * Lb z α c = 1 := by
    have e : Lb z α p * (Lb z α q * (Lb z α s * (Lb z α b * Lb z α c))) =
        (Lb z α p * Lb z α q * Lb z α s) * (Lb z α b * Lb z α c) := by
      simp only [mul_assoc]
    rw [e, h3, one_mul] at hprod
    exact hprod
  have h4 := eq_inv_of_mul_eq_one_left h2
  rw [inv_eq_of_mul_eq_one_right (C.sq F hc)] at h4
  exact C.ne b c hb hc hbc h4

end P61

end CFSG.Quasithin.Fan86
