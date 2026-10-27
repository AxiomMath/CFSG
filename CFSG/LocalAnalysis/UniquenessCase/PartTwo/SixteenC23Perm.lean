module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c23_exists_fixed_conj {p : ℕ} [Fact p.Prime] {T : Subgroup G} (hT : IsPGroup p T)
    {X : Set G} (hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hp : ¬ p ∣ Nat.card X) :
    ∃ x ∈ X, ∀ t ∈ T, t * x * t⁻¹ = x := by
  let _ : MulAction T X :=
    { smul := fun t x => ⟨(t : G) * x * (t : G)⁻¹, hX t t.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : T) : G) * x * ((1 : T) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  obtain ⟨x, hx⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card X hp
  exact ⟨x, x.2, fun t ht => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx ⟨t, ht⟩)⟩

theorem c23_card_eq_ncard_orbit_mul (H : Subgroup G) (d : G) :
    Nat.card ↥H = Set.ncard {y : G | ∃ h ∈ H, y = h * d * h⁻¹} *
      Nat.card ↥(H ⊓ Subgroup.centralizer ({d} : Set G)) := by
  let _ : MulAction ↥H G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : ↥H) (g : G), h • g = (h : G) * g * (h : G)⁻¹ := fun h g => by
    show ConjAct.toConjAct (h : G) • g = _
    rw [ConjAct.smul_def]
    simp
  have hidx := MulAction.index_stabilizer ↥H d
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥H d)
  have hstab : (MulAction.stabilizer ↥H d).map H.subtype =
      H ⊓ Subgroup.centralizer ({d} : Set G) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := MulAction.mem_stabilizer_iff.1 hh
      rw [hsmul] at h1
      show (h : G) * d = d * h
      calc (h : G) * d = ((h : G) * d * (h : G)⁻¹) * h := by group
        _ = d * h := by rw [h1]
    · rintro ⟨hgH, hgC⟩
      refine ⟨⟨g, hgH⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
      rw [hsmul]
      have := Subgroup.mem_centralizer_singleton_iff.1 hgC
      show g * d * g⁻¹ = d
      rw [this]
      group
  have horb : MulAction.orbit ↥H d = {y : G | ∃ h ∈ H, y = h * d * h⁻¹} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h d)⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, (hsmul ⟨h, hh⟩ d)⟩
  rw [← horb, ← hidx, ← hcard, ← Subgroup.card_map_of_injective H.subtype_injective, hstab]
  ring

theorem c23_exists_calM_ne_conj {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) {z m : G}
    (hm : m ∈ M) (hz : ¬ UniqueMax M (M ⊓ centralizer ({z} : Set G))) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧
      M ⊓ centralizer ({m * z * m⁻¹} : Set G) ≤ N ∧ N ≠ M := by
  have hMmem : M ∈ calMOf (M ⊓ centralizer ({z} : Set G)) := ⟨hM, inf_le_left⟩
  have hex : ∃ N₀ ∈ calMOf (M ⊓ centralizer ({z} : Set G)), N₀ ≠ M := by
    by_contra h
    have hsingle : calMOf (M ⊓ centralizer ({z} : Set G)) = {M} := by
      rw [Set.eq_singleton_iff_unique_mem]
      exact ⟨hMmem, fun b hb => by
        by_contra hbM
        exact h ⟨b, hb, hbM⟩⟩
    exact hz hsingle
  obtain ⟨N₀, hN₀mem, hN₀ne⟩ := hex
  let N : Subgroup G := N₀.map (MulAut.conj m).toMonoidHom
  refine ⟨N, ?_, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hN₀mem.1 (MulAut.conj m)
  · intro x hx
    obtain ⟨hxM, hxC⟩ := hx
    have hxc : x * (m * z * m⁻¹) = (m * z * m⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    let y : G := m⁻¹ * x * m
    have hyM : y ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
    have hyz : y * z * y⁻¹ = z := by
      show (m⁻¹ * x * m) * z * (m⁻¹ * x * m)⁻¹ = z
      calc (m⁻¹ * x * m) * z * (m⁻¹ * x * m)⁻¹
          = m⁻¹ * (x * (m * z * m⁻¹) * x⁻¹) * m := by group
        _ = m⁻¹ * (m * z * m⁻¹) * m := by rw [hxc]; group
        _ = z := by group
    have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]
    have hyN₀ : y ∈ N₀ := hN₀mem.2 ⟨hyM, hyC⟩
    exact Subgroup.mem_map.mpr ⟨y, hyN₀, by
      show (MulAut.conj m) y = x
      rw [MulAut.conj_apply]
      show m * (m⁻¹ * x * m) * m⁻¹ = x
      group⟩
  · intro hNM
    apply hN₀ne
    apply le_antisymm
    · intro x hx
      have hxN : (MulAut.conj m) x ∈ N := Subgroup.mem_map_of_mem _ hx
      rw [hNM, MulAut.conj_apply] at hxN
      have hxM : m⁻¹ * (m * x * m⁻¹) * m ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem hm) hxN) hm
      rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at hxM
    · intro x hx
      have hxN : (MulAut.conj m) x ∈ N := by
        rw [hNM, MulAut.conj_apply]
        exact M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxN
      have hyx' : y = x := (MulAut.conj m).injective hyx
      rwa [hyx'] at hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
