module

public import CFSG.Monster.GMS.S365Basic
public import CFSG.Sporadic.Co1.Module.Pairs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Group

variable {G : Type*} [Group G]

theorem comm_mul_iff {g t c : G} (hgc : g * c = c * g) :
    g * t = t * g ↔ g * (t * c) = t * c * g := by
  constructor
  · intro h
    calc g * (t * c) = g * t * c := (mul_assoc _ _ _).symm
      _ = t * g * c := by rw [h]
      _ = t * (g * c) := mul_assoc _ _ _
      _ = t * (c * g) := by rw [hgc]
      _ = t * c * g := (mul_assoc _ _ _).symm
  · intro h
    have h1 : g * t * c = t * g * c := by
      calc g * t * c = g * (t * c) := mul_assoc _ _ _
        _ = t * c * g := h
        _ = t * (c * g) := mul_assoc _ _ _
        _ = t * (g * c) := by rw [hgc]
        _ = t * g * c := (mul_assoc _ _ _).symm
    exact mul_right_cancel h1

theorem centralizer_inf_inf_eq_of_mem_cosetSet {x y t w : G} (hw : w ∈ cosetSet x y t) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨c, hc, rfl⟩ := mem_cosetSet_iff.1 hw
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, ht⟩
    have hgc : g * c = c * g := by
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · exact hx
      · exact hy
      · calc g * (x * y) = g * x * y := (mul_assoc _ _ _).symm
          _ = x * g * y := by rw [hx]
          _ = x * (g * y) := mul_assoc _ _ _
          _ = x * (y * g) := by rw [hy]
          _ = x * y * g := (mul_assoc _ _ _).symm
    exact ⟨⟨hx, hy⟩, (comm_mul_iff hgc).1 ht⟩
  · rintro ⟨⟨hx, hy⟩, ht⟩
    have hgc : g * c = c * g := by
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · exact hx
      · exact hy
      · calc g * (x * y) = g * x * y := (mul_assoc _ _ _).symm
          _ = x * g * y := by rw [hx]
          _ = x * (g * y) := mul_assoc _ _ _
          _ = x * (y * g) := by rw [hy]
          _ = x * y * g := (mul_assoc _ _ _).symm
    exact ⟨⟨hx, hy⟩, (comm_mul_iff hgc).2 ht⟩

theorem card_eq_card_inf_mul_ncard_conj (Γ : Subgroup G) (x : G) :
    Nat.card ↥Γ = Nat.card ↥(Γ ⊓ Subgroup.centralizer ({x} : Set G)) *
      {z : G | ∃ g ∈ Γ, g * x * g⁻¹ = z}.ncard := by
  classical
  let _ : MulAction ↥Γ G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp Γ.subtype)
  have hact : ∀ (g : ↥Γ) (z : G), g • z = (g : G) * z * (g : G)⁻¹ := fun g z => rfl
  have h : Nat.card (MulAction.stabilizer ↥Γ x) * (MulAction.orbit ↥Γ x).ncard =
      Nat.card ↥Γ := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  have horb : MulAction.orbit ↥Γ x = {z : G | ∃ g ∈ Γ, g * x * g⁻¹ = z} := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hstab : Nat.card (MulAction.stabilizer ↥Γ x) =
      Nat.card ↥(Γ ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨(g.1 : G), Subgroup.mem_inf.2 ⟨g.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩⟩
        invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · have := g.2
      rw [MulAction.mem_stabilizer_iff, hact] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · rw [MulAction.mem_stabilizer_iff, hact]
      have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
  rw [← hstab, ← horb]
  exact h.symm

end Group

section Co1

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs

theorem card_inf_stab_pair
    {a b : Fin 24 → ZMod 2} (ha : a ∈ co1Orbit 0) (hb : b ∈ co1Orbit 0)
    (hab : a + b ∈ co1Orbit 0) :
    Nat.card ↥(co1Stab a ⊓ co1Stab b) = 9196830720 := by
  rw [co1Orbit_zero] at ha hb hab
  obtain ⟨g, hg⟩ := ha
  have hg' : g • v₂ = a := hg
  subst hg'
  have hb' : g⁻¹ • b ∈ cls 3 := by
    refine ⟨orbit_smul_mem _ hb, ?_⟩
    have : v₂ + g⁻¹ • b = g⁻¹ • (g • v₂ + b) := by rw [smul_add, inv_smul_smul]
    rw [this]
    exact orbit_smul_mem _ hab
  have h1 := cls_card_stab (j := 3) (by norm_num) hb'
  rw [cls_ncard (by norm_num)] at h1
  have h3 : dat.subSizes[3]! = 4600 := by decide
  rw [h3] at h1
  have hc : Nat.card ↥(MulAction.stabilizer Co1 v₂ ⊓
      MulAction.stabilizer Co1 (g⁻¹ • b)) = 9196830720 := by omega
  rw [co1Stab_eq, co1Stab_eq]
  have h2 := card_inf_stabilizer_smul₂ g v₂ (g⁻¹ • b)
  rw [smul_inv_smul] at h2
  rw [h2]
  exact hc

end Co1

end S365

end CFSG.Monster.GMS
