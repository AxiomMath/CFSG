module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Vn_isElemAbelian (hS : Sit H M S) (δ : Geo H M) : IsElemAbelian 2 (Vn δ) :=
  S34.isElemAbelian_Vn' hS.glob δ

theorem Zv_central (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Zv δ ≤ centerOf (stab δ) := hS.glob.central δ hδ

omit [Finite G] in
theorem Vn_normal (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Vn δ : Set G) :=
  stab_le_normalizer_Vn δ

theorem Zv_le_Vn_S5 (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) : Zv δ ≤ Vn δ :=
  S34.Zv_le_Vn hS.glob hδ

theorem Vn_le_Qv_self (hS : Sit H M S) (δ : Geo H M) : Vn δ ≤ Qv δ :=
  S34.pairVn_le_Qv hS.glob δ

theorem comm_Vn_Qv (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ⁅Vn δ, Qv δ⁆ = Zv δ := by
  refine le_antisymm (S34.comm_Vn_Qv_le hS.glob hδ) ?_
  obtain ⟨l, hl⟩ := exists_adj δ
  have hl' : l ∈ nbrs δ := hl
  obtain ⟨x, hxδ, hxl⟩ := IsConcreteLE.not_le_iff_exists.mp (Q_not_le hS hδ hl')
  have hx : x ∈ stab l ⊓ stab δ := ⟨Qv_le_stab hS hl' hxδ, pCoreOf_le 2 _ hxδ⟩
  intro z hz
  obtain ⟨y, hy, hyz⟩ := (EmptyFaithful.Stellmacher.OrdinaryProofs.comm_Zv_surj
    hS.glob.amalg hδ hl' (hS.glob.central δ hδ) hx hxl).2 z hz
  have hmem := Subgroup.commutator_mem_commutator hxδ (Zv_le_Vn hl' hy)
  rw [Subgroup.commutator_comm, commutatorElement_def] at hmem
  rwa [show x * y * x⁻¹ * y⁻¹ = z by simpa [mul_assoc] using hyz] at hmem

omit [Finite G] in
theorem exists_nbr_dist_succ {δ ρ : Geo H M} {d : ℕ} (h : dist δ ρ = d + 1) :
    ∃ μ ∈ nbrs δ, dist μ ρ = d := by
  obtain ⟨μ, hμ, hd⟩ := exists_adj_dist_eq (G₀ := H ⊔ M) rfl (α := ρ) (δ := δ) (d := d)
    (by rw [CosetGeom.dist_comm]; exact h)
  exact ⟨μ, hμ, by rw [CosetGeom.dist_comm]; exact hd⟩

theorem Vn_le_Qv_dist (_hS : Sit H M S) {δ ρ : Geo H M} (h : dist δ ρ + 2 ≤ bMin H M) :
    Vn δ ≤ Qv ρ :=
  S34.Vn_le_Qv_of_dist_succ_lt (by omega)

theorem Vn_le_stab_dist (hS : Sit H M S) {δ ρ : Geo H M} (h : dist δ ρ + 1 ≤ bMin H M) :
    Vn δ ≤ stab ρ := by
  refine iSup₂_le fun μ hμ => Zv_le_stab_of_dist_le_bMin hS.glob.amalg ?_
  have := dist_le_dist_nbr hμ ρ
  have e : dist ρ δ = dist δ ρ := CosetGeom.dist_comm _ _
  have e' : dist μ ρ = dist ρ μ := CosetGeom.dist_comm _ _
  omega

theorem Vn_commute_dist (hS : Sit H M S) {δ ρ : Geo H M} (h : dist δ ρ + 3 ≤ bMin H M) :
    ∀ a ∈ Vn δ, ∀ b ∈ Vn ρ, a * b = b * a :=
  S34.Vn_commute hS.glob.amalg (by omega)

omit [Finite G] in
theorem Zv_le_Qv_dist {l' ρ : Geo H M} (h : dist l' ρ < bMin H M) : Zv l' ≤ Qv ρ :=
  Zv_le_Qv_of_dist_lt_bMin h

theorem Zv_le_stab_dist (hS : Sit H M S) {l' ρ : Geo H M} (h : dist l' ρ ≤ bMin H M) :
    Zv l' ≤ stab ρ :=
  Zv_le_stab_of_dist_le_bMin hS.glob.amalg h

theorem Zv_le_stab_dist_S5 (hS : Sit H M S) {δ ρ : Geo H M} (hδ : vtype δ = false)
    (h : dist δ ρ ≤ bMin H M + 1) : Zv δ ≤ stab ρ := by
  rcases Nat.eq_zero_or_pos (dist δ ρ) with h0 | hpos
  · rw [dist_eq_zero_iff rfl] at h0
    subst h0
    exact (Zv_le_Qv hS.glob.amalg δ).trans (pCoreOf_le 2 _)
  · obtain ⟨μ, hμ, hd⟩ := exists_nbr_dist_succ (δ := δ) (ρ := ρ) (d := dist δ ρ - 1) (by omega)
    exact (Zv_le_Zv_of_nbr hS hδ hμ).trans (Zv_le_stab_dist hS (by omega))

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin
