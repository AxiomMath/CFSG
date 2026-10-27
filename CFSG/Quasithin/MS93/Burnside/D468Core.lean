module

public import CFSG.Quasithin.MS93.S46R468GR

public section

namespace CFSG.Yardstones.M71b2fd3d34b9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
  CFSG.Quasithin.MS93.S46R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideD468_commutator_mem_qv (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) {s t : (puAmalgam c.pu.le).Universal}
    (hs : s ∈ Qv (puAmalgam c.pu.le) β) (ht : t ∈ Qv (puAmalgam c.pu.le) β) :
    ⁅s, t⁆ ∈ Qv (puAmalgam c.pu.le) α := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hZc : ∀ e ∈ ZH (puAmalgam c.pu.le) β, ∀ g ∈ Qv (puAmalgam c.pu.le) β, g * e = e * g :=
    fun e he g hg => Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β he) g hg
  have he : ∀ z ∈ ZM (puAmalgam c.pu.le) α, ∀ g ∈ Qv (puAmalgam c.pu.le) β,
      ⁅z⁻¹, g⁆ ∈ ZH (puAmalgam c.pu.le) β := fun z hz g hg => by
    refine h464' α β hα hαβ ?_
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hz) hg
  have hconj : ∀ z ∈ ZM (puAmalgam c.pu.le) α, ∀ g ∈ Qv (puAmalgam c.pu.le) β,
      g * z * g⁻¹ = z * ⁅z⁻¹, g⁆ := fun z _ g _ => by rw [commutatorElement_def]; group
  have hst : ∀ z ∈ ZM (puAmalgam c.pu.le) α,
      (s * t) * z * (s * t)⁻¹ = (t * s) * z * (t * s)⁻¹ := by
    intro z hz
    have e₁ := he z hz s hs
    have e₂ := he z hz t ht
    have h1 : (s * t) * z * (s * t)⁻¹ = z * ⁅z⁻¹, s⁆ * ⁅z⁻¹, t⁆ := by
      calc (s * t) * z * (s * t)⁻¹ = s * (t * z * t⁻¹) * s⁻¹ := by group
        _ = s * (z * ⁅z⁻¹, t⁆) * s⁻¹ := by rw [hconj z hz t ht]
        _ = (s * z * s⁻¹) * (s * ⁅z⁻¹, t⁆ * s⁻¹) := by group
        _ = (z * ⁅z⁻¹, s⁆) * ⁅z⁻¹, t⁆ := by
            rw [hconj z hz s hs, hZc _ e₂ s hs, mul_inv_cancel_right]
        _ = z * ⁅z⁻¹, s⁆ * ⁅z⁻¹, t⁆ := by group
    have h2 : (t * s) * z * (t * s)⁻¹ = z * ⁅z⁻¹, t⁆ * ⁅z⁻¹, s⁆ := by
      calc (t * s) * z * (t * s)⁻¹ = t * (s * z * s⁻¹) * t⁻¹ := by group
        _ = t * (z * ⁅z⁻¹, s⁆) * t⁻¹ := by rw [hconj z hz s hs]
        _ = (t * z * t⁻¹) * (t * ⁅z⁻¹, s⁆ * t⁻¹) := by group
        _ = (z * ⁅z⁻¹, t⁆) * ⁅z⁻¹, s⁆ := by
            rw [hconj z hz t ht, hZc _ e₁ t ht, mul_inv_cancel_right]
        _ = z * ⁅z⁻¹, t⁆ * ⁅z⁻¹, s⁆ := by group
    have h3 : ⁅z⁻¹, s⁆ * ⁅z⁻¹, t⁆ = ⁅z⁻¹, t⁆ * ⁅z⁻¹, s⁆ :=
      hZc _ e₂ _ (zh_le_qv _ β e₁)
    rw [h1, h2, mul_assoc, h3, ← mul_assoc]
  obtain ⟨y, hy, hyβ⟩ := exists_mem_zm_not_mem_zh h465 c hα hαβ
  have hts : t * s ∈ Qv (puAmalgam c.pu.le) β := Subgroup.mul_mem _ ht hs
  have hTαn : Qv (puAmalgam c.pu.le) β ≤
      Subgroup.normalizer (ZM (puAmalgam c.pu.le) α : Set (puAmalgam c.pu.le).Universal) :=
    (qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α)
  have hy' : (t * s)⁻¹ * y * (t * s)⁻¹⁻¹ ∈ ZM (puAmalgam c.pu.le) α :=
    (Subgroup.mem_normalizer_iff.mp (hTαn (Subgroup.inv_mem _ hts)) y).mp hy
  have hcomm : ⁅s, t⁆ * y = y * ⁅s, t⁆ := by
    have h1 := hst _ hy'
    have e : ⁅s, t⁆ * y * ⁅s, t⁆⁻¹ = y := by
      calc ⁅s, t⁆ * y * ⁅s, t⁆⁻¹
          = (s * t) * ((t * s)⁻¹ * y * (t * s)⁻¹⁻¹) * (s * t)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = (t * s) * ((t * s)⁻¹ * y * (t * s)⁻¹⁻¹) * (t * s)⁻¹ := h1
        _ = y := by group
    calc ⁅s, t⁆ * y = (⁅s, t⁆ * y * ⁅s, t⁆⁻¹) * ⁅s, t⁆ := by group
      _ = y * ⁅s, t⁆ := by rw [e]
  have hcT : ⁅s, t⁆ ∈ Qv (puAmalgam c.pu.le) β := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ht)
      (Subgroup.inv_mem _ hs)) (Subgroup.inv_mem _ ht)
  exact mem_qv_of_commute c.pu c.via h464' hsq h466 hα hαβ hy hyβ hcT hcomm

end CFSG.Yardstones.M71b2fd3d34b9
