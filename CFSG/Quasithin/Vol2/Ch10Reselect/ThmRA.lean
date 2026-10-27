module

public import CFSG.Quasithin.Vol2.Ch10Reselect.JGroup
public import CFSG.Quasithin.Vol2.Ch10Reselect.LineSub2

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

private lemma normalizer_U_of_fsuML (s : ↥(fsuML T L)) :
    (s : G) ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
  have h := mem_acting_of_mem_fsuML (I := I) s.2
  unfold UModel.acting at h
  exact (Subgroup.mem_inf.mp h).1

private lemma conj_mem_commutator_of {H K : Subgroup G} {s : G}
    (hH : s ∈ Subgroup.normalizer (H : Set G)) (hK : s ∈ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ ⁅H, K⁆) : s * x * s⁻¹ ∈ ⁅H, K⁆ := by
  have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    have hc : ⁅s * h * s⁻¹, s * k * s⁻¹⁆ ∈ ⁅H, K⁆ :=
      Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hH h).mp hh)
        ((Subgroup.mem_normalizer_iff.mp hK k).mp hk)
    rw [Subgroup.mem_comap]
    simpa [commutatorElement_def, mul_assoc] using hc
  exact Subgroup.mem_comap.mp (hle hx)

private lemma normalizer_commutator_of_mem {H K : Subgroup G} {s : G}
    (hH : s ∈ Subgroup.normalizer (H : Set G)) (hK : s ∈ Subgroup.normalizer (K : Set G)) :
    s ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_commutator_of hH hK
  · intro hy
    have h := conj_mem_commutator_of ((Subgroup.normalizer (H : Set G)).inv_mem hH)
      ((Subgroup.normalizer (K : Set G)).inv_mem hK) hy
    have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
    rwa [e] at h

theorem fsuML_le_normalizer_lineSub (M : RModel T L I K) {w : Fin 2 → K}
    (hw : ∀ (γ : ↥(fsuML T L)) (p : UTilde K), p ∈ linePair K w → actML M γ p ∈ linePair K w) :
    fsuML T L ≤ Subgroup.normalizer (M.lineSub w : Set G) := by
  have fwd : ∀ s : ↥(fsuML T L), ∀ u : G, u ∈ M.lineSub w →
      (s : G) * u * (s : G)⁻¹ ∈ M.lineSub w := by
    intro s u hu
    obtain ⟨huU, hp⟩ := (UModel.mem_lineSub_iff M w).mp hu
    have hsuU : (s : G) * u * (s : G)⁻¹ ∈ fsuUL T L I :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_U_of_fsuML s) u).mp huU
    refine (UModel.mem_lineSub_iff M w).mpr ⟨hsuU, ?_⟩
    have e : Multiplicative.toAdd (M.ψ ⟨(s : G) * u * (s : G)⁻¹, hsuU⟩) =
        actML M s (Multiplicative.toAdd (M.ψ ⟨u, huU⟩)) :=
      actML_ψ M s ⟨u, huU⟩ hsuU
    have hact : actML M s (Multiplicative.toAdd (M.ψ ⟨u, huU⟩)) ∈ linePair K w :=
      hw s _ (mem_lineAdd_iff.mp hp)
    exact mem_lineAdd_iff.mpr (by rw [e]; exact hact)
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact fwd ⟨s, hs⟩ u
  · intro hu
    have h : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ ∈ M.lineSub w :=
      fwd ⟨s⁻¹, (fsuML T L).inv_mem hs⟩ (s * u * s⁻¹) hu
    have e : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [e] at h

theorem fsuML_le_normalizer_lineJ (M : RModel T L I K) {w : Fin 2 → K}
    (hw : ∀ (γ : ↥(fsuML T L)) (p : UTilde K), p ∈ linePair K w → actML M γ p ∈ linePair K w) :
    fsuML T L ≤ Subgroup.normalizer (M.lineJ w : Set G) := by
  intro s hs
  exact normalizer_commutator_of_mem (fsuML_le_normalizer_lineSub M hw hs)
    (Subgroup.mem_inf.mp hs).2

theorem Z_le_centralizer_L (T L I : Subgroup G) :
    fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l (le_fsuL0 T L hl)

theorem jData_of_line (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) (hA : Concl326A T L I)
    [Nontrivial K] (M : RModel T L I K) {w : Fin 2 → K} (hw0 : w ≠ 0)
    (hw : ∀ (γ : ↥(fsuML T L)) (p : UTilde K), p ∈ linePair K w → actML M γ p ∈ linePair K w) :
    JData T L I (M.lineJ w) :=
  { fsu := hfsu
    lt := hlt
    hA := hA
    le_U := UModel.lineJ_le_U M w (L_le_normalizer_fsuUL T L I)
    perf := UModel.commutator_lineJ M hw0 (L_le_normalizer_fsuUL T L I)
      (Z_le_centralizer_L T L I)
    norm := fsuML_le_normalizer_lineJ M hw }

end CFSG.Quasithin.Vol2.Ch10Reselect
