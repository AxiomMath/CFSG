module

public import CFSG.LocalAnalysis.StandardType.FF81.CentACore
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
import CFSG.LocalAnalysis.StandardType.FF81.CentAO2
import CFSG.LocalAnalysis.StandardType.FF81.CentANormUi
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusion84
import CFSG.LocalAnalysis.StandardType.FF81.CentASigmaNorm
import CFSG.LocalAnalysis.StandardType.FF81.CentASigmaExcl
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin CFSG.Open

private theorem caCore_card_liftSub {G : Type} [Group G] {m : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2))
    (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) :
    Nat.card (liftSub φ K) = Nat.card K := by
  rw [liftSub]
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
  exact Subgroup.card_map_of_injective φ.symm.injective

private theorem caCore_card_uOne_eq_uTwo {G : Type} [Group G] {m : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)} :
    Nat.card (liftSub φ (uOne m)) = Nat.card (liftSub φ (uTwo m)) := by
  rw [caCore_card_liftSub, caCore_card_liftSub]
  have hc : Nat.card ((uOne m).map (sigmaStd m).toMonoidHom) = Nat.card (uOne m) :=
    Subgroup.card_map_of_injective (sigmaStd m).injective
  rw [sigmaStd_map_uOne m] at hc
  exact hc.symm

private theorem caCore_map_conj_sigma_le {G : Type} [Group G] {m : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)} {σ : G}
    (hσY : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y)
    (hσφ : ∀ y : ↥Y, φ ⟨σ * (y : G) * σ⁻¹, hσY (y : G) y.2⟩ = sigmaStd m (φ y))
    {K K' : Subgroup (GL (BlkIdx 1 m) (ZMod 2))}
    (hK : K.map (sigmaStd m).toMonoidHom = K') :
    (liftSub φ K).map (MulAut.conj σ).toMonoidHom ≤ liftSub φ K' := by
  intro x hx
  change x ∈ (liftSub φ K).map (MulAut.conj σ).toMonoidHom at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  change σ * u * σ⁻¹ ∈ liftSub φ K'
  rw [mem_liftSub] at hu ⊢
  obtain ⟨huY, huK⟩ := hu
  refine ⟨hσY u huY, ?_⟩
  rw [hσφ ⟨u, huY⟩]
  rw [← hK]
  exact Subgroup.mem_map_of_mem (sigmaStd m).toMonoidHom huK

private theorem caCore_conj_le_uOne_or_uTwo {G : Type} [Group G] [Finite G] {m : ℕ}
    {Y L R : Subgroup G} {b t : G} {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}
    (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ)
    (hfus : CentAFus Y b t φ) {W : Subgroup G} (hWU : W ≤ liftSub φ (uSub 1 m))
    (hconj : ∀ u ∈ W, u ≠ 1 → ∃ y ∈ Y, y * t * y⁻¹ = u)
    {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) :
    W.map (MulAut.conj h).toMonoidHom ≤ liftSub φ (uOne m) ∨
      W.map (MulAut.conj h).toMonoidHom ≤ liftSub φ (uTwo m) := by
  refine (SubgroupClass.subset_union).mp ?_
  intro x hx
  change x ∈ W.map (MulAut.conj h).toMonoidHom at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  by_cases hu1 : u = 1
  · left
    simpa [hu1] using (liftSub φ (uOne m)).one_mem
  · obtain ⟨y, hyY, rfl⟩ := hconj u hu hu1
    change h * (y * t * y⁻¹) * h⁻¹ ∈
      (liftSub φ (uOne m) : Set G) ∪ (liftSub φ (uTwo m) : Set G)
    have hmem : h * (y * t * y⁻¹) * h⁻¹ ∈ liftSub φ (uSub 1 m) :=
      conj_mem_liftSub_uSub hchar hS hh (hWU hu)
    have hmem' : (h * y) * t * (h * y)⁻¹ ∈ liftSub φ (uSub 1 m) := by
      rwa [show (h * y) * t * (h * y)⁻¹ = h * (y * t * y⁻¹) * h⁻¹ from by group]
    have hswap := conj_mem_liftSub_uOne_or_uTwo hS hfus hmem'
    have hconj : (h * y) * t * (h * y)⁻¹ = h * (y * t * y⁻¹) * h⁻¹ := by group
    rcases hswap with h1 | h2
    · left
      rwa [hconj] at h1
    · right
      rwa [hconj] at h2

private theorem caCore_map_uOne_eq_uTwo_of_not_mem {G : Type} [Group G] [Finite G]
    {m : ℕ} {Y L R : Subgroup G} {b t : G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)} (hchar : IsCharTwoType G)
    (hS : CentASetting m Y L R b t φ) (hfus : CentAFus Y b t φ) {h : G}
    (hh : h ∈ Subgroup.centralizer ({t} : Set G)) (hY : h ∉ Y) :
    (liftSub φ (uOne m)).map (MulAut.conj h).toMonoidHom = liftSub φ (uTwo m) := by
  have hchoice := caCore_conj_le_uOne_or_uTwo hchar hS hfus
    (W := liftSub φ (uOne m)) (liftSub_mono (uOne_le_uSub m))
    (fun u hu hu1 => exists_conj_eq_of_mem_liftSub_uOne hS hu hu1) hh
  have hcard : Nat.card ((liftSub φ (uOne m)).map (MulAut.conj h).toMonoidHom) =
      Nat.card (liftSub φ (uOne m)) :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  rcases hchoice with hle | hle
  · have hself : (liftSub φ (uOne m)).map (MulAut.conj h).toMonoidHom =
        liftSub φ (uOne m) :=
      Subgroup.eq_of_le_of_card_ge hle hcard.ge
    exfalso
    exact hY (normalizer_liftSub_uOne_le hchar hS
      ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hself))
  · exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard]; exact caCore_card_uOne_eq_uTwo.ge)

private theorem caCore_map_uTwo_eq_uOne_of_not_mem {G : Type} [Group G] [Finite G]
    {m : ℕ} {Y L R : Subgroup G} {b t : G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)} (hchar : IsCharTwoType G)
    (hS : CentASetting m Y L R b t φ) (hfus : CentAFus Y b t φ) {h : G}
    (hh : h ∈ Subgroup.centralizer ({t} : Set G)) (hY : h ∉ Y) :
    (liftSub φ (uTwo m)).map (MulAut.conj h).toMonoidHom = liftSub φ (uOne m) := by
  have hchoice := caCore_conj_le_uOne_or_uTwo hchar hS hfus
    (W := liftSub φ (uTwo m)) (liftSub_mono (uTwo_le_uSub m))
    (fun u hu hu1 => exists_conj_eq_of_mem_liftSub_uTwo hS hu hu1) hh
  have hcard : Nat.card ((liftSub φ (uTwo m)).map (MulAut.conj h).toMonoidHom) =
      Nat.card (liftSub φ (uTwo m)) :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  rcases hchoice with hle | hle
  · exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard]; exact caCore_card_uOne_eq_uTwo.le)
  · have hself : (liftSub φ (uTwo m)).map (MulAut.conj h).toMonoidHom =
        liftSub φ (uTwo m) :=
      Subgroup.eq_of_le_of_card_ge hle hcard.ge
    exfalso
    exact hY (normalizer_liftSub_uTwo_le hchar hS
      ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hself))

theorem centralizer_le_of_setting {G : Type} [Group G] [Finite G] (hchar : IsCharTwoType G)
    {m : ℕ} {Y L R : Subgroup G} {b t : G} {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}
    (hS : CentASetting m Y L R b t φ) (hfus : CentAFus Y b t φ) :
    Subgroup.centralizer ({t} : Set G) ≤ Y := by
  intro h hh
  by_contra hY
  have h12 := caCore_map_uOne_eq_uTwo_of_not_mem hchar hS hfus hh hY
  have h21 := caCore_map_uTwo_eq_uOne_of_not_mem hchar hS hfus hh hY
  obtain ⟨σ, hσH, hσ2, hσY, hσφ⟩ := exists_sigma_of_swap hchar hS hh h12 h21
  have hσle : (liftSub φ (uOne m)).map (MulAut.conj σ).toMonoidHom ≤
      liftSub φ (uTwo m) :=
    caCore_map_conj_sigma_le hσY hσφ (sigmaStd_map_uOne m)
  have hHσ : ∀ g ∈ Subgroup.centralizer ({t} : Set G), g ∈ Y ∨ g * σ ∈ Y := by
    intro g hg
    by_cases hgY : g ∈ Y
    · exact Or.inl hgY
    · right
      have hg21 := caCore_map_uTwo_eq_uOne_of_not_mem hchar hS hfus hg hgY
      apply normalizer_liftSub_uOne_le hchar hS
      apply (Subgroup.mem_normalizer_iff_map_conj_eq).mpr
      have hle : (liftSub φ (uOne m)).map (MulAut.conj (g * σ)).toMonoidHom ≤
          liftSub φ (uOne m) := by
        intro x hx
        change x ∈ (liftSub φ (uOne m)).map (MulAut.conj (g * σ)).toMonoidHom at hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        change (g * σ) * u * (g * σ)⁻¹ ∈ liftSub φ (uOne m)
        have hσu : σ * u * σ⁻¹ ∈ liftSub φ (uTwo m) :=
          hσle (Subgroup.mem_map_of_mem (MulAut.conj σ).toMonoidHom hu)
        have hgu : g * (σ * u * σ⁻¹) * g⁻¹ ∈ liftSub φ (uOne m) := by
          rw [← hg21]
          exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hσu
        simpa only [show (g * σ) * u * (g * σ)⁻¹ =
          g * (σ * u * σ⁻¹) * g⁻¹ from by group] using hgu
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (g * σ)).injective).ge
  exact false_of_sigma hchar hS hσH hσ2 hσY hσφ hHσ

end CFSG.StandardType.FF81.CentA

end
