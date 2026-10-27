module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Bar
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)

variable {G : Type} [Group G] [Finite G]

theorem c8_star_of_le_normal (D : Data G) {V₀ V L K T' N : Subgroup G} {hV : IsElemAbelian 2 V}
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M)
    (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)))
    (hIm : barSub V₀ V hV (K ⊓ D.M) = pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hTK : T' ≤ K) (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal)
    (hcomm : ∀ t ∈ T', t ^ 2 = 1 → ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ N)
    (h3 : ¬ 3 ∣ Nat.card N) : C8Star D V₀ V L hV := by
  have hTM : T' ≤ D.M := by
    obtain ⟨Q, rfl⟩ := hT'
    exact map_subtype_le _
  have hTKM : T' ≤ K ⊓ D.M := le_inf hTK hTM
  refine ⟨T', ψ, hT', (barSub_mono V₀ V hV hTKM).trans hIm.le, ?_⟩
  set R : Subgroup G := N ⊓ D.M with hRdef
  have hO2pK : N ≤ K := hNK
  have hconj : ∀ {k x : G}, k ∈ K → x ∈ N → k * x * k⁻¹ ∈ N := by
    intro k x hk hx
    have h := hN.conj_mem ⟨x, hNK hx⟩ (by simpa [mem_subgroupOf] using hx) ⟨k, hk⟩
    simpa [mem_subgroupOf] using h
  have hRK : R ≤ K ⊓ D.M := by
    rw [hRdef]
    exact le_inf (inf_le_left.trans hO2pK) inf_le_right
  have hYX : ∀ y ∈ K ⊓ D.M, ∀ x ∈ R, y * x * y⁻¹ ∈ R := by
    intro y hy x hx
    rw [hRdef] at hx ⊢
    exact ⟨hconj hy.1 hx.1,
      D.M.mul_mem (D.M.mul_mem hy.2 hx.2) (D.M.inv_mem hy.2)⟩
  have hXbar : barSub V₀ V hV R ≤
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
    (barSub_mono V₀ V hV hRK).trans hIm.le
  have hXn : ∀ g ∈ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)),
      ∀ x ∈ barSub V₀ V hV R, g * x * g⁻¹ ∈ barSub V₀ V hV R := by
    intro g hg x hx
    rw [← hIm] at hg
    exact c8_conj_mem_barSub V₀ V hV hYX g hg x hx
  have h3R : ¬ 3 ∣ Nat.card (barSub V₀ V hV R) := by
    intro hdvd
    exact h3 (hdvd.trans ((c8_card_barSub_dvd V₀ V hV R).trans
      (Subgroup.card_dvd_of_le (show R ≤ N from inf_le_left))))
  have hRbar : barSub V₀ V hV R ≤ pullSub ψ (tauSym 3).range :=
    c8_le_pullSub_range_of_normal ψ hXbar hXn h3R
  intro t htT' ht2 ht
  have hs : actTil V₀ V hV ⟨t, ht⟩ ∈
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
    rw [← hIm]
    exact actTil_mem_barSub V₀ V hV (hTKM htT') ht
  refine c8_mem_pullSub_range_of_commutator_mem ψ hs ?_
  intro p hp
  rw [← hIm] at hp
  obtain ⟨⟨k, hks⟩, hkKM, rfl⟩ := (mem_barSub V₀ V hV (K ⊓ D.M) p).1 hp
  have hkK : k ∈ K := hkKM.1
  have hkM : k ∈ D.M := hkKM.2
  have htM : t ∈ D.M := hTM htT'
  have hmem : t * k * t⁻¹ * k⁻¹ ∈ R := by
    rw [hRdef]
    exact ⟨hcomm t htT' ht2 k hkK,
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem htM hkM) (D.M.inv_mem htM))
        (D.M.inv_mem hkM)⟩
  have hstab : t * k * t⁻¹ * k⁻¹ ∈ stabTil V₀ V :=
    (⟨t, ht⟩ * ⟨k, hks⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hks⟩⁻¹ : ↥(stabTil V₀ V)).2
  have heq : actTil V₀ V hV ⟨t, ht⟩ * actTil V₀ V hV ⟨k, hks⟩ *
        (actTil V₀ V hV ⟨t, ht⟩)⁻¹ * (actTil V₀ V hV ⟨k, hks⟩)⁻¹
      = actTil V₀ V hV (⟨t, ht⟩ * ⟨k, hks⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hks⟩⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [heq]
  have hprod : (⟨t * k * t⁻¹ * k⁻¹, hstab⟩ : ↥(stabTil V₀ V)) =
      ⟨t, ht⟩ * ⟨k, hks⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hks⟩⁻¹ := Subtype.ext rfl
  rw [← hprod]
  exact hRbar (actTil_mem_barSub V₀ V hV hmem hstab)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
