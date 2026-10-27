module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCore
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def KS1618Card : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → (∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A) →
    ∀ g : G, g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) → g * c * g⁻¹ ∈ A →
      Nat.card (A ⊓ L.map (MulAut.conj g).toMonoidHom : Subgroup G) = 9

variable {G : Type} [Group G] [Finite G]

theorem step1618Trans_of (h1616 : Step1616) (h138 : Item138N) (hCard : KS1618Card)
    (hF : KS1617Fus) : Step1618Trans := by
  intro G _ _ A c L h h1617 g hg hgc
  have h9g := hCard G A c L h h1617 g hg hgc
  refine ⟨h9g, fun y hy hy1 z hz hz1 => ?_⟩
  obtain ⟨n, hz'⟩ := h1616 G A c L h
  have hn3 := Proof1617.not_three_dvd_of_isZ3 h h138 hz'
  obtain ⟨hcL, -, -⟩ := Proof1617.facts_of_isZ3 h hz'
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  set DG := A ⊓ Lg with hDG
  set c' := g * c * g⁻¹ with hc'
  have hmemLg : ∀ x, x ∈ Lg ↔ g⁻¹ * x * g ∈ L := fun x => by
    rw [hLg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  set D' := DG.map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hmemD' : ∀ x, x ∈ D' ↔ g * x * g⁻¹ ∈ DG := fun x => by
    rw [hD', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hD'L : D' ≤ L := by
    intro x hx
    have h1 := (Subgroup.mem_inf.mp ((hmemD' x).mp hx)).2
    rw [hmemLg] at h1
    simpa [mul_assoc] using h1
  have hDGab : CFSG.Assembly.IsElemAbelian 3 DG :=
    Proof169.isElemAbelian_of_le h.isElemAbelian inf_le_left
  have hD'ab : CFSG.Assembly.IsElemAbelian 3 D' :=
    Proof1617.isElemAbelian_map' (MulAut.conj g⁻¹).toMonoidHom hDGab
  have hD'9 : Nat.card D' = 9 := by
    rw [hD', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h9g]
  have hy' : g⁻¹ * y * g ∈ D' := by
    rw [hmemD']
    simpa [mul_assoc] using hy
  have hz'' : g⁻¹ * z * g ∈ D' := by
    rw [hmemD']
    simpa [mul_assoc] using hz
  have hy'1 : g⁻¹ * y * g ≠ 1 := fun h1 => hy1 (by
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hz'1 : g⁻¹ * z * g ≠ 1 := fun h1 => hz1 (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨w', hw'LN, hw'yz⟩ := hF G L D' n hz'.1 hn3 hz'.2.1 hD'L hD'ab hD'9 _ hy' hy'1 _ hz''
    hz'1
  obtain ⟨hw'L, hw'N⟩ := Subgroup.mem_inf.mp hw'LN
  refine ⟨g * w' * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  ·
    have hc'A : c' ∈ A := hgc
    have hc'Lg : c' ∉ Lg := by
      intro hc'L
      rw [hmemLg] at hc'L
      apply hcL
      simpa [hc', mul_assoc] using hc'L
    have hc'3 : c' ^ 3 = 1 := h.isElemAbelian.2 c' hc'A
    obtain ⟨-, h27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc'3
      (fun hc'D => hc'Lg (Subgroup.mem_inf.mp hc'D).2) le_rfl h9g
      (fun s hs => h.isElemAbelian.2 s hs.1) (fun s hs => h.commute hc'A hs.1)
    have hAeq : A = Subgroup.zpowers c' ⊔ DG :=
      (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hc'A) inf_le_left)
        (by rw [h27, h.card_eq])).symm
    have hLgc : Lg ≤ Subgroup.centralizer ({c'} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxL := (hmemLg x).mp hx
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hxL)
      calc x * c' = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [hc']; group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
        _ = c' * x := by rw [hc']; group
    have hwLg : g * w' * g⁻¹ ∈ Lg := by
      rw [hmemLg]
      simpa [mul_assoc] using hw'L
    have hwDG : g * w' * g⁻¹ ∈ Subgroup.normalizer (DG : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hx' : g⁻¹ * x * g ∈ D' := by
        rw [hmemD']
        simpa [mul_assoc] using hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hw'N _).mp hx'
      rw [hmemD'] at h1
      have heq : g * (w' * (g⁻¹ * x * g) * w'⁻¹) * g⁻¹ =
          g * w' * g⁻¹ * x * (g * w' * g⁻¹)⁻¹ := by group
      rwa [heq] at h1
    exact Proof1617.mem_normalizer_of_mem_normalizer_inf hAeq hLgc
      (Subgroup.mem_inf.mpr ⟨hwLg, hwDG⟩)
  ·
    rw [hmemLg]
    simpa [mul_assoc] using hw'L
  ·
    calc g * w' * g⁻¹ * y * (g * w' * g⁻¹)⁻¹
        = g * (w' * (g⁻¹ * y * g) * w'⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hw'yz]
      _ = z := by group

end CFSG.RankThree.PartTwo.Sec16
