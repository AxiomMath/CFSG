module

public import CFSG.Quasithin.AppendixH.Common.OctadAltCore
public import CFSG.Quasithin.AppendixH.Common.OctadActionRange

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

theorem pCoreOf_eq_octFix_of_stab {O : Finset (Fin 24)}
    (hO : IsOctad O) {Z : Finset (Fin 24)} (hZO : Z ⊆ O) (hZ : Z.card ≤ 2) {H : Subgroup S24}
    (h1 : octFix O ≤ H) (h2 : H ≤ octStab O) (h3 : ∀ g ∈ H, ∀ z ∈ Z, g z ∈ Z)
    (h4 : ∀ g ∈ octStab O, (∀ z ∈ Z, g z = z) → g ∈ H) : pCoreOf 2 H = octFix O := by
  apply le_antisymm
  ·
    change (pCore 2 H).map H.subtype ≤ octFix O
    let Z' : Finset ↥O := Z.subtype (· ∈ O)
    let ψ : ↥H →* Equiv.Perm ↥O := (octAct O).comp (Subgroup.inclusion h2)
    have hZ'mem : ∀ a : ↥O, a ∈ Z' ↔ (a : Fin 24) ∈ Z := by
      intro a
      change a ∈ Z.subtype (· ∈ O) ↔ (a : Fin 24) ∈ Z
      exact Finset.mem_subtype
    have hZ'card : Z'.card ≤ 2 := by
      have hle : Z'.card ≤ Z.card := by
        change (Z.subtype (· ∈ O)).card ≤ Z.card
        rw [Finset.card_subtype]
        exact Finset.card_filter_le Z (· ∈ O)
      omega
    have hQ : 5 ≤ Fintype.card ↥O - Z'.card := by
      have hcardO : Fintype.card ↥O = 8 := by rw [Fintype.card_coe, hO.1]
      omega
    have hHalt : ψ.range ≤ alternatingGroup ↥O := by
      intro σ hσ
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
      change (octAct O) (Subgroup.inclusion h2 g) ∈ alternatingGroup ↥O
      have h : (octAct O) (Subgroup.inclusion h2 g) ∈ (octAct O).range :=
        MonoidHom.mem_range.mpr ⟨Subgroup.inclusion h2 g, rfl⟩
      rwa [range_octAct hO] at h
    have hHZ : ∀ σ ∈ ψ.range, ∀ z, σ z ∈ Z' ↔ z ∈ Z' := by
      intro σ hσ z
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
      change (octAct O) (Subgroup.inclusion h2 g) z ∈ Z' ↔ z ∈ Z'
      simp only [hZ'mem]
      have hψgz : (((octAct O) (Subgroup.inclusion h2 g) z : ↥O) : Fin 24) =
          (g : S24) (z : Fin 24) := octAct_apply (Subgroup.inclusion h2 g) z
      rw [hψgz]
      constructor
      · intro hz
        have hz' := h3 ((g : S24))⁻¹ (H.inv_mem g.2) ((g : S24) (z : Fin 24)) hz
        have hgz : (g : S24)⁻¹ ((g : S24) (z : Fin 24)) = (z : Fin 24) := by
          simp [Equiv.Perm.inv_def]
        rwa [hgz] at hz'
      · intro hz
        exact h3 (g : S24) g.2 (z : Fin 24) hz
    have hHA : ∀ σ ∈ alternatingGroup ↥O, (∀ z ∈ Z', σ z = z) → σ ∈ ψ.range := by
      intro σ hσ hσfix
      have hσrange : σ ∈ (octAct O).range := by
        rw [range_octAct hO]; exact hσ
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hσrange
      have hgfixZ : ∀ z ∈ Z, (g : S24) (z : Fin 24) = z := by
        intro z hz
        have hzO : z ∈ O := hZO hz
        have hz' : (⟨z, hzO⟩ : ↥O) ∈ Z' := by
          rw [hZ'mem]
          simpa using hz
        have h := hσfix ⟨z, hzO⟩ hz'
        have h2 : (octAct O g ⟨z, hzO⟩ : ↥O) = ⟨z, hzO⟩ := by rw [hg]; exact h
        have h3' := congrArg (Subtype.val : ↥O → Fin 24) h2
        simpa [octAct_apply] using h3'
      have hgH : (g : S24) ∈ H := h4 (g : S24) g.2 hgfixZ
      refine MonoidHom.mem_range.mpr ⟨⟨(g : S24), hgH⟩, ?_⟩
      change (octAct O) (Subgroup.inclusion h2 ⟨(g : S24), hgH⟩) = σ
      rw [show Subgroup.inclusion h2 ⟨(g : S24), hgH⟩ = g from Subtype.ext rfl, hg]
    have hNH : (pCore 2 H).map ψ ≤ ψ.range := Subgroup.map_le_range (f := ψ) (pCore 2 H)
    have hNn : ∀ h ∈ ψ.range, ∀ n ∈ (pCore 2 H).map ψ,
        h * n * h⁻¹ ∈ (pCore 2 H).map ψ := by
      intro h hh n hn
      obtain ⟨h₀, rfl⟩ := MonoidHom.mem_range.mp hh
      obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
      have hconj : ψ h₀ * ψ n₀ * (ψ h₀)⁻¹ = ψ (h₀ * n₀ * h₀⁻¹) := by
        simp only [map_mul, map_inv]
      rw [hconj]
      exact ⟨h₀ * n₀ * h₀⁻¹,
        (CFSG.pCore_normal (G := H) (p := 2)).conj_mem n₀ hn₀ h₀, rfl⟩
    have hN2 : IsPGroup 2 ((pCore 2 H).map ψ) :=
      (CFSG.pCore_isPGroup (G := H) (p := 2)).map ψ
    have hNbot : (pCore 2 H).map ψ = ⊥ :=
      eq_bot_of_normal_isPGroup_two (Q := ↥O) Z' hZ'card hQ hHalt hHZ hHA hNH hNn hN2
    have hpcle : pCore 2 H ≤ (octFix O).subgroupOf H := by
      intro n hn
      have hmem : ψ n ∈ (pCore 2 H).map ψ := ⟨n, hn, rfl⟩
      rw [hNbot] at hmem
      have hψn1 : ψ n = 1 := by simpa using hmem
      rw [Subgroup.mem_subgroupOf]
      have hker : Subgroup.inclusion h2 n ∈ (octAct O).ker := MonoidHom.mem_ker.mpr hψn1
      rw [ker_octAct O, Subgroup.mem_subgroupOf] at hker
      exact hker
    have hmap := Subgroup.map_mono (f := H.subtype) hpcle
    rwa [Subgroup.map_subgroupOf_eq_of_le h1] at hmap
  ·
    change octFix O ≤ (pCore 2 H).map H.subtype
    have hKp : IsPGroup 2 ((octFix O).subgroupOf H) :=
      (isPGroup_octFix (O := O) hO).of_equiv (Subgroup.subgroupOfEquivOfLe h1).symm
    have hKn : ((octFix O).subgroupOf H).Normal := by
      have hbase : ((octFix O).subgroupOf (octStab O)).Normal := normal_octFix O
      rw [← Subgroup.comap_inclusion_subgroupOf h2 (octFix O)]
      exact hbase.comap _
    have hle : (octFix O).subgroupOf H ≤ pCore 2 H := by
      show (octFix O).subgroupOf H ≤ sSup {N : Subgroup H | N.Normal ∧ IsPGroup 2 N}
      exact le_sSup ⟨hKn, hKp⟩
    have hmap := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le h1] at hmap

end CFSG.ASVolI.AppH
