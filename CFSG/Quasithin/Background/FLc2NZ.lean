module

public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLcGrp

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem isSylowTwoOf_conj_of_mem [Finite G] {S L : Subgroup G} (hS : IsSylowTwoOf S L) {l : G} (hl : l ∈ L) :
    IsSylowTwoOf (conjSub l⁻¹ S) L := by
  have hS' := hS
  rw [A4.isSylowTwoOf_iff_maximal] at hS' ⊢
  obtain ⟨hSL, hS2, hmax⟩ := hS'
  refine ⟨fun x hx => ?_, hS2.map (MulAut.conj l⁻¹).toMonoidHom, fun P hPL hP hSP => ?_⟩
  · rw [mem_conjSub, inv_inv] at hx
    have : x = l⁻¹ * (l * x * l⁻¹) * l := by group
    rw [this]
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) (hSL hx)) hl
  · have hP' : IsPGroup 2 (conjSub l P) := hP.map (MulAut.conj l).toMonoidHom
    have hSP' : S ≤ conjSub l P := by
      intro s hs
      rw [mem_conjSub]
      apply hSP
      rw [mem_conjSub, inv_inv]
      have : l * (l⁻¹ * s * l) * l⁻¹ = s := by group
      rw [this]
      exact hs
    have hP'L : conjSub l P ≤ L := by
      intro x hx
      rw [mem_conjSub] at hx
      have : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
      rw [this]
      exact L.mul_mem (L.mul_mem hl (hPL hx)) (L.inv_mem hl)
    have hle := hmax _ hP'L hP' hSP'
    intro x hx
    rw [mem_conjSub, inv_inv]
    apply hle
    rw [mem_conjSub]
    have : l⁻¹ * (l * x * l⁻¹) * l = x := by group
    rw [this]
    exact hx

theorem normalizer_le_centralizer_of_sylow [Finite G] {L SL Zs : Subgroup G} (hSyl : IsSylowTwoOf SL L)
    (hN : L ⊓ Subgroup.normalizer (SL : Set G) ≤ SL) (hSZ : ∀ s ∈ SL, ∀ z ∈ Zs, s * z * s⁻¹ = z) :
    L ⊓ Subgroup.normalizer (Zs : Set G) ≤ L ⊓ Subgroup.centralizer (Zs : Set G) := by
  rintro l ⟨hlL, hlN⟩
  refine ⟨hlL, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  set P : Subgroup G := L ⊓ Subgroup.centralizer ({v} : Set G) with hP
  have hSLL : SL ≤ L := hSyl.1
  have hfix : ∀ s ∈ SL, s * v * s⁻¹ = v := fun s hs => hSZ s hs v hv
  have hcentr : ∀ x : G, x * v * x⁻¹ = v → x ∈ Subgroup.centralizer ({v} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [hx]
  have hSLP : SL ≤ P := fun s hs => ⟨hSLL hs, hcentr s (hfix s hs)⟩
  set SL' : Subgroup G := conjSub l⁻¹ SL with hSL'
  have hSyl' : IsSylowTwoOf SL' L := isSylowTwoOf_conj_of_mem hSyl hlL
  have hSL'P : SL' ≤ P := by
    intro x hx
    have hxL : x ∈ L := hSyl'.1 hx
    refine ⟨hxL, hcentr x ?_⟩
    rw [hSL', mem_conjSub, inv_inv] at hx
    have hlv : l * v * l⁻¹ ∈ Zs := (Subgroup.mem_normalizer_iff.1 hlN v).1 hv
    have h1 := hSZ _ hx _ hlv
    have h2 : x * v * x⁻¹ = l⁻¹ * ((l * x * l⁻¹) * (l * v * l⁻¹) * (l * x * l⁻¹)⁻¹) * l := by group
    rw [h2, h1]
    group
  have hSylP : IsSylowTwoOf SL P := A4.isSylowTwoOf_mono hSyl hSLP (inf_le_left)
  have hSylP' : IsSylowTwoOf SL' P := A4.isSylowTwoOf_mono hSyl' hSL'P (inf_le_left)
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_of_isSylowTwoOf hSylP
  obtain ⟨Q₂, hQ₂⟩ := exists_sylow_of_isSylowTwoOf hSylP'
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (↥P) Q₁ Q₂
  have hpQ : (Q₂ : Subgroup ↥P) = (Q₁ : Subgroup ↥P).map (MulAut.conj p).toMonoidHom := by
    rw [← hp]
    rfl
  have hnorm : (l * (p : G)) ∈ Subgroup.normalizer (SL : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have key : ∀ y : G, y ∈ SL ↔ (l * (p : G)) * y * (l * (p : G))⁻¹ ∈ SL := by
      intro y
      have hconj : ∀ y : ↥P, y ∈ (Q₁ : Subgroup ↥P) ↔ (MulAut.conj p) y ∈ (Q₂ : Subgroup ↥P) := by
        intro y
        rw [hpQ]
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := (MulAut.conj p).injective hzy
          rw [← this]
          exact hz
      constructor
      · intro hy
        have hyP : y ∈ P := hSLP hy
        have h1 : (⟨y, hyP⟩ : ↥P) ∈ (Q₁ : Subgroup ↥P) := by rw [hQ₁]; exact hy
        have h2 := (hconj _).1 h1
        rw [hQ₂] at h2
        have h3 : (p : G) * y * (p : G)⁻¹ ∈ SL' := h2
        rw [hSL', mem_conjSub, inv_inv] at h3
        have e : (l * (p : G)) * y * (l * (p : G))⁻¹ = l * ((p : G) * y * (p : G)⁻¹) * l⁻¹ := by
          group
        rw [e]
        exact h3
      · intro hw
        have hpy : (p : G) * y * (p : G)⁻¹ ∈ SL' := by
          rw [hSL', mem_conjSub, inv_inv]
          have e : l * ((p : G) * y * (p : G)⁻¹) * l⁻¹ = (l * (p : G)) * y * (l * (p : G))⁻¹ := by
            group
          rw [e]
          exact hw
        have hpyP : (p : G) * y * (p : G)⁻¹ ∈ P := hSL'P hpy
        have hyP : y ∈ P := by
          have : y = (p : G)⁻¹ * ((p : G) * y * (p : G)⁻¹) * (p : G) := by group
          rw [this]
          exact P.mul_mem (P.mul_mem (P.inv_mem p.2) hpyP) p.2
        have h3 : (MulAut.conj p) (⟨y, hyP⟩ : ↥P) ∈ (Q₂ : Subgroup ↥P) := by
          rw [hQ₂]
          exact hpy
        have h4 := (hconj _).2 h3
        rw [hQ₁] at h4
        exact h4
    exact key t
  have hlpL : l * (p : G) ∈ L := L.mul_mem hlL p.2.1
  have hlpSL : l * (p : G) ∈ SL := hN ⟨hlpL, hnorm⟩
  have hpP : (p : G) ∈ P := p.2
  have hlP : l ∈ P := by
    have : l = (l * (p : G)) * (p : G)⁻¹ := by group
    rw [this]
    exact P.mul_mem (hSLP hlpSL) (P.inv_mem hpP)
  exact Subgroup.mem_centralizer_iff.1 hlP.2 v (Set.mem_singleton v)

end CFSG.Quasithin.FLc
