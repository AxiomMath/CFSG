module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsLK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggStdPair_unique {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {w : G} {X₁ X₂ : Subgroup G}
    (h₁ : GGStdPair p Bs w X₁) (h₂ : GGStdPair p Bs w X₂) : X₁ = X₂ := by
  have hcent : Subgroup.centralizer (Subgroup.zpowers w : Set G) =
      Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hQ : LargeEvenPComponent p (Subgroup.centralizer (Subgroup.zpowers w : Set G)) X₂ :=
    hcent.symm ▸ h₂.2.2.1
  have hX2leX1 : X₂ ≤ X₁ :=
    ggQ2_absorb hLB hHyp (Subgroup.zpowers_le.mpr h₁.1) (Subgroup.mem_zpowers w) h₁ hQ
      h₂.2.2.2.2.2
  exact (ggF2 h₂.2.2.1 h₁.2.2.1 hX2leX1).symm

theorem GGStdPair.of_zpowers_eq {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {w w' : G}
    (h : GGStdPair p Bs w X) (hw : Subgroup.zpowers w' = Subgroup.zpowers w) :
    GGStdPair p Bs w' X := by
  obtain ⟨hwBs, hw1, hpc, hnorm, hiff, hA⟩ := h
  have hcent : ∀ v : G, Subgroup.centralizer (Subgroup.zpowers v : Set G) =
      Subgroup.centralizer ({v} : Set G) := fun v => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine ⟨?_, ?_, ?_, hnorm, ?_, hA⟩
  · have h1 : w' ∈ Subgroup.zpowers w := hw ▸ Subgroup.mem_zpowers w'
    exact (Subgroup.zpowers_le.mpr hwBs) h1
  · intro h1
    apply hw1
    have h2 : w ∈ Subgroup.zpowers w' := hw.symm ▸ Subgroup.mem_zpowers w
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h2
    exact h2
  · rw [← hcent, hw, hcent]
    exact hpc
  · intro b hb
    rw [hw]
    exact hiff b hb

theorem ggStdPair_lineStab_normalizes {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {w : G} {X : Subgroup G}
    (hX : GGStdPair p Bs w X) (hw : w ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφw : φ ⟨w, hw⟩ ∈ Subgroup.zpowers (⟨w, hw⟩ : ↥Bs)) :
    φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs)) := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgw : g * w * g⁻¹ ∈ Subgroup.zpowers w := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφw
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 := congrArg Subtype.val hk
    rw [hφg] at h1
    simpa using h1
  have hmap : (Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * w * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hzp : Subgroup.zpowers w = Subgroup.zpowers (g * w * g⁻¹) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgw) ?_).symm
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hXg : GGStdPair p Bs w (X.map (MulAut.conj g).toMonoidHom) :=
    (ggStdPair_conj hgN hX).of_zpowers_eq hzp
  have hXeq : X.map (MulAut.conj g).toMonoidHom = X := ggStdPair_unique hLB hHyp hXg hX
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have h1 : (MulAut.conj g).toMonoidHom k ∈ X.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hk
      rw [hXeq] at h1
      simpa [MulAut.conj_apply] using h1
    · intro hk
      rw [← hXeq] at hk
      obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hk
      have h1 : k' = k := by
        have h2 : g * k' * g⁻¹ = g * k * g⁻¹ := by simpa [MulAut.conj_apply] using hkk'
        simpa using h2
      exact h1 ▸ hk'
  have hφi := inv_apply_of_forall hφg
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX l).mp hl,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN), fun b => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
    group
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    have hgX' := Subgroup.inv_mem _ hgX
    have hgN' := Subgroup.inv_mem _ hgN
    refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hgX' l).mp hl
    · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hgN
    · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
      rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
      group

theorem ggQ2_nbrLineStab_normalizes {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hy : y ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs)) :
    φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
  ggStdPair_lineStab_normalizes hLB hHyp (ggStdPair_nbr hLB hP hHyp hAJ hK1 hnb) hy hφ hφy

theorem ggQ2_lineStab_normalizes_L {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥) (hx : x ∈ Bs)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
  ggStdPair_lineStab_normalizes hLB hHyp (ggStdPair_L hP hHyp hAJ) hx hφ hφx

end CFSG.StandardType

end
