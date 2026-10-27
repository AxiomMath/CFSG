module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsPrime
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_exists_fixed_in_D {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) {φ : MulAut ↥Bs}
    (hR : GGIsReflection p φ) : ∃ u : ↥Bs, (u : G) ∈ D ∧ u ≠ 1 ∧ φ u = u := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hcardD : Nat.card D = p ^ 2 := hStdSub.1.2.2.1
  have hp' : p.Prime := hI.2.2.2.2.2.1.1
  let F : Subgroup ↥Bs := MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥Bs)
  let D' : Subgroup ↥Bs := D.subgroupOf Bs
  have hFcard : Nat.card F * p = Nat.card ↥Bs := hR.2
  have hD'card : Nat.card D' = p ^ 2 := by
    change Nat.card (D.subgroupOf Bs) = p ^ 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDBs).toEquiv, hcardD]
  have hFindex : F.index = p := by
    rw [Subgroup.index_eq_card_div (H := F), ← hFcard]
    exact Nat.mul_div_cancel_left p Nat.card_pos
  have hrel : F.relIndex D' * Nat.card (F ⊓ D' : Subgroup ↥Bs) = Nat.card D' :=
    Subgroup.relIndex_mul_card F D'
  have hrel_le : F.relIndex D' ≤ F.index := by
    have htop : F.relIndex (⊤ : Subgroup ↥Bs) ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact F.index_ne_zero_of_finite
    have h := Subgroup.relIndex_le_of_le_right (H := F) (K := D') (L := ⊤) le_top htop
    simpa using h
  have hbig : p ≤ Nat.card (F ⊓ D' : Subgroup ↥Bs) := by
    have h1 : F.relIndex D' * Nat.card (F ⊓ D' : Subgroup ↥Bs) = p ^ 2 := by
      rw [hrel, hD'card]
    have h2 : F.relIndex D' * Nat.card (F ⊓ D' : Subgroup ↥Bs) ≤
        p * Nat.card (F ⊓ D' : Subgroup ↥Bs) :=
      Nat.mul_le_mul_right _ (hrel_le.trans_eq hFindex)
    rw [h1] at h2
    exact Nat.le_of_mul_le_mul_left (by simpa [pow_two] using h2) hp'.pos
  have hNontriv : Nontrivial (F ⊓ D' : Subgroup ↥Bs) :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le hp'.one_lt hbig)
  obtain ⟨u', hu'F, hu'ne⟩ := Subgroup.exists_ne_one_of_nontrivial (F ⊓ D')
  exact ⟨u', Subgroup.mem_subgroupOf.mp hu'F.2, hu'ne, hu'F.1⟩

private theorem ggQ2s08b_stdPair'_of_zpowers_eq {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {w w' : G} (h : GGStdPair' p Bs w X) (hw : Subgroup.zpowers w' = Subgroup.zpowers w) :
    GGStdPair' p Bs w' X := by
  obtain ⟨hwBs, hw1, hpc, hnorm, hcard, hA⟩ := h
  have hcent : ∀ v : G, Subgroup.centralizer (Subgroup.zpowers v : Set G) =
      Subgroup.centralizer ({v} : Set G) := fun v => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine ⟨?_, ?_, ?_, hnorm, hcard, hA⟩
  · have h1 : w' ∈ Subgroup.zpowers w := hw ▸ Subgroup.mem_zpowers w'
    exact (Subgroup.zpowers_le.mpr hwBs) h1
  · intro h1
    apply hw1
    have h2 : w ∈ Subgroup.zpowers w' := hw.symm ▸ Subgroup.mem_zpowers w
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h2
    exact h2
  · rw [← hcent, hw, hcent]
    exact hpc

theorem ggQ2s08_nbr_normalizes_K (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y) : g ∈ Subgroup.normalizer (K : Set G) := by
  have hK : GGStdPair' p Bs y K := ggStdPair'_nbr hLB hP hHyp hCav hnb
  have hKg : GGStdPair' p Bs (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) :=
    ggStdPair'_conj hg hK
  have hmap : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * y * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hzp : Subgroup.zpowers y = Subgroup.zpowers (g * y * g⁻¹) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy) ?_).symm
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hpair : GGStdPair' p Bs y (K.map (MulAut.conj g).toMonoidHom) :=
    ggQ2s08b_stdPair'_of_zpowers_eq hKg hzp
  have hKeq : K.map (MulAut.conj g).toMonoidHom = K :=
    ggStdPair'_unique hLB hHyp hp hpair hK
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have h1 : (MulAut.conj g).toMonoidHom k ∈ K.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hk
    rw [hKeq] at h1
    simpa [MulAut.conj_apply] using h1
  · intro hk
    rw [← hKeq] at hk
    obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hk
    have h1 : k' = k := by
      have h2 : g * k' * g⁻¹ = g * k * g⁻¹ := by simpa [MulAut.conj_apply] using hkk'
      simpa using h2
    exact h1 ▸ hk'

end CFSG.StandardType

end

