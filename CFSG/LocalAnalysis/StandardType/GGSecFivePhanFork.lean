module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCount
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def ggPhanDisjRoots {k : ℕ} (γ δ : Fin k → ℤ) : Prop :=
  ∃ (a b c d : Fin k) (s s' u u' : ℤ), a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧ (u = 1 ∨ u = -1) ∧ (u' = 1 ∨ u' = -1) ∧
    γ = Pi.single a s + Pi.single b s' ∧ δ = Pi.single c u + Pi.single d u'

private theorem ggPhanNegMulPm {a b c : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) : -(a * b * c) = 1 ∨ -(a * b * c) = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num

private theorem ggPhanReflRoot_sq {k : ℕ} {t : ggWeylD k} {γ : Fin k → ℤ}
    (h : GGDReflRoot k t γ) : t * t = 1 := by
  obtain ⟨w, i, rfl, -⟩ := h
  have h2 : (coxeterMatrix (isFiniteType_cartanD k)).simple i *
      (coxeterMatrix (isFiniteType_cartanD k)).simple i = 1 := by
    simpa [pow_two] using (coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.simple_sq i
  calc (w * (coxeterMatrix (isFiniteType_cartanD k)).simple i * w⁻¹) *
        (w * (coxeterMatrix (isFiniteType_cartanD k)).simple i * w⁻¹)
      = w * ((coxeterMatrix (isFiniteType_cartanD k)).simple i *
          (coxeterMatrix (isFiniteType_cartanD k)).simple i) * w⁻¹ := by group
    _ = 1 := by rw [h2]; simp

private theorem ggPhanDReflectPair {k : ℕ} {a b c : Fin k} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (s t u v : ℤ) (hu : u = 1 ∨ u = -1) :
    ggDReflect (Pi.single a u + Pi.single c v) (Pi.single a s + Pi.single b t) =
      Pi.single b t + Pi.single c (-(s * u * v)) := by
  rcases hu with rfl | rfl
  · funext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
      simp [ggDReflect_apply, ggDDot_single_add_single, hxa, hxb, hxc, hab, hac, hbc,
        Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · funext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
      simp [ggDReflect_apply, ggDDot_single_add_single, hxa, hxb, hxc, hab, hac, hbc,
        Ne.symm hab, Ne.symm hac, Ne.symm hbc]

private def ggPhanSixRoots (k : ℕ) (t1 t2 t3 : Fin k) : Fin 6 → (Fin k → ℤ)
  | 0 => Pi.single t1 1 - Pi.single t2 1
  | 1 => Pi.single t1 1 + Pi.single t2 1
  | 2 => Pi.single t2 1 - Pi.single t3 1
  | 3 => Pi.single t2 1 + Pi.single t3 1
  | 4 => Pi.single t1 1 - Pi.single t3 1
  | 5 => Pi.single t1 1 + Pi.single t3 1

private theorem ggPhanPairEq {k : ℕ} {a b : Fin k} (hab : a ≠ b) {r r' : ℤ}
    (hr : r = 1 ∨ r = -1) (hr' : r' = 1 ∨ r' = -1) :
    ((Pi.single a r + Pi.single b r' : Fin k → ℤ) = Pi.single a 1 - Pi.single b 1) ∨
    ((Pi.single a r + Pi.single b r' : Fin k → ℤ) = -(Pi.single a 1 - Pi.single b 1)) ∨
    ((Pi.single a r + Pi.single b r' : Fin k → ℤ) = Pi.single a 1 + Pi.single b 1) ∨
    ((Pi.single a r + Pi.single b r' : Fin k → ℤ) = -(Pi.single a 1 + Pi.single b 1)) := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
  · right; right; left; rfl
  · left; rw [sub_eq_add_neg, Pi.single_neg]
  · right; left
    funext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hxa, hxb, hab, Ne.symm hab]
  · right; right; right
    funext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hxa, hxb, hab, Ne.symm hab]

private theorem ggPhanSixRoots_mem {k : ℕ} {t1 t2 t3 : Fin k} (h12 : t1 ≠ t2) (h13 : t1 ≠ t3)
    (h23 : t2 ≠ t3) {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hsupp : ∀ i, γ i ≠ 0 → i = t1 ∨ i = t2 ∨ i = t3) :
    ∃ j : Fin 6, γ = ggPhanSixRoots k t1 t2 t3 j ∨ γ = -ggPhanSixRoots k t1 t2 t3 j := by
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair hγ
  have hγe := ggDRootSet_eq_single_add_single hγ hab ha hb
  have hsa := ggDRootSet_sign hγ ha
  have hsb := ggDRootSet_sign hγ hb
  rcases hsupp a ha with ha1 | ha2 | ha3
  · subst a
    rcases hsupp b hb with hb1 | hb2 | hb3
    · subst b; exact (hab rfl).elim
    · subst b
      rcases ggPhanPairEq h12 hsa hsb with h | h | h | h
      · exact ⟨0, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨0, Or.inr (by rw [hγe, h]; rfl)⟩
      · exact ⟨1, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨1, Or.inr (by rw [hγe, h]; rfl)⟩
    · subst b
      rcases ggPhanPairEq h13 hsa hsb with h | h | h | h
      · exact ⟨4, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨4, Or.inr (by rw [hγe, h]; rfl)⟩
      · exact ⟨5, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨5, Or.inr (by rw [hγe, h]; rfl)⟩
  · subst a
    rcases hsupp b hb with hb1 | hb2 | hb3
    · subst b
      rcases ggPhanPairEq (a := t2) (b := t1) h12.symm hsa hsb with h | h | h | h
      · exact ⟨0, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨0, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨1, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
      · exact ⟨1, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
    · subst b; exact (hab rfl).elim
    · subst b
      rcases ggPhanPairEq (a := t2) (b := t3) h23 hsa hsb with h | h | h | h
      · exact ⟨2, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨2, Or.inr (by rw [hγe, h]; rfl)⟩
      · exact ⟨3, Or.inl (by rw [hγe, h]; rfl)⟩
      · exact ⟨3, Or.inr (by rw [hγe, h]; rfl)⟩
  · subst a
    rcases hsupp b hb with hb1 | hb2 | hb3
    · subst b
      rcases ggPhanPairEq (a := t3) (b := t1) h13.symm hsa hsb with h | h | h | h
      · exact ⟨4, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨4, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨5, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
      · exact ⟨5, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
    · subst b
      rcases ggPhanPairEq (a := t3) (b := t2) h23.symm hsa hsb with h | h | h | h
      · exact ⟨2, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨2, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, sub_eq_add_neg])⟩
      · exact ⟨3, Or.inl (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
      · exact ⟨3, Or.inr (by rw [hγe, h]; simp [ggPhanSixRoots, add_comm])⟩
    · subst b; exact (hab rfl).elim

private theorem ggPhan_three_coords {k : ℕ} (hk : 5 ≤ k) (Φ : Set (Fin k → ℤ))
    (hroot : ∀ γ ∈ Φ, γ ∈ ggDRootSet k)
    (hrefl : ∀ γ ∈ Φ, ∀ δ ∈ Φ, ggDReflect γ δ ∈ Φ)
    (hno : ∀ γ ∈ Φ, ∀ δ ∈ Φ, ¬ ggPhanDisjRoots γ δ)
    {γ0 : Fin k → ℤ} (hγ0 : γ0 ∈ Φ)
    {a0 b0 : Fin k} {s0 t0 : ℤ} (hab0 : a0 ≠ b0)
    (hs0 : s0 = 1 ∨ s0 = -1) (ht0 : t0 = 1 ∨ t0 = -1)
    (hγ0e : γ0 = Pi.single a0 s0 + Pi.single b0 t0) :
    ∃ t1 t2 t3 : Fin k, t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
      ∀ γ ∈ Φ, ∀ i, γ i ≠ 0 → i = t1 ∨ i = t2 ∨ i = t3 := by
  classical
  have hmeet : ∀ γ ∈ Φ, γ a0 ≠ 0 ∨ γ b0 ≠ 0 := by
    intro γ hγ
    by_contra h
    push Not at h
    obtain ⟨hga, hgb⟩ := h
    have hγr := hroot γ hγ
    obtain ⟨c, d, hcd, hc, hd⟩ := ggDRootSet_exists_pair hγr
    have hγe := ggDRootSet_eq_single_add_single hγr hcd hc hd
    have hca : c ≠ a0 := fun e => hc (e ▸ hga)
    have hda : d ≠ a0 := fun e => hd (e ▸ hga)
    have hcb : c ≠ b0 := fun e => hc (e ▸ hgb)
    have hdb : d ≠ b0 := fun e => hd (e ▸ hgb)
    exact hno γ0 hγ0 γ hγ ⟨a0, b0, c, d, s0, t0, γ c, γ d, hab0, hcd, hca.symm, hda.symm,
      hcb.symm, hdb.symm, hs0, ht0, ggDRootSet_sign hγr hc, ggDRootSet_sign hγr hd,
      hγ0e, hγe⟩
  have hex : ∃ c0 : Fin k, c0 ≠ a0 ∧ c0 ≠ b0 := by
    by_contra h
    have h' : ∀ c : Fin k, c = a0 ∨ c = b0 := by
      intro c
      by_cases hc : c = a0
      · exact Or.inl hc
      · exact Or.inr (by
          by_contra hb
          exact h ⟨c, hc, hb⟩)
    have hsub : (Finset.univ : Finset (Fin k)) = {a0, b0} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact h' c
    have hcard := congrArg Finset.card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    simp [hab0] at hcard
    omega
  by_cases hsame : ∀ γ ∈ Φ, ∀ i, γ i ≠ 0 → i = a0 ∨ i = b0
  · obtain ⟨c0, hc0a, hc0b⟩ := hex
    refine ⟨a0, b0, c0, hab0, hc0a.symm, hc0b.symm, ?_⟩
    intro γ hγ i hi
    rcases hsame γ hγ i hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hsame
    obtain ⟨δ1, hδ1Φ, c, hδ1c, hca, hcb⟩ := hsame
    refine ⟨a0, b0, c, hab0, hca.symm, hcb.symm, ?_⟩
    intro γ hγ i hi
    by_contra hnot
    push Not at hnot
    obtain ⟨hia, hib, hic⟩ := hnot
    have hγr := hroot γ hγ
    have hγmeet := hmeet γ hγ
    by_cases hγa : γ a0 ≠ 0
    · have hγrep : γ = Pi.single a0 (γ a0) + Pi.single i (γ i) :=
        ggDRootSet_eq_single_add_single hγr (Ne.symm hia) hγa hi
      by_cases hδa : δ1 a0 ≠ 0
      · have hδrep : δ1 = Pi.single a0 (δ1 a0) + Pi.single c (δ1 c) :=
          ggDRootSet_eq_single_add_single (hroot δ1 hδ1Φ) (Ne.symm hca) hδa hδ1c
        have hR : ggDReflect γ γ0 =
            Pi.single b0 t0 + Pi.single i (-(s0 * (γ a0) * (γ i))) := by
          calc ggDReflect γ γ0
              = ggDReflect (Pi.single a0 (γ a0) + Pi.single i (γ i))
                  (Pi.single a0 s0 + Pi.single b0 t0) := by
                conv_lhs => rw [hγrep, hγ0e]
            _ = Pi.single b0 t0 + Pi.single i (-(s0 * (γ a0) * (γ i))) :=
              ggPhanDReflectPair hab0 (Ne.symm hia) (Ne.symm hib) s0 t0 (γ a0) (γ i)
                (ggDRootSet_sign hγr hγa)
        refine hno (ggDReflect γ γ0) (hrefl γ hγ γ0 hγ0) δ1 hδ1Φ
          ⟨b0, i, a0, c, t0, -(s0 * (γ a0) * (γ i)), δ1 a0, δ1 c,
            hib.symm, Ne.symm hca, hab0.symm, Ne.symm hcb, hia, hic, ht0,
            ggPhanNegMulPm hs0 (ggDRootSet_sign hγr hγa) (ggDRootSet_sign hγr hi),
            ggDRootSet_sign (hroot δ1 hδ1Φ) hδa, ggDRootSet_sign (hroot δ1 hδ1Φ) hδ1c,
            hR, hδrep⟩
      · have hδb : δ1 b0 ≠ 0 := by
          rcases hmeet δ1 hδ1Φ with h | h
          · exact absurd h hδa
          · exact h
        have hδrep : δ1 = Pi.single b0 (δ1 b0) + Pi.single c (δ1 c) :=
          ggDRootSet_eq_single_add_single (hroot δ1 hδ1Φ) (Ne.symm hcb) hδb hδ1c
        refine hno γ hγ δ1 hδ1Φ
          ⟨a0, i, b0, c, γ a0, γ i, δ1 b0, δ1 c,
            Ne.symm hia, Ne.symm hcb, hab0, Ne.symm hca, hib, hic,
            ggDRootSet_sign hγr hγa, ggDRootSet_sign hγr hi,
            ggDRootSet_sign (hroot δ1 hδ1Φ) hδb, ggDRootSet_sign (hroot δ1 hδ1Φ) hδ1c,
            hγrep, hδrep⟩
    · have hγb : γ b0 ≠ 0 := by
        rcases hγmeet with h | h
        · exact absurd h hγa
        · exact h
      have hγrep : γ = Pi.single b0 (γ b0) + Pi.single i (γ i) :=
        ggDRootSet_eq_single_add_single hγr (Ne.symm hib) hγb hi
      by_cases hδa : δ1 a0 ≠ 0
      · have hδrep : δ1 = Pi.single a0 (δ1 a0) + Pi.single c (δ1 c) :=
          ggDRootSet_eq_single_add_single (hroot δ1 hδ1Φ) (Ne.symm hca) hδa hδ1c
        refine hno γ hγ δ1 hδ1Φ
          ⟨b0, i, a0, c, γ b0, γ i, δ1 a0, δ1 c,
            hib.symm, Ne.symm hca, hab0.symm, Ne.symm hcb, hia, hic,
            ggDRootSet_sign hγr hγb, ggDRootSet_sign hγr hi,
            ggDRootSet_sign (hroot δ1 hδ1Φ) hδa, ggDRootSet_sign (hroot δ1 hδ1Φ) hδ1c,
            hγrep, hδrep⟩
      · have hδb : δ1 b0 ≠ 0 := by
          rcases hmeet δ1 hδ1Φ with h | h
          · exact absurd h hδa
          · exact h
        have hδrep : δ1 = Pi.single b0 (δ1 b0) + Pi.single c (δ1 c) :=
          ggDRootSet_eq_single_add_single (hroot δ1 hδ1Φ) (Ne.symm hcb) hδb hδ1c
        have hR : ggDReflect γ γ0 =
            Pi.single a0 s0 + Pi.single i (-(t0 * (γ b0) * (γ i))) := by
          calc ggDReflect γ γ0
              = ggDReflect (Pi.single b0 (γ b0) + Pi.single i (γ i))
                  (Pi.single b0 t0 + Pi.single a0 s0) := by
                conv_lhs => rw [hγrep, show γ0 = Pi.single b0 t0 + Pi.single a0 s0 from by
                  rw [hγ0e, add_comm]]
            _ = Pi.single a0 s0 + Pi.single i (-(t0 * (γ b0) * (γ i))) :=
              ggPhanDReflectPair hab0.symm (Ne.symm hib) (Ne.symm hia) t0 s0 (γ b0) (γ i)
                (ggDRootSet_sign hγr hγb)
        refine hno (ggDReflect γ γ0) (hrefl γ hγ γ0 hγ0) δ1 hδ1Φ
          ⟨a0, i, b0, c, s0, -(t0 * (γ b0) * (γ i)), δ1 b0, δ1 c,
            Ne.symm hia, Ne.symm hcb, hab0, Ne.symm hca, hib, hic, hs0,
            ggPhanNegMulPm ht0 (ggDRootSet_sign hγr hγb) (ggDRootSet_sign hγr hi),
            ggDRootSet_sign (hroot δ1 hδ1Φ) hδb, ggDRootSet_sign (hroot δ1 hδ1Φ) hδ1c,
            hR, hδrep⟩

theorem ggDk_memberRoots_L_disjSupp_phan
    (hGen : GGSecFiveGenPhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {k : ℕ} (hk : 5 ≤ k) {σ : Fin k ≃ ι} (hM : M = (ggCoxeterMatrixD k).reindex σ)
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) :
    ∃ t t' : M.Group, GGDDisjSupp k (φ t) (φ t') ∧
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hk1 : k ≠ 1 := by omega
  have hp1 : 1 < p := (ggRouteCfg_prime hcfg).1.one_lt
  have hp0 : 0 < p := (ggRouteCfg_prime hcfg).1.pos
  let Φ : Set (Fin k → ℤ) := ggDMemberRoots e φ L
  have hroot : ∀ γ ∈ Φ, γ ∈ ggDRootSet k := by
    rintro γ ⟨t, ht, -⟩
    exact ht.mem hk1
  have hrefl : ∀ γ ∈ Φ, ∀ δ ∈ Φ, ggDReflect γ δ ∈ Φ := by
    rintro γ ⟨t, ht, htL⟩ δ ⟨t', ht', ht'L⟩
    refine ⟨t * t' * t⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact ht'.conj (ht.action hk2)
    · have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ htL ht'L) (Subgroup.inv_mem _ htL)
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hgenL := hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns
  have hRne : ∃ r, r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e := by
    by_contra h
    have hempty : {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hr => h ⟨r, hr⟩
    have hLbot : L = ⊥ := by
      rw [hgenL]
      simp [hempty]
    exact ggRouteCfg_ne_bot hcfg hLbot
  obtain ⟨r0, hr0A, hr0R⟩ := hRne
  obtain ⟨w0, i0, hw0⟩ := hr0R
  let F : M.Group →* MulAut ↥Bs := (ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom
  let tg : M.Group := w0 * M.simple i0 * w0⁻¹
  have htgF : F tg = r0 := by
    change ((e tg : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r0
    exact hw0.symm
  obtain ⟨γ0, hγ0⟩ := exists_ggDReflRoot_of_conj φ hφ w0 i0
  have hγ0Φ : γ0 ∈ Φ := by
    refine ⟨tg, hγ0, ?_⟩
    change F tg ∈ ggAutomizer L Bs
    rw [htgF]
    exact hr0A
  by_contra hcon
  have hno : ∀ γ ∈ Φ, ∀ δ ∈ Φ, ¬ ggPhanDisjRoots γ δ := by
    rintro γ ⟨t, ht, htL⟩ δ ⟨t', ht', ht'L⟩ hdisj
    obtain ⟨a, b, c, d, s, s', u, u', hab, hcd, hac, had, hbc, hbd, hs, hs', hu, hu', hγe,
      hδe⟩ := hdisj
    exact hcon ⟨t, t', ⟨a, b, c, d, s, s', u, u', hab, hcd, hac, had, hbc, hbd, hs, hs', hu,
      hu', by simpa only [hγe] using ht, by simpa only [hδe] using ht'⟩, htL, ht'L⟩
  obtain ⟨a0, b0, s0, t0, hab0, hs0, ht0, hγ0e⟩ := hroot γ0 hγ0Φ
  obtain ⟨t1, t2, t3, h12, h13, h23, hsupp⟩ :=
    ggPhan_three_coords hk Φ hroot hrefl hno hγ0Φ hab0 hs0 ht0 hγ0e
  have hsixmem : ∀ j : Fin 6, ggPhanSixRoots k t1 t2 t3 j ∈ ggDRootSet k := by
    intro j
    fin_cases j
    · change Pi.single t1 1 - Pi.single t2 1 ∈ ggDRootSet k
      exact ⟨t1, t2, 1, -1, h12, Or.inl rfl, Or.inr rfl, by
        rw [sub_eq_add_neg, Pi.single_neg]⟩
    · change Pi.single t1 1 + Pi.single t2 1 ∈ ggDRootSet k
      exact ⟨t1, t2, 1, 1, h12, Or.inl rfl, Or.inl rfl, rfl⟩
    · change Pi.single t2 1 - Pi.single t3 1 ∈ ggDRootSet k
      exact ⟨t2, t3, 1, -1, h23, Or.inl rfl, Or.inr rfl, by
        rw [sub_eq_add_neg, Pi.single_neg]⟩
    · change Pi.single t2 1 + Pi.single t3 1 ∈ ggDRootSet k
      exact ⟨t2, t3, 1, 1, h23, Or.inl rfl, Or.inl rfl, rfl⟩
    · change Pi.single t1 1 - Pi.single t3 1 ∈ ggDRootSet k
      exact ⟨t1, t3, 1, -1, h13, Or.inl rfl, Or.inr rfl, by
        rw [sub_eq_add_neg, Pi.single_neg]⟩
    · change Pi.single t1 1 + Pi.single t3 1 ∈ ggDRootSet k
      exact ⟨t1, t3, 1, 1, h13, Or.inl rfl, Or.inl rfl, rfl⟩
  have hroot_gen : ∀ ρ : Fin k → ℤ, ρ ∈ ggDRootSet k → ∃ u : M.Group,
      GGDReflRoot k (φ u) ρ ∧ F u ∈ ggCoxRefl M e := by
    intro ρ hρ
    obtain ⟨t, ht⟩ := exists_ggDReflRoot hρ
    have ht' : GGDReflRoot k (φ (φ.symm t)) ρ := by simpa using ht
    exact ⟨φ.symm t, ht', mem_ggCoxRefl_of_ggDReflRoot e φ hφ ht'⟩
  obtain ⟨u1, hu1root, hu1R⟩ := hroot_gen (ggPhanSixRoots k t1 t2 t3 0) (hsixmem 0)
  obtain ⟨u2, hu2root, hu2R⟩ := hroot_gen (ggPhanSixRoots k t1 t2 t3 2) (hsixmem 2)
  obtain ⟨u3, hu3root, hu3R⟩ := hroot_gen (ggPhanSixRoots k t1 t2 t3 3) (hsixmem 3)
  have hD42 : ggDReflect (ggPhanSixRoots k t1 t2 t3 0) (ggPhanSixRoots k t1 t2 t3 2) =
      ggPhanSixRoots k t1 t2 t3 4 := by
    have h := ggPhanDReflectPair (a := t2) (b := t3) (c := t1) h23 h12.symm h13.symm
      (1 : ℤ) (-1) (-1) 1 (Or.inr rfl)
    simpa [ggPhanSixRoots, sub_eq_add_neg, Pi.single_neg, add_comm, add_left_comm,
      add_assoc] using h
  have hD43 : ggDReflect (ggPhanSixRoots k t1 t2 t3 0) (ggPhanSixRoots k t1 t2 t3 3) =
      ggPhanSixRoots k t1 t2 t3 5 := by
    have h := ggPhanDReflectPair (a := t2) (b := t3) (c := t1) h23 h12.symm h13.symm
      (1 : ℤ) 1 (-1) 1 (Or.inr rfl)
    simpa [ggPhanSixRoots, sub_eq_add_neg, Pi.single_neg, add_comm, add_left_comm,
      add_assoc] using h
  have hD64 : ggDReflect (ggPhanSixRoots k t1 t2 t3 4) (ggPhanSixRoots k t1 t2 t3 3) =
      ggPhanSixRoots k t1 t2 t3 1 := by
    have h := ggPhanDReflectPair (a := t3) (b := t2) (c := t1) h23.symm h13.symm h12.symm
      (1 : ℤ) 1 (-1) 1 (Or.inr rfl)
    simpa [ggPhanSixRoots, sub_eq_add_neg, Pi.single_neg, add_comm, add_left_comm,
      add_assoc] using h
  have hu1sq : φ u1 * φ u1 = 1 := ggPhanReflRoot_sq hu1root
  have hu1inv : (φ u1)⁻¹ = φ u1 := inv_eq_of_mul_eq_one_right hu1sq
  let u4 : M.Group := u1 * u2 * u1
  let u5 : M.Group := u1 * u3 * u1
  let u6 : M.Group := u4 * u3 * u4
  have hu4root : GGDReflRoot k (φ u4) (ggPhanSixRoots k t1 t2 t3 4) := by
    have h := hu2root.conj (hu1root.action hk2)
    have h' : GGDReflRoot k (φ (u1 * u2 * u1))
        (ggDReflect (ggPhanSixRoots k t1 t2 t3 0) (ggPhanSixRoots k t1 t2 t3 2)) := by
      simpa only [map_mul, hu1inv] using h
    simpa [u4, hD42] using h'
  have hu5root : GGDReflRoot k (φ u5) (ggPhanSixRoots k t1 t2 t3 5) := by
    have h := hu3root.conj (hu1root.action hk2)
    have h' : GGDReflRoot k (φ (u1 * u3 * u1))
        (ggDReflect (ggPhanSixRoots k t1 t2 t3 0) (ggPhanSixRoots k t1 t2 t3 3)) := by
      simpa only [map_mul, hu1inv] using h
    simpa [u5, hD43] using h'
  have hu4sq : φ u4 * φ u4 = 1 := ggPhanReflRoot_sq hu4root
  have hu4inv : (φ u4)⁻¹ = φ u4 := inv_eq_of_mul_eq_one_right hu4sq
  have hu6root : GGDReflRoot k (φ u6) (ggPhanSixRoots k t1 t2 t3 1) := by
    have h := hu3root.conj (hu4root.action hk2)
    have h' : GGDReflRoot k (φ (u4 * u3 * u4))
        (ggDReflect (ggPhanSixRoots k t1 t2 t3 4) (ggPhanSixRoots k t1 t2 t3 3)) := by
      simpa only [map_mul, hu4inv] using h
    simpa [u6, hD64] using h'
  let w : Fin 6 → M.Group
    | 0 => u1
    | 1 => u6
    | 2 => u2
    | 3 => u3
    | 4 => u4
    | 5 => u5
  have hrootw : ∀ j : Fin 6, GGDReflRoot k (φ (w j)) (ggPhanSixRoots k t1 t2 t3 j) := by
    intro j
    fin_cases j
    · exact hu1root
    · exact hu6root
    · exact hu2root
    · exact hu3root
    · exact hu4root
    · exact hu5root
  let r1 : MulAut ↥Bs := F u1
  let r2 : MulAut ↥Bs := F u2
  let r3 : MulAut ↥Bs := F u3
  let R3 : Finset (MulAut ↥Bs) := {r1, r2, r3}
  let C : Subgroup (MulAut ↥Bs) := Subgroup.closure (R3 : Set (MulAut ↥Bs))
  have hmem_u1 : F u1 ∈ C := Subgroup.subset_closure (by simp [R3, r1])
  have hmem_u2 : F u2 ∈ C := Subgroup.subset_closure (by simp [R3, r2])
  have hmem_u3 : F u3 ∈ C := Subgroup.subset_closure (by simp [R3, r3])
  have hmem_u4 : F u4 ∈ C := by
    simp only [u4, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem_u1 hmem_u2) hmem_u1
  have hmem_u5 : F u5 ∈ C := by
    simp only [u5, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem_u1 hmem_u3) hmem_u1
  have hmem_u6 : F u6 ∈ C := by
    simp only [u6, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem_u4 hmem_u3) hmem_u4
  have hmemw : ∀ j : Fin 6, F (w j) ∈ C := by
    intro j
    fin_cases j
    · exact hmem_u1
    · exact hmem_u6
    · exact hmem_u2
    · exact hmem_u3
    · exact hmem_u4
    · exact hmem_u5
  have hclC : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → r ∈ C := by
    intro r hrA hrR
    obtain ⟨w0', i0', hw0'⟩ := hrR
    let t : M.Group := w0' * M.simple i0' * w0'⁻¹
    have htF : F t = r := by
      change ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r
      exact hw0'.symm
    obtain ⟨γ, hγ⟩ := exists_ggDReflRoot_of_conj φ hφ w0' i0'
    have hγΦ : γ ∈ Φ := by
      refine ⟨t, hγ, ?_⟩
      change F t ∈ ggAutomizer L Bs
      rw [htF]
      exact hrA
    obtain ⟨j, hj⟩ := ggPhanSixRoots_mem (t1 := t1) (t2 := t2) (t3 := t3)
      h12 h13 h23 (hroot γ hγΦ) (hsupp γ hγΦ)
    have hφeq : φ t = φ (w j) := by
      rcases hj with h | h
      · exact hγ.unique hk2 (hrootw j) (Or.inl h.symm)
      · exact hγ.unique hk2 (hrootw j) (Or.inr (by rw [h]; simp))
    have ht_eq : t = w j := φ.injective hφeq
    rw [← htF, ht_eq]
    exact hmemw j
  have hR3 : ∀ r ∈ R3, GGIsReflection p r := by
    intro r hr
    simp only [R3, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact ggCoxRefl_isReflection hpres.2 hu1R
    · exact ggCoxRefl_isReflection hpres.2 hu2R
    · exact ggCoxRefl_isReflection hpres.2 hu3R
  have hcount := ggPhan_card_bstar_le hGen hcfg hns hpres hle3 hbig R3 hR3 hclC
  have hcard3 : R3.card ≤ 3 := by
    change ({r1, r2, r3} : Finset (MulAut ↥Bs)).card ≤ 3
    have h1 := Finset.card_insert_le r1 ({r2, r3} : Finset (MulAut ↥Bs))
    have h2 := Finset.card_insert_le r2 ({r3} : Finset (MulAut ↥Bs))
    simp only [Finset.card_singleton] at h2
    omega
  have hcount4 : Nat.card Bs ≤ p ^ 4 := by
    refine hcount.trans (Nat.pow_le_pow_right hp0 ?_)
    omega
  have hge : p ^ k ≤ Nat.card Bs := ggDk_card_bstar_ge hcfg hpres (by omega) hM
  have h5 : p ^ 5 ≤ Nat.card Bs := (Nat.pow_le_pow_right hp0 hk).trans hge
  have hlt : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp1 (by norm_num)
  exact absurd (h5.trans hcount4) (not_le_of_gt hlt)

end CFSG.StandardType

end
