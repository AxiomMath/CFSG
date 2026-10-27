module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma s16k_zmod2_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  exact (h a).resolve_left ha

lemma s16k_exists_pcycle_fix {n p : ℕ} {m : G6.PermMod n} (hp : p.Prime) (hpodd : Odd p)
    (s : Finset (Fin n)) (hscard : s.card = p) {b : ZMod 2}
    (hconst : ∀ i ∈ s, Multiplicative.toAdd m i = b) :
    ∃ c : Equiv.Perm (Fin n), c.IsCycle ∧ c.support = s ∧ orderOf c = p ∧
      c ∈ alternatingGroup (Fin n) ∧ G6.permAct n c m = m := by
  obtain ⟨c, hcon, hcsup⟩ := Finset.exists_cycleOn s
  have hsnt : (s : Set (Fin n)).Nontrivial :=
    Finset.nontrivial_coe.mpr
      (Finset.one_lt_card_iff_nontrivial.mp (by rw [hscard]; exact hp.one_lt))
  have hcsupp : c.support = s := by
    refine le_antisymm hcsup ?_
    intro x hx
    exact Equiv.Perm.mem_support.mpr (hcon.apply_ne hsnt hx)
  have hcyc : c.IsCycle := by
    rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
    refine ⟨(s : Set (Fin n)), hsnt, hcon, fun x hx => ?_⟩
    rw [← hcsupp]
    exact Equiv.Perm.mem_support.mpr hx
  have hord : orderOf c = p := by
    rw [hcyc.orderOf, hcsupp, hscard]
  have hsign : Equiv.Perm.sign c = 1 := by
    rw [hcyc.sign, hcsupp, hscard, hpodd.neg_one_pow]
    simp
  have hmemA : c ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  have hfix : G6.permAct n c m = m := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    by_cases hi : i ∈ s
    · have hi' : c⁻¹ i ∈ s := by
        rw [← hcsupp]
        refine (Equiv.Perm.apply_mem_support (f := c) (x := c⁻¹ i)).mp ?_
        simpa using (show i ∈ c.support from by rw [hcsupp]; exact hi)
      rw [hconst (c⁻¹ i) hi', hconst i hi]
    · have hci : c i = i := by
        rw [← Equiv.Perm.notMem_support, hcsupp]
        exact hi
      have hcinv : c⁻¹ i = i := (Equiv.symm_apply_eq c).mpr hci.symm
      rw [hcinv]
  exact ⟨c, hcyc, hcsupp, hord, hmemA, hfix⟩

theorem s16k_alt_fix_noncyclic (n : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 * p ≤ n)
    (m : G6.PermMod n) (hm : m ∈ G6.coreMod n) (h1 : m ≠ 1) (h2 : m ≠ G6.allOnes n) :
    ∃ B : Subgroup ↥(alternatingGroup (Fin n)), IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, G6.permAct n (b : Equiv.Perm (Fin n)) m = m := by
  classical
  have hpodd : Odd p := hp.odd_iff.mpr (by have := hp.two_le; omega)
  let Δ : Finset (Fin n) := Finset.univ.filter (fun i => Multiplicative.toAdd m i ≠ 0)
  let Γ : Finset (Fin n) := Finset.univ \ Δ
  have hsum : Δ.card + Γ.card = n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Δ)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h' : (Finset.univ \ Δ).card = Γ.card := rfl
    rw [h'] at h
    omega
  have hcases : 2 * p ≤ Δ.card ∨ (p ≤ Δ.card ∧ p ≤ Γ.card) ∨ 2 * p ≤ Γ.card := by
    omega
  have hmain : ∃ (s1 s2 : Finset (Fin n)), s1.card = p ∧ s2.card = p ∧
      (s1 ⊆ Δ ∨ s1 ⊆ Γ) ∧ (s2 ⊆ Δ ∨ s2 ⊆ Γ) ∧ _root_.Disjoint s1 s2 := by
    rcases hcases with hA | ⟨hpa, hpb⟩ | hD
    · obtain ⟨s1, hs1sub, hs1card⟩ := Finset.exists_subset_card_eq (s := Δ) (n := p) (by omega)
      have h2 : p ≤ (Δ \ s1).card := by
        rw [Finset.card_sdiff_of_subset hs1sub, hs1card]
        omega
      obtain ⟨s2, hs2sub, hs2card⟩ := Finset.exists_subset_card_eq (s := Δ \ s1) (n := p) h2
      refine ⟨s1, s2, hs1card, hs2card, Or.inl hs1sub,
        Or.inl (hs2sub.trans (Finset.sdiff_subset (s := Δ) (t := s1))), ?_⟩
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hs2sub hx2)).2 hx1
    · obtain ⟨s1, hs1sub, hs1card⟩ := Finset.exists_subset_card_eq (s := Δ) (n := p) hpa
      obtain ⟨s2, hs2sub, hs2card⟩ := Finset.exists_subset_card_eq (s := Γ) (n := p) hpb
      refine ⟨s1, s2, hs1card, hs2card, Or.inl hs1sub, Or.inr hs2sub, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hs2sub hx2)).2 (hs1sub hx1)
    · obtain ⟨s1, hs1sub, hs1card⟩ := Finset.exists_subset_card_eq (s := Γ) (n := p) (by omega)
      have h2 : p ≤ (Γ \ s1).card := by
        rw [Finset.card_sdiff_of_subset hs1sub, hs1card]
        omega
      obtain ⟨s2, hs2sub, hs2card⟩ := Finset.exists_subset_card_eq (s := Γ \ s1) (n := p) h2
      refine ⟨s1, s2, hs1card, hs2card, Or.inr hs1sub,
        Or.inr (hs2sub.trans (Finset.sdiff_subset (s := Γ) (t := s1))), ?_⟩
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hs2sub hx2)).2 hx1
  obtain ⟨s1, s2, hs1card, hs2card, hs1side, hs2side, hsdisj⟩ := hmain
  have hdata1 : ∃ b : ZMod 2, ∀ i ∈ s1, Multiplicative.toAdd m i = b := by
    rcases hs1side with hsub | hsub
    · refine ⟨1, fun i hi => s16k_zmod2_eq_one ?_⟩
      simpa [Δ] using hsub hi
    · refine ⟨0, fun i hi => ?_⟩
      have hmem : i ∉ Δ := (Finset.mem_sdiff.mp (hsub hi)).2
      simpa [Δ] using hmem
  have hdata2 : ∃ b : ZMod 2, ∀ i ∈ s2, Multiplicative.toAdd m i = b := by
    rcases hs2side with hsub | hsub
    · refine ⟨1, fun i hi => s16k_zmod2_eq_one ?_⟩
      simpa [Δ] using hsub hi
    · refine ⟨0, fun i hi => ?_⟩
      have hmem : i ∉ Δ := (Finset.mem_sdiff.mp (hsub hi)).2
      simpa [Δ] using hmem
  obtain ⟨b1, hb1⟩ := hdata1
  obtain ⟨b2, hb2⟩ := hdata2
  obtain ⟨c1, hc1cyc, hc1supp, hc1ord, hc1A, hc1fix⟩ :=
    s16k_exists_pcycle_fix hp hpodd s1 hs1card hb1
  obtain ⟨c2, hc2cyc, hc2supp, hc2ord, hc2A, hc2fix⟩ :=
    s16k_exists_pcycle_fix hp hpodd s2 hs2card hb2
  have hdisjc : c1.Disjoint c2 := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, hc1supp, hc2supp]
    exact hsdisj
  let A := alternatingGroup (Fin n)
  let xA : A := ⟨c1, hc1A⟩
  let yA : A := ⟨c2, hc2A⟩
  have hcommA : Commute xA yA := by
    rw [commute_iff_eq]
    exact Subtype.ext (by simpa [xA, yA] using hdisjc.commute.eq)
  let B : Subgroup A := Subgroup.closure ({xA, yA} : Set A)
  have hpair : ({xA, yA} : Set A).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hcommA
    · exact hcommA.symm
    · exact absurd rfl hab
  letI : CommGroup B := Subgroup.closureCommGroupOfComm hpair
  have hxB : xA ∈ B := Subgroup.subset_closure (by simp)
  have hyB : yA ∈ B := Subgroup.subset_closure (by simp)
  let xB : B := ⟨xA, hxB⟩
  let yB : B := ⟨yA, hyB⟩
  have hxordA : orderOf xA = p := by
    have h4 : orderOf c1 = orderOf xA := by
      simpa [xA] using Subgroup.orderOf_coe xA
    rw [← h4]
    exact hc1ord
  have hyordA : orderOf yA = p := by
    have h4 : orderOf c2 = orderOf yA := by
      simpa [yA] using Subgroup.orderOf_coe yA
    rw [← h4]
    exact hc2ord
  have hxord : orderOf xB = p := by
    have h1 : orderOf ((xB : B) : A) = orderOf xB := Subgroup.orderOf_coe xB
    have h2 : ((xB : B) : A) = xA := rfl
    rw [h1.symm, h2]
    exact hxordA
  have hyord : orderOf yB = p := by
    have h1 : orderOf ((yB : B) : A) = orderOf yB := Subgroup.orderOf_coe yB
    have h2 : ((yB : B) : A) = yA := rfl
    rw [h1.symm, h2]
    exact hyordA
  have hxBpow : xB ^ p = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one xB
  have hyBpow : yB ^ p = 1 := by
    rw [← hyord]
    exact pow_orderOf_eq_one yB
  have hBpow : ∀ b : B, b ^ p = 1 := by
    intro b
    refine Subgroup.closure_induction
      (p := fun a ha => (⟨a, ha⟩ : B) ^ p = 1) ?_ ?_ ?_ ?_ b.2
    · intro a ha
      have hmem : a ∈ ({xA, yA} : Set A) := ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · have h : (⟨xA, Subgroup.subset_closure ha⟩ : B) = xB := Subtype.ext rfl
        rw [h]
        exact hxBpow
      · have h : (⟨yA, Subgroup.subset_closure ha⟩ : B) = yB := Subtype.ext rfl
        rw [h]
        exact hyBpow
    · have h : (⟨(1 : A), Subgroup.one_mem B⟩ : B) = 1 := Subtype.ext rfl
      rw [h, one_pow]
    · intro x y hx hy ihx ihy
      have h : (⟨x * y, B.mul_mem hx hy⟩ : B) =
          (⟨x, hx⟩ : B) * (⟨y, hy⟩ : B) := Subtype.ext rfl
      rw [h, mul_pow, ihx, ihy, mul_one]
    · intro x hx ihx
      have h : (⟨x⁻¹, B.inv_mem hx⟩ : B) = (⟨x, hx⟩ : B)⁻¹ := Subtype.ext rfl
      rw [h, inv_pow, ihx, inv_one]
  have hIsP : IsPGroup p B := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro b
    exact ⟨1, by rw [pow_one, orderOf_dvd_iff_pow_eq_one]; exact hBpow b⟩
  have hnotcyc : ¬ IsCyclic B := by
    intro hcyc
    haveI := hcyc
    have hcardx : Nat.card (Subgroup.zpowers xB) = p := by
      rw [Nat.card_zpowers, hxord]
    have hcardy : Nat.card (Subgroup.zpowers yB) = p := by
      rw [Nat.card_zpowers, hyord]
    have heq : Subgroup.zpowers xB = Subgroup.zpowers yB := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, hcardx, hcardy]
    have hy_mem : yB ∈ Subgroup.zpowers xB := by
      rw [heq]
      exact Subgroup.mem_zpowers yB
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_mem
    have hkA : xA ^ k = yA := by
      have := congrArg (Subtype.val : B → A) hk
      simpa [xB, yB] using this
    have hkPerm : c1 ^ k = c2 := by
      have := congrArg (Subtype.val : A → Equiv.Perm (Fin n)) hkA
      simpa [xA, yA] using this
    have hle : c2.support ≤ c1.support := by
      rw [← hkPerm]
      exact Equiv.Perm.support_zpow_le c1 k
    have hdisjsupp : _root_.Disjoint c1.support c2.support := hdisjc.disjoint_support
    have hemp : c2.support = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (Finset.disjoint_left.mp hdisjsupp) (hle hx) hx
    have hc2one : c2 = 1 := Equiv.Perm.support_eq_empty_iff.mp hemp
    have hordone : orderOf c2 = 1 := by rw [hc2one, orderOf_one]
    rw [hc2ord] at hordone
    exact hp.ne_one hordone
  refine ⟨B, hIsP, hnotcyc, ?_⟩
  let K : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {σ | G6.permAct n σ m = m}
      mul_mem' := by
        intro σ τ hσ hτ
        show G6.permAct n (σ * τ) m = m
        rw [map_mul, MulAut.mul_apply, hτ, hσ]
      one_mem' := by simp
      inv_mem' := by
        intro σ hσ
        show G6.permAct n σ⁻¹ m = m
        have h : G6.permAct n σ (G6.permAct n σ⁻¹ m) = G6.permAct n σ m := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, hσ]
        exact (G6.permAct n σ).injective h }
  have hle : B ≤ K.comap A.subtype := by
    rw [Subgroup.closure_le (K.comap A.subtype)]
    intro z hz
    rcases hz with rfl | rfl
    · show G6.permAct n (xA : Equiv.Perm (Fin n)) m = m
      simpa [xA] using hc1fix
    · show G6.permAct n (yA : Equiv.Perm (Fin n)) m = m
      simpa [yA] using hc2fix
  intro b hb
  have hbK : A.subtype b ∈ K := hle hb
  show G6.permAct n (b : Equiv.Perm (Fin n)) m = m
  simpa [K] using hbK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
