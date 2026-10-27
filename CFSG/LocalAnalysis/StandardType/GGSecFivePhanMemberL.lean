module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCount
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupMemberRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedTop
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoinWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpFix
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDSupport_equiv {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ) :
    Equivalence (fun a b : Fin k => a = b ∨ ∃ γ ∈ Φ, γ a ≠ 0 ∧ γ b ≠ 0) := by
  refine ⟨fun a => Or.inl rfl, fun {a b} h => ?_, fun {a b c} hab hbc => ?_⟩
  · rcases h with rfl | ⟨γ, hγ, ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨γ, hγ, hb, ha⟩
  · rcases hab with rfl | ⟨γ, hγ, ha, hb⟩
    · exact hbc
    · by_cases hab' : a = b
      · rw [hab']; exact hbc
      · rcases hbc with rfl | ⟨δ, hδ, hb', hc⟩
        · exact Or.inr ⟨γ, hγ, ha, hb⟩
        · by_cases hbc' : b = c
          · rw [← hbc']; exact Or.inr ⟨γ, hγ, ha, hb⟩
          · by_cases hac : a = c
            · exact Or.inl hac
            · have hγr := hΦ.1 hγ
              have hδr := hΦ.1 hδ
              have hγa := ggDRootSet_eq_zero hδr hbc' hb' hc hab' hac
              have hγc := ggDRootSet_eq_zero hγr hab' ha hb (Ne.symm hac) (Ne.symm hbc')
              have hdot : ggDDot γ δ ≠ 0 := by
                rw [ggDRootSet_dot_eq hγr hab' ha hb δ, hγa, mul_zero, zero_add]
                exact mul_ne_zero hb hb'
              exact Or.inr ⟨ggDReflect δ γ, hΦ.2 δ hδ γ hγ, by
                rw [ggDReflect_apply, hγa, mul_zero, sub_zero]
                exact ha, by
                rw [ggDReflect_apply, hγc, zero_sub]
                exact neg_ne_zero.mpr (mul_ne_zero hdot hc)⟩

theorem ggD_eq_pm_of_supp {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {γ δ : Fin k → ℤ} (hγ : γ ∈ Φ) (hδ : δ ∈ Φ) {a b : Fin k} (hab : a ≠ b)
    (ha : γ a ≠ 0) (hb : γ b ≠ 0) (ha' : δ a ≠ 0) (hb' : δ b ≠ 0) :
    δ = γ ∨ δ = -γ := by
  by_cases h0 : ggDDot γ δ = 0
  · exfalso
    have hγr := hΦ.1 hγ
    have hδr := hΦ.1 hδ
    rcases ggDRootSet_orth hγr hδr h0 with ⟨a', b', S, ha'b', hS, hγ', hδ'⟩ |
      ⟨a', b', c', d', s, s', u, u', -, -, hac, had, hbc, hbd, -, -, -, -, hγe, hδe⟩
    · have h1 : Pi.single a' 1 + Pi.single b' S ∈ Φ := by
        rcases hγ' with rfl | rfl
        · exact hγ
        · simpa using hΦ.neg_mem hγ
      have h2 : Pi.single a' 1 - Pi.single b' S ∈ Φ := by
        rcases hδ' with rfl | rfl
        · exact hδ
        · simpa using hΦ.neg_mem hδ
      rcases hS with rfl | rfl
      · exact hss a' b' ha'b' ⟨h1, h2⟩
      · rw [Pi.single_neg, ← sub_eq_add_neg] at h1
        rw [Pi.single_neg, sub_neg_eq_add] at h2
        exact hss a' b' ha'b' ⟨h2, h1⟩
    · have hz : γ a = 0 ∨ δ a = 0 := by
        rw [hγe, hδe]
        by_cases hxa : a = a'
        · exact Or.inr (hxa ▸ ggDPair_apply_of_ne hac had u u')
        by_cases hxb : a = b'
        · exact Or.inr (hxb ▸ ggDPair_apply_of_ne hbc hbd u u')
        exact Or.inl (ggDPair_apply_of_ne hxa hxb s s')
      rcases hz with h | h
      · exact ha h
      · exact ha' h
  · have hγr := hΦ.1 hγ
    have hδr := hΦ.1 hδ
    rw [ggDRootSet_dot_eq hγr hab ha hb] at h0
    rw [ggDRootSet_eq_single_add_single hγr hab ha hb,
      ggDRootSet_eq_single_add_single hδr hab ha' hb']
    rcases ggDRootSet_sign hγr ha with h1 | h1 <;>
      rcases ggDRootSet_sign hγr hb with h2 | h2 <;>
      rcases ggDRootSet_sign hδr ha' with h3 | h3 <;>
      rcases ggDRootSet_sign hδr hb' with h4 | h4 <;>
      rw [h1, h2, h3, h4] <;> rw [h1, h2, h3, h4] at h0 <;>
      first
      | (left; rfl)
      | (right; simp only [Pi.single_neg, neg_add, neg_neg]; done)
      | (norm_num at h0)

theorem ggD_exists_signedA {k : ℕ} (hk : 2 ≤ k) {Φ : Set (Fin k → ℤ)}
    (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    (hpair : ∀ a b : Fin k, a ≠ b → ∃ γ ∈ Φ, γ a ≠ 0 ∧ γ b ≠ 0) :
    ∃ ε : Fin k → ℤ, (∀ a, ε a = 1 ∨ ε a = -1) ∧
      Φ = {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)} := by
  let a0 : Fin k := ⟨0, by omega⟩
  have hroot : ∀ c : Fin k, c ≠ a0 → ∃ γ : Fin k → ℤ, γ ∈ Φ ∧ γ a0 ≠ 0 ∧ γ c ≠ 0 :=
    fun c hc => hpair a0 c (Ne.symm hc)
  choose γ₀ hγ₀ using hroot
  let ρ : (c : Fin k) → c ≠ a0 → Fin k → ℤ :=
    fun c hc => if γ₀ c hc a0 = 1 then γ₀ c hc else -γ₀ c hc
  have hρmem : ∀ c hc, ρ c hc ∈ Φ := by
    intro c hc
    dsimp only [ρ]
    split_ifs with h
    · exact (hγ₀ c hc).1
    · exact hΦ.neg_mem (hγ₀ c hc).1
  have hρroot : ∀ c hc, ρ c hc ∈ ggDRootSet k := fun c hc => hΦ.1 (hρmem c hc)
  have hρa0 : ∀ c hc, ρ c hc a0 = 1 := by
    intro c hc
    have hs := ggDRootSet_sign (hΦ.1 (hγ₀ c hc).1) (hγ₀ c hc).2.1
    dsimp only [ρ]
    split_ifs with h
    · exact h
    · rcases hs with h1 | h1
      · exact absurd h1 h
      · simp only [Pi.neg_apply, h1, neg_neg]
  have hρc : ∀ c hc, ρ c hc c ≠ 0 := by
    intro c hc
    dsimp only [ρ]
    split_ifs with h
    · exact (hγ₀ c hc).2.2
    · exact neg_ne_zero.mpr (hγ₀ c hc).2.2
  have hρsign : ∀ c hc, ρ c hc c = 1 ∨ ρ c hc c = -1 :=
    fun c hc => ggDRootSet_sign (hρroot c hc) (hρc c hc)
  let ε : Fin k → ℤ := fun a => if h : a = a0 then 1 else -(ρ a h) a
  have hεa0 : ε a0 = 1 := by simp only [ε, dif_pos rfl]
  have hεc : ∀ c (hc : c ≠ a0), ε c = -(ρ c hc) c := fun c hc => by
    simp only [ε, dif_neg hc]
  have hεsign : ∀ a, ε a = 1 ∨ ε a = -1 := by
    intro a
    by_cases ha : a = a0
    · rw [ha, hεa0]; exact Or.inl rfl
    · rw [hεc a ha]
      rcases hρsign a ha with h | h <;> rw [h] <;> norm_num
  have hεne : ∀ a, ε a ≠ 0 := by
    intro a
    rcases hεsign a with h | h <;> rw [h] <;> norm_num
  have hρeq : ∀ c hc, ρ c hc = Pi.single a0 (1 : ℤ) + Pi.single c ((ρ c hc) c) := by
    intro c hc
    simpa only [hρa0 c hc] using ggDRootSet_eq_single_add_single (hρroot c hc)
      (Ne.symm hc) (by rw [hρa0]; norm_num) (hρc c hc)
  have hmem : ∀ a b : Fin k, a ≠ b →
      Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ := by
    intro a b hab
    by_cases ha : a = a0
    · have hb : b ≠ a0 := by rintro rfl; exact hab ha
      rw [ha, hεa0, hεc b hb, Pi.single_neg, sub_neg_eq_add, ← hρeq b hb]
      exact hρmem b hb
    · by_cases hb : b = a0
      · rw [hb, hεa0, hεc a ha]
        have heq : -(ρ a ha) = Pi.single a (-(ρ a ha) a) - Pi.single a0 1 := by
          conv_lhs => rw [hρeq a ha]
          rw [Pi.single_neg]
          abel
        rw [← heq]
        exact hΦ.neg_mem (hρmem a ha)
      · have hdot : ggDDot (ρ b hb) (ρ a ha) = 1 := by
          rw [ggDRootSet_dot_eq (hρroot b hb) (Ne.symm hb) (by rw [hρa0]; norm_num)
            (hρc b hb)]
          have hb0 : (ρ a ha) b = 0 :=
            ggDRootSet_eq_zero (hρroot a ha) (Ne.symm ha) (by rw [hρa0]; norm_num)
              (hρc a ha) hb (Ne.symm hab)
          rw [hρa0 b hb, hρa0 a ha, hb0, mul_zero, add_zero, mul_one]
        have hrefl : ggDReflect (ρ a ha) (ρ b hb) =
            Pi.single a (-(ρ a ha) a) - Pi.single b (-(ρ b hb) b) := by
          conv_lhs => rw [ggDReflect, hdot, one_smul, hρeq b hb, hρeq a ha]
          rw [Pi.single_neg, Pi.single_neg]
          abel
        rw [hεc a ha, hεc b hb, ← hrefl]
        exact hΦ.2 (ρ a ha) (hρmem a ha) (ρ b hb) (hρmem b hb)
  refine ⟨ε, hεsign, ?_⟩
  ext η
  refine ⟨fun hη => ?_, fun hη => ?_⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair (hΦ.1 hη)
    have h0 := hmem a b hab
    have h0a : (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) a ≠ 0 := by
      rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero]
      exact hεne a
    have h0b : (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) b ≠ 0 := by
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_sub]
      exact neg_ne_zero.mpr (hεne b)
    rcases ggD_eq_pm_of_supp hΦ hss h0 hη hab h0a h0b ha hb with h | h
    · exact ⟨a, b, hab, h⟩
    · refine ⟨b, a, hab.symm, ?_⟩
      rw [h]
      abel
  · obtain ⟨a, b, hab, rfl⟩ := hη
    exact hmem a b hab

theorem ggDReflect_supp_ne_zero {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) {r a b : Fin k} (har : a ≠ r) (hbr : b ≠ r) (hab : a ≠ b)
    (hγr : γ r ≠ 0) (hγa : γ a ≠ 0) (hδr : δ r ≠ 0) (hδb : δ b ≠ 0) :
    ggDReflect γ δ a ≠ 0 ∧ ggDReflect γ δ b ≠ 0 := by
  have hδa : δ a = 0 :=
    ggDRootSet_eq_zero hδ (Ne.symm hbr) hδr hδb har hab
  have hγb : γ b = 0 :=
    ggDRootSet_eq_zero hγ (Ne.symm har) hγr hγa hbr (Ne.symm hab)
  have hdot : ggDDot γ δ ≠ 0 := by
    rw [ggDRootSet_dot_eq hγ (Ne.symm har) hγr hγa δ, hδa, mul_zero, add_zero]
    exact mul_ne_zero hγr hδr
  constructor
  · rw [ggDReflect_apply, hδa, ggDDot_comm, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hdot hγa)
  · rw [ggDReflect_apply, hγb, mul_zero, sub_zero]
    exact hδb

theorem ggDk_memberRoots_L_phan
    (hGen : GGSecFiveGenPhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι} (hM : M = (ggCoxeterMatrixD k).reindex σ)
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) :
    Nat.card Bs = p ^ k ∧ ∃ ε : Fin k → ℤ, (∀ a, ε a = 1 ∨ ε a = -1) ∧
      ggDMemberRoots e φ L =
        {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)} ∧
      ∃ xb : ↥Bs, (xb : G) = x ∧ ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η →
        ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) ↔ ggDDot ε η = 0) := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hk1 : k ≠ 1 := by omega
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
  have hW : GGWeylOfType p (ggCoxeterMatrixD k) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hΦ : GGDSubsys k (ggDMemberRoots e φ L) := ggDMemberRoots_subsys hk2 φ L
  have hssL := hss L (Or.inl rfl)
  let a0 : Fin k := ⟨0, by omega⟩
  let rel : Fin k → Fin k → Prop :=
    fun a b => a = b ∨ ∃ γ ∈ ggDMemberRoots e φ L, γ a ≠ 0 ∧ γ b ≠ 0
  have heq : Equivalence rel := ggDSupport_equiv hΦ
  let st : Setoid (Fin k) := ⟨rel, heq⟩
  let rep : Fin k → Fin k := fun a => Quotient.out (Quotient.mk st a)
  have rep_rel : ∀ a, rel a (rep a) := by
    intro a
    exact heq.symm (Quotient.exact (Quotient.out_eq (Quotient.mk st a)))
  have rep_idem : ∀ a, rep (rep a) = rep a := by
    intro a
    exact congrArg Quotient.out (Quotient.out_eq (Quotient.mk st a))
  have rel_rep : ∀ {a b : Fin k}, rel a b → rep a = rep b := by
    intro a b h
    exact congrArg Quotient.out (Quotient.sound h)
  let S : Finset (Fin k) := Finset.univ.image rep
  let F : Finset (Fin k) := Finset.univ \ S
  have hFmem : ∀ x, x ∈ F ↔ rep x ≠ x := by
    intro x
    constructor
    · intro hx
      have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
      intro hxx
      exact hxS (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hxx⟩)
    · intro hxx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
      intro hxS
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hxS
      exact hxx (by rw [← hy]; exact rep_idem y)
  have hroot : ∀ x : F, ∃ (t : M.Group) (γ : Fin k → ℤ), GGDReflRoot k (φ t) γ ∧
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
      γ (rep x.1) ≠ 0 ∧ γ x.1 ≠ 0 := by
    intro x
    have hxF : rep x.1 ≠ x.1 := (hFmem x.1).mp x.2
    rcases heq.symm (rep_rel x.1) with h | ⟨γ, hγ, hrep, hxx⟩
    · exact absurd h hxF
    · obtain ⟨t, ht, htL⟩ := hγ
      exact ⟨t, γ, ht, htL, hrep, hxx⟩
  choose t γ ht htL hγrep hγx using hroot
  let R0 : Finset (MulAut ↥Bs) :=
    F.attach.image fun x => ((e (t x) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  have hR : ∀ r ∈ R0, GGIsReflection p r := by
    intro r hr
    dsimp only [R0] at hr
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hr
    exact ggCoxRefl_isReflection hpres.2
      (mem_ggCoxRefl_of_ggDReflRoot e φ hφ (ht x))
  have hgen : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      r ∈ Subgroup.closure (R0 : Set (MulAut ↥Bs)) := by
    intro r hrA hrR
    obtain ⟨w, i, hwi⟩ := hrR
    obtain ⟨δ, hδ⟩ := exists_ggDReflRoot_of_conj φ hφ w i
    have hδΦ : δ ∈ ggDMemberRoots e φ L := ⟨w * M.simple i * w⁻¹, hδ, hwi ▸ hrA⟩
    obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair (hδ.mem hk1)
    have hrepab : rep a = rep b := rel_rep (Or.inr ⟨δ, hδΦ, ha, hb⟩)
    have hin : ∀ x : F, ((e (t x) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        Subgroup.closure (R0 : Set (MulAut ↥Bs)) := fun x => by
      refine Subgroup.subset_closure ?_
      dsimp only [R0]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_attach F x, rfl⟩
    by_cases hb_rep : b = rep a
    · have haF : a ∈ F := (hFmem a).mpr (by rw [← hb_rep]; exact Ne.symm hab)
      let xa : F := ⟨a, haF⟩
      have hsign : δ = γ xa ∨ δ = -γ xa :=
        ggD_eq_pm_of_supp hΦ hssL (γ := γ xa) (δ := δ) (hγ := ⟨t xa, ht xa, htL xa⟩) (hδ := hδΦ)
          (a := rep a) (b := a) (hab := by rw [← hb_rep]; exact Ne.symm hab)
          (ha := hγrep xa) (hb := hγx xa) (ha' := hb_rep ▸ hb) (hb' := ha)
      have hsign' : γ xa = δ ∨ γ xa = -δ := by
        rcases hsign with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; simp)
      have huu : w * M.simple i * w⁻¹ = t xa :=
        φ.injective (GGDReflRoot.unique hk2 hδ (ht xa) hsign')
      rw [hwi, huu]
      exact hin xa
    · by_cases ha_rep : a = rep b
      · have hbF : b ∈ F := (hFmem b).mpr (fun h => hb_rep (h.symm.trans hrepab.symm))
        let xb : F := ⟨b, hbF⟩
        have hsign : δ = γ xb ∨ δ = -γ xb :=
          ggD_eq_pm_of_supp hΦ hssL (γ := γ xb) (δ := δ) (hγ := ⟨t xb, ht xb, htL xb⟩) (hδ := hδΦ)
            (a := rep b) (b := b) (hab := by rw [← ha_rep]; exact hab)
            (ha := hγrep xb) (hb := hγx xb) (ha' := ha_rep ▸ ha) (hb' := hb)
        have hsign' : γ xb = δ ∨ γ xb = -δ := by
          rcases hsign with h | h
          · exact Or.inl h.symm
          · exact Or.inr (by rw [h]; simp)
        have huu : w * M.simple i * w⁻¹ = t xb :=
          φ.injective (GGDReflRoot.unique hk2 hδ (ht xb) hsign')
        rw [hwi, huu]
        exact hin xb
      · have haF : a ∈ F := (hFmem a).mpr (fun h => ha_rep (h ▸ hrepab))
        have hbF : b ∈ F := (hFmem b).mpr (fun h => hb_rep (h.symm.trans hrepab.symm))
        let xa : F := ⟨a, haF⟩
        let xb : F := ⟨b, hbF⟩
        have hγaΦ : γ xa ∈ ggDMemberRoots e φ L := ⟨t xa, ht xa, htL xa⟩
        have hγbΦ : γ xb ∈ ggDMemberRoots e φ L := ⟨t xb, ht xb, htL xb⟩
        have hSupp : ggDReflect (γ xa) (γ xb) a ≠ 0 ∧
            ggDReflect (γ xa) (γ xb) b ≠ 0 :=
          ggDReflect_supp_ne_zero (hΦ.1 hγaΦ) (hΦ.1 hγbΦ) (r := rep b) ha_rep
            ((hFmem b).mp hbF).symm hab (hrepab ▸ hγrep xa) (hγx xa) (hγrep xb) (hγx xb)
        have hsign : δ = ggDReflect (γ xa) (γ xb) ∨
            δ = -ggDReflect (γ xa) (γ xb) :=
          ggD_eq_pm_of_supp hΦ hssL (γ := ggDReflect (γ xa) (γ xb)) (δ := δ)
            (hγ := hΦ.2 (γ xa) hγaΦ (γ xb) hγbΦ) (hδ := hδΦ) (a := a) (b := b) (hab := hab)
            (ha := hSupp.1) (hb := hSupp.2) (ha' := ha) (hb' := hb)
        have hsign' : ggDReflect (γ xa) (γ xb) = δ ∨
            ggDReflect (γ xa) (γ xb) = -δ := by
          rcases hsign with h | h
          · exact Or.inl h.symm
          · exact Or.inr (by rw [h]; simp)
        have hc : GGDReflRoot k (φ (t xa) * φ (t xb) * (φ (t xa))⁻¹)
            (ggDReflect (γ xa) (γ xb)) := (ht xb).conj ((ht xa).action hk2)
        have hc' : GGDReflRoot k (φ (t xa * t xb * (t xa)⁻¹))
            (ggDReflect (γ xa) (γ xb)) := by
          simpa only [map_mul, map_inv] using hc
        have huu : w * M.simple i * w⁻¹ = t xa * t xb * (t xa)⁻¹ :=
          φ.injective (GGDReflRoot.unique hk2 hδ hc' hsign')
        rw [hwi, huu]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (mul_mem (hin xa) (hin xb)) (inv_mem (hin xa))
  have hR0card : R0.card ≤ F.card := by
    dsimp only [R0]
    simpa using Finset.card_image_le (s := F.attach)
      (f := fun x : F => ((e (t x) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
  have hup : Nat.card Bs ≤ p ^ (R0.card + 1) :=
    ggPhan_card_bstar_le hGen hcfg hns hpres hle3 hbig R0 hR hgen
  have hlow : p ^ k ≤ Nat.card Bs := ggDk_card_bstar_ge hcfg hpres hk hM
  have hall : ∀ a b : Fin k, rel a b := by
    by_contra hno
    push Not at hno
    obtain ⟨a₁, b₁, hnot⟩ := hno
    have hrepne : rep a₁ ≠ rep b₁ := by
      intro h
      exact hnot (heq.trans (rep_rel a₁) (heq.symm (h.symm ▸ rep_rel b₁)))
    have hFcard : F.card ≤ k - 2 := by
      have hr1 : rep a₁ ∈ S := Finset.mem_image.mpr ⟨a₁, Finset.mem_univ a₁, rfl⟩
      have hr2 : rep b₁ ∈ S := Finset.mem_image.mpr ⟨b₁, Finset.mem_univ b₁, rfl⟩
      have hsub : F ⊆ Finset.univ \ ({rep a₁, rep b₁} : Finset (Fin k)) := by
        intro c hc
        have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, ?_⟩
        intro hcp
        rcases Finset.mem_insert.mp hcp with h | h
        · exact hcS (h.symm ▸ hr1)
        · exact hcS ((Finset.mem_singleton.mp h).symm ▸ hr2)
      calc F.card ≤ (Finset.univ \ ({rep a₁, rep b₁} : Finset (Fin k))).card :=
            Finset.card_le_card hsub
        _ = k - 2 := by
            rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
              Finset.card_pair hrepne]
    have hle1 : Nat.card Bs ≤ p ^ (F.card + 1) :=
      le_trans hup (Nat.pow_le_pow_right hp.pos (by omega))
    have hle2 : p ^ (F.card + 1) ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (le_trans hlow (le_trans hle1 hle2)) (not_le.mpr hlt)
  have hrepconst : ∀ a : Fin k, rep a = rep a0 := fun a => rel_rep (hall a a0)
  have hSsingle : S = {rep a0} := by
    ext c
    constructor
    · intro hc
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hc
      rw [Finset.mem_singleton]
      rw [← hy, hrepconst y]
    · intro hc
      rw [Finset.mem_singleton] at hc
      exact Finset.mem_image.mpr ⟨a0, Finset.mem_univ a0, hc.symm⟩
  have hFcard : F.card = k - 1 := by
    dsimp only [F]
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, hSsingle, Finset.inter_univ,
      Finset.card_singleton]
  have hcard : Nat.card Bs = p ^ k := by
    refine le_antisymm ?_ hlow
    calc Nat.card Bs ≤ p ^ (R0.card + 1) := hup
      _ ≤ p ^ (k - 1 + 1) := by
          rw [← hFcard]
          exact Nat.pow_le_pow_right hp.pos (by omega)
      _ = p ^ k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hpairAll : ∀ a b : Fin k, a ≠ b →
      ∃ γ ∈ ggDMemberRoots e φ L, γ a ≠ 0 ∧ γ b ≠ 0 := by
    intro a b hab
    rcases hall a b with h | h
    · exact absurd h hab
    · exact h
  obtain ⟨ε, hε, hset⟩ := ggD_exists_signedA hk2 hΦ hssL hpairAll
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hcfg.1.1.1.2.2.2.2.2.2.1
  let xb : ↥Bs := ⟨x, hcfg.1.1.2.1.1 hxB⟩
  have hfix : ∀ (u : M.Group) (γ : Fin k → ℤ), GGDReflRoot k (φ u) γ → ggDDot ε γ = 0 →
      (((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) := by
    intro u γ hu h0
    obtain ⟨a, b, hab, rfl⟩ := eq_signedA_of_ggDDot_eq_zero hε (hu.mem hk1) h0
    have hγΦ : Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ L := by
      rw [hset]
      exact ⟨a, b, hab, rfl⟩
    obtain ⟨t, ht, htL⟩ := hγΦ
    rw [φ.injective (hu.unique hk2 ht (Or.inl rfl))]
    exact ggAutomizer_apply_eq_of_le_centralizer (x := xb) hLcomp.1 htL
  refine ⟨hcard, ε, hε, hset, xb, rfl, fun u γ hu => ⟨fun hx => ?_, hfix u γ hu⟩⟩
  by_contra h0
  let H : Subgroup (ggWeylD k) := (MulAction.stabilizer (MulAut ↥Bs) xb).comap
    ((ggAutomizerJoin L Bs 𝒦).subtype.comp (e.toMonoidHom.comp φ.symm.toMonoidHom))
  have hH : ∀ w, w ∈ H ↔ ((e (φ.symm w) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb :=
    fun w => Iff.rfl
  have htop := ggDk_eq_top_of_signedA hk hε (H := H) (fun t γ ht hγ => (hH t).2
    (hfix (φ.symm t) γ (by rwa [MulEquiv.apply_symm_apply]) hγ)) hu h0
    ((hH (φ u)).2 (by rwa [MulEquiv.symm_apply_apply]))
  have hb : ∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ xb = xb := fun ψ hψ => by
    have h := (hH (φ (e.symm ⟨ψ, hψ⟩))).1 (by rw [htop]; exact Subgroup.mem_top _)
    rwa [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at h
  exact hx1 (congrArg Subtype.val (ggWeylD_eq_one_of_fixed hp hp2
    (ggRouteCfg_isElemAbelian hcfg) (ggRouteCfg_noTransvection hcfg) hk hW
    (fun ψ hψ => mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hψ))
    hcard hb))

end CFSG.StandardType

end
