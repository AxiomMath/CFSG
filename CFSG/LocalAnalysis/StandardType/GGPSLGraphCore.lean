module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphBlockSolvable
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphNonsolvableBlock
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphSettingOfHyps
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphThetaNeOne
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphTorusBound
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphTypes
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphOrbitData

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pslGraph_core {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Group.IsSolvable ↥(pslChat B) := by
  classical
  by_contra hns
  obtain ⟨P, hP, hstar⟩ := pslGraph_primFamily S
  obtain ⟨e0, he0P, he0ns⟩ := pslGraph_exists_nonsolvable_block P hP hns
  have he0star : formAdj (RingHom.id K) G e0 = e0 := by
    by_contra h
    exact he0ns (pslGraph_typeIII_solvable S P hP e0 he0P h)
  have he0I : pslTypeI G B e0 := by
    by_contra hI
    have hII : pslTypeII G B e0 := by
      refine ⟨he0star, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hI ⟨he0star, hcon⟩
    exact he0ns (pslGraph_typeII_solvable S P hP e0 he0P hII)
  obtain ⟨hrk0, hq0⟩ := pslGraph_typeI_two S P hP e0 he0P he0I he0ns
  obtain ⟨e1, he1P, he1nI⟩ := pslGraph_exists_not_typeI S P hP
  have hbound := pslGraph_torus_bound S
  obtain ⟨R, hRP, hRtrans, hnorm, hdim, hRdata⟩ := pslGraph_orbit_data S P hP hstar
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf1, hf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨(m : ℕ), PNat.one_le m, by rw [Nat.card_eq_fintype_card, hm]⟩
  let kind : Matrix (Fin n) (Fin n) K → ℕ := fun r =>
    if pslTypeI G B r then 0 else if pslTypeII G B r then 1 else 2
  have hk2 : ∀ r, kind r = 2 ↔ formAdj (RingHom.id K) G r ≠ r := by
    intro r
    constructor
    · intro hr hstarr
      by_cases hI : pslTypeI G B r
      · simp [kind, hI] at hr
      · by_cases hII : pslTypeII G B r
        · simp [kind, hI, hII] at hr
        · apply hII
          refine ⟨hstarr, ?_⟩
          by_contra hcon
          push Not at hcon
          exact hI ⟨hstarr, hcon⟩
    · intro hne
      have hI : ¬ pslTypeI G B r := fun h => hne h.1
      have hII : ¬ pslTypeII G B r := fun h => hne h.1
      simp [kind, hI, hII]
  have hk1 : ∀ r, kind r = 1 ↔ pslTypeII G B r := by
    intro r
    constructor
    · intro hr
      by_cases hI : pslTypeI G B r
      · simp [kind, hI] at hr
      · by_cases hII : pslTypeII G B r
        · exact hII
        · simp [kind, hI, hII] at hr
    · intro hII
      have hI : ¬ pslTypeI G B r := by
        intro hI
        obtain ⟨-, a, ha, hne⟩ := hII
        exact hne (hI.2 a ha)
      simp [kind, hI, hII]
  have hk0 : ∀ r, kind r = 0 ↔ pslTypeI G B r := by
    intro r
    by_cases hI : pslTypeI G B r
    · simp [kind, hI]
    · by_cases hII : pslTypeII G B r <;> simp [kind, hI, hII]
  have hkle : ∀ r, kind r ≤ 2 := by
    intro r
    by_cases hI : pslTypeI G B r <;> by_cases hII : pslTypeII G B r <;> simp [kind, hI, hII]
  have hnotI_solv : ∀ r ∈ P, ¬ pslTypeI G B r → Group.IsSolvable ↥(pslBlock B r) := by
    intro r hr hnI
    by_cases hs : formAdj (RingHom.id K) G r = r
    · refine pslGraph_typeII_solvable S P hP r hr ⟨hs, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hnI ⟨hs, hcon⟩
    · exact pslGraph_typeIII_solvable S P hP r hr hs
  refine pslGraph_arith (Nat.card K) n f hf hf1 R kind
    (fun r => blockDegree (pslAlg B) r) (fun r => Matrix.rank r)
    (fun r _ => hkle r) (fun r hr => (hRdata r hr).2.1)
    (fun r hr h1 => (hRdata r hr).2.2.2 ((hk1 r).1 h1)) ?_ ?_ ?_ ?_ ?_
  ·
    refine hdim.trans (Finset.sum_congr rfl (fun r _ => ?_))
    by_cases h : formAdj (RingHom.id K) G r = r
    · have : ¬ kind r = 2 := fun h2 => (hk2 r).1 h2 h
      simp [h, this]
    · have := (hk2 r).2 h
      simp [h, this]
  ·
    have := hbound
    rw [hnorm] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [pslRho]
    by_cases h : pslTypeII G B r
    · simp [h, (hk1 r).2 h]
    · have : ¬ kind r = 1 := fun h1 => h ((hk1 r).1 h1)
      simp [h, this]
  ·
    refine ⟨e0, ?_, (hk0 e0).2 he0I, hrk0, hq0⟩
    obtain ⟨r, ⟨hrR, hr⟩, -⟩ := hRtrans e0 he0P
    rcases hr with rfl | hr
    · exact hrR
    · rw [he0star] at hr; rw [← hr]; exact hrR
  ·
    obtain ⟨r, ⟨hrR, hr⟩, -⟩ := hRtrans e1 he1P
    refine ⟨r, hrR, ?_⟩
    rw [Ne, hk0]
    rcases hr with rfl | hr
    · exact he1nI
    · rw [hr]
      intro h
      exact he1nI ((pslGraph_typeI_star S e1).1 h)
  ·
    intro r hr hkr h4
    have hnI : ¬ pslTypeI G B r := fun h => hkr ((hk0 r).2 h)
    have hsolv := hnotI_solv r (hRP hr) hnI
    rcases pslGraph_block_solvable_cases S P hP r (hRP hr) hsolv with h | ⟨-, h2⟩
    · exact h
    · exfalso
      have h4' : 4 ≤ Nat.card K ^ blockDegree (pslAlg B) r := h4
      rw [h2] at h4'
      omega


theorem pslGraphNone_holds : PSLGraphNone := by
  classical
  intro n K _ _ _ hn A B α hα2 hodd hcomm hfix L₁ hL₁
  obtain ⟨G, hS⟩ := pslGraph_setting_of_hyps hn A B hα2 hodd hcomm hfix
  haveI : Group.IsSolvable ↥(pslChat B) := pslGraph_core hS
  have hle : L₁ ≤ (pslChat B).map (proj n K) := by
    intro g hg
    obtain ⟨x, rfl⟩ := proj_surjective n K g
    refine ⟨x, ?_, rfl⟩
    exact hL₁ _ hg
  haveI : Group.IsSolvable ↥((pslChat B).map (proj n K)) :=
    solvable_of_surjective (MonoidHom.subgroupMap_surjective (proj n K) (pslChat B))
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

end CFSG.StandardType
