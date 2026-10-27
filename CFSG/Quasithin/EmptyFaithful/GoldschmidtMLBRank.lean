module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevel

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure YData (Y : Type) [Group Y] (U : Subgroup Y) (P : Fin 2 → Subgroup Y) : Prop where
  res : ResidualOvergroupsAt Y U P
  norm : ∀ j, Subgroup.normalizer (U : Set Y) ≤ P j
  charTwo : ∀ j, CharTwo (P j)
  le_perfectCore : ∀ j, U ≤ perfectCore (P j)
  inner : ∀ j, ∀ g ∈ P j, ∃ y ∈ perfectCore (P j), ∀ x ∈ perfectCore (P j),
    ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore (P j))
  solv : ∀ X : Subgroup Y, U ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (U : Set Y)

variable {Y : Type} [Group Y] {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

theorem YData.covBy (h : YData Y U P) (j : Fin 2) : P j ⋖ ⊤ :=
  (h.res.2.2.1 (P j) (h.res.2.1 j)).mpr ⟨j, rfl⟩

theorem YData.hall [Finite Y] (h : YData Y U P) (hU : IsSylowTwoOf U ⊤) (j : Fin 2) {x : Y}
    (hx : x ∈ leviCent (P j)) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 (P j) := by
  set Λ := perfectCore (P j) with hΛ
  have hxL := mem_leviCent.mp hx
  have hxP : x ∈ P j := hxL.1
  have hp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨m, hmP, hm⟩ := BenderStart.exists_mem_conj_mem_of_isSylowTwoOf hU (h.res.2.1 j)
    ((Subgroup.zpowers_le).mpr hxP) hp
  have hmN : m ∈ Subgroup.normalizer (P j : Set Y) := Subgroup.le_normalizer hmP
  have hxΛ : x ∈ Λ := by
    have h1 : m⁻¹ * x * m ∈ Λ := h.le_perfectCore j (hm x (Subgroup.mem_zpowers x))
    have h2 := conj_mem_perfectCore hmN h1
    simpa [mul_assoc] using h2
  have hΛP : Λ ≤ P j := perfectCore_le _
  have hRn : pCoreOf 2 Λ ≤ P j := (pCoreOf_le 2 Λ).trans hΛP
  have hxnR : x ∈ Subgroup.normalizer (pCoreOf 2 Λ : Set Y) :=
    localGroup_le_normalizer_pCoreOf 2 Λ hxΛ
  have hV : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ pCoreOf 2 Λ) :=
    hp.to_sup_of_normal_right' (pCoreOf_isPGroup 2 Λ) ((Subgroup.zpowers_le).mpr hxnR)
  have hVΛ : Subgroup.zpowers x ⊔ pCoreOf 2 Λ ≤ Λ :=
    sup_le ((Subgroup.zpowers_le).mpr hxΛ) (pCoreOf_le 2 Λ)
  have key : ∀ y ∈ Λ, (Subgroup.zpowers x ⊔ pCoreOf 2 Λ).map (MulAut.conj y).toMonoidHom ≤
      Subgroup.zpowers x ⊔ pCoreOf 2 Λ := by
    intro y hy
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · have hc : ⁅x, y⁆ ∈ pCoreOf 2 Λ := hxL.2 y hy
      have hc' : y * x * y⁻¹ = (⁅x, y⁆)⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      show y * x * y⁻¹ ∈ _
      rw [hc']
      exact mul_mem (Subgroup.mem_sup_right ((pCoreOf 2 Λ).inv_mem hc))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    · rintro _ ⟨z, hz, rfl⟩
      exact Subgroup.mem_sup_right (conj_mem_R (hΛP hy) hz)
  have hnorm : Λ ≤ Subgroup.normalizer
      ((Subgroup.zpowers x ⊔ pCoreOf 2 Λ : Subgroup Y) : Set Y) := fun y hy =>
    mem_normalizer_of_map_le (key y hy) (key y⁻¹ (Λ.inv_mem hy))
  have hxV := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hVΛ hnorm hV
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  exact CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hRn (le_normalizer_R (P j))
    (pCoreOf_isPGroup 2 Λ) hxV

theorem YData.lieLevel [Finite Y] (h : YData Y U P) (hU : IsSylowTwoOf U ⊤) :
    LieLevel (⊤ : Subgroup Y) U P where
  le_L _ := le_top
  S_le j := h.res.2.1 j
  ne := h.res.1
  ne_L j := (h.covBy j).lt.ne
  cover A hUA _ hA := by
    obtain ⟨M, hM, hAM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hA
    obtain ⟨j, hj⟩ := (h.res.2.2.1 M (hUA.trans hAM)).mp hM.covBy_top
    fin_cases j
    · exact Or.inl (hj ▸ hAM)
    · exact Or.inr (hj ▸ hAM)
  maxl j A hPA hA := (h.covBy j).eq_or_eq hPA hA
  solv01 := h.res.2.2.2.1
  nonsolv A hUA _ hA hns := by
    obtain ⟨j, hjk, hd⟩ := h.res.2.2.2.2.1 A hUA hA hns
    refine ⟨j, hjk, ?_⟩
    rw [← dInf_eq_perfectCore, ← hd]
    exact dInf_le A
  norm_le j := inf_le_right.trans (h.norm j)
  solv A hUA _ hs := h.solv A hUA hs
  charTwo := h.charTwo
  split j g hg := by
    obtain ⟨y, hy, hc⟩ := h.inner j g hg
    have hyP : y ∈ P j := perfectCore_le _ hy
    have hmem : g * y⁻¹ ∈ leviCent (P j) :=
      mem_leviCent.mpr ⟨(P j).mul_mem hg ((P j).inv_mem hyP), hc⟩
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (leviCent (P j) : Set Y) :=
      le_normalizer_leviCent (P j) (Subgroup.le_normalizer ((P j).inv_mem hyP))
    refine ⟨y, hy, y⁻¹ * g, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp hyinv (g * y⁻¹)).mp hmem
    simpa [mul_assoc] using this
  hall j _ hx _ hk := h.hall hU j hx hk

end CFSG.Quasithin.GoldMLB
