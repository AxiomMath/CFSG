module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.GroupTheory.CoprimeSectionStability
public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem frattini_map_subtype_ne_of_ne_bot (Q : Subgroup G) (hne : Q ≠ ⊥) :
    (frattini ↥Q).map Q.subtype ≠ Q := by
  intro hΦQ
  apply hne
  have htop : frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective Q.subtype_injective
    have h1 : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1]
    exact hΦQ
  have h := frattini_nongenerating (G := ↥Q) (K := (⊥ : Subgroup ↥Q))
    (by rw [htop, sup_top_eq])
  rw [eq_bot_iff]
  intro q hq
  have : (⟨q, hq⟩ : ↥Q) ∈ (⊥ : Subgroup ↥Q) := by rw [h]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

private theorem exists_chief_step49 {H Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQH : H ≤ Subgroup.normalizer (Q : Set G)) (hne : Q ≠ ⊥) :
    ∃ M : Subgroup G, M ≤ Q ∧ M ≠ Q ∧ H ≤ Subgroup.normalizer (M : Set G) ∧ HChief H Q M := by
  classical
  set Φ : Subgroup G := (frattini Q).map Q.subtype with hΦdef
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hΦH : H ≤ Subgroup.normalizer (Φ : Set G) := fun h hh => by
    rw [hΦdef]
    exact CFSG.RankThree.GF2n.mem_normalizer_map_subtype_of_characteristic (hQH hh) (frattini Q)
  have hΦne : Φ ≠ Q := fun hΦQ' =>
    frattini_map_subtype_ne_of_ne_bot Q hne (hΦdef.symm.trans hΦQ')
  obtain ⟨M, hΦM, hmax⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Φ ≤ Y ∧ Y ≤ Q ∧ Y ≠ Q ∧ H ≤ Subgroup.normalizer (Y : Set G))
    ⟨le_rfl, hΦQ, hΦne, hΦH⟩
  obtain ⟨-, hMQ, hMne, hMH⟩ := hmax.prop
  haveI : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hcommΦ : ⁅Q, Q⁆ ≤ Φ := by
    rw [← Subgroup.map_subtype_commutator Q, hΦdef]
    exact Subgroup.map_mono (CFSG.commutator_le_frattini_of_isPGroup (p := 2) (R := Q))
  have hcommM : ⁅Q, Q⁆ ≤ M := hcommΦ.trans hΦM
  have hpowM : ∀ x ∈ Q, x ^ 2 ∈ M := by
    intro x hx
    have h2 : x ^ 2 ∈ Φ := by
      rw [hΦdef]
      exact Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : Q) ^ 2,
        CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (R := Q) (⟨x, hx⟩ : Q), rfl⟩
    exact hΦM h2
  refine ⟨M, hMQ, hMne, hMH, ?_⟩
  refine ⟨lt_of_le_of_ne hMQ hMne, hQH, hMH, ?_, ?_, hpowM, ?_⟩
  · intro x hx y hy
    have hc : ⁅x, y⁆ ∈ M := (Subgroup.commutator_le.mp hcommM) x hx y (hMQ hy)
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]; group
    rw [hxy]
    exact M.mul_mem hc hy
  · intro x hx y hy
    exact (Subgroup.commutator_le.mp hcommM) x hx y hy
  · intro X hMX hXQ hXH
    by_cases hXeq : X = Q
    · exact Or.inr hXeq
    · exact Or.inl (hmax.eq_of_le ⟨hΦM.trans hMX, hXQ, hXeq, hXH⟩ hMX).symm

theorem chief_series49 {H Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQH : H ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ (n : ℕ) (N : ℕ → Subgroup G), N 0 = Q ∧ N n = ⊥ ∧ (∀ i < n, HChief H (N i) (N (i + 1))) := by
  classical
  suffices key : ∀ d : ℕ, ∀ Q' : Subgroup G, Nat.card Q' = d → IsPGroup 2 Q' →
      H ≤ Subgroup.normalizer (Q' : Set G) →
      ∃ (n : ℕ) (N : ℕ → Subgroup G), N 0 = Q' ∧ N n = ⊥ ∧
        (∀ i < n, HChief H (N i) (N (i + 1))) by
    exact key (Nat.card Q) Q rfl hQ hQH
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro Q' hcard hQ' hQ'H
    by_cases hbot : Q' = ⊥
    · exact ⟨0, fun _ => ⊥, by simp [hbot], by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · obtain ⟨M, hMQ', hMne, hMH, hchief⟩ := exists_chief_step49 hQ' hQ'H hbot
      obtain ⟨n, N, hN0, hNn, hNchief⟩ := ih (Nat.card M)
        (by rw [← hcard]; exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hMQ' hMne))
        M rfl (hQ'.to_le hMQ') hMH
      let N' : ℕ → Subgroup G :=
        fun i => Nat.rec (motive := fun _ => Subgroup G) Q' (fun j _ => N j) i
      have hN'0 : N' 0 = Q' := rfl
      have hN'succ : ∀ j, N' (j + 1) = N j := fun j => rfl
      refine ⟨n + 1, N', hN'0, ?_, ?_⟩
      · rw [hN'succ n, hNn]
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          rw [hN'0, hN'succ 0, hN0]
          exact hchief
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          rw [hN'succ j, hN'succ (j + 1)]
          exact hNchief j (by omega)

theorem wprod49 {Z Q : Subgroup G} (n : ℕ) (N : ℕ → Subgroup G) (h0 : N 0 = Q) (hn : N n = ⊥)
    (hanti : ∀ i < n, N (i + 1) ≤ N i)
    (hnormN : ∀ i < n, N i ≤ Subgroup.normalizer (N (i + 1) : Set G)) :
    ∏ i ∈ Finset.range n, wIdx Z (N i) (N (i + 1)) =
      (Q ⊓ Subgroup.centralizer (Z : Set G)).relIndex Q := by
  classical
  have key : ∀ i < n, wIdx Z (N i) (N (i + 1)) *
      (N (i + 1) ⊓ Subgroup.centralizer (Z : Set G)).relIndex (N (i + 1)) =
      (N i ⊓ Subgroup.centralizer (Z : Set G)).relIndex (N i) := by
    intro i hi
    have h := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul (D := Z)
      (N := N i) (M := N (i + 1)) (hanti i hi) (hnormN i hi)
    unfold wIdx
    rw [h]
    exact Nat.mul_comm _ _
  have tel : ∀ m ≤ n,
      (∏ i ∈ Finset.range m, wIdx Z (N i) (N (i + 1))) *
        (N m ⊓ Subgroup.centralizer (Z : Set G)).relIndex (N m) =
      (N 0 ⊓ Subgroup.centralizer (Z : Set G)).relIndex (N 0) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      rw [Finset.prod_range_succ, mul_assoc, key k hk']
      exact ih (by omega)
  have hmain := tel n le_rfl
  have hlast : (N n ⊓ Subgroup.centralizer (Z : Set G)).relIndex (N n) = 1 := by
    rw [hn]
    simp [Subgroup.relIndex_bot_right]
  rw [hlast, mul_one, h0] at hmain
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
