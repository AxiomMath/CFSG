module

public import CFSG.GroupTheory.SylowAutConj
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.CoprimeCentralizerTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

open scoped Pointwise

@[expose] def SylOddConcl (X : Type*) [Group X] [Finite X] (q p : ℕ) : Prop :=
  ∀ S : Subgroup X, IsPGroup q S → ¬ q ∣ S.index →
    (∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
        2 ≤ Open.pRank p (centralizer (E : Set X))) ∧
      ∀ α : MulAut X, (∃ k : ℕ, α ^ (q ^ k) = 1) → (∀ s ∈ S, α s ∈ S) →
        ∀ s ∈ S, s ^ q = 1 → α s = s

theorem SylOddConcl.of_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) {q p : ℕ} [Fact p.Prime] (h : SylOddConcl Y q p) : SylOddConcl X q p := by
  intro S hS hSi
  let S' : Subgroup Y := S.map e.toMonoidHom
  have hS' : IsPGroup q S' := hS.map e.toMonoidHom
  have hS'i : ¬ q ∣ S'.index := by
    change ¬ q ∣ (S.map e.toMonoidHom).index
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective S]
    exact hSi
  obtain ⟨⟨E', hE'S', hE'A, hE'q, hE'p⟩, hauto⟩ := h S' hS' hS'i
  let E : Subgroup X := E'.map e.symm.toMonoidHom
  have hES : E ≤ S := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hE'S'
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
      ext x
      simp
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  have hEA : IsElemAbelian q E := IsElemAbelian.map hE'A e.symm.toMonoidHom
  have hEq : Nat.card E = q ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE'q]
  have hEp : 2 ≤ Open.pRank p (centralizer (E : Set X)) := by
    change 2 ≤ Open.pRank p
      (centralizer (E'.map e.symm.toMonoidHom : Set X))
    rw [GroupTheory.CoprimeTransport.pRank_centralizer_map_mulEquiv e.symm E']
    exact hE'p
  refine ⟨⟨E, hES, hEA, hEq, hEp⟩, ?_⟩
  intro α hα hαS s hs hsq
  have hα' : ∃ k : ℕ, (MulAut.congr e α) ^ (q ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hα'S : ∀ y ∈ S', (MulAut.congr e α) y ∈ S' := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have hcongr : (MulAut.congr e α) (e.toMonoidHom t) = e.toMonoidHom (α t) := by
      simp [MulAut.congr_apply]
    rw [hcongr]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hαS t ht)
  have hfix := hauto (MulAut.congr e α) hα' hα'S (e s)
    (Subgroup.mem_map_of_mem e.toMonoidHom hs) (by rw [← map_pow, hsq, map_one])
  simpa using e.injective hfix

theorem sylOddConcl_of_torus {X : Type*} [Group X] [Finite X] {q p : ℕ} [Fact q.Prime]
    [Fact p.Prime] {S₀ E₀ : Subgroup X} (hS₀ : IsPGroup q S₀) (hS₀i : ¬ q ∣ S₀.index)
    (hS₀c : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) (hE₀S₀ : E₀ ≤ S₀) (hE₀ : IsElemAbelian q E₀)
    (hE₀q : Nat.card E₀ = q ^ 2) (hE₀p : 2 ≤ Open.pRank p (centralizer (E₀ : Set X)))
    {Φ : MulAut X} (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hΦS : ∀ s ∈ S₀, Φ s ∈ S₀) {m a : ℕ} (hm : ¬ q ∣ m) (hΦm : Φ ^ (q ^ a * m) = 1)
    (hΦfix : ∀ s ∈ S₀, s ^ q = 1 → (Φ ^ m) s = s) : SylOddConcl X q p := by
  intro S hS hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hS₀.toSylow hS₀i) (hS.toSylow hSi)
  have hSmap : S = S₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : (↑(g • (hS₀.toSylow hS₀i)) : Subgroup X) = S := by
      rw [hg]
      simp
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    congr 1
  let E : Subgroup X := E₀.map (MulAut.conj g).toMonoidHom
  have hES : E ≤ S := by
    rw [hSmap]
    exact Subgroup.map_mono hE₀S₀
  have hEA : IsElemAbelian q E := IsElemAbelian.map hE₀ (MulAut.conj g).toMonoidHom
  have hEq : Nat.card E = q ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀q]
  have hEp : 2 ≤ Open.pRank p (centralizer (E : Set X)) := by
    change 2 ≤ Open.pRank p
      (centralizer (E₀.map (MulAut.conj g).toMonoidHom : Set X))
    rw [GroupTheory.CoprimeTransport.pRank_centralizer_map_mulEquiv (MulAut.conj g) E₀]
    exact hE₀p
  refine ⟨⟨E, hES, hEA, hEq, hEp⟩, ?_⟩
  intro α hα hαS s hs hsq
  have hφ : ∃ k : ℕ, (Φ ^ m) ^ (q ^ k) = 1 := by
    refine ⟨a, ?_⟩
    rw [← pow_mul, mul_comm, hΦm]
  have hpow : ∀ n : ℕ, ∀ s ∈ S₀, (Φ ^ n) s ∈ S₀ := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih => intro s hs; rw [pow_succ, MulAut.mul_apply]; exact ih (Φ s) (hΦS s hs)
  have hφi : ¬ q ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).index := by
    intro hdvd
    exact hm (hdvd.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  exact CFSG.apply_eq_self_of_pow_eq_one hS₀ hS₀i hS₀c hφ (hpow m) hφi hΦfix hS hSi hα hαS
    s hs hsq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
