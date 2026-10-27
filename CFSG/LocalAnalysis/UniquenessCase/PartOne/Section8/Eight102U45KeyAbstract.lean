module

public import CFSG.GroupTheory.SylowAutConj
public import CFSG.GroupTheory.ConjMulPowCyclic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open

@[expose] def U45KeyConcl (X : Type*) [Group X] (p : ℕ) : Prop :=
  ∀ R : Subgroup (MulAut X), IsElemAbelian p R →
    ∃ S : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
      ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ s ∈ S, α s = s) ∧
        Nat.card R ≤ p * Nat.card C

theorem U45KeyConcl.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : U45KeyConcl Y p) : U45KeyConcl X p := by
  intro R hR
  let f : MulAut X ≃* MulAut Y := MulAut.congr e
  obtain ⟨S', hS', hS'i, C', hC', hfix', hcard'⟩ := h (R.map f.toMonoidHom) (hR.map _)
  refine ⟨S'.map e.symm.toMonoidHom, hS'.map _, ?_, C'.map f.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [Subgroup.index_map_of_bijective (f := e.symm.toMonoidHom) e.symm.bijective]
  · intro γ hγ
    obtain ⟨γ', hγ'C', rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨α, hαR, hαeq⟩ := Subgroup.mem_map.mp (hC' hγ'C')
    rw [← hαeq]
    simpa using hαR
  · intro γ hγ s hs
    obtain ⟨γ', hγ'C', rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨s', hs'S', rfl⟩ := Subgroup.mem_map.mp hs
    have hfs : (f.symm γ') (e.symm s') = e.symm (γ' s') := by
      simp [f, MulAut.congr_symm_apply]
    change (f.symm γ') (e.symm s') = e.symm s'
    rw [hfs, hfix' γ' hγ'C' s' hs'S']
  · rw [← Subgroup.card_map_of_injective (f := f.toMonoidHom) (K := R) f.injective,
      Subgroup.card_map_of_injective (f := f.symm.toMonoidHom) (K := C') f.symm.injective]
    exact hcard'

theorem u45KeyConcl_of_card_le {X : Type*} [Group X] [Finite X] {p : ℕ}
    (h : ∀ R : Subgroup (MulAut X), IsElemAbelian p R → Nat.card R ≤ p) :
    U45KeyConcl X p := by
  intro R hR
  obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := X)
  refine ⟨(S : Subgroup X), S.isPGroup', S.not_dvd_index, ⊥, bot_le, ?_, ?_⟩
  · intro α hα s hs
    rw [Subgroup.mem_bot] at hα
    rw [hα]
    rfl
  · rw [Subgroup.card_bot, mul_one]
    exact h R hR

theorem u45KeyConcl_of_torus {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Φ : MulAut X} (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    {m a : ℕ} (hm : ¬ p ∣ m) (hΦm : Φ ^ (p ^ a * m) = 1)
    {P₀ : Subgroup X} (hP₀ : IsPGroup p P₀) (hP₀i : ¬ p ∣ P₀.index)
    (hΦP : ∀ s ∈ P₀, (Φ ^ m) s ∈ P₀) {S₀ : Subgroup X} (hS₀ : IsPGroup 3 S₀)
    (hS₀i : ¬ 3 ∣ S₀.index) (hPS : ∀ x ∈ P₀, ∀ s ∈ S₀, x * s = s * x)
    (hΦS : ∀ s ∈ S₀, (Φ ^ m) s = s) : U45KeyConcl X p := by
  intro R hR
  have hφp : (Φ ^ m) ^ (p ^ a) = 1 := by
    rw [← pow_mul, Nat.mul_comm, hΦm]
  have hφi : ¬ p ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).index :=
    fun hd => hm (hd.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  obtain ⟨Q, hRQ⟩ := CFSG.exists_sylow_forall_apply_mem hR.isPGroup
  obtain ⟨β, -, hβconj⟩ :=
    CFSG.exists_mulAut_map_eq_and_conj_mem hP₀ hP₀i ⟨a, hφp⟩ hΦP hφi
      Q.isPGroup' Q.not_dvd_index hR.isPGroup hRQ
  have hφfix : Φ ^ m ∈ fixingSubgroup (MulAut X) (S₀ : Set X) :=
    (mem_fixingSubgroup_iff _).2 hΦS
  refine ⟨S₀.map β.symm.toMonoidHom, hS₀.map _, ?_, R, le_rfl, ?_,
    Nat.le_mul_of_pos_left _ (Fact.out : p.Prime).pos⟩
  · rwa [Subgroup.index_map_of_bijective (f := β.symm.toMonoidHom) β.symm.bijective]
  · intro α hα s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨s₀, hs₀, j, hβ⟩ := hβconj α hα
    have hj : ((Φ ^ m) ^ j) t = t := (mem_fixingSubgroup_iff _).1 (pow_mem hφfix j) t ht
    have hβt : (β * α * β⁻¹) t = t := by
      rw [hβ, MulAut.mul_apply, hj, MulAut.conj_apply, hPS s₀ hs₀ t ht, mul_assoc,
        mul_inv_cancel, mul_one]
    have hinj : β (α (β.symm t)) = β (β.symm t) := by
      rw [MulEquiv.apply_symm_apply]
      simpa [MulAut.mul_apply] using hβt
    exact β.injective hinj

theorem u45KeyConcl_of_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) {Φ : MulAut X}
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hΦinn : ∀ k : ℕ, Φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → Φ ^ k = 1)
    {m a : ℕ} (hm : ¬ p ∣ m) (hΦm : Φ ^ (p ^ a * m) = 1)
    (hrank : Open.pRank p (⊤ : Subgroup X) ≤ 1) {S₀ : Subgroup X} (hS₀ : IsPGroup 3 S₀)
    (hS₀i : ¬ 3 ∣ S₀.index) (hΦS : ∀ s ∈ S₀, (Φ ^ m) s = s) : U45KeyConcl X p := by
  intro R hR
  have hφp : (Φ ^ m) ^ (p ^ a) = 1 := by
    rw [← pow_mul, Nat.mul_comm, hΦm]
  have hφi : ¬ p ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (Φ ^ m)).index :=
    fun hd => hm (hd.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  have hφinn : ∀ k : ℕ, (Φ ^ m) ^ k ∈ (MulAut.conj : X →* MulAut X).range →
      (Φ ^ m) ^ k = 1 := by
    intro k hk
    rw [← pow_mul] at hk ⊢
    exact hΦinn (m * k) hk
  obtain ⟨P₀, hP₀⟩ := CFSG.exists_sylow_forall_apply_mem
    (GroupTheory.WielandtProduct.isPGroup_zpowers_of_pow_eq_one hφp)
  have hΦP : ∀ s ∈ (P₀ : Subgroup X), (Φ ^ m) s ∈ P₀ := hP₀ _ (mem_zpowers _)
  have hP₀cyc : IsCyclic (P₀ : Subgroup X) := by
    by_contra hnc
    obtain ⟨B, hB, hBcard⟩ :=
      CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
        ((Fact.out : p.Prime).odd_of_ne_two hp2) P₀.isPGroup' hnc
    have h2 := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt
      (le_top : B ≤ ⊤) (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB) hBcard
    have hrankP := (CFSG.SectionRank.pRank_top_le_of_injective (Fact.out : p.Prime).one_lt
      (P₀ : Subgroup X).subtype (P₀ : Subgroup X).subtype_injective).trans hrank
    omega
  obtain ⟨Q, hRQ⟩ := CFSG.exists_sylow_forall_apply_mem hR.isPGroup
  obtain ⟨β, -, hβconj⟩ :=
    CFSG.exists_mulAut_map_eq_and_conj_mem P₀.isPGroup' P₀.not_dvd_index ⟨a, hφp⟩ hΦP hφi
      Q.isPGroup' Q.not_dvd_index hR.isPGroup hRQ
  let R' : Subgroup (MulAut X) := R.map (MulAut.conj β).toMonoidHom
  have hcardle := CFSG.card_le_mul_card_inf_zpowers (R := R') hp2 hZ P₀.isPGroup' hP₀cyc hΦP
    hφinn (hR.map _) (by
      intro α hα
      obtain ⟨α₀, hα₀, rfl⟩ := Subgroup.mem_map.mp hα
      exact hβconj α₀ hα₀)
  have hconj : MulAut.conj β.symm = (MulAut.conj β).symm := by
    ext y
    simp [MulAut.conj_apply, MulAut.conj_symm_apply]
  have hφfix : Φ ^ m ∈ fixingSubgroup (MulAut X) (S₀ : Set X) :=
    (mem_fixingSubgroup_iff _).2 hΦS
  refine ⟨S₀.map β.symm.toMonoidHom, hS₀.map _, ?_,
    (R' ⊓ zpowers (Φ ^ m)).map (MulAut.conj β.symm).toMonoidHom, ?_, ?_, ?_⟩
  · rwa [Subgroup.index_map_of_bijective (f := β.symm.toMonoidHom) β.symm.bijective]
  · intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
    have hmem : (MulAut.conj β).symm δ ∈ R := Subgroup.mem_map_equiv.mp hδ.1
    simpa [hconj] using hmem
  · intro γ hγ s hs
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    have hδt : δ t = t :=
      (mem_fixingSubgroup_iff _).1 (zpowers_le.2 hφfix hδ.2) t ht
    change (MulAut.conj β.symm) δ (β.symm t) = β.symm t
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hδt]
  · rw [← Subgroup.card_map_of_injective (f := (MulAut.conj β).toMonoidHom) (K := R)
      (MulAut.conj β).injective, Subgroup.card_map_of_injective
      (f := (MulAut.conj β.symm).toMonoidHom) (MulAut.conj β.symm).injective]
    exact hcardle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
