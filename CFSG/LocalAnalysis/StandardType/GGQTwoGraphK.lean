module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrAt
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD5
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphFinish
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphSwap
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphClassify
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled
public import CFSG.LocalAnalysis.StandardType.GGQTwoSwapAB
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private lemma ggQ2gk_D_shift {k : ℕ} (hk : 2 ≤ k) (i j : Fin (2 * k)) :
    CartanMatrix.D (2 * k + 1) ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ =
      CartanMatrix.D (2 * k) i j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem ggQ2gk_gamma_of_normalizer_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (h : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)) :
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  rw [mem_ggAutomizer_iff] at hφ ⊢
  obtain ⟨g, -, hgN, hg⟩ := hφ
  exact ⟨g, h hgN, hgN, hg⟩

private theorem ggQ2gk_premises (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1b : GGQTwoNoTwoNodeIndInput) (h5 : GGQTwoCentralizerInput) (hnode : GGQ2TwoNodeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} [Fact (Nat.Prime 3)] (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∨
      (ggAutomizer J Bs ≠ ⊥ ∧ GGQTwoK1 3 B Bs x D J) := by
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  by_cases hrow : ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ((GGQTwoTwoNodeRowAt 3 L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt 3 K J ∧ y ∉ K))
  · obtain ⟨y, K, hnb, h⟩ := hrow
    exact Or.inl (hnode rfl hS hI1 hnb h)
  right
  have hnr : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ¬ (GGQTwoTwoNodeRowAt 3 L J ∨ GGQTwoTwoNodeRowAt 3 K J) := by
    intro y K hnb h
    obtain ⟨hL, hK⟩ := h1b G 3 B Bs x L D J hS hI1 y K hnb
    rcases h with h | h
    · exact hrow ⟨y, K, hnb, Or.inl ⟨h, hL h⟩⟩
    · exact hrow ⟨y, K, hnb, Or.inr ⟨h, hK h⟩⟩
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  exact ⟨hAJS, ggQ2_K1_of_I1 hLB hP hH hI1⟩

private theorem ggQ2gk_sigma {ι : Type} {k : ℕ} (e : Fin (2 * k + 1) ≃ ι) (e₀ : ι)
    (he0 : e₀ = e ⟨0, by omega⟩) :
    ∃ σ : Fin (2 * k) ≃ {i // i ≠ e₀}, ∀ j, (σ j : ι) = e ⟨j.val + 1, by omega⟩ := by
  subst he0
  refine ⟨Equiv.ofBijective (fun j => ⟨e ⟨j.val + 1, by omega⟩, ?_⟩) ⟨?_, ?_⟩, fun j => rfl⟩
  · intro h
    have := congrArg Fin.val (e.injective h)
    simp at this
  · intro a b hab
    have := congrArg Fin.val (e.injective (Subtype.ext_iff.mp hab))
    simp only at this
    exact Fin.ext (by omega)
  · rintro ⟨i, hi⟩
    obtain ⟨t, rfl⟩ := e.surjective i
    have ht : t.val ≠ 0 := fun h => hi (congrArg e (Fin.ext (by simpa using h)))
    refine ⟨⟨t.val - 1, by omega⟩, Subtype.ext ?_⟩
    show e ⟨t.val - 1 + 1, _⟩ = e t
    congr 1
    exact Fin.ext (by simp; omega)

private theorem ggQ2gk_swap_compat {ι : Type} [DecidableEq ι] {k : ℕ} (hk : 2 ≤ k)
    (e : Fin (2 * k + 1) ≃ ι) {e₀ : ι} (σ : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hσ : ∀ j, (σ j : ι) = e ⟨j.val + 1, by omega⟩) (j : Fin (2 * k)) :
    ((σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) ⟨2 * k - 1, by omega⟩ j) :
        {i // i ≠ e₀}) : ι) =
      Equiv.swap (e ⟨2 * k + 1 - 2, by omega⟩) (e ⟨2 * k + 1 - 1, by omega⟩) (σ j : ι) := by
  rw [hσ, hσ]
  by_cases h1 : j = ⟨2 * k - 2, by omega⟩
  · subst h1
    rw [Equiv.swap_apply_left]
    have : (e ⟨2 * k + 1 - 2, by omega⟩ : ι) = e ⟨(2 * k - 2) + 1, by omega⟩ := by
      congr 1; exact Fin.ext (by simp; omega)
    rw [this, Equiv.swap_apply_left]
    congr 1; exact Fin.ext (by simp; omega)
  · by_cases h2 : j = ⟨2 * k - 1, by omega⟩
    · subst h2
      rw [Equiv.swap_apply_right]
      have : (e ⟨2 * k + 1 - 1, by omega⟩ : ι) = e ⟨(2 * k - 1) + 1, by omega⟩ := by
        congr 1; exact Fin.ext (by simp; omega)
      rw [this, Equiv.swap_apply_right]
      congr 1; exact Fin.ext (by simp; omega)
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        apply h1
        have := congrArg Fin.val (e.injective h)
        simp only at this
        exact Fin.ext (by simp; omega)
      · intro h
        apply h2
        have := congrArg Fin.val (e.injective h)
        simp only at this
        exact Fin.ext (by simp; omega)

private theorem ggQ2gk_four_ne : ((4 : ℤ) : ZMod 3) ≠ 0 := by decide

private theorem ggQ2gk_perm4 : ∀ π : Equiv.Perm (Fin 4), π 0 = 0 → π 1 = 1 →
    π = 1 ∨ π = Equiv.swap (2 : Fin 4) 3 := by
  decide

theorem ggQ2_gammaNbrGraph_core (P : GGQ2NbrPosPred) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h1b : GGQTwoNoTwoNodeIndInput)
    (h5 : GGQTwoCentralizerInput) (hnode : GGQ2TwoNodeInput) :
    GGQ2GammaNbrGraphAt P := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ _ y K hnb M hD hV φ hφ hφy π μ c w hSc hw hT hπa _
  subst hp
  classical
  rcases ggQ2gk_premises hLB hP h1b h5 hnode hS hI1 with hN | ⟨hAJ, hK1⟩
  · exact ggQ2gk_gamma_of_normalizer_le hφ hN
  obtain ⟨k, hk, f, hf⟩ := hD
  have hb : ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0 :=
    ggQ2g_leaf_of_D M.toLin M.b M.a M.a_ne_b M.a_leaf hk f hf
  rcases ggQ2g_classify M.toLin M.b M.a M.a_ne_b M.a_leaf hk f hf with hDm | hEm
  · obtain ⟨e, hecart, hecox, he0, hea⟩ : ∃ e : Fin (2 * k + 1) ≃ M.ι,
        (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D (2 * k + 1) i j) ∧
        M.coxeter = (ggCoxeterMatrixD (2 * k + 1)).reindex e ∧ M.b = e ⟨0, by omega⟩ ∧
        (M.a = e ⟨2 * k - 1, by omega⟩ ∨ M.a = e ⟨2 * k, by omega⟩) := by
      obtain ⟨e, h1, h2, h3, h4⟩ := hDm
      exact ⟨e, h1, h2, h3, h4⟩
    obtain ⟨σ, hσ⟩ := ggQ2gk_sigma e M.b he0
    have hσc : ∀ i j, M.cartan (σ i : M.ι) (σ j : M.ι) = CartanMatrix.D (2 * k) i j := by
      intro i j
      rw [hσ i, hσ j]
      exact (hecart _ _).trans (ggQ2gk_D_shift hk i j)
    obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.b σ hσc hSc
    have hπσ : ∀ i, π (σ i) = σ (π' i) := fun i => hπσ₀ i
    have hμσ : ∀ i, μ (σ i) = μ' i := fun i => hμσ₀ i
    have hamoved : π' ≠ 1 := by
      intro h1'
      obtain ⟨ja, hja⟩ := σ.surjective ⟨M.a, M.a_ne_b⟩
      exact hπa (by rw [← hja, hπσ, h1', Equiv.Perm.one_apply])
    have hstruct : (∀ j, μ' j = μ' ⟨0, by omega⟩) →
        π' = Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) ⟨2 * k - 1, by omega⟩ →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
      intro hμc hπs
      have hM : M.cartan = (CartanMatrix.D (2 * k + 1)).submatrix e.symm e.symm := by
        ext i j
        simp only [Matrix.submatrix_apply]
        rw [← hecart (e.symm i) (e.symm j)]
        simp
      have hdet : (((M.toLin.swapAB hb).cartan.det : ℤ) : ZMod 3) ≠ 0 := by
        show ((M.cartan.det : ℤ) : ZMod 3) ≠ 0
        rw [hM, Matrix.det_submatrix_equiv_self, CartanMatrix.D_det (by omega)]
        exact ggQ2gk_four_ne
      have hbas : (M.toLin.swapAB hb).Basis :=
        ggQ2g_basis (M.toLin.swapAB hb) (M.toLin.swapAB hb).a M.yV hdet hV
      have hfix := (ggQ2_fixed_lin M).2
      have hT' : ∀ i : (M.toLin.swapAB hb).ι, i ≠ (M.toLin.swapAB hb).a →
          (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
            ((M.toLin.swapAB hb).coroot i) = c • μ' ⟨0, by omega⟩ • w ((M.toLin.swapAB hb).coroot
              (Equiv.swap (e ⟨2 * k + 1 - 2, by omega⟩) (e ⟨2 * k + 1 - 1, by omega⟩) i)) := by
        intro i hi
        obtain ⟨j, hj⟩ := σ.surjective ⟨i, hi⟩
        have hh := hT (σ j)
        rw [hμσ, hμc, hπσ, hπs, ggQ2gk_swap_compat hk e σ hσ j] at hh
        have hi' : (σ j : M.ι) = i := congrArg Subtype.val hj
        rw [hi'] at hh
        exact hh
      obtain ⟨w', hw', hstab⟩ := ggQ2g_swap_stable (by norm_num) (M.toLin.swapAB hb) hbas
        (m := 2 * k + 1) (by omega) e hecox he0 M.yV hfix hV hw hT' hφy
      refine ggQ2_finish_of_weyl hLB hP hS hAJ hK1 hnb M hφ ⟨w', hw', fun v hv => ?_⟩
      have hv' : v ∈ Submodule.span (ZMod 3) ({M.yV, M.xV} : Set M.V) := by
        rwa [Set.pair_comm] at hv
      have h2 : w' (ggLin (p := 3) M.model φ v) ∈
          Submodule.span (ZMod 3) ({M.yV, M.xV} : Set M.V) := hstab M.xV v hv'
      rwa [Set.pair_comm] at h2
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      obtain ⟨hμc, hπ1⟩ := ggQ2g_scaledD4 π' μ' hμ'0 hrel
      by_cases h0 : π' 0 = 0
      · rcases ggQ2gk_perm4 π' h0 hπ1 with h | h
        · exact absurd h hamoved
        · exact hstruct (fun j => (hμc j).trans (hμc _).symm) h
      · exact (ggQ2_gammaNbrGraphD5_false hLB hP h5 hS rfl M e hecart he0 hea hV hφ hφy π μ c w
          hSc hw hT hπa (fun i hi hpi => by
            have hi0 : i = σ 0 := Subtype.ext (by rw [hσ 0]; exact hi)
            apply h0
            have h2 : (σ (π' 0) : M.ι) = (σ 0 : M.ι) := by
              rw [← hπσ, ← hi0]
              exact hpi.trans hi.symm
            exact σ.injective (Subtype.ext h2))).elim
    · obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD (2 * k) (by omega) π' μ' hμ'0 hrel
      rcases hπc with h | h
      · exact absurd h hamoved
      · exact hstruct hμc h
  · obtain ⟨hk3, e, hecart, he0, hea⟩ : k = 3 ∧ ∃ e : Fin 7 ≃ M.ι,
        (∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 7 i j) ∧ M.b = e 0 ∧
        (M.a = e 1 ∨ M.a = e 6) := by
      obtain ⟨h3, e, h1, h2, h4⟩ := hEm
      exact ⟨h3, e, h1, h2, h4⟩
    let τ : Fin 6 → Fin 7 := ![6, 5, 4, 3, 1, 2]
    have hτ0 : ∀ j, τ j ≠ 0 := by decide
    have hτi : ∀ a b, τ a = τ b → a = b := by decide
    have hτs : ∀ t : Fin 7, t ≠ 0 → ∃ j, τ j = t := by decide
    have hτc : ∀ i j : Fin 6, CartanMatrix.E 7 (τ i) (τ j) = CartanMatrix.D 6 i j := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [τ, CartanMatrix.E, CartanMatrix.D]
    let σ : Fin 6 ≃ {i // i ≠ M.b} := Equiv.ofBijective
      (fun j => ⟨e (τ j), fun h => hτ0 j (e.injective (h.trans he0))⟩)
      ⟨fun a b hab => hτi a b (e.injective (Subtype.ext_iff.mp hab)), by
        rintro ⟨i, hi⟩
        obtain ⟨t, rfl⟩ := e.surjective i
        have ht : t ≠ 0 := fun h => hi (by rw [he0, h])
        obtain ⟨j, hj⟩ := hτs t ht
        exact ⟨j, Subtype.ext (by simp [hj])⟩⟩
    have hσ : ∀ j, (σ j : M.ι) = e (τ j) := fun j => rfl
    have hσc : ∀ i j, M.cartan (σ i : M.ι) (σ j : M.ι) = CartanMatrix.D 6 i j := by
      intro i j
      rw [hσ i, hσ j, hecart]
      exact hτc i j
    subst hk3
    obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.b σ hσc hSc
    have hπσ : ∀ i, π (σ i) = σ (π' i) := fun i => hπσ₀ i
    obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD 6 (by norm_num) π' μ' hμ'0 hrel
    have hπ0 : π' 0 = 0 := by
      rcases hπc with h | h
      · rw [h]; rfl
      · rw [h, Equiv.swap_apply_of_ne_of_ne] <;> decide
    have hea1 : M.a = e 1 := by
      rcases hea with h | h
      · exact h
      · exfalso
        apply hπa
        have hja : (⟨M.a, M.a_ne_b⟩ : {k // k ≠ M.b}) = σ 0 := Subtype.ext (by rw [hσ]; exact h)
        rw [hja, hπσ, hπ0]
    exact (ggQ2_gammaNbrGraphE7_false hLB hP h5 hS rfl hnb hK1 M e hecart he0 hea1 hV hφ hφy π μ c
      w hSc hw hT hπa).elim

theorem ggQ2_gammaNbrGraph_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1b : GGQTwoNoTwoNodeIndInput) (h5 : GGQTwoCentralizerInput)
    (hnode : GGQ2TwoNodeInput) : GGQ2GammaNbrGraphInput :=
  ggQ2_gammaNbrGraph_core GGQ2PosNotInL hLB hP h1b h5 hnode

end CFSG.StandardType
