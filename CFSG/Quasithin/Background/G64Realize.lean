module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.G6Swap
public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type*} [CommGroup V]

theorem RealizesVia.exists_modEquiv {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ e : V ≃* D.Mod, ∀ (γ : D.Gam) (v : V) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
      e v = QuotientGroup.mk m →
        e (((π γ : ↥H) : MulAut V) v) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := by
  obtain ⟨_, _, _, _, _, _, _, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  let e : V ≃* D.Mod := Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)
  refine ⟨e, fun γ v m hm hvm => ?_⟩
  exact hβe γ ⟨v, trivial⟩ m trivial hm hvm

theorem RealizesVia.exists_secHom {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ β : ↥D.sec →* V, (∀ m : ↥D.sec, β m = 1 ↔ (m : D.Amb) ∈ D.ker) ∧
      ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
        β ⟨D.act γ (m : D.Amb), hm⟩ = ((π γ : ↥H) : MulAut V) (β m) := by
  obtain ⟨e, he⟩ := RealizesVia.exists_modEquiv h
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (D.ker.subgroupOf D.sec)), fun m => ?_,
    fun γ m hm => ?_⟩
  · show e.symm (QuotientGroup.mk m) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · show e.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩) =
      ((π γ : ↥H) : MulAut V) (e.symm (QuotientGroup.mk m))
    rw [MulEquiv.symm_apply_eq]
    exact (he γ (e.symm (QuotientGroup.mk m)) m hm (e.apply_symm_apply _)).symm

theorem RealizesVia.exists_secEquiv {D : FFModel} (hker : D.ker = ⊥) {H : Subgroup (MulAut V)}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ E : V ≃* ↥D.sec, ∀ (γ : D.Gam) (v : V),
      ((E (((π γ : ↥H) : MulAut V) v) : ↥D.sec) : D.Amb) = D.act γ ((E v : ↥D.sec) : D.Amb) := by
  obtain ⟨e, he⟩ := RealizesVia.exists_modEquiv h
  have hqi : Function.Injective (QuotientGroup.mk' (D.ker.subgroupOf D.sec)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker,
      Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  let Q : ↥D.sec ≃* D.Mod :=
    MulEquiv.ofBijective (QuotientGroup.mk' (D.ker.subgroupOf D.sec))
      ⟨hqi, QuotientGroup.mk'_surjective _⟩
  refine ⟨e.trans Q.symm, fun γ v => ?_⟩
  set m : ↥D.sec := Q.symm (e v) with hm
  have hm' : e v = QuotientGroup.mk m := by
    rw [hm]
    exact (Q.apply_symm_apply (e v)).symm
  have hact : D.act γ (m : D.Amb) ∈ D.sec := h.2.2.2.2.2.1 γ m m.2
  have := he γ v m hact hm'
  show ((Q.symm (e (((π γ : ↥H) : MulAut V) v)) : ↥D.sec) : D.Amb) = D.act γ (m : D.Amb)
  rw [this]
  have : Q.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hact⟩) = ⟨D.act γ (m : D.Amb), hact⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]

theorem permAct_ofAdd_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    G6.permAct n σ (Multiplicative.ofAdd (Pi.single i 1)) =
      Multiplicative.ofAdd (Pi.single (σ i) 1) := by
  apply Multiplicative.toAdd.injective
  funext l
  rw [G6.permAct_apply]
  simp only [toAdd_ofAdd]
  by_cases hl : l = σ i
  · subst hl
    simp
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne]
    intro h
    exact hl (by rw [← h]; simp)

@[expose] def pairVec {n : ℕ} (i j : Fin n) : G6.PermMod n :=
  Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1)

theorem pairVec_mem_coreMod {n : ℕ} (i j : Fin n) : pairVec i j ∈ G6.coreMod n := by
  rw [G6.mem_coreMod, pairVec, toAdd_ofAdd]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ↓reduceIte]
  decide

theorem permAct_pairVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    G6.permAct n σ (pairVec i j) = pairVec (σ i) (σ j) := by
  rw [pairVec, ofAdd_add, map_mul, permAct_ofAdd_single, permAct_ofAdd_single, pairVec, ofAdd_add]

theorem toAdd_pairVec_apply {n : ℕ} (i j l : Fin n) :
    Multiplicative.toAdd (pairVec i j) l =
      (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
  rw [pairVec, toAdd_ofAdd, Pi.add_apply, Pi.single_apply, Pi.single_apply]

private theorem eq_one_of_fix_pairs {n : ℕ} (hn : 3 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin n, i ≠ j → pairVec (σ i) (σ j) = pairVec i j) : σ = 1 := by
  by_contra h1
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  obtain ⟨j, hji, hjσ⟩ : ∃ j : Fin n, j ≠ i ∧ j ≠ σ i := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, σ i} := by
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · simp [hcon j hj]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := i) (b := σ i)
    omega
  have hpair := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x (σ i)) (h i j hji.symm)
  have hsij : σ i ≠ σ j := fun e => hji (σ.injective e).symm
  simp only [toAdd_pairVec_apply] at hpair
  simp [hsij, hi, hjσ.symm] at hpair

theorem symDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.symDn n).Faithful := by
  intro (σ : Equiv.Perm (Fin n)) hσ
  refine eq_one_of_fix_pairs (by omega) fun i j hij => ?_
  have hm := hσ (pairVec i j) (pairVec_mem_coreMod i j)
  change G6.permAct n σ (pairVec i j) * (pairVec i j)⁻¹ ∈
    Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n at hm
  rw [permAct_pairVec] at hm
  obtain ⟨⟨z, hz⟩, -⟩ := hm
  obtain ⟨l, hli, hlj, hlσi, hlσj⟩ : ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ σ i ∧ l ≠ σ j := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j, σ i, σ j} := by
      intro l _
      by_cases h1 : l = i
      · simp [h1]
      by_cases h2 : l = j
      · simp [h2]
      by_cases h3 : l = σ i
      · simp [h3]
      simp [hcon l h1 h2 h3]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h4 : ({i, j, σ i, σ j} : Finset (Fin n)).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      exact Nat.succ_le_succ (Finset.card_le_two)
    omega
  have hcoord := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x l) hz
  simp only [toAdd_zpow, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    toAdd_pairVec_apply, hli, hlj, hlσi, hlσj, G6.allOnes, toAdd_ofAdd, ite_false, add_zero,
    zsmul_eq_mul, mul_one] at hcoord
  have hz0 : (z : ZMod 2) = 0 := hcoord.trans (by decide)
  have hone : G6.allOnes n ^ z = 1 := by
    apply Multiplicative.toAdd.injective
    funext l'
    simp [G6.allOnes, toAdd_zpow, hz0]
  have hz' : G6.allOnes n ^ z = pairVec (σ i) (σ j) * (pairVec i j)⁻¹ := hz
  rw [hone] at hz'
  exact (mul_inv_eq_one.1 hz'.symm)

theorem symCore_faithful {n : ℕ} (hn : 3 ≤ n) : (symCoreModel n).Faithful := by
  intro (σ : Equiv.Perm (Fin n)) hσ
  refine eq_one_of_fix_pairs hn fun i j hij => ?_
  have hm := hσ (pairVec i j) (pairVec_mem_coreMod i j)
  change G6.permAct n σ (pairVec i j) * (pairVec i j)⁻¹ ∈ (⊥ : Subgroup (G6.PermMod n)) at hm
  have hm' : G6.permAct n σ (pairVec i j) = pairVec i j := mul_inv_eq_one.1 (Subgroup.mem_bot.1 hm)
  rw [permAct_pairVec] at hm'
  exact hm'

@[expose] def permModel (n : ℕ) (Z : Subgroup (G6.PermMod n)) : FFModel where
  Gam := Equiv.Perm (Fin n)
  Amb := G6.PermMod n
  act σ x := G6.permAct n σ x
  sec := G6.coreMod n
  ker := Z

theorem symDn_eq_permModel (n : ℕ) :
    FFModel.symDn n = permModel n (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) := rfl

theorem symCoreModel_eq_permModel (n : ℕ) : symCoreModel n = permModel n ⊥ := rfl

theorem isSwap_of_realization {n : ℕ} (hn : 5 ≤ n) {Z : Subgroup (G6.PermMod n)}
    (hZ : Z ≤ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) {H : Subgroup (MulAut V)}
    {π : Equiv.Perm (Fin n) →* ↥H} (h : (permModel n Z).RealizesVia H ⊤ ⊥ π)
    (hinj : Function.Injective π) {a : MulAut V} (ha : a ∈ H)
    (hcard : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ((MulEquiv.ofBijective π ⟨hinj, h.1⟩).symm ⟨a, ha⟩).IsSwap := by
  set θ := (MulEquiv.ofBijective π ⟨hinj, h.1⟩).symm with hθ
  obtain ⟨β₀, hβk, hβe⟩ := RealizesVia.exists_secHom h
  let β : G6.coreMod n →* V := β₀
  have hequiv : ∀ (x : H) (u : G6.coreMod n), β (G6.coreAct n (θ x) u) = (x : MulAut V) (β u) := by
    intro x u
    have hx : π (θ x) = x := by
      rw [hθ]
      exact (MulEquiv.ofBijective π ⟨hinj, h.1⟩).apply_symm_apply x
    have h2 : ((π (θ x) : ↥H) : MulAut V) = (x : MulAut V) := congrArg Subtype.val hx
    have hact : G6.permAct n (θ x) (u : G6.PermMod n) ∈ G6.coreMod n :=
      G6.permAct_mem_coreMod (θ x) u.2
    rw [← h2]
    exact hβe (θ x) u hact
  have hker : β.ker ≤ G6.natKer n := by
    intro u hu
    have := (hβk u).1 hu
    exact (hZ this).1
  exact G6.isSwap_of_card_commV_eq_two hn θ β hequiv hker ha hcard

theorem eq_zero_or_eq_one_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    (c : K) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : ({0, 1, c} : Finset K).card ≤ Fintype.card K := Finset.card_le_univ _
  rw [← Nat.card_eq_fintype_card, hK] at hsub
  have h3 : ({0, 1, c} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hcon.2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, hcon.1.symm⟩
  omega

theorem BinaryNaturalSL.exists_equiv_vec {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ n 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSL n K) →* ↥H)
      (E : V ≃* Multiplicative (Fin n → K)), Nat.card K = 2 ∧ Function.Surjective π ∧
      ∀ (γ : ↥(StatedSL n K)) (v : V),
        Multiplicative.toAdd (E (((π γ : ↥H) : MulAut V) v)) =
          ((γ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
            (Multiplicative.toAdd (E v)) := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  obtain ⟨E, hE⟩ := RealizesVia.exists_secEquiv (D := FFModel.nat (StatedSL n K)) rfl hπ
  refine ⟨K, hK, hKf, π, E.trans Subgroup.topEquiv, by simpa using hK2, hπ.1, fun γ v => ?_⟩
  exact congrArg Multiplicative.toAdd (hE γ v)

theorem BinaryNaturalSL.card_eq {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ n 1) : Nat.card V = 2 ^ n := by
  obtain ⟨K, _, _, _, E, hK, -, -⟩ := BinaryNaturalSL.exists_equiv_vec h
  rw [Nat.card_congr E.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem BinaryNaturalSL.eq_top {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ n 1) : H = ⊤ := by
  classical
  obtain ⟨K, _, _, π, E, hK, hπ, hE⟩ := BinaryNaturalSL.exists_equiv_vec h
  rw [eq_top_iff]
  intro ψ _
  let A : (Fin n → K) ≃+ (Fin n → K) := MulEquiv.toAdditive ((E.symm.trans ψ).trans E)
  have hA : ∀ (c : K) (x : Fin n → K), A (c • x) = c • A x := by
    intro c x
    rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
    · simp
    · simp
  let L : (Fin n → K) ≃ₗ[K] (Fin n → K) := A.toLinearEquiv hA
  let g : Matrix.GeneralLinearGroup (Fin n) K :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv L)
  have hg : ∀ x, (g : Matrix (Fin n) (Fin n) K).mulVec x = L x := by
    intro x
    have := Matrix.GeneralLinearGroup.toLin_apply g x
    rw [show Matrix.GeneralLinearGroup.toLin g = LinearMap.GeneralLinearGroup.ofLinearEquiv L from
      MulEquiv.apply_symm_apply _ _] at this
    exact this.symm
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hK (g : Matrix (Fin n) (Fin n) K).det with h0 | h1
    · exact absurd h0 (g.isUnit.map Matrix.detMonoidHom).ne_zero
    · exact h1
  have hgmem : g ∈ StatedSL n K := Subgroup.subset_closure hdet
  have key : ((π ⟨g, hgmem⟩ : ↥H) : MulAut V) = ψ := by
    ext v
    apply E.injective
    apply Multiplicative.toAdd.injective
    rw [hE, hg]
    show Multiplicative.toAdd (E (ψ (E.symm (E v)))) = Multiplicative.toAdd (E (ψ v))
    rw [MulEquiv.symm_apply_apply]
  rw [← key]
  exact (π ⟨g, hgmem⟩).2

end CFSG.Quasithin.G64
