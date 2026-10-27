module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.D6InnerAux
public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigid
public import CFSG.LocalAnalysis.StandardType.FS81.OrthInner
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

private theorem subset_D6 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7}
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 6 := by
  intro M hM
  obtain ⟨c, hcC, hcActs⟩ := hM
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, -, hb₀E, -, -, -⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, -, -, -, -, -⟩ := hA
  obtain ⟨-, hdisj, -, -, -, -⟩ := hCanon
  have hB' : Adapted B b₀ K E := hB
  obtain ⟨hspan, hb0, hbiK⟩ := hB
  have hcNE : c ∈ Subgroup.normalizer (E : Set G) := by
    have h := B.mem_normalizer_of_acts hcActs
    rwa [hspan] at h
  have hCK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hcNK : c ∈ Subgroup.normalizer (K : Set G) := hCK hcC
  have hcomm : c * b₀ = b₀ * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hc_b0 : c * b₀ * c⁻¹ = b₀ := by
    rw [hcomm]
    simp
  have hcol0 : (fun i => M i 0) = Pi.single (0 : Fin 7) 1 := by
    apply B.vec_injective
    rw [← hcActs 0, hb0, hc_b0, B.vec_single, hb0]
  have h0 : ∀ i : Fin 7, M i 0 = if i = 0 then 1 else 0 := by
    intro i
    rw [congrFun hcol0 i, Pi.single_apply]
  have hrow0 : ∀ j : Fin 7, j ≠ 0 → M 0 j = 0 := by
    intro j hj
    have hbK : B.b j ∈ K := hbiK j hj
    have hconjK : c * B.b j * c⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hcNK (B.b j)).mp hbK
    have hvK : B.vec (fun i => M i j) ∈ K := by
      rw [← hcActs j]
      exact hconjK
    exact vec_mem_K_imp_zero hB' hb₀ord hdisj hb₀E hvK
  have hcNB : c⁻¹ ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hspan]
    exact Subgroup.inv_mem _ hcNE
  obtain ⟨N, hNActs⟩ := B.exists_acts hcNB
  have hNM : N * M = 1 := by
    have h := B.acts_mul hNActs hcActs
    rw [inv_mul_cancel] at h
    exact B.acts_unique h B.acts_one
  have hIsConj : ∀ v : Coords 7, v ≠ 0 → v 0 = 0 → wt v = 2 →
      IsConjLine b₀ (B.line v) := by
    intro v hv hv0 hwt
    exact (hrec.2 v hv).mpr (Or.inr (Or.inl ⟨hwt, hv0⟩))
  have hweight : ∀ v : Coords 7, v ≠ 0 → v 0 = 0 → wt v = 2 → wt (M *ᵥ v) = 2 := by
    intro v hv hv0 hwt
    have hconj := isConjLine_map_conj (hIsConj v hv hv0 hwt) c
    rw [line_map_conj hcActs v] at hconj
    have hMv0 : (M *ᵥ v) 0 = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = 0
      · subst hj
        rw [h0 0]
        simp [hv0]
      · rw [hrow0 j hj, zero_mul]
    have hMvne : M *ᵥ v ≠ 0 := by
      intro hzero
      have h1 : N *ᵥ (M *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
      rw [hzero, Matrix.mulVec_zero] at h1
      exact hv h1.symm
    have hcond := (hrec.2 (M *ᵥ v) hMvne).mp hconj
    rcases hcond with ⟨h1, h10⟩ | ⟨h2, -⟩ | ⟨h7, -⟩
    · exact absurd hMv0 h10
    · exact h2
    · exfalso
      have := wt_le_of_apply_zero hMv0
      omega
  have h2 : ∀ i j : Fin 6, i ≠ j →
      wt (M *ᵥ (Pi.single i.succ 1 + Pi.single j.succ 1)) = 2 ∧
        wt (M *ᵥ (Pi.single i.succ 1 - Pi.single j.succ 1)) = 2 := by
    intro i j hij
    have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
    have hzero : ∀ k : Fin 6, (Pi.single k.succ (1 : ZMod 3) : Coords 7) 0 = 0 := by
      intro k
      exact Pi.single_eq_of_ne (Fin.succ_ne_zero k).symm 1
    constructor
    · refine hweight _ ?_ ?_ ?_
      · intro hv
        have hw := wt_single_add_single (a := 1) (b := 1) hs one_ne_zero one_ne_zero
        rw [hv] at hw
        simp [wt] at hw
      · rw [Pi.add_apply, hzero i, hzero j, add_zero]
      · exact wt_single_add_single hs one_ne_zero one_ne_zero
    · refine hweight _ ?_ ?_ ?_
      · intro hv
        have hw := wt_single_sub_single (a := 1) (b := 1) hs one_ne_zero one_ne_zero
        rw [hv] at hw
        simp [wt] at hw
      · rw [Pi.sub_apply, hzero i, hzero j, sub_zero]
      · exact wt_single_sub_single hs one_ne_zero one_ne_zero
  obtain ⟨σ, s, hsign, hσ0, hs0, hM_eq⟩ :=
    exists_spMat_succ_of_wt_two (n := 6) (by norm_num) M ⟨N, hNM⟩ h0
      (fun j => hrow0 j.succ (Fin.succ_ne_zero j)) h2
  let u : Coords 7 := fun _ => 1
  have hu_ne : u ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [u] at this
  have hu_wt : wt u = 7 := by
    rw [wt]
    have hf : (Finset.univ.filter fun i : Fin 7 => u i ≠ 0) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      simp [u]
    rw [hf, Finset.card_univ, Fintype.card_fin]
  have hu_prod : ∏ i : Fin 6, u i.succ = 1 := by simp [u]
  have hu_conj : IsConjLine b₀ (B.line u) :=
    (hrec.2 u hu_ne).mpr (Or.inr (Or.inr ⟨hu_wt, hu_prod⟩))
  have hMu_conj : IsConjLine b₀ (B.line (M *ᵥ u)) := by
    have := isConjLine_map_conj hu_conj c
    rwa [line_map_conj hcActs u] at this
  have hMu_wt : wt (M *ᵥ u) = 7 := by
    have hvec : M *ᵥ u = fun i => s (σ.symm i) := by
      rw [hM_eq, spMat_mulVec]
      funext i
      simp [u]
    rw [hvec, wt]
    have hf : (Finset.univ.filter fun i : Fin 7 => s (σ.symm i) ≠ 0) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      rcases hsign (σ.symm i) with h | h <;> rw [h] <;> decide
    rw [hf, Finset.card_univ, Fintype.card_fin]
  have hMu_ne : M *ᵥ u ≠ 0 := by
    intro h
    rw [h] at hMu_wt
    simp [wt] at hMu_wt
  have hMu_prod : ∏ i : Fin 6, (M *ᵥ u) i.succ = 1 := by
    have hcond := (hrec.2 (M *ᵥ u) hMu_ne).mp hMu_conj
    rcases hcond with ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h7, hp⟩
    · omega
    · omega
    · exact hp
  have hprod_s : ∏ i : Fin 6, s (σ.symm i.succ) = 1 := by
    simpa [hM_eq, spMat_mulVec, u] using hMu_prod
  have hσsymm0 : σ.symm 0 = 0 := by
    have h := Equiv.symm_apply_apply σ 0
    rwa [hσ0] at h
  have hprod : ∏ i : Fin 6, s i.succ = 1 := by
    have hne : ∀ i : Fin 6, σ.symm i.succ ≠ 0 := by
      intro i hi
      have h1 : i.succ = σ 0 := by
        rw [← Equiv.apply_symm_apply σ i.succ, hi, hσ0]
      exact Fin.succ_ne_zero i (h1.trans hσ0)
    let f : Fin 6 → Fin 6 := fun i => (σ.symm i.succ).pred (hne i)
    have hf : ∀ i, (f i).succ = σ.symm i.succ := fun i => Fin.succ_pred _ _
    have hfinj : Function.Injective f := by
      intro i j hij
      have h1 : (f i).succ = (f j).succ := by rw [hij]
      rw [hf i, hf j] at h1
      exact Fin.succ_inj.mp (σ.symm.injective h1)
    let e : Equiv.Perm (Fin 6) :=
      Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
    have he : ∀ i, (e i).succ = σ.symm i.succ := by
      intro i
      rw [show e i = f i from Equiv.ofBijective_apply f _ i, hf i]
    have h1 : ∏ i : Fin 6, s i.succ = ∏ i : Fin 6, s (e i).succ :=
      (Equiv.prod_comp e (fun j => s j.succ)).symm
    have h2 : ∏ i : Fin 6, s (e i).succ = ∏ i : Fin 6, s (σ.symm i.succ) :=
      Finset.prod_congr rfl fun i _ => by rw [he i]
    rw [h1, h2, hprod_s]
  exact ⟨σ, s, hsign, ⟨hσ0, hs0, hprod⟩, hM_eq⟩

private theorem eq_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) = B.realized K ∧
      B.realized K = evenFix0 6 := by
  have hstd' : StdLoc b₀ K E Row.D6 := hstd
  obtain ⟨-, hHyp, -⟩ := hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, -, -, -, -, -⟩ := hA
  have hsubC : B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 6 :=
    subset_D6 hstd' hB hrec
  have hsubKC : B.realized K ⊆ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
    rintro A ⟨g, hgK, hA⟩
    exact ⟨g, hKC hgK, hA⟩
  obtain ⟨B', hB', -, hB'even⟩ := exists_basis_localOrth_even_D6 hstd'
  have hcardK : Nat.card ↥(B.realized K) = Nat.card ↥(B'.realized K) :=
    (card_realized_eq_card_ggInduced B hB.1 K).trans
      (card_realized_eq_card_ggInduced B' hB'.1 K).symm
  have hle1 : Nat.card ↥(evenFix0 6) ≤ Nat.card ↥(B'.realized K) :=
    Nat.card_mono (Set.toFinite _) hB'even
  have hle2 : Nat.card ↥(B.realized K) ≤
      Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) :=
    Nat.card_mono (Set.toFinite _) hsubKC
  have hle4 : Nat.card ↥(evenFix0 6) ≤
      Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := by
    calc Nat.card ↥(evenFix0 6) ≤ Nat.card ↥(B'.realized K) := hle1
      _ = Nat.card ↥(B.realized K) := hcardK.symm
      _ ≤ Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := hle2
  have heqC : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 6 :=
    Set.eq_of_subset_of_ncard_le hsubC (by simpa using hle4)
  have hle5 : Nat.card ↥(evenFix0 6) ≤ Nat.card ↥(B.realized K) := by
    calc Nat.card ↥(evenFix0 6) ≤ Nat.card ↥(B'.realized K) := hle1
      _ = Nat.card ↥(B.realized K) := hcardK.symm
  have heqK : B.realized K = evenFix0 6 :=
    Set.eq_of_subset_of_ncard_le (hsubKC.trans hsubC) (by simpa using hle5)
  exact ⟨heqC.trans heqK.symm, heqK⟩

private theorem inner_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {c : G}
    (hc : c ∈ Subgroup.centralizer ({b₀} : Set G)) :
    ∃ k ∈ K, ∀ y ∈ K, c * y * c⁻¹ = k * y * k⁻¹ := by
  have hstd' : StdLoc b₀ K E Row.D6 := hstd
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, hKn, hcenter, -, -, -, -⟩ := hA
  obtain ⟨hrow, -, hsup, hmaxA, hcardA, -⟩ := hCanon
  have hCK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hcNK : c ∈ Subgroup.normalizer (K : Set G) := hCK hc
  have hA'K : (E ⊓ K).map (MulAut.conj c).toMonoidHom ≤ K := by
    rintro x ⟨a, ha, rfl⟩
    change c * a * c⁻¹ ∈ K
    exact (Subgroup.mem_normalizer_iff.mp hcNK a).mp ha.2
  have hA'elem : IsElemAbelian 3 ((E ⊓ K).map (MulAut.conj c).toMonoidHom) :=
    hmaxA.2.1.map _
  have hA'card : Nat.card ↥((E ⊓ K).map (MulAut.conj c).toMonoidHom) = 3 ^ Row.D6.n := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcardA]
  obtain ⟨-, hconjA⟩ :=
    rowElemAb3_D6 hrow hcenter (inf_le_right : E ⊓ K ≤ K) hmaxA.2.1 hcardA
  obtain ⟨k₁, hk₁K, hk₁A⟩ := hconjA _ hA'K hA'elem hA'card
  have hk₁C : k₁ ∈ Subgroup.centralizer ({b₀} : Set G) := hKC hk₁K
  have hc₁C : k₁ * c ∈ Subgroup.centralizer ({b₀} : Set G) :=
    (Subgroup.centralizer ({b₀} : Set G)).mul_mem hk₁C hc
  have hcomp : (MulAut.conj k₁).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (k₁ * c)).toMonoidHom := by
    ext x
    change k₁ * (c * x * c⁻¹) * k₁⁻¹ = (k₁ * c) * x * (k₁ * c)⁻¹
    group
  have hc₁A : (E ⊓ K).map (MulAut.conj (k₁ * c)).toMonoidHom = E ⊓ K := by
    rw [← hcomp, ← Subgroup.map_map, hk₁A]
  have hc₁Amem : k₁ * c ∈ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hc₁A
  have hcomm₁ : (k₁ * c) * b₀ = b₀ * (k₁ * c) := by
    rw [mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp hc, ← mul_assoc,
      Subgroup.mem_centralizer_singleton_iff.mp hk₁C, mul_assoc]
  have hc₁z : k₁ * c ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    change (k₁ * c) * b₀ * (k₁ * c)⁻¹ = b₀
    exact mul_inv_eq_iff_eq_mul.mpr hcomm₁
  have hc₁E : k₁ * c ∈ Subgroup.normalizer (E : Set G) := by
    rw [← hsup]
    exact Subgroup.inf_normalizer_le_normalizer_sup (Subgroup.zpowers b₀) (E ⊓ K)
      ⟨hc₁z, hc₁Amem⟩
  have hc₁span : k₁ * c ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hB.1]
    exact hc₁E
  obtain ⟨M, hMActs⟩ := B.exists_acts hc₁span
  have hMmem : M ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) :=
    ⟨k₁ * c, hc₁C, hMActs⟩
  have hMmemK : M ∈ B.realized K := by
    have heq := (eq_D6 hstd' hB hrec).1
    rwa [heq] at hMmem
  obtain ⟨k₂, hk₂K, hk₂Acts⟩ := hMmemK
  let c₂ : G := k₂⁻¹ * (k₁ * c)
  have hc₂fix : ∀ j : Fin 7, c₂ * B.b j * c₂⁻¹ = B.b j := by
    intro j
    have h1 : (k₁ * c) * B.b j * (k₁ * c)⁻¹ = B.vec (fun i => M i j) := hMActs j
    have h2 : k₂ * B.b j * k₂⁻¹ = B.vec (fun i => M i j) := hk₂Acts j
    calc c₂ * B.b j * c₂⁻¹
        = k₂⁻¹ * ((k₁ * c) * B.b j * (k₁ * c)⁻¹) * k₂ := by
          simp only [c₂]
          group
      _ = k₂⁻¹ * (B.vec (fun i => M i j)) * k₂ := by rw [h1]
      _ = k₂⁻¹ * (k₂ * B.b j * k₂⁻¹) * k₂ := by rw [h2]
      _ = B.b j := by group
  have hc₂centE : ∀ y ∈ E, c₂ * y * c₂⁻¹ = y := by
    intro y hy
    have hy' : y ∈ B.span := by rwa [hB.1]
    have hfix : ∀ j : Fin 7, (MulAut.conj c₂) (B.b j) = B.b j := fun j => hc₂fix j
    have h := Subgroup.closure_induction (k := Set.range B.b)
      (p := fun y _ => (MulAut.conj c₂) y = y)
      (fun x hx => by
        obtain ⟨j, rfl⟩ := hx
        exact hfix j)
      (by simp)
      (fun x y _ _ ihx ihy => by rw [map_mul, ihx, ihy])
      (fun x _ ih => by rw [map_inv, ih]) hy'
    show c₂ * y * c₂⁻¹ = y
    exact h
  have hc₂centA : ∀ a ∈ E ⊓ K, c₂ * a * c₂⁻¹ = a := by
    intro a ha
    exact hc₂centE a ha.1
  have hc₂C : c₂ ∈ Subgroup.centralizer ({b₀} : Set G) := by
    have h1 : k₂⁻¹ ∈ Subgroup.centralizer ({b₀} : Set G) :=
      (Subgroup.centralizer ({b₀} : Set G)).inv_mem (hKC hk₂K)
    exact (Subgroup.centralizer ({b₀} : Set G)).mul_mem h1 hc₁C
  have hc₂NK : c₂ ∈ Subgroup.normalizer (K : Set G) := hCK hc₂C
  obtain ⟨-, ⟨e⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_D6 hrow hcenter
  have hQ : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
  have hdim : Module.finrank (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2) = 2 * 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType
      (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2)) ↔ Even 6 :=
    ⟨fun _ => ⟨3, rfl⟩,
      fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (ZMod 2) 6⟩
  obtain ⟨k, hkK, hk⟩ := exists_inner_of_centralizes hQ hdim htype
    omegaAutIsometric_quadPlus_six e hmaxA hc₂NK hc₂centA
  refine ⟨k₁⁻¹ * k₂ * k, ?_, ?_⟩
  · exact K.mul_mem (K.mul_mem (K.inv_mem hk₁K) hk₂K) hkK
  intro y hy
  have hc_eq : c = k₁⁻¹ * k₂ * c₂ := by
    simp only [c₂]
    group
  rw [hc_eq]
  calc (k₁⁻¹ * k₂ * c₂) * y * (k₁⁻¹ * k₂ * c₂)⁻¹
      = k₁⁻¹ * k₂ * (c₂ * y * c₂⁻¹) * (k₁⁻¹ * k₂)⁻¹ := by group
    _ = k₁⁻¹ * k₂ * (k * y * k⁻¹) * (k₁⁻¹ * k₂)⁻¹ := by rw [hk y hy]
    _ = (k₁⁻¹ * k₂ * k) * y * (k₁⁻¹ * k₂ * k)⁻¹ := by group

theorem realized_centralizer_subset_evenFix0_D6 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.D6 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 Row.D6.n :=
  subset_D6 hstd hB hrec

theorem realized_centralizer_eq_realized_D6 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.D6 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) = B.realized K ∧
      B.realized K = evenFix0 Row.D6.n :=
  eq_D6 hstd hB hrec

theorem exists_inner_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) {c : G} (hc : c ∈ Subgroup.centralizer ({b₀} : Set G)) :
    ∃ k ∈ K, ∀ y ∈ K, c * y * c⁻¹ = k * y * k⁻¹ :=
  inner_D6 hstd hB hrec hc

end CFSG.StandardType.FrameRoute.FS81
