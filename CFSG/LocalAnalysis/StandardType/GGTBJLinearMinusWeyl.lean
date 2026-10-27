module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNsNorm
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrameSigned
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.CoordSL

open Polynomial Matrix CFSG.RankThree.CALinearPlane

@[expose] noncomputable def frameSigned {G : Type} [Group G] {F : Type} [Field F] {g : F[X]}
    [Fact (Irreducible g)] {n s t p : ℕ} [NeZero p]
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) (A₀ : Matrix.SpecialLinearGroup (Fin n) F)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin t)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1) :
    (Fin s → Multiplicative (ZMod p)) →* G :=
  (frameHom ψ A₀ ε hC hCp).comp
    (MulEquiv.piMultiplicative fun _ : Fin s => ZMod p).symm.toMonoidHom

variable {G : Type} [Group G] {F : Type} [Field F] {g : F[X]}
  [Fact (Irreducible g)] {n s t p : ℕ} [NeZero p]

@[simp] theorem frameSigned_apply
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) (A₀ : Matrix.SpecialLinearGroup (Fin n) F)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin t)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1)
    (f : Fin s → Multiplicative (ZMod p)) :
    frameSigned ψ A₀ ε hC hCp f =
      SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC fun i => (Multiplicative.toAdd (f i)).val) := by
  change (frameHom ψ A₀ ε hC hCp) ((MulEquiv.piMultiplicative fun x => ZMod p).symm f) = _
  rw [MulEquiv.piMultiplicative_symm_apply, frameHom_apply, SLRep.ggFrame_apply]

variable {K : Type} [Field K]

theorem coordBlockSL_mono {n : ℕ} {J J' : Finset (Fin n)} (h : J ⊆ J') :
    coordBlockSL K J ≤ coordBlockSL K J' := by
  intro g hg
  rw [mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun hi' hiJ => hi' (h hiJ)) (fun hj' hjJ => hj' (h hjJ)))

variable {g : K[X]} [Fact (Irreducible g)] {s r : ℕ} {β : Fin s → ZMod p}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}

omit [NeZero p] in
private theorem blockAct_comm_projN {S : Finset (Fin s)}
    (hS : ∀ i ∈ S, β i = 0)
    {m : Matrix (Fin s) (Fin s) (AdjoinRoot g)}
    (hm : ∀ i j, (i ∉ S ∨ j ∉ S) → m i j = if i = j then 1 else 0) :
    projN (r := r) β ∘ₗ blockAct g m = projN (r := r) β ∧
      blockAct g m ∘ₗ projN (r := r) β = projN (r := r) β := by
  have hrow : ∀ i, i ∉ S → ∀ j, m i j = if i = j then 1 else 0 :=
    fun i hi j => hm i j (Or.inl hi)
  have hcol : ∀ j, j ∉ S → ∀ i, m i j = if i = j then 1 else 0 :=
    fun j hj i => hm i j (Or.inr hj)
  constructor
  · refine LinearMap.ext fun x => Prod.ext (funext fun i => ?_) rfl
    simp only [LinearMap.comp_apply, blockAct_apply, projN_apply]
    by_cases hi : β i = 0
    · simp [hi]
    · have hiS : i ∉ S := fun h => hi (hS i h)
      have hsum : (m *ᵥ x.1) i = x.1 i := by
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
        · rw [hrow i hiS i, if_pos rfl, one_mul]
        · intro j _ hji
          rw [hrow i hiS j, if_neg (Ne.symm hji), zero_mul]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      simp [hi, hsum]
  · refine LinearMap.ext fun x => Prod.ext (funext fun i => ?_) rfl
    simp only [LinearMap.comp_apply, blockAct_apply, projN_apply]
    set y : Fin s → AdjoinRoot g := fun j => if β j = 0 then 0 else x.1 j with hy
    change (m *ᵥ y) i = y i
    by_cases hi : β i = 0
    · have hyi : y i = 0 := by simp [hy, hi]
      rw [hyi, Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hiS : i ∈ S
      · by_cases hjS : j ∈ S
        · simp [hy, hS j hjS]
        · rw [hcol j hjS i, if_neg (by rintro rfl; exact hjS hiS), zero_mul]
      · rw [hrow i hiS j]
        by_cases hji : i = j
        · subst hji
          simp [hy, hi]
        · rw [if_neg hji, zero_mul]
    · have hiS : i ∉ S := fun h => hi (hS i h)
      have hsum : (m *ᵥ y) i = y i := by
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
        · rw [hrow i hiS i, if_pos rfl, one_mul]
        · intro j _ hji
          rw [hrow i hiS j, if_neg (Ne.symm hji), zero_mul]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
      rw [hsum]

omit [NeZero p] in
private theorem theta_mem_zeroBlock {S : Finset (Fin s)}
    (hS : ∀ i ∈ S, β i = 0)
    {M : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) S) :
    theta g ε M ∈ coordBlockSL K (zeroCoords ε β) := by
  obtain ⟨h1, h2⟩ := blockAct_comm_projN (r := r) (g := g) (β := β) hS
    (m := (M : Matrix (Fin s) (Fin s) (AdjoinRoot g))) (mem_coordBlockSL_iff.mp hM)
  refine ⟨?_, ?_⟩
  · rw [coe_theta]
    apply frameForm_injective g ε
    rw [frameForm_mul, frameForm_compIndicator, frameForm_thetaMat]
    exact h1
  · rw [coe_theta]
    apply frameForm_injective g ε
    rw [frameForm_mul, frameForm_thetaMat, frameForm_compIndicator]
    exact h2



private theorem torusSL_pow_p {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r p : ℕ} [NeZero p] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1} (hCp : rootMat g ^ p = 1) (t : Fin s → ZMod p) :
    (SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd t)) ^ p = 1 := by
  have ht : (Multiplicative.ofAdd t : Multiplicative (Fin s → ZMod p)) ^ p = 1 := by
    change p • t = 0
    funext i
    simp [nsmul_eq_mul]
  rw [← map_pow, ht, map_one]

private theorem eq_one_of_mem_center_of_pow_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p : ℕ} [Fact p.Prime] (hpF : p ∣ Nat.card K + 1)
    {z : Matrix.SpecialLinearGroup (Fin n) K}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) (hzp : z ^ p = 1) :
    z = 1 := by
  have hp2 : p ≠ 2 := CFSG.StandardType.SpNS.ne_two_of_dvd_card_add_one hpF
  have hK : ¬ p ∣ Nat.card K - 1 :=
    CFSG.StandardType.SpNS.not_dvd_card_sub_one Fact.out hp2 hpF
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  by_cases hn : n = 0
  · subst hn
    exact Subtype.ext (Subsingleton.elim _ _)
  · have hi : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hcp : c ^ p = 1 := by
      have hmat : ((z : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_pow, hzp, Matrix.SpecialLinearGroup.coe_one]
      rw [← hc, ← map_pow] at hmat
      have hii := congrFun (congrFun hmat hi) hi
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using hii
    have hc1 : c = 1 := CFSG.StandardType.OrdPNS.eq_one_of_pow_eq_one Fact.out hK hcp
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl


private theorem signedPerm_eq_of_rel {p : ℕ} [Fact p.Prime]
    {s : ℕ} {π : Equiv.Perm (Fin s)} {σ : Fin s → ZMod p}
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {t t' : Fin s → ZMod p} (hrel : ∀ i, t' (π i) = σ i * t i)
    {f f' : Fin s → Multiplicative (ZMod p)}
    (ht : ∀ i, t i = Multiplicative.toAdd (f i))
    (ht' : ∀ i, t' i = Multiplicative.toAdd (f' i)) :
    f' = fun i => f (π.symm i) ^ (if σ (π.symm i) = 1 then (1 : ℤ) else -1) := by
  funext j
  have h := hrel (π.symm j)
  rw [Equiv.apply_symm_apply] at h
  change Multiplicative.toAdd (f' j) =
    Multiplicative.toAdd (f (π.symm j) ^ (if σ (π.symm j) = 1 then (1 : ℤ) else -1))
  by_cases hj : σ (π.symm j) = 1
  · rw [if_pos hj, zpow_one, ← ht' j, ← ht (π.symm j), h, hj, one_mul]
  · have hneg : σ (π.symm j) = -1 := (hσ _).resolve_left hj
    rw [if_neg hj, _root_.zpow_neg_one, toAdd_inv, ← ht' j, ← ht (π.symm j), h, hneg]
    exact neg_one_mul _

private theorem frameSigned_ofAdd {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r p : ℕ} [NeZero p] {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
    {A₁ : Matrix.SpecialLinearGroup (Fin n) K}
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1} (u : Fin s → ZMod p) :
    frameSigned ψ A₁ ε hC hCp (fun i => Multiplicative.ofAdd (u i)) =
      SLRep.ggFrame ψ A₁ (SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd u)) := by
  simp [frameSigned_apply, SlNsRootGen.torusSL_apply, toAdd_ofAdd]

private theorem ofAdd_coordPerm_swap {p : ℕ} (i j : Fin s)
    (f : Fin s → Multiplicative (ZMod p)) :
    (fun m => Multiplicative.ofAdd
      (SlNsRootGen.swapMap i j (fun m => Multiplicative.toAdd (f m)) m)) =
      SpJoin.coordPerm s p (Equiv.swap i j) f := by
  funext m
  rw [SpJoin.coordPerm_apply, SlNsRootGen.swapMap]
  simp [Equiv.symm_swap]

private theorem ofAdd_coordInv {p : ℕ} (i : Fin s)
    (f : Fin s → Multiplicative (ZMod p)) :
    (fun m => Multiplicative.ofAdd
      (SlNsRootGen.negMap i (fun m => Multiplicative.toAdd (f m)) m)) =
      SpJoin.coordInv s p i f := by
  funext m
  rw [SpJoin.coordInv_apply, SlNsRootGen.negMap, Function.update_apply]
  by_cases hm : m = i
  · subst hm
    simp
  · simp [hm]

private theorem ggFrame_conj_torus {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r p : ℕ} [NeZero p] {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
    {A₁ : Matrix.SpecialLinearGroup (Fin n) K}
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}
    {w : Matrix.SpecialLinearGroup (Fin n) K} {t t' : Fin s → ZMod p}
    (hw : w * SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd t) * w⁻¹ =
      SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd t')) :
    SLRep.ggFrame ψ A₁ w * frameSigned ψ A₁ ε hC hCp (fun i => Multiplicative.ofAdd (t i)) *
      (SLRep.ggFrame ψ A₁ w)⁻¹ =
      frameSigned ψ A₁ ε hC hCp (fun i => Multiplicative.ofAdd (t' i)) := by
  have h := congrArg (SLRep.ggFrame ψ A₁) hw
  rw [map_mul, map_mul, map_inv] at h
  simpa [frameSigned_apply, SlNsRootGen.torusSL_apply] using h


theorem signed_of_frame
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    [Fact p.Prime] (hpF : p ∣ Nat.card F + 1)
    {g : F[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p F)
    (hζ : AdjoinRoot.root g ^ p = 1) {hC : (rootMat g).det = 1}
    {hCp : rootMat g ^ p = 1} {s t : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin t)
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (A₁ : Matrix.SpecialLinearGroup (Fin n) F) :
    (∀ x ∈ ψ.range, (∀ f, ∃ f', x * frameSigned ψ A₁ ε hC hCp f * x⁻¹ =
        frameSigned ψ A₁ ε hC hCp f') →
      ∃ σ ∈ SpJoin.spSignedGroup s p, ∀ f,
        x * frameSigned ψ A₁ ε hC hCp f * x⁻¹ = frameSigned ψ A₁ ε hC hCp (σ f)) ∧
    ∀ i : Fin s, ∃ m ∈ ψ.range, ∀ f,
      m * frameSigned ψ A₁ ε hC hCp f * m⁻¹ =
        frameSigned ψ A₁ ε hC hCp (SpJoin.spReflPerm s p i f) := by
  classical
  have hp2 : p ≠ 2 := CFSG.StandardType.SpNS.ne_two_of_dvd_card_add_one hpF
  have hkerφ : (SLRep.ggFrame ψ A₁).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := SLRep.ker_ggFrame_le hker A₁
  constructor
  · rintro x ⟨u, rfl⟩ hx
    set v : Matrix.SpecialLinearGroup (Fin n) F := A₁⁻¹ * u * A₁ with hv
    have hgu : SLRep.ggFrame ψ A₁ v = ψ u := by
      rw [SLRep.ggFrame_apply]
      congr 1
      simp [hv]
      group
    have hgg_of : ∀ (a : Fin s → ZMod p) (f' : Fin s → Multiplicative (ZMod p)),
        ψ u * frameSigned ψ A₁ ε hC hCp (fun i => Multiplicative.ofAdd (a i)) * (ψ u)⁻¹ =
          frameSigned ψ A₁ ε hC hCp f' →
        SLRep.ggFrame ψ A₁ (v * SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a) * v⁻¹) =
          SLRep.ggFrame ψ A₁
            (SlNsRootGen.torusSL ε hC hCp
              (Multiplicative.ofAdd fun i => Multiplicative.toAdd (f' i))) := by
      intro a f' hf'
      rw [map_mul, map_mul, map_inv, hgu]
      simpa [frameSigned_ofAdd, SlNsRootGen.torusSL_apply] using hf'
    have hz_eq : ∀ (a a' : Fin s → ZMod p),
        SLRep.ggFrame ψ A₁ (v * SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a) * v⁻¹) =
          SLRep.ggFrame ψ A₁ (SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a')) →
        v * SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a) * v⁻¹ =
          SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a') := by
      intro a a' hgg
      set T := SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a) with hT
      set T' := SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a') with hT'
      have hTp : T ^ p = 1 := torusSL_pow_p hCp a
      have hT'p : T' ^ p = 1 := torusSL_pow_p hCp a'
      set z := (v * T * v⁻¹) * T'⁻¹ with hz
      have hzk : z ∈ (SLRep.ggFrame ψ A₁).ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hgg, mul_inv_cancel]
      have hzc := hkerφ hzk
      have hzp : z ^ p = 1 := by
        have hcomm : Commute z T' := (Subgroup.mem_center_iff.mp hzc T').symm
        have hA : v * T * v⁻¹ = z * T' := by rw [hz]; group
        have hAp : (v * T * v⁻¹) ^ p = 1 := by
          rw [conj_pow, hTp, mul_one, mul_inv_cancel]
        calc z ^ p = z ^ p * T' ^ p := by rw [hT'p, mul_one]
          _ = (z * T') ^ p := (hcomm.mul_pow p).symm
          _ = (v * T * v⁻¹) ^ p := by rw [hA]
          _ = 1 := hAp
      have hz1 : z = 1 := eq_one_of_mem_center_of_pow_eq_one hpF hzc hzp
      calc v * T * v⁻¹ = z * T' := by rw [hz]; group
        _ = T' := by rw [hz1, one_mul]
    have hnorm : ∀ a : Fin s → ZMod p, ∃ a',
        v * SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a) * v⁻¹ =
          SlNsRootGen.torusSL ε hC hCp (Multiplicative.ofAdd a') := by
      intro a
      obtain ⟨f', hf'⟩ := hx (fun i => Multiplicative.ofAdd (a i))
      exact ⟨_, hz_eq a _ (hgg_of a f' hf')⟩
    obtain ⟨π, σ, hσ, hrel⟩ :=
      SlNsRootGen.exists_signedPerm_of_conj hpF hgd ε hC hCp v hnorm
    let e : Fin s → ℤ := fun i => if σ i = 1 then 1 else -1
    have he : ∀ i, e i = 1 ∨ e i = -1 := by
      intro i
      by_cases h : σ i = 1 <;> simp [e, h]
    obtain ⟨σperm, hσperm, hact⟩ := signedPerm_mem_spSignedGroup π e he
    refine ⟨σperm, hσperm, fun f => ?_⟩
    obtain ⟨f', hf'⟩ := hx f
    have hrel' : ∀ i, (fun m => Multiplicative.toAdd (f' m)) (π i) =
        σ i * (fun m => Multiplicative.toAdd (f m)) i :=
      hrel (fun m => Multiplicative.toAdd (f m)) (fun m => Multiplicative.toAdd (f' m))
        (hz_eq _ _ (hgg_of _ f' hf'))
    have hfeq : f' = σperm f := by
      rw [hact]
      exact signedPerm_eq_of_rel hσ hrel' (fun i => rfl) (fun i => rfl)
    rwa [hfeq] at hf'
  · intro i
    by_cases hlt : i.val + 1 < s
    · let j : Fin s := ⟨i.val + 1, hlt⟩
      obtain ⟨w, -, hwconj⟩ :=
        SlNsRootGen.exists_swap_mem_pairBlock (K := F) ε hC hCp i j
      refine ⟨SLRep.ggFrame ψ A₁ w, ?_, ?_⟩
      · rw [← SLRep.range_ggFrame]
        exact ⟨_, rfl⟩
      · intro f
        have hconj := ggFrame_conj_torus (ψ := ψ) (A₁ := A₁) (hC := hC)
          (hwconj (fun m => Multiplicative.toAdd (f m)))
        rw [SpJoin.spReflPerm_of_lt s p i hlt]
        rw [show (fun m => Multiplicative.ofAdd (Multiplicative.toAdd (f m))) = f from
          funext fun m => ofAdd_toAdd (f m)] at hconj
        rw [ofAdd_coordPerm_swap i j f] at hconj
        exact hconj
    · obtain ⟨w, -, hwconj⟩ :=
        SlNsRootGen.exists_neg_mem_zeroBlock (K := F) ε hC hCp hζ hpF i
      refine ⟨SLRep.ggFrame ψ A₁ w, ?_, ?_⟩
      · rw [← SLRep.range_ggFrame]
        exact ⟨_, rfl⟩
      · intro f
        have hconj := ggFrame_conj_torus (ψ := ψ) (A₁ := A₁) (hC := hC)
          (hwconj (fun m => Multiplicative.toAdd (f m)))
        rw [SpJoin.spReflPerm_of_not_lt s p i hlt]
        rw [show (fun m => Multiplicative.ofAdd (Multiplicative.toAdd (f m))) = f from
          funext fun m => ofAdd_toAdd (f m)] at hconj
        rw [ofAdd_coordInv i f] at hconj
        exact hconj

theorem zeroBlock_automizer
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    [Fact p.Prime] (hpF : p ∣ Nat.card F + 1)
    {g : F[X]} [Fact (Irreducible g)]
    (hζ : AdjoinRoot.root g ^ p = 1) {hC : (rootMat g).det = 1}
    {hCp : rootMat g ^ p = 1} {s t : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin t)
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₁ : Matrix.SpecialLinearGroup (Fin n) F) (β : Fin s → ZMod p) :
    (∀ x ∈ (coordBlockSL F (zeroCoords ε β)).map (SLRep.ggFrame ψ A₁),
      ∀ f : Fin s → Multiplicative (ZMod p), (∀ i, β i = 0 → f i = 1) →
        x * frameSigned ψ A₁ ε hC hCp f = frameSigned ψ A₁ ε hC hCp f * x) ∧
    (∀ i j : Fin s, β i = 0 → β j = 0 →
      ∃ m ∈ (coordBlockSL F (zeroCoords ε β)).map (SLRep.ggFrame ψ A₁), ∀ f,
        m * frameSigned ψ A₁ ε hC hCp f * m⁻¹ =
          frameSigned ψ A₁ ε hC hCp (SpJoin.coordPerm s p (Equiv.swap i j) f)) ∧
    ∀ i : Fin s, β i = 0 →
      ∃ m ∈ (coordBlockSL F (zeroCoords ε β)).map (SLRep.ggFrame ψ A₁), ∀ f,
        m * frameSigned ψ A₁ ε hC hCp f * m⁻¹ =
          frameSigned ψ A₁ ε hC hCp (SpJoin.coordInv s p i f) := by
  classical
  constructor
  · rintro x ⟨M, hM, rfl⟩ f hf
    rw [frameSigned_apply, ← map_mul, ← map_mul]
    congr 1
    exact (comm_zeroBlock_of_torus (β := β)
      (k := fun i => (Multiplicative.toAdd (f i)).val)
      (fun i hi => by rw [hf i hi]; simp) hM).symm
  constructor
  · intro i j hi hj
    by_cases hij : i = j
    · subst hij
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      intro f
      rw [one_mul, inv_one, mul_one, Equiv.swap_self]
      simp
    · have hS : ∀ m ∈ ({i, j} : Finset (Fin s)), β m = 0 := by
        intro m hm
        rw [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact hi
        · exact hj
      obtain ⟨w, hwmem, hwconj⟩ :=
        SlNsRootGen.exists_swap_mem_pairBlock (K := F) ε hC hCp i j
      have hwz : w ∈ coordBlockSL F (zeroCoords ε β) := by
        obtain ⟨M, hM, hMw⟩ := hwmem
        have hmem := theta_mem_zeroBlock (K := F) (ε := ε) (β := β) hS hM
        rwa [hMw] at hmem
      refine ⟨SLRep.ggFrame ψ A₁ w, ⟨w, hwz, rfl⟩, ?_⟩
      intro f
      have hconj := ggFrame_conj_torus (ψ := ψ) (A₁ := A₁) (hC := hC)
        (hwconj (fun m => Multiplicative.toAdd (f m)))
      rw [show (fun m => Multiplicative.ofAdd (Multiplicative.toAdd (f m))) = f from
        funext fun m => ofAdd_toAdd (f m)] at hconj
      rw [ofAdd_coordPerm_swap i j f] at hconj
      exact hconj
  · intro i hi
    have hle : SlNsRootGen.blockCoords ε i ⊆ zeroCoords ε β := by
      intro x hx
      rcases hε : ε x with ⟨a, m⟩ | z
      · have hm : m = i := (SlNsRootGen.mem_blockCoords_inl hε).mp hx
        rw [mem_zeroCoords_inl hε, hm]
        exact hi
      · exact mem_zeroCoords_inr hε
    obtain ⟨w, hwmem, hwconj⟩ :=
      SlNsRootGen.exists_neg_mem_zeroBlock (K := F) ε hC hCp hζ hpF i
    have hwz : w ∈ coordBlockSL F (zeroCoords ε β) :=
      coordBlockSL_mono hle (show w ∈ coordBlockSL F (SlNsRootGen.blockCoords ε i) from hwmem)
    refine ⟨SLRep.ggFrame ψ A₁ w, ⟨w, hwz, rfl⟩, ?_⟩
    intro f
    have hconj := ggFrame_conj_torus (ψ := ψ) (A₁ := A₁) (hC := hC)
      (hwconj (fun m => Multiplicative.toAdd (f m)))
    rw [show (fun m => Multiplicative.ofAdd (Multiplicative.toAdd (f m))) = f from
      funext fun m => ofAdd_toAdd (f m)] at hconj
    rw [ofAdd_coordInv i f] at hconj
    exact hconj

theorem classBlock_automizer
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    [Fact p.Prime]
    {g : F[X]} [Fact (Irreducible g)]
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1} {s t : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin t)
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₁ : Matrix.SpecialLinearGroup (Fin n) F) (β : Fin s → ZMod p) (c : ZMod p) :
    (∀ x ∈ (coordBlockSL (AdjoinRoot g) (classSet β c)).map
        ((SLRep.ggFrame ψ A₁).comp (theta g ε)),
      ∀ f : Fin s → Multiplicative (ZMod p),
        (∀ i ∈ classSet β c, ∀ j ∈ classSet β c, f i = f j) →
        x * frameSigned ψ A₁ ε hC hCp f = frameSigned ψ A₁ ε hC hCp f * x) ∧
    ∀ i ∈ classSet β c, ∀ j ∈ classSet β c,
      ∃ m ∈ (coordBlockSL (AdjoinRoot g) (classSet β c)).map
          ((SLRep.ggFrame ψ A₁).comp (theta g ε)), ∀ f,
        m * frameSigned ψ A₁ ε hC hCp f * m⁻¹ =
          frameSigned ψ A₁ ε hC hCp (SpJoin.coordPerm s p (Equiv.swap i j) f) := by
  classical
  constructor
  · rintro x ⟨M, hM, rfl⟩ f hconst
    change SLRep.ggFrame ψ A₁ (theta g ε M) * frameSigned ψ A₁ ε hC hCp f =
      frameSigned ψ A₁ ε hC hCp f * SLRep.ggFrame ψ A₁ (theta g ε M)
    rw [frameSigned_apply, ← map_mul, ← map_mul]
    congr 1
    exact comm_classBlock_of_torus (c := c)
      (k := fun i => (Multiplicative.toAdd (f i)).val)
      (fun i j hi hj => by
        rw [hconst i (mem_classSet.mpr hi) j (mem_classSet.mpr hj)]) hM
  · intro i hi j hj
    have hsub : ({i, j} : Finset (Fin s)) ⊆ classSet β c := by
      intro m hm
      rw [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact hi
      · exact hj
    obtain ⟨w, hwmem, hwconj⟩ :=
      SlNsRootGen.exists_swap_mem_pairBlock (K := F) ε hC hCp i j
    obtain ⟨M, hM, hMw⟩ := hwmem
    have hM' : M ∈ coordBlockSL (AdjoinRoot g) (classSet β c) := coordBlockSL_mono hsub hM
    refine ⟨SLRep.ggFrame ψ A₁ (theta g ε M), ⟨M, hM', rfl⟩, ?_⟩
    intro f
    have hw := hwconj (fun m => Multiplicative.toAdd (f m))
    rw [← hMw] at hw
    have hconj := ggFrame_conj_torus (ψ := ψ) (A₁ := A₁) (hC := hC) hw
    rw [show (fun m => Multiplicative.ofAdd (Multiplicative.toAdd (f m))) = f from
      funext fun m => ofAdd_toAdd (f m)] at hconj
    rw [ofAdd_coordPerm_swap i j f] at hconj
    exact hconj


end CFSG.StandardType.CoordSL

end
