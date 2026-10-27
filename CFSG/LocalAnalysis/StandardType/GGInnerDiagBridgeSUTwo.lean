module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag

public section

namespace CFSG.StandardType.InnerDiagSU

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits

private theorem suTwo_two_scalar {F : Type} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    (h1 : M * longRootMatrix (0 : Fin 2) (1 : F) = longRootMatrix 0 1 * M)
    (h2 : M * longRootMatrix (1 : Fin 2) (1 : F) = longRootMatrix 1 1 * M) :
    ∃ c : F, M = Matrix.scalar (Fin 2) c := by
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h2 0) 0
  simp [longRootMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have h10 : M 1 0 = 0 := e1
  have h01 : M 0 1 = 0 := e3
  have h11 : M 1 1 = M 0 0 := by
    have h := e2
    rw [e3, zero_add, add_zero] at h
    exact h.symm
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h10, h01, h11]

private theorem suTwo_center_scalar {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {z : SU (unitaryInvolution F 2 f) 2} (hz : z ∈ Subgroup.center _) :
    ∃ c : F, mat (unitaryInvolution F 2 f) 2 z = Matrix.scalar (Fin 2) c := by
  have hcomm : ∀ v : SU (unitaryInvolution F 2 f) 2,
      (↑z : GL (Fin 2) F) * ↑v = ↑v * ↑z := by
    intro v
    exact congrArg (fun w : SU (unitaryInvolution F 2 f) 2 => (w : GL (Fin 2) F))
      (Subgroup.mem_center_iff.mp hz v).symm
  refine suTwo_two_scalar ?_ ?_
  · have hv := hcomm (longRootHom (unitaryInvolution F 2 f)
      (show (0 : Fin 2) ≠ Fin.rev 0 from by decide)
      (Multiplicative.ofAdd oneTZ))
    have hmat := congrArg (fun A : GL (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F)) hv
    simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ, mat_apply] using hmat
  · have hv := hcomm (longRootHom (unitaryInvolution F 2 f)
      (show (1 : Fin 2) ≠ Fin.rev 1 from by decide)
      (Multiplicative.ofAdd oneTZ))
    have hmat := congrArg (fun A : GL (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F)) hv
    simpa only [Units.val_mul, coe_longRootHom, toAdd_ofAdd, oneTZ, mat_apply] using hmat

private theorem suTwo_toBlock_mul_four {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {p : Fin n}
    (hp : p ≠ Fin.rev p) {a b c d : SU σ n}
    (ha : IsBlk (blkPair p) (mat σ n a)) (hb : IsBlk (blkPair p) (mat σ n b))
    (hc : IsBlk (blkPair p) (mat σ n c)) :
    SUExtras.toBlock p (Fin.rev p) (mat σ n (a * b * c * d)) =
      SUExtras.toBlock p (Fin.rev p) (mat σ n a) *
        SUExtras.toBlock p (Fin.rev p) (mat σ n b) *
        SUExtras.toBlock p (Fin.rev p) (mat σ n c) *
        SUExtras.toBlock p (Fin.rev p) (mat σ n d) := by
  rw [map_mul, map_mul, map_mul,
    toBlock_mul hp (blkPair_hblk p) (blkPair_rev p) ((ha.mul hb).mul hc),
    toBlock_mul hp (blkPair_hblk p) (blkPair_rev p) (ha.mul hb),
    toBlock_mul hp (blkPair_hblk p) (blkPair_rev p) ha]

private theorem suTwo_eq_one_of_rankOne_long {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {p : Fin 2} (hp : p ≠ Fin.rev p)
    {G : Type*} [Group G] (β γ : SU (unitaryInvolution F 2 f) 2 →* G)
    (hker : γ.ker ≤ Subgroup.center _) (e : F)
    (hpos : ∀ z : traceZero (unitaryInvolution F 2 f),
      β (longRootHom _ hp (Multiplicative.ofAdd z)) = γ (longRootHom _ hp (Multiplicative.ofAdd z)))
    (hneg : ∀ z : traceZero (unitaryInvolution F 2 f), ∃ z' : traceZero (unitaryInvolution F 2 f),
      (z' : F) = e * z ∧ β (longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z)) =
        γ (longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z'))) : e = 1 := by
  obtain ⟨z', hz'e, hz'⟩ := hneg oneTZ
  have hz'v : (z' : F) = e := by rw [hz'e]; exact mul_one e
  set X : traceZero (unitaryInvolution F 2 f) → SU (unitaryInvolution F 2 f) 2 :=
    fun z => longRootHom _ hp (Multiplicative.ofAdd z) with hX
  set Y : traceZero (unitaryInvolution F 2 f) → SU (unitaryInvolution F 2 f) 2 :=
    fun z => longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z) with hY
  have hmX : ∀ z, mat _ 2 (X z) = longRootMatrix p (z : F) := fun z => by
    rw [mat_apply, hX, coe_longRootHom, toAdd_ofAdd]
  have hmY : ∀ z, mat _ 2 (Y z) = longRootMatrix (Fin.rev p) (z : F) := fun z => by
    rw [mat_apply, hY, coe_longRootHom, toAdd_ofAdd]
  have hbX : ∀ z, IsBlk (blkPair p) (mat _ 2 (X z)) := fun z => by
    rw [hmX]; exact isBlk_longRootMatrix p _
  have hbY : ∀ z, IsBlk (blkPair p) (mat _ 2 (Y z)) := fun z => by
    rw [hmY]; exact isBlk_longRootMatrix_rev p _
  have htX : ∀ z, SUExtras.toBlock p (Fin.rev p) (mat _ 2 (X z)) = !![1, (z : F); 0, 1] :=
    fun z => by rw [hmX]; exact toBlock_longRootMatrix hp _
  have htY : ∀ z, SUExtras.toBlock p (Fin.rev p) (mat _ 2 (Y z)) = !![1, 0; (z : F), 1] :=
    fun z => by rw [hmY]; exact toBlock_longRootMatrix_rev hp _
  have hbase : Y oneTZ * X oneTZ * Y oneTZ * X oneTZ = X oneTZ * Y oneTZ * X oneTZ * X oneTZ := by
    apply mat_injective
    refine eq_of_isBlk_blkPair (p := p) ?_ ?_ ?_
    · rw [map_mul, map_mul, map_mul]
      exact (((hbY _).mul (hbX _)).mul (hbY _)).mul (hbX _)
    · rw [map_mul, map_mul, map_mul]
      exact (((hbX _).mul (hbY _)).mul (hbX _)).mul (hbX _)
    · rw [suTwo_toBlock_mul_four hp (hbY _) (hbX _) (hbY _),
        suTwo_toBlock_mul_four hp (hbX _) (hbY _) (hbX _), htX, htY]
      exact block_identity
  have hγ : γ (Y z' * X oneTZ * Y z' * X oneTZ) = γ (X oneTZ * Y z' * X oneTZ * X oneTZ) := by
    have h := congrArg β hbase
    simp only [map_mul] at h
    rw [hpos, hz'] at h
    simpa only [map_mul] using h
  have hz : (X oneTZ * Y z' * X oneTZ * X oneTZ)⁻¹ * (Y z' * X oneTZ * Y z' * X oneTZ) ∈
      Subgroup.center _ :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hγ, inv_mul_cancel])
  obtain ⟨c, hc⟩ := suTwo_center_scalar (z := _) hz
  have hB : mat _ 2 (Y z' * X oneTZ * Y z' * X oneTZ) =
      mat _ 2 (X oneTZ * Y z' * X oneTZ * X oneTZ) * Matrix.scalar (Fin 2) c := by
    rw [← hc, ← map_mul, mul_inv_cancel_left]
  have hblk := congrArg (SUExtras.toBlock p (Fin.rev p)) hB
  rw [toBlock_mul_scalar, suTwo_toBlock_mul_four hp (hbY _) (hbX _) (hbY _),
    suTwo_toBlock_mul_four hp (hbX _) (hbY _) (hbX _), htX, htY, hz'v] at hblk
  exact eq_one_of_block_eq_smul hblk

private theorem suTwo_levelWeyl_agree_last {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {k : Fin (2 / 2)} (hk : ¬ k.val + 1 < 2 / 2)
    {G : Type*} [Group G] (ψ β : SU (unitaryInvolution F 2 f) 2 →* G)
    (d : Fin 2 → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1)
    (hker : (ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd))).ker ≤ Subgroup.center _)
    (hpos : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) 2 (Pi.single k 1),
      β z = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z))
    (t : Fin 2 → F) (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1)
    (hneg : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) 2 (-Pi.single k 1),
      β z = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z)) :
    β (levelWeyl (unitaryInvolution_involutive hF) oneTZ k) =
      ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)
        (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)) := by
  have hp := lowIdx_ne_rev (n := 2) k k
  have hp' := rev_ne_rev_rev hp
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have h0t := ne_zero_of_unitary ht
  have h0d := ne_zero_of_unitary hd
  have hdi : ∀ s, unitaryInvolution F 2 f ((d s)⁻¹) * (d (Fin.rev s))⁻¹ = 1 := fun s => by
    rw [map_inv₀, ← mul_inv, hd s, inv_one]
  set p := lowIdx (n := 2) k with hpdef
  set e := (d (Fin.rev p))⁻¹ * t (Fin.rev p) * (t (Fin.rev (Fin.rev p)))⁻¹ *
    d (Fin.rev (Fin.rev p)) with he
  have hX : ∀ z, β (longRootHom _ hp (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp (Multiplicative.ofAdd z)) := fun z =>
    hpos _ (longRootHom_mem_last hF hk z).1
  have hY : ∀ z : traceZero (unitaryInvolution F 2 f), ∃ z' : traceZero (unitaryInvolution F 2 f),
      (z' : F) = e * z ∧ β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
        γ' (longRootHom _ hp' (Multiplicative.ofAdd z')) := by
    intro z
    set w : traceZero (unitaryInvolution F 2 f) :=
      ⟨t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹, (mem_traceZero _).mpr
        (mul_mem_traceZero_of_unitary ht (Fin.rev p) ((mem_traceZero _).mp z.2))⟩ with hw
    refine ⟨⟨(d (Fin.rev p))⁻¹ * w * ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹, (mem_traceZero _).mpr
      (mul_mem_traceZero_of_unitary hdi (Fin.rev p) ((mem_traceZero _).mp w.2))⟩, ?_, ?_⟩
    · show (d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
        ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹ = e * z
      rw [he, inv_inv]
      ring
    · rw [hneg _ (longRootHom_mem_last hF hk z).2]
      show ψ (conjSU (diagJ t ht) _ (longRootHom _ hp' (Multiplicative.ofAdd z))) =
        ψ (conjSU (diagJ d hd) _ (longRootHom _ hp' (Multiplicative.ofAdd _)))
      rw [conjSU_diagJ_longRootHom, conjSU_diagJ_longRootHom]
      congr 1
      apply longRootHom_congr
      show t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹ =
        d (Fin.rev p) * ((d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
          ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹) * (d (Fin.rev (Fin.rev p)))⁻¹
      field_simp [h0d (Fin.rev p), h0d (Fin.rev (Fin.rev p)), h0t (Fin.rev (Fin.rev p))]
      rw [mul_div_mul_right _ _ (h0d _)]
  have he1 : e = 1 := suTwo_eq_one_of_rankOne_long hp β γ' hker e hX hY
  have hY1 : ∀ z, β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp' (Multiplicative.ofAdd z)) := by
    intro z
    obtain ⟨z', hz', h⟩ := hY z
    rw [h, longRootHom_congr hp' (by rw [hz', he1, one_mul] : (z' : F) = z)]
  show β (levelWeyl _ oneTZ k) = γ' (levelWeyl _ oneTZ k)
  unfold levelWeyl
  rw [dite_eq_right hk, longWeyl_def]
  simp only [map_mul, hX, hY1]

private theorem suTwo_exists_diagJ_of_torus {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) 2 →* G) (hker : ψ.ker ≤ Subgroup.center _) (x : G)
    (hx : ∀ γ ∈ (rootDatum hF 2).roots, ∃ h ∈ ggTorus (rootDatum hF 2),
      ∀ z ∈ (rootDatum hF 2).rootGroup γ, x⁻¹ * ψ z * x = ψ (h * z * h⁻¹)) :
    ∃ (d : Fin 2 → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1),
      ∀ u, x⁻¹ * ψ u * x = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) u) := by
  have hσ := unitaryInvolution_involutive hF
  have hsr : (Pi.single (0 : Fin (2 / 2)) 1 : Fin (2 / 2) → ℤ) ∈ (rootDatum hF 2).roots :=
    single_mem_roots (D := rootDatum hF 2) (0 : Fin (2 / 2))
  have hnr : (-Pi.single (0 : Fin (2 / 2)) 1 : Fin (2 / 2) → ℤ) ∈ (rootDatum hF 2).roots :=
    neg_single_mem_roots (D := rootDatum hF 2) (0 : Fin (2 / 2))
  obtain ⟨h₁, hh₁, hz₁⟩ := hx _ hsr
  obtain ⟨h₂, hh₂, hz₂⟩ := hx _ hnr
  obtain ⟨hd₁, huni₁⟩ := eq_diagonal_of_mem_ggTorus hF hh₁
  obtain ⟨hd₂, huni₂⟩ := eq_diagonal_of_mem_ggTorus hF hh₂
  set d : Fin 2 → F := fun s => mat _ 2 h₁ s s with hddef
  set t : Fin 2 → F := fun s => mat _ 2 h₂ s s with htdef
  have hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1 := by
    intro s; rw [hddef]; exact huni₁ s
  have ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1 := by
    intro s; rw [htdef]; exact huni₂ s
  set β : SU (unitaryInvolution F 2 f) 2 →* G := (MulAut.conj x⁻¹).toMonoidHom.comp ψ with hβ
  have hβx : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [hβ]
  set γ' : SU (unitaryInvolution F 2 f) 2 →* G :=
    ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have hker' : γ'.ker ≤ Subgroup.center _ := ker_comp_conjSU_le_center ψ hker _ _
  have hpos0 : ∀ z ∈ rootGroup _ hσ 2 (Pi.single (0 : Fin (2 / 2)) 1),
      β z = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z) := by
    intro z hz
    rw [hβx, hz₁ z hz, conj_eq_conjSU_diagJ hd₁ huni₁]
  have hneg0 : ∀ z ∈ rootGroup _ hσ 2 (-Pi.single (0 : Fin (2 / 2)) 1),
      β z = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z) := by
    intro z hz
    rw [hβx, hz₂ z hz, conj_eq_conjSU_diagJ hd₂ huni₂]
  have hsingle : ∀ a b : Fin (2 / 2), a = b := by
    intro a b
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    norm_num at ha hb
    omega
  have hA : ∀ k : Fin (2 / 2), ∀ z ∈ rootGroup _ hσ 2 (Pi.single k 1), β z = γ' z := by
    intro k z hz
    rw [hsingle k (0 : Fin (2 / 2))] at hz
    simpa only [hγ', MonoidHom.comp_apply] using hpos0 z hz
  have hW : ∀ k : Fin (2 / 2), β (levelWeyl hσ oneTZ k) = γ' (levelWeyl hσ oneTZ k) := by
    intro k
    rw [hsingle k (0 : Fin (2 / 2))]
    have h := suTwo_levelWeyl_agree_last hF (by norm_num) ψ β d hd hker' hpos0 t ht hneg0
    simpa only [hγ', MonoidHom.comp_apply] using h
  have hE : β.eqLocus γ' = ⊤ :=
    eq_top_of_rankOne_le (isCTGroupDatum hF 2 le_rfl oneTZ one_ne_zero) _ fun k =>
      sup_le (fun z hz => hA k z hz)
        (fun y hy => agree_neg_of_levelWeyl hF le_rfl β γ' (hA k) (hW k) y hy)
  refine ⟨d, hd, ?_⟩
  intro u
  have hu : u ∈ β.eqLocus γ' := by rw [hE]; exact Subgroup.mem_top u
  rw [← hβx]
  exact hu

theorem suInnerDiagConj_two {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) : SUInnerDiagConj hF 2 := by
  intro G _ ψ hker c hc
  obtain ⟨g, ⟨s, rfl⟩, hγ⟩ := hc
  obtain ⟨d, hd, hD⟩ := suTwo_exists_diagJ_of_torus hF ψ hker (c * ψ s) hγ
  refine ⟨(s : GL (Fin 2) F) * diagJ d hd,
    (isJUnitary_of_mem_SU s).mul (isJUnitary_diagJ d hd), fun u => ?_⟩
  have h1 : c⁻¹ * ψ u * c = ψ s * ((c * ψ s)⁻¹ * ψ u * (c * ψ s)) * (ψ s)⁻¹ := by group
  rw [h1, hD u, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSU]
  group

end CFSG.StandardType.InnerDiagSU
