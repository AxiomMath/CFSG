module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUWitt

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace RestSU

section Frame

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem inv_eq_of_conjTr_mul {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n) :
    ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      antidiag n * conjTr σ (P : Matrix (Fin n) (Fin n) F) := by
  have hJ := antidiag_mul_self (F := F) n
  have h1 : antidiag n * conjTr σ (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by rw [Matrix.mul_assoc, hP, hJ]
  calc ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (antidiag n * conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)) *
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h1, Matrix.one_mul]
    _ = antidiag n * conjTr σ (P : Matrix (Fin n) (Fin n) F) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem inv_apply_rev {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (h0 : 0 < n) (b : Fin n) :
    ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Fin.rev ⟨0, h0⟩) b =
      σ ((P : Matrix (Fin n) (Fin n) F) b ⟨0, h0⟩) := by
  rw [inv_eq_of_conjTr_mul hP, Matrix.mul_apply, Finset.sum_eq_single ⟨0, h0⟩]
  · simp [antidiag, conjTr]
  · intro k _ hk
    simp only [antidiag, Matrix.of_apply, Fin.rev_rev]
    rw [ite_eq_right hk, zero_mul]
  · simp

theorem mul_single_mul_apply (P R : Matrix (Fin n) (Fin n) F) (i j : Fin n) (c : F)
    (a b : Fin n) : (P * single i j c * R) a b = P a i * c * R j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.single_apply_same]
    · intro k _ hk
      rw [Matrix.single_apply_of_row_ne hk.symm, mul_zero]
    · simp
  · intro k _ hk
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro l _
    rw [Matrix.single_apply_of_col_ne _ _ hk.symm, mul_zero]
  · simp

theorem conj_agrees {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (h0 : 0 < n) {I : Finset (Fin n)}
    (hcol : ∀ a, a ∉ I → (P : Matrix (Fin n) (Fin n) F) a ⟨0, h0⟩ = 0) (c : F) (a b : Fin n)
    (hab : a ∉ I ∨ b ∉ I) :
    ((P : Matrix (Fin n) (Fin n) F) * (1 + single (⟨0, h0⟩ : Fin n) (Fin.rev ⟨0, h0⟩) c) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) a b =
        (1 : Matrix (Fin n) (Fin n) F) a b := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.add_apply, mul_single_mul_apply, inv_apply_rev hP h0]
  rcases hab with ha | hb
  · rw [hcol a ha, zero_mul, zero_mul, add_zero]
  · rw [hcol b hb, map_zero, mul_zero, add_zero]

end Frame

section Block

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem conjTr_frame_mul {Q : GL (Fin (m + 1)) F} (hQ : UFusion.IsUFrame σ Q)
    (g : SU σ (m + 1)) :
    conjTr σ (((Q * (g : GL (Fin (m + 1)) F) : GL (Fin (m + 1)) F)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((Q * (g : GL (Fin (m + 1)) F) : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = antidiag (m + 1) := by
  have hg := (mem_SU.mp g.2).2
  unfold UFusion.IsUFrame at hQ
  rw [Units.val_mul, conjTr_mul]
  calc conjTr σ ((g : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        conjTr σ (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((g : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      conjTr σ ((g : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (conjTr σ (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) *
        ((g : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
          simp only [Matrix.mul_assoc]
    _ = antidiag (m + 1) := by rw [hQ, hg]

theorem conj_mem_suBlock {Q : GL (Fin (m + 1)) F} (hQ : UFusion.IsUFrame σ Q) (g : SU σ (m + 1))
    {I : Finset (Fin (m + 1))}
    (hcol : ∀ a, a ∉ I → ((Q * (g : GL (Fin (m + 1)) F) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) a ⟨0, by omega⟩ = 0)
    {x : SU σ (m + 1)} {c : F}
    (hx : ((x : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + single (⟨0, by omega⟩ : Fin (m + 1)) (Fin.rev ⟨0, by omega⟩) c) :
    g * x * g⁻¹ ∈ UFusion.suBlock Q I := by
  rw [UFusion.mem_suBlock, UFusion.mem_glBlock]
  intro a b hab
  have e : Q * ((g * x * g⁻¹ : SU σ (m + 1)) : GL (Fin (m + 1)) F) * Q⁻¹ =
      (Q * (g : GL (Fin (m + 1)) F)) * (x : GL (Fin (m + 1)) F) *
        (Q * (g : GL (Fin (m + 1)) F))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, Units.val_mul, Units.val_mul, hx]
  exact conj_agrees (conjTr_frame_mul hQ g) _ hcol c a b hab

variable [Finite F] [CharP F 2] {f : ℕ}

theorem exists_SU_col_pair (hF : Nat.card F = (2 ^ f) ^ 2) (hm : 1 ≤ m)
    {Q : GL (Fin (m + 1)) F} (hQ : UFusion.IsUFrame (unitaryInvolution F 2 f) Q)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ g : SU (unitaryInvolution F 2 f) (m + 1), ∀ a, a ≠ i → a ≠ j →
      ((Q * (g : GL (Fin (m + 1)) F) : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) a ⟨0, by omega⟩ = 0 := by
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ := unitaryInvolution_involutive hF
  set z : Fin (m + 1) → F := Pi.single i 1 + Pi.single j 1 with hz
  set Qm := (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hQm
  set Qi := ((Q⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hQi
  set y : Fin (m + 1) → F := Qi *ᵥ z with hy
  have hQQi : Qm * Qi = 1 := by
    rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQy : Qm *ᵥ y = z := by rw [hy, mulVec_mulVec, hQQi, one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h
    have h1 := congrFun h i
    simp [hz, hij.symm] at h1
  have hy0 : y ≠ 0 := by
    intro h
    apply hz0
    rw [← hQy, h, mulVec_zero]
  have hiso : conjTr σ Qi * antidiag (m + 1) * Qi = 1 := by
    unfold UFusion.IsUFrame at hQ
    rw [← hQ]
    calc conjTr σ Qi * (conjTr σ Qm * Qm) * Qi = (conjTr σ Qi * conjTr σ Qm) * (Qm * Qi) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← conjTr_mul, hQQi, conjTr_one, Matrix.one_mul]
  have hσz : (σ ∘ z) = z := by
    funext t
    simp only [Function.comp_apply, hz, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  have hyy : (GGOppRadSpU.suForm σ hσ (m + 1)).β y y = 0 := by
    rw [hy, GGOppRadSpU.suForm_mulVec, hiso, one_mulVec, hσz, hz]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, one_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
    exact CharTwo.add_self_eq_zero 1
  have hmid : GGOppRadSpU.IsMid 0 y := fun a ha => by
    rcases ha with ha | ha
    · exact absurd ha (Nat.not_lt_zero _)
    · exact absurd a.isLt (by omega)
  obtain ⟨g, c, -, hg⟩ := GGOppRadSpU.exists_SU_map_mid hF (m := 0) (n := m + 1) (by omega) hmid
    hy0 hyy
  refine ⟨g, fun a hai haj => ?_⟩
  rw [natRep_apply] at hg
  have hcol : ((Q * (g : GL (Fin (m + 1)) F) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ Pi.single ⟨0, by omega⟩ 1 = c • z := by
    rw [Units.val_mul, ← mulVec_mulVec, hg, mulVec_smul, hQy]
  have h1 := congrFun hcol a
  rw [mulVec_single_one, col_apply] at h1
  rw [h1, Pi.smul_apply, hz, Pi.add_apply, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj,
    add_zero, smul_zero]

end Block

section Long

open CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg

theorem ht_le_of_mem_roots {n : ℕ} {δ : Fin (n / 2) → ℤ}
    (hδ : δ ∈ roots (isFiniteType_cartan n) (divisible n)) : ht δ ≤ (n : ℤ) - 1 := by
  rw [roots_eq] at hδ
  rcases hδ with ⟨i, j, -, -, -, -, h⟩ | ⟨i, -, h⟩ | ⟨hodd, i, -, h⟩
  · rw [ht_eq_of_weight_sub h.symm]
    have := i.isLt
    have := j.isLt
    omega
  · have h' : weight n i - weight n (Fin.rev i) = toStd n δ := by
      rw [weight_rev', sub_neg_eq_add, ← two_nsmul, h]
    rw [ht_eq_of_weight_sub h']
    simp only [Fin.val_rev]
    omega
  · have hn : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
    have hk : Fin.rev (⟨n / 2, by omega⟩ : Fin n) = ⟨n / 2, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    have h' : weight n i - weight n ⟨n / 2, by omega⟩ = toStd n δ := by
      rw [weight_eq_zero_of_rev_eq hk, sub_zero, h]
    rw [ht_eq_of_weight_sub h']
    have := i.isLt
    omega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} [Fact (Nat.Prime 2)]

theorem ggTopRoot_longRoot (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    GGLongRoot (rootDatum hF n) (ggTopRoot n) := by
  refine ⟨1, ggTopRoot n, ggTopRoot_mem_roots hn, fun δ hδ => ?_, ?_⟩
  · exact (ht_le_of_mem_roots hδ).trans (ht_ggTopRoot hn).ge
  · rw [map_one]
    rfl

theorem mat_eq_of_mem_rootGroup_top (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {z : SU (unitaryInvolution F 2 f) n} (hz : z ∈ (rootDatum hF n).rootGroup (ggTopRoot n)) :
    ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + single (⟨0, by omega⟩ : Fin n) (Fin.rev ⟨0, by omega⟩)
        (((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩
          (Fin.rev ⟨0, by omega⟩)) := by
  have hmax : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), ht δ ≤ ht (ggTopRoot n) :=
    fun δ hδ => (ht_le_of_mem_roots hδ).trans (ht_ggTopRoot hn).ge
  exact mat_eq_of_mem_rootGroup_maxHeight (unitaryInvolution_involutive hF) hn
    (ggTopRoot_mem_roots hn) hmax hz

theorem exists_top_root_elt (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    ∃ x₀ ∈ (rootDatum hF n).rootGroup (ggTopRoot n),
      x₀ ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧ x₀ ^ 2 = 1 := by
  set σ := unitaryInvolution F 2 f with hσdef
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hi : i₀ ≠ Fin.rev i₀ := by
    intro h
    have := congrArg Fin.val h
    simp only [hi₀, Fin.val_rev] at this
    omega
  have hL : Fin.rev i₀ ≠ Fin.rev (Fin.rev i₀) := by
    rw [Fin.rev_rev]
    exact hi.symm
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  set x₀ := longRootHom σ hi (Multiplicative.ofAdd ζ) with hx₀
  have hw : 2 • weight n i₀ = toStd n (ggTopRoot n) := by
    rw [toStd_ggTopRoot hn, weight_rev', sub_neg_eq_add, two_nsmul]
  refine ⟨x₀, ?_, ?_, ?_⟩
  · change x₀ ∈ rootGroup σ (unitaryInvolution_involutive hF) n (ggTopRoot n)
    refine (le_sup_right.trans le_sup_left :
      (⨆ (i : Fin n) (hi : i ≠ Fin.rev i) (_ : 2 • weight n i = toStd n (ggTopRoot n)),
        (longRootHom σ hi).range) ≤ _) ?_
    exact Subgroup.mem_iSup_of_mem i₀ (Subgroup.mem_iSup_of_mem hi
      (Subgroup.mem_iSup_of_mem hw ⟨Multiplicative.ofAdd ζ, rfl⟩))
  · intro hc
    set y₀ := longRootHom σ hL (Multiplicative.ofAdd ζ) with hy₀
    have hcomm := congrArg (fun u : SU σ n => ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (Subgroup.mem_center_iff.mp hc y₀)
    simp only [Subgroup.coe_mul, Units.val_mul, hx₀, hy₀, coe_longRootHom, toAdd_ofAdd,
      longRootMatrix, Fin.rev_rev] at hcomm
    have h1 := congrFun (congrFun hcomm i₀) i₀
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      single_mul_single_same, Matrix.add_apply, Matrix.one_apply_eq] at h1
    simp only [single_apply_of_col_ne _ _ hi.symm, single_apply_of_row_ne hi.symm,
      single_apply_same, add_zero, zero_add] at h1
    have h2 : (ζ : F) * ζ = 0 := by linear_combination -h1
    exact hζ (mul_self_eq_zero.mp h2)
  · rw [hx₀, ← map_pow]
    have h2 : (Multiplicative.ofAdd ζ) ^ 2 = 1 := by
      rw [← ofAdd_nsmul, two_nsmul, ← ofAdd_zero]
      congr 1
      apply Subtype.ext
      exact CharTwo.add_self_eq_zero (ζ : F)
    rw [h2, map_one]

end Long

end RestSU

section Inputs

theorem rootPlane_psu_core {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} (hf : 1 ≤ f)
    {ψ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1))
      .PSU (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p ∣ 2 ^ f + 1) :
    ∃ (E : Subgroup G)
      (γ : Fin (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)).rank → ℤ)
      (u : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)) (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        GGRootClass (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) .PSU γ ∧
        E ≤ Subgroup.centralizer
          (ggRootSub (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ γ u :
            Set G) ∧
        r ∈ ggRootSub (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ γ u ∧
        orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := card_galoisField_two_mul 2 f hf
  obtain ⟨Q, hQ, hBT⟩ := ggUnitaryBstarFrameInput_holds G p B Bs x L D J m f hf ψ hctx s1 hp
  obtain ⟨-, ⟨⟨-, -, hDcard, -⟩, -⟩, -, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hrk : 2 ≤ (m + 1) / 2 := hctx.2.2.2.1.2
  have hn : 2 ≤ m + 1 := by omega
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact hctx.j_isComponentOf_inf
  obtain ⟨I, hJI, hDI⟩ := ggUnitarySemisimpleComponentInput_holds G m f hf ψ hker Q hQ D
    (fun g hg => hBT (hctx.d_le_bstar hg)) J hJ
  have hI : 1 < I.card := by
    by_contra hle
    have hbot := UFusion.uFrameBlock_eq_bot_of_card_le_one ψ Q (I := I) (by omega)
    rw [hbot] at hJI
    exact ne_bot_of_isComponentOf' hJ (le_bot_iff.mp hJI)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hI
  obtain ⟨g, hg⟩ := RestSU.exists_SU_col_pair hF (by omega : 1 ≤ m) hQ hij
  obtain ⟨x₀, hx₀, hx₀c, hx₀2⟩ := RestSU.exists_top_root_elt hF hn
  have hblock : ∀ z ∈ (Unitary.rootDatum hF (m + 1)).rootGroup (ggTopRoot (m + 1)),
      g * z * g⁻¹ ∈ UFusion.suBlock Q I := by
    intro z hz
    refine RestSU.conj_mem_suBlock hQ g (fun a ha => hg a (fun h => ha (h ▸ hi))
      (fun h => ha (h ▸ hj))) (RestSU.mat_eq_of_mem_rootGroup_top hF hn hz)
  have hDcent : ∀ d ∈ D, d ∈ Subgroup.centralizer (UFusion.uFrameBlock ψ Q I : Set G) := by
    intro d hd
    obtain ⟨e, he, heI⟩ := hDI d hd
    exact UFusion.mem_centralizer_uFrameBlock he heI
  refine ⟨D, ggTopRoot (m + 1), g, ψ (g * x₀ * g⁻¹), hctx.d_le_bstar, hctx.d_elem, hDcard,
    ⟨ggTopRoot_mem_roots hn, fun _ => RestSU.ggTopRoot_longRoot hF hn⟩, ?_,
    ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩, ?_, fun e he _ => Or.inl he⟩
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hmem : ψ ((MulAut.conj g).toMonoidHom z) ∈ UFusion.uFrameBlock ψ Q I :=
      ⟨_, hblock z hz, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hDcent d hd)) _ hmem
  · apply orderOf_eq_prime
    · rw [← map_pow, conj_pow, hx₀2, mul_one, mul_inv_cancel, map_one]
    · intro h1
      have hc : g * x₀ * g⁻¹ ∈ Subgroup.center _ := hker h1
      apply hx₀c
      have hcg := Subgroup.mem_center_iff.mp hc g
      have e : x₀ = g * x₀ * g⁻¹ := by
        calc x₀ = g⁻¹ * ((g * x₀ * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * x₀ * g⁻¹)) := by rw [← hcg]
          _ = g * x₀ * g⁻¹ := by group
      rw [e]
      exact hc


@[expose] def GGPSUSplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSU ∧ p ∣ 2 ^ f + 1

@[expose] def GGPSUNonsplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSU ∧ ¬ p ∣ 2 ^ f + 1

theorem ggRootPlaneAt_PSU_of_split (h₁ : GGRootPlaneInputOn GGPSUSplit)
    (h₂ : GGRootPlaneInputOn GGPSUNonsplit) : GGRootPlaneAt .PSU := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1
  by_cases hp : p ∣ 2 ^ f + 1
  · exact h₁ G p B Bs x L D J t n f ψ ⟨ht, hp⟩ hctx s1
  · exact h₂ G p B Bs x L D J t n f ψ ⟨ht, hp⟩ hctx s1

theorem ggRootPlaneInputOn_PSUSplit : GGRootPlaneInputOn GGPSUSplit := by
  intro G _ _ p B Bs x L D J t n f
  by_cases ht : t = .PSU
  · subst ht
    by_cases hf : 1 ≤ f
    · have e : ggU .PSU n f =
          ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
            Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rw [e]
      intro ψ hP hctx s1
      obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact rootPlane_psu_core hf hctx s1 hP.2
    · intro ψ _ hctx
      exact absurd hctx.2.2.2.1.1.2.1 hf
  · intro ψ hP
    exact absurd hP.1 ht

theorem ggRootPlaneAt_PSU_of_nonsplit (h₂ : GGRootPlaneInputOn GGPSUNonsplit) :
    GGRootPlaneAt .PSU :=
  ggRootPlaneAt_PSU_of_split ggRootPlaneInputOn_PSUSplit h₂

end Inputs

end CFSG.StandardType
