module

public import CFSG.Quasithin.Vol2.Ch3Sec3G2XS3
public import CFSG.Quasithin.Vol2.Ch3Sec3ThreeL32
public import CFSG.Quasithin.Background.JonesParshallG2TwoH1
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

namespace G2Three

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

@[expose] def codeMat (l : List ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if (l.getD j 0).testBit i then 1 else 0

theorem zornCoord_decodeZ : ∀ c < 256, ∀ i : Fin 8,
    (zornCoord (F := ZMod 2) (decodeZ c)) i = if c.testBit i then 1 else 0 := by
  decide +kernel

theorem zornCoord_symm_basis : ∀ j : Fin 8,
    (zornCoord (F := ZMod 2)).symm (Pi.single j 1) = decodeZ (2 ^ (j : ℕ)) := by
  decide +kernel

theorem cmat_eq (g : ↥(cayleyGroup (ZMod 2))) : cmat g = codeMat (matCode (g : Amb)) := by
  ext i j
  have h1 : cmat g i j =
      zornCoord ((g : Amb) ((zornCoord (F := ZMod 2)).symm (Pi.single j 1))) i := by
    simp [cmat, zmat, LinearMap.toMatrix'_apply]
  rw [h1, zornCoord_symm_basis j, ← decodeZ_encodeZ ((g : Amb) (decodeZ (2 ^ (j : ℕ)))),
    zornCoord_decodeZ _ (encodeZ_lt _) i]
  simp [codeMat, matCode, List.getD_eq_getElem?_getD]

@[expose] def fGMat (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Ix3 → ZMod 2 :=
  q6 ((M *ᵥ zornCoord (zI (q6 0 0 0 1 0 0))) 0) ((M *ᵥ zornCoord (zI (q6 0 0 0 0 1 0))) 0)
    ((M *ᵥ zornCoord (zI (q6 0 0 0 0 0 1))) 0) ((M *ᵥ zornCoord (zI (q6 1 0 0 0 0 0))) 0)
    ((M *ᵥ zornCoord (zI (q6 0 1 0 0 0 0))) 0) ((M *ᵥ zornCoord (zI (q6 0 0 1 0 0 0))) 0)

theorem fG_eq_fGMat {g : ↥(cayleyGroup (ZMod 2))} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hM : cmat g⁻¹ = M) : fG g = fGMat M := by
  simp only [fG, fGMat, ellG_eq_of_cmat hM]

theorem no_common_cob : ∀ p ∈ [(1, 32), (2, 8), (4, 9)], ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    ¬ (fGMat (codeMat (sM p.1)) = (codeMat (sM p.1)).submatrix embQ embQ *ᵥ
        q6 x₀ x₁ x₂ x₃ x₄ x₅ - q6 x₀ x₁ x₂ x₃ x₄ x₅ ∧
      fGMat (codeMat (sM p.2)) = (codeMat (sM p.2)).submatrix embQ embQ *ᵥ
        q6 x₀ x₁ x₂ x₃ x₄ x₅ - q6 x₀ x₁ x₂ x₃ x₄ x₅) := by
  decide +kernel

theorem sM_sq : ∀ k ∈ [1, 32, 2, 8, 4, 9], mmul (sM k) (sM k) = idMat := by
  decide +kernel

theorem fix_ab : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    matA6 *ᵥ q6 x₀ x₁ x₂ x₃ x₄ x₅ = q6 x₀ x₁ x₂ x₃ x₄ x₅ →
      matB6 *ᵥ q6 x₀ x₁ x₂ x₃ x₄ x₅ = q6 x₀ x₁ x₂ x₃ x₄ x₅ → q6 x₀ x₁ x₂ x₃ x₄ x₅ = 0 := by
  decide +kernel

theorem fix_of_equiv {Γ M : Type*} [Group Γ] [AddCommGroup M] {μ : Γ →* AddMonoid.End M}
    {Φ : Γ → M} (hΦ : Φ ∈ Z1A μ) (b x : Γ) (h : Φ (b * x * b⁻¹) = μ b (Φ x)) :
    μ (b * x * b⁻¹) (Φ b) = Φ b := by
  have h1 := hΦ b x
  have h2 := hΦ (b * x * b⁻¹) b
  rw [show b * x * b⁻¹ * b = b * x by group, h1, h, add_comm (μ b (Φ x))] at h2
  exact (add_right_cancel h2).symm

theorem eq_zero_of_equiv
    {Φ : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2}
    (hΦ : Φ ∈ Z1A g2Act) (b : ↥(cayleyGroup (ZMod 2)))
    (hb : ∀ i : Fin 2, ∃ x, b * x * b⁻¹ = Subgroup.inclusion subG2_le (gensK i) ∧
      Φ (b * x * b⁻¹) = g2Act b (Φ x)) : Φ b = 0 := by
  have hfix : ∀ i : Fin 2, muK (gensK i) (Φ b) = Φ b := by
    intro i
    obtain ⟨x, hx, h⟩ := hb i
    have := fix_of_equiv hΦ b x h
    rw [hx] at this
    exact this
  have h0 := hfix 0
  have h1 := hfix 1
  rw [muK_gens0] at h0
  rw [muK_gens1] at h1
  rw [q6_eta (Φ b)] at h0 h1 ⊢
  exact fix_ab _ _ _ _ _ _ h0 h1

theorem le_cayley : quasithinG2 (ZMod 2) ≤ cayleyGroup (ZMod 2) :=
  (CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup (K := ZMod 2)).le

@[expose] def sC (k : ℕ) : ↥(cayleyGroup (ZMod 2)) := ⟨sElt k, le_cayley (sElt_mem_G k)⟩

theorem sElt_sq {k : ℕ} (hk : k ∈ [1, 32, 2, 8, 4, 9]) : sElt k * sElt k = 1 := by
  have hk64 : k < 64 := by simp at hk; omega
  apply linearEquiv_eq_of_matCode
  rw [matCode_mul, matCode_sElt hk64, matCode_one]
  exact sM_sq k hk

theorem cmat_sC {k : ℕ} (hk : k < 64) : cmat (sC k) = codeMat (sM k) := by
  rw [cmat_eq]
  exact congrArg codeMat (matCode_sElt hk)

theorem false_of_fG {p : ℕ × ℕ} (hp : p ∈ [(1, 32), (2, 8), (4, 9)]) (m : Ix3 → ZMod 2)
    (h₁ : (fG + coboundaryA g2Act m : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2) (sC p.1) = 0)
    (h₂ : (fG + coboundaryA g2Act m : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2) (sC p.2) = 0) :
    False := by
  have hk : p.1 ∈ [1, 32, 2, 8, 4, 9] ∧ p.2 ∈ [1, 32, 2, 8, 4, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  have key : ∀ k ∈ [1, 32, 2, 8, 4, 9],
      (fG + coboundaryA g2Act m : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2) (sC k) = 0 →
      fGMat (codeMat (sM k)) = (codeMat (sM k)).submatrix embQ embQ *ᵥ m - m := by
    intro k hk' h0
    have h : fG (sC k) + (g2Act (sC k) m - m) = 0 := h0
    have hk64 : k < 64 := by simp at hk'; omega
    have hinv : (sC k)⁻¹ = sC k := inv_eq_of_mul_eq_one_right (Subtype.ext (sElt_sq hk'))
    have hM : cmat (sC k)⁻¹ = codeMat (sM k) := by rw [hinv]; exact cmat_sC hk64
    rw [fG_eq_fGMat hM, g2Act_eq_mulVec, cmat_sC hk64] at h
    rw [eq_neg_of_add_eq_zero_left h]
    funext i
    exact ZMod.neg_eq_self_mod_two _
  have e1 := key _ hk.1 h₁
  have e2 := key _ hk.2 h₂
  rw [q6_eta m] at e1 e2
  exact no_common_cob p hp _ _ _ _ _ _ ⟨e1, e2⟩


theorem pairs_mem : (1 ∈ sE8.getD 1 [] ∧ 32 ∈ sE8.getD 1 []) ∧
    (2 ∈ sE8.getD 2 [] ∧ 8 ∈ sE8.getD 2 []) ∧ (4 ∈ sE8.getD 6 [] ∧ 9 ∈ sE8.getD 6 []) := by
  decide

theorem sE8_fixQ : ∀ e < 8,
    (o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length
      ≤ 8 ∧
    (8 ≤ (o0Codes.filter fun c =>
      !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length →
        e = 1 ∨ e = 2 ∨ e = 6) := by
  decide +kernel

theorem offender_bound {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤ 64 ∧
      (64 ≤ (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2)))) →
        ∃ e, (e = 1 ∨ e = 2 ∨ e = 6) ∧ ∀ l, l ∈ idx B ↔ l ∈ sE8.getD e []) := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length := fun i hi => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [Bool.and_eq_true]
    exact ⟨hc.1, hc.2 i hi⟩
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && (fixQB (sM i) c && fixQB (sM j) c)).length :=
    fun i hi j hj => by
      rw [hC]
      refine length_filter_le fun c hc => ?_
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨hc.1, hc.2 i hi, hc.2 j hj⟩
  have hsingle : ∀ i ∈ idx B, i ≠ 0 →
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length ≤ 16 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).2]
    · rw [(sOuter_fix i h).2]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exfalso
    exact hB1 (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn]))
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn]
    constructor
    · omega
    · intro h
      omega
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    have hbound : Nat.card (fixV (B.map (g2QAct (ZMod 2)))) < 16 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).2
        · have := (hCi j hj).trans_eq (sOuter_fix j h').2
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).2
        omega
    rw [hn]
    constructor
    · omega
    · intro h
      omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
        o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
      refine List.filter_congr fun c _ => ?_
      congr 1
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    rw [hcard8, hC, hfilter]
    obtain ⟨h1, h2⟩ := sE8_fixQ e he
    refine ⟨by omega, fun h => ⟨e, h2 (by omega), hiff⟩⟩


section Coc

variable {G : Type} [Group G]

theorem cq_mul (q ℓ₁ ℓ₂ : G) :
    ℓ₁ * ℓ₂ * q * (ℓ₁ * ℓ₂)⁻¹ * q⁻¹ =
      ℓ₁ * (ℓ₂ * q * ℓ₂⁻¹ * q⁻¹) * ℓ₁⁻¹ * (ℓ₁ * q * ℓ₁⁻¹ * q⁻¹) := by
  group

theorem exists_cocycle {L Q U : Subgroup G} (σ : ↥L →* ↥subG2) (hσ : Function.Surjective σ)
    (hσQ : ∀ ℓ : ↥L, σ ℓ = 1 → (ℓ : G) ∈ Q) (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {q : G} (hq : q ∈ Q) (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    (κ : ↥U → Ix3 → ZMod 2) (hκ : ∀ u u' : ↥U, κ (u * u') = κ u + κ u')
    (hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ → κ u' = muK (σ ℓ) (κ u)) :
    ∃ f ∈ Z1A muK, ∀ ℓ : ↥L, f (σ ℓ) = κ ⟨_, hcU ℓ⟩ := by
  classical
  let lift : ↥subG2 → ↥L := fun γ => (hσ γ).choose
  have hlift : ∀ γ, σ (lift γ) = γ := fun γ => (hσ γ).choose_spec
  have hfib : ∀ ℓ ℓ' : ↥L, σ ℓ = σ ℓ' → κ ⟨_, hcU ℓ⟩ = κ ⟨_, hcU ℓ'⟩ := by
    intro ℓ ℓ' hll
    have ho : ((ℓ⁻¹ * ℓ' : ↥L) : G) ∈ Q := hσQ _ (by rw [map_mul, map_inv, hll, inv_mul_cancel])
    have hoq : ((ℓ⁻¹ * ℓ' : ↥L) : G) * q = q * ((ℓ⁻¹ * ℓ' : ↥L) : G) := hQc _ ho _ hq
    have hoq' : ((ℓ⁻¹ * ℓ' : ↥L) : G) * q * ((ℓ⁻¹ * ℓ' : ↥L) : G)⁻¹ = q := by
      rw [hoq]
      group
    refine congrArg κ (Subtype.ext ?_)
    have e : (ℓ' : G) = ℓ * ((ℓ⁻¹ * ℓ' : ↥L) : G) := by simp
    show (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ = (ℓ' : G) * q * (ℓ' : G)⁻¹ * q⁻¹
    rw [e]
    calc (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ =
        ℓ * (((ℓ⁻¹ * ℓ' : ↥L) : G) * q * ((ℓ⁻¹ * ℓ' : ↥L) : G)⁻¹) * (ℓ : G)⁻¹ * q⁻¹ := by
          rw [hoq']
      _ = _ := by group
  refine ⟨fun γ => κ ⟨_, hcU (lift γ)⟩, fun γ δ => ?_, fun ℓ => hfib _ _ (hlift _)⟩
  set ℓ₁ := lift γ
  set ℓ₂ := lift δ
  have h12 : σ (ℓ₁ * ℓ₂) = γ * δ := by rw [map_mul, hlift, hlift]
  show κ ⟨_, hcU (lift (γ * δ))⟩ = κ ⟨_, hcU ℓ₁⟩ + muK γ (κ ⟨_, hcU ℓ₂⟩)
  rw [hfib (lift (γ * δ)) (ℓ₁ * ℓ₂) (by rw [hlift, h12])]
  have hmem : (ℓ₁ : G) * ((ℓ₂ : G) * q * (ℓ₂ : G)⁻¹ * q⁻¹) * (ℓ₁ : G)⁻¹ ∈ U := by
    have h1 := U.mul_mem (hcU (ℓ₁ * ℓ₂)) (U.inv_mem (hcU ℓ₁))
    have e : ((ℓ₁ * ℓ₂ : ↥L) : G) * q * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ * q⁻¹ *
        ((ℓ₁ : G) * q * (ℓ₁ : G)⁻¹ * q⁻¹)⁻¹ =
        (ℓ₁ : G) * ((ℓ₂ : G) * q * (ℓ₂ : G)⁻¹ * q⁻¹) * (ℓ₁ : G)⁻¹ := by
      push_cast
      group
    rwa [e] at h1
  have e2 : (⟨_, hcU (ℓ₁ * ℓ₂)⟩ : ↥U) = ⟨_, hmem⟩ * ⟨_, hcU ℓ₁⟩ := by
    apply Subtype.ext
    show ((ℓ₁ * ℓ₂ : ↥L) : G) * q * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ * q⁻¹ = _
    push_cast
    exact cq_mul q ℓ₁ ℓ₂
  rw [e2, hκ, hκe ℓ₁ ⟨_, hcU ℓ₂⟩ ⟨_, hmem⟩ rfl, hlift, add_comm]

theorem commute_of_cob {L Q U : Subgroup G} (σ : ↥L →* ↥subG2) (hUQ : U ≤ Q)
    (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {q : G} (hq : q ∈ Q)
    (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    (κ : ↥U → Ix3 → ZMod 2) (hκ : ∀ u u' : ↥U, κ (u * u') = κ u + κ u')
    (hκ0 : ∀ u : ↥U, κ u = 0 → u = 1)
    (hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ → κ u' = muK (σ ℓ) (κ u))
    (hLU : ∀ ℓ : ↥L, ∀ u : ↥U, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U)
    {m : Ix3 → ZMod 2} (hf : ∀ ℓ : ↥L, κ ⟨_, hcU ℓ⟩ = muK (σ ℓ) m - m) (v : ↥U)
    (hv : κ v = m) (ℓ : ↥L) : (ℓ : G) * (q * (v : G)⁻¹) = q * (v : G)⁻¹ * ℓ := by
  set w : ↥U := ⟨_, hLU ℓ v⟩
  have hw : κ w = muK (σ ℓ) m := by rw [hκe ℓ v w rfl, hv]
  have hκinv : ∀ u : ↥U, κ u⁻¹ = -κ u := fun u => by
    have := hκ u u⁻¹
    rw [mul_inv_cancel] at this
    have h0 : κ 1 = 0 := by
      have := hκ 1 1
      rw [mul_one] at this
      exact left_eq_add.mp this
    rw [h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hu0 : (⟨_, hcU ℓ⟩ : ↥U) * w⁻¹ * v = 1 := by
    apply hκ0
    rw [hκ, hκ, hκinv, hf, hw, hv]
    abel
  have h1 : ((ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹) * ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * v = 1 :=
    congrArg Subtype.val hu0
  have hy : (ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹ ∈ U := by
    have := U.inv_mem (hLU ℓ v)
    rwa [show ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ = (ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹ by group] at this
  have hab : q⁻¹ * ((ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹) =
      ((ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹) * q⁻¹ := hQc _ (Q.inv_mem hq) _ (hUQ hy)
  have hvq : (v : G)⁻¹ * q = q * (v : G)⁻¹ := hQc _ (Q.inv_mem (hUQ v.2)) _ hq
  have key : (ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹ * q⁻¹ * v = 1 := by
    calc (ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹ * q⁻¹ * v =
        ((ℓ : G) * q * (ℓ : G)⁻¹) * (((ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹) * q⁻¹) * v := by group
      _ = ((ℓ : G) * q * (ℓ : G)⁻¹) * (q⁻¹ * ((ℓ : G) * (v : G)⁻¹ * (ℓ : G)⁻¹)) * v := by
          rw [hab]
      _ = 1 := by
          rw [← h1]
          group
  have key' : (ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹ = (v : G)⁻¹ * q := by
    calc (ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹ =
        ((ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹ * q⁻¹ * v) * ((v : G)⁻¹ * q) := by group
      _ = (v : G)⁻¹ * q := by rw [key, one_mul]
  calc (ℓ : G) * (q * (v : G)⁻¹) = ((ℓ : G) * q * (v : G)⁻¹ * (ℓ : G)⁻¹) * ℓ := by group
    _ = (v : G)⁻¹ * q * ℓ := by rw [key']
    _ = q * (v : G)⁻¹ * ℓ := by rw [hvq]

end Coc

end G2Three

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace G2Three

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix
open scoped commutatorElement

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

@[expose] noncomputable def coordQ (x : ModQ) : Ix3 → ZMod 2 :=
  Multiplicative.toAdd (zornSecEquiv (quasithinG2 (ZMod 2)) x)

theorem coordQ_act (g : ↥(quasithinG2 (ZMod 2))) (x : ModQ) :
    coordQ (g2QAct (ZMod 2) g x) = g2Act ⟨g, le_cayley g.2⟩ (coordQ x) := by
  induction x using QuotientGroup.induction_on with
  | H m =>
    exact (CFSG.Quasithin.Vol2.KGNat.linModelZorn (quasithinG2 (ZMod 2)) le_cayley).e_act g m _

theorem coordQ_mul (x y : ModQ) : coordQ (x * y) = coordQ x + coordQ y := by
  simp [coordQ]

theorem coordQ_one : coordQ 1 = 0 := by
  simp [coordQ]

theorem coordQ_injective : Function.Injective coordQ := fun _ _ h =>
  (zornSecEquiv (quasithinG2 (ZMod 2))).injective (Multiplicative.toAdd.injective h)

theorem coordQ_surjective : Function.Surjective coordQ := fun w => by
  obtain ⟨x, hx⟩ := (zornSecEquiv (quasithinG2 (ZMod 2))).surjective (Multiplicative.ofAdd w)
  exact ⟨x, by simp [coordQ, hx]⟩

theorem subG2_eq :
    subG2 = ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  rw [← g2Two_commutator_eq, CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]

variable {G : Type} [Group G]

theorem false_of_cob_case {L Q U : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2))) (β : ↥U →* ModQ)
    (hβs : Function.Surjective β) (hβ1 : ∀ u, β u = 1 → u = 1)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥U),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (σ : ↥L →* ↥subG2) (hσv : ∀ ℓ : ↥L, ((σ ℓ : ↥subG2) : Amb) =
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb))
    (hUQ : U ≤ Q) (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hLU : ∀ ℓ : ↥L, ∀ u : ↥U, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U)
    (hCL : ∀ x ∈ Q, x ∈ Subgroup.centralizer (L : Set G) → x = 1)
    {q : G} (hqQ : q ∈ Q) (hqU : q ∉ U) (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    {f : ↥subG2 → Ix3 → ZMod 2} (hfσ : ∀ ℓ : ↥L, f (σ ℓ) = coordQ (β ⟨_, hcU ℓ⟩))
    {m : Ix3 → ZMod 2} (hm : coboundaryA muK m = f) : False := by
  have hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ →
      coordQ (β u') = muK (σ ℓ) (coordQ (β u)) := by
    intro ℓ u u' hu'
    rw [hβe ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ u u' hu', coordQ_act]
    have e : Subgroup.inclusion subG2_le (σ ℓ) =
        ⟨_, le_cayley (ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩).2⟩ := Subtype.ext (hσv ℓ)
    show _ = g2Act (Subgroup.inclusion subG2_le (σ ℓ)) _
    rw [e]
  obtain ⟨x, hx⟩ := coordQ_surjective m
  obtain ⟨v, rfl⟩ := hβs x
  have hf' : ∀ ℓ : ↥L, coordQ (β ⟨_, hcU ℓ⟩) = muK (σ ℓ) m - m := fun ℓ => by
    rw [← hfσ ℓ, ← hm]
    rfl
  have hc := commute_of_cob σ hUQ hQc hqQ hcU (fun u => coordQ (β u))
    (fun u u' => by simp only [map_mul, coordQ_mul])
    (fun u hu => hβ1 u (coordQ_injective (hu.trans coordQ_one.symm))) hκe hLU hf' v hx
  have hqv : q * (v : G)⁻¹ = 1 := hCL _ (Q.mul_mem hqQ (Q.inv_mem (hUQ v.2)))
    (Subgroup.mem_centralizer_iff.mpr fun ℓ hℓ => hc ⟨ℓ, hℓ⟩)
  apply hqU
  rw [mul_inv_eq_one.mp hqv]
  exact v.2

theorem phi_eq_zero
    {L U A : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2))) (β : ↥U →* ModQ)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥U),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (σ : ↥L →* ↥subG2) (hσs : Function.Surjective σ) (hσv : ∀ ℓ : ↥L, ((σ ℓ : ↥subG2) : Amb) =
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb))
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {q : G} (hqA : ∀ a ∈ A, a * q = q * a)
    (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    {f : ↥subG2 → Ix3 → ZMod 2} (hfσ : ∀ ℓ : ↥L, f (σ ℓ) = coordQ (β ⟨_, hcU ℓ⟩))
    {m : Ix3 → ZMod 2} (hm : coboundaryA muK m = f - cocK) {a : G} (haA : a ∈ A) :
    (fG + coboundaryA g2Act m : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2)
      ⟨ρ ⟨a, hAN haA⟩, le_cayley (ρ ⟨a, hAN haA⟩).2⟩ = 0 := by
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ↥(cayleyGroup (ZMod 2)) → Ix3 → ZMod 2,
      Φ = fG + coboundaryA g2Act m := ⟨_, rfl⟩
  rw [← hΦdef]
  have hΦ : Φ ∈ Z1A g2Act := by
    rw [hΦdef]
    exact add_mem fG_mem (B1A_le_Z1A _ ⟨m, rfl⟩)
  have hΦf : ∀ γ : ↥subG2, Φ (Subgroup.inclusion subG2_le γ) = f γ := fun γ => by
    have h1 : coboundaryA muK m γ = f γ - cocK γ := congrFun hm γ
    change muK γ m - m = f γ - cocK γ at h1
    rw [hΦdef]
    show fG (Subgroup.inclusion subG2_le γ) + (muK γ m - m) = f γ
    rw [h1]
    show cocK γ + (f γ - cocK γ) = f γ
    abel
  obtain ⟨b, hb⟩ : ∃ b : ↥(cayleyGroup (ZMod 2)),
      (b : Amb) = ((ρ ⟨a, hAN haA⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) :=
    ⟨⟨_, le_cayley (ρ ⟨a, hAN haA⟩).2⟩, rfl⟩
  have hbe : (⟨_, le_cayley (ρ ⟨a, hAN haA⟩).2⟩ : ↥(cayleyGroup (ZMod 2))) = b :=
    Subtype.ext hb.symm
  rw [hbe]
  have hconj : ∀ (ℓ : ↥L) (hℓ' : a * ℓ * a⁻¹ ∈ L),
      Subgroup.inclusion subG2_le (σ ⟨_, hℓ'⟩) = b * Subgroup.inclusion subG2_le (σ ℓ) * b⁻¹ := by
    intro ℓ hℓ'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
      Subgroup.coe_inclusion, hσv, hσv, hb]
    show ((ρ ⟨_, Subgroup.le_normalizer hℓ'⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) =
      ((ρ ⟨a, hAN haA⟩ * ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ * (ρ ⟨a, hAN haA⟩)⁻¹ :
        ↥(quasithinG2 (ZMod 2))) : Amb)
    congr 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hqa : a * q = q * a := hqA a haA
  have h1 : a⁻¹ * q * a = q := by
    calc a⁻¹ * q * a = a⁻¹ * (q * a) := by group
      _ = a⁻¹ * (a * q) := by rw [hqa]
      _ = q := by group
  have h2 : a⁻¹ * q⁻¹ = q⁻¹ * a⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hqa]
  have hequiv : ∀ (ℓ : ↥L) (hℓ' : a * ℓ * a⁻¹ ∈ L),
      f (σ ⟨_, hℓ'⟩) = g2Act b (f (σ ℓ)) := by
    intro ℓ hℓ'
    have hc : a * ℓ * a⁻¹ * q * (a * ℓ * a⁻¹)⁻¹ * q⁻¹ =
        a * ((ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹) * a⁻¹ := by
      calc a * ℓ * a⁻¹ * q * (a * ℓ * a⁻¹)⁻¹ * q⁻¹ =
          a * ℓ * (a⁻¹ * q * a) * (ℓ : G)⁻¹ * (a⁻¹ * q⁻¹) := by group
        _ = a * ℓ * q * (ℓ : G)⁻¹ * (q⁻¹ * a⁻¹) := by rw [h1, h2]
        _ = a * ((ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹) * a⁻¹ := by group
    rw [hfσ, hfσ]
    show coordQ (β ⟨_, hcU ⟨_, hℓ'⟩⟩) = g2Act b (coordQ (β ⟨_, hcU ℓ⟩))
    rw [hβe ⟨a, hAN haA⟩ ⟨_, hcU ℓ⟩ ⟨_, hcU ⟨_, hℓ'⟩⟩ hc, coordQ_act, hbe]
  apply eq_zero_of_equiv hΦ
  intro i
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : ↥L, σ ℓ₀ = gensK i := hσs (gensK i)
  have hℓ : a⁻¹ * ℓ₀ * a ∈ L := by
    have h3 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (L : Set G)).inv_mem (hAN haA)) ℓ₀).mp ℓ₀.2
    simpa using h3
  have hℓ' : a * ((⟨_, hℓ⟩ : ↥L) : G) * a⁻¹ ∈ L := by
    rw [show a * ((⟨_, hℓ⟩ : ↥L) : G) * a⁻¹ = ℓ₀ by
      show a * (a⁻¹ * ℓ₀ * a) * a⁻¹ = ℓ₀
      group]
    exact ℓ₀.2
  have he : (⟨_, hℓ'⟩ : ↥L) = ℓ₀ := Subtype.ext (by
    show a * (a⁻¹ * ℓ₀ * a) * a⁻¹ = ℓ₀
    group)
  refine ⟨Subgroup.inclusion subG2_le (σ ⟨_, hℓ⟩), ?_, ?_⟩
  · rw [← hconj ⟨_, hℓ⟩ hℓ', he, hℓ₀]
  · rw [← hconj ⟨_, hℓ⟩ hℓ', hΦf, hΦf, hequiv ⟨_, hℓ⟩ hℓ']

theorem false_of_q
    {L Q U A : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2))) (β : ↥U →* ModQ)
    (hβs : Function.Surjective β) (hβ1 : ∀ u, β u = 1 → u = 1)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥U),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2))
    (hρL' : ∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hKL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = 1 → ℓ ∈ Q)
    (hUQ : U ≤ Q) (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQLU : ⁅Q, L⁆ ≤ U)
    (hLU : ∀ ℓ : ↥L, ∀ u : ↥U, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U)
    (hCL : ∀ x ∈ Q, x ∈ Subgroup.centralizer (L : Set G) → x = 1)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {q : G} (hqQ : q ∈ Q) (hqU : q ∉ U)
    (hqA : ∀ a ∈ A, a * q = q * a) {p : ℕ × ℕ} (hp : p ∈ [(1, 32), (2, 8), (4, 9)])
    {a₁ a₂ : G} (ha₁A : a₁ ∈ A) (ha₂A : a₂ ∈ A)
    (ha₁ : ρ ⟨a₁, hAN ha₁A⟩ = sEltG p.1) (ha₂ : ρ ⟨a₂, hAN ha₂A⟩ = sEltG p.2) : False := by
  have hσmem : ∀ ℓ : ↥L,
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) ∈ subG2 := by
    intro ℓ
    rw [subG2_eq]
    exact Subgroup.mem_subgroupOf.mp (hρL ℓ ℓ.2)
  obtain ⟨σ, hσdef⟩ : ∃ σ : ↥L →* ↥subG2, σ = ((quasithinG2 (ZMod 2)).subtype.comp
      (ρ.comp (Subgroup.inclusion Subgroup.le_normalizer))).codRestrict subG2 hσmem := ⟨_, rfl⟩
  have hσv : ∀ ℓ : ↥L, ((σ ℓ : ↥subG2) : Amb) =
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) := by
    intro ℓ
    rw [hσdef]
    rfl
  have hσs : Function.Surjective σ := by
    intro γ
    have h1 : (γ : Amb) ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
      rw [← subG2_eq]
      exact γ.2
    obtain ⟨ℓ, hℓ, e⟩ :=
      hρL' ⟨γ, Subgroup.commutator_le_self _ h1⟩ (Subgroup.mem_subgroupOf.mpr h1)
    refine ⟨⟨ℓ, hℓ⟩, Subtype.ext ?_⟩
    rw [hσv]
    exact congrArg (fun x : ↥(quasithinG2 (ZMod 2)) => (x : Amb)) e
  have hσQ : ∀ ℓ : ↥L, σ ℓ = 1 → (ℓ : G) ∈ Q := by
    intro ℓ h1
    have h2 : ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1 := by
      apply Subtype.ext
      rw [← hσv, h1]
      rfl
    exact hKL _ ℓ.2 h2
  have hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ →
      coordQ (β u') = muK (σ ℓ) (coordQ (β u)) := by
    intro ℓ u u' hu'
    rw [hβe ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ u u' hu', coordQ_act]
    have e : Subgroup.inclusion subG2_le (σ ℓ) =
        ⟨_, le_cayley (ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩).2⟩ := Subtype.ext (hσv ℓ)
    show _ = g2Act (Subgroup.inclusion subG2_le (σ ℓ)) _
    rw [e]
  have hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U := by
    intro ℓ
    have h1 : ⁅(ℓ : G), q⁆ ∈ ⁅L, Q⁆ := Subgroup.commutator_mem_commutator ℓ.2 hqQ
    rw [Subgroup.commutator_comm] at h1
    rw [← commutatorElement_def]
    exact hQLU h1
  obtain ⟨f, hfZ, hfσ⟩ := exists_cocycle σ hσs hσQ hQc hqQ hcU (fun u => coordQ (β u))
    (fun u u' => by simp only [map_mul, coordQ_mul]) hκe
  rcases Z1A_K_cases hfZ with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact false_of_cob_case ρ β hβs hβ1 hβe σ hσv hUQ hQc hLU hCL hqQ hqU hcU hfσ hm
  · have e1 := phi_eq_zero ρ β hβe σ hσs hσv hAN hqA hcU hfσ hm ha₁A
    have e2 := phi_eq_zero ρ β hβe σ hσs hσv hAN hqA hcU hfσ hm ha₂A
    have hb : ∀ (a : G) (haA : a ∈ A) (k : ℕ), ρ ⟨a, hAN haA⟩ = sEltG k →
        (⟨_, le_cayley (ρ ⟨a, hAN haA⟩).2⟩ : ↥(cayleyGroup (ZMod 2))) = sC k := by
      intro a haA k hk
      apply Subtype.ext
      show ((ρ ⟨a, hAN haA⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) = sElt k
      rw [hk]
      rfl
    rw [hb a₁ ha₁A _ ha₁] at e1
    rw [hb a₂ ha₂A _ ha₂] at e2
    exact false_of_fG hp m e1 e2

theorem exists_q [Finite G] {L Q U A : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2))) (β : ↥U →* ModQ)
    (hβs : Function.Surjective β) (hβi : Function.Injective β)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥U),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hUQ : U ≤ Q) (hUQne : U ≠ Q) (hcardU : Nat.card ↥U = 64)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAQ : Nat.card ↥Q ≤ Nat.card ↥A) (hρS : ∀ a (ha : a ∈ A), ρ ⟨a, hAN ha⟩ ∈ sSubG)
    (hρQ : ∀ a (ha : a ∈ A), ρ ⟨a, hAN ha⟩ = 1 → a ∈ Q)
    (hA1 : ∃ a, ∃ ha : a ∈ A, ρ ⟨a, hAN ha⟩ ≠ 1) :
    ∃ q ∈ Q, q ∉ U ∧ (∀ a ∈ A, a * q = q * a) ∧ ∃ p ∈ [(1, 32), (2, 8), (4, 9)],
      ∃ a₁, ∃ ha₁ : a₁ ∈ A, ∃ a₂, ∃ ha₂ : a₂ ∈ A,
        ρ ⟨a₁, hAN ha₁⟩ = sEltG p.1 ∧ ρ ⟨a₂, hAN ha₂⟩ = sEltG p.2 := by
  classical
  set ρA : ↥A →* ↥(quasithinG2 (ZMod 2)) := ρ.comp (Subgroup.inclusion hAN) with hρAdef
  set B := ρA.range with hBdef
  have hBS : B ≤ sSubG := by
    rintro _ ⟨a, rfl⟩
    exact hρS a.1 a.2
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρA (Subtype.ext (hAc _ a.2 _ b.2))
  have hB2 : ∀ x ∈ B, x ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ 2 = 1 := Subtype.ext (by simpa using hA2 _ a.2)
    rw [← map_pow, ha, map_one]
  have hBne : B ≠ ⊥ := by
    obtain ⟨a, haA, ha1⟩ := hA1
    intro hb
    apply ha1
    have h2 : ρA ⟨a, haA⟩ ∈ B := ⟨_, rfl⟩
    rw [hb, Subgroup.mem_bot] at h2
    exact h2
  set X := Q ⊓ Subgroup.centralizer (A : Set G) with hXdef
  have hAB : Nat.card ↥A ≤ Nat.card ↥B * Nat.card ↥X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρA.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρA).toEquiv] at h1
    rw [h1]
    refine Nat.mul_le_mul_left _ ?_
    have hkX : ∀ k : ↥ρA.ker, ((k : ↥A) : G) ∈ X := fun k =>
      Subgroup.mem_inf.mpr ⟨hρQ _ k.1.2 (MonoidHom.mem_ker.mp k.2),
        Subgroup.mem_centralizer_iff.mpr fun b hb => hAc _ hb _ k.1.2⟩
    refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥A) : G), hkX k⟩ : ↥X)) ?_
    intro k₁ k₂ h12
    have h3 : ((k₁ : ↥A) : G) = ((k₂ : ↥A) : G) := congrArg (fun x : ↥X => (x : G)) h12
    exact Subtype.ext (Subtype.ext h3)
  set Y := U ⊓ Subgroup.centralizer (A : Set G) with hYdef
  have hfix : ∀ u : ↥U, β u ∈ fixV (B.map (g2QAct (ZMod 2))) ↔
      (u : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro u
    rw [mem_fixV]
    constructor
    · intro hu
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hau : a * u * a⁻¹ ∈ U := hAU a ha u u.2
      have h1 := hβe ⟨a, hAN ha⟩ u ⟨_, hau⟩ rfl
      have h2 := hu _ ⟨ρA ⟨a, ha⟩, ⟨_, rfl⟩, rfl⟩
      have h3 : a * (u : G) * a⁻¹ = u := congrArg Subtype.val (hβi (h1.trans h2))
      calc a * (u : G) = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h3]
    · intro hu x hx
      obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
      have hua : (u : G) = a * u * (a : G)⁻¹ := by
        rw [Subgroup.mem_centralizer_iff.mp hu _ a.2]
        group
      exact (hβe ⟨a, hAN a.2⟩ u u hua).symm
  have hY : Nat.card ↥Y = Nat.card ↥(fixV (B.map (g2QAct (ZMod 2)))) := by
    refine Nat.card_congr (Equiv.ofBijective (fun y =>
      (⟨β ⟨y.1, y.2.1⟩, (hfix _).mpr y.2.2⟩ : ↥(fixV (B.map (g2QAct (ZMod 2)))))) ⟨?_, ?_⟩)
    · intro y₁ y₂ h12
      have h3 : β ⟨y₁.1, y₁.2.1⟩ = β ⟨y₂.1, y₂.2.1⟩ := congrArg Subtype.val h12
      have h4 : (y₁ : G) = y₂ := congrArg (fun x : ↥U => (x : G)) (hβi h3)
      exact Subtype.ext h4
    · rintro ⟨x, hx⟩
      obtain ⟨u, rfl⟩ := hβs x
      exact ⟨⟨u, u.2, (hfix u).mp hx⟩, rfl⟩
  have hX0 : 0 < Nat.card ↥X := Nat.card_pos
  have hrelQ := Subgroup.relIndex_mul_card (H := X) (K := Q)
  rw [inf_of_le_left inf_le_left] at hrelQ
  have hrelU := Subgroup.relIndex_mul_card (H := X) (K := U)
  have hXU : X ⊓ U = Y := by
    ext x
    constructor
    · rintro ⟨⟨-, hc⟩, hu⟩
      exact ⟨hu, hc⟩
    · rintro ⟨hu, hc⟩
      exact ⟨⟨hUQ hu, hc⟩, hu⟩
  rw [hXU] at hrelU
  have hrel_le : X.relIndex U ≤ X.relIndex Q :=
    Subgroup.relIndex_le_of_le_right hUQ Subgroup.index_ne_zero_of_finite
  have hs : X.relIndex Q ≤ Nat.card ↥B := by
    have h1 : X.relIndex Q * Nat.card ↥X ≤ Nat.card ↥B * Nat.card ↥X := by
      rw [hrelQ]
      exact hAQ.trans hAB
    exact Nat.le_of_mul_le_mul_right h1 hX0
  have h64 : 64 ≤ Nat.card ↥B * Nat.card ↥Y := by
    rw [← hcardU, ← hrelU]
    exact Nat.mul_le_mul_right _ (hrel_le.trans hs)
  have hBidx : Nat.card ↥B = (idx B).card := card_eq_idx hBS
  obtain ⟨hle64, hcls⟩ := offender_bound hBS hBne hBc hB2
  rw [← hBidx, ← hY] at hle64 hcls
  have hXV : ¬ X ≤ U := by
    intro hXU'
    have hYX : Y = X := by rw [← hXU]; exact inf_of_le_left hXU'
    have hQU := Subgroup.relIndex_mul_card (H := U) (K := Q)
    rw [inf_of_le_left hUQ] at hQU
    have hidx1 : U.relIndex Q ≠ 1 := fun h1 =>
      hUQne (le_antisymm hUQ (Subgroup.relIndex_eq_one.mp h1))
    have hidx0 : U.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h128 : 128 ≤ Nat.card ↥Q := by
      rw [← hQU, hcardU]
      omega
    rw [hYX] at hle64
    have := hAQ.trans hAB
    omega
  obtain ⟨q, hqX, hqU⟩ := IsConcreteLE.not_le_iff_exists.mp hXV
  refine ⟨q, hqX.1, hqU, Subgroup.mem_centralizer_iff.mp hqX.2, ?_⟩
  obtain ⟨e, he, hiff⟩ := hcls h64
  obtain ⟨p, hp, hp1, hp2⟩ : ∃ p ∈ [(1, 32), (2, 8), (4, 9)],
      p.1 ∈ sE8.getD e [] ∧ p.2 ∈ sE8.getD e [] := by
    rcases he with rfl | rfl | rfl
    · exact ⟨(1, 32), by simp, pairs_mem.1⟩
    · exact ⟨(2, 8), by simp, pairs_mem.2.1⟩
    · exact ⟨(4, 9), by simp, pairs_mem.2.2⟩
  obtain ⟨a₁, ha₁⟩ := (mem_idx.mp ((hiff _).mpr hp1)).2
  obtain ⟨a₂, ha₂⟩ := (mem_idx.mp ((hiff _).mpr hp2)).2
  exact ⟨p, hp, a₁.1, a₁.2, a₂.1, a₂.2, ha₁, ha₂⟩

theorem false_of_three [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L)
    (hTC : tC L T = ⊥) (hVQ : vPlus L T ≠ qL L T) : False := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQle : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hG2.1 hTL
  have hUQ : blockU L ≤ qL L T := hUV.trans hVQle
  have hQT : qL L T ≤ T := ThreeL32.qL_le h
  have hZL : blockZ L = ⊥ := ThreeL32.blockZ_eq_bot h hTL hG2.1 hTC
  have hQe : IsElemAbelian 2 (qL L T) := ThreeL32.isElemAbelian_qL h38 h39 h hG2.1 hTL hTC
  have hQc : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hQe ha hb
  have hQLU : ⁅qL L T, L⁆ ≤ blockU L := Hyp331.commutator_qL_le_blockU hG2.1 hTL
  have hMp := Hyp331.mPlus_eq_of_le (L := L) (T := T) hTL
  obtain ⟨-, ⟨hJ, -⟩, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L := (Subgroup.commutator_mono hVQle le_rfl).trans hQLU
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le T).mpr fun y hy => hy.1.1
  have hVU : vPlus L T = blockU L := by
    refine le_antisymm ?_ hUV
    rw [hV4]
    refine sup_le hVL fun z hz => ?_
    have h1 : z ∈ tC L T := ⟨hZT hz.1, hz.2⟩
    rw [hTC, Subgroup.mem_bot] at h1
    rw [h1]
    exact (blockU L).one_mem
  obtain ⟨ρ, β, hβs, hβk, hβe, hρL, hρL', hρT, hK⟩ := G2Rho.exists_rho h38 h39 h51 h hTL hG2
  have hβ1 : ∀ u, β u = 1 → u = 1 := fun u hu => by
    have h1 := (hβk u).mp hu
    rw [hZL, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hβi : Function.Injective β := (injective_iff_map_eq_one β).mpr hβ1
  have hcardU : Nat.card ↥(blockU L) = 64 := by
    rw [← card_ModQ]
    exact Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)
  obtain ⟨A, hAmax, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (vPlus L T : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup₂_le fun A hA => hcon A hA)
  obtain ⟨hAT, hAe, hAm⟩ := hAmax
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hAT.trans hTL
  have hA1 : ∃ a, ∃ ha : a ∈ A, ρ ⟨a, hAN ha⟩ ≠ 1 := by
    obtain ⟨a, haA, haC⟩ := IsConcreteLE.not_le_iff_exists.mp hAV
    exact ⟨a, haA, fun h1 => haC (hQV (hK a (Subgroup.mem_sup_right (hAT haA)) _ h1))⟩
  obtain ⟨q, hqQ, hqU, hqA, p, hp, a₁, ha₁A, a₂, ha₂A, ha₁, ha₂⟩ :=
    exists_q ρ β hβs hβi hβe hUQ (fun e => hVQ (hVU.trans e)) hcardU hAN
      (fun a ha u hu => (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hAN ha)) u).mp
        hu)
      (fun a ha b hb => ThreeL32.comm_of_isElemAbelian hAe ha hb) hAe.2 (hAm _ hQT hQe)
      (fun a ha => hρT a (hAT ha))
      (fun a ha h1 => hK a (Subgroup.mem_sup_right (hAT ha)) _ h1) hA1
  exact false_of_q ρ β hβs hβ1 hβe hρL hρL'
    (fun ℓ hℓ h1 => hK ℓ (Subgroup.mem_sup_left hℓ) _ h1) hUQ hQc hQLU
    (fun ℓ u => (Subgroup.mem_normalizer_iff.mp
      (C1.mem_normalizer_blockU (Subgroup.le_normalizer ℓ.2)) u).mp u.2)
    (fun x hx hxL => ThreeL32.eq_one_of_mem_centralizer h hTC hx hxL) hAN hqQ hqU hqA hp
    ha₁A ha₂A ha₁ ha₂

end G2Three

namespace ThreeL32

theorem insp3_3_25ThreeRest_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) : Insp3_3_25ThreeRest := by
  intro G _ _ T M L D h hTL hG hTC hVQ _
  exact G2Three.false_of_three h38 h39 h51 h hTL hG hTC hVQ

end ThreeL32

end CFSG.Quasithin.H13
