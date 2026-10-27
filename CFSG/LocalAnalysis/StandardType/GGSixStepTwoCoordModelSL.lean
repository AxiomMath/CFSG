module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralClassical

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

open Multiplicative

section FrameHom

variable {G : Type} [Group G] {n e s r p : ℕ} {F : Type} [Field F]
  (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) (A₀ : Matrix.SpecialLinearGroup (Fin n) F)
  (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)

@[expose] noncomputable def frameHom [NeZero p] (hCp : C ^ p = 1) :
    Multiplicative (Fin s → ZMod p) →* G where
  toFun t := SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC fun i => (toAdd t i).val)
  map_one' := by
    have h0 : (fun i => (toAdd (1 : Multiplicative (Fin s → ZMod p)) i).val) = 0 := by
      funext i
      simp
    rw [h0, SLNS.nsSL_zero, map_one]
  map_mul' a b := by
    rw [← map_mul, SLNS.nsSL_mul]
    congr 1
    refine SLNS.nsSL_congr ε hC hCp fun i => ?_
    simp only [toAdd_mul, Pi.add_apply, ZMod.val_add, Nat.mod_mod]

theorem frameHom_apply [NeZero p] (hCp : C ^ p = 1) (t : Fin s → ZMod p) :
    frameHom ψ A₀ ε hC hCp (ofAdd t) = ψ (A₀ * SLNS.nsSL ε hC (fun i => (t i).val) * A₀⁻¹) :=
  rfl

theorem frameHom_natCast [NeZero p] (hCp : C ^ p = 1) (k : Fin s → ℕ) :
    frameHom ψ A₀ ε hC hCp (ofAdd fun i => (k i : ZMod p)) =
      SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC k) := by
  change SLRep.ggFrame ψ A₀ _ = _
  congr 1
  exact SLNS.nsSL_congr ε hC hCp fun i => by simp [ZMod.val_natCast]

theorem frameHom_injective [NeZero p] (hCp : C ^ p = 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) (he : 0 < e)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) :
    Function.Injective (frameHom ψ A₀ ε hC hCp) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  set t := toAdd a with ht
  have hmem : SLNS.nsSL ε hC (fun i => (t i).val) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) :=
    SLRep.ker_ggFrame_le hker A₀ ha
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  have hblock : ∀ i, C ^ (t i).val = c • 1 := by
    intro i
    ext a' b'
    have h1 := congrFun (congrFun hc (ε.symm (Sum.inl (a', i)))) (ε.symm (Sum.inl (b', i)))
    change scalar (Fin n) c _ _ = SLNS.nsMat ε C (fun i => (t i).val) _ _ at h1
    rw [SLNS.nsMat_block, scalar_apply, diagonal_apply] at h1
    rw [← h1, Matrix.smul_apply, one_apply, smul_eq_mul]
    simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Prod.mk.injEq, and_true, mul_ite,
      mul_one, mul_zero]
  have hne : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  have ht0 : t = 0 := by
    funext i
    by_contra hti
    have hdvd : ¬ p ∣ (t i).val := fun h => hti (by
      rw [Pi.zero_apply, ← ZMod.natCast_zmod_val (t i), (ZMod.natCast_eq_zero_iff _ _).mpr h])
    have hu := hunit _ hdvd c
    rw [hblock i, sub_self] at hu
    exact not_isUnit_zero hu
  rw [← ofAdd_toAdd a, ← ht, ht0, ofAdd_zero]


theorem frameHom_pow_p [NeZero p] (hCp : C ^ p = 1) (a : Multiplicative (Fin s → ZMod p)) :
    frameHom ψ A₀ ε hC hCp a ^ p = 1 := by
  have ha : a ^ p = 1 := by
    apply toAdd.injective
    funext i
    simp [toAdd_pow]
  rw [← map_pow, ha, map_one]

theorem range_frameHom [NeZero p] (hCp : C ^ p = 1) {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    (hframe : ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC k)) :
    (frameHom ψ A₀ ε hC hCp).range = Bs := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      (frameHom_pow_p ψ A₀ ε hC hCp a)
    obtain ⟨k', rfl⟩ := hframe b hb
    change SLRep.ggFrame ψ A₀ _ * SLRep.ggFrame ψ A₀ _ =
      SLRep.ggFrame ψ A₀ _ * SLRep.ggFrame ψ A₀ _
    rw [← map_mul, ← map_mul, SLNS.nsSL_comm]
  · intro b hb
    obtain ⟨k, rfl⟩ := hframe b hb
    exact ⟨_, frameHom_natCast ψ A₀ ε hC hCp k⟩

end FrameHom

section Moves

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] (g : K[X]) [Fact (Irreducible g)]
  {n s r p : ℕ} [Fact p.Prime] (ψ : Matrix.SpecialLinearGroup (Fin n) K →* G)
  (A₀ : Matrix.SpecialLinearGroup (Fin n) K) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
  (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1)

theorem exists_conj_frameHom (hζ : AdjoinRoot.root g ^ p = 1) (π : Equiv.Perm (Fin s))
    (η : Fin s → (ZMod p)ˣ) (hη : ∀ i, η i ∈ galExp g hζ) :
    ∃ M : Matrix.SpecialLinearGroup (Fin n) K, ∀ t : Fin s → ZMod p,
      (SLRep.ggFrame ψ A₀ M)⁻¹ * frameHom ψ A₀ ε hC hCp (ofAdd t) * SLRep.ggFrame ψ A₀ M =
        frameHom ψ A₀ ε hC hCp (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  have hσ : ∀ i, ∃ σ : AdjoinRoot g ≃ₐ[K] AdjoinRoot g,
      σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ (((η (π.symm i))⁻¹ : (ZMod p)ˣ) : ZMod p).val :=
    fun i => (galExp g hζ).inv_mem (hη (π.symm i))
  choose σ hσ using hσ
  obtain ⟨M, hM⟩ := exists_move g ε π.symm σ
  refine ⟨M, fun t => ?_⟩
  have hrel : SLNS.nsMat ε (rootMat g) (fun i => (t i).val) * (M : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) *
        SLNS.nsMat ε (rootMat g) (fun i => ((η i : ZMod p) * t (π i)).val) := by
    refine hM _ _ fun i => ?_
    simp only [Equiv.apply_symm_apply]
    rw [hσ i, pow_val_pow_val hζ, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  have hrel' : M⁻¹ * SLNS.nsSL ε hC (fun i => (t i).val) * M =
      SLNS.nsSL ε hC (fun i => ((η i : ZMod p) * t (π i)).val) := by
    have h1 : SLNS.nsSL ε hC (fun i => (t i).val) * M =
        M * SLNS.nsSL ε hC (fun i => ((η i : ZMod p) * t (π i)).val) := Subtype.ext hrel
    rw [mul_assoc, h1, inv_mul_cancel_left]
  rw [frameHom_apply, frameHom_apply, ← hrel']
  simp only [SLRep.ggFrame_apply, ← map_inv, ← map_mul]
  congr 1
  group

theorem exists_move_mem (hζ : AdjoinRoot.root g ^ p = 1) {Bs : Subgroup G}
    (hBs : (frameHom ψ A₀ ε hC hCp).range = Bs) (π : Equiv.Perm (Fin s))
    (η : Fin s → (ZMod p)ˣ) (hη : ∀ i, η i ∈ galExp g hζ) :
    ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ t : Fin s → ZMod p,
      w⁻¹ * frameHom ψ A₀ ε hC hCp (ofAdd t) * w =
        frameHom ψ A₀ ε hC hCp (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  obtain ⟨M, hM⟩ := exists_conj_frameHom g ψ A₀ ε hC hCp hζ π η hη
  refine ⟨SLRep.ggFrame ψ A₀ M, Subgroup.mem_inf.mpr ⟨⟨A₀ * M * A₀⁻¹, rfl⟩,
    hBs ▸ mem_normalizer_range_of_conj π η hM⟩, hM⟩

end Moves

theorem rootPB_dim_pos {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] :
    0 < (rootPB g).dim :=
  (Fact.out : Irreducible g).natDegree_pos

section Inputs

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem exists_frame_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hns : ¬ p ∣ 2 ^ f - 1)
    (g : (GaloisField 2 f)[X]) [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p (GaloisField 2 f))
    (hC : (rootMat g).det = 1) :
    ∃ (s r : ℕ) (ε : Fin (m + 1) ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC k) := by
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hX : ∀ b : Bs, ∃ X : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
      X ^ p = 1 ∧ (b : G) = ψ X := fun b =>
    SLNSRest.exists_sl_of_innerDiag hm hker hCψ hp hpF (hctx.2.1.2.1.2 b b.2)
      (hctx.2.2.2.2.2.2.1.2 _ (Bs.inv_mem b.2))
  choose X hXp hXb using hX
  have hXc : ∀ b c : Bs, X b * X c = X c * X b := fun b c =>
    SLNSRest.commute_of_map_eq hker hp hpF (hXp b) (by
      have h := TableB.IsElemAbelian.comm hctx.2.1.2.1 b.2 c.2
      rw [hXb b, hXb c] at h
      exact h)
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g hp hpK hgd
      (Set.range fun b : Bs => (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
      (by
        rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
        change (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X c : _) =
          (X c : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X b : _)
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hXc])
      (by
        rintro _ ⟨b, rfl⟩
        rw [← Matrix.SpecialLinearGroup.coe_pow, hXp, Matrix.SpecialLinearGroup.coe_one])
  refine ⟨s, r, ε, A₀, fun b hb => ?_⟩
  obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
  refine ⟨k, ?_⟩
  have h1 : X ⟨b, hb⟩ * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
  have h2 : X ⟨b, hb⟩ = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    rw [← h1, mul_inv_cancel_right]
  exact (hXb ⟨b, hb⟩).trans (congrArg ψ h2)

end Inputs

end CoordSL

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CoordSL Multiplicative

section Inputs

@[expose] def GGSLCoordCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : Matrix.SpecialLinearGroup (Fin n) F →* G,
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (s r : ℕ) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin n) F) (hC : (rootMat g).det = 1)
      (hCp : rootMat g ^ p = 1) (hζ : AdjoinRoot.root g ^ p = 1) (b : G) (L₁ : Subgroup G),
      b ∈ (frameHom ψ A₀ ε hC hCp).range → b ≠ 1 →
      IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
      Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (L₁ : Set G) :
        Subgroup G) ≤ p ^ 2 →
      ∀ β : Fin s → ZMod p, frameHom ψ A₀ ε hC hCp (ofAdd β) = b →
        (∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
          ∀ t : Fin s → ZMod p, t j = 0 → t j' = 0 → frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁) ∨
        (∃ (k : Fin s) (c : ZMod p) (ε' : Fin s → (ZMod p)ˣ), c ≠ 0 ∧
          (∀ i, ε' i ∈ galExp g hζ) ∧ (∀ i, i ≠ k → β i = (ε' i : ZMod p) * c) ∧
          ∀ t : Fin s → ZMod p, t k = 0 → ∑ i, (↑(ε' i)⁻¹ : ZMod p) * t i = 0 →
            frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ L₁)

@[expose] def GGSLCoordContraryInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → ¬ p ∣ 2 ^ f - 1 →
    ∀ (g : (GaloisField 2 f)[X]) [Fact (Irreducible g)] (s r : ℕ)
      (ε : Fin (m + 1) ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
      (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1) (hζ : AdjoinRoot.root g ^ p = 1),
      (frameHom ψ A₀ ε hC hCp).range = Bs → (s : ZMod p) - 1 = 0 →
        ∃ (k : Fin s) (o : Fin s → (ZMod p)ˣ) (t : Fin s → ZMod p),
          (∀ i, o i ∈ galExp g hζ) ∧ t ≠ 0 ∧ t k = 0 ∧ ∑ i, (o i : ZMod p) * t i = 0 ∧
            frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ D

theorem ggStepTwoCoordModelOn_PSL_of_inputs (hcomp : GGSLCoordCompInput)
    (hcontr : GGSLCoordContraryInput) : GGStepTwoCoordModelOn .PSL := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hlin
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hns : ¬ p ∣ 2 ^ f - 1 := fun h => hlin (Or.inl ⟨rfl, h⟩)
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p (GaloisField 2 f)) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (cyclotomic_ne_zero p (GaloisField 2 f)), natDegree_cyclotomic,
      Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p (GaloisField 2 f))
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC : (rootMat g).det = 1 := det_rootMat hp hpF hpK hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := (root_isPrimitiveRoot hp hpK hgd).pow_eq_one
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame_of_ctx hctx s1 hns g hgd hC
  have hrange : (frameHom ψ A₀ ε hC hCp).range = Bs :=
    range_frameHom ψ A₀ ε hC hCp hctx.bstar hframe
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hG₀ : ψ.range = ggG0 p B x L D J := hctx.range_eq
  refine ⟨s, galExp g hζ, frameHom ψ A₀ ε hC hCp,
    ⟨frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp hpF hpK hgd), hrange, ?_, ?_, ?_⟩⟩
  ·
    intro π η hη _
    obtain ⟨w, hw, hws⟩ := exists_move_mem g ψ A₀ ε hC hCp hζ hrange π η hη
    refine ⟨w, ?_, hws⟩
    rw [← hG₀]
    exact hw
  ·
    exact hcontr G p B Bs x L D J m f ψ hctx s1 hns g s r ε A₀ hC hCp hζ hrange
  ·
    intro b L₁ hpair β hβ
    obtain ⟨hb, hb1, hcomp', hcard⟩ := hpair
    rw [← hG₀] at hcomp'
    rw [← hrange] at hb hcard
    exact hcomp G (GaloisField 2 f) (m + 1) p hp2 hpF ψ hker g hgd s r ε A₀ hC hCp hζ b L₁ hb hb1
      hcomp' hcard β hβ

end Inputs

end CFSG.StandardType
