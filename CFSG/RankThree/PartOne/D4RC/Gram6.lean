module

public import CFSG.RankThree.PartOne.D4RC.Gram
public import CFSG.RankThree.PartOne.D4RC.LieStd
public import CFSG.RankThree.PartOne.D4RC.RootLong
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.RankThree.PartOne.D4RC.Fix6

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
  CFSG.SeitzReduction CFSG.Timmesfeld.ARS
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)

open scoped Matrix MatrixGroups Pointwise

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Col

variable {L : Type} [Field L]

theorem rg_col_ne_zero {m : ModGL d4 L} {a : L}
    (h : (m : Module.End L (RootModule d4 L)) (Finsupp.single rgHi 1) =
      a • Finsupp.single rgHi 1) : a ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  have h2 := congrArg (((m⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L)) ·) h
  simp only [map_zero] at h2
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h2
  have h3 := congrArg (· rgHi) h2
  simp at h3

variable (L) in
def rgColTheta : Subgroup (ModGL d4 L) where
  carrier := {m | ∃ a : L, (m : Module.End L (RootModule d4 L)) (Finsupp.single rgHi 1) =
    a • Finsupp.single rgHi 1}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Units.val_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro x ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have h := congrArg (((x⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L)) ·) ha
    simp only [map_smul] at h
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply] at h
    calc ((x⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L)) (Finsupp.single rgHi 1) =
        a⁻¹ • a • ((x⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L))
          (Finsupp.single rgHi 1) := by
          rw [smul_smul, inv_mul_cancel₀ (rg_col_ne_zero ha), one_smul]
      _ = a⁻¹ • Finsupp.single rgHi 1 := by rw [← h]

theorem mem_rgColTheta {m : ModGL d4 L} : m ∈ rgColTheta L ↔ ∃ a : L,
    (m : Module.End L (RootModule d4 L)) (Finsupp.single rgHi 1) = a • Finsupp.single rgHi 1 :=
  Iff.rfl

theorem rg_borel_le_col : borelGroup d4 L ≤ rgColTheta L :=
  fun _ hb => mem_rgColTheta.2 ⟨_, rg_col (rg_upper hb)⟩

theorem rg_parabolic_le_col : parabolicSubgroup d4 L d4PerpNodes ≤ rgColTheta L := by
  refine sup_le rg_borel_le_col ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  have hv : (Finsupp.single rgHi 1 : RootModule d4 L) = rootVec d4 L (highRoot d4) :=
    (CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_highRoot d4)).symm
  refine mem_rgColTheta.2 ⟨((-1) ^ stringDown d4 j (highRoot d4) *
    (((1 : Lˣ) ^ (-∑ k, d4.cartan j k * highRoot d4 k) : Lˣ) : L)), ?_⟩
  rw [hv, weylElt_rootVec j 1 (isRoot_highRoot d4), rcp_reflect_highRoot j hj]

theorem rg_canonicalRep_rootVec (w : WeylGroup d4) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    ∃ ε : L, ε ≠ 0 ∧ ((canonicalRep (coxeterSystem d4) L w : ModGL d4 L) :
      Module.End L (RootModule d4 L)) (rootVec d4 L β) = ε • rootVec d4 L (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem d4).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact rg_list_prod_weylElt_rootVec ω hβ

end Col

section Conj

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}

theorem rgt_exists_conj [CharP K 2] (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    (sp : RclSpecial F x i) (D : RclAlgData F i) :
    ∃ g : 𝒞[K, σ], rcaA0 sp D = conjSub ((Xh σ.toRingHom).map e.symm.toMonoidHom) g ∧
      ∃ κ : L, κ ≠ 0 ∧ ((F.g0⁻¹ * triEmb K σ L (sp.c * g) : ModGL d4 L) :
        Module.End L (RootModule d4 L)) (Finsupp.single rgHi 1) =
          κ • ((D.ρ D.H' : ModGL d4 L) : Module.End L (RootModule d4 L))
            (rootVec d4 L (D.σ' 0 1)) := by
  classical
  obtain rfl : ℓ = 2 := F.hℓ2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hkc : Nat.card (fixSubfield σ) = 2 ^ f :=
    card_fixSubfield_cube Nat.prime_two F.hf F.hK σ F.hσ
  have hβ : IsRoot d4 (D.σ' 0 1) := D.frame.isRoot 0 1 (by decide)
  have hX : ∀ t : fixSubfield σ, D.ρ (D.H' * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (algebraMap (fixSubfield σ) L t) * D.H'⁻¹) =
        D.ρ D.H' * pinnedX TwistTag.D4.tag L (D.σ' 0 1)
          ((D.e : L) * algebraMap (fixSubfield σ) L t) * (D.ρ D.H')⁻¹ := fun t => by
    rw [D.root]
  have hz : ∀ t : fixSubfield σ, F.n * twistHom TwistTag.D4 L (iterateFrobenius L 2 f)
      (D.ρ D.H' * pinnedX TwistTag.D4.tag L (D.σ' 0 1)
        ((D.e : L) * algebraMap (fixSubfield σ) L t) * (D.ρ D.H')⁻¹) * F.n⁻¹ =
      D.ρ D.H' * pinnedX TwistTag.D4.tag L (D.σ' 0 1)
        ((D.e : L) * algebraMap (fixSubfield σ) L t) * (D.ρ D.H')⁻¹ := fun t => by
    rw [← hX t, D.Φ_eq]
    exact congrArg D.ρ (D.a0 t)
  obtain ⟨k₁, hk₁G, hFk₁, hk₁⟩ := rcd_mem_fixed_iff F.hf F.hg0C F.hg0
    (rcb_rho_mem_adjointGroup D D.H') hβ D.e.ne_zero hkc hz
  obtain ⟨k₀, hk₀⟩ : k₁ ∈ (triEmb K σ L).range := by
    refine F.hperf (Subgroup.zpowers k₁) (Subgroup.zpowers_le.2 hk₁G) (fun y hy => ?_)
      (Subgroup.mem_zpowers k₁)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, hFk₁]
  have hXh := fun v => rcg_triEmb_Xh_iff σ hσ3 F.hσ hkc (MulEquiv.refl 𝒞[K, σ]) e hcompat
    (L := L) v
  set B := (Xh σ.toRingHom).map e.symm.toMonoidHom with hB
  set ι := triEmb K σ L with hι
  have himg : ∀ t : fixSubfield σ, ι (sp.c * (rcaTheta sp D ⟨_, D.a0 t⟩ : 𝒞[K, σ]) * sp.c⁻¹) =
      F.g0 * (D.ρ D.H' * pinnedX TwistTag.D4.tag L (D.σ' 0 1)
        ((D.e : L) * algebraMap (fixSubfield σ) L t) * (D.ρ D.H')⁻¹) * F.g0⁻¹ := fun t => by
    rw [hι, rcb_triEmb_theta]
    exact congrArg (fun Y => F.g0 * Y * F.g0⁻¹) (hX t)
  have hconj : ∀ b : 𝒞[K, σ], ι (k₀ * b * k₀⁻¹) = k₁ * ι b * k₁⁻¹ := fun b => by
    rw [map_mul, map_mul, map_inv, hk₀]
  refine ⟨sp.c⁻¹ * k₀, le_antisymm ?_ ?_, ?_⟩
  · intro a ha
    obtain ⟨t, rfl⟩ := (rcb_mem_rcaA0 sp D).1 ha
    obtain ⟨c', hc', hv⟩ := (hk₁ _).1 ⟨t, rfl⟩
    obtain ⟨b, hbB, hb⟩ := (hXh (pinnedX d4 L (highRoot d4) c')).2 ⟨c', hc', rfl⟩
    refine ⟨b, hbB, ?_⟩
    have h1 : sp.c * (rcaTheta sp D ⟨_, D.a0 t⟩ : 𝒞[K, σ]) * sp.c⁻¹ = k₀ * b * k₀⁻¹ := by
      apply triEmb_injective (K := K) (σ := σ) (L := L)
      rw [← hι, himg, hconj, hv]
      exact congrArg (fun Y => k₁ * Y * k₁⁻¹) hb.symm
    change sp.c⁻¹ * k₀ * b * (sp.c⁻¹ * k₀)⁻¹ = _
    calc sp.c⁻¹ * k₀ * b * (sp.c⁻¹ * k₀)⁻¹ = sp.c⁻¹ * (k₀ * b * k₀⁻¹) * sp.c := by group
      _ = _ := by rw [← h1]; group
  · rintro _ ⟨b, hbB, rfl⟩
    obtain ⟨c', hc', hv⟩ := (hXh (ι b)).1 ⟨b, hbB, rfl⟩
    obtain ⟨t, ht⟩ := (hk₁ (k₁ * pinnedX TwistTag.D4.tag L (highRoot TwistTag.D4.tag) c' *
      k₁⁻¹)).2 ⟨c', hc', rfl⟩
    have h1 : sp.c * (rcaTheta sp D ⟨_, D.a0 t⟩ : 𝒞[K, σ]) * sp.c⁻¹ = k₀ * b * k₀⁻¹ := by
      apply triEmb_injective (K := K) (σ := σ) (L := L)
      rw [← hι, himg, hconj, ← ht]
      exact congrArg (fun Y => k₁ * Y * k₁⁻¹) hv.symm
    refine (rcb_mem_rcaA0 sp D).2 ⟨t, ?_⟩
    change sp.c⁻¹ * k₀ * b * (sp.c⁻¹ * k₀)⁻¹ = _
    calc sp.c⁻¹ * k₀ * b * (sp.c⁻¹ * k₀)⁻¹ = sp.c⁻¹ * (k₀ * b * k₀⁻¹) * sp.c := by group
      _ = _ := by rw [← h1]; group
  ·
    have hck : sp.c * (sp.c⁻¹ * k₀) = k₀ := by group
    rw [hck, hk₀]
    obtain ⟨c', hc', hv⟩ := (hk₁ _).1 ⟨1, rfl⟩
    have he1 : (D.e : L) * algebraMap (fixSubfield σ) L 1 ≠ 0 := by
      rw [map_one, mul_one]
      exact D.e.ne_zero
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      rw [pinnedX_zero, mul_one, mul_inv_cancel, mul_inv_eq_one, mul_eq_left, mul_inv_eq_one,
        mul_eq_left] at hv
      exact he1 (pinnedX_injective TwistTag.D4.tag L _
        (hv.trans (pinnedX_zero TwistTag.D4.tag L _).symm))
    obtain ⟨w, hw⟩ := rcd_exists_smul_highRoot hβ
    set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
    have hnC : n ∈ adjointGroup TwistTag.D4.tag L :=
      canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L w
    have hnx : ∀ c : L, n * pinnedX TwistTag.D4.tag L (highRoot TwistTag.D4.tag) c * n⁻¹ =
        pinnedX TwistTag.D4.tag L (D.σ' 0 1) c := fun c => by
      rw [hn, canonicalRep_mul_pinnedX_mul_inv_of_two h2L w (isRoot_highRoot _) c, hw]
    set m := (F.g0 * D.ρ D.H' * n)⁻¹ * k₁ with hm
    have hmC : m ∈ adjointGroup TwistTag.D4.tag L :=
      mul_mem (inv_mem (mul_mem (mul_mem F.hg0C (rcb_rho_mem_adjointGroup D D.H')) hnC)) hk₁G
    have hmx : m * pinnedX TwistTag.D4.tag L (highRoot TwistTag.D4.tag) c' * m⁻¹ =
        pinnedX TwistTag.D4.tag L (highRoot TwistTag.D4.tag)
          ((D.e : L) * algebraMap (fixSubfield σ) L 1) := by
      have e1 : m * pinnedX TwistTag.D4.tag L (highRoot TwistTag.D4.tag) c' * m⁻¹ =
          (F.g0 * D.ρ D.H' * n)⁻¹ * (k₁ * pinnedX TwistTag.D4.tag L
            (highRoot TwistTag.D4.tag) c' * k₁⁻¹) * (F.g0 * D.ρ D.H' * n) := by
        rw [hm]
        group
      rw [e1, ← hv, ← hnx]
      group
    obtain ⟨a, ha⟩ := mem_rgColTheta.1
      (rg_parabolic_le_col (rcp_mem_parabolicSubgroup_of_conj hmC hc'0 hmx))
    obtain ⟨ε', hε', hε'v⟩ := rg_canonicalRep_rootVec (L := L) w (isRoot_highRoot d4)
    have hk : k₁ = F.g0 * D.ρ D.H' * n * m := by rw [hm]; group
    refine ⟨a * ε', mul_ne_zero (rg_col_ne_zero ha) hε', ?_⟩
    have hv' : (Finsupp.single rgHi 1 : RootModule d4 L) = rootVec d4 L (highRoot d4) :=
      (CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_highRoot d4)).symm
    rw [hk, show F.g0⁻¹ * (F.g0 * D.ρ D.H' * n * m) = D.ρ D.H' * n * m by group,
      Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul,
      map_smul, hv', hε'v, hw, map_smul, smul_smul]

theorem rgt_entry_triEmb (y : 𝒞[K, σ]) :
    rgEntry ((triEmb K σ L y : ModGL d4 L) : Module.End L (RootModule d4 L)) =
      algebraMap K L (rgEntry ((y : ModGL d4 K) : Module.End K (RootModule d4 K))) := by
  rw [rgEntry, rgEntry, triEmb_apply, baseChangeGL_apply_single, Finsupp.mapRange_apply]

theorem rgt_entry_eq (sp : RclSpecial F x i) (D : RclAlgData F i) {g : 𝒞[K, σ]} {κ : L}
    (hcol : ((F.g0⁻¹ * triEmb K σ L (sp.c * g) : ModGL d4 L) : Module.End L (RootModule d4 L))
      (Finsupp.single rgHi 1) = κ • ((D.ρ D.H' : ModGL d4 L) : Module.End L (RootModule d4 L))
        (rootVec d4 L (D.σ' 0 1)))
    (z : 𝒞[K, σ]) (X : ↥(fixSubgroup D.Φ')) :
    rgEntry ((triEmb K σ L (g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g) : ModGL d4 L) :
      Module.End L (RootModule d4 L)) =
      κ * ((((triEmb K σ L (sp.c * g))⁻¹ * triEmb K σ L (sp.c * z * sp.c⁻¹) * F.g0 :
        ModGL d4 L) : Module.End L (RootModule d4 L))
          (((D.ρ ((X : SL(3, L)) * D.H') : ModGL d4 L) : Module.End L (RootModule d4 L))
            (rootVec d4 L (D.σ' 0 1)))) rgLo := by
  set ι := triEmb K σ L with hι
  set W : ModGL d4 L := (ι (sp.c * g))⁻¹ * ι (sp.c * z * sp.c⁻¹) * F.g0 with hW
  have h1 : ι (g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g) =
      W * D.ρ X * (F.g0⁻¹ * ι (sp.c * g)) := by
    have h := rcb_triEmb_theta sp D X
    rw [← hι] at h
    calc ι (g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g) =
        (ι (sp.c * g))⁻¹ * ι (sp.c * z * sp.c⁻¹) *
          ι (sp.c * (rcaTheta sp D X : 𝒞[K, σ]) * sp.c⁻¹) * ι (sp.c * g) := by
          simp only [map_mul, map_inv]
          group
      _ = W * D.ρ X * (F.g0⁻¹ * ι (sp.c * g)) := by
          rw [h, hW]
          group
  rw [rgEntry, h1, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hcol,
    map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  simp only [Units.val_mul, Module.End.mul_apply]

variable (L) in
@[expose] noncomputable def rgStd : SL(3, L) →* ModGL d4 L := d4rhoStd L

theorem rgt_d4Chain_01 : d4Chain 0 1 = (Pi.single 0 1 : Fin d4.rank → ℤ) := by
  funext k
  fin_cases k <;> rfl

omit [Fact ℓ.Prime] [CharP L ℓ] [Finite K] [Algebra K L] [IsAlgClosure K L] in
theorem rgt_std_rootVec [CharP L 2] (M : SL(3, L)) :
    ((rgStd L M : ModGL d4 L) : Module.End L (RootModule d4 L))
        (rootVec d4 L (Pi.single 0 1 : Fin d4.rank → ℤ)) =
      rsLie ((M : Matrix (Fin 3) (Fin 3) L) * Matrix.single 0 1 1 *
        (M : Matrix (Fin 3) (Fin 3) L)⁻¹) :=
  rsLie_rootVec M

theorem rgt_rho_rootVec (D : RclAlgData F i) :
    ∃ v : WeylGroup d4, ∃ ε' : L, ε' ≠ 0 ∧ ∀ M : SL(3, L),
      ((D.ρ M : ModGL d4 L) : Module.End L (RootModule d4 L)) (rootVec d4 L (D.σ' 0 1)) =
        ε' • ((canonicalRep (coxeterSystem d4) L v : ModGL d4 L) :
          Module.End L (RootModule d4 L)) (rsLie ((M : Matrix (Fin 3) (Fin 3) L) *
            Matrix.single 0 1 1 * (M : Matrix (Fin 3) (Fin 3) L)⁻¹)) := by
  obtain rfl : ℓ = 2 := F.hℓ2
  obtain ⟨v, hρ, hσ⟩ := D.std
  obtain ⟨ε₀, hε₀, hεv⟩ := rg_canonicalRep_rootVec (L := L) v (isRoot_single d4 0)
  refine ⟨v, ε₀⁻¹, inv_ne_zero hε₀, fun M => ?_⟩
  have h01 : D.σ' 0 1 = v • (Pi.single 0 1 : Fin d4.rank → ℤ) := by
    rw [hσ 0 1, rgt_d4Chain_01]
  set n := canonicalRep (coxeterSystem d4) L v with hn
  have hinv : ((n⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L))
      (rootVec d4 L (v • (Pi.single 0 1 : Fin d4.rank → ℤ))) =
        ε₀⁻¹ • rootVec d4 L (Pi.single 0 1 : Fin d4.rank → ℤ) := by
    have h := congrArg (((n⁻¹ : ModGL d4 L) : Module.End L (RootModule d4 L)) ·) hεv
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, map_smul] at h
    rw [h, smul_smul, inv_mul_cancel₀ hε₀, one_smul]
  have hρM : D.ρ M = n * rgStd L M * n⁻¹ := by
    rw [hρ]
    rfl
  rw [hρM, h01, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hinv,
    map_smul, map_smul, rgt_std_rootVec]

end Conj

end CFSG.RankThree.PartOne.D4RC
