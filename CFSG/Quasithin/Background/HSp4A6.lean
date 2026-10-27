module

public import CFSG.Quasithin.Background.HSp4A6Data
public import CFSG.Quasithin.Background.HSp4Bridge
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4A6

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauMat tauSp_tauSp frobAut)
open scoped Matrix

theorem psiHom_injective : Function.Injective psiHom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact psiMat_eq_one σ (congrArg Units.val hσ)

@[expose] noncomputable def Γ₆
    : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :=
  (alternatingGroup (Fin 6)).map psiHom

@[expose] noncomputable def psiEquiv
    : ↥(alternatingGroup (Fin 6)) ≃* ↥Γ₆ :=
  Subgroup.equivMapOfInjective _ psiHom psiHom_injective

theorem mem_statedSp_of_psi
    (σ : Perm (Fin 6)) : psiHom σ ∈ StatedSp 2 (ZMod 2) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
    (psiMat_symplectic σ)

theorem Γ₆_le : Γ₆ ≤ StatedSp 2 (ZMod 2) := by
  rintro _ ⟨σ, -, rfl⟩
  exact mem_statedSp_of_psi σ

theorem map_top_psiHom
    : (⊤ : Subgroup (Perm (Fin 6))).map psiHom = StatedSp 2 (ZMod 2) := by
  have hle : (⊤ : Subgroup (Perm (Fin 6))).map psiHom ≤ StatedSp 2 (ZMod 2) := by
    rintro _ ⟨σ, -, rfl⟩
    exact mem_statedSp_of_psi σ
  have hc1 : Nat.card ↥((⊤ : Subgroup (Perm (Fin 6))).map psiHom) = 720 := by
    rw [Subgroup.card_map_of_injective psiHom_injective, Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hc2 : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])

theorem exists_psi_of_mem_statedSp {B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hB : B ∈ StatedSp 2 (ZMod 2)) : ∃ s : Perm (Fin 6), psiHom s = B := by
  rw [← map_top_psiHom] at hB
  obtain ⟨s, -, hs⟩ := hB
  exact ⟨s, hs⟩

theorem conj_mem_Γ₆
    {B γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)} (hB : B ∈ StatedSp 2 (ZMod 2))
    (hγ : γ ∈ Γ₆) : B * γ * B⁻¹ ∈ Γ₆ := by
  obtain ⟨s, rfl⟩ := exists_psi_of_mem_statedSp hB
  obtain ⟨a, ha, rfl⟩ := hγ
  refine ⟨s * a * s⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  have := (alternatingGroup.normal (α := Fin 6)).conj_mem a ha s
  exact this

theorem Γ₆_eq_commutator :
    Γ₆ = (commutator ↥(StatedSp 2 (ZMod 2))).map (StatedSp 2 (ZMod 2)).subtype := by
  rw [Subgroup.map_subtype_commutator, Γ₆, ← alternatingGroup.commutator_perm_eq (by simp),
    map_commutator_eq, MonoidHom.range_eq_map, map_top_psiHom]

theorem tauSp_mem_Γ₆
    {γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)} (hγ : γ ∈ Γ₆) :
    ((tauSp ⟨γ, Γ₆_le hγ⟩ : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) ∈ Γ₆ := by
  have h1 : (commutator ↥(StatedSp 2 (ZMod 2))).map tauSp ≤
      commutator ↥(StatedSp 2 (ZMod 2)) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  rw [Γ₆_eq_commutator] at hγ ⊢
  obtain ⟨x, hx, rfl⟩ := hγ
  exact ⟨tauSp x, h1 ⟨x, hx, rfl⟩, rfl⟩

@[expose] noncomputable def tau₆ : ↥Γ₆ →* ↥Γ₆ where
  toFun γ := ⟨((tauSp ⟨γ, Γ₆_le γ.2⟩ : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)),
    tauSp_mem_Γ₆ γ.2⟩
  map_one' := by
    apply Subtype.ext
    change ((tauSp (1 : StatedSp 2 (ZMod 2)) : StatedSp 2 (ZMod 2)) :
      GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    change ((tauSp (⟨x, Γ₆_le x.2⟩ * ⟨y, Γ₆_le y.2⟩ : StatedSp 2 (ZMod 2)) :
      StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = _
    rw [map_mul]
    rfl

theorem coe_tau₆ (γ : ↥Γ₆) :
    (((tau₆ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      tauMat ((γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :=
  rfl

theorem tauSp_tauSp_two (g : StatedSp 2 (ZMod 2)) : tauSp (tauSp g) = g := by
  rw [tauSp_tauSp]
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]
  ext i j
  simp only [Matrix.map_apply]
  rw [CFSG.QuasithinUnique.Lin2.Five.frobAut_apply]
  generalize ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 2)) i j = x
  revert x
  decide

theorem tau₆_tau₆ (γ : ↥Γ₆) : tau₆ (tau₆ γ) = γ := by
  apply Subtype.ext
  change ((tauSp (tauSp ⟨γ, Γ₆_le γ.2⟩) : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = _
  rw [tauSp_tauSp_two]

theorem tau₆_surjective
    : Function.Surjective tau₆ := fun γ => ⟨tau₆ γ, tau₆_tau₆ γ⟩

@[expose] noncomputable def tau₆Equiv : MulAut ↥Γ₆ :=
  MulEquiv.ofBijective tau₆ ⟨fun x y h => by rw [← tau₆_tau₆ x, h, tau₆_tau₆],
    tau₆_surjective⟩

theorem mem_Γ₆_iff {γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)} :
    γ ∈ Γ₆ ↔ ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ psiHom σ = γ := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩

theorem isNatIrr : IsNatIrr Γ₆ := by
  intro U hU
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨v, hv⟩, hv0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp h
  have hv0' : v ≠ 0 := fun h' => hv0 (Subtype.ext h')
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact U.zero_mem
  obtain ⟨σ, hσ, hσw⟩ := transitive_psiMat v w hv0' hw
  rw [← hσw]
  exact hU (psiHom σ) (mem_Γ₆_iff.mpr ⟨σ, hσ, rfl⟩) v hv

theorem hasScalarCommutant : HasScalarCommutant Γ₆ := by
  intro f hf
  have hψ : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∀ v, f (psiMat σ *ᵥ v) = psiMat σ *ᵥ f v :=
    fun σ hσ v => hf (psiHom σ) (mem_Γ₆_iff.mpr ⟨σ, hσ, rfl⟩) v
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  have hw := stab_fix (f (Pi.single (Sum.inl 0) 1)) fun σ hσ hσe => by
    rw [← hψ σ hσ, hσe]
  have hall : ∀ v, v ≠ 0 → ∃ σ : Perm (Fin 6),
      f v = psiMat σ *ᵥ f (Pi.single (Sum.inl 0) 1) ∧
        v = psiMat σ *ᵥ Pi.single (Sum.inl 0) 1 := by
    intro v hv
    obtain ⟨σ, hσ, hσv⟩ := transitive_psiMat _ v he0 hv
    exact ⟨σ, by rw [← hσv, hψ σ hσ], hσv.symm⟩
  rcases hw with h0 | h1
  · refine ⟨0, fun v => ?_⟩
    rw [zero_smul]
    by_cases hv : v = 0
    · rw [hv, map_zero]
    obtain ⟨σ, hfv, -⟩ := hall v hv
    rw [hfv, h0, Matrix.mulVec_zero]
  · refine ⟨1, fun v => ?_⟩
    rw [one_smul]
    by_cases hv : v = 0
    · rw [hv, map_zero]
    obtain ⟨σ, hfv, hv'⟩ := hall v hv
    rw [hfv, h1, ← hv']

theorem zmod_two_cases (D : ZMod 2) : D = 0 ∨ D = 1 := by
  fin_cases D
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] noncomputable def g₃
    : ↥Γ₆ := ⟨psiHom cyc345, mem_Γ₆_iff.mpr ⟨cyc345, sign_cyc345, rfl⟩⟩

theorem card_fix_matAut (M : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // matAut M v = v} =
      Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 //
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v = v} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
      invFun := fun w => ⟨Multiplicative.ofAdd w.1, congrArg Multiplicative.ofAdd w.2⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }

theorem card_fix_g₃
    : Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
    natAut Γ₆ g₃ v = v} = 4 :=
  (card_fix_matAut _).trans card_fix_cyc345.1

theorem card_fix_tau_g₃
    : Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
    natAut Γ₆ (tau₆ g₃) v = v} = 1 :=
  (card_fix_matAut _).trans card_fix_cyc345.2

theorem not_isoMod
    : ¬ Pair.IsoMod (pairImg Γ₆ tau₆) (V₁ (Fin 2 ⊕ Fin 2) (ZMod 2))
    (V₂ (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  rintro ⟨e, he⟩
  set l := pairHom Γ₆ tau₆ g₃ with hl
  have hlm : l ∈ pairImg Γ₆ tau₆ := pairHom_mem_pairImg _ _ _
  let F₁ := {v : V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) // l v = v}
  let F₂ := {w : V₂ (Fin 2 ⊕ Fin 2) (ZMod 2) // l w = w}
  have hfix : ∀ v : V₁ (Fin 2 ⊕ Fin 2) (ZMod 2), l v = v → l (e v) = e v := by
    intro v h1
    have hv1 : l ↑v ∈ V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) := by rw [h1]; exact v.2
    have e1 := he l hlm v hv1
    calc l (e v) = e ⟨l v, hv1⟩ := e1.symm
      _ = e v := congrArg (fun z => ((e z : ↥(V₂ (Fin 2 ⊕ Fin 2) (ZMod 2))) :
          PairMod (Fin 2 ⊕ Fin 2) (ZMod 2))) (Subtype.ext h1)
  have hinj : Nat.card F₁ ≤ Nat.card F₂ := by
    refine Nat.card_le_card_of_injective (fun v => ⟨e v.1, hfix v.1 v.2⟩) ?_
    intro v w h
    have := congrArg (fun z : F₂ => z.1) h
    exact Subtype.ext (e.injective this)
  have h1 : Nat.card F₁ = 4 := by
    rw [← card_fix_g₃]
    exact Nat.card_congr
      { toFun := fun v => ⟨(v.1 : PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)).1,
          congrArg Prod.fst v.2⟩
        invFun := fun u => ⟨⟨(u.1, 1), mem_V₁.mpr rfl⟩, by
          change ((natAut Γ₆ g₃) u.1, (natAut Γ₆ (tau₆ g₃)) 1) = (u.1, 1)
          rw [u.2, map_one]⟩
        left_inv := fun v => by
          apply Subtype.ext; apply Subtype.ext
          exact Prod.ext rfl (mem_V₁.mp v.1.2).symm
        right_inv := fun u => rfl }
  have h2 : Nat.card F₂ = 1 := by
    rw [← card_fix_tau_g₃]
    exact Nat.card_congr
      { toFun := fun v => ⟨(v.1 : PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)).2,
          congrArg Prod.snd v.2⟩
        invFun := fun u => ⟨⟨(1, u.1), mem_V₂.mpr rfl⟩, by
          change ((natAut Γ₆ g₃) 1, (natAut Γ₆ (tau₆ g₃)) u.1) = (1, u.1)
          rw [u.2, map_one]⟩
        left_inv := fun v => by
          apply Subtype.ext; apply Subtype.ext
          exact Prod.ext (mem_V₂.mp v.1.2).symm rfl
        right_inv := fun u => rfl }
  omega

@[expose] noncomputable def conjB
    (B : StatedSp 2 (ZMod 2)) : MulAut ↥Γ₆ :=
  Γ₆.normalizerMonoidHom ⟨(B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)), by
    rw [Subgroup.mem_normalizer_iff]
    intro γ
    constructor
    · intro hγ
      exact conj_mem_Γ₆ B.2 hγ
    · intro hγ
      have h2 := conj_mem_Γ₆ ((StatedSp 2 (ZMod 2)).inv_mem B.2) hγ
      simpa [mul_assoc] using h2⟩

theorem coe_conjB (B : StatedSp 2 (ZMod 2)) (γ : ↥Γ₆) :
    ((conjB B γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ * (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ := rfl

theorem conjB_mul
    (C D : StatedSp 2 (ZMod 2)) : conjB (C * D) = conjB C * conjB D := by
  refine MulEquiv.ext fun γ => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_conjB, coe_conjB, coe_conjB, Subgroup.coe_mul]
  group

theorem conjB_one : conjB 1 = 1 := by
  refine MulEquiv.ext fun γ => Subtype.ext ?_
  rw [coe_conjB, OneMemClass.coe_one, one_mul, inv_one, mul_one]
  rfl

@[expose] noncomputable def autΦ
    (p : StatedSp 2 (ZMod 2) × Bool) : MulAut ↥Γ₆ :=
  if p.2 then conjB p.1 * tau₆Equiv else conjB p.1

theorem card_fix_conjB (B : StatedSp 2 (ZMod 2)) (γ : ↥Γ₆) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (conjB B γ) v = v} =
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ γ v = v} := by
  have : natAut Γ₆ (conjB B γ) = matAut (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * natAut Γ₆ γ *
      (matAut (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)))⁻¹ := by
    change matHom (((conjB B γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) = _
    rw [coe_conjB, map_mul, map_mul, map_inv]
    rfl
  rw [this, Sp4.card_fix_conj]

theorem eq_of_conjB_eq
    {B B' : StatedSp 2 (ZMod 2)} (h : ∀ γ : ↥Γ₆, conjB B γ = conjB B' γ) :
    B = B' := by
  set C := (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * B with hC
  have hcomm : ∀ γ ∈ Γ₆, C * γ = γ * C := by
    intro γ hγ
    have h1 : (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ * (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ =
        (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ * (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ := by
      have := congrArg Subtype.val (h ⟨γ, hγ⟩)
      rwa [coe_conjB, coe_conjB] at this
    rw [hC]
    calc (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * B * γ
        = (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * ((B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ *
            (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹) * B := by group
      _ = (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * ((B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ *
            (B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹) * B := by rw [h1]
      _ = γ * ((B' : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * B) := by group
  obtain ⟨c, hc⟩ := hasScalarCommutant
    (Matrix.mulVecLin (C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).toAddMonoidHom
    fun γ hγ v => by
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, ← Units.val_mul, hcomm γ hγ]
  have hc' : ∀ v, (C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v = c • v :=
    fun v => hc v
  rcases zmod_two_cases c with h0 | h1
  · exfalso
    have h2 := congrArg (fun w => ((C⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ w) (hc' (Pi.single (Sum.inl 0) 1))
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h2
    have := congrFun h2 (Sum.inl 0)
    simp at this
  · have hC1 : C = 1 := Units.ext (Matrix.ext_iff_mulVec.mpr fun v => by
      rw [hc', h1, one_smul, Units.val_one, Matrix.one_mulVec])
    apply Subtype.ext
    rw [hC, inv_mul_eq_one] at hC1
    exact hC1.symm

theorem autΦ_injective : Function.Injective autΦ := by
  rintro ⟨B, ε⟩ ⟨B', ε'⟩ h
  have hτfix : ∀ C : StatedSp 2 (ZMod 2), (∀ γ, tau₆ γ = conjB C γ) → False := by
    intro C hC
    have h1 := card_fix_conjB C g₃
    rw [← hC, card_fix_tau_g₃, card_fix_g₃] at h1
    omega
  cases ε <;> cases ε' <;> simp only [autΦ, ↓reduceIte, Bool.false_eq_true] at h
  · rw [eq_of_conjB_eq fun γ => congrArg (fun α : MulAut ↥Γ₆ => α γ) h]
  · exfalso
    refine hτfix (B'⁻¹ * B) fun γ => ?_
    have h2 : conjB (B'⁻¹ * B) = tau₆Equiv := by
      rw [conjB_mul, h, ← mul_assoc, ← conjB_mul, inv_mul_cancel, conjB_one, one_mul]
    rw [h2]
    rfl
  · exfalso
    refine hτfix (B⁻¹ * B') fun γ => ?_
    have h2 : conjB (B⁻¹ * B') = tau₆Equiv := by
      rw [conjB_mul, ← h, ← mul_assoc, ← conjB_mul, inv_mul_cancel, conjB_one, one_mul]
    rw [h2]
    rfl
  · rw [eq_of_conjB_eq fun γ => congrArg (fun α : MulAut ↥Γ₆ => α γ) (mul_right_cancel h)]

theorem autΦ_surjective : Function.Surjective autΦ := by
  have : Finite (MulAut ↥Γ₆) := MulEquiv.finite_left
  have hle : Nat.card (MulAut ↥Γ₆) ≤ 1440 := by
    have h :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    rwa [Nat.card_congr (MulAut.congr psiEquiv).toEquiv] at h
  have hc : Nat.card (StatedSp 2 (ZMod 2) × Bool) = 1440 := by
    rw [Nat.card_prod, ← map_top_psiHom, Subgroup.card_map_of_injective psiHom_injective,
      Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_bool]
    rfl
  exact (autΦ_injective.bijective_of_nat_card_le (by rw [hc]; exact hle)).2

theorem hAut
    (α : MulAut ↥Γ₆) : ∃ (A : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (σ : ZMod 2 ≃+* ZMod 2),
    (∀ γ, (((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *
        ((γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map σ *
          ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))) ∨
    ∀ γ, (((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *
        (((tau₆ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map σ *
          ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  obtain ⟨⟨B, ε⟩, rfl⟩ := autΦ_surjective α
  refine ⟨(B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)), RingEquiv.refl _, ?_⟩
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2),
      M.map (RingEquiv.refl (ZMod 2)) = M := fun M => by ext; rfl
  cases ε
  · left
    intro γ
    rw [hmap]
    change (((B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * γ * (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ :
      GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) = _
    rw [Units.val_mul, Units.val_mul]
  · right
    intro γ
    rw [hmap]
    change (((B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * (tau₆ γ : ↥Γ₆) *
      (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) = _
    rw [Units.val_mul, Units.val_mul]

end Sp4A6

end H

end CFSG.Quasithin
