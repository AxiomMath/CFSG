module

public import CFSG.RankThree.PartOne.D4RC.LinesSylow
public import CFSG.RankThree.PartOne.D4RC.RxGen
public import CFSG.RankThree.PartOne.D4RC.RxGenU

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Alg

variable {L : Type} [Field L] {k : Type} [Field k] [Algebra k L]

@[expose] def rcaT12 (H' : SL(3, L)) : Multiplicative k →* SL(3, L) where
  toFun t := H' * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
    (algebraMap k L (Multiplicative.toAdd t)) * H'⁻¹
  map_one' := by
    rw [toAdd_one, map_zero, Matrix.SpecialLinearGroup.transvection_coeff_zero, mul_one,
      mul_inv_cancel]
  map_mul' s t := by
    rw [toAdd_mul, map_add, Matrix.SpecialLinearGroup.transvection_add]
    group

theorem rclA0AlgOf_eq_range (H' : SL(3, L)) : rclA0AlgOf L k H' = (rcaT12 (k := k) H').range := by
  unfold rclA0AlgOf
  have : {X | ∃ t : k, X = H' * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (algebraMap k L t) * H'⁻¹} =
      ((rcaT12 (k := k) H').range : Set SL(3, L)) := by
    ext X
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.toAdd t, rfl⟩
  rw [this, Subgroup.closure_eq]

end Alg

section Conj

variable {G : Type*} [Group G]

theorem rca_map_conj_le {P A : Subgroup G} (hA : A ≤ P) {g : G} (hg : g ∈ P) :
    A.map (MulAut.conj g).toMonoidHom ≤ P := by
  rintro _ ⟨a, ha, rfl⟩
  exact P.mul_mem (P.mul_mem hg (hA ha)) (P.inv_mem hg)

theorem rca_le_iSup_conj {P A : Subgroup G}
    (h : Subgroup.normalClosure ((A.subgroupOf P : Subgroup ↥P) : Set ↥P) = ⊤) :
    P ≤ ⨆ g ∈ P, A.map (MulAut.conj g).toMonoidHom := by
  set N := ⨆ g ∈ P, A.map (MulAut.conj g).toMonoidHom with hN
  have hle : ∀ g ∈ P, A.map (MulAut.conj g).toMonoidHom ≤ N := fun g hg =>
    le_iSup₂ (f := fun g (_ : g ∈ P) => A.map (MulAut.conj g).toMonoidHom) g hg
  have hNn : ∀ h ∈ P, N ≤ N.comap (MulAut.conj h).toMonoidHom := fun h hh =>
    iSup₂_le fun g hg => by
      rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
      have e : (MulAut.conj h).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (h * g)).toMonoidHom := MonoidHom.ext fun a => by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hle (h * g) (P.mul_mem hh hg)
  have hM : (N.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 hn⟩
  have hA : ((A.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊆ N.subgroupOf P := fun a ha => by
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha ⊢
    exact hle 1 P.one_mem (Subgroup.mem_map.mpr ⟨a, ha, by simp⟩)
  have h2 := Subgroup.normalClosure_le_normal hA
  rw [h] at h2
  intro u hu
  have h3 := h2 (Subgroup.mem_top (⟨u, hu⟩ : ↥P))
  rwa [Subgroup.mem_subgroupOf] at h3

end Conj

section Theta

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}

abbrev rcaW (sp : RclSpecial F x i) : Subgroup (Subgroup.centralizer ({x} : Set 𝒞[K, σ])) :=
  (rclQ F i).comap (rclPsi sp)

theorem rcaW_map (sp : RclSpecial F x i) : (rcaW sp).map (rclPsi sp) = rclQ F i := by
  obtain ⟨-, -, -, -, -, hQψ, -, -⟩ := rcl_psi_props F sp
  rw [rcaW, Subgroup.map_comap_eq, inf_eq_right.2 hQψ]

@[expose] def rcaPsiEquiv (sp : RclSpecial F x i) : ↥(rclPx sp) ≃* ↥(rclQ F i) :=
  (((Subgroup.equivMapOfInjective (rcaW sp) _ (Subgroup.subtype_injective _)).symm).trans
    (Subgroup.equivMapOfInjective (rcaW sp) _
      (d4QPsi_injective triEmb_injective F.g0 sp.c x))).trans
    (MulEquiv.subgroupCongr (rcaW_map sp))

theorem rcaPsiEquiv_apply (sp : RclSpecial F x i) (u : ↥(rclPx sp)) :
    (rcaPsiEquiv sp u : ModGL TwistTag.D4.tag L) =
      rclPsi sp ⟨u, rclPx_le_centralizer sp u.2⟩ := by
  set w := (Subgroup.equivMapOfInjective (rcaW sp) _ (Subgroup.subtype_injective _)).symm u
    with hw
  have h1 : ((w : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) : 𝒞[K, σ]) = u := by
    have key := (Subgroup.equivMapOfInjective (rcaW sp) _
      (Subgroup.subtype_injective (Subgroup.centralizer ({x} : Set 𝒞[K, σ])))).apply_symm_apply
        (u : ↥((rcaW sp).map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype))
    have h3 := congrArg
      (fun v : ↥((rcaW sp).map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype) =>
        (v : 𝒞[K, σ])) key
    simp only [Subgroup.coe_equivMapOfInjective_apply] at h3
    rw [hw]
    exact h3
  have h2 : (w : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) =
      ⟨u, rclPx_le_centralizer sp u.2⟩ := Subtype.ext h1
  change ((Subgroup.equivMapOfInjective (rcaW sp) _
    (d4QPsi_injective triEmb_injective F.g0 sp.c x) w : ModGL TwistTag.D4.tag L)) = _
  rw [Subgroup.coe_equivMapOfInjective_apply, h2]

@[expose] def rcaRhoEquiv (D : RclAlgData F i) : ↥(fixSubgroup D.Φ') ≃* ↥(rclQ F i) :=
  (Subgroup.equivMapOfInjective _ D.ρ D.frame.injective).trans
    (MulEquiv.subgroupCongr (rcl_map_fix_eq D.frame.injective
      (by rw [D.frame.range, D.sigma_eq]) D.Φ_eq))

theorem rcaRhoEquiv_apply (D : RclAlgData F i) (X : ↥(fixSubgroup D.Φ')) :
    (rcaRhoEquiv D X : ModGL TwistTag.D4.tag L) = D.ρ X := rfl

@[expose] def rcaTheta (sp : RclSpecial F x i) (D : RclAlgData F i) :
    ↥(fixSubgroup D.Φ') ≃* ↥(rclPx sp) :=
  (rcaRhoEquiv D).trans (rcaPsiEquiv sp).symm

theorem rcaTheta_psi (sp : RclSpecial F x i) (D : RclAlgData F i) (X : ↥(fixSubgroup D.Φ')) :
    rclPsi sp ⟨rcaTheta sp D X, rclPx_le_centralizer sp (rcaTheta sp D X).2⟩ = D.ρ X := by
  rw [← rcaPsiEquiv_apply, rcaTheta, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    rcaRhoEquiv_apply]

@[expose] def rcaA0 (sp : RclSpecial F x i) (D : RclAlgData F i) : Subgroup 𝒞[K, σ] :=
  (((rclA0AlgOf L (fixSubfield σ) D.H').subgroupOf (fixSubgroup D.Φ')).map
    (rcaTheta sp D).toMonoidHom).map (rclPx sp).subtype

theorem rcaA0_le (sp : RclSpecial F x i) (D : RclAlgData F i) : rcaA0 sp D ≤ rclPx sp := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem rca_normalClosure (sp : RclSpecial F x i) (D : RclAlgData F i) :
    Subgroup.normalClosure (((rcaA0 sp D).subgroupOf (rclPx sp) : Subgroup ↥(rclPx sp)) :
      Set ↥(rclPx sp)) = ⊤ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ
  have : Finite (fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hkc]; exact (pow_pos hℓ.pos _).ne')
  set A' : Subgroup ↥(fixSubgroup D.Φ') :=
    (rclA0AlgOf L (fixSubfield σ) D.H').subgroupOf (fixSubgroup D.Φ') with hA'
  have hgen : Subgroup.normalClosure (A' : Set ↥(fixSubgroup D.Φ')) = ⊤ := by
    rcases F.hε with h1 | h1
    · have h2 : (2 : fixSubfield σ) = 0 := by
        have h := CharP.cast_eq_zero L ℓ
        rw [F.hℓ2] at h
        apply (algebraMap (fixSubfield σ) L).injective
        rw [map_ofNat, map_zero]
        exact_mod_cast h
      rw [hA', D.H'_split h1]
      exact rcl_gen_split h2 D.Φ' D.H (D.split h1)
    · have hq2 : 2 < ℓ ^ f := by
        have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
        by_contra hlt
        have h2 : ℓ ^ f = 2 := by omega
        have hpd := F.hpd
        rw [h2, h1] at hpd
        have h3 : (p : ℤ) ∣ 3 := by simpa using hpd
        have := Int.le_of_dvd (by norm_num) h3
        have := F.hp3
        omega
      rw [hA', D.H'_unit h1]
      exact rcl_gen_unitary F.hℓ2 F.hf hkc hq2 D.Φ' D.H (D.unit h1)
  have hsub : (rcaA0 sp D).subgroupOf (rclPx sp) = A'.map (rcaTheta sp D).toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (rclPx sp).subtype_injective _
  rw [hsub, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (rcaTheta sp D).surjective, hgen,
    Subgroup.map_top_of_surjective _ (rcaTheta sp D).surjective]

theorem rca_iSup_eq (sp : RclSpecial F x i) (D : RclAlgData F i) :
    ⨆ g ∈ rclPx sp, (rcaA0 sp D).map (MulAut.conj g).toMonoidHom = rclPx sp :=
  le_antisymm (iSup₂_le fun _ hg => rca_map_conj_le (rcaA0_le sp D) hg)
    (rca_le_iSup_conj (rca_normalClosure sp D))

end Theta

end CFSG.RankThree.PartOne.D4RC
