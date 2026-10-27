module

public import CFSG.Quasithin.Vol2.KGNatSp4Semi
public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.Quasithin.Vol2.KGNatSp4Flag

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem spB_e0 (y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (vec4 1 0 0 0) y = y (.inr 0) := by
  rw [toBilin'_spJ_apply]
  simp [vec4, Fin.sum_univ_two]

theorem spB_mat (g : StatedSp 2 K) (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ x) (mat 2 K g *ᵥ y) = Matrix.toBilin' (spJ K) x y :=
  spB_mulVec g.2 x y

theorem mem_gS3_iff (g : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    x ∈ gmapSp g (spHyp K) ↔ Matrix.toBilin' (spJ K) (mat 2 K g *ᵥ vec4 1 0 0 0) x = 0 := by
  rw [mem_gmapSp, mem_spHyp, ← spB_e0 (mat 2 K g⁻¹ *ᵥ x), ← spB_mat g, mat_mulVec_inv]

theorem mem_gS1_iff (g : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    x ∈ gmapSp g (spLine K) ↔ ∃ c : K, x = c • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
  rw [mem_gmapSp, mem_spLine]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(mat 2 K g⁻¹ *ᵥ x) (.inl 0), ?_⟩
    rw [← Matrix.mulVec_smul]
    conv_lhs => rw [← mat_mulVec_inv g x]
    congr 1
    exact vec4_eq (by simp [vec4]) (by simp [vec4, h1]) (by simp [vec4, h2]) (by simp [vec4, h3])
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, mat_inv_mulVec]
    exact ⟨by simp [vec4], by simp [vec4], by simp [vec4]⟩

theorem v0_ne_zero (g : StatedSp 2 K) : mat 2 K g *ᵥ vec4 1 0 0 0 ≠ 0 := by
  intro h
  have := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h
  simp only [mat_inv_mulVec, Matrix.mulVec_zero] at this
  exact one_ne_zero (congrFun this (.inl 0))

theorem mem_gS1_of_perp (g : StatedSp 2 K) {x : Fin 2 ⊕ Fin 2 → K}
    (hx : ∀ y ∈ gmapSp g (spHyp K), Matrix.toBilin' (spJ K) x y = 0) :
    x ∈ gmapSp g (spLine K) := by
  rw [mem_gmapSp, mem_spLine]
  have key : ∀ y' ∈ spHyp K, Matrix.toBilin' (spJ K) (mat 2 K g⁻¹ *ᵥ x) y' = 0 := by
    intro y' hy'
    rw [← spB_mat g, mat_mulVec_inv]
    exact hx _ ((mem_gmapSp).mpr (by rwa [mat_inv_mulVec]))
  have k0 := key (vec4 1 0 0 0) rfl
  have k1 := key (vec4 0 1 0 0) rfl
  have k3 := key (vec4 0 0 0 1) rfl
  rw [toBilin'_spJ_apply] at k0 k1 k3
  simp [vec4, Fin.sum_univ_two] at k0 k1 k3
  exact ⟨k3, k0, k1⟩

section Geom

variable {T T' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} {σ σ' : K →+* K}

theorem hyp_of_line (g : StatedSp 2 K) (hinj : Function.Injective T)
    (horth : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 → Matrix.toBilin' (spJ K) (T x) (T y) = 0)
    (h1 : ∀ x ∈ gmapSp g (spLine K), T x ∈ gmapSp g (spLine K)) :
    ∀ x ∈ gmapSp g (spHyp K), T x ∈ gmapSp g (spHyp K) := by
  have hv0 : mat 2 K g *ᵥ vec4 1 0 0 0 ∈ gmapSp g (spLine K) :=
    (mem_gS1_iff g _).mpr ⟨1, (one_smul K _).symm⟩
  obtain ⟨c, hc⟩ := (mem_gS1_iff g _).mp (h1 _ hv0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← map_zero T] at hc
    exact v0_ne_zero g (hinj hc)
  intro x hx
  have h2 := horth _ _ ((mem_gS3_iff g x).mp hx)
  rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact (mem_gS3_iff g _).mpr ((mul_eq_zero.mp h2).resolve_left hc0)

theorem line_of_hyp (g : StatedSp 2 K) (hT : ∀ (c : K) x, T (c • x) = σ c • T x)
    (hTT' : ∀ x, T (T' x) = x)
    (horth : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 → Matrix.toBilin' (spJ K) (T x) (T y) = 0)
    (h3' : ∀ x ∈ gmapSp g (spHyp K), T' x ∈ gmapSp g (spHyp K)) :
    ∀ x ∈ gmapSp g (spLine K), T x ∈ gmapSp g (spLine K) := by
  have hTv0 : T (mat 2 K g *ᵥ vec4 1 0 0 0) ∈ gmapSp g (spLine K) := by
    refine mem_gS1_of_perp g fun y hy => ?_
    rw [← hTT' y]
    exact horth _ _ ((mem_gS3_iff g _).mp (h3' y hy))
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_gS1_iff g x).mp hx
  rw [hT]
  exact (gmapSp g (spLine K)).smul_mem _ hTv0

theorem stab_line_iff_stab_hyp (g : StatedSp 2 K) (hT : ∀ (c : K) x, T (c • x) = σ c • T x)
    (hT' : ∀ (c : K) x, T' (c • x) = σ' c • T' x) (hTT' : ∀ x, T (T' x) = x)
    (hT'T : ∀ x, T' (T x) = x)
    (horth : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 → Matrix.toBilin' (spJ K) (T x) (T y) = 0)
    (horth' : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T' x) (T' y) = 0) :
    (∀ x, x ∈ gmapSp g (spLine K) ↔ T x ∈ gmapSp g (spLine K)) ↔
      (∀ x, x ∈ gmapSp g (spHyp K) ↔ T x ∈ gmapSp g (spHyp K)) := by
  have hinj : Function.Injective T := fun a b h => by rw [← hT'T a, h, hT'T]
  have hinj' : Function.Injective T' := fun a b h => by rw [← hTT' a, h, hTT']
  constructor
  · intro h
    have h1 : ∀ x ∈ gmapSp g (spLine K), T x ∈ gmapSp g (spLine K) := fun x hx => (h x).mp hx
    have h1' : ∀ x ∈ gmapSp g (spLine K), T' x ∈ gmapSp g (spLine K) := fun x hx =>
      (h (T' x)).mpr (by rwa [hTT'])
    have h3 := hyp_of_line g hinj horth h1
    have h3' := hyp_of_line g hinj' horth' h1'
    exact fun x => ⟨h3 x, fun hx => by rw [← hT'T x]; exact h3' _ hx⟩
  · intro h
    have h3 : ∀ x ∈ gmapSp g (spHyp K), T x ∈ gmapSp g (spHyp K) := fun x hx => (h x).mp hx
    have h3' : ∀ x ∈ gmapSp g (spHyp K), T' x ∈ gmapSp g (spHyp K) := fun x hx =>
      (h (T' x)).mpr (by rwa [hTT'])
    have h1 := line_of_hyp g hT hTT' horth h3'
    have h1' := line_of_hyp g hT' hT'T horth' h3
    exact fun x => ⟨h1 x, fun hx => by rw [← hT'T x]; exact h1' _ hx⟩

end Geom

theorem inv_conj_mem_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {τ : G}
    (hτ : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := by
  let φ : ↥H → ↥H := fun h => ⟨τ * h * τ⁻¹, hτ h h.2⟩
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext (by
    have h1 : τ * (a : G) * τ⁻¹ = τ * b * τ⁻¹ := congrArg Subtype.val hab
    exact mul_left_cancel (mul_right_cancel h1))
  intro h hh
  obtain ⟨h', hh'⟩ := Finite.surjective_of_injective hφ ⟨h, hh⟩
  have h1 : τ * (h' : G) * τ⁻¹ = h := congrArg Subtype.val hh'
  rw [← h1, show τ⁻¹ * (τ * (h' : G) * τ⁻¹) * τ = h' by group]
  exact h'.2

theorem factN13Sp4_holds : Ch11.SecA.FactN13Sp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ U₃ hU₁ hU₃ τ hτZ hτH
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  have hU₁' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U₁ := by rw [hK]; exact hU₁
  have hU₃' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 3 U₃ := by rw [hK]; exact hU₃
  obtain ⟨S₁, hS₁, hc₁, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₁'
  obtain ⟨S₃, hS₃, hc₃, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₃'
  rw [(eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one]), (eq_std_of_stable_sp hS₃).2.2 hc₃]
  have hτZ' : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp hτZ z).mp hz
  have hτZ'' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz =>
    (Ch11.SecA.mem_stabW.mp (Subgroup.inv_mem _ hτZ) z).mp hz
  have hτH' := inv_conj_mem_of_conj_mem hτH
  have hτiH : ∀ h ∈ H, τ⁻¹ * h * τ⁻¹⁻¹ ∈ H := by simpa using hτH'
  have hτiH' : ∀ h ∈ H, τ⁻¹⁻¹ * h * τ⁻¹ ∈ H := by simpa using hτH
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 τ hτZ'
    hτZ'' hτH'
  obtain ⟨σ', hσ'⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 τ⁻¹ hτZ''
    (by simpa using hτZ') hτiH'
  have hTf : ∀ w, hf.autMap τ hτZ' (f w) = f (τ w) := hf.autMap_apply _ _
  have hT'f : ∀ w, hf.autMap τ⁻¹ hτZ'' (f w) = f (τ⁻¹ w) := hf.autMap_apply _ _
  have hTT' : ∀ x, hf.autMap τ hτZ' (hf.autMap τ⁻¹ hτZ'' x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT'f, hTf, MulAut.apply_inv_self]
  have hT'T : ∀ x, hf.autMap τ⁻¹ hτZ'' (hf.autMap τ hτZ' x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hTf, hT'f, MulAut.inv_apply_self]
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      hf.autMap τ hτZ' (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ hf.autMap τ hτZ' x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, hτH _ (π γ).2⟩
    refine ⟨γ', fun x => ?_⟩
    have h1 := hf.autMap_lin τ hτZ' γ' γ (congrArg Subtype.val hγ').symm x
    exact (congrArg _ (linModelNat_lin _ γ x).symm).trans (h1.trans (linModelNat_lin _ γ' _))
  have hnorm' : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      hf.autMap τ⁻¹ hτZ'' (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ hf.autMap τ⁻¹ hτZ'' x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, hτiH _ (π γ).2⟩
    refine ⟨γ', fun x => ?_⟩
    have h1 := hf.autMap_lin τ⁻¹ hτZ'' γ' γ (congrArg Subtype.val hγ').symm x
    exact (congrArg _ (linModelNat_lin _ γ x).symm).trans (h1.trans (linModelNat_lin _ γ' _))
  have horth := orth_of_semilinear_normalizing hσ hnorm
  have horth' := orth_of_semilinear_normalizing hσ' hnorm'
  have hstab : ∀ S : Submodule K (Fin 2 ⊕ Fin 2 → K),
      τ ∈ Ch11.SecA.stabW (hf.pre S.toAddSubgroup) ↔
        ∀ x, x ∈ S ↔ hf.autMap τ hτZ' x ∈ S := by
    intro S
    rw [Ch11.SecA.mem_stabW]
    constructor
    · intro h x
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hTf]
      exact h w
    · intro h w
      rw [hf.mem_pre, hf.mem_pre, ← hTf]
      exact h (f w)
  rw [hstab, hstab]
  exact stab_line_iff_stab_hyp g hσ hσ' hTT' hT'T horth horth'

end CFSG.Quasithin.Vol2.KGNat
