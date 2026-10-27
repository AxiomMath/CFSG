module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfD4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.SylowCenters
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.EvenBN.TrialityD4
open scoped commutatorElement

section Data

variable {X : Type} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem cbAt_trialityD4Data : CBAt X d.S := by
  intro b hb hc
  have hbB : b ∈ d.B := by
    have h1 : (d.S : Set X) = (sixClosure d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ : Set X) := rfl
    rw [h1, d.normalizer_eq] at hb
    exact hb
  obtain ⟨x, hx, t, ht, rfl⟩ := d.mem_B_iff.mp hbB
  obtain ⟨⟨l, m⟩, rfl⟩ := d.mem_J.mp ht
  have key : ∀ y ∈ d.S, x * (d.torus (l, m) * y * (d.torus (l, m))⁻¹) * x⁻¹ = y := fun y hy => by
    calc x * (d.torus (l, m) * y * (d.torus (l, m))⁻¹) * x⁻¹ =
          x * d.torus (l, m) * y * (x * d.torus (l, m))⁻¹ := by group
      _ = y := by rw [hc y hy, mul_inv_cancel_right]
  have h1 := key (d.x₁ 1) (d.U₁_le_S (d.x₁_mem_U₁ 1))
  have h2 := key (d.x₂ 1) (d.U₂_le_S (d.x₂_mem_U₂ 1))
  rw [d.torus_x₁] at h1
  rw [d.torus_x₂] at h2
  have hm : (m : d.Γ) = 1 := by
    have e1 : x⁻¹ * d.x₁ 1 * x = d.x₁ ((m : d.Γ) * 1) := by
      rw [← h1]
      group
    have e : ⁅x⁻¹, d.x₁ 1⁆ = d.x₁ ((m : d.Γ) + 1) := by
      rw [commutatorElement_def, inv_inv, e1, d.x₁_inv, mul_one, ← d.x₁_add]
    have hF : ⁅x⁻¹, d.x₁ 1⁆ ∈ d.F := d.commutator_S_eq ▸
      Subgroup.commutator_mem_commutator (inv_mem hx) (d.U₁_le_S (d.x₁_mem_U₁ 1))
    rw [e] at hF
    have h0 := d.x₁_mem_D_iff.mp (d.F_le_D hF)
    rw [← CharTwo.sub_eq_add, sub_eq_zero] at h0
    exact h0
  have hl : (l : d.Γ₀) = 1 := by
    have e1 : x⁻¹ * d.x₂ 1 * x = d.x₂ ((l : d.Γ₀) * 1) := by
      rw [← h2]
      group
    have e : ⁅x⁻¹, d.x₂ 1⁆ = d.x₂ ((l : d.Γ₀) + 1) := by
      rw [commutatorElement_def, inv_inv, e1, d.x₂_inv, mul_one, ← d.x₂_add]
    have hF : ⁅x⁻¹, d.x₂ 1⁆ ∈ d.F := d.commutator_S_eq ▸
      Subgroup.commutator_mem_commutator (inv_mem hx) (d.U₂_le_S (d.x₂_mem_U₂ 1))
    rw [e] at hF
    have h0 := d.x₂_mem_M_iff.mp (d.F_le_M hF)
    rw [← CharTwo.sub_eq_add, sub_eq_zero] at h0
    exact h0
  have ht1 : d.torus (l, m) = 1 := by
    rw [show (l, m) = (1 : (d.Γ₀)ˣ × d.Γˣ) from Prod.ext (Units.ext hl) (Units.ext hm), map_one]
  rw [ht1, mul_one]
  exact hx

end Data


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem invAt_d4 {f : ℕ} (hf : 3 ≤ f) (hσ : σ.toRingHom ^ 3 = 1)
    (hσq : ∀ c, σ c = c ^ (2 ^ f)) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hk : Nat.card (fixedSubfield σ) = 2 ^ f) :
    InvAt (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hf1 : 1 ≤ f := by omega
  have hS : (modelData hf1 K σ hσ hσq hK hk).S =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Model.sixClosure_eq σ hσ
  rw [← hS]
  intro z hz hz1 hzc
  have hzV : z ∈ (modelData hf1 K σ hσ hσq hK hk).V := by
    rw [← (modelData hf1 K σ hσ hσq hK hk).S_inf_centralizer_S]
    exact ⟨hz, Subgroup.mem_centralizer_iff.mpr fun y hy => (hzc y hy).symm⟩
  obtain ⟨c, hc⟩ := hzV
  change fixedSubfield σ at c
  have hzc6 : z = Model.cx₆ σ hσ c := hc.symm
  subst hzc6
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    have h0 := Model.cx₆_add σ hσ 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.mp h0.symm)
  set a : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩ with ha
  have hcard1 : (TwistTag.D4.orbit a).card = 1 := by decide
  have hmin : TwistTag.D4.orbitMin a = ⟨2, by decide⟩ := by decide
  obtain ⟨R, hRu, -, -, -, -, hRrange, hRle, hRker, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a
  have hmemR : ∀ A, R A ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun A =>
    hRle (hRrange ▸ ⟨A, rfl⟩)
  let φ := R.codRestrict _ hmemR
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hA' : A ∈ R.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hA
    obtain ⟨l, hl2, hlA⟩ := hRker A hA'
    have hl1 : (l : orbitField TwistTag.D4 K σ.toRingHom a) = 1 := by
      apply Subtype.ext
      have h1 : (((l : orbitField TwistTag.D4 K σ.toRingHom a) : K) + 1) ^ 2 = 0 := by
        have h2 := congrArg Subtype.val hl2
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
        have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h2 + (((l : orbitField TwistTag.D4 K σ.toRingHom a) : K) + 1) * h3
      have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      rw [← CharTwo.sub_eq_add, sub_eq_zero] at h4
      exact h4
    rw [hl1, one_smul] at hlA
    exact Subtype.ext hlA
  have hsσ : ((σ.toRingHom ^ (TwistTag.D4.orbit a).card) (c : K)) = (c : K) := by
    rw [hcard1, pow_one]
    exact c.2
  set s : orbitField TwistTag.D4 K σ.toRingHom a := ⟨(c : K), hsσ⟩ with hsdef
  have hs0 : s ≠ 0 := fun h0 => hc0 (Subtype.ext (congrArg Subtype.val h0))
  have hRs : φ (xT s) = Model.cx₂ σ hσ c := by
    apply Subtype.ext
    have hxu : xT s = uSL s := Subtype.ext (by rw [coe_xT, coe_uSL])
    change R (xT s) = pinnedX TwistTag.D4.tag K (trialityRoot 1) (c : K)
    rw [hxu, hRu, coe_orbitX, hcard1, hmin]
    have hroot : trialityRoot 1 = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hroot, pinnedX_single]
    simp [hsdef]
  have hconj : (Model.cv σ * Model.cu σ) * Model.cx₂ σ hσ c * (Model.cv σ * Model.cu σ)⁻¹ =
      Model.cx₆ σ hσ c := by
    have hu : (Model.cu σ)⁻¹ = Model.cu σ := inv_eq_of_mul_eq_one_right (Model.cu_mul_self σ)
    have hv : (Model.cv σ)⁻¹ = Model.cv σ := inv_eq_of_mul_eq_one_right (Model.cv_mul_self σ)
    rw [mul_inv_rev, hu, hv, ← Model.cv_x₅ σ hσ, ← Model.cu_x₂ σ hσ]
    group
  have hF : Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) = 2 ^ f := by
    have heq : orbitField TwistTag.D4 K σ.toRingHom a = fixedSubfield σ := by
      ext x
      change (σ.toRingHom ^ (TwistTag.D4.orbit a).card) x = x ↔ σ x = x
      rw [hcard1, pow_one]
      rfl
    rw [heq]
    exact hk
  have : CharP (orbitField TwistTag.D4 K σ.toRingHom a) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_inv_of_hom hF hf
    ((MulAut.conj (Model.cv σ * Model.cu σ)).toMonoidHom.comp φ)
    ((MulAut.conj (Model.cv σ * Model.cu σ)).injective.comp hφ) hs0
  have hz : ((MulAut.conj (Model.cv σ * Model.cu σ)).toMonoidHom.comp φ) (xT s) =
      Model.cx₆ σ hσ c := by
    rw [MonoidHom.comp_apply, hRs, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hconj
  rw [hz] at hy2
  exact ⟨y, hy1, hy2, hy3⟩

end Model

theorem ordTrialityD4_ne {q : ℕ} (hq : 8 ≤ q) : CFSG.Open.ordTrialityD4 q ≠ 20160 := by
  intro h
  have a1 : 8 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have a2 : 1 ≤ q ^ 8 + q ^ 4 + 1 := by omega
  have a3 : 64 ≤ q ^ 2 := by
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have a4 : 8 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have a5 : 1 ≤ q ^ 6 - 1 := by norm_num at a4; omega
  have a6 : 1 ≤ q ^ 2 - 1 := by omega
  unfold CFSG.Open.ordTrialityD4 at h
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a5) a6
  norm_num at this
  omega

theorem false_of_autConf_3d4 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : ChevalleyExceptionalModel M .trialityD4 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  have hcard : Nat.card M = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hM
  obtain ⟨K, _, _, _, σ, -, hσq, hK, hk, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.TrialityCover.triality_model (by omega) hM.2
  have hσ : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσq c
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h34 : ¬ IsPSL 3 2 2 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e.toEquiv, hcard] at h1
    exact ordTrialityD4_ne h8 h1
  have hS : (modelData (by omega) K σ hσ hσq hK hk).S =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Model.sixClosure_eq σ hσ
  have hCB := cbAt_trialityD4Data (modelData (by omega) K σ hσ hσq hK hk)
  rw [hS] at hCB
  exact not_autConf_of_at (isSylowTwoOf_d4U (σ := σ)) (n4At_d4 (σ := σ) (by omega) hK hσq) h34
    hCB (invAt_d4 σ hf hσ hσq hK hk) (h.map e)

end CFSG.Quasithin.H13.S126C
