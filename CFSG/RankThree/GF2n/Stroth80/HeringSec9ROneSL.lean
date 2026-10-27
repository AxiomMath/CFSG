module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneC

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

section Elations

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem elation_mul {u f₁ f₂ : ι → K} (h : f₁ ⬝ᵥ u = 0) :
    (1 + Matrix.vecMulVec u f₁) * (1 + Matrix.vecMulVec u f₂) =
      1 + Matrix.vecMulVec u (f₁ + f₂) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul]
  ext i j
  simp [Matrix.vecMulVec_apply, mul_add]
  ring

def elationGroup [CharP K 2] (u : ι → K) : Subgroup (GL ι K) where
  carrier := {g | ∃ f : ι → K, f ⬝ᵥ u = 0 ∧ (g : Matrix ι ι K) = 1 + Matrix.vecMulVec u f}
  one_mem' := ⟨0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩
  mul_mem' := by
    rintro a b ⟨f₁, h₁, ha⟩ ⟨f₂, h₂, hb⟩
    refine ⟨f₁ + f₂, by rw [add_dotProduct, h₁, h₂, add_zero], ?_⟩
    rw [Units.val_mul, ha, hb, elation_mul h₁]
  inv_mem' := by
    rintro a ⟨f, h, ha⟩
    have hsq : (a : Matrix ι ι K) * a = 1 := by
      rw [ha, elation_mul h]
      have : f + f = 0 := by
        ext i
        simp only [Pi.add_apply, Pi.zero_apply]
        exact CharTwo.add_self_eq_zero _
      rw [this]
      simp
    have hsq' : a * a = 1 := Units.ext (by rw [Units.val_mul, hsq]; rfl)
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq'
    exact ⟨f, h, by rw [hinv]; exact ha⟩

theorem eigen_of_commute_elation {u f : ι → K} (hf : f ≠ 0) {g : Matrix ι ι K}
    (hcomm : g * (1 + Matrix.vecMulVec u f) = (1 + Matrix.vecMulVec u f) * g) :
    ∃ c : K, g *ᵥ u = c • u := by
  have h1 : Matrix.vecMulVec (g *ᵥ u) f = Matrix.vecMulVec u (f ᵥ* g) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul] at hcomm
    exact add_left_cancel hcomm
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  refine ⟨(f ᵥ* g) j / f j, ?_⟩
  ext i
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.vecMulVec_apply] at h2
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination h2

theorem elationGroup_comm [CharP K 2] (u : ι → K) {a b : GL ι K} (ha : a ∈ elationGroup u)
    (hb : b ∈ elationGroup u) : a * b = b * a := by
  obtain ⟨f₁, h₁, ha⟩ := ha
  obtain ⟨f₂, h₂, hb⟩ := hb
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ha, hb, elation_mul h₁, elation_mul h₂, add_comm f₁ f₂]

theorem conj_elation_mem [CharP K 2] {u : ι → K} {g : GL ι K} {c : K} (hc0 : c ≠ 0)
    (hg : (g : Matrix ι ι K) *ᵥ u = c • u) {a : GL ι K} (ha : a ∈ elationGroup u) :
    g * a * g⁻¹ ∈ elationGroup u := by
  obtain ⟨f, hf, ha⟩ := ha
  have hginv : ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u = c⁻¹ • u := by
    have h1 : ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hg, Matrix.mulVec_smul] at h1
    calc ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u
        = c⁻¹ • (c • (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  refine ⟨c • (f ᵥ* ((g⁻¹ : GL ι K) : Matrix ι ι K)), ?_, ?_⟩
  · rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, hginv, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hf, mul_zero, mul_zero]
  · rw [Units.val_mul, Units.val_mul, ha, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hg, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    congr 1
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
    ring

end Elations

theorem not_slMNat_of_three_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) {m : ℕ} (hm : 3 ≤ m) : ¬ SLMNat hc x m := by
  classical
  rintro ⟨K, fK, finK, hK, hnat⟩
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans (one_part_a hc hsplit0 h4 hxL hx.2)
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  have hYN : Y ⊓ hc.CN x ≤ Q := Y_inf_CN_le_Q h34 h311a hc hs hxL hxQ hQY hYR hYsl
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hrel := HS6.relIndex_SL h34 hc hsx hK (by omega) hnat
  have hEidx := relIndex_LB_inf_X hc hsplit0 h4
  have hEN : ¬ (LB M Q B ⊓ X ≤ hc.CN x) := by
    intro hle
    have h1 := Subgroup.relIndex_dvd_of_le_left (LB M Q B) hle
    rw [hrel, hEidx] at h1
    have h2 : Nat.card Z ^ (m - 1) ≤ Nat.card Z := Nat.le_of_dvd Nat.card_pos h1
    have h3 : Nat.card Z ^ 2 ≤ Nat.card Z ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨e, he, heN⟩ := SetLike.not_le_iff_exists.mp hEN
  have h35all := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hVQB : Vt M (LB M Q B) B Z x ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n x hsx ⟨K, inferInstance, inferInstance, hK, m, by omega,
      hnat⟩
  obtain ⟨n', γ, M₀, -, hglob⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z x) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z x) :=
    fun c e he => hc.smul_mem_img_Vt hglob x c he
  obtain ⟨m', φ', hnorm', ψ', c', hker', hequiv', -, -, hSeq'⟩ :=
    exists_natural_data_of_subspace hc.hyp (hc.Vt_le_Q x) sec39_Z_le_Vt (hc.Rt_le_H0 x)
      (hc.Rt_normalizes_Vt hxL) (fun _ => Ctx.mem_CN (hc := hc)) hglob hS
  obtain ⟨b, hbV, hb0, hu0, hBb, hP1, hP2, hcount⟩ := hc.matrix_elation_data hs5.width hs5.n_gt
    hs5.noA2 h35all.2.2.1 h35all.2.2.2 hglob (hc.B_le_Vt hxL) (le_inf (hc.Vt_le_Q x) hVQB) hS
    (hc.Rt_le_H0 x) (hc.Rt_normalizes_Vt hxL) hLR φ' c' hSeq'
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hφN : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) x), r ∈ hc.CN x → φ' ⟨r, hr⟩ = 1 :=
    fun r hr hN => by
      have : (⟨r, hr⟩ : ↥(Rt M (LB M Q B) x)) ∈ φ'.ker := by
        rw [hker']
        exact Subgroup.mem_subgroupOf.mpr hN
      exact this
  have hφN' : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) x), φ' ⟨r, hr⟩ = 1 → r ∈ hc.CN x :=
    fun r hr h1 => by
      have : (⟨r, hr⟩ : ↥(Rt M (LB M Q B) x)) ∈ φ'.ker := h1
      rw [hker'] at this
      exact Subgroup.mem_subgroupOf.mp this
  have heR : e ∈ Rt M (LB M Q B) x := hLR he.1
  obtain ⟨f₀, hf₀u, hφe⟩ := hP1 e he.1
  have hf₀ : f₀ ≠ 0 := by
    rintro rfl
    apply heN
    refine hφN' e heR (Units.ext ?_)
    rw [hφe]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have heig : ∀ (y : G) (hy : y ∈ Y), ∃ c : GaloisField 2 n', c ≠ 0 ∧
      (φ' ⟨y, hYR hy⟩ : Matrix (Fin m') (Fin m') (GaloisField 2 n')) *ᵥ c' ⟨b, hbV⟩ =
        c • c' ⟨b, hbV⟩ := by
    intro y hy
    have hqN : ⁅e, y⁆ ∈ hc.CN x := hQN (hcXY e he.2 y hy)
    have hcommGL : φ' ⟨e, heR⟩ * φ' ⟨y, hYR hy⟩ = φ' ⟨y, hYR hy⟩ * φ' ⟨e, heR⟩ := by
      have h2 : φ' ⁅(⟨e, heR⟩ : ↥(Rt M (LB M Q B) x)), ⟨y, hYR hy⟩⁆ = 1 :=
        hφN (⁅e, y⁆) (hNR hqN) hqN
      rw [map_commutatorElement] at h2
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    have hcommM : (φ' ⟨y, hYR hy⟩ : Matrix (Fin m') (Fin m') (GaloisField 2 n')) *
        (1 + Matrix.vecMulVec (c' ⟨b, hbV⟩) f₀) =
        (1 + Matrix.vecMulVec (c' ⟨b, hbV⟩) f₀) * φ' ⟨y, hYR hy⟩ := by
      have h3 := congrArg Units.val hcommGL
      rw [Units.val_mul, Units.val_mul, hφe] at h3
      exact h3.symm
    obtain ⟨c, hc⟩ := eigen_of_commute_elation hf₀ hcommM
    refine ⟨c, ?_, hc⟩
    rintro rfl
    rw [zero_smul] at hc
    apply hu0
    have h4' : (((φ' ⟨y, hYR hy⟩)⁻¹ : GL (Fin m') (GaloisField 2 n')) :
        Matrix (Fin m') (Fin m') (GaloisField 2 n')) *ᵥ
        ((φ' ⟨y, hYR hy⟩ : Matrix (Fin m') (Fin m') (GaloisField 2 n')) *ᵥ c' ⟨b, hbV⟩) =
        c' ⟨b, hbV⟩ := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hc, Matrix.mulVec_zero] at h4'
    exact h4'.symm
  obtain ⟨σ, hσ, hσQ⟩ := exists_mem_LB_inf_Y_not_mem hc h4
  obtain ⟨fσ, hfσu, hφσ⟩ := hP1 σ hσ.1
  let ψY : ↥Y →* GL (Fin m') (GaloisField 2 n') := φ'.comp (Subgroup.inclusion hYR)
  let K₂ : Subgroup G := ((elationGroup (c' ⟨b, hbV⟩)).comap ψY).map Y.subtype
  have hmemK₂ : ∀ (y : G) (hy : y ∈ Y),
      y ∈ K₂ ↔ φ' ⟨y, hYR hy⟩ ∈ elationGroup (c' ⟨b, hbV⟩) := by
    intro y hy
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro h
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hK₂Y : K₂ ≤ Y := Subgroup.map_subtype_le _
  have hQK₂ : Q ≤ K₂ := fun q hq => by
    refine (hmemK₂ q (hQY hq)).mpr ?_
    rw [hφN q (hYR (hQY hq)) (hQN hq)]
    exact (elationGroup (c' ⟨b, hbV⟩)).one_mem
  have hσK₂ : σ ∈ K₂ := (hmemK₂ σ hσ.2).mpr ⟨fσ, hfσu, hφσ⟩
  have hnormK₂ : ∀ y ∈ Y, ∀ k ∈ K₂, y * k * y⁻¹ ∈ K₂ := by
    intro y hy k hk
    have hkY : k ∈ Y := hK₂Y hk
    have hyk : y * k * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hkY) (Y.inv_mem hy)
    refine (hmemK₂ _ hyk).mpr ?_
    obtain ⟨c, hc0, hcg⟩ := heig y hy
    have hkE := (hmemK₂ k hkY).mp hk
    have := conj_elation_mem hc0 hcg hkE
    have e1 : φ' ⟨y * k * y⁻¹, hYR hyk⟩ =
        φ' ⟨y, hYR hy⟩ * φ' ⟨k, hYR hkY⟩ * (φ' ⟨y, hYR hy⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact this
  have hK₂eq : K₂ = Y := eq_of_normal_of_ne_Q hq4 hq2 hYsl hQK₂ hK₂Y hnormK₂
    (fun h => hσQ (h hσK₂))
  have hnc : ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ⁅y₁, y₂⁆ ∉ Q := by
    by_contra hall
    push Not at hall
    exact hσQ (mem_of_comm_mem_Q hq4 hq2 hYsl hσ.2 fun y hy => hall σ hσ.2 y hy)
  obtain ⟨y₁, hy₁, y₂, hy₂, hcQ⟩ := hnc
  have hE₁ : φ' ⟨y₁, hYR hy₁⟩ ∈ elationGroup (c' ⟨b, hbV⟩) :=
    (hmemK₂ y₁ hy₁).mp (hK₂eq ▸ hy₁)
  have hE₂ : φ' ⟨y₂, hYR hy₂⟩ ∈ elationGroup (c' ⟨b, hbV⟩) :=
    (hmemK₂ y₂ hy₂).mp (hK₂eq ▸ hy₂)
  have hcomm : φ' ⟨y₁, hYR hy₁⟩ * φ' ⟨y₂, hYR hy₂⟩ = φ' ⟨y₂, hYR hy₂⟩ * φ' ⟨y₁, hYR hy₁⟩ :=
    elationGroup_comm _ hE₁ hE₂
  have hYm : ⁅y₁, y₂⁆ ∈ Y := Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁))
    (Y.inv_mem hy₂)
  have hcom1 : φ' ⁅(⟨y₁, hYR hy₁⟩ : ↥(Rt M (LB M Q B) x)), ⟨y₂, hYR hy₂⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hN := hφN' ⁅y₁, y₂⁆ (hYR hYm) hcom1
  exact hcQ (hYN ⟨hYm, hN⟩)

end HS9

@[expose] def Sec97OneTypesNoSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
    ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      (∀ m : ℕ, 2 ≤ m → ¬ SpMNat hc x m) ∧ (∀ m : ℕ, 3 ≤ m → ¬ OmegaPlusNat hc x m) ∧
      (∀ m : ℕ, 2 ≤ m → ¬ OmegaMinusNat hc x m)

theorem sec97OneTypes_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hT : Sec97OneTypesNoSL) : Sec97OneTypes := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
  obtain ⟨hSp, hOm, hOmM⟩ := hT G M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
  exact ⟨fun m hm => HS9.not_slMNat_of_three_le h34 h311a hc hs hsplit h4 hx hxQ hm, hSp, hOm,
    hOmM⟩

theorem sec97One_of_noSL (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) (hT : Sec97OneTypesNoSL) (hO : Sec97OneOmega) :
    Sec97OneStatement :=
  sec97One_of h34 h310 h311a (sec97OneTypes_of h34 h311a hT) hO

end CFSG.RankThree.GF2n.Stroth80
