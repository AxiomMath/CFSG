module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Aux
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Descent
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_mem)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

theorem fieldSU4_mul (φ ψ : K ≃+* K) : fieldSU4 (φ * ψ) = fieldSU4 φ * fieldSU4 ψ := by
  ext g : 2
  change glAut (φ * ψ) (g : GL (Fin 4) K) = glAut φ (glAut ψ (g : GL (Fin 4) K))
  rw [map_mul]
  rfl

theorem fieldSU4_one : fieldSU4 1 = 1 := by
  ext g : 2
  change glAut 1 (g : GL (Fin 4) K) = g
  rw [map_one]
  rfl

theorem fieldSU4_pow (φ : K ≃+* K) (m : ℕ) : fieldSU4 φ ^ m = fieldSU4 (φ ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, fieldSU4_one]
  | succ m ih => rw [pow_succ, ih, ← fieldSU4_mul, ← pow_succ]

theorem fieldSU4_apply_of_mem_Dstd {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) {x : SU4} (hx : x ∈ Dstd) :
    fieldSU4 φ x = x := by
  obtain ⟨a, rfl⟩ := hx
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSU4, coe_glAut, coe_torusSU4, diagonal_map (map_zero φ)]
  congr 1
  funext k
  refine CFSG.RankThree.PartTwo.KFacts.KS21.U58.ringAut_fix_cube_root hφ3 ?_
  have hk : torusSnoc 3 (fun i => (a i : Kˣ)) k ∈ μ3 := torusSnoc_mem 3 (fun i => (a i).2) k
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp hk, Units.val_one]

theorem mul_apply_apply_eq_one {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {F α : MulAut X} (g : X) (hα : ∀ x, α x = g * F x * g⁻¹) (hF3 : F ^ 3 = 1)
    (hα3 : α ^ 3 = 1) : g * F g * F (F g) = 1 := by
  have hF3' : ∀ x, F (F (F x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hF3
    simpa [pow_succ] using this
  have hα3' : ∀ x, α (α (α x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hα3
    simpa [pow_succ] using this
  have key : ∀ x, α (α (α x)) = (g * F g * F (F g)) * x * (g * F g * F (F g))⁻¹ := by
    intro x
    simp only [hα, map_mul, map_inv, hF3']
    group
  have hN : g * F g * F (F g) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := key x
    rw [hα3' x] at h1
    calc x * (g * F g * F (F g)) = (g * F g * F (F g)) * x * (g * F g * F (F g))⁻¹ *
          (g * F g * F (F g)) := by rw [← h1]
      _ = (g * F g * F (F g)) * x := by group
  rw [hZ] at hN
  exact Subgroup.mem_bot.mp hN

theorem apply_eq_of_commute_conj {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {α : MulAut X} {p : X} (hc : α * MulAut.conj p = MulAut.conj p * α) : α p = p := by
  have hmem : p⁻¹ * α p ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun f : MulAut X => f (α.symm y)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
      at h1
    calc y * (p⁻¹ * α p) = (p⁻¹ * (p * y * p⁻¹) * p) * (p⁻¹ * α p) := by group
      _ = (p⁻¹ * (α p * y * (α p)⁻¹) * p) * (p⁻¹ * α p) := by rw [h1]
      _ = (p⁻¹ * α p) * y := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

theorem unitary_of_mem_SU4 (x : SU4) :
    (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hK.bar)ᵀ *
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have h : (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ4)ᵀ *
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := x.2.2
  have hb : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hK.bar =
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ4 := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hb]
  exact h

section Main

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Item434Kit Item434Alt

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_outer (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* SU4)
    (hA27 : Nat.card (A.map (quotConj e)) = 27)
    (hout : ∃ α ∈ A.map (quotConj e), fieldFactor4 α ≠ 1) : False := by
  obtain ⟨α₀, hα₀A, hα₀⟩ := hout
  have hAe := isElemAbelian_map_quotConj h e
  have hinj := conj_injective_of_center_eq_bot center_SU4
  have hAc : ∀ a ∈ A.map (quotConj e), ∀ b ∈ A.map (quotConj e), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A.map (quotConj e), a ^ 3 = 1 := hAe.2
  obtain ⟨β, hβA, hβ1, hβψ⟩ : ∃ β ∈ A.map (quotConj e), β ≠ 1 ∧ fieldFactor4 β = 1 := by
    by_contra hcon
    push Not at hcon
    have hψinj : Function.Injective (fieldFactor4.comp (A.map (quotConj e)).subtype) := by
      rw [injective_iff_map_eq_one]
      intro b hb
      by_contra hne
      exact hcon b b.2 (fun h1 => hne (Subtype.ext h1)) hb
    have := Nat.card_le_card_of_injective _ hψinj
    rw [hA27, CFSG.RankThree.PartTwo.KFacts.KS21.U58.card_ringAut_K] at this
    omega
  obtain ⟨p₁, hp₁⟩ := mem_range_conj_of_fieldFactor4_eq_one hβψ
  have hp₁1 : p₁ ≠ 1 := fun h1 => hβ1 (by rw [← hp₁, h1, map_one])
  have hp₁3 : p₁ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hp₁, map_one]
    exact hA3 β hβA
  have hfixp₁ : α₀ p₁ = p₁ := by
    apply apply_eq_of_commute_conj center_SU4
    rw [hp₁]
    exact hAc α₀ hα₀A β hβA
  set φ : K ≃+* K := fieldFactor4 α₀ with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hA3 α₀ hα₀A, map_one]
  obtain ⟨g₀, hg₀⟩ := exists_conj_field4 α₀
  have hα : ∀ x, α₀ x = g₀ * fieldSU4 φ x * g₀⁻¹ := fun x => Subtype.ext (by rw [hg₀ x]; rfl)
  have hN : g₀ * fieldSU4 φ g₀ * fieldSU4 φ (fieldSU4 φ g₀) = 1 :=
    mul_apply_apply_eq_one center_SU4 g₀ hα (by rw [fieldSU4_pow, hφ3, fieldSU4_one])
      (hA3 α₀ hα₀A)
  have hN' : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
      (((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ).map φ = 1 := by
    have := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hN
    simpa [coe_fieldSU4, coe_glAut] using this
  have hfix : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((p₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((p₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have h1 := hg₀ p₁
    rw [hfixp₁] at h1
    have h2 : (p₁ : GL (Fin 4) K) * g₀ = g₀ * glAut φ (p₁ : GL (Fin 4) K) := by
      calc (p₁ : GL (Fin 4) K) * g₀ =
          ((g₀ : GL (Fin 4) K) * glAut φ (p₁ : GL (Fin 4) K) * (g₀ : GL (Fin 4) K)⁻¹) * g₀ := by
            rw [← h1]
        _ = g₀ * glAut φ (p₁ : GL (Fin 4) K) := by group
    have := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h2
    simpa [coe_glAut] using this.symm
  have hφ1 : φ ≠ 1 := hα₀
  obtain ⟨H, hH, hgH, d, -, hpH⟩ := exists_fixed_orthonormal_eigenbasis
    (unitary_of_mem_SU4 g₀) hφ3 hφ1 hN' (unitary_of_mem_SU4 p₁)
    (by
      have := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hp₁3
      simpa using this)
    hfix
  let Hu : GL (Fin 4) K := ⟨H, (H.map hK.bar)ᵀ, mul_eq_one_comm.mp hH, hH⟩
  have hHu : Hu ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary]
    simpa using hH
  obtain ⟨h₀, hh₀⟩ := exists_SU4_conj_eq hHu
  have hh₀' : ∀ z : GL (Fin 4) K, (h₀ : GL (Fin 4) K)⁻¹ * z * h₀ = Hu⁻¹ * z * Hu := by
    intro z
    have h1 := hh₀ ((h₀ : GL (Fin 4) K)⁻¹ * z * h₀)
    have h2 : Hu * ((h₀ : GL (Fin 4) K)⁻¹ * z * h₀) * Hu⁻¹ = z := by rw [h1]; group
    calc (h₀ : GL (Fin 4) K)⁻¹ * z * h₀ =
        Hu⁻¹ * (Hu * ((h₀ : GL (Fin 4) K)⁻¹ * z * h₀) * Hu⁻¹) * Hu := by group
      _ = Hu⁻¹ * z * Hu := by rw [h2]
  set E : Subgroup SU4 := Dstd.map (MulAut.conj h₀).toMonoidHom with hE
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ Dstd isElemAbelian_Dstd
  have hEcard : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj h₀).injective, card_Dstd]
  have hEfix : ∀ y ∈ E, α₀ y = y := by
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [hg₀]
    have e1 : (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K) = Hu * (x : GL (Fin 4) K) * Hu⁻¹ :=
      (hh₀ (x : GL (Fin 4) K)).symm
    have e2 : glAut φ (x : GL (Fin 4) K) = x := by
      have := congrArg (fun y : SU4 => (y : GL (Fin 4) K)) (fieldSU4_apply_of_mem_Dstd hφ3 hx)
      simpa [coe_fieldSU4] using this
    have e3 : (g₀ : GL (Fin 4) K) * glAut φ Hu = Hu := by
      apply Units.ext
      rw [Units.val_mul, coe_glAut]
      exact hgH
    change (g₀ : GL (Fin 4) K) * glAut φ (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K) *
      (g₀ : GL (Fin 4) K)⁻¹ = (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K)
    rw [e1, map_mul, map_mul, map_inv, e2]
    calc (g₀ : GL (Fin 4) K) * (glAut φ Hu * x * (glAut φ Hu)⁻¹) * (g₀ : GL (Fin 4) K)⁻¹ =
        ((g₀ : GL (Fin 4) K) * glAut φ Hu) * x * ((g₀ : GL (Fin 4) K) * glAut φ Hu)⁻¹ := by
          group
      _ = Hu * x * Hu⁻¹ := by rw [e3]
  have hp₁E : p₁ ∈ E := by
    have hdiag : ((((h₀⁻¹ * p₁ * h₀ : SU4) : GL (Fin 4) K)) :
        Matrix (Fin 4) (Fin 4) K).IsDiag := by
      have e4 : (((h₀⁻¹ * p₁ * h₀ : SU4) : GL (Fin 4) K)) = Hu⁻¹ * (p₁ : GL (Fin 4) K) * Hu :=
        hh₀' p₁
      rw [e4]
      have e5 : ((Hu⁻¹ * (p₁ : GL (Fin 4) K) * Hu : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          diagonal d := by
        rw [Units.val_mul, Units.val_mul]
        change (H.map hK.bar)ᵀ * ((p₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * H = _
        rw [Matrix.mul_assoc, hpH, ← Matrix.mul_assoc, hH, Matrix.one_mul]
      rw [e5]
      exact isDiag_diagonal d
    refine ⟨h₀⁻¹ * p₁ * h₀, mem_Dstd_of_isDiag hdiag ?_, ?_⟩
    · have h3 := conj_pow (a := h₀⁻¹) (b := p₁) (i := 3)
      rw [inv_inv] at h3
      rw [h3, hp₁3, mul_one, inv_mul_cancel]
    · change h₀ * (h₀⁻¹ * p₁ * h₀) * h₀⁻¹ = p₁
      group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ã₀, hã₀A, hã₀⟩ := hα₀A
  obtain ⟨a₁, ha₁A, ha₁⟩ := hβA
  have hlift : ∀ b : G, (∀ y ∈ E, quotConj e b y = y) →
      ∀ z ∈ liftSub e hZ E, b * z = z * b := by
    intro b hb z hz
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hz
    set ι := layerEquiv e hZ
    have hconj : layerConj G b (ι.symm y) = ι.symm y := by
      apply layerQuot_injective e hZ
      rw [← quotConj_layerQuot]
      have hy' : layerQuot e (ι.symm y) = y := ι.apply_symm_apply y
      rw [hy', hb y hy]
    have h1 : b * ((ι.symm y : layer G) : G) * b⁻¹ = ι.symm y := by
      rw [← layerConj_apply_coe, hconj]
    change b * ((ι.symm y : layer G) : G) = ((ι.symm y : layer G) : G) * b
    calc b * ((ι.symm y : layer G) : G) = b * ((ι.symm y : layer G) : G) * b⁻¹ * b := by group
      _ = ((ι.symm y : layer G) : G) * b := by rw [h1]
  have hÊ : CFSG.Assembly.IsElemAbelian 3 (liftSub e hZ E) := isElemAbelian_liftSub e hZ hEe
  have hÊcard : Nat.card (liftSub e hZ E) = 27 := by rw [card_liftSub, hEcard]
  have hã₀fix : ∀ y ∈ E, quotConj e ã₀ y = y := by
    rw [hã₀]
    exact hEfix
  have ha₁fix : ∀ y ∈ E, quotConj e a₁ y = y := by
    intro y hy
    rw [ha₁, ← hp₁]
    have hc : p₁ * y = y * p₁ := congrArg Subtype.val (hEe.1.is_comm.comm ⟨p₁, hp₁E⟩ ⟨y, hy⟩)
    change p₁ * y * p₁⁻¹ = y
    rw [hc]
    group
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hã₀L : ã₀ ∉ layer G := fun hl => by
    apply hα₀
    rw [hφdef, ← hã₀, quotConj_eq_conj_layerQuot e hl]
    exact fieldFactor4_conj _
  have hã₀Ê : ã₀ ∉ liftSub e hZ E := fun hz => hã₀L (liftSub_le e hZ E hz)
  have hã₀3 : ã₀ ^ 3 = 1 := h.isE27.1.2 ã₀ hã₀A
  have ha₁1 : a₁ ≠ 1 := fun h1 => hβ1 (by rw [← ha₁, h1, map_one])
  have ha₁3 : a₁ ^ 3 = 1 := h.isE27.1.2 a₁ ha₁A
  have ha₁ord : orderOf a₁ = 3 := orderOf_eq_prime ha₁3 ha₁1
  have hã₀ni : ã₀ ∉ Subgroup.zpowers a₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hα₀
    rw [hφdef, ← hã₀, ← hk, map_zpow, ha₁, ← hp₁, ← map_zpow]
    exact fieldFactor4_conj _
  obtain ⟨hD, hDcard⟩ := Sec5.isElemAbelian_sup_zpowers hÊ hã₀Ê hã₀3
    (fun z hz => (hlift ã₀ hã₀fix z hz).symm)
  obtain ⟨-, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers
    (Source.isElemAbelian_of_le h.isE27.1 (Subgroup.zpowers_le.mpr ha₁A)) hã₀ni hã₀3
    (fun x hx => hAcomm x (Subgroup.zpowers_le.mpr ha₁A hx) ã₀ hã₀A)
  have hBA : Subgroup.zpowers a₁ ⊔ Subgroup.zpowers ã₀ ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr ha₁A) (Subgroup.zpowers_le.mpr hã₀A)
  have hB9 : 9 ≤ Nat.card (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers ã₀ : Subgroup G) := by
    rw [hBcard, Nat.card_zpowers, ha₁ord]
  have hDa₁ : liftSub e hZ E ⊔ Subgroup.zpowers ã₀ ≤ Subgroup.centralizer ({a₁} : Set G) := by
    refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hlift a₁ ha₁fix z hz).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hAcomm a₁ ha₁A ã₀ hã₀A).symm
  have hDã₀ : liftSub e hZ E ⊔ Subgroup.zpowers ã₀ ≤ Subgroup.centralizer ({ã₀} : Set G) := by
    refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hlift ã₀ hã₀fix z hz).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
  have hBD : (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers ã₀ : Subgroup G) ≤
      Subgroup.centralizer ((liftSub e hZ E ⊔ Subgroup.zpowers ã₀ : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mp (hDa₁ hz)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mp (hDã₀ hz)
  refine false_of_le_centralizer h hBA hB9 hD (by rw [hDcard, hÊcard]) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.mp (hBD hb) z hz).symm

end Main

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
