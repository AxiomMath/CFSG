module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EB1
public import CFSG.RankThree.PartTwo.Sec21.Hering214EFour
public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Hering2119
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

section Root

variable {L : Type} [Group L] {F : Type} [Field F] [CharP F 2]

theorem commute_of_root_lifts (Ψ : L →* projectiveSL 3 F) (hΨ : Function.Surjective Ψ)
    (hker : ∀ z : L, Ψ z = 1 → ∀ h : L, h * z = z * h) (g : GL (Fin 3) F) {A A' : L} {a a' : F}
    (hA : Ψ A = conjAut 3 F g (proj 3 F (xSL a)))
    (hA' : Ψ A' = conjAut 3 F g (proj 3 F (xSL a'))) : A * A' = A' * A := by
  set φ : SpecialLinearGroup (Fin 3) F →* projectiveSL 3 F :=
    (conjAut 3 F g).toMonoidHom.comp (proj 3 F) with hφ
  have hφapp : ∀ m, φ m = conjAut 3 F g (proj 3 F m) := fun _ => rfl
  rw [← hφapp] at hA hA'
  obtain ⟨s, hs⟩ := hΨ (φ pSL)
  obtain ⟨u, hu⟩ := hΨ (φ uSL)
  have hpinv : (pSL : SpecialLinearGroup (Fin 3) F)⁻¹ = pSL :=
    inv_eq_of_mul_eq_one_right pSL_mul_self
  have huinv : (uSL : SpecialLinearGroup (Fin 3) F)⁻¹ = uSL :=
    inv_eq_of_mul_eq_one_right uSL_mul_self
  have hconj : ∀ p q : SpecialLinearGroup (Fin 3) F,
      φ p * φ q * (φ p)⁻¹ = φ (p * q * p⁻¹) := fun p q => by rw [map_mul, map_mul, map_inv]
  have hcomm : ∀ p q : SpecialLinearGroup (Fin 3) F, p * q = q * p → φ p * φ q = φ q * φ p :=
    fun p q h => by rw [← map_mul, h, map_mul]
  refine commute_of_lift_relations Ψ hker (x := φ (xSL a)) (x' := φ (xSL a'))
    (y := φ (zSL a)) (y' := φ (zSL a')) (hcomm _ _ (xSL_mul_comm a a'))
    (hcomm _ _ (xSL_mul_zSL_comm a a)) (hcomm _ _ (xSL_mul_zSL_comm a a'))
    (hcomm _ _ (xSL_mul_zSL_comm a' a)) (hcomm _ _ (xSL_mul_zSL_comm a' a'))
    (hcomm _ _ (zSL_mul_comm a a')) (by rw [← map_mul, xSL_mul_self, map_one]) (s := s) (u := u)
    ?_ ?_ ?_ ?_ ?_ hA hA'
  · rw [hs, hconj, hpinv, pSL_xSL]
  · rw [hs, hconj, hpinv, pSL_xSL]
  · rw [hs, hconj, hpinv, pSL_zSL]
  · rw [hu, hconj, huinv, uSL_xSL, map_mul]
  · rw [hu, hconj, huinv, uSL_xSL, map_mul]

end Root

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroupsMinus_of_model {E L : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) {F : Type} [Field F] [CharP F 2]
    (Ψ : ↥L →* projectiveSL 3 F) (hΨ : Function.Surjective Ψ)
    (hker : ∀ z : ↥L, Ψ z = 1 → ∀ h : ↥L, h * z = z * h) (g : GL (Fin 3) F) {τ : Fˣ}
    (hτ1 : τ ≠ 1)
    (hpart1 : ∀ e (he : e ∈ E), ∃ s t : Fˣ, ∀ x : ↥L,
      Ψ (L.normalizerMonoidHom ⟨e, hEL he⟩ x) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Ψ x))
    (hpart2 : ∃ e, ∃ he : e ∈ E, ∀ x : ↥L,
      Ψ (L.normalizerMonoidHom ⟨e, hEL he⟩ x) = conjAut 3 F (g * diagUnits 1 τ 1 * g⁻¹) (Ψ x)) :
    ∃ V ∈ fourGroupsMinus E, V ≤ L := by
  classical
  set cg : MulAut (projectiveSL 3 F) := conjAut 3 F g with hcg
  have hframe : ∀ (d : GL (Fin 3) F) (w : projectiveSL 3 F),
      conjAut 3 F (g * d * g⁻¹) (cg w) = cg (conjAut 3 F d w) := by
    intro d w
    rw [map_mul, map_mul, map_inv]
    simp [MulAut.mul_apply, hcg]
  let inR : ↥L → Prop := fun x => ∃ a : F, Ψ x = cg (proj 3 F (xSL a))
  have hcommR : ∀ x y : ↥L, inR x → inR y → x * y = y * x := fun x y ⟨a, ha⟩ ⟨b, hb⟩ =>
    commute_of_root_lifts Ψ hΨ hker g ha hb
  have hmulR : ∀ x y : ↥L, inR x → inR y → inR (x * y) := fun x y ⟨a, ha⟩ ⟨b, hb⟩ =>
    ⟨a + b, by rw [map_mul, ha, hb, xSL_add, map_mul, map_mul]⟩
  have hinvR : ∀ x : ↥L, inR x → inR x⁻¹ := fun x ⟨a, ha⟩ =>
    ⟨a, by rw [map_inv, ha, ← map_inv, ← map_inv, inv_eq_of_mul_eq_one_right (xSL_mul_self a)]⟩
  have honeR : inR 1 := ⟨0, by rw [map_one, xSL_zero, map_one, map_one]⟩
  have hconjR : ∀ e (he : e ∈ E) (x : ↥L), inR x →
      inR (L.normalizerMonoidHom ⟨e, hEL he⟩ x) := by
    intro e he x ⟨a, ha⟩
    obtain ⟨s, t, hst⟩ := hpart1 e he
    refine ⟨(1 : F) * (s : F)⁻¹ * a, ?_⟩
    rw [hst x, ha, hframe, ← xHom_ofAdd, conjAut_diagUnits_xHom, xHom_ofAdd, Units.val_one]
  let T : Subgroup G :=
    { carrier := {y | ∃ hy : y ∈ L, inR ⟨y, hy⟩ ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, hR₁, k₁, hk₁⟩ ⟨h₂, hR₂, k₂, hk₂⟩
        refine ⟨L.mul_mem h₁ h₂, hmulR ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ hR₁ hR₂, k₁ + k₂, ?_⟩
        have hc : Commute y₁ y₂ := congrArg Subtype.val (hcommR ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ hR₁ hR₂)
        rw [hc.mul_pow, pow_add, pow_mul, hk₁, one_pow, one_mul, mul_comm (2 ^ k₁), pow_mul,
          hk₂, one_pow]
      one_mem' := ⟨L.one_mem, honeR, 0, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, hR, k, hk⟩
        exact ⟨L.inv_mem hy, hinvR ⟨y, hy⟩ hR, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hTL : T ≤ L := fun y hy => hy.1
  have hT2 : IsPGroup 2 T := by
    rintro ⟨y, hy, -, k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro x ⟨hx, hRx, -⟩ y ⟨hy, hRy, -⟩
    exact congrArg Subtype.val (hcommR ⟨x, hx⟩ ⟨y, hy⟩ hRx hRy)
  have hET : E ≤ Subgroup.normalizer (T : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun y ⟨hy, hR, k, hk⟩ => ?_
    have hyN : e * y * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEL he) y).mp hy
    refine ⟨hyN, ?_, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    exact hconjR e he ⟨y, hy⟩ hR
  have hne : ⁅T, E⁆ ≠ ⊥ := by
    obtain ⟨e₀, he₀, h₀⟩ := hpart2
    obtain ⟨x₀, hx₀⟩ := hΨ (cg (proj 3 F (xSL 1)))
    obtain ⟨b, m, hm2, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 2
      (by norm_num)
    have hmodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)
    set y₀ : ↥L := x₀ ^ m with hy₀
    have hroot2 : ∀ w : projectiveSL 3 F, w * w = 1 → w ^ m = w := by
      intro w hw
      obtain ⟨j, rfl⟩ := hmodd
      rw [pow_succ, pow_mul, sq, hw, one_pow, one_mul]
    have hΨy₀ : Ψ y₀ = cg (proj 3 F (xSL 1)) := by
      rw [hy₀, map_pow, hx₀]
      exact hroot2 _ (by rw [← map_mul, ← map_mul, xSL_mul_self, map_one, map_one])
    have hy₀T : (y₀ : G) ∈ T := ⟨y₀.2, ⟨1, hΨy₀⟩, b, by
      rw [← Subgroup.coe_pow, hy₀, ← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one,
        Subgroup.coe_one]⟩
    intro hbot
    have hmem : ⁅(y₀ : G), e₀⁆ ∈ ⁅T, E⁆ := Subgroup.commutator_mem_commutator hy₀T he₀
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have hfix : L.normalizerMonoidHom ⟨e₀, hEL he₀⟩ y₀ = y₀ := by
      apply Subtype.ext
      change e₀ * (y₀ : G) * e₀⁻¹ = y₀
      rw [← hmem, mul_inv_cancel_right]
    have h1 := h₀ y₀
    rw [hfix, hΨy₀, hframe, ← xHom_ofAdd, conjAut_diagUnits_xHom] at h1
    have h2 := Multiplicative.ofAdd.injective (Hering214.xHom_injective (cg.injective h1))
    simp only [Units.val_one, one_mul, mul_one] at h2
    apply hτ1
    exact Units.ext (by rw [Units.val_one]; exact inv_eq_one.mp h2.symm)
  obtain ⟨V, hV, hVT⟩ := exists_fourGroupsMinus_le_of_comm hE hT2 hTc hET hne
  exact ⟨V, hV, hVT.trans hTL⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
