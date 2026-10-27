module

public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Groups

variable {Q P : Type*} [Group Q] [Group P]

theorem mem_center_of_comm_mem_center [Group.IsPerfect Q] {x : Q}
    (hx : ∀ y : Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Q) : x ∈ Subgroup.center Q := by
  let f : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hx y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.mp (hx b)
        show x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹)
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e, hb a, mul_inv_cancel_right] }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff]
    have h1 := Abelianization.commutator_subset_ker f
    rwa [Group.IsPerfect.commutator_eq_top] at h1
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : f y = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top y)
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hy
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * x * y := by group
    _ = x * y := by rw [h1]; group

theorem ker_le_center_of_isQuasisimple (hQ : CFSG.IsQuasisimple Q) (φ : Q →* P)
    (hφ : Function.Surjective φ) (hP : Nontrivial P) : φ.ker ≤ Subgroup.center Q := by
  rcases A3.eq_top_or_le_center_of_subnormal hQ (φ.normal_ker.isSubnormal) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hP
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hx : φ x = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
    have hy : φ y = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y)
    exact hab (hx.trans hy.symm)
  · exact h

noncomputable def centerQuotEquiv [Group.IsPerfect Q] (φ : Q →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Q) : Q ⧸ Subgroup.center Q ≃* P ⧸ Subgroup.center P :=
  let ψ : Q →* P ⧸ Subgroup.center P := (QuotientGroup.mk' (Subgroup.center P)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψk : ψ.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      refine mem_center_of_comm_mem_center fun y => hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [← Subgroup.mem_center_iff.mp hx (φ y)]
      group
    · intro hx
      exact Subgroup.map_center_le_center hφ ⟨x, hx, rfl⟩
  (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem le_center_of_isSolvable_of_isQuasisimple (hQ : CFSG.IsQuasisimple Q) {N : Subgroup Q}
    [N.Normal] (hN : Group.IsSolvable ↥N) : N ≤ Subgroup.center Q := by
  rcases A3.eq_top_or_le_center_of_subnormal hQ (Subgroup.Normal.isSubnormal ‹_›) with h | h
  · exfalso
    obtain ⟨hperf, -, a, b, hab⟩ := hQ
    have : Group.IsSolvable Q := by
      rw [h] at hN
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom) Subgroup.topEquiv.surjective
    have hnt : Nontrivial Q := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a 1, Subsingleton.elim b 1]
    exact Group.IsPerfect.not_isSolvable Q this
  · exact h

end Groups

section SL2

theorem card_center_sl2_le {F : Type*} [Field F] [Finite F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ 2 := by
  classical
  have hsc : ∀ A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F),
      (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = r := by
      rw [← hrA]; simp
    rw [h00]
    refine ⟨hrA.symm, ?_⟩
    rw [Fintype.card_fin, pow_two] at hr
    exact hr
  let g : ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) → Bool :=
    fun A => decide (((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1)
  have hg : Function.Injective g := by
    intro A B hAB
    obtain ⟨hA, hA2⟩ := hsc A A.2
    obtain ⟨hB, hB2⟩ := hsc B B.2
    have hAv := mul_self_eq_one_iff.mp hA2
    have hBv := mul_self_eq_one_iff.mp hB2
    have hAB' : ((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ↔
        ((B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      simpa [g] using hAB
    have h00 : ((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      by_cases ha1 : ((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      · rw [ha1, hAB'.mp ha1]
      · have hb1 : ((B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 1 :=
          fun hb => ha1 (hAB'.mpr hb)
        rw [hAv.resolve_left ha1, hBv.resolve_left hb1]
    apply Subtype.ext
    apply Subtype.ext
    rw [hA, hB, h00]
  calc Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ Nat.card Bool :=
        Nat.card_le_card_of_injective g hg
    _ = 2 := by simp

theorem card_mul_card_ker_of_sl2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {S : Type*} [Group S]
    (θ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* S) (hθ : Function.Surjective θ)
    [Nontrivial S] : Nat.card S * Nat.card θ.ker = p * (p ^ 2 - 1) ∧ Nat.card θ.ker ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq := A313.isQuasisimple_sl2 hp hp5
  have hker := ker_le_center_of_isQuasisimple hq θ hθ inferInstance
  refine ⟨?_, (Subgroup.card_le_of_le hker).trans card_center_sl2_le⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv] at h1
  rw [← h1, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    Nat.card_zmod]
  norm_num

theorem prime_eq_seven_of_sl2 {p c N : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2) (hN : N = 168 ∨ N = 360 ∨ N = 2520 ∨ N = 6048)
    (h : N * c = p * (p ^ 2 - 1)) : N = 168 ∧ p = 7 := by
  have hNc : N * c ≤ 12096 := by
    rcases hN with rfl | rfl | rfl | rfl <;> omega
  have hp24 : p ≤ 23 := by
    by_contra hlt
    push Not at hlt
    have h1 : 575 ≤ p ^ 2 - 1 := by
      have : 576 ≤ p ^ 2 := by nlinarith
      omega
    have h2 : 24 * 575 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul (by omega) h1
    omega
  interval_cases p <;> norm_num at hp <;> rcases hN with rfl | rfl | rfl | rfl <;> omega

end SL2

end CFSG.Quasithin.H13.A5
