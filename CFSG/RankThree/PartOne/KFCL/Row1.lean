module

public import CFSG.RankThree.PartOne.KFCL.L4Root
public import CFSG.RankThree.PartOne.KFCL.L4Frame
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.RankThree.PartOne.KFCL

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.PartOne
open scoped MatrixGroups

theorem rootModelRow_one : RootModelRow 1 := by
  intro G _ _ p A c L E h15 hF hF13 hout hEI
  have h := h15.h12
  obtain ⟨f, hf1, hpf, ⟨φ⟩, -, hEA, -⟩ := hout
  have hp : p.Prime := h.prime
  have hp3 : 3 < p := h.three_lt
  have : NeZero f := ⟨by omega⟩
  let K := GaloisField 2 f
  have hcardK : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : p ∣ Nat.card K - 1 := by rw [hcardK]; exact hpf
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ p := by
    have h1 : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.2 (by simpa [hx] using IsPrimitiveRoot.orderOf x)⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ2 : ζ ≠ ζ⁻¹ := by
    intro h2
    have : ζ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [h2]; exact inv_mul_cancel₀ hζ0
    have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 this)
    omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hcardK]
    have hpos : 0 < 2 ^ f - 1 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
      omega
    have := Nat.le_of_dvd hpos hpf
    omega
  let ψ₀ : ↥(lieGenerated p E) ≃* SL(4, K) :=
    φ.trans ((S15K.projSLEquivProjectiveSL 4 K).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL K))
  let E' : Subgroup ↥(lieGenerated p E) := E.subgroupOf (lieGenerated p E)
  let E₀ : Subgroup SL(4, K) := E'.map ψ₀.toMonoidHom
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
    simpa using this
  have hpowE : ∀ a ∈ E, a ^ p = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show ψ₀ x * ψ₀ y = ψ₀ y * ψ₀ x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommE _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
  have hpow : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show ψ₀ x ^ p = 1
    have : x ^ p = 1 := Subtype.ext (by simpa using hpowE _ (Subgroup.mem_subgroupOf.1 hx))
    rw [← map_pow, this, map_one]
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcard : Nat.card E₀ = p ^ 3 := by
    rw [Subgroup.card_map_of_injective ψ₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv]
    exact hEcard
  obtain ⟨Af, hAf⟩ := L4.exists_frame hp hζ E₀ hcomm hpow hcard
  let ψ : ↥(lieGenerated p E) ≃* SL(4, K) := ψ₀.trans (L4.conjSL Af)
  have hψ : E'.map ψ.toMonoidHom = L4.torus p K := by
    rw [← hAf, Subgroup.map_map]
    rfl
  have hT : (L4.torus p K).map ψ.symm.toMonoidHom = E.subgroupOf (lieGenerated p E) := by
    rw [← hψ, Subgroup.map_map]
    have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  obtain ⟨R0, hR0⟩ := L4.exists_stdRoot (p := p) h4 hζp hζ0 hζ2
  rw [← hT]
  exact ⟨R0.map ψ.symm, Or.inl (hR0.map ψ.symm)⟩

theorem kfCompGenRow_one (hEI : Sec1511.KFEI) (hAt : KFAtRow 1) : KFCompGenRow 1 :=
  kfCompGenRow_of_rootModel (by norm_num) (by norm_num) hEI hAt rootModelRow_one

end CFSG.RankThree.PartOne.KFCL
