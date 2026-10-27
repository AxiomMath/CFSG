module

public import CFSG.Quasithin.Vol2.Ch11SecBK10T
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.Sz

open Matrix CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_apply_of_lt (u v : K) {i j : Fin 4} (hij : i < j) : suzukiS a u v i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [suzukiS] at hij ⊢

theorem suzukiS_mul_suzukiD (u v : K) (l : Kˣ) :
    (suzukiS a u v * suzukiD a l).BlockTriangular OrderDual.toDual ∧
      ∀ i, (suzukiS a u v * suzukiD a l) i i = suzukiD a l i i := by
  rw [suzukiD_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [mul_diagonal, suzukiS_apply_of_lt u v (OrderDual.toDual_lt_toDual.mp hij), zero_mul]
  · rw [mul_diagonal, diagonal_apply_eq]
    fin_cases i <;> simp [suzukiS]

variable [Finite K]

theorem eq_one_of_map_conj (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K} {l : Kˣ}
    (hl : ∀ x : Kˣ, x ∈ Subgroup.zpowers l) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M.BlockTriangular OrderDual.toDual) (hMd : ∀ i, M i i = suzukiD a l i i)
    (g : GL (Fin 4) K)
    (h : M.map σ = (g : Matrix (Fin 4) (Fin 4) K) * M * ((g⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) : σ = 1 := by
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ : Odd (orderOf σ) :=
    Odd.of_dvd_nat (by rw [hcard]; exact odd_two_mul_add_one a) (orderOf_dvd_natCard σ)
  set m₂ : K := (l : K) ^ 2 ^ a with hm₂
  set m₁ : K := (l : K) * m₂ with hm₁
  have hm₂0 : m₂ ≠ 0 := pow_ne_zero _ l.ne_zero
  have hm₁0 : m₁ ≠ 0 := mul_ne_zero l.ne_zero hm₂0
  have hd : ∀ i, M i i = ![m₁, m₂, m₂⁻¹, m₁⁻¹] i := fun i => by
    rw [hMd, suzukiD_eq, diagonal_apply_eq]
  have hmem : ∀ i, σ (M i i) = m₁ ∨ σ (M i i) = m₂ ∨ σ (M i i) = m₂⁻¹ ∨ σ (M i i) = m₁⁻¹ := by
    intro i
    obtain ⟨j, hj⟩ := exists_diag_eq_of_map_eq_conj hM σ g h i
    rw [hj, hd j]
    fin_cases j <;> simp
  have h1 := hmem 0
  have h2 := hmem 1
  rw [hd 0] at h1
  rw [hd 1] at h2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  obtain ⟨e1, e2⟩ := eq_of_mem_four hσ hm₁0 hm₂0 h1 h2
  refine eq_one_of_fix_generator hl ?_
  have hl' : (l : K) = m₁ * m₂⁻¹ := by
    rw [hm₁, mul_assoc, mul_inv_cancel₀ hm₂0, mul_one]
  rw [hl', map_mul, map_inv₀, e1, e2]


theorem exists_conj_mul_szFieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (suzukiGroup a K)) :
    ∃ (g : suzukiGroup a K) (σ : K ≃+* K), α = MulAut.conj g * szFieldAut a K σ := by
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  obtain ⟨-, hout⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  set ψ : (K ≃+* K) →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' (inner (suzukiGroup a K))).comp (szFieldAut a K) with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hσ
    obtain ⟨g, hg⟩ := hσ
    have h1 := congrArg (fun φ : MulAut (suzukiGroup a K) =>
      (((φ (suzukiDElt a K l) : suzukiGroup a K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) hg
    simp only [MulAut.conj_apply, coe_szFieldAut, coe_suzukiDElt, Subgroup.coe_mul,
      Subgroup.coe_inv, Units.val_mul] at h1
    rw [Subgroup.mem_bot]
    exact eq_one_of_map_conj hK hl (by rw [suzukiD]; exact blockTriangular_diagonal _)
      (fun _ => rfl) (g : GL (Fin 4) K)
      h1.symm
  have hbij : Function.Bijective ψ :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; exact Nat.le_of_dvd (by omega) hout)
  obtain ⟨σ, hσ⟩ := hbij.2 (QuotientGroup.mk' _ α)
  rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem] at hσ
  obtain ⟨g, hg⟩ := hσ
  refine ⟨g⁻¹, σ, ?_⟩
  rw [map_inv, hg, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]

theorem torusRigidAt_sz (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TorusRigidAt (suzukiGroup a K) (suzukiU a K) := by
  classical
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  obtain ⟨-, hout⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
  have hodd : Odd (Nat.card (Outer (suzukiGroup a K))) :=
    Odd.of_dvd_nat (odd_two_mul_add_one a) hout
  obtain ⟨P, -, hN, -⟩ := Suzuki_model_opposite_root_interface ha hK
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  set y := suzukiDElt a K l with hy
  have hyB : y ∈ suzukiB a K := suzukiT_le_suzukiB a K (suzukiDElt_mem_suzukiT a K l)
  intro Sh hSh2 _ hSs
  refine ⟨y, fun s hs => ?_, ?_, fun y' hy' _ β hβ hβy' => ?_⟩
  ·
    obtain ⟨k, hk⟩ := hSh2 ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨b, hb⟩ := mem_inner_of_two_pow hodd hk'
    have hbN : b ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      rw [← MulAut.conj_apply, hb]
      exact hSs s hs w
    rw [hN] at hbN
    rw [← hb, MulAut.conj_apply]
    have e : y * (b * y * b⁻¹)⁻¹ = ⁅y, b⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact commutatorElement_mem_suzukiU hK hyB hbN
  ·
    have h1 : orderOf y ∣ Nat.card (suzukiT a K) := by
      have := orderOf_dvd_natCard (⟨y, suzukiDElt_mem_suzukiT a K l⟩ : suzukiT a K)
      rwa [Subgroup.orderOf_mk] at this
    rw [(suzuki_borel_structure hK).2.2.1] at h1
    refine Odd.of_dvd_nat ?_ h1
    have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have h3 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).1 hy'
  have hy'eq : y' = suzukiSElt a K u v * y := by rw [huv, inv_mul_cancel_right]
  obtain ⟨g, σ, rfl⟩ := exists_conj_mul_szFieldAut ha hK β
  have hM : ((y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v * suzukiD a l := by
    rw [hy'eq]
    rfl
  have e1 : szFieldAut a K σ y' = g⁻¹ * y' * g := by
    have h1 := hβy'
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    calc szFieldAut a K σ y' = g⁻¹ * (g * szFieldAut a K σ y' * g⁻¹) * g := by group
      _ = g⁻¹ * y' * g := by rw [h1]
  have e2 := congrArg (fun z : suzukiGroup a K =>
    ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) e1
  simp only [coe_szFieldAut, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e2
  have hfix : ((y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ =
      (((g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((((g : GL (Fin 4) K)⁻¹)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [e2, inv_inv]
  obtain ⟨hT, hD⟩ := suzukiS_mul_suzukiD (a := a) u v l
  rw [← hM] at hT hD
  have hσ1 := eq_one_of_map_conj hK hl hT hD _ hfix
  rw [hσ1, map_one, mul_one] at hβ1 hβr ⊢
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ ⟨g, rfl⟩

theorem torusRigid_sz (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TorusRigid (suzukiGroup a K) := by
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPU, -⟩ := Suzuki_model_opposite_root_interface ha hK
  have hS : QuasithinUnique.IsSylowTwoOf (suzukiU a K) ⊤ := by
    rw [← hPU]
    refine ⟨le_top, P.isPGroup', ?_⟩
    change ¬ 2 ∣ (P : Subgroup (suzukiGroup a K)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  exact TorusRigid.of_at hS (torusRigidAt_sz ha hK)

end BK10.Sz

end CFSG.Quasithin.Vol2.Ch11.SecD
