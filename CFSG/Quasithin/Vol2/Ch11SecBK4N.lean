module

public import CFSG.Quasithin.Vol2.Ch11SecBK4M
public import CFSG.Quasithin.Vol2.Ch11SecBK4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.Quasithin.Vol2.KGNat (spJ)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem exists_similitude_conjV [IsMulCommutative ↥V] {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (hT : ∀ w, f (SecA.conjV V x hxV w) = TL (f w)) :
    ∃ c : K, ∀ u v, Matrix.toBilin' (spJ K) (TL u) (TL v) = c * Matrix.toBilin' (spJ K) u v := by
  refine KGNat.exists_similitude TL fun γ => ?_
  obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, G2Q8.conjV_mul_conjV_inv_mem hxL hxV (π γ).2⟩
  refine ⟨γ', fun z => ?_⟩
  obtain ⟨w, rfl⟩ := hf.surj z
  have h1 : SecA.conjV V x hxV (((π γ : ↥(autOn L V)) : MulAut ↥V) w) =
      ((π γ' : ↥(autOn L V)) : MulAut ↥V) (SecA.conjV V x hxV w) := by
    have h2 : ((π γ' : ↥(autOn L V)) : MulAut ↥V) =
        SecA.conjV V x hxV * ((π γ : ↥(autOn L V)) : MulAut ↥V) * (SecA.conjV V x hxV)⁻¹ :=
      congrArg Subtype.val hγ'
    rw [h2, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have e1 := hf.act γ w
  have e2 := hf.act γ' (SecA.conjV V x hxV w)
  have h3 : TL ((KGNat.linModelNat (StatedSp 2 K)).lin γ (f w)) =
      (KGNat.linModelNat (StatedSp 2 K)).lin γ' (TL (f w)) :=
    calc TL ((KGNat.linModelNat (StatedSp 2 K)).lin γ (f w))
        = TL (f (((π γ : ↥(autOn L V)) : MulAut ↥V) w)) := congrArg _ e1.symm
      _ = f (SecA.conjV V x hxV (((π γ : ↥(autOn L V)) : MulAut ↥V) w)) := (hT _).symm
      _ = f (((π γ' : ↥(autOn L V)) : MulAut ↥V) (SecA.conjV V x hxV w)) := congrArg f h1
      _ = (KGNat.linModelNat (StatedSp 2 K)).lin γ' (f (SecA.conjV V x hxV w)) := e2
      _ = (KGNat.linModelNat (StatedSp 2 K)).lin γ' (TL (f w)) := by rw [hT]
  simp only [KGNat.linModelNat_lin] at h3
  exact h3

theorem oddCodim_sp4 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxp : x ^ p ∈ Subgroup.centralizer (V : Set G)) :
    2 * n ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨T, σ, hσ, hT⟩ := exists_semilinear_conjV hf
    (fun T hT => KGNat.commutant_statedSp T hT) (x₀ := KGNat.vec4 (1 : K) 0 0 0)
    (fun h => one_ne_zero (congrFun h (.inl 0))) hxV hxL
  have hTp := iterate_eq_of_pow hf hxV hT hxp
  obtain ⟨y₀, hy₀⟩ : ∃ y, T y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx1 (mem_centralizer_of_sp4 hLV hVL hf hxV hxL fun v => by rw [hT, h])
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (map_zero T)
  have hM := card_fun_four hK
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hbound : Nat.card {z : Fin 2 ⊕ Fin 2 → K // T z = z} ≤ 2 ^ (2 * n) := by
    by_cases hσ1 : ∃ θ, σ θ ≠ θ
    · have h1 := card_fix_cube_of_odd T σ hσ hpodd hTp hy₀0 hσ1
      have h2 : Nat.card {z : Fin 2 ⊕ Fin 2 → K // T z = z} ^ 3 ≤ (2 ^ (2 * n)) ^ 3 := by
        rw [← pow_mul]
        exact h1.trans (hM ▸ Nat.pow_le_pow_right (by norm_num) (by omega))
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
    simp only [not_exists, ne_eq, not_not] at hσ1
    by_contra hgt
    rw [not_le] at hgt
    let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
      { toFun := T
        map_add' := map_add T
        map_smul' := fun c z => by rw [hσ, hσ1]; rfl }
    have hTL : ∀ z, TL z = T z := fun z => rfl
    let C' : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
      { carrier := {y | T y = y}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_add, ha, hb]
        zero_mem' := by simp
        smul_mem' := fun c y hy => by
          simp only [Set.mem_ofPred_eq] at hy ⊢
          rw [hσ, hσ1, hy] }
    have hC' : ∀ y, y ∈ C' ↔ T y = y := fun y => Iff.rfl
    have hcardC' : Nat.card C' = Nat.card {z : Fin 2 ⊕ Fin 2 → K // T z = z} := rfl
    have hC3 : Nat.card K ^ 3 ≤ Nat.card C' := by
      have hfin : Nat.card C' = Nat.card K ^ Module.finrank K C' := Module.natCard_eq_pow_finrank
      have hgt' : Nat.card K ^ 2 < Nat.card C' := by
        rw [hcardC', hK, ← pow_mul, mul_comm]
        exact hgt
      rw [hfin] at hgt' ⊢
      have : 2 < Module.finrank K C' := by
        by_contra hle
        rw [not_lt] at hle
        have := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq) hle
        omega
      exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq) this
    have hsup : ∀ z, ∃ c ∈ C', ∃ t : K, z = c + t • y₀ := by
      have h1 := card_mul_le_of_mem (le_sup_left : C' ≤ C' ⊔ (K ∙ y₀))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)) (by exact hy₀)
      have htop : (C' ⊔ (K ∙ y₀)).toAddSubgroup = ⊤ := by
        refine AddSubgroup.eq_top_of_card_eq _ (le_antisymm (Nat.card_le_card_of_injective
          (fun a => a.1) Subtype.val_injective) ?_)
        have h4 : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 3 * Nat.card K := by
          rw [hM, hK, ← pow_mul, ← pow_add]
          ring_nf
        rw [h4]
        exact (Nat.mul_le_mul_right _ hC3).trans h1
      intro z
      have hz : z ∈ (C' ⊔ (K ∙ y₀)).toAddSubgroup := htop ▸ AddSubgroup.mem_top z
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hd
      exact ⟨c, hc, t, rfl⟩
    obtain ⟨μ, hμ⟩ := exists_similitude_conjV hf hxV hxL TL hT
    have hμ1 : μ = 1 := by
      by_contra hne
      have hiso : ∀ a ∈ C', ∀ b ∈ C', Matrix.toBilin' (spJ K) a b = 0 := by
        intro a ha b hb
        have h1 := hμ a b
        rw [hTL, hTL, (hC' a).mp ha, (hC' b).mp hb] at h1
        have h2 : (μ - 1) * Matrix.toBilin' (spJ K) a b = 0 := by linear_combination -h1
        exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
      let ψ : C' → K := fun a => Matrix.toBilin' (spJ K) a.1 y₀
      have hψ : Function.Injective ψ := by
        rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
        have h1 : ∀ z, Matrix.toBilin' (spJ K) (a - a') z = 0 := by
          intro z
          obtain ⟨c, hc, t, rfl⟩ := hsup z
          rw [LinearMap.map_sub₂, map_add, map_add, map_smul, map_smul, hiso a ha c hc,
            hiso a' ha' c hc]
          have h2 : ψ ⟨a, ha⟩ = ψ ⟨a', ha'⟩ := h
          simp only [ψ] at h2
          rw [h2]
          ring
        exact Subtype.ext (sub_eq_zero.mp (KGNat.toBilin'_spJ_nondegenerate.1 _ h1))
      have h1 := Nat.card_le_card_of_injective ψ hψ
      have h2 : Nat.card K ^ 3 ≤ Nat.card K ^ 1 := by rw [pow_one]; exact hC3.trans h1
      have := (Nat.pow_le_pow_iff_right hq).mp h2
      omega
    set v := T y₀ - y₀ with hv
    have hv0 : v ≠ 0 := sub_ne_zero.mpr hy₀
    have hperp : ∀ c ∈ C', Matrix.toBilin' (spJ K) c v = 0 := by
      intro c hc
      have h1 := hμ c y₀
      rw [hμ1, one_mul, hTL, hTL, (hC' c).mp hc] at h1
      rw [hv, LinearMap.map_sub, h1, sub_self]
    have hvC : v ∈ C' := by
      obtain ⟨c₁, hc₁, t₁, ht₁⟩ := hsup v
      by_cases ht : t₁ = 0
      · rw [ht, zero_smul, add_zero] at ht₁
        rw [ht₁]
        exact hc₁
      exfalso
      apply hv0
      refine KGNat.toBilin'_spJ_nondegenerate.1 v fun z => ?_
      obtain ⟨c, hc, t, rfl⟩ := hsup z
      have hy : y₀ = t₁⁻¹ • (v - c₁) := by
        rw [ht₁, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [map_add, map_smul, K7.bil_comm, hperp c hc, hy, map_smul, map_sub, K7.bil_self,
        K7.bil_comm, hperp c₁ hc₁]
      ring
    have hTT : ∀ z, T (T z) = z := by
      intro z
      obtain ⟨c, hc, t, rfl⟩ := hsup z
      have hTv : T v = v := (hC' v).mp hvC
      have hTy : T y₀ = y₀ + v := by rw [hv]; abel
      have hTz : T (c + t • y₀) = c + t • (y₀ + v) := by
        rw [map_add, hσ, hσ1, (hC' c).mp hc, hTy]
      have hT2 : T (c + t • (y₀ + v)) = c + t • y₀ := by
        rw [map_add, hσ, hσ1, (hC' c).mp hc, map_add, hTy, hTv, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
      rw [hTz, hT2]
    exact hy₀ (eq_id_of_iterate_two T hpodd hTp hTT y₀)
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T (f w) = f w :=
    fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]
  have h3 := le_rkIdx_add hV hf hC hM hbound
  omega

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
