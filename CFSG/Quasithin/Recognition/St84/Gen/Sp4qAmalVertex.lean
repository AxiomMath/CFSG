module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalCoord
public import CFSG.Quasithin.Background.F1Hyp

import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalModule
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalCoord
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalLocal
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.ClassicalGroups CFSG.QuasithinUnique
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private noncomputable def conjEnd (L : Subgroup G) (p : ℕ) :
    ↥L →* AddMonoid.End (Additive ↥(pCoreOf p L)) where
  toFun x :=
    { toFun := fun v => Additive.ofMul
        ⟨x * v.toMul * x⁻¹, PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩
      map_zero' := by
        rw [ofMul_eq_zero]
        apply Subtype.ext
        show (x : G) * (1 : G) * (x : G)⁻¹ = 1
        group
      map_add' := fun v w => by
        apply Additive.ofMul.injective
        apply Subtype.ext
        show (x : G) * ((v + w).toMul : G) * (x : G)⁻¹ =
          ((x : G) * (v.toMul : G) * (x : G)⁻¹) * ((x : G) * (w.toMul : G) * (x : G)⁻¹)
        rw [toMul_add]
        simp only [Subgroup.coe_mul]
        group }
  map_one' := by
    ext v
    show (1 : G) * (v.toMul : G) * (1 : G)⁻¹ = (v.toMul : G)
    group
  map_mul' := fun x y => by
    ext v
    show ((x * y : ↥L) : G) * (v.toMul : G) * (((x * y : ↥L) : G))⁻¹ =
      (x : G) * ((y : G) * (v.toMul : G) * (y : G)⁻¹) * (x : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

private theorem conjEnd_apply (L : Subgroup G) (p : ℕ) (x : ↥L) (u : ↥(pCoreOf p L)) :
    conjEnd L p x (Additive.ofMul u) =
      Additive.ofMul ⟨x * u * x⁻¹, PCoreSection.conj_mem_pCoreOf x.2 u.2⟩ := rfl

section

variable {L S : Subgroup G} {f : ℕ}

private theorem exists_conjAction
    (hQ : IsElemAbelian 2 (pCoreOf 2 L))
    (α : ↥L →* SL(2, GaloisField 2 f)) (hαsurj : Function.Surjective α)
    (hαker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L) :
    ∃ ρ : SL(2, GaloisField 2 f) →* AddMonoid.End (Additive ↥(pCoreOf 2 L)),
      ∀ (x : ↥L) (v : Additive ↥(pCoreOf 2 L)),
        ρ (α x) v = Additive.ofMul ⟨x * v.toMul * x⁻¹,
          PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩ := by
  classical
  let F := GaloisField 2 f
  let Q := pCoreOf 2 L
  let V := Additive ↥Q
  haveI hQcomm : IsMulCommutative ↥Q := hQ.1
  let φ : ↥L →* AddMonoid.End V := conjEnd L 2
  have hker_le : α.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxQ : (x : G) ∈ Q := (hαker x).mp hx
    refine AddMonoidHom.ext (fun v => ?_)
    rw [show v = Additive.ofMul v.toMul from (ofMul_toMul v).symm]
    show (conjEnd L 2 x) (Additive.ofMul v.toMul) = Additive.ofMul v.toMul
    apply Additive.ofMul.injective
    apply Subtype.ext
    have hcomm : (⟨x, hxQ⟩ : ↥Q) * v.toMul = v.toMul * ⟨x, hxQ⟩ :=
      hQcomm.is_comm.comm _ _
    have hcommG : (x : G) * (v.toMul : G) = (v.toMul : G) * (x : G) :=
      congrArg Subtype.val hcomm
    calc (x : G) * (v.toMul : G) * (x : G)⁻¹ = ((v.toMul : G) * (x : G)) * (x : G)⁻¹ := by
          rw [hcommG]
      _ = (v.toMul : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  let ρ : SL(2, F) →* AddMonoid.End V :=
    (QuotientGroup.lift α.ker φ hker_le).comp
      (QuotientGroup.quotientKerEquivOfSurjective α hαsurj).symm.toMonoidHom
  have hρ : ∀ (x : ↥L) (v : V), ρ (α x) v = φ x v := by
    intro x v
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective α hαsurj) (QuotientGroup.mk x) =
        α x := rfl
    have h2 : (QuotientGroup.quotientKerEquivOfSurjective α hαsurj).symm (α x) =
        QuotientGroup.mk x := by
      rw [← h1, MulEquiv.symm_apply_apply]
    change (QuotientGroup.lift α.ker φ hker_le) ((QuotientGroup.quotientKerEquivOfSurjective
      α hαsurj).symm (α x)) v = φ x v
    rw [h2]
    rfl
  have hρ' : ∀ (x : ↥L) (v : V), ρ (α x) v = Additive.ofMul ⟨x * v.toMul * x⁻¹,
      PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩ := by
    intro x v
    rw [hρ, show v = Additive.ofMul v.toMul from (ofMul_toMul v).symm]
    exact conjEnd_apply L 2 x v.toMul
  exact ⟨ρ, hρ'⟩

private theorem exists_lin2_action
    (hQ : IsElemAbelian 2 (pCoreOf 2 L))
    (α : ↥L →* SL(2, GaloisField 2 f)) (hαsurj : Function.Surjective α)
    (hαker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L)
    (β : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 f))
    (hβsurj : Function.Surjective β)
    (hβker : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβeq : ∀ (x : ↥L) (u v : ↥(blockU L)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) =
        (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec
          (Multiplicative.toAdd (β u)))
    (hU : blockU L = pCoreOf 2 L) :
    ∃ (ρ : SL(2, GaloisField 2 f) →* AddMonoid.End (Additive ↥(pCoreOf 2 L)))
      (β' : Additive ↥(pCoreOf 2 L) →+ (Fin 2 → GaloisField 2 f)),
      Function.Surjective β' ∧
      (∀ (k : SL(2, GaloisField 2 f)) (v : Additive ↥(pCoreOf 2 L)),
        β' (ρ k v) =
          (k : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec (β' v)) ∧
      (∀ (k : SL(2, GaloisField 2 f)) (v : Additive ↥(pCoreOf 2 L)),
        β' v = 0 → ρ k v = v) ∧
      (∀ (x : ↥L) (v : Additive ↥(pCoreOf 2 L)),
        ρ (α x) v = Additive.ofMul ⟨x * v.toMul * x⁻¹,
          PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩) := by
  classical
  let F := GaloisField 2 f
  let Q := pCoreOf 2 L
  let V := Additive ↥Q
  obtain ⟨ρ, hρ⟩ := exists_conjAction hQ α hαsurj hαker
  let eU : ↥Q ≃* ↥(blockU L) := (MulEquiv.subgroupCongr hU).symm
  let βQ : ↥Q →* Multiplicative (Fin 2 → F) := β.comp eU.toMonoidHom
  let β' : V →+ (Fin 2 → F) := βQ.toAdditiveLeft
  have hβ'surj : Function.Surjective β' := by
    intro y
    obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd y)
    refine ⟨Additive.ofMul (eU.symm u), ?_⟩
    change Multiplicative.toAdd (β (eU (eU.symm u))) = y
    rw [MulEquiv.apply_symm_apply, hu, toAdd_ofAdd]
  have hβ'ρ : ∀ (k : SL(2, F)) (v : V),
      β' (ρ k v) = (k : Matrix (Fin 2) (Fin 2) F).mulVec (β' v) := by
    intro k v
    obtain ⟨x, rfl⟩ := hαsurj k
    rw [hρ x]
    have hvu : ((eU ⟨x * v.toMul * x⁻¹,
        PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩ : ↥(blockU L)) : G) =
        (x : G) * ((eU v.toMul : ↥(blockU L)) : G) * (x : G)⁻¹ := by
      rw [MulEquiv.subgroupCongr_symm_apply, MulEquiv.subgroupCongr_symm_apply]
      rfl
    have h := hβeq x (eU v.toMul) (eU ⟨x * v.toMul * x⁻¹,
      PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩) hvu
    change Multiplicative.toAdd (β (eU ⟨x * v.toMul * x⁻¹,
      PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩)) =
      (α x : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β (eU v.toMul)))
    exact h
  have hβ'ker : ∀ (k : SL(2, F)) (v : V), β' v = 0 → ρ k v = v := by
    intro k v hv
    obtain ⟨x, rfl⟩ := hαsurj k
    rw [hρ x]
    rw [show v = Additive.ofMul v.toMul from (ofMul_toMul v).symm]
    have hzero : β (eU v.toMul) = 1 := by
      have h := hv
      simp only [β', MonoidHom.coe_toAdditiveLeft, Function.comp_apply, βQ,
        MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe] at h
      exact Multiplicative.toAdd.injective h
    have hmem : eU v.toMul ∈ (blockZ L).subgroupOf (blockU L) := by
      rw [← hβker]
      exact MonoidHom.mem_ker.mpr hzero
    have hcent : ((eU v.toMul : ↥(blockU L)) : G) ∈
        Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hmem).2
    have hcomm : (x : G) * ((eU v.toMul : ↥(blockU L)) : G) =
        ((eU v.toMul : ↥(blockU L)) : G) * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp hcent) (x : G) x.2
    apply Additive.ofMul.injective
    apply Subtype.ext
    calc (x : G) * (v.toMul : G) * (x : G)⁻¹
        = (x : G) * ((eU v.toMul : ↥(blockU L)) : G) * (x : G)⁻¹ := by
          rw [MulEquiv.subgroupCongr_symm_apply]
      _ = ((eU v.toMul : ↥(blockU L)) : G) := by
          rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      _ = (v.toMul : G) := by rw [MulEquiv.subgroupCongr_symm_apply]
  exact ⟨ρ, β', hβ'surj, hβ'ρ, hβ'ker, hρ⟩

private theorem eq_top_of_fixed_commutators
    (hU : blockU L = pCoreOf 2 L)
    (α : ↥L →* SL(2, GaloisField 2 f))
    (ρ : SL(2, GaloisField 2 f) →* AddMonoid.End (Additive ↥(pCoreOf 2 L)))
    (hρ : ∀ (x : ↥L) (v : Additive ↥(pCoreOf 2 L)),
      ρ (α x) v = Additive.ofMul ⟨x * v.toMul * x⁻¹,
        PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩) :
    ∀ W : AddSubgroup (Additive ↥(pCoreOf 2 L)),
      (∀ (k : SL(2, GaloisField 2 f)) (v : Additive ↥(pCoreOf 2 L)),
        ρ k v - v ∈ W) → W = ⊤ := by
  intro W hW
  let Q := pCoreOf 2 L
  let W' : Subgroup ↥Q :=
    { carrier := {q | Additive.ofMul q ∈ W}
      one_mem' := by
        show Additive.ofMul (1 : ↥Q) ∈ W
        rw [ofMul_one]
        exact W.zero_mem
      mul_mem' := fun {a b} ha hb => by
        show Additive.ofMul (a * b) ∈ W
        rw [ofMul_mul]
        exact W.add_mem ha hb
      inv_mem' := fun {a} ha => by
        show Additive.ofMul a⁻¹ ∈ W
        rw [ofMul_inv]
        exact W.neg_mem ha }
  have hW'g : ⁅L, Q⁆ ≤ W'.map Q.subtype := by
    rw [Subgroup.commutator_le]
    intro b hb a ha
    have hmemW : Additive.ofMul (⟨b * a * b⁻¹ * a⁻¹,
        (Q.mul_mem (PCoreSection.conj_mem_pCoreOf hb ha) (Q.inv_mem ha))⟩ : ↥Q) ∈ W := by
      have hba := hW (α (⟨b, hb⟩ : ↥L)) (Additive.ofMul ⟨a, ha⟩)
      rw [hρ] at hba
      have hsub : Additive.ofMul (⟨b * a * b⁻¹,
          PCoreSection.conj_mem_pCoreOf hb ha⟩ : ↥Q) -
          Additive.ofMul (⟨a, ha⟩ : ↥Q) =
          Additive.ofMul (⟨b * a * b⁻¹ * a⁻¹,
            (Q.mul_mem (PCoreSection.conj_mem_pCoreOf hb ha) (Q.inv_mem ha))⟩ : ↥Q) := by
        rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      have hba' : Additive.ofMul (⟨b * a * b⁻¹,
          PCoreSection.conj_mem_pCoreOf hb ha⟩ : ↥Q) -
          Additive.ofMul (⟨a, ha⟩ : ↥Q) ∈ W := hba
      rw [hsub] at hba'
      exact hba'
    exact Subgroup.mem_map.mpr ⟨⟨b * a * b⁻¹ * a⁻¹,
      Q.mul_mem (PCoreSection.conj_mem_pCoreOf hb ha) (Q.inv_mem ha)⟩, hmemW, rfl⟩
  have hQle : Q ≤ W'.map Q.subtype := by
    have hQeq : ⁅Q, L⁆ = Q := by simpa [blockU, blockQ] using hU
    have h := hW'g
    rw [← Subgroup.commutator_comm] at h
    rw [hQeq] at h
    exact h
  rw [eq_top_iff]
  intro v
  have hv : Additive.ofMul v.toMul ∈ W := by
    have hQ := hQle v.toMul.2
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hQ
    have hqv : Additive.ofMul q = v := by
      rw [show v = Additive.ofMul v.toMul from (ofMul_toMul v).symm]
      exact congrArg Additive.ofMul (Subtype.ext hqe)
    rw [← hqv]
    exact hq
  simpa using hv

private theorem card_fixed_of_centralizer (hf : 2 ≤ f)
    (hC : 2 ^ (2 * f) ≤
      Nat.card ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (S : Set G)))
    (α : ↥L →* SL(2, GaloisField 2 f)) (hαsurj : Function.Surjective α)
    (ρ : SL(2, GaloisField 2 f) →* AddMonoid.End (Additive ↥(pCoreOf 2 L)))
    (hρ : ∀ (x : ↥L) (v : Additive ↥(pCoreOf 2 L)),
      ρ (α x) v = Additive.ofMul ⟨x * v.toMul * x⁻¹,
        PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ ∃ t : GaloisField 2 f,
      (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1]) :
    Nat.card (GaloisField 2 f) ^ 2 ≤
      Nat.card {v : Additive ↥(pCoreOf 2 L) // ∀ k : SL(2, GaloisField 2 f),
        (∃ t : GaloisField 2 f,
          (k : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1]) →
          ρ k v = v} := by
  classical
  let F := GaloisField 2 f
  let Q := pCoreOf 2 L
  let V := Additive ↥Q
  have hf0 : f ≠ 0 := by omega
  have hFcard : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  have hcardF : Nat.card F ^ 2 = 2 ^ (2 * f) := by
    rw [hFcard, ← pow_mul]
    congr 1
    omega
  let upperFixed : Type := {v : V // ∀ k : SL(2, F),
    (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) → ρ k v = v}
  have hC' : Nat.card F ^ 2 ≤ Nat.card upperFixed := by
    rw [hcardF]
    let emb : ↥(Q ⊓ Subgroup.centralizer (S : Set G)) → upperFixed := fun u =>
      ⟨Additive.ofMul ⟨u.1, u.2.1⟩, by
        intro k hk
        obtain ⟨t, ht⟩ := hk
        obtain ⟨x, hx⟩ := hαsurj k
        have hxS : (x : G) ∈ S := (hmem x).mpr ⟨t, by rw [hx]; exact ht⟩
        have hcu := (Subgroup.mem_centralizer_iff.mp u.2.2) (x : G) hxS
        rw [← hx, hρ]
        apply Additive.ofMul.injective
        apply Subtype.ext
        calc (x : G) * (u.1 : G) * (x : G)⁻¹ = ((u.1 : G) * (x : G)) * (x : G)⁻¹ := by
              rw [hcu]
          _ = (u.1 : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]⟩
    have hinj : Function.Injective emb := by
      intro u w huv
      have h : u.1 = w.1 := by
        simpa [emb] using congrArg (fun z : upperFixed => Additive.toMul z.1) huv
      exact Subtype.ext h
    exact hC.trans (Nat.card_le_card_of_injective emb hinj)
  exact hC'

private theorem exists_o3Coord_of_lin2 (hf : 2 ≤ f)
    (hQ : IsElemAbelian 2 (pCoreOf 2 L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (3 * f))
    (hC : 2 ^ (2 * f) ≤
      Nat.card ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (S : Set G)))
    (α : ↥L →* SL(2, GaloisField 2 f)) (hαsurj : Function.Surjective α)
    (hαker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L)
    (β : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 f))
    (hβsurj : Function.Surjective β)
    (hβker : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβeq : ∀ (x : ↥L) (u v : ↥(blockU L)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) =
        (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec
          (Multiplicative.toAdd (β u)))
    (hU : blockU L = pCoreOf 2 L)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ ∃ t : GaloisField 2 f,
      (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1]) :
    ∃ γ : Additive ↥(pCoreOf 2 L) ≃+ (Fin 3 → GaloisField 2 f),
      ∀ (x : ↥L) (v : Additive ↥(pCoreOf 2 L)),
        γ (Additive.ofMul ⟨x * v.toMul * x⁻¹,
            PCoreSection.conj_mem_pCoreOf x.2 v.toMul.2⟩) =
          (sp4RadMat (α x)).mulVec (γ v) := by
  classical
  let F := GaloisField 2 f
  let Q := pCoreOf 2 L
  let V := Additive ↥Q
  have hf0 : f ≠ 0 := by omega
  have hFcard : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ρ, β', hβ'surj, hβ'ρ, hβ'ker, hρ⟩ :=
    exists_lin2_action hQ α hαsurj hαker β hβsurj hβker hβeq hU
  have hgen := eq_top_of_fixed_commutators hU α ρ hρ
  have hC' := card_fixed_of_centralizer hf hC α hαsurj ρ hρ hmem
  have hcardV : Nat.card V = Nat.card F ^ 3 := by
    rw [show Nat.card V = Nat.card ↥Q from Nat.card_congr Additive.toMul, hcard, hFcard,
      ← pow_mul]
    congr 1
    omega
  have hV2 : ∀ v : V, v + v = 0 := by
    intro v
    have hv : ((v.toMul : ↥Q) : G) ^ 2 = 1 := hQ.2 (v.toMul : G) v.toMul.2
    rw [pow_two] at hv
    show Additive.ofMul v.toMul + Additive.ofMul v.toMul = 0
    rw [← ofMul_mul]
    have hv' : v.toMul * v.toMul = 1 := by
      apply Subtype.ext
      simpa using hv
    rw [hv', ofMul_one]
  haveI hQcomm : IsMulCommutative ↥Q := hQ.1
  haveI : Finite V := inferInstanceAs (Finite (Additive ↥Q))
  obtain ⟨γ, hγ, -⟩ := exists_o3Coord (F := F) hF4 hV2 hcardV ρ β' hβ'surj hβ'ρ hβ'ker hgen hC'
  refine ⟨γ, ?_⟩
  intro x v
  have h := hγ (α x) (Additive.ofMul v)
  rw [hρ x (Additive.ofMul v)] at h
  exact h

theorem exists_sp4VertexCoord (hf : 2 ≤ f) (hS : IsSylowTwoOf S L)
    (hL : IsLin2Type L f) (hU : blockU L = pCoreOf 2 L)
    (hQ : IsElemAbelian 2 (pCoreOf 2 L))
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (3 * f))
    (hC : 2 ^ (2 * f) ≤
      Nat.card ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (S : Set G))) :
    Nonempty (Sp4VertexCoord L S (GaloisField 2 f)) := by
  classical
  obtain ⟨α, β, hαsurj, hαker, hβsurj, hβker, hβeq, hmem⟩ :=
    exists_normalized_lin2 (by omega) hS hL
  obtain ⟨γ, hγ⟩ := exists_o3Coord_of_lin2 hf hQ hcard hC α hαsurj hαker β hβsurj hβker
    hβeq hU hmem
  refine ⟨⟨α, γ.toMultiplicativeRight, hαsurj, hαker, ?_, hmem⟩⟩
  intro x u v hv
  have hvu : Additive.ofMul ⟨x * u * x⁻¹, PCoreSection.conj_mem_pCoreOf x.2 u.2⟩ =
      Additive.ofMul v := congrArg Additive.ofMul (Subtype.ext hv.symm)
  change γ (Additive.ofMul v) = (sp4RadMat (α x)).mulVec (γ (Additive.ofMul u))
  rw [← hvu]
  exact hγ x (Additive.ofMul u)

end

section

variable {L1 L2 S : Subgroup G} {f : ℕ}

theorem Sp4qLocalData.exists_coord_left (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    Nonempty (Sp4VertexCoord L1 S (GaloisField 2 f)) :=
  exists_sp4VertexCoord hf (hD.isSylowTwoOf_left hH) hD.lin_left hD.blockU_left hD.elem_left
    hD.card_left (hD.card_inf_centralizer_left hH).ge

theorem Sp4qLocalData.exists_coord_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    Nonempty (Sp4VertexCoord L2 S (GaloisField 2 f)) :=
  exists_sp4VertexCoord hf (hD.isSylowTwoOf_right hH) hD.lin_right hD.blockU_right hD.elem_right
    hD.card_right (hD.card_inf_centralizer_right hH).ge

end

end CFSG.Quasithin.F112R.St84
