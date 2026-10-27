module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec3

open scoped MatrixGroups IsMulCommutative commutatorElement

namespace AltSLTwo

@[expose] def v₁ : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def v₂ : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def c₃ : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def negOne : SL(2, ZMod 3) := ⟨!![2, 0; 0, 2], by decide⟩

@[expose] def qi : SL(2, ZMod 3) := ⟨!![0, 2; 1, 0], by decide⟩

@[expose] def qj : SL(2, ZMod 3) := ⟨!![1, 1; 1, 2], by decide⟩

@[expose] def d₁ : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (v₁, 1)

@[expose] def d₂ : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (v₂, 1)

@[expose] def w₃ : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (c₃, 1)

@[expose] def zz : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (1, negOne)

@[expose] def b₁ : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (1, qi)

@[expose] def b₂ : alternatingGroup (Fin 4) × SL(2, ZMod 3) := (1, qj)

theorem d₁_mul_d₁ : d₁ * d₁ = 1 := by decide

theorem d₂_mul_d₂ : d₂ * d₂ = 1 := by decide

theorem d₁_mul_d₂ : d₁ * d₂ = d₂ * d₁ := by decide

theorem d₁_ne_one : d₁ ≠ 1 := by decide

theorem d₁_mul_w₃ : d₁ * w₃ = w₃ * d₂ := by decide

theorem d₂_mul_w₃ : d₂ * w₃ = w₃ * (d₁ * d₂) := by decide

theorem b₁_mul_d₁ : b₁ * d₁ = d₁ * b₁ := by decide

theorem b₁_mul_d₂ : b₁ * d₂ = d₂ * b₁ := by decide

theorem b₂_mul_d₁ : b₂ * d₁ = d₁ * b₂ := by decide

theorem b₂_mul_d₂ : b₂ * d₂ = d₂ * b₂ := by decide

theorem b₁_mul_b₂ : b₁ * b₂ = zz * b₂ * b₁ := by decide

theorem zz_sq : zz ^ 2 = 1 := by decide

theorem zz_ne_one : zz ≠ 1 := by decide

abbrev EightGrp : Type := Multiplicative (ZMod 2 × ZMod 2) × Multiplicative (ZMod 2)

theorem eightGrp_sq : ∀ a : EightGrp, a ^ 2 = 1 := by decide

theorem eightGrp_card : Nat.card EightGrp = 8 := by
  rw [Nat.card_eq_fintype_card]; rfl

@[expose] def kleinHom : Multiplicative (ZMod 2 × ZMod 2) →* alternatingGroup (Fin 4) :=
  MonoidHom.mk' (fun a => v₁ ^ (Multiplicative.toAdd a).1.val *
    v₂ ^ (Multiplicative.toAdd a).2.val) (by decide)

@[expose] def negOneHom : Multiplicative (ZMod 2) →* SL(2, ZMod 3) :=
  MonoidHom.mk' (fun a => negOne ^ (Multiplicative.toAdd a).val) (by decide)

@[expose] def eightHom : EightGrp →* alternatingGroup (Fin 4) × SL(2, ZMod 3) :=
  kleinHom.prodMap negOneHom

theorem eightHom_injective : Function.Injective eightHom := by
  have h1 : Function.Injective kleinHom := by decide
  have h2 : Function.Injective negOneHom := by decide
  exact h1.prodMap h2

theorem card_eq : Nat.card (alternatingGroup (Fin 4) × SL(2, ZMod 3)) = 288 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := alternatingGroup (Fin 4)),
    card_alternatingGroup, Matrix.card_SL_field]
  norm_num [Fin.prod_univ_two, ZMod.card, Nat.factorial]

end AltSLTwo

open AltSLTwo

theorem coprime_two_eight_eight {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : Nat.Coprime p 288 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h' : p ∣ 2 ^ 5 * 3 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
    omega

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem apply_apply_comm_of_finrank_eq_one {W : Submodule K V} (hW : Module.finrank K W = 1)
    {f g : Module.End K V} (hf : ∀ x ∈ W, f x ∈ W) (hg : ∀ x ∈ W, g x ∈ W) {v : V}
    (hv : v ∈ W) : f (g v) = g (f v) := by
  obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K W)
  have hspan := (finrank_eq_one_iff_of_nonzero' w hw0).mp hW
  obtain ⟨a, ha⟩ := hspan ⟨f w, hf w w.2⟩
  obtain ⟨b, hb⟩ := hspan ⟨g w, hg w w.2⟩
  obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
  have ha' : f w = a • (w : V) := (congrArg Subtype.val ha).symm
  have hb' : g w = b • (w : V) := (congrArg Subtype.val hb).symm
  have hc' : v = c • (w : V) := (congrArg Subtype.val hc).symm
  rw [hc']
  simp only [map_smul, ha', hb', smul_smul]
  congr 1
  ring

theorem three_le_finrank_eigenspace (h2 : (2 : K) ≠ 0) {σ₁ σ₂ τ β₁ β₂ ζ : Module.End K V}
    (h11 : σ₁ * σ₁ = 1) (h22 : σ₂ * σ₂ = 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    (hτ₁ : σ₁ * τ = τ * σ₂) (hτ₂ : σ₂ * τ = τ * (σ₁ * σ₂)) (hτ : Function.Injective τ)
    (hβ₁₁ : β₁ * σ₁ = σ₁ * β₁) (hβ₁₂ : β₁ * σ₂ = σ₂ * β₁) (hβ₂₁ : β₂ * σ₁ = σ₁ * β₂)
    (hβ₂₂ : β₂ * σ₂ = σ₂ * β₂) (hβ₁ : Function.Injective β₁) (hβ₂ : Function.Injective β₂)
    (hζ : β₁ * β₂ = ζ * β₂ * β₁) (hσ₁ : σ₁ ≠ 1) (hdim : Module.finrank K V ≤ 4) :
    3 ≤ Module.finrank K (ζ.eigenspace 1) := by
  have app : ∀ (f g h : Module.End K V), f * g = h → ∀ v, f (g v) = h v := fun f g h e v => by
    rw [← e, Module.End.mul_apply]
  have e11 : ∀ v, σ₁ (σ₁ v) = v := fun v => by rw [app _ _ _ h11, Module.End.one_apply]
  have e22 : ∀ v, σ₂ (σ₂ v) = v := fun v => by rw [app _ _ _ h22, Module.End.one_apply]
  have e12 : ∀ v, σ₁ (σ₂ v) = σ₂ (σ₁ v) := fun v => by rw [app _ _ _ h12, Module.End.mul_apply]
  have eτ₁ : ∀ v, σ₁ (τ v) = τ (σ₂ v) := fun v => by rw [app _ _ _ hτ₁, Module.End.mul_apply]
  have eτ₂ : ∀ v, σ₂ (τ v) = τ (σ₁ (σ₂ v)) := fun v => by
    rw [app _ _ _ hτ₂, Module.End.mul_apply, Module.End.mul_apply]
  have hneg : ∀ (f : Module.End K V) (v : V), f v = v → f v = -v → v = 0 := fun f v h1 h2' => by
    have hv : v = -v := h1.symm.trans h2'
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hv]
      exact add_neg_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2
  set W₁ := σ₁.eigenspace 1 ⊓ σ₂.eigenspace (-1) with hW₁
  set W₂ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace 1 with hW₂
  set W₃ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace (-1) with hW₃
  have mem : ∀ (s t : K) (v : V), v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t ↔
      σ₁ v = s • v ∧ σ₂ v = t • v := fun s t v => by
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  have mem₁ : ∀ v, v ∈ W₁ ↔ σ₁ v = v ∧ σ₂ v = -v := fun v => by
    rw [hW₁, mem, one_smul, neg_one_smul]
  have mem₂ : ∀ v, v ∈ W₂ ↔ σ₁ v = -v ∧ σ₂ v = v := fun v => by
    rw [hW₂, mem, one_smul, neg_one_smul]
  have mem₃ : ∀ v, v ∈ W₃ ↔ σ₁ v = -v ∧ σ₂ v = -v := fun v => by
    rw [hW₃, mem, neg_one_smul]
  have hτ13 : ∀ v ∈ W₁, τ v ∈ W₃ := fun v hv => by
    rw [mem₁] at hv
    rw [mem₃]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, map_neg]⟩
  have hτ32 : ∀ v ∈ W₃, τ v ∈ W₂ := fun v hv => by
    rw [mem₃] at hv
    rw [mem₂]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, neg_neg]⟩
  have hτ21 : ∀ v ∈ W₂, τ v ∈ W₁ := fun v hv => by
    rw [mem₂] at hv
    rw [mem₁]
    exact ⟨by rw [eτ₁, hv.2], by rw [eτ₂, hv.2, hv.1, map_neg]⟩
  have hle : ∀ {W W' : Submodule K V}, (∀ v ∈ W, τ v ∈ W') →
      Module.finrank K W ≤ Module.finrank K W' := fun {W W'} h =>
    LinearMap.finrank_le_finrank_of_injective (f := τ.restrict h)
      (fun x y hxy => Subtype.ext (hτ (congrArg Subtype.val hxy)))
  have hk13 := hle hτ13
  have hk32 := hle hτ32
  have hk21 := hle hτ21
  have hinf₂₃ : W₂ ⊓ W₃ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hneg σ₂ v ((mem₂ v).mp hv.1).2 ((mem₃ v).mp hv.2).2
  have hinf₁ : W₁ ⊓ (W₂ ⊔ W₃) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hsup : W₂ ⊔ W₃ ≤ σ₁.eigenspace (-1) := sup_le inf_le_left inf_le_left
    have h3 := hsup hv.2
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h3
    exact hneg σ₁ v ((mem₁ v).mp hv.1).1 h3
  have hsum : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) =
      Module.finrank K W₁ + (Module.finrank K W₂ + Module.finrank K W₃) := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂ ⊔ W₃)
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W₂ W₃
    rw [hinf₁, finrank_bot, add_zero] at e1
    rw [hinf₂₃, finrank_bot, add_zero] at e2
    rw [e1, e2]
  have hVle : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) ≤ Module.finrank K V := Submodule.finrank_le _
  obtain ⟨v, hv⟩ : ∃ v, σ₁ v ≠ v := by
    by_contra h
    push Not at h
    exact hσ₁ (LinearMap.ext fun v => by rw [h v, Module.End.one_apply])
  set u := v - σ₁ v with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hσu : σ₁ u = -u := by rw [hu, map_sub, e11, neg_sub]
  have hup : u + σ₂ u ∈ W₂ := by
    rw [mem₂]
    refine ⟨?_, ?_⟩
    · rw [map_add, e12, hσu, map_neg, neg_add]
    · rw [map_add, e22, add_comm]
  have hum : u - σ₂ u ∈ W₃ := by
    rw [mem₃]
    refine ⟨?_, ?_⟩
    · rw [map_sub, e12, hσu, map_neg]
      abel
    · rw [map_sub, e22, neg_sub]
  have hk1 : 1 ≤ Module.finrank K W₂ ∨ 1 ≤ Module.finrank K W₃ := by
    by_contra hcon
    push Not at hcon
    have h2' : Module.finrank K W₂ = 0 := by omega
    have h3' : Module.finrank K W₃ = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h2' h3'
    have a1 : u + σ₂ u = 0 := by
      have := hup
      rw [h2'] at this
      exact (Submodule.mem_bot K).mp this
    have a2 : u - σ₂ u = 0 := by
      have := hum
      rw [h3'] at this
      exact (Submodule.mem_bot K).mp this
    have h2u : (2 : K) • u = 0 := by
      rw [two_smul]
      calc u + u = (u + σ₂ u) + (u - σ₂ u) := by abel
        _ = 0 := by rw [a1, a2, add_zero]
    exact hu0 ((smul_eq_zero.mp h2u).resolve_left h2)
  have hd₁ : Module.finrank K W₁ = 1 := by omega
  have hd₂ : Module.finrank K W₂ = 1 := by omega
  have hd₃ : Module.finrank K W₃ = 1 := by omega
  have pres : ∀ β : Module.End K V, β * σ₁ = σ₁ * β → β * σ₂ = σ₂ * β → ∀ (s t : K),
      ∀ v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t, β v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t := by
    intro β hb1 hb2 s t v hv
    rw [mem] at hv ⊢
    refine ⟨?_, ?_⟩
    · rw [app _ _ _ hb1.symm, Module.End.mul_apply, hv.1, map_smul]
    · rw [app _ _ _ hb2.symm, Module.End.mul_apply, hv.2, map_smul]
  have hfix : ∀ W : Submodule K V, Module.finrank K W = 1 → (∀ v ∈ W, β₁ v ∈ W) →
      (∀ v ∈ W, β₂ v ∈ W) → ∀ v ∈ W, ζ v = v := by
    intro W hW hb1 hb2 v hv
    have hb : ∀ x ∈ W, (β₂ * β₁) x ∈ W := fun x hx => hb2 _ (hb1 x hx)
    have hinj : Function.Injective ((β₂ * β₁).restrict hb) := fun x y hxy => by
      have h' : β₂ (β₁ x) = β₂ (β₁ y) := congrArg Subtype.val hxy
      exact Subtype.ext (hβ₁ (hβ₂ h'))
    obtain ⟨⟨v', hv'⟩, hv'v⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
    have hv'v' : β₂ (β₁ v') = v := congrArg Subtype.val hv'v
    have hcomm := apply_apply_comm_of_finrank_eq_one hW hb1 hb2 hv'
    have hζ' : β₁ (β₂ v') = ζ (β₂ (β₁ v')) := by
      change (β₁ * β₂) v' = (ζ * β₂ * β₁) v'
      rw [hζ]
    rw [← hv'v', ← hζ', hcomm]
  have hW₁f := hfix W₁ hd₁ (pres β₁ hβ₁₁ hβ₁₂ 1 (-1)) (pres β₂ hβ₂₁ hβ₂₂ 1 (-1))
  have hW₂f := hfix W₂ hd₂ (pres β₁ hβ₁₁ hβ₁₂ (-1) 1) (pres β₂ hβ₂₁ hβ₂₂ (-1) 1)
  have hW₃f := hfix W₃ hd₃ (pres β₁ hβ₁₁ hβ₁₂ (-1) (-1)) (pres β₂ hβ₂₁ hβ₂₂ (-1) (-1))
  have hsub : W₁ ⊔ (W₂ ⊔ W₃) ≤ ζ.eigenspace 1 := by
    refine sup_le ?_ (sup_le ?_ ?_) <;> intro v hv <;>
      rw [Module.End.mem_eigenspace_iff, one_smul]
    · exact hW₁f v hv
    · exact hW₂f v hv
    · exact hW₃f v hv
  calc 3 = Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) := by rw [hsum, hd₁, hd₂, hd₃]
    _ ≤ Module.finrank K (ζ.eigenspace 1) := Submodule.finrank_mono hsub

end LinearAlgebra

theorem finrank_eigenspace_le_two_of_pRank_le_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P) [IsElementaryAbelian p (P ⧸ frattini P)]
    {σ : MulAut P} (hσ : σ ^ 2 = 1) (hrank : CFSG.pRank p (fixedSubgroupOf σ) ≤ 2)
    (f : Module.End (ZMod p) (Additive (P ⧸ frattini P)))
    (hf : ∀ x : P, f (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((σ x : P) : P ⧸ frattini P)) :
    Module.finrank (ZMod p) (f.eigenspace 1) ≤ 2 := by
  classical
  have hp' : p.Prime := hp.out
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  set C := fixedSubgroupOf σ with hC_def
  let Z := Subgroup.zpowers σ
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hσ, one_zpow, Subgroup.coe_one]⟩
  let α : Z →* MulAut P := Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini P, α b n ∈ frattini P := by
    intro b n hn
    have h := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini P).Characteristic) (α b)
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (frattini P) := not_two_dvd_card_of_odd hp2 (hP.to_subgroup _)
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α (frattini P) hN
    hcop
  have hlift : ∀ w ∈ f.eigenspace 1, ∃ c ∈ C, w = Additive.ofMul (c : P ⧸ frattini P) := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff, one_smul] at hw
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hwx : w = Additive.ofMul (x : P ⧸ frattini P) := by rw [hx]; rfl
    have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN
        ⟨σ, Subgroup.mem_zpowers σ⟩ (x : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      have h := hw
      rw [hwx, hf] at h
      exact congrArg Additive.toMul h
    have hmem : (x : P ⧸ frattini P) ∈ {q : P ⧸ frattini P | ∀ b : Z,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN b q =
          q} := by
      rintro ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hb' : (⟨σ ^ k, hb⟩ : Z) = ⟨σ, Subgroup.mem_zpowers σ⟩ ^ k := Subtype.ext (by simp)
      rw [hb', map_zpow]
      exact zpow_apply_eq_self_of_apply_eq_self hfixa k
    rw [hset] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    refine ⟨c, hc ⟨σ, Subgroup.mem_zpowers σ⟩, ?_⟩
    rw [hwx, ← hcx]
    rfl
  have hVcomm : IsMulCommutative (P ⧸ frattini P) := inferInstance
  let g : C →* P ⧸ frattini P := (QuotientGroup.mk' (frattini P)).comp C.subtype
  have hcomm_ker : commutator C ≤ g.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hVcomm.is_comm.comm _ _
  have hrange : Nat.card g.range ≤ Nat.card (C ⧸ commutator C) := by
    have h1 := Subgroup.card_ker_mul_card_range g
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator C)
    have h3 := Subgroup.card_le_of_le hcomm_ker
    have hpos : 0 < Nat.card g.ker := Nat.card_pos
    have h4 : Nat.card g.range * Nat.card g.ker ≤
        Nat.card (C ⧸ commutator C) * Nat.card g.ker := by
      calc Nat.card g.range * Nat.card g.ker = Nat.card C := by rw [← h1, mul_comm]
        _ = Nat.card (C ⧸ commutator C) * Nat.card (commutator C) := h2
        _ ≤ Nat.card (C ⧸ commutator C) * Nat.card g.ker := Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  have hCC : Nat.card (C ⧸ commutator C) ≤ p ^ 2 := by
    have hC : IsPGroup p C := hP.to_subgroup C
    have hrank' := (class_two_small_rank_order_bounds hC (subgroup_pow_eq_one hexp C)
      (subgroup_commutator_le_center hclass C)).1 hrank
    obtain ⟨k, hk⟩ := (hC.to_quotient (commutator C)).exists_card_eq
    have hk2 := (quotient_commutator_rank hp' (subgroup_pow_eq_one hexp C) hk).2
    rw [hk]
    exact Nat.pow_le_pow_right hp'.pos (hk2 ▸ hrank')
  have hcardE : Nat.card (f.eigenspace 1) ≤ p ^ 2 := by
    refine le_trans ?_ (hrange.trans hCC)
    refine Nat.card_le_card_of_injective
      (fun w => (⟨Additive.toMul (w : Additive (P ⧸ frattini P)), ?_⟩ : g.range)) ?_
    · obtain ⟨c, hc, hcw⟩ := hlift w w.2
      exact ⟨⟨c, hc⟩, by rw [hcw]; rfl⟩
    · intro w₁ w₂ h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  have : Fintype (f.eigenspace 1) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := f.eigenspace 1)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  rw [hpow] at hcardE
  exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hcardE

theorem exists_involution_three_le_pRank_of_class_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P)
    (ρ : alternatingGroup (Fin 4) × SL(2, ZMod 3) →* MulAut P) (hρ : Function.Injective ρ) :
    ∃ g, g ≠ 1 ∧ g ^ 2 = 1 ∧ 3 ≤ CFSG.pRank p (fixedSubgroupOf (ρ g)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hp' : p.Prime := hp.out
  obtain ⟨hchar, hVcomm, hVexp, hVelem, d, hVcard, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let E : MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (P ⧸ frattini P)) (q : P ⧸ frattini P),
      E σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)
  have hq : ∀ (σ : MulAut P) (x : P), q σ (x : P ⧸ frattini P) = ((σ x : P) : P ⧸ frattini P) :=
    fun σ x => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ σ x
  let ρV : alternatingGroup (Fin 4) × SL(2, ZMod 3) →*
      Module.End (ZMod p) (Additive (P ⧸ frattini P)) := E.comp (q.comp ρ)
  have hρV : ∀ (g : alternatingGroup (Fin 4) × SL(2, ZMod 3)) (x : P),
      ρV g (Additive.ofMul (x : P ⧸ frattini P)) =
        Additive.ofMul ((ρ g x : P) : P ⧸ frattini P) := fun g x => by
    change E (q (ρ g)) _ = _
    rw [hE, hq]
  have hinv : ∀ g (v : Additive (P ⧸ frattini P)), ρV g⁻¹ (ρV g v) = v := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : ∀ g, Function.Injective (ρV g) := fun g x y h => by
    rw [← hinv g x, h, hinv g y]
  have hdim : Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 4 := by
    have h8 := (class_two_eight_action_inverting_quotient hp2 hP hexp hclass eightGrp_sq
      eightGrp_card (ρ.comp eightHom) (hρ.comp eightHom_injective) (fun a ha =>
        Nat.le_of_lt_succ (hcon (eightHom a)
          (fun h => ha (eightHom_injective (h.trans (map_one _).symm)))
          (by rw [← map_pow, eightGrp_sq, map_one])))).1
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    have hrank := pRank_eq_of_isMulCommutative hp' hVexp hVcomm
      (k := Module.finrank (ZMod p) (Additive (P ⧸ frattini P))) hpow
    rw [← hrank]
    rcases h8 with h | h <;> omega
  have hσ₁ : ρV d₁ ≠ 1 := by
    intro h1
    have hρd : ρ d₁ ≠ 1 := fun h => d₁_ne_one (hρ (h.trans (map_one ρ).symm))
    have hord : orderOf (ρ d₁) = 2 := orderOf_eq_prime (by
      rw [← map_pow, pow_two, d₁_mul_d₁, map_one]) hρd
    apply hρd
    refine CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial 2
      (ρ d₁) hord (not_two_dvd_card_of_odd hp2 hP) ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h1
    simp only [hρV, Module.End.one_apply] at h
    exact congrArg Additive.toMul h
  have h3 := three_le_finrank_eigenspace (σ₁ := ρV d₁) (σ₂ := ρV d₂) (τ := ρV w₃)
    (β₁ := ρV b₁) (β₂ := ρV b₂) (ζ := ρV zz) (two_ne_zero_zmod hp' hp2)
    (by simpa only [map_mul, map_one] using congrArg ρV d₁_mul_d₁)
    (by simpa only [map_mul, map_one] using congrArg ρV d₂_mul_d₂)
    (by simpa only [map_mul] using congrArg ρV d₁_mul_d₂)
    (by simpa only [map_mul] using congrArg ρV d₁_mul_w₃)
    (by simpa only [map_mul] using congrArg ρV d₂_mul_w₃) (hinj w₃)
    (by simpa only [map_mul] using congrArg ρV b₁_mul_d₁)
    (by simpa only [map_mul] using congrArg ρV b₁_mul_d₂)
    (by simpa only [map_mul] using congrArg ρV b₂_mul_d₁)
    (by simpa only [map_mul] using congrArg ρV b₂_mul_d₂) (hinj b₁) (hinj b₂)
    (by simpa only [map_mul] using congrArg ρV b₁_mul_b₂) hσ₁ hdim
  have h2 := finrank_eigenspace_le_two_of_pRank_le_two hp2 hP hexp hclass
    (σ := ρ zz) (by rw [← map_pow, zz_sq, map_one])
    (Nat.le_of_lt_succ (hcon zz zz_ne_one zz_sq)) (ρV zz) (hρV zz)
  omega

@[expose] def restrictCharacteristic {Q : Type*} [Group Q] (D : Subgroup Q)
    [hD : D.Characteristic] : MulAut Q →* MulAut D where
  toFun σ :=
    { toFun := fun x => ⟨σ x, (Subgroup.characteristic_iff_map_le.mp hD σ) ⟨x, x.2, rfl⟩⟩
      invFun := fun x => ⟨σ⁻¹ x, (Subgroup.characteristic_iff_map_le.mp hD σ⁻¹) ⟨x, x.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self Q σ x)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self Q σ x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Q) (y : Q)) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' := fun _ _ => MulEquiv.ext fun _ => Subtype.ext rfl

theorem restrictCharacteristic_apply_coe {Q : Type*} [Group Q] (D : Subgroup Q)
    [D.Characteristic] (σ : MulAut Q) (x : D) :
    ((restrictCharacteristic D σ x : D) : Q) = σ (x : Q) :=
  rfl

theorem exists_involution_three_le_pRank {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : alternatingGroup (Fin 4) × SL(2, ZMod 3) →* MulAut P) (hρ : Function.Injective ρ) :
    ∃ g, g ≠ 1 ∧ g ^ 2 = 1 ∧ 3 ≤ CFSG.pRank p (fixedSubgroupOf (ρ g)) := by
  have hp' : p.Prime := hp.out
  have hp2 : p ≠ 2 := by omega
  have hnt : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (MulAut P) := ⟨fun σ τ => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact d₁_ne_one (hρ (Subsingleton.elim _ _))
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  let ρD := (restrictCharacteristic D).comp ρ
  have hρD : Function.Injective ρD := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfixg : ρ g ∈ fixingSubgroup (MulAut P) (D : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h := congrArg (fun σ : MulAut D => ((σ ⟨y, hy⟩ : D) : P)) hg
      exact h
    obtain ⟨k, hk⟩ := hDfix ⟨ρ g, hfixg⟩
    have hk' : (ρ g) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h1 : orderOf (ρ g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (ρ g) ∣ 288 :=
      (orderOf_map_dvd ρ g).trans (AltSLTwo.card_eq ▸ orderOf_dvd_natCard g)
    have hcop : Nat.Coprime (p ^ k) 288 := Nat.Coprime.pow_left k (coprime_two_eight_eight hp' hp3)
    have h1' := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact hρ ((orderOf_eq_one_iff.mp h1').trans (map_one ρ).symm)
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hxy : ⁅(x : P), (y : P)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set P) :=
      hDcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _))
    have hcoe : ((⁅x, y⁆ : D) : P) = ⁅(x : P), (y : P)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
    exact Subgroup.mem_centralizer_iff.mp hxy.2 w w.2
  obtain ⟨g, hg1, hg2, hgr⟩ :=
    exists_involution_three_le_pRank_of_class_two hp2 hDp hDexp' hDclass ρD hρD
  refine ⟨g, hg1, hg2, hgr.trans ?_⟩
  let f : fixedSubgroupOf (ρD g) →* fixedSubgroupOf (ρ g) :=
    (D.subtype.comp (fixedSubgroupOf (ρD g)).subtype).codRestrict _ fun x => by
      have hx := x.2
      rw [mem_fixedSubgroupOf] at hx ⊢
      exact congrArg Subtype.val hx
  have hf : Function.Injective f := fun x y h => by
    have h' : ((x : D) : P) = ((y : D) : P) :=
      congrArg (fun z : fixedSubgroupOf (ρ g) => (z : P)) h
    exact Subtype.ext (Subtype.ext h')
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp'.one_lt f hf

theorem le_localRank_of_commute_involution {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : 1 < p) {x : G} (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) {E : Subgroup G}
    (hEc : IsMulCommutative E) (hEp : ∀ w ∈ E, w ^ p = 1)
    (hEx : E ≤ Subgroup.centralizer ({x} : Set G)) {r : ℕ} (hr : Nat.card E = p ^ r) :
    r ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hU2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hUne : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (by
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rwa [h, Subgroup.mem_bot] at this)
  have hEU : E ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro w hw
    have hwx : Commute w x := Subgroup.mem_centralizer_singleton_iff.mp (hEx hw)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(hwx.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers x k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hy' : y = x ^ k := by
        calc y = w⁻¹ * (w * y * w⁻¹) * w := by group
          _ = w⁻¹ * x ^ k * w := by rw [hk]
          _ = x ^ k := by rw [mul_assoc, ((hwx.zpow_right k).eq).symm, inv_mul_cancel_left]
      rw [hy']
      exact Subgroup.zpow_mem_zpowers x k
  have hbdd : BddAbove
      {k | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧ CFSG.Assembly.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨F, -, -, hF⟩ := CFSG.SectionRank.exists_pRank hp H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change CFSG.Open.pRank p H ≤ Nat.card G
    omega
  exact (CFSG.SectionRank.le_pRank hp hEU ⟨hEc, hEp⟩ hr).trans
    (le_csSup hbdd ⟨_, ⟨Subgroup.zpowers x, hUne, hU2, rfl⟩, rfl⟩)

theorem exists_involution_elemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {X P : Subgroup G} (hP : IsPGroup p P)
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (e : X ≃* alternatingGroup (Fin 4) × SL(2, ZMod 3))
    (hfaith : X ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ x ^ 2 = 1 ∧ ∃ E : Subgroup G,
      E ≤ P ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsMulCommutative E ∧ (∀ w ∈ E, w ^ p = 1) ∧
        ∃ r, 3 ≤ r ∧ Nat.card E = p ^ r := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : alternatingGroup (Fin 4) × SL(2, ZMod 3) →* G := X.subtype.comp e.symm.toMonoidHom
  have hφN : ∀ g, φ g ∈ Subgroup.normalizer (P : Set G) := fun g => hXP (e.symm g).2
  have hφinj : Function.Injective φ := fun a b h => e.symm.injective (Subtype.ext h)
  let ρ : alternatingGroup (Fin 4) × SL(2, ZMod 3) →* MulAut P :=
    P.normalizerMonoidHom.comp (φ.codRestrict _ hφN)
  have hρapp : ∀ g (y : P), ((ρ g y : P) : G) = φ g * y * (φ g)⁻¹ := fun g y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : φ g ∈ X ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨(e.symm g).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : G)) hg
      simp only [hρapp, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    rw [hfaith, Subgroup.mem_bot] at hc
    exact hφinj (hc.trans (map_one φ).symm)
  obtain ⟨g, hg1, hg2, hgr⟩ := exists_involution_three_le_pRank hp3 hP ρ hρ
  refine ⟨φ g, (e.symm g).2, fun h => hg1 (hφinj (h.trans (map_one φ).symm)),
    by rw [← map_pow, hg2, map_one], ?_⟩
  let f : fixedSubgroupOf (ρ g) →* G := P.subtype.comp (fixedSubgroupOf (ρ g)).subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
  have hmap : (⊤ : Subgroup (fixedSubgroupOf (ρ g))).map f ≤
      P ⊓ Subgroup.centralizer ({φ g} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    have hy := y.2
    rw [mem_fixedSubgroupOf] at hy
    have h := congrArg Subtype.val hy
    rw [hρapp, mul_inv_eq_iff_eq_mul] at h
    exact Subgroup.mem_inf.mpr ⟨((y : P)).2,
      Subgroup.mem_centralizer_singleton_iff.mpr h.symm⟩
  have hle : 3 ≤ CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({φ g} : Set G)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hgr
    exact hgr.trans ((CFSG.SectionRank.pRank_le_map hp.one_lt f hf ⊤).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hmap))
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (P ⊓ Subgroup.centralizer ({φ g} : Set G))
  exact ⟨E, hEH, hE.1, hE.2, _, hle, hcard⟩

theorem rank3II_3_9_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {X P : Subgroup G} (hP : IsPGroup p P) (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hX : Nonempty (X ≃* alternatingGroup (Fin 4) × SL(2, ZMod 3)))
    (hfaith : X ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    2 < CFSG.Assembly.RankThreeEven.localRank p G := by
  obtain ⟨e⟩ := hX
  obtain ⟨x, -, hx1, hx2, E, hE, hEc, hEp, r, hr3, hr⟩ :=
    exists_involution_elemAbelian hp hp3 hP hXP e hfaith
  exact lt_of_lt_of_le (by omega)
    (le_localRank_of_commute_involution hp.one_lt hx1 hx2 hEc hEp (hE.trans inf_le_right) hr)

theorem rank3II_3_9 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {X P : Subgroup G} (hP : IsPGroup p P) (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hX : Nonempty (X ≃* alternatingGroup (Fin 4) × SL(2, ZMod 3)))
    (hfaith : X ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    2 < CFSG.Assembly.RankThreeEven.localRank p ↥(X ⊔ P) := by
  obtain ⟨e⟩ := hX
  obtain ⟨x, hxX, hx1, hx2, E, hE, hEc, hEp, r, hr3, hr⟩ :=
    exists_involution_elemAbelian hp hp3 hP hXP e hfaith
  have hxK : x ∈ X ⊔ P := Subgroup.mem_sup_left hxX
  have hEK : E ≤ X ⊔ P := (hE.trans inf_le_left).trans le_sup_right
  let x' : ↥(X ⊔ P) := ⟨x, hxK⟩
  have hx1' : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx2' : x' ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx2)
  have hE'c : IsMulCommutative (E.subgroupOf (X ⊔ P)) := ⟨⟨fun a b => by
    have := hEc.is_comm.comm ⟨((a : ↥(X ⊔ P)) : G), a.2⟩ ⟨((b : ↥(X ⊔ P)) : G), b.2⟩
    have h' : ((a : ↥(X ⊔ P)) : G) * ((b : ↥(X ⊔ P)) : G) =
        ((b : ↥(X ⊔ P)) : G) * ((a : ↥(X ⊔ P)) : G) := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h')⟩⟩
  have hE'p : ∀ w ∈ E.subgroupOf (X ⊔ P), w ^ p = 1 := fun w hw =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hEp _ hw)
  have hE'x : E.subgroupOf (X ⊔ P) ≤ Subgroup.centralizer ({x'} : Set ↥(X ⊔ P)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hE hw).2
  have hr' : Nat.card (E.subgroupOf (X ⊔ P)) = p ^ r := by
    rw [← hr]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  exact lt_of_lt_of_le (by omega)
    (le_localRank_of_commute_involution hp.one_lt hx1' hx2' hE'c hE'p hE'x hr')

end CFSG.RankThree.PartTwo.Sec3
