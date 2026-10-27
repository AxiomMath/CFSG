module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalLevi

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoTorus
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSpecial
import CFSG.LieType.Chevalley.SylowOpposition
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Reduced
import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.EvenBN.G2
open Matrix
open scoped MatrixGroups


variable {G : Type} [Group G]

private theorem eq_zero_of_smul_cube {K : Type} [Field K] [CharP K 2] {u : K} (hu0 : u ≠ 0)
    (h1u : 1 + u ≠ 0) {x : Fin 2 → K} (h : ((1 + u) ^ 3) • x = x + (u ^ 3) • x) : x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ((1 + u) ^ 3 - 1 - u ^ 3) • x = 0 := by
    rw [sub_smul, sub_smul, one_smul, h]
    abel
  have hc : (1 + u) ^ 3 - 1 - u ^ 3 = u * (1 + u) := by linear_combination (u + u ^ 2) * h2
  rw [hc] at key
  exact (smul_eq_zero.mp key).resolve_left (mul_ne_zero hu0 h1u)

theorem exists_mulEquiv_parB_of_coords [Finite G] {L Q Z N : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    (hQL : Q ≤ L) (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) (hZcen : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ Z)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z)
    (α : ↥L →* SL(2, K)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q)
    (γ : ↥Q →* Multiplicative (Fin 3 → K)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = Z.subgroupOf Q)
    (hγeq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u)))
    (δ : ↥Z ≃* Multiplicative (Fin 2 → K))
    (hδeq : ∀ (ℓ : ↥L) (u v : ↥Z), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (δ v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (δ u)))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (hNZ : ∀ n ∈ N, ∀ z ∈ Z, n * z * n⁻¹ ∈ Z)
    (hNL : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ * l⁻¹ ∈ Q) (hNodd : Odd (Nat.card N))
    (hNcard : Nat.card N = Nat.card K - 1) (hNinf : N ⊓ L = ⊥)
    (hNQ1 : ∀ n ∈ N, (∀ u ∈ Q, n * u * n⁻¹ = u) → n = 1)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card Q)) :
    ∃ ψ : ↥(L ⊔ N) ≃* ↥(Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K)),
      ∀ x : ↥L, ∃ y ∈ Model.M K,
        ((ψ ⟨x, Subgroup.mem_sup_left x.2⟩ : ↥(Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K))) :
          ModGL Tag.G2 K) = y * G2q.leviBHom (α x, 1) := by
  classical
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by omega
  have hLQ' : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q := fun ℓ hℓ u hu =>
    (Subgroup.mem_normalizer_iff.mp (hLQ hℓ) u).mp hu
  have hNQ' : ∀ n ∈ N, ∀ u ∈ Q, n * u * n⁻¹ ∈ Q := fun n hn u hu =>
    (Subgroup.mem_normalizer_iff.mp (hNQ hn) u).mp hu
  have hNL' : ∀ n ∈ N, ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = n * ℓ * n⁻¹ ∧ α ℓ' = α ℓ := by
    intro n hn ℓ
    have hc := hNL n hn ℓ ℓ.2
    have e : n * ℓ * n⁻¹ = (n * ℓ * n⁻¹ * (ℓ : G)⁻¹) * ℓ := by group
    have hmem : n * ℓ * n⁻¹ ∈ L := by
      rw [e]
      exact L.mul_mem (hQL hc) ℓ.2
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    have e' : (⟨n * ℓ * n⁻¹, hmem⟩ : ↥L) = ⟨_, hQL hc⟩ * ℓ := Subtype.ext e
    rw [e', map_mul, (hker _).mpr hc, one_mul]
  obtain ⟨τ, c, hc0, hτγ, hτδ, hsq⟩ := exists_torus_radCoord hK4 hZQ hZc hQ2 hZcen hLQ' hLZ α hα
    γ hγ hγker hγeq δ hδeq hNQ' hNZ hNL' hNodd hNcard hNQ1
  have hfixQ : ∀ x ∈ Q, (∀ n ∈ N, n * x * n⁻¹ = x) → x = 1 := fun x hx h =>
    eq_one_of_commute_torus_radCoord hK γ hγker δ τ hτγ hτδ hx h
  obtain ⟨ε, hεinj, hεL, hεN, hεmul, hεsup, hεdisj, hεdec⟩ :=
    exists_leviHom_of_torus hQL hLQ hNQ hcop hNL hfixQ hNinf α hα hker τ
  have hγR : ∀ (p : SL(2, K) × Kˣ) (v w : ↥Q), (w : G) = ε p * v * (ε p)⁻¹ →
      Multiplicative.toAdd (γ w) =
        ((p.2 : K) ^ 2) • (sp4RadMat p.1).mulVec (Multiplicative.toAdd (γ v)) := by
    intro p v w hw
    obtain ⟨hg, hαg⟩ := hεL p.1
    obtain ⟨ht, hτt⟩ := hεN p.2
    let u : ↥Q := ⟨ε (1, p.2) * v * (ε (1, p.2))⁻¹, hNQ' _ ht v v.2⟩
    have h1 := hτγ ⟨ε (1, p.2), ht⟩ v u rfl
    rw [hτt] at h1
    have h2 := hγeq ⟨ε (p.1, 1), hg⟩ u w (by
      change (w : G) = ε (p.1, 1) * (ε (1, p.2) * v * (ε (1, p.2))⁻¹) * (ε (p.1, 1))⁻¹
      rw [hw, hεmul p]
      group)
    rw [hαg, h1, Matrix.mulVec_smul] at h2
    exact h2
  have hδR : ∀ (p : SL(2, K) × Kˣ) (z w : ↥Z), (w : G) = ε p * z * (ε p)⁻¹ →
      Multiplicative.toAdd (δ w) =
        ((p.2 : K) ^ 3) • (p.1 : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (δ z)) := by
    intro p z w hw
    obtain ⟨hg, hαg⟩ := hεL p.1
    obtain ⟨ht, hτt⟩ := hεN p.2
    let u : ↥Z := ⟨ε (1, p.2) * z * (ε (1, p.2))⁻¹, hNZ _ ht z z.2⟩
    have h1 := hτδ ⟨ε (1, p.2), ht⟩ z u rfl
    rw [hτt] at h1
    have h2 := hδeq ⟨ε (p.1, 1), hg⟩ u w (by
      change (w : G) = ε (p.1, 1) * (ε (1, p.2) * z * (ε (1, p.2))⁻¹) * (ε (p.1, 1))⁻¹
      rw [hw, hεmul p]
      group)
    rw [hαg, h1, Matrix.mulVec_smul] at h2
    exact h2
  let sc : Multiplicative (Fin 2 → K) ≃* Multiplicative (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd (c⁻¹ • Multiplicative.toAdd v)
      invFun := fun v => Multiplicative.ofAdd (c • Multiplicative.toAdd v)
      left_inv := fun v => by simp [smul_smul, hc0]
      right_inv := fun v => by simp [smul_smul, hc0]
      map_mul' := fun v w => by simp [smul_add] }
  let δ' : ↥Z ≃* Multiplicative (Fin 2 → K) := δ.trans sc
  have hδ' : ∀ z, Multiplicative.toAdd (δ' z) = c⁻¹ • Multiplicative.toAdd (δ z) := fun z => rfl
  have hδ'R : ∀ (p : SL(2, K) × Kˣ) (z w : ↥Z), (w : G) = ε p * z * (ε p)⁻¹ →
      Multiplicative.toAdd (δ' w) =
        ((p.2 : K) ^ 3) • (p.1 : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (δ' z)) := by
    intro p z w hw
    rw [hδ', hδ', hδR p z w hw, Matrix.mulVec_smul, smul_smul, smul_smul, mul_comm]
  have hsq' : ∀ (u : ↥Q) (hu : (u : G) ^ 2 ∈ Z) (x b₀ b₁ : K),
      Multiplicative.toAdd (γ u) = ![x, b₀ ^ 2, b₁ ^ 2] →
        Multiplicative.toAdd (δ' ⟨(u : G) ^ 2, hu⟩) = (x + b₀ * b₁) • ![b₀, b₁] := by
    intro u hu x b₀ b₁ h
    rw [hδ', hsq u hu x b₀ b₁ h, smul_smul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hYM : Model.Y K ≤ Model.M K := Model.Y_le_M
  have hRZ' : ∀ r ∈ Model.leviB K ⊔ Model.J₄ K, ∀ z ∈ Model.Y K, r * z * r⁻¹ ∈ Model.Y K := by
    intro r hr z hz
    rw [← G2q.range_leviBHom] at hr
    obtain ⟨p, rfl⟩ := hr
    exact G2q.leviBHom_conj_mem_Y p hz
  have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := by
    intro z hz
    have h1 : δ (⟨z, hz⟩ ^ 2) = δ 1 := by
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      ext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    have h2 := congrArg Subtype.val (δ.injective h1)
    simpa using h2
  have hεQ : ∀ p, ∀ u ∈ Q, ε p * u * (ε p)⁻¹ ∈ Q := by
    intro p u hu
    obtain ⟨hg, -⟩ := hεL p.1
    obtain ⟨ht, -⟩ := hεN p.2
    rw [hεmul p]
    have e : ε (p.1, 1) * ε (1, p.2) * u * (ε (p.1, 1) * ε (1, p.2))⁻¹ =
        ε (p.1, 1) * (ε (1, p.2) * u * (ε (1, p.2))⁻¹) * (ε (p.1, 1))⁻¹ := by group
    rw [e]
    exact hLQ' _ hg _ (hNQ' _ ht u hu)
  have hRQ : ε.range ≤ Subgroup.normalizer (Q : Set G) := by
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hεQ p u, fun h => ?_⟩
    have h' := hεQ p⁻¹ _ h
    have e : ε p⁻¹ * (ε p * u * (ε p)⁻¹) * (ε p⁻¹)⁻¹ = u := by
      rw [map_inv]
      group
    rwa [e] at h'
  have hRZ : ∀ r ∈ ε.range, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z := by
    rintro _ ⟨p, rfl⟩ z hz
    obtain ⟨hg, -⟩ := hεL p.1
    obtain ⟨ht, -⟩ := hεN p.2
    rw [hεmul p]
    have e : ε (p.1, 1) * ε (1, p.2) * z * (ε (p.1, 1) * ε (1, p.2))⁻¹ =
        ε (p.1, 1) * (ε (1, p.2) * z * (ε (1, p.2))⁻¹) * (ε (p.1, 1))⁻¹ := by group
    rw [e]
    exact hLZ _ hg _ (hNZ _ ht z hz)
  haveI : (Z.subgroupOf Q).Normal := by
    rw [← hγker]
    exact MonoidHom.normal_ker γ
  let eR : ↥ε.range ≃* ↥(Model.leviB K ⊔ Model.J₄ K) :=
    (MonoidHom.ofInjective hεinj).symm.trans G2q.leviBEquiv
  have hεsymm : ∀ r : ↥ε.range, ε ((MonoidHom.ofInjective hεinj).symm r) = r := by
    intro r
    rw [← MonoidHom.ofInjective_apply hεinj, MulEquiv.apply_symm_apply]
  have hsymmε : ∀ p, (MonoidHom.ofInjective hεinj).symm ⟨ε p, ⟨p, rfl⟩⟩ = p := by
    intro p
    apply hεinj
    rw [hεsymm]
  let fQ : ↥Q ⧸ Z.subgroupOf Q ≃* Multiplicative (Fin 3 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hγker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective γ hγ)
  have hfQ : ∀ v : ↥Q, fQ (QuotientGroup.mk v) = γ v := fun v => rfl
  let fM : ↥Q ⧸ Z.subgroupOf Q ≃* ↥(Model.M K) ⧸ (Model.Y K).subgroupOf (Model.M K) :=
    fQ.trans G2q.radBQuot.symm
  have hfM : ∀ (v : ↥Q) (v' : ↥(Model.M K)),
      fM (QuotientGroup.mk v) = QuotientGroup.mk v' ↔ γ v = G2q.radBCoord v' := by
    intro v v'
    change G2q.radBQuot.symm (fQ (QuotientGroup.mk v)) = _ ↔ _
    rw [hfQ, MulEquiv.symm_apply_eq, G2q.radBQuot_mk]
  let gY : ↥Z ≃* ↥(Model.Y K) := δ'.trans G2q.zBCoord.symm
  have hgY : ∀ z, G2q.zBCoord (gY z) = δ' z := fun z => MulEquiv.apply_symm_apply _ _
  have hfR : ∀ (r : ↥ε.range) (v w : ↥Q) (v' w' : ↥(Model.M K)),
      (w : G) = (r : G) * v * (r : G)⁻¹ →
      (w' : ModGL Tag.G2 K) = (eR r : ModGL Tag.G2 K) * v' * (eR r : ModGL Tag.G2 K)⁻¹ →
        fM (QuotientGroup.mk v) = QuotientGroup.mk v' →
          fM (QuotientGroup.mk w) = QuotientGroup.mk w' := by
    intro r v w v' w' hw hw' hvv'
    rw [hfM] at hvv' ⊢
    rw [← hεsymm r] at hw
    have h1 := G2q.radBCoord_conj_leviBHom ((MonoidHom.ofInjective hεinj).symm r) v' w' hw'
    have h2 := hγR _ v w hw
    apply Multiplicative.toAdd.injective
    rw [h1, h2, hvv']
  have hgR : ∀ (r : ↥ε.range) (z w : ↥Z), (w : G) = (r : G) * z * (r : G)⁻¹ →
      (gY w : ModGL Tag.G2 K) =
        (eR r : ModGL Tag.G2 K) * (gY z : ModGL Tag.G2 K) * (eR r : ModGL Tag.G2 K)⁻¹ := by
    intro r z w hw
    rw [← hεsymm r] at hw
    let p := (MonoidHom.ofInjective hεinj).symm r
    let w'' : ↥(Model.Y K) := ⟨G2q.leviBHom p * gY z * (G2q.leviBHom p)⁻¹,
      G2q.leviBHom_conj_mem_Y p (gY z).2⟩
    have h1 := G2q.zBCoord_conj_leviBHom p (gY z) w'' rfl
    have h2 := hδ'R p z w hw
    have h3 : gY w = w'' := by
      apply G2q.zBCoord.injective
      apply Multiplicative.toAdd.injective
      rw [h1, hgY, hgY, h2]
    exact congrArg Subtype.val h3
  have hsqR : ∀ (v : ↥Q) (v' : ↥(Model.M K)),
      fM (QuotientGroup.mk v) = QuotientGroup.mk v' →
        ∀ hz : (v : G) ^ 2 ∈ Z,
          (gY ⟨(v : G) ^ 2, hz⟩ : ModGL Tag.G2 K) = (v' : ModGL Tag.G2 K) ^ 2 := by
    intro v v' hvv' hz
    rw [hfM] at hvv'
    obtain ⟨b₀, hb₀⟩ := isSquare_of_charTwo' ((Multiplicative.toAdd (γ v)) 1)
    obtain ⟨b₁, hb₁⟩ := isSquare_of_charTwo' ((Multiplicative.toAdd (γ v)) 2)
    have hγv : Multiplicative.toAdd (γ v) =
        ![(Multiplicative.toAdd (γ v)) 0, b₀ ^ 2, b₁ ^ 2] := by
      ext i
      fin_cases i <;> simp [hb₀, hb₁, sq]
    have hv' : (v' : ModGL Tag.G2 K) ^ 2 ∈ Model.Y K := G2q.sq_mem_Y_of_mem_M v'.2
    have h1 := hsq' v hz _ b₀ b₁ hγv
    have h2 := G2q.zBCoord_sq v' hv' (x₀ := (Multiplicative.toAdd (γ v)) 0) (b₀ := b₀)
      (b₁ := b₁) (by rw [← hvv']; exact hγv)
    have h3 : gY ⟨(v : G) ^ 2, hz⟩ = ⟨(v' : ModGL Tag.G2 K) ^ 2, hv'⟩ := by
      apply G2q.zBCoord.injective
      apply Multiplicative.toAdd.injective
      rw [hgY, h1, h2]
    exact congrArg Subtype.val h3
  have hεN' : ∀ n (hn : n ∈ N), ε (1, τ ⟨n, hn⟩) = n := by
    intro n hn
    obtain ⟨ht, hτt⟩ := hεN (τ ⟨n, hn⟩)
    exact congrArg Subtype.val (τ.injective hτt)
  have hNR : N ≤ ε.range := fun n hn => ⟨(1, τ ⟨n, hn⟩), hεN' n hn⟩
  have hNnorm : ∀ r ∈ ε.range, ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    rintro _ ⟨p, rfl⟩ n hn
    rw [← hεN' n hn]
    have e : ε p * ε (1, τ ⟨n, hn⟩) * (ε p)⁻¹ = ε (1, τ ⟨n, hn⟩) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, Prod.fst_inv, mul_one, mul_inv_cancel]
      · simp only [Prod.snd_mul, Prod.snd_inv]
        rw [mul_comm p.2, mul_inv_cancel_right]
    rw [e]
    exact (hεN _).1
  have hZ'c : ∀ a ∈ Model.Y K, ∀ b ∈ Model.Y K, a * b = b * a := fun a ha b hb =>
    G2q.mul_comm_of_mem_Y_of_mem_M ha (hYM hb)
  have hN := crossedHomPrincipalOn_of_odd eR hRQ hRZ hRZ' hZ'c
    (fun z hz => G2q.sq_eq_one_of_mem_Y hz) hNR hNodd
  have hfixφ : ∀ φ : ↥Q →* ↥(Model.Y K), (∀ v : ↥Q, (v : G) ∈ Z → φ v = 1) →
      (∀ n : ↥ε.range, (n : G) ∈ N → ∀ (v w : ↥Q), (w : G) = (n : G) * v * (n : G)⁻¹ →
        (φ w : ModGL Tag.G2 K) =
          (eR n : ModGL Tag.G2 K) * (φ v : ModGL Tag.G2 K) * (eR n : ModGL Tag.G2 K)⁻¹) →
      φ = 1 := by
    intro φ hφZ hφN
    have hΦmul : ∀ u₁ u₂ : ↥Q, Multiplicative.toAdd (G2q.zBCoord (φ (u₁ * u₂))) =
        Multiplicative.toAdd (G2q.zBCoord (φ u₁)) + Multiplicative.toAdd (G2q.zBCoord (φ u₂)) := by
      intro u₁ u₂
      rw [map_mul, map_mul, toAdd_mul]
    have hΦZ : ∀ u₁ u₂ : ↥Q, γ u₁ = γ u₂ →
        Multiplicative.toAdd (G2q.zBCoord (φ u₂)) = Multiplicative.toAdd (G2q.zBCoord (φ u₁)) := by
      intro u₁ u₂ h
      have hk : u₁⁻¹ * u₂ ∈ γ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      rw [hγker] at hk
      have h1 := hφZ _ (Subgroup.mem_subgroupOf.mp hk)
      have e : u₂ = u₁ * (u₁⁻¹ * u₂) := by group
      rw [e, hΦmul, h1, map_one, toAdd_one, add_zero]
    have hΦt : ∀ (t : Kˣ) (u : ↥Q), ∃ u' : ↥Q,
        Multiplicative.toAdd (γ u') = ((t : K) ^ 2) • Multiplicative.toAdd (γ u) ∧
          Multiplicative.toAdd (G2q.zBCoord (φ u')) =
            ((t : K) ^ 3) • Multiplicative.toAdd (G2q.zBCoord (φ u)) := by
      intro t u
      obtain ⟨ht, -⟩ := hεN t
      let n : ↥ε.range := ⟨ε (1, t), ⟨(1, t), rfl⟩⟩
      let u' : ↥Q := ⟨ε (1, t) * u * (ε (1, t))⁻¹, hNQ' _ ht u u.2⟩
      refine ⟨u', ?_, ?_⟩
      · rw [hγR (1, t) u u' rfl, sp4RadMat_one, Matrix.one_mulVec]
      · have h1 := hφN n ht u u' rfl
        have hn : ((eR n : ↥(Model.leviB K ⊔ Model.J₄ K)) : ModGL Tag.G2 K) =
            G2q.leviBHom (1, t) := by
          change G2q.leviBHom ((MonoidHom.ofInjective hεinj).symm n) = _
          rw [hsymmε]
        have h2 : (φ u' : ModGL Tag.G2 K) =
            G2q.leviBHom (1, t) * (φ u : ModGL Tag.G2 K) * (G2q.leviBHom (1, t))⁻¹ := by
          rw [h1, hn]
        rw [G2q.zBCoord_conj_leviBHom (1, t) (φ u) (φ u') h2]
        simp
    refine MonoidHom.ext fun v => ?_
    rw [MonoidHom.one_apply]
    obtain ⟨u₀, hu₀0, hu₀1⟩ := exists_ne_ne (by omega : 3 ≤ Nat.card K) (0 : K) 1
    have h1u : (1 : K) + u₀ ≠ 0 := by
      intro h
      apply hu₀1
      calc u₀ = (1 + u₀) + 1 := by
            rw [add_comm (1 : K) u₀, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = 1 := by rw [h, zero_add]
    obtain ⟨v₁, hγ₁, hΦ₁⟩ := hΦt (Units.mk0 u₀ hu₀0) v
    obtain ⟨v₂, hγ₂, hΦ₂⟩ := hΦt (Units.mk0 (1 + u₀) h1u) v
    have hγeq' : γ (v * v₁) = γ v₂ := by
      apply Multiplicative.toAdd.injective
      rw [hγ₂, map_mul, toAdd_mul, hγ₁]
      simp only [Units.val_mk0]
      rw [CharTwo.add_sq, one_pow, add_smul, one_smul]
    have hΦeq := hΦZ _ _ hγeq'
    rw [hΦmul, hΦ₂, hΦ₁] at hΦeq
    simp only [Units.val_mk0] at hΦeq
    have hΦv := eq_zero_of_smul_cube hu₀0 h1u hΦeq
    apply G2q.zBCoord.injective
    rw [map_one]
    exact Multiplicative.toAdd.injective (hΦv.trans toAdd_one.symm)
  have hH1 : CrossedHomPrincipal Q Z ε.range (Model.Y K) (Model.leviB K ⊔ Model.J₄ K) eR :=
    crossedHomPrincipal_of_normal eR hRQ hRZ hRZ' hZ'c hNR hNnorm hN hfixφ
  obtain ⟨θ, ψ, hψQ, hψR, -, -⟩ := exists_vertexIso_special (G' := ModGL Tag.G2 K)
    (Q := Q) (R := ε.range) (Z := Z) (Q' := Model.M K) (R' := Model.leviB K ⊔ Model.J₄ K)
    (Z' := Model.Y K) hRQ hεdisj G2q.leviB_sup_J₄_le_normalizer_M G2q.disjoint_M_leviB_sup_J₄
    hZQ hZc hZ2 hQ2 hRZ hYM (fun z hz x hx => G2q.mul_comm_of_mem_Y_of_mem_M hz hx)
    (fun z hz => G2q.sq_eq_one_of_mem_Y hz) (fun x hx => G2q.sq_mem_Y_of_mem_M hx) hRZ'
    eR fM gY hfR hgR hsqR hH1
  refine ⟨(MulEquiv.subgroupCongr hεsup.symm).trans ψ, fun x => ?_⟩
  obtain ⟨v, hv, hx⟩ := hεdec x
  refine ⟨θ ⟨v, hv⟩, (θ ⟨v, hv⟩).2, ?_⟩
  have hxe : (MulEquiv.subgroupCongr hεsup.symm ⟨x, Subgroup.mem_sup_left x.2⟩ :
      ↥(Q ⊔ ε.range)) = ⟨v, Subgroup.mem_sup_left hv⟩ *
        ⟨ε (α x, 1), Subgroup.mem_sup_right ⟨(α x, 1), rfl⟩⟩ := Subtype.ext hx
  have e1 : ((ψ ⟨v, Subgroup.mem_sup_left hv⟩ :
      ↥(Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K))) : ModGL Tag.G2 K) = θ ⟨v, hv⟩ :=
    hψQ ⟨v, hv⟩
  have e2 : ((ψ ⟨ε (α x, 1), Subgroup.mem_sup_right ⟨(α x, 1), rfl⟩⟩ :
      ↥(Model.M K ⊔ (Model.leviB K ⊔ Model.J₄ K))) : ModGL Tag.G2 K) =
        G2q.leviBHom (α x, 1) := by
    rw [hψR ⟨ε (α x, 1), ⟨(α x, 1), rfl⟩⟩]
    change G2q.leviBHom ((MonoidHom.ofInjective hεinj).symm _) = _
    rw [hsymmε]
  rw [MulEquiv.trans_apply, hxe, map_mul, Subgroup.coe_mul, e1, e2]

end CFSG.Quasithin.F112R.St84

end
