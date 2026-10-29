module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep10
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep9B

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_GL_two {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (h : Module.finrank (ZMod 2) N = 2) : Nat.card (N ≃ₗ[ZMod 2] N) = 6 := by
  classical
  haveI : Module.Finite (ZMod 2) N := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) N h
  let e : (N ≃ₗ[ZMod 2] N) ≃* GL (Fin 2) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) N).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
  decide

@[expose] noncomputable def qEquiv {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (P : Submodule (ZMod 2) M) (γ : M ≃ₗ[ZMod 2] M) (hγ : ∀ v, v ∈ P ↔ γ v ∈ P) :
    (M ⧸ P) ≃ₗ[ZMod 2] (M ⧸ P) :=
  Submodule.Quotient.equiv P P γ (by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hγ x).1 hx
    · intro hv
      exact ⟨γ.symm v, (hγ (γ.symm v)).2 (by simpa using hv), by simp⟩)

theorem qEquiv_apply {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (P : Submodule (ZMod 2) M) (γ : M ≃ₗ[ZMod 2] M) (hγ : ∀ v, v ∈ P ↔ γ v ∈ P) (m : M) :
    qEquiv P γ hγ (Submodule.Quotient.mk m) = Submodule.Quotient.mk (γ m) := by
  unfold qEquiv
  rw [Submodule.Quotient.equiv_apply]
  rfl

theorem qEquiv_mul {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (P : Submodule (ZMod 2) M) (γ δ : M ≃ₗ[ZMod 2] M) (hγ : ∀ v, v ∈ P ↔ γ v ∈ P)
    (hδ : ∀ v, v ∈ P ↔ δ v ∈ P) (hγδ : ∀ v, v ∈ P ↔ (γ * δ) v ∈ P) :
    qEquiv P (γ * δ) hγδ = qEquiv P γ hγ * qEquiv P δ hδ := by
  apply LinearEquiv.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => rfl

theorem qEquiv_congr {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (P : Submodule (ZMod 2) M) {γ₁ γ₂ : M ≃ₗ[ZMod 2] M} (heq : γ₁ = γ₂)
    (h₁ : ∀ v, v ∈ P ↔ γ₁ v ∈ P) (h₂ : ∀ v, v ∈ P ↔ γ₂ v ∈ P) :
    qEquiv P γ₁ h₁ = qEquiv P γ₂ h₂ := by
  subst heq
  rfl

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

@[expose] noncomputable def DIEnv.sigmaQ (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G} (hkK : k ∈ K₁)
    (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρ : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a) :
    (Additive ↥E.I ⧸ E.fl) ≃ₗ[ZMod 2] (Additive ↥E.I ⧸ E.fl) :=
  qEquiv E.fl (E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩)
    (E.kap_stab_fl hkK hkN hρ)

theorem DIEnv.sigmaQ_mul (E : DIEnv T L V V₁ V₂ K₁ g D) {k l : G}
    (hkK : k ∈ K₁) (hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρk : D.ρ ⟨k, hkN⟩ (D.π E.a) = D.π E.a)
    (hlK : l ∈ K₁) (hlN : l ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρl : D.ρ ⟨l, hlN⟩ (D.π E.a) = D.π E.a)
    (hklK : k * l ∈ K₁) (hklN : k * l ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hρkl : D.ρ ⟨k * l, hklN⟩ (D.π E.a) = D.π E.a) :
    E.sigmaQ hklK hklN hρkl = E.sigmaQ hkK hkN hρk * E.sigmaQ hlK hlN hρl := by
  unfold DIEnv.sigmaQ
  have hγ : E.kap ⟨D.ρ ⟨k * l, hklN⟩, L128A.HatU.rho_mem_img D hklK hklN⟩ =
      E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ *
        E.kap ⟨D.ρ ⟨l, hlN⟩, L128A.HatU.rho_mem_img D hlK hlN⟩ :=
    (congrArg E.kap (Subtype.ext (map_mul D.ρ ⟨k, hkN⟩ ⟨l, hlN⟩))).trans (map_mul E.kap _ _)
  have h₂ : ∀ v, v ∈ E.fl ↔
      (E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ *
        E.kap ⟨D.ρ ⟨l, hlN⟩, L128A.HatU.rho_mem_img D hlK hlN⟩) v ∈ E.fl := by
    intro v
    rw [← hγ]
    exact E.kap_stab_fl hklK hklN hρkl v
  exact (qEquiv_congr E.fl hγ (E.kap_stab_fl hklK hklN hρkl) h₂).trans
    (qEquiv_mul E.fl _ _ (E.kap_stab_fl hkK hkN hρk) (E.kap_stab_fl hlK hlN hρl) h₂)

@[expose] noncomputable def DIEnv.sigma (E : DIEnv T L V V₁ V₂ K₁ g D) :
    ↥(k0Sub K₁ D (D.π E.a)) →* ((Additive ↥E.I ⧸ E.fl) ≃ₗ[ZMod 2] (Additive ↥E.I ⧸ E.fl)) :=
  MonoidHom.mk'
    (fun k => E.sigmaQ (mem_k0Sub.1 k.2).1 (mem_k0Sub.1 k.2).2.choose
      (mem_k0Sub.1 k.2).2.choose_spec)
    (fun k l => E.sigmaQ_mul (mem_k0Sub.1 k.2).1 _ _ (mem_k0Sub.1 l.2).1 _ _
      (mem_k0Sub.1 (k * l).2).1 _ _)

theorem DIEnv.sigma_apply (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G} (hk : k ∈ k0Sub K₁ D (D.π E.a)) :
    E.sigma ⟨k, hk⟩ = E.sigmaQ (mem_k0Sub.1 hk).1 (mem_k0Sub.1 hk).2.choose
      (mem_k0Sub.1 hk).2.choose_spec := rfl

theorem DIEnv.sigma_one_mem (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    {k : G} (hk : k ∈ k0Sub K₁ D (D.π E.a)) (h : E.sigma ⟨k, hk⟩ = 1) {i : G} (hi : i ∈ E.I) :
    k * i * k⁻¹ * i⁻¹ ∈ E.I ⊓ wcSub T L V V₁ := by
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hk
  have hq : E.sigmaQ hkK hkN hρ = 1 := by
    rw [← E.sigma_apply hk]
    exact h
  have hm : E.sigmaQ hkK hkN hρ (Submodule.Quotient.mk (Additive.ofMul ⟨i, hi⟩)) =
      Submodule.Quotient.mk (Additive.ofMul ⟨i, hi⟩) := by
    rw [hq]
    rfl
  unfold DIEnv.sigmaQ at hm
  rw [qEquiv_apply] at hm
  have hdiff := (Submodule.Quotient.eq E.fl).1 hm
  have hkiI : k * i * k⁻¹ ∈ E.I := (Subgroup.mem_normalizer_iff.1 (E.hKI hkK) i).1 hi
  have hact := E.action hkN (E.hKI hkK) (E.hK₁H hkK) (L128A.HatU.rho_mem_img D hkK hkN)
    (Additive.ofMul ⟨i, hi⟩)
  have hγi : E.kap ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ (Additive.ofMul ⟨i, hi⟩) =
      Additive.ofMul ⟨k * i * k⁻¹, hkiI⟩ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hact
  rw [hγi] at hdiff
  have hval : Additive.ofMul (⟨k * i * k⁻¹, hkiI⟩ * (⟨i, hi⟩ : ↥E.I)⁻¹ : ↥E.I) =
      Additive.ofMul ⟨k * i * k⁻¹, hkiI⟩ - Additive.ofMul ⟨i, hi⟩ := by
    rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hmem : (Additive.ofMul (⟨k * i * k⁻¹, hkiI⟩ * (⟨i, hi⟩ : ↥E.I)⁻¹ : ↥E.I)) ∈ E.fl := by
    rw [hval]
    exact hdiff
  have hmem' := (E.mem_DI_iff h1222 h12213 h1289 h12810 h12813 F2 F3 hpt
    (E.I.mul_mem hkiI (E.I.inv_mem hi))).2 hmem
  exact hmem'

theorem DIEnv.sigma_y0_ne_one (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hy0 : E.y₀ ∈ k0Sub K₁ D (D.π E.a)) : E.sigma ⟨E.y₀, hy0⟩ ≠ 1 := by
  intro h1
  obtain ⟨hyK, hyN, hρ⟩ := mem_k0Sub.1 hy0
  have hyL : E.y₀ ∈ L := (Subgroup.mem_inf.1 E.hy₀).1
  have hyV : E.y₀ ∈ Subgroup.normalizer (V : Set G) := E.hcx.hyp.hyp.irrPlus.2.2.1 hyL
  have hρS : D.ρ ⟨E.y₀, hyN⟩ ∈ stabS E.S := rho_stab_S D E.hSV E.hSπ hyV hyN
  have hpS : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ∈ stabS E.fp := by
    have hmem : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ∈
        kmapOf (D.img K₁) E.kap (stabS E.S) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hρS)
    rw [hpt] at hmem
    exact hmem
  have hlS : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ∈ stabS E.fl := by
    have hmem : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ∈
        kmapOf (D.img K₁) E.kap (stabS (Submodule.span (ZMod 2) {D.π E.a})) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (mem_stabS_span_of_fix hρ))
    rw [E.hY₁] at hmem
    exact hmem
  have hy3 : E.y₀ ^ 3 = 1 := by
    rw [← E.hy₀3]
    exact pow_orderOf_eq_one _
  have hh1 : (⟨E.y₀, hyN⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hy3)
  have hρ3 : (D.ρ ⟨E.y₀, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow, hh1, map_one]
  have hγ3 : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ^ 3 = 1 := by
    have hk3 : (⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ : ↥(D.img K₁)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hρ3)
    rw [← map_pow, hk3, map_one]
  have hγ1 : E.kap ⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ ≠ 1 := by
    intro h
    have hk : (⟨D.ρ ⟨E.y₀, hyN⟩, L128A.HatU.rho_mem_img D hyK hyN⟩ : ↥(D.img K₁)) = 1 :=
      E.kap.injective (h.trans (map_one E.kap).symm)
    have hρ1 : D.ρ ⟨E.y₀, hyN⟩ = 1 := congrArg Subtype.val hk
    exact order_three_not_mem_two_group (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
      ((E.hker E.y₀ hyK hyN).1 hρ1) E.hy₀3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord := orderOf_eq_prime hγ3 hγ1
  have hF := F3 (Additive ↥E.I) E.hM E.fp E.fl E.fPl E.hp E.hℓ E.hPl E.hpℓ E.hℓPl _ hord
  have hF' := (hF.1 hpS hlS).2.1
  have hall : ∀ v : Additive ↥E.I, v ∈ E.fl := by
    intro v
    apply hF'
    have hq : E.sigmaQ hyK hyN hρ = 1 := by
      rw [← E.sigma_apply hy0]
      exact h1
    have hm : E.sigmaQ hyK hyN hρ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
      rw [hq]
      rfl
    unfold DIEnv.sigmaQ at hm
    rw [qEquiv_apply] at hm
    exact (Submodule.Quotient.eq E.fl).1 hm
  have htop : E.fl = ⊤ := eq_top_iff.2 (fun x _ => hall x)
  have hfin := E.hℓ
  rw [htop, finrank_top, E.hM] at hfin
  norm_num at hfin

theorem DIEnv.sigma_pow_three (E : DIEnv T L V V₁ V₂ K₁ g D) {h : G}
    (hhK : h ∈ k0Sub K₁ D (D.π E.a)) (k : ℕ) (hord : orderOf h = 3 ^ k) :
    E.sigma ⟨h, hhK⟩ ^ 3 = 1 := by
  have hfr : Module.finrank (ZMod 2) (Additive ↥E.I ⧸ E.fl) = 2 := by
    have := Submodule.finrank_quotient_add_finrank E.fl
    rw [E.hM, E.hℓ] at this
    omega
  have hpow : h ^ (3 ^ k) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one h
  have hσpow : E.sigma ⟨h, hhK⟩ ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have h1 : (⟨h, hhK⟩ : ↥(k0Sub K₁ D (D.π E.a))) ^ (3 ^ k) = 1 :=
      Subtype.ext (by simpa using hpow)
    rw [h1, map_one]
  have hd1 : orderOf (E.sigma ⟨h, hhK⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hσpow
  have hd2 : orderOf (E.sigma ⟨h, hhK⟩) ∣ 6 := by
    haveI : Finite (Additive ↥E.I) := (inferInstance : Finite ↥E.I)
    haveI : Finite (Additive ↥E.I ⧸ E.fl) :=
      Finite.of_surjective (Submodule.Quotient.mk : Additive ↥E.I → _)
        (Submodule.Quotient.mk_surjective _)
    have := orderOf_dvd_natCard (E.sigma ⟨h, hhK⟩)
    rwa [card_GL_two hfr] at this
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
  have hj1 : j ≤ 1 := by
    by_contra hc
    push Not at hc
    have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hc
    rw [← hjeq] at h9
    have h96 := dvd_trans h9 hd2
    norm_num at h96
  have hd3 : orderOf (E.sigma ⟨h, hhK⟩) ∣ 3 := by
    rw [hjeq]
    have : 3 ^ j ∣ 3 ^ 1 := pow_dvd_pow 3 hj1
    simpa using this
  exact orderOf_dvd_iff_pow_eq_one.1 hd3

end Env

end CFSG.Quasithin.H13.C1294
