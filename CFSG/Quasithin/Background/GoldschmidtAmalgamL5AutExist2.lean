module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutExist
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutRel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmN

variable {D : Type*} [Group D] {G₁ G₂ G₁' G₂' : Subgroup D} {a b s ρ x y : D}

theorem eq_of_same_action {G Q : Subgroup D} {z : D}
    (hC : ∀ g ∈ G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q)
    (hQG : ∀ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hZ : ∀ w ∈ Q, (∀ v ∈ Q, w * v = v * w) → w = 1 ∨ w = z)
    (hzQ : z ∈ Q) (hzc : ∀ v ∈ Q, z * v = v * z) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    {y₁ y₂ : D} (h₁ : y₁ ∈ G) (h₂ : y₂ ∈ G) (h₁3 : y₁ ^ 3 = 1) (h₂3 : y₂ ^ 3 = 1)
    (hact : ∀ q ∈ Q, y₁⁻¹ * q * y₁ = y₂⁻¹ * q * y₂) : y₁ = y₂ := by
  have hcQ : ∀ q ∈ Q, (y₂ * y₁⁻¹) * q = q * (y₂ * y₁⁻¹) := by
    intro q hq
    have e := hact q hq
    have e2 : y₂ * y₁⁻¹ * q * (y₁ * y₂⁻¹) = q := by
      calc y₂ * y₁⁻¹ * q * (y₁ * y₂⁻¹) = y₂ * (y₁⁻¹ * q * y₁) * y₂⁻¹ := by group
        _ = y₂ * (y₂⁻¹ * q * y₂) * y₂⁻¹ := by rw [e]
        _ = q := by group
    calc y₂ * y₁⁻¹ * q = (y₂ * y₁⁻¹ * q * (y₁ * y₂⁻¹)) * (y₂ * y₁⁻¹) := by group
      _ = q * (y₂ * y₁⁻¹) := by rw [e2]
  have hcG : y₂ * y₁⁻¹ ∈ G := G.mul_mem h₂ (G.inv_mem h₁)
  have hcQ' : y₂ * y₁⁻¹ ∈ Q := hC _ hcG hcQ
  rcases hZ _ hcQ' hcQ with h1 | h1
  · exact (mul_inv_eq_one.mp h1).symm
  · exfalso
    have hy₂ : y₂ = z * y₁ := by rw [← h1]; group
    have hzy : y₁ * z * y₁⁻¹ = z := by
      have hmem : y₁ * z * y₁⁻¹ ∈ Q := hQG y₁ h₁ z hzQ
      have hcent : ∀ v ∈ Q, (y₁ * z * y₁⁻¹) * v = v * (y₁ * z * y₁⁻¹) := by
        intro v hv
        have hv' : y₁⁻¹ * v * y₁ ∈ Q := by
          have := hQG y₁⁻¹ (G.inv_mem h₁) v hv
          simpa using this
        have hzv := hzc _ hv'
        calc y₁ * z * y₁⁻¹ * v = y₁ * (z * (y₁⁻¹ * v * y₁)) * y₁⁻¹ := by group
          _ = y₁ * ((y₁⁻¹ * v * y₁) * z) * y₁⁻¹ := by rw [hzv]
          _ = v * (y₁ * z * y₁⁻¹) := by group
      rcases hZ _ hmem hcent with h2 | h2
      · exfalso
        apply hz1
        have : z = y₁⁻¹ * (y₁ * z * y₁⁻¹) * y₁ := by group
        rw [this, h2]; group
      · exact h2
    have hcomm : Commute z y₁ := by
      have : y₁ * z = z * y₁ := by
        calc y₁ * z = (y₁ * z * y₁⁻¹) * y₁ := by group
          _ = z * y₁ := by rw [hzy]
      exact this.symm
    have h3 : (z * y₁) ^ 3 = z := by
      rw [hcomm.mul_pow, h₁3, mul_one]
      calc z ^ 3 = z * z * z := pow_three' z
        _ = z * (z * z) := mul_assoc _ _ _
        _ = z := by rw [hz2, mul_one]
    rw [hy₂, h3] at h₂3
    exact hz1 h₂3

theorem aut_comm_inv {x t : D} (hc : x * t = t * x) : x * t⁻¹ = t⁻¹ * x := by
  calc x * t⁻¹ = t⁻¹ * (t * x) * t⁻¹ := by group
    _ = t⁻¹ * (x * t) * t⁻¹ := by rw [hc]
    _ = t⁻¹ * x := by group

theorem aut_conj_comm_conj {x t g : D} (hc : x * t = t * x) :
    t * (x⁻¹ * g * x) * t⁻¹ = x⁻¹ * (t * g * t⁻¹) * x := by
  have h1 : t * x⁻¹ = x⁻¹ * t := by
    calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
      _ = x⁻¹ * (t * x) * x⁻¹ := by rw [hc]
      _ = x⁻¹ * t := by group
  have h2 := aut_comm_inv hc
  calc t * (x⁻¹ * g * x) * t⁻¹ = (t * x⁻¹) * g * (x * t⁻¹) := by group
    _ = (x⁻¹ * t) * g * (t⁻¹ * x) := by rw [h1, h2]
    _ = x⁻¹ * (t * g * t⁻¹) * x := by group

theorem aut_commute_of_gens {S : Set D} {τ : D} (h : ∀ g ∈ S, g * τ = τ * g) :
    ∀ g ∈ Subgroup.closure S, g * τ = τ * g := by
  have : Subgroup.closure S ≤ Subgroup.centralizer ({τ} : Set D) := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (h g hg).symm
  intro g hg
  have := Subgroup.mem_centralizer_iff.mp (this hg) τ rfl
  exact this.symm

theorem conj_rR_hom {θ Θ : Tr →* Tr} (h1 : rR * θ rA * rR = Θ rA) (h2 : rR * θ rB * rR = Θ rB)
    (h3 : rR * θ rS * rR = Θ rS) (h4 : θ rR = rR) (h4' : Θ rR = rR) :
    ∀ w : Tr, rR * θ w * rR = Θ w := by
  have hinv : rR⁻¹ = rR := inv_eq_of_mul_eq_one_right rR_sq
  let κ : Tr →* Tr := (MulAut.conj rR).toMonoidHom
  have hκ : ∀ g, κ g = rR * g * rR := fun g => by
    show rR * g * rR⁻¹ = _
    rw [hinv]
  have key : κ.comp θ = Θ := by
    apply tr_hom_ext
    · simpa only [MonoidHom.comp_apply, hκ] using h1
    · simpa only [MonoidHom.comp_apply, hκ] using h2
    · simpa only [MonoidHom.comp_apply, hκ] using h3
    · simp only [MonoidHom.comp_apply, hκ, h4, h4', rR_sq, one_mul]
  intro w
  have := congrArg (fun f : Tr →* Tr => f w) key
  simpa only [MonoidHom.comp_apply, hκ] using this

variable [Finite D]

namespace AutHyp

variable (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)

include H

omit [Finite D] in
theorem emb_rA : H.emb rA = a := embR_rA H.hA.toTRel H.hAρ.toRhoRel
omit [Finite D] in
theorem emb_rB : H.emb rB = b := embR_rB H.hA.toTRel H.hAρ.toRhoRel
omit [Finite D] in
theorem emb_rS : H.emb rS = s := embR_rS H.hA.toTRel H.hAρ.toRhoRel
omit [Finite D] in
theorem emb_rR : H.emb rR = ρ := embR_rR H.hA.toTRel H.hAρ.toRhoRel

theorem exists_conjHom {t : D} (ht : t ∈ G₁ ⊓ G₂) :
    ∃ θ : Tr →* Tr, ∀ w : Tr, H.emb (θ w) = t * H.emb w * t⁻¹ := by
  have hmem : ∀ w : Tr, t * H.emb w * t⁻¹ ∈ H.emb.range := by
    intro w
    rw [H.range_emb]
    have hw : H.emb w ∈ G₁' ⊓ G₂' := by rw [← H.range_emb]; exact ⟨w, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (H.normal_T' ht) (H.emb w)).mp hw
  refine ⟨MonoidHom.mk' (fun w => coordOf H.emb (t * H.emb w * t⁻¹)) ?_,
    fun w => emb_coordOf (hmem w)⟩
  intro v w
  apply H.emb_injective
  show H.emb (coordOf H.emb (t * H.emb (v * w) * t⁻¹)) =
    H.emb (coordOf H.emb (t * H.emb v * t⁻¹) * coordOf H.emb (t * H.emb w * t⁻¹))
  have e1 := emb_coordOf (hmem v)
  have e2 := emb_coordOf (hmem w)
  have e3 := emb_coordOf (hmem (v * w))
  rw [e3, map_mul H.emb (coordOf H.emb (t * H.emb v * t⁻¹)) (coordOf H.emb (t * H.emb w * t⁻¹)),
    e1, e2, map_mul H.emb v w]
  group

omit [Finite D] in
theorem conj_mem_Q1 {t : D} (ht : t ∈ G₁ ⊓ G₂) {w : Tr} (hw : inQ1 w) :
    t * H.emb w * t⁻¹ ∈ Q1r.map H.emb := by
  rw [← H.pCore₁]
  have hmem : H.emb w ∈ pCoreOf 2 G₁' := by
    rw [H.pCore₁]; exact Subgroup.mem_map_of_mem _ hw
  have hnorm : G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₁' : Set D) :=
    H.normal₁.trans (normalizer_le_normalizer_pCoreOf 2 G₁')
  exact (Subgroup.mem_normalizer_iff.mp (hnorm ht.1) (H.emb w)).mp hmem

omit [Finite D] in
theorem conjHom_inQ1 {t : D} (ht : t ∈ G₁ ⊓ G₂) {θ : Tr →* Tr}
    (hθ : ∀ w : Tr, H.emb (θ w) = t * H.emb w * t⁻¹) {w : Tr} (hw : inQ1 w) : inQ1 (θ w) := by
  have h := H.conj_mem_Q1 ht hw
  rw [← hθ w] at h
  obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp h
  have := H.emb_injective hvw
  rw [← this]
  exact hv

omit [Finite D] in
theorem inQ1_of_conjHom {t : D} (ht : t ∈ G₁ ⊓ G₂) {θ : Tr →* Tr}
    (hθ : ∀ w : Tr, H.emb (θ w) = t * H.emb w * t⁻¹) {w : Tr} (hw : inQ1 (θ w)) : inQ1 w := by
  have h := H.conj_mem_Q1 ((G₁ ⊓ G₂).inv_mem ht) hw
  have e : t⁻¹ * H.emb (θ w) * t⁻¹⁻¹ = H.emb w := by rw [hθ w]; group
  rw [e] at h
  obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp h
  have := H.emb_injective hvw
  rw [← this]
  exact hv

omit [Finite D] in
theorem conjHom_actA {t : D} (ht : t ∈ G₁ ⊓ G₂) {θ : Tr →* Tr}
    (hθ : ∀ w : Tr, H.emb (θ w) = t * H.emb w * t⁻¹) (hxt : x * t = t * x) :
    ∀ w : Tr, inQ1 w → θ (actA w) = actA (θ w) := by
  intro w hw
  apply H.emb_injective
  have e1 := aRho_conj_embR H.hA H.hAρ w hw
  have e2 := aRho_conj_embR H.hA H.hAρ (θ w) (H.conjHom_inQ1 ht hθ hw)
  rw [hθ (actA w), ← e1, ← e2, hθ w]
  exact aut_conj_comm_conj hxt

omit [Finite D] in
theorem conjHom_rS {t : D} (ht : t ∈ G₁ ⊓ G₂) {θ : Tr →* Tr}
    (hθ : ∀ w : Tr, H.emb (θ w) = t * H.emb w * t⁻¹) (hxt : x * t = t * x) :
    inQ1 (θ rS * rS⁻¹) ∧ actA (θ rS * rS⁻¹) = θ rS * rS⁻¹ := by
  have hq1 : inQ1 (θ rS * rS⁻¹) := by
    rcases Q1_or (θ rS) with h | h
    · exact absurd (H.inQ1_of_conjHom ht hθ h) rS_not_inQ1
    · exact h
  refine ⟨hq1, ?_⟩
  apply H.emb_injective
  rw [← aRho_conj_embR H.hA H.hAρ _ hq1, map_mul, map_inv, hθ rS, H.emb_rS]
  have hx' := aut_comm_inv hxt
  have hσ : x * (t * s * t⁻¹) * x = t * s * t⁻¹ := by
    calc x * (t * s * t⁻¹) * x = (x * t) * s * (t⁻¹ * x) := by group
      _ = (t * x) * s * (x * t⁻¹) := by rw [hxt, hx']
      _ = t * (x * s * x) * t⁻¹ := by group
      _ = t * s * t⁻¹ := by rw [H.hA.hxs]
  have hu : x * ((t * s * t⁻¹) * s⁻¹) * x⁻¹ = (t * s * t⁻¹) * s⁻¹ := by
    calc x * ((t * s * t⁻¹) * s⁻¹) * x⁻¹
        = (x * (t * s * t⁻¹) * x) * (x⁻¹ * s⁻¹ * x⁻¹) := by group
      _ = (t * s * t⁻¹) * (x * s * x)⁻¹ := by rw [hσ]; group
      _ = (t * s * t⁻¹) * s⁻¹ := by rw [H.hA.hxs]
  have key : x⁻¹ * (x * ((t * s * t⁻¹) * s⁻¹) * x⁻¹) * x = (t * s * t⁻¹) * s⁻¹ := by group
  rw [hu] at key
  exact key

end AutHyp

namespace AutHyp

variable (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)

include H

omit [Finite D] in
theorem rho_mem_pCore' : ρ ∈ pCoreOf 2 G₁' := by
  have h := Subgroup.mem_map_of_mem H.emb (show rR ∈ Q1r from rR_inQ1)
  rw [H.emb_rR, ← H.pCore₁] at h
  exact h

theorem rho_mem_pCore : ρ ∈ pCoreOf 2 G₁ := by
  have h2 : pCoreOf 2 G₁' ≤ pCoreOf 2 G₁ := by
    rw [← pCoreOf_inf_eq_of_relIndex_two H.le₁ H.idx₁]; exact inf_le_left
  exact h2 H.rho_mem_pCore'

omit [Finite D] in
theorem rho_mem_G₁' : ρ ∈ G₁' := pCoreOf_le 2 G₁' H.rho_mem_pCore'

omit [Finite D] in
theorem rho_comm : x * ρ = ρ * x := (aRho_comm H.hAρ).symm

theorem rho_mem_T : ρ ∈ G₁ ⊓ G₂ := H.amalgam.pCoreOf_left_le H.rho_mem_pCore

theorem exists_tau_norm : ∃ τ : D, τ ∈ G₁ ⊓ G₂ ∧ τ ∈ pCoreOf 2 G₁ ∧ τ ∉ G₁' ∧ x * τ = τ * x ∧
    ∃ Θ : Tr →* Tr, (Θ = MonoidHom.id Tr ∨ Θ = thetaStd) ∧
      ∀ w : Tr, τ * H.emb w * τ⁻¹ = H.emb (Θ w) := by
  obtain ⟨τ₁, hτ₁P, hτ₁G, hτ₁x⟩ := H.exists_tau₁
  have hτ₁T : τ₁ ∈ G₁ ⊓ G₂ := H.amalgam.pCoreOf_left_le hτ₁P
  have hxτ₁ : x * τ₁ = τ₁ * x := by
    calc x * τ₁ = (x * τ₁ * x⁻¹) * x := by group
      _ = τ₁ * x := by rw [hτ₁x]
  obtain ⟨θ, hθ⟩ := H.exists_conjHom hτ₁T
  have hinjθ : Function.Injective θ := by
    intro w v hwv
    apply H.emb_injective
    have h1 := hθ w
    have h2 := hθ v
    rw [hwv] at h1
    have h3 : τ₁ * H.emb w * τ₁⁻¹ = τ₁ * H.emb v * τ₁⁻¹ := h1.symm.trans h2
    exact mul_left_cancel (mul_right_cancel h3)
  have hact := H.conjHom_actA hτ₁T hθ hxτ₁
  have hAB : actA (θ rA) = θ rB := by
    have := hact rA rA_inQ1
    rw [actA_rA] at this
    exact this.symm
  have hBB : actA (θ rB) = (θ rA)⁻¹ * (θ rB)⁻¹ := by
    have := hact rB rB_inQ1
    rw [actA_rB, map_mul, map_inv, map_inv] at this
    exact this.symm
  have hRR : actA (θ rR) = θ rR := by
    have := hact rR rR_inQ1
    rw [actA_rR] at this
    exact this.symm
  obtain ⟨hq1, hq2⟩ := H.conjHom_rS hτ₁T hθ hxτ₁
  have hts : θ rS * rS⁻¹ * rS = θ rS := inv_mul_cancel_right _ _
  have hcls := classify_tau (θ rA) (H.conjHom_inQ1 hτ₁T hθ rA_inQ1)
    (by rw [← map_pow, rA_pow_four, map_one])
    (fun h => rA_sq_ne_one (hinjθ (by rw [map_mul, h, map_one])))
    (θ rB) hAB (by rw [← map_pow, rB_pow_four, map_one])
    (by rw [← map_mul, ← map_mul, rA_mul_rB]) hBB
    (θ rR) (H.conjHom_inQ1 hτ₁T hθ rR_inQ1) hRR (by rw [← map_mul, rR_sq, map_one])
    (by rw [← map_mul, ← map_mul, rR_rA_rR, map_inv])
    (by rw [← map_mul, ← map_mul, rR_rB_rR, map_inv])
    (θ rS * rS⁻¹) hq1 hq2 (by rw [hts, ← map_mul, rS_sq, map_one])
    (by rw [hts, ← map_mul, ← map_mul, rS_rA_rS])
    (by rw [hts, ← map_mul, ← map_mul, rS_rB_rS])
    (by rw [hts, ← map_mul, ← map_mul, rR_rS_rR])
  rw [hts] at hcls
  obtain ⟨c, hc, Θ, hΘ, hcΘ⟩ : ∃ c : D, (c = 1 ∨ c = ρ) ∧ ∃ Θ : Tr →* Tr,
      (Θ = MonoidHom.id Tr ∨ Θ = thetaStd) ∧ ∀ w : Tr, c * H.emb (θ w) * c⁻¹ = H.emb (Θ w) := by
    rcases hcls with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
    · have hid : θ = MonoidHom.id Tr := tr_hom_ext e1 e2 e3 e4
      refine ⟨1, Or.inl rfl, MonoidHom.id Tr, Or.inl rfl, fun w => ?_⟩
      rw [hid]; simp
    · have hid := conj_rR_hom (θ := θ) (Θ := MonoidHom.id Tr) e1 e2 e3 e4 rfl
      refine ⟨ρ, Or.inr rfl, MonoidHom.id Tr, Or.inl rfl, fun w => ?_⟩
      have hRinv : rR⁻¹ = rR := inv_eq_of_mul_eq_one_right rR_sq
      have : H.emb (rR * θ w * rR⁻¹) = ρ * H.emb (θ w) * ρ⁻¹ := by
        rw [map_mul, map_mul, map_inv, H.emb_rR]
      rw [← this, hRinv, hid w]
    · have hstd : θ = thetaStd := tr_hom_ext e1 e2 e3 e4
      refine ⟨1, Or.inl rfl, thetaStd, Or.inr rfl, fun w => ?_⟩
      rw [hstd]; simp
    · have hst := conj_rR_hom (θ := θ) (Θ := thetaStd) e1 e2 e3 e4 thetaStd_rR
      refine ⟨ρ, Or.inr rfl, thetaStd, Or.inr rfl, fun w => ?_⟩
      have hRinv : rR⁻¹ = rR := inv_eq_of_mul_eq_one_right rR_sq
      have : H.emb (rR * θ w * rR⁻¹) = ρ * H.emb (θ w) * ρ⁻¹ := by
        rw [map_mul, map_mul, map_inv, H.emb_rR]
      rw [← this, hRinv, hst w]
  have hcT : c ∈ G₁ ⊓ G₂ := by
    rcases hc with rfl | rfl
    · exact (G₁ ⊓ G₂).one_mem
    · exact H.rho_mem_T
  have hcP : c ∈ pCoreOf 2 G₁ := by
    rcases hc with rfl | rfl
    · exact (pCoreOf 2 G₁).one_mem
    · exact H.rho_mem_pCore
  have hcG : c ∈ G₁' := by
    rcases hc with rfl | rfl
    · exact G₁'.one_mem
    · exact H.rho_mem_G₁'
  have hcx : x * c = c * x := by
    rcases hc with rfl | rfl
    · simp
    · exact H.rho_comm
  refine ⟨c * τ₁, (G₁ ⊓ G₂).mul_mem hcT hτ₁T, (pCoreOf 2 G₁).mul_mem hcP hτ₁P, ?_, ?_, Θ, hΘ,
    fun w => ?_⟩
  · intro hmem
    apply hτ₁G
    have := G₁'.mul_mem (G₁'.inv_mem hcG) hmem
    simpa using this
  · calc x * (c * τ₁) = (x * c) * τ₁ := by group
      _ = c * x * τ₁ := by rw [hcx]
      _ = c * (x * τ₁) := by group
      _ = c * (τ₁ * x) := by rw [hxτ₁]
      _ = c * τ₁ * x := by group
  · rw [← hcΘ w, hθ w]
    group

omit [Finite D] in
theorem eq_of_action {y₁ y₂ : D} (h₁ : y₁ ∈ G₂') (h₂ : y₂ ∈ G₂') (h₁3 : y₁ ^ 3 = 1)
    (h₂3 : y₂ ^ 3 = 1)
    (hact : ∀ w : Tr, inQ2 w → y₁⁻¹ * H.emb w * y₁ = y₂⁻¹ * H.emb w * y₂) : y₁ = y₂ := by
  refine eq_of_same_action (G := G₂') (Q := pCoreOf 2 G₂') (z := H.emb zR) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h₁ h₂ h₁3 h₂3 ?_
  · intro g hg hc
    apply H.vertex₂.charTwo
    exact ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => (hc q hq).symm⟩
  · intro g hg q hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂' hg) q).mp hq
  · intro w hw hcent
    rw [H.pCore₂] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have : w₀ = 1 ∨ w₀ = zR := by
      apply Q2_center w₀ hw₀
      intro v hv
      apply H.emb_injective
      rw [map_mul, map_mul]
      exact hcent (H.emb v) (by rw [H.pCore₂]; exact Subgroup.mem_map_of_mem _ hv)
    rcases this with rfl | rfl
    · left; exact map_one _
    · right; rfl
  · rw [H.pCore₂]; exact Subgroup.mem_map_of_mem _ zR_mem_Q2
  · intro v hv
    rw [H.pCore₂] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul, ← map_mul, zR_central]
  · intro h
    apply zR_ne_one
    apply H.emb_injective
    rw [h, map_one]
  · rw [← map_mul, zR_sq, map_one]
  · intro q hq
    rw [H.pCore₂] at hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    exact hact w hw

omit [Finite D] in
theorem conj_y_mem {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) : τ * y * τ⁻¹ ∈ G₂' :=
  (Subgroup.mem_normalizer_iff.mp (H.normal₂ hτT.2) y).mp H.y_mem

omit [Finite D] in
theorem conj_y_cube {τ : D} : (τ * y * τ⁻¹) ^ 3 = 1 := by
  rw [conj_pow, H.hB.hy]
  group

omit [Finite D] in
theorem tau_y_of_id {τ : D} (hτT : τ ∈ G₁ ⊓ G₂)
    (hconj : ∀ w : Tr, τ * H.emb w * τ⁻¹ = H.emb w) : τ * y * τ⁻¹ = y := by
  have hspec := H.hB.vertexSpec H.hA.toTRel H.hAρ.toRhoRel H.emb_injective
  refine (H.eq_of_action H.y_mem (H.conj_y_mem hτT) H.hB.hy H.conj_y_cube ?_).symm
  intro w hw
  have e1 : y⁻¹ * H.emb w * y = H.emb (Fq alpha5 w) := hspec.conj w hw
  have hτ1 : τ⁻¹ * H.emb w * τ = H.emb w := by
    calc τ⁻¹ * H.emb w * τ = τ⁻¹ * (τ * H.emb w * τ⁻¹) * τ := by rw [hconj w]
      _ = H.emb w := by group
  calc y⁻¹ * H.emb w * y = H.emb (Fq alpha5 w) := e1
    _ = τ * H.emb (Fq alpha5 w) * τ⁻¹ := (hconj _).symm
    _ = τ * (y⁻¹ * H.emb w * y) * τ⁻¹ := by rw [e1]
    _ = τ * (y⁻¹ * (τ⁻¹ * H.emb w * τ) * y) * τ⁻¹ := by rw [hτ1]
    _ = (τ * y * τ⁻¹)⁻¹ * H.emb w * (τ * y * τ⁻¹) := by group

omit [Finite D] in
theorem tau_y_of_std {τ : D} (hτT : τ ∈ G₁ ⊓ G₂)
    (hconj : ∀ w : Tr, τ * H.emb w * τ⁻¹ = H.emb (thetaStd w)) : τ * y * τ⁻¹ = y⁻¹ := by
  have hspec := H.hB.vertexSpec H.hA.toTRel H.hAρ.toRhoRel H.emb_injective
  have hy₁3 : (y⁻¹) ^ 3 = 1 := by rw [inv_pow, H.hB.hy, inv_one]
  refine (H.eq_of_action (G₂'.inv_mem H.y_mem) (H.conj_y_mem hτT) hy₁3 H.conj_y_cube ?_).symm
  intro w' hw'
  have e1 : y * H.emb w' * y⁻¹ = H.emb (Fq alpha5 (Fq alpha5 w')) := hspec.conj_pos hw'
  have hwQ : inQ2 (thetaStd w') := thetaStd_Q2 w' hw'
  have hθw : thetaStd (thetaStd w') = w' := thetaStd_invol w'
  have hτ1 : τ⁻¹ * H.emb w' * τ = H.emb (thetaStd w') := by
    have h := hconj (thetaStd w')
    rw [hθw] at h
    calc τ⁻¹ * H.emb w' * τ = τ⁻¹ * (τ * H.emb (thetaStd w') * τ⁻¹) * τ := by rw [h]
      _ = H.emb (thetaStd w') := by group
  calc (y⁻¹)⁻¹ * H.emb w' * y⁻¹ = y * H.emb w' * y⁻¹ := by group
    _ = H.emb (Fq alpha5 (Fq alpha5 w')) := e1
    _ = H.emb (thetaStd (Fq alpha5 (thetaStd w'))) := by
      rw [thetaStd_alpha _ hwQ, hθw]
    _ = τ * H.emb (Fq alpha5 (thetaStd w')) * τ⁻¹ := (hconj _).symm
    _ = τ * (y⁻¹ * H.emb (thetaStd w') * y) * τ⁻¹ := by rw [hspec.conj _ hwQ]
    _ = τ * (y⁻¹ * (τ⁻¹ * H.emb w' * τ) * y) * τ⁻¹ := by rw [hτ1]
    _ = (τ * y * τ⁻¹)⁻¹ * H.emb w' * (τ * y * τ⁻¹) := by group

theorem not_central {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁')
    (hc₁ : ∀ g ∈ G₁', g * τ = τ * g) (hc₂ : ∀ g ∈ G₂', g * τ = τ * g) : False := by
  have hτG₂ : τ ∉ G₂' := by
    intro h
    have : τ ∈ (G₁ ⊓ G₂) ⊓ G₂' := ⟨hτT, h⟩
    rw [H.T_inf₂] at this
    exact hτG this.1
  have hG₁ : Subgroup.closure ((G₁' : Set D) ∪ {τ}) = G₁ :=
    closure_union_eq_of_relIndex_two H.le₁ H.idx₁ hτT.1 hτG
  have hG₂ : Subgroup.closure ((G₂' : Set D) ∪ {τ}) = G₂ :=
    closure_union_eq_of_relIndex_two H.le₂ H.idx₂ hτT.2 hτG₂
  have hcen : ∀ g : D, g * τ = τ * g →
      g ∈ Subgroup.normalizer (Subgroup.zpowers τ : Set D) := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_right (show Commute g τ from hg) k).symm).eq
  have hN₁ : G₁ ≤ Subgroup.normalizer (Subgroup.zpowers τ : Set D) := by
    intro g hg
    rw [← hG₁] at hg
    refine hcen g (aut_commute_of_gens (S := (G₁' : Set D) ∪ {τ}) (fun g hg => ?_) g hg)
    rcases hg with hg | hg
    · exact hc₁ g hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
  have hN₂ : G₂ ≤ Subgroup.normalizer (Subgroup.zpowers τ : Set D) := by
    intro g hg
    rw [← hG₂] at hg
    refine hcen g (aut_commute_of_gens (S := (G₂' : Set D) ∪ {τ}) (fun g hg => ?_) g hg)
    rcases hg with hg | hg
    · exact hc₂ g hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
  have hbot := eq_bot_of_normalizes_vAmalgam H.amalgam.amalgam (Subgroup.zpowers_le.mpr hτT) hN₁ hN₂
  have hτ1 : τ = 1 := Subgroup.zpowers_eq_bot.mp hbot
  apply hτG
  rw [hτ1]
  exact G₁'.one_mem

theorem exists_tau : ∃ τ : D, TauRel a b s ρ x y τ ∧ τ ∈ G₁ ⊓ G₂ ∧ τ ∉ G₁' := by
  obtain ⟨τ, hτT, hτP, hτG, hτx, Θ, hΘ, hconj⟩ := H.exists_tau_norm
  rcases hΘ with rfl | rfl
  · exfalso
    have hconj' : ∀ w : Tr, τ * H.emb w * τ⁻¹ = H.emb w := fun w => by rw [hconj w]; rfl
    have hy := H.tau_y_of_id hτT hconj'
    have key : ∀ w : Tr, H.emb w * τ = τ * H.emb w := fun w => by
      calc H.emb w * τ = (τ * H.emb w * τ⁻¹) * τ := by rw [hconj' w]
        _ = τ * H.emb w := by group
    have hyτ : y * τ = τ * y := by
      calc y * τ = (τ * y * τ⁻¹) * τ := by rw [hy]
        _ = τ * y := by group
    refine H.not_central hτT hτG ?_ ?_
    · rw [← H.eG₁]
      refine aut_commute_of_gens (fun g hg => ?_)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h | h | h | h
      · rw [h, ← H.emb_rA]; exact key rA
      · rw [h, ← H.emb_rB]; exact key rB
      · rw [h, ← H.emb_rS]; exact key rS
      · rw [h, ← H.emb_rR]; exact key rR
      · rw [h]; exact hτx
    · rw [← H.eG₂]
      refine aut_commute_of_gens (fun g hg => ?_)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h | h | h | h
      · rw [h, ← H.emb_rA]; exact key rA
      · rw [h, ← H.emb_rB]; exact key rB
      · rw [h, ← H.emb_rS]; exact key rS
      · rw [h, ← H.emb_rR]; exact key rR
      · rw [h]; exact hyτ
  · have hy := H.tau_y_of_std hτT hconj
    have hxinvτx : x⁻¹ * τ * x = τ := by
      calc x⁻¹ * τ * x = x⁻¹ * (τ * x) := by group
        _ = x⁻¹ * (x * τ) := by rw [hτx]
        _ = τ := by group
    have hu : τ * τ = 1 := by
      have hτ2P : τ * τ ∈ pCoreOf 2 G₁ := (pCoreOf 2 G₁).mul_mem hτP hτP
      have hτ2T' : τ * τ ∈ G₁' ⊓ G₂' := mul_self_mem_of_relIndex_two H.relIndex_T hτT
      have hτ2 : τ * τ ∈ pCoreOf 2 G₁' := by
        rw [← pCoreOf_inf_eq_of_relIndex_two H.le₁ H.idx₁]
        exact ⟨hτ2P, hτ2T'.1⟩
      rw [H.pCore₁] at hτ2
      obtain ⟨wu, hwu, hwue⟩ := Subgroup.mem_map.mp hτ2
      have hfix : actA wu = wu := by
        apply H.emb_injective
        rw [← aRho_conj_embR H.hA H.hAρ wu hwu, hwue]
        calc x⁻¹ * (τ * τ) * x = (x⁻¹ * τ * x) * (x⁻¹ * τ * x) := by group
          _ = τ * τ := by rw [hxinvτx]
      have hcentral : ∀ w : Tr, wu * w = w * wu := by
        intro w
        apply H.emb_injective
        rw [map_mul, map_mul, hwue]
        have h1 : τ * H.emb w * τ⁻¹ = H.emb (thetaStd w) := hconj w
        have h2 : τ * H.emb (thetaStd w) * τ⁻¹ = H.emb (thetaStd (thetaStd w)) :=
          hconj (thetaStd w)
        rw [thetaStd_invol] at h2
        calc τ * τ * H.emb w = (τ * (τ * H.emb w * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
          _ = H.emb w * (τ * τ) := by rw [h1, h2]
      have hwu1 : wu = 1 := by
        rcases actA_fix wu hwu hfix with h | h
        · exact h
        · exfalso
          rcases Tr_center wu hcentral with h' | h'
          · rw [h] at h'; exact rR_ne_one h'
          · rw [h] at h'; exact rR_ne_zR h'
      rw [← hwue, hwu1, map_one]
    have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hu
    refine ⟨τ, ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_⟩, hτT, hτG⟩
    · have h := hconj rA
      rw [hτinv, thetaStd_rA, map_mul, map_mul, map_inv, H.emb_rA, H.emb_rB] at h
      exact h
    · have h := hconj rB
      rw [hτinv, thetaStd_rB, map_mul, map_mul, H.emb_rA, H.emb_rB] at h
      exact h
    · have h := hconj rS
      rw [hτinv, thetaStd_rS, map_mul, H.emb_rS, H.emb_rR] at h
      exact h
    · have h := hconj rR
      rw [hτinv, thetaStd_rR, H.emb_rR] at h
      exact h
    · calc τ * x * τ = (τ * x) * τ := rfl
        _ = (x * τ) * τ := by rw [← hτx]
        _ = x * (τ * τ) := by group
        _ = x := by rw [hu, mul_one]
    · rw [hτinv] at hy
      exact hy

end AutHyp

end CFSG.Quasithin.F6.GoldAmL5
