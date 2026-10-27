module

public import CFSG.Quasithin.Vol2.Ch10SecKRSz

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_rho (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (ρ : ↥J →* SL5) (hρ : Function.Surjective ρ)
    (hker : ∀ j : ↥J, ρ j = 1 → ∃ k : ℕ, j ^ 2 ^ k = 1)
    (hU : ∀ j : ↥J, ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (hcen : ∀ j : ↥J, (j : G) ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ↔ ρ j ∈ Q1)
    (h3 : InvStd (piL ρ c.le).range 3)
    (htriv : ∀ x ∈ (piL ρ c.le).range, ∀ v, x • v + v ∈ stdE 5 3)
    (hqX : Nonempty (↥(piL ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL ρ c.le).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hUN : uniSL 5 ≤ Subgroup.normalizer ((piL ρ c.le).range : Set SL5)) : False := by
  have hX3 : (piL ρ c.le).range = X3 := eq_X3_of_E3 h3 htriv hqX hUN
  have hPJ : theta (CE t w) ≤ J := Conf.theta_CE_le_J c h38 h318 h36' hE hK7L5 hVe hq e5 eJ
  have hX := Conf.map_pre_M3_rho c hTw h37 h38 ρ hρ hker hU hcen hPJ h3 htriv hqX hX3
  have hlift : ∀ j : ↥J, (j : G) ^ 3 = 1 → ρ j ∈ Q1 → (j : G) ∈ theta (CE t w) :=
    fun j hj3 hjQ => mem_theta ⟨(hcen j).mpr hjQ, c.J_le j.2⟩ hj3
  have hX3t : ∀ x ∈ pre ρ (theta (CE t w)) (M 3),
      t⁻¹ * x * t⁻¹⁻¹ ∈ pre ρ (theta (CE t w)) (M 3) := fun x hx => by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hx
    rw [hX] at h1
    exact h1
  have hX3t' : ∀ x ∈ pre ρ (theta (CE t w)) (M 3),
      t * x * t⁻¹ ∈ pre ρ (theta (CE t w)) (M 3) := fun x hx => by
    rw [← hX, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hx
    exact hx
  have hRt : ∀ z ∈ theta (pre ρ (theta (CE t w)) (M 3)),
      t⁻¹ * z * t ∈ theta (pre ρ (theta (CE t w)) (M 3)) := fun z hz => by
    have h1 := conj_mem_theta (g := t⁻¹) hX3t hz
    rwa [inv_inv] at h1
  have hRt' : ∀ z ∈ theta (pre ρ (theta (CE t w)) (M 3)),
      t * z * t⁻¹ ∈ theta (pre ρ (theta (CE t w)) (M 3)) := fun z hz =>
    conj_mem_theta hX3t' hz
  have hkerL : ∀ l : ↥L, piL ρ c.le l = 1 → ∃ k : ℕ, l ^ 2 ^ k = 1 := fun l hl => by
    obtain ⟨m, hm⟩ := hker _ hl
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  obtain ⟨d, hd3, hdρ⟩ := exists_three_lift (piL ρ c.le) hkerL
    (hX3 ▸ dS_mem_X3 : dS ∈ (piL ρ c.le).range) dS_pow
  have hdJ : (d : G) ∈ J := c.le d.2
  have hdρ' : ρ ⟨d, hdJ⟩ = dS := hdρ
  have hd3' : (d : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hd3
  have hdR : (d : G) ∈ Subgroup.normalizer
      (theta (pre ρ (theta (CE t w)) (M 3)) : Set G) :=
    mem_normalizer_theta ρ hPJ hlift (d := ⟨d, hdJ⟩) (by rw [hdρ', P0_eq]; exact dS_mem_M1)
  have hd'R : t⁻¹ * (d : G) * t ∈ Subgroup.normalizer
      (theta (pre ρ (theta (CE t w)) (M 3)) : Set G) :=
    mem_normalizer_of_conj_mem fun z hz => by
      have hz1 := hRt _ ((Subgroup.mem_normalizer_iff.mp hdR _).mp (hRt' z hz))
      rwa [show t⁻¹ * ((d : G) * (t * z * t⁻¹) * (d : G)⁻¹) * t =
        t⁻¹ * (d : G) * t * z * (t⁻¹ * (d : G) * t)⁻¹ by group] at hz1
  have hd'3 : (t⁻¹ * (d : G) * t) ^ 3 = 1 := by
    rw [show t⁻¹ * (d : G) * t = t⁻¹ * (d : G) * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hd3']
    group
  have hd'Lt : t⁻¹ * (d : G) * t ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff, show t * (t⁻¹ * (d : G) * t) * t⁻¹ = d by group]
    exact d.2
  have hcomm : (d : G) * (t⁻¹ * d * t) * (d : G)⁻¹ * (t⁻¹ * d * t)⁻¹ ∈ pCoreOf 2 L := by
    have h1 := (pCoreOf 2 L).inv_mem (Conf.comm_mem_of_conjugate c h37 hd'Lt d d.2)
    rwa [show ((t⁻¹ * (d : G) * t) * d * (t⁻¹ * (d : G) * t)⁻¹ * (d : G)⁻¹)⁻¹ =
      (d : G) * (t⁻¹ * d * t) * (d : G)⁻¹ * (t⁻¹ * d * t)⁻¹ by group] at h1
  have hdw : (d : G) ∈ Subgroup.centralizer ({w} : Set G) := c.J_le hdJ
  have hdu : (d : G) ∉ Subgroup.centralizer ({t * w * t⁻¹} : Set G) := fun h => by
    have h1 := (hcen ⟨d, hdJ⟩).mp h
    rw [hdρ'] at h1
    exact dS_mulVec_ne (mem_Q1_iff_mulVec.mpr h1)
  have hd'u : t⁻¹ * (d : G) * t ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) := by
    have h1 := conj_mem_centralizer (g := t⁻¹) hdw
    rwa [inv_inv, Conf.t_inv_conj_w c hTw h37 h38] at h1
  have hd'w : t⁻¹ * (d : G) * t ∉ Subgroup.centralizer ({w} : Set G) := fun h => by
    apply hdu
    have h1 := conj_mem_centralizer (g := t) h
    rwa [show t * (t⁻¹ * (d : G) * t) * t⁻¹ = d by group] at h1
  exact false_of_E27 c.hyp.fsu.qtke (pCoreOf_theta_ne_bot ρ hρ hker hPJ hlift)
    (three_dvd_card_theta ρ hρ hker hPJ hlift) (not_nine_dvd_card_theta ρ hker hPJ)
    (fun x hx => theta_le _ ((theta_le _).trans inf_le_left hx)) hdR hd'R
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hd3' hd'3
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L d.2)
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
      (conjugate_le_normalizer c.hyp c.ht hd'Lt)) hcomm
    ((Conf.pCoreOf_L_le c hTw).trans (Conf.Tw_le_centralizer_u c hTw h37 h38))
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (c.le.trans c.J_le)) hdw hd'u hdu hd'w

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
