module

public import CFSG.Quasithin.Vol2.Ch10SecKRSy
public import CFSG.Quasithin.Vol2.Ch10SecKRSn
public import CFSG.Quasithin.Vol2.Ch10SecKRSr
public import CFSG.Quasithin.Vol2.Ch10SecKRSx

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

theorem cS_not_mem_uniSL : cS ∉ uniSL 5 := fun h => by
  have h21 := h.1 (show (1 : Fin 5) < 2 by decide)
  exact absurd h21 (by decide)

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.map_pre_M3_rho (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (ρ : ↥J →* SL5) (hρ : Function.Surjective ρ)
    (hker : ∀ j : ↥J, ρ j = 1 → ∃ k : ℕ, j ^ 2 ^ k = 1)
    (hU : ∀ j : ↥J, ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (hcen : ∀ j : ↥J, (j : G) ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ↔ ρ j ∈ Q1)
    (hPJ : theta (CE t w) ≤ J) (h3 : InvStd (piL ρ c.le).range 3)
    (htriv : ∀ x ∈ (piL ρ c.le).range, ∀ v, x • v + v ∈ stdE 5 3)
    (hqX : Nonempty (↥(piL ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL ρ c.le).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hX3 : (piL ρ c.le).range = X3) :
    (pre ρ (theta (CE t w)) (M 3)).map (MulAut.conj t⁻¹).toMonoidHom =
      pre ρ (theta (CE t w)) (M 3) := by
  have hlift : ∀ j : ↥J, (j : G) ^ 3 = 1 → ρ j ∈ Q1 → (j : G) ∈ theta (CE t w) :=
    fun j hj3 hjQ => mem_theta ⟨(hcen j).mpr hjQ, c.J_le j.2⟩ hj3
  have hQ : img ρ (theta (CE t w)) = Q1 := img_eq_Q1 ρ hρ hker hlift (by
    rintro _ ⟨⟨x, hxJ⟩, hx, rfl⟩
    exact (hcen ⟨x, hxJ⟩).mp (theta_le _ (Subgroup.mem_subgroupOf.mp hx)).1)
  have hPx : ∀ x, t * x * t⁻¹ ∈ theta (CE t w) ↔ x ∈ theta (CE t w) := fun x => by
    refine ⟨fun h => ?_, Conf.conj_mem_theta_CE' c hTw h37 h38⟩
    have h1 := Conf.conj_mem_theta_CE c hTw h37 h38 h
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h1
  have hσP : (theta (CE t w)).map (MulAut.conj t⁻¹).toMonoidHom = theta (CE t w) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, hPx]
  have hSmem : ∀ x, x ∈ pre ρ (theta (CE t w)) (uniSL 5) ↔
      x ∈ theta (CE t w) ∧ x ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := fun x => by
    rw [mem_pre hPJ]
    exact ⟨fun ⟨hxP, hxU⟩ => ⟨hxP, (hU ⟨x, hPJ hxP⟩).mp hxU⟩,
      fun ⟨hxP, hxT⟩ => ⟨hxP, (hU ⟨x, hPJ hxP⟩).mpr hxT⟩⟩
  have hTwN := Conf.t_mem_normalizer_Tw c hTw h37 h38
  have hσS : (pre ρ (theta (CE t w)) (uniSL 5)).map (MulAut.conj t⁻¹).toMonoidHom =
      pre ρ (theta (CE t w)) (uniSL 5) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, hSmem, hSmem, hPx,
      ← Subgroup.mem_normalizer_iff.mp hTwN x]
  have hkerL : ∀ l : ↥L, piL ρ c.le l = 1 → ∃ k : ℕ, l ^ 2 ^ k = 1 := fun l hl => by
    obtain ⟨m, hm⟩ := hker _ hl
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  obtain ⟨c₁, hc₁3, hc₁ρ⟩ := exists_three_lift (piL ρ c.le) hkerL
    (hX3 ▸ cS_mem_X3 : cS ∈ (piL ρ c.le).range) cS_pow
  have hc₁J : (c₁ : G) ∈ J := c.le c₁.2
  have hc₁ρ' : ρ ⟨c₁, hc₁J⟩ = cS := hc₁ρ
  have hc₁3' : (c₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hc₁3
  have hc₁P : (c₁ : G) ∈ theta (CE t w) := hlift ⟨c₁, hc₁J⟩ hc₁3' (hc₁ρ' ▸ cS_mem_Q1)
  have hc₁2 : (c₁ : G) ∈ pre ρ (theta (CE t w)) (M 2) :=
    (mem_pre hPJ).mpr ⟨hc₁P, by
      show ρ ⟨c₁, hc₁J⟩ ∈ M 2
      rw [hc₁ρ']
      exact mem_M2_of_X3 cS_mem_X3 cS_mem_Q1⟩
  have hc₁S : (c₁ : G) ∉ pre ρ (theta (CE t w)) (uniSL 5) := fun h => by
    obtain ⟨_, hU'⟩ := (mem_pre hPJ).mp h
    have h1 : ρ ⟨c₁, hc₁J⟩ ∈ uniSL 5 := hU'
    rw [hc₁ρ'] at h1
    exact cS_not_mem_uniSL h1
  have hd₁P : t⁻¹ * (c₁ : G) * t ∈ theta (CE t w) := Conf.conj_mem_theta_CE c hTw h37 h38 hc₁P
  have hd₁J : t⁻¹ * (c₁ : G) * t ∈ J := hPJ hd₁P
  have hd₁Lt : t⁻¹ * (c₁ : G) * t ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff, show t * (t⁻¹ * (c₁ : G) * t) * t⁻¹ = c₁ by group]
    exact c₁.2
  have hd₁N := rho_mem_normalizer ρ c.le hd₁J (conjugate_le_normalizer c.hyp c.ht hd₁Lt)
  have hd₁c := rho_comm_mem_pCoreOf ρ c.le hd₁J (Conf.comm_mem_of_conjugate c h37 hd₁Lt)
  obtain ⟨-, hd₁fix⟩ := normalizer_E3 h3 htriv hqX hd₁N hd₁c
  have hc₁4 : t⁻¹ * (c₁ : G) * t ∈ pre ρ (theta (CE t w)) (M 4) :=
    (mem_pre hPJ).mpr ⟨hd₁P, mem_M4_of_fix hd₁fix⟩
  have hd₂P : t⁻¹ * (t⁻¹ * (c₁ : G) * t) * t ∈ theta (CE t w) :=
    Conf.conj_mem_theta_CE c hTw h37 h38 hd₁P
  have hd₂J : t⁻¹ * (t⁻¹ * (c₁ : G) * t) * t ∈ J := hPJ hd₂P
  have hd₂L : t⁻¹ * (t⁻¹ * (c₁ : G) * t) * t ∈ L := by
    have htt : t * t ∈ T1 T L := hTw ▸ Conf.t_sq_mem c hTw h37 h38
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htt.2) c₁).mp
      c₁.2
    rwa [show (t * t)⁻¹ * (c₁ : G) * (t * t)⁻¹⁻¹ = t⁻¹ * (t⁻¹ * (c₁ : G) * t) * t by
      simp only [mul_inv_rev, inv_inv, mul_assoc]] at h1
  have hd₂X : ρ ⟨_, hd₂J⟩ ∈ X3 := by
    rw [← hX3]
    exact ⟨⟨_, hd₂L⟩, rfl⟩
  have hc₁2' : t⁻¹ * (t⁻¹ * (c₁ : G) * t) * t ∈ pre ρ (theta (CE t w)) (M 2) :=
    (mem_pre hPJ).mpr ⟨hd₂P, mem_M2_of_X3 hd₂X ((hcen ⟨_, hd₂J⟩).mp (theta_le _ hd₂P).1)⟩
  exact map_pre_M3 ρ hPJ hQ hσP hσS hc₁2 hc₁S hc₁4 hc₁2'

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
