module

public import CFSG.Quasithin.H13.AS91Sec5ResCore
public import CFSG.Quasithin.H13.AS91Sec5ResFacts

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem card_T : Nat.card (c.T : Subgroup G) = 2 ^ 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sylow.card_eq_multiplicity (c.T.subtype c.T_le)
  have hf : (Nat.card c.G13).factorization 2 = 21 := by
    rw [c.card_G13, show (2 ^ 13 * 3 * (2 ^ 4 * 720) : ℕ) = 2 ^ 21 * 135 by norm_num,
      Nat.factorization_mul (by norm_num : (2 : ℕ) ^ 21 ≠ 0) (by norm_num : (135 : ℕ) ≠ 0),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 135)]
  rw [hf] at h
  have h' : Nat.card ((c.T : Subgroup G).subgroupOf c.G13) = 2 ^ 21 := h
  rw [← h']
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.T_le).toEquiv.symm

private theorem T_le_G1 : (c.T : Subgroup G) ≤ c.G1 := c.T_le.trans (c.G13_le_inf.trans inf_le_left)

theorem T_le_G3 : (c.T : Subgroup G) ≤ c.G3 := c.T_le.trans (c.G13_le_inf.trans inf_le_right)

theorem card_map_T (D : c.ToddCore) :
    Nat.card ↥(((c.T : Subgroup G).subgroupOf c.G1).map D.φ) = 2 ^ 10 := by
  have h := Subgroup.card_ker_mul_card_range
    (D.φ.domRestrict ((c.T : Subgroup G).subgroupOf c.G1))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, D.ker_eq] at h
  have hET : c.E.subgroupOf c.G1 ≤ (c.T : Subgroup G).subgroupOf c.G1 := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (c.E_le_T (Subgroup.mem_subgroupOf.mp hx))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.E_le_G1).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.T_le_G1).toEquiv, c.card_E, c.card_T,
    show (2 : ℕ) ^ 21 = 2 ^ 11 * 2 ^ 10 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

namespace ToddCore

variable {c} (D : c.ToddCore)

@[expose] noncomputable def φA : ↥c.G1 →* ↥AutPerm := D.φ.codRestrict AutPerm D.φ_mem

theorem ker_φA : D.φA.ker = c.E.subgroupOf c.G1 := by
  rw [ToddCore.φA, MonoidHom.ker_codRestrict, D.ker_eq]

theorem φA_surjective : Function.Surjective D.φA := by
  intro σ
  have hσ : (σ : Equiv.Perm (Fin 24)) ∈ D.φ.range := by
    rw [D.range_eq]
    exact σ.2
  obtain ⟨h, hh⟩ := hσ
  exact ⟨h, Subtype.ext hh⟩

end ToddCore

theorem card_map_G12 (D : c.ToddCore) :
    Nat.card ↥(((c.G1 ⊓ c.G2).subgroupOf c.G1).map D.φA) = 64512 := by
  have h := Subgroup.card_ker_mul_card_range (D.φA.domRestrict ((c.G1 ⊓ c.G2).subgroupOf c.G1))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, D.ker_φA] at h
  have hEH : c.E.subgroupOf c.G1 ≤ (c.G1 ⊓ c.G2).subgroupOf c.G1 := fun x hx =>
    Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨x.2, c.E_le_G2 (Subgroup.mem_subgroupOf.mp hx)⟩)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.E_le_G1).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : c.G1 ⊓ c.G2 ≤ c.G1)).toEquiv,
    c.card_E, c.card_G1_inf_G2, show (2 : ℕ) ^ 17 * 1008 = 2 ^ 11 * 64512 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem resM24T_nonempty : Nonempty (ResM24T c) := by
  classical
  obtain ⟨D⟩ := c.toddCore_nonempty
  have hz1 : z ≠ 1 := fun h => c.S.z_ne_one (c.S_z.trans h)
  have hconj : ∀ (h : ↥c.G1) (a : G) (ha : a ∈ c.E),
      D.todd ⟨(h : G) * a * (h : G)⁻¹, c.conj_mem_E h ha⟩ =
        rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩ (D.todd ⟨a, ha⟩) :=
    fun h a ha => D.todd_equiv h ⟨a, ha⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup S24, P = ((c.T : Subgroup G).subgroupOf c.G1).map D.φ :=
    ⟨_, rfl⟩
  have hPle : P ≤ M24g := by
    rw [hP, ← D.range_eq]
    exact Subgroup.map_le_range _ _
  have hPcard : Nat.card P = 2 ^ 10 := by rw [hP]; exact c.card_map_T D
  have hmemP : ∀ σ ∈ P, ∃ t : ↥c.G1, (t : G) ∈ (c.T : Subgroup G) ∧ D.φ t = σ := by
    intro σ hσ
    rw [hP] at hσ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hσ
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩
  obtain ⟨ez, hez⟩ : ∃ w : W11, w = D.todd ⟨z, c.z_mem_E⟩ := ⟨_, rfl⟩
  have hez1 : ez ≠ 1 := by
    rw [hez]
    intro h
    apply hz1
    have h' : (⟨z, c.z_mem_E⟩ : ↥c.E) = 1 := D.todd.injective (h.trans (map_one D.todd).symm)
    exact congrArg Subtype.val h'
  obtain ⟨U, hU, hfix⟩ := M24G.fix_sylow P hPle hPcard
  have hezfix : ∀ (σ : S24) (hσ : σ ∈ P), rho11 AutPerm le_rfl ⟨σ, hPle hσ⟩ ez = ez := by
    intro σ hσ
    obtain ⟨t, ht, rfl⟩ := hmemP σ hσ
    have htz : (t : G) * z * (t : G)⁻¹ = z := by
      simpa using c.G3_comm_z (inv_mem (c.T_le_G3 ht))
    show rho11 AutPerm le_rfl ⟨D.φ t, D.φ_mem t⟩ ez = ez
    rw [hez, ← hconj t z c.z_mem_E]
    congr 1
    exact Subtype.ext htz
  have hezU : ez = M24G.sextClass U := ((hfix ez).1 hezfix).resolve_left hez1
  have hZE := c.Z_le_E
  obtain ⟨V, hV⟩ : ∃ V : Subgroup W11, V = (c.Z.subgroupOf c.E).map D.todd.toMonoidHom :=
    ⟨_, rfl⟩
  have hmemV : ∀ (a : G) (ha : a ∈ c.E), D.todd ⟨a, ha⟩ ∈ V ↔ a ∈ c.Z := by
    intro a ha
    rw [hV, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hbe⟩
      have hbe' : D.todd b = D.todd ⟨a, ha⟩ := hbe
      have hb' : b = ⟨a, ha⟩ := D.todd.injective hbe'
      subst hb'
      exact Subgroup.mem_subgroupOf.mp hb
    · intro haZ
      exact ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr haZ, rfl⟩
  have hVall : ∀ v ∈ V, ∃ (a : G) (ha : a ∈ c.E), a ∈ c.Z ∧ D.todd ⟨a, ha⟩ = v := by
    intro v hv
    rw [hV] at hv
    obtain ⟨⟨a, ha⟩, haZ, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨a, ha, Subgroup.mem_subgroupOf.mp haZ, rfl⟩
  have hVcard : Nat.card V = 8 := by
    have hinjT : Function.Injective D.todd.toMonoidHom := D.todd.injective
    rw [hV, Subgroup.card_map_of_injective hinjT,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv, c.card_Z]
  have hsext : ∀ v ∈ V, v ≠ 1 → ∃ U', IsSextet U' ∧ M24G.sextClass U' = v := by
    intro v hv hv1
    obtain ⟨a, haE, haZ, rfl⟩ := hVall v hv
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hv1 (by rw [show (⟨1, haE⟩ : ↥c.E) = 1 from rfl, map_one])
    obtain ⟨k, hk, hka⟩ := c.exists_K_conj c.z_mem_Z haZ hz1 ha1
    refine ⟨D.φ ⟨k, c.K_le_G1 hk⟩ • U,
      (M24G.isSextet_smul_iff (D.φ_mem ⟨k, c.K_le_G1 hk⟩)).2 hU, ?_⟩
    rw [M24G.sextClass_smul (D.φ_mem ⟨k, c.K_le_G1 hk⟩) hU, ← hezU, hez,
      ← hconj ⟨k, c.K_le_G1 hk⟩ z c.z_mem_E]
    congr 1
    exact Subtype.ext hka
  have hinv : ∀ (σ : S24) (hσ : σ ∈ P), ∀ v ∈ V, rho11 AutPerm le_rfl ⟨σ, hPle hσ⟩ v ∈ V := by
    intro σ hσ v hv
    obtain ⟨t, ht, rfl⟩ := hmemP σ hσ
    obtain ⟨a, haE, haZ, rfl⟩ := hVall v hv
    show rho11 AutPerm le_rfl ⟨D.φ t, D.φ_mem t⟩ (D.todd ⟨a, haE⟩) ∈ V
    rw [← hconj t a haE, hmemV]
    exact (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer ht) a).mp haZ
  have hkey : ∀ h : ↥c.G1,
      V.map (rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩).toMonoidHom ≤ V ↔
        ∀ a ∈ c.Z, (h : G) * a * (h : G)⁻¹ ∈ c.Z := by
    intro h
    constructor
    · intro hle a haZ
      have haE := hZE haZ
      have h2 := hle (Subgroup.mem_map_of_mem _ ((hmemV a haE).2 haZ))
      rw [← hmemV _ (c.conj_mem_E h haE), hconj h a haE]
      exact h2
    · intro hZ w hw
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨a, haE, haZ, rfl⟩ := hVall v hv
      show rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩ (D.todd ⟨a, haE⟩) ∈ V
      rw [← hconj h a haE, hmemV]
      exact hZ a haZ
  have hmapV : ∀ h : ↥c.G1,
      V.map (rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩).toMonoidHom = V ↔ (h : G) ∈ c.G2 := by
    intro h
    constructor
    · intro hEq
      have hfwd := (hkey h).1 hEq.le
      rw [Loc49.G2, Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨hfwd n, fun hn => ?_⟩
      have hinj : Function.Injective
          (fun b : ↥c.Z => (⟨(h : G) * b * (h : G)⁻¹, hfwd b b.2⟩ : ↥c.Z)) := by
        intro b b' hbb
        have h1 : (h : G) * b * (h : G)⁻¹ = (h : G) * b' * (h : G)⁻¹ := congrArg Subtype.val hbb
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
      obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨_, hn⟩
      have h1 : (h : G) * b * (h : G)⁻¹ = (h : G) * n * (h : G)⁻¹ := congrArg Subtype.val hb
      have h2 : (b : G) = n := mul_left_cancel (mul_right_cancel h1)
      rw [← h2]
      exact b.2
    · intro hh
      have hle := (hkey h).2 fun a haZ => (Subgroup.mem_normalizer_iff.mp hh a).mp haZ
      have hinj : Function.Injective (rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩).toMonoidHom :=
        (rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩).injective
      exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge
  have hS : {σ : ↥AutPerm | V.map (rho11 AutPerm le_rfl σ).toMonoidHom = V} =
      ((((c.G1 ⊓ c.G2).subgroupOf c.G1).map D.φA : Subgroup ↥AutPerm) : Set ↥AutPerm) := by
    ext σ
    obtain ⟨h, rfl⟩ := D.φA_surjective σ
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · intro hh
      have hh' : V.map (rho11 AutPerm le_rfl ⟨D.φ h, D.φ_mem h⟩).toMonoidHom = V := hh
      exact ⟨h, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨h.2, (hmapV h).1 hh'⟩), rfl⟩
    · rintro ⟨h', hh', hEq⟩
      have h2 := (hmapV h').2 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hh')).2
      rw [← hEq]
      exact h2
  have hstab :
      Nat.card ↥{σ : ↥M24g | V.map (rho11 AutPerm le_rfl σ).toMonoidHom = V} = 64512 := by
    show Nat.card ↥{σ : ↥AutPerm | V.map (rho11 AutPerm le_rfl σ).toMonoidHom = V} = 64512
    rw [hS]
    exact c.card_map_G12 D
  obtain ⟨l, hl, hVl⟩ := M24G.eq_trioSpace_of_invariant P hPle hPcard V hVcard hsext hinv hstab
  have hezV : ez ∈ V := by rw [hez]; exact (hmemV z c.z_mem_E).2 c.z_mem_Z
  have hlU : M24G.TrioIn l U := by
    have hU' : M24G.sextClass U ∈ M24G.trioSpace l := by rw [← hVl, ← hezU]; exact hezV
    rcases (M24G.mem_trioSpace hl).1 hU' with h1 | ⟨U', hU'', hlU', hcl⟩
    · exact absurd h1 (M24G.sextClass_ne_one hU)
    · rw [← M24G.sextClass_inj hU'' hU hcl]
      exact hlU'
  have hstab₃ : ∀ h : ↥c.G1, (h : G) ∈ c.G3 ↔ D.φ h • U = U := by
    intro h
    have hsx : IsSextet (D.φ h • U) := (M24G.isSextet_smul_iff (D.φ_mem h)).2 hU
    have hcl : M24G.sextClass (D.φ h • U) =
        D.todd ⟨(h : G) * z * (h : G)⁻¹, c.conj_mem_E h c.z_mem_E⟩ := by
      rw [M24G.sextClass_smul (D.φ_mem h) hU, ← hezU, hez, hconj]
    constructor
    · intro hh
      apply M24G.sextClass_inj hsx hU
      rw [hcl, ← hezU, hez]
      congr 1
      apply Subtype.ext
      simpa using c.G3_comm_z (inv_mem hh)
    · intro hh
      have h1 : D.todd ⟨(h : G) * z * (h : G)⁻¹, c.conj_mem_E h c.z_mem_E⟩ =
          D.todd ⟨z, c.z_mem_E⟩ := by
        rw [← hcl, hh, ← hezU, hez]
      have h2 : (h : G) * z * (h : G)⁻¹ = z := congrArg Subtype.val (D.todd.injective h1)
      show (h : G) ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (h : G) * z = (h : G) * z * (h : G)⁻¹ * h := by group
        _ = z * h := by rw [h2]
  have hstab₂ : ∀ h : ↥c.G1, (h : G) ∈ c.G2 ↔ D.φ h • l = l := by
    intro h
    have hlx : IsTrio (D.φ h • l) := (M24G.isTrio_smul_iff (D.φ_mem h)).2 hl
    rw [← hmapV h, hVl, ← M24G.trioSpace_smul (D.φ_mem h) hl]
    exact ⟨fun h1 => M24G.trioSpace_inj hlx hl h1, fun h1 => by rw [h1]⟩
  exact ⟨⟨⟨D.φ, D.range_eq, D.ker_eq, l, U, hl, hU, hlU, hstab₂, hstab₃⟩, D.todd,
    D.todd_equiv⟩⟩

end Loc49

theorem resM24T_holds :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c) :=
  fun _ _ _ _ _ c => c.resM24T_nonempty

end CFSG.Quasithin.H13.AS91
