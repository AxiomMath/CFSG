module

public import CFSG.Sporadic.Recognition.LyonsAS4Cover
public import CFSG.Sporadic.Recognition.LyonsAS4Embed
public import CFSG.Sporadic.Recognition.JankoWongCover
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.JankoWong CFSG.GH74.GLS

namespace Cover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem center_eq (h : IsCover8 ρ z) : Subgroup.center E = Subgroup.zpowers z := by
  apply le_antisymm
  · intro c hc
    have hcen : (⟨ρ c, (mem_alternatingGroup).mpr (h.sign_rho c)⟩ : alternatingGroup (Fin 8)) ∈
        Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨a, ha⟩
      obtain ⟨e, rfl⟩ : a ∈ ρ.range := h.range_eq ▸ ha
      apply Subtype.ext
      change ρ e * ρ c = ρ c * ρ e
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc e]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
    have h1 : ρ c = 1 := congrArg Subtype.val hcen
    rw [← h.ker_eq]
    exact h1
  · rw [Subgroup.zpowers_le]
    exact h.central

theorem card_center (h : IsCover8 ρ z) : Nat.card (Subgroup.center E) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [center_eq h, Nat.card_zpowers, orderOf_eq_prime h.sq_eq_one h.ne_one]

noncomputable def quotientCenterEquiv (h : IsCover8 ρ z) :
    E ⧸ Subgroup.center E ≃* alternatingGroup (Fin 8) := by
  let ρ' : E →* alternatingGroup (Fin 8) :=
    ρ.codRestrict (alternatingGroup (Fin 8)) fun e => (mem_alternatingGroup).mpr (h.sign_rho e)
  have hker : ρ'.ker = Subgroup.center E := by
    rw [center_eq h, ← h.ker_eq]
    ext e
    simp only [MonoidHom.mem_ker, ρ']
    constructor
    · intro he
      exact congrArg Subtype.val he
    · intro he
      exact Subtype.ext he
  have hsurj : Function.Surjective ρ' := by
    rintro ⟨a, ha⟩
    obtain ⟨e, he⟩ : a ∈ ρ.range := h.range_eq ▸ ha
    exact ⟨e, Subtype.ext he⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj)

theorem isDoubleCoverOfAlt {E : Type} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}
    (h : IsCover8 ρ z) : IsDoubleCoverOfAlt E 8 := by
  have hnab : ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
    · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    · intro h
      have h2 := congrArg (fun p : alternatingGroup (Fin 8) => (p : Equiv.Perm (Fin 8)) 2) h
      revert h2
      decide
  refine ⟨⟨h.perfect, ?_, ?_⟩, card_center h, ⟨quotientCenterEquiv h⟩⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact (quotientCenterEquiv h).isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(quotientCenterEquiv h).symm a, (quotientCenterEquiv h).symm b, fun hba => hab ?_⟩
    have := congrArg (quotientCenterEquiv h) hba
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

end Cover8

namespace IsCover11

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

@[expose] def Lsub (ρ : E →* Perm (Fin 11)) : Subgroup E := fix012.comap ρ

theorem mem_Lsub {e : E} : e ∈ Lsub ρ ↔ ρ e ∈ fix012 := Iff.rfl

theorem z_mem_Lsub (h : IsCover11 ρ z) : z ∈ Lsub ρ := by
  rw [mem_Lsub, h.rho_z]; exact one_mem _

@[expose] def ρLfix (ρ : E →* Perm (Fin 11)) : ↥(Lsub ρ) →* ↥fix012 :=
  (ρ.domRestrict (Lsub ρ)).codRestrict fix012 fun l => l.2

@[expose] noncomputable def ρL (ρ : E →* Perm (Fin 11)) : ↥(Lsub ρ) →* Perm (Fin 8) :=
  fix012Equiv.toMonoidHom.comp (ρLfix ρ)

theorem embed8_ρL (l : ↥(Lsub ρ)) : embed8 (ρL ρ l) = ρ l := by
  change embed8 (fix012Equiv (ρLfix ρ l)) = ρ l
  rw [embed8_fix012Equiv]
  rfl

theorem ρL_eq_one_iff (l : ↥(Lsub ρ)) : ρL ρ l = 1 ↔ ρ l = 1 := by
  constructor
  · intro hl
    rw [← embed8_ρL, hl, map_one]
  · intro hl
    apply embed8_injective
    rw [embed8_ρL, hl, map_one]

theorem cover8_ker (h : IsCover11 ρ z) :
    (ρL ρ).ker = Subgroup.zpowers (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) := by
  ext l
  rw [MonoidHom.mem_ker, ρL_eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · intro hl
    rcases h.mem_ker_iff.mp hl with h1 | h1
    · exact ⟨0, by apply Subtype.ext; simpa using h1.symm⟩
    · exact ⟨1, by apply Subtype.ext; simpa using h1.symm⟩
  · rintro ⟨n, rfl⟩
    rw [Subgroup.coe_zpow, map_zpow, show ρ ((⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) : E) = 1 from h.rho_z,
      one_zpow]

theorem cover8_range (h : IsCover11 ρ z) : (ρL ρ).range = alternatingGroup (Fin 8) := by
  ext σ
  constructor
  · rintro ⟨l, rfl⟩
    rw [mem_alternatingGroup, ← sign_embed8, embed8_ρL]
    exact h.sign_rho l
  · intro hσ
    have h1 : embed8 σ ∈ fix012 ⊓ alternatingGroup (Fin 11) := by
      rw [← map_embed8_alternatingGroup]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨e, he⟩ : embed8 σ ∈ ρ.range := h.range_eq ▸ h1.2
    have heL : e ∈ Lsub ρ := by rw [mem_Lsub, he]; exact h1.1
    refine ⟨⟨e, heL⟩, ?_⟩
    apply embed8_injective
    rw [embed8_ρL]
    exact he

theorem Lsub_isPerfect (h : IsCover11 ρ z) : Group.IsPerfect ↥(Lsub ρ) := by
  classical
  have hA : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hDmap : (commutator ↥(Lsub ρ)).map (ρL ρ) = alternatingGroup (Fin 8) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, cover8_range h]
    exact Subgroup.isPerfect_iff.mp hA
  have hz2 : (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact Subtype.ext (by simpa [pow_two] using h.sq_eq_one)
  have hzD : (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) ∈ commutator ↥(Lsub ρ) := by
    by_contra hzD
    have hσ : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 8) := by
      simp [mem_alternatingGroup, Perm.sign_mul]
    rw [← hDmap] at hσ
    obtain ⟨d, hd, hdσ⟩ := hσ
    have hd2 : d ^ 2 ∈ commutator ↥(Lsub ρ) := Subgroup.pow_mem _ hd 2
    have hσ2 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) ^ 2 = 1 := by decide
    have hd2ker : (ρL ρ) (d ^ 2) = 1 := by
      rw [map_pow, hdσ, hσ2]
    have hd2' : d ^ 2 ∈ (ρL ρ).ker := hd2ker
    rw [cover8_ker h, Subgroup.mem_zpowers_iff] at hd2'
    obtain ⟨n, hn⟩ := hd2'
    have hsq : (d : E) ^ 2 = z := by
      apply h.sq_eq_z_of_type22
      rw [← embed8_ρL, hdσ, cycleType_embed8]
      exact JankoWong.cycleType_type22_of_card hσ2 (by decide)
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · rw [zpow_mul, hz2, one_zpow] at hn
      have : (d : E) ^ 2 = 1 := by
        have := congrArg Subtype.val hn
        simpa using this.symm
      exact h.ne_one (hsq ▸ this)
    · rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one] at hn
      exact hzD (hn ▸ hd2)
  have htop : commutator ↥(Lsub ρ) = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have hl : (ρL ρ) l ∈ (commutator ↥(Lsub ρ)).map (ρL ρ) := by
      rw [hDmap]
      exact (cover8_range h).le ⟨l, rfl⟩
    obtain ⟨d, hd, hdl⟩ := hl
    have hker : d⁻¹ * l ∈ (ρL ρ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, inv_mul_cancel]
    rw [cover8_ker h, Subgroup.mem_zpowers_iff] at hker
    obtain ⟨n, hn⟩ := hker
    have hmem : (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) ^ n ∈ commutator ↥(Lsub ρ) :=
      Subgroup.zpow_mem _ hzD n
    have : l = d * (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) ^ n := by rw [hn]; group
    rw [this]
    exact Subgroup.mul_mem _ hd hmem
  exact ⟨htop⟩

theorem cover8 (h : IsCover11 ρ z) :
    IsCover8 (ρL ρ) (⟨z, h.z_mem_Lsub⟩ : ↥(Lsub ρ)) where
  ne_one := fun hh => h.ne_one (congrArg Subtype.val hh)
  sq_eq_one := Subtype.ext h.sq_eq_one
  central := Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h.mul_z_comm g)
  ker_eq := cover8_ker h
  range_eq := cover8_range h
  perfect := Lsub_isPerfect h

theorem isDoubleCoverOfAlt_Lsub {E : Type} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}
    (h : IsCover11 ρ z) : IsDoubleCoverOfAlt ↥(Lsub ρ) 8 :=
  Cover8.isDoubleCoverOfAlt h.cover8

end IsCover11

end CFSG.Sporadic.Recognition.LyonsSims
