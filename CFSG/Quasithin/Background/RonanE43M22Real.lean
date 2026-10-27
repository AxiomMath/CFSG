module

public import CFSG.Quasithin.Background.RonanE43M22Lat
public import CFSG.Quasithin.Background.RonanE43Real

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  CFSG.QuasithinUnique.Unc25K1.Six Equiv

@[expose] def RealA6 (y : Perm (Fin 6)) : Prop :=
  ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * y * g⁻¹ = y⁻¹

instance (y : Perm (Fin 6)) : Decidable (RealA6 y) := by
  unfold RealA6
  infer_instance

theorem realA6_all : ∀ y : Perm (Fin 6), Perm.sign y = 1 → y * y * y = 1 → RealA6 y := by
  decide +kernel

theorem real_A6 (y : alternatingGroup (Fin 6)) (hy : y ^ 3 = 1) :
    ∃ g : alternatingGroup (Fin 6), g * y * g⁻¹ = y⁻¹ := by
  have hs : Perm.sign (y : Perm (Fin 6)) = 1 := Equiv.Perm.mem_alternatingGroup.mp y.2
  have h3 : (y : Perm (Fin 6)) * y * y = 1 := by
    have := congrArg Subtype.val hy
    simpa [pow_succ, mul_assoc] using this
  obtain ⟨g, hgs, hg⟩ := realA6_all _ hs h3
  exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hgs⟩, Subtype.ext hg⟩

section M22


theorem m22_hL6 : Subgroup.closure {g | g ∈ l6Gens} ≤ Cm 3 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
  have ha := List.all_eq_true.mp incl6 3 (by simp)
  simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
  have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [m22_len]; norm_num
  have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
  have h2 : Lm 3 = (cert.tGens :: cert.lat)[3] := List.getD_eq_getElem _ _ hlen3
  show _ ≤ Subgroup.closure {g | g ∈ Lm 3}
  rw [h2, Subgroup.closure_le]
  intro g hg
  have := List.all_eq_true.mp ha g hg
  rw [List.getD_eq_getElem _ _ hlen3] at this
  exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth (cert.members_closed hcl _ hmem) g).mpr
    (Std.HashSet.contains_iff_mem.mp this)

theorem m22_L6_eq : Subgroup.closure {g | g ∈ l6Gens} = Cm 3 := by
  refine Subgroup.eq_of_le_of_card_ge m22_hL6 ?_
  rw [m22_Cm_card 3 (by norm_num), ext6.1]
  rfl

theorem real3_X6 (y : ↥(Subgroup.closure {g | g ∈ l6Gens})) (hy : y ^ 3 = 1) :
    ∃ g : ↥(Subgroup.closure {g | g ∈ l6Gens}), g * y * g⁻¹ = y⁻¹ := by
  obtain ⟨-, V, hVn, -, -, hVcard, ⟨e⟩⟩ := ext6
  let φ : ↥(Subgroup.closure {g | g ∈ l6Gens}) →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' V)
  have hφs : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective V)
  have hker : φ.ker = V := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' V x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hV2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 4) hVcard
  obtain ⟨gb, hgb⟩ := real_A6 (φ y) (by rw [← map_pow, hy, map_one])
  obtain ⟨g₁, rfl⟩ := hφs gb
  refine exists_real_of_real_mod_two_kernel φ hV2 hy g₁ ?_
  rw [map_mul, map_mul, map_inv]
  exact hgb

theorem real3_Pm3 (y : ↥(Pm 3)) (hy : y ^ 3 = 1) : ∃ g : ↥(Pm 3), g * y * g⁻¹ = y⁻¹ := by
  let e : ↥(Pm 3) ≃* ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    (Subgroup.subgroupOfEquivOfLe (m22_Cm_le 3 (by norm_num))).trans
      (MulEquiv.subgroupCongr m22_L6_eq.symm)
  obtain ⟨g, hg⟩ := real3_X6 (e y) (by rw [← map_pow, hy, map_one])
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
  exact hg

theorem real3_M22 (y : ↥Mgrp) (hy3 : y ^ 3 = 1) : ∃ g : ↥Mgrp, g * y * g⁻¹ = y⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hy1 : y = 1
  · exact ⟨1, by simp [hy1]⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥(Pm 3)) := inferInstance
  let Q : Subgroup ↥Mgrp := (S : Subgroup ↥(Pm 3)).map (Pm 3).subtype
  have hQp : IsPGroup 3 Q := S.isPGroup'.map (Pm 3).subtype
  have hQle : Q ≤ Pm 3 := Subgroup.map_subtype_le _
  have hrel : Q.relIndex (Pm 3) = (S : Subgroup ↥(Pm 3)).index :=
    congrArg Subgroup.index
      (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _)
  have hidx77 : (Pm 3).index = 77 := by
    have h1 := Subgroup.card_mul_index (Pm 3)
    have hM : Nat.card ↥Mgrp = 443520 :=
      cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check cert_check)
        (LatCert.sizesOK_of_check cert_check)
    rw [m22_Pm_card 3 (by norm_num), hM] at h1
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at h1
    omega
  have hQidx : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.relIndex_mul_index hQle
    rw [hrel, hidx77] at h1
    rw [← h1]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact S.not_dvd_index h
    · omega
  let PS : Sylow 3 ↥Mgrp := hQp.toSylow hQidx
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord]; norm_num)
  obtain ⟨R, hR⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Mgrp R PS
  have hgPS : ((g • R : Sylow 3 ↥Mgrp) : Subgroup ↥Mgrp) = Q :=
    congrArg (fun P : Sylow 3 ↥Mgrp => (P : Subgroup ↥Mgrp)) hg
  have hyQ : g * y * g⁻¹ ∈ Q := by
    rw [← hgPS]
    show g * y * g⁻¹ ∈ (R : Subgroup ↥Mgrp).map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨y, hR (Subgroup.mem_zpowers y), by simp [MulAut.conj_apply]⟩
  obtain ⟨p, -, hp⟩ := Subgroup.mem_map.mp hyQ
  have hp3 : p ^ 3 = 1 := by
    apply Subtype.ext
    have : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; simp
    rw [← hp] at this
    simpa using this
  obtain ⟨h, hh⟩ := real3_Pm3 p hp3
  refine ⟨g⁻¹ * (h : ↥Mgrp) * g, ?_⟩
  have hh' : (h : ↥Mgrp) * (p : ↥Mgrp) * (h : ↥Mgrp)⁻¹ = (p : ↥Mgrp)⁻¹ := by
    have := congrArg Subtype.val hh
    simpa using this
  have hp' : (p : ↥Mgrp) = g * y * g⁻¹ := hp
  rw [hp'] at hh'
  calc g⁻¹ * (h : ↥Mgrp) * g * y * (g⁻¹ * (h : ↥Mgrp) * g)⁻¹
      = g⁻¹ * ((h : ↥Mgrp) * (g * y * g⁻¹) * (h : ↥Mgrp)⁻¹) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹)⁻¹ * g := by rw [hh']
    _ = y⁻¹ := by group

end M22

end CFSG.Quasithin.RonanE43
