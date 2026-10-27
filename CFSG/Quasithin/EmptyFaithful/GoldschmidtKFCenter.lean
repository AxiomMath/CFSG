module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.Open CFSG.Quasithin CFSG.LieType.CurtisTits

theorem input15338CenterRank_of_catalogStep (hcat : CatalogStepFact) : Input15338CenterRank := by
  intro C _ _ hq hS F hFZ hFel
  classical
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥(Subgroup.center C)))
  set Z₂ : Subgroup C := (S : Subgroup ↥(Subgroup.center C)).map (Subgroup.center C).subtype
    with hZ₂
  have hZ₂c : Z₂ ≤ Subgroup.center C := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hZ₂n : Z₂.Normal := Subgroup.normal_of_le_center hZ₂c
  have hZ₂p : IsPGroup 2 ↥Z₂ :=
    IsPGroup.of_equiv S.isPGroup'
      (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _))
  let π : C →* C ⧸ Z₂ := QuotientGroup.mk' Z₂
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z₂
  have hker : π.ker = Z₂ := QuotientGroup.ker_mk' Z₂
  have hπnt : ∃ k, π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Subgroup.center C := hZ₂c ((QuotientGroup.eq_one_iff x).mp (hcon x))
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]
  have hq' : CFSG.IsQuasisimple (C ⧸ Z₂) := isQuasisimple_of_surjective hq hπs hπnt
  have hcenter : Subgroup.center (C ⧸ Z₂) = (Subgroup.center C).map π :=
    center_eq_map_center_of_isQuasisimple hq hπs (hker.le.trans hZ₂c)
  let f : ↥(Subgroup.center C) →* C ⧸ Z₂ := π.comp (Subgroup.center C).subtype
  have hfrange : f.range = Subgroup.center (C ⧸ Z₂) := by
    rw [hcenter, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfker : f.ker = (S : Subgroup ↥(Subgroup.center C)) := by
    ext z
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, Subgroup.coe_subtype, π,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ₂]
    exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)
  have hodd : Odd (Nat.card (Subgroup.center (C ⧸ Z₂))) := by
    rw [← hfrange, ← Subgroup.index_ker f, hfker]
    have := S.not_dvd_index
    exact Nat.odd_iff.mpr (by omega)
  have hSQ : SQTKGroup (C ⧸ Z₂) := by
    refine ⟨fun p hp hp2 => ?_, hS.2.quotient Z₂⟩
    have : Fact p.Prime := ⟨hp⟩
    have hnd : ¬ p ∣ Nat.card Z₂ := by
      intro h
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hZ₂p
      rw [hk] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    exact (le_of_eq (CFSG.SectionRank.pRank_quotient_eq Z₂ hnd)).trans (hS.1 p hp hp2)
  have hcard3 := hcat (C ⧸ Z₂) hq' hSQ hodd
  have hFπ : ∀ x ∈ F, π x ∈ Subgroup.center (C ⧸ Z₂) := fun x hx => by
    rw [hcenter]
    exact ⟨x, hFZ hx, rfl⟩
  have hinj : Function.Injective
      (fun x : ↥F => (⟨π x, hFπ x x.2⟩ : ↥(Subgroup.center (C ⧸ Z₂)))) := by
    intro a b hab
    have hab' : π (a : C) = π (b : C) := congrArg Subtype.val hab
    have hx : (a : C) * (b : C)⁻¹ ∈ Z₂ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
    obtain ⟨k, hk⟩ := hZ₂p ⟨_, hx⟩
    have hk' : ((a : C) * (b : C)⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h3 : ((a : C) * (b : C)⁻¹) ^ 3 = 1 :=
      hFel.2 _ (F.mul_mem a.2 (F.inv_mem b.2))
    have hg := pow_gcd_eq_one.mpr ⟨h3, hk'⟩
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2) : Nat.gcd 3 (2 ^ k) = 1),
      pow_one] at hg
    exact Subtype.ext (mul_inv_eq_one.mp hg)
  calc Nat.card F ≤ Nat.card ↥(Subgroup.center (C ⧸ Z₂)) := Nat.card_le_card_of_injective _ hinj
    _ ≤ 3 := by rcases hcard3 with h | h <;> omega

end CFSG.Quasithin.SBd19F
