module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RProj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem finite_mulAut_ThetaQ (S : OmegaModel W) : Finite (MulAut W) := by
  haveI : Finite W :=
    Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

private theorem card_sup_of_commute_of_inf_eq_bot_aux {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B)
      = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

private theorem exists_scalar_mul_omega_of_mem (hK : Nat.card S.K = 4)
    (hΩ : Nat.card S.omega = 3600) {E : Subgroup (MulAut W)} (hEN : E ≤ omegaNorm S)
    (hE : IsElemAbelian 3 E) {x : MulAut W} (hx : x ∈ E) (hxlin : x ∈ linSub S) :
    ∃ z ∈ scalarSub S, ∃ h ∈ S.omega, z * h = x ∧ z ^ 3 = 1 ∧ h ^ 3 = 1 := by
  have hxsup : x ∈ scalarSub S ⊔ isoSub S := omegaNorm_inf_linSub_le_sup S ⟨hEN hx, hxlin⟩
  obtain ⟨z, hz, h, hh, hzh⟩ := (mem_scalarSub_sup_isoSub_iff S).mp hxsup
  have hhlin : h ∈ linSub S := ((mem_isoSub_iff S).mp hh).1
  have hcomm : Commute z h := scalarSub_commute S hz hhlin
  have hz3 : z ^ 3 = 1 := by
    have h : (⟨z, hz⟩ : scalarSub S) ^ 3 = 1 := by
      have h' := pow_card_eq_one' (G := scalarSub S) (x := ⟨z, hz⟩)
      rw [card_scalarSub_of_card_four S hK] at h'
      exact h'
    simpa using congrArg Subtype.val h
  have hh3 : h ^ 3 = 1 := by
    have h1 : (z * h) ^ 3 = z ^ 3 * h ^ 3 := hcomm.mul_pow 3
    rw [hzh, hE.2 x hx, hz3, one_mul] at h1
    exact h1.symm
  have hhΩ : h ∈ S.omega :=
    le_omega_of_isPGroup_three_of_le_isoSub S hK hΩ
      (isElemAbelian_zpowers (p := 3) hh3).isPGroup (Subgroup.zpowers_le.mpr hh)
      (Subgroup.mem_zpowers h)
  exact ⟨z, hz, h, hhΩ, hzh, hz3, hh3⟩

theorem exists_subgroup_card_nine_centralizer_factor (hK : Nat.card S.K = 4)
    (hΩ : Nat.card S.omega = 3600) {E : Subgroup (MulAut W)} (hEN : E ≤ omegaNorm S)
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3) {a : MulAut W} (haE : a ∈ E)
    (haω : a ∉ S.omega) :
    ∃ Q : Subgroup (MulAut W), Q ≤ E ∧ Nat.card Q = 3 ^ 2 ∧
      ∀ x ∈ Q, ∀ u ∈ S.factor 1, x * u = u * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut W) := finite_mulAut_ThetaQ S
  have hEp : IsPGroup 3 E := hE.isPGroup
  have hΩ0 : S.omega = S.factor 0 ⊔ S.factor 1 := by
    rw [omega_eq_omega0_of_card S (by rw [hΩ, hK]; norm_num), ← factor_sup]
  have hF0ω : S.factor 0 ≤ S.omega := by rw [hΩ0]; exact le_sup_left
  have hF1ω : S.factor 1 ≤ S.omega := by rw [hΩ0]; exact le_sup_right
  have hF0O : S.factor 0 ≤ isoSub S := hF0ω.trans (omega_le_isoSub S)
  have hF1O : S.factor 1 ≤ isoSub S := hF1ω.trans (omega_le_isoSub S)
  have hF1lin : S.factor 1 ≤ linSub S := fun x hx => ((mem_isoSub_iff S).mp (hF1O hx)).1
  have hElin : E ≤ linSub S := le_linSub_of_isPGroup_three S hK hEp hEN
  obtain ⟨za, hza, ha, hha, hzaha, hza3, hha3⟩ :=
    exists_scalar_mul_omega_of_mem S hK hΩ hEN hE haE (hElin haE)
  have hza_ne : za ≠ 1 := by
    intro h
    apply haω
    rw [← hzaha, h, one_mul]
    exact hha
  have hza_order : orderOf za = 3 := orderOf_eq_prime hza3 hza_ne
  set T : Subgroup (MulAut W) := E ⊓ S.omega with hT
  have hTleE : T ≤ E := by rw [hT]; exact inf_le_left
  have hTleΩ : T ≤ S.omega := by rw [hT]; exact inf_le_right
  have hTpgroup : IsPGroup 3 T := (hE.mono hTleE).isPGroup
  have hmul := Subgroup.relIndex_mul_card (H := T) (K := E)
  rw [inf_of_le_left hTleE] at hmul
  have hrel12 : T.relIndex E ∣ 12 := by
    rw [hT]; exact relIndex_inf_omega_dvd_twelve S hK hΩ hEN
  have hrel27 : T.relIndex E ∣ 27 :=
    ⟨Nat.card ↥T, by rw [hmul, hEcard]; norm_num⟩
  have hrel3 : T.relIndex E ∣ 3 := by
    have h := Nat.dvd_gcd hrel12 hrel27
    rwa [show Nat.gcd 12 27 = 3 by norm_num] at h
  have hrel_ne1 : T.relIndex E ≠ 1 := by
    intro h1
    have hmem : a ∈ T := Subgroup.relIndex_eq_one.mp h1 haE
    rw [hT, Subgroup.mem_inf] at hmem
    exact haω hmem.2
  have hrel_eq3 : T.relIndex E = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hrel3 with h | h
    · exact absurd h hrel_ne1
    · exact h
  have hcardT : Nat.card ↥T = 9 := by
    have h := hmul
    rw [hrel_eq3] at h
    have : 3 * Nat.card ↥T = 27 := by rw [h, hEcard]; norm_num
    omega
  have hhaT : ha ∈ T := by
    have hha_commT : ∀ t ∈ T, Commute ha t := by
      intro t ht
      have htlin : t ∈ linSub S :=
        ((mem_isoSub_iff S).mp (omega_le_isoSub S (hTleΩ ht))).1
      have hza_comm : Commute za t := scalarSub_commute S hza htlin
      have hat : Commute a t := hE.comm haE (hTleE ht)
      have h1 : Commute (za⁻¹ * a) t := (hza_comm.inv_left).mul_left hat
      have hha_eq : ha = za⁻¹ * a := by rw [← hzaha]; group
      rw [← hha_eq] at h1
      exact h1
    have hzp_le : Subgroup.zpowers ha ≤ Subgroup.centralizer (T : Set (MulAut W)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro t ht
      exact (hha_commT t ht).symm
    have hH'elem : IsElemAbelian 3 (T ⊔ Subgroup.zpowers ha) :=
      IsElemAbelian.sup_of_commute (hE.mono hTleE) (isElemAbelian_zpowers (p := 3) hha3)
        (fun t ht y hy => Subgroup.mem_centralizer_iff.mp (hzp_le hy) t ht)
    have hH'Ω : T ⊔ Subgroup.zpowers ha ≤ S.omega :=
      sup_le hTleΩ (Subgroup.zpowers_le.mpr hha)
    have hH'card_le : Nat.card ↥(T ⊔ Subgroup.zpowers ha) ≤ 9 := by
      obtain ⟨k, hk⟩ := hH'elem.isPGroup.exists_card_eq
      have hkdvd : 3 ^ k ∣ 3600 := by
        have h1 : Nat.card ↥(T ⊔ Subgroup.zpowers ha) ∣ Nat.card ↥S.omega :=
          Subgroup.card_dvd_of_le hH'Ω
        rw [hk, hΩ] at h1
        exact h1
      have hk_le : k ≤ 2 := by
        by_contra h
        have hlt : 2 < k := not_le.mp h
        have h3 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hlt
        exact (by norm_num : ¬ (3 ^ 3 ∣ 3600)) (h3.trans hkdvd)
      calc Nat.card ↥(T ⊔ Subgroup.zpowers ha) = 3 ^ k := hk
        _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk_le
        _ = 9 := by norm_num
    have hHeq : T = T ⊔ Subgroup.zpowers ha :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardT]; exact hH'card_le)
    have h1 : ha ∈ T ⊔ Subgroup.zpowers ha := Subgroup.mem_sup_right (Subgroup.mem_zpowers ha)
    rw [← hHeq] at h1
    exact h1
  have hzaE : za ∈ E := by
    have hza_eq : za = a * ha⁻¹ := by rw [← hzaha]; group
    rw [hza_eq]
    exact E.mul_mem haE (E.inv_mem (hTleE hhaT))
  set T₀ : Subgroup (MulAut W) := E ⊓ S.factor 0 with hT₀
  have hT₀elem : IsElemAbelian 3 T₀ := by rw [hT₀]; exact hE.mono inf_le_left
  have hT₀leE : T₀ ≤ E := by rw [hT₀]; exact inf_le_left
  have hT₀leF0 : T₀ ≤ S.factor 0 := by rw [hT₀]; exact inf_le_right
  have hTinfF0 : T ⊓ S.factor 0 = T₀ := by
    rw [hT, hT₀, inf_assoc, inf_of_le_right hF0ω]
  have hTsup : T ≤ S.factor 1 ⊔ S.factor 0 := by
    rw [sup_comm, ← hΩ0]
    exact hTleΩ
  have hbound : ∀ f : ↥T →* MulAut W, f.range ≤ S.factor 1 → Nat.card f.range ≤ 3 := by
    intro f hf
    have hp : IsPGroup 3 ↥(f.range) :=
      hTpgroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hkdvd : 3 ^ k ∣ 60 := by
      have h1 : Nat.card ↥(f.range) ∣ Nat.card ↥(S.factor 1) := Subgroup.card_dvd_of_le hf
      rw [hk, card_factor S 1, hK] at h1
      norm_num at h1
      exact h1
    have hk_le : k ≤ 1 := by
      by_contra h
      have hlt : 1 < k := not_le.mp h
      have h2 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hlt
      exact (by norm_num : ¬ (3 ^ 2 ∣ 60)) (h2.trans hkdvd)
    calc Nat.card ↥(f.range) = 3 ^ k := hk
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk_le
      _ = 3 := by norm_num
  have hproj := card_le_mul_card_inf_of_le_sup (H := MulAut W) (B := T)
    (L₁ := S.factor 1) (L₂ := S.factor 0)
    (factor_commute S (j := 1) (l := 0) (by decide))
    (by rw [inf_comm]; exact factor_inf_factor S) hTsup hbound
  have hT₀_ge3 : 3 ≤ Nat.card ↥T₀ := by
    have h := hproj
    rw [hTinfF0, hcardT] at h
    omega
  have hcardT₀_dvd3 : Nat.card ↥T₀ ∣ 3 := by
    obtain ⟨k, hk⟩ := hT₀elem.isPGroup.exists_card_eq
    have hkdvd : 3 ^ k ∣ 60 := by
      have h1 : Nat.card ↥T₀ ∣ Nat.card ↥(S.factor 0) := Subgroup.card_dvd_of_le hT₀leF0
      rw [hk, card_factor S 0, hK] at h1
      norm_num at h1
      exact h1
    have hk_le : k ≤ 1 := by
      by_contra h
      have hlt : 1 < k := not_le.mp h
      have h2 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hlt
      exact (by norm_num : ¬ (3 ^ 2 ∣ 60)) (h2.trans hkdvd)
    rw [hk]
    simpa using pow_dvd_pow 3 hk_le
  have hcardT₀ : Nat.card ↥T₀ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hcardT₀_dvd3 with h | h
    · omega
    · exact h
  have hcommZ : ∀ x ∈ Subgroup.zpowers za, ∀ y ∈ T₀, x * y = y * x := by
    intro x hx y hy
    have hxZ : x ∈ scalarSub S := Subgroup.zpowers_le.mpr hza hx
    have hyLin : y ∈ linSub S := ((mem_isoSub_iff S).mp (hF0O (hT₀leF0 hy))).1
    exact scalarSub_commute S hxZ hyLin
  have hinf_bot : Subgroup.zpowers za ⊓ T₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxZ : x ∈ scalarSub S := Subgroup.zpowers_le.mpr hza hx.1
    have hxO : x ∈ isoSub S := hF0O (hT₀leF0 hx.2)
    have hxZinfO : x ∈ scalarSub S ⊓ isoSub S := ⟨hxZ, hxO⟩
    rw [scalarSub_inf_isoSub S] at hxZinfO
    exact hxZinfO
  have hcardZp : Nat.card ↥(Subgroup.zpowers za) = 3 := by
    rw [Nat.card_zpowers, hza_order]
  have hcardQ : Nat.card ↥(Subgroup.zpowers za ⊔ T₀) = 3 ^ 2 := by
    rw [card_sup_of_commute_of_inf_eq_bot_aux hcommZ hinf_bot, hcardZp, hcardT₀]
    norm_num
  refine ⟨Subgroup.zpowers za ⊔ T₀, ?_, hcardQ, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hzaE) hT₀leE
  · intro x hx u hu
    have hQcent : Subgroup.zpowers za ⊔ T₀ ≤
        Subgroup.centralizer (S.factor 1 : Set (MulAut W)) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro v hv
        exact (scalarSub_commute S hza (hF1lin hv)).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (factor_commute S (j := 0) (l := 1) (by decide) y (hT₀leF0 hy) v hv).symm
    exact (Subgroup.mem_centralizer_iff.mp (hQcent hx) u hu).symm

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
