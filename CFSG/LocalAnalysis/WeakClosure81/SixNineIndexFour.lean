module

public import CFSG.GroupTheory.AlternatingFive.HomPermFive
public import CFSG.LocalAnalysis.WeakClosure81.SixNineConcrete
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75
  CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_mul_mem_of_mQuot_eq_two {R A U A' U' : Subgroup G}
    (hAel : IsElemAbelian 2 A) (hUA : U ≤ A) (hk : E3.mQuot A U = 2)
    (hA' : ¬ A' ≤ U')
    (hmul : ∀ a ∈ A, a ∉ U → ∀ a' ∈ A', a' ∉ U' → a * a' ∈ R) : A ≤ R := by
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  obtain ⟨a', ha'A', ha'U'⟩ : ∃ a' ∈ A', a' ∉ U' := by
    by_contra h
    push Not at h
    exact hA' h
  have hprod : ∀ a ∈ A, a ∉ U → ∀ b ∈ A, b ∉ U → a * b ∈ R := by
    intro a ha haU b hb hbU
    have h1 : a * a' ∈ R := hmul a ha haU a' ha'A' ha'U'
    have h2 : b * a' ∈ R := hmul b hb hbU a' ha'A' ha'U'
    have h3 : (a * a') * (b * a')⁻¹ ∈ R :=
      R.mul_mem h1 (R.inv_mem h2)
    have hb2 : b * b = 1 := by simpa [pow_two] using hAel.2 b hb
    have heq : (a * a') * (b * a')⁻¹ = a * b := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2]
      group
    rwa [heq] at h3
  have hcardA : Nat.card ↥A = 4 * Nat.card ↥U := by
    rw [E3.card_eq_two_pow_mul hA2 hUA, hk]
    norm_num
  have hUpos : 0 < Nat.card ↥U := Nat.card_pos
  have hA_ncard : (A : Set G).ncard = Nat.card ↥A :=
    (Nat.card_coe_set_eq (A : Set G)).symm
  have hU_ncard : (U : Set G).ncard = Nat.card ↥U :=
    (Nat.card_coe_set_eq (U : Set G)).symm
  have hdiff : ((A : Set G) \ (U : Set G)).ncard = 3 * Nat.card ↥U := by
    rw [Set.ncard_diff (fun x hx => hUA hx) (Set.toFinite _), hA_ncard, hU_ncard, hcardA]
    omega
  have hex : ∀ t ∈ A, ∃ a ∈ A, a ∉ U ∧ t * a ∉ U := by
    intro t ht
    by_contra h
    push Not at h
    have himg : (fun a : G => t * a) '' ((A : Set G) \ (U : Set G)) ⊆ (U : Set G) := by
      rintro x ⟨a, ha, rfl⟩
      exact h a ha.1 ha.2
    have hinj : Function.Injective (fun a : G => t * a) := fun a b hab =>
      mul_left_cancel hab
    have h1 : ((A : Set G) \ (U : Set G)).ncard ≤ (U : Set G).ncard := by
      calc ((A : Set G) \ (U : Set G)).ncard
          = ((fun a : G => t * a) '' ((A : Set G) \ (U : Set G))).ncard :=
            (Set.ncard_image_of_injective _ hinj).symm
        _ ≤ (U : Set G).ncard := Set.ncard_le_ncard himg (Set.toFinite _)
    rw [hdiff, hU_ncard] at h1
    omega
  intro t ht
  obtain ⟨a, haA, haU, htaU⟩ := hex t ht
  have htaA : t * a ∈ A := A.mul_mem ht haA
  have hcomm : a * t = t * a := by
    simpa using congrArg Subtype.val
      (hAel.1.is_comm.comm (⟨a, haA⟩ : ↥A) (⟨t, ht⟩ : ↥A))
  have ha2 : a * a = 1 := by simpa [pow_two] using hAel.2 a haA
  have ht_eq : t = a * (t * a) := by
    calc t = (a * a) * t := by rw [ha2, one_mul]
      _ = a * (a * t) := by rw [mul_assoc]
      _ = a * (t * a) := by rw [hcomm]
  have hR : a * (t * a) ∈ R := hprod a haA haU (t * a) htaA htaU
  rwa [← ht_eq] at hR

theorem exists_first_case_of_mQuot_eq_two {H A : Subgroup G}
    (ψ : ↥H →* Equiv.Perm (Fin 5))
    (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H)
    (hrange : alternatingGroup (Fin 5) ≤ ψ.range)
    (hAel : IsElemAbelian 2 A) (hTI : IsTI A) (hrk : 2 < rk ↥A) (hAH : A ≤ H)
    (hinner : (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5))
    (hk : E3.mQuot A (A ⊓ pCoreOf 2 H) = 2)
    (hfb : ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G)) :
    ∃ h ∈ H, InCalO 2 (normalizer (A : Set G)) ⊥ A h ∧
      twoResidual H = (A ⊔ conjSubgroup A h) ⊔ pCoreOf 2 (twoResidual H) := by
  classical
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  set Ā : Subgroup (Equiv.Perm (Fin 5)) := (A.subgroupOf H).map ψ with hĀdef
  have hcardĀ : Nat.card Ā = 4 := by
    rw [hĀdef,
      CFSG.GroupTheory.AlternatingFive.card_map_subgroupOf_eq_two_pow ψ hker hAH hA2, hk]
    norm_num
  have hĀle : Ā ≤ alternatingGroup (Fin 5) := by
    rw [hĀdef]
    exact hinner
  have hĀsyl :=
    CFSG.GroupTheory.AlternatingFive.isSylowOf_alternatingGroup_of_card_four hĀle hcardĀ
  obtain ⟨σ, hσA5, hσne⟩ :=
    CFSG.GroupTheory.AlternatingFive.exists_conjSubgroup_ne_of_card_four hĀle hcardĀ
  have hσrange : σ ∈ ψ.range := hrange hσA5
  obtain ⟨hx, hxψ⟩ := MonoidHom.mem_range.mp hσrange
  set h : G := hx.1 with hhdef
  have hh : h ∈ H := hx.2
  have hψ : ψ ⟨h, hh⟩ = σ := by
    have he : (⟨h, hh⟩ : ↥H) = hx := Subtype.ext rfl
    rw [he, hxψ]
  have hAhH : conjSubgroup A h ≤ H := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxH : h * x * h⁻¹ ∈ H := hAH hx
    have hx' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [hx']
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hxH) hh
  have hsub : (conjSubgroup A h).subgroupOf H =
      conjSubgroup (A.subgroupOf H) ⟨h, hh⟩ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hAhH, map_conjSubgroup_subgroupOf' hAH hh]
  set Āh : Subgroup (Equiv.Perm (Fin 5)) :=
    ((conjSubgroup A h).subgroupOf H).map ψ with hĀhdef
  have hĀh_eq : Āh = conjSubgroup Ā σ := by
    rw [hĀhdef, hsub, ← map_conjSubgroup_hom ψ (A.subgroupOf H) ⟨h, hh⟩, hψ, hĀdef]
  have hne : Ā ≠ Āh := by
    rw [hĀh_eq]
    exact hσne.symm
  have hĀh_le : Āh ≤ alternatingGroup (Fin 5) := by
    have hA5norm : (alternatingGroup (Fin 5)).Normal := inferInstance
    have hfix : conjSubgroup (alternatingGroup (Fin 5)) σ = alternatingGroup (Fin 5) := by
      rw [conjSubgroup_eq_iff_mem_normalizer, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hA5norm.conj_mem x hx σ
      · intro hx
        have h1 : σ⁻¹ * (σ * x * σ⁻¹) * σ ∈ alternatingGroup (Fin 5) := by
          simpa using hA5norm.conj_mem (σ * x * σ⁻¹) hx σ⁻¹
        have h2 : σ⁻¹ * (σ * x * σ⁻¹) * σ = x := by group
        rwa [h2] at h1
    rw [hĀh_eq]
    exact (E3.conjSubgroup_mono_left σ hĀle).trans (le_of_eq hfix)
  have hcardĀh : Nat.card Āh = 4 := by
    rw [hĀh_eq, card_conjSubgroup' σ Ā, hcardĀ]
  have hĀh_syl :=
    CFSG.GroupTheory.AlternatingFive.isSylowOf_alternatingGroup_of_card_four hĀh_le hcardĀh
  have hsup : Ā ⊔ Āh = alternatingGroup (Fin 5) :=
    CFSG.Quasithin.SteinbergBS.sup_sylow_eq_alternating hĀsyl hĀh_syl hne
  have hUleA : nVSub A h ≤ A := inf_le_left
  have hUleH : nVSub A h ≤ H := hUleA.trans hAH
  have hUmapA : Subgroup.map ψ ((nVSub A h).subgroupOf H) ≤ Ā := by
    rw [hĀdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hUleA)
  have hU0N : (nVSub A h).subgroupOf H ≤
      Subgroup.normalizer ((conjSubgroup A h).subgroupOf H) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change x.1 ∈ conjSubgroup A h ↔ u.1 * x.1 * u.1⁻¹ ∈ conjSubgroup A h
    exact Subgroup.mem_normalizer_iff.mp
      ((inf_le_right : nVSub A h ≤ Subgroup.normalizer (conjSubgroup A h))
        (Subgroup.mem_subgroupOf.mp hu)) x.1
  have hUmapN : Subgroup.map ψ ((nVSub A h).subgroupOf H) ≤
      Subgroup.normalizer (Āh : Set (Equiv.Perm (Fin 5))) := by
    refine (Subgroup.map_mono hU0N).trans ?_
    rw [hĀhdef]
    exact Subgroup.le_normalizer_map ψ
  have hUmap_bot : Subgroup.map ψ ((nVSub A h).subgroupOf H) ≤ ⊥ := by
    have hbot : Ā ⊓ Subgroup.normalizer (Āh : Set (Equiv.Perm (Fin 5))) = ⊥ :=
      CFSG.GroupTheory.AlternatingFive.inf_normalizer_eq_bot_of_card_four
        hĀle hĀh_le hcardĀ hcardĀh hne
    exact (le_inf hUmapA hUmapN).trans (le_of_eq hbot)
  have hnVQ : nVSub A h ≤ pCoreOf 2 H := by
    intro x hx
    have hxH : x ∈ H := hUleH hx
    have hxmap : ψ ⟨x, hxH⟩ ∈ Subgroup.map ψ ((nVSub A h).subgroupOf H) :=
      Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hx1 : ψ ⟨x, hxH⟩ = 1 :=
      Subgroup.mem_bot.mp (hUmap_bot hxmap)
    have hxker : (⟨x, hxH⟩ : ↥H) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx1
    rw [hker] at hxker
    exact Subgroup.mem_subgroupOf.mp hxker
  have hB0 : nVSub A h = A ⊓ pCoreOf 2 H :=
    le_antisymm (le_inf hUleA hnVQ) (inf_pCoreOf_le_nVSub hfb hh)
  have hmap_sup : (((A ⊔ conjSubgroup A h).subgroupOf H).map ψ) =
      alternatingGroup (Fin 5) := by
    rw [Subgroup.subgroupOf_sup hAH hAhH, Subgroup.map_sup, ← hĀdef, ← hĀhdef, hsup]
  have hX : ¬ IsPGroup 2 (A ⊔ conjSubgroup A h : Subgroup G) := by
    intro h2
    have hAHH : A ⊔ conjSubgroup A h ≤ H := sup_le hAH hAhH
    have h2sub : IsPGroup 2 ↥((A ⊔ conjSubgroup A h).subgroupOf H) :=
      IsPGroup.of_equiv h2 (Subgroup.subgroupOfEquivOfLe hAHH).symm
    have h2img : IsPGroup 2
        ↥((((A ⊔ conjSubgroup A h).subgroupOf H).map ψ)) := h2sub.map ψ
    rw [hmap_sup] at h2img
    obtain ⟨n, hn⟩ := h2img.exists_card_eq
    rw [CFSG.Quasithin.SteinbergCB.nat_card_alternating_five] at hn
    have hnle : n ≤ 5 := by
      by_contra h
      have h6 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h6
      omega
    interval_cases n <;> norm_num at hn
  have hO : InCalO 2 (normalizer (A : Set G)) ⊥ A h :=
    inCalO_of_conj_inf_pCoreOf_le hAel hk.le hfb hh hX
  have hk' : E3.mQuot A (nVSub A h) = 2 := by
    rw [hB0]
    exact hk
  have hBne : nVSub A h ≠ ⊥ := by
    intro hbot
    rw [hbot, E3.mQuot_bot_eq_rk] at hk'
    omega
  have hmul : ∀ a ∈ A, a ∉ nVSub A h →
      ∀ a' ∈ conjSubgroup A h, a' ∉ bSub A h → a * a' ∈ twoResidual H := by
    intro a ha haU a' ha' ha'U
    have hodd : Odd (orderOf (a * a')) :=
      odd_orderOf_mul hAel hTI hBne ha haU ha' ha'U
    have hmem : a * a' ∈ H := H.mul_mem (hAH ha) (hAhH ha')
    exact CFSG.Quasithin.F6.mem_twoResidual_of_odd hmem hodd
  have hA_le_R : A ≤ twoResidual H :=
    le_of_mul_mem_of_mQuot_eq_two (R := twoResidual H) (U := nVSub A h)
      (A' := conjSubgroup A h) (U' := bSub A h) hAel inf_le_left hk'
      (fun hle => hO.1.1 (hle.trans inf_le_right)) hmul
  have hAh_le_R : conjSubgroup A h ≤ twoResidual H := by
    have hnorm : h ∈ Subgroup.normalizer ((twoResidual H : Subgroup G) : Set G) :=
      le_normalizer_twoResidual H hh
    have hconj : conjSubgroup (twoResidual H) h = twoResidual H :=
      (conjSubgroup_eq_iff_mem_normalizer).2 hnorm
    exact (E3.conjSubgroup_mono_left h hA_le_R).trans (le_of_eq hconj)
  have hX_le_R : A ⊔ conjSubgroup A h ≤ twoResidual H :=
    sup_le hA_le_R hAh_le_R
  have hR_le : twoResidual H ≤
      (A ⊔ conjSubgroup A h) ⊔ pCoreOf 2 (twoResidual H) := by
    intro r hr
    have hrH : r ∈ H := twoResidual_le H hr
    have hrA5 : ψ ⟨r, hrH⟩ ∈ alternatingGroup (Fin 5) := by
      have h := CFSG.GroupTheory.AlternatingFive.twoResidual_le_map_comap_alternatingGroup ψ hr
      obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp h
      have hy_eq : y = ⟨r, hrH⟩ := Subtype.ext hyr
      rw [hy_eq] at hy
      exact hy
    have hxmem : ψ ⟨r, hrH⟩ ∈
        (((A ⊔ conjSubgroup A h).subgroupOf H).map ψ) := by
      rw [hmap_sup]
      exact hrA5
    obtain ⟨x, hxX, hxψ⟩ := Subgroup.mem_map.mp hxmem
    have hxG_X : x.1 ∈ A ⊔ conjSubgroup A h := by
      have := hxX
      rwa [Subgroup.mem_subgroupOf] at this
    have hqH : x.1⁻¹ * r ∈ H := H.mul_mem (H.inv_mem x.2) hrH
    have hqker : ψ ⟨x.1⁻¹ * r, hqH⟩ = 1 := by
      have hsplit : (⟨x.1⁻¹ * r, hqH⟩ : ↥H) = x⁻¹ * ⟨r, hrH⟩ := by
        ext
        rfl
      rw [hsplit, map_mul, map_inv, hxψ, inv_mul_cancel]
    have hqQ : x.1⁻¹ * r ∈ pCoreOf 2 H := by
      have hmem : (⟨x.1⁻¹ * r, hqH⟩ : ↥H) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact hqker
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hqR : x.1⁻¹ * r ∈ twoResidual H :=
      (twoResidual H).mul_mem ((twoResidual H).inv_mem (hX_le_R hxG_X)) hr
    have hqO : x.1⁻¹ * r ∈ pCoreOf 2 (twoResidual H) :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (twoResidual_le H) ⟨hqR, hqQ⟩
    have hprod : x.1 * (x.1⁻¹ * r) ∈
        (A ⊔ conjSubgroup A h) ⊔ pCoreOf 2 (twoResidual H) :=
      ((A ⊔ conjSubgroup A h) ⊔ pCoreOf 2 (twoResidual H)).mul_mem
        (Subgroup.mem_sup_left hxG_X) (Subgroup.mem_sup_right hqO)
    rwa [show x.1 * (x.1⁻¹ * r) = r by group] at hprod
  refine ⟨h, hh, hO, le_antisymm hR_le ?_⟩
  exact sup_le hX_le_R
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (twoResidual H))

end CFSG.LocalAnalysis.WeakClosure81
