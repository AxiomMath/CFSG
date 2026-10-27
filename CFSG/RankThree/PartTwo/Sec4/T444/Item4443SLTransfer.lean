module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLCore
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.Item4442Proof
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeisCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_normalizer_centralizer_of_le {I L : Subgroup Y}
    (hIL : I ≤ Subgroup.normalizer (L : Set Y)) :
    I ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) :=
  fun i hi => Subgroup.mem_normalizer_iff.mpr fun c =>
    ⟨fun hc => conj_mem_centralizer (hIL hi) hc, fun hc => by
      have := conj_mem_centralizer (Subgroup.inv_mem _ (hIL hi)) hc
      simpa [mul_assoc] using this⟩

theorem le_centralizer_of_quotient {I L T : Subgroup Y} (hTI : T ≤ I)
    [hTn : (T.subgroupOf I).Normal] (hT2 : IsPGroup 2 T)
    (eI : I ⧸ T.subgroupOf I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hIp : Group.IsPerfect I) (hLq : CFSG.IsQuasisimple L)
    (hLcard : Nat.card L = 20160 * Nat.card (L ⊓ Subgroup.centralizer (L : Set Y) : Subgroup Y))
    (hIL : I ≤ Subgroup.normalizer (L : Set Y))
    (hIC : I ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hnt : ¬ I ≤ Subgroup.centralizer (L : Set Y)) :
    T ≤ Subgroup.centralizer (L : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (L : Set Y) with hC
  have hIT : I ≤ Subgroup.normalizer (T : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTI).mp hTn
  have hIq : CFSG.IsQuasisimple (I ⧸ T.subgroupOf I) :=
    LocalCores.isQuasisimple_of_mulEquiv eI.symm isQuasisimple_SL
  have hTcard : Nat.card (T.subgroupOf I) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTI).toEquiv
  have hIcard : Nat.card I = 60480 * Nat.card T := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf I),
      Nat.card_congr eI.toEquiv, KFacts.KS14.card_SL_three_four, hTcard]
  have hICn := le_normalizer_centralizer_of_le hIL
  have hLCn := le_normalizer_centralizer_of_le (Subgroup.le_normalizer : L ≤ _)
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hK : Nat.card (I ⊓ C : Subgroup Y) ≤ 3 * Nat.card T := by
    set K : Subgroup I := (I ⊓ C).subgroupOf I with hKdef
    have hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      fun i hi => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hi, hICn hi⟩
    set f := QuotientGroup.mk' (T.subgroupOf I) with hf
    have hKfn : (K.map f).Normal := hKn.map f (QuotientGroup.mk'_surjective _)
    have hKcard : Nat.card K = Nat.card (I ⊓ C : Subgroup Y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rcases LocalCores.quasisimple_normal_subgroups hIq hKfn with htop | hcen
    ·
      exfalso
      apply hnt
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' K).comp (T.subgroupOf I).subtype) := by
        intro q
        obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective K q
        have hi : f i ∈ K.map f := htop ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hki⟩ := hi
        rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hki
        refine ⟨⟨k⁻¹ * i, hki⟩, ?_⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq]
        change (k⁻¹ * i)⁻¹ * i ∈ K
        rw [show (k⁻¹ * i)⁻¹ * i = i⁻¹ * k * i by group]
        have := hKn.conj_mem k hk i⁻¹
        simpa [mul_assoc] using this
      have hTs : Group.IsNilpotent (T.subgroupOf I) := (hT2.comap_subtype (K := I)).isNilpotent
      have hsolv : Group.IsSolvable (I ⧸ K) := Group.isSolvable_of_surjective hsurj
      have hperf : Group.IsPerfect (I ⧸ K) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective K)
      have hsub : Subsingleton (I ⧸ K) := by
        by_contra hnt'
        rw [not_subsingleton_iff_nontrivial] at hnt'
        exact Group.IsPerfect.not_isSolvable _ hsolv
      intro x hx
      have h1 : (QuotientGroup.mk' K ⟨x, hx⟩ : I ⧸ K) = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (Subgroup.mem_subgroupOf.mp h1).2
    ·
      have hZ3 : Nat.card (Subgroup.center (I ⧸ T.subgroupOf I)) = 3 := by
        rw [← KFacts.L34.card_center_specialLinearGroup KFacts.L34.card_galoisField_two_two,
          ← Subgroup.map_center_eq eI, Subgroup.card_map_of_injective eI.injective]
      have h1 := KFacts.KS18.card_eq_card_map_mul_card_inf_ker f K
      have h2 : Nat.card (K.map f) ≤ 3 := hZ3 ▸ Subgroup.card_le_of_le hcen
      have h3 : Nat.card ↥(K ⊓ f.ker) ≤ Nat.card T := by
        rw [hf, QuotientGroup.ker_mk', ← hTcard]
        exact Subgroup.card_le_of_le inf_le_right
      rw [← hKcard, h1]
      exact Nat.mul_le_mul h2 h3
  have hLIC : L ≤ I ⊔ C := by
    have h1 := Item4443SL.card_sup_mul_card_inf hICn
    have h2 := Item4443SL.card_sup_mul_card_inf hLCn
    rw [hIcard] at h1
    rw [hLcard] at h2
    have hZLpos : 0 < Nat.card (L ⊓ C : Subgroup Y) := Nat.card_pos
    have h3 : Nat.card (L ⊔ C : Subgroup Y) = 20160 * Nat.card C := by
      have h4 : Nat.card (L ⊔ C : Subgroup Y) * Nat.card (L ⊓ C : Subgroup Y) =
          (20160 * Nat.card C) * Nat.card (L ⊓ C : Subgroup Y) := by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right hZLpos h4
    have hle : I ⊔ C ≤ L ⊔ C := sup_le hIC le_sup_right
    have hge : Nat.card (L ⊔ C : Subgroup Y) ≤ Nat.card (I ⊔ C : Subgroup Y) := by
      rw [h3]
      by_contra hlt
      push Not at hlt
      have h5 : Nat.card (I ⊔ C : Subgroup Y) * Nat.card (I ⊓ C : Subgroup Y) <
          20160 * Nat.card C * (3 * Nat.card T) :=
        calc Nat.card (I ⊔ C : Subgroup Y) * Nat.card (I ⊓ C : Subgroup Y)
            ≤ Nat.card (I ⊔ C : Subgroup Y) * (3 * Nat.card T) := Nat.mul_le_mul_left _ hK
          _ < 20160 * Nat.card C * (3 * Nat.card T) :=
              Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      rw [h1] at h5
      nlinarith
    rw [Subgroup.eq_of_le_of_card_ge hle hge]
    exact le_sup_left
  have hTC : T ≤ Subgroup.normalizer (C : Set Y) := hTI.trans hICn
  have hTCset : ((T ⊔ C : Subgroup Y) : Set Y) = (T : Set Y) * (C : Set Y) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T C hTC
  have hNTC : I ⊔ C ≤ Subgroup.normalizer ((T ⊔ C : Subgroup Y) : Set Y) := by
    refine sup_le (fun i hi => Item4442.mem_normalizer_sup (hIT hi) (hICn hi))
      (le_sup_right.trans Subgroup.le_normalizer)
  set K' := L ⊓ (T ⊔ C) with hK'def
  have hK'n : (K'.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun l hl => ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hl, hNTC (hLIC hl)⟩
  rcases LocalCores.quasisimple_normal_subgroups hLq hK'n with htop | hcen
  ·
    exfalso
    have hLTC : L ≤ T ⊔ C := fun l hl => by
      have : (⟨l, hl⟩ : L) ∈ K'.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hdvd : Nat.card (L ⊔ C : Subgroup Y) ∣ Nat.card (T ⊔ C : Subgroup Y) :=
      Subgroup.card_dvd_of_le (sup_le hLTC le_sup_right)
    have h2 := Item4443SL.card_sup_mul_card_inf hLCn
    have h3 := Item4443SL.card_sup_mul_card_inf hTC
    rw [hLcard] at h2
    have h5 : Nat.card (L ⊔ C : Subgroup Y) = 20160 * Nat.card C := by
      have h6 : Nat.card (L ⊔ C : Subgroup Y) * Nat.card (L ⊓ C : Subgroup Y) =
          (20160 * Nat.card C) * Nat.card (L ⊓ C : Subgroup Y) := by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h6
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, h5] at h3
    have h6 : (20160 * m * Nat.card (T ⊓ C : Subgroup Y)) * Nat.card C =
        Nat.card T * Nat.card C := by rw [← h3]; ring
    have h7 := Nat.eq_of_mul_eq_mul_right hCpos h6
    have h3T : 3 ∣ Nat.card T := ⟨6720 * m * Nat.card (T ⊓ C : Subgroup Y), by rw [← h7]; ring⟩
    exact not_three_dvd_card_of_isPGroup_two hT2 h3T
  ·
    intro t ht
    have ht' : t ∈ ((L ⊔ C : Subgroup Y) : Set Y) := hIC (hTI ht)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C hLCn] at ht'
    obtain ⟨l, hl, c, hc, hlc⟩ := ht'
    have hlc' : l * c = t := hlc
    have hlK : l ∈ K' := by
      refine ⟨hl, ?_⟩
      have : l = t * c⁻¹ := by rw [← hlc']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc))
    have hlZ := hcen (Subgroup.mem_subgroupOf.mpr hlK : (⟨l, hl⟩ : L) ∈ K'.subgroupOf L)
    have hlC : l ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlZ ⟨y, hy⟩)
    rw [← hlc']
    exact Subgroup.mul_mem _ hlC hc

omit [Finite Y] in
theorem subgroupOf_le_normalizer_subgroupOf {H K N : Subgroup Y}
    (hHK : H ≤ Subgroup.normalizer (K : Set Y)) :
    H.subgroupOf N ≤ Subgroup.normalizer ((K.subgroupOf N : Subgroup N) : Set N) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hHK (Subgroup.mem_subgroupOf.mp hh)) k

omit [Finite Y] in
theorem mk_injective_of_inf_eq_bot {T H : Subgroup Y}
    (hHN : H ≤ Subgroup.normalizer (T : Set Y)) (hHT : H ⊓ T = ⊥) :
    Function.Injective ((QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set Y)))).comp
      (Subgroup.inclusion hHN)) := by
  have : (T.subgroupOf (Subgroup.normalizer (T : Set Y))).Normal := Subgroup.normal_in_normalizer
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  have hxT : (x : Y) ∈ T := Subgroup.mem_subgroupOf.mp hx
  have : (x : Y) ∈ H ⊓ T := ⟨x.2, hxT⟩
  rw [hHT] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))

omit [Finite Y] in
theorem range_mk_comp_inclusion {T H : Subgroup Y} (hHN : H ≤ Subgroup.normalizer (T : Set Y)) :
    ((QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set Y)))).comp
      (Subgroup.inclusion hHN)).range =
      (H.subgroupOf (Subgroup.normalizer (T : Set Y))).map
        (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set Y)))) := by
  have : (T.subgroupOf (Subgroup.normalizer (T : Set Y))).Normal := Subgroup.normal_in_normalizer
  rw [MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr h.2
  · intro hx
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

theorem le_of_quotient {A I L T : Subgroup Y} (hTI : T ≤ I) [hTn : (T.subgroupOf I).Normal]
    (hT2 : IsPGroup 2 T)
    (eI : I ⧸ T.subgroupOf I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hIp : Group.IsPerfect I) (hLq : CFSG.IsQuasisimple L)
    (hIL : I ≤ Subgroup.normalizer (L : Set Y))
    (hIC : I ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hnt : ¬ I ≤ Subgroup.centralizer (L : Set Y)) (hA : Late.IsE27 A)
    (hAI : A ≤ Subgroup.normalizer (I : Set Y)) (hAL : A ≤ Subgroup.normalizer (L : Set Y))
    (hAT : A ≤ Subgroup.normalizer (T : Set Y))
    (hinner : ∀ a ∈ A, ∃ i ∈ I, ∀ x ∈ I, (a * x * a⁻¹)⁻¹ * (i * x * i⁻¹) ∈ T)
    (h445 : ∀ y ∈ Subgroup.centralizer (A : Set Y), y ^ 3 = 1 → y ∈ A)
    (hZ : IsZ3L34OrHeisSL34 ↥(A ⊔ L)) : I ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hshape, -, -⟩ := shape_sup hA hAL hLq.1 hZ
  obtain ⟨hLcard, hZL3⟩ := card_of_shape hshape
  have hTC := le_centralizer_of_quotient hTI hT2 eI hIp hLq hLcard hIL hIC hnt
  set N := Subgroup.normalizer (T : Set Y) with hNdef
  have hIT : I ≤ N := (Subgroup.normal_subgroupOf_iff_le_normalizer hTI).mp hTn
  have hLN : L ≤ N := fun l hl => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp (hTC ht) l hl).symm)
  have : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  set q := QuotientGroup.mk' (T.subgroupOf N) with hq
  set Ab := (A.subgroupOf N).map q with hAb
  set Ib := (I.subgroupOf N).map q with hIb
  set Lb := (L.subgroupOf N).map q with hLb
  have hqT : ∀ x : N, q x = 1 ↔ (x : Y) ∈ T := fun x => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hLT : L ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : x ∈ L ⊓ Subgroup.centralizer (L : Set Y) := ⟨hx.1, hTC hx.2⟩
    have h1 : orderOf x ∣ 3 := by
      have := orderOf_dvd_natCard (⟨x, hxZ⟩ : (L ⊓ Subgroup.centralizer (L : Set Y) :
        Subgroup Y))
      rw [Subgroup.orderOf_mk] at this
      exact this.trans hZL3
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx.2⟩
    have h2 : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.mpr (KFacts.KS18.eq_one_of_pow_two_of_pow_three (m := k) (n := 1) h2
      (by rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mp h1))
  have hALT : (A ⊔ L) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx2 : ¬ 3 ∣ orderOf x := by
      intro h3
      obtain ⟨k, hk⟩ := hT2 ⟨x, hx.2⟩
      have h2 : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have := h3.trans (orderOf_dvd_of_pow_eq_one h2)
      exact absurd (Nat.prime_three.dvd_of_dvd_pow this) (by norm_num)
    have hxL : x ∈ L := Item4442.mem_of_mem_sup_of_isPGroup hA.isPGroup hAL hx.1 hx2
    rw [← hLT]
    exact ⟨hxL, hx.2⟩
  have hAT1 : A ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hALT ▸ (⟨Subgroup.mem_sup_left hx.1, hx.2⟩ : x ∈ (A ⊔ L) ⊓ T)
  set ψI := q.comp (Subgroup.inclusion hIT) with hψI
  have hψIrange : ψI.range = Ib := range_mk_comp_inclusion hIT
  have hψIker : ψI.ker = T.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, hψI, MonoidHom.comp_apply, hqT, Subgroup.mem_subgroupOf]
    rfl
  have eIb : Ib ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    ((MulEquiv.subgroupCongr hψIrange).symm.trans
      ((QuotientGroup.quotientKerEquivRange ψI).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hψIker))).trans eI
  have hALN : A ⊔ L ≤ N := sup_le hAT hLN
  set ψL := q.comp (Subgroup.inclusion hLN) with hψL
  have eLb : L ≃* Lb := (MonoidHom.ofInjective (mk_injective_of_inf_eq_bot hLN hLT)).trans
    (MulEquiv.subgroupCongr (range_mk_comp_inclusion hLN))
  have eAb : A ≃* Ab := (MonoidHom.ofInjective (mk_injective_of_inf_eq_bot hAT hAT1)).trans
    (MulEquiv.subgroupCongr (range_mk_comp_inclusion hAT))
  have hALb : Ab ⊔ Lb = ((A ⊔ L).subgroupOf N).map q := by
    rw [hAb, hLb, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hAT hLN]
  have eALb : ↥(A ⊔ L) ≃* ↥(Ab ⊔ Lb) :=
    (MonoidHom.ofInjective (mk_injective_of_inf_eq_bot hALN hALT)).trans
      (MulEquiv.subgroupCongr ((range_mk_comp_inclusion hALN).trans hALb.symm))
  have hLCn := le_normalizer_centralizer_of_le (Subgroup.le_normalizer : L ≤ _)
  have hTN3 : ¬ 3 ∣ Nat.card (T.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : T ≤ N)).toEquiv]
    exact not_three_dvd_card_of_isPGroup_two hT2
  have hcore : CoreHyp Ab Ib Lb := by
    refine ⟨⟨eIb⟩, LocalCores.isQuasisimple_of_mulEquiv eLb hLq,
      (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hIL)).trans
        (Subgroup.le_normalizer_map q), ?_, ?_, ?_,
      (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hAI)).trans
        (Subgroup.le_normalizer_map q),
      (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hAL)).trans
        (Subgroup.le_normalizer_map q), ?_, ?_, IsZ3L34OrHeisSL34.of_mulEquiv eALb hZ⟩
    ·
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ ((L ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) :=
        hIC (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLCn] at hx'
      obtain ⟨l, hl, c, hc, hlc⟩ := hx'
      have hcN : c ∈ N := by
        have : c = l⁻¹ * x := by rw [← hlc]; group
        rw [this]
        exact N.mul_mem (N.inv_mem (hLN hl)) x.2
      have hxe : x = ⟨l, hLN hl⟩ * ⟨c, hcN⟩ := Subtype.ext hlc.symm
      rw [hxe, map_mul]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨l, hLN hl⟩,
        Subgroup.mem_subgroupOf.mpr hl, rfl⟩) (Subgroup.mem_sup_right ?_)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l', hl', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc _ (Subgroup.mem_subgroupOf.mp hl'))
    ·
      intro hle
      apply hnt
      intro i hi
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := Subgroup.mem_centralizer_iff.mp (hle ⟨⟨i, hIT hi⟩, Subgroup.mem_subgroupOf.mpr hi,
        rfl⟩) (q ⟨l, hLN hl⟩) ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      rw [← map_mul, ← map_mul, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      have hw : (l * i)⁻¹ * (i * l) ∈ L ⊓ T := by
        refine ⟨?_, by simpa using h1⟩
        have h2 : i⁻¹ * l⁻¹ * i ∈ L :=
          (Subgroup.mem_normalizer_iff''.mp (hIL hi) _).mp (L.inv_mem hl)
        have h3 : (l * i)⁻¹ * (i * l) = (i⁻¹ * l⁻¹ * i) * l := by group
        rw [h3]
        exact L.mul_mem h2 hl
      rw [hLT, Subgroup.mem_bot] at hw
      have := congrArg (l * i * ·) hw
      simp only [mul_one, mul_inv_cancel_left] at this
      exact this.symm
    ·
      refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, by rw [← Nat.card_congr eAb.toEquiv, hA.2]⟩
      · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
        obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
        apply Subtype.ext
        change q a * q b = q b * q a
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (show (a : Y) * b = b * a from congrArg Subtype.val
          (hA.1.1.is_comm.comm (⟨a, Subgroup.mem_subgroupOf.mp ha⟩ : A)
            ⟨b, Subgroup.mem_subgroupOf.mp hb⟩))
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow]
        have : a ^ 3 = 1 := Subtype.ext (by
          simpa using hA.1.2 (a : Y) (Subgroup.mem_subgroupOf.mp ha))
        rw [this, map_one]
    ·
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨i, hi, hai⟩ := hinner a (Subgroup.mem_subgroupOf.mp ha)
      refine ⟨q ⟨i, hIT hi⟩, ⟨⟨i, hIT hi⟩, Subgroup.mem_subgroupOf.mpr hi, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, hq,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simpa using hai (x : Y) (Subgroup.mem_subgroupOf.mp hx)
    ·
      intro y hy hy3
      have hAp : IsPGroup 3 (A.subgroupOf N) := hA.isPGroup.comap_subtype
      obtain ⟨w, hwC, hw3, rfl⟩ := exists_lift_pow_three_eq_one hTN3 hAp hy hy3
      have hwA : (w : Y) ∈ A := by
        refine h445 _ ?_ (by simpa using congrArg Subtype.val hw3)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hwC ⟨a, hAT ha⟩
          (Subgroup.mem_subgroupOf.mpr ha))
      exact ⟨w, Subgroup.mem_subgroupOf.mpr hwA, rfl⟩
  have hIbL := hcore.le
  have hILT : ∀ i ∈ I, ∃ l ∈ L, l⁻¹ * i ∈ T := by
    intro i hi
    obtain ⟨l, hl, hli⟩ := hIbL ⟨⟨i, hIT hi⟩, Subgroup.mem_subgroupOf.mpr hi, rfl⟩
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hli
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, by simpa using hli⟩
  set K : Subgroup I := (I ⊓ L).subgroupOf I with hKdef
  have hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    fun i hi => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hi, hIL hi⟩
  have hsurj : Function.Surjective ((QuotientGroup.mk' K).comp (T.subgroupOf I).subtype) := by
    intro qq
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective K qq
    obtain ⟨l, hl, hlt⟩ := hILT i i.2
    refine ⟨⟨⟨l⁻¹ * i, hTI hlt⟩, Subgroup.mem_subgroupOf.mpr hlt⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact I.mul_mem (I.inv_mem (hTI hlt)) i.2
    · change (l⁻¹ * (i : Y))⁻¹ * i ∈ L
      rw [show (l⁻¹ * (i : Y))⁻¹ * i = (i : Y)⁻¹ * l * i by group]
      exact (Subgroup.mem_normalizer_iff''.mp (hIL i.2) l).mp hl
  have hTs : Group.IsNilpotent (T.subgroupOf I) := (hT2.comap_subtype (K := I)).isNilpotent
  have hsolv : Group.IsSolvable (I ⧸ K) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (I ⧸ K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective K)
  have hsub : Subsingleton (I ⧸ K) := by
    by_contra hnt'
    rw [not_subsingleton_iff_nontrivial] at hnt'
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro x hx
  have h1 : (QuotientGroup.mk' K ⟨x, hx⟩ : I ⧸ K) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (Subgroup.mem_subgroupOf.mp h1).2

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
