module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613CfgDefs
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen

public section

namespace CFSG.StandardType

namespace L613Cfg

open Multiplicative CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4 CFSG.StandardType.L613KG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Comb

theorem zmod3_eq_one_or_two (z : ZMod 3) (hz : z ≠ 0) : z = 1 ∨ z = 2 := by
  revert z
  decide

theorem exists_other_pair : ∀ a b : Fin 4, a ≠ b →
    ∃ c d : Fin 4, c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  decide

theorem single_ne_zero_iff {a m : Fin 4} : (Pi.single a (1 : ZMod 3) : Fin 4 → ZMod 3) m ≠ 0 ↔
    m = a := by
  by_cases h : m = a
  · subst h
    simp
  · simp [h]

theorem eq_zero_of_plane {Dbar : AddSubgroup (Fin 4 → ZMod 3)} (hcard : Nat.card Dbar = 9)
    {a b : Fin 4} (hab : a ≠ b) (ha : (Pi.single a 1 : Fin 4 → ZMod 3) ∈ Dbar)
    (hb : (Pi.single b 1 : Fin 4 → ZMod 3) ∈ Dbar) {s : Fin 4 → ZMod 3} (hs : s ∈ Dbar)
    {m : Fin 4} (hma : m ≠ a) (hmb : m ≠ b) : s m = 0 := by
  classical
  set φ : ZMod 3 × ZMod 3 → Fin 4 → ZMod 3 :=
    fun p => p.1.val • (Pi.single a 1 : Fin 4 → ZMod 3) + p.2.val • Pi.single b 1 with hφ
  have hφa : ∀ p, φ p a = p.1 := fun p => by
    change (p.1.val • Pi.single a 1 + p.2.val • Pi.single b 1 : Fin 4 → ZMod 3) a = p.1
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hab, smul_zero, add_zero, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hφb : ∀ p, φ p b = p.2 := fun p => by
    change (p.1.val • Pi.single a 1 + p.2.val • Pi.single b 1 : Fin 4 → ZMod 3) b = p.2
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hab.symm, smul_zero, zero_add, nsmul_eq_mul, mul_one,
      ZMod.natCast_zmod_val]
  have hφm : ∀ p, φ p m = 0 := fun p => by
    change (p.1.val • Pi.single a 1 + p.2.val • Pi.single b 1 : Fin 4 → ZMod 3) m = 0
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne hma,
      Pi.single_eq_of_ne hmb, smul_zero, smul_zero, add_zero]
  have hinj : Function.Injective φ := fun p q h =>
    Prod.ext (by rw [← hφa p, h, hφa]) (by rw [← hφb p, h, hφb])
  have hsub : Set.range φ ⊆ (Dbar : Set (Fin 4 → ZMod 3)) := by
    rintro _ ⟨p, rfl⟩
    exact Dbar.add_mem (Dbar.nsmul_mem ha _) (Dbar.nsmul_mem hb _)
  have heq : Set.range φ = (Dbar : Set (Fin 4 → ZMod 3)) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_range_of_injective hinj, ← Nat.card_coe_set_eq, Nat.card_prod, Nat.card_zmod]
    exact hcard.le
  have hs' : s ∈ Set.range φ := by rw [heq]; exact hs
  obtain ⟨p, rfl⟩ := hs'
  exact hφm p

theorem exists_supp_two_or_three {Dbar : AddSubgroup (Fin 4 → ZMod 3)}
    (hcard : Nat.card Dbar = 9) :
    ∃ t ∈ Dbar, (supp t).card = 2 ∨ (supp t).card = 3 := by
  classical
  by_contra hno
  push Not at hno
  have key : ∀ i : Fin 4, ∃ j, j ≠ i ∧ (Pi.single j 1 : Fin 4 → ZMod 3) ∈ Dbar := by
    intro i
    have := Fintype.ofFinite Dbar
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩, huw, hi⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun t : Dbar => (t : Fin 4 → ZMod 3) i)
      (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]; norm_num)
    simp only at hi
    set c := u - w with hcdef
    have hc : c ∈ Dbar := Dbar.sub_mem hu hw
    have hc0 : c ≠ 0 := fun h => huw (Subtype.ext (sub_eq_zero.mp h))
    have hci : c i = 0 := by rw [hcdef, Pi.sub_apply, hi, sub_self]
    have hle : (supp c).card ≤ 3 := by
      have hsub : supp c ⊆ Finset.univ.erase i := fun m hm =>
        Finset.mem_erase.mpr ⟨fun h => (mem_supp.mp hm) (h ▸ hci), Finset.mem_univ _⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        at this
    have hpos : 0 < (supp c).card := by
      rw [Finset.card_pos]
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      apply hc0
      funext m
      by_contra hm
      have : m ∈ supp c := mem_supp.mpr hm
      rw [hemp] at this
      exact Finset.notMem_empty _ this
    obtain ⟨h2, h3⟩ := hno c hc
    have h1 : (supp c).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    have hcj : c j ≠ 0 := mem_supp.mp (by rw [hj]; exact Finset.mem_singleton_self j)
    have hcm : ∀ m, m ≠ j → c m = 0 := fun m hm => by
      by_contra h
      have : m ∈ supp c := mem_supp.mpr h
      rw [hj, Finset.mem_singleton] at this
      exact hm this
    have hji : j ≠ i := fun h => hcj (h ▸ hci)
    refine ⟨j, hji, ?_⟩
    rcases zmod3_eq_one_or_two (c j) hcj with h | h
    · have e : (Pi.single j 1 : Fin 4 → ZMod 3) = c := by
        funext m
        by_cases hm : m = j
        · subst hm
          rw [Pi.single_eq_same, h]
        · rw [Pi.single_eq_of_ne hm, hcm m hm]
      rw [e]
      exact hc
    · have e : (Pi.single j 1 : Fin 4 → ZMod 3) = c + c := by
        funext m
        by_cases hm : m = j
        · subst hm
          rw [Pi.single_eq_same, Pi.add_apply, h]
          decide
        · rw [Pi.single_eq_of_ne hm, Pi.add_apply, hcm m hm, add_zero]
      rw [e]
      exact Dbar.add_mem hc hc
  obtain ⟨j, -, hj⟩ := key 0
  obtain ⟨k, hkj, hk⟩ := key j
  have hsupp : supp ((Pi.single j 1 : Fin 4 → ZMod 3) + Pi.single k 1) = {j, k} := by
    ext m
    simp only [mem_supp, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply]
    by_cases hmj : m = j
    · subst hmj
      simp [Pi.single_eq_of_ne hkj.symm]
    · by_cases hmk : m = k
      · subst hmk
        simp [Pi.single_eq_of_ne hkj]
      · simp [hmj, hmk]
  have := (hno _ (Dbar.add_mem hj hk)).1
  rw [hsupp, Finset.card_pair hkj.symm] at this
  exact this rfl

end Comb

section Split

theorem frame_pow_three {H : Type*} [Group H] (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* H)
    (s : Fin 4 → ZMod 3) : ι₁ (ofAdd s) ^ 3 = 1 := by
  rw [← map_pow, ← ofAdd_nsmul]
  have h : (3 • s : Fin 4 → ZMod 3) = 0 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [h, ofAdd_zero, map_one]

theorem frame_comm {H : Type*} [Group H] (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* H)
    (s t : Fin 4 → ZMod 3) : ι₁ (ofAdd s) * ι₁ (ofAdd t) = ι₁ (ofAdd t) * ι₁ (ofAdd s) := by
  rw [← map_mul ι₁, ← map_mul ι₁, mul_comm (ofAdd s)]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem split {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    (hfr : ∀ s s' : Fin 4 → ZMod 3,
      (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s')
    (hdim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8)
    {Dbar : Set (Fin 4 → ZMod 3)} {J : Subgroup (Om8 K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' Dbar)))
    {t₀ : Fin 4 → ZMod 3} (ht₀ : t₀ ∈ Dbar) :
    ((∀ g ∈ J, ∀ w, act g (act (ι₁ (ofAdd t₀)) w - w) = act (ι₁ (ofAdd t₀)) w - w) ∧
        ∀ s, SuppLE s t₀ → ι₁ (ofAdd s) ∈ Subgroup.centralizer (J : Set (Om8 K))) ∨
      ∀ s : Fin 4 → ZMod 3, (∀ i, s i ≠ 0 → t₀ i = 0) →
        ι₁ (ofAdd s) ∈ Subgroup.centralizer (J : Set (Om8 K)) := by
  set H := Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' Dbar) with hHdef
  set y := ι₁ (ofAdd t₀) with hydef
  have hy3 : y ^ 3 = 1 := frame_pow_three ι₁ t₀
  have hyH : ∀ h ∈ H, h * y = y * h := fun h hh =>
    ((Subgroup.mem_centralizer_iff.mp hh) y ⟨t₀, ht₀, rfl⟩).symm
  have hframeH : ∀ s, ι₁ (ofAdd s) ∈ H := by
    intro s
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, -, rfl⟩
    exact frame_comm ι₁ t s
  let U : Subgroup (Om8 K) :=
    { carrier := {g | g ∈ H ∧ ∀ w, act g (act y w - w) = act y w - w}
      mul_mem' := fun {g g'} hg hg' => ⟨H.mul_mem hg.1 hg'.1, fun w => by
        rw [act_mul, hg'.2 w, hg.2 w]⟩
      one_mem' := ⟨H.one_mem, fun w => act_one _⟩
      inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, fun w => by
        conv_lhs => rw [← hg.2 w]
        rw [act_inv_act]⟩ }
  have hUH : U ≤ H := fun g hg => hg.1
  have hUn : (U.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUH]
    intro g h hg hh
    refine ⟨H.mul_mem (H.mul_mem hh hg.1) (H.inv_mem hh), fun w => ?_⟩
    have hh' : h⁻¹ * y = y * h⁻¹ := hyH _ (H.inv_mem hh)
    rw [act_mul, act_mul, act_comm_of_commute hh' w, hg.2 (act h⁻¹ w),
      act_comm_of_commute (hyH h hh) (act h⁻¹ w), act_act_inv]
  rcases ggComponent_le_or_commute hJ hUn.isSubnormal with hle | hc
  · refine Or.inl ⟨fun g hg => (hle hg).2, fun s hs => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact commute_of_fix hy3 (hyH g (hle hg).1) (hyH _ (hframeH s)) (hle hg).2
      (fun v hv => (hfr s t₀).mpr hs v hv)
  · refine Or.inr fun s hs => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hc g hg _ (Subgroup.mem_inf.mpr ⟨hframeH s, hframeH s,
      fun w => act_comm_of_disjoint hfr hdim hs w⟩)

end Split

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem centralizer_plane_eq {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    {Dbar : Set (Fin 4 → ZMod 3)} {a b : Fin 4} (hab : a ≠ b)
    (ha : (Pi.single a 1 : Fin 4 → ZMod 3) ∈ Dbar) (hb : (Pi.single b 1 : Fin 4 → ZMod 3) ∈ Dbar)
    (hplane : ∀ s ∈ Dbar, ∀ m, m ≠ a → m ≠ b → s m = 0) :
    Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' Dbar) =
      Subgroup.centralizer {ι₁ (ofAdd (Pi.single a 1)), ι₁ (ofAdd (Pi.single b 1))} := by
  refine le_antisymm (Subgroup.centralizer_le ?_) fun g hg => ?_
  · rintro _ (rfl | rfl)
    · exact ⟨_, ha, rfl⟩
    · exact ⟨_, hb, rfl⟩
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  rintro _ ⟨s, hs, rfl⟩
  have hga : Commute (ι₁ (ofAdd (Pi.single a 1))) g := hg _ (Set.mem_insert _ _)
  have hgb : Commute (ι₁ (ofAdd (Pi.single b 1))) g := hg _ (Set.mem_insert_of_mem _ rfl)
  have hdec : s = (s a).val • (Pi.single a 1 : Fin 4 → ZMod 3) + (s b).val • Pi.single b 1 := by
    funext m
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    by_cases hma : m = a
    · subst hma
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hab, smul_zero, add_zero, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val]
    · by_cases hmb : m = b
      · subst hmb
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hma, smul_zero, zero_add, nsmul_eq_mul,
          mul_one, ZMod.natCast_zmod_val]
      · rw [Pi.single_eq_of_ne hma, Pi.single_eq_of_ne hmb, smul_zero, smul_zero, add_zero,
          hplane s hs m hma hmb]
  have e : ι₁ (ofAdd s) = ι₁ (ofAdd (Pi.single a 1)) ^ (s a).val *
      ι₁ (ofAdd (Pi.single b 1)) ^ (s b).val := by
    conv_lhs => rw [hdec]
    rw [ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
  show ι₁ (ofAdd s) * g = g * ι₁ (ofAdd s)
  rw [e]
  exact ((hga.pow_left _).mul_left (hgb.pow_left _)).eq

theorem exists_supp_three (hOF : GGOmegaFourFactorInput) (hK3 : 3 ∣ Nat.card K - 1)
    {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    (hfr : ∀ s s' : Fin 4 → ZMod 3,
      (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s')
    (hdim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8)
    {Dbar : AddSubgroup (Fin 4 → ZMod 3)} (hcard : Nat.card Dbar = 9) {J : Subgroup (Om8 K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' (Dbar : Set (Fin 4 → ZMod 3)))))
    (hCJ : ∀ s, ι₁ (ofAdd s) ∈ Subgroup.centralizer (J : Set (Om8 K)) → s ∈ Dbar) :
    ∃ t ∈ Dbar, (supp t).card = 3 := by
  obtain ⟨t, htD, h2 | h3⟩ := exists_supp_two_or_three hcard
  swap
  · exact ⟨t, htD, h3⟩
  exfalso
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp h2
  obtain ⟨c, d, hcd, hac, had, hbc, hbd⟩ := exists_other_pair a b hab
  have hta : t a ≠ 0 := mem_supp.mp (by rw [hsupp]; exact Finset.mem_insert_self a {b})
  have htb : t b ≠ 0 := mem_supp.mp (by rw [hsupp]; simp)
  have htm : ∀ m, m ≠ a → m ≠ b → t m = 0 := fun m hma hmb => by
    by_contra h
    have hm := mem_supp.mpr h
    rw [hsupp, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h' | h'
    · exact hma h'
    · exact hmb h'
  have hdisj : ∀ m, m ≠ a → m ≠ b →
      ∀ i, (Pi.single m (1 : ZMod 3) : Fin 4 → ZMod 3) i ≠ 0 → t i = 0 := by
    intro m hma hmb i hi
    rw [single_ne_zero_iff] at hi
    subst hi
    exact htm _ hma hmb
  rcases split hfr hdim hJ htD with ⟨-, hin⟩ | hout
  · have hsuppa : SuppLE (Pi.single a 1) t := fun i hi => by
      rw [single_ne_zero_iff] at hi
      subst hi
      exact hta
    have hsuppb : SuppLE (Pi.single b 1) t := fun i hi => by
      rw [single_ne_zero_iff] at hi
      subst hi
      exact htb
    have hea : (Pi.single a 1 : Fin 4 → ZMod 3) ∈ Dbar := hCJ _ (hin _ hsuppa)
    have heb : (Pi.single b 1 : Fin 4 → ZMod 3) ∈ Dbar := hCJ _ (hin _ hsuppb)
    have hplane : ∀ s ∈ (Dbar : Set (Fin 4 → ZMod 3)), ∀ m, m ≠ a → m ≠ b → s m = 0 :=
      fun s hs m hma hmb => eq_zero_of_plane hcard hab hea heb hs hma hmb
    rcases split hfr hdim hJ (Dbar.add_mem hea heb) with ⟨htriv, -⟩ | hout2
    · rw [centralizer_plane_eq hab hea heb hplane] at hJ
      rcases hOF K hK3 ι₁ hfr hdim a b c d hab hcd hac had hbc hbd J hJ htriv with h | h
      · have hmem : (Pi.single c 1 + Pi.single d 1 : Fin 4 → ZMod 3) ∈ Dbar := hCJ _ (by
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact Subgroup.mem_centralizer_singleton_iff.mp (h hg))
        have h0 := hplane _ hmem c (Ne.symm hac) (Ne.symm hbc)
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcd, add_zero] at h0
        exact one_ne_zero h0
      · have hmem : (Pi.single c 1 - Pi.single d 1 : Fin 4 → ZMod 3) ∈ Dbar := hCJ _ (by
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact Subgroup.mem_centralizer_singleton_iff.mp (h hg))
        have h0 := hplane _ hmem c (Ne.symm hac) (Ne.symm hbc)
        rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcd, sub_zero] at h0
        exact one_ne_zero h0
    · have hdisj2 : ∀ i, (Pi.single c (1 : ZMod 3) : Fin 4 → ZMod 3) i ≠ 0 →
          (Pi.single a 1 + Pi.single b 1 : Fin 4 → ZMod 3) i = 0 := by
        intro i hi
        rw [single_ne_zero_iff] at hi
        subst hi
        rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hac), Pi.single_eq_of_ne (Ne.symm hbc),
          add_zero]
      have hec : (Pi.single c 1 : Fin 4 → ZMod 3) ∈ Dbar := hCJ _ (hout2 _ hdisj2)
      have h0 := hplane _ hec c (Ne.symm hac) (Ne.symm hbc)
      rw [Pi.single_eq_same] at h0
      exact one_ne_zero h0
  · have hec : (Pi.single c 1 : Fin 4 → ZMod 3) ∈ Dbar :=
      hCJ _ (hout _ (hdisj c (Ne.symm hac) (Ne.symm hbc)))
    have hed : (Pi.single d 1 : Fin 4 → ZMod 3) ∈ Dbar :=
      hCJ _ (hout _ (hdisj d (Ne.symm had) (Ne.symm hbd)))
    exact hta (eq_zero_of_plane hcard hcd hec hed htD hac had)

end Main

end L613Cfg

end CFSG.StandardType
