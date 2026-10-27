module

public import CFSG.Quasithin.H13.L32AC50f
public import CFSG.Quasithin.H13.L32AC50e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_Y (S : Setting147 G T L V H) {π : ↥H →* Equiv.Perm (Fin 7)}
    (hker : π.ker = CFSG.Open.pCore 2 ↥H) {R : Subgroup (Equiv.Perm (Fin 7))}
    (hTR : (T.subgroupOf H).map π ≤ R) (hRr : R ≤ π.range)
    (h3 : ((T.subgroupOf H).map π).relIndex R = 3)
    (hn : ¬ R ≤ Subgroup.normalizer
      (((T.subgroupOf H).map π : Subgroup (Equiv.Perm (Fin 7))) : Set (Equiv.Perm (Fin 7)))) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ H, oTwoUpper Y = Y ∧
      T ≤ Subgroup.normalizer (Y : Set G) ∧
      quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) ∧
      (∀ u (hu : u ∈ Y), π ⟨u, hYH hu⟩ ∈ R) ∧
      ∀ y ∈ R, y ^ 3 = 1 → ∃ u, ∃ hu : u ∈ Y, π ⟨u, hYH hu⟩ = y := by
  obtain ⟨h1, h2, h3'⟩ := s3_preim S hker hTR hRr h3 hn
  refine ⟨oTwoUpper (preim π R), (oTwoUpper_le _).trans (preim_le π R), h1, h2, h3', ?_, ?_⟩
  · intro u hu
    obtain ⟨hu', hR⟩ := mem_preim.mp (oTwoUpper_le _ hu)
    exact hR
  · intro y hy hy3
    obtain ⟨u, hu, hu', hπ⟩ := exists_lift_three hRr hy hy3
    exact ⟨u, hu, hπ⟩

theorem two_le_pRank_of_injective {A C : Type*} [Group A] [Group C] [Finite C] (ι : A →* C)
    (hι : Function.Injective ι) {P : Subgroup A} (hP : IsElementaryAbelian 3 P)
    (h9 : Nat.card P = 9) : 2 ≤ CFSG.pRank 3 C := by
  set P' := P.map ι with hP'
  let e : ↥P ≃* ↥P' := P.equivMapOfInjective ι hι
  have hP'e : IsElementaryAbelian 3 P' := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x', rfl⟩ := e.surjective x
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hP.toIsMulCommutative.is_comm.comm x' y']
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨x', rfl⟩ := e.surjective x
      rw [← map_pow,
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 P) x',
        map_one]
  exact two_le_pRank_of_e9 hP'e (by rw [← Nat.card_congr e.toEquiv, h9])

theorem false_of_six (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h2 : Lemma14_7_2) (h4 : Lemma14_7_4_two_three) (S : Setting147 G T L V H)
    {π : ↥H →* Equiv.Perm (Fin 7)} (hker : π.ker = CFSG.Open.pCore 2 ↥H)
    (hT : (π.range = ⊤ ∧ (T.subgroupOf H).map π = Alt7.tsSub) ∨
      (π.range = alternatingGroup (Fin 7) ∧ (T.subgroupOf H).map π = Alt7.taSub))
    {I : Subgroup G} (hV1I : fsuV1 T V ≤ I) (hIU : I < conjClosure V H)
    (hIn : H ≤ Subgroup.normalizer (I : Set G))
    {β : ↥(conjClosure V H) →* ↥(G6.coreMod 7)} (hβker : β.ker = I.subgroupOf (conjClosure V H))
    (hβ : ∀ (h : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = h * x * (h : G)⁻¹ →
      β x' = G6.coreAct 7 (π h) (β x)) : False := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp h13322 hMod h1222
  have hV1c : Nat.card (fsuV1 T V) = 2 := (hMod G T L V S.hyp.hyp S.hyp.fsu).2.2.2.1
  set PT := (T.subgroupOf H).map π with hPT
  have hcase : ∃ Ra Rb Rc : Subgroup (Equiv.Perm (Fin 7)),
      (PT ≤ Ra ∧ Ra ≤ π.range ∧ PT.relIndex Ra = 3 ∧
        ¬ Ra ≤ Subgroup.normalizer (PT : Set (Equiv.Perm (Fin 7)))) ∧
      (PT ≤ Rb ∧ Rb ≤ π.range ∧ PT.relIndex Rb = 3 ∧
        ¬ Rb ≤ Subgroup.normalizer (PT : Set (Equiv.Perm (Fin 7)))) ∧
      (PT ≤ Rc ∧ Rc ≤ π.range ∧ PT.relIndex Rc = 3 ∧
        ¬ Rc ≤ Subgroup.normalizer (PT : Set (Equiv.Perm (Fin 7)))) ∧
      Alt7.y1 ∈ Ra ∧ Alt7.y1 ^ 2 ∈ Ra ∧ Alt7.c012 ∈ Rb ∧ Alt7.c456 ∈ Rc ∧
      Alt7.c456 ^ 2 ∈ Rc ∧ (∀ r ∈ Rb, ∀ i, Alt7.e0123 (r⁻¹ i) = Alt7.e0123 i) ∧
      (∀ r ∈ Rc, ∀ i, Alt7.e0123 (r⁻¹ i) = Alt7.e0123 i) ∧ Alt7.taSub ≤ PT := by
    rcases hT with ⟨hR, hPTe⟩ | ⟨hR, hPTe⟩
    · rw [hPTe]
      refine ⟨Alt7.raSSub, Alt7.rbSSub, Alt7.rcSSub, ⟨Alt7.ts_sub_raS, by rw [hR]; exact le_top,
        relIndex_eq_three_of_card Alt7.ts_sub_raS (by rw [Alt7.card_raSSub, Alt7.card_tsSub]),
        not_le_normalizer_of Alt7.raS_not_normal⟩, ⟨Alt7.ts_sub_rbS, by rw [hR]; exact le_top,
        relIndex_eq_three_of_card Alt7.ts_sub_rbS (by rw [Alt7.card_rbSSub, Alt7.card_tsSub]),
        not_le_normalizer_of Alt7.rbS_not_normal⟩, ⟨Alt7.ts_sub_rcS, by rw [hR]; exact le_top,
        relIndex_eq_three_of_card Alt7.ts_sub_rcS (by rw [Alt7.card_rcSSub, Alt7.card_tsSub]),
        not_le_normalizer_of Alt7.rcS_not_normal⟩, Alt7.c456_facts.2.2.2.1,
        Alt7.c456_facts.2.2.2.2.1, Alt7.c456_facts.2.2.2.2.2.1, Alt7.c456_facts.1,
        Alt7.c456_facts.2.2.1, Alt7.e0123_fixed.1, Alt7.e0123_fixed.2,
        fun g hg => Alt7.ta_sub_ts g hg⟩
    · rw [hPTe]
      have hsgn : ∀ (l : List (Equiv.Perm (Fin 7))) (_ : ∀ a ∈ l, sign a = 1) a, a ∈ l →
          a ∈ π.range := fun l hl a ha => by rw [hR]; exact mem_alternatingGroup.mpr (hl a ha)
      refine ⟨Alt7.raASub, Alt7.rbASub, Alt7.rcASub, ⟨Alt7.ta_sub_raA,
        fun a ha => hsgn _ Alt7.raA_sign a ha,
        relIndex_eq_three_of_card Alt7.ta_sub_raA (by rw [Alt7.card_raASub, Alt7.card_taSub]),
        not_le_normalizer_of Alt7.raA_not_normal⟩, ⟨Alt7.ta_sub_rbA,
        fun a ha => hsgn _ Alt7.rbA_sign a ha,
        relIndex_eq_three_of_card Alt7.ta_sub_rbA (by rw [Alt7.card_rbASub, Alt7.card_taSub]),
        not_le_normalizer_of Alt7.rbA_not_normal⟩, ⟨Alt7.ta_sub_rcA,
        fun a ha => hsgn _ Alt7.rcA_sign a ha,
        relIndex_eq_three_of_card Alt7.ta_sub_rcA (by rw [Alt7.card_rcASub, Alt7.card_taSub]),
        not_le_normalizer_of Alt7.rcA_not_normal⟩, Alt7.three_facts.1, Alt7.three_facts.2.1,
        Alt7.three_facts.2.2.2.1, Alt7.c456_facts.2.2.2.2.2.2, Alt7.c456_facts.2.1,
        fun r hr => Alt7.e0123_fixed.1 r (Alt7.a_sub_s.2.1 r hr),
        fun r hr => Alt7.e0123_fixed.2 r (Alt7.a_sub_s.2.2 r hr), le_rfl⟩
  obtain ⟨Ra, Rb, Rc, ⟨ha1, ha2, ha3, ha4⟩, ⟨hb1, hb2, hb3, hb4⟩, ⟨hc1, hc2, hc3, hc4⟩,
    hy1, hy2, hab, hc456, hc456', hfb, hfc, hTA⟩ := hcase
  obtain ⟨Ya, hYaH, hYao, hTYa, hYaT, hYaR, hYal⟩ := exists_Y S hker ha1 ha2 ha3 ha4
  obtain ⟨Yb, hYbH, hYbo, hTYb, hYbT, hYbR, hYbl⟩ := exists_Y S hker hb1 hb2 hb3 hb4
  obtain ⟨Yc, hYcH, hYco, hTYc, hYcT, hYcR, hYcl⟩ := exists_Y S hker hc1 hc2 hc3 hc4
  have hVI := (h2 _ T L V H S I hV1I hIU hIn Yb V₂ hV2 hYbH hYbo hTYb hYbT).1
  have hV12 : fsuV1 T V ≤ V₂ := hV2.1
  obtain ⟨v, hv, hvV1⟩ : ∃ v ∈ V₂, v ∉ fsuV1 T V := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from hall)
    rw [hV2.2.2.2, hV1c] at this
    omega
  have hvU : v ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 hv)
  have hvI : v ∉ I := fun h => hvV1 (hVI ▸ ⟨hV2.2.1 hv, h⟩)
  set w := β ⟨v, hvU⟩ with hw
  have hw1 : w ≠ 1 := fun h => hvI (by
    have : (⟨v, hvU⟩ : ↥(conjClosure V H)) ∈ β.ker := h
    rw [hβker, Subgroup.mem_subgroupOf] at this
    exact this)
  have hcard12 : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by rw [hV2.2.2.2, hV1c]
  have htwo : ∀ v' (hv' : v' ∈ V₂), β ⟨v', le_conjClosure V H (hV2.2.1 hv')⟩ = 1 ∨
      β ⟨v', le_conjClosure V H (hV2.2.1 hv')⟩ = w := by
    intro v' hv'
    by_cases h1 : v' ∈ fsuV1 T V
    · left
      show (⟨v', _⟩ : ↥(conjClosure V H)) ∈ β.ker
      rw [hβker, Subgroup.mem_subgroupOf]
      exact hV1I h1
    · right
      have hm := L32NSet14.mul_mem_of_card_eq_two_mul hV12 hcard12 (by rw [hV1c]; norm_num)
        (V₂.inv_mem hv) hv' (fun h => hvV1 (by simpa using (fsuV1 T V).inv_mem h)) h1
      have hmU : v⁻¹ * v' ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 (V₂.mul_mem
        (V₂.inv_mem hv) hv'))
      have e : (⟨v', le_conjClosure V H (hV2.2.1 hv')⟩ : ↥(conjClosure V H)) =
          ⟨v, hvU⟩ * ⟨v⁻¹ * v', hmU⟩ := Subtype.ext (by simp)
      have hk : β ⟨v⁻¹ * v', hmU⟩ = 1 := by
        show (⟨v⁻¹ * v', hmU⟩ : ↥(conjClosure V H)) ∈ β.ker
        rw [hβker, Subgroup.mem_subgroupOf]
        exact hV1I hm
      rw [e, map_mul, hk, mul_one]
  have hfix : ∀ t ∈ Alt7.taList, G6.coreAct 7 t w = w := by
    intro t ht
    obtain ⟨t', ht', hπt⟩ := hTA ht
    have ht'H : (t' : G) ∈ H := t'.2
    have hconj : (t' : G) * v * (t' : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 ht') v).mp hv
    have e := hβ t' ⟨v, hvU⟩ ⟨(t' : G) * v * (t' : G)⁻¹, le_conjClosure V H (hV2.2.1 hconj)⟩ rfl
    rw [hπt] at e
    rcases htwo _ hconj with h | h
    · exact absurd (by rw [← e, h] : G6.coreAct 7 t w = 1)
        (fun h' => hw1 ((MulEquiv.map_eq_one_iff _).mp h'))
    · rw [← e, h]
  rcases Alt7.toAdd_fixed hfix with h0 | h45 | h0123 | h012345
  · exact hw1 (Alt7.coords_injective (h0.trans (by rfl)))
  ·
    obtain ⟨u₁, hu₁, hπu₁⟩ := hYal _ hy1 Alt7.three_facts.2.2.1
    obtain ⟨u₂, hu₂, hπu₂⟩ := hYal _ hy2 (by
      rw [← pow_mul, mul_comm, pow_mul, Alt7.three_facts.2.2.1, one_pow])
    refine false_of_three S hV1I hIU hIn hβker hβ h2 hV2 hYaH hYao hTYa hYaT hv hu₁ hu₂ ?_
    rw [hπu₁, hπu₂, ← hw, h45]
    exact Alt7.e45_rank
  ·
    have hcomm : ∀ (Y : Subgroup G) (hYH : Y ≤ H) (R : Subgroup (Equiv.Perm (Fin 7))),
        (∀ u (hu : u ∈ Y), π ⟨u, hYH hu⟩ ∈ R) →
        (∀ r ∈ R, ∀ i, Alt7.e0123 (r⁻¹ i) = Alt7.e0123 i) → ⁅V₂, Y⁆ ≤ I := by
      intro Y hYH R hYR hfR
      rw [Subgroup.commutator_le]
      intro v' hv' y hy
      have hv'U : v' ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 hv')
      have hyU : y * v'⁻¹ * y⁻¹ ∈ conjClosure V H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (hYH hy)) _).mp
          ((conjClosure V H).inv_mem hv'U)
      have hfixR : ∀ x : ↥(G6.coreMod 7), (Alt7.coords x = 0 ∨ Alt7.coords x = Alt7.e0123) →
          G6.coreAct 7 (π ⟨y, hYH hy⟩) x = x := by
        intro x hx
        apply Alt7.coords_injective
        funext i
        rw [Alt7.coords_coreAct]
        rcases hx with hx | hx
        · rw [hx]
          rfl
        · rw [hx]
          exact hfR _ (hYR y hy) i
      have hβv : Alt7.coords (β ⟨v', hv'U⟩) = 0 ∨ Alt7.coords (β ⟨v', hv'U⟩) = Alt7.e0123 := by
        rcases htwo v' hv' with h | h
        · left
          rw [h]
          rfl
        · right
          rw [h]
          exact h0123
      have e1 : β ⟨y * v'⁻¹ * y⁻¹, hyU⟩ = G6.coreAct 7 (π ⟨y, hYH hy⟩) (β ⟨v', hv'U⟩)⁻¹ := by
        rw [← map_inv]
        exact hβ ⟨y, hYH hy⟩ _ _ rfl
      have hm : ⁅v', y⁆ ∈ conjClosure V H := by
        rw [commutatorElement_def]
        have := (conjClosure V H).mul_mem hv'U hyU
        simpa [mul_assoc] using this
      have e2 : (⟨⁅v', y⁆, hm⟩ : ↥(conjClosure V H)) = ⟨v', hv'U⟩ * ⟨y * v'⁻¹ * y⁻¹, hyU⟩ :=
        Subtype.ext (by simp [commutatorElement_def, mul_assoc])
      have hk : β ⟨⁅v', y⁆, hm⟩ = 1 := by
        rw [e2, map_mul, e1, map_inv, hfixR _ hβv, mul_inv_cancel]
      have : (⟨⁅v', y⁆, hm⟩ : ↥(conjClosure V H)) ∈ β.ker := hk
      rw [hβker, Subgroup.mem_subgroupOf] at this
      exact this
    have hYbC := (h2 _ T L V H S I hV1I hIU hIn Yb V₂ hV2 hYbH hYbo hTYb hYbT).2.2
      (hcomm Yb hYbH Rb hYbR hfb)
    have hYcC := (h2 _ T L V H S I hV1I hIU hIn Yc V₂ hV2 hYcH hYco hTYc hYcT).2.2
      (hcomm Yc hYcH Rc hYcR hfc)
    have hYbC' : Yb ≤ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
        ((Subgroup.commutator_comm Yb V₂).trans hYbC)
    have hYcC' : Yc ≤ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
        ((Subgroup.commutator_comm Yc V₂).trans hYcC)
    obtain ⟨a, ha, hπa⟩ := hYbl _ hab Alt7.three_facts.2.2.2.2.2.1
    obtain ⟨b, hb, hπb⟩ := hYcl _ hc456 Alt7.three_facts.2.2.2.2.2.2.1
    set C := Subgroup.centralizer (V₂ : Set G) with hC
    set A := C ⊓ H with hA
    have haA : a ∈ A := ⟨hYbC' ha, hYbH ha⟩
    have hbA : b ∈ A := ⟨hYcC' hb, hYcH hb⟩
    let φ : ↥A →* Equiv.Perm (Fin 7) := π.comp (Subgroup.inclusion inf_le_right)
    have hφa : φ ⟨a, haA⟩ = Alt7.c012 := hπa
    have hφb : φ ⟨b, hbA⟩ = Alt7.c456 := hπb
    have hker2 : IsPGroup 2 φ.ker := by
      rintro ⟨k, hk⟩
      have hk' : Subgroup.inclusion inf_le_right k ∈ CFSG.Open.pCore 2 ↥H := by
        rw [← hker]
        exact hk
      have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥H) := by
        exact CFSG.pCore_isPGroup
      obtain ⟨n, hn⟩ := hp ⟨_, hk'⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z : CFSG.Open.pCore 2 ↥H => ((z : ↥H) : G)) hn
      simpa using this
    have hE : Alt7.e9Sub ≤ φ.range := by
      intro x hx
      obtain ⟨i, j, rfl⟩ := Alt7.mem_e9Sub.mp hx
      exact ⟨⟨a, haA⟩ ^ i * ⟨b, hbA⟩ ^ j, by rw [map_mul, map_pow, map_pow, hφa, hφb]⟩
    obtain ⟨P, hP, hP9⟩ := exists_e9_of_hom φ hker2 hE Alt7.card_e9Sub
      Alt7.e9_facts.2.2.1 Alt7.e9_facts.2.2.2
    have h2r := two_le_pRank_of_injective (Subgroup.inclusion (inf_le_left : A ≤ C))
      (Subgroup.inclusion_injective _) hP hP9
    have h1r := (h4 _ T L V V₂ S.hyp hV2).2.2.2.2
    have h2r' : 2 ≤ CFSG.pRank 3 ↥(Subgroup.centralizer (V₂ : Set G)) := h2r
    omega
  ·
    obtain ⟨u₁, hu₁, hπu₁⟩ := hYcl _ hc456 Alt7.three_facts.2.2.2.2.2.2.1
    obtain ⟨u₂, hu₂, hπu₂⟩ := hYcl _ hc456' (by
      rw [← pow_mul, mul_comm, pow_mul, Alt7.three_facts.2.2.2.2.2.2.1, one_pow])
    refine false_of_three S hV1I hIU hIn hβker hβ h2 hV2 hYcH hYco hTYc hYcT hv hu₁ hu₂ ?_
    rw [hπu₁, hπu₂, ← hw, h012345]
    exact Alt7.e012345_rank

end CFSG.Quasithin.H13.L32A.C
