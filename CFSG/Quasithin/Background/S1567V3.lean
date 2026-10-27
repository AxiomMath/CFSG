module

public import CFSG.Quasithin.Background.S1567V2
public import CFSG.Quasithin.Background.S1567Z5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section MS

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem false_of_twoLocal_ge (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    {A : Subgroup G} (hAne : A ≠ ⊥) (hApg : IsPGroup 2 ↥A)
    (hTn : T ≤ Subgroup.normalizer (A : Set G)) (hXEn : XE153 E ≤ Subgroup.normalizer (A : Set G))
    (hYFn : YF153 Mc M E s ≤ Subgroup.normalizer (A : Set G)) : False := by
  have hloc : IsTwoLocal (Subgroup.normalizer (A : Set G)) := ⟨A, hAne, hApg, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hInM : InM T M' := ⟨hM', hTn.trans hle⟩
  rcases (k.c.hyp.lemma_15_3_2_three h11).mp hInM with rfl | rfl
  · exact r67.XE_not_le (fun x hx => hle (hXEn hx))
  · exact YF_not_le_Mc h11 h113 k gl (fun y hy => hle (hYFn hy))

theorem not_normal_char_TE (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    {C : Subgroup G} (hCT : C ≤ TE153 T E) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf (TE153 T E)).Characteristic)
    (hCG : G0_153 T Mc M E s ≤ Subgroup.normalizer (C : Set G)) : False := by
  have hCp : IsPGroup 2 ↥C := k.c.hyp.qtfe.sylow.1.to_le (hCT.trans inf_le_left)
  have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
    (T_le_normalizer_TE k.r66).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCT hchar)
  refine false_of_twoLocal_ge h11 h113 k r67 gl hC1 hCp hTn ?_ ?_
  · exact fun _ hx => hCG (Subgroup.mem_sup_right (Subgroup.mem_sup_left hx))
  · exact fun _ hy => hCG (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))

theorem centralizer_pCore_G0_le (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) :
    G0_153 T Mc M E s ⊓ Subgroup.centralizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G) ≤
      pCoreOf 2 (G0_153 T Mc M E s) := fun _ hx =>
  centralizer_V0_inf_G0_le_pCore k r67
    ⟨hx.1, Subgroup.centralizer_le (V0_le_pCore_NT r68) hx.2⟩

theorem not_G0_le_centralizer_Z (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    ¬ G0_153 T Mc M E s ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro h
  have hMc := k.c.hyp.lemma_15_3_4 h11
  have hY : YF153 Mc M E s ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun y hy => h (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
  exact YF_not_le_Mc h11 h113 k gl (hY.trans (le_of_eq hMc.symm))

theorem exists_two_ne_one_of_card_four67 {K : Subgroup G} (hK4 : Nat.card K = 4)
    (hK2 : ∀ x ∈ K, x * x = 1) : ∃ a ∈ K, ∃ b ∈ K, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hK4
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  by_contra hcon
  push Not at hcon
  have hle : K ≤ Subgroup.zpowers a := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · rw [hcon x hx a ha hx1 ha1']
      exact Subgroup.mem_zpowers a
  have h1 : Nat.card K ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf a ≤ 2 :=
    orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hK2 a ha)
  omega

theorem false_of_E4_le_centralizer_G0 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s)
    {K : Subgroup G} (hK4 : Nat.card K = 4) (hKT : K ≤ TE153 T E) (hK2 : ∀ x ∈ K, x * x = 1)
    (hKc : ∀ x ∈ K, ∀ g ∈ G0_153 T Mc M E s, x * g = g * x) : False := by
  have hSG : TE153 T E ≤ G0_153 T Mc M E s :=
    (le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left
  have hsT : s ∈ T := s_mem_T67 gl
  have hsS : s ∈ Subgroup.normalizer (TE153 T E : Set G) := T_le_normalizer_TE k.r66 hsT
  have hss : s * s ∈ TE153 T E := s_mul_s_mem_TE k gl
  have hKS : ∀ x ∈ K, ∀ u ∈ TE153 T E, x * u = u * x := fun x hx u hu => hKc x hx u (hSG hu)
  have hσS : ∀ x ∈ K, ∀ u ∈ TE153 T E, (s * x * s⁻¹) * u = u * (s * x * s⁻¹) := by
    intro x hx u hu
    have hu' : s⁻¹ * u * s ∈ TE153 T E := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (TE153 T E : Set G)).inv_mem hsS) u).mp hu
      simpa using this
    have h := hKS x hx _ hu'
    calc s * x * s⁻¹ * u = s * (x * (s⁻¹ * u * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * u * s) * x) * s⁻¹ := by rw [h]
      _ = u * (s * x * s⁻¹) := by group
  have hZ2 := k.c.hyp.lemma_15_3_2_two.2
  have hZuniq : ∀ z₁ ∈ quasithinOmegaOneCenter T, ∀ z₂ ∈ quasithinOmegaOneCenter T, z₁ ≠ 1 → z₂ ≠ 1 →
      z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂ n₁ n₂
    obtain ⟨y, -, hy'⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp hZ2
    have e1 : (⟨z₁, h₁⟩ : ↥(quasithinOmegaOneCenter T)) = y :=
      hy' _ (fun h => n₁ (congrArg Subtype.val h))
    have e2 : (⟨z₂, h₂⟩ : ↥(quasithinOmegaOneCenter T)) = y :=
      hy' _ (fun h => n₂ (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hmemZ : ∀ x : G, x ∈ T → (∀ g ∈ T, x * g = g * x) → x * x = 1 →
      x ∈ quasithinOmegaOneCenter T := by
    intro x hxT hxc hx2
    refine Subgroup.subset_closure ⟨⟨hxT, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr (fun g hg => (hxc g hg).symm)
    · rw [pow_two]
      exact hx2
  have hcentT : ∀ x : G, (∀ u ∈ TE153 T E, x * u = u * x) → x * s = s * x →
      ∀ g ∈ T, x * g = g * x := by
    intro x hxS hxs g hg
    rcases coset_of_relIndex_two k.r66.relIndex_two hg hsT gl.s_not_mem with h | h
    · exact hxS g h
    · have h1 := hxS _ h
      calc x * g = x * ((g * s⁻¹) * s) := by group
        _ = (x * (g * s⁻¹)) * s := by group
        _ = ((g * s⁻¹) * x) * s := by rw [h1]
        _ = (g * s⁻¹) * (x * s) := by group
        _ = (g * s⁻¹) * (s * x) := by rw [hxs]
        _ = g * x := by group
  have hcase : ∀ x ∈ K, x ≠ 1 → x * s = s * x → False := by
    intro x hx hx1 hxs
    have hxZ : x ∈ quasithinOmegaOneCenter T :=
      hmemZ x (hKT hx).1 (hcentT x (hKS x hx) hxs) (hK2 x hx)
    apply not_G0_le_centralizer_Z h11 h113 k gl
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      simp
    · rw [hZuniq z hz x hxZ hz1 hx1]
      exact hKc x hx g hg
  have hd : ∀ x ∈ K, x ≠ 1 → x * s ≠ s * x →
      x * (s * x * s⁻¹) ∈ quasithinOmegaOneCenter T ∧ x * (s * x * s⁻¹) ≠ 1 := by
    intro x hx hx1 hxs
    have hxT : x ∈ T := (hKT hx).1
    have hxx : x * x = 1 := hK2 x hx
    have hσσ : (s * x * s⁻¹) * (s * x * s⁻¹) = 1 := by
      calc (s * x * s⁻¹) * (s * x * s⁻¹) = s * (x * x) * s⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    have hcomm : (s * x * s⁻¹) * x = x * (s * x * s⁻¹) := hσS x hx x (hKT hx)
    have hdd : (x * (s * x * s⁻¹)) * (x * (s * x * s⁻¹)) = 1 := by
      calc (x * (s * x * s⁻¹)) * (x * (s * x * s⁻¹))
          = x * ((s * x * s⁻¹) * x) * (s * x * s⁻¹) := by group
        _ = x * (x * (s * x * s⁻¹)) * (s * x * s⁻¹) := by rw [hcomm]
        _ = (x * x) * ((s * x * s⁻¹) * (s * x * s⁻¹)) := by group
        _ = 1 := by rw [hxx, hσσ]; group
    have hdS : ∀ u ∈ TE153 T E, (x * (s * x * s⁻¹)) * u = u * (x * (s * x * s⁻¹)) := by
      intro u hu
      calc (x * (s * x * s⁻¹)) * u = x * ((s * x * s⁻¹) * u) := by group
        _ = x * (u * (s * x * s⁻¹)) := by rw [hσS x hx u hu]
        _ = (x * u) * (s * x * s⁻¹) := by group
        _ = (u * x) * (s * x * s⁻¹) := by rw [hKS x hx u hu]
        _ = u * (x * (s * x * s⁻¹)) := by group
    have he1 : s * (s * x * s⁻¹) * s⁻¹ = x := by
      have h := hKS x hx (s * s) hss
      calc s * (s * x * s⁻¹) * s⁻¹ = ((s * s) * x) * (s * s)⁻¹ := by group
        _ = (x * (s * s)) * (s * s)⁻¹ := by rw [h]
        _ = x := mul_inv_cancel_right _ _
    have hds : (x * (s * x * s⁻¹)) * s = s * (x * (s * x * s⁻¹)) := by
      have h1 : s * (x * (s * x * s⁻¹)) * s⁻¹ = x * (s * x * s⁻¹) := by
        calc s * (x * (s * x * s⁻¹)) * s⁻¹
            = (s * x * s⁻¹) * (s * (s * x * s⁻¹) * s⁻¹) := by group
          _ = (s * x * s⁻¹) * x := by rw [he1]
          _ = x * (s * x * s⁻¹) := hcomm
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    refine ⟨hmemZ _ (T.mul_mem hxT (T.mul_mem (T.mul_mem hsT hxT) (T.inv_mem hsT)))
      (hcentT _ hdS hds) hdd, ?_⟩
    intro h1
    apply hxs
    have h2 : s * x * s⁻¹ = x := by
      have h3 : s * x * s⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right hxx
    calc x * s = (s * x * s⁻¹) * s := by rw [h2]
      _ = s * x := by group
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one_of_card_four67 hK4 hK2
  have habK : a * b ∈ K := K.mul_mem ha hb
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right (hK2 a ha))).symm
  by_cases hA : a * s = s * a
  · exact hcase a ha ha1 hA
  by_cases hB : b * s = s * b
  · exact hcase b hb hb1 hB
  by_cases hAB : (a * b) * s = s * (a * b)
  · exact hcase (a * b) habK hab1 hAB
  obtain ⟨hdaZ, hda1⟩ := hd a ha ha1 hA
  obtain ⟨hdbZ, hdb1⟩ := hd b hb hb1 hB
  obtain ⟨-, hdab1⟩ := hd (a * b) habK hab1 hAB
  have e1 : a * (s * a * s⁻¹) = b * (s * b * s⁻¹) := hZuniq _ hdaZ _ hdbZ hda1 hdb1
  have hdd : (a * (s * a * s⁻¹)) * (a * (s * a * s⁻¹)) = 1 := by
    have hxx : a * a = 1 := hK2 a ha
    have hσσ : (s * a * s⁻¹) * (s * a * s⁻¹) = 1 := by
      calc (s * a * s⁻¹) * (s * a * s⁻¹) = s * (a * a) * s⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    have hcomm : (s * a * s⁻¹) * a = a * (s * a * s⁻¹) := hσS a ha a (hKT ha)
    calc (a * (s * a * s⁻¹)) * (a * (s * a * s⁻¹))
        = a * ((s * a * s⁻¹) * a) * (s * a * s⁻¹) := by group
      _ = a * (a * (s * a * s⁻¹)) * (s * a * s⁻¹) := by rw [hcomm]
      _ = (a * a) * ((s * a * s⁻¹) * (s * a * s⁻¹)) := by group
      _ = 1 := by rw [hxx, hσσ]; group
  have hbσa : (s * a * s⁻¹) * b = b * (s * a * s⁻¹) := hσS a ha b (hKT hb)
  have e3 : (a * b) * (s * (a * b) * s⁻¹) =
      (a * (s * a * s⁻¹)) * (b * (s * b * s⁻¹)) := by
    calc (a * b) * (s * (a * b) * s⁻¹) = a * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by group
      _ = a * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [hbσa]
      _ = (a * (s * a * s⁻¹)) * (b * (s * b * s⁻¹)) := by group
  apply hdab1
  rw [e3, ← e1]
  exact hdd

theorem isSQTKIn_G0 (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368NoTwo T Mc M E s) :
    IsSQTKIn (G0_153 T Mc M E s) := sqtkGroup_G0_NT c r68

theorem charTwo_G0 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) : CharTwo (G0_153 T Mc M E s) :=
  centralizer_pCore_G0_le k r67 r68

theorem ms2_G0 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s) :
    ∃ H' : Subgroup G, H' < G0_153 T Mc M E s ∧ ¬ 2 ∣ H'.relIndex (G0_153 T Mc M E s) ∧
      TE153 T E = pCoreOf 2 H' := by
  have hSyl := isSylowTwoOf_TE_G0_NT k.c k.L k.r66 r67 gl r68
  have hSG : TE153 T E ≤ G0_153 T Mc M E s := hSyl.1
  have hp : IsPGroup 2 ↥(TE153 T E) := k.c.hyp.qtfe.sylow.1.to_le inf_le_left
  refine ⟨TE153 T E, lt_of_le_of_ne hSG ?_, hSyl.2.2, ?_⟩
  · intro h
    refine r67.XE_not_le (fun x hx => ?_)
    have hxG : x ∈ G0_153 T Mc M E s := Subgroup.mem_sup_right (Subgroup.mem_sup_left hx)
    rw [← h] at hxG
    exact k.c.hyp.T_le hxG.1
  · exact le_antisymm (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hp)
      (pCoreOf_le 2 _)

theorem ms3_G0 (h11 : StageLemma14111) (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    ∀ C : Subgroup G, C ≤ TE153 T E → C ≠ ⊥ → (C.subgroupOf (TE153 T E)).Characteristic →
      ¬ G0_153 T Mc M E s ≤ Subgroup.normalizer (C : Set G) :=
  fun _ hCT hC1 hchar hCG => not_normal_char_TE h11 h113 k r67 gl hCT hC1 hchar hCG

theorem isMSPair_G0_TE_of_exists_L (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hL : ∃ L : Subgroup G, L ∈ cComp (G0_153 T Mc M E s) ∧
      ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G) ∧
      IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :
    IsMSPair (G0_153 T Mc M E s) (TE153 T E) :=
  ⟨⟨isSQTKIn_G0 k.c r68, charTwo_G0 k r67 r68, hL⟩, Or.inl (ms2_G0 k r67 gl r68),
    ms3_G0 h11 h113 k r67 gl⟩

end MS

end S1567

theorem stageTheorem1531_of_inputsLoc (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618Cat) (i44 : Stage15344) (i46 : Stage15346Four) (i49c : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (hI : Input15367Inspect) (h56 : AsB56)
    (hI1 : InspectListF618) (hNP : InspectRemainingNP) (hloc : Input15368PsiL3Loc) :
    StageTheorem1531 :=
  stageTheorem1531_of_inputsNoTwo h11 h113 hF i44 i46 i49c i50 i65
    (stage15367Rest_of_inspect h113 hI)
    (stage1531InspectBCatNoTwo_of_inputs_loc h11 h113 h56 hI1 hNP hloc)

end CFSG.Quasithin
