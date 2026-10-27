module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Ctx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111HSide
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111P1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Rank2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Set17B
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Triple
public import CFSG.Quasithin.EmptyFaithful.S152He13C
public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G]

theorem exists_z0 {T Mc M : Subgroup G} (h1515 : Lemma1515Concl T Mc M)
    (hV : V154 T Mc M ≠ ⊥) : ∃ z ∈ quasithinOmegaOneCenter T ⊓ V154 T Mc M, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hb : quasithinOmegaOneCenter T ⊓ V154 T Mc M = ⊥ :=
    eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hcon z hz)
  refine hV (le_bot_iff.mp ?_)
  calc V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M) :=
        h1515.gen
    _ ≤ ⊥ := conjClosure_le fun h _ z hz => by
        rw [hb] at hz
        rw [Subgroup.mem_bot.mp hz]
        simp

theorem eq_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hne
  have h3 : ({1, a, b} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, a, b, Ne.symm ha1, Ne.symm hb1, hne, rfl⟩
  have hsub : ({1, a, b} : Set G) ⊆ (A : Set G) := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hA' : (A : Set G).ncard = Nat.card A := (Nat.card_coe_set_eq (A : Set G)).symm
  omega

theorem rigidContradiction {T Mc M H D : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (h1416 : StageLemma1416) (h1515 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (hTM : T ≤ M) (hH : IsHStar T M H) (hV : ¬ V154 T Mc M ≤ pCoreOf 2 H)
    (ctx : Ctx15111 T Mc M H) (hDY : D ≤ conjClosure (V154 T Mc M) H)
    (hD : E2.IsExtraspecialPlus 2 D) (φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3))
    (hφs : Function.Surjective φ) (hφk : φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H))
    (hCore : Input15111YCoreFree) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVT : V154 T Mc M ≤ T := ctx.hyp28.le_T
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := hq.sylow.1
  obtain ⟨hrel, hnT⟩ := relIndex_eq_three hq hH ctx.normalizer_eq hVT hV hDY hD φ hφs hφk
  have hsolv : Group.IsSolvable H :=
    isSolvable_of_index_three (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm) hrel
      fun hn => hnT ((Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mp hn)
  obtain ⟨U, x, z, s, hext, φ', hφ's, hφ'k⟩ :=
    exists_setting17 ctx.hyp28 ctx.chartwo ctx.q32 ctx.res ctx.v16 hsolv
  have hHP := le_normalizer_dpP s φ' hφ's hφ'k
  obtain ⟨a, haA, haC, ha2⟩ := exists_involution_dpA s
  have haP : a ∈ E2.dpP H (V154 T Mc M) U z := Subgroup.mem_sup_right haA
  have haT : a ∈ T := s.dp.QT (dpP_le_pCoreOf s haP)
  have hP1 : P1Hyp T (V154 T Mc M) M :=
    ⟨hVT, hT2, hTM, ctx.normalizer_eq, ctx.om, h19.six_pCore, h19.six_charTwo, h19.six_autOn⟩
  obtain ⟨P1, c, hTP1, hP1M, hcP1, hc3, hcfree, hP1rel, hnP1⟩ :=
    hP1.exists_P1 haT ha2 haC fun r hr => comm_mem_V s hHP haP hr.1 hr.2
  have hHM : H ⊓ M = T := by
    have h1 := Subgroup.relIndex_mul_relIndex T (H ⊓ M) H (le_inf hTH hTM) inf_le_left
    rw [hrel] at h1
    have h2 : (H ⊓ M).relIndex H ≠ 1 := fun h2 =>
      hH.2.1 (inf_le_right.trans' (Subgroup.relIndex_eq_one.mp h2))
    have h3 : (H ⊓ M).relIndex H = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ h1) with h | h
      · exact absurd h h2
      · exact h
    rw [h3] at h1
    have h4 : T.relIndex (H ⊓ M) = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h4) (le_inf hTH hTM)
  have hPH : P1 ⊓ H = T :=
    le_antisymm (fun y hy => hHM ▸ ⟨hy.2, hP1M hy.1⟩) (le_inf hTP1 hTH)
  have htriple : F6.IsGoldschmidtTripleIn (P1 ⊔ H) P1 H :=
    isGoldschmidtTripleIn_of_index_three hq.sylow hTP1 hTH hPH hP1rel hrel hnP1 hnT
  set V := V154 T Mc M with hVdef
  have hV16 : Nat.card V = 16 := by simpa using ctx.v16
  have hVne : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV16
    omega
  obtain ⟨z0, hz0Z, hz01⟩ := exists_z0 h1515 hVne
  have hz0V : z0 ∈ V := hz0Z.2
  have hVP1 : V ≤ P1 := hVT.trans hTP1
  have hP1N : P1 ≤ Subgroup.normalizer (V : Set G) := ctx.normalizer_eq ▸ hP1M
  have hDH : E2.dpP H V U z ≤ H := (dpP_le_pCoreOf s).trans (pCoreOf_le 2 H)
  by_cases hbot : pCoreOf 2 (P1 ⊔ H) = ⊥
  · exact hCore G (P1 ⊔ H) P1 H V (E2.dpP H V U z) c htriple hbot hVP1 hP1N hV16
      ctx.hyp28.elem hV hcP1 hc3 hcfree hDH hHP hext
  have hTI : T ≤ P1 ⊔ H := hTP1.trans le_sup_left
  have hperf : perfectCore (P1 ⊔ H) ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    ((h1416 G T Mc hq).2.2.2 (P1 ⊔ H) ⟨hTI, hbot⟩).1
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥(P1 ⊔ H) :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr
        (stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hbot),
      kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hbot⟩
  have hVI : V ≤ P1 ⊔ H := hVP1.trans le_sup_left
  have hHI : H ≤ P1 ⊔ H := le_sup_right
  have hcI : c ∈ P1 ⊔ H := Subgroup.mem_sup_left hcP1
  have hzI : z ∈ P1 ⊔ H := Subgroup.mem_sup_right s.dp.zH
  have hV16' : Nat.card ↥(V.subgroupOf (P1 ⊔ H)) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv).trans hV16
  have hVP' : V.subgroupOf (P1 ⊔ H) ≤ P1.subgroupOf (P1 ⊔ H) := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hVP1 (Subgroup.mem_subgroupOf.mp hy))
  have hVn' : P1.subgroupOf (P1 ⊔ H) ≤
      Subgroup.normalizer ((V.subgroupOf (P1 ⊔ H) : Subgroup _) : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgN := Subgroup.mem_normalizer_iff.mp (hP1N (Subgroup.mem_subgroupOf.mp hg)) (y : G)
    simpa [Subgroup.mem_subgroupOf] using hgN
  have hVH' : ¬ V.subgroupOf (P1 ⊔ H) ≤ pCoreOf 2 (H.subgroupOf (P1 ⊔ H)) := by
    intro hle
    apply hV
    intro v hv
    have h1 : (⟨v, hVI hv⟩ : ↥(P1 ⊔ H)) ∈ pCoreOf 2 (H.subgroupOf (P1 ⊔ H)) :=
      hle (Subgroup.mem_subgroupOf.mpr hv)
    have h2 := CFSG.LieType.BorelTits.map_pCoreOf_le (r := 2) (P1 ⊔ H).subtype
      (H.subgroupOf (P1 ⊔ H))
    rw [Subgroup.map_subgroupOf_eq_of_le hHI] at h2
    exact h2 ⟨_, h1, rfl⟩
  have key := rank_two_perfect (c := (⟨c, hcI⟩ : ↥(P1 ⊔ H))) (ch := (⟨z, hzI⟩ : ↥(P1 ⊔ H)))
    htriple.subgroupOf hSQTK hV16' hVP' hVn' hVH'
    (Subgroup.mem_subgroupOf.mpr hcP1) (Subtype.ext (by simpa using hc3))
    (fun v hv hcv => by
      have := hcfree v (Subgroup.mem_subgroupOf.mp hv) (by simpa using congrArg Subtype.val hcv)
      exact Subtype.ext this)
    (Subgroup.mem_subgroupOf.mpr s.dp.zH) (Subtype.ext (by simpa using s.z3'))
  have hback : ∀ w : ↥(P1 ⊔ H), w ∈ perfectCore (⊤ : Subgroup ↥(P1 ⊔ H)) →
      (w : G) ∈ perfectCore (P1 ⊔ H) := by
    intro w hw
    have hmap := map_perfectCore (P1 ⊔ H).subtype (⊤ : Subgroup ↥(P1 ⊔ H))
    have e : (⊤ : Subgroup ↥(P1 ⊔ H)).map (P1 ⊔ H).subtype = P1 ⊔ H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [e] at hmap
    rw [← hmap]
    exact ⟨w, hw, rfl⟩
  have hnormI : P1 ⊔ H ≤ Subgroup.normalizer (perfectCore (P1 ⊔ H) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le _)).mp (perfectCore_normal _)
  rcases key with hc' | hz'
  ·
    have hcen := Subgroup.mem_centralizer_iff.mp (hperf (hback _ hc')) z0 hz0Z.1
    refine hz01 (hcfree z0 hz0V ?_)
    calc c * z0 * c⁻¹ = z0 * c * c⁻¹ := by rw [hcen]
      _ = z0 := by group
  ·
    have hzP := hback _ hz'
    have hzc : z0 * z = z * z0 := Subgroup.mem_centralizer_iff.mp (hperf hzP) z0 hz0Z.1
    have hczc : c⁻¹ * z * c ∈ perfectCore (P1 ⊔ H) := by
      have := (Subgroup.mem_normalizer_iff.mp (hnormI (Subgroup.inv_mem _ hcI)) z).mp hzP
      simpa using this
    have hzc' : z0 * (c⁻¹ * z * c) = (c⁻¹ * z * c) * z0 :=
      Subgroup.mem_centralizer_iff.mp (hperf hczc) z0 hz0Z.1
    have hz1c : (c * z0 * c⁻¹) * z = z * (c * z0 * c⁻¹) := by
      calc (c * z0 * c⁻¹) * z = c * (z0 * (c⁻¹ * z * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * z * c) * z0) * c⁻¹ := by rw [hzc']
        _ = z * (c * z0 * c⁻¹) := by group
    have hz1V : c * z0 * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hP1N hcP1) z0).mp hz0V
    have hz11 : c * z0 * c⁻¹ ≠ 1 := fun h1 => hz01 (by
      have : z0 = c⁻¹ * (c * z0 * c⁻¹) * c := by group
      rw [this, h1]
      group)
    have hz10 : c * z0 * c⁻¹ ≠ z0 := fun h1 => hz01 (hcfree z0 hz0V h1)
    have hcjV : cjSub z V = V := by
      rcases s.inf_eq s.zK with h | h
      · exact h
      · exfalso
        have hmem : ∀ y ∈ V, y * z = z * y → y ∈ E2.Setting17.Z0 H V := by
          intro y hy hyz
          rw [← h]
          refine ⟨hy, mem_cjSub.mpr ?_⟩
          have : z⁻¹ * y * z = y := by
            calc z⁻¹ * y * z = z⁻¹ * (y * z) := by group
              _ = y := by rw [hyz]; group
          rw [this]
          exact hy
        exact hz10 (eq_of_card_two s.Z0_card (hmem _ hz1V hz1c) (hmem _ hz0V hzc) hz11 hz01)
    have hzN : z ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_iff_cjSub_eq.mpr hcjV
    have hzT : z ∈ T := hHM ▸ ⟨s.dp.zH, ctx.normalizer_eq ▸ hzN⟩
    obtain ⟨k, hk⟩ := hT2 ⟨z, hzT⟩
    exact s.dp.z1 (E2.eq_one_of_odd_orderOf_of_pow_two_pow s.dp.zodd
      (by simpa using congrArg Subtype.val hk))

theorem input15111Y_of_coreFree (h15 : StageLemma1515CE) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h215 : E215) (h1416 : StageLemma1416)
    (hCore : Input15111YCoreFree) : SBc12.Input15111Y := by
  intro G _ _ T Mc M hq hM hCE H hH hV hD
  obtain ⟨D, hDY, -, hDext, φ, hφs, hφk⟩ := hD
  exact rigidContradiction hq h1416 (h15 G T Mc M hq hM hCE) (h159 G T Mc M hq hM hCE)
    hM.1.1.2 hH hV (ctx15111 h158 h159 h215 hq hM hCE hH hV) hDY hDext φ hφs hφk hCore

theorem input15111YRigid_of_coreFree (h15 : StageLemma1515CE) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h215 : E215) (h1416 : StageLemma1416)
    (hCore : Input15111YCoreFree) : He13.Input15111YRigid :=
  He13.input15111YRigid_of_input15111Y (input15111Y_of_coreFree h15 h158 h159 h215 h1416 hCore)

end Y15111

end CFSG.Quasithin
