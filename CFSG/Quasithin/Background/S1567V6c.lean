module

public import CFSG.Quasithin.Background.S1567V6b
public import CFSG.Quasithin.Background.S1567V4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Matrix commutatorElement

namespace S1567

section Glue

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem map_eq_top_of_mem_cComp (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))))
    {L : Subgroup G} (hL : L ∈ cComp (G0_153 T Mc M E s)) :
    (L.subgroupOf (G0_153 T Mc M E s)).map
      (QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))) = ⊤ := by
  obtain ⟨e⟩ := exists_quotEquiv_L32 r68 hL3
  have : IsSimpleGroup ↥(CFSG.Open.StatedSL 3 (ZMod 2)) :=
    S153E59.isSimpleGroup_statedSL_three_two
  have : IsSimpleGroup (↥(G0_153 T Mc M E s) ⧸
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s)) := e.isSimpleGroup
  have hK := (cComp_pCore_bijOn (G0_153 T Mc M E s)).mapsTo hL
  obtain ⟨hnt, -, hsub, -⟩ := hK
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance
    (A3.subnormal_top_iff.mp hsub) with h | h
  · exact absurd h hnt
  · exact h

theorem exists_mul_of_mem_cComp (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))))
    {L : Subgroup G} (hL : L ∈ cComp (G0_153 T Mc M E s)) :
    ∀ g ∈ G0_153 T Mc M E s, ∃ l ∈ L, ∃ q ∈ pCoreOf 2 (G0_153 T Mc M E s), g = l * q := by
  intro g hg
  have hmap := map_eq_top_of_mem_cComp r68 hL3 hL
  have hmem : QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))
      (⟨g, hg⟩ : ↥(G0_153 T Mc M E s)) ∈
      (L.subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.mp hmem
  have hq : l⁻¹ * (⟨g, hg⟩ : ↥(G0_153 T Mc M E s)) ∈
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s) :=
    QuotientGroup.eq.mp hlg
  rw [Subgroup.mem_subgroupOf] at hq hl
  refine ⟨(l : G), hl, (l : G)⁻¹ * g, hq, ?_⟩
  simp

theorem alpha153_eq_one_of_perfect (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (ld : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) {L : Subgroup G} (hLG : L ≤ G0_153 T Mc M E s)
    (hperf : ⁅L, L⁆ = L) :
    ∀ x ∈ L, ∃ hx : x ∈ G0_153 T Mc M E s,
      alpha153 T Mc M E s r68.le_normalizer ⟨x, hx⟩ = 1 := by
  have hcard := card_mulAut_quot_YE h113 c ld r66
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E))) :=
    isCyclic_of_prime_card hcard
  have hcomm : IsMulCommutative (MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E))) :=
    (MonoidHom.id _).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
  have hker : ⁅L, L⁆ ≤ (alpha153 T Mc M E s r68.le_normalizer).ker.map
      (G0_153 T Mc M E s).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, hLG hg₁⟩ : ↥(G0_153 T Mc M E s)), ⟨g₂, hLG hg₂⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hker (hperf ▸ hx)
  subst hyx
  exact ⟨y.2, hy⟩

end Glue

section Main

theorem case3Excl (h113 : StageLemma14113) : Case3Excl := by
  classical
  intro G _ _ T Mc M V₁ V₂ E t s L c r45 r46 r49 r50 ld r66 r67 gl r68 hL3 hL hN hprod h3
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, ld, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  have hLG : L ≤ G0_153 T Mc M E s := le_of_mem_cComp hL
  obtain ⟨⟨n, F, _, _, α', hFn, ⟨hα's, hα'k⟩, h1, h2⟩, -⟩ := h3
  obtain ⟨e⟩ := exists_quotEquiv_L32 r68 hL3
  obtain ⟨α₀, hα₀s, hα₀k⟩ := exists_modO2Surj hLG hN e (map_eq_top_of_mem_cComp r68 hL3 hL)
  have hF2 : Fintype.card F = 2 := card_field_eq_two α₀ hα₀s hα₀k α' hα's hα'k
  have hm : Case3Mod L (c134Q (G0_153 T Mc M E s) L) α' := ⟨hF2, hα's, h1, h2⟩
  have hmul := exists_mul_of_mem_cComp r68 hL3 hL
  have hV₀ab : IsElemAbelian 2 (V0_153 T Mc M E s) :=
    isElemAbelian_V0_NoTwo k.c k.r46 k.L k.r66 r67 gl r68
  have hV₀N : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hV₀L : L ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hLG.trans hV₀N
  have hV₀Q : V0_153 T Mc M E s ≤ c134Q (G0_153 T Mc M E s) L :=
    (V0_le_Q k gl r68).trans
      (Subgroup.commutator_mono le_rfl (oTwoUpper_G0_le_of_mul_TE k hN hLG hprod))
  have hV₀64 : 64 ≤ Nat.card (V0_153 T Mc M E s) :=
    (sixtyFour_le_card_VE67 k r67).trans (Subgroup.card_le_of_le (VE67_le_V0 k r67))
  have hVG : V0_153 T Mc M E s ≤ G0_153 T Mc M E s := V0_le_G0_NT r68
  have hQT : pCoreOf 2 (G0_153 T Mc M E s) ≤ TE153 T E :=
    pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple
  have hXQ : ¬ XE153 E ≤ pCoreOf 2 (G0_153 T Mc M E s) := fun h =>
    r67.XE_not_le fun x hx => k.c.hyp.T_le (hQT (h hx)).1
  obtain ⟨A, hA, hAQ⟩ : ∃ A, IsMaxElemAbelian (G0_153 T Mc M E s) A ∧
      ¬ A ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
    by_contra hcon
    push Not at hcon
    exact hXQ ((XE_le_thompsonJ_NT k.c k.L k.r66 r67 gl r68).trans
      (iSup₂_le fun A hA => hcon A hA : thompsonJ (G0_153 T Mc M E s) ≤ _))
  have hAG : A ≤ G0_153 T Mc M E s := hA.1
  have hAN : A ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hAG.trans hV₀N
  have hAα : ∀ a ∈ A, ∃ ha : a ∈ G0_153 T Mc M E s,
      alpha153 T Mc M E s r68.le_normalizer ⟨a, ha⟩ = 1 := fun a ha =>
    alpha153_eq_one_of_mem_thompsonJ k.c k.L k.r66 r67 gl r68 (B6.le_thompsonJ hA ha)
  have hLα := alpha153_eq_one_of_perfect h113 k.c k.L k.r66 r68 hLG hL.2.1
  have hQα : ∀ q ∈ pCoreOf 2 (G0_153 T Mc M E s), ∀ hq : q ∈ G0_153 T Mc M E s,
      alpha153 T Mc M E s r68.le_normalizer ⟨q, hq⟩ = 1 →
        q ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := fun q hq hqG h =>
    pCore_inf_ker_alpha_le_centralizer_V0 h113 k r67 gl r68 hq hqG h
  have hCQ : ∀ x ∈ G0_153 T Mc M E s, x ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) →
      x ∈ pCoreOf 2 (G0_153 T Mc M E s) := fun x hx hc =>
    centralizer_V0_inf_G0_le_pCore k r67 ⟨hx, hc⟩
  have hAfac : ∀ a ∈ A, ∃ l ∈ L, ∃ q ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G), a = l * q := by
    intro a ha
    obtain ⟨haG, ha1⟩ := hAα a ha
    obtain ⟨l, hl, q, hq, rfl⟩ := hmul a haG
    obtain ⟨hlG, hl1⟩ := hLα l hl
    refine ⟨l, hl, q, ?_, rfl⟩
    have hqG : q ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hq
    apply hQα q hq hqG
    have e1 : (⟨q, hqG⟩ : ↥(G0_153 T Mc M E s)) = (⟨l, hlG⟩ : ↥(G0_153 T Mc M E s))⁻¹ *
        ⟨l * q, haG⟩ := by
      ext
      simp
    rw [e1, map_mul, map_inv, hl1, ha1]
    simp
  have hÂL : autI hV₀ab A ≤ autI hV₀ab L := by
    intro φ hφ
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := (mem_autI hV₀ab).1 hφ
    obtain ⟨l, hl, q, hq, hlq⟩ := hAfac a haA
    have hlN : l ∈ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hV₀L hl
    have hqN : q ∈ Subgroup.normalizer (V0_153 T Mc M E s : Set G) :=
      Subgroup.centralizer_le_normalizer _ hq
    have e1 : (⟨a, haN⟩ : ↥(Subgroup.normalizer (V0_153 T Mc M E s : Set G))) =
        ⟨l, hlN⟩ * ⟨q, hqN⟩ := by
      ext
      exact hlq
    have : convI hV₀ab ⟨a, haN⟩ = convI hV₀ab ⟨l, hlN⟩ := by
      rw [e1, map_mul, (convI_eq_one_iff hV₀ab ⟨q, hqN⟩).2 hq, mul_one]
    rw [this]
    exact convI_mem_autI hV₀ab hl hlN
  have hoff := (offender_core hV₀ab hVG hV₀N hA
    (bot_le : (⊥ : Subgroup (MulAut (IntMod (V0_153 T Mc M E s) hV₀ab))) ≤ autI hV₀ab A)).1
  rw [B1.card_bot_mul_card_fixV] at hoff
  have hDL : preI hV₀ab L hV₀L (autI hV₀ab A) ≤ L := preI_le hV₀ab
  have hDN : preI hV₀ab L hV₀L (autI hV₀ab A) ≤
      Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hDL.trans hV₀L
  have hautD : autI hV₀ab (preI hV₀ab L hV₀L (autI hV₀ab A)) = autI hV₀ab A :=
    autI_preI hV₀ab hÂL
  have hcardD : Nat.card (preI hV₀ab L hV₀L (autI hV₀ab A)) =
      Nat.card (autI hV₀ab A) * Nat.card ↥(L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) :=
    card_preI hV₀ab hÂL
  have hfixD : Nat.card (fixV (autI hV₀ab A)) = Nat.card ↥(V0_153 T Mc M E s ⊓
      Subgroup.centralizer ((preI hV₀ab L hV₀L (autI hV₀ab A) : Subgroup G) : Set G)) := by
    have := card_fixV_autI hV₀ab hDN
    rwa [hautD] at this
  let cI : ↥L →* MulAut (IntMod (V0_153 T Mc M E s) hV₀ab) := convHom hV₀ab L hV₀L
  have hDmem : ∀ x : ↥L, (x : G) ∈ preI hV₀ab L hV₀L (autI hV₀ab A) → cI x ∈ autI hV₀ab A :=
    fun x hx => ((mem_preI hV₀ab).1 hx).2
  generalize hDdef : preI hV₀ab L hV₀L (autI hV₀ab A) = D at hDL hDN hautD hcardD hfixD hDmem
  have hker : ∀ x : ↥L, (x : G) ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) → α' x = 1 := by
    intro x hx
    have hxQ : (x : G) ∈ pCoreOf 2 L := by
      rw [pCoreOf_eq_inf_of_normal hLG hN]
      exact ⟨x.2, hCQ _ (hLG x.2) hx⟩
    have h3 : x ∈ CFSG.pCore 2 ↥L := (mem_pCoreOf_iff_mem_pCore67 x).1 hxQ
    rw [← hα'k] at h3
    exact h3
  have hker' : ∀ x : ↥L, α' x = 1 →
      (x : G) ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := by
    intro x hx
    have h3 : x ∈ CFSG.pCore 2 ↥L := by rw [← hα'k]; exact hx
    have h4 : (x : G) ∈ pCoreOf 2 L := (mem_pCoreOf_iff_mem_pCore67 x).2 h3
    rw [pCoreOf_eq_inf_of_normal hLG hN] at h4
    obtain ⟨hxG, hx1⟩ := hLα _ x.2
    exact hQα _ h4.2 hxG hx1
  have hcI_ker : ∀ x : ↥L, cI x = 1 → α' x = 1 := by
    intro x hx
    apply hker
    have h3 : x ∈ cI.ker := hx
    rw [show cI.ker = _ from ker_convHom hV₀ab L hV₀L, Subgroup.mem_subgroupOf] at h3
    exact h3.2
  have hÂab := isElemAbelian2_autI hV₀ab hA.2.1 hAN
  have hcomm : ∀ x y : ↥L, (x : G) ∈ D → (y : G) ∈ D → α' x * α' y = α' y * α' x := by
    intro x y hx hy
    have h1 : cI (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hÂab.1 _ (hDmem x hx) _ (hDmem y hy)]
      simp
    have h2 := hcI_ker _ h1
    rw [map_mul, map_mul, map_inv, map_mul, mul_inv_eq_one] at h2
    exact h2
  have hsq : ∀ x : ↥L, (x : G) ∈ D → α' x * α' x = 1 := by
    intro x hx
    have h1 : cI (x * x) = 1 := by
      rw [map_mul, ← pow_two]
      exact hÂab.2 _ (hDmem x hx)
    have h2 := hcI_ker _ h1
    rwa [map_mul] at h2
  have hΛab : IsElemAbelian 2 (imGL L D α') := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, haD, ha⟩ := mem_imGL.mp x.2
      obtain ⟨b, hbD, hb⟩ := mem_imGL.mp y.2
      show (x : Matrix.GeneralLinearGroup (Fin 3) F) * y = y * x
      rw [← ha, ← hb, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm a b haD hbD]
    · obtain ⟨a, haD, rfl⟩ := mem_imGL.mp hx
      rw [pow_two, ← Subgroup.coe_mul, hsq a haD]
      rfl
  have hΛcard : Nat.card (autI hV₀ab A) ≤ Nat.card (imGL L D α') := by
    let αGL : ↥L →* Matrix.GeneralLinearGroup (Fin 3) F :=
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype.comp α'
    have h := card_map_mul_card_inf_ker αGL (D.subgroupOf L)
    have hD' : Nat.card (D.subgroupOf L) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
    have hle : αGL.ker ⊓ D.subgroupOf L ≤
        (L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)).subgroupOf L := by
      intro x hx
      have hx1 : α' x = 1 := Subtype.ext (by simpa [αGL] using (MonoidHom.mem_ker.mp hx.1))
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hker' x hx1⟩
    have hle' : Nat.card ↥(αGL.ker ⊓ D.subgroupOf L) ≤
        Nat.card ↥(L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) :=
      (Subgroup.card_le_of_le hle).trans
        (le_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv))
    have hκ : 0 < Nat.card ↥(L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) := Nat.card_pos
    have h' : Nat.card (imGL L D α') * Nat.card ↥(αGL.ker ⊓ D.subgroupOf L) = Nat.card D := by
      rw [← hD']
      exact h
    refine Nat.le_of_mul_le_mul_right ?_ hκ
    calc Nat.card (autI hV₀ab A) *
          Nat.card ↥(L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) = Nat.card D := hcardD.symm
      _ = Nat.card (imGL L D α') * Nat.card ↥(αGL.ker ⊓ D.subgroupOf L) := h'.symm
      _ ≤ Nat.card (imGL L D α') *
          Nat.card ↥(L ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) :=
        Nat.mul_le_mul_left _ hle'
  have hΛ1 : imGL L D α' ≠ ⊥ := by
    intro hbot
    have hDC : D ≤ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := by
      intro x hx
      have hxL : x ∈ L := hDL hx
      have h1 : α' ⟨x, hxL⟩ = 1 := by
        have hmem : ((α' ⟨x, hxL⟩ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
            Matrix.GeneralLinearGroup (Fin 3) F) ∈ imGL L D α' := mem_imGL.mpr ⟨⟨x, hxL⟩, hx, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext hmem
      exact hker' ⟨x, hxL⟩ h1
    have hbot' : autI hV₀ab A = ⊥ := by
      rw [← hautD]
      exact autI_eq_bot_of_le_centralizer hV₀ab hDC
    have hAC : A ≤ Subgroup.centralizer (V0_153 T Mc M E s : Set G) :=
      (autI_eq_bot_iff hV₀ab hAN).1 hbot'
    exact hAQ fun a ha => hCQ a (hAG ha) (hAC ha)
  have hlt := index_gt_of_case3 hm hV₀Q hV₀L hV₀ab hV₀64 hΛab hΛ1
  have hoff' : Nat.card (V0_153 T Mc M E s) ≤
      Nat.card (autI hV₀ab A) * Nat.card (fixV (autI hV₀ab A)) := hoff
  rw [hfixD] at hoff'
  have hmul := Nat.mul_le_mul_right
    (Nat.card ↥(V0_153 T Mc M E s ⊓ Subgroup.centralizer (D : Set G))) hΛcard
  omega

end Main

end S1567

end CFSG.Quasithin
