module

public import CFSG.Quasithin.Background.S1567V3
public import CFSG.Quasithin.EmptyFaithful.S146F3
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section CComp

theorem top_mem_cComp_top_of_simple {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : (⊤ : Subgroup Q) ∈ cComp (⊤ : Subgroup Q) := by
  have hnt : (⊤ : Subgroup Q) ≠ ⊥ := top_ne_bot
  have hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hmem : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
      apply hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
    · exact h
  refine ⟨hnt, hperf, ?_, ?_⟩
  · exact A3.subnormal_top_iff.mpr (Subgroup.IsSubnormal.top)
  · intro K hKlt hKne _ hKsub
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance (A3.subnormal_top_iff.mp hKsub) with h | h
    · exact hKne h
    · exact (ne_of_lt hKlt) h

end CComp

section ExistsL

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem exists_cComp_L (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2)))) :
    ∃ L : Subgroup G, L ∈ cComp (G0_153 T Mc M E s) ∧
      (L.subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))) = ⊤ := by
  set G0 := G0_153 T Mc M E s with hG0
  have hQD : pCoreOf 2 G0 ≤ G0 := pCoreOf_le 2 _
  have hNn : ((pCoreOf 2 G0).subgroupOf G0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 _)
  have : Group.IsNilpotent ↥(pCoreOf 2 G0) := (pCoreOf_isPGroup 2 G0).isNilpotent
  have hsol : Group.IsSolvable ↥(pCoreOf 2 G0) := inferInstance
  have hbij := cComp_quotient_bijOn_of_le hQD hNn hsol
  have h5 : CFSG.pPrimeCore 3 ↥G0 = (pCoreOf 2 G0).subgroupOf G0 := by
    rw [r68.pCore_eq]
    exact (Subgroup.comap_map_eq_self_of_injective G0.subtype_injective _).symm
  obtain ⟨e⟩ := hL3
  let e' : (↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq h5.symm).trans e
  have : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := S153E59.isSimpleGroup_statedSL_three_two
  have : IsSimpleGroup (↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0) := e'.isSimpleGroup
  have hcard : Nat.card (↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0) = 168 := by
    rw [Nat.card_congr e'.toEquiv]
    exact S153E59.card_statedSL_three_two
  have hnc : ∃ a b : ↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let : CommGroup (↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0) :=
      { (inferInstance : Group (↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0)) with mul_comm := hcon }
    have hp := IsSimpleGroup.prime_card (α := ↥G0 ⧸ (pCoreOf 2 G0).subgroupOf G0)
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  have htop := top_mem_cComp_top_of_simple hnc
  obtain ⟨L, hL, hLmap⟩ := hbij.surjOn htop
  exact ⟨L, hL, hLmap⟩

theorem G0_eq_L_mul_TE (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s) {L : Subgroup G}
    (hL : L ∈ cComp (G0_153 T Mc M E s))
    (hLmap : (L.subgroupOf (G0_153 T Mc M E s)).map
      (QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))) = ⊤) :
    ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G) := by
  have hLG : L ≤ G0_153 T Mc M E s := le_of_mem_cComp hL
  have hQT : pCoreOf 2 (G0_153 T Mc M E s) ≤ TE153 T E :=
    pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple
  have hTG : TE153 T E ≤ G0_153 T Mc M E s :=
    (le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left
  apply Set.Subset.antisymm
  · intro g hg
    have hmem : QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))
        (⟨g, hg⟩ : ↥(G0_153 T Mc M E s)) ∈
        (L.subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' ((pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s))) := by
      rw [hLmap]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.mp hmem
    have hq : l⁻¹ * (⟨g, hg⟩ : ↥(G0_153 T Mc M E s)) ∈
        (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s) :=
      QuotientGroup.eq.mp hlg
    rw [Subgroup.mem_subgroupOf] at hq hl
    refine ⟨(l : G), hl, (l : G)⁻¹ * g, hQT hq, ?_⟩
    simp
  · rintro _ ⟨l, hl, t', ht, rfl⟩
    exact (G0_153 T Mc M E s).mul_mem (hLG hl) (hTG ht)

end ExistsL

section Normal

variable {G : Type} [Group G] [Finite G]

theorem cComp_pCore_bijOn (X : Subgroup G) :
    Set.BijOn (fun L : Subgroup G =>
      (L.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)))
      (cComp X) (cComp (⊤ : Subgroup (↥X ⧸ (pCoreOf 2 X).subgroupOf X))) := by
  have hQD : pCoreOf 2 X ≤ X := pCoreOf_le 2 _
  have hNn : ((pCoreOf 2 X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 _)
  have : Group.IsNilpotent ↥(pCoreOf 2 X) := (pCoreOf_isPGroup 2 X).isNilpotent
  exact cComp_quotient_bijOn_of_le hQD hNn inferInstance

theorem normalizer_of_mem_cComp_of_map_eq_top {X L : Subgroup G} (hL : L ∈ cComp X)
    (hLmap : (L.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)) = ⊤) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hbij := cComp_pCore_bijOn X
  have hgn : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hg
  have hXmap : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgn
  have hL' : L.map (MulAut.conj g).toMonoidHom ∈ cComp X := by
    have := cComp_map_mulEquiv (MulAut.conj g) hL
    rwa [hXmap] at this
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hf : Subgroup.map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X))
      ((L.map (MulAut.conj g).toMonoidHom).subgroupOf X) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X) (⟨g, hg⟩⁻¹ * x * ⟨g, hg⟩ : ↥X) ∈
        (L.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)) := by
      rw [hLmap]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hmem
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hl ⊢
      refine ⟨(l : G), hl, ?_⟩
      simp
    · rw [map_mul, map_mul, map_inv]
      simp only [QuotientGroup.mk'_apply] at hlx ⊢
      rw [hlx, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
  have heq := hbij.injOn hL' hL (hf.trans hLmap.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end Normal

section O2L

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_inf_of_normal {X L : Subgroup G} (hLX : L ≤ X) (hN : X ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L = L ⊓ pCoreOf 2 X := by
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 L) ?_
    have hnorm : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
      intro g hg
      refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
      rw [CFSG.QuasithinUnique.C5.conjSubgroup_pCoreOf, conjSubgroup_eq_iff_mem_normalizer.mpr (hN hg)]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX) hnorm (pCoreOf_isPGroup 2 L)
  · have hnorm : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 X : Subgroup G) : Set G) := fun l hl =>
      mem_normalizer_inf67 (Subgroup.le_normalizer hl) (le_normalizer_pCoreOf 2 X (hLX hl))
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      ((pCoreOf_isPGroup 2 X).to_le inf_le_right)

omit [Finite G] in
theorem mem_pCoreOf_iff_mem_pCore67 {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem exists_modO2Surj {X L : Subgroup G} (hLX : L ≤ X) (hN : X ≤ Subgroup.normalizer (L : Set G))
    (e : (↥X ⧸ (pCoreOf 2 X).subgroupOf X) ≃* ↥(StatedSL 3 (ZMod 2)))
    (hLmap : (L.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)) = ⊤) :
    ∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  let α : ↥L →* ↥(StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)).comp (Subgroup.inclusion hLX))
  refine ⟨α, ?_, ?_⟩
  · intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    have hq : q ∈ (L.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)) := by
      rw [hLmap]
      exact Subgroup.mem_top q
    obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp hq
    refine ⟨⟨(l : G), hl⟩, ?_⟩
    simp only [α, MonoidHom.comp_apply]
    exact congrArg e hlq
  · ext l
    simp only [MonoidHom.mem_ker, α, MonoidHom.comp_apply]
    rw [map_eq_one_iff e.toMonoidHom e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, ← mem_pCoreOf_iff_mem_pCore67, pCoreOf_eq_inf_of_normal hLX hN]
    simp [Subgroup.mem_inf, l.2]

omit [Finite G] in
theorem isRankTwoLie2Derived_of_modO2 {L : Subgroup G} (α : ↥L →* ↥(StatedSL 3 (ZMod 2)))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hcomm : ∀ t, e1 z * t = t * e1 z := fun t => by
      obtain ⟨w, rfl⟩ := e1.surjective t
      rw [← map_mul, ← map_mul]
      exact congrArg e1 (Subgroup.mem_center_iff.mp hz w).symm
    have h1 : e1 z = 1 := S153E59.statedSL_center hcomm
    have h2 : z = 1 := e1.injective (h1.trans (map_one e1).symm)
    rw [h2]
    exact Subgroup.one_mem _
  let e2 : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine Or.inl ⟨1, isPSL_three_two_iff.mpr ⟨?_⟩⟩
  exact (e2.trans e1).trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm

end O2L

section Assemble

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem exists_quotEquiv_L32 (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2)))) :
    Nonempty ((↥(G0_153 T Mc M E s) ⧸ (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s)) ≃*
      ↥(StatedSL 3 (ZMod 2))) := by
  have h5 : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s) := by
    rw [r68.pCore_eq]
    exact (Subgroup.comap_map_eq_self_of_injective (G0_153 T Mc M E s).subtype_injective _).symm
  obtain ⟨e⟩ := hL3
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h5.symm).trans e⟩

theorem exists_L_isMSPair (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2)))) :
    ∃ L : Subgroup G, L ∈ cComp (G0_153 T Mc M E s) ∧
      G0_153 T Mc M E s ≤ Subgroup.normalizer (L : Set G) ∧
      ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G) ∧
      (∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) ∧
      IsMSPair (G0_153 T Mc M E s) (TE153 T E) := by
  obtain ⟨L, hL, hLmap⟩ := exists_cComp_L r68 hL3
  have hLG : L ≤ G0_153 T Mc M E s := le_of_mem_cComp hL
  have hN := normalizer_of_mem_cComp_of_map_eq_top hL hLmap
  have hprod := G0_eq_L_mul_TE k r67 gl r68 hL hLmap
  obtain ⟨e⟩ := exists_quotEquiv_L32 r68 hL3
  obtain ⟨α, hαs, hαk⟩ := exists_modO2Surj hLG hN e hLmap
  refine ⟨L, hL, hN, hprod, ⟨α, hαs, hαk⟩, ?_⟩
  exact isMSPair_G0_TE_of_exists_L h11 h113 k r67 gl r68
    ⟨L, hL, hprod, isRankTwoLie2Derived_of_modO2 α hαs hαk⟩

theorem oTwoUpper_G0_le_of_mul_TE (k : Ctx67 G T Mc M V₁ V₂ E t) {L : Subgroup G}
    (hN : G0_153 T Mc M E s ≤ Subgroup.normalizer (L : Set G))
    (hLG : L ≤ G0_153 T Mc M E s)
    (hprod : ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G)) :
    oTwoUpper (G0_153 T Mc M E s) ≤ L := by
  have hLn : (L.subgroupOf (G0_153 T Mc M E s)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr hN
  have hTp : IsPGroup 2 ↥(TE153 T E) := k.c.hyp.qtfe.sylow.1.to_le inf_le_left
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((L : Set G) * (TE153 T E : Set G)) := hprod ▸ hx
  obtain ⟨l, hl, t', ht', rfl⟩ := hx'
  obtain ⟨n, hn⟩ := hTp ⟨t', ht'⟩
  refine ⟨n, ?_⟩
  let π := QuotientGroup.mk' (L.subgroupOf (G0_153 T Mc M E s))
  have hTG : TE153 T E ≤ G0_153 T Mc M E s :=
    (le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left
  have hlG : l ∈ G0_153 T Mc M E s := hLG hl
  have htG : t' ∈ G0_153 T Mc M E s := hTG ht'
  have hlt : l * t' ∈ G0_153 T Mc M E s := (G0_153 T Mc M E s).mul_mem hlG htG
  have hπ : π (⟨l * t', hlt⟩ : ↥(G0_153 T Mc M E s)) = π ⟨t', htG⟩ := by
    have : (⟨l * t', hlt⟩ : ↥(G0_153 T Mc M E s)) = ⟨l, hlG⟩ * ⟨t', htG⟩ := rfl
    rw [this, map_mul]
    have hl1 : π ⟨l, hlG⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hl)
    rw [hl1, one_mul]
  have h1 : (⟨t', htG⟩ : ↥(G0_153 T Mc M E s)) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    exact Subtype.ext (by simpa using this)
  have hpow : π ((⟨l * t', hlt⟩ : ↥(G0_153 T Mc M E s)) ^ 2 ^ n) = 1 := by
    rw [map_pow, hπ, ← map_pow, h1, map_one]
  have hmem := (QuotientGroup.eq_one_iff _).mp hpow
  rw [Subgroup.mem_subgroupOf] at hmem
  exact hmem

end Assemble

end S1567

end CFSG.Quasithin
