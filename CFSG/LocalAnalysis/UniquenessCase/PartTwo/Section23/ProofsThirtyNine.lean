module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.Quasithin.Background.B4NaturalSLTwo
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.SylowQuotientSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem s23_39_exists_s (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∃ (hV : IsElemAbelian 2 c.V)
      (hnat : BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z))
      (s : MulAut (Vtil ⊥ c.V hV)) (z : Vtil ⊥ c.V hV) (l : G),
      s ∈ barSub ⊥ c.V hV c.L ∧ s ≠ 1 ∧ z ≠ 1 ∧ s z = z ∧
      l ∈ D.T ⊓ c.L ∧ ∀ hstab : l ∈ stabTil ⊥ c.V, s = actTil ⊥ c.V hV ⟨l, hstab⟩ := by
  classical
  obtain ⟨hV, -, hnat⟩ := h23 h1930 c
  have hsupN : c.L ⊔ D.T ≤ c.N := Ctx23L.sup_le_N D Ch c
  have hNnorm : Subgroup.normalizer (c.V : Set G) = c.N := c.normalizer_V_eq h4 h1930
  have hLnorm : c.L ≤ Subgroup.normalizer (c.V : Set G) := by
    rw [hNnorm]; exact le_sup_left.trans hsupN
  have hTnorm : D.T ≤ Subgroup.normalizer (c.V : Set G) := by
    rw [hNnorm]; exact le_sup_right.trans hsupN
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  have hstabL : c.L ≤ stabTil ⊥ c.V := le_stabTil hLnorm (by rw [hbotnorm]; exact le_top)
  have hstabT : D.T ≤ stabTil ⊥ c.V := le_stabTil hTnorm (by rw [hbotnorm]; exact le_top)
  let H : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
  have hnatH : BinaryNaturalSL H ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z) := hnat
  let actL : ↥c.L →* MulAut (Vtil ⊥ c.V hV) :=
    (actTil ⊥ c.V hV).comp (Subgroup.inclusion hstabL)
  let ψ : ↥c.L →* H := actL.codRestrict H fun l => by
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := c.L) l.2 (hstabL l.2)
  have hψsurj : Function.Surjective ψ := by
    intro h
    obtain ⟨g, hgL, hgact⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV c.L h.1).1 h.2
    refine ⟨⟨(g : G), hgL⟩, ?_⟩
    apply Subtype.ext
    have hval : actL ⟨(g : G), hgL⟩ = actTil ⊥ c.V hV g := by
      apply congrArg (actTil ⊥ c.V hV)
      exact Subtype.ext rfl
    exact hval.trans hgact
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T
      (Subgroup.normalizer (c.L : Set G)) :=
    D.sylowG.of_le c.hL.1.1 le_top
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ c.L) c.L :=
    hSylN.inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  let S : Sylow 2 H := Q.mapSurjective hψsurj
  have hEvenH : Even (Nat.card H) := by
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨eH⟩⟩ := BinaryNaturalSL.exists_equiv hnatH
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hEvenK : Even (Nat.card K) := by
      rw [hKcard]
      have hn : (CFSG.Open.pRank 2 D.Z) ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hKcard
        have hlt : 1 < Nat.card K := Finite.one_lt_card
        omega
      have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by omega
      rw [show 2 ^ (CFSG.Open.pRank 2 D.Z) =
          2 * 2 ^ (CFSG.Open.pRank 2 D.Z - 1) by
        rw [← pow_succ', Nat.sub_add_cancel hn1]]
      exact even_two_mul _
    have hEvenSL : Even (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      exact Even.mul_right hEvenK _
    rw [← Nat.card_congr eH.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact hEvenSL
  have hSne : (S : Subgroup H) ≠ ⊥ := S.ne_bot_of_dvd_card (even_iff_two_dvd.mp hEvenH)
  obtain ⟨s0, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  let sH : H := s0.1
  let s' : MulAut (Vtil ⊥ c.V hV) := sH.1
  have hsS : sH ∈ (S : Subgroup H) := s0.2
  have hsH : s' ∈ H := sH.2
  have hs1' : s' ≠ 1 := by
    intro h
    apply hs1
    apply Subtype.ext
    simpa [sH, s'] using h
  have hmemS : sH ∈ (S : Subgroup H) := hsS
  rw [show (S : Subgroup H) = (Q : Subgroup ↥c.L).map ψ by
    rw [show S = Q.mapSurjective hψsurj from rfl, Sylow.coe_mapSurjective]] at hmemS
  obtain ⟨q, hqQ, hqψ⟩ := Subgroup.mem_map.mp hmemS
  have hqT : (q : G) ∈ D.T := by
    have hqsub : (q : ↥c.L) ∈ (D.T ⊓ c.L).subgroupOf c.L := by
      rw [← hQ]; exact hqQ
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hqsub)).1
  have hqL : (q : G) ∈ c.L := q.2
  have hs_eq : s' = actTil ⊥ c.V hV ⟨(q : G), hstabL hqL⟩ := by
    rw [show s' = (ψ q : MulAut (Vtil ⊥ c.V hV)) from
      (congrArg Subtype.val hqψ).symm]
    rfl
  obtain ⟨zsub, hzsub1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  let z₀ : G := zsub.1
  have hz₀Z : z₀ ∈ D.Z := zsub.2
  have hz₀1 : z₀ ≠ 1 := fun h => hzsub1 (Subtype.ext h)
  have hz₀V : z₀ ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hz₀Z
  let z : Vtil ⊥ c.V hV := mkTil ⊥ c.V hV (IntMod.mk hV ⟨z₀, hz₀V⟩)
  have hz1 : z ≠ 1 := by
    intro hz
    apply hz₀1
    have hmem : z₀ * (1 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      refine (mkTil_eq_iff ⊥ c.V hV (IntMod.mk hV ⟨z₀, hz₀V⟩)
        (1 : IntMod c.V hV)).mp ?_
      simpa [z] using hz
    simpa using hmem
  have hsz : s' z = z := by
    rw [hs_eq]
    rw [show z = mkTil ⊥ c.V hV (IntMod.mk hV ⟨z₀, hz₀V⟩) from rfl]
    rw [actTil_mk]
    have hcomm : z₀ * (q : G) = (q : G) * z₀ :=
      Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D hqT) z₀ hz₀Z
    have hz₀C : (q : G) * z₀ * (q : G)⁻¹ = z₀ := by
      rw [← hcomm]
      group
    have hval : (actStab ⊥ c.V hV ⟨(q : G), hstabL hqL⟩ (IntMod.mk hV ⟨z₀, hz₀V⟩)).val = z₀ := by
      rw [actStab_apply_val]; exact hz₀C
    have hEq : actStab ⊥ c.V hV ⟨(q : G), hstabL hqL⟩ (IntMod.mk hV ⟨z₀, hz₀V⟩) =
        IntMod.mk hV ⟨z₀, hz₀V⟩ := IntMod.val_injective hval
    rw [hEq]
  refine ⟨hV, ?_, s', z, (q : G), hsH, hs1', hz1, hsz, ⟨hqT, hqL⟩, ?_⟩
  · simpa [H] using hnatH
  · intro hstab
    exact hs_eq.trans (by congr 1)


private theorem actTil_fixes_mkTil (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V}
    {l z : G} (hlT : l ∈ D.T) (hstab : l ∈ stabTil ⊥ c.V)
    (hzZ : z ∈ D.Z) :
    actTil ⊥ c.V hV ⟨l, hstab⟩
        (mkTil ⊥ c.V hV (IntMod.mk hV ⟨z, uc22p22v_le_conjClosure c.N D.Z hzZ⟩)) =
      mkTil ⊥ c.V hV (IntMod.mk hV ⟨z, uc22p22v_le_conjClosure c.N D.Z hzZ⟩) := by
  rw [actTil_mk]
  have hcomm : z * l = l * z :=
    Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D hlT) z hzZ
  have hval : (actStab ⊥ c.V hV ⟨l, hstab⟩
      (IntMod.mk hV ⟨z, uc22p22v_le_conjClosure c.N D.Z hzZ⟩)).val = z := by
    rw [actStab_apply_val]
    calc l * z * l⁻¹ = z * l * l⁻¹ := by rw [hcomm]
      _ = z := by group
  have hEq : actStab ⊥ c.V hV ⟨l, hstab⟩
      (IntMod.mk hV ⟨z, uc22p22v_le_conjClosure c.N D.Z hzZ⟩) =
      IntMod.mk hV ⟨z, uc22p22v_le_conjClosure c.N D.Z hzZ⟩ := IntMod.val_injective hval
  rw [hEq]

private theorem fixed_point_mem_image (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V}
    (hnat : BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z))
    {s : MulAut (Vtil ⊥ c.V hV)}
    (hsH : s ∈ barSub ⊥ c.V hV c.L) (hs1 : s ≠ 1)
    {z : Vtil ⊥ c.V hV} (hz1 : z ≠ 1) (hsz : s z = z)
    (hfixZ : ∀ w : D.Z,
      s (mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) =
        mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) :
    ∀ u : Vtil ⊥ c.V hV, s u = u →
      ∃ w : D.Z, u = mkTil ⊥ c.V hV
        (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩) := by
  classical
  let toTil : D.Z → Vtil ⊥ c.V hV := fun w =>
    mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)
  let g : D.Z → {u : Vtil ⊥ c.V hV // s u = u} := fun w => ⟨toTil w, hfixZ w⟩
  have hginj : Function.Injective g := by
    intro w1 w2 h
    apply Subtype.ext
    have hval : toTil w1 = toTil w2 := congrArg Subtype.val h
    have hmem : w1.1 * (w2.1)⁻¹ ∈ (⊥ : Subgroup G) := by
      refine (mkTil_eq_iff ⊥ c.V hV (IntMod.mk hV ⟨w1.1,
        uc22p22v_le_conjClosure c.N D.Z w1.2⟩) (IntMod.mk hV ⟨w2.1,
        uc22p22v_le_conjClosure c.N D.Z w2.2⟩)).mp ?_
      simpa [toTil] using hval
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hcardZ : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930)
  have hcardFix : Nat.card {u : Vtil ⊥ c.V hV // s u = u} = 2 ^ CFSG.Open.pRank 2 D.Z :=
    BinaryNaturalSL.card_fixed_eq hnat hsH hs1 hz1 hsz
  have hbij : Function.Bijective g :=
    (Nat.bijective_iff_injective_and_card g).2 ⟨hginj, by rw [hcardZ, hcardFix]⟩
  intro u hu
  obtain ⟨w, hw⟩ := hbij.2 ⟨u, hu⟩
  exact ⟨w, (congrArg Subtype.val hw).symm⟩


theorem commutator_mem_Z_of_mem_T (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {t v : G} (ht : t ∈ D.T) (hv : v ∈ c.V) :
    t * v * t⁻¹ * v⁻¹ ∈ D.Z := by
  classical
  obtain ⟨hV, hnat, s, z, l, hsH, hs1, hz1, hsz, ⟨hlT, hlL⟩, hs_eq_all⟩ :=
    s23_39_exists_s D Ch h4 h23 h1930 c
  have hsupN : c.L ⊔ D.T ≤ c.N := Ctx23L.sup_le_N D Ch c
  have hNnorm : Subgroup.normalizer (c.V : Set G) = c.N := c.normalizer_V_eq h4 h1930
  have hLnorm : c.L ≤ Subgroup.normalizer (c.V : Set G) := by
    rw [hNnorm]; exact le_sup_left.trans hsupN
  have hTnorm : D.T ≤ Subgroup.normalizer (c.V : Set G) := by
    rw [hNnorm]; exact le_sup_right.trans hsupN
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  have hstabL : c.L ≤ stabTil ⊥ c.V := le_stabTil hLnorm (by rw [hbotnorm]; exact le_top)
  have hstabT : D.T ≤ stabTil ⊥ c.V := le_stabTil hTnorm (by rw [hbotnorm]; exact le_top)
  have hs_eq : s = actTil ⊥ c.V hV ⟨l, hstabL hlL⟩ := hs_eq_all (hstabL hlL)
  have hfixZ : ∀ w : D.Z,
      s (mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) =
        mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩) := by
    intro w
    rw [hs_eq]
    exact actTil_fixes_mkTil D Ch h4 h1930 c hlT (hstabL hlL) w.2
  have hsurj : ∀ u : Vtil ⊥ c.V hV, s u = u →
      ∃ w : D.Z, u = mkTil ⊥ c.V hV
        (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩) :=
    fixed_point_mem_image D Ch h4 h23 h1930 c hnat hsH hs1 hz1 hsz hfixZ
  let f : MulAut (Vtil ⊥ c.V hV) := actTil ⊥ c.V hV ⟨t, hstabT ht⟩
  have htL : t * l * t⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp (c.hL.1.1 ht) l).1 hlL
  have hfsH : f * s * f⁻¹ ∈ barSub ⊥ c.V hV c.L := by
    rw [hs_eq]
    have hprod : f * actTil ⊥ c.V hV ⟨l, hstabL hlL⟩ * f⁻¹ =
        actTil ⊥ c.V hV ⟨t * l * t⁻¹, hstabL htL⟩ := by
      rw [show f = actTil ⊥ c.V hV ⟨t, hstabT ht⟩ from rfl]
      simp only [← map_mul, ← map_inv]
      congr 1
    rw [hprod]
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := c.L) htL (hstabL htL)
  have hfixf : ∀ u : Vtil ⊥ c.V hV, s u = u → f u = u := by
    intro u hu
    obtain ⟨w, rfl⟩ := hsurj u hu
    exact actTil_fixes_mkTil D Ch h4 h1930 c ht (hstabT ht) w.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp D.sylowG.isPGroup) ⟨t, ht⟩
  have hfpow : f ^ (2 ^ k) = 1 := by
    rw [show f = actTil ⊥ c.V hV ⟨t, hstabT ht⟩ from rfl]
    rw [← map_pow]
    have htpow : ((⟨t, hstabT ht⟩ : ↥(stabTil ⊥ c.V)) ^ (2 ^ k)) = 1 := by
      apply Subtype.ext
      show t ^ (2 ^ k) = 1
      have hord : orderOf t = 2 ^ k := (Subgroup.orderOf_mk t ht).symm.trans hk
      rw [← hord]
      exact pow_orderOf_eq_one t
    rw [htpow, map_one]
  have hA2 := BinaryNaturalSL.fixed_mul_inv hnat hsH hs1 hz1 hsz hfsH hfixf hfpow
  have hcommV : t * v * t⁻¹ * v⁻¹ ∈ c.V :=
    c.V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTnorm ht) v).1 hv) (c.V.inv_mem hv)
  let vT : Vtil ⊥ c.V hV := mkTil ⊥ c.V hV (IntMod.mk hV ⟨v, hv⟩)
  have hfvT : f vT * vT⁻¹ = mkTil ⊥ c.V hV
      (IntMod.mk hV ⟨t * v * t⁻¹ * v⁻¹, hcommV⟩) := by
    have h1 : f vT = mkTil ⊥ c.V hV
        (actStab ⊥ c.V hV ⟨t, hstabT ht⟩ (IntMod.mk hV ⟨v, hv⟩)) := by
      rw [show f = actTil ⊥ c.V hV ⟨t, hstabT ht⟩ from rfl, actTil_mk]
    rw [h1, ← map_inv, ← map_mul]
    apply congrArg (mkTil ⊥ c.V hV)
    apply IntMod.val_injective
    rw [IntMod.val_mul, actStab_apply_val, IntMod.val_inv]
    rfl
  have hfixed := hA2 vT
  rw [hfvT] at hfixed
  obtain ⟨w, hw⟩ := hsurj _ hfixed
  have hEqG : t * v * t⁻¹ * v⁻¹ = w.1 := by
    have hmem : (t * v * t⁻¹ * v⁻¹) * (w.1)⁻¹ ∈ (⊥ : Subgroup G) := by
      refine (mkTil_eq_iff ⊥ c.V hV (IntMod.mk hV ⟨t * v * t⁻¹ * v⁻¹, hcommV⟩)
        (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)).mp ?_
      simpa using hw
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  rw [hEqG]
  exact w.2


private theorem V_le_centralizerMod_Q (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.V ≤ centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← hUZ]
    exact (h4 h1930 c).2.2
  have hVleT : c.V ≤ D.T := c.V_le_T h4 h1930
  have hVleM : c.V ≤ D.M := hVleT.trans D.sylowM.le
  have hQT : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  intro v hv
  refine ⟨hVleM hv, hVleM.trans hZM hv, ?_⟩
  intro q hq
  have h := commutator_mem_Z_of_mem_T D Ch h4 h23 h1930 c (hQT hq) hv
  have e : (q * v * q⁻¹ * v⁻¹)⁻¹ = v * q * v⁻¹ * q⁻¹ := by group
  rw [← e]
  exact D.Z.inv_mem h

private theorem V_le_pCoreOf_M (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.V ≤ CFSG.Open.pCoreOf 2 D.M := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← hUZ]
    exact (h4 h1930 c).2.2
  have hZ2 : IsPGroup 2 D.Z := CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_Z h4 h1930)
  have hchar : CFSG.QuasithinUnique.CharTwo D.M := D.standing.charTwo D.M D.maxLocal.1
  let D' : Subgroup G := centralizerMod D.Z D.M Q ⊓ Subgroup.centralizer (D.Z : Set G)
  have hD'leM : D' ≤ D.M :=
    inf_le_left.trans (centralizerMod_le_left D.Z D.M Q)
  have hD'2 : IsPGroup 2 D' := by
    rintro ⟨d, hd⟩
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stability hZM hZ2 hchar
      hd.1.1 hd.2 hd.1.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hQnorm : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hD'norm : D.M ≤ Subgroup.normalizer (D' : Set G) := by
    refine le_normalizer_inf ?_ ?_
    · exact le_normalizer_centralizerMod hZM Subgroup.le_normalizer hQnorm
    · exact hZM.trans (normalizer_le_normalizer_centralizer D.Z)
  have hD'leQ : D' ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hD'leM hD'norm hD'2
  have hVleD' : c.V ≤ D' := by
    intro v hv
    refine ⟨V_le_centralizerMod_Q D Ch h4 h23 h1930 c hv, ?_⟩
    exact (c.V_le_T h4 h1930).trans (uc22main1_T_le_centralizer D) hv
  exact hVleD'.trans hD'leQ

theorem E_le_pCoreOf_M_of_s23_23 (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.E ≤ CFSG.Open.pCoreOf 2 D.M := by
  exact uc22p22v_conjClosure_le (N := D.M) (E := c.V) (F := CFSG.Open.pCoreOf 2 D.M)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    (V_le_pCoreOf_M D Ch h4 h23 h1930 c)

private theorem E_le_centralizerMod_Q (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.E ≤ centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← hUZ]
    exact (h4 h1930 c).2.2
  have hMnormC : D.M ≤ Subgroup.normalizer
      (centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M) : Set G) :=
    le_normalizer_centralizerMod hZM Subgroup.le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  exact uc22p22v_conjClosure_le (N := D.M) (E := c.V)
    (F := centralizerMod D.Z D.M (CFSG.Open.pCoreOf 2 D.M))
    hMnormC (V_le_centralizerMod_Q D Ch h4 h23 h1930 c)

theorem commutator_E_pCoreOf_le_Z (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z := by
  rw [Subgroup.commutator_le]
  intro e he q hq
  exact (mem_centralizerMod.mp (E_le_centralizerMod_Q D Ch h4 h23 h1930 c he)).2.2 q hq

private theorem centModE_le_normalizer (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    D.M ≤ Subgroup.normalizer (centModE D Ch c : Set G) := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← hUZ]
    exact (h4 h1930 c).2.2
  exact le_normalizer_centralizerMod hZM Subgroup.le_normalizer
    (uc22p22v_le_normalizer_conjClosure D.M c.V)


private theorem centModE_clause4 (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∀ Y : Subgroup G, Y ≤ D.M → (Y.subgroupOf D.M).Normal → centModE D Ch c ≤ Y →
      (∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ centModE D Ch c) → Y ≤ centModE D Ch c := by
  classical
  intro Y hYM hYnormal hCY hY2
  let C : Subgroup G := centModE D Ch c
  let S : Subgroup G := D.T ⊓ Y
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← hUZ]
    exact (h4 h1930 c).2.2
  have hCnormM : D.M ≤ Subgroup.normalizer (C : Set G) :=
    centModE_le_normalizer D Ch h4 h1930 c
  have hCnormY : (C.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).2 (hYM.trans hCnormM)
  letI : (C.subgroupOf Y).Normal := hCnormY
  have hMY : D.M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYnormal
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S Y :=
    D.sylowM.inf_of_le_normalizer hYM hMY
  have hquot : IsPGroup 2 (↥Y ⧸ C.subgroupOf Y) := by
    rw [IsPGroup.iff_orderOf]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Y) q
    obtain ⟨k, hk⟩ := hY2 y.1 y.2
    have hclasspow : (QuotientGroup.mk' (C.subgroupOf Y) y) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff (N := C.subgroupOf Y) _).2
      exact Subgroup.mem_subgroupOf.mpr hk
    have hdvd := orderOf_dvd_of_pow_eq_one hclasspow
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hYleCS : Y ≤ C ⊔ S :=
    CFSG.GroupTheory.le_sup_of_isPGroup_quotient_of_isSylowOf hCY hSyl hquot
  have hCSleCentV : C ⊔ S ≤ centralizerMod D.Z D.M c.V := by
    apply sup_le
    · exact centralizerMod_anti_right (V₁ := D.Z) (X := D.M) (U := c.V) (U' := c.E)
        (uc22p22v_le_conjClosure D.M c.V)
    · intro s hs
      have hsT : s ∈ D.T := (Subgroup.mem_inf.mp hs).1
      have hsY : s ∈ Y := (Subgroup.mem_inf.mp hs).2
      have hsM : s ∈ D.M := hYM hsY
      refine ⟨hsM, hZM hsM, ?_⟩
      intro v hv
      exact commutator_mem_Z_of_mem_T D Ch h4 h23 h1930 c hsT hv
  have hYleCentV : Y ≤ centralizerMod D.Z D.M c.V := hYleCS.trans hCSleCentV
  have hE_le_CmodY : c.E ≤ centralizerMod D.Z D.M Y := by
    refine uc22p22v_conjClosure_le (N := D.M) (E := c.V)
      (F := centralizerMod D.Z D.M Y) ?_ ?_
    · refine le_normalizer_centralizerMod hZM Subgroup.le_normalizer ?_
      exact hMY
    · intro v hv
      have hvM : v ∈ D.M := (c.V_le_T h4 h1930).trans D.sylowM.le hv
      refine ⟨hvM, hZM hvM, ?_⟩
      intro y hy
      have hyC : y ∈ centralizerMod D.Z D.M c.V := hYleCentV hy
      have h := (mem_centralizerMod.mp hyC).2.2 v hv
      have e : (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ := by group
      rw [← e]
      exact D.Z.inv_mem h
  intro y hy
  refine ⟨hYM hy, hZM (hYM hy), ?_⟩
  intro e he
  have heC : e ∈ centralizerMod D.Z D.M Y := hE_le_CmodY he
  have h := (mem_centralizerMod.mp heC).2.2 y hy
  have e : (e * y * e⁻¹ * y⁻¹)⁻¹ = y * e * y⁻¹ * e⁻¹ := by group
  rw [← e]
  exact D.Z.inv_mem h

private theorem stabTil_T_and_L (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.L ≤ stabTil ⊥ c.V ∧ D.T ≤ stabTil ⊥ c.V := by
  have hsupN : c.L ⊔ D.T ≤ c.N := Ctx23L.sup_le_N D Ch c
  have hNnorm : Subgroup.normalizer (c.V : Set G) = c.N := c.normalizer_V_eq h4 h1930
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  exact ⟨le_stabTil (by rw [hNnorm]; exact le_sup_left.trans hsupN)
      (by rw [hbotnorm]; exact le_top),
    le_stabTil (by rw [hNnorm]; exact le_sup_right.trans hsupN)
      (by rw [hbotnorm]; exact le_top)⟩

private theorem actTil_mul_inv_eq_mkTil (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} (g : stabTil ⊥ c.V) {v : G} (hv : v ∈ c.V)
    (hcomm : (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ c.V) :
    actTil ⊥ c.V hV g (mkTil ⊥ c.V hV (IntMod.mk hV ⟨v, hv⟩)) *
        (mkTil ⊥ c.V hV (IntMod.mk hV ⟨v, hv⟩))⁻¹ =
      mkTil ⊥ c.V hV (IntMod.mk hV ⟨(g : G) * v * (g : G)⁻¹ * v⁻¹, hcomm⟩) := by
  rw [actTil_mk, ← map_inv, ← map_mul]
  apply congrArg (mkTil ⊥ c.V hV)
  apply IntMod.val_injective
  rw [IntMod.val_mul, actStab_apply_val, IntMod.val_inv]
  rfl

private theorem ker_actTil_comp_inclusion (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {X : Subgroup G} (hX : X ≤ stabTil ⊥ c.V) :
    ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hX)).ker =
      (X ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf X := by
  ext t
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  change actTil ⊥ c.V hV ⟨(t : G), hX t.2⟩ = 1 ↔
    (t : G) ∈ X ∧ (t : G) ∈ Subgroup.centralizer (c.V : Set G)
  rw [actTil_eq_one_iff]
  constructor
  · intro h
    refine ⟨t.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : (t : G) * v * (t : G)⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp (h v hv)
    have h2 : (t : G) * v = v * (t : G) := by
      have h3 : ((t : G) * v) * (v * (t : G))⁻¹ = 1 := by
        rw [mul_inv_rev, ← h1]
        group
      exact mul_inv_eq_one.mp h3
    exact h2.symm
  · rintro ⟨-, hcent⟩ v hv
    rw [Subgroup.mem_bot]
    have hcomm : (t : G) * v = v * (t : G) :=
      (Subgroup.mem_centralizer_iff.mp hcent v hv).symm
    rw [hcomm]
    group

private theorem range_actTil_comp_inclusion (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {X : Subgroup G} (hX : X ≤ stabTil ⊥ c.V) :
    ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hX)).range = barSub ⊥ c.V hV X := by
  ext φ
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := X) x.2 (hX x.2)
  · intro hφ
    obtain ⟨g, hg, hgact⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV X φ).1 hφ
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    have h1 : actTil ⊥ c.V hV (Subgroup.inclusion hX ⟨(g : G), hg⟩) =
        actTil ⊥ c.V hV g := by
      apply congrArg (actTil ⊥ c.V hV)
      exact Subtype.ext rfl
    exact h1.trans hgact

private theorem relIndex_inf_centralizer_eq_card_barSub (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V} {X : Subgroup G}
    (hX : X ≤ stabTil ⊥ c.V) :
    (X ⊓ Subgroup.centralizer (c.V : Set G)).relIndex X =
      Nat.card (barSub ⊥ c.V hV X) := by
  rw [show (X ⊓ Subgroup.centralizer (c.V : Set G)).relIndex X =
      ((X ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf X).index from rfl,
    ← ker_actTil_comp_inclusion D Ch c hX, Subgroup.index_ker,
    range_actTil_comp_inclusion D Ch c hX]

private theorem barSub_T_le_barSub_L_of_data (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V}
    (hnat : BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z))
    {s : MulAut (Vtil ⊥ c.V hV)} {z : Vtil ⊥ c.V hV} {l : G}
    (hsH : s ∈ barSub ⊥ c.V hV c.L) (hs1 : s ≠ 1) (hz1 : z ≠ 1) (hsz : s z = z)
    (hlT : l ∈ D.T) (hlL : l ∈ c.L)
    (hs_eq : ∀ hstab : l ∈ stabTil ⊥ c.V, s = actTil ⊥ c.V hV ⟨l, hstab⟩)
    (hfixZ : ∀ w : D.Z,
      s (mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) =
        mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩))
    (hsurj : ∀ u : Vtil ⊥ c.V hV, s u = u →
      ∃ w : D.Z, u = mkTil ⊥ c.V hV
        (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) :
    barSub ⊥ c.V hV D.T ≤ barSub ⊥ c.V hV c.L := by
  classical
  obtain ⟨hstabL, -⟩ := stabTil_T_and_L D Ch h4 h1930 c
  intro φ hφ
  obtain ⟨g, hgT, rfl⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV D.T φ).1 hφ
  let f : MulAut (Vtil ⊥ c.V hV) := actTil ⊥ c.V hV g
  have hnorm : ∀ h ∈ barSub ⊥ c.V hV c.L, f * h * f⁻¹ ∈ barSub ⊥ c.V hV c.L := by
    intro h hh
    obtain ⟨g', hg'L, rfl⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV c.L h).1 hh
    have htL' : (g : G) * (g' : G) * (g : G)⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (c.hL.1.1 hgT) (g' : G)).1 hg'L
    have hprod : f * actTil ⊥ c.V hV g' * f⁻¹ =
        actTil ⊥ c.V hV ⟨(g : G) * (g' : G) * (g : G)⁻¹, hstabL htL'⟩ := by
      rw [show f = actTil ⊥ c.V hV g from rfl]
      simp only [← map_mul, ← map_inv]
      congr 1
    rw [hprod]
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := c.L) htL' (hstabL htL')
  have hfix : ∀ u : Vtil ⊥ c.V hV, s u = u → f u = u := by
    intro u hu
    obtain ⟨w, rfl⟩ := hsurj u hu
    exact actTil_fixes_mkTil D Ch h4 h1930 c hgT g.2 w.2
  have hmod : ∀ u : Vtil ⊥ c.V hV, s (f u * u⁻¹) = f u * u⁻¹ := by
    intro u
    obtain ⟨x, rfl⟩ := mkTil_surjective (V₀ := ⊥) (V := c.V) hV u
    have hgV : (g : G) ∈ Subgroup.normalizer (c.V : Set G) :=
      stabTil_le_normalizer ⊥ c.V g.2
    have hcommV : (g : G) * x.val * (g : G)⁻¹ * x.val⁻¹ ∈ c.V :=
      c.V.mul_mem ((Subgroup.mem_normalizer_iff.mp hgV x.val).1 x.val_mem)
        (c.V.inv_mem x.val_mem)
    have hzZ : (g : G) * x.val * (g : G)⁻¹ * x.val⁻¹ ∈ D.Z :=
      commutator_mem_Z_of_mem_T D Ch h4 h23 h1930 c hgT x.val_mem
    have hfix' : s (mkTil ⊥ c.V hV
        (IntMod.mk hV ⟨(g : G) * x.val * (g : G)⁻¹ * x.val⁻¹, hcommV⟩)) =
        mkTil ⊥ c.V hV
          (IntMod.mk hV ⟨(g : G) * x.val * (g : G)⁻¹ * x.val⁻¹, hcommV⟩) := by
      have h := hfixZ ⟨(g : G) * x.val * (g : G)⁻¹ * x.val⁻¹, hzZ⟩
      rwa [show IntMod.mk hV ⟨(g : G) * x.val * (g : G)⁻¹ * x.val⁻¹, hcommV⟩ =
          IntMod.mk hV ⟨(g : G) * x.val * (g : G)⁻¹ * x.val⁻¹,
            uc22p22v_le_conjClosure c.N D.Z hzZ⟩ from Subtype.ext rfl] at h
    change s (actTil ⊥ c.V hV g
        (mkTil ⊥ c.V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) *
      (mkTil ⊥ c.V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩))⁻¹) =
      actTil ⊥ c.V hV g
        (mkTil ⊥ c.V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) *
      (mkTil ⊥ c.V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩))⁻¹
    rw [actTil_mul_inv_eq_mkTil D Ch c g x.val_mem hcommV]
    exact hfix'
  exact BinaryNaturalSL.mem_of_normalizes hnat hsH hs1 hz1 hsz hnorm hfix hmod

private theorem exists_sylow_barSub_T_inf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} :
    ∃ S : Sylow 2 (barSub ⊥ c.V hV c.L),
      (S : Subgroup (barSub ⊥ c.V hV c.L)).map (barSub ⊥ c.V hV c.L).subtype =
        barSub ⊥ c.V hV (D.T ⊓ c.L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hstabL, -⟩ := stabTil_T_and_L D Ch h4 h1930 c
  let H : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
  let actL : ↥c.L →* MulAut (Vtil ⊥ c.V hV) :=
    (actTil ⊥ c.V hV).comp (Subgroup.inclusion hstabL)
  let ψ : ↥c.L →* H := actL.codRestrict H fun l => by
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := c.L) l.2 (hstabL l.2)
  have hψsurj : Function.Surjective ψ := by
    intro h
    obtain ⟨g, hgL, hgact⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV c.L h.1).1 h.2
    refine ⟨⟨(g : G), hgL⟩, ?_⟩
    apply Subtype.ext
    have hval : actL ⟨(g : G), hgL⟩ = actTil ⊥ c.V hV g := by
      apply congrArg (actTil ⊥ c.V hV)
      exact Subtype.ext rfl
    exact hval.trans hgact
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ c.L) c.L :=
    (D.sylowG.of_le c.hL.1.1 le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  let S : Sylow 2 H := Q.mapSurjective hψsurj
  have hcomp : H.subtype.comp ψ = actL := by
    ext l
    rfl
  have hSmap : (S : Subgroup H).map H.subtype = barSub ⊥ c.V hV (D.T ⊓ c.L) := by
    rw [Sylow.coe_mapSurjective hψsurj Q, hQ, Subgroup.map_map, hcomp]
    ext φ
    rw [Subgroup.mem_map, mem_barSub]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨(q : G), hstabL q.2⟩, Subgroup.mem_subgroupOf.mp hq, ?_⟩
      apply congrArg (actTil ⊥ c.V hV)
      exact Subtype.ext rfl
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨(g : G), (Subgroup.mem_inf.mp hg).2⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hg
      · apply congrArg (actTil ⊥ c.V hV)
        exact Subtype.ext rfl
  exact ⟨S, hSmap⟩

private theorem barSub_T_eq_barSub_T_inf_L_of_le (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V}
    (hle : barSub ⊥ c.V hV D.T ≤ barSub ⊥ c.V hV c.L) :
    barSub ⊥ c.V hV D.T = barSub ⊥ c.V hV (D.T ⊓ c.L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSmap⟩ := exists_sylow_barSub_T_inf_L D Ch h4 h1930 c (hV := hV)
  have hSylBar : CFSG.ABGLocalTools.IsSylowOf 2
      (barSub ⊥ c.V hV (D.T ⊓ c.L)) (barSub ⊥ c.V hV c.L) := ⟨S, hSmap⟩
  have hle' : barSub ⊥ c.V hV (D.T ⊓ c.L) ≤ barSub ⊥ c.V hV D.T :=
    barSub_mono (V₀ := ⊥) (V := c.V) hV inf_le_left
  have hQ2 : IsPGroup 2 (barSub ⊥ c.V hV D.T) := by
    change IsPGroup 2 ((D.T.subgroupOf (stabTil ⊥ c.V)).map (actTil ⊥ c.V hV))
    exact (IsPGroup.comap_subtype (K := stabTil ⊥ c.V) D.sylowG.isPGroup).map
      (actTil ⊥ c.V hV)
  exact CFSG.ABGLocalTools.IsSylowOf.eq_of_le hSylBar hle' hle hQ2

private theorem card_barSub_T_inf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V}
    (hnat : BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z)) :
    Nat.card (barSub ⊥ c.V hV (D.T ⊓ c.L)) = 2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSmap⟩ := exists_sylow_barSub_T_inf_L D Ch h4 h1930 c (hV := hV)
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eH⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hcardH : Nat.card (barSub ⊥ c.V hV c.L) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr eH.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKne : Nat.card K ≠ 0 := hKpos.ne'
  have hKgt : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by
    by_contra h
    have h0 : CFSG.Open.pRank 2 D.Z = 0 := by omega
    rw [h0, pow_zero] at hKcard
    omega
  have hEven : 2 ∣ Nat.card K := by
    rw [hKcard]
    exact dvd_pow_self 2 (by omega)
  have hOdd : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by
    obtain ⟨m, hm⟩ := hEven
    have hmpos : 0 < m := by
      have hpos : 0 < 2 * m := by rw [← hm]; exact hKpos
      omega
    have hm2 : 0 < m ^ 2 := pow_pos hmpos 2
    have hrew : Nat.card K ^ 2 - 1 = 2 * (2 * m ^ 2 - 1) + 1 := by
      rw [hm]
      rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]
      omega
    rw [hrew]
    exact Nat.not_two_dvd_bit1 _
  have hOddne : Nat.card K ^ 2 - 1 ≠ 0 := by
    intro h0
    exact hOdd (by rw [h0]; exact dvd_zero 2)
  have hfacK : Nat.factorization (Nat.card K) 2 = CFSG.Open.pRank 2 D.Z := by
    rw [hKcard, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hfacOdd : Nat.factorization (Nat.card K ^ 2 - 1) 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hOdd
  have hfac : Nat.factorization (Nat.card (barSub ⊥ c.V hV c.L)) 2 =
      CFSG.Open.pRank 2 D.Z := by
    rw [hcardH, Nat.factorization_mul hKne hOddne, Finsupp.add_apply, hfacK, hfacOdd,
      add_zero]
  have hcardS : Nat.card S = 2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [Sylow.card_eq_multiplicity S, hfac]
  calc Nat.card (barSub ⊥ c.V hV (D.T ⊓ c.L))
      = Nat.card (S : Subgroup (barSub ⊥ c.V hV c.L)) := by
        rw [← hSmap, Subgroup.card_subtype]
    _ = Nat.card S := rfl
    _ = 2 ^ CFSG.Open.pRank 2 D.Z := hcardS

private theorem s23_39_B_data (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∃ hV : IsElemAbelian 2 c.V,
      BinaryNaturalSL (barSub ⊥ c.V hV c.L) ⊤ ⊥ 2 (CFSG.Open.pRank 2 D.Z) ∧
      barSub ⊥ c.V hV D.T = barSub ⊥ c.V hV (D.T ⊓ c.L) ∧
      Nat.card (barSub ⊥ c.V hV (D.T ⊓ c.L)) = 2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  obtain ⟨hV, hnat, s, z, l, hsH, hs1, hz1, hsz, ⟨hlT, hlL⟩, hs_eq_all⟩ :=
    s23_39_exists_s D Ch h4 h23 h1930 c
  obtain ⟨hstabL, -⟩ := stabTil_T_and_L D Ch h4 h1930 c
  have hs_eq : s = actTil ⊥ c.V hV ⟨l, hstabL hlL⟩ := hs_eq_all (hstabL hlL)
  have hfixZ : ∀ w : D.Z,
      s (mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩)) =
        mkTil ⊥ c.V hV (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩) := by
    intro w
    rw [hs_eq]
    exact actTil_fixes_mkTil D Ch h4 h1930 c hlT (hstabL hlL) w.2
  have hsurj : ∀ u : Vtil ⊥ c.V hV, s u = u →
      ∃ w : D.Z, u = mkTil ⊥ c.V hV
        (IntMod.mk hV ⟨w.1, uc22p22v_le_conjClosure c.N D.Z w.2⟩) :=
    fixed_point_mem_image D Ch h4 h23 h1930 c hnat hsH hs1 hz1 hsz hfixZ
  have hle : barSub ⊥ c.V hV D.T ≤ barSub ⊥ c.V hV c.L :=
    barSub_T_le_barSub_L_of_data D Ch h4 h23 h1930 c hnat hsH hs1 hz1 hsz hlT hlL
      hs_eq_all hfixZ hsurj
  exact ⟨hV, hnat, barSub_T_eq_barSub_T_inf_L_of_le D Ch h4 h1930 c hle,
    card_barSub_T_inf_L D Ch h4 h1930 c hnat⟩

theorem exists_mem_T_inf_L_mul_inv_mem_centralizer (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {t : G} (ht : t ∈ D.T) :
    ∃ l ∈ D.T ⊓ c.L, t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G) := by
  classical
  obtain ⟨hV, -, hEq, -⟩ := s23_39_B_data D Ch h4 h23 h1930 c
  obtain ⟨-, hstabT⟩ := stabTil_T_and_L D Ch h4 h1930 c
  have hmem : actTil ⊥ c.V hV ⟨t, hstabT ht⟩ ∈ barSub ⊥ c.V hV (D.T ⊓ c.L) := by
    rw [← hEq]
    exact actTil_mem_barSub (V₀ := ⊥) (V := c.V) hV (X := D.T) ht (hstabT ht)
  obtain ⟨g, hg, hgact⟩ := (mem_barSub (V₀ := ⊥) (V := c.V) hV (D.T ⊓ c.L)
    (actTil ⊥ c.V hV ⟨t, hstabT ht⟩)).1 hmem
  have hlT : (g : G) ∈ D.T := (Subgroup.mem_inf.mp hg).1
  have hlL : (g : G) ∈ c.L := (Subgroup.mem_inf.mp hg).2
  have hgl : actTil ⊥ c.V hV ⟨(g : G), hstabT hlT⟩ =
      actTil ⊥ c.V hV ⟨t, hstabT ht⟩ := by
    rw [← hgact]
  have hcomm : actTil ⊥ c.V hV
      ⟨t * (g : G)⁻¹, hstabT (D.T.mul_mem ht (D.T.inv_mem hlT))⟩ = 1 := by
    have hsub : (⟨t * (g : G)⁻¹, hstabT (D.T.mul_mem ht (D.T.inv_mem hlT))⟩ :
        stabTil ⊥ c.V) = ⟨t, hstabT ht⟩ * ⟨(g : G), hstabT hlT⟩⁻¹ := by
      exact Subtype.ext rfl
    rw [hsub, map_mul, map_inv, hgl]
    group
  refine ⟨(g : G), ⟨hlT, hlL⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : ((t * (g : G)⁻¹) * v * (t * (g : G)⁻¹)⁻¹ * v⁻¹) = 1 :=
    Subgroup.mem_bot.mp ((actTil_eq_one_iff ⊥ c.V hV
      ⟨t * (g : G)⁻¹, hstabT (D.T.mul_mem ht (D.T.inv_mem hlT))⟩).1 hcomm v hv)
  have h2 : (t * (g : G)⁻¹) * v = v * (t * (g : G)⁻¹) := by
    have h3 : ((t * (g : G)⁻¹) * v) * (v * (t * (g : G)⁻¹))⁻¹ = 1 := by
      rw [mul_inv_rev, ← h1]
      group
    exact mul_inv_eq_one.mp h3
  exact h2.symm

theorem relIndex_centralizer_V_eq (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    (D.T ⊓ Subgroup.centralizer (c.V : Set G)).relIndex D.T =
      2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  obtain ⟨hV, -, hEq, hcard⟩ := s23_39_B_data D Ch h4 h23 h1930 c
  obtain ⟨-, hstabT⟩ := stabTil_T_and_L D Ch h4 h1930 c
  rw [relIndex_inf_centralizer_eq_card_barSub D Ch c (hV := hV) hstabT, hEq, hcard]

theorem relIndex_centralizer_V_in_T_inf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ((D.T ⊓ c.L) ⊓ Subgroup.centralizer (c.V : Set G)).relIndex (D.T ⊓ c.L) =
      2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  obtain ⟨hV, -, -, hcard⟩ := s23_39_B_data D Ch h4 h23 h1930 c
  obtain ⟨hstabL, hstabT⟩ := stabTil_T_and_L D Ch h4 h1930 c
  have hX : D.T ⊓ c.L ≤ stabTil ⊥ c.V := inf_le_left.trans hstabT
  rw [relIndex_inf_centralizer_eq_card_barSub D Ch c (hV := hV) hX, hcard]

theorem binaryNaturalSL_barSub_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    BinaryNaturalSL (barSub ⊥ c.V (c.isElemAbelian_V h4 h1930) c.L) ⊤ ⊥ 2
      (CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨_, hnat, -⟩ := s23_39_B_data D Ch h4 h23 h1930 c
  exact hnat

end Ctx23L


@[expose] def S23_39Ab (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, IsMulCommutative c.E

theorem s23_39_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (hab : S23_39Ab D Ch) : S23_39 D Ch := by
  intro h1930 c
  exact ⟨hab h1930 c,
    Ctx23L.E_le_pCoreOf_M_of_s23_23 D Ch h4 h23 h1930 c,
    Ctx23L.commutator_E_pCoreOf_le_Z D Ch h4 h23 h1930 c,
    Ctx23L.centModE_clause4 D Ch h4 h23 h1930 c⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
