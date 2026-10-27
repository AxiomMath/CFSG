module

public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
public import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

namespace Rem187QProof

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_centralizer {H : Subgroup G} {c : G} (hcH : c ∈ H)
    (hcL : ∀ l ∈ inSubgroup perfectResidual H,
      c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) :
    QuotientGroup.mk' (CFSG.pCore 2 H) ⟨c, hcH⟩ ∈ Subgroup.centralizer
      (((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) : Subgroup _) : Set _) := by
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxL : (x : G) ∈ inSubgroup perfectResidual H := ⟨x, hx, rfl⟩
  have h2 : c * (x : G) * c⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 H :=
    pCoreOf_perfectResidual_le H (hcL _ hxL)
  have h3 : (⟨c, hcH⟩ * x * ⟨c, hcH⟩⁻¹ * x⁻¹ : H) ∈ CFSG.pCore 2 H :=
    (mem_pCore_iff_mem_pCoreOf _).mpr (by simpa using h2)
  have h4 : π (⟨c, hcH⟩ * x * ⟨c, hcH⟩⁻¹ * x⁻¹) = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  simp only [map_mul, map_inv] at h4
  calc π x * π ⟨c, hcH⟩
      = (π ⟨c, hcH⟩ * π x * (π ⟨c, hcH⟩)⁻¹ * (π x)⁻¹)⁻¹ * (π ⟨c, hcH⟩ * π x) := by group
    _ = π ⟨c, hcH⟩ * π x := by rw [h4, inv_one, one_mul]

theorem exists_mem_scriptH_le_centralizer {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) {s : G} (hsH : s ∈ H) (hsS : s ∈ CFSG.Open.pCoreOf 2 (H ⊓ M))
    (hsA : s ∈ Subgroup.centralizer (A : Set G))
    (hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H)) {c : G} (hcA : c ∈ A)
    (hcL : ∀ l ∈ inSubgroup perfectResidual H,
      c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) :
    ∃ Hc ∈ scriptH A M, Hc ≤ Subgroup.centralizer ({c} : Set G) ∧
      inSubgroup perfectResidual Hc =
        inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAM := sec18Std_le h
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb := (perfectResidual H).map π with hLbdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hcH : c ∈ H := hAH hcA
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hsC : s ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsA c hcA).symm
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H := pCoreOf_perfectResidual_le H
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  obtain ⟨eL⟩ := Claim184LcProof.quotient_mulEquiv_map hLH hLO
  set Lc := inSubgroup perfectResidual (H ⊓ C) with hLcdef
  have hLcHC : Lc ≤ H ⊓ C := Subgroup.map_subtype_le _
  have hLcH : Lc ≤ H := hLcHC.trans inf_le_left
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hLcN : H ⊓ C ≤ Subgroup.normalizer (Lc : Set G) :=
    le_normalizer_inSubgroup_perfectResidual _
  have hLcimg : (Lc.subgroupOf H).map π = Lb :=
    Claim184LcProof.map_perfectResidual_inf_centralizer hcH hc3 (mk_mem_centralizer hcH hcL)
  have hLcO : CFSG.Open.pCoreOf 2 Lc ≤ CFSG.Open.pCoreOf 2 H :=
    Claim184LcProof.pCoreOf_le_of_map_eq hLcH hLcimg
  obtain ⟨eLc⟩ := Claim184LcProof.quotient_mulEquiv_map hLcH hLcO
  have hLc_q : CFSG.IsQuasisimple (Lc ⧸ CFSG.pCore 2 Lc) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (eL.trans ((MulEquiv.subgroupCongr (hLimg.trans hLcimg.symm)).trans eLc.symm))
      (isQuasisimple_of_mem_oTwoComponentsIn hH₀.2.1)
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ C with hTdef
  have hTHM : T ≤ H ⊓ M := inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTC : T ≤ C := inf_le_right
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hsT : s ∈ T := ⟨hsS, hsC⟩
  have hNT : ∀ x, x ∈ H → x ∈ M → x ∈ C → x ∈ Subgroup.normalizer (T : Set G) :=
    fun x hxH hxM hxC => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hxH, hxM⟩,
        Subgroup.le_normalizer hxC⟩
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha => hNT a (hAH ha) (hAM ha) (hAC ha)
  have hALc : A ≤ Subgroup.normalizer (Lc : Set G) := fun a ha => hLcN ⟨hAH ha, hAC ha⟩
  have hTLc : T ≤ Subgroup.normalizer (Lc : Set G) := fun t ht => hLcN ⟨hTH ht, hTC ht⟩
  set Y := Lc ⊔ A ⊔ T with hYdef
  have hYHC : Y ≤ H ⊓ C :=
    sup_le (sup_le hLcHC (le_inf hAH hAC)) (le_inf hTH hTC)
  have hYC : Y ≤ C := hYHC.trans inf_le_right
  have hYT : Y ⊓ M ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    hNT x (hYHC hx.1).1 hx.2 (hYHC hx.1).2
  have hYLc : Y ≤ Subgroup.normalizer (Lc : Set G) := hYHC.trans hLcN
  have hTO : ¬ T ≤ CFSG.Open.pCoreOf 2 Y := fun hle =>
    Claim184LcProof.not_mem_pCoreOf_of_inducesOuterTheta hsH (le_sup_left.trans le_sup_left)
      hYLc hLcimg hLcO hout (hle hsT)
  obtain ⟨hY, hYres⟩ :=
    Claim184LcProof.sup_mem_scriptH_of_le h hH hLcH hTH hLcp hLc_q hT2 hTM hALc hTLc hAT hYT hTO
  exact ⟨Y, hY, hYC, hYres⟩

theorem mem_of_mk_mem {H : Subgroup G} {c : G} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    (hcL : ∀ l ∈ inSubgroup perfectResidual H,
      c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H))
    {a : G} (haH : a ∈ H) (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha3 : a ^ 3 = 1)
    (hmem : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨a, haH⟩ ∈
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H))) :
    a ∈ inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Lc := inSubgroup perfectResidual (H ⊓ C) with hLcdef
  have hLcHC : Lc ≤ H ⊓ C := Subgroup.map_subtype_le _
  have hLcN : H ⊓ C ≤ Subgroup.normalizer (Lc : Set G) :=
    le_normalizer_inSubgroup_perfectResidual _
  have hLcimg := Claim184LcProof.map_perfectResidual_inf_centralizer hcH hc3
    (mk_mem_centralizer hcH hcL)
  rw [← hLcimg] at hmem
  obtain ⟨l, hl, hla⟩ := hmem
  have hlLc : (l : G) ∈ Lc := Subgroup.mem_subgroupOf.mp hl
  have hr : (l : G)⁻¹ * a ∈ CFSG.Open.pCoreOf 2 H := by
    have h1 : π (l⁻¹ * ⟨a, haH⟩) = 1 := by rw [map_mul, map_inv, hla, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    simpa using h1
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hr⟩
  have hn' : ((l : G)⁻¹ * a) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine Item183NMProof.mem_of_mul_mem_of_pow hLcHC hLcN ⟨haH, haC⟩ ha3 (Lc.inv_mem hlLc)
    (n := n) ?_
  have e : a * (l : G)⁻¹ = (l : G) * ((l : G)⁻¹ * a) * (l : G)⁻¹ := by group
  rw [e, conj_pow, hn', mul_one, mul_inv_cancel]

theorem card_inf_ge_and_not_mem {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M)
    (eL : inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      projSL 3 (GaloisField 2 2))
    {s : G} (hsH : s ∈ H) (hsS : s ∈ CFSG.Open.pCoreOf 2 (H ⊓ M))
    {X : Subgroup (H ⧸ CFSG.pCore 2 H)} [hXn : X.Normal] (hX : Sec4.IsZ3L34OrHeisSL34 X)
    (hXt : X ⊔ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hsH⟩ : H)) = ⊤)
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hcL : ∀ l ∈ inSubgroup perfectResidual H,
      c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) :
    9 ≤ Nat.card (A ⊓ inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) :
      Subgroup G) ∧ c ∉ inSubgroup perfectResidual H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  set Lb : Subgroup (H ⧸ Q) := (perfectResidual H).map π with hLb
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hcH : c ∈ H := hAH hcA
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQ, mem_pCore_iff_mem_pCoreOf]
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ X) := by
    have h1 := ht2.map (QuotientGroup.mk' X)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' X) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self X), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ X) := by
    have := hq2.isNilpotent
    infer_instance
  have hLbeq : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆ → Lb = ⁅X, X⁆ := fun hp => by
    rw [hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
    exact perfectResidual_eq_commutator hqs hp
  have hLO : CFSG.Open.pCoreOf 2 L ≤ R := pCoreOf_perfectResidual_le H
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  obtain ⟨eL'⟩ := Claim184LcProof.quotient_mulEquiv_map hLH hLO
  have hLbcard : Nat.card Lb = 20160 := by
    rw [← hLimg, ← Nat.card_congr eL'.toEquiv, Nat.card_congr eL.toEquiv,
      KFacts.L34.card_projSL]
  have hAX : ∀ a (ha : a ∈ H), a ∈ A → π ⟨a, ha⟩ ∈ X := by
    intro a ha haA
    refine mem_of_isPGroup_quotient hq2 (k := 1) ?_
    rw [pow_one, ← map_pow]
    have : (⟨a, ha⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 a haA)
    rw [this, map_one]
  rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
  swap
  ·
    exfalso
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
    have hXX : ⁅X, X⁆ = V.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, hcomm]
    have hVp : Group.IsPerfect V := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVmp : ⁅V.map X.subtype, V.map X.subtype⁆ = V.map X.subtype := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
        Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLbV : Lb = V.map X.subtype := by
      rw [hLbeq (by rw [hXX, hVmp]), hXX]
    have hVcard : Nat.card (V.map X.subtype) = 60480 := by
      rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_congr eV.toEquiv,
        KFacts.KS14.card_SL_three_four]
    rw [← hLbV, hLbcard] at hVcard
    norm_num at hVcard
  obtain ⟨e⟩ := he
  have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
  set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
  have hcomm := KFacts.KS18.commutator_eq_range e'
  have hrp : ⁅(KFacts.KS18.inrY e').range, (KFacts.KS18.inrY e').range⁆ =
      (KFacts.KS18.inrY e').range := by
    have := KFacts.KS18.isPerfect_projectiveSL (GaloisField 2 2)
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hLbr : Lb = (KFacts.KS18.inrY e').range := by
    rw [hLbeq (by rw [hcomm, hrp]), hcomm]
  have hXcard : Nat.card X = 3 * Nat.card Lb := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_prod, hLbr,
      ← Nat.card_congr (MonoidHom.ofInjective (KFacts.KS18.inrY_injective e')).toEquiv]
    simp
  set f : A.subgroupOf H →* H ⧸ Q := π.comp (A.subgroupOf H).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
    have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
    have : ((a : H) : G) ∈ A ⊓ R := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
  set Ab := f.range with hAb
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, ← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAbX : Ab ≤ X := by
    rintro _ ⟨a, rfl⟩
    exact hAX _ (a : H).2 (Subgroup.mem_subgroupOf.mp a.2)
  have hD : 9 ≤ Nat.card (Ab ⊓ Lb : Subgroup (H ⧸ Q)) := by
    have hLbn : Lb.Normal := by
      have hc := CFSG.perfect_residual_characterization (G := H)
      have : (perfectResidual H).Characteristic := hc.2.1
      exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective Q)
    have h1 := Sec6.card_sup_mul_card_inf (X := Ab) (N := Lb)
      (fun x _ => (Subgroup.normalizer_eq_top_iff.mpr hLbn).symm ▸ Subgroup.mem_top x)
    have hLbX : Lb ≤ X := by rw [hLbr]; exact KFacts.KS18.range_inrY_le e'
    have h2 : Nat.card (Ab ⊔ Lb : Subgroup (H ⧸ Q)) ≤ Nat.card X :=
      Subgroup.card_le_of_le (sup_le hAbX hLbX)
    rw [hAb27, hLbcard] at h1
    rw [hXcard, hLbcard] at h2
    nlinarith
  have hD' : 9 ≤ Nat.card ((Ab ⊓ Lb).comap f) := by
    have h1 : (((Ab ⊓ Lb).comap f).map f : Subgroup (H ⧸ Q)) = Ab ⊓ Lb :=
      Subgroup.map_comap_eq_self inf_le_left
    rw [← Subgroup.card_map_of_injective hfinj, h1]
    exact hD
  have hsub : (((Ab ⊓ Lb).comap f).map (A.subgroupOf H).subtype).map H.subtype ≤
      A ⊓ inSubgroup perfectResidual (H ⊓ C) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have haA : ((a : H) : G) ∈ A := Subgroup.mem_subgroupOf.mp a.2
    refine ⟨haA, ?_⟩
    have haC : ((a : H) : G) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨_, haA⟩ ⟨c, hcA⟩))
    exact mem_of_mk_mem hcH hc3 hcL (a : H).2 haC (hA.1.2 _ haA) (Subgroup.mem_inf.mp ha).2
  have hcard : Nat.card ((Ab ⊓ Lb).comap f) ≤
      Nat.card (A ⊓ inSubgroup perfectResidual (H ⊓ C) : Subgroup G) := by
    calc Nat.card ((Ab ⊓ Lb).comap f)
        = Nat.card ((((Ab ⊓ Lb).comap f).map (A.subgroupOf H).subtype).map H.subtype) := by
          rw [Subgroup.card_map_of_injective H.subtype_injective,
            Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      _ ≤ _ := Subgroup.card_le_of_le hsub
  refine ⟨hD'.trans hcard, fun hcLm => hc1 ?_⟩
  have hcX : π ⟨c, hcH⟩ ∈ X := hAX c hcH hcA
  have hcZ := KFacts.KS18.mem_range_inlY_of_mem_centralizer e' hk hcX
    (hLbr ▸ mk_mem_centralizer hcH hcL)
  have hcLb : π ⟨c, hcH⟩ ∈ Lb := by
    rw [← hLimg]
    exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcLm, rfl⟩
  rw [hLbr] at hcLb
  obtain ⟨z, hz⟩ := hcZ
  obtain ⟨p, hp⟩ := hcLb
  have hzp : KFacts.KS18.inlY e' z = KFacts.KS18.inrY e' p := hz.trans hp.symm
  rw [KFacts.KS18.inlY_apply, KFacts.KS18.inrY_apply] at hzp
  have hzp' := congrArg Prod.snd (e'.symm.injective (Subtype.ext hzp))
  have hp1 : p = 1 := hzp'.symm
  have h1 : π ⟨c, hcH⟩ = 1 := by rw [← hp, hp1, map_one]
  have hcR : c ∈ R := (hmemR _).mp h1
  have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
  have : c ∈ A ⊓ R := ⟨hcA, hcR⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this

end Rem187QProof

end CFSG.RankThree.PartTwo.Sec18
