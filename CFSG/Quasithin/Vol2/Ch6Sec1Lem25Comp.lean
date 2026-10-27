module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24Three
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem27
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem22

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

section Generic

theorem isQuasisimple_quot_pCore_two_of_surjective {W Q : Type*} [Group W] [Finite W]
    [Group Q] (hQ : CFSG.IsQuasisimple Q) (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) : CFSG.IsQuasisimple (W ⧸ CFSG.pCore 2 W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective ρ hρ
  have hOn : (CFSG.pCore 2 W).Normal := CFSG.pCore_normal
  have hOp : IsPGroup 2 (CFSG.pCore 2 W) := CFSG.pCore_isPGroup
  have hkerO : ρ.ker ≤ CFSG.pCore 2 W := le_sSup ⟨inferInstance, hker⟩
  have hO'n : ((CFSG.pCore 2 W).map ρ).Normal := hOn.map _ hρ
  have hO'p : IsPGroup 2 ((CFSG.pCore 2 W).map ρ) := hOp.map _
  have hO'c : (CFSG.pCore 2 W).map ρ ≤ Subgroup.center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hO'n with htop | hc
    · exfalso
      have h2 : IsPGroup 2 (⊤ : Subgroup Q) := htop ▸ hO'p
      have h3 : IsPGroup 2 Q := h2.of_equiv Subgroup.topEquiv
      have hnil := h3.isNilpotent
      have hsolv : Group.IsSolvable Q := inferInstance
      have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
      exact hlt.ne hQ.1.commutator_eq_top
    · exact hc
  have hquot := (CFSG.LocalCores.quasisimple_central_quotient hQ _ hO'c).1
  let φ : W →* Q ⧸ (CFSG.pCore 2 W).map ρ := (QuotientGroup.mk' _).comp ρ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hρ
  have hφker : φ.ker = CFSG.pCore 2 W := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have h2 := mul_mem hy (hkerO h1)
      rwa [mul_inv_cancel_left] at h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  have e : W ⧸ CFSG.pCore 2 W ≃* Q ⧸ (CFSG.pCore 2 W).map ρ :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquot

theorem mem_pCore_two_of_mem_fittingSubgroup {X : Type*} [Group X] [Finite X] {y : X}
    (hy : y ∈ CFSG.fittingSubgroup X) (hyp : ∃ k : ℕ, y ^ (2 ^ k) = 1) :
    y ∈ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.fittingSubgroup X
  obtain ⟨k, hk⟩ := hyp
  have hk' : (⟨y, hy⟩ : F) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hpg : IsPGroup 2 (Subgroup.zpowers (⟨y, hy⟩ : F)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change ((⟨y, hy⟩ : F) ^ n) ^ (2 ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hmem : y ∈ (P : Subgroup F).map F.subtype :=
    ⟨⟨y, hy⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  exact Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent 2 P hmem

end Generic

theorem existsComponent6_1_25_of (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) : ExistsComponent6_1_25 := by
  intro G _ _ T M L V n h l hl hlN
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h22 := stmt6_1_22 h432 h6110 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h22
  have h1 := h.lemma_6_1_24_one h432 h6111 h6119 hl hlN
  obtain ⟨-, hidx, -⟩ := h.lemma_6_1_24_two h432 h6111 h6119 hl hlN
  have h3 := h.lemma_6_1_24_three h432 h6111 h6119 hl hlN
  have h4 := h.lemma_6_1_24_four h432
  have hCHI := h.centralizerMod_normalizer_le h432 h6111 h6119
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.2.1
  rw [inf_eq_right.mpr le_sup_left, h.conjClosure_sup_T_eq] at h17
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  obtain ⟨hUO, -⟩ := h.lemma_6_1_20_one h432
  set Z := ch6ZS T L V with hZ
  set I := Subgroup.centralizer (Z : Set G) with hI
  set H := Subgroup.normalizer (Z : Set G) with hH
  set U := conjClosure V I with hU
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set CI := centralizerMod Z I U with hCI
  set CH := centralizerMod Z H U with hCH
  have hZV : Z ≤ V := inf_le_left
  have hIH : I ≤ H := Subgroup.centralizer_le_normalizer _
  have hCHeq : CH = CI :=
    le_antisymm (fun x hx => ⟨hCHI hx, hx.2.1, hx.2.2⟩) (centralizerMod_mono_left U hIH)
  have hCI2 : IsPGroup 2 CI := by
    have e : CI = pCoreOf 2 I := h17.symm
    rw [e]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨-, ⟨hRAB, -⟩, -, -, -, -⟩ := h21
  have hRI : R ≤ I := by
    rw [hRAB]
    refine sup_le (inf_le_left.trans (hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I))) ?_
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV))
  have hRC : ¬ R ≤ CH := by
    intro hle
    have hRCU : U ⊓ Subgroup.centralizer (V : Set G) = R := by
      rw [h1]
      refine le_antisymm (centralizerMod_le_left _ _ _) fun x hx => ?_
      exact ⟨hx, (hle hx).2.1, (hle hx).2.2⟩
    rw [hRCU, Subgroup.relIndex_self, one_mul] at hidx
    exact h22.ne (le_antisymm h22.le (Subgroup.relIndex_eq_one.mp hidx.symm))
  have hCII : CI ≤ I := centralizerMod_le_left _ _ _
  have hICI : I ≤ Subgroup.normalizer (CI : Set G) :=
    le_normalizer_centralizerMod (Subgroup.centralizer_le_normalizer _) Subgroup.le_normalizer
      (le_normalizer_conjClosure V I)
  set C' : Subgroup ↥I := CI.subgroupOf I with hC'
  have hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCII).mpr hICI
  set π : ↥I →* ↥I ⧸ C' := QuotientGroup.mk' C' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C'
  have hπ1 : ∀ x : ↥I, π x = 1 ↔ (x : G) ∈ CI := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  set Rs := (R.subgroupOf I).map π with hRs
  obtain ⟨r₀, hr₀R, hr₀C⟩ : ∃ r ∈ R, r ∉ CH := Set.not_subset.mp hRC
  have hr₀ : π ⟨r₀, hRI hr₀R⟩ ∈ Rs := ⟨⟨r₀, hRI hr₀R⟩, Subgroup.mem_subgroupOf.mpr hr₀R, rfl⟩
  have hRs1 : π ⟨r₀, hRI hr₀R⟩ ≠ 1 := fun h0 => hr₀C (hCHeq ▸ (hπ1 _).mp h0)
  have hRs2 : IsPGroup 2 Rs :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRI).symm).map π
  have hO2 : CFSG.pCore 2 (↥I ⧸ C') = ⊥ := by
    set P := ((CFSG.pCore 2 (↥I ⧸ C')).comap π).map I.subtype with hP
    have hPmem : ∀ x : ↥I, (x : G) ∈ P ↔ π x ∈ CFSG.pCore 2 (↥I ⧸ C') := fun x => by
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [show y = x from Subtype.ext hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hPI : P ≤ I := Subgroup.map_subtype_le _
    have hIP : I ≤ Subgroup.normalizer (P : Set G) := by
      intro i hi
      refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
      have hxI : x ∈ I := hPI hx
      have hx' := (hPmem ⟨x, hxI⟩).mp hx
      have hc : π (⟨i, hi⟩ * ⟨x, hxI⟩ * ⟨i, hi⟩⁻¹) ∈ CFSG.pCore 2 (↥I ⧸ C') := by
        rw [map_mul, map_mul, map_inv]
        exact CFSG.pCore_normal.conj_mem _ hx' _
      exact (hPmem ⟨i * x * i⁻¹, I.mul_mem (I.mul_mem hi hxI) (I.inv_mem hi)⟩).mpr hc
    have hP2 : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ CI := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 (↥I ⧸ C'))) ⟨π y, hy⟩
      refine ⟨k, ?_⟩
      have hk' : π (y ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      simpa using (hπ1 _).mp hk'
    have hPC := h4 P hPI hIP hP2
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨w', rfl⟩ : ∃ w', π w' = w := hπs w
    have hw' : (w' : G) ∈ P := (hPmem w').mpr hw
    rw [Subgroup.mem_bot]
    exact (hπ1 w').mpr (hPC hw')
  have hF : Rs ≤ Subgroup.centralizer (CFSG.fittingSubgroup (↥I ⧸ C') : Set (↥I ⧸ C')) := by
    set N := ((CFSG.fittingSubgroup (↥I ⧸ C')).comap π).map I.subtype with hN
    have hNmem : ∀ x : ↥I, (x : G) ∈ N ↔ π x ∈ CFSG.fittingSubgroup (↥I ⧸ C') := fun x => by
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [show y = x from Subtype.ext hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hNI : N ≤ I := Subgroup.map_subtype_le _
    have hCN : CI ≤ N := fun x hx => (hNmem ⟨x, hCII hx⟩).mpr (by
      rw [(hπ1 ⟨x, hCII hx⟩).mpr hx]
      exact Subgroup.one_mem _)
    have hIN : I ≤ Subgroup.normalizer (N : Set G) := by
      intro i hi
      refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
      have hxI : x ∈ I := hNI hx
      have hx' := (hNmem ⟨x, hxI⟩).mp hx
      have hc : π (⟨i, hi⟩ * ⟨x, hxI⟩ * ⟨i, hi⟩⁻¹) ∈ CFSG.fittingSubgroup (↥I ⧸ C') := by
        rw [map_mul, map_mul, map_inv]
        exact CFSG.fittingSubgroup_normal.conj_mem _ hx' _
      exact (hNmem ⟨i * x * i⁻¹, I.mul_mem (I.mul_mem hi hxI) (I.inv_mem hi)⟩).mpr hc
    have hCNn : (CI.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr (hNI.trans hICI)
    let f : ↥N →* CFSG.fittingSubgroup (↥I ⧸ C') :=
      (π.comp (Subgroup.inclusion hNI)).codRestrict _ fun x => (hNmem ⟨x, hNI x.2⟩).mp x.2
    have hfs : Function.Surjective f := by
      rintro ⟨w, hw⟩
      obtain ⟨w', rfl⟩ : ∃ w', π w' = w := hπs w
      exact ⟨⟨w', (hNmem w').mpr hw⟩, rfl⟩
    have hfk : f.ker = CI.subgroupOf N := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact (hπ1 ⟨x, hNI x.2⟩).mp (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((hπ1 ⟨x, hNI x.2⟩).mpr hx)
    have e : (↥N ⧸ CI.subgroupOf N) ≃* CFSG.fittingSubgroup (↥I ⧸ C') :=
      (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs)
    have hnil : Group.IsNilpotent (↥N ⧸ CI.subgroupOf N) :=
      Group.nilpotent_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hRN := h3 N hCN hNI hIN hCNn hnil
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w', rfl⟩ : ∃ w', π w' = w := hπs w
    have hw'N : (w' : G) ∈ N := (hNmem w').mpr hw
    have hc := hRN (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hr) hw'N)
    have h1' : π (r * w' * r⁻¹ * w'⁻¹) = 1 := (hπ1 _).mpr (hCHeq ▸ hc)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1'
    calc π w' * π r = (π r * π w' * (π r)⁻¹ * (π w')⁻¹)⁻¹ * (π r * π w') := by group
      _ = π r * π w' := by rw [h1', inv_one, one_mul]
  have hex : ∃ Kb : Subgroup (↥I ⧸ C'), CFSG.IsComponent Kb ∧
      ¬ Rs ≤ Subgroup.centralizer (Kb : Set (↥I ⧸ C')) := by
    by_contra hcon
    push Not at hcon
    have hE : Rs ≤ Subgroup.centralizer (CFSG.layer (↥I ⧸ C') : Set (↥I ⧸ C')) := by
      rw [Subgroup.le_centralizer_iff]
      show sSup {K : Subgroup (↥I ⧸ C') | CFSG.IsComponent K} ≤ _
      refine sSup_le fun K hK => ?_
      exact Subgroup.le_centralizer_iff.mp (hcon K hK)
    have hFs : Rs ≤ Subgroup.centralizer
        (CFSG.generalizedFitting (↥I ⧸ C') : Set (↥I ⧸ C')) := by
      rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting, sup_le_iff]
      exact ⟨Subgroup.le_centralizer_iff.mp hF, Subgroup.le_centralizer_iff.mp hE⟩
    set Cs := Subgroup.centralizer (CFSG.generalizedFitting (↥I ⧸ C') : Set (↥I ⧸ C'))
      with hCs
    have hCsle : Cs ≤ CFSG.generalizedFitting (↥I ⧸ C') :=
      CFSG.centralizer_generalizedFitting_le _
    have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥I ⧸ C')).1
    have hCsn : Cs.Normal := Subgroup.normal_centralizer
    have hCscomm : IsMulCommutative Cs := ⟨⟨fun x y => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp x.2 y (hCsle y.2)).symm⟩⟩
    have hCsF : Cs ≤ CFSG.fittingSubgroup (↥I ⧸ C') :=
      CFSG.LocalCores.fitting_characteristic.2.2 Cs hCsn inferInstance
    apply hRs1
    have hmem : π ⟨r₀, hRI hr₀R⟩ ∈ CFSG.pCore 2 (↥I ⧸ C') := by
      refine mem_pCore_two_of_mem_fittingSubgroup (hCsF (hFs hr₀)) ?_
      obtain ⟨k, hk⟩ := hRs2 ⟨_, hr₀⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [hO2, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨Kb, hKb, hKbR⟩ := hex
  have hKbC : Kb ∈ cComp (⊤ : Subgroup (↥I ⧸ C')) := mem_cComp_top_of_isComponent hKb
  have hsolv : Group.IsSolvable ↥CI := by
    have := hCI2.isNilpotent
    infer_instance
  obtain ⟨K, hKC, hKimg⟩ := (cComp_quotient_bijOn_of_le hCII hC'n hsolv).surjOn hKbC
  have hKI : K ≤ I := le_of_mem_cComp hKC
  have hKmem : ∀ x : ↥K, π ⟨x, hKI x.2⟩ ∈ Kb := fun x => by
    rw [← hKimg]
    exact ⟨⟨x, hKI x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  refine ⟨K, hKC, ?_, ?_⟩
  ·
    let ρ : ↥K →* ↥Kb := (π.comp (Subgroup.inclusion hKI)).codRestrict Kb hKmem
    have hρs : Function.Surjective ρ := by
      rintro ⟨w, hw⟩
      rw [← hKimg] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    have hρk : IsPGroup 2 ρ.ker := by
      intro x
      have hx1 : π ⟨x.1, hKI x.1.2⟩ = 1 := congrArg Subtype.val x.2
      obtain ⟨k, hk⟩ := hCI2 ⟨x.1, (hπ1 _).mp hx1⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact isQuasisimple_quot_pCore_two_of_surjective hKb.1 ρ hρs hρk
  ·
    intro hle
    apply hKbR
    rw [← hKimg]
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hc := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hk)
      (Subgroup.mem_subgroupOf.mp hr))
    have h1' : π (k * r * k⁻¹ * r⁻¹) = 1 := (hπ1 _).mpr (hCHeq ▸ hc)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1'
    calc π k * π r = (π k * π r * (π k)⁻¹ * (π r)⁻¹) * (π r * π k) := by group
      _ = π r * π k := by rw [h1', one_mul]

end CFSG.Quasithin.H13
