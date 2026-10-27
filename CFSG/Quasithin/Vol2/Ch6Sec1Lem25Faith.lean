module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Comp
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25DL
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Phi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem mem_CH_of_comm (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) {r : G} (hr : r ∈ ch6R T L V l)
    (hc : ∀ K₀ ∈ cComp (Subgroup.centralizer (ch6ZS T L V : Set G)),
      CFSG.IsQuasisimple (KQ K₀) → ∀ k ∈ K₀, r * k * r⁻¹ * k⁻¹ ∈ ch6CH T L V) :
    r ∈ ch6CH T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := h.lemma_6_1_24_three h432 h6111 h6119 hl hlN
  have h4 := h.lemma_6_1_24_four h432
  have hCHI := h.centralizerMod_normalizer_le h432 h6111 h6119
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.2.1
  rw [inf_eq_right.mpr le_sup_left, h.conjClosure_sup_T_eq] at h17
  have hRI0 := h.R_le_I h432 h6111 h6119 hl hlN
  set Z := ch6ZS T L V with hZ
  set I := Subgroup.centralizer (Z : Set G) with hI
  set H := Subgroup.normalizer (Z : Set G) with hH
  set U := conjClosure V I with hU
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set CI := centralizerMod Z I U with hCI
  set CH := centralizerMod Z H U with hCH
  have hIH : I ≤ H := Subgroup.centralizer_le_normalizer _
  have hCHeq : CH = CI :=
    le_antisymm (fun x hx => ⟨hCHI hx, hx.2.1, hx.2.2⟩) (centralizerMod_mono_left U hIH)
  have hCI2 : IsPGroup 2 CI := by
    have e : CI = pCoreOf 2 I := h17.symm
    rw [e]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRI : R ≤ I := hRI0
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
  have hrI : r ∈ I := hRI hr
  have hE : Subgroup.zpowers (π ⟨r, hrI⟩) ≤
      Subgroup.centralizer (CFSG.layer (↥I ⧸ C') : Set (↥I ⧸ C')) := by
    rw [Subgroup.le_centralizer_iff]
    show sSup {K : Subgroup (↥I ⧸ C') | CFSG.IsComponent K} ≤ _
    refine sSup_le fun Kb hKb => ?_
    rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    have hKbC : Kb ∈ cComp (⊤ : Subgroup (↥I ⧸ C')) := mem_cComp_top_of_isComponent hKb
    have hsolv : Group.IsSolvable ↥CI := by
      have := hCI2.isNilpotent
      infer_instance
    obtain ⟨K₀, hK₀C, hK₀img⟩ := (cComp_quotient_bijOn_of_le hCII hC'n hsolv).surjOn hKbC
    have hK₀I : K₀ ≤ I := le_of_mem_cComp hK₀C
    have hK₀mem : ∀ x : ↥K₀, π ⟨x, hK₀I x.2⟩ ∈ Kb := fun x => by
      rw [← hK₀img]
      exact ⟨⟨x, hK₀I x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    have hq : CFSG.IsQuasisimple (KQ K₀) := by
      let ρ : ↥K₀ →* ↥Kb := (π.comp (Subgroup.inclusion hK₀I)).codRestrict Kb hK₀mem
      have hρs : Function.Surjective ρ := by
        rintro ⟨w, hw⟩
        rw [← hK₀img] at hw
        obtain ⟨k, hk, rfl⟩ := hw
        exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
      have hρk : IsPGroup 2 ρ.ker := by
        intro x
        have hx1 : π ⟨x.1, hK₀I x.1.2⟩ = 1 := congrArg Subtype.val x.2
        obtain ⟨k, hk⟩ := hCI2 ⟨x.1, (hπ1 _).mp hx1⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      exact isQuasisimple_quot_pCore_two_of_surjective hKb.1 ρ hρs hρk
    have hcK₀ := hc K₀ hK₀C hq
    rw [← hK₀img]
    rintro _ ⟨k, hk, rfl⟩
    have hkK₀ : (k : G) ∈ K₀ := Subgroup.mem_subgroupOf.mp hk
    have h1' : π (⟨r, hrI⟩ * k * (⟨r, hrI⟩ : ↥I)⁻¹ * k⁻¹) = 1 :=
      (hπ1 _).mpr (hCHeq ▸ hcK₀ k hkK₀)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1'
    calc π k * π ⟨r, hrI⟩ =
        (π ⟨r, hrI⟩ * π k * (π ⟨r, hrI⟩)⁻¹ * (π k)⁻¹)⁻¹ * (π ⟨r, hrI⟩ * π k) := by group
      _ = π ⟨r, hrI⟩ * π k := by rw [h1', inv_one, one_mul]
  have hrR : π ⟨r, hrI⟩ ∈ Rs := ⟨⟨r, hrI⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hFs : Subgroup.zpowers (π ⟨r, hrI⟩) ≤ Subgroup.centralizer
      (CFSG.generalizedFitting (↥I ⧸ C') : Set (↥I ⧸ C')) := by
    rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting, sup_le_iff]
    refine ⟨?_, Subgroup.le_centralizer_iff.mp hE⟩
    rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hF hrR
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
  have hmem : π ⟨r, hrI⟩ ∈ CFSG.pCore 2 (↥I ⧸ C') := by
    refine mem_pCore_two_of_mem_fittingSubgroup (hCsF (hFs (Subgroup.mem_zpowers _))) ?_
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ : IsPGroup 2 R) ⟨r, hr⟩
    refine ⟨k, ?_⟩
    have hk' : r ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow]
    have e : (⟨r, hrI⟩ : ↥I) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
    rw [e, map_one]
  rw [hO2, Subgroup.mem_bot] at hmem
  show r ∈ CH
  rw [hCHeq]
  exact (hπ1 _).mp hmem

end Hyp6116

end CFSG.Quasithin.H13
