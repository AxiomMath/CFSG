module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentC
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

section Assembly

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem pCoreOf_subgroupOf_ch615 (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite G] in
theorem commutator_subgroupOf_ch615 {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    (⁅A, B⁆).subgroupOf H = ⁅A.subgroupOf H, B.subgroupOf H⁆ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hA hB)]

omit [Finite G] in
theorem le_commutator_sup_of_quot_ch615 {A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (h : (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)) ≤
      ⁅(A.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)),
        (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))⁆) :
    A ≤ ⁅A, B⁆ ⊔ pCoreOf 2 H := by
  intro a ha
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 H) ⟨a, hAH ha⟩ ∈
      ⁅(A.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)),
        (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))⁆ :=
    h (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha))
  rw [← Subgroup.map_commutator] at h1
  obtain ⟨w, hw, hwa⟩ := h1
  have hker : w⁻¹ * ⟨a, hAH ha⟩ ∈ CFSG.Open.pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (CFSG.Open.pCore 2 H), MonoidHom.mem_ker, map_mul, map_inv,
      hwa, inv_mul_cancel]
  have hwG : (w : G) ∈ ⁅A, B⁆ := by
    have := Subgroup.mem_map_of_mem H.subtype hw
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAH,
      Subgroup.map_subgroupOf_eq_of_le hBH] at this
  have hO : ((w⁻¹ * ⟨a, hAH ha⟩ : H) : G) ∈ pCoreOf 2 H := ⟨_, hker, rfl⟩
  have e : a = (w : G) * ((w⁻¹ * ⟨a, hAH ha⟩ : H) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwG) (Subgroup.mem_sup_right hO)

theorem Cx615B.le_commutator_sup_ch615 (h331 : Stmt3_3_1) (hR : RankTwoThreeClassTwo)
    (c : Cx615B G T M L V H n) :
    H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤
      ⁅H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G), thompsonJ T⁆ ⊔ pCoreOf 2 H := by
  classical
  have hMP := c.toCx615.minParabolic h331
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hTH : T ≤ H := c.hH.1.1
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hTH
  have hCJ : H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ kerIn (H ⊓ M) H :=
    hMP.inf_centralizer_le_kerIn c.toCx615.UH_red.2 c.toCx615.not_le_centralizer_UH
  refine le_commutator_sup_of_quot_ch615 inf_le_left hJTH ?_
  set C' := (H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G)).subgroupOf H with hC'
  set φ := QuotientGroup.mk' (CFSG.Open.pCore 2 H) with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set Cb := C'.map φ with hCb
  set Jb := ((thompsonJ T).subgroupOf H).map φ with hJb
  set Kb := twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 H)) with hKbdef
  have hker' : c.cvH.ker = C' := ker_convHom c.hU H hHN
  have hmemC : ∀ g : ↥H, c.cvH g = 1 → g ∈ C' := fun g hg => hker' ▸ hg
  have hO'C : CFSG.Open.pCore 2 H ≤ C' := by
    rw [← pCoreOf_subgroupOf_ch615]
    exact Subgroup.subgroupOf_mono H (le_inf (pCoreOf_le 2 H)
      (MinParabolic.pCoreOf_le_centralizer c.toCx615.UH_red.2))
  have hKb : Kb = ((oTwoUpper H).subgroupOf H).map φ := by
    rw [hKbdef, ← B6.twoResidual_map_top hsurj, B6.twoResidual_top_eq_subgroupOf,
      twoResidual_eq_oTwoUpper']
  have hKbn : (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 H)) ≤
      Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.Open.pCore 2 H)) :=
    le_normalizer_twoResidual ⊤
  have hKJK : Kb ≤ ⁅Kb, Jb⁆ := by
    have e : ⁅oTwoUpper H, thompsonJ T⁆ = oTwoUpper H := c.JK
    have h1 : ((oTwoUpper H).subgroupOf H).map φ = ⁅((oTwoUpper H).subgroupOf H).map φ, Jb⁆ := by
      conv_lhs => rw [← e]
      rw [commutator_subgroupOf_ch615 (oTwoUpper_le H) hJTH, Subgroup.map_commutator]
    rw [hKb]
    exact h1.le
  have hJb2 : IsPGroup 2 Jb := by
    have h1 : IsPGroup 2 ((thompsonJ T).subgroupOf H) :=
      (c.hyp.sylow.1.to_le (thompsonJ_le_self T)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hJTH).symm
    exact h1.map φ
  have hCbodd : ∀ g ∈ Cb, Odd (orderOf g) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, hC', Subgroup.mem_subgroupOf] at hg
    obtain ⟨e, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hg2 : ((g : G) ^ r) ^ 2 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hm, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    have hzp : IsPGroup 2 (Subgroup.zpowers ((g : G) ^ r)) := by
      rintro ⟨u, hu⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      refine ⟨e, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
    have hle : Subgroup.zpowers ((g : G) ^ r) ≤ kerIn (H ⊓ M) H :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (hCJ hg) r)
    have hO := hMP.le_pCoreOf_of_isPGroup_of_le_kerIn hzp hle (Subgroup.mem_zpowers _)
    have hO' : g ^ r ∈ CFSG.Open.pCore 2 H := by
      rw [← pCoreOf_subgroupOf_ch615, Subgroup.mem_subgroupOf]
      exact hO
    have h1 : φ g ^ r = 1 := by
      rw [← map_pow, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hO'
    exact Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one h1)
  have hCbK : Cb ≤ Kb := fun g hg => by
    rw [hKbdef, twoResidual_eq_oTwoUpper']
    exact mem_oTwoUpper_of_odd (Subgroup.mem_top g) (hCbodd g hg)
  by_cases hab : ∀ g ∈ Kb, ∀ h ∈ Kb, g * h = h * g
  · exact fun g hg => mem_commutator_of_comm_ch615 hab hJb2 (le_top.trans hKbn) hKJK hCbK hg
      (hCbodd g hg)
  have hnc : ∃ g ∈ Kb, ∃ h ∈ Kb, g * h ≠ h * g := by
    by_contra hall
    exact hab fun g hg h hh => by
      by_contra hne
      exact hall ⟨g, hg, h, hh, hne⟩
  obtain ⟨hBsolv, hdata⟩ := c.blocks_ch615
  have hsolvH : Group.IsSolvable ↥H := by
    have hJs : Group.IsSolvable ↥(kerIn (H ⊓ M) H) := by
      have hsol := hMP.subgroupOf.isSolvable_kerIn
      rw [B6.kerIn_subgroupOf_top] at hsol
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hMP.kerIn_le_H).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hMP.kerIn_le_H).surjective
    have hKs : Group.IsSolvable ↥(oTwoUpper H) := by
      have hKN : oTwoUpper H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) :=
        (oTwoUpper_le H).trans hHN
      set g := (convHom c.hU (oTwoUpper H) hKN).rangeRestrict with hg
      have hrange : (convHom c.hU (oTwoUpper H) hKN).range ≤ autI c.hU (thompsonJ H) := by
        rw [range_convHom]
        refine autI_mono c.hU ?_
        rw [← twoResidual_eq_oTwoUpper']
        exact c.e23.1
      have hs1 : Group.IsSolvable ↥(convHom c.hU (oTwoUpper H) hKN).range :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hrange)
          (Subgroup.inclusion_injective hrange)
      have hkerle : oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤
          kerIn (H ⊓ M) H :=
        (inf_le_inf_right _ (oTwoUpper_le H)).trans hCJ
      have hs2 : Group.IsSolvable
          ↥(oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G)) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hkerle)
          (Subgroup.inclusion_injective hkerle)
      refine Group.isSolvable_of_ker_le_range
        (Subgroup.inclusion (inf_le_left :
          oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ oTwoUpper H)) g ?_
      intro k hk
      rw [hg, MonoidHom.ker_rangeRestrict, ker_convHom] at hk
      refine ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    refine B6.isSolvable_of_twoResidual ?_
    rw [B6.twoResidual_top_eq_subgroupOf, twoResidual_eq_oTwoUpper']
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (oTwoUpper_le H)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (oTwoUpper_le H)).symm.surjective
  have hsolvQ : Group.IsSolvable (↥H ⧸ CFSG.Open.pCore 2 H) := inferInstance
  have hX := hMP.subgroupOf
  have hkerφ : φ.ker ≤ (H ⊓ M).subgroupOf H := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hX.pCore_le_M
  have hQ := hX.map_of_surjective hsurj hkerφ
  have hOQ := B6.pCore_quotient_pCore (X := ↥H)
  obtain ⟨p, hp, hp2, hZ⟩ := hQ.exists_odd_prime_of_solvable hsolvQ
  have hKp := hQ.isPGroup_twoResidual_of_pCore_eq_bot hOQ hsolvQ hp hZ
  have hfr := hQ.kerIn_eq_frattini_twoResidual hOQ hsolvQ hp hp2 hZ
  rw [B6.kerIn_map_top hsurj hkerφ, B6.kerIn_subgroupOf_top] at hfr
  have hCbΦ : Cb ≤ (frattini Kb).map Kb.subtype := by
    rw [hKbdef, ← hfr]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hCJ)
  have hm3 : ∀ E : Subgroup (↥H ⧸ CFSG.Open.pCore 2 H), IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 H) := by
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2).exists_card_eq
      rw [hk]
      intro hd
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
      omega
    have hrank := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 H) h3
    have hle := c.toCx615.sqtk.1 3 Nat.prime_three (by norm_num)
    have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
    obtain ⟨k, hk⟩ := hE3.exists_card_eq
    have hkr := le_pRank Nat.prime_three le_top hE hk
    rw [hrank] at hkr
    have hk2 : k ≤ 2 := hkr.trans hle
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hφC : ∀ g : ↥H, c.cvH g = 1 → φ g ∈ Cb := fun g hg =>
    Subgroup.mem_map_of_mem φ (hmemC g hg)
  have hKbmem : ∀ k ∈ (oTwoUpper H).subgroupOf H, φ k ∈ Kb := fun k hk => by
    rw [hKb]; exact Subgroup.mem_map_of_mem φ hk
  rcases hdata with ⟨x, hx, hcyc⟩ | ⟨x, hx, y, hy, a, ha, s, -, hx1, hx3, hax, hay, hsx, hsy, hgen⟩
  ·
    exfalso
    obtain ⟨g, hg, h, hh, hgh⟩ := hnc
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have : Fact (IsPGroup p Kb) := ⟨hKp⟩
    have hw : ∀ u : ↥Kb, ∃ i : ℤ, ((⟨φ x, hKbmem x hx⟩ : ↥Kb) ^ i)⁻¹ * u ∈ frattini Kb := by
      intro u
      obtain ⟨u, hu⟩ := u
      rw [hKb] at hu
      obtain ⟨k, hk, rfl⟩ := hu
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hcyc k hk)
      refine ⟨i, ?_⟩
      have h1 : c.cvH ((x ^ i)⁻¹ * k) = 1 := by
        rw [map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
      obtain ⟨f, hf, hff⟩ := hCbΦ (hφC _ h1)
      have : f = (⟨φ x, hKbmem x hx⟩ ^ i)⁻¹ * ⟨φ k, hKbmem k hk⟩ := Subtype.ext (by
        rw [Subgroup.coe_subtype] at hff
        simp [hff])
      rw [← this]
      exact hf
    have hcomm := comm_of_frattini_zpowers_ch615 hw ⟨g, hg⟩ ⟨h, hh⟩
    exact hgh (by simpa using congrArg Subtype.val hcomm)
  ·
    have hKbN : Kb.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKbn)
    refine le_commutator_of_rankTwo_ch615 (P := Kb) (s := φ s) hR hp hKp hCbΦ hm3 hnc (hKbmem x hx)
      (hKbmem y hy) (Subgroup.mem_map_of_mem φ ha) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro hxC
      obtain ⟨g, hg, hgx⟩ := hxC
      apply hx1
      have hg' : g⁻¹ * x ∈ CFSG.Open.pCore 2 H := by
        rw [← QuotientGroup.ker_mk' (CFSG.Open.pCore 2 H), MonoidHom.mem_ker, map_mul, map_inv]
        rw [← hφ, hgx, inv_mul_cancel]
      have hxC' : x ∈ C' := by
        have e : x = g * (g⁻¹ * x) := by group
        rw [e]
        exact C'.mul_mem hg (hO'C hg')
      rw [← hker'] at hxC'
      exact hxC'
    · rw [← map_pow]; exact hφC _ (by rw [map_pow]; exact hx3)
    · have := hφC _ hax
      simpa only [map_mul, map_inv] using this
    · have := hφC _ hay
      simpa only [map_mul, map_inv] using this
    · have := hφC _ hsx
      simpa only [map_mul, map_inv] using this
    · have := hφC _ hsy
      simpa only [map_mul, map_inv] using this
    · intro k hk
      rw [hKb] at hk
      obtain ⟨k, hk, rfl⟩ := hk
      have h1 := hgen k hk
      rw [← Set.image_pair, ← MonoidHom.map_closure] at h1
      obtain ⟨w, hw, hwk⟩ := h1
      refine ⟨φ w, ?_, ?_⟩
      · have := Subgroup.mem_map_of_mem φ hw
        rwa [MonoidHom.map_closure, Set.image_pair] at this
      · rw [← map_inv, ← map_mul]
        exact hφC _ (by rw [map_mul, map_inv, hwk, inv_mul_cancel])

theorem res615Cent_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (hR : RankTwoThreeClassTwo) :
    Res615Cent := fun _ _ _ _ _ _ _ _ _ c =>
  c.le_pCoreOf_of_le_commutator_ch615 h331 h432 (c.le_commutator_sup_ch615 h331 hR)

end Assembly

end CFSG.Quasithin.H13
