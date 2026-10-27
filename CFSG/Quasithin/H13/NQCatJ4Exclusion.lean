module

public import CFSG.Quasithin.H13.NQCatJ4Module
public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped Pointwise

theorem card_GL_eleven_dvd {e : ℕ} (he : e ≤ 2) : Nat.card (GL (Fin e) (ZMod 11)) ∣ 13200 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases e <;> simp only [Fin.prod_univ_succ, Fin.prod_univ_zero] <;> norm_num

theorem le_sixteen_of_two_pow_dvd {m : ℕ} (h : 2 ^ m ∣ 13200) : 2 ^ m ≤ 16 := by
  rcases (show m ≤ 4 ∨ 5 ≤ m by omega) with h4 | h5
  · calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
      _ = 16 := by norm_num
  · have h32 : 2 ^ 5 ∣ 13200 := (pow_dvd_pow 2 h5).trans h
    norm_num at h32

theorem mul_comm_of_normal_of_card_le_two {H : Type*} [Group H] [Finite H] {D : Subgroup H}
    [D.Normal] (hD : Nat.card D ≤ 2) {d : H} (hd : d ∈ D) (h : H) : h * d = d * h := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, one_mul]
  have hc : h * d * h⁻¹ ∈ D := Subgroup.Normal.conj_mem inferInstance d hd h
  by_cases he : h * d * h⁻¹ = d
  · calc h * d = h * d * h⁻¹ * h := by group
      _ = d * h := by rw [he]
  exfalso
  have hc1 : h * d * h⁻¹ ≠ 1 := fun h1 => hd1 (by
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group)
  have hdvd : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd
  have hord1 : orderOf d ≠ 1 := fun h1 => hd1 (orderOf_eq_one_iff.1 h1)
  have hpos : 0 < orderOf d := orderOf_pos d
  have hcard2 : Nat.card D = 2 ∧ orderOf d = 2 := by
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hzD : zpowers d = D := eq_of_le_of_card_ge (zpowers_le.2 hd)
    (by rw [Nat.card_zpowers, hcard2.1, hcard2.2])
  classical
  have hcz : h * d * h⁻¹ ∈ zpowers d := hzD ▸ hc
  rw [mem_zpowers_iff_mem_range_orderOf, hcard2.2, Finset.mem_image] at hcz
  obtain ⟨k, hk, hke⟩ := hcz
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact hc1 (by rw [← hke, pow_zero])
  · exact he (by rw [← hke, pow_one])

theorem card_two_subgroup_le {H : Type*} [Group H] [Finite H] (hsolv : Group.IsSolvable H)
    (hprimes : ∀ p ∈ (Nat.card H).primeFactors, p = 2 ∨ p = 11)
    (hD : Nat.card (CFSG.pCore 2 H) ≤ 2)
    (hR : ∃ e ≤ 2, Nat.card (CFSG.pCore 11 H ⧸ frattini (CFSG.pCore 11 H)) = 11 ^ e)
    {U : Subgroup H} (hU : IsPGroup 2 U) : Nat.card U ≤ 32 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hDn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hRn : (CFSG.pCore 11 H).Normal := CFSG.pCore_normal
  have hFDR : CFSG.fittingSubgroup H ≤ CFSG.pCore 2 H ⊔ CFSG.pCore 11 H := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    rcases hprimes p p.2 with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  let φ : U →* MulAut (CFSG.pCore 11 H) :=
    (MulAut.conjNormal (H := CFSG.pCore 11 H)).comp U.subtype
  have hker : ∀ u ∈ φ.ker, ((u : U) : H) ∈ CFSG.pCore 2 H := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hcR : ∀ r ∈ CFSG.pCore 11 H, r * (u : H) = u * r := by
      intro r hr
      have h1 := congrArg (fun α : MulAut (CFSG.pCore 11 H) =>
        (((α ⟨r, hr⟩ : CFSG.pCore 11 H)) : H)) hu
      simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply,
        Subgroup.coe_subtype] at h1
      calc r * (u : H) = (u : H) * r * (u : H)⁻¹ * u := by rw [h1]
        _ = u * r := by group
    have hcF : (u : H) ∈ centralizer (CFSG.fittingSubgroup H : Set H) := by
      rw [mem_centralizer_iff]
      intro f hf
      have hle : CFSG.pCore 2 H ⊔ CFSG.pCore 11 H ≤ centralizer ({(u : H)} : Set H) := by
        refine sup_le (fun d hd => ?_) (fun r hr => ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mul_comm_of_normal_of_card_le_two hD hd u).symm
        · rw [mem_centralizer_singleton_iff]
          exact hcR r hr
      have := hle (hFDR hf)
      rw [mem_centralizer_singleton_iff] at this
      exact this
    have huF : (u : H) ∈ CFSG.fittingSubgroup H :=
      CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hcF
    have hzp : IsPGroup 2 (zpowers (⟨u, huF⟩ : CFSG.fittingSubgroup H)) := by
      obtain ⟨n, hn⟩ := hU u
      have hx : (⟨(u : H), huF⟩ : CFSG.fittingSubgroup H) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        have := congrArg (fun v : U => (v : H)) hn
        simpa using this
      intro g
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
      refine ⟨n, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hx, one_zpow, Subgroup.coe_one]
    obtain ⟨P, hP⟩ := hzp.exists_le_sylow
    have hmap := Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent 2 P
    exact hmap ⟨⟨u, huF⟩, hP (mem_zpowers _), rfl⟩
  have hkcard : Nat.card φ.ker ≤ 2 := by
    let g : φ.ker → CFSG.pCore 2 H := fun k => ⟨((k : U) : H), hker k k.2⟩
    have hg : Function.Injective g := fun a b hab => by
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact (Nat.card_le_card_of_injective g hg).trans hD
  have hrcard : Nat.card φ.range ≤ 16 := by
    obtain ⟨e, he, hecard⟩ := hR
    have : Finite (MulAut (CFSG.pCore 11 H)) :=
      Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (CFSG.pCore 11 H)))
    have hbound := CFSG.RankThree.GroupTheory.SteinbergBK.pow_factorization_card_mulAut_dvd
      (p := 2) (q := 11) (by norm_num) CFSG.pCore_isPGroup hecard
    obtain ⟨m, hm⟩ := (hU.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).exists_card_eq
    have hdvd : 2 ^ m ∣ Nat.card (MulAut (CFSG.pCore 11 H)) :=
      hm ▸ card_subgroup_dvd_card φ.range
    have hm' : m ≤ (Nat.card (MulAut (CFSG.pCore 11 H))).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
    rw [hm]
    exact le_sixteen_of_two_pow_dvd ((((pow_dvd_pow 2 hm').trans hbound).trans
      (Nat.ordProj_dvd _ _)).trans (card_GL_eleven_dvd he))
  have hUcard : Nat.card U = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [hUcard]
  calc Nat.card φ.range * Nat.card φ.ker ≤ 16 * 2 := Nat.mul_le_mul hrcard hkcard
    _ = 32 := by norm_num

theorem card_sylow_two_J4J
    (U : Sylow 2 Sporadic.J4.J) : Nat.card U = 2 ^ 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [U.card_eq_multiplicity, Sporadic.J4.QT.card_J_factorization Sporadic.J4.j4Facts]

theorem le_normalizer_map_of_normal {H : Subgroup Sporadic.J4.J} (K : Subgroup H) [K.Normal] :
    H ≤ normalizer ((K.map H.subtype : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) := by
  rw [← normal_subgroupOf_iff_le_normalizer (map_subtype_le K), ← comap_subtype,
    comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

theorem map_pCore_eleven_le
    {H : Subgroup Sporadic.J4.J} (hQH : j4Q ≤ H) :
    (CFSG.pCore 11 H).map H.subtype ≤ j4Q := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hRn : (CFSG.pCore 11 H).Normal := CFSG.pCore_normal
  have hQ'p : IsPGroup 11 (j4Q.subgroupOf H) :=
    j4Data.isPGroup.of_equiv (subgroupOfEquivOfLe hQH).symm
  have hsup : IsPGroup 11 (j4Q.subgroupOf H ⊔ CFSG.pCore 11 H : Subgroup H) :=
    hQ'p.to_sup_of_normal_right CFSG.pCore_isPGroup
  have hle : (j4QSylow : Subgroup Sporadic.J4.J) ≤
      (j4Q.subgroupOf H ⊔ CFSG.pCore 11 H : Subgroup H).map H.subtype := by
    intro g hg
    rw [coe_j4QSylow] at hg
    have hgH : g ∈ H := hQH hg
    exact ⟨⟨g, hgH⟩, (le_sup_left : j4Q.subgroupOf H ≤ j4Q.subgroupOf H ⊔ CFSG.pCore 11 H)
      (show (⟨g, hgH⟩ : H) ∈ j4Q.subgroupOf H from hg), rfl⟩
  have heq := j4QSylow.is_maximal' (hsup.map H.subtype) hle
  rw [coe_j4QSylow] at heq
  rw [← heq]
  exact map_mono le_sup_right

theorem not_permutable_j4Q
    (U : Sylow 2 Sporadic.J4.J) :
    (j4Q : Set Sporadic.J4.J) * ((U : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) ≠
      ((U : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) * (j4Q : Set Sporadic.J4.J) := by
  intro hQU
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set H := NQTerm.permProd j4Q U hQU with hHdef
  have hQH : j4Q ≤ H := NQTerm.le_permProd_left j4Q U hQU
  have hUH : (U : Subgroup Sporadic.J4.J) ≤ H := NQTerm.le_permProd_right j4Q U hQU
  have hU21 := card_sylow_two_J4J U
  obtain ⟨d, hd, hHcard⟩ := NQTerm.card_permProd j4Q U hQU
  rw [j4Data.card_closure] at hd
  rw [hU21] at hHcard
  have hprimes : ∀ p ∈ (Nat.card H).primeFactors, p = 2 ∨ p = 11 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    rw [hHcard] at hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1
        (hpp.dvd_of_dvd_pow (h.trans hd)))
  have hsolv : Group.IsSolvable H := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hsub : (Nat.card H).primeFactors ⊆ {2, 11} := fun p hp => by
      rcases hprimes p hp with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans (by decide)
  have hDJp : IsPGroup 2 ((CFSG.pCore 2 H).map H.subtype) :=
    CFSG.pCore_isPGroup.map H.subtype
  have hDJcard : Nat.card ((CFSG.pCore 2 H).map H.subtype) ≤ 2 ^ 21 := by
    obtain ⟨P, hP⟩ := hDJp.exists_le_sylow
    calc Nat.card ((CFSG.pCore 2 H).map H.subtype) ≤ Nat.card P := card_le_of_le hP
      _ = 2 ^ 21 := card_sylow_two_J4J P
  have : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hQD : j4Q ≤ normalizer (((CFSG.pCore 2 H).map H.subtype : Subgroup Sporadic.J4.J) :
      Set Sporadic.J4.J) :=
    hQH.trans (le_normalizer_map_of_normal _)
  have hD2 := card_le_two_of_normalized hDJp hQD (commute_z_of_normalized hDJp hDJcard hQD)
  rw [card_map_of_injective H.subtype_injective] at hD2
  have hRQ := map_pCore_eleven_le hQH
  have hRp : IsPGroup 11 (CFSG.pCore 11 H) := CFSG.pCore_isPGroup
  have hRexp : ∀ r : CFSG.pCore 11 H, r ^ 11 = 1 := fun r => by
    have h1 : ((r : H) : Sporadic.J4.J) ∈ j4Q := hRQ ⟨r, r.2, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    exact j4Data.pow_eleven h1
  obtain ⟨-, -, -, -, e, hecard, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hRp
  have he : e ≤ 2 := by
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    have hRcard : Nat.card (CFSG.pCore 11 H) = Nat.card ((CFSG.pCore 11 H).map H.subtype) :=
      (card_map_of_injective H.subtype_injective).symm
    have hk3 : k ≤ 3 := by
      have h1 := card_le_of_le hRQ
      rw [← hRcard, hk, j4Data.card_closure] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have hqm := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini (CFSG.pCore 11 H))
    rw [hk, hecard] at hqm
    rcases (show k ≤ 2 ∨ k = 3 by omega) with hk2 | rfl
    · have h1 : 11 ^ e ≤ 11 ^ k := Nat.le_of_dvd (by positivity) (Dvd.intro _ hqm.symm)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans
        (Nat.pow_le_pow_right (by norm_num) hk2))
    ·
      have hRQeq : (CFSG.pCore 11 H).map H.subtype = j4Q :=
        eq_of_le_of_card_ge hRQ (by rw [← hRcard, hk, j4Data.card_closure])
      have hΦ : frattini (CFSG.pCore 11 H) ≠ ⊥ := by
        rw [CFSG.RankThree.PartTwo.frattini_eq_commutator hRp hRexp]
        intro hc
        apply j4Data.not_isMulCommutative
        refine ⟨⟨fun a b => ?_⟩⟩
        have ha : (a : Sporadic.J4.J) ∈ (CFSG.pCore 11 H).map H.subtype := hRQeq ▸ a.2
        have hb : (b : Sporadic.J4.J) ∈ (CFSG.pCore 11 H).map H.subtype := hRQeq ▸ b.2
        obtain ⟨a', ha', ha'e⟩ := ha
        obtain ⟨b', hb', hb'e⟩ := hb
        have hcomm : (⟨a', ha'⟩ : CFSG.pCore 11 H) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := by
          have h1 := Subgroup.commutator_mem_commutator (mem_top (⟨a', ha'⟩ :
            CFSG.pCore 11 H)) (mem_top (⟨b', hb'⟩ : CFSG.pCore 11 H))
          rw [← _root_.commutator_def, hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1
        apply Subtype.ext
        have h2 := congrArg (fun t : CFSG.pCore 11 H => ((t : H) : Sporadic.J4.J)) hcomm
        simp only [Subgroup.coe_mul] at h2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha'e, ← hb'e]
        exact h2
      obtain ⟨m, hm⟩ := (hRp.to_subgroup (frattini (CFSG.pCore 11 H))).exists_card_eq
      have hm1 : 1 ≤ m := by
        by_contra hm0
        apply hΦ
        exact eq_bot_of_card_eq _ (by rw [hm, show m = 0 by omega, pow_zero])
      rw [hm, ← pow_add] at hqm
      have h3 := Nat.pow_right_injective (by norm_num : 2 ≤ 11) hqm
      omega
  have hUp : IsPGroup 2 ((U : Subgroup Sporadic.J4.J).subgroupOf H) :=
    U.isPGroup'.of_equiv (subgroupOfEquivOfLe hUH).symm
  have h32 := card_two_subgroup_le hsolv hprimes hD2 ⟨e, he, hecard⟩ hUp
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv, hU21] at h32
  norm_num at h32

end CFSG.Quasithin.H13.NQCat
