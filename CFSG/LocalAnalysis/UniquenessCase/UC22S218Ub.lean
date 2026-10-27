module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ua
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.ClassicalGroups.Symplectic.Sp4LagrangianParabolic
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutPsp4
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.Quasithin.Vol2.KGFactInspOutDer
import CFSG.RankThree.PartOne.S11c.PlaneLift
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (projUnipotent proj)
open CFSG.Quasithin.H13.L32A.C.SkPf (sp4T sp4T_range_le isSylowTwoOf_sylow)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_fix_iff)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uc22s218u_model {r : ℕ} (hr : r.Prime) (hrK : r ∣ Nat.card K - 1) :
    ∃ x ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K))), orderOf x = r ∧
      ∃ Y : Subgroup (StatedProj (StatedSp 2 K)),
        Y ≤ centralizer ((zpowers x : Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) ∧
          Nonempty (↥Y ≃* SL(2, K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rw [Nat.card_units]; exact hrK)
  let lam0 : SL(2, K) →* StatedProj (StatedSp 2 K) :=
    (proj 2 K).comp (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam (0 : Fin 2))
  refine ⟨sp4T K (Pi.mulSingle 1 β), sp4T_range_le ⟨_, rfl⟩, ?_, lam0.range, ?_,
    ⟨(MonoidHom.ofInjective (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.proj_lam_injective (F := K) 0)).symm⟩⟩
  · rw [orderOf_injective (sp4T K) uc22p218c_sp4T_injective, orderOf_piMulSingle, hβ]
  · rintro _ ⟨g, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have hc : Commute (sp4T K (Pi.mulSingle 1 β)) (lam0 g) :=
      ((CFSG.ClassicalGroups.Symplectic.Sp4.commute_lam_torusHom_mulSingle (i := 0) (j := 1) (by decide) g
        β).map (proj 2 K)).symm
    exact (hc.zpow_left k).eq

end Model

section Abstract

variable {X : Type} [Group X]

theorem uc22s218u_exists_sp4 {n r : ℕ} (hX : IsSp4 X n) (hn : 2 ≤ n) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) :
    ∃ x ∈ normalizer (U : Set X), orderOf x = r ∧ ∃ Y : Subgroup X,
      Y ≤ centralizer ((zpowers x : Subgroup X) : Set X) ∧ IsL2 ↥Y n ∧
        Nat.card Y = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨φ, rfl⟩ := uc22p218c_exists_mulEquiv_map e hU
  obtain ⟨x, hx, hxo, Y, hY, ⟨f⟩⟩ := uc22s218u_model (K := K) hr (by rw [hK]; exact hrn)
  refine ⟨φ x, ?_, by rw [MulEquiv.orderOf_eq, hxo], Y.map φ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map]
    exact mem_map_of_mem _ hx
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have h1 := congrArg φ (mem_centralizer_iff.1 (hY hy) (x ^ k) (zpow_mem (mem_zpowers x) k))
    rw [map_mul, map_mul, map_zpow] at h1
    exact h1
  · haveI := Fintype.ofFinite K
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
      ((Y.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans f)
  · rw [card_map_of_injective (f := φ.toMonoidHom) φ.injective, Nat.card_congr f.toEquiv,
      CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2, hK]

end Abstract

section Group

variable {G : Type} [Group G] [Finite G]

theorem uc22s218u_exists_lift {L : Subgroup G} {n r : ℕ} (hX : IsSp4 (Bar2 L) n) (hn : 2 ≤ n) (Q : Sylow 2 ↥L)
    (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) :
    ∃ x ∈ L, x ∈ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) ∧ orderOf x = r ∧
      PartTwo.S19.HasL2SzSection n (L ⊓ centralizer ((zpowers x : Subgroup G) : Set G)) ∧
      ∀ q : ℕ, q.Prime → q ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) →
        ∃ z ∈ L ⊓ centralizer ((zpowers x : Subgroup G) : Set G), orderOf z = q := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrn
  have hSb : IsSylowTwoOf ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) ⊤ :=
    isSylowTwoOf_sylow (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  obtain ⟨xb, hxbN, hxb, Yb, hYb, hL2, hYc⟩ := uc22s218u_exists_sp4 hX hn hSb hr hrn
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) xb
  have hx₀ : x₀ ^ r ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow, ← hxb]
    exact pow_orderOf_eq_one _
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hx₀⟩
  have hc' : (x₀ ^ r) ^ 2 ^ c = 1 := congrArg Subtype.val hc
  have hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x₀)).Coprime (2 ^ c) := by
    rw [hxb]
    exact (Nat.coprime_two_right.2 (hr.odd_of_ne_two hr2)).pow_right c
  have hmk : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (x₀ ^ 2 ^ c)) = r := by
    rw [map_pow, hcop.orderOf_pow, hxb]
  have hord : orderOf (x₀ ^ 2 ^ c) = r := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
    · rw [← pow_mul, mul_comm (2 ^ c), pow_mul, hc']
    · rw [← hmk]
      exact orderOf_map_dvd _ _
  set x' : ↥L := x₀ ^ 2 ^ c with hx'
  have hx'N : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x' ∈ normalizer
      (((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    rw [hx', map_pow]
    exact pow_mem hxbN _
  have hkey : ∀ g : ↥L, QuotientGroup.mk' (CFSG.pCore 2 ↥L) g ∈ normalizer
      (((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L)) →
      ∀ h ∈ (Q : Subgroup ↥L).map L.subtype, (g : G) * h * (g : G)⁻¹ ∈ (Q : Subgroup ↥L).map L.subtype := by
    intro g hg h hh
    obtain ⟨q, hq, rfl⟩ := mem_map.1 hh
    have h1 : (QuotientGroup.mk (g * q * g⁻¹) : Bar2 L) ∈
        (Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact (mem_normalizer_iff.1 hg _).1 (mem_map_of_mem _ hq)
    exact uc22p218d_mem_of_mk_mem Q h1
  have hxN : (x' : G) ∈ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hkey x' hx'N h, fun hh => ?_⟩
    have h1 := hkey x'⁻¹ (by rw [map_inv]; exact inv_mem hx'N) _ hh
    have e : ((x'⁻¹ : ↥L) : G) * ((x' : G) * h * (x' : G)⁻¹) * ((x'⁻¹ : ↥L) : G)⁻¹ = h := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h1
  have hNr : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hx'p : IsPGroup r (zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hYC : Yb ≤ (centralizer ((zpowers x' : Subgroup ↥L) : Set ↥L)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [← CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hNr hx'p, MonoidHom.map_zpowers]
    refine hYb.trans (centralizer_le ?_)
    rw [SetLike.coe_subset_coe, zpowers_le, hx', map_pow]
    exact pow_mem (mem_zpowers _) _
  set C' : Subgroup ↥L := centralizer ((zpowers x' : Subgroup ↥L) : Set ↥L) ⊓
    Yb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hC'
  let f : ↥C' →* ↥Yb := ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp C'.subtype).codRestrict Yb
    fun c => (mem_inf.1 c.2).2
  have hf : Function.Surjective f := by
    rintro ⟨yb, hyb⟩
    obtain ⟨c, hcC, hce⟩ := mem_map.1 (hYC hyb)
    exact ⟨⟨c, mem_inf.2 ⟨hcC, by rw [mem_comap, hce]; exact hyb⟩⟩, Subtype.ext hce⟩
  have hsec : PartTwo.S19.HasL2SzSection n (L ⊓ centralizer ((zpowers (x' : G) : Subgroup G) : Set G)) := by
    refine PartTwo.S19.hasL2SzSection_of_surjective (Y := C'.map L.subtype) ?_ (Or.inl hL2)
      (f.comp (C'.equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom)
      (hf.comp (C'.equivMapOfInjective L.subtype L.subtype_injective).symm.surjective)
    rintro _ ⟨c, hc, rfl⟩
    refine mem_inf.2 ⟨c.2, mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have h1 := congrArg Subtype.val
      (mem_centralizer_iff.1 (mem_inf.1 hc).1 (x' ^ k) (zpow_mem (mem_zpowers x') k))
    simpa using h1
  refine ⟨(x' : G), x'.2, hxN, by rw [Subgroup.orderOf_coe, hord], hsec, fun q hq hqd => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨zb, hzb⟩ := exists_prime_orderOf_dvd_card' (G := ↥Yb) q (by rw [hYc]; exact hqd)
  obtain ⟨z₀, hz₀C, hz₀e⟩ := mem_map.1 (hYC zb.2)
  have h1 : q ∣ orderOf z₀ := by
    rw [← hzb, ← Subgroup.orderOf_coe zb, ← hz₀e]
    exact orderOf_map_dvd _ _
  refine ⟨((z₀ ^ (orderOf z₀ / q) : ↥L) : G), mem_inf.2 ⟨(z₀ ^ (orderOf z₀ / q)).2,
    mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have h2 : Commute (x' ^ k) z₀ := mem_centralizer_iff.1 hz₀C (x' ^ k) (zpow_mem (mem_zpowers x') k)
    have h3 := congrArg Subtype.val (h2.pow_right (orderOf z₀ / q)).eq
    simpa using h3
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos z₀).ne' h1

theorem uc22s218u_exists_trivial_action (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hML : D.M ≤ normalizer (L : Set G)) {n p : ℕ} (hX : IsSp4 (Bar2 L) n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M) (h3 : 3 ≤ CFSG.Open.pRank p D.M) :
    ∃ y ∈ D.M, orderOf y = p ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : ↥D.M →* MulAut (Bar2 L) := (rhoL L).comp (inclusion hML) with hρ
  set ψ : ↥D.M →* Outer (Bar2 L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp ρ with hψ
  have hcomm : ∀ a b : Outer (Bar2 L), a * b = b * a := by
    haveI := CFSG.Quasithin.H13.KGInsp4316.outer_cyclic_psp4
      (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    letI : CommGroup (Outer (Bar2 L)) := IsCyclic.commGroup
    exact mul_comm
  have hψp : ¬ p ∣ Nat.card ψ.range := by
    intro hdvd
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.range) p hdvd
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨m', hm'T, hm'⟩ := uc22s218u_exists_normalizer_of_comm D.sylowM ψ hcomm m
    have h1 : p ∣ orderOf (m' : G) := by
      rw [Subgroup.orderOf_coe, ← ha, ← Subgroup.orderOf_coe a, ← hm, ← hm']
      exact orderOf_map_dvd ψ m'
    have hyo : orderOf ((m' : G) ^ (orderOf (m' : G) / p)) = p := orderOf_pow_orderOf_div (orderOf_pos _).ne' h1
    have hy1 : zpowers ((m' : G) ^ (orderOf (m' : G) / p)) ≠ ⊥ := by
      intro h
      rw [zpowers_eq_bot.1 h, orderOf_one] at hyo
      exact hp.one_lt.ne hyo
    exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hp hp2 hyo
      (uc22p22r_mem_uniqueSet_of_sp D hp hsp (zpowers_le.2 (pow_mem m'.2 _))
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])) hy1)
      (zpowers_le.2 (pow_mem hm'T _))
  by_contra hno
  push Not at hno
  obtain ⟨E, hEM, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h3
  set ρE : ↥E →* MulAut (Bar2 L) := ρ.comp (inclusion hEM) with hρE
  have hEp : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (by rw [Subgroup.coe_pow]; exact hEel.2 e e.2)
  have hρEi : Function.Injective ρE := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra he1
    have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
    obtain ⟨l, hl, hl'⟩ := hno e (hEM e.2) (orderOf_eq_prime (hEel.2 e e.2) he1')
    apply hl'
    have h0 : rhoL L (inclusion hML (inclusion hEM e)) = 1 := he
    have h1 : rhoL L (inclusion hML (inclusion hEM e)) (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h0]
      rfl
    exact (rhoL_fix_iff L _ ⟨l, hl⟩).1 h1
  have hρEr : ∀ e, ρE e ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    intro e
    have h1 : ψ (inclusion hEM e) = 1 := by
      have h2 : orderOf (ψ (inclusion hEM e)) ∣ p := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, ← map_pow, hEp e, map_one, map_one]
      rcases (Nat.dvd_prime hp).1 h2 with h | h
      · exact orderOf_eq_one_iff.1 h
      · exfalso
        apply hψp
        have h4 := orderOf_dvd_natCard (⟨ψ (inclusion hEM e), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ↥ψ.range)
        rwa [Subgroup.orderOf_mk, h] at h4
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hι := CFSG.RankThree.PartOne.conj_injective_of_center_bot (uc22p218d_center_eq_bot_sp4 hX)
  let f : ↥E →* Bar2 L := (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
    (ρE.codRestrict (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) hρEr)
  have hf : Function.Injective f := (MonoidHom.ofInjective hι).symm.injective.comp
    fun a b h => hρEi (congrArg Subtype.val h)
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) :=
    CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => hEel.1.is_comm.comm a b) hEp hEc f hf le_top
  have h2 := uc22p218d_pRank_le_two_sp4 hX hp hp2
  omega

end Group

end CFSG.LocalAnalysis.UniquenessCase.UC22
