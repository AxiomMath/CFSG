module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.GH74.Uniqueness.Section14Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

theorem uc22p22ve_map_sylow {X Y : Type*} [Group X] [Group Y] [Finite X] {q : ℕ} [Fact q.Prime]
    (f : X →* Y) {W Q : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf q Q W)
    (hW : IsPGroup q ↥(W.map f)) : Q.map f = W.map f := by
  obtain ⟨S, rfl⟩ := hQ
  have hg : Function.Surjective (f.subgroupMap W) := f.subgroupMap_surjective W
  haveI : Finite ↥(W.map f) := Finite.of_surjective _ hg
  have hT := (S.mapSurjective hg)
  have hidx : ((S.mapSurjective hg : Sylow q ↥(W.map f)) : Subgroup ↥(W.map f)).index = 1 := by
    obtain ⟨n, hn⟩ := hW.index ((S.mapSurjective hg : Sylow q ↥(W.map f)) : Subgroup ↥(W.map f))
    rcases n with _ | n
    · simpa using hn
    · exfalso
      have h1 : q ∣ ((S.mapSurjective hg : Sylow q ↥(W.map f)) : Subgroup ↥(W.map f)).index := by
        rw [hn]
        exact dvd_pow_self q (Nat.succ_ne_zero n)
      have h2 := (S : Subgroup ↥W).index_map_dvd hg
      rw [← Sylow.coe_mapSurjective hg] at h2
      exact S.not_dvd_index (h1.trans h2)
  have htop : ((S.mapSurjective hg : Sylow q ↥(W.map f)) : Subgroup ↥(W.map f)) = ⊤ :=
    Subgroup.index_eq_one.1 hidx
  rw [Sylow.coe_mapSurjective] at htop
  have hcomp : (W.map f).subtype.comp (f.subgroupMap W) = f.comp W.subtype := by
    ext x
    rfl
  calc ((S : Subgroup ↥W).map W.subtype).map f
      = (S : Subgroup ↥W).map (f.comp W.subtype) := by rw [Subgroup.map_map]
    _ = (S : Subgroup ↥W).map ((W.map f).subtype.comp (f.subgroupMap W)) := by rw [hcomp]
    _ = ((S : Subgroup ↥W).map (f.subgroupMap W)).map (W.map f).subtype := by
      rw [Subgroup.map_map]
    _ = (⊤ : Subgroup ↥(W.map f)).map (W.map f).subtype := by rw [htop]
    _ = W.map f := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem uc22p22ve_exists_sylow_normalized_of_pGroup {X : Type*} [Group X] [Finite X] {q : ℕ}
    [Fact q.Prime] {A W : Subgroup X} (hA : IsPGroup q ↥A) (hAW : A ≤ normalizer (W : Set X)) :
    ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf q P W ∧ A ≤ normalizer (P : Set X) := by
  set K : Subgroup X := A ⊔ W with hK
  have hWK : W ≤ K := le_sup_right
  have hAK : A ≤ K := le_sup_left
  have hKN : K ≤ normalizer (W : Set X) := sup_le hAW Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  set PK : Subgroup X := (Q : Subgroup ↥K).map K.subtype with hPK
  have hSyl : CFSG.ABGLocalTools.IsSylowOf q PK K := ⟨Q, rfl⟩
  have hAPK : A ≤ PK := fun a ha =>
    Subgroup.mem_map.2 ⟨⟨a, hAK ha⟩, hQ (show (⟨a, hAK ha⟩ : ↥K) ∈ A.subgroupOf K from ha), rfl⟩
  refine ⟨PK ⊓ W, hSyl.inf_of_le_normalizer hWK hKN, fun a ha => ?_⟩
  have hPKK : PK ≤ K := hSyl.le
  exact Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hAPK ha), hKN (hPKK (hAPK ha))⟩)

variable {G : Type} [Group G] [Finite G]

private theorem uc22p22ve_mem_normalizer_commutator {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

private theorem uc22p22ve_mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  exact and_congr (hH h) (hK h)

private theorem uc22p22ve_coprime {M A W : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hAodd : Odd (Nat.card A)) (hAq : ¬ q ∣ Nat.card A)
    (hW : W ≤ barPreimage M (CFSG.pCore q (Bar2 M))) : Nat.Coprime (Nat.card A) (Nat.card W) := by
  refine Nat.coprime_of_dvd fun r hr hrA hrW => ?_
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) r hrW
  obtain ⟨hxM, hxq⟩ := uc22p21c_mem_barPreimage.1 (hW x.2)
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := q) (G := Bar2 M)) ⟨_, hxq⟩
  have hj' : uc22p21cPi M ⟨(x : G), hxM⟩ ^ (q ^ j) = 1 := congrArg Subtype.val hj
  have hker : (⟨(x : G), hxM⟩ : ↥M) ^ (q ^ j) ∈ CFSG.pCore 2 ↥M := by
    apply (QuotientGroup.eq_one_iff _).1
    show uc22p21cPi M ((⟨(x : G), hxM⟩ : ↥M) ^ (q ^ j)) = 1
    rw [map_pow]
    exact hj'
  obtain ⟨i, hi⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, hker⟩
  have hi' : ((⟨(x : G), hxM⟩ : ↥M) ^ (q ^ j)) ^ (2 ^ i) = 1 := congrArg Subtype.val hi
  have hpow : (x : G) ^ (q ^ j * 2 ^ i) = 1 := by
    have := congrArg Subtype.val hi'
    simpa [← pow_mul] using this
  have hord : r ∣ q ^ j * 2 ^ i := by
    have h1 : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
    rw [← h1]
    exact orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.Prime.dvd_mul hr).1 hord with h | h
  · exact hAq (by
      have := (Nat.prime_dvd_prime_iff_eq hr (Fact.out : q.Prime)).1 (hr.dvd_of_dvd_pow h)
      rwa [this] at hrA)
  · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
    rw [this] at hrA
    exact (Nat.not_even_iff_odd.2 hAodd) (even_iff_two_dvd.2 hrA)


private abbrev uc22p22ve_pi (M V : Subgroup G) : ↥M →* MBar M V :=
  QuotientGroup.mk' (kerAct M V).normalCore

theorem uc22p22ve_exists_lift (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D) (c : Ctx22b D Ch)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (Qb : Subgroup (MBar D.M c.V))
    (hQb : Qb ∈ F05.calQ (G := MBar D.M c.V) q)
    (A : Subgroup G) (hAM : A ≤ D.M)
    (hA : (Odd (Nat.card A) ∧ IsMulCommutative ↥A ∧ ¬ q ∣ Nat.card A) ∨ IsPGroup q ↥A) :
    ∃ Q : Subgroup G, Q ≤ D.M ∧ IsPGroup q ↥Q ∧ Q ≤ ⁅D.M, D.M⁆ ∧
      Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ∧ (barImage D.M Q).Normal ∧
      Q ⊓ centralizer (c.V : Set G) = ⊥ ∧ mbarImage D.M c.V Q = Qb ∧
      (∀ x ∈ Q, x ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧ ¬ IsCyclic ↥Q ∧ A ≤ normalizer (Q : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hNc := cTilde_bot_normal D.M c.V c.hVM
  obtain ⟨hQbn, hQbnc, hQbp, hQbexp, hQbcl, hQble⟩ := hQb
  have hhyp : F11.Hyp11 D ⊥ c.V := uc22p22c_hyp11 D (hV h1930 c).1
    (uc22p22o_not_isTI_of_hC D (uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM) c.hC)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (F11.O2p q D.M)
  have h1 := (h1110 c.V hhyp q hq hq2 P hP).1
  have hQbP : Qb ≤ mbarImage D.M c.V (P ⊓ ⁅D.M, D.M⁆) := by
    set e := mbarEquiv D.M c.V with he
    set Qb' : Subgroup (F11.MBar11 D.M ⊥ c.V) := Qb.map e.toMonoidHom with hQb'
    haveI hn : Qb'.Normal := hQbn.map _ e.surjective
    have hp : IsPGroup q ↥Qb' := hQbp.map _
    have hle : Qb' ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ c.V)), ⊤⁆ := by
      refine (Subgroup.map_mono hQble).trans ?_
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    have hcore : Qb' ≤ pCoreOf q ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ c.V)), ⊤⁆ :=
      CFSG.LieType.BorelTits.le_pCoreOf q hle inferInstance hp
    rw [h1, ← map_mbarImage] at hcore
    exact (Subgroup.map_le_map_iff_of_injective e.injective).1 hcore
  set Oq : Subgroup G := barPreimage D.M (CFSG.pCore q (Bar2 D.M)) with hOq
  set Wb : Subgroup G := (Qb.comap (uc22p22ve_pi D.M c.V)).map D.M.subtype with hWb
  set W₀ : Subgroup G := Oq ⊓ ⁅D.M, D.M⁆ ⊓ Wb with hW₀
  have mem_Wb : ∀ x : G, x ∈ Wb ↔ ∃ h : x ∈ D.M, uc22p22ve_pi D.M c.V ⟨x, h⟩ ∈ Qb := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hmemW : ∀ x : G, x ∈ W₀ ↔ x ∈ Oq ∧ x ∈ ⁅D.M, D.M⁆ ∧ x ∈ Wb := by
    intro x
    simp only [hW₀, Subgroup.mem_inf]
    tauto
  have hW₀Oq : W₀ ≤ Oq := fun x hx => ((hmemW x).1 hx).1
  have hW₀M : W₀ ≤ D.M := hW₀Oq.trans (uc22p21c_barPreimage_le _ _)
  have hOqN : D.M ≤ normalizer (Oq : Set G) :=
    uc22p22f_normalizer_barPreimage D.M (CFSG.pCore q (Bar2 D.M))
  have hcomN : D.M ≤ normalizer ((⁅D.M, D.M⁆ : Subgroup G) : Set G) := fun g hg =>
    uc22p22ve_mem_normalizer_commutator (Subgroup.le_normalizer hg)
  have hWbN : D.M ≤ normalizer (Wb : Set G) := by
    intro m hm
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨hxM, hxQ⟩ := (mem_Wb x).1 hx
    have hmem : m * x * m⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm)
    refine (mem_Wb _).2 ⟨hmem, ?_⟩
    have e : (⟨m * x * m⁻¹, hmem⟩ : ↥D.M) = ⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : ↥D.M)⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hQbn.conj_mem _ hxQ _
  have hW₀N : D.M ≤ normalizer (W₀ : Set G) := fun g hg =>
    uc22p22ve_mem_normalizer_inf (uc22p22ve_mem_normalizer_inf (hOqN hg) (hcomN hg)) (hWbN hg)
  have hW₀img : mbarImage D.M c.V W₀ = Qb := by
    ext y
    constructor
    · intro hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨h, hQm⟩ := (mem_Wb _).1 ((hmemW _).1 hm).2.2
      exact hQm
    · intro hy
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 (hQbP hy)
      refine Subgroup.mem_map.2 ⟨m, ?_, hmy⟩
      have hmP : (m : G) ∈ P ⊓ ⁅D.M, D.M⁆ := hm
      show (m : G) ∈ W₀
      refine (hmemW (m : G)).2 ⟨hP.le (Subgroup.mem_inf.1 hmP).1, (Subgroup.mem_inf.1 hmP).2,
        (mem_Wb (m : G)).2 ⟨m.2, ?_⟩⟩
      have : uc22p22ve_pi D.M c.V m = y := hmy
      rw [show (⟨(m : G), m.2⟩ : ↥D.M) = m from rfl, this]
      exact hy
  have hAN : A ≤ normalizer (W₀ : Set G) := hAM.trans hW₀N
  obtain ⟨Q, hQsyl, hAQ⟩ : ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q W₀ ∧
      A ≤ normalizer (Q : Set G) := by
    rcases hA with ⟨hAodd, hAcomm, hAq⟩ | hAp
    · haveI : Group.IsSolvable ↥A := Group.isSolvable_of_comm fun a b => hAcomm.is_comm.comm a b
      exact CFSG.GH74.Uniqueness.exists_sylow_normalized_of_coprime hAN
        (uc22p22ve_coprime hAodd hAq hW₀Oq) q
    · exact uc22p22ve_exists_sylow_normalized_of_pGroup hAp hAN
  have hQle : Q ≤ W₀ := hQsyl.le
  have hQp : IsPGroup q ↥Q := hQsyl.isPGroup
  have hQM : Q ≤ D.M := hQle.trans hW₀M
  have hsylM : CFSG.ABGLocalTools.IsSylowOf q (Q.subgroupOf D.M) (W₀.subgroupOf D.M) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff D.M, Subgroup.map_subgroupOf_eq_of_le hQM,
      Subgroup.map_subgroupOf_eq_of_le hW₀M]
    exact hQsyl
  have hmb : mbarImage D.M c.V Q = Qb := by
    have hpg : IsPGroup q ↥((W₀.subgroupOf D.M).map (uc22p22ve_pi D.M c.V)) := by
      have h : (W₀.subgroupOf D.M).map (uc22p22ve_pi D.M c.V) = Qb := hW₀img
      rw [h]
      exact hQbp
    exact (uc22p22ve_map_sylow _ hsylM hpg).trans hW₀img
  have hbi : barImage D.M Q = barImage D.M W₀ := by
    have hpg : IsPGroup q ↥((W₀.subgroupOf D.M).map (uc22p21cPi D.M)) := by
      have hle : (W₀.subgroupOf D.M).map (uc22p21cPi D.M) ≤ CFSG.pCore q (Bar2 D.M) := by
        rintro _ ⟨m, hm, rfl⟩
        exact (uc22p21c_mem_barPreimage.1 (hW₀Oq hm)).2
      exact (CFSG.pCore_isPGroup (p := q) (G := Bar2 D.M)).to_le hle
    exact uc22p22ve_map_sylow _ hsylM hpg
  have hbN : (barImage D.M Q).Normal := by
    rw [hbi]
    exact uc22p22u_barImage_normal hW₀N
  have hnc : ¬ IsCyclic ↥Q := by
    intro hcyc
    have hsurj : Function.Surjective (uc22br4_phi D.M c.V Q hQM).rangeRestrict :=
      MonoidHom.rangeRestrict_surjective _
    have hcyc' : IsCyclic ↥(uc22br4_phi D.M c.V Q hQM).range := isCyclic_of_surjective _ hsurj
    rw [uc22br4_range_phi D.M c.V Q hQM, hmb] at hcyc'
    exact hQbnc hcyc'
  obtain ⟨P', hP'syl, hQP'⟩ : ∃ P' : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q P' Oq ∧ Q ≤ P' := by
    obtain ⟨S, hS⟩ := (hQp.comap_subtype (K := Oq)).exists_le_sylow
    refine ⟨S.map Oq.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hW₀Oq (hQle hx)⟩,
      hS (show (⟨x, hW₀Oq (hQle hx)⟩ : ↥Oq) ∈ Q.subgroupOf Oq from hx), rfl⟩
  obtain ⟨E, hEQ, hEel, hEcard⟩ := uc22p22u_exists_elemAbelian_sq hq hq2 hQp hnc
  have hrk : 1 < CFSG.Open.pRank q P' :=
    lt_of_lt_of_le (by norm_num)
      (CFSG.SectionRank.le_pRank hq.one_lt (hEQ.trans hQP') hEel hEcard)
  have hbot : P' ⊓ centralizer (c.V : Set G) = ⊥ := h10 h1930 c q hq hq2 P' hP'syl hrk
  have hQV : Q ⊓ centralizer (c.V : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ P' ⊓ centralizer (c.V : Set G) :=
      Subgroup.mem_inf.2 ⟨hQP' (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hbot] at hx'
    exact hx'
  have hker : (uc22br4_phi D.M c.V Q hQM).ker = ⊥ := by
    rw [uc22br4_ker_phi D.M c.V Q c.hVM hQM, eq_bot_iff]
    intro x hx
    have hx1 : (x : G) ∈ Q ⊓ centralizer (c.V : Set G) := Subgroup.mem_inf.2 ⟨x.2, hx⟩
    rw [hQV] at hx1
    exact Subtype.ext (Subgroup.mem_bot.1 hx1)
  have hinj : Function.Injective (uc22br4_phi D.M c.V Q hQM) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hexp : ∀ x ∈ Q, x ^ q = 1 := by
    intro x hx
    have hmem : uc22br4_phi D.M c.V Q hQM ⟨x, hx⟩ ∈ Qb := by
      rw [← hmb, ← uc22br4_range_phi D.M c.V Q hQM]
      exact ⟨⟨x, hx⟩, rfl⟩
    have h1 : uc22br4_phi D.M c.V Q hQM (⟨x, hx⟩ ^ q) = 1 := by
      rw [map_pow]
      exact hQbexp _ hmem
    have h2 : (⟨x, hx⟩ : ↥Q) ^ q = 1 := hinj (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hclass : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := by
    set T : Subgroup ↥Q := ⊤ with hT
    have hQtop : T.map Q.subtype = Q := by
      rw [hT, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h1 : (⁅⁅T, T⁆, T⁆ : Subgroup ↥Q).map (uc22br4_phi D.M c.V Q hQM) = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hT, ← MonoidHom.range_eq_map,
        uc22br4_range_phi D.M c.V Q hQM, hmb]
      exact hQbcl
    have h2 : (⁅⁅T, T⁆, T⁆ : Subgroup ↥Q) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx1 : uc22br4_phi D.M c.V Q hQM x ∈
          (⁅⁅T, T⁆, T⁆ : Subgroup ↥Q).map (uc22br4_phi D.M c.V Q hQM) :=
        Subgroup.mem_map_of_mem _ hx
      rw [h1, Subgroup.mem_bot] at hx1
      exact Subgroup.mem_bot.2 (hinj (by rw [hx1, map_one]))
    calc ⁅⁅Q, Q⁆, Q⁆ = ⁅⁅T.map Q.subtype, T.map Q.subtype⁆, T.map Q.subtype⁆ := by rw [hQtop]
      _ = (⁅⁅T, T⁆, T⁆ : Subgroup ↥Q).map Q.subtype := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator]
      _ = ⊥ := by rw [h2, Subgroup.map_bot]
  exact ⟨Q, hQM, hQp, fun x hx => ((hmemW x).1 (hQle hx)).2.1, fun x hx => hW₀Oq (hQle hx), hbN,
    hQV, hmb, hexp, hclass, hnc, hAQ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
