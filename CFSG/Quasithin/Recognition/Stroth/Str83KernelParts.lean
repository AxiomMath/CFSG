module

public import CFSG.Quasithin.Recognition.Stroth.Str83Props
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Background.RonanF13Core
public import CFSG.Quasithin.Recognition.St84.Gen.S3Slice
public import CFSG.Quasithin.Background.RonanF13Listed
public import CFSG.GH74.Uniqueness.Bender.SuzukiAut
public import CFSG.Quasithin.Background.RonanF13SetupOf
public import CFSG.Quasithin.Recognition.Stroth.BenderFrame
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.WeissStrothLeaves

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open Subgroup

private theorem mem_normalCore_iff {G : Type} [Group G] {H : Subgroup G} {x : G} :
    x ∈ H.normalCore ↔ ∀ g : G, g * x * g⁻¹ ∈ H := Iff.rfl

private theorem borelOf_le_bigB_left {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    borelOf L1 S ≤ bigB L1 L2 S := by
  unfold bigB
  exact le_sup_left.trans le_sup_left

private theorem borelOf_le_bigB_right {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    borelOf L2 S ≤ bigB L1 L2 S := by
  unfold bigB
  exact le_sup_right.trans le_sup_left

private theorem pCoreOf_le_bigB_left {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) : pCoreOf 2 L1 ≤ bigB L1 L2 S :=
  ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.h1.sylow).trans inf_le_left).trans
    (le_sup_right : S ≤ bigB L1 L2 S)

private theorem pCoreOf_le_bigB_right {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) : pCoreOf 2 L2 ≤ bigB L1 L2 S :=
  ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.h2.sylow).trans inf_le_left).trans
    (le_sup_right : S ≤ bigB L1 L2 S)

theorem f112_mem_K1_of_commutator_mem
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) {x : G} (hx : x ∈ bigB L1 L2 S)
    (hc : ∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    (⟨x, le_sup_right (a := L1) hx⟩ : ↥(L1 ⊔ bigB L1 L2 S)) ∈ f112K1 L1 L2 S := by
  classical
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF
  have hpcB : pCoreOf 2 L1 ≤ bigB L1 L2 S := pCoreOf_le_bigB_left hF
  have hinf : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
    (prop_F19_of_listed rankOneListedFacts hF).1
  have hstep : ∀ l ∈ L1, l⁻¹ * x * l ∈ bigB L1 L2 S := by
    intro l hl
    have h1 : l⁻¹ * x * l * x⁻¹ ∈ pCoreOf 2 L1 := by
      have h2 : x * l⁻¹ * x⁻¹ * l ∈ pCoreOf 2 L1 := by
        simpa using hc l⁻¹ (L1.inv_mem hl)
      have h3 := (pCoreOf 2 L1).inv_mem h2
      rwa [show (x * l⁻¹ * x⁻¹ * l)⁻¹ = l⁻¹ * x * l * x⁻¹ from by group] at h3
    have heq : l⁻¹ * x * l = (l⁻¹ * x * l * x⁻¹) * x := by group
    rw [heq]
    exact Subgroup.mul_mem _ (hpcB h1) hx
  unfold f112K1
  rw [hinf]
  refine mem_normalCore_iff.mpr ?_
  intro g
  obtain ⟨l, hl, b, hb, hgl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp (g⁻¹).2
  have hg : (g : G) = (l * b)⁻¹ := by rw [← hgl]; simp
  have hcoe : ((g * ⟨x, le_sup_right (a := L1) hx⟩ * g⁻¹ :
      ↥(L1 ⊔ bigB L1 L2 S)) : G) = (g : G) * x * (g : G)⁻¹ := by simp
  have hconj : ((g * ⟨x, le_sup_right (a := L1) hx⟩ * g⁻¹ :
      ↥(L1 ⊔ bigB L1 L2 S)) : G) = b⁻¹ * (l⁻¹ * x * l) * b := by
    rw [hcoe, hg]
    group
  rw [Subgroup.mem_subgroupOf, hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((bigB L1 L2 S).inv_mem hb) (hstep l hl)) hb

theorem f112_mem_K2_of_commutator_mem
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) {x : G} (hx : x ∈ bigB L1 L2 S)
    (hc : ∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) :
    (⟨x, le_sup_right (a := L2) hx⟩ : ↥(L2 ⊔ bigB L1 L2 S)) ∈ f112K2 L1 L2 S := by
  classical
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 hF.symm
    rwa [bigB_comm L1 L2 S] at h
  have hpcB : pCoreOf 2 L2 ≤ bigB L1 L2 S := pCoreOf_le_bigB_right hF
  have hinf : (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
    rw [inf_comm]
    exact (prop_F19_of_listed rankOneListedFacts hF).1
  have hstep : ∀ l ∈ L2, l⁻¹ * x * l ∈ bigB L1 L2 S := by
    intro l hl
    have h1 : l⁻¹ * x * l * x⁻¹ ∈ pCoreOf 2 L2 := by
      have h2 : x * l⁻¹ * x⁻¹ * l ∈ pCoreOf 2 L2 := by
        simpa using hc l⁻¹ (L2.inv_mem hl)
      have h3 := (pCoreOf 2 L2).inv_mem h2
      rwa [show (x * l⁻¹ * x⁻¹ * l)⁻¹ = l⁻¹ * x * l * x⁻¹ from by group] at h3
    have heq : l⁻¹ * x * l = (l⁻¹ * x * l * x⁻¹) * x := by group
    rw [heq]
    exact Subgroup.mul_mem _ (hpcB h1) hx
  unfold f112K2
  rw [hinf]
  refine mem_normalCore_iff.mpr ?_
  intro g
  obtain ⟨l, hl, b, hb, hgl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp (g⁻¹).2
  have hg : (g : G) = (l * b)⁻¹ := by rw [← hgl]; simp
  have hcoe : ((g * ⟨x, le_sup_right (a := L2) hx⟩ * g⁻¹ :
      ↥(L2 ⊔ bigB L1 L2 S)) : G) = (g : G) * x * (g : G)⁻¹ := by simp
  have hconj : ((g * ⟨x, le_sup_right (a := L2) hx⟩ * g⁻¹ :
      ↥(L2 ⊔ bigB L1 L2 S)) : G) = b⁻¹ * (l⁻¹ * x * l) * b := by
    rw [hcoe, hg]
    group
  rw [Subgroup.mem_subgroupOf, hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((bigB L1 L2 S).inv_mem hb) (hstep l hl)) hb

private theorem exists_conj_cartan_of_complement {K : Type} [Group K] [Finite K]
    {q i e : ℕ} {Q : Subgroup K} {t : K} (hc : BenderCore q i e Q t)
    (hQ2 : IsPGroup 2 Q) {D : Subgroup K} (hD : D ≤ GH74.Uniqueness.Bender.borel Q)
    (hDodd : Odd (Nat.card D)) (hQD : Q ⊔ D = GH74.Uniqueness.Bender.borel Q) :
    ∃ g ∈ Q, D = (cartan Q t).map (MulAut.conj g).toMonoidHom := by
  classical
  let N : Subgroup K := GH74.Uniqueness.Bender.borel Q
  have hQle : Q ≤ N := le_borel Q
  letI : (Q.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hQinf : Q ⊓ D = ⊥ := CFSG.Quasithin.RonanF13.inf_eq_bot_of_odd hQ2 hDodd
  have hDle : cartan Q t ≤ N := cartan_le_borel Q t
  have hcompD : (Q.subgroupOf N).IsComplement' (D.subgroupOf N) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxQ, hxD⟩
        apply Subtype.ext
        have hx : (x : K) ∈ Q ⊓ D := ⟨hxQ, hxD⟩
        rwa [hQinf, Subgroup.mem_bot] at hx
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(Q.subgroupOf N).one_mem, (D.subgroupOf N).one_mem⟩
    · have hsup : Q.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQle hD, hQD, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (Q.subgroupOf N) (D.subgroupOf N), hsup]
      rfl
  have hcompC : (Q.subgroupOf N).IsComplement' ((cartan Q t).subgroupOf N) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxQ, hxC⟩
        apply Subtype.ext
        have hx : (x : K) ∈ Q ⊓ cartan Q t := ⟨hxQ, hxC⟩
        rwa [hc.inf_eq, Subgroup.mem_bot] at hx
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(Q.subgroupOf N).one_mem, ((cartan Q t).subgroupOf N).one_mem⟩
    · have hsup : Q.subgroupOf N ⊔ (cartan Q t).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQle hDle, hc.sup_eq, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (Q.subgroupOf N) ((cartan Q t).subgroupOf N), hsup]
      rfl
  have hcop : Nat.Coprime (Nat.card (Q.subgroupOf N)) (Q.subgroupOf N).index := by
    rw [hcompD.symm.index_eq_card]
    have hcardD : Nat.card (D.subgroupOf N) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
    rw [hcardD]
    have hcardQ : Nat.card (Q.subgroupOf N) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
    obtain ⟨m, hm⟩ := hQ2.exists_card_eq
    rw [hcardQ, hm]
    exact (Nat.coprime_two_left.mpr hDodd).pow_left m
  obtain ⟨u, hu⟩ :=
    CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      (Q.subgroupOf N) ((cartan Q t).subgroupOf N) (D.subgroupOf N)
      (Subgroup.normal_in_normalizer) hcompC hcompD hcop
  refine ⟨((u : N) : K), u.2, ?_⟩
  have huK := congrArg (fun X : Subgroup N => X.map N.subtype) hu
  rw [Subgroup.map_subgroupOf_eq_of_le hD, Subgroup.map_map] at huK
  have hcomp : (N.subtype.comp (MulAut.conj (u : N)).toMonoidHom) =
      ((MulAut.conj (((u : N) : K))).toMonoidHom.comp N.subtype) := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hDle] at huK
  exact huK

theorem exists_involution_cartan_eq {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (Q : Sylow 2 K) {D : Subgroup K}
    (hD : D ≤ GH74.Uniqueness.Bender.borel (Q : Subgroup K))
    (hDodd : Odd (Nat.card D))
    (hQD : (Q : Subgroup K) ⊔ D = GH74.Uniqueness.Bender.borel (Q : Subgroup K)) :
    ∃ t : K, t * t = 1 ∧ t ∉ GH74.Uniqueness.Bender.borel (Q : Subgroup K) ∧
      cartan (Q : Subgroup K) t = D := by
  classical
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨g, hg, hDg⟩ := exists_conj_cartan_of_complement hc Q.isPGroup' hD hDodd hQD
  have hgN : g ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := Subgroup.le_normalizer hg
  have hQmap : (Q : Subgroup K).map (MulAut.conj g).toMonoidHom = (Q : Subgroup K) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hbmap : (GH74.Uniqueness.Bender.borel (Q : Subgroup K)).map
      (MulAut.conj g).toMonoidHom = GH74.Uniqueness.Bender.borel (Q : Subgroup K) := by
    rw [GH74.Uniqueness.Bender.borel, Subgroup.map_equiv_normalizer_eq, hQmap]
  refine ⟨g * t₀ * g⁻¹, ?_, ?_, ?_⟩
  · calc (g * t₀ * g⁻¹) * (g * t₀ * g⁻¹) = g * (t₀ * t₀) * g⁻¹ := by group
      _ = 1 := by rw [hc.sq_eq_one]; group
  · intro hmem
    apply hc.not_mem
    have hmem' : (MulAut.conj g⁻¹) (g * t₀ * g⁻¹) ∈
        (GH74.Uniqueness.Bender.borel (Q : Subgroup K)).map
          (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hmem
    have hQmap' : (Q : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom = (Q : Subgroup K) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer _).inv_mem hgN)
    have hbmap' : (GH74.Uniqueness.Bender.borel (Q : Subgroup K)).map
        (MulAut.conj g⁻¹).toMonoidHom = GH74.Uniqueness.Bender.borel (Q : Subgroup K) := by
      rw [GH74.Uniqueness.Bender.borel, Subgroup.map_equiv_normalizer_eq, hQmap']
    rw [hbmap'] at hmem'
    simpa [MulAut.conj_apply, mul_assoc] using hmem'
  · calc cartan (Q : Subgroup K) (g * t₀ * g⁻¹)
        = cartan ((Q : Subgroup K).map (MulAut.conj g).toMonoidHom)
            ((MulAut.conj g) t₀) := by rw [hQmap]; rfl
      _ = (cartan (Q : Subgroup K) t₀).map (MulAut.conj g).toMonoidHom := cartan_map _ _ _
      _ = D := hDg.symm

private theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  refine ⟨2 ^ m - 1, ?_⟩
  have hpos : 0 < 2 ^ m := by positivity
  rw [pow_succ]
  omega

private theorem card_eq_one_of_isPGroup_two_of_odd {H : Type} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (hodd : Odd (Nat.card H)) : Nat.card H = 1 := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hk0 : k = 0 := by
    rcases k with _ | m
    · rfl
    · exfalso
      have heven : Even (2 ^ (m + 1)) := ⟨2 ^ m, by rw [pow_succ]; omega⟩
      exact (Nat.not_even_iff_odd.mpr (hk ▸ hodd)) heven
  rw [hk, hk0]
  simp

private theorem exists_sylow_image
    {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ (Q : Sylow 2 (oTwoQuot ↥L)) (hQ : (Q : Subgroup (oTwoQuot ↥L)) =
      ((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))),
      ((borelOf L S).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) =
        GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L)) := by
  obtain ⟨hpg, hodd, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  exact ⟨hpg.toSylow hodd, IsPGroup.toSylow_coe hpg hodd, hmap⟩

private theorem not_isPGroup_borelOf_of_l2
    {G : Type} [Group G] [Finite G] {L S : Subgroup G} {f : ℕ}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hf : 2 ≤ f) (hL2 : IsL2Quot f (oTwoQuot ↥L)) :
    ¬ IsPGroup 2 ↥(borelOf L S) := by
  intro hB2
  obtain ⟨e⟩ := hL2
  have hBt : BenderType (oTwoQuot ↥L) f 1 1 := BenderType.linear f hf e
  obtain ⟨Q, hQ, himg⟩ := exists_sylow_image hsyl
  obtain ⟨t, hc⟩ := hBt.exists_benderCore Q
  have hsub2 : IsPGroup 2 ↥((borelOf L S).subgroupOf L) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe (F1.borelOf_le L S)).symm
  have hcart2 : IsPGroup 2 ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t) := by
    refine (hsub2.map (QuotientGroup.mk' (pCore 2 ↥L))).to_le ?_
    rw [himg]
    exact cartan_le_borel Q t
  have hodd : Odd (Nat.card ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t)) := by
    rw [hc.card_cartan, mul_one]
    exact odd_two_pow_sub_one (by omega)
  have h1 := card_eq_one_of_isPGroup_two_of_odd hcart2 hodd
  rw [hc.card_cartan, mul_one] at h1
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

private theorem not_isPGroup_borelOf_of_sz
    {G : Type} [Group G] [Finite G] {L S : Subgroup G} {a : ℕ}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) :
    ¬ IsPGroup 2 ↥(borelOf L S) := by
  intro hB2
  obtain ⟨e⟩ := hSz
  have hBt : BenderType (oTwoQuot ↥L) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  obtain ⟨Q, hQ, himg⟩ := exists_sylow_image hsyl
  obtain ⟨t, hc⟩ := hBt.exists_benderCore Q
  have hsub2 : IsPGroup 2 ↥((borelOf L S).subgroupOf L) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe (F1.borelOf_le L S)).symm
  have hcart2 : IsPGroup 2 ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t) := by
    refine (hsub2.map (QuotientGroup.mk' (pCore 2 ↥L))).to_le ?_
    rw [himg]
    exact cartan_le_borel Q t
  have hodd : Odd (Nat.card ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t)) := by
    rw [hc.card_cartan, mul_one]
    exact odd_two_pow_sub_one (by omega)
  have h1 := card_eq_one_of_isPGroup_two_of_odd hcart2 hodd
  rw [hc.card_cartan, mul_one] at h1
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem oTwoQuotConj_eq_conj_mk {G : Type} [Group G] {L : Subgroup G}
    (x : ↥L) (hxN : (x : G) ∈ Subgroup.normalizer (L : Set G)) :
    oTwoQuotConj L ⟨(x : G), hxN⟩ = MulAut.conj (QuotientGroup.mk x) := by
  apply MulEquiv.ext
  intro k
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
  rw [oTwoQuotConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1

theorem exists_commutator_lift
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) (hR : Hyp111R L1 L2 S)
    {D1 D2 : Subgroup G} (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hB1D : borelOf L1 S = (S ⊓ L1) ⊔ D1)
    (hD2leB : D2 ≤ bigB L1 L2 S)
    (hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x)
    {n i e : ℕ} (hBt : BenderType (oTwoQuot ↥L1) n i e)
    (hNF : ∀ (Q : Sylow 2 (oTwoQuot ↥L1)) (t : oTwoQuot ↥L1), t * t = 1 →
      t ∉ GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L1)) →
      ∀ σ : MulAut (oTwoQuot ↥L1),
        (∀ x ∈ (Q : Subgroup (oTwoQuot ↥L1)), σ x ∈ (Q : Subgroup (oTwoQuot ↥L1))) →
        (∀ x ∈ cartan (Q : Subgroup (oTwoQuot ↥L1)) t, σ x = x) →
        ∃ d₀ ∈ cartan (Q : Subgroup (oTwoQuot ↥L1)) t,
          ∀ k, σ k = d₀ * k * d₀⁻¹)
    {d : G} (hd : d ∈ D2) :
    ∃ δ ∈ D1, ∀ l ∈ L1, (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 := by
  classical
  let π : ↥L1 →* oTwoQuot ↥L1 := QuotientGroup.mk' (pCore 2 ↥L1)
  obtain ⟨hTpg, hTodd, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hF.h1.sylow
  let T : Subgroup (oTwoQuot ↥L1) := ((S ⊓ L1).subgroupOf L1).map π
  let Q : Sylow 2 (oTwoQuot ↥L1) := hTpg.toSylow hTodd
  have hQ : (Q : Subgroup (oTwoQuot ↥L1)) = T := IsPGroup.toSylow_coe hTpg hTodd
  let D1b : Subgroup (oTwoQuot ↥L1) := (D1.subgroupOf L1).map π
  have hD1leL1 : D1 ≤ L1 := hD1.1.trans (F1.borelOf_le L1 S)
  have hD1bodd : Odd (Nat.card ↥D1b) := by
    have hle : Nat.card ↥D1b ∣ Nat.card ↥D1 := by
      have h1 : Nat.card ↥(D1.subgroupOf L1) = Nat.card ↥D1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD1leL1).toEquiv
      rw [show D1b = (D1.subgroupOf L1).map π from rfl, ← h1]
      exact Subgroup.card_map_dvd _ π
    exact Odd.of_dvd_nat hD1.2.1 hle
  have hD1bsup : (Q : Subgroup (oTwoQuot ↥L1)) ⊔ D1b =
      GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L1)) := by
    have hmap_sup : T ⊔ D1b = (((S ⊓ L1).subgroupOf L1) ⊔ (D1.subgroupOf L1)).map π := by
      rw [Subgroup.map_sup]
    rw [hQ, hmap_sup,
      ← Subgroup.subgroupOf_sup (B := L1) (inf_le_right : S ⊓ L1 ≤ L1) hD1leL1, ← hB1D]
    exact hmap
  have hD1ble : D1b ≤ GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L1)) := by
    rw [← hD1bsup]
    exact le_sup_right
  obtain ⟨t, ht2, htQ, hcart⟩ := exists_involution_cartan_eq hBt Q hD1ble hD1bodd hD1bsup
  have hdN : d ∈ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1 (hD2leB hd)
  let σ : MulAut (oTwoQuot ↥L1) := oTwoQuotConj L1 ⟨d, hdN⟩
  have hσQ : ∀ x ∈ (Q : Subgroup (oTwoQuot ↥L1)), σ x ∈ (Q : Subgroup (oTwoQuot ↥L1)) := by
    intro x hx
    rw [hQ] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hsS : (s : G) ∈ S ⊓ L1 := Subgroup.mem_subgroupOf.mp hs
    have hds : d * (s : G) * d⁻¹ ∈ S ⊓ L1 :=
      (Subgroup.mem_normalizer_iff.mp ((F1.bigB_le_normalizer_sylow hR).1 (hD2leB hd))
        (s : G)).mp hsS
    have hval : σ (π s) = π ⟨d * (s : G) * d⁻¹, hds.2⟩ :=
      oTwoQuotConj_mk L1 ⟨d, hdN⟩ s
    rw [hval]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hds)
  have hσD : ∀ x ∈ cartan (Q : Subgroup (oTwoQuot ↥L1)) t, σ x = x := by
    intro x hx
    rw [hcart] at hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hsD1 : (s : G) ∈ D1 := Subgroup.mem_subgroupOf.mp hs
    have hsL1 : (s : G) ∈ L1 := hD1leL1 hsD1
    have hdsL1 : d * (s : G) * d⁻¹ ∈ L1 :=
      (Subgroup.mem_normalizer_iff.mp hdN (s : G)).mp hsL1
    have hcommd : d * (s : G) * d⁻¹ = (s : G) := by
      have h1 := hcomm (s : G) hsD1 d hd
      calc d * (s : G) * d⁻¹ = d * (d⁻¹ * (s : G)) := by rw [← h1]; group
        _ = (s : G) := by group
    have hval : σ (π s) = π ⟨d * (s : G) * d⁻¹, hdsL1⟩ := oTwoQuotConj_mk L1 ⟨d, hdN⟩ s
    rw [hval]
    rw [show (⟨d * (s : G) * d⁻¹, hdsL1⟩ : ↥L1) = s from Subtype.ext hcommd]
  obtain ⟨d₀, hd₀, hd₀conj⟩ := hNF Q t ht2 htQ σ hσQ hσD
  have hd₀D1b : d₀ ∈ D1b := hcart ▸ hd₀
  obtain ⟨y, hy, hπy⟩ := Subgroup.mem_map.mp hd₀D1b
  have hyD1 : (y : G) ∈ D1 := Subgroup.mem_subgroupOf.mp hy
  have hyN : (y : G) ∈ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1 (borelOf_le_bigB_left L1 L2 S (hD1.1 hyD1))
  have hxN : d * (y : G)⁻¹ ∈ Subgroup.normalizer (L1 : Set G) :=
    (Subgroup.normalizer _).mul_mem hdN ((Subgroup.normalizer _).inv_mem hyN)
  have hδeq : oTwoQuotConj L1 ⟨(y : G), hyN⟩ = MulAut.conj d₀ := by
    have h1 : oTwoQuotConj L1 ⟨(y : G), hyN⟩ = MulAut.conj (π y) :=
      oTwoQuotConj_eq_conj_mk y hyN
    rw [hπy] at h1
    exact h1
  have hxρ : oTwoQuotConj L1 ⟨d * (y : G)⁻¹, hxN⟩ = 1 := by
    have hsub : (⟨d * (y : G)⁻¹, hxN⟩ : ↥(Subgroup.normalizer (L1 : Set G))) =
        (⟨d, hdN⟩ : ↥(Subgroup.normalizer (L1 : Set G))) *
          (⟨(y : G), hyN⟩ : ↥(Subgroup.normalizer (L1 : Set G)))⁻¹ :=
      Subtype.ext (by simp)
    rw [hsub, map_mul, map_inv]
    have hdσ : oTwoQuotConj L1 ⟨d, hdN⟩ = MulAut.conj d₀ := MulEquiv.ext hd₀conj
    rw [hdσ, hδeq, mul_inv_cancel]
  refine ⟨(y : G), hyD1, fun l hl => ?_⟩
  have h := (oTwoQuotConj_eq_one_iff L1 ⟨d * (y : G)⁻¹, hxN⟩).mp hxρ l⁻¹ (L1.inv_mem hl)
  simpa using h

private theorem not_isPGroup_K1_of_borelInf
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) (hR : Hyp111R L1 L2 S)
    {D1 D2 : Subgroup G}
    (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB1D : borelOf L1 S = (S ⊓ L1) ⊔ D1)
    (hD2leB : D2 ≤ bigB L1 L2 S)
    (hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x)
    (hHodd : Odd (Nat.card ↥(D1 ⊔ D2)))
    (hD2ne : D2 ≠ ⊥)
    (hBB : IsPGroup 2 ↥(borelOf L1 S ⊓ borelOf L2 S))
    {n i e : ℕ} (hBt : BenderType (oTwoQuot ↥L1) n i e)
    (hNF : ∀ (Q : Sylow 2 (oTwoQuot ↥L1)) (t : oTwoQuot ↥L1), t * t = 1 →
      t ∉ GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L1)) →
      ∀ σ : MulAut (oTwoQuot ↥L1),
        (∀ x ∈ (Q : Subgroup (oTwoQuot ↥L1)), σ x ∈ (Q : Subgroup (oTwoQuot ↥L1))) →
        (∀ x ∈ cartan (Q : Subgroup (oTwoQuot ↥L1)) t, σ x = x) →
        ∃ d₀ ∈ cartan (Q : Subgroup (oTwoQuot ↥L1)) t,
          ∀ k, σ k = d₀ * k * d₀⁻¹) :
    ¬ IsPGroup 2 ↥(f112K1 L1 L2 S) := by
  intro hK1
  have hD2leD1 : D2 ≤ D1 := by
    intro d hd
    obtain ⟨δ, hδD1, hδcomm⟩ :=
      exists_commutator_lift hF hR hD1 hB1D hD2leB hcomm hBt hNF hd
    have hdD2b : d ∈ bigB L1 L2 S := hD2leB hd
    have hδD1b : δ ∈ bigB L1 L2 S :=
      borelOf_le_bigB_left L1 L2 S (hD1.1 hδD1)
    have hxbigB : d * δ⁻¹ ∈ bigB L1 L2 S :=
      Subgroup.mul_mem _ hdD2b (Subgroup.inv_mem _ hδD1b)
    have hxK1 : (⟨d * δ⁻¹, le_sup_right (a := L1) hxbigB⟩ :
        ↥(L1 ⊔ bigB L1 L2 S)) ∈ f112K1 L1 L2 S :=
      f112_mem_K1_of_commutator_mem hF hxbigB hδcomm
    have hxH : d * δ⁻¹ ∈ D1 ⊔ D2 :=
      Subgroup.mul_mem _ ((le_sup_right : D2 ≤ D1 ⊔ D2) hd)
        ((le_sup_left : D1 ≤ D1 ⊔ D2) (D1.inv_mem hδD1))
    have hxodd : Odd (orderOf (d * δ⁻¹)) :=
      Odd.of_dvd_nat hHodd (Subgroup.orderOf_dvd_natCard (D1 ⊔ D2) hxH)
    obtain ⟨k, hk⟩ := hK1.exists_orderOf_dvd_pow
      (⟨⟨d * δ⁻¹, le_sup_right (a := L1) hxbigB⟩, hxK1⟩ : ↥(f112K1 L1 L2 S))
    have h2 : orderOf (⟨⟨d * δ⁻¹, le_sup_right (a := L1) hxbigB⟩, hxK1⟩ :
        ↥(f112K1 L1 L2 S)) = orderOf (d * δ⁻¹) := by
      rw [Subgroup.orderOf_mk]
      exact Subgroup.orderOf_mk _ _
    have hdvd : orderOf (d * δ⁻¹) ∣ 2 ^ k := by
      rw [← h2]
      exact hk
    have hcop : Nat.Coprime (orderOf (d * δ⁻¹)) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hxodd).pow_right k
    have hx1 : d * δ⁻¹ = 1 := orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)
    have hdeq : d = δ := by
      calc d = (d * δ⁻¹) * δ := by group
        _ = δ := by rw [hx1, one_mul]
    rw [hdeq]
    exact hδD1
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D2, d ≠ 1 := by
    by_contra h
    apply hD2ne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, by simpa [Subgroup.mem_bot] using hx1⟩
  have hdD1 : d ∈ D1 := hD2leD1 hd
  have hdBB : d ∈ borelOf L1 S ⊓ borelOf L2 S := ⟨hD1.1 hdD1, hD2.1 hd⟩
  have hdodd : Odd (orderOf d) :=
    Odd.of_dvd_nat hD2.2.1 (Subgroup.orderOf_dvd_natCard D2 hd)
  obtain ⟨k, hk⟩ := hBB ⟨d, hdBB⟩
  have hdvd : orderOf d ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk d hdBB]
    exact orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf d) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hdodd).pow_right k
  exact hd1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))

private theorem not_isPGroup_K2_of_borelInf
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : Hyp111 L1 L2 S) (hR : Hyp111R L1 L2 S)
    {D1 D2 : Subgroup G}
    (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB2D : borelOf L2 S = (S ⊓ L2) ⊔ D2)
    (hD1leB : D1 ≤ bigB L1 L2 S)
    (hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x)
    (hHodd : Odd (Nat.card ↥(D1 ⊔ D2)))
    (hD1ne : D1 ≠ ⊥)
    (hBB : IsPGroup 2 ↥(borelOf L1 S ⊓ borelOf L2 S))
    {n i e : ℕ} (hBt : BenderType (oTwoQuot ↥L2) n i e)
    (hNF : ∀ (Q : Sylow 2 (oTwoQuot ↥L2)) (t : oTwoQuot ↥L2), t * t = 1 →
      t ∉ GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L2)) →
      ∀ σ : MulAut (oTwoQuot ↥L2),
        (∀ x ∈ (Q : Subgroup (oTwoQuot ↥L2)), σ x ∈ (Q : Subgroup (oTwoQuot ↥L2))) →
        (∀ x ∈ cartan (Q : Subgroup (oTwoQuot ↥L2)) t, σ x = x) →
        ∃ d₀ ∈ cartan (Q : Subgroup (oTwoQuot ↥L2)) t,
          ∀ k, σ k = d₀ * k * d₀⁻¹) :
    ¬ IsPGroup 2 ↥(f112K2 L1 L2 S) := by
  intro hK2
  have hD1leD2 : D1 ≤ D2 := by
    intro d hd
    have hD1leB' : D1 ≤ bigB L2 L1 S := by rwa [bigB_comm]
    have hcomm' : ∀ x ∈ D2, ∀ y ∈ D1, x * y = y * x :=
      fun x hx y hy => (hcomm y hy x hx).symm
    obtain ⟨δ, hδD2, hδcomm⟩ :=
      exists_commutator_lift hF.symm hR.symm hD2 hB2D hD1leB' hcomm' hBt hNF hd
    have hdB1 : d ∈ bigB L1 L2 S := hD1leB hd
    have hδD2b : δ ∈ bigB L1 L2 S :=
      borelOf_le_bigB_right L1 L2 S (hD2.1 hδD2)
    have hxbigB : d * δ⁻¹ ∈ bigB L1 L2 S :=
      Subgroup.mul_mem _ hdB1 (Subgroup.inv_mem _ hδD2b)
    have hxK2 : (⟨d * δ⁻¹, le_sup_right (a := L2) hxbigB⟩ :
        ↥(L2 ⊔ bigB L1 L2 S)) ∈ f112K2 L1 L2 S :=
      f112_mem_K2_of_commutator_mem hF hxbigB hδcomm
    have hxH : d * δ⁻¹ ∈ D1 ⊔ D2 :=
      Subgroup.mul_mem _ ((le_sup_left : D1 ≤ D1 ⊔ D2) hd)
        ((le_sup_right : D2 ≤ D1 ⊔ D2) (D2.inv_mem hδD2))
    have hxodd : Odd (orderOf (d * δ⁻¹)) :=
      Odd.of_dvd_nat hHodd (Subgroup.orderOf_dvd_natCard (D1 ⊔ D2) hxH)
    obtain ⟨k, hk⟩ := hK2.exists_orderOf_dvd_pow
      (⟨⟨d * δ⁻¹, le_sup_right (a := L2) hxbigB⟩, hxK2⟩ : ↥(f112K2 L1 L2 S))
    have h2 : orderOf (⟨⟨d * δ⁻¹, le_sup_right (a := L2) hxbigB⟩, hxK2⟩ :
        ↥(f112K2 L1 L2 S)) = orderOf (d * δ⁻¹) := by
      rw [Subgroup.orderOf_mk]
      exact Subgroup.orderOf_mk _ _
    have hdvd : orderOf (d * δ⁻¹) ∣ 2 ^ k := by
      rw [← h2]
      exact hk
    have hcop : Nat.Coprime (orderOf (d * δ⁻¹)) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hxodd).pow_right k
    have hx1 : d * δ⁻¹ = 1 := orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)
    have hdeq : d = δ := by
      calc d = (d * δ⁻¹) * δ := by group
        _ = δ := by rw [hx1, one_mul]
    rw [hdeq]
    exact hδD2
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D1, d ≠ 1 := by
    by_contra h
    apply hD1ne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, by simpa [Subgroup.mem_bot] using hx1⟩
  have hdD2 : d ∈ D2 := hD1leD2 hd
  have hdBB : d ∈ borelOf L1 S ⊓ borelOf L2 S := ⟨hD1.1 hd, hD2.1 hdD2⟩
  have hdodd : Odd (orderOf d) :=
    Odd.of_dvd_nat hD1.2.1 (Subgroup.orderOf_dvd_natCard D1 hd)
  obtain ⟨k, hk⟩ := hBB ⟨d, hdBB⟩
  have hdvd : orderOf d ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk d hdBB]
    exact orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf d) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hdodd).pow_right k
  exact hd1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))

theorem str83Kernel_of_borelInf_at
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a f : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L2))
    (hBB : IsPGroup 2 ↥(borelOf L1 S ⊓ borelOf L2 S)) :
    ¬ IsPGroup 2 ↥(f112K1 L1 L2 S) ∧ ¬ IsPGroup 2 ↥(f112K2 L1 L2 S) := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hset : RonanF13.F13Setup L1 L2 S := RonanF13.F13Setup.of_hyp111R hR
  obtain ⟨D1, D2, hD1, hD2, hB1D, hB2D, hcomm, hBE, hHall, hHab⟩ :=
    RonanF13.core5 hset (RonanF13.rankOneTwist_of_listed hF.h1.listed)
      (RonanF13.rankOneTwist_of_listed hF.h2.listed)
  have hbig : bigB L1 L2 S = S ⊔ D1 ⊔ D2 := hBE
  have hD2leB : D2 ≤ bigB L1 L2 S := by rw [hbig]; exact le_sup_right
  have hD1ne : D1 ≠ ⊥ := by
    intro hbot
    exact not_isPGroup_borelOf_of_sz hF.h1.sylow ha hSz (by
      rw [hB1D, hbot, sup_bot_eq]
      exact hF.h1.sylow.2.1)
  have hD2ne : D2 ≠ ⊥ := by
    intro hbot
    exact not_isPGroup_borelOf_of_l2 hF.h2.sylow hf hL2 (by
      rw [hB2D, hbot, sup_bot_eq]
      exact hF.h2.sylow.2.1)
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hK1 : ¬ IsPGroup 2 ↥(f112K1 L1 L2 S) :=
    not_isPGroup_K1_of_borelInf hF hR hD1 hD2 hB1D hD2leB hcomm hHall.2.1 hD2ne hBB hBt1
      (fun Q t ht htQ σ hσQ hσD =>
        BenderType.aut_eq_conj_cartan_suzuki hBt1 Q ht htQ σ hσQ hσD)
  have hD1leB : D1 ≤ bigB L1 L2 S := hD1.1.trans (borelOf_le_bigB_left L1 L2 S)
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 := BenderType.linear f hf (Classical.choice hL2)
  have hK2 : ¬ IsPGroup 2 ↥(f112K2 L1 L2 S) :=
    not_isPGroup_K2_of_borelInf hF hR hD1 hD2 hB2D hD1leB hcomm hHall.2.1 hD1ne hBB hBt2
      (fun Q t ht htQ σ hσQ hσD =>
        BenderType.aut_eq_conj_cartan_linear hBt2 Q ht htQ σ hσQ hσD)
  exact ⟨hK1, hK2⟩

theorem str83_exists_cartan_delta
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    ∃ D1 D2 : Subgroup G,
      RonanF13.HallTwoPrime D1 (borelOf L1 S) ∧ RonanF13.HallTwoPrime D2 (borelOf L2 S) ∧
      borelOf L1 S = (S ⊓ L1) ⊔ D1 ∧ borelOf L2 S = (S ⊓ L2) ⊔ D2 ∧
      (∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x) ∧ bigB L1 L2 S = S ⊔ D1 ⊔ D2 ∧
      ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1,
        (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hset : RonanF13.F13Setup L1 L2 S := RonanF13.F13Setup.of_hyp111R hR
  obtain ⟨D1, D2, hD1, hD2, hB1D, hB2D, hcomm, hBE, -, -⟩ :=
    RonanF13.core5 hset (RonanF13.rankOneTwist_of_listed hF.h1.listed)
      (RonanF13.rankOneTwist_of_listed hF.h2.listed)
  have hD2leB : D2 ≤ bigB L1 L2 S := by
    unfold bigB
    rw [hBE]
    exact le_sup_right
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  refine ⟨D1, D2, hD1, hD2, hB1D, hB2D, hcomm, hBE, fun d hd => ?_⟩
  exact exists_commutator_lift hF hR hD1 hB1D hD2leB hcomm hBt1
    (fun Q t ht htQ σ hσQ hσD =>
      BenderType.aut_eq_conj_cartan_suzuki hBt1 Q ht htQ σ hσQ hσD) hd

theorem str83Kernel_of_borelInf (h : Str83BorelInf) :
    Str83Kernel := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨f, hL2f⟩ := hL2
  have hf : 2 ≤ f := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig
    hF.1.h2.listed hBig hL2f
  change ¬ IsPGroup 2 ↥(f112K1 L1 L2 S) ∧ ¬ IsPGroup 2 ↥(f112K2 L1 L2 S)
  exact str83Kernel_of_borelInf_at hF.1 ha hSz hf hL2f
    (h G L1 L2 S a hF ha hSz hBig ⟨f, hL2f⟩)

theorem str83BorelInf_of_caseI (hI : Str83CaseI)
    (hT : Str83TorusFaithful) : Str83BorelInf := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  classical
  set T : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hTdef
  have hF' : F112HypW L1 L2 T := f112HypW_sup_inf hF
  have hB2T : borelOf L2 T = borelOf L2 S := by
    unfold borelOf
    rw [sup_inf_inf_right L1 L2 S]
  have hsupT : (T ⊓ L1) ⊔ (T ⊓ L2) = T := by
    rw [hTdef, sup_inf_inf_left, sup_inf_inf_right]
  have hnormT : bigB L1 L2 T ≤ Subgroup.normalizer (T : Set G) :=
    bigB_le_normalizer_of_sup_inf_eq hF'.1 hsupT
  have hcase := hI G L1 L2 T a hF' hnormT ha hSz hBig hL2
  have hfaith := hT G L1 L2 T a hF' hnormT ha hSz hBig hL2
  have hZle : omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 (L1 ⊔ bigB L1 L2 T)) :=
    omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf hF'.1
  have hcle : Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (L1 ⊔ bigB L1 L2 T)) : Set G) ≤
      Subgroup.centralizer (omegaOneCenterOf T : Set G) :=
    Subgroup.centralizer_le hZle
  have hno : ∀ d ∈ borelOf L1 S ⊓ borelOf L2 S, Odd (orderOf d) → d = 1 := by
    intro d hd hdodd
    have hdL : d ∈ L1 := (F1.borelOf_le L1 S) hd.1
    have hdC : d ∈ Subgroup.centralizer (omegaOneCenterOf T : Set G) :=
      hcle (hcase ((le_sup_left : L1 ≤ L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 T)) hdL))
    have hdB2 : d ∈ borelOf L2 T := by rw [hB2T]; exact hd.2
    exact hfaith d hdB2 hdodd (fun z hz =>
      ((Subgroup.mem_centralizer_iff.mp hdC) z hz).symm)
  refine (IsPGroup.iff_card (p := 2) (G := ↥(borelOf L1 S ⊓ borelOf L2 S))).mpr
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro p hp hpdvd
  by_contra hpne
  have hpodd : Odd p := hp.odd_of_ne_two hpne
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(borelOf L1 S ⊓ borelOf L2 S)) p hpdvd
  have hx' : orderOf (x : G) = p := by
    rw [← Subgroup.orderOf_mk (x : G) x.2]
    exact hx
  have hxodd : Odd (orderOf (x : G)) := by rw [hx']; exact hpodd
  have hx1 : (x : G) = 1 := hno (x : G) x.2 hxodd
  have hone : orderOf x = 1 := by
    rw [show x = 1 from Subtype.ext hx1, orderOf_one]
  exact hp.ne_one (by rw [← hx]; exact hone)

end CFSG.Quasithin.Stroth
