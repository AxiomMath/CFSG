module

public import CFSG.Quasithin.H13.A5S1521d
public import CFSG.Quasithin.H13.A5Sit20d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff piQ_eq_iff Tstar
  isComponent_of_isComponentOf_top mem_normalizer_of_centralizes_sylow centralizes_of_comm_central
  central_of_normal_pGroup)
open scoped commutatorElement

section A38

variable {X : Type} [Group X] [Finite X]

theorem conj_eq_or_eq_of_two {K : Subgroup X} (hK : CFSG.IsComponent K) {t : X}
    (hcl : conjClosure K ⊤ = K ⊔ K.map (MulAut.conj t).toMonoidHom) (g : X) :
    K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj t).toMonoidHom := by
  by_contra hne
  simp only [not_or] at hne
  have hKg := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  have hKt := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  have h1 := (CFSG.LocalCores.distinct_components_commute hKg hK).resolve_left hne.1
  have h2 := (CFSG.LocalCores.distinct_components_commute hKg hKt).resolve_left hne.2
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rw [← hcl]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_conjClosure (Subgroup.mem_top g) hk
  have hC : K ⊔ K.map (MulAut.conj t).toMonoidHom ≤
      Subgroup.centralizer (K.map (MulAut.conj g).toMonoidHom : Set X) := by
    refine sup_le ?_ ?_
    · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm _ _).trans h1)
      exact this
    · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm _ _).trans h2)
      exact this
  have hab : ⁅K.map (MulAut.conj g).toMonoidHom, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hC)
  have hperf : Group.IsPerfect ↥(K.map (MulAut.conj g).toMonoidHom) := hKg.1.1
  have hnt : Nontrivial ↥(K.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hKg.1
  have hbot : K.map (MulAut.conj g).toMonoidHom = ⊥ :=
    (Subgroup.isPerfect_iff.mp hperf).symm.trans hab
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(K.map (MulAut.conj g).toMonoidHom))
  apply ha
  have : (a : X) ∈ (⊥ : Subgroup X) := hbot ▸ a.2
  exact Subtype.ext (Subgroup.mem_bot.mp this)

theorem mem_normalizer_of_odd (h38 : A38Part3 X) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    {x : X} {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    x ∈ Subgroup.normalizer (K : Set X) := by
  have hK' := isComponent_of_isComponentOf_top hK
  obtain ⟨hnorm, -⟩ := h38 K (A5.mem_cComp_of_isComponentOf_top hK)
  rcases hnorm with hn | ⟨-, t, htN, -, -, hcl⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.mem_top x
  · have hdich := conj_eq_or_eq_of_two hK' hcl
    have hx2 : x ^ 2 ∈ Subgroup.normalizer (K : Set X) := by
      by_cases hx : x ∈ Subgroup.normalizer (K : Set X)
      · exact Subgroup.pow_mem _ hx 2
      · have hKx : K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj t).toMonoidHom := by
          rcases hdich x with h | h
          · refine absurd ?_ hx
            rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
            exact h
          · exact h
        rcases hdich (x ^ 2) with h | h
        · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
          exact h
        · exfalso
          apply hx
          have hmul : (MulAut.conj (x ^ 2)).toMonoidHom =
              (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
            ext y
            simp [pow_two, mul_assoc]
          have h' : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
              K.map (MulAut.conj x).toMonoidHom := by
            rw [Subgroup.map_map, ← hmul, h, hKx]
          have hinj : Function.Injective (Subgroup.map (MulAut.conj x).toMonoidHom) :=
            Subgroup.map_injective (MulAut.conj x).injective
          rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
          exact hinj h'
    obtain ⟨j, rfl⟩ := hm
    have e : x = (x ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hxm, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hx2 _

end A38

@[expose] noncomputable def imQ {G : Type} [Group G] (H X : Subgroup G) : Subgroup (Hstar H) :=
  (X.subgroupOf H).map (piQ H)

section ImQ

variable {G : Type} [Group G] {H : Subgroup G}

theorem mem_imQ {X : Subgroup G} (hXH : X ≤ H) {y : Hstar H} :
    y ∈ imQ H X ↔ ∃ x, ∃ hx : x ∈ X, piQ H ⟨x, hXH hx⟩ = y := by
  constructor
  · rintro ⟨⟨x, hxH⟩, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hXH hx⟩, hx, rfl⟩

theorem imQ_le_of_odd {X : Subgroup G} (hXH : X ≤ H) (hX : oTwoRes X = X) {P : Subgroup (Hstar H)}
    (hP : ∀ x (hx : x ∈ X), (∃ m : ℕ, Odd m ∧ x ^ m = 1) → piQ H ⟨x, hXH hx⟩ ∈ P) :
    imQ H X ≤ P := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_imQ hXH).mp hy
  have hx' : x ∈ oTwoRes X := hX.symm ▸ hx
  have key : ∀ z (hz : z ∈ oTwoRes X), piQ H ⟨z, hXH (oTwoRes_le X hz)⟩ ∈ P := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact hP z hz.1 hz.2
    | one => rw [show (⟨1, _⟩ : ↥H) = 1 from rfl, map_one]; exact P.one_mem
    | mul a c ha hc iha ihc =>
      have e : (⟨a * c, hXH (oTwoRes_le X (Subgroup.mul_mem _ ha hc))⟩ : ↥H) =
          ⟨a, hXH (oTwoRes_le X ha)⟩ * ⟨c, hXH (oTwoRes_le X hc)⟩ := rfl
      rw [e, map_mul]
      exact P.mul_mem iha ihc
    | inv a ha iha =>
      have e : (⟨a⁻¹, hXH (oTwoRes_le X (Subgroup.inv_mem _ ha))⟩ : ↥H) =
          (⟨a, hXH (oTwoRes_le X ha)⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact P.inv_mem iha
  exact key x hx'

theorem imQ_le_oTwoRes {X : Subgroup G} (hXH : X ≤ H) (hX : oTwoRes X = X) :
    imQ H X ≤ oTwoRes (imQ H X) :=
  imQ_le_of_odd hXH hX fun x hx ⟨m, hm, hxm⟩ =>
    Subgroup.subset_closure ⟨(mem_imQ hXH).mpr ⟨x, hx, rfl⟩, m, hm, by
      rw [← map_pow]
      have : (⟨x, hXH hx⟩ : ↥H) ^ m = 1 := Subtype.ext hxm
      rw [this, map_one]⟩

end ImQ

theorem isSolvable_of_decomp {G : Type} [Group G] [Finite G] {X : Subgroup G} {c : G}
    (hc : c ∈ X)
    (hdec : ∀ x ∈ X, x ∈ pCoreOf 2 X ∨ c * c * x ∈ pCoreOf 2 X ∨ c * x ∈ pCoreOf 2 X) :
    Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥X := CFSG.Open.pCore 2 ↥X with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : Group.IsNilpotent ↥N := hNp.isNilpotent
  have hmem : ∀ x : ↥X, (x : G) ∈ pCoreOf 2 X → x ∈ N := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← Subtype.ext hyx]
    exact hy
  set c' : ↥X := ⟨c, hc⟩
  have hzp : ∀ a : ↥X ⧸ N, a ∈ Subgroup.zpowers (QuotientGroup.mk c' : ↥X ⧸ N) := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rcases hdec x x.2 with h | h | h
    · have : (QuotientGroup.mk x : ↥X ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr (hmem x h)
      rw [this]
      exact Subgroup.one_mem _
    · have h1 : (QuotientGroup.mk (c' * c' * x) : ↥X ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hmem (c' * c' * x) h)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h1
      have e : (QuotientGroup.mk x : ↥X ⧸ N) =
          ((QuotientGroup.mk c' : ↥X ⧸ N) * QuotientGroup.mk c')⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
        (Subgroup.mem_zpowers _))
    · have h1 : (QuotientGroup.mk (c' * x) : ↥X ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hmem (c' * x) h)
      rw [QuotientGroup.mk_mul] at h1
      have e : (QuotientGroup.mk x : ↥X ⧸ N) = (QuotientGroup.mk c')⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hcomm : ∀ a b : ↥X ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp b)
    exact ((Commute.refl _).zpow_zpow i j).eq
  have : Group.IsSolvable (↥X ⧸ N) := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_subgroup_quotient N

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem sqtkHyp_Hstar : SQTKHyp (Hstar H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.h13.simple
  have hsq := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
    S.pCoreOf_H_ne_bot
  have hp : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf H) :=
    (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).symm
  refine ⟨inferInstance, sqt_quotient_two_group hsq.1 _ hp, kGroup_quotient hsq.2 _, ?_⟩
  exact S.pCore_two_Hstar

theorem isSylowTwoOf_Tstar : IsSylowTwoOf (Tstar T H) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp S.hF.sylow_H
  have hPT : (P : Subgroup ↥H) = T.subgroupOf H := by
    rw [← hP]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  let P' := P.mapSurjective (piQ_surjective H)
  have hP' : (P' : Subgroup (Hstar H)) = Tstar T H := by
    rw [Sylow.coe_mapSurjective, hPT]
    rfl
  refine ⟨le_top, hP' ▸ P'.isPGroup', ?_⟩
  have : (Tstar T H).subgroupOf ⊤ = (Tstar T H).comap (⊤ : Subgroup (Hstar H)).subtype := rfl
  rw [this, Subgroup.index_comap_of_surjective _ (fun y => ⟨⟨y, trivial⟩, rfl⟩), ← hP']
  exact P'.not_dvd_index

theorem piQ_V_eq {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) {w : G} (hw : w ∈ V) :
    piQ H ⟨w, S.V_le_H hw⟩ = 1 ∨ piQ H ⟨w, S.V_le_H hw⟩ = piQ H ⟨v, S.V_le_H hv⟩ := by
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun h => hvQ (h hv)
  obtain ⟨hVp, -⟩ := S.hF.F95_1 S.relIndex_V3 hVQ
  by_cases hwQ : w ∈ pCoreOf 2 H
  · exact Or.inl ((piQ_eq_one_iff _).2 hwQ)
  · right
    rw [piQ_eq_iff]
    have hidx : (V₃.subgroupOf V).index = 2 := S.relIndex_V3
    have h1 : (⟨w, hw⟩ : ↥V) ∉ V₃.subgroupOf V := fun h =>
      hwQ (by rw [Subgroup.mem_subgroupOf, hVp] at h; exact h.2)
    have h2 : (⟨v, hv⟩ : ↥V)⁻¹ ∉ V₃.subgroupOf V := fun h =>
      hvQ (by rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf, hVp] at h; exact h.2)
    have h3 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false h1 h2)
    rw [Subgroup.mem_subgroupOf, hVp] at h3
    exact h3.2

theorem comm_Tstar {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) {t : Hstar H}
    (ht : t ∈ Tstar T H) :
    t * piQ H ⟨v, S.V_le_H hv⟩ = piQ H ⟨v, S.V_le_H hv⟩ * t := by
  obtain ⟨t0, ht0', rfl⟩ := ht
  have ht0 : (t0 : G) ∈ T := ht0'
  have hw : (t0 : G) * v * (t0 : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (S.hF.T_normalizes_V ht0) v).mp hv
  have e : piQ H ⟨(t0 : G) * v * (t0 : G)⁻¹, S.V_le_H hw⟩ =
      piQ H t0 * piQ H ⟨v, S.V_le_H hv⟩ * (piQ H t0)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rcases S.piQ_V_eq hv hvQ hw with h | h
  · exfalso
    rw [e, mul_inv_eq_one, mul_eq_left] at h
    exact hvQ ((piQ_eq_one_iff _).1 h)
  · rw [e] at h
    calc piQ H t0 * piQ H ⟨v, S.V_le_H hv⟩ =
        piQ H t0 * piQ H ⟨v, S.V_le_H hv⟩ * (piQ H t0)⁻¹ * piQ H t0 := by group
      _ = piQ H ⟨v, S.V_le_H hv⟩ * piQ H t0 := by rw [h]

theorem piQ_v_sq' {v : G} (hv : v ∈ V) :
    piQ H ⟨v, S.V_le_H hv⟩ * piQ H ⟨v, S.V_le_H hv⟩ = 1 := by
  rw [← map_mul, piQ_eq_one_iff]
  show v * v ∈ pCoreOf 2 H
  rw [S.sq_eq_one_of_mem_V hv]
  exact Subgroup.one_mem _

theorem exists_component (hF956 : A5.StmtF956i) {Y : Subgroup G} (SY : A5SitY S Y)
    (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))) {v : G} (hv : v ∈ V)
    (hvQ : v ∉ pCoreOf 2 H) :
    ∃ K : Subgroup (Hstar H), IsComponentOf K ⊤ ∧
      ∃ k ∈ K, k * piQ H ⟨v, S.V_le_H hv⟩ ≠ piQ H ⟨v, S.V_le_H hv⟩ * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  set b := piQ H ⟨v, S.V_le_H hv⟩ with hbdef
  have hF : quasithinGenFitting (⊤ : Subgroup (Hstar H)) ≤ Subgroup.centralizer {b} := by
    unfold quasithinGenFitting
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨-, hNn, hNnil⟩
      have hN : N.Normal := ⟨fun n hn g => by
        have := hNn.conj_mem ⟨n, trivial⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, trivial⟩
        rw [Subgroup.mem_subgroupOf] at this
        exact this⟩
      refine (CFSG.normal_nilpotent_le_sup_pCore hN hNnil).trans (iSup_le fun p => ?_)
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hp : (p.1 : ℕ).Prime := Nat.prime_of_mem_primeFactors p.1.2
      have ha' : a ∈ CFSG.Open.pCore (p.1 : ℕ) (Hstar H) := by assumption
      exact S.lemma_13_5_20 hF956 SY h1519 hp ha' hv
    · rintro K hK k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hno K hK k hk
  have hb2 : b * b = 1 := S.piQ_v_sq' hv
  have hP : IsPGroup 2 ↥(Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime (by rw [pow_two]; exact hb2) fun h => hvQ ?_
    exact (piQ_eq_one_iff _).1 h
  have hY : pCoreOf 2 (⊤ : Subgroup (Hstar H)) = ⊥ :=
    S.sqtkHyp_Hstar.pCoreOf_two_of_subnormal (IsSubnormal.refl ⊤)
  have hPF : Subgroup.zpowers b ≤
      Subgroup.centralizer (quasithinGenFitting (⊤ : Subgroup (Hstar H)) : Set (Hstar H)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hF hh)
  have hc := centralizer_of_centralizes_genFitting hP
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun _ => by simp) hY hPF
  have hbz : ∀ g : Hstar H, g * b = b * g := fun g =>
    Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_zpowers b)) g trivial
  have hnorm : (Subgroup.zpowers b).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * b ^ k * g⁻¹ = b ^ k := by
      rw [((show Commute g b from hbz g).zpow_right k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers b k⟩
  have hbO := le_pCore 2 hnorm hP (Subgroup.mem_zpowers b)
  rw [S.pCore_two_Hstar, Subgroup.mem_bot, hbdef, piQ_eq_one_iff] at hbO
  exact hvQ hbO

theorem mem_normalizer_component {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H)
    {K : Subgroup (Hstar H)} (hK : IsComponentOf K ⊤) :
    piQ H ⟨v, S.V_le_H hv⟩ ∈ Subgroup.normalizer (K : Set (Hstar H)) :=
  mem_normalizer_of_centralizes_sylow hK
    (L246C127.isSylowTwoOf_inf_of_isSubnormal' hK.2.1 S.isSylowTwoOf_Tstar)
    fun _ hx => S.comm_Tstar hv hvQ hx.1

theorem not_centralizes_Y {Y : Subgroup G} (SY : A5SitY S Y)
    (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))) {v : G} (hv : v ∈ V)
    (hvQ : v ∉ pCoreOf 2 H) {K : Subgroup (Hstar H)} (hK : IsComponentOf K ⊤)
    (hKb : ∃ k ∈ K, k * piQ H ⟨v, S.V_le_H hv⟩ ≠ piQ H ⟨v, S.V_le_H hv⟩ * k) :
    ∃ l, ∃ hl : l ∈ Y, ∃ k ∈ K, piQ H ⟨l, SY.Y_le_H hl⟩ * k ≠
      k * piQ H ⟨l, SY.Y_le_H hl⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have hVH := S.V_le_H
  have hbK := S.mem_normalizer_component hv hvQ hK
  have hH1H : H ⊓ Subgroup.normalizer (Y : Set G) ≤ H := inf_le_left
  have hOH : pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)) ≤ H :=
    (pCoreOf_le 2 _).trans hH1H
  set D : Subgroup (Hstar H) :=
    ((pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))).subgroupOf H).map (piQ H) with hD
  have hDp : IsPGroup 2 D := by
    refine IsPGroup.map ?_ _
    exact (pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm
  have hpre : ∀ k ∈ K, ∃ g : ↥H, (g : G) ∈ Subgroup.normalizer (Y : Set G) ∧ piQ H g = k := by
    intro k hk
    obtain ⟨g, rfl⟩ := piQ_surjective H k
    exact ⟨g, S.mem_normalizer_Y_of_comm SY g.2 fun l hl => (hno l hl _ hk).symm, rfl⟩
  have hnormO : ∀ g ∈ H ⊓ Subgroup.normalizer (Y : Set G),
      ∀ q ∈ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)), g * q * g⁻¹ ∈
        pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)) := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hg) q).mp hq
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    intro k hk d hd
    obtain ⟨g, hgN, rfl⟩ := hpre k hk
    obtain ⟨q, hq', rfl⟩ := hd
    have hq : (q : G) ∈ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)) := hq'
    refine ⟨g * q * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show (g : G) * q * (g : G)⁻¹ ∈ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))
    exact hnormO _ ⟨g.2, hgN⟩ _ hq
  have hbD : ∀ k ∈ K, piQ H ⟨v, hVH hv⟩ * k * (piQ H ⟨v, hVH hv⟩)⁻¹ * k⁻¹ ∈ D := by
    intro k hk
    obtain ⟨g, hgN, rfl⟩ := hpre k hk
    have hvO := h1519 hv
    refine ⟨⟨v, hVH hv⟩ * g * ⟨v, hVH hv⟩⁻¹ * g⁻¹, ?_, by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩
    show v * g * v⁻¹ * (g : G)⁻¹ ∈ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))
    have h1 := hnormO _ ⟨g.2, hgN⟩ _ (Subgroup.inv_mem _ hvO)
    have := Subgroup.mul_mem _ hvO h1
    simpa [mul_assoc] using this
  have hcent := central_of_normal_pGroup hK (inf_le_left : K ⊓ D ≤ K)
    (fun k hk n hn => ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk), hKD k hk n hn.2⟩)
    (hDp.to_le inf_le_right)
  have hc : ∀ k ∈ K, ∀ k' ∈ K, k' * (piQ H ⟨v, hVH hv⟩ * k * (piQ H ⟨v, hVH hv⟩)⁻¹ * k⁻¹) =
      (piQ H ⟨v, hVH hv⟩ * k * (piQ H ⟨v, hVH hv⟩)⁻¹ * k⁻¹) * k' := by
    intro k hk k' hk'
    have hmem : piQ H ⟨v, hVH hv⟩ * k * (piQ H ⟨v, hVH hv⟩)⁻¹ * k⁻¹ ∈ K := K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hbK k).mp hk) (K.inv_mem hk)
    exact hcent _ ⟨hmem, hbD k hk⟩ k' hk'
  obtain ⟨k, hk, hne⟩ := hKb
  exact hne (centralizes_of_comm_central hK hbK hc k hk)

end A5Sit

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}

@[expose] noncomputable def Ut (_S : A5Sit G T V V₁ V₃ L₁ H) : Type :=
  ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)

noncomputable instance (S : A5Sit G T V V₁ V₃ L₁ H) : CommGroup (S.Ut) :=
  have := S.normal_V1_UH
  { (inferInstance : Group (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H))) with
    mul_comm := S.UH_quot_comm }

noncomputable instance (S : A5Sit G T V V₁ V₃ L₁ H) : Finite (S.Ut) :=
  inferInstanceAs (Finite (↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)))

variable (S : A5Sit G T V V₁ V₃ L₁ H)
include S

@[expose] noncomputable def utMk : ↥(conjClosure V₃ H) →* S.Ut :=
  have := S.normal_V1_UH
  QuotientGroup.mk' (V₁.subgroupOf (conjClosure V₃ H))

theorem utMk_surjective : Function.Surjective S.utMk := by
  have := S.normal_V1_UH
  exact QuotientGroup.mk'_surjective _

theorem utMk_eq_one_iff (u : ↥(conjClosure V₃ H)) : S.utMk u = 1 ↔ (u : G) ∈ V₁ := by
  have := S.normal_V1_UH
  show (QuotientGroup.mk' _ u : ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem ut_sq (w : S.Ut) : w ^ 2 = 1 := by
  have := S.normal_V1_UH
  rw [pow_two]
  exact S.UH_quot_sq w

theorem exists_rhoA : ∃ ρ : Hstar H →* MulAut S.Ut, Function.Injective ρ ∧
    ∀ (h : ↥H) (u u' : ↥(conjClosure V₃ H)), (u' : G) = h * u * (h : G)⁻¹ →
      ρ (piQ H h) (S.utMk u) = S.utMk u' := by
  have := S.normal_V1_UH
  obtain ⟨ρ0, hρ0⟩ := S.exists_actQ
  have hinv : ∀ x : Hstar H, ∀ w, ρ0 x⁻¹ (ρ0 x w) = w := fun x w => by
    show (ρ0 x⁻¹ * ρ0 x) w = w
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' : ∀ x : Hstar H, ∀ w, ρ0 x (ρ0 x⁻¹ w) = w := fun x w => by
    show (ρ0 x * ρ0 x⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  let f : Hstar H → MulAut S.Ut := fun x =>
    { toFun := fun w => ρ0 x w
      invFun := fun w => ρ0 x⁻¹ w
      left_inv := hinv x
      right_inv := hinv' x
      map_mul' := fun a c => (ρ0 x).map_mul a c }
  let ρ : Hstar H →* MulAut S.Ut :=
    { toFun := f
      map_one' := by
        ext w
        show ρ0 1 w = w
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        ext w
        show ρ0 (x * y) w = ρ0 x (ρ0 y w)
        rw [map_mul]
        rfl }
  refine ⟨ρ, ?_, fun h u u' hu' => hρ0 h u u' hu'⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨h, rfl⟩ := piQ_surjective H x
  rw [piQ_eq_one_iff, S.hF.pCoreOf_eq_centralizerMod]
  refine ⟨h.2, S.hF.H_normalizes_V₁ h.2, fun u hu => ?_⟩
  have hu' : u⁻¹ ∈ conjClosure V₃ H := Subgroup.inv_mem _ hu
  have hmem : (h : G) * u⁻¹ * (h : G)⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H h.2) _).mp hu'
  have e := hρ0 h ⟨u⁻¹, hu'⟩ ⟨_, hmem⟩ rfl
  have h1 : ((⟨_, hmem⟩ : ↥(conjClosure V₃ H)) :
      ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) =
        ((⟨u⁻¹, hu'⟩ : ↥(conjClosure V₃ H)) :
          ↥(conjClosure V₃ H) ⧸ V₁.subgroupOf (conjClosure V₃ H)) := by
    rw [← e]
    have := congrArg (fun φ : MulAut S.Ut => φ (S.utMk ⟨u⁻¹, hu'⟩)) hx
    exact this
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  simpa [mul_assoc] using h1

@[expose] noncomputable def Vt3 : Subgroup S.Ut :=
  (V₃.subgroupOf (conjClosure V₃ H)).map S.utMk

theorem card_Vt3 : Nat.card S.Vt3 ≤ 4 := by
  have h1 := B1More.card_map_mul_card_inf_ker (V₃.subgroupOf (conjClosure V₃ H)) S.utMk
  have h8 : Nat.card ↥(V₃.subgroupOf (conjClosure V₃ H)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_conjClosure V₃ H)).toEquiv, S.card_V3]
  have h2 : 2 ≤ Nat.card ↥(V₃.subgroupOf (conjClosure V₃ H) ⊓ S.utMk.ker) := by
    have hle : V₁.subgroupOf (conjClosure V₃ H) ≤ V₃.subgroupOf (conjClosure V₃ H) ⊓
        S.utMk.ker := fun u hu => ⟨S.V1_le_V3 hu, (S.utMk_eq_one_iff u).mpr hu⟩
    refine le_trans ?_ (Subgroup.card_le_of_le hle)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (S.V1_le_V3.trans (le_conjClosure V₃ H))).toEquiv, S.card_V1]
  rw [h8] at h1
  rw [Vt3]
  nlinarith

@[expose] noncomputable def rhoA : Hstar H →* MulAut S.Ut := Classical.choose S.exists_rhoA

theorem rhoA_injective : Function.Injective S.rhoA := (Classical.choose_spec S.exists_rhoA).1

theorem rhoA_mk (h : ↥H) (u u' : ↥(conjClosure V₃ H)) (hu' : (u' : G) = h * u * (h : G)⁻¹) :
    S.rhoA (piQ H h) (S.utMk u) = S.utMk u' :=
  (Classical.choose_spec S.exists_rhoA).2 h u u' hu'

theorem imQ_le_normalizer (h38 : A38ForSQTK) {X : Subgroup G} (hXH : X ≤ H)
    (hX : oTwoRes X = X) {K : Subgroup (Hstar H)} (hK : IsComponentOf K ⊤) :
    imQ H X ≤ Subgroup.normalizer (K : Set (Hstar H)) :=
  imQ_le_of_odd hXH hX fun x hx ⟨m, hm, hxm⟩ =>
    mem_normalizer_of_odd (h38 _ S.sqtkHyp_Hstar) hK hm (by
      rw [← map_pow]
      have : (⟨x, hXH hx⟩ : ↥H) ^ m = 1 := Subtype.ext hxm
      rw [this, map_one])

theorem mem_normalizer_V_of_comm {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) {g : G}
    (hg : g ∈ H) (hcomm : piQ H ⟨g, hg⟩ * piQ H ⟨v, S.V_le_H hv⟩ =
      piQ H ⟨v, S.V_le_H hv⟩ * piQ H ⟨g, hg⟩) :
    g ∈ H ⊓ Subgroup.normalizer (V : Set G) := by
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun h => hvQ (h hv)
  obtain ⟨h1, h2⟩ := S.hF.F95_3 S.relIndex_V3 hVQ
  rw [← h2, ← h1]
  refine ⟨hg, le_normalizer_pCoreOf 2 H hg, fun w hw => ?_⟩
  have hc : piQ H ⟨g, hg⟩ * piQ H ⟨w, S.V_le_H hw⟩ = piQ H ⟨w, S.V_le_H hw⟩ * piQ H ⟨g, hg⟩ := by
    rcases S.piQ_V_eq hv hvQ hw with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hcomm
  rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, piQ_eq_one_iff] at hc
  simpa [mul_assoc] using hc

theorem rhoA_comm_mem_Vt3 {v : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) (w : S.Ut) :
    S.rhoA (piQ H ⟨v, S.V_le_H hv⟩) w * w⁻¹ ∈ S.Vt3 := by
  obtain ⟨u, rfl⟩ := S.utMk_surjective w
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun h => hvQ (h hv)
  obtain ⟨-, hUV, -⟩ := S.hF.F95_2_aux S.relIndex_V3 hVQ
  have hmem : v * u * v⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H (S.V_le_H hv)) u).mp u.2
  rw [S.rhoA_mk ⟨v, S.V_le_H hv⟩ u ⟨_, hmem⟩ rfl, ← map_inv, ← map_mul]
  refine ⟨⟨v * u * v⁻¹, hmem⟩ * u⁻¹, ?_, rfl⟩
  show v * u * v⁻¹ * (u : G)⁻¹ ∈ V₃
  have h1 := hUV (Subgroup.commutator_mem_commutator u.2 hv)
  have h2 := V₃.inv_mem h1
  rw [commutatorElement_inv, commutatorElement_def] at h2
  exact h2

theorem pair_Hstar (hF956 : A5.StmtF956i) {v : G} (hv : v ∈ V) (x : Hstar H) :
    (∃ k : ℕ, (piQ H ⟨v, S.V_le_H hv⟩ * (x * piQ H ⟨v, S.V_le_H hv⟩ * x⁻¹)) ^ 2 ^ k = 1) ∨
      (piQ H ⟨v, S.V_le_H hv⟩ * (x * piQ H ⟨v, S.V_le_H hv⟩ * x⁻¹)) ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := piQ_surjective H x
  have hVH := S.V_le_H
  have hyH : v * ((g : G) * v * (g : G)⁻¹) ∈ H :=
    H.mul_mem (hVH hv) (H.mul_mem (H.mul_mem g.2 (hVH hv)) (H.inv_mem g.2))
  have e : piQ H ⟨v, hVH hv⟩ * (piQ H g * piQ H ⟨v, hVH hv⟩ * (piQ H g)⁻¹) =
      piQ H ⟨_, hyH⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e]
  have hyI : v * ((g : G) * v * (g : G)⁻¹) ∈ V ⊔ conjSub ((g : G)⁻¹)⁻¹ V := by
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ?_)
    rw [inv_inv, mem_conjSub]
    simpa [mul_assoc] using hv
  by_cases hI : ∀ z ∈ V ⊔ conjSub ((g : G)⁻¹)⁻¹ V, ∃ n : ℕ, z ^ 2 ^ n ∈ pCoreOf 2 H
  · left
    obtain ⟨n, hn⟩ := hI _ hyI
    refine ⟨n, ?_⟩
    rw [← map_pow, piQ_eq_one_iff]
    simpa using hn
  · obtain ⟨hN, ⟨e3⟩⟩ := S.I_S3 hF956 (H.inv_mem g.2) hI
    set I := V ⊔ conjSub ((g : G)⁻¹)⁻¹ V
    set π := QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)
    have hπ1 : ∀ z : ↥I, π z = 1 ↔ (z : G) ∈ pCoreOf 2 H := fun z => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rcases A5.perm3_cube_of_odd (e3 (π ⟨_, hyI⟩)) with h3 | h2
    · right
      rw [← map_pow, ← map_pow] at h3
      have h := (hπ1 _).1 (e3.injective (h3.trans (map_one e3).symm))
      rw [← map_pow, piQ_eq_one_iff]
      simpa using h
    · left
      refine ⟨1, ?_⟩
      rw [← map_pow, ← map_pow] at h2
      have h := (hπ1 _).1 (e3.injective (h2.trans (map_one e3).symm))
      rw [← map_pow, piQ_eq_one_iff]
      simpa using h

@[expose] noncomputable def toHyp1321 (hF956 : A5.StmtF956i) {v : G} (hv : v ∈ V)
    (hvQ : v ∉ pCoreOf 2 H) (K : Subgroup (Hstar H)) (hK : IsComponentOf K ⊤)
    (hKb : ∃ k ∈ K, k * piQ H ⟨v, S.V_le_H hv⟩ ≠ piQ H ⟨v, S.V_le_H hv⟩ * k) :
    A5.Hyp1321 (Hstar H) S.Ut where
  ρ := S.rhoA
  inj := S.rhoA_injective
  sq := S.ut_sq
  sqtk := S.sqtkHyp_Hstar
  K := K
  comp := hK
  b := piQ H ⟨v, S.V_le_H hv⟩
  b2 := S.piQ_v_sq' hv
  bN := S.mem_normalizer_component hv hvQ hK
  bc := hKb
  D := S.Vt3
  hD := S.rhoA_comm_mem_Vt3 hv hvQ
  hD4 := S.card_Vt3
  syl := ⟨Tstar T H ⊓ K, L246C127.isSylowTwoOf_inf_of_isSubnormal' hK.2.1 S.isSylowTwoOf_Tstar,
    fun _ hs => S.comm_Tstar hv hvQ hs.1⟩
  pair := S.pair_Hstar hF956 hv

@[expose] noncomputable def toHypY (hF956 : A5.StmtF956i) (h38 : A38ForSQTK) {v : G}
    (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) (K : Subgroup (Hstar H)) (hK : IsComponentOf K ⊤)
    (hKb : ∃ k ∈ K, k * piQ H ⟨v, S.V_le_H hv⟩ ≠ piQ H ⟨v, S.V_le_H hv⟩ * k) {Y : Subgroup G}
    (SY : A5SitY S Y) (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G))) :
    A5.HypY (S.toHyp1321 hF956 hv hvQ K hK hKb) where
  L := imQ H Y
  normK := S.imQ_le_normalizer h38 SY.Y_le_H SY.oTwoRes_eq hK
  comm := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := (mem_imQ SY.Y_le_H).mp hl
    exact (S.piQ_V_comm_Y SY hv hy).symm
  solv := by
    have := isSolvable_of_decomp SY.c_mem SY.decomp
    let f : ↥Y →* ↥(imQ H Y) :=
      { toFun := fun y => ⟨piQ H ⟨y, SY.Y_le_H y.2⟩, (mem_imQ SY.Y_le_H).mpr ⟨y, y.2, rfl⟩⟩
        map_one' := Subtype.ext (map_one (piQ H))
        map_mul' := fun a c => Subtype.ext (by
          show piQ H _ = piQ H _ * piQ H _
          rw [← map_mul]
          rfl) }
    refine Group.isSolvable_of_surjective (f := f) ?_
    rintro ⟨α, hα⟩
    obtain ⟨y, hy, rfl⟩ := (mem_imQ SY.Y_le_H).mp hα
    exact ⟨⟨y, hy⟩, rfl⟩
  res := imQ_le_oTwoRes SY.Y_le_H SY.oTwoRes_eq
  noncent := by
    obtain ⟨l, hl, k, hk, hlk⟩ := S.not_centralizes_Y SY h1519 hv hvQ hK hKb
    exact ⟨_, (mem_imQ SY.Y_le_H).mpr ⟨l, hl, rfl⟩, k, hk, hlk⟩
  normC := by
    intro k _ hkb l hl
    obtain ⟨g, rfl⟩ := piQ_surjective H k
    obtain ⟨y, hy, rfl⟩ := (mem_imQ SY.Y_le_H).mp hl
    have hgV := S.mem_normalizer_V_of_comm hv hvQ g.2 hkb
    have hgY := SY.normalizer_le hgV
    have hyy : (g : G) * y * (g : G)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgY y).mp hy
    refine (mem_imQ SY.Y_le_H).mpr ⟨_, hyy, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

@[expose] noncomputable def toHypL1 (hF956 : A5.StmtF956i) (h38 : A38ForSQTK) {v : G}
    (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) (K : Subgroup (Hstar H)) (hK : IsComponentOf K ⊤)
    (hKb : ∃ k ∈ K, k * piQ H ⟨v, S.V_le_H hv⟩ ≠ piQ H ⟨v, S.V_le_H hv⟩ * k)
    (h3 : ∀ l ∈ L₁, l ^ 3 ∈ pCoreOf 2 L₁) :
    A5.HypL1 (S.toHyp1321 hF956 hv hvQ K hK hKb) where
  L := imQ H L₁
  normK := S.imQ_le_normalizer h38 S.L1_le_H S.oTwoRes_L1 hK
  comm := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := (mem_imQ S.L1_le_H).mp hl
    exact (S.piQ_V_comm_L1 hv hl0).symm
  res := imQ_le_oTwoRes S.L1_le_H S.oTwoRes_L1
  three := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro l hl m hm hlm
    obtain ⟨l0, hl0, rfl⟩ := (mem_imQ S.L1_le_H).mp hl
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L₁ ⟨_, h3 l0 hl0⟩
    have h2 : (piQ H ⟨l0, S.L1_le_H hl0⟩ ^ 3) ^ 2 ^ k = 1 := by
      rw [← map_pow, ← map_pow]
      have : ((⟨l0, S.L1_le_H hl0⟩ : ↥H) ^ 3) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have hm3 : (piQ H ⟨l0, S.L1_le_H hl0⟩ ^ 3) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hlm, one_pow]
    have h4 : orderOf (piQ H ⟨l0, S.L1_le_H hl0⟩ ^ 3) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hm3)
    rw [Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm), Nat.dvd_one,
      orderOf_eq_one_iff] at h4
    exact h4
  Dinv := by
    intro l hl d hd
    obtain ⟨l0, hl0, rfl⟩ := (mem_imQ S.L1_le_H).mp hl
    obtain ⟨u, hu, rfl⟩ := hd
    have hu' : (u : G) ∈ V₃ := hu
    have hN : l0 ∈ Subgroup.normalizer (V₃ : Set G) :=
      S.hF.L₁T_normalizes_Vp (le_sup_left (a := L₁Of S.L V₁) (S.L1_eq ▸ hl0))
    have hmem : l0 * u * l0⁻¹ ∈ conjClosure V₃ H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H (S.L1_le_H hl0)) u).mp
        u.2
    show S.rhoA (piQ H ⟨l0, S.L1_le_H hl0⟩) (S.utMk u) ∈ S.Vt3
    rw [S.rhoA_mk ⟨l0, S.L1_le_H hl0⟩ u ⟨_, hmem⟩ rfl]
    exact ⟨⟨_, hmem⟩, (Subgroup.mem_normalizer_iff.mp hN u).mp hu', rfl⟩
  Dnt := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hle : ⁅V₃, L₁⁆ ≤ V₁ := by
      rw [Subgroup.commutator_le]
      intro d hd l0 hl0
      have hdU : d ∈ conjClosure V₃ H := le_conjClosure V₃ H hd
      have hmem : l0 * d * l0⁻¹ ∈ conjClosure V₃ H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H (S.L1_le_H hl0)) d).mp
          hdU
      have h1 : S.rhoA (piQ H ⟨l0, S.L1_le_H hl0⟩) (S.utMk ⟨d, hdU⟩) = S.utMk ⟨d, hdU⟩ :=
        hall _ ((mem_imQ S.L1_le_H).mpr ⟨l0, hl0, rfl⟩) (S.utMk ⟨d, hdU⟩) ⟨⟨d, hdU⟩, hd, rfl⟩
      rw [S.rhoA_mk ⟨l0, S.L1_le_H hl0⟩ ⟨d, hdU⟩ ⟨_, hmem⟩ rfl, ← div_eq_one, ← map_div,
        S.utMk_eq_one_iff] at h1
      have h2 : l0 * d * l0⁻¹ * d⁻¹ ∈ V₁ := by simpa [div_eq_mul_inv] using h1
      have h3' := V₁.inv_mem h2
      rw [commutatorElement_def]
      simpa [mul_assoc] using h3'
    rw [S.commutator_V3_L1] at hle
    have := Subgroup.card_le_of_le hle
    rw [S.card_V3, S.card_V1] at this
    omega

end A5Sit

end CFSG.Quasithin.H13
