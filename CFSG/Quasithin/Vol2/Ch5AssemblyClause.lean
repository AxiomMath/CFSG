module

import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
import CFSG.Sporadic.Schreier.M23Gens
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.Timmesfeld.Final.Simple
import CFSG.Quasithin.Vol2.Ch5Sec1Basic
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Simple

variable {Q S : Type*} [Group Q] [Group S]

theorem exists_mul_ne_mul_of_not_prime [IsSimpleGroup S] (h : ¬ (Nat.card S).Prime) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra hc
  have hc' : ∀ a b : S, a * b = b * a := fun a b => by
    by_contra hab
    exact hc ⟨a, b, hab⟩
  let _ : CommGroup S := { (inferInstance : Group S) with mul_comm := hc' }
  exact h (IsSimpleGroup.prime_card (α := S))

theorem isPerfect_of_mulEquiv (e : Q ≃* S) [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect Q := by
  have : IsSimpleGroup Q := e.isSimpleGroup
  rw [Group.isPerfect_def]
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator Q) with h | h
  · exfalso
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hc := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top (e.symm a))) (e.symm b)
      (Subgroup.mem_top _)
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hc.symm
  · exact h

end Simple

theorem a7_not_comm : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    by decide⟩

theorem m23_not_comm : ∃ a b : NativeSporadic.M23, a * b ≠ b * a :=
  ⟨CFSG.Sporadic.Schreier.m23GenA, CFSG.Sporadic.Schreier.m23GenB, by decide⟩

theorem j2_not_comm' : ∃ a b : NativeSporadic.J2, a * b ≠ b * a := by
  have := CFSG.Sporadic.J2.isSimpleGroup_J2
  refine exists_mul_ne_mul_of_not_prime ?_
  rw [CFSG.Sporadic.J2.card_J2]
  intro hp
  have := hp.eq_one_or_self_of_dvd 2 ⟨302400, rfl⟩
  omega

section CComp

variable {G : Type} [Group G]

theorem mem_cComp_of_normal_of_simple [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (hn : (X.subgroupOf Y).Normal) (hX : ⁅X, X⁆ = X)
    (hs : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X)) : quasithinIsCComponent X Y := by
  refine ⟨?_, hX, A3.subnormal_of_normal hXY hn, ?_⟩
  · intro h
    subst h
    have hss : Subsingleton (↥(⊥ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊥ : Subgroup G)) :=
      ⟨fun a b => by
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        congr 1
        exact Subsingleton.elim _ _⟩
    exact not_nontrivial_iff_subsingleton.mpr hss hs.toNontrivial
  · intro K hKX hK hKp hKsub
    have hpc := CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥X
    have hKX' : IsSubnormal K X := A3.subnormal_of_le_of_le hKsub hKX.le hXY
    obtain ⟨P, hPX, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKX' hKX
    have : (P.subgroupOf X).Normal := hPn
    have hNs : Group.IsSolvable ↥(pCoreOf 2 X) := isSolvable_pCoreOf_two X
    rcases Subgroup.Normal.eq_bot_or_eq_top
        ((P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with h | h
    ·
      have hPN : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
        exact h
      have hKO : K ≤ pCoreOf 2 X := by
        intro k hk
        have hkX : k ∈ X := hKX.le hk
        exact ⟨⟨k, hkX⟩, hpc ▸ hPN (show (⟨k, hkX⟩ : ↥X) ∈ P.subgroupOf X from hKP hk), rfl⟩
      have hKs : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKO)
          (Subgroup.inclusion_injective hKO)
      have := (isSolvable_iff_perfectCore_eq_bot K).mp hKs
      rw [perfectCore_eq_self_of_perfect hKp] at this
      exact hK this
    ·
      have hXeq : X = P ⊔ pCoreOf 2 X := by
        refine le_antisymm ?_ (sup_le hPX.le (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
        intro x hx
        have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ ∈
            (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
          rw [h]; exact Subgroup.mem_top _
        obtain ⟨p, hp, hpx⟩ := hmem
        have hpn : p⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := QuotientGroup.eq.mp hpx
        have hx' : x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
        rw [hx']
        exact Subgroup.mul_mem_sup hp ⟨p⁻¹ * ⟨x, hx⟩, hpc ▸ hpn, rfl⟩
      have hle := perfectCore_le_of_sup_solvable hPX.le hPn hXeq hNs
      rw [perfectCore_eq_self_of_perfect hX] at hle
      exact hPX.not_ge hle

theorem oThreePrimeResidual_le (X : Subgroup G) : oThreePrimeResidual X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oThreePrimeResidual_normal (X : Subgroup G) :
    ((oThreePrimeResidual X).subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oThreePrimeResidual_le X), oThreePrimeResidual,
    Subgroup.le_normalizer_closure_iff]
  rintro h hh g ⟨hg, k, hk⟩
  refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hh hg) (X.inv_mem hh), k, ?_⟩
  rw [conj_pow, hk, mul_one, mul_inv_cancel]

theorem perfect_oThreePrimeResidual [Finite G] (X : Subgroup G)
    (hQ : Group.IsPerfect (↥(oThreePrimeResidual X) ⧸ CFSG.pCore 2 ↥(oThreePrimeResidual X))) :
    ⁅oThreePrimeResidual X, oThreePrimeResidual X⁆ = oThreePrimeResidual X := by
  refine le_antisymm (A3.commutator_self_le _) ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := oThreePrimeResidual X with hR
  set D : Subgroup ↥R := commutator ↥R with hD
  set N : Subgroup ↥R := CFSG.pCore 2 ↥R with hN
  have hDN : D ⊔ N = ⊤ := by
    have h1 : D.map (QuotientGroup.mk' N) = ⊤ := by
      rw [hD, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' N) D
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  have hP : IsPGroup 2 (↥R ⧸ D) := by
    have hNm : N.map (QuotientGroup.mk' D) = ⊤ := by
      have h3 := Subgroup.map_sup D N (QuotientGroup.mk' D)
      rw [hDN, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D),
        QuotientGroup.map_mk'_self, bot_sup_eq] at h3
      exact h3.symm
    have h4 : IsPGroup 2 ↥(N.map (QuotientGroup.mk' D)) :=
      (CFSG.pCore_isPGroup (G := ↥R) (p := 2)).map _
    intro y
    obtain ⟨k, hk⟩ := h4 ⟨y, by rw [hNm]; exact Subgroup.mem_top _⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgen : ∀ g ∈ {x | x ∈ X ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1}, g ∈ ⁅R, R⁆ := by
    rintro g ⟨hgX, k, hk⟩
    have hgR : g ∈ R := Subgroup.subset_closure ⟨hgX, k, hk⟩
    obtain ⟨m, hm⟩ := hP (QuotientGroup.mk' D ⟨g, hgR⟩)
    have h3 : (QuotientGroup.mk' D ⟨g, hgR⟩) ^ (3 ^ k) = 1 := by
      rw [← map_pow]
      have : (⟨g, hgR⟩ : ↥R) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have hord : orderOf (QuotientGroup.mk' D ⟨g, hgR⟩) = 1 := by
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hm)
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 3 2)),
        Nat.dvd_one] at hd
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨⟨g, hgR⟩, hord, rfl⟩
  exact (Subgroup.closure_le _).mpr hgen

end CComp

section Clause

variable {G : Type} [Group G]

theorem centralizerComponentClause_of_KZ
    [Finite G] {T H : Subgroup G}
    (hK : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2)
    (hle : oTwoUpper H ≤
      oThreePrimeResidual (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
    (hKZ : Nonempty (O2Q (oThreePrimeResidual
          (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃*
            alternatingGroup (Fin 7)) ∨
        Nonempty (O2Q (oThreePrimeResidual
          (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃* NativeSporadic.J2) ∨
        Nonempty (O2Q (oThreePrimeResidual
          (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ≃* NativeSporadic.M23)) :
    CentralizerComponentClause T H := by
  set C := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hC
  set KZ := oThreePrimeResidual C with hKZdef
  have key : ∀ (S : Type) [Group S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      Nonempty (O2Q KZ ≃* S) → quasithinIsCComponent KZ C ∧ CFSG.IsQuasisimple (O2Q KZ) := by
    intro S _ _ hnab ⟨e⟩
    have : IsSimpleGroup (O2Q KZ) := e.isSimpleGroup
    have : Group.IsPerfect (O2Q KZ) := isPerfect_of_mulEquiv e hnab
    have hperf : ⁅KZ, KZ⁆ = KZ := perfect_oThreePrimeResidual C this
    exact ⟨mem_cComp_of_normal_of_simple (oThreePrimeResidual_le C) (oThreePrimeResidual_normal C)
      hperf ‹_›, isQuasisimple_of_isSimpleGroup_of_isPerfect⟩
  have hA5 := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hK
  rcases hKZ with h | h | h
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    obtain ⟨h1, h2⟩ := key (alternatingGroup (Fin 7)) a7_not_comm h
    exact ⟨KZ, h1, hle, h2, Or.inl ⟨hA5, Or.inl h⟩⟩
  · have := CFSG.Sporadic.J2.isSimpleGroup_J2
    obtain ⟨h1, h2⟩ := key NativeSporadic.J2 j2_not_comm' h
    exact ⟨KZ, h1, hle, h2, Or.inl ⟨hA5, Or.inr (Or.inl h)⟩⟩
  · have := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    obtain ⟨h1, h2⟩ := key NativeSporadic.M23 m23_not_comm h
    exact ⟨KZ, h1, hle, h2, Or.inl ⟨hA5, Or.inr (Or.inr h)⟩⟩

theorem omegaOneCenter_le (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le T).mpr fun _ hz => (Subgroup.mem_inf.mp hz.1).1

theorem le_centralizer_omegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mpr
    ((Subgroup.closure_le _).mpr fun _ hz => (Subgroup.mem_inf.mp hz.1).2)

theorem omegaOneCenter_le_pCoreOf [Finite G] {T X : Subgroup G} (hT : IsPGroup 2 T)
    (hZX : quasithinOmegaOneCenter T ≤ X)
    (hXC : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 X := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZX ?_
    (hT.to_le (omegaOneCenter_le T))
  rw [Subgroup.le_set_normalizer_iff]
  intro x hx z hz
  rw [← Subgroup.mem_centralizer_iff.mp (hXC hx) z hz, mul_inv_cancel_right]
  exact hz

theorem omegaOneCenter_ne_bot [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hc := hT.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center T) := hT.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center T) := by
    rcases hcp.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton_iff_nontrivial.mpr hc)
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  intro h0
  have hzZ : ((z : T) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(z : T).2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
      exact congrArg Subtype.val this
    · rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  rw [h0, Subgroup.mem_bot] at hzZ
  have : orderOf ((z : T) : G) = 1 := by rw [hzZ, orderOf_one]
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz] at this
  exact absurd this (by norm_num)

theorem centralizerComponentClause_of_L34
    [Finite G] (h39 : Vol2Native.A39ForSQTKCat)
    {T M L H : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hK : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2)
    (hmax : quasithinIsMaximalLocal T (oTwoUpper H))
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) : CentralizerComponentClause T H := by
  have : IsSimpleGroup G := hyp.simple
  have hTC := le_centralizer_omegaOneCenter T
  have hHC : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH)
  have hKC := (oTwoUpper_le H).trans hHC
  have hTne : T ≠ ⊥ := by
    intro hT0
    apply hyp.faithful.1.2.2.2
    have hle : pCoreOf 2 (L ⊔ T) ≤ T :=
      (hyp.isSylowTwoOf le_sup_right).le_of_normalizes
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        (Subgroup.le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ T)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact le_bot_iff.mp (hle.trans hT0.le)
  have hZne := omegaOneCenter_ne_bot hyp.sylow.1 hTne
  have hZC := (omegaOneCenter_le T).trans hTC
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hCO : pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≠ ⊥ :=
    fun h0 => hZne (le_bot_iff.mp (h0 ▸ omegaOneCenter_le_pCoreOf hyp.sylow.1 hZC le_rfl))
  obtain ⟨L', hL', hKL'⟩ := Vol2Native.lemma_1_2_4_exists hloc Vol2Native.a37ForSQTKCat_proved h39
    hCO (hyp.isSylowTwoOf hTC) hKC hmax.1.2.1
  have hL'C := le_of_mem_cComp hL'
  have hlocal : quasithinIsLocal T L' := by
    refine ⟨hyp.sylow.1, cComp_mem_of_le hL' le_sup_left (sup_le hL'C hTC),
      (hyp.isSylowTwoOf le_sup_right).2.2, fun h0 => hZne (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact omegaOneCenter_le_pCoreOf hyp.sylow.1 ((omegaOneCenter_le T).trans le_sup_right)
      (sup_le hL'C hTC)
  have hL'K : L' = oTwoUpper H := hmax.2 L' hlocal hKL'
  rw [hL'K] at hL'
  have : IsSimpleGroup (O2Q (oTwoUpper H)) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK
  have : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL')
  have : Group.IsPerfect (O2Q (oTwoUpper H)) := inferInstance
  exact ⟨oTwoUpper H, hL', le_rfl, isQuasisimple_of_isSimpleGroup_of_isPerfect,
    Or.inr (Or.inl ⟨rfl, hK⟩)⟩

theorem centralizerComponentClause_of_3D4
    [Finite G] {T H : Subgroup G}
    (hK : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 3)
    (hle : oTwoUpper H ≤
      oThreePrimeResidual (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
    (hKZ : Is3D4 2 1 (O2Q (oThreePrimeResidual
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))))) :
    CentralizerComponentClause T H := by
  set C := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hC
  set KZ := oThreePrimeResidual C with hKZdef
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_3d4_simplicity _ 2 1 hKZ
  have hc : Nat.card (O2Q KZ) = 211341312 := by
    have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hKZ
    norm_num [CFSG.Open.ordTrialityD4] at h1
    exact h1
  have hnab : ∃ a b : O2Q KZ, a * b ≠ b * a := by
    refine exists_mul_ne_mul_of_not_prime ?_
    rw [hc]
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 ⟨105670656, rfl⟩
    omega
  have : Group.IsPerfect (O2Q KZ) := isPerfect_of_mulEquiv (MulEquiv.refl _) hnab
  have hperf : ⁅KZ, KZ⁆ = KZ := perfect_oThreePrimeResidual C this
  exact ⟨KZ, mem_cComp_of_normal_of_simple (oThreePrimeResidual_le C)
    (oThreePrimeResidual_normal C) hperf hs, hle, isQuasisimple_of_isSimpleGroup_of_isPerfect,
    Or.inr (Or.inr ⟨hK, hKZ⟩)⟩

end Clause

end CFSG.Quasithin.H13
