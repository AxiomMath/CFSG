module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_lift_of_fixed {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hb3 : b ^ 3 = 1) {y : L ⧸ aschbacherSolvableCore 3 L}
    (hy : thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hbN⟩) y = y) :
    ∃ l : L, b * (l : G) = l * b ∧ (l : L ⧸ aschbacherSolvableCore 3 L) = y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set n : N := ⟨b, hbN⟩ with hn
  set Z := Subgroup.zpowers n with hZ
  have hn3 : n ^ 3 = 1 := Subtype.ext (by simp [hn, hb3])
  have hZ3 : IsPGroup 3 Z := by
    rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn3, one_zpow]
  set α : Z →* MulAut L := L.normalizerMonoidHom.comp Z.subtype with hα
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hfixk : ∀ k : ℤ, thetaQuotMulAut L (L.normalizerMonoidHom (n ^ k))
      (l₀ : L ⧸ aschbacherSolvableCore 3 L) = (l₀ : L ⧸ aschbacherSolvableCore 3 L) := by
    intro k
    rw [map_zpow, map_zpow]
    have h1 : ∀ m : ℕ, (thetaQuotMulAut L (L.normalizerMonoidHom n) ^ m)
        (l₀ : L ⧸ aschbacherSolvableCore 3 L) = (l₀ : L ⧸ aschbacherSolvableCore 3 L) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
    rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast]
      exact h1 m
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← h1 m]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hinv : ∀ a : Z, ∀ x : L, x * l₀⁻¹ ∈ aschbacherSolvableCore 3 L →
      α a x * l₀⁻¹ ∈ aschbacherSolvableCore 3 L := by
    rintro ⟨a, ha⟩ x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hxl : (x : L ⧸ aschbacherSolvableCore 3 L) = (l₀ : L ⧸ aschbacherSolvableCore 3 L) :=
      QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
    have h3 := hfixk k
    rw [← hxl, thetaQuotMulAut_mk] at h3
    rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
    rw [← hxl]
    exact h3
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hZ3 α
    (aschbacherSolvableCore 3 L) three_not_dvd_card_aschbacherSolvableCore l₀).1 hinv
  refine ⟨c, ?_, ?_⟩
  · have h1 := congrArg (fun x : L => (x : G)) (hcfix ⟨n, Subgroup.mem_zpowers n⟩)
    simp only [hα, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [Sec4.normalizerMonoidHom_apply_coe] at h1
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [h1]
  · exact QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])

end Lift

theorem commute_of_isCyclic_two {M : Type*} [Group M] {V : Subgroup M} [Finite V]
    (hV2 : IsPGroup 2 V) (hVc : IsCyclic V) {s : M} (hs : ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hs3 : s ^ 3 = 1) : ∀ v ∈ V, s * v = v * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsss : s * s * s = 1 := by rw [← hs3, pow_three, mul_assoc]
  have hsN : s ∈ Subgroup.normalizer (V : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hs v, fun hv => ?_⟩
    have h1 := hs _ (hs _ hv)
    have h2 : s * (s * (s * v * s⁻¹) * s⁻¹) * s⁻¹ = v := by
      calc s * (s * (s * v * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * v * (s * s * s)⁻¹ := by group
        _ = v := by rw [hsss]; group
    rwa [h2] at h1
  set σ := V.normalizerMonoidHom ⟨s, hsN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨s, hsN⟩ : Subgroup.normalizer (V : Set M)) ^ 3 = 1 :=
      Subtype.ext (by simp [hs3])
    rw [this, map_one]
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    have h2 : orderOf σ ∣ Nat.card (MulAut V) := orderOf_dvd_natCard σ
    rw [IsCyclic.card_mulAut V] at h2
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk] at h2
    have hcop : Nat.Coprime 3 (Nat.totient (2 ^ k)) := by
      rcases k with _ | k
      · simp
      · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
        norm_num
        exact Nat.Coprime.pow_right _ (by norm_num)
    have h3 : orderOf σ ∣ Nat.gcd 3 (Nat.totient (2 ^ k)) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  intro v hv
  have h1 := congrArg (fun τ : MulAut V => ((τ ⟨v, hv⟩ : V) : M)) hσ1
  simp only [hσ, MulAut.one_apply] at h1
  rw [Sec4.normalizerMonoidHom_apply_coe] at h1
  calc s * v = s * v * s⁻¹ * s := by group
    _ = v * s := by rw [h1]

section Theta

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_range_conj_of_mem_sup {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hg : g ∈ L ⊔ thetaQuotCentralizer L) :
    thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgN⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range := by
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set φ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set M : Subgroup G := (((MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range).comap
    φ).map N.subtype with hM
  have hLM : L ≤ M := by
    intro l hl
    refine ⟨⟨l, Subgroup.le_normalizer hl⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have h1 : φ ⟨l, Subgroup.le_normalizer hl⟩ =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩) :=
      KFacts.thetaQuotMulAut_compAction_of_mem hl _
    rw [h1]
    exact ⟨_, rfl⟩
  have hCM : thetaQuotCentralizer L ≤ M := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c, Subgroup.mem_comap.mpr ?_, rfl⟩
    have h1 : φ c = 1 := MonoidHom.mem_ker.mp hc
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨v, hv, hvg⟩ := (sup_le hLM hCM) hg
  have : v = ⟨g, hgN⟩ := Subtype.ext hvg
  rw [← this]
  exact hv

theorem conj_mem_sup_thetaQuotCentralizer {n g : G} (hn : n ∈ Subgroup.normalizer (L : Set G))
    (hg : g ∈ L ⊔ thetaQuotCentralizer L) : n * g * n⁻¹ ∈ L ⊔ thetaQuotCentralizer L := by
  have hLn : L.map (MulAut.conj n).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hCn : (thetaQuotCentralizer L).map (MulAut.conj n).toMonoidHom = thetaQuotCentralizer L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L hn)
  have h1 : n * g * n⁻¹ ∈ (L ⊔ thetaQuotCentralizer L).map (MulAut.conj n).toMonoidHom :=
    ⟨g, hg, rfl⟩
  rwa [Subgroup.map_sup, hLn, hCn] at h1

theorem innThetaNoncyclic_of (hL : L ∈ thetaComponents 3 G) {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1) {A U : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (hUN : U ≤ Subgroup.normalizer (L : Set G)) (hUs : U ≤ L ⊔ thetaQuotCentralizer L)
    (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUA : ⁅U, A⁆ = U)
    (hUC : ¬ U ≤ thetaQuotCentralizer L)
    (hUθ : U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))) :
    InnThetaNoncyclic (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hbN⟩)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _hL := hL
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Q := L ⧸ aschbacherSolvableCore 3 L with hQ
  set φ : N →* MulAut Q := (thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set Θ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) with hΘ
  set Wg : Subgroup G := Θ ⊓ (L ⊔ thetaQuotCentralizer L) with hWg
  have hsupN : L ⊔ thetaQuotCentralizer L ≤ N :=
    sup_le Subgroup.le_normalizer (Sec6.thetaQuotCentralizer_le_normalizer L)
  have hWgN : Wg ≤ N := inf_le_right.trans hsupN
  set W := (Wg.subgroupOf N).map φ with hW
  set V := (U.subgroupOf N).map φ with hV
  obtain ⟨hΘs, hΘ3⟩ := Item422Proof.inSubgroup_theta_solvable_coprime
    (Subgroup.centralizer ({b} : Set G))
  have hUWg : U ≤ Wg := le_inf hUθ hUs
  have hcardW : Nat.card W ∣ Nat.card Θ := by
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWgN).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hfin : Finite (MulAut Q) := Finite.of_injective (fun σ : MulAut Q => (σ : Q → Q))
    (fun σ τ h => MulEquiv.ext (congrFun h))
  refine ⟨W, V, ?_, fun h => hΘ3 (h.trans hcardW), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have := hΘs
    have hWs : Group.IsSolvable (Wg.subgroupOf N) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_left : Wg ≤ Θ)).comp
          (Subgroup.subgroupOfEquivOfLe hWgN).toMonoidHom)
        ((Subgroup.inclusion_injective (inf_le_left : Wg ≤ Θ)).comp
          (Subgroup.subgroupOfEquivOfLe hWgN).injective)
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective (Wg.subgroupOf N))
  ·
    rintro _ ⟨g, hg, rfl⟩
    exact mem_range_conj_of_mem_sup g.2 (Subgroup.mem_subgroupOf.mp hg).2
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgb : (g : G) * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.theta_le _ (Subgroup.mem_subgroupOf.mp hg).1)
    have h1 : (⟨b, hbN⟩ : N) * g = g * ⟨b, hbN⟩ := Subtype.ext hgb.symm
    change φ ⟨b, hbN⟩ * φ g = φ g * φ ⟨b, hbN⟩
    rw [← map_mul, h1, map_mul]
  ·
    intro y hy
    obtain ⟨l, hlb, rfl⟩ := exists_lift_of_fixed hbN hb3 hy
    have hlN : (l : G) ∈ N := Subgroup.le_normalizer l.2
    have hconj : MulAut.conj (l : Q) = φ ⟨l, hlN⟩ := by
      change _ = thetaQuotMulAut L (compAction L ⟨l, hlN⟩)
      rw [KFacts.thetaQuotMulAut_compAction_of_mem l.2]
      rfl
    rintro _ ⟨g, hg, rfl⟩
    rw [hconj, ← map_inv, ← map_mul, ← map_mul]
    obtain ⟨hgΘ, hgS⟩ := Subgroup.mem_subgroupOf.mp hg
    have hlC : (l : G) ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hlb.symm
    have hmemG : (l : G) * g * (l : G)⁻¹ ∈ Wg :=
      ⟨(Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta _ hlC) g).mp hgΘ,
        conj_mem_sup_thetaQuotCentralizer hlN hgS⟩
    have hmem : (⟨l, hlN⟩ : N) * g * (⟨l, hlN⟩ : N)⁻¹ ∈ Wg.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hmemG
    exact Subgroup.mem_map_of_mem φ hmem
  ·
    exact Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
      (hUWg (Subgroup.mem_subgroupOf.mp hu))
  ·
    exact (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm).map φ
  ·
    intro hcyc
    have hVfin : Finite V := inferInstance
    apply hUC
    rw [← hUA, Subgroup.commutator_le]
    intro u hu x hx
    have huN := hUN hu
    have hxN := hAN hx
    have hcomm := commute_of_isCyclic_two (V := V)
      ((hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm).map φ) hcyc
      (s := φ ⟨x, hxN⟩) (by
        rintro _ ⟨u', hu', rfl⟩
        refine ⟨⟨x, hxN⟩ * u' * ⟨x, hxN⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hAU hx) u').mp (Subgroup.mem_subgroupOf.mp hu')
        · rw [map_mul, map_mul, map_inv])
      (by
        rw [← map_pow]
        have : (⟨x, hxN⟩ : N) ^ 3 = 1 := Subtype.ext (by simp [hA3 x hx])
        rw [this, map_one])
      (φ ⟨u, huN⟩) ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have hmem : ⁅u, x⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem huN hxN) (N.inv_mem huN)) (N.inv_mem hxN)
    refine ⟨⟨⁅u, x⁆, hmem⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have he : (⟨⁅u, x⁆, hmem⟩ : N) = ⁅(⟨u, huN⟩ : N), ⟨x, hxN⟩⁆ := Subtype.ext rfl
    change φ ⟨⁅u, x⁆, hmem⟩ = 1
    rw [he, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm


theorem mem_thetaQuotCentralizer_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    z ∈ thetaQuotCentralizer L := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, fun l _ => ?_⟩
  · exact Subgroup.centralizer_le_normalizer _ (Subgroup.center_le_centralizer _ hz)
  · rw [← Subgroup.mem_center_iff.mp hz l, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem mem_thetaQuotCentralizer_iff_zpowers {A : Subgroup G} {a : G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (h9 : Nat.card (autThetaQuot A L) = 9) :
    ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a := by
  classical
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set φ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set φA : A →* MulAut (L ⧸ aschbacherSolvableCore 3 L) := φ.comp (Subgroup.inclusion hAN)
    with hφA
  have hrange : φA.range = autThetaQuot A L := by
    ext τ
    rw [mem_autThetaQuot_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hAN x.2, x.2, rfl⟩
    · rintro ⟨h, hN, hA, rfl⟩
      exact ⟨⟨h, hA⟩, rfl⟩
  have hker : ∀ x : A, x ∈ φA.ker ↔ (x : G) ∈ thetaQuotCentralizer L := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact ⟨⟨x, hAN x.2⟩, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hAN x.2⟩ := Subtype.ext hyx
      rw [this] at hy
      exact hy
  have hcardker : Nat.card φA.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φA.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φA).toEquiv, hrange, h9, h27] at h1
    omega
  have haker : (⟨a, haA⟩ : A) ∈ φA.ker := (hker _).mpr (mem_thetaQuotCentralizer_of_mem_center haZ)
  have hzker : Subgroup.zpowers (⟨a, haA⟩ : A) = φA.ker := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haker) ?_
    rw [hcardker, Nat.card_zpowers, Subgroup.orderOf_mk, ha3]
  intro y hy
  rw [← hker ⟨y, hy⟩, ← hzker, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem orderOf_psi_eq_three {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hb3 : b ^ 3 = 1) (hbC : b ∉ thetaQuotCentralizer L) :
    orderOf (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hbN⟩)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ fun h => hbC ⟨⟨b, hbN⟩, h, rfl⟩
  rw [← map_pow, ← map_pow]
  have : (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simp [hb3])
  rw [this, map_one, map_one]

theorem inducesOuterTheta_iff {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    InducesOuterTheta x L ↔ thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) ∉
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

end Theta

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
