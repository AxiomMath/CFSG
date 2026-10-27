module

public import CFSG.RankThree.S4Free.Stellmacher24Ext
public import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs
import CFSG.CGT.T75M.SzOut
import CFSG.Blueprint.SourceSuzukiTransport
import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs

public section

namespace CFSG.RankThree.S4Free

open CFSG.Blueprint Subgroup
open scoped commutatorElement

namespace Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K] {X : Type*} [Group X]

theorem le_normalizer_of_sylow_le (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) (S : Sylow 2 X)
    {U : Subgroup X} (hSU : (S : Subgroup X) ≤ U) (hU : U ≠ ⊤) :
    U ≤ normalizer ((S : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  by_contra hle
  obtain ⟨u, huU, huN⟩ := Set.not_subset.mp hle
  set S' : Sylow 2 X := u • S with hS'
  have hS'U : ((S' : Sylow 2 X) : Subgroup X) ≤ U := Sylow.smul_le hSU ⟨u, huU⟩
  have hS'S : S' ≠ S := fun h => huN (Sylow.smul_eq_iff_mem_normalizer.mp h)
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardSyl : Nat.card (Sylow 2 X) = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    have h1 := card_mul_index (normalizer ((S : Subgroup X) : Set X))
    rw [card_normalizer_sylow hK e S, Nat.card_congr e.toEquiv,
      CFSG.LieType.Ree.suzuki_order hK] at h1
    rw [Sylow.card_eq_index_normalizer S]
    have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
      Nat.mul_pos (by positivity) (by omega)
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hfree : ∀ Q : Sylow 2 X, Q ≠ S → ∀ s : (S : Subgroup X), s • Q = Q → s = 1 := by
    intro Q hQ s hs
    have h1 : (s : X) ∈ (S : Subgroup X) ⊓ normalizer (Q : Set X) :=
      ⟨s.2, Sylow.smul_eq_iff_mem_normalizer.mp hs⟩
    rw [S.isPGroup'.inf_normalizer_sylow Q, inf_eq_bot_of_sylow_ne hK e (Ne.symm hQ)] at h1
    exact Subtype.ext (mem_bot.mp h1)
  have horbit : ∀ Q : Sylow 2 X, Q ≠ S → Q ∈ MulAction.orbit (S : Subgroup X) S' := by
    have hsub : MulAction.orbit (S : Subgroup X) S' ⊆ {S}ᶜ := by
      rintro _ ⟨s, rfl⟩ hsS
      apply hS'S
      have hsS' : s • S' = S := Set.mem_singleton_iff.mp hsS
      have h1 : S' = s⁻¹ • (s • S') := (inv_smul_smul s S').symm
      rw [h1, hsS']
      exact Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer (s⁻¹).2)
    have hcard1 : (MulAction.orbit (S : Subgroup X) S').ncard = (2 ^ (2 * a + 1)) ^ 2 := by
      have hst : MulAction.stabilizer (S : Subgroup X) S' = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        exact mem_bot.mpr (hfree S' hS'S s hs)
      rw [← MulAction.index_stabilizer, hst, index_bot, (card_sylow_and_center ha hK e S).1]
    have hcard2 : ({S}ᶜ : Set (Sylow 2 X)).ncard = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [Set.compl_eq_univ_diff, Set.ncard_diff_singleton_of_mem (Set.mem_univ S),
        Set.ncard_univ, hcardSyl, Nat.add_sub_cancel]
    have heq : MulAction.orbit (S : Subgroup X) S' = {S}ᶜ :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2, hcard1]) (Set.toFinite _)
    intro Q hQ
    rw [heq]
    exact hQ
  have hall : ∀ Q : Sylow 2 X, (Q : Subgroup X) ≤ U := by
    intro Q
    by_cases hQ : Q = S
    · rw [hQ]
      exact hSU
    · obtain ⟨s, rfl⟩ := horbit Q hQ
      exact Sylow.smul_le hS'U ⟨(s : X), hSU s.2⟩
  have hnc : normalClosure ((S : Subgroup X) : Set X) ≤ U := by
    rw [normalClosure, closure_le]
    intro y hy
    obtain ⟨c, hc, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hgc : g * c * g⁻¹ ∈ ((g • S : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hc
    exact hall _ hgc
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  have : IsSimpleGroup X := e.isSimpleGroup
  have hS1 : (S : Subgroup X) ≠ ⊥ := by
    intro h
    have h1 := (card_sylow_and_center ha hK e S).1
    rw [h, card_bot] at h1
    have : 2 ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  rcases (normalClosure_normal (s := ((S : Subgroup X) : Set X))).eq_bot_or_eq_top with h | h
  · exact hS1 (eq_bot_iff.mpr (h ▸ subset_normalClosure))
  · exact hU (eq_top_iff.mpr (h ▸ hnc))

theorem mem_centralizer_of_sq_eq_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {z : X}
    (hzS : z ∈ (S : Subgroup X)) (hz : z ^ 2 = 1) :
    z ∈ centralizer ((S : Subgroup X) : Set X) := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  · have hC := centralizer_eq_sylow_of_mulEquiv hK e S (orderOf_eq_prime hz hz1) hzS
    rw [mem_centralizer_iff]
    intro s hs
    have : s ∈ centralizer ({z} : Set X) := by
      rw [hC]
      exact hs
    exact mem_centralizer_singleton_iff.mp this

theorem exists_conj_of_pow_eq_one (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) {σ : MulAut X} {k : ℕ}
    (hσ : σ ^ 2 ^ k = 1) : ∃ g : X, σ = MulAut.conj g := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  obtain ⟨e₀⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 (2 * a + 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * a + 1) (by omega)]
  set φ : X ≃* CFSG.Open.Sz a :=
    (e.trans (CFSG.Blueprint.EvenSource.suzukiGroupMapEquiv a
      (FiniteField.ringEquivOfCardEq (K := K) (K' := GaloisField 2 (2 * a + 1)) hcard))).trans
      e₀.symm
    with hφ
  set σ' := MulAut.congr φ σ with hσ'def
  have hσ' : σ' ^ 2 ^ k = 1 := by rw [hσ'def, ← map_pow, hσ, map_one]
  have hodd := CFSG.CGT.T75M.sz_outer_odd ha (MulEquiv.refl (CFSG.Open.Sz a))
  set o : CFSG.ComponentClassification.OuterAutomorphisms.Outer (CFSG.Open.Sz a) :=
    QuotientGroup.mk σ' with ho
  have h1 : o ^ 2 ^ k = 1 := by rw [ho, ← QuotientGroup.mk_pow, hσ', QuotientGroup.mk_one]
  have hc : Nat.Coprime (2 ^ k)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (CFSG.Open.Sz a))) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have h4 := Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard o)
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff σ').1 (orderOf_eq_one_iff.1 h4)
  refine ⟨φ.symm g, ?_⟩
  apply (MulAut.congr φ).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply,
    ← hσ'def]
  exact hg.symm

theorem suzukiSubgroupInput_of_mulEquiv
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) {J : Subgroup X}
    (hJ : J ≠ ⊤) (hJ4 : ∃ F : Subgroup X, F ≤ J ∧ CFSG.Open.IsElemAbelian 2 F ∧ Nat.card F = 4) :
    (∃ Q : Subgroup X, IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index ∧ J ≤ normalizer (Q : Set X)) ∨
      ∃ a' : ℕ, 1 ≤ a' ∧ ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
        Nat.card K' = 2 ^ (2 * a' + 1) ∧ Nonempty (↥J ≃* suzukiGroup a' K') := by
  have hmodel : CFSG.Quasithin.IsSz (2 * a + 1) (suzukiGroup a K) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨F, hFJ, hF, hF4⟩ := hJ4
  have hJ' : J.map e.toMonoidHom ≠ ⊤ := fun h => hJ (by
    rw [← comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective J, h, comap_top])
  have hF' : ∃ E : Subgroup (suzukiGroup a K), E ≤ J.map e.toMonoidHom ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 4 :=
    ⟨F.map e.toMonoidHom, map_mono hFJ, Stell.isElemAbelian_map hF _,
      by rw [card_map_of_injective e.injective, hF4]⟩
  rcases hSub (2 * a + 1) (suzukiGroup a K) hmodel (J.map e.toMonoidHom) hJ' hF' with
    ⟨Q, hQ⟩ | ⟨k, -, -, hk⟩
  · left
    refine ⟨(Q : Subgroup (suzukiGroup a K)).comap e.toMonoidHom,
      Q.isPGroup'.comap_of_injective e.toMonoidHom e.injective, ?_, ?_⟩
    · rw [index_comap_of_surjective _ e.surjective]
      exact Q.not_dvd_index
    · intro j hj
      rw [mem_normalizer_iff]
      intro x
      have h1 := (mem_normalizer_iff.mp (hQ ⟨j, hj, rfl⟩)) (e x)
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] at h1 ⊢
      exact h1
  · right
    obtain ⟨-, a', ha', K', _, _, hk', hK', ⟨e'⟩⟩ := hk
    rw [hk'] at hK'
    exact ⟨a', ha', K', inferInstance, inferInstance, hK',
      ⟨(J.equivMapOfInjective e.toMonoidHom e.injective).trans e'⟩⟩

theorem eq_one_of_forall_commute (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) {g : X}
    (hg : ∀ x : X, g * x = x * g) : g = 1 := by
  obtain ⟨-, hnt, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  have hperf := (CFSG.LieType.Ree.suzuki_perfect ha hK).1
  have hc : e g ∈ center (suzukiGroup a K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hg x]
  rcases (inferInstance : (center (suzukiGroup a K)).Normal).eq_bot_or_eq_top with h | h
  · rw [h, mem_bot] at hc
    exact e.injective (by rw [map_one]; exact hc)
  · exfalso
    have hbot : commutator (suzukiGroup a K) = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [mem_centralizer_iff]
      intro y _
      have hy : y ∈ center (suzukiGroup a K) := by
        rw [h]
        exact mem_top y
      exact (mem_center_iff.mp hy x).symm
    obtain ⟨w, hw⟩ := exists_ne (1 : suzukiGroup a K)
    have hw' : w ∈ (⊥ : Subgroup (suzukiGroup a K)) := by
      rw [← hbot, hperf]
      exact mem_top w
    exact hw (mem_bot.mp hw')

theorem eq_of_le_inf_sylow (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K)
    {Q Q' : Sylow 2 X} {P : Subgroup X} (hP : P ≠ ⊥) (hPQ : P ≤ Q) (hPQ' : P ≤ Q') : Q = Q' := by
  by_contra hne
  exact hP (eq_bot_iff.mpr ((le_inf hPQ hPQ').trans (inf_eq_bot_of_sylow_ne hK e hne).le))

theorem not_dvd_relIndex_of_le (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K)
    (S : Sylow 2 X) {P J : Subgroup X} (hP : P ≠ ⊥) (hPS : P ≤ S) (hPJ : P ≤ J) :
    ¬ 2 ∣ (S : Subgroup X).relIndex J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hP2 : IsPGroup 2 (P.subgroupOf J) := (S.isPGroup'.to_le hPS).comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hP2.exists_le_sylow
  have hQ₀2 : IsPGroup 2 ((Q₀ : Subgroup J).map J.subtype) := Q₀.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hQ₀2.exists_le_sylow
  have hPQ : P ≤ Q := fun x hx =>
    hQ ⟨⟨x, hPJ hx⟩, hQ₀ (show (⟨x, hPJ hx⟩ : J) ∈ P.subgroupOf J from hx), rfl⟩
  have hQS : Q = S := eq_of_le_inf_sylow hK e hP hPQ hPS
  have hle : (Q₀ : Subgroup J) ≤ (S : Subgroup X).subgroupOf J := by
    intro y hy
    have : (y : X) ∈ (Q : Subgroup X) := hQ ⟨y, hy, rfl⟩
    rw [hQS] at this
    exact this
  exact fun hd => Q₀.not_dvd_index (hd.trans (index_dvd_of_le hle))

theorem mem_normalizer_of_map_conj_le
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {P : Subgroup X} (hP : P ≠ ⊥)
    (hPS : P ≤ S) {g : X} (hg : P.map (MulAut.conj g).toMonoidHom ≤ S) :
    g ∈ normalizer ((S : Subgroup X) : Set X) := by
  have hP' : P.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun h =>
    hP ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ ((g • S : Sylow 2 X) : Subgroup X) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hPS hx)
  exact Sylow.smul_eq_iff_mem_normalizer.mp (eq_of_le_inf_sylow hK e hP' hle hg)

end Suzuki

namespace Stell

open Suzuki

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {x y c d : G}
    (hcx : Commute c x) (hcy : Commute c y) (hdx : Commute d x) (hdy : Commute d y)
    (hcd : Commute c d) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc x * c * (y * d) * (c⁻¹ * x⁻¹) * (d⁻¹ * y⁻¹)
      = x * (c * y) * d * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by group
    _ = x * y * (c * d * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcy.eq]; group
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by
        rw [hcd.eq, mul_inv_cancel_right]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [(hdx.inv_right).eq]; group

@[expose] def innerPart {H : Type*} [Group H] (A E : Subgroup H) : Subgroup H where
  carrier := {g | g ∈ E ∧ ∃ b ∈ A, ∀ x ∈ E, b * x * b⁻¹ = g * x * g⁻¹}
  mul_mem' := by
    rintro g g' ⟨hg, b, hb, hgb⟩ ⟨hg', b', hb', hgb'⟩
    refine ⟨E.mul_mem hg hg', b * b', A.mul_mem hb hb', fun x hx => ?_⟩
    have h1 := hgb' x hx
    have h2 := hgb (g' * x * g'⁻¹) (E.mul_mem (E.mul_mem hg' hx) (E.inv_mem hg'))
    calc b * b' * x * (b * b')⁻¹ = b * (b' * x * b'⁻¹) * b⁻¹ := by group
      _ = g * (g' * x * g'⁻¹) * g⁻¹ := by rw [h1, h2]
      _ = g * g' * x * (g * g')⁻¹ := by group
  one_mem' := ⟨E.one_mem, 1, A.one_mem, fun x _ => by group⟩
  inv_mem' := by
    rintro g ⟨hg, b, hb, hgb⟩
    refine ⟨E.inv_mem hg, b⁻¹, A.inv_mem hb, fun x hx => ?_⟩
    have h1 := hgb (g⁻¹ * x * g) (E.mul_mem (E.mul_mem (E.inv_mem hg) hx) hg)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
    calc b⁻¹ * x * b⁻¹⁻¹ = b⁻¹ * (b * (g⁻¹ * x * g) * b⁻¹) * b := by rw [h1, inv_inv]
      _ = g⁻¹ * x * g⁻¹⁻¹ := by group

section Inner

variable {H : Type*} [Group H] {S M A : Subgroup H}

theorem innerPart_le (A E : Subgroup H) : innerPart A E ≤ E := fun _ hg => hg.1

variable [Finite H]

theorem exists_isL24_or_isL24Sz_of_inner
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) (h : Hyp24 S M A)
    {E : Subgroup H} {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (eE : ↥E ≃* suzukiGroup a K)
    (hinner : ∀ b ∈ A, ∃ g ∈ E, ∀ x ∈ E, b * x * b⁻¹ = g * x * g⁻¹)
    (hnc : ¬ A ≤ centralizer (E : Set H)) (hSE : ¬ 2 ∣ S.relIndex E)
    (hME : M.subgroupOf E = normalizer ((S.subgroupOf E : Subgroup E) : Set E)) :
    ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TE : Sylow 2 E := (h.isPGroup.comap_subtype : IsPGroup 2 (S.subgroupOf E)).toSylow hSE
    with hTEdef
  have hTE : (TE : Subgroup E) = S.subgroupOf E := IsPGroup.toSylow_coe _ _
  set AE := innerPart A E with hAEdef
  have hZ : ∀ g ∈ E, (∀ x ∈ E, g * x * g⁻¹ = x) → g = 1 := by
    intro g hg hgx
    have := eq_one_of_forall_commute ha hK eE (g := ⟨g, hg⟩) fun x => Subtype.ext (by
      have h1 := hgx x x.2
      change g * (x : H) = (x : H) * g
      calc g * (x : H) = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h1])
    exact congrArg Subtype.val this
  have huniq : ∀ g ∈ E, ∀ g' ∈ E, (∀ x ∈ E, g * x * g⁻¹ = g' * x * g'⁻¹) → g = g' := by
    intro g hg g' hg' hgg'
    have h1 := hZ (g'⁻¹ * g) (E.mul_mem (E.inv_mem hg') hg) fun x hx => by
      calc g'⁻¹ * g * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
        _ = g'⁻¹ * (g' * x * g'⁻¹) * g' := by rw [hgg' x hx]
        _ = x := by group
    calc g = g' * (g'⁻¹ * g) := by group
      _ = g' := by rw [h1, mul_one]
  have hprod : ∀ g ∈ E, ∀ b : H, (∀ x ∈ E, b * x * b⁻¹ = g * x * g⁻¹) → ∀ g' ∈ E, ∀ b' : H,
      (∀ x ∈ E, b' * x * b'⁻¹ = g' * x * g'⁻¹) →
        ∀ x ∈ E, (b * b') * x * (b * b')⁻¹ = (g * g') * x * (g * g')⁻¹ := by
    intro g hg b hgb g' hg' b' hgb' x hx
    calc b * b' * x * (b * b')⁻¹ = b * (b' * x * b'⁻¹) * b⁻¹ := by group
      _ = g * (g' * x * g'⁻¹) * g⁻¹ := by
          rw [hgb' x hx, hgb _ (E.mul_mem (E.mul_mem hg' hx) (E.inv_mem hg'))]
      _ = g * g' * x * (g * g')⁻¹ := by group
  have hAEsq : ∀ g ∈ AE, g * g = 1 := by
    rintro g ⟨hg, b, hb, hgb⟩
    have hb2 : b * b = 1 := by rw [← pow_two]; exact h.elemAb.2 b hb
    apply hZ (g * g) (E.mul_mem hg hg)
    intro x hx
    have := hprod g hg b hgb g hg b hgb x hx
    rw [hb2] at this
    rw [← this]
    group
  have hAEcomm : ∀ g ∈ AE, ∀ g' ∈ AE, g * g' = g' * g := by
    rintro g ⟨hg, b, hb, hgb⟩ g' ⟨hg', b', hb', hgb'⟩
    have hbb' : b * b' = b' * b := isElemAbelian_comm h.elemAb hb hb'
    refine huniq _ (E.mul_mem hg hg') _ (E.mul_mem hg' hg) fun x hx => ?_
    rw [← hprod g hg b hgb g' hg' b' hgb' x hx, hbb', hprod g' hg' b' hgb' g hg b hgb x hx]
  have hAEel : CFSG.Open.IsElemAbelian 2 AE :=
    isElemAbelian_of_forall hAEcomm fun g hg => by rw [pow_two]; exact hAEsq g hg
  have hinvT : ∀ w (hw : w ∈ E), w * w = 1 →
      (⟨w, hw⟩ : E) ∈ normalizer ((TE : Subgroup E) : Set E) → w ∈ S := by
    intro w hw hw2 hwN
    have hw2' : IsPGroup 2 (zpowers (⟨w, hw⟩ : E)) := by
      have hdvd : orderOf (⟨w, hw⟩ : E) ∣ 2 ^ 1 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [pow_one, pow_two]; exact hw2))
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
    have h1 : (⟨w, hw⟩ : E) ∈ zpowers (⟨w, hw⟩ : E) ⊓ normalizer ((TE : Subgroup E) : Set E) :=
      ⟨mem_zpowers _, hwN⟩
    have h3 := hw2'.inf_normalizer_sylow TE
    change zpowers _ ⊓ normalizer ((TE : Subgroup E) : Set E) = zpowers _ ⊓ (TE : Subgroup E)
      at h3
    rw [h3] at h1
    have h2 : (⟨w, hw⟩ : E) ∈ (TE : Subgroup E) := h1.2
    rw [hTE, mem_subgroupOf] at h2
    exact h2
  have hAES : AE ≤ S := by
    rintro g ⟨hg, b, hb, hgb⟩
    have hbS : b ∈ S := h.le_S hb
    refine hinvT g hg (hAEsq g ⟨hg, b, hb, hgb⟩) ?_
    rw [mem_normalizer_iff]
    intro y
    change y ∈ (TE : Subgroup E) ↔ _ ∈ (TE : Subgroup E)
    rw [hTE, mem_subgroupOf, mem_subgroupOf]
    change (y : H) ∈ S ↔ g * (y : H) * g⁻¹ ∈ S
    rw [← hgb y y.2]
    constructor
    · intro hy
      exact S.mul_mem (S.mul_mem hbS hy) (S.inv_mem hbS)
    · intro hy
      have := S.mul_mem (S.mul_mem (S.inv_mem hbS) hy) hbS
      rwa [show b⁻¹ * (b * (y : H) * b⁻¹) * b = y by group] at this
  have hAE1 : AE ≠ ⊥ := by
    intro hbot
    apply hnc
    intro b hb
    obtain ⟨g, hg, hgb⟩ := hinner b hb
    have hg1 : g = 1 := by
      have hgA : g ∈ AE := ⟨hg, b, hb, hgb⟩
      rw [hbot] at hgA
      exact mem_bot.mp hgA
    rw [mem_centralizer_iff]
    intro x hx
    have := hgb x hx
    rw [hg1, one_mul, inv_one, mul_one] at this
    calc x * b = b * x * b⁻¹ * b := by rw [this]
      _ = b * x := by group
  have hAE2 : IsPGroup 2 AE := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hAEsq _ x.2)⟩
  obtain ⟨k, hk⟩ := hAE2.exists_card_eq
  have hAE' : AE.subgroupOf E ≠ ⊥ := by
    rw [Ne, subgroupOf_eq_bot]
    intro hdis
    exact hAE1 (eq_bot_iff.mpr fun x hx => (hdis.le_bot ⟨hx, innerPart_le A E hx⟩))
  have hAET : AE.subgroupOf E ≤ (TE : Subgroup E) := by
    rw [hTE]
    exact fun x hx => hAES hx
  have hSyl : ∀ J : Subgroup H, AE ≤ J → J ≤ E → ¬ 2 ∣ S.relIndex J := by
    intro J hAJ hJE
    have h1 := not_dvd_relIndex_of_le hK eE TE hAE' hAET (J := J.subgroupOf E)
      (fun x hx => hAJ hx)
    rwa [hTE, relIndex_subgroupOf hJE] at h1
  have hMEg : ∀ g (hg : g ∈ E),
      g ∈ M ↔ (⟨g, hg⟩ : E) ∈ normalizer ((TE : Subgroup E) : Set E) := by
    intro g hg
    rw [hTE, ← hME, mem_subgroupOf]
  have hEM : ¬ E ≤ M := by
    intro hle
    apply normalizer_sylow_ne_top hK eE TE
    rw [eq_top_iff]
    intro x _
    exact (hMEg x x.2).mp (hle x.2)
  by_cases hk1 : k = 1
  ·
    subst hk1
    obtain ⟨⟨t, htA⟩, ht1⟩ := ne_bot_iff_exists_ne_one.mp hAE1
    have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
    obtain ⟨htE, a₀, ha₀A, hta₀⟩ := htA
    have htt : t * t = 1 := hAEsq t ⟨htE, a₀, ha₀A, hta₀⟩
    have hAEz : AE = zpowers t := by
      symm
      refine eq_of_le_of_card_ge (zpowers_le.mpr ⟨htE, a₀, ha₀A, hta₀⟩) ?_
      rw [hk, pow_one, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact htt) ht1']
    have hAEt : ∀ g ∈ AE, g = 1 ∨ g = t := by
      intro g hg
      rw [hAEz, mem_zpowers_iff_mem_range_orderOf,
        orderOf_eq_prime (by rw [pow_two]; exact htt) ht1'] at hg
      simp only [Finset.mem_image, Finset.mem_range] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      interval_cases i
      · left; rw [pow_zero]
      · right; rw [pow_one]
    set B := A ⊓ centralizer (E : Set H) with hBdef
    have hBA : B ≤ A := inf_le_left
    have hcent : ∀ b : H, (∀ x ∈ E, b * x * b⁻¹ = x) → b ∈ centralizer (E : Set H) := by
      intro b hb
      rw [mem_centralizer_iff]
      intro x hx
      calc x * b = b * x * b⁻¹ * b := by rw [hb x hx]
        _ = b * x := by group
    have ha₀B : a₀ ∉ B := by
      rintro ⟨-, ha₀c⟩
      apply ht1'
      apply hZ t htE
      intro x hx
      rw [← hta₀ x hx]
      have := (mem_centralizer_iff.mp ha₀c) x hx
      rw [← this]
      group
    have hidx : B.relIndex A = 2 := by
      change (B.subgroupOf A).index = 2
      rw [index_eq_two_iff]
      refine ⟨⟨a₀, ha₀A⟩, fun β => ?_⟩
      obtain ⟨g, hg, hgb⟩ := hinner β β.2
      have hgAE : g ∈ AE := ⟨hg, β, β.2, hgb⟩
      simp only [mem_subgroupOf, Subgroup.coe_mul, hBdef, mem_inf]
      rcases hAEt g hgAE with hg1 | hgt
      ·
        rw [hg1] at hgb
        have hβc : (β : H) ∈ centralizer (E : Set H) :=
          hcent β fun x hx => by rw [hgb x hx]; group
        refine Or.inr ⟨⟨β.2, hβc⟩, ?_⟩
        rintro ⟨-, hc⟩
        apply ha₀B
        refine ⟨ha₀A, ?_⟩
        have := mul_mem (inv_mem hβc) hc
        rwa [inv_mul_cancel_left] at this
      ·
        rw [hgt] at hgb
        have hβa : (β : H) * a₀ ∈ centralizer (E : Set H) := by
          refine hcent _ fun x hx => ?_
          rw [hprod t htE β hgb t htE a₀ hta₀ x hx, htt]
          group
        refine Or.inl ⟨⟨A.mul_mem β.2 ha₀A, hβa⟩, ?_⟩
        rintro ⟨-, hc⟩
        apply ha₀B
        refine ⟨ha₀A, ?_⟩
        have := mul_mem (inv_mem hc) hβa
        rwa [inv_mul_cancel_left] at this
    have hto : orderOf (⟨t, htE⟩ : E) = 2 :=
      orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact htt)) fun h' =>
        ht1' (congrArg Subtype.val h')
    obtain ⟨f, hf5, hft⟩ := exists_orderOf_eq_five_inv hK eE hto
    have hay : a₀ * (f : H) * a₀⁻¹ = (f : H)⁻¹ := by
      rw [hta₀ f f.2]
      exact congrArg Subtype.val hft
    have hyB : (f : H) ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      rintro b ⟨-, hbc⟩
      exact ((mem_centralizer_iff.mp hbc) f f.2).symm
    have hyM : (f : H) ∉ M := by
      intro hfM
      have hfN := (hMEg f f.2).mp hfM
      apply not_five_dvd_card_normalizer hK eE TE
      rw [← hf5, ← Subgroup.orderOf_mk (⟨f, f.2⟩ : E) hfN]
      exact orderOf_dvd_natCard _
    exact ⟨_, Or.inl (isL24_zpowers_sup h hBA hidx ha₀A ha₀B hyB hay (p := 5) (by norm_num)
      (by norm_num) (by rw [Subgroup.orderOf_coe]; exact hf5) hyM)⟩
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h' | h'
    · interval_cases k
      · exfalso
        rw [pow_zero] at hk
        exact hAE1 (card_eq_one.mp hk)
      · exact absurd rfl hk1
    · exact h'
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := AE) 2 (n := 2)
    (by rw [hk]; exact pow_dvd_pow 2 hk2)
  set F := F₀.map AE.subtype with hFdef
  have hFAE : F ≤ AE := map_subtype_le F₀
  have hF4 : Nat.card F = 4 := by
    rw [hFdef, card_map_of_injective AE.subtype_injective, hF₀]
    norm_num
  have hFel : CFSG.Open.IsElemAbelian 2 F :=
    isElemAbelian_of_forall (fun x hx y hy => hAEcomm x (hFAE hx) y (hFAE hy))
      fun x hx => by rw [pow_two]; exact hAEsq x (hFAE hx)
  obtain ⟨J₀, ⟨hAJ₀, hJ₀E, hJ₀M⟩, hmin⟩ := exists_minimal_subgroup
    (fun J => AE ≤ J ∧ J ≤ E ∧ ¬ J ≤ M) ⟨E, innerPart_le A E, le_rfl, hEM⟩
  have hJ₀sz : ∃ a' : ℕ, 1 ≤ a' ∧ ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
      Nat.card K' = 2 ^ (2 * a' + 1) ∧ Nonempty (↥J₀ ≃* suzukiGroup a' K') := by
    by_cases hJE : J₀ = E
    · exact ⟨a, ha, K, inferInstance, inferInstance, hK,
        ⟨(MulEquiv.subgroupCongr hJE).trans eE⟩⟩
    · have hJ' : J₀.subgroupOf E ≠ ⊤ := by
        intro htop
        apply hJE
        refine le_antisymm hJ₀E fun x hx => ?_
        have : (⟨x, hx⟩ : E) ∈ J₀.subgroupOf E := by
          rw [htop]
          exact mem_top _
        exact this
      have hF' : ∃ F' : Subgroup E, F' ≤ J₀.subgroupOf E ∧ CFSG.Open.IsElemAbelian 2 F' ∧
          Nat.card F' = 4 :=
        ⟨F.subgroupOf E, fun x hx => hAJ₀ (hFAE hx), isElemAbelian_subgroupOf hFel, by
          rw [Nat.card_congr (subgroupOfEquivOfLe (hFAE.trans (innerPart_le A E))).toEquiv,
            hF4]⟩
      rcases suzukiSubgroupInput_of_mulEquiv hSub ha hK eE hJ' hF' with
        ⟨Q, hQ2, hQi, hJQ⟩ | ⟨a', ha', K', _, _, hK', ⟨e'⟩⟩
      · exfalso
        set QS := hQ2.toSylow hQi with hQSdef
        have hAE2' : IsPGroup 2 (AE.subgroupOf E) := hAE2.comap_subtype
        have hAEQ : AE.subgroupOf E ≤ (QS : Subgroup E) := by
          have h1 := hAE2'.inf_normalizer_sylow QS
          have h2 : AE.subgroupOf E ≤ AE.subgroupOf E ⊓ normalizer (QS : Set E) :=
            le_inf le_rfl fun x hx => hJQ (hAJ₀ hx)
          rw [h1] at h2
          exact h2.trans inf_le_right
        have hQT : QS = TE := eq_of_le_inf_sylow hK eE hAE' hAEQ hAET
        apply hJ₀M
        intro x hx
        refine (hMEg x (hJ₀E hx)).mpr ?_
        rw [← hQT]
        exact hJQ (show (⟨x, hJ₀E hx⟩ : E) ∈ J₀.subgroupOf E from hx)
      · exact ⟨a', ha', K', inferInstance, inferInstance, hK',
          ⟨(subgroupOfEquivOfLe hJ₀E).symm.trans e'⟩⟩
  set Z := (A ⊔ AE) ⊓ centralizer (E : Set H) with hZdef
  have hAAE : ∀ c ∈ A, ∀ g ∈ AE, c * g = g * c := by
    intro c hc g hgAE
    obtain ⟨g', hg', hcg'⟩ := hinner c hc
    have h1 := hcg' g hgAE.1
    rw [hAEcomm g' ⟨hg', c, hc, hcg'⟩ g hgAE, mul_inv_cancel_right] at h1
    calc c * g = c * g * c⁻¹ * c := by group
      _ = g * c := by rw [h1]
  have hAAEcomm : ∀ x ∈ A ⊔ AE, ∀ y ∈ A ⊔ AE, x * y = y * x := by
    have h1 : A ⊔ AE ≤ centralizer (A : Set H) := sup_le
      (fun b hb => mem_centralizer_iff.mpr fun c hc => isElemAbelian_comm h.elemAb hc hb)
      (fun g hg => mem_centralizer_iff.mpr fun c hc => hAAE c hc g hg)
    have h2 : A ⊔ AE ≤ centralizer (AE : Set H) := sup_le
      (fun b hb => mem_centralizer_iff.mpr fun g hg => (hAAE b hb g hg).symm)
      (fun g hg => mem_centralizer_iff.mpr fun g' hg' => hAEcomm g' hg' g hg)
    have hle : A ⊔ AE ≤ centralizer ((A ⊔ AE : Subgroup H) : Set H) :=
      sup_le (le_centralizer_iff.mpr h1) (le_centralizer_iff.mpr h2)
    intro x hx y hy
    exact ((mem_centralizer_iff.mp (hle hy)) x hx)
  have hAN : A ≤ normalizer (AE : Set H) := fun c hc =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => (hAAE c hc g hg).symm)
  have hAAEsq : ∀ x ∈ A ⊔ AE, x * x = 1 := by
    intro x hx
    have hx' : x ∈ ((A ⊔ AE : Subgroup H) : Set H) := hx
    rw [coe_mul_of_left_le_normalizer_right A AE hAN] at hx'
    obtain ⟨b, hb, g, hg, rfl⟩ := hx'
    have hb2 : b * b = 1 := by rw [← pow_two]; exact h.elemAb.2 b hb
    calc b * g * (b * g) = b * (g * b) * g := by group
      _ = b * (b * g) * g := by rw [hAAE b hb g hg]
      _ = (b * b) * (g * g) := by group
      _ = 1 := by rw [hb2, hAEsq g hg, one_mul]
  have hZS : Z ≤ S := inf_le_left.trans (sup_le h.le_S hAES)
  have hdecomp : ∀ b ∈ A, ∀ g ∈ E, (∀ x ∈ E, b * x * b⁻¹ = g * x * g⁻¹) → b * g⁻¹ ∈ Z := by
    intro b hb g hg hgb
    refine mem_inf.mpr ⟨mul_mem (mem_sup_left hb)
      (inv_mem (mem_sup_right (show g ∈ AE from ⟨hg, b, hb, hgb⟩))), ?_⟩
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hgb (g⁻¹ * x * g) (E.mul_mem (E.mul_mem (E.inv_mem hg) hx) hg)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
    calc x * (b * g⁻¹) = b * (g⁻¹ * x * g) * b⁻¹ * (b * g⁻¹) := by rw [h1]
      _ = b * g⁻¹ * x := by group
  have hZJ₀ : Z ⊓ J₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨-, hzc⟩, hzJ⟩
    refine mem_bot.mpr (hZ z (hJ₀E hzJ) fun x hx => ?_)
    rw [← (mem_centralizer_iff.mp hzc) x hx]
    group
  set L := J₀ ⊔ A with hLdef
  have hJ₀L : J₀ ≤ L := le_sup_left
  have hAEJ₀L : AE ≤ L := hAJ₀.trans hJ₀L
  have hZL : Z ≤ L := inf_le_left.trans (sup_le le_sup_right hAEJ₀L)
  have hcZJ : ∀ z ∈ Z, ∀ j ∈ J₀, z * j = j * z := fun z hz j hj =>
    ((mem_centralizer_iff.mp hz.2) j (hJ₀E hj)).symm
  have hcZA : ∀ z ∈ Z, ∀ b ∈ A, z * b = b * z := fun z hz b hb =>
    hAAEcomm z hz.1 b (mem_sup_left hb)
  have hLcomm : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    have hle : L ≤ centralizer (Z : Set H) := sup_le
      (fun j hj => mem_centralizer_iff.mpr fun z' hz' => hcZJ z' hz' j hj)
      (fun b hb => mem_centralizer_iff.mpr fun z' hz' => hcZA z' hz' b hb)
    exact (mem_centralizer_iff.mp (hle hl)) z hz
  have hLJZ : L = J₀ ⊔ Z := by
    refine le_antisymm (sup_le le_sup_left fun b hb => ?_) (sup_le hJ₀L hZL)
    obtain ⟨g, hg, hgb⟩ := hinner b hb
    have hbg : b = (b * g⁻¹) * g := by group
    rw [hbg, sup_comm]
    exact mul_mem (mem_sup_left (hdecomp b hb g hg hgb)) (mem_sup_right (hAJ₀ ⟨hg, b, hb, hgb⟩))
  have hJ₀N : J₀ ≤ normalizer (Z : Set H) := fun j hj =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => hcZJ z hz j hj)
  have hLprod : ∀ l ∈ L, ∃ j ∈ J₀, ∃ z ∈ Z, j * z = l := by
    intro l hl
    have hl' : l ∈ ((J₀ ⊔ Z : Subgroup H) : Set H) := by rw [← hLJZ]; exact hl
    rw [coe_mul_of_left_le_normalizer_right J₀ Z hJ₀N] at hl'
    exact hl'
  have hLSyl : ¬ 2 ∣ S.relIndex L := by
    have hSL : IsPGroup 2 (S.subgroupOf L) := h.isPGroup.comap_subtype
    obtain ⟨P, hP⟩ := hSL.exists_le_sylow
    have hTJ2 : IsPGroup 2 (S.subgroupOf J₀) := h.isPGroup.comap_subtype
    set TJ := hTJ2.toSylow (hSyl J₀ hAJ₀ hJ₀E) with hTJdef
    have hPS : (P : Subgroup L) ≤ S.subgroupOf L := by
      intro p hp
      obtain ⟨j, hj, z, hz, hjz⟩ := hLprod p p.2
      have hzP : (⟨z, hZL hz⟩ : L) ∈ P :=
        hP (show (⟨z, hZL hz⟩ : L) ∈ S.subgroupOf L from hZS hz)
      have hjP : (⟨j, hJ₀L hj⟩ : L) ∈ P := by
        have heq : (⟨j, hJ₀L hj⟩ : L) = p * ⟨z, hZL hz⟩⁻¹ := Subtype.ext (by simp [← hjz])
        rw [heq]
        exact P.mul_mem hp (P.inv_mem hzP)
      have hX2 : IsPGroup 2 (((P : Subgroup L).map L.subtype).subgroupOf J₀) :=
        (P.isPGroup'.map _).comap_subtype
      have hle : (TJ : Subgroup J₀) ≤ ((P : Subgroup L).map L.subtype).subgroupOf J₀ :=
        fun y hy => ⟨⟨y, hJ₀L y.2⟩, hP (show (⟨(y : H), hJ₀L y.2⟩ : L) ∈ S.subgroupOf L from hy),
          rfl⟩
      have heq := TJ.is_maximal' hX2 hle
      have hj' : (⟨j, hj⟩ : J₀) ∈ ((P : Subgroup L).map L.subtype).subgroupOf J₀ :=
        ⟨⟨j, hJ₀L hj⟩, hjP, rfl⟩
      rw [heq] at hj'
      have hjS : j ∈ S := hj'
      show (p : H) ∈ S
      rw [← hjz]
      exact S.mul_mem hjS (hZS hz)
    exact fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPS))
  obtain ⟨a', ha', K', _, _, hK', ⟨eJ⟩⟩ := hJ₀sz
  have hJ₀perf : ⁅J₀, J₀⁆ = J₀ := by
    have h1 : commutator ↥J₀ = ⊤ := by
      apply map_injective (f := eJ.toMonoidHom) eJ.injective
      rw [_root_.commutator_def, map_commutator, map_top_of_surjective _ eJ.surjective,
        ← _root_.commutator_def, (CFSG.LieType.Ree.suzuki_perfect ha' hK').1]
    rw [← map_subtype_commutator, h1, ← MonoidHom.range_eq_map, range_subtype]
  have hsup : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L := by
    intro x hxL hxM
    obtain ⟨j, hj, z, hz, rfl⟩ := hLprod x hxL
    have hjM : j ∉ M := fun hjM => hxM (M.mul_mem hjM (h.le_M (hZS hz)))
    have hjE := hJ₀E hj
    have hJ : AE ⊔ AE.map (MulAut.conj j).toMonoidHom = J₀ := by
      refine hmin _ ⟨le_sup_left, sup_le (innerPart_le A E)
        (map_conj_le (innerPart_le A E) hjE), ?_⟩ (sup_le hAJ₀ (map_conj_le hAJ₀ hj))
      intro hle
      apply hjM
      refine (hMEg j hjE).mpr (mem_normalizer_of_map_conj_le hK eE TE hAE' hAET ?_)
      rintro _ ⟨y, hy, rfl⟩
      have hyj : (j : H) * y * j⁻¹ ∈ AE.map (MulAut.conj j).toMonoidHom := ⟨y, hy, rfl⟩
      have hyjE : (j : H) * y * j⁻¹ ∈ E := E.mul_mem (E.mul_mem hjE y.2) (E.inv_mem hjE)
      have hyjM := hle (mem_sup_right hyj)
      have hyy : (y : H) * y = 1 := hAEsq y hy
      have h1 := hinvT _ hyjE (by
        rw [show (j : H) * y * j⁻¹ * (j * y * j⁻¹) = j * (y * y) * j⁻¹ by group, hyy, mul_one,
          mul_inv_cancel]) ((hMEg _ hyjE).mp hyjM)
      rw [hTE]
      exact h1
    set X := A ⊔ A.map (MulAut.conj (j * z)).toMonoidHom with hXdef
    have hXL : X ≤ L := sup_le le_sup_right (map_conj_le le_sup_right hxL)
    have hJXZ : J₀ ≤ X ⊔ Z := by
      rw [← hJ]
      refine sup_le ?_ ?_
      · rintro g ⟨hg, b, hb, hgb⟩
        have hbZ := hdecomp b hb g hg hgb
        rw [show g = (b * g⁻¹)⁻¹ * b by group]
        exact mul_mem (mem_sup_right (inv_mem hbZ)) (mem_sup_left (mem_sup_left hb))
      · rintro _ ⟨g, ⟨hg, b, hb, hgb⟩, rfl⟩
        have hbZ := hdecomp b hb g hg hgb
        have hcj : (b * g⁻¹) * j = j * (b * g⁻¹) :=
          ((mem_centralizer_iff.mp hbZ.2) j hjE).symm
        have hzb : z * b = b * z := hcZA z hz b hb
        have e1 : (MulAut.conj j).toMonoidHom g =
            (b * g⁻¹)⁻¹ * ((j * z) * b * (j * z)⁻¹) := by
          calc (MulAut.conj j).toMonoidHom g = j * g * j⁻¹ := rfl
            _ = (b * g⁻¹)⁻¹ * ((b * g⁻¹) * j) * g * j⁻¹ := by group
            _ = (b * g⁻¹)⁻¹ * (j * (b * g⁻¹)) * g * j⁻¹ := by rw [hcj]
            _ = (b * g⁻¹)⁻¹ * (j * (z * b * z⁻¹) * j⁻¹) := by
                rw [show z * b * z⁻¹ = b by rw [hzb]; group]
                group
            _ = (b * g⁻¹)⁻¹ * ((j * z) * b * (j * z)⁻¹) := by group
        rw [e1]
        exact mul_mem (mem_sup_right (inv_mem hbZ)) (mem_sup_left (mem_sup_right ⟨b, hb, rfl⟩))
    have hJ₀X : J₀ ≤ X := by
      rw [← hJ₀perf, commutator_le]
      intro j₁ hj₁ j₂ hj₂
      have hXN : X ≤ normalizer (Z : Set H) := fun y hy =>
        centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun c hc => hLcomm c hc y (hXL hy))
      have h1 : j₁ ∈ ((X ⊔ Z : Subgroup H) : Set H) := hJXZ hj₁
      have h2 : j₂ ∈ ((X ⊔ Z : Subgroup H) : Set H) := hJXZ hj₂
      rw [coe_mul_of_left_le_normalizer_right X Z hXN] at h1 h2
      obtain ⟨x₁, hx₁, c₁, hc₁, rfl⟩ := h1
      obtain ⟨x₂, hx₂, c₂, hc₂, rfl⟩ := h2
      rw [commutatorElement_mul_mul_of_commute (hLcomm c₁ hc₁ x₁ (hXL hx₁))
        (hLcomm c₁ hc₁ x₂ (hXL hx₂)) (hLcomm c₂ hc₂ x₁ (hXL hx₁)) (hLcomm c₂ hc₂ x₂ (hXL hx₂))
        (hLcomm c₁ hc₁ c₂ (hZL hc₂)), commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem hx₁ hx₂) (X.inv_mem hx₁)) (X.inv_mem hx₂)
    exact le_antisymm hXL (sup_le hJ₀X le_sup_left)
  have hsz : SzOverOTwo ↥L := by
    set R : Subgroup L := Z.subgroupOf L with hRdef
    have hRn : R.Normal := ⟨fun r hr l => by
      change (l : H) * r * (l : H)⁻¹ ∈ Z
      rw [← hLcomm r hr l l.2, mul_inv_cancel_right]
      exact hr⟩
    set ψ : ↥J₀ →* ↥L ⧸ R := (QuotientGroup.mk' R).comp (inclusion hJ₀L) with hψdef
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have h1 : inclusion hJ₀L y ∈ R := (QuotientGroup.eq_one_iff _).mp hy
      have h2 : (y : H) ∈ Z ⊓ J₀ := ⟨h1, y.2⟩
      rw [hZJ₀] at h2
      exact Subtype.ext (mem_bot.mp h2)
    have hψsurj : Function.Surjective ψ := by
      intro w
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective R w
      obtain ⟨j, hj, z, hz, hjz⟩ := hLprod l l.2
      refine ⟨⟨j, hj⟩, ?_⟩
      change (QuotientGroup.mk' R) (inclusion hJ₀L ⟨j, hj⟩) = (QuotientGroup.mk' R) l
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      change (j : H)⁻¹ * l ∈ Z
      rw [← hjz, inv_mul_cancel_left]
      exact hz
    set eψ := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩ with heψ
    have hR2 : IsPGroup 2 R := fun r =>
      ⟨1, Subtype.ext (Subtype.ext (by rw [pow_one, pow_two]; exact hAAEsq _ r.2.1))⟩
    have hOR : oTwo ↥L = R := by
      apply le_antisymm
      · have hQ : oTwo (↥L ⧸ R) = ⊥ := oTwo_eq_bot hK' (eψ.symm.trans eJ)
        have : ((oTwo ↥L).map (QuotientGroup.mk' R)).Normal :=
          (inferInstance : (oTwo ↥L).Normal).map _ (QuotientGroup.mk'_surjective R)
        have hmap : (oTwo ↥L).map (QuotientGroup.mk' R) ≤ oTwo (↥L ⧸ R) :=
          le_oTwo ((oTwo_isPGroup ↥L).map _)
        rw [hQ, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
        exact hmap
      · exact le_oTwo hR2
    refine ⟨R, hRn, hOR.le, ?_, a', ha', K', inferInstance, inferInstance, hK',
      ⟨eψ.symm.trans eJ⟩⟩
    rw [hOR, relIndex_self]
    norm_num
  exact ⟨L, Or.inr ⟨⟨le_sup_right, fun hle => hJ₀M (hJ₀L.trans hle), hLSyl, hsup⟩, hsz⟩⟩

theorem relIndex_le_two_pow_of_mulEquiv {L : Subgroup H}
    (hAL : A ≤ L) (hA : CFSG.Open.IsElemAbelian 2 A) {R : Subgroup L} [R.Normal]
    (hOR : oTwo ↥L ≤ R) (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K) :
    ((oTwo ↥L).map L.subtype).relIndex A ≤ 2 ^ (2 * a + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← card_map_subgroupOf_eq_relIndex hAL hA hOR hodd (QuotientGroup.mk' R)
    (QuotientGroup.ker_mk' R)]
  have hsq : ∀ g ∈ (A.subgroupOf L).map (QuotientGroup.mk' R), g ^ 2 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    have : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ hg)
    rw [← map_pow, this, map_one]
  have hA2 : IsPGroup 2 ((A.subgroupOf L).map (QuotientGroup.mk' R)) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hsq g g.2)⟩
  obtain ⟨Q, hQ⟩ := hA2.exists_le_sylow
  have hle : (A.subgroupOf L).map (QuotientGroup.mk' R) ≤
      (Q : Subgroup (↥L ⧸ R)) ⊓ centralizer ((Q : Subgroup (↥L ⧸ R)) : Set (↥L ⧸ R)) :=
    fun g hg => ⟨hQ hg, mem_centralizer_of_sq_eq_one hK e Q (hQ hg) (hsq g hg)⟩
  calc Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' R))
      ≤ Nat.card ((Q : Subgroup (↥L ⧸ R)) ⊓
          centralizer ((Q : Subgroup (↥L ⧸ R)) : Set (↥L ⧸ R)) : Subgroup (↥L ⧸ R)) :=
        card_le_of_le hle
    _ = 2 ^ (2 * a + 1) := (card_sylow_and_center ha hK e Q).2.1

end Inner

end Stell

end CFSG.RankThree.S4Free
