module

public import CFSG.Quasithin.H13.L32A753a
public import CFSG.Quasithin.H13.L32A753b
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux
public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Background.SmithB45AltBase

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

omit [Finite G] in
theorem tildeOf_commutator {V₁ U K : Subgroup G} (hU : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hK : K ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ ⁅U, K⁆ = ⁅tildeOf V₁ U, tildeOf V₁ K⁆ := by
  have hc : ⁅U, K⁆.subgroupOf (Subgroup.normalizer (V₁ : Set G)) =
      ⁅U.subgroupOf (Subgroup.normalizer (V₁ : Set G)),
        K.subgroupOf (Subgroup.normalizer (V₁ : Set G))⁆ := by
    apply Subgroup.map_injective (Subgroup.normalizer (V₁ : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hU,
      Subgroup.map_subgroupOf_eq_of_le hK,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le.2 fun u hu k hk =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) (hK hk))
          (Subgroup.inv_mem _ (hU hu))) (Subgroup.inv_mem _ (hK hk)))]
  unfold tildeOf secImg
  rw [hc, Subgroup.map_commutator]

namespace Ctx753

theorem fact_tilde (C : Ctx753 T L V K) :
    Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))) :=
  factElem C.f918 (le_conjClosure V (hz T V))

theorem psu_pCore (C : Ctx753 T L V K) : IsPSU 3 3 1 (↥K ⧸ CFSG.pCore 2 ↥K) :=
  isPSU_congr (QuotientGroup.quotientMulEquivOfEq (SBc13.pCoreOf_subgroupOf_eq_pCore_J1 K)) C.psu

theorem isSimple_pCore (C : Ctx753 T L V K) : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 C.psu_pCore).2

theorem K_not_le_pCoreOf (C : Ctx753 T L V K) : ¬ K ≤ pCoreOf 2 (hz T V) := by
  intro hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 ↥K := (pCoreOf_isPGroup 2 (hz T V)).to_le hK
  have : Group.IsNilpotent ↥K := hKp.isNilpotent
  exact not_isSolvable_of_mem_cComp C.mem_cComp inferInstance

theorem autK_ne_bot (C : Ctx753 T L V K) : autIH (fsuV1 T V) V (hz T V) K ≠ ⊥ := by
  have := C.fact_tilde
  intro h0
  apply C.K_not_le_pCoreOf
  intro k hk
  have hkH : k ∈ hz T V := C.le_hz hk
  refine mem_pCoreOf_of_actH_eq_one C.f918 (x := ⟨k, hkH⟩) ?_
  have hmem : actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V)) ⟨k, hkH⟩ ∈
      autIH (fsuV1 T V) V (hz T V) K := by
    rw [autIH_eq_map C.f918 C.le_hz]
    exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  rw [h0, Subgroup.mem_bot] at hmem
  exact hmem

theorem nonempty_equiv_autK (C : Ctx753 T L V K) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autIH (fsuV1 T V) V (hz T V) K)) :=
  nonempty_mulEquiv_quotient_autI C.f918 (le_conjClosure V (hz T V)) C.isSimple_pCore
    C.autK_ne_bot

theorem b42TypeU33_autK (C : Ctx753 T L V K) :
    B42TypeU33 ↥(autIH (fsuV1 T V) V (hz T V) K) := by
  obtain ⟨e⟩ := C.nonempty_equiv_autK
  set A := autIH (fsuV1 T V) V (hz T V) K with hA
  have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := C.isSimple_pCore
  have hs : IsSimpleGroup ↥A := e.symm.isSimpleGroup
  have hcard : Nat.card ↥A = 6048 := by
    rw [← Nat.card_congr e.toEquiv]
    exact SBc11.card_of_isPSU_three_three C.psu_pCore
  have hZ : Subgroup.center ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with hb | ht
    · exact hb
    · exfalso
      have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => by
        have ha : a ∈ Subgroup.center ↥A := ht ▸ trivial
        exact (Subgroup.mem_center_iff.mp ha b).symm
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 (by rw [hcard]; norm_num)
      have hN : (Subgroup.zpowers x).Normal :=
        ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h2
      · have : x = 1 := by
          have := Subgroup.mem_zpowers x
          rw [h1, Subgroup.mem_bot] at this
          exact this
        rw [this, orderOf_one] at hx
        exact absurd hx (by norm_num)
      · have h3 := Nat.card_zpowers x
        rw [h2, Subgroup.card_top, hcard, hx] at h3
        exact absurd h3 (by norm_num)
  refine ⟨hZ, ?_⟩
  have e' : ↥A ⧸ Subgroup.center ↥A ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e.symm
  exact isPSU_congr e'.symm C.psu_pCore

noncomputable abbrev actU (C : Ctx753 T L V K) :
    ↥(hz T V) →* MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) :=
  actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V))

theorem autK_le_autH (C : Ctx753 T L V K) :
    autIH (fsuV1 T V) V (hz T V) K ≤ autIH (fsuV1 T V) V (hz T V) (hz T V) := by
  rw [autIH_eq_map C.f918 C.le_hz, autIH_eq_map C.f918 le_rfl]
  exact Subgroup.map_mono fun x _ => Subgroup.mem_subgroupOf.mpr x.2

theorem autH_le_normalizer (C : Ctx753 T L V K) :
    autIH (fsuV1 T V) V (hz T V) (hz T V) ≤
      Subgroup.normalizer (autIH (fsuV1 T V) V (hz T V) K :
        Set (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))))) := by
  rw [autIH_eq_map C.f918 le_rfl, autIH_eq_map C.f918 C.le_hz]
  rintro _ ⟨h, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨h * k * h⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (C.le_normalizer h.2) k).mp hk
  · rintro ⟨k, hk, hke⟩
    refine ⟨h⁻¹ * k * h, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ⊢
      have hN := (Subgroup.mem_normalizer_iff.mp (C.le_normalizer (Subgroup.inv_mem _ h.2))
        (k : G)).mp hk
      simpa using hN
    · have e2 : y = (C.actU h)⁻¹ * (C.actU h * y * (C.actU h)⁻¹) * C.actU h := by group
      rw [e2, ← hke]
      simp only [map_mul, map_inv]

theorem center_autK (C : Ctx753 T L V K) :
    Subgroup.center ↥(autIH (fsuV1 T V) V (hz T V) K) = ⊥ :=
  C.b42TypeU33_autK.1

theorem autH_inf_centralizer_le (C : Ctx753 T L V K) :
    autIH (fsuV1 T V) V (hz T V) (hz T V) ⊓
        Subgroup.centralizer (autIH (fsuV1 T V) V (hz T V) K :
          Set (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))))) ≤
      autIH (fsuV1 T V) V (hz T V) K := by
  have := C.fact_tilde
  rintro x ⟨hxH, hxC⟩
  rw [autIH_eq_map C.f918 le_rfl] at hxH
  obtain ⟨h₀, -, rfl⟩ := hxH
  set D : Subgroup G := ((Subgroup.centralizer (autIH (fsuV1 T V) V (hz T V) K :
      Set (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))))).comap C.actU).map
      (hz T V).subtype with hD
  have hDH : D ≤ hz T V := by
    rintro _ ⟨d, -, rfl⟩
    exact d.2
  have hmemK : ∀ k : ↥(hz T V), (k : G) ∈ K → C.actU k ∈ autIH (fsuV1 T V) V (hz T V) K := by
    intro k hk
    rw [autIH_eq_map C.f918 C.le_hz]
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hDN : hz T V ≤ Subgroup.normalizer (D : Set G) := by
    intro h hh
    have key : ∀ g ∈ hz T V, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
      intro g hg d hd
      obtain ⟨d', hd', rfl⟩ := hd
      refine ⟨⟨g, hg⟩ * d' * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hd' ⊢
      intro y hy
      have hy' : C.actU ⟨g, hg⟩⁻¹ * y * (C.actU ⟨g, hg⟩⁻¹)⁻¹ ∈
          autIH (fsuV1 T V) V (hz T V) K := by
        have hn := C.autH_le_normalizer (by
          rw [autIH_eq_map C.f918 le_rfl]
          exact ⟨⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.mpr (by simp [hg]), rfl⟩)
        exact (Subgroup.mem_normalizer_iff.mp hn y).mp hy
      have h1 := hd' _ hy'
      simp only [map_mul, map_inv, inv_inv] at h1 ⊢
      calc y * (C.actU ⟨g, hg⟩ * C.actU d' * (C.actU ⟨g, hg⟩)⁻¹) =
            C.actU ⟨g, hg⟩ * (((C.actU ⟨g, hg⟩)⁻¹ * y * C.actU ⟨g, hg⟩) * C.actU d') *
              (C.actU ⟨g, hg⟩)⁻¹ := by group
        _ = C.actU ⟨g, hg⟩ * (C.actU d' * ((C.actU ⟨g, hg⟩)⁻¹ * y * C.actU ⟨g, hg⟩)) *
              (C.actU ⟨g, hg⟩)⁻¹ := by rw [h1]
        _ = C.actU ⟨g, hg⟩ * C.actU d' * (C.actU ⟨g, hg⟩)⁻¹ * y := by group
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨key h hh d, fun hd => ?_⟩
    have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hd
    simpa [mul_assoc] using this
  have hDp : IsPGroup 2 ↥D := by
    rintro ⟨_, ⟨d, hd, rfl⟩⟩
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := C.T_le.trans C.le_normalizer
    have hdKT : (d : G) ∈ K ⊔ T := by rw [← C.eq_sup]; exact d.2
    obtain ⟨k, hk, t, ht, hkt⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTK).1 hdKT
    obtain ⟨a, ha⟩ := C.isPGroup_T ⟨t, ht⟩
    have ht' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨k', hk', hpow⟩ := A4.exists_pow_mul_eq hk (hTK ht) (2 ^ a)
    have hdK : ((d ^ 2 ^ a : ↥(hz T V)) : G) ∈ K := by
      rw [Subgroup.coe_pow, hkt, hpow, ht', mul_one]
      exact hk'
    have hcen : C.actU (d ^ 2 ^ a) = 1 := by
      have hm := hmemK _ hdK
      have hc : (⟨C.actU (d ^ 2 ^ a), hm⟩ : ↥(autIH (fsuV1 T V) V (hz T V) K)) ∈
          Subgroup.center ↥(autIH (fsuV1 T V) V (hz T V) K) := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hd
        change (z : MulAut _) * C.actU (d ^ 2 ^ a) = C.actU (d ^ 2 ^ a) * (z : MulAut _)
        rw [map_pow]
        exact (Commute.pow_right (hd z z.2) _).eq
      rw [C.center_autK, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    have hQ := mem_pCoreOf_of_actH_eq_one C.f918 hcen
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨_, hQ⟩
    have hb' : ((d : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    change (d : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, hb']
  have hDQ : D ≤ pCoreOf 2 (hz T V) := le_pCoreOf_of_le_normalizer hDH hDN hDp
  have hh₀ : (h₀ : G) ∈ D := ⟨h₀, by
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    exact hxC, rfl⟩
  have h1 : C.actU h₀ = 1 :=
    C.f918.actH_eq_one_of_mem_pCoreOf (le_conjClosure V (hz T V)) (hDQ hh₀)
  rw [h1]
  exact Subgroup.one_mem _

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem commV_autK (C : Ctx753 T L V K) :
    commV (autIH (fsuV1 T V) V (hz T V) K) = ⊤ := by
  have : IsMulCommutative ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  have hUN : conjClosure V (hz T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    C.f918.toHypF98.toHypF91.conjClosure_Vp_le_pCoreOf.trans
      ((pCoreOf_le 2 _).trans C.f918.H_le_normalizer_V₁)
  have hKN : K ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    C.le_hz.trans C.f918.H_le_normalizer_V₁
  refine InternalSec.commV_autOn_eq_top
    (secImg_le_normalizer_secImg (C.le_hz.trans (le_normalizer_conjClosure V (hz T V)))) ?_
  rw [← tildeOf_commutator hUN hKN, C.conjClosure_eq, ← C.comm_eq]

theorem exists_qset (C : Ctx753 T L V K) :
    ∃ A ∈ Qset (autIH (fsuV1 T V) V (hz T V) (hz T V)), True := by
  obtain ⟨B, -, hB⟩ := C.f918.F918_2
  exact ⟨_, hB, trivial⟩

theorem index_fixV_autK_le
    (C : Ctx753 T L V K) :
    (fixV (autIH (fsuV1 T V) V (hz T V) K)).index ≤ 2 ^ 12 := by
  obtain ⟨A, ⟨⟨hA, hr⟩, -⟩, -⟩ := C.exists_qset
  have hsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))), v ^ 2 = 1 := fun v => by
    have h := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))).2
      v.1 v.2
    exact Subtype.ext (by simpa using h)
  exact M753.index_fixV_le_of_index_le_sq C.autK_le_autH C.autH_le_normalizer
    C.autH_inf_centralizer_le C.b42TypeU33_autK hA.1 hA.2.1 hA.2.2
    (B45Alt.index_le_sq_of_rAV_le_two hsq hA hr)

end Ctx753

end CFSG.Quasithin.H13.L32A
