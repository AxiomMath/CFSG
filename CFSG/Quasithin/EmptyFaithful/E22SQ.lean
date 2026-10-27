module

public import CFSG.Quasithin.EmptyFaithful.E22PTypeII

public section

namespace CFSG.Quasithin.E22S

open CFSG.Open CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

theorem e22s_isE_of_quasisimple_normal {G : Type} [Group G] [Finite G] {T A K J : Subgroup G}
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (hSyl : IsSylowIn 2 (T ⊓ K) K) (hJK : J ≤ K)
    (hJn : (J.subgroupOf K).Normal)
    (hJperf : Group.IsPerfect ↥(J.subgroupOf K))
    (hJs : IsSimpleGroup (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)))
    (hJz : ∀ z ∈ Subgroup.center ↥(J.subgroupOf K), ∃ n : ℕ, z ^ 2 ^ n = 1)
    (h2q : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈ J)
    (hAK : A ≤ T ⊓ K) (hAR : ¬ A ≤ Subgroup.centralizer (J : Set G))
    (hAI : (K ⊓ Subgroup.centralizer (J : Set G)).relIndex A ≤ 2)
    (hC : T ⊓ Subgroup.centralizer (A : Set G) ≤ K) : IsE 1 ⊤ T A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rg : Subgroup G := K ⊓ Subgroup.centralizer (J : Set G)
  set R' : Subgroup ↥K := Rg.subgroupOf K with hR'
  set J' : Subgroup ↥K := J.subgroupOf K
  have hmemR' : ∀ x : ↥K, x ∈ R' ↔ ∀ y ∈ J', x * y = y * x := by
    intro x
    constructor
    · intro hx y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : G) hy).symm
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      exact (congrArg Subtype.val (hx ⟨m, hJK hm⟩ (Subgroup.mem_subgroupOf.mpr hm))).symm
  have hR'n : R'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hmemR'] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ J' := by
      have := hJn.conj_mem y hy g⁻¹
      simpa using this
    have h1 : x * (g⁻¹ * y * g) = (g⁻¹ * y * g) * x := hx _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [h1]
      _ = y * (g * x * g⁻¹) := by group
  have hR'2 : IsPGroup 2 R' := by
    intro x
    obtain ⟨n, hn⟩ := h2q (x : ↥K).1 (x : ↥K).2
    have hxR : (x : ↥K) ^ 2 ^ n ∈ R' := R'.pow_mem x.2 _
    have hxJ : (x : ↥K) ^ 2 ^ n ∈ J' := Subgroup.mem_subgroupOf.mpr (by simpa using hn)
    have hz : (⟨(x : ↥K) ^ 2 ^ n, hxJ⟩ : ↥J') ∈ Subgroup.center ↥J' := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (((hmemR' _).mp hxR g.1 g.2).symm)
    obtain ⟨k, hk⟩ := hJz _ hz
    refine ⟨n + k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg (fun u : ↥J' => ((u : ↥K) : G)) hk
    simpa [pow_add, pow_mul] using h1
  let φ : ↥K →* ↥K ⧸ R' := QuotientGroup.mk' R'
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective R'
  have hker : φ.ker = R' := QuotientGroup.ker_mk' R'
  have hJperf' : ⁅J', J'⁆ = J' := Subgroup.isPerfect_iff.mp hJperf
  let ψ : ↥J' →* ↥K ⧸ R' := φ.comp J'.subtype
  have hψker : ψ.ker = Subgroup.center ↥J' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      have h1 : (x : ↥K) ∈ R' := (QuotientGroup.eq_one_iff _).mp hx
      exact Subtype.ext (((hmemR' _).mp h1 g.1 g.2).symm)
    · intro hx
      have h1 : (x : ↥K) ∈ R' :=
        (hmemR' _).mpr fun y hy => (congrArg Subtype.val (hx ⟨y, hy⟩)).symm
      exact (QuotientGroup.eq_one_iff _).mpr h1
  set L' : Subgroup (↥K ⧸ R') := ψ.range with hL'
  have hL'eq : L' = J'.map φ := by rw [hL', MonoidHom.range_comp, Subgroup.range_subtype]
  have hL'n : L'.Normal := by
    rw [hL'eq]
    exact Subgroup.Normal.map hJn φ hφ
  have hL's : IsSimpleGroup ↥L' :=
    ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hψker)).isSimpleGroup
  have hL'nc : ∃ a b : ↥L', a * b ≠ b * a := by
    by_contra hcon
    have hcomm : ∀ a b : ↥L', a * b = b * a := fun a b => by
      by_contra h
      exact hcon ⟨a, b, h⟩
    have : Group.IsPerfect ↥J' := hJperf
    have : Group.IsPerfect ↥L' := Group.IsPerfect.range ψ
    have : Nontrivial ↥L' := hL's.toNontrivial
    have : IsMulCommutative ↥L' := isMulCommutative_iff.mpr hcomm
    exact Group.IsPerfect.not_isMulCommutative ↥L' ‹_›
  have hC' : Subgroup.centralizer (L' : Set (↥K ⧸ R')) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.mem_bot]
    suffices hx : x ∈ R' from (QuotientGroup.eq_one_iff x).mpr hx
    set X : Subgroup ↥K := (Subgroup.centralizer (L' : Set (↥K ⧸ R'))).comap φ
    have hxX : x ∈ X := hq
    have hcomm : ⁅J', X⁆ ≤ Subgroup.centralizer (J' : Set ↥K) := by
      rw [Subgroup.commutator_le]
      intro a ha w hw
      have h1 : ⁅a, w⁆ ∈ R' := by
        rw [← hker, MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp hw (φ a) ⟨⟨a, ha⟩, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((hmemR' _).mp h1 y hy).symm
    have hJX : ⁅J', X⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hJperf
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm)
    rw [hmemR']
    intro y hy
    have h1 : ⁅y, x⁆ ∈ ⁅J', X⁆ := Subgroup.commutator_mem_commutator hy hxX
    rw [hJX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hSK : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    have h := (isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ K) (K := K) (H := K) inf_le_right
      le_rfl).mpr hSyl
    rwa [Subgroup.subgroupOf_self] at h
  set S₀ : Subgroup ↥K := (T ⊓ K).subgroupOf K
  have hS' : IsSylowIn 2 (S₀.map φ) ⊤ := isSylowIn_two_map_top hφ hSK
  have hLS : L' ⊔ S₀.map φ = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, n, hn, hxsn⟩ := exists_mul_eq_of_pow_mem (p := 2) hJn h2q hSyl x.1 x.2
    have hx : x = (⟨s, hSyl.le hs⟩ : ↥K) * ⟨n, hJK hn⟩ := Subtype.ext hxsn
    rw [hx, QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨⟨s, hSyl.le hs⟩, hs, rfl⟩)
      (Subgroup.mem_sup_left ⟨⟨⟨n, hJK hn⟩, Subgroup.mem_subgroupOf.mpr hn⟩, rfl⟩)
  have hB'ne : (A.subgroupOf K).map φ ≠ ⊥ := by
    intro h
    apply hAR
    intro a ha
    have haK : a ∈ K := (hAK ha).2
    have h1 : φ ⟨a, haK⟩ ∈ (A.subgroupOf K).map φ := ⟨⟨a, haK⟩, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨a, haK⟩ : ↥K) ∈ R' := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h3 := (hmemR' _).mp h2 ⟨m, hJK hm⟩ (Subgroup.mem_subgroupOf.mpr hm)
    exact (congrArg Subtype.val h3).symm
  have hE' : ETwo (↥K ⧸ R') (S₀.map φ) ((A.subgroupOf K).map φ) := by
    have := hL'n
    have := hL's
    exact eTwo_of_normal_simple L' (S₀.map φ) ((A.subgroupOf K).map φ) hL'nc hC' hS' hLS hB'ne
  have hres : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) := by
    have hnormtop : ∀ g : ↥K, g ∈ Subgroup.normalizer (J' : Set ↥K) := fun g => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hJn]
      exact Subgroup.mem_top g
    have h2' : ∀ x : ↥K, ∃ k : ℕ, x ^ 2 ^ k ∈ J' := fun x => by
      obtain ⟨k, hk⟩ := h2q x.1 x.2
      exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
    have h1 : twoResidual (⊤ : Subgroup ↥K) ≤ J' :=
      twoResidual_le_of_isTwoQuotient le_top (fun g _ => hnormtop g) fun y _ => h2' y
    have h3 : perfectCore (⊤ : Subgroup ↥K) ≤ twoResidual (⊤ : Subgroup ↥K) :=
      perfectCore_le_of_sup_solvable (twoResidual_le ⊤)
        (Subgroup.Normal.subgroupOf
          (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))) _)
        (by rw [sup_comm]; exact (sup_twoResidual_eq hSK).symm)
        (isSolvable_of_isPGroup_two hSK.isPGroup)
    exact le_antisymm (h1.trans (le_perfectCore_of_perfect le_top hJperf')) h3
  have hker2 : Group.IsSolvable φ.ker := by
    rw [hker]
    exact isSolvable_of_isPGroup_two hR'2
  have hZ : IsTwoClosed ((CFSG.Open.pCore 2 (↥K ⧸ R')).comap φ) := by
    have := hL'n
    have := hL's
    rw [pCore_two_eq_bot_of_normal_simple L' hL'nc hC', MonoidHom.comap_bot, hker]
    refine ⟨R', ⟨le_rfl, hR'2, ?_⟩, ?_⟩
    · rw [Subgroup.relIndex_self]
      norm_num
    · rw [Subgroup.subgroupOf_self]
      infer_instance
  have hBS : A.subgroupOf K ≤ S₀ := fun a ha => ⟨(hAK ha).1, a.2⟩
  have hE : ETwo ↥K S₀ (A.subgroupOf K) :=
    eTwo_of_surjective φ hφ hZ hSK.isPGroup hBS hres hE'
  have hcard : Nat.card (barRad ↥K (A.subgroupOf K)) ≤ 2 ^ 1 := by
    have := hL'n
    have := hL's
    have h1 := card_barRad_eq_of_surjective φ hφ hker2 (A.subgroupOf K)
    rw [← h1]
    have hrad : CFSG.solvableRadical (↥K ⧸ R') = ⊥ :=
      solvableRadical_eq_bot_of_normal_simple L' hL'nc hC'
    have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical (↥K ⧸ R'))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hrad])
    unfold barRad
    rw [Subgroup.card_map_of_injective hinj, ← Subgroup.relIndex_ker, hker]
    have h2 : R'.relIndex (A.subgroupOf K) = Rg.relIndex A := by
      rw [hR']
      exact Subgroup.relIndex_subgroupOf (hAK.trans inf_le_right)
    rw [h2]
    simpa using hAI
  refine ⟨le_top, ?_, hSyl, Or.inr ⟨hE, hcard⟩⟩
  intro t ht
  rw [mem_tauOf] at ht
  obtain ⟨htT, -, hta⟩ := ht
  refine Subgroup.mem_inf.mpr ⟨htT, hC ⟨htT, ?_⟩⟩
  show t ∈ Subgroup.centralizer (A : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := hta a ha
  rw [hO2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end CFSG.Quasithin.E22S
