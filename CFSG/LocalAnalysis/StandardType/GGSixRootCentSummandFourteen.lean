module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandBasic
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise

section Dichotomy

variable {X : Type} [Group X]

theorem ggRCS_piece_le_or_commutator_le [Finite X] {p : ℕ} {V S Q U : Subgroup X}
    (hS : GGRCSPiece p V S Q) (hUV : U ≤ V) (hU : IsSubnormal U V) :
    S ≤ U ⊔ Q ∨ ⁅S, U⁆ ≤ Q := by
  obtain ⟨hSV, hsn, -, -, -, hQS, -, hQn, hq⟩ := hS
  have hQSn : (Q.subgroupOf S).Normal := ggRCS_normal_subgroupOf hSV hQS hQn
  set π := QuotientGroup.mk' (Q.subgroupOf V) with hπ
  have hC := ggRCS_isComponent_of_isComponentOf_top
    (ggRCS_isComponentOf_map_quot hSV hsn (@hq hQSn))
  have hU' : ((U.subgroupOf V).map π).IsSubnormal := by
    have h1 : IsSubnormal (U.subgroupOf V) ⊤ := by
      have h := ggAssemblyIsSubnormal_subgroupOf hU V
      rwa [Subgroup.subgroupOf_self] at h
    have h2 := ggIsSubnormal_map π h1
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact ggRCS_isSubnormal_of_top h2 rfl
  have hπ1 : ∀ v : ↥V, π v = 1 ↔ (v : X) ∈ Q := fun v => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rcases CFSG.LocalCores.component_subnormal_subgroup hC hU' with hle | hc
  · left
    intro s hs
    obtain ⟨u, hu, hus⟩ := hle ⟨⟨s, hSV hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have h1 : π (u⁻¹ * ⟨s, hSV hs⟩) = 1 := by rw [map_mul, map_inv, hus, inv_mul_cancel]
    have hq' : (u : X)⁻¹ * s ∈ Q := by simpa using (hπ1 _).mp h1
    have hs' : s = (u : X) * ((u : X)⁻¹ * s) := by group
    rw [hs']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hu))
      (Subgroup.mem_sup_right hq')
  · right
    rw [Subgroup.commutator_le]
    intro s hs u hu
    have h1 : ⁅π ⟨s, hSV hs⟩, π ⟨u, hUV hu⟩⁆ ∈
        ⁅(S.subgroupOf V).map π, (U.subgroupOf V).map π⁆ :=
      Subgroup.commutator_mem_commutator ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hc, Subgroup.mem_bot, ← map_commutatorElement] at h1
    have h2 := (hπ1 _).mp h1
    simpa [commutatorElement_def] using h2

theorem ggRCS_le_of_le_sup_two [Finite X] {S T Q : Subgroup X} (hperf : ⁅S, S⁆ = S)
    (hST : S ≤ Subgroup.normalizer (T : Set X)) (hQS : Q ≤ S) (hQ2 : IsPGroup 2 Q)
    (hle : S ≤ T ⊔ Q) : S ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := S ⊔ T with hW
  have hTW : T ≤ W := le_sup_right
  have hSW : S ≤ W := le_sup_left
  have hTn : (T.subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTW]
    intro t w ht hw
    have hwN : w ∈ Subgroup.normalizer (T : Set X) := (sup_le hST Subgroup.le_normalizer) hw
    exact (Subgroup.mem_normalizer_iff.mp hwN t).mp ht
  set π := QuotientGroup.mk' (T.subgroupOf W) with hπ
  have hπ1 : ∀ w : ↥W, π w = 1 ↔ (w : X) ∈ T := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hSQ : (S.subgroupOf W).map π ≤ (Q.subgroupOf W).map π := by
    rintro _ ⟨s, hs, rfl⟩
    have hsQT : (s : X) ∈ (Q : Set X) * (T : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q T (hQS.trans hST), sup_comm]
      exact hle (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨q, hq, t, ht, hqt⟩ := Set.mem_mul.mp hsQT
    refine ⟨⟨q, hSW (hQS hq)⟩, Subgroup.mem_subgroupOf.mpr hq, ?_⟩
    have h1 : π (⟨q, hSW (hQS hq)⟩⁻¹ * s) = 1 := by
      rw [hπ1]
      have : ((⟨q, hSW (hQS hq)⟩⁻¹ * s : ↥W) : X) = t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hqt, inv_mul_cancel_left]
      rw [this]
      exact ht
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hQW2 : IsPGroup 2 ↥(Q.subgroupOf W) := by
    intro y
    obtain ⟨k, hk⟩ := hQ2 ⟨((y : ↥W) : X), Subgroup.mem_subgroupOf.mp y.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hnil : Group.IsNilpotent ↥((Q.subgroupOf W).map π) := (hQW2.map π).isNilpotent
  have hperf' : ⁅S.subgroupOf W, S.subgroupOf W⁆ = S.subgroupOf W := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSW, hperf]
  have hbot := CFSG.SeitzReduction.perfect_eq_bot_of_le inferInstance
    (by rw [← Subgroup.map_commutator, hperf']) hSQ
  intro s hs
  have h1 : π ⟨s, hSW hs⟩ ∈ (S.subgroupOf W).map π := ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (hπ1 _).mp h1

end Dichotomy

section Normalizer

variable {X : Type} [Group X] [Finite X] {p : ℕ}

omit [Finite X] in
theorem ggRCS_mul_eq_one_of_two (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ2 : IsPGroup 2 Q) {x y : X} (hxy : Commute x y) {n : ℕ} (hx : x ^ p ^ n = 1)
    (hy : y ^ p ^ n = 1) (hQ : x * y ∈ Q) : x * y = 1 := by
  obtain ⟨k, hk⟩ := hQ2 ⟨x * y, hQ⟩
  have h2 : (x * y) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hp' : (x * y) ^ p ^ n = 1 := by rw [hxy.mul_pow, hx, hy, one_mul]
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : orderOf (x * y) = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hp') hcop)
    (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp h1

theorem ggRCS_le_normalizer_of_component [hp : Fact p.Prime] (hp2 : p ≠ 2) {V E S Q : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) {e : X} (heE : e ∈ E)
    (he1 : e ≠ 1) (hS : GGRCSPiece p V S Q) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hKp : p ∣ Nat.card K) (heK : e ∈ Subgroup.normalizer (K : Set X)) :
    S ≤ Subgroup.normalizer (K : Set X) := by
  have hSV : S ≤ V := hS.1
  have hperf : ⁅S, S⁆ = S := hS.2.2.1
  have hQS : Q ≤ S := hS.2.2.2.2.2.1
  have hQ2 : IsPGroup 2 Q := hS.2.2.2.2.2.2.1
  have hUN : Subgroup.normalClosure (K : Set X) ≤ Subgroup.normalizer (K : Set X) := by
    show Subgroup.closure (Group.conjugatesOfSet (K : Set X)) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have hmem : c * a * c⁻¹ ∈ conjSub c K := ggConj_mem_conjSub c ha
    by_cases hcK : conjSub c K = K
    · exact Subgroup.le_normalizer (hcK ▸ hmem)
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK c) hcK hmem hy).symm
  set U := Subgroup.normalClosure (K : Set X) with hU
  have hUn : U.Normal := Subgroup.normalClosure_normal
  have hUV : ((V ⊓ U).subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro a v ha hv
    exact ⟨V.mul_mem (V.mul_mem hv ha.1) (V.inv_mem hv), hUn.conj_mem a ha.2 v⟩
  rcases ggRCS_piece_le_or_commutator_le hS inf_le_left
      (ggIsSubnormal_of_normal inf_le_left hUV) with hle | hc
  · have hSN : S ≤ Subgroup.normalizer ((V ⊓ U : Subgroup X) : Set X) := fun s hs =>
      ggMem_normalizer_inf (Subgroup.le_normalizer (hSV hs))
        (Subgroup.le_normalizer_of_normal (H := U) (Subgroup.mem_top s))
    exact (ggRCS_le_of_le_sup_two hperf hSN hQS hQ2 hle).trans (inf_le_right.trans hUN)
  intro l hl
  by_contra hlK
  have hne : conjSub l K ≠ K := fun heq =>
    hlK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  obtain ⟨R, hRVK, hRp, hR⟩ := hfus.exists_sylow_le hE heE he1 heK
  refine ggNot_dvd_card_of_central hK.1.1.commutator_eq_top (fun y hy => ?_) hR hKp
  have hyV : y ∈ V := (hRVK hy).1
  have hyK : y ∈ K := (hRVK hy).2
  obtain ⟨n, hn⟩ := hRp ⟨y, hy⟩
  have hyn : y ^ p ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hcomm : l * y * l⁻¹ * y⁻¹ ∈ Q := by
    have h1 : ⁅l, y⁆ ∈ ⁅S, V ⊓ U⁆ :=
      Subgroup.commutator_mem_commutator hl ⟨hyV, Subgroup.subset_normalClosure hyK⟩
    simpa [commutatorElement_def] using hc h1
  have hly : l * y * l⁻¹ ∈ conjSub l K := ggConj_mem_conjSub l hyK
  have hc1 : Commute (l * y * l⁻¹) y⁻¹ :=
    ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK l) hne hly (K.inv_mem hyK)
  have hpow1 : (l * y * l⁻¹) ^ p ^ n = 1 := by
    rw [conj_pow, hyn, mul_one, mul_inv_cancel]
  have hpow2 : y⁻¹ ^ p ^ n = 1 := by rw [inv_pow, hyn, inv_one]
  have h1 := ggRCS_mul_eq_one_of_two hp.out hp2 hQ2 hc1 hpow1 hpow2 hcomm
  have hyl : y ∈ conjSub l K := by
    have : l * y * l⁻¹ = y := by
      calc l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
        _ = y := by rw [h1, one_mul]
    rw [← this]
    exact hly
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (ggCommute_of_isComponent_ne hK (ggIsComponent_conjSub hK l) hne hyl hx).symm

end Normalizer

section Centralizer

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem ggRCS_mem_normalizer_of_conj_mem {T : Subgroup X} {k : X}
    (h : ∀ t ∈ T, k * t * k⁻¹ ∈ T) : k ∈ Subgroup.normalizer (T : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]

omit [Finite X] in
theorem ggRCS_mem_of_pow_mem (hp : p.Prime) {R T K : Subgroup X} (hRT : R ≤ T) (hTK : T ≤ K)
    (hR : ¬ p ∣ R.relIndex K) {k : X} (hkK : k ∈ K)
    (hkT : k ∈ Subgroup.normalizer (T : Set X)) {n : ℕ} (hkn : k ^ p ^ n ∈ T) : k ∈ T := by
  set W := Subgroup.zpowers k ⊔ T with hW
  have hTW : T ≤ W := le_sup_right
  have hWK : W ≤ K := sup_le (Subgroup.zpowers_le.mpr hkK) hTK
  have hkW : k ∈ W := le_sup_left (a := Subgroup.zpowers k) (Subgroup.mem_zpowers k)
  have h1 : T.relIndex W ∣ R.relIndex K := by
    have e1 := Subgroup.relIndex_mul_relIndex R T W hRT hTW
    have e2 := Subgroup.relIndex_mul_relIndex R W K (hRT.trans hTW) hWK
    exact ⟨R.relIndex T * W.relIndex K, by rw [← e2, ← e1]; ring⟩
  have hTn : (T.subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTW]
    intro t w ht hw
    have hwN : w ∈ Subgroup.normalizer (T : Set X) :=
      (sup_le (Subgroup.zpowers_le.mpr hkT) Subgroup.le_normalizer) hw
    exact (Subgroup.mem_normalizer_iff.mp hwN t).mp ht
  set g : ↥W ⧸ T.subgroupOf W := QuotientGroup.mk ⟨k, hkW⟩ with hg
  have hgen : ∀ x : ↥W ⧸ T.subgroupOf W, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    have hw : (w : X) ∈ (Subgroup.zpowers k : Set X) * (T : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ T (Subgroup.zpowers_le.mpr hkT)]
      exact w.2
    obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.mp hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨i, ?_⟩
    change g ^ i = QuotientGroup.mk w
    rw [hg, ← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((((⟨k, hkW⟩ : ↥W) ^ i)⁻¹ * w : ↥W) : X) = t := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, ← hat,
        inv_mul_cancel_left]
    rw [this]
    exact ht
  have h2 : T.relIndex W ∣ p ^ n := by
    rw [Subgroup.relIndex, Subgroup.index, ← orderOf_eq_card_of_forall_mem_zpowers hgen]
    apply orderOf_dvd_of_pow_eq_one
    rw [hg, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hkn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hj0 : j = 0 := by
    by_contra hj0
    exact hR ((hj ▸ dvd_pow_self p hj0).trans h1)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj hkW

theorem ggRCS_le_centralizer_of_le_sup {S Y Q K : Subgroup X} (hperf : ⁅S, S⁆ = S)
    (hSK : S ≤ Subgroup.normalizer (K : Set X)) (hYK : Y ≤ K) (hQ2 : IsPGroup 2 Q)
    (hle : S ≤ Y ⊔ Subgroup.centralizer (K : Set X)) (hc : ⁅S, Y⁆ ≤ Q ⊓ K) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set X) with hC
  set Nn := Subgroup.normalizer (K : Set X) with hNn
  have hCN : C ≤ Nn := Subgroup.centralizer_le_normalizer _
  have hYN : Y ≤ Nn := hYK.trans Subgroup.le_normalizer
  have hQKN : Q ⊓ K ≤ Nn := inf_le_right.trans Subgroup.le_normalizer
  have hCn : (C.subgroupOf Nn).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCN]
    intro c n hc hn
    exact (Subgroup.mem_normalizer_iff.mp (ggMem_normalizer_centralizer hn) c).mp hc
  set ρ := QuotientGroup.mk' (C.subgroupOf Nn) with hρ
  have hρ1 : ∀ w : ↥Nn, ρ w = 1 ↔ (w : X) ∈ C := fun w => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hSY : (S.subgroupOf Nn).map ρ ≤ (Y.subgroupOf Nn).map ρ := by
    rintro _ ⟨s, hs, rfl⟩
    have hsYC : (s : X) ∈ (Y : Set X) * (C : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y C (fun y hy =>
        ggMem_normalizer_centralizer (hYN hy))]
      exact hle (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨y, hy, c, hc', hyc⟩ := Set.mem_mul.mp hsYC
    refine ⟨⟨y, hYN hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    have h1 : ρ (⟨y, hYN hy⟩⁻¹ * s) = 1 := by
      rw [hρ1]
      have : ((⟨y, hYN hy⟩⁻¹ * s : ↥Nn) : X) = c := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hyc, inv_mul_cancel_left]
      rw [this]
      exact hc'
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hcomm : ⁅S.subgroupOf Nn, Y.subgroupOf Nn⁆ ≤ (Q ⊓ K).subgroupOf Nn := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf]
    have h1 := hc (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb))
    simpa [commutatorElement_def] using h1
  have hperf' : ⁅S.subgroupOf Nn, S.subgroupOf Nn⁆ = S.subgroupOf Nn := by
    apply Subgroup.map_injective Nn.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSK, hperf]
  have hSQ : (S.subgroupOf Nn).map ρ ≤ ((Q ⊓ K).subgroupOf Nn).map ρ :=
    calc (S.subgroupOf Nn).map ρ = ⁅(S.subgroupOf Nn).map ρ, (S.subgroupOf Nn).map ρ⁆ := by
          rw [← Subgroup.map_commutator, hperf']
      _ ≤ ⁅(S.subgroupOf Nn).map ρ, (Y.subgroupOf Nn).map ρ⁆ := Subgroup.commutator_mono le_rfl hSY
      _ = (⁅S.subgroupOf Nn, Y.subgroupOf Nn⁆).map ρ := (Subgroup.map_commutator _ _ _).symm
      _ ≤ ((Q ⊓ K).subgroupOf Nn).map ρ := Subgroup.map_mono hcomm
  have hQK2 : IsPGroup 2 ↥((Q ⊓ K).subgroupOf Nn) := by
    intro y
    obtain ⟨k, hk⟩ := hQ2 ⟨((y : ↥Nn) : X), (Subgroup.mem_subgroupOf.mp y.2).1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hnil : Group.IsNilpotent ↥(((Q ⊓ K).subgroupOf Nn).map ρ) := (hQK2.map ρ).isNilpotent
  have hbot := CFSG.SeitzReduction.perfect_eq_bot_of_le inferInstance
    (by rw [← Subgroup.map_commutator, hperf']) hSQ
  intro s hs
  have h1 : ρ ⟨s, hSK hs⟩ ∈ (S.subgroupOf Nn).map ρ := ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (hρ1 _).mp h1

theorem ggRCS_le_or_le_centralizer [hp : Fact p.Prime] {V E S Q : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hS : GGRCSPiece p V S Q) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hOut : Group.IsSolvable (Outer K))
    (hSK : S ≤ Subgroup.normalizer (K : Set X)) :
    S ≤ K ∨ S ≤ Subgroup.centralizer (K : Set X) := by
  have hS' := hS
  obtain ⟨hSV, -, hperf, -, hgen, hQS, hQ2, hQn, -⟩ := hS
  have hQV : Q ≤ V := hQS.trans hSV
  have hSKC : S ≤ K ⊔ Subgroup.centralizer (K : Set X) :=
    CFSG.SeitzReduction.perfect_le_sup_centralizer hOut hperf hSK
  have hKsn : IsSubnormal (V ⊓ K) V := by
    have h1 : IsSubnormal K ⊤ := (ggAssemblyIsSubnormal_iff le_top).mpr hK.2.subgroupOf
    have h2 := ggIsSubnormal_inf h1 V
    rwa [inf_comm, top_inf_eq] at h2
  rcases ggRCS_piece_le_or_commutator_le hS' inf_le_left hKsn with hle | hc
  · left
    have hSN : S ≤ Subgroup.normalizer ((V ⊓ K : Subgroup X) : Set X) := fun s hs =>
      ggMem_normalizer_inf (Subgroup.le_normalizer (hSV hs)) (hSK hs)
    exact (ggRCS_le_of_le_sup_two hperf hSN hQS hQ2 hle).trans inf_le_right
  right
  set C := Subgroup.centralizer (K : Set X) with hC
  obtain ⟨e, he, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
  obtain ⟨R, hRVK, -, hR⟩ := hfus.exists_sylow_le hE he he1 (hEK he)
  have hcK : ∀ s ∈ S, ∀ y ∈ V ⊓ K, s * y * s⁻¹ * y⁻¹ ∈ Q ⊓ K := by
    intro s hs y hy
    have h1 : ⁅s, y⁆ ∈ ⁅S, V ⊓ K⁆ := Subgroup.commutator_mem_commutator hs hy
    refine ⟨by simpa [commutatorElement_def] using hc h1, ?_⟩
    have hsy : s * y * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hSK hs) y).mp hy.2
    exact K.mul_mem hsy (K.inv_mem hy.2)
  have key : ∀ s ∈ S, (∃ n : ℕ, s ^ p ^ n = 1) → s ∈ (V ⊓ K) ⊔ C := by
    rintro s hs ⟨n, hn⟩
    obtain ⟨k, hk, c, hcC, rfl⟩ :=
      CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute
        (fun k hk c hc => (Subgroup.mem_centralizer_iff.mp hc) k hk) (hSKC hs)
    have hkc : Commute k c := (Subgroup.mem_centralizer_iff.mp hcC) k hk
    have hconj : ∀ y ∈ K, (k * c) * y * (k * c)⁻¹ = k * y * k⁻¹ := by
      intro y hy
      have hcy : c * y = y * c := ((Subgroup.mem_centralizer_iff.mp hcC) y hy).symm
      calc (k * c) * y * (k * c)⁻¹ = k * (c * y) * c⁻¹ * k⁻¹ := by group
        _ = k * (y * c) * c⁻¹ * k⁻¹ := by rw [hcy]
        _ = k * y * k⁻¹ := by group
    set T := R ⊔ (Q ⊓ K) ⊔ (K ⊓ C) with hT
    have hTK : T ≤ K := sup_le (sup_le (hRVK.trans inf_le_right) inf_le_right) inf_le_left
    have hRT : R ≤ T := le_sup_left.trans le_sup_left
    have hQKT : Q ⊓ K ≤ T := le_sup_right.trans le_sup_left
    have hZT : K ⊓ C ≤ T := le_sup_right
    have hkT : k ∈ Subgroup.normalizer (T : Set X) := by
      refine ggRCS_mem_normalizer_of_conj_mem fun t ht => ?_
      have hle' : T ≤ T.comap (MulAut.conj k).toMonoidHom := by
        refine sup_le (sup_le (fun r hr => ?_) (fun q hq => ?_)) (fun z hz => ?_)
        · have hrVK := hRVK hr
          have h1 := hcK (k * c) hs r hrVK
          rw [hconj r hrVK.2] at h1
          show k * r * k⁻¹ ∈ T
          have : k * r * k⁻¹ = (k * r * k⁻¹ * r⁻¹) * r := by group
          rw [this]
          exact T.mul_mem (hQKT h1) (hRT hr)
        · show k * q * k⁻¹ ∈ T
          rw [← hconj q hq.2]
          refine hQKT ⟨?_, ?_⟩
          · exact (Subgroup.normal_subgroupOf_iff hQV).mp hQn q (k * c) hq.1 (hSV hs)
          · exact (Subgroup.mem_normalizer_iff.mp (hSK hs) q).mp hq.2
        · show k * z * k⁻¹ ∈ T
          have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hz.2) k hk
          rw [hkz, mul_inv_cancel_right]
          exact hZT hz
      exact hle' ht
    have hkn : k ^ p ^ n ∈ T := by
      have h1 : k ^ p ^ n * c ^ p ^ n = 1 := by rw [← hkc.mul_pow, hn]
      have h2 : k ^ p ^ n = (c ^ p ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
      refine hZT ⟨K.pow_mem hk _, ?_⟩
      rw [h2]
      exact C.inv_mem (C.pow_mem hcC _)
    have hkT' := ggRCS_mem_of_pow_mem hp.out hRT hTK hR hk hkT hkn
    have hTle : T ≤ (V ⊓ K) ⊔ C :=
      sup_le (sup_le (hRVK.trans le_sup_left)
        ((le_inf (inf_le_left.trans hQV) inf_le_right).trans le_sup_left))
        (inf_le_right.trans le_sup_right)
    exact Subgroup.mul_mem _ (hTle hkT') (Subgroup.mem_sup_right hcC)
  have hS2 : S ≤ (V ⊓ K) ⊔ C :=
    hgen.trans ((Subgroup.closure_le _).mpr fun s ⟨hs, hn⟩ => key s hs hn)
  have hc' : ⁅S, V ⊓ K⁆ ≤ Q ⊓ K := by
    rw [Subgroup.commutator_le]
    intro s hs y hy
    simpa [commutatorElement_def] using hcK s hs y hy
  exact ggRCS_le_centralizer_of_le_sup hperf hSK inf_le_right hQ2 hS2 hc'

end Centralizer

section Main

variable {X : Type} [Group X] [Finite X] {p : ℕ}

omit [Finite X] in
theorem ggRCS_inf_eq_bot_of_two (hp : p.Prime) (hp2 : p ≠ 2) {Q P : Subgroup X}
    (hQ2 : IsPGroup 2 Q) (hP : IsPGroup p P) : Q ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hQ2 ⟨x, hx.1⟩
  obtain ⟨b, hb⟩ := hP ⟨x, hx.2⟩
  have h2 : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hpb : x ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcop : Nat.Coprime (p ^ b) (2 ^ a) :=
    Nat.Coprime.pow b a ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpb) hcop)
    (orderOf_dvd_of_pow_eq_one h2)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

theorem ggRCS_le_centralizer_of_normal {V S Q F : Subgroup X} (hS : GGRCSPiece p V S Q)
    (hFn : F.Normal) (hFV : F ≤ V) (hSF : ¬ S ≤ F ⊔ Q) (hQF : Q ⊓ F = ⊥) :
    S ≤ Subgroup.centralizer (F : Set X) := by
  rcases ggRCS_piece_le_or_commutator_le hS hFV
      (ggIsSubnormal_of_normal hFV (hFn.subgroupOf V)) with hle | hc
  · exact absurd hle hSF
  · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hQF]
    exact le_inf hc (Subgroup.commutator_le_right S F)

theorem ggRCS_exists_component [hp : Fact p.Prime] (hp2 : p ≠ 2) (hO2 : CFSG.pCore 2 X = ⊥)
    (hOut : ∀ K : Subgroup X, CFSG.IsComponent K → Group.IsSolvable (Outer K))
    {V E S : Subgroup X} (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hS : GGRCSQuasiPiece p V S) :
    ∃ K : Subgroup X, CFSG.IsComponent K ∧ S ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hSQ⟩ := hS
  have hS' : GGRCSQuasiPiece p V S := ⟨Q, hSQ⟩
  obtain ⟨hSV, hsn, hperf, hpS, -, hQS, hQ2, hQn, -⟩ := id hSQ
  have hQV : Q ≤ V := hQS.trans hSV
  have hQsol : Group.IsSolvable ↥Q := by
    have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    infer_instance
  have hSnot : ∀ A : Subgroup X, Group.IsSolvable A → ¬ S ≤ A := by
    intro A hA hle
    have h1 := CFSG.SeitzReduction.perfect_eq_bot_of_le hA hperf hle
    rw [h1, Subgroup.card_bot] at hpS
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp hpS)
  by_contra hcon
  push Not at hcon
  have hOV : LargeEvenPPrimeCore p X ≤ V := hfus.pPrimeCore_le hp.out hE hEcard
  have hSO := ggRCS_le_centralizer_pPrimeCore hp.out hp2 hO2 hOV hS'
  have hPn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hPV : CFSG.pCore p X ≤ V := hfus.pCore_le hp.out hE hEcard p
  have hSP : S ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
    refine ggRCS_le_centralizer_of_normal hSQ hPn hPV ?_
      (ggRCS_inf_eq_bot_of_two hp.out hp2 hQ2 CFSG.pCore_isPGroup)
    intro hle
    have hSN : S ≤ Subgroup.normalizer ((CFSG.pCore p X : Subgroup X) : Set X) :=
      fun s _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top s)
    have hSP' := ggRCS_le_of_le_sup_two hperf hSN hQS hQ2 hle
    have : Group.IsNilpotent ↥(CFSG.pCore p X) := CFSG.pCore_isPGroup.isNilpotent
    exact hSnot _ inferInstance hSP'
  have hSF : S ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.le_centralizer_iff]
    refine iSup_le fun q => ?_
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact Subgroup.le_centralizer_iff.mp hSP
    · have hq : (q.1.1).Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hcop : Nat.Coprime p (Nat.card (CFSG.pCore q.1.1 X)) := by
        have : Fact (q.1.1).Prime := ⟨hq⟩
        obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := q.1.1) (G := X))
        rw [hm]
        exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp.out hq).mpr (Ne.symm hqp))
      have hle : CFSG.pCore q.1.1 X ≤ LargeEvenPPrimeCore p X :=
        le_sSup ⟨CFSG.pCore_normal, hcop⟩
      exact hle.trans (Subgroup.le_centralizer_iff.mp hSO)
  have hcomp : ∀ K : Subgroup X, CFSG.IsComponent K → S ≤ Subgroup.centralizer (K : Set X) := by
    intro K hK
    by_cases hKO : K ≤ LargeEvenPPrimeCore p X
    · exact hSO.trans (Subgroup.centralizer_le hKO)
    have hKp : p ∣ Nat.card K := by
      by_contra hnd
      exact hKO (ggLe_pPrimeCore_of_isSubnormal hK.2 hnd)
    by_cases hKV : K ≤ V
    · have hKc : IsComponentOf K V := (isComponentOf_iff_isComponent_subgroupOf hKV).mpr
        (CFSG.LocalCores.component_overgroup hK hKV)
      have hQK : Q ≤ Subgroup.centralizer (K : Set X) := by
        rcases ggComponent_le_or_commute hKc hQn.isSubnormal with hle | hc
        · exact absurd hle (ggComponent_not_le_of_isSolvable hKc hQsol)
        · intro q hq
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          exact hc k hk q ⟨hQV hq, hq⟩
      rcases ggComponent_le_or_commute hKc ((ggAssemblyIsSubnormal_iff hSV).mp hsn) with
        hle | hc
      · rcases ggRCS_piece_le_or_commutator_le hSQ hKV hKc.2.1 with hle' | hc'
        · have hSN : S ≤ Subgroup.normalizer (K : Set X) := hle'.trans
            (sup_le Subgroup.le_normalizer (hQK.trans (Subgroup.centralizer_le_normalizer _)))
          exact absurd (ggRCS_le_of_le_sup_two hperf hSN hQS hQ2 hle') (hcon K hK)
        · exfalso
          have hKQ : K ≤ Q :=
            calc K = ⁅K, K⁆ := (ggComponent_perfect hKc).symm
              _ ≤ ⁅S, K⁆ := Subgroup.commutator_mono hle le_rfl
              _ ≤ Q := hc'
          exact ggComponent_not_le_of_isSolvable hKc hQsol hKQ
      · intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact hc k hk s ⟨hSV hs, hs⟩
    · have hEK := ggLemmaThreeThirteen_top hfus hE hEcard hK hKp hKV
      obtain ⟨e, he, he1⟩ := ggExists_ne_one_of_card hp.out hEcard
      have hSN := ggRCS_le_normalizer_of_component hp2 hfus hE he he1 hSQ hK hKp (hEK he)
      rcases ggRCS_le_or_le_centralizer hfus hE hEcard hSQ hK hEK (hOut K hK) hSN with h | h
      · exact absurd h (hcon K hK)
      · exact h
  have hLay : S ≤ Subgroup.centralizer (CFSG.layer X : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    show sSup {K : Subgroup X | CFSG.IsComponent K} ≤ _
    exact sSup_le fun K hK => Subgroup.le_centralizer_iff.mp (hcomp K hK)
  have hFs : S ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    show CFSG.fittingSubgroup X ⊔ CFSG.layer X ≤ _
    exact sup_le (Subgroup.le_centralizer_iff.mp hSF) (Subgroup.le_centralizer_iff.mp hLay)
  have hSle : S ≤ CFSG.generalizedFitting X :=
    hFs.trans (CFSG.centralizer_generalizedFitting_le X)
  have hab : ⁅S, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hSle.trans (Subgroup.le_centralizer_iff.mp hFs))
  rw [hperf] at hab
  rw [hab, Subgroup.card_bot] at hpS
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp hpS)

end Main

end CFSG.StandardType
