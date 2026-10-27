module

public import CFSG.Quasithin.H13.L32A5Props
public import CFSG.Quasithin.H13.L32AHStr

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups Pointwise commutatorElement

theorem sl24_order_three : ∀ A : SL(2, F4), A ^ 3 = 1 → A ≠ 1 → ∀ v : Fin 2 → F4,
    (A : Matrix (Fin 2) (Fin 2) F4).mulVec ((A : Matrix (Fin 2) (Fin 2) F4).mulVec v) +
      (A : Matrix (Fin 2) (Fin 2) F4).mulVec v + v = 0 := by
  decide +kernel

theorem sl24_two_elt : ∀ A : SL(2, F4), A ^ 4 = 1 → A ^ 2 = 1 := by
  decide +kernel

theorem sl24_card_fix : ∀ A : SL(2, F4), A ^ 2 = 1 → A ≠ 1 →
    (Finset.univ.filter fun v : Fin 2 → F4 => (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = v).card =
      4 := by
  decide +kernel

theorem sl24_fix_comm : ∀ A : SL(2, F4), A ^ 2 = 1 → ∀ v : Fin 2 → F4,
    (A : Matrix (Fin 2) (Fin 2) F4).mulVec ((A : Matrix (Fin 2) (Fin 2) F4).mulVec v + v) =
      (A : Matrix (Fin 2) (Fin 2) F4).mulVec v + v := by
  decide +kernel

theorem f4_key : ∀ v w : Fin 2 → F4, v + -w + -(w + v) = 0 := by
  decide

theorem f4_key2 : ∀ a b v : Fin 2 → F4, a + b + v = 0 → v + -(a + -b) = 0 := by
  decide

variable {G : Type} [Group G]

theorem mem_u0 {T V : Subgroup G} {u : G} :
    u ∈ u0 T V ↔ u ∈ fsuU T V ∧ u ∈ Subgroup.normalizer (fsuV1 T V : Set G) ∧
      ∀ k ∈ kz T V, u * k * u⁻¹ * k⁻¹ ∈ fsuV1 T V := Iff.rfl

variable [Finite G] {T L V : Subgroup G}

theorem isElemAbelian_fsuU_of (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    IsElemAbelian 2 (fsuU T V) := by
  rw [F7.isElemAbelian_iff]
  have hV := (hMod G T L V h.hyp h.fsu).1
  refine ⟨fun x hx y hy => fsuU_comm h hx hy, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, -, v, hv, rfl⟩ := hx
    rw [conj_pow, F7.isElemAbelian_pow_eq_one hV hv]
    group
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (fsuU_comm h ha hb) 2), iha, ihb, one_mul]
  | inv a _ iha =>
    rw [inv_pow, iha, inv_one]

theorem mem_u0_iff (h : Hyp147 G T L V) (hMod : StmtL32NModule) {u : G} :
    u ∈ u0 T V ↔ u ∈ fsuU T V ∧ ∀ k ∈ kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  rw [mem_u0]
  constructor
  · rintro ⟨hu, -, hk⟩
    refine ⟨hu, fun k hk' => ?_⟩
    have := inv_mem (hk k hk')
    rwa [show (u * k * u⁻¹ * k⁻¹)⁻¹ = k * u * k⁻¹ * u⁻¹ by group] at this
  · rintro ⟨hu, hk⟩
    refine ⟨hu, ?_, fun k hk' => ?_⟩
    · have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
      exact F8.le_normalizer_of_le (isElemAbelian_fsuU_of h hMod) hV1U hu
    · have := inv_mem (hk k hk')
      rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ by group] at this


theorem isL24Section_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    IsL24Section (kz T V) (fsuU T V) (u0 T V) := by
  obtain ⟨U₀, hU₀, hL24⟩ := (h63 G T L V h).2.2.2.2.2.2
  have e : U₀ = u0 T V := by
    ext u
    rw [hU₀, mem_u0_iff h hMod]
  rwa [← e]

theorem hz_le_normalizer_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    hz T V ≤ Subgroup.normalizer (u0 T V : Set G) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hHN : hz T V = Subgroup.normalizer (fsuV1 T V : Set G) :=
    (normalizer_eq_centralizer_of_card_two hV1).symm
  exact le_normalizer_centralizerMod hHN.le (hHN.le.trans (le_normalizer_conjClosure V _))
    (le_normalizer_oTwoUpper (hz T V))


theorem fsuV1_le_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) : fsuV1 T V ≤ u0 T V := by
  intro z hz0
  refine (mem_u0_iff h hMod).mpr ⟨inf_le_left.trans (le_conjClosure V _) hz0, fun k hk => ?_⟩
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  rw [(Subgroup.mem_centralizer_iff.mp hkH z hz0).symm, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem l1_le_kz (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    L₁Of L (fsuV1 T V) ≤ kz T V := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  rw [← lOne_eq_L₁Of]
  refine oTwoUpper_mono (inf_le_right.trans ?_)
  rw [normalizer_eq_centralizer_of_card_two hV1]

omit [Finite G] in
theorem l24_ker_iff {X Y : Subgroup G} {β : ↥X →* Multiplicative (Fin 2 → F4)}
    (hβk : β.ker = Y.subgroupOf X) (x : ↥X) :
    β x = 1 ↔ (x : G) ∈ Y := by
  rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]

theorem inf_u0_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) : V ⊓ u0 T V = fsuV1 T V := by
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hV1 : fsuV1 T V ≤ V ⊓ u0 T V := le_inf inf_le_left (fsuV1_le_u0 h hMod)
  have hN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer ((V ⊓ u0 T V : Subgroup G) : Set G) := by
    intro g hg
    have hgV : g ∈ Subgroup.normalizer (V : Set G) :=
      hLTV (sup_le_sup_right (L32NSet14.Setting.L1_le.trans inf_le_left) T hg)
    have hgU : g ∈ Subgroup.normalizer (u0 T V : Set G) :=
      hz_le_normalizer_u0 h hMod (hF.L₁T_le_H hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp hgV x, Subgroup.mem_normalizer_iff.mp hgU x]
  rcases hF.irred _ hV1 inf_le_left hN with he | he
  · exact he
  · exfalso
    have hVU0 : V ≤ u0 T V := he.symm.le.trans inf_le_right
    have hUU0 : fsuU T V ≤ u0 T V := by
      rw [fsuU_eq_conjClosure_hz hMod h]
      exact conjClosure_le fun k hk v hv =>
        (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_u0 h hMod hk) v).mp (hVU0 hv)
    obtain ⟨-, π, β, -, -, hβs, hβk, -⟩ := isL24Section_u0 h hMod h63
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ![1, 0])
    have h1 : β u = 1 := (l24_ker_iff hβk u).mpr (hUU0 u.2)
    rw [h1] at hu
    exact absurd hu (by decide)

theorem relIndex_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    (u0 T V).relIndex (fsuU T V) = 16 := by
  obtain ⟨-, π, β, -, -, hβs, hβk, -⟩ := isL24Section_u0 h hMod h63
  rw [Subgroup.relIndex, ← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

theorem relIndex_sup_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    (u0 T V).relIndex (V ⊔ u0 T V) = 4 ∧ (V ⊔ u0 T V).relIndex (fsuU T V) = 4 := by
  obtain ⟨hVe, hV8, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hUe := isElemAbelian_fsuU_of h hMod
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [F7.isElemAbelian_comm hUe (hVU hv) (hU0U hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxU : x ∈ fsuU T V := by
        have := mul_mem (mul_mem (inv_mem (hVU hv)) (hU0U hx)) (hVU hv)
        rwa [show v⁻¹ * (v * x * v⁻¹) * v = x by group] at this
      rwa [F7.isElemAbelian_comm hUe (hVU hv) hxU, mul_inv_cancel_right] at hx
  have h1 := L32NSet14.card_sup_mul_card_inf hVN
  rw [inf_u0_eq h hMod h63 hF, hV8, hV1] at h1
  have hpos : 0 < Nat.card ↥(u0 T V) := Nat.card_pos
  have h4 : (u0 T V).relIndex (V ⊔ u0 T V) = 4 := by
    have h2 := Subgroup.relIndex_mul_card (u0 T V) (V ⊔ u0 T V)
    rw [inf_eq_left.mpr le_sup_right] at h2
    have h3 : Nat.card ↥(V ⊔ u0 T V) = 4 * Nat.card ↥(u0 T V) := by omega
    rw [h3] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  refine ⟨h4, ?_⟩
  have h5 := Subgroup.relIndex_mul_relIndex (u0 T V) (V ⊔ u0 T V) (fsuU T V) le_sup_right
    (sup_le hVU hU0U)
  rw [h4, relIndex_u0 h hMod h63] at h5
  omega

theorem sl24_sq_of_two_pow (A : SL(2, F4)) (n : ℕ) (hA : A ^ 2 ^ n = 1) : A ^ 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [pow_zero, pow_one] at hA
      rw [hA, one_pow]
    · simpa using hA
    · have h4 : (A ^ 2 ^ n) ^ 4 = 1 := by
        rw [← pow_mul, show 2 ^ n * 4 = 2 ^ (n + 2) by ring]
        exact hA
      have h2 := sl24_two_elt _ h4
      exact ih (n + 1) (by omega) (by rw [pow_succ, pow_mul]; exact h2)

theorem commutator_le_sup_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    ⁅fsuU T V, pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)⁆ ≤ V ⊔ u0 T V := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨hKU, π, β, -, hπk, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  obtain ⟨-, hV8, -, hV1c, -⟩ := hMod G T L V h.hyp h.fsu
  have hUe := isElemAbelian_fsuU_of h hMod
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1U0 := fsuV1_le_u0 h hMod
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le h le_sup_right
  have hQHR : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have hTH : T ≤ hz T V := le_sup_right.trans hF.L₁T_le_H
    have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans hF.L₁T_le_H
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le h hTH).trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  set BV := (V.subgroupOf (fsuU T V)).map β with hBV
  have hBVc : Nat.card ↥BV = 4 := by
    rw [hBV, ← Subgroup.relIndex_ker, hβk, Subgroup.relIndex_subgroupOf hVU]
    have h2 := Subgroup.relIndex_mul_card (u0 T V) V
    rw [inf_comm, inf_u0_eq h hMod h63 hF, hV1c, hV8] at h2
    omega
  have hfix : ∀ k : ↥(kz T V), (k : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → π k ≠ 1 →
      ∀ y : Multiplicative (Fin 2 → F4),
        ((π k : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (Multiplicative.toAdd y) =
          Multiplicative.toAdd y → y ∈ BV := by
    intro k hkR hk1 y hy
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ⟨(k : G), hkR⟩
    have hk2 : π k ^ 2 = 1 := by
      refine sl24_sq_of_two_pow _ n ?_
      rw [← map_pow]
      have : k ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [this, map_one]
    let F : Finset (Multiplicative (Fin 2 → F4)) := Finset.univ.filter fun y =>
      ((π k : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (Multiplicative.toAdd y) =
        Multiplicative.toAdd y
    have hFc : F.card = 4 := by
      have := sl24_card_fix (π k) hk2 hk1
      rw [← this]
      exact Finset.card_bij (fun y _ => Multiplicative.toAdd y)
        (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩)
        (fun _ _ _ _ h => h)
        (fun v hv => ⟨Multiplicative.ofAdd v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by rw [toAdd_ofAdd]; exact (Finset.mem_filter.mp hv).2⟩, rfl⟩)
    have hsub : (BV : Set (Multiplicative (Fin 2 → F4))) ⊆ (F : Set _) := by
      rintro _ ⟨v, hv, rfl⟩
      have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
      have hkv : (k : G) * v * (k : G)⁻¹ ∈ fsuU T V :=
        (Subgroup.mem_normalizer_iff.mp (hKU k.2) v).mp v.2
      have h1 := hβe k v ⟨_, hkv⟩ rfl
      have h2 : β ⟨_, hkv⟩ = β v := by
        have h3 : (k : G) * v * (k : G)⁻¹ * (v : G)⁻¹ ∈ fsuV1 T V :=
          (S14.pCoreOf_L1T_le hkR).2.2 v hvV
        have h4 : β (⟨_, hkv⟩ * v⁻¹) = 1 :=
          (l24_ker_iff hβk _).mpr (hV1U0 (by simpa using h3))
        rw [map_mul, map_inv] at h4
        exact mul_inv_eq_one.mp h4
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h5 := congrArg Multiplicative.toAdd (h1.symm.trans h2)
      rwa [toAdd_ofAdd] at h5
    have heq : (BV : Set (Multiplicative (Fin 2 → F4))) = (F : Set _) := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [Set.ncard_coe_finset, hFc]
      show 4 ≤ Nat.card ↥BV
      rw [hBVc]
    have hyF : y ∈ (F : Set _) := by simpa [F] using hy
    rw [← heq] at hyF
    exact hyF
  rw [Subgroup.commutator_le]
  intro u hu r hr
  have hKN : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hr' : r ∈ ((kz T V : Set G) * (pCoreOf 2 (hz T V) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN]
    exact (R1_le_kz_sup S0 hF h63 h1222 h1332 h1334).1 hr
  obtain ⟨k, hk, q, hq, rfl⟩ := hr'
  show ⁅u, k * q⁆ ∈ V ⊔ u0 T V
  have hkR : k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have hr2 : k * q ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := hr
    have := mul_mem hr2 (inv_mem (hQHR hq))
    rwa [mul_inv_cancel_right] at this
  have hc : q * u⁻¹ * q⁻¹ * u ∈ fsuV1 T V := by
    have h1 := hF.commutator_conjClosure_le u⁻¹
      (by rw [← fsuU_eq_conjClosure_hz hMod h]; exact inv_mem hu) q hq
    have := inv_mem h1
    rwa [show (u⁻¹ * q * u⁻¹⁻¹ * q⁻¹)⁻¹ = q * u⁻¹ * q⁻¹ * u by group] at this
  have hkU : k * u * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp hu
  have hkc : k * (q * u⁻¹ * q⁻¹ * u) = (q * u⁻¹ * q⁻¹ * u) * k :=
    (Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ hk) _ hc).symm
  have hcomm : ∀ {x y : G}, x ∈ fsuU T V → y ∈ fsuU T V → x * y = y * x :=
    fun hx hy => F7.isElemAbelian_comm hUe hx hy
  have e : ⁅u, k * q⁆ = (q * u⁻¹ * q⁻¹ * u) * (u * (k * u * k⁻¹)⁻¹) := by
    calc ⁅u, k * q⁆ = u * (k * (q * u⁻¹ * q⁻¹ * u)) * u⁻¹ * k⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = u * (q * u⁻¹ * q⁻¹ * u) * (k * u⁻¹ * k⁻¹) := by rw [hkc]; group
      _ = (q * u⁻¹ * q⁻¹ * u) * (u * (k * u * k⁻¹)⁻¹) := by
          rw [hcomm hu (hVU (Subgroup.mem_inf.mp hc).1), mul_assoc]
          group
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hc).1) ?_
  have hxU : u * (k * u * k⁻¹)⁻¹ ∈ fsuU T V := mul_mem hu (inv_mem hkU)
  by_cases hk1 : π ⟨k, hk⟩ = 1
  · refine Subgroup.mem_sup_right ((l24_ker_iff hβk ⟨_, hxU⟩).mp ?_)
    have h1 := hβe ⟨k, hk⟩ ⟨u, hu⟩ ⟨_, hkU⟩ rfl
    rw [hk1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd] at h1
    have e2 : (⟨u * (k * u * k⁻¹)⁻¹, hxU⟩ : ↥(fsuU T V)) = ⟨u, hu⟩ * (⟨_, hkU⟩)⁻¹ := rfl
    rw [e2, map_mul, map_inv, h1, mul_inv_cancel]
  · have h1 := hβe ⟨k, hk⟩ ⟨u, hu⟩ ⟨_, hkU⟩ rfl
    set v := Multiplicative.toAdd (β ⟨u, hu⟩) with hv
    have hy : ((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        (((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec v + v) =
          ((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec v + v := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ⟨k, hkR⟩
      refine sl24_fix_comm _ (sl24_sq_of_two_pow _ n ?_) v
      rw [← map_pow]
      have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [this, map_one]
    obtain ⟨w, hw, hwy⟩ := hfix ⟨k, hk⟩ hkR hk1
      (Multiplicative.ofAdd (((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec v + v))
      (by rw [toAdd_ofAdd]; exact hy)
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have hxw : β (⟨_, hxU⟩ * w⁻¹) = 1 := by
      have e2 : (⟨u * (k * u * k⁻¹)⁻¹, hxU⟩ : ↥(fsuU T V)) = ⟨u, hu⟩ * (⟨_, hkU⟩)⁻¹ := rfl
      rw [map_mul, map_inv, e2, map_mul, map_inv, h1, hwy]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one]
      exact f4_key _ _
    have hmem := (l24_ker_iff hβk _).mp hxw
    have e3 : u * (k * u * k⁻¹)⁻¹ = (u * (k * u * k⁻¹)⁻¹ * (w : G)⁻¹) * w := by group
    rw [e3]
    exact mul_mem (Subgroup.mem_sup_right (by simpa using hmem)) (Subgroup.mem_sup_left hwV)

theorem mem_sup_u0_of_comm (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {x : G} (hxL : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : G}
    (hu : u ∈ fsuU T V) (hxu : x * u * x⁻¹ * u⁻¹ ∈ V ⊔ u0 T V) : u ∈ V ⊔ u0 T V := by
  obtain ⟨hKU, π, β, -, hπk, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hUe := isElemAbelian_fsuU_of h hMod
  have hcomm : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V → a * b = b * a :=
    fun ha hb => F7.isElemAbelian_comm hUe ha hb
  have hsq : ∀ {a : G}, a ∈ fsuU T V → a * a = 1 := fun ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe ha
  have hxK : x ∈ kz T V := l1_le_kz h hMod hxL
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hSU : V ⊔ u0 T V ≤ fsuU T V := sup_le hVU hU0U
  have hxH : x ∈ hz T V := oTwoUpper_le _ hxK
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    hLTV (Subgroup.mem_sup_left ((L32NSet14.Setting.L1_le.trans inf_le_left) hxL))
  have hxN : x ∈ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) := by
    rw [← conjSub_eq_self_iff, conjSub, Subgroup.map_sup]
    rw [show V.map (MulAut.conj x).toMonoidHom = V from conjSub_eq_self_iff.mpr hxV,
      show (u0 T V).map (MulAut.conj x).toMonoidHom = u0 T V from
        conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 h hMod hxH)]
  have hπ3 : π ⟨x, hxK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxK⟩ : ↥(kz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hπ1 : π ⟨x, hxK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨x, hxK⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kz T V)) ⟨x, h2⟩
    have h2n : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hord : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
        (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one h2n)
    exact hx1 (orderOf_eq_one_iff.mp hord)
  have hxu' : x * u * x⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hxK) u).mp hu
  set w := x * u * x⁻¹ * u⁻¹ with hw
  have hwU : w ∈ fsuU T V := hSU hxu
  have hxw : x * w * x⁻¹ ∈ V ⊔ u0 T V := (Subgroup.mem_normalizer_iff.mp hxN w).mp hxu
  have hxwU : x * w * x⁻¹ ∈ fsuU T V := hSU hxw
  have hmem : u * (x * w * x⁻¹)⁻¹ ∈ fsuU T V := mul_mem hu (inv_mem hxwU)
  have h0 : u * (x * w * x⁻¹)⁻¹ ∈ u0 T V := by
    refine (l24_ker_iff hβk ⟨_, hmem⟩).mp ?_
    have e1 := hβe ⟨x, hxK⟩ ⟨u, hu⟩ ⟨_, hxu'⟩ rfl
    have e2 := hβe ⟨x, hxK⟩ ⟨w, hwU⟩ ⟨_, hxwU⟩ rfl
    have ew : (⟨w, hwU⟩ : ↥(fsuU T V)) = ⟨_, hxu'⟩ * (⟨u, hu⟩)⁻¹ := rfl
    have e3 : (⟨u * (x * w * x⁻¹)⁻¹, hmem⟩ : ↥(fsuU T V)) = ⟨u, hu⟩ * (⟨_, hxwU⟩)⁻¹ := rfl
    rw [e3, map_mul, map_inv, e2, ew, map_mul, map_inv, e1]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one, Matrix.mulVec_add, Matrix.mulVec_neg]
    exact f4_key2 _ _ _ (sl24_order_three _ hπ3 hπ1 _)
  rw [show u = (u * (x * w * x⁻¹)⁻¹) * (x * w * x⁻¹) by group]
  exact mul_mem (Subgroup.mem_sup_right h0) hxw

end CFSG.Quasithin.H13.L32A
