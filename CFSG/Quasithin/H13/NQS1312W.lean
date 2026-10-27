module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases
public import CFSG.Quasithin.H13.NQS1312P

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

@[expose] def lperpList : List ℕ :=
  [0, 4, 8, 12, 17, 21, 25, 29, 32, 36, 40, 44, 49, 53, 57, 61]

theorem lperp_spec :
    (∀ c ∈ lperpList, c < 64 ∧ ∃ c' ∈ lperpList, c = c' ^^^ vapp kc c') ∧
    (∀ c ∈ lperpList, ∀ c' ∈ lperpList, c ^^^ c' ∈ lperpList) ∧
    (∀ c ∈ lperpList, vapp kc c = c → c = 0) ∧ lperpList.Nodup ∧ lperpList.length = 16 := by
  decide +kernel

theorem lperp_lt (c : ℕ) (hc : c ∈ lperpList) : c < 64 := (lperp_spec.1 c hc).1

theorem kc_lt : ∀ v < 64, vapp kc v < 64 := by
  decide +kernel

theorem alt5_fix_le : ∀ π : alternatingGroup (Fin 5), π ≠ 1 →
    ((Finset.univ : Finset (Fin 5 → ZMod 2)).filter (fun x =>
      ∑ i, x i = 0 ∧ ∀ i, x ((π : Equiv.Perm (Fin 5))⁻¹ i) = x i)).card ≤ 8 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
  {Φ : Additive V ≃ₗ[ZMod 2] W6}

omit [Finite G] in
theorem ptOf_xor (c c' : ℕ) :
    ptOf Φ (vecOf (c ^^^ c')) = ptOf Φ (vecOf c) * ptOf Φ (vecOf c') := by
  rw [vecOf_xor, ptOf_add]

omit [Finite G] in
theorem ptOf_inv (w : W6) : (ptOf Φ w)⁻¹ = ptOf Φ w := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) _ (ptOf_mem _)

omit [Finite G] in
theorem conj_ptOf_k {k₁ : G} (hk₁ : k₁ ∈ normalizer (V : Set G)) (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL)
    (c : ℕ) : k₁ * ptOf Φ (vecOf c) * k₁⁻¹ = ptOf Φ (vecOf (vapp kc c)) := by
  rw [conj_ptOf hk₁ (tau_eq_iff.1 hτ), glLin_vecOf_of_coe coe_kGL]

omit [Finite G] in
theorem commutator_ptOf_k {k₁ : G} (hk₁ : k₁ ∈ normalizer (V : Set G))
    (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL) (c : ℕ) :
    ⁅ptOf Φ (vecOf c), k₁⁆ = ptOf Φ (vecOf (c ^^^ vapp kc c)) := by
  have h1 : ⁅ptOf Φ (vecOf c), k₁⁆ = ptOf Φ (vecOf c) * (k₁ * ptOf Φ (vecOf c) * k₁⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h1, conj_ptOf_k hk₁ hτ, ptOf_inv, ptOf_xor]

omit [Finite G] in
theorem ptOf_lperp_mem_blockU {K : Subgroup G} {k₁ : G} (hk₁K : k₁ ∈ K)
    (hk₁ : k₁ ∈ normalizer (V : Set G)) (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL)
    (hVK : V ≤ normalizer (K : Set G)) (hVO : V ⊓ K ≤ pCoreOf 2 K) {c : ℕ}
    (hc : c ∈ lperpList) : ptOf Φ (vecOf c) ∈ blockU K := by
  have hmemK : ∀ c' : ℕ, ⁅ptOf Φ (vecOf c'), k₁⁆ ∈ K := fun c' => by
    rw [commutatorElement_def]
    have h1 : ptOf Φ (vecOf c') * k₁ * (ptOf Φ (vecOf c'))⁻¹ ∈ K :=
      (mem_normalizer_iff.1 (hVK (ptOf_mem _)) k₁).1 hk₁K
    exact K.mul_mem h1 (K.inv_mem hk₁K)
  obtain ⟨c', hc', rfl⟩ := (lperp_spec.1 c hc).2
  obtain ⟨c'', -, hc''⟩ := (lperp_spec.1 c' hc').2
  have hc'K : ptOf Φ (vecOf c') ∈ K := by
    rw [hc'', ← commutator_ptOf_k hk₁ hτ]
    exact hmemK c''
  rw [← commutator_ptOf_k hk₁ hτ]
  exact Subgroup.commutator_mem_commutator (hVO ⟨ptOf_mem _, hc'K⟩) hk₁K

omit [Finite G] in
theorem lperp_eq_of_mem_centralizer {K : Subgroup G} {k₁ : G} (hk₁K : k₁ ∈ K)
    (hk₁ : k₁ ∈ normalizer (V : Set G)) (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL) {c c' : ℕ}
    (hc : c ∈ lperpList) (hc' : c' ∈ lperpList)
    (h : (ptOf Φ (vecOf c))⁻¹ * ptOf Φ (vecOf c') ∈ centralizer (K : Set G)) : c = c' := by
  have hx : (ptOf Φ (vecOf c))⁻¹ * ptOf Φ (vecOf c') = ptOf Φ (vecOf (c ^^^ c')) := by
    rw [ptOf_inv, ptOf_xor]
  rw [hx] at h
  have h1 : k₁ * ptOf Φ (vecOf (c ^^^ c')) * k₁⁻¹ = ptOf Φ (vecOf (c ^^^ c')) := by
    rw [(mem_centralizer_iff.1 h) k₁ hk₁K]
    group
  rw [conj_ptOf_k hk₁ hτ] at h1
  have hxl := lperp_spec.2.1 c hc c' hc'
  have h2 : vapp kc (c ^^^ c') = c ^^^ c' :=
    vecOf_injective (kc_lt _ (lperp_lt _ hxl)) (lperp_lt _ hxl) (ptOf_injective h1)
  have h3 := lperp_spec.2.2.1 _ hxl h2
  exact Nat.xor_eq_zero_iff.1 h3

omit [IsElementaryAbelian 2 V] in
theorem inf_le_pCoreOf_of_pCoreOf_le {K Q : Subgroup G} (hc : CharTwo (K ⊔ Q))
    (hO : pCoreOf 2 (K ⊔ Q) ≤ Q) (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G)) :
    V ⊓ K ≤ pCoreOf 2 K := by
  have hVO : V ≤ pCoreOf 2 (K ⊔ Q) := by
    refine fun v hv => hc ⟨mem_sup_right (hVQ hv), mem_centralizer_iff.2 fun q hq => ?_⟩
    exact (mem_centralizer_iff.1 (hQC (hO hq)) v hv).symm
  intro v hv
  exact SBc17.inf_pCoreOf_sup_le K Q ⟨hv.2, hVO hv.1⟩

omit [IsElementaryAbelian 2 V] in
theorem inf_le_pCoreOf_of_isSylowTwoOf {K Q : Subgroup G} (hc : CharTwo (K ⊔ Q))
    (hQs : IsSylowTwoOf Q (K ⊔ Q)) (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G)) :
    V ⊓ K ≤ pCoreOf 2 K :=
  inf_le_pCoreOf_of_pCoreOf_le hc (B6.pCoreOf_two_le_of_isSylowTwoOf hQs) hVQ hQC

theorem false_of_c27A5_line
    (hA3 : A3Orbits G) (h38 : A38ForSQTK) {T L : Subgroup G} {z : G} (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G)) {M W : Subgroup G}
    (h : SBc17.C27A5 (lineH Φ) (pCoreOf 2 (L ⊔ T)) M K W) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, -, -, -, hVQ, -, hLV, -, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, ⟨α, hα, hker, β, -, hβker, hβ⟩, hsyl, -, -⟩ := h
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  obtain ⟨g3, hg3⟩ := exists_orderOf_three_alt (m := 5) (by norm_num)
  have hK3 : 3 ∣ Nat.card K := three_dvd_card_of_surjective α hα hg3
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  obtain ⟨hk₁K, -⟩ := le_normalizer_of_commute_three hA3 h38 (isSQTKIn_lineN hH) lineH_le_lineN
    lineN_le_normalizer_lineH (cComp_mem_of_subnormal isSubnormal_lineH hK) (le_of_mem_cComp hK)
    hK3 (mem_lineN_of_tau_k2 (hLV hxL) hxτ) (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H
    (not_mem_lineH_of_tau_k2 (hLV hxL) hxτ)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hVO := inf_le_pCoreOf_of_isSylowTwoOf hKQc hsyl hVQ hQC
  have hVK : V ≤ normalizer (K : Set G) := hVQ.trans hQK
  have hU : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ blockU K := fun c hc =>
    ptOf_lperp_mem_blockU hk₁K (hLV hk₁L) hk₁τ hVK hVO hc
  have hQKs : IsSylowTwoOf (Q ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsyl le_sup_left (sup_le Subgroup.le_normalizer hQK)
  have hne : ((Q ⊓ K).subgroupOf K).map α ≠ ⊥ := by
    intro h0
    have h1 := Subgroup.index_map_dvd ((Q ⊓ K).subgroupOf K) hα
    rw [h0, Subgroup.index_bot] at h1
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [h60] at h1
    exact hQKs.2.2 (dvd_trans (by norm_num) h1)
  obtain ⟨⟨π, hπ⟩, hπ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hπ1 : π ≠ 1 := fun h1 => hπ1' (Subtype.ext h1)
  obtain ⟨y, hy, hyπ⟩ := Subgroup.mem_map.1 hπ
  have hyQ : (y : G) ∈ Q := (Subgroup.mem_subgroupOf.1 hy).1
  let f : ℕ → Fin 5 → ZMod 2 := fun c => if hc : c ∈ lperpList then
    ((Multiplicative.toAdd (β ⟨ptOf Φ (vecOf c), hU c hc⟩) : evenWeight 5) : Fin 5 → ZMod 2)
    else 0
  have hfc : ∀ c (hc : c ∈ lperpList), f c =
      ((Multiplicative.toAdd (β ⟨ptOf Φ (vecOf c), hU c hc⟩) : evenWeight 5) : Fin 5 → ZMod 2) :=
    fun c hc => by simp only [f, hc, ↓reduceDIte]
  have hmaps : ∀ c ∈ lperpList.toFinset, f c ∈ (Finset.univ : Finset (Fin 5 → ZMod 2)).filter
      (fun x => ∑ i, x i = 0 ∧ ∀ i, x ((↑(π : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) =
        x i) := by
    intro c hc
    rw [List.mem_toFinset] at hc
    rw [Finset.mem_filter, hfc c hc]
    refine ⟨Finset.mem_univ _, ?_, fun i => ?_⟩
    · have h1 := (Multiplicative.toAdd (β ⟨ptOf Φ (vecOf c), hU c hc⟩)).2
      simpa only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] using h1
    · have hcen : (y : G) * ptOf Φ (vecOf c) * (y : G)⁻¹ = ptOf Φ (vecOf c) := by
        rw [← (mem_centralizer_iff.1 (hQC hyQ)) _ (ptOf_mem _)]
        group
      have := hβ y ⟨ptOf Φ (vecOf c), hU c hc⟩ ⟨ptOf Φ (vecOf c), hU c hc⟩ hcen.symm i
      rw [← hyπ]
      exact this.symm
  have hinj : Set.InjOn f lperpList.toFinset := by
    intro c hc c' hc' hcc
    rw [Finset.mem_coe, List.mem_toFinset] at hc hc'
    rw [hfc c hc, hfc c' hc'] at hcc
    have h1 : β ⟨ptOf Φ (vecOf c), hU c hc⟩ = β ⟨ptOf Φ (vecOf c'), hU c' hc'⟩ := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext hcc
    have h2 : (⟨ptOf Φ (vecOf c), hU c hc⟩ : ↥(blockU K))⁻¹ * ⟨ptOf Φ (vecOf c'), hU c' hc'⟩ ∈
        β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [hβker, Subgroup.mem_subgroupOf] at h2
    exact lperp_eq_of_mem_centralizer hk₁K (hLV hk₁L) hk₁τ hc hc' h2.2
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [List.toFinset_card_of_nodup lperp_spec.2.2.2.1, lperp_spec.2.2.2.2] at hcard
  have := alt5_fix_le π hπ1
  omega

end CFSG.Quasithin.H13.U3.NLine
