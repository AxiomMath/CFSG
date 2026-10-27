module

public import CFSG.Quasithin.Background.ONanE68Dich
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.E6SevenTwo
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
open scoped commutatorElement

section Solvable

variable {G : Type} [Group G]

theorem isSolvable_sup_pGroup [Finite G] {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hK : Group.IsSolvable ↥K) :
    Group.IsSolvable ↥(K ⊔ Q) := by
  have hQs : Group.IsSolvable ↥Q := by
    have := hQ.isNilpotent
    infer_instance
  have hnorm : (K.subgroupOf (Q ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hQK
  have hnormD : (K.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQK
  have hker : (QuotientGroup.mk' (K.subgroupOf (Q ⊔ K))).ker ≤
      (K.subgroupOf (Q ⊔ K)).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  let e₁ := Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ Q ⊔ K)
  have h1 : Group.IsSolvable ↥(K.subgroupOf (Q ⊔ K)) :=
    Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient Q K hQK
  have h2 : Group.IsSolvable (↥(Q ⊔ K) ⧸ K.subgroupOf (Q ⊔ K)) := by
    have : Group.IsSolvable (↥Q ⧸ K.subgroupOf Q) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := e₂.toMonoidHom) e₂.surjective
  have := Group.isSolvable_of_ker_le_range _ _ hker
  rwa [sup_comm] at this

theorem mem_of_orderOf_three_of_mem_sup {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {c : G} (hc : c ∈ K ⊔ Q)
    (h3 : orderOf c = 3) : c ∈ K := by
  obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_sup hQ hQK hc
  have hcop : Nat.Coprime (2 ^ n) (orderOf c) := by
    rw [h3]
    exact Nat.Coprime.pow_left n (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem K hn m

end Solvable

section Count

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le_card {D W : Subgroup G} {c : G}
    (hW : ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ W) :
    (D ⊓ Subgroup.centralizer ({c} : Set G)).relIndex D ≤ Nat.card W := by
  classical
  let H : Subgroup ↥D := (D ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf D
  have hcomm : ∀ a b : ↥D, a⁻¹ * b ∈ H → (a : G) * c * (a : G)⁻¹ * c⁻¹ =
      (b : G) * c * (b : G)⁻¹ * c⁻¹ := by
    intro a b hab
    have h1 : ((a⁻¹ * b : ↥D) : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hab)).2
    have h2 : c * ((a : G)⁻¹ * b) = ((a : G)⁻¹ * b) * c :=
      Subgroup.mem_centralizer_iff.1 h1 c rfl
    have h3 : (b : G) * c * (b : G)⁻¹ = (a : G) * c * (a : G)⁻¹ := by
      have e : (b : G) = (a : G) * ((a : G)⁻¹ * b) := by group
      calc (b : G) * c * (b : G)⁻¹ = (a : G) * (((a : G)⁻¹ * b) * c * ((a : G)⁻¹ * b)⁻¹) *
            (a : G)⁻¹ := by rw [e]; group
        _ = (a : G) * c * (a : G)⁻¹ := by rw [← h2]; group
    rw [h3]
  let f : ↥D ⧸ H → W := Quotient.lift
    (fun d : ↥D => (⟨(d : G) * c * (d : G)⁻¹ * c⁻¹, hW d d.2⟩ : W))
    (fun a b hab => Subtype.ext (hcomm a b (QuotientGroup.leftRel_apply.1 hab)))
  have hf : Function.Injective f := by
    intro q₁ q₂ h12
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    have h1 : (a : G) * c * (a : G)⁻¹ * c⁻¹ = (b : G) * c * (b : G)⁻¹ * c⁻¹ :=
      congrArg Subtype.val h12
    apply QuotientGroup.eq.2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(a⁻¹ * b : ↥D).2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have h2 : (a : G) * c * (a : G)⁻¹ = (b : G) * c * (b : G)⁻¹ := mul_right_cancel h1
    have e : c * ((a : G)⁻¹ * b) = ((a : G)⁻¹ * b) * c := by
      calc c * ((a : G)⁻¹ * b) = (a : G)⁻¹ * ((a : G) * c * (a : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((b : G) * c * (b : G)⁻¹) * b := by rw [h2]
        _ = ((a : G)⁻¹ * b) * c := by group
    exact e
  exact Nat.card_le_card_of_injective f hf

end Count

section Dichotomy

variable {G : Type} [Group G] [Finite G] {T M V U K : Subgroup G}

theorem block_dichotomy_solv (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hKH : K ≤ Subgroup.centralizer (U : Set G))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : CharTwo K) (hsolv : Group.IsSolvable ↥K) :
    K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ M ∨
      ∃ B : Subgroup G, IsChi0Block (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) B ∧ ¬ B ≤ M ∧
        ⁅B, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆ = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  set K' := K ⊔ Q with hK'def
  have hQK' : Q ≤ K' := le_sup_right
  have hK'H : K' ≤ H := sup_le hKH hQH.1
  have hK'c : CharTwo K' := Vol2Native.L239.charTwo_sup_of_le_normalizer hK h.isPGroup_Q hQN
  have hQsyl : IsSylowTwoOf Q K' := A4.isSylowTwoOf_mono hQH hQK' hK'H
  have hK'solv : Group.IsSolvable ↥K' := isSolvable_sup_pGroup h.isPGroup_Q hQN hsolv
  have hcgs : cgsIn K' Q ≤ K' ⊓ M := by
    refine le_inf (iSup_le fun C => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      inf_le_left) ?_
    exact (cgsIn_mono_left hK'H).trans ((e6_5_two h hU).1.trans inf_le_right)
  have hO2 : pCoreOf 2 K' ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK'c
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQK'.trans h1)
  have hsq : IsSQTKIn K' :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ :=
    asc129StatementSolv G K' Q (K' ⊓ M) hsq hK'c hQsyl hcgs inf_le_left hK'solv
  by_cases hall : ∀ i, Lb i ≤ M
  · left
    intro y hy
    obtain ⟨m, hm, z, hz, rfl⟩ := hprod y hy
    refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun w hw => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hw
    exact hall j (hz j)
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨hchi, -, hJ⟩ := hLb i
    exact ⟨Lb i, hchi, hi, hJ⟩

theorem borel_le_M_or_alt3 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) {D : Subgroup G}
    (hKH : K ≤ Subgroup.centralizer (U : Set G))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : CharTwo K) (hsolv : Group.IsSolvable ↥K) (hD2 : IsPGroup 2 D)
    (hDn : K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ Subgroup.normalizer (D : Set G))
    (hDK : D ≤ K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) :
    K ≤ M ∨ ∃ (B' : Subgroup G) (c : G), c ∈ K ∧ orderOf c = 3 ∧ Nat.card (blockU B') = 4 ∧
      (∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ blockU B') ∧
      (V ⊓ Subgroup.centralizer (B' : Set G)).relIndex V ≤ 2 ∧
      B' = blockU B' ⊔ Subgroup.zpowers c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hK'H : K ⊔ Q ≤ H := sup_le hKH hQH.1
  have hQsyl : IsSylowTwoOf Q (K ⊔ Q) := A4.isSylowTwoOf_mono hQH le_sup_right hK'H
  have hK'c : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hK h.isPGroup_Q hQN
  have hK'solv : Group.IsSolvable ↥(K ⊔ Q) := isSolvable_sup_pGroup h.isPGroup_Q hQN hsolv
  rcases block_dichotomy_solv h hU hKH hQN hK hsolv with hle | ⟨B', hchi, -, hJ⟩
  · exact Or.inl (le_sup_left.trans hle)
  right
  have hblock : IsBlock2 (K ⊔ Q) B' := hchi.1
  have h3 : IsAltType B' 3 :=
    C1Pack.isAltType_three_of_isChiBlock_of_isSolvable (C1GN.isChiBlock_of_isChi0Block hblock hchi)
      hK'solv
  obtain ⟨hQU, hU4, -, -, -, -, c, hcB, hc3, -, -, hLeq⟩ := IsShort2.alt3_structure hblock.1 h3
  have hBK : B' ≤ K ⊔ Q := hblock.2.1
  have hcK : c ∈ K :=
    mem_of_orderOf_three_of_mem_sup h.isPGroup_Q hQN (hBK hcB) hc3
  have hodd : Odd (orderOf c) := by rw [hc3]; decide
  have hcomm := CFSG.ClassicalInvolution.commutator_zpowers_le_of_isSubnormal
    (IsBlock2.isSubnormal hblock) hDK hDn hD2 hcB hodd
  have hBD : B' ⊓ D ≤ pCoreOf 2 B' := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (hD2.to_le inf_le_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxD : x ∈ Subgroup.normalizer (D : Set G) := hDn (hBK hx)
    have hxB : x ∈ Subgroup.normalizer (B' : Set G) := Subgroup.le_normalizer hx
    constructor
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.1 hxB y).1 hy.1,
        (Subgroup.mem_normalizer_iff.1 hxD y).1 hy.2⟩
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.1 hxB y).2 hy.1,
        (Subgroup.mem_normalizer_iff.1 hxD y).2 hy.2⟩
  refine ⟨B', c, hcK, hc3, hU4, fun d hd => ?_, ?_, hLeq⟩
  · have hmem : d * c * d⁻¹ * c⁻¹ ∈ ⁅D, Subgroup.zpowers c⁆ :=
      Subgroup.commutator_mem_commutator hd (Subgroup.mem_zpowers c)
    have h1 : d * c * d⁻¹ * c⁻¹ ∈ pCoreOf 2 B' := hBD (hcomm hmem)
    have h2 : pCoreOf 2 B' = blockU B' := hQU
    rwa [h2] at h1
  · exact relIndex_le_two_of_alt3 hK'c hblock h3 hQsyl hJ.symm h.le_inf_centralizer inf_le_right

end Dichotomy

end E68Proof

end E6

end CFSG.Quasithin
