module

public import CFSG.Quasithin.Recognition.St84.EdgeStab

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem oTwoPrime_mono {X Y : Subgroup G} (hXY : X ≤ Y) : oTwoPrime X ≤ oTwoPrime Y := by
  rw [oTwoPrime, oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hx, n, hn⟩
  exact Subgroup.subset_closure ⟨hXY hx, n, hn⟩

theorem oTwoPrime_le_of_odd_relIndex {X Y : Subgroup G} [Finite ↥X]
    (hYX : Y ≤ X) (hY : (Y.subgroupOf X).Normal) (hodd : ¬ 2 ∣ Y.relIndex X) :
    oTwoPrime X ≤ Y := by
  classical
  haveI : (Y.subgroupOf X).Normal := hY
  rw [oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hxX, n, hxn⟩
  let xX : ↥X := ⟨x, hxX⟩
  let q : ↥X →* (↥X ⧸ Y.subgroupOf X) := QuotientGroup.mk' (Y.subgroupOf X)
  have hxXn : xX ^ 2 ^ n = 1 := Subtype.ext hxn
  have hqpow : (q xX) ^ 2 ^ n = 1 := by
    rw [← map_pow, hxXn, map_one]
  have hdvd1 : orderOf (q xX) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hqpow
  have hdvd2 : orderOf (q xX) ∣ Nat.card (↥X ⧸ Y.subgroupOf X) := orderOf_dvd_natCard _
  have hoddq : ¬ 2 ∣ Nat.card (↥X ⧸ Y.subgroupOf X) := hodd
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (↥X ⧸ Y.subgroupOf X)) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    · rw [Nat.coprime_pow_left_iff hnpos]
      exact Nat.coprime_two_left.mpr
        (Nat.not_even_iff_odd.mp (fun he => hoddq (even_iff_two_dvd.mp he)))
  have hone : orderOf (q xX) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hxq : q xX = 1 := orderOf_eq_one_iff.mp hone
  have hxY : xX ∈ Y.subgroupOf X :=
    (QuotientGroup.eq_one_iff (N := Y.subgroupOf X) xX).mp hxq
  exact Subgroup.mem_subgroupOf.mp hxY

theorem relIndex_stabilizer_inf_stabilizer (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex
      (MulAction.stabilizer G α) = 2 ^ nOf Γ α + 1 := by
  classical
  let Gα := MulAction.stabilizer G α
  let Δ : SubMulAction Gα V := neighborActionOf h Gα le_rfl
  haveI : Finite Gα := h.finite_stab α
  obtain ⟨N, hN⟩ := h.locL2 α
  have htrans : MulAction.IsPretransitive Gα Δ := by
    refine ⟨fun x y => ?_⟩
    have hx : Γ.Adj α (x : V) := (SimpleGraph.mem_neighborSet (G := Γ) α (x : V)).mp x.2
    have hy : Γ.Adj α (y : V) := (SimpleGraph.mem_neighborSet (G := Γ) α (y : V)).mp y.2
    obtain ⟨g, hgN, hg⟩ := hN.trans (x : V) (y : V) hx hy
    refine ⟨⟨g, hN.le hgN⟩, ?_⟩
    apply Subtype.ext
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
    exact hg
  haveI := htrans
  let βΔ : Δ := ⟨β, by
    change β ∈ Γ.neighborSet α
    rw [SimpleGraph.mem_neighborSet]
    exact hαβ⟩
  have hidx : (MulAction.stabilizer Gα βΔ).index = Nat.card Δ :=
    MulAction.index_stabilizer_of_transitive Gα βΔ
  have hstab : MulAction.stabilizer Gα βΔ =
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).subgroupOf Gα := by
    ext g
    constructor
    · intro hg
      refine Subgroup.mem_subgroupOf.mpr ⟨g.2, ?_⟩
      have h' := congrArg (fun z : Δ => (z : V)) (MulAction.mem_stabilizer_iff.mp hg)
      rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at h'
      simpa [βΔ] using h'
    · intro hg
      exact MulAction.mem_stabilizer_iff.mpr (by
        apply Subtype.ext
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
        exact (Subgroup.mem_subgroupOf.mp hg).2)
  calc (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex Gα
      = (MulAction.stabilizer Gα βΔ).index := by rw [hstab]; rfl
    _ = Nat.card Δ := hidx
    _ = 2 ^ nOf Γ α + 1 := (h.valency α).2

theorem not_two_dvd_relIndex_stabilizer_inf_stabilizer (h : Hyp30 Γ G) {α β : V}
    (hαβ : Γ.Adj α β) :
    ¬ 2 ∣ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex
      (MulAction.stabilizer G α) := by
  rw [relIndex_stabilizer_inf_stabilizer h hαβ]
  have heven : Even (2 ^ nOf Γ α) :=
    even_two.pow_of_ne_zero (by have := (h.valency α).1; omega)
  exact (heven.add_odd odd_one).not_two_dvd_nat

theorem relIndex_pointSubgroup_local (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    (N ⊓ MulAction.stabilizer G β).relIndex N = 2 ^ nOf Γ α + 1 := by
  classical
  haveI : Finite ↥N := finite_of_le_stabilizer h (α := α) (H := N) hN.le
  let Δ : SubMulAction N V := hN.neighborAction h.adj_smul
  let βΔ : Δ := ⟨β, by
    change β ∈ Γ.neighborSet α
    rw [SimpleGraph.mem_neighborSet]
    exact hαβ⟩
  haveI : MulAction.IsPretransitive N Δ := hN.neighborAction_isPretransitive h.adj_smul
  have hidx : (MulAction.stabilizer N βΔ).index = Nat.card Δ :=
    MulAction.index_stabilizer_of_transitive N βΔ
  have hstab : MulAction.stabilizer N βΔ = (N ⊓ MulAction.stabilizer G β).subgroupOf N :=
    (hN.pointSubgroup_eq_stabilizer h.adj_smul hαβ).symm
  calc (N ⊓ MulAction.stabilizer G β).relIndex N
      = (MulAction.stabilizer N βΔ).index := by rw [hstab]; rfl
    _ = Nat.card Δ := hidx
    _ = 2 ^ nOf Γ α + 1 := (h.valency α).2

theorem not_two_dvd_relIndex_pointSubgroup_local (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    ¬ 2 ∣ (N ⊓ MulAction.stabilizer G β).relIndex N := by
  rw [relIndex_pointSubgroup_local h hN hαβ]
  have heven : Even (2 ^ nOf Γ α) :=
    even_two.pow_of_ne_zero (by have := (h.valency α).1; omega)
  exact (heven.add_odd odd_one).not_two_dvd_nat

theorem isSylowTwoOf_pCoreOf_edgeStab (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    IsSylowTwoOf (pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β))
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  have hSylow := isSylowTwoOf_edgeSylow h hαβ (localSubgroup_spec h α) (localSubgroup_spec h β)
  rw [← edgeSylow_eq_pCoreOf_edge h hαβ (localSubgroup_spec h α) (localSubgroup_spec h β)] at hSylow
  exact hSylow

theorem exists_complement_pCoreOf_edgeStab (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    ∃ K : Subgroup G, K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ∧
      K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥ ∧
      K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
        (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  classical
  let H := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let S := pCoreOf 2 H
  have hSle : S ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  haveI : Finite ↥H := finite_of_le_stabilizer h (α := α) (H := H) inf_le_left
  let Ssub : Subgroup H := S.subgroupOf H
  have hSsubNormal : Ssub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  haveI : Ssub.Normal := hSsubNormal
  have hSylow : IsSylowTwoOf S H := isSylowTwoOf_pCoreOf_edgeStab h hαβ
  have hSp : IsPGroup 2 Ssub :=
    hSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSle).symm
  have hSodd : ¬ 2 ∣ Ssub.index := hSylow.2.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime (Nat.card Ssub) Ssub.index := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSodd |>.pow_left k
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime (N := Ssub) hcop
  let K : Subgroup G := K'.map H.subtype
  have hKleH : K ≤ H := Subgroup.map_subtype_le _
  have hKinf : K ⊓ S = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨b₁, hb₁, hb₁x⟩ := Subgroup.mem_map.mp hx.1
    obtain ⟨b₂, hb₂, hb₂x⟩ := Subgroup.mem_map.mp hx.2
    have hbS : b₁ ∈ Ssub := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨b₂, hb₂, hb₂x.trans hb₁x.symm⟩
    have hbot : b₁ ∈ (⊥ : Subgroup H) := by
      have hdisj : K' ⊓ Ssub = ⊥ := by
        rw [inf_comm]
        exact hK'.disjoint.eq_bot
      have : b₁ ∈ K' ⊓ Ssub := ⟨hb₁, hbS⟩
      rwa [hdisj] at this
    rw [Subgroup.mem_bot] at hbot
    rw [← hb₁x, hbot]
    rfl
  have hKsup : K ⊔ S = H := by
    have hmap := congrArg (Subgroup.map H.subtype) hK'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, H.range_subtype] at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hSle] at hmap
    rw [sup_comm]
    exact hmap
  exact ⟨K, hKleH, hKinf, hKsup⟩

theorem odd_card_of_complement (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)) :
    Odd (Nat.card K) := by
  classical
  let H := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let S := pCoreOf 2 H
  have hSle : S ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  haveI : Finite ↥H := finite_of_le_stabilizer h (α := α) (H := H) inf_le_left
  have hSylow : IsSylowTwoOf S H := isSylowTwoOf_pCoreOf_edgeStab h hαβ
  have hoddS : Odd (S.relIndex H) := by
    rw [← Nat.not_even_iff_odd]
    exact fun he => hSylow.2.2 (even_iff_two_dvd.mp he)
  have hSsubNormal : (S.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hcomp : (K.subgroupOf H).IsComplement' (S.subgroupOf H) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hx1 : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx.1
      have hx2 : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx.2
      have hxKS : (x : G) ∈ K ⊓ S := ⟨hx1, hx2⟩
      rw [hKinf] at hxKS
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxKS))
    · have hsup_sub : K.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hKle hSle, hKsup, Subgroup.subgroupOf_self]
      haveI : (S.subgroupOf H).Normal := hSsubNormal
      rw [← Subgroup.mul_normal (K.subgroupOf H) (S.subgroupOf H), hsup_sub]
      rfl
  have hcard := hcomp.card_mul_card
  have hcardS : Nat.card (S.subgroupOf H) * S.relIndex H = Nat.card H := by
    have h := Subgroup.card_mul_index (S.subgroupOf H)
    rwa [show (S.subgroupOf H).index = S.relIndex H from rfl] at h
  have hcardK : Nat.card K = Nat.card (K.subgroupOf H) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv).symm
  have h3 : Nat.card (K.subgroupOf H) = S.relIndex H := by
    haveI : Finite ↥(S.subgroupOf H) := Subtype.finite
    have h4 : Nat.card (K.subgroupOf H) * Nat.card (S.subgroupOf H) =
        S.relIndex H * Nat.card (S.subgroupOf H) := by
      calc Nat.card (K.subgroupOf H) * Nat.card (S.subgroupOf H)
          = Nat.card H := hcard
        _ = Nat.card (S.subgroupOf H) * S.relIndex H := hcardS.symm
        _ = S.relIndex H * Nat.card (S.subgroupOf H) := mul_comm _ _
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
  rw [hcardK, h3]
  exact hoddS

theorem isSylowTwoOf_of_edgeStab (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {P : Subgroup G}
    (hP : IsSylowTwoOf P (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)) :
    IsSylowTwoOf P (MulAction.stabilizer G α) := by
  refine F7.isSylowTwoOf_of_relIndex (hP.1.trans inf_le_left) hP.2.1 ?_
  change ¬ 2 ∣ P.relIndex (MulAction.stabilizer G α)
  rw [← Subgroup.relIndex_mul_relIndex P (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (MulAction.stabilizer G α) hP.1 inf_le_left]
  exact Nat.prime_two.not_dvd_mul hP.2.2
    (not_two_dvd_relIndex_stabilizer_inf_stabilizer h hαβ)

theorem pointSylowN_map_phi (h : Hyp30 Γ G) {v : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G v (nOf Γ v) N) (a : V) :
    (((hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 a :
        Sylow 2 N) : Subgroup N).map hN.phi) =
      (hN.pointSylow h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 a :
        Subgroup (PSL(2, GaloisField 2 (nOf Γ v)))) := by
  rw [show ((hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 a :
        Sylow 2 N) : Subgroup N) =
      (hN.pointSylow h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 a :
        Subgroup (PSL(2, GaloisField 2 (nOf Γ v)))).comap hN.phi from rfl]
  exact Subgroup.map_comap_eq_self_of_surjective hN.phi_surjective _

theorem le_oTwoPrime_stabilizer (h : Hyp30 Γ G) {v : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G v (nOf Γ v) N) :
    N ≤ oTwoPrime (MulAction.stabilizer G v) := by
  classical
  haveI : Finite ↥N := finite_of_le_stabilizer h (α := v) (H := N) hN.le
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := h.exists_adj v
  obtain ⟨b, hb, hba⟩ := h.exists_adj_ne v a
  let L := PSL(2, GaloisField 2 (nOf Γ v))
  let Sa : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 a
  let Sb : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2 (h.valency v).1 b
  have hbij := hN.pointSylow_bijective h.adj_smul (h.finite_stab v) (h.valency v).2
    (h.valency v).1
  have hne : (hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2
        (h.valency v).1 a) ≠
      (hN.pointSylowN h.adj_smul (h.finite_stab v) (h.valency v).2
        (h.valency v).1 b) := by
    intro hEq
    have h1 : (hN.pointSylow h.adj_smul (h.finite_stab v) (h.valency v).2
          (h.valency v).1 a : Subgroup L) =
        (hN.pointSylow h.adj_smul (h.finite_stab v) (h.valency v).2
          (h.valency v).1 b : Subgroup L) := by
      rw [← pointSylowN_map_phi h hN a, ← pointSylowN_map_phi h hN b, hEq]
    have h2 : (⟨a, ha⟩ : hN.neighborAction h.adj_smul) = ⟨b, hb⟩ :=
      hbij.1 (Sylow.ext h1)
    exact hba (congrArg Subtype.val h2).symm
  let S1 : Subgroup G := (Sa : Subgroup N).map N.subtype
  let S2 : Subgroup G := (Sb : Subgroup N).map N.subtype
  have hS1le : S1 ≤ N := Subgroup.map_subtype_le _
  have hS2le : S2 ≤ N := Subgroup.map_subtype_le _
  have hS1p : IsPGroup 2 S1 := Sa.isPGroup'.map N.subtype
  have hS2p : IsPGroup 2 S2 := Sb.isPGroup'.map N.subtype
  have hex : ∃ g ∈ S2, g ∉ Subgroup.normalizer (S1 : Set G) := by
    by_contra hcon
    have hnorm : S2 ≤ Subgroup.normalizer (S1 : Set G) := by
      intro g hg
      by_contra hg'
      exact hcon ⟨g, hg, hg'⟩
    have hsub : (Subgroup.normalizer (S1 : Set G)).subgroupOf N =
        Subgroup.normalizer ((Sa : Subgroup N) : Set N) := by
      rw [Subgroup.subgroupOf_normalizer_eq (H := S1) (N := N) hS1le,
        subgroupOf_map_subtype_eq]
    have hSb_le : (Sb : Subgroup N) ≤ Subgroup.normalizer ((Sa : Subgroup N) : Set N) := by
      intro x hx
      have hxS2 : (x : G) ∈ S2 := Subgroup.mem_map_of_mem N.subtype hx
      have hxnorm : (x : G) ∈ Subgroup.normalizer (S1 : Set G) := hnorm hxS2
      have hx' : x ∈ (Subgroup.normalizer (S1 : Set G)).subgroupOf N :=
        Subgroup.mem_subgroupOf.mpr hxnorm
      rwa [hsub] at hx'
    have hSaSylowN : IsSylowTwoOf (Sa : Subgroup N) ⊤ :=
      F7.isSylowTwoOf_of_relIndex le_top Sa.isPGroup' (by
        simpa using Sa.not_dvd_index)
    let K := Subgroup.normalizer ((Sa : Subgroup N) : Set N)
    have hSaNorm : (Sa : Subgroup N) ≤ Subgroup.normalizer ((Sa : Subgroup N) : Set N) :=
      Subgroup.le_normalizer
    have hSaK : IsSylowTwoOf (Sa : Subgroup N) K :=
      F7.isSylowTwoOf_mono_right hSaSylowN hSaNorm le_top
    have hSaKn : ((Sa : Subgroup N).subgroupOf K).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
    haveI : ((Sa : Subgroup N).subgroupOf K).Normal := hSaKn
    obtain ⟨x, hxK, hxle⟩ :=
      F7.isSylowTwoOf_exists_conj_le hSaK hSb_le Sb.isPGroup'
    have hconj : conjSub x (Sa : Subgroup N) = (Sa : Subgroup N) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hxK
    have hSb_le_Sa : (Sb : Subgroup N) ≤ (Sa : Subgroup N) := by
      rw [← hconj]
      exact hxle
    have heqSub : (Sa : Subgroup N) = (Sb : Subgroup N) :=
      Sb.is_maximal' Sa.isPGroup' hSb_le_Sa
    exact hne (Sylow.ext heqSub)
  obtain ⟨g, hgS2, hgnorm⟩ := hex
  have hgN : g ∈ N := hS2le hgS2
  have hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    have h' := (isPGroup_iff_pow_pow_eq_one (p := 2) (G := ↥S2)).mp hS2p ⟨g, hgS2⟩
    obtain ⟨k, hk⟩ := h'
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgmem : g ∈ oTwoPrime (MulAction.stabilizer G v) :=
    Subgroup.subset_closure ⟨hN.le hgN, hg2⟩
  have hsup := hN.sylow_sup_zpowers_eq_G h.adj_smul (h.finite_stab v) (h.valency v).2
    (h.valency v).1 Sa hgN hgnorm
  rw [← hsup]
  refine sup_le ?_ (Subgroup.zpowers_le.mpr hgmem)
  intro x hx
  exact le_oTwoPrime_of_isPGroup hS1p (hS1le.trans hN.le) hx

theorem IsLocL2.eq_oTwoPrime (h : Hyp30 Γ G) {v : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G v (nOf Γ v) N) :
    N = oTwoPrime (MulAction.stabilizer G v) := by
  classical
  refine le_antisymm (le_oTwoPrime_stabilizer h hN) ?_
  haveI : Finite ↥(MulAction.stabilizer G v) := h.finite_stab v
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := h.exists_adj v
  let Gv := MulAction.stabilizer G v
  let Ga := MulAction.stabilizer G a
  let B := N ⊓ Ga
  let S := pCoreOf 2 B
  have hSB : S ≤ B := CFSG.LieType.BorelTits.pCoreOf_le 2 B
  have hSleN : S ≤ N := hSB.trans inf_le_left
  have hSylowB : IsSylowTwoOf S B := by
    rw [show S = vertexSylowMap h hN a from edgeSylow_eq_vertexSylowMap h hN ha]
    exact isSylowTwoOf_vertexSylowMap_edge hN ha
  have hSylowN : IsSylowTwoOf S N := by
    refine F7.isSylowTwoOf_of_relIndex hSleN hSylowB.2.1 ?_
    change ¬ 2 ∣ S.relIndex N
    rw [← Subgroup.relIndex_mul_relIndex S B N hSB inf_le_left]
    exact Nat.prime_two.not_dvd_mul hSylowB.2.2
      (not_two_dvd_relIndex_pointSubgroup_local h hN ha)
  have hSylowH : IsSylowTwoOf S (Gv ⊓ Ga) :=
    isSylowTwoOf_edgeSylow h ha hN (localSubgroup_spec h a)
  have hSrelG : ¬ 2 ∣ S.relIndex Gv := (isSylowTwoOf_of_edgeStab h ha hSylowH).2.2
  have hodd : ¬ 2 ∣ N.relIndex Gv := by
    intro hd
    apply hSrelG
    rw [← Subgroup.relIndex_mul_relIndex S N Gv hSleN hN.le]
    exact dvd_mul_of_dvd_right hd _
  exact oTwoPrime_le_of_odd_relIndex hN.le hN.normal hodd

theorem Hyp30.isLocL2_oTwoPrime (h : Hyp30 Γ G) (v : V) :
    IsLocL2 Γ G v (nOf Γ v) (oTwoPrime (MulAction.stabilizer G v)) := by
  obtain ⟨N, hN⟩ := h.locL2 v
  have hEq := IsLocL2.eq_oTwoPrime h hN
  rw [hEq] at hN
  exact hN

theorem oTwoPrime_eq_localSubgroup (h : Hyp30 Γ G) (v : V) :
    oTwoPrime (MulAction.stabilizer G v) = localSubgroup h v :=
  (IsLocL2.eq_oTwoPrime h (localSubgroup_spec h v)).symm

theorem frattini_oTwoPrime (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊔
      oTwoPrime (MulAction.stabilizer G α) = MulAction.stabilizer G α := by
  rw [oTwoPrime_eq_localSubgroup h α]
  exact frattini_edgeLocal h (localSubgroup_spec h α) hαβ

theorem eq_bot_of_normal_in_oTwoPrime (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {X : Subgroup G}
    (hXα : X ≤ oTwoPrime (MulAction.stabilizer G α))
    (hnα : (X.subgroupOf (oTwoPrime (MulAction.stabilizer G α))).Normal)
    (hXβ : X ≤ oTwoPrime (MulAction.stabilizer G β))
    (hnβ : (X.subgroupOf (oTwoPrime (MulAction.stabilizer G β))).Normal) :
    X = ⊥ := by
  have hLe : X ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf (hXα.trans (oTwoPrime_le _))
      (hXβ.trans (oTwoPrime_le _))
  have hα : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G α, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgL, hg⟩ := (Hyp30.isLocL2_oTwoPrime h α).trans a b ha hb
    have hXnorm : oTwoPrime (MulAction.stabilizer G α) ≤
        Subgroup.normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXα).mp hnα
    have hgn : g ∈ Subgroup.normalizer (X : Set G) := hXnorm hgL
    exact ⟨g, ⟨hgn, oTwoPrime_le _ hgL⟩, hg⟩
  have hβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ Subgroup.normalizer (X : Set G) ⊓ MulAction.stabilizer G β, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hgL, hg⟩ := (Hyp30.isLocL2_oTwoPrime h β).trans a b ha hb
    have hXnorm : oTwoPrime (MulAction.stabilizer G β) ≤
        Subgroup.normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXβ).mp hnβ
    have hgn : g ∈ Subgroup.normalizer (X : Set G) := hXnorm hgL
    exact ⟨g, ⟨hgn, oTwoPrime_le _ hgL⟩, hg⟩
  exact eq_bot_of_normalizer_trans h hαβ hLe hα hβ

theorem complement_inf_oTwoPrime (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)) :
    (K ⊓ oTwoPrime (MulAction.stabilizer G α)) ⊓
        pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥ ∧
      (K ⊓ oTwoPrime (MulAction.stabilizer G α)) ⊔
        pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
          oTwoPrime (MulAction.stabilizer G α) ⊓ MulAction.stabilizer G β := by
  classical
  let H := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let S := pCoreOf 2 H
  have hSleH : S ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  haveI : Finite ↥H := finite_of_le_stabilizer h (α := α) (H := H) inf_le_left
  have hSleB : S ≤ oTwoPrime (MulAction.stabilizer G α) ⊓ MulAction.stabilizer G β := by
    rw [show S = pCoreOf 2 (localSubgroup h α ⊓ MulAction.stabilizer G β) from
      edgeSylow_eq_pCoreOf_edge h hαβ (localSubgroup_spec h α) (localSubgroup_spec h β)]
    refine le_inf ?_ ?_
    · rw [oTwoPrime_eq_localSubgroup h α]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hSsubNormal : (S.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  constructor
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx1 : x ∈ K := hx.1.1
    have hx2 : x ∈ S := hx.2
    have hxKS : x ∈ K ⊓ S := ⟨hx1, hx2⟩
    rw [hKinf] at hxKS
    exact hxKS
  · refine le_antisymm ?_ ?_
    · refine sup_le ?_ hSleB
      exact le_inf inf_le_right (inf_le_left.trans (hKle.trans inf_le_right))
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL, hxGβ⟩ := hx
      have hxH : x ∈ H := ⟨oTwoPrime_le _ hxL, hxGβ⟩
      have hsup_sub : K.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hKle hSleH, hKsup, Subgroup.subgroupOf_self]
      have hmul : ((↑(K.subgroupOf H) : Set H)) * ((↑(S.subgroupOf H) : Set H)) = Set.univ := by
        haveI : (S.subgroupOf H).Normal := hSsubNormal
        rw [← Subgroup.mul_normal (K.subgroupOf H) (S.subgroupOf H), hsup_sub]
        rfl
      have hx' : (⟨x, hxH⟩ : H) ∈
          ((↑(K.subgroupOf H) : Set H)) * ((↑(S.subgroupOf H) : Set H)) := by
        rw [hmul]
        trivial
      obtain ⟨k, hk, s, hs, hks⟩ := Set.mem_mul.mp hx'
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hksG : (k : G) * (s : G) = x := by
        have h := congrArg Subtype.val hks
        simpa using h
      have hsL : (s : G) ∈ oTwoPrime (MulAction.stabilizer G α) := (hSleB hsS).1
      have hkL : (k : G) ∈ oTwoPrime (MulAction.stabilizer G α) := by
        have hk_eq : (k : G) = x * (s : G)⁻¹ := by
          rw [← hksG]; group
        rw [hk_eq]
        exact (oTwoPrime (MulAction.stabilizer G α)).mul_mem hxL
          ((oTwoPrime (MulAction.stabilizer G α)).inv_mem hsL)
      rw [← hksG]
      exact Subgroup.mul_mem_sup ⟨hkK, hkL⟩ hsS

theorem eq_bot_of_pCoreOf_eq (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    (heq : pCoreOf 2 (MulAction.stabilizer G α) =
      pCoreOf 2 (MulAction.stabilizer G β)) :
    pCoreOf 2 (MulAction.stabilizer G α) = ⊥ := by
  let Q := pCoreOf 2 (MulAction.stabilizer G α)
  have hQα : Q ≤ oTwoPrime (MulAction.stabilizer G α) :=
    (Hyp30.isLocL2_oTwoPrime h α).oTwo_le
  have hQβ : Q ≤ oTwoPrime (MulAction.stabilizer G β) := by
    rw [show Q = pCoreOf 2 (MulAction.stabilizer G β) from heq]
    exact (Hyp30.isLocL2_oTwoPrime h β).oTwo_le
  have hQnα : (Q.subgroupOf (oTwoPrime (MulAction.stabilizer G α))).Normal := by
    rw [show Q = pCoreOf 2 (MulAction.stabilizer G α) from rfl]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le _).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hQnβ : (Q.subgroupOf (oTwoPrime (MulAction.stabilizer G β))).Normal := by
    rw [show Q = pCoreOf 2 (MulAction.stabilizer G β) from heq]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le _).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  exact eq_bot_of_normal_in_oTwoPrime h hαβ hQα hQnα hQβ hQnβ

theorem le_of_normal_isSylowTwoOf {S P H : Subgroup G} [Finite ↥H] (hS : IsSylowTwoOf S H)
    (hSn : (S.subgroupOf H).Normal) (hPH : P ≤ H) (hP : IsPGroup 2 P) : P ≤ S := by
  classical
  haveI : (S.subgroupOf H).Normal := hSn
  have hS' : IsSylowTwoOf (S.subgroupOf H) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · simpa using hS.2.2
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨y, hy, hyle⟩ := F7.isSylowTwoOf_exists_conj_le (G := ↥H) hS' le_top hP'
  have hyN : y ∈ Subgroup.normalizer ((S.subgroupOf H) : Set H) :=
    Subgroup.le_normalizer_of_normal (K := ⊤) hy
  have hconj : conjSub y (S.subgroupOf H) = S.subgroupOf H :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hyN
  rw [hconj] at hyle
  intro x hx
  have hx' : (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  exact hyle hx' 

theorem isPGroup_zpowers_of_pow_two {x : G} {m : ℕ} (hm : x ^ 2 ^ m = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  refine IsPGroup.of_card (n := k) ?_
  rw [Nat.card_zpowers, hk]

theorem mem_pCoreOf_of_fixes_two (h : Hyp30 Γ G) {α : V} {x : G}
    (hxα : x ∈ MulAction.stabilizer G α) (hx2 : ∃ m : ℕ, x ^ 2 ^ m = 1)
    {a b : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b) (hab : a ≠ b)
    (hxa : x • a = a) (hxb : x • b = b) :
    x ∈ pCoreOf 2 (MulAction.stabilizer G α) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxGa : x ∈ MulAction.stabilizer G a := MulAction.mem_stabilizer_iff.mpr hxa
  have hxH : x ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G a := ⟨hxα, hxGa⟩
  let H := MulAction.stabilizer G α ⊓ MulAction.stabilizer G a
  haveI : Finite ↥H := finite_of_le_stabilizer h (α := α) (H := H) inf_le_left
  let S := pCoreOf 2 H
  have hSylow : IsSylowTwoOf S H := by
    rw [show S = pCoreOf 2 (localSubgroup h α ⊓ MulAction.stabilizer G a) from
      edgeSylow_eq_pCoreOf_edge h ha (localSubgroup_spec h α) (localSubgroup_spec h a)]
    exact isSylowTwoOf_edgeSylow h ha (Nα := localSubgroup h α) (Nβ := localSubgroup h a)
      (localSubgroup_spec h α) (localSubgroup_spec h a)
  have hSn : (S.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hz2 : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_two hx2.choose_spec
  have hzx : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hxS : x ∈ S := le_of_normal_isSylowTwoOf hSylow hSn hzx hz2 (Subgroup.mem_zpowers x)
  have hSeq : S = vertexSylowMap h (localSubgroup_spec h α) a := by
    rw [show S = pCoreOf 2 (localSubgroup h α ⊓ MulAction.stabilizer G a) from
      edgeSylow_eq_pCoreOf_edge h ha (localSubgroup_spec h α) (localSubgroup_spec h a)]
    exact edgeSylow_eq_vertexSylowMap h (localSubgroup_spec h α) ha
  by_contra hxQ
  have hxV : x ∈ vertexSylowMap h (localSubgroup_spec h α) a := by
    rwa [← hSeq]
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxV
  have hyQ : (y : G) ∉ pCoreOf 2 (MulAction.stabilizer G α) := by
    intro hyQ'
    exact hxQ (by rw [← hyx]; exact hyQ')
  obtain ⟨z, hz, huniq⟩ :=
    (localSubgroup_spec h α).fixes_unique_of_mem_sylow_not_pcore h.adj_smul
      (h.finite_stab α) (h.valency α).2 (h.valency α).1
      ((localSubgroup_spec h α).pointSylowN h.adj_smul (h.finite_stab α)
        (h.valency α).2 (h.valency α).1 a) hy hyQ
  have hyx' : (y : G) = x := hyx
  have hza : a = z := huniq a ⟨ha, by rw [hyx']; exact hxa⟩
  have hzb : b = z := huniq b ⟨hb, by rw [hyx']; exact hxb⟩
  exact hab (hza.trans hzb.symm)

theorem le_pCoreOf_of_isPGroup_fixes_two (h : Hyp30 Γ G) {α : V} {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPα : P ≤ MulAction.stabilizer G α)
    {a b : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b) (hab : a ≠ b)
    (hPa : ∀ y ∈ P, y • a = a) (hPb : ∀ y ∈ P, y • b = b) :
    P ≤ pCoreOf 2 (MulAction.stabilizer G α) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := MulAction.stabilizer G α ⊓ MulAction.stabilizer G a
  haveI : Finite ↥H := finite_of_le_stabilizer h (α := α) (H := H) inf_le_left
  let S := pCoreOf 2 H
  have hPa' : P ≤ MulAction.stabilizer G a := by
    intro y hy
    exact MulAction.mem_stabilizer_iff.mpr (hPa y hy)
  have hPH : P ≤ H := le_inf hPα hPa'
  have hSylow : IsSylowTwoOf S H := by
    rw [show S = pCoreOf 2 (localSubgroup h α ⊓ MulAction.stabilizer G a) from
      edgeSylow_eq_pCoreOf_edge h ha (localSubgroup_spec h α) (localSubgroup_spec h a)]
    exact isSylowTwoOf_edgeSylow h ha (Nα := localSubgroup h α) (Nβ := localSubgroup h a)
      (localSubgroup_spec h α) (localSubgroup_spec h a)
  have hSn : (S.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hPS : P ≤ S := le_of_normal_isSylowTwoOf hSylow hSn hPH hP
  have hSeq : S = vertexSylowMap h (localSubgroup_spec h α) a := by
    rw [show S = pCoreOf 2 (localSubgroup h α ⊓ MulAction.stabilizer G a) from
      edgeSylow_eq_pCoreOf_edge h ha (localSubgroup_spec h α) (localSubgroup_spec h a)]
    exact edgeSylow_eq_vertexSylowMap h (localSubgroup_spec h α) ha
  by_contra hPQ
  obtain ⟨x, hxP, hxQ⟩ := Set.not_subset.mp hPQ
  have hxS : x ∈ S := hPS hxP
  have hxV : x ∈ vertexSylowMap h (localSubgroup_spec h α) a := hSeq ▸ hxS
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxV
  have hyQ : (y : G) ∉ pCoreOf 2 (MulAction.stabilizer G α) := by
    intro hyQ'
    exact hxQ (by rw [← hyx]; exact hyQ')
  obtain ⟨z, hz, huniq⟩ :=
    (localSubgroup_spec h α).fixes_unique_of_mem_sylow_not_pcore h.adj_smul
      (h.finite_stab α) (h.valency α).2 (h.valency α).1
      ((localSubgroup_spec h α).pointSylowN h.adj_smul (h.finite_stab α)
        (h.valency α).2 (h.valency α).1 a) hy hyQ
  have hyx' : (y : G) = x := hyx
  have hza : a = z := huniq a ⟨ha, by rw [hyx']; exact hPa x hxP⟩
  have hzb : b = z := huniq b ⟨hb, by rw [hyx']; exact hPb x hxP⟩
  exact hab (hza.trans hzb.symm)

theorem le_oTwoRes_of_odd_card {P X : Subgroup G} (hPX : P ≤ X) (hP : Odd (Nat.card P)) :
    P ≤ oTwoRes X := by
  intro x hx
  refine Subgroup.subset_closure ⟨hPX hx, orderOf x, ?_, pow_orderOf_eq_one x⟩
  exact Odd.of_dvd_nat hP (Subgroup.orderOf_dvd_natCard P hx)

theorem eq_of_dvd_of_le_sub_one {q d : ℕ} (hq : 4 ≤ q) (hd : d ∣ q + 1) (hge : q - 1 ≤ d) :
    d = q + 1 := by
  obtain ⟨c, hc⟩ := hd
  by_cases hc0 : c = 0
  · subst hc0; omega
  by_cases hc1 : c = 1
  · subst hc1; simpa using hc.symm
  · exfalso
    have hc2 : 2 ≤ c := by omega
    have h2 : 2 * d ≤ q + 1 := by
      calc 2 * d = d * 2 := by ring
        _ ≤ d * c := Nat.mul_le_mul_left d hc2
        _ = q + 1 := hc.symm
    omega

theorem oTwoRes_trans (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ oTwoRes (oTwoPrime (MulAction.stabilizer G α)), g • a = b := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := oTwoPrime (MulAction.stabilizer G α)
  have hN : IsLocL2 Γ G α (nOf Γ α) N := Hyp30.isLocL2_oTwoPrime h α
  let M := oTwoRes N
  have hMN : (M.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoRes N)
  haveI : (M.subgroupOf N).Normal := hMN
  let Δ : SubMulAction N V := hN.neighborAction h.adj_smul
  haveI : MulAction.IsPretransitive N Δ := hN.neighborAction_isPretransitive h.adj_smul
  haveI : Finite ↥N := finite_of_le_stabilizer h (α := α) (H := N) (oTwoPrime_le _)
  haveI : Finite (Γ.neighborSet α) :=
    Nat.finite_of_card_ne_zero (by rw [(h.valency α).2]; positivity)
  haveI : Finite ↥Δ :=
    Finite.of_injective (fun x : Δ => (⟨x.1, x.2⟩ : Γ.neighborSet α))
      (fun a b h => Subtype.ext (congrArg Subtype.val h))
  have hΔcard : Nat.card ↥Δ = 2 ^ nOf Γ α + 1 := (h.valency α).2
  suffices htransM : ∀ x y : Δ, y ∈ MulAction.orbit (M.subgroupOf N) x by
    intro a b ha hb
    let aΔ : Δ := ⟨a, by
      change a ∈ Γ.neighborSet α
      rw [SimpleGraph.mem_neighborSet]
      exact ha⟩
    let bΔ : Δ := ⟨b, by
      change b ∈ Γ.neighborSet α
      rw [SimpleGraph.mem_neighborSet]
      exact hb⟩
    have hy := htransM aΔ bΔ
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨m, hm⟩ := hy
    refine ⟨(m : N), m.2, ?_⟩
    have h := congrArg Subtype.val hm
    simpa [SubMulAction.val_smul, MulAction.subgroup_smul_def] using h
  by_cases hn1 : nOf Γ α = 1
  ·
    have hquot : Nat.card (↥N ⧸ CFSG.pCore 2 ↥N) = 6 := by
      calc Nat.card (↥N ⧸ CFSG.pCore 2 ↥N)
          = Nat.card (PSL(2, GaloisField 2 (nOf Γ α))) :=
            Nat.card_congr hN.quot.some.toEquiv
        _ = 6 := by
            have hc := CFSG.Walter.psl2_even_card (f := nOf Γ α)
              (by have := (h.valency α).1; omega)
            rw [hn1] at hc ⊢
            exact hc
    have h3dvd : 3 ∣ Nat.card ↥N := by
      have h1 : Nat.card ↥N =
          Nat.card (CFSG.pCore 2 ↥N) * (CFSG.pCore 2 ↥N).index :=
        (Subgroup.card_mul_index (CFSG.pCore 2 ↥N)).symm
      have h2 : (CFSG.pCore 2 ↥N).index = Nat.card (↥N ⧸ CFSG.pCore 2 ↥N) := rfl
      rw [h1, h2, hquot]
      exact dvd_mul_of_dvd_right (by norm_num : 3 ∣ 6) _
    obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3dvd
    have hgM : g ∈ M.subgroupOf N := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Subgroup.subset_closure ⟨g.2, 3, by norm_num, ?_⟩
      have hg3 : (g : ↥N) ^ 3 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
      simpa using congrArg Subtype.val hg3
    have hgQ : (g : G) ∉ pCoreOf 2 (MulAction.stabilizer G α) := by
      intro hgq
      haveI : Finite ↥(pCoreOf 2 (MulAction.stabilizer G α)) :=
        finite_of_le_stabilizer h (α := α) (H := pCoreOf 2 (MulAction.stabilizer G α))
          (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      have hdiv : orderOf (g : G) ∣ Nat.card (pCoreOf 2 (MulAction.stabilizer G α)) :=
        Subgroup.orderOf_dvd_natCard _ hgq
      have hgordG : orderOf (g : G) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hgord
      have hpow : ∃ k : ℕ, Nat.card (pCoreOf 2 (MulAction.stabilizer G α)) = 2 ^ k :=
        (pCoreOf_isPGroup' (MulAction.stabilizer G α)).exists_card_eq
      obtain ⟨k, hk⟩ := hpow
      rw [hgordG, hk] at hdiv
      have hcop : Nat.Coprime (2 ^ k) 3 :=
        (Nat.coprime_two_left.mpr (by norm_num : Odd 3)).pow_left k
      exact absurd (Nat.eq_one_of_dvd_coprimes hcop hdiv dvd_rfl) (by norm_num)
    have hmoves : ∃ x : Δ, g • x ≠ x := by
      by_contra hcon
      push Not at hcon
      apply hgQ
      rw [← inf_kernelOnNeighbors_eq_pCoreOf h hN]
      refine ⟨g.2, ?_⟩
      change (g : G) ∈ kernelOnNeighbors Γ G α
      rw [mem_kernelOnNeighbors]
      refine ⟨hN.le g.2, fun v hv => ?_⟩
      let vΔ : Δ := ⟨v, by
        change v ∈ Γ.neighborSet α
        rw [SimpleGraph.mem_neighborSet]
        exact hv⟩
      have h := congrArg Subtype.val (hcon vΔ)
      rwa [SubMulAction.val_smul, MulAction.subgroup_smul_def] at h
    let pt : Δ := hmoves.choose
    have hpt : g • pt ≠ pt := hmoves.choose_spec
    let P := Subgroup.zpowers g
    haveI : Fintype ↥P := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit P pt) := Fintype.ofFinite _
    have hPcard : Nat.card ↥P = 3 := by
      rw [Nat.card_zpowers]
      exact hgord
    have hdvd : (MulAction.orbit P pt).ncard ∣ 3 := by
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥P) pt
      have hcard : Fintype.card (MulAction.orbit ↥P pt) = (MulAction.orbit P pt).ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rw [hcard] at h
      have hcardP : Fintype.card ↥P = 3 := by
        rw [← Nat.card_eq_fintype_card]; exact hPcard
      rw [hcardP] at h
      exact dvd_of_mul_right_eq _ h
    have h2sub : ({pt, g • pt} : Set Δ) ⊆ MulAction.orbit P pt := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact MulAction.mem_orbit_self (M := P) pt
      · exact MulAction.mem_orbit (γ := P) pt (⟨g, Subgroup.mem_zpowers g⟩ : P)
    have h2card : ({pt, g • pt} : Set Δ).ncard = 2 :=
      Set.ncard_pair (Ne.symm hpt)
    have hge2 : 2 ≤ (MulAction.orbit P pt).ncard := by
      rw [← h2card]
      exact Set.ncard_le_ncard h2sub (Set.toFinite _)
    have h3orbit : (MulAction.orbit P pt).ncard = 3 := by
      have hcases : (MulAction.orbit P pt).ncard = 1 ∨ (MulAction.orbit P pt).ncard = 3 :=
        (Nat.dvd_prime Nat.prime_three).mp hdvd
      rcases hcases with h1 | h3
      · omega
      · exact h3
    have hΔcard3 : Nat.card ↥Δ = 3 := by
      rw [hΔcard, hn1]
      norm_num
    have horbit : MulAction.orbit P pt = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, hΔcard3, h3orbit]
    intro x' y'
    have hPM : P ≤ M.subgroupOf N := by
      rw [Subgroup.zpowers_le]
      exact hgM
    have hx' : x' ∈ MulAction.orbit (M.subgroupOf N) pt := by
      have h1 : x' ∈ MulAction.orbit P pt := by rw [horbit]; trivial
      rw [MulAction.mem_orbit_iff] at h1
      obtain ⟨p, hp⟩ := h1
      exact MulAction.mem_orbit_iff.mpr ⟨⟨p, hPM p.2⟩, hp⟩
    have hy' : y' ∈ MulAction.orbit (M.subgroupOf N) pt := by
      have h1 : y' ∈ MulAction.orbit P pt := by rw [horbit]; trivial
      rw [MulAction.mem_orbit_iff] at h1
      obtain ⟨p, hp⟩ := h1
      exact MulAction.mem_orbit_iff.mpr ⟨⟨p, hPM p.2⟩, hp⟩
    obtain ⟨m1, hm1⟩ := MulAction.mem_orbit_iff.mp hy'
    obtain ⟨m2, hm2⟩ := MulAction.mem_orbit_iff.mp hx'
    exact MulAction.mem_orbit_iff.mpr ⟨m1 * m2⁻¹, by
      rw [mul_smul, ← hm2, inv_smul_smul]
      exact hm1⟩
  ·
    have hn2 : 2 ≤ nOf Γ α := by
      have := (h.valency α).1
      omega
    have hq4 : 4 ≤ 2 ^ nOf Γ α := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ nOf Γ α := Nat.pow_le_pow_right (by norm_num) hn2
    have hγ := edgeGamma_spec h hN hαβ
    have hβγ : β ≠ edgeGamma h hN hαβ := fun hb => hγ.2.1 hb.symm
    have hfin : (Γ.neighborSet α \ {β, edgeGamma h hN hαβ}).Finite :=
      (h.finite_neighborSet α).sdiff
    have hcardγ : (Γ.neighborSet α \ {β, edgeGamma h hN hαβ}).ncard = 2 ^ nOf Γ α - 1 :=
      ncard_neighborSet_diff_two h hαβ hγ.1 hβγ
    have hpos : 0 < (Γ.neighborSet α \ {β, edgeGamma h hN hαβ}).ncard := by
      rw [hcardγ]
      omega
    obtain ⟨δ, hδ⟩ := (Set.ncard_pos (hs := hfin)).mp hpos
    rw [Set.mem_sdiff] at hδ
    obtain ⟨hδneigh, hδne⟩ := hδ
    have hδadj : Γ.Adj α δ := (SimpleGraph.mem_neighborSet (G := Γ) α δ).mp hδneigh
    have hδβ : δ ≠ β := by intro h1; exact hδne (by simp [h1])
    have hδγ : δ ≠ edgeGamma h hN hαβ := by intro h1; exact hδne (by simp [h1])
    let K := edgeTorus h hN hαβ
    have hKleN : K ≤ N := edgeTorus_le h hN hαβ
    have hKodd : Odd (Nat.card K) := by
      rw [(edgeTorus_cyclic h hN hαβ).2]
      have heven : Even (2 ^ nOf Γ α) :=
        even_two.pow_of_ne_zero (by have := (h.valency α).1; omega)
      exact Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
    have hKM : K ≤ M := le_oTwoRes_of_odd_card hKleN hKodd
    have hKsubM : K.subgroupOf N ≤ M.subgroupOf N := by
      intro k hk
      exact Subgroup.mem_subgroupOf.mpr (hKM (Subgroup.mem_subgroupOf.mp hk))
    let hKα : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
    let ΔK : SubMulAction K V := neighborActionOf h K hKα
    let δΔK : ΔK := ⟨δ, by
      change δ ∈ Γ.neighborSet α
      rw [SimpleGraph.mem_neighborSet]
      exact hδadj⟩
    have hstabK : MulAction.stabilizer K δΔK = ⊥ := by
      have h' := stabilizer_edgeTorus_neighbor h hN hαβ hδadj hδβ hδγ
      dsimp only at h'
      exact h'
    have hKset_card : ((fun k : K => (k : G) • δ) '' Set.univ).ncard =
        2 ^ nOf Γ α - 1 := by
      rw [Set.ncard_image_of_injective _ ?_, Set.ncard_univ]
      · exact (edgeTorus_cyclic h hN hαβ).2
      · intro k1 k2 h12
        have hinv : (k1⁻¹ * k2) • δΔK = δΔK := by
          apply Subtype.ext
          rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
          have h3 : ((k1⁻¹ * k2 : K) : G) • δ = δ := by
            have h12' : (k2 : G) • δ = (k1 : G) • δ := h12.symm
            have h4 : (k1 : G)⁻¹ • ((k2 : G) • δ) = δ := by
              rw [h12', inv_smul_smul]
            simpa [mul_smul] using h4
          simpa using h3
        have hmem : k1⁻¹ * k2 ∈ MulAction.stabilizer K δΔK :=
          MulAction.mem_stabilizer_iff.mpr hinv
        rw [hstabK] at hmem
        have h1 : k1⁻¹ * k2 = 1 := Subgroup.mem_bot.mp hmem
        have h2 : k2 = k1 := by
          have := congrArg (fun x : K => k1 * x) h1
          simpa using this
        exact h2.symm
    let δΔ : Δ := ⟨δ, by
      change δ ∈ Γ.neighborSet α
      rw [SimpleGraph.mem_neighborSet]
      exact hδadj⟩
    let OΔ : Set Δ := MulAction.orbit (M.subgroupOf N) δΔ
    have hOblock : MulAction.IsBlock N OΔ :=
      MulAction.IsBlock.orbit_of_normal (G := N) (N := M.subgroupOf N) δΔ
    have hOne : OΔ.Nonempty := ⟨δΔ, MulAction.mem_orbit_self δΔ⟩
    have hOdvd : OΔ.ncard ∣ 2 ^ nOf Γ α + 1 := by
      have h := hOblock.ncard_dvd_card hOne
      rwa [hΔcard] at h
    have hOge : 2 ^ nOf Γ α - 1 ≤ OΔ.ncard := by
      have hsub : ((fun k : K => (k : G) • δ) '' Set.univ) ⊆ Subtype.val '' OΔ := by
        rintro v ⟨k, -, rfl⟩
        let m : ↥(M.subgroupOf N) :=
          ⟨⟨k, hKleN k.2⟩, Subgroup.mem_subgroupOf.mpr (hKM k.2)⟩
        refine ⟨m • δΔ, MulAction.mem_orbit δΔ m, ?_⟩
        show ((m • δΔ : Δ) : V) = (k : G) • δ
        rw [MulAction.subgroup_smul_def, SubMulAction.val_smul]
        rfl
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [hKset_card, Set.ncard_image_of_injective _ Subtype.val_injective] at hle
      exact hle
    have hOcard : OΔ.ncard = 2 ^ nOf Γ α + 1 :=
      eq_of_dvd_of_le_sub_one hq4 hOdvd hOge
    have hOuniv : OΔ = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, hΔcard, hOcard]
    intro x' y'
    have hxu : x' ∈ OΔ := by rw [hOuniv]; trivial
    have hyu : y' ∈ OΔ := by rw [hOuniv]; trivial
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp hyu
    obtain ⟨m', hm'⟩ := MulAction.mem_orbit_iff.mp hxu
    have hx'inv : m'⁻¹ • x' = δΔ := by rw [← hm', inv_smul_smul]
    exact MulAction.mem_orbit_iff.mpr ⟨m * m'⁻¹, by rw [mul_smul, hx'inv]; exact hm⟩

theorem edgeLocal_eq_sup_oTwoRes (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    MulAction.stabilizer G α ⊓ MulAction.stabilizer G β =
      ((MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
          oTwoRes (oTwoPrime (MulAction.stabilizer G α))) ⊔
        ((MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ⊓
          oTwoRes (oTwoPrime (MulAction.stabilizer G β))) := by
  classical
  let Gα := MulAction.stabilizer G α
  let Gβ := MulAction.stabilizer G β
  have hNα : IsLocL2 Γ G α (nOf Γ α) (oTwoPrime Gα) := Hyp30.isLocL2_oTwoPrime h α
  have hNβ : IsLocL2 Γ G β (nOf Γ β) (oTwoPrime Gβ) := Hyp30.isLocL2_oTwoPrime h β
  have hLα : oTwoPrime Gα ≤ Gα := oTwoPrime_le Gα
  have hLβ : oTwoPrime Gβ ≤ Gβ := oTwoPrime_le Gβ
  have hnormα : Gα ≤ Subgroup.normalizer (oTwoRes (oTwoPrime Gα) : Set G) := by
    have hNnorm : Gα ≤ Subgroup.normalizer (oTwoPrime Gα : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLα).mp hNα.normal
    intro g hg
    have hconj : conjSub g (oTwoPrime Gα) = oTwoPrime Gα :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hNnorm hg)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (oTwoRes (oTwoPrime Gα)) = oTwoRes (oTwoPrime Gα)
    rw [conjSub_oTwoRes, hconj]
  have hnormβ : Gβ ≤ Subgroup.normalizer (oTwoRes (oTwoPrime Gβ) : Set G) := by
    have hNnorm : Gβ ≤ Subgroup.normalizer (oTwoPrime Gβ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLβ).mp hNβ.normal
    intro g hg
    have hconj : conjSub g (oTwoPrime Gβ) = oTwoPrime Gβ :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hNnorm hg)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (oTwoRes (oTwoPrime Gβ)) = oTwoRes (oTwoPrime Gβ)
    rw [conjSub_oTwoRes, hconj]
  have hsubA : oTwoRes (oTwoPrime Gα) ≤ Gα :=
    (oTwoRes_le _).trans hLα
  have hsubB : oTwoRes (oTwoPrime Gβ) ≤ Gβ :=
    (oTwoRes_le _).trans hLβ
  have hnA : ((oTwoRes (oTwoPrime Gα)).subgroupOf Gα).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormα
  have hnB : ((oTwoRes (oTwoPrime Gβ)).subgroupOf Gβ).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormβ
  have htA : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ oTwoRes (oTwoPrime Gα), g • a = b := oTwoRes_trans h hαβ
  have htB : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ oTwoRes (oTwoPrime Gβ), g • a = b := oTwoRes_trans h hαβ.symm
  exact inf_stabilizer_eq_sup h hαβ hsubA hsubB hnA hnB htA htB

theorem sup_pCoreOf_eq_edgeSylow_of_not_le (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    (hne : ¬ pCoreOf 2 (MulAction.stabilizer G α) ≤
      pCoreOf 2 (MulAction.stabilizer G β)) :
    pCoreOf 2 (MulAction.stabilizer G α) ⊔ pCoreOf 2 (MulAction.stabilizer G β) =
      pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Gα := MulAction.stabilizer G α
  let Gβ := MulAction.stabilizer G β
  let H := Gα ⊓ Gβ
  let Qα := pCoreOf 2 Gα
  let Qβ := pCoreOf 2 Gβ
  let S := pCoreOf 2 H
  let Nβ := oTwoPrime Gβ
  have hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ := Hyp30.isLocL2_oTwoPrime h β
  have hNα : IsLocL2 Γ G α (nOf Γ α) (oTwoPrime Gα) := Hyp30.isLocL2_oTwoPrime h α
  have hQαS : Qα ≤ S := by
    have hle := le_edgeSylow_of_isPGroup h hNα hαβ (pCoreOf_isPGroup' Gα) ?_
    · rw [← edgeSylow_eq_pCoreOf_edge h hαβ hNα hNβ] at hle
      exact hle
    · refine le_inf hNα.oTwo_le ?_
      intro q hq
      exact MulAction.mem_stabilizer_iff.mpr
        (hNα.Q_fixes_neighbors h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1
          β hαβ q hq)
  have hQβS : Qβ ≤ S := by
    have h1 : S = pCoreOf 2 (Nβ ⊓ Gα) := by
      rw [show S = pCoreOf 2 (oTwoPrime Gα ⊓ Gβ) from
        edgeSylow_eq_pCoreOf_edge h hαβ hNα hNβ]
      exact pCoreOf_inf_eq h hαβ hNα hNβ
    have hle := le_edgeSylow_of_isPGroup h hNβ hαβ.symm (pCoreOf_isPGroup' Gβ) ?_
    · rw [← h1] at hle
      exact hle
    · refine le_inf hNβ.oTwo_le ?_
      intro q hq
      exact MulAction.mem_stabilizer_iff.mpr
        (hNβ.Q_fixes_neighbors h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1
          α hαβ.symm q hq)
  have hRleS : Qα ⊔ Qβ ≤ S := sup_le hQαS hQβS
  have hSleH : S ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hRH : Qα ⊔ Qβ ≤ H := hRleS.trans hSleH
  have hRnorm : ((Qα ⊔ Qβ).subgroupOf H).Normal := by
    have hQαH : Qα ≤ H := hQαS.trans hSleH
    have hQβH : Qβ ≤ H := hQβS.trans hSleH
    have h1 : (Qα.subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        ((inf_le_left : H ≤ Gα).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gα))
    have h2 : (Qβ.subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        ((inf_le_right : H ≤ Gβ).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gβ))
    haveI : (Qα.subgroupOf H).Normal := h1
    haveI : (Qβ.subgroupOf H).Normal := h2
    rw [Subgroup.subgroupOf_sup hQαH hQβH]
    infer_instance
  let Kβ := edgeTorus h hNβ hαβ.symm
  have hKβleNβ : Kβ ≤ Nβ := edgeTorus_le h hNβ hαβ.symm
  have hKβleGα : Kβ ≤ Gα := edgeTorus_fixes h hNβ hαβ.symm
  have hKβleGβ : Kβ ≤ Gβ := hKβleNβ.trans (oTwoPrime_le Gβ)
  have hKβleH : Kβ ≤ H := le_inf hKβleGα hKβleGβ
  have hKβnorm : Kβ ≤ Subgroup.normalizer (((Qα ⊔ Qβ : Subgroup G)) : Set G) :=
    hKβleH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRnorm)
  have hS_eq_vertex : S = vertexSylowMap h hNβ α := by
    have h1 : S = pCoreOf 2 (Nβ ⊓ Gα) := by
      rw [show S = pCoreOf 2 (oTwoPrime Gα ⊓ Gβ) from
        edgeSylow_eq_pCoreOf_edge h hαβ hNα hNβ]
      exact pCoreOf_inf_eq h hαβ hNα hNβ
    rw [h1]
    exact edgeSylow_eq_vertexSylowMap h hNβ hαβ.symm
  have hKNinf : (Kβ.subgroupOf Nβ) ⊓
      (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1 α :
        Subgroup Nβ) = ⊥ := by
    have h' := edgeTorus_N_facts h hNβ hαβ.symm
    dsimp only at h'
    exact h'.1
  have hKNsup : (Kβ.subgroupOf Nβ) ⊔
      (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1 α :
        Subgroup Nβ) =
      Subgroup.normalizer (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2
        (h.valency β).1 α : Subgroup Nβ) := by
    have h' := edgeTorus_N_facts h hNβ hαβ.symm
    dsimp only at h'
    exact h'.2.1
  have hlt : Qβ < Qα ⊔ Qβ := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    refine hne ?_
    have h2 : Qα ≤ Qα ⊔ Qβ := le_sup_left
    rw [show Qα ⊔ Qβ = Qβ from heq.symm] at h2
    exact h2
  have hex : ∃ r ∈ (Qα ⊔ Qβ : Subgroup G), r ∉ Qβ := by
    by_contra hcon
    push Not at hcon
    exact hne (le_sup_left.trans (fun x hx => hcon x hx))
  obtain ⟨r, hrR, hrQ⟩ := hex
  have hrS : r ∈ S := hRleS hrR
  have hrV : r ∈ vertexSylowMap h hNβ α := hS_eq_vertex ▸ hrS
  have hrNβ : r ∈ Nβ := vertexSylowMap_le hNβ α hrV
  have hrS' : (⟨r, hrNβ⟩ : ↥Nβ) ∈
      (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1 α :
        Subgroup Nβ) := by
    exact (Subgroup.mem_map_iff_mem Nβ.subtype_injective).mp hrV
  have hSr : S ≤ Qα ⊔ Qβ := by
    intro y hyS
    by_cases hyQ : y ∈ Qβ
    · exact Subgroup.mem_sup_right hyQ
    · have hyV : y ∈ vertexSylowMap h hNβ α := hS_eq_vertex ▸ hyS
      have hyNβ : y ∈ Nβ := vertexSylowMap_le hNβ α hyV
      have hyS' : (⟨y, hyNβ⟩ : ↥Nβ) ∈
          (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1 α :
            Subgroup Nβ) := by
        exact (Subgroup.mem_map_iff_mem Nβ.subtype_injective).mp hyV
      have hrQ' : ((⟨r, hrNβ⟩ : ↥Nβ) : G) ∉ pCoreOf 2 Gβ := hrQ
      have hyQ' : ((⟨y, hyNβ⟩ : ↥Nβ) : G) ∉ pCoreOf 2 Gβ := hyQ
      obtain ⟨k, hk⟩ := hNβ.torus_transitive_on_sylow h.adj_smul (h.finite_stab β)
        (h.valency β).2 (h.valency β).1
        (hNβ.pointSylowN h.adj_smul (h.finite_stab β) (h.valency β).2 (h.valency β).1 α)
        (Kβ.subgroupOf Nβ) hKNinf hKNsup hrS' hyS' hrQ' hyQ'
      have hkG : (k : G) * r * (k : G)⁻¹ * y⁻¹ ∈ Qβ := by
        have h := Subgroup.mem_subgroupOf.mp hk
        simpa using h
      have hkrR : (k : G) * r * (k : G)⁻¹ ∈ Qα ⊔ Qβ := by
        have hkKβ : (k : G) ∈ Kβ := Subgroup.mem_subgroupOf.mp k.2
        exact (Subgroup.mem_normalizer_iff.mp (hKβnorm hkKβ) r).mp hrR
      have hyA : y * ((k : G) * r * (k : G)⁻¹)⁻¹ ∈ Qβ := by
        have h := Qβ.inv_mem hkG
        simpa [mul_inv_rev] using h
      have hy_eq : y = (y * ((k : G) * r * (k : G)⁻¹)⁻¹) *
          ((k : G) * r * (k : G)⁻¹) := by group
      rw [hy_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyA) hkrR
  exact le_antisymm hRleS hSr

theorem sup_pCoreOf_eq_edgeSylow (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    (hQα : pCoreOf 2 (MulAction.stabilizer G α) ≠ ⊥) :
    pCoreOf 2 (MulAction.stabilizer G α) ⊔ pCoreOf 2 (MulAction.stabilizer G β) =
      pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  by_cases hle : pCoreOf 2 (MulAction.stabilizer G α) ≤
      pCoreOf 2 (MulAction.stabilizer G β)
  ·
    by_cases hle' : pCoreOf 2 (MulAction.stabilizer G β) ≤
        pCoreOf 2 (MulAction.stabilizer G α)
    · exact absurd (eq_bot_of_pCoreOf_eq h hαβ (le_antisymm hle hle')) hQα
    · rw [sup_comm, inf_comm]
      exact sup_pCoreOf_eq_edgeSylow_of_not_le h hαβ.symm hle'
  · exact sup_pCoreOf_eq_edgeSylow_of_not_le h hαβ hle

end CFSG.Quasithin.St84
