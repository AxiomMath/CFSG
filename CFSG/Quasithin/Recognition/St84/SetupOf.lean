module

public import CFSG.Quasithin.Recognition.St84.EdgeStabB
public import CFSG.Quasithin.Recognition.St84.Track
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.Quasithin.Recognition.St84.Singularity
public import CFSG.Quasithin.Recognition.St84.Gold26
public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_edgeTorusSylow (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    ∃ (S : Sylow 2 (oTwoPrime (MulAction.stabilizer G α)))
      (K' : Subgroup (oTwoPrime (MulAction.stabilizer G α))),
      (S : Subgroup (oTwoPrime (MulAction.stabilizer G α))).map
          (oTwoPrime (MulAction.stabilizer G α)).subtype =
        pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) ∧
      K'.map (oTwoPrime (MulAction.stabilizer G α)).subtype =
        K ⊓ oTwoPrime (MulAction.stabilizer G α) ∧
      K' ⊓ (S : Subgroup (oTwoPrime (MulAction.stabilizer G α))) = ⊥ ∧
      K' ⊔ (S : Subgroup (oTwoPrime (MulAction.stabilizer G α))) =
        Subgroup.normalizer ((S : Subgroup (oTwoPrime (MulAction.stabilizer G α))) :
          Set (oTwoPrime (MulAction.stabilizer G α))) := by
  classical
  let Gα := MulAction.stabilizer G α
  let Gβ := MulAction.stabilizer G β
  let N := oTwoPrime Gα
  let Sg := pCoreOf 2 (Gα ⊓ Gβ)
  have hN : IsLocL2 Γ G α (nOf Γ α) N := h.isLocL2_oTwoPrime α
  have hSylowH : IsSylowTwoOf Sg (Gα ⊓ Gβ) := isSylowTwoOf_pCoreOf_edgeStab h hαβ
  have hSg_eq : Sg = vertexSylowMap h hN β := by
    rw [show Sg = pCoreOf 2 (N ⊓ MulAction.stabilizer G β) from
      edgeSylow_eq_pCoreOf_edge h hαβ hN (h.isLocL2_oTwoPrime β)]
    exact edgeSylow_eq_vertexSylowMap h hN hαβ
  have hSylowN : IsSylowTwoOf Sg N := by
    rw [hSg_eq]
    exact isSylowTwoOf_vertexSylowMap h hN hαβ
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow hSylowN
  let K' : Subgroup N := (K ⊓ N).subgroupOf N
  have hSmap : (S : Subgroup N).map N.subtype = Sg := by
    rw [hS, Subgroup.map_subgroupOf_eq_of_le hSylowN.1]
  have hKmap : K'.map N.subtype = K ⊓ N :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hKS : K' ⊓ (S : Subgroup N) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxK : (x : G) ∈ K := (Subgroup.mem_subgroupOf.mp hx.1).1
    have hxS : (x : G) ∈ Sg := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem N.subtype hx.2
    have hxbot : (x : G) ∈ K ⊓ Sg := ⟨hxK, hxS⟩
    rw [hKinf] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hcomp := complement_inf_oTwoPrime h hαβ hKle hKinf hKsup
  have hpoint : hN.pointSubgroup β =
      Subgroup.normalizer ((hN.pointSylowN h.adj_smul (h.finite_stab α)
        (h.valency α).2 (h.valency α).1 β : Sylow 2 N) : Subgroup N) :=
    hN.pointSubgroup_eq_normalizer_pointSylowN h.adj_smul (h.finite_stab α)
      (h.valency α).2 (h.valency α).1 hαβ
  have hSeq : S = hN.pointSylowN h.adj_smul (h.finite_stab α)
      (h.valency α).2 (h.valency α).1 β := by
    apply Sylow.ext
    rw [hS]
    calc (Sg).subgroupOf N
        = (vertexSylowMap h hN β).subgroupOf N := by rw [hSg_eq]
      _ = (hN.pointSylowN h.adj_smul (h.finite_stab α)
            (h.valency α).2 (h.valency α).1 β : Subgroup N) := by
          rw [vertexSylowMap]
          ext x
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
          constructor
          · rintro ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            simpa [hyx'] using hy
          · intro hx
            exact ⟨x, hx, rfl⟩
  have hsup : K' ⊔ (S : Subgroup N) = Subgroup.normalizer ((S : Subgroup N) : Set N) := by
    calc K' ⊔ (S : Subgroup N)
        = (((K ⊓ N) ⊔ Sg).subgroupOf N) := by
          rw [show K' = (K ⊓ N).subgroupOf N from rfl,
            show (S : Subgroup N) = Sg.subgroupOf N from hS]
          exact (Subgroup.subgroupOf_sup inf_le_right hSylowN.1).symm
      _ = ((N ⊓ MulAction.stabilizer G β).subgroupOf N) := by
          rw [show (K ⊓ N) = K ⊓ oTwoPrime Gα from rfl, hcomp.2]
      _ = Subgroup.normalizer ((S : Subgroup N) : Set N) := by
          rw [hSeq]
          exact hpoint
  exact ⟨S, K', hSmap, hKmap, hKS, hsup⟩


theorem exists_fixed_neighbor (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    ∃ γ : V, Γ.Adj α γ ∧ γ ≠ β ∧ ∀ k ∈ K, k • γ = γ := by
  classical
  let n := nOf Γ α
  have hn1 : 1 ≤ n := (h.valency α).1
  have hcard : Nat.card (Γ.neighborSet α) = 2 ^ n + 1 := (h.valency α).2
  have hN : IsLocL2 Γ G α n (oTwoPrime (MulAction.stabilizer G α)) := h.isLocL2_oTwoPrime α
  rcases lt_or_ge n 2 with hn | hn
  ·
    have hn1' : n = 1 := by omega
    have hoddK : Odd (Nat.card ↥K) := odd_card_of_complement h hαβ hKle hKinf hKsup
    haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by
      rintro h0
      rw [h0] at hoddK
      exact (Nat.not_odd_zero) hoddK)
    obtain ⟨γ, hαγ, hγβ⟩ := h.exists_adj_ne α β
    refine ⟨γ, hαγ, hγβ, fun k hk => ?_⟩
    letI : Fintype ↥K := Fintype.ofFinite _
    haveI : Finite (MulAction.orbit ↥K γ) := by
      have hfin : (MulAction.orbit ↥K γ : Set V).Finite := by
        simpa [MulAction.orbit] using Set.finite_range (fun k : ↥K => k • γ)
      exact hfin.to_subtype
    letI : Fintype (MulAction.orbit ↥K γ) := Fintype.ofFinite _
    have horb_dvd : Nat.card (MulAction.orbit ↥K γ) ∣ Nat.card ↥K := by
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥K) γ
      exact ⟨_, by simpa only [Nat.card_eq_fintype_card] using h.symm⟩
    have hoddorb : Odd (Nat.card (MulAction.orbit ↥K γ)) := hoddK.of_dvd_nat horb_dvd
    have horb_sub : (MulAction.orbit ↥K γ : Set V) ⊆
        {x : V | Γ.Adj α x ∧ x ≠ β} := by
      rintro x ⟨k, rfl⟩
      have hkα : (k : G) • α = α := (Subgroup.mem_inf.mp (hKle k.2)).1
      have hkβ : (k : G) • β = β := (Subgroup.mem_inf.mp (hKle k.2)).2
      refine ⟨?_, ?_⟩
      · rw [← hkα]
        simpa only [MulAction.subgroup_smul_def] using (h.adj_smul (k : G) α γ).2 hαγ
      · intro hx
        apply hγβ
        have : (k : G) • γ = β := by simpa [MulAction.subgroup_smul_def] using hx
        calc γ = (k : G)⁻¹ • ((k : G) • γ) := by simp
          _ = (k : G)⁻¹ • β := by rw [this]
          _ = β := by
            have h := congrArg (fun x : V => (k : G)⁻¹ • x) hkβ
            simpa using h.symm
    have hneighbor_fin : (Γ.neighborSet α).Finite := h.finite_neighborSet α
    have htarget : ({x : V | Γ.Adj α x ∧ x ≠ β}).ncard = 2 := by
      have hset : {x : V | Γ.Adj α x ∧ x ≠ β} = Γ.neighborSet α \ {β} := by
        ext x
        simp [SimpleGraph.mem_neighborSet]
      rw [hset, Set.ncard_sdiff_singleton_of_mem (by
        rw [SimpleGraph.mem_neighborSet]; exact hαβ)]
      have h3 : (Γ.neighborSet α).ncard = 3 := by
        rw [← Nat.card_coe_set_eq, hcard, hn1']
        norm_num
      omega
    have horb_le : Nat.card (MulAction.orbit ↥K γ) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc (MulAction.orbit ↥K γ : Set V).ncard
          ≤ ({x : V | Γ.Adj α x ∧ x ≠ β}).ncard :=
            Set.ncard_le_ncard horb_sub (hneighbor_fin.subset (fun x hx => hx.1))
        _ = 2 := htarget
    have hone : Nat.card (MulAction.orbit ↥K γ) = 1 := by
      have hpos : 0 < Nat.card (MulAction.orbit ↥K γ) := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_pos (Set.finite_range (fun k : ↥K => k • γ))).mpr
          ⟨γ, MulAction.mem_orbit_self γ⟩
      rcases Nat.eq_or_lt_of_le horb_le with h | h
      · exfalso
        have heven : Even (Nat.card (MulAction.orbit ↥K γ)) := by rw [h]; norm_num
        exact (Nat.not_even_iff_odd.mpr hoddorb) heven
      · omega
    haveI : Subsingleton (MulAction.orbit ↥K γ) := (Nat.card_eq_one_iff_unique.mp hone).1
    let xK : MulAction.orbit ↥K γ :=
      ⟨(⟨k, hk⟩ : ↥K) • γ, MulAction.mem_orbit γ (⟨k, hk⟩ : ↥K)⟩
    have hsingle : xK = ⟨γ, MulAction.mem_orbit_self γ⟩ := Subsingleton.elim _ _
    have hfix : (⟨k, hk⟩ : ↥K) • γ = γ := congrArg Subtype.val hsingle
    simpa [MulAction.subgroup_smul_def] using hfix
  ·
    obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ :=
      exists_edgeTorusSylow h hαβ hKle hKinf hKsup
    have hcyc := hN.torus_cyclic h.adj_smul (h.finite_stab α) hcard hn1 S K' hKS hsup
    have hK'card : Nat.card ↥K' = 2 ^ n - 1 := hcyc.2
    have hpow : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hK'ne : K' ≠ ⊥ := by
      intro hbot
      rw [hbot] at hK'card
      simp at hK'card
      omega
    haveI : IsCyclic ↥K' := hcyc.1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K')
    let N : Subgroup G := oTwoPrime (MulAction.stabilizer G α)
    let gN : N := ((g : ↥K') : N)
    have hg1 : g ≠ 1 := by
      intro hg1
      apply hK'ne
      rw [eq_bot_iff]
      intro x hx
      have hx' := hg ⟨x, hx⟩
      rw [hg1] at hx'
      simpa using hx'
    have hgN1 : gN ≠ 1 := by
      intro h
      apply hg1
      exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : G)) h))
    have hfixg := hN.torus_fixes_two h.adj_smul (h.finite_stab α) hcard hn1 S K' hKS hsup g hg1
    have hK'eq : Subgroup.zpowers gN = K' := by
      change Subgroup.zpowers (K'.subtype g) = K'
      rw [← MonoidHom.map_zpowers K'.subtype g]
      refine le_antisymm ?_ ?_
      · rintro x ⟨y, hy, rfl⟩
        exact y.2
      · intro x hx
        exact Subgroup.mem_map_of_mem _ (hg ⟨x, hx⟩)
    let F : Set V := {a : V | Γ.Adj α a ∧ ∀ k ∈ K', k • a = a}
    have hFeq : F = {a : V | Γ.Adj α a ∧ (gN : G) • a = a} := by
      ext a
      constructor
      · intro ha
        exact ⟨ha.1, ha.2 g g.2⟩
      · rintro ⟨ha, hga⟩
        refine ⟨ha, fun k hk => ?_⟩
        have hgle : Subgroup.zpowers gN ≤ MulAction.stabilizer N a :=
          Subgroup.zpowers_le.mpr (by
            rw [MulAction.mem_stabilizer_iff]
            simpa [MulAction.subgroup_smul_def] using hga)
        have hK'le : K' ≤ MulAction.stabilizer N a := by
          rwa [hK'eq] at hgle
        exact MulAction.mem_stabilizer_iff.mp (hK'le hk)
    have hFcard : F.ncard = 2 := by
      rw [hFeq]
      exact hfixg
    have hβF : β ∈ F := by
      refine ⟨hαβ, fun k hk => ?_⟩
      have hkK : (k : G) ∈ K := by
        have hmem : (k : G) ∈ K'.map N.subtype := Subgroup.mem_map_of_mem _ hk
        rw [hKmap] at hmem
        exact hmem.1
      have := (Subgroup.mem_inf.mp (hKle hkK)).2
      simpa [MulAction.subgroup_smul_def] using MulAction.mem_stabilizer_iff.mp this
    have hFfin : F.Finite :=
      (h.finite_neighborSet α).subset (fun a ha => by
        simpa [SimpleGraph.mem_neighborSet] using ha.1)
    have hone_lt : 1 < F.ncard := by rw [hFcard]; norm_num
    obtain ⟨γ, hγF, hγβ⟩ := Set.exists_ne_of_one_lt_ncard hone_lt β
    refine ⟨γ, hγF.1, hγβ, fun k hk => ?_⟩
    have hkα : k • α = α := (Subgroup.mem_inf.mp (hKle hk)).1
    have hkβ : k • β = β := (Subgroup.mem_inf.mp (hKle hk)).2
    have hpair : F = ({β, γ} : Set V) := by
      have hsub : ({β, γ} : Set V) ⊆ F := by
        intro a ha
        rcases ha with ha | ha
        · subst ha; exact hβF
        · subst ha; exact hγF
      have hpaircard : ({β, γ} : Set V).ncard = 2 := Set.ncard_pair (Ne.symm hγβ)
      refine (Set.eq_of_subset_of_ncard_le hsub ?_ hFfin).symm
      rw [hFcard, hpaircard]
    have hkF : ∀ a ∈ F, k • a ∈ F := by
      intro a ha
      have hka : Γ.Adj α (k • a) := by
        rw [← hkα]
        exact (h.adj_smul k α a).2 ha.1
      refine ⟨hka, fun z hz => ?_⟩
      have hkGα : k ∈ MulAction.stabilizer G α := MulAction.mem_stabilizer_iff.mpr hkα
      have hknormN : k ∈ Subgroup.normalizer (N : Set G) :=
        le_normalizer_oTwoPrime (MulAction.stabilizer G α) hkGα
      have hKiff : ∀ h : G, h ∈ K ↔ k⁻¹ * h * k ∈ K := by
        intro h
        constructor
        · intro hh
          exact K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
        · intro hh
          have : h = k * (k⁻¹ * h * k) * k⁻¹ := by group
          rw [this]
          exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
      have hNiff : ∀ h : G, h ∈ N ↔ k⁻¹ * h * k ∈ N :=
        Subgroup.mem_normalizer_iff''.mp hknormN
      have hknorm : k ∈ Subgroup.normalizer (K'.map N.subtype : Set G) := by
        rw [hKmap, Subgroup.mem_normalizer_iff'']
        intro h
        rw [Subgroup.mem_inf, Subgroup.mem_inf, hKiff h, hNiff h]
      have hzmem : (k⁻¹ : G) * (z : G) * k ∈ K'.map N.subtype :=
        ((Subgroup.mem_normalizer_iff''.mp hknorm) (z : G)).mp
          (Subgroup.mem_map_of_mem _ hz)
      obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.mp hzmem
      have hz'val : (z' : G) = (k⁻¹ : G) * (z : G) * k := hz'eq
      calc z • (k • a) = ((z : G) * k) • a := by
            rw [MulAction.subgroup_smul_def, mul_smul]
        _ = (k * (z' : G)) • a := by
          congr 1
          rw [hz'val]
          group
        _ = k • (z' • a) := by
            rw [mul_smul, MulAction.subgroup_smul_def]
        _ = k • a := by rw [ha.2 z' hz']
    have hkγF : k • γ ∈ F := hkF γ hγF
    rw [hpair] at hkγF
    rcases hkγF with h | h
    · exfalso
      have : γ = β := by
        calc γ = k⁻¹ • (k • γ) := by simp
          _ = k⁻¹ • β := by rw [h]
          _ = k⁻¹ • (k • β) := by rw [hkβ]
          _ = β := by simp
      exact hγβ this
    · exact h


theorem exists_conj_eq_of_complement {F : Subgroup G} [Finite ↥F] {N : Subgroup G}
    (hNF : N ≤ F) (hNnorm : (N.subgroupOf F).Normal) (hSylow : IsSylowTwoOf N F)
    {H K : Subgroup G} (hHF : H ≤ F) (hKF : K ≤ F)
    (hNH : N ⊔ H = F) (hNK : N ⊔ K = F)
    (hNH' : N ⊓ H = ⊥) (hNK' : N ⊓ K = ⊥) :
    ∃ n ∈ N, K = conjSub n⁻¹ H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥N :=
    Finite.of_injective (Subgroup.inclusion hNF) (Subgroup.inclusion_injective hNF)
  let N' : Subgroup ↥F := N.subgroupOf F
  let H' : Subgroup ↥F := H.subgroupOf F
  let K' : Subgroup ↥F := K.subgroupOf F
  haveI : N'.Normal := hNnorm
  have hN'p : IsPGroup 2 ↥N' :=
    hSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hNF).symm
  haveI : Group.IsNilpotent ↥N' := hN'p.isNilpotent
  have hN'solv : Group.IsSolvable ↥N' := inferInstance
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNF).toEquiv
  have hN'index : N'.index = N.relIndex F := rfl
  have hcop : Nat.Coprime (Nat.card ↥N') N'.index := by
    rw [hN'card, hN'index]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSylow.2.1
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSylow.2.2)
  have hNHmul : (N' : Set ↥F) * (H' : Set ↥F) = Set.univ := by
    have hsup : N' ⊔ H' = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNF hHF, hNH, Subgroup.subgroupOf_self]
    rw [← Subgroup.normal_mul N' H', hsup]
    rfl
  have hNKmul : (N' : Set ↥F) * (K' : Set ↥F) = Set.univ := by
    have hsup : N' ⊔ K' = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNF hKF, hNK, Subgroup.subgroupOf_self]
    rw [← Subgroup.normal_mul N' K', hsup]
    rfl
  have hNH'F : N' ⊓ H' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx.1
    have hxH : (x : G) ∈ H := Subgroup.mem_subgroupOf.mp hx.2
    have hxbot : (x : G) ∈ N ⊓ H := ⟨hxN, hxH⟩
    rw [hNH'] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hNK'F : N' ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx.1
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx.2
    have hxbot : (x : G) ∈ N ⊓ K := ⟨hxN, hxK⟩
    rw [hNK'] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  obtain ⟨n, hn, hEq⟩ :=
    CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N' hN'solv hcop
      hNHmul hNKmul hNH'F hNK'F
  refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hn, ?_⟩
  have hmap := congrArg (Subgroup.map F.subtype) hEq
  rw [Subgroup.map_subgroupOf_eq_of_le hKF, Subgroup.map_map] at hmap
  have hcomp : F.subtype.comp (MulAut.conj n⁻¹).toMonoidHom =
      (MulAut.conj ((n : G)⁻¹)).toMonoidHom.comp F.subtype := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHF] at hmap
  exact hmap


theorem card_conjSub (g : G) (H : Subgroup G) :
    Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _)

theorem inf_eq_bot_of_odd_of_isPGroup {A B : Subgroup G} (hA : Odd (Nat.card ↥A))
    (hB : IsPGroup 2 ↥B) : A ⊓ B = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by
    rintro h0
    rw [h0] at hA
    exact Nat.not_odd_zero hA)
  haveI : Finite ↥(A ⊓ B) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have h2 : IsPGroup 2 ↥(A ⊓ B) := hB.to_le inf_le_right
  have hodd : Odd (Nat.card ↥(A ⊓ B)) := hA.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hn0 : n = 0 := by
    by_contra hn0
    have heven : Even (2 ^ n) := by
      rw [show n = (n - 1) + 1 by omega, pow_succ]
      exact even_two.mul_left _
    rw [hn] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]

theorem card_mul_pCoreOf_edgeStab (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    Nat.card ↥K * Nat.card ↥(pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)) =
      Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  let Gα := MulAction.stabilizer G α
  let Gβ := MulAction.stabilizer G β
  let S := pCoreOf 2 (Gα ⊓ Gβ)
  have hSle : S ≤ Gα ⊓ Gβ := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSnorm : K ≤ Subgroup.normalizer (S : Set G) :=
    hKle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Gα ⊓ Gβ))
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    S K hSnorm (by rw [disjoint_iff, inf_comm, hKinf])
  rw [sup_comm, hKsup] at h
  rw [mul_comm (Nat.card ↥K) (Nat.card ↥S)]
  exact h.symm


theorem exists_normalizer_fixes_moves (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β)
    {K : Subgroup G}
    (hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hKinf : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hKsup : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    ∃ x ∈ Subgroup.normalizer (K : Set G), x • α = α ∧ x • β ≠ β := by
  classical
  obtain ⟨γ, hαγ, hγβ, hKγ⟩ := exists_fixed_neighbor h hαβ hKle hKinf hKsup
  obtain ⟨g, hgL, hgβ⟩ := (h.isLocL2_oTwoPrime α).trans β γ hαβ hαγ
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.mp ((h.isLocL2_oTwoPrime α).le hgL)
  let Gα := MulAction.stabilizer G α
  let Gβ := MulAction.stabilizer G β
  let Gγ := MulAction.stabilizer G γ
  let F := Gα ⊓ Gγ
  let S := pCoreOf 2 (Gα ⊓ Gβ)
  let SF := pCoreOf 2 F
  haveI : Finite ↥F := finite_of_le_stabilizer h (H := F) inf_le_left
  have hF_eq : F = conjSub g (Gα ⊓ Gβ) := by
    have hGγ_eq : Gγ = conjSub g Gβ := by
      have h := stabilizer_smul_eq_conjSub g β
      rwa [hgβ] at h
    have hGα_eq : Gα = conjSub g Gα := by
      have h := stabilizer_smul_eq_conjSub g α
      rwa [hgα] at h
    calc F = Gα ⊓ Gγ := rfl
      _ = conjSub g Gα ⊓ conjSub g Gβ := by
          conv_lhs => rw [hGα_eq, hGγ_eq]
      _ = conjSub g (Gα ⊓ Gβ) := by rw [← conjSub_inf]
  have hSF_eq : SF = conjSub g S := by
    rw [show SF = pCoreOf 2 F from rfl, hF_eq, pCoreOf_conjSub]
  have hSylowS : IsSylowTwoOf S (Gα ⊓ Gβ) := isSylowTwoOf_pCoreOf_edgeStab h hαβ
  have hSylowSF : IsSylowTwoOf SF F := by
    rw [hF_eq, hSF_eq]
    exact F7.isSylowTwoOf_conj hSylowS g
  have hSFle : SF ≤ F := hSylowSF.1
  have hSFnorm : F ≤ Subgroup.normalizer (SF : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 F
  have hKleF : K ≤ F :=
    le_inf (fun k hk => (Subgroup.mem_inf.mp (hKle hk)).1)
      (fun k hk => MulAction.mem_stabilizer_iff.mpr (hKγ k hk))
  have hoddK : Odd (Nat.card ↥K) := odd_card_of_complement h hαβ hKle hKinf hKsup
  have hKinfF : K ⊓ SF = ⊥ := inf_eq_bot_of_odd_of_isPGroup hoddK hSylowSF.2.1
  have hcardF : Nat.card ↥K * Nat.card ↥SF = Nat.card ↥F := by
    rw [hSF_eq, hF_eq, card_conjSub, card_conjSub]
    exact card_mul_pCoreOf_edgeStab h hαβ hKle hKinf hKsup
  have hKsupF : K ⊔ SF = F := by
    have hsup_le : K ⊔ SF ≤ F := sup_le hKleF hSFle
    have hsupcard : Nat.card ↥(K ⊔ SF) = Nat.card ↥F := by
      have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        SF K (hKleF.trans hSFnorm) (by rw [disjoint_iff, inf_comm, hKinfF])
      rw [sup_comm] at h
      rw [h, mul_comm (Nat.card ↥SF) (Nat.card ↥K), hcardF]
    exact Subgroup.eq_of_le_of_card_ge hsup_le (le_of_eq hsupcard.symm)
  have hKconjle : conjSub g K ≤ F := by
    rw [hF_eq]
    exact conjSub_mono g hKle
  have hKconjinf : conjSub g K ⊓ SF = ⊥ := by
    rw [hSF_eq, ← conjSub_inf, hKinf, conjSub_bot]
  have hKconjsup : conjSub g K ⊔ SF = F := by
    rw [hF_eq, hSF_eq, ← conjSub_sup, hKsup]
  obtain ⟨n, hnSF, hnEq⟩ := exists_conj_eq_of_complement hSFle
    (Subgroup.normal_subgroupOf_of_le_normalizer hSFnorm) hSylowSF hKleF hKconjle
    (by rw [sup_comm]; exact hKsupF) (by rw [sup_comm]; exact hKconjsup)
    (by rw [inf_comm]; exact hKinfF) (by rw [inf_comm]; exact hKconjinf)
  refine ⟨n * g, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub (n * g) K = K
    rw [conjSub_mul, hnEq, conjSub_inv_conjSub]
  · have hnGα : n ∈ Gα := (Subgroup.mem_inf.mp (hSFle hnSF)).1
    have hnα : n • α = α := MulAction.mem_stabilizer_iff.mp hnGα
    rw [mul_smul, hgα, hnα]
  · have hnGγ : n ∈ Gγ := (Subgroup.mem_inf.mp (hSFle hnSF)).2
    have hnγ : n • γ = γ := MulAction.mem_stabilizer_iff.mp hnGγ
    rw [mul_smul, hgβ, hnγ]
    exact hγβ


theorem Hyp30.exists_setup (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {K : Subgroup G}
    (hK₁ : K ⊓ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = ⊥)
    (hK₂ : K ⊔ pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    ∃ X : Setup Γ G, X.vert 0 = α ∧ X.vert 1 = β ∧ X.K = K := by
  classical
  have hKle : K ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    rw [← hK₂]
    exact le_sup_left
  obtain ⟨x, hxnorm, hxα, hxβ⟩ := exists_normalizer_fixes_moves h hαβ hKle hK₁ hK₂
  have hKle' : K ≤ MulAction.stabilizer G β ⊓ MulAction.stabilizer G α := by
    rw [inf_comm (MulAction.stabilizer G β) (MulAction.stabilizer G α)]
    exact hKle
  have hK₁' : K ⊓ pCoreOf 2 (MulAction.stabilizer G β ⊓ MulAction.stabilizer G α) = ⊥ := by
    rw [inf_comm (MulAction.stabilizer G β) (MulAction.stabilizer G α)]
    exact hK₁
  have hK₂' : K ⊔ pCoreOf 2 (MulAction.stabilizer G β ⊓ MulAction.stabilizer G α) =
      MulAction.stabilizer G β ⊓ MulAction.stabilizer G α := by
    rw [inf_comm (MulAction.stabilizer G β) (MulAction.stabilizer G α), hK₂]
  obtain ⟨y, hynorm, hyβ, hyα⟩ :=
    exists_normalizer_fixes_moves h hαβ.symm hKle' hK₁' hK₂'
  have hcross : CrossPair α β x y := ⟨hxα, hxβ, hyβ, hyα⟩
  have hKα : ∀ k ∈ K, k • α = α := fun k hk => (Subgroup.mem_inf.mp (hKle hk)).1
  have hKβ : ∀ k ∈ K, k • β = β := fun k hk => (Subgroup.mem_inf.mp (hKle hk)).2
  obtain ⟨T, hTK, -, hT0, hT1⟩ :=
    exists_kTrack h.adj_smul hαβ hKα hKβ hcross hxnorm hynorm
  refine ⟨{ T with hyp := h, K_inf := ?_, K_sup := ?_ }, ?_, ?_, ?_⟩
  · simpa [hT0, hT1, hTK] using hK₁
  · simpa [hT0, hT1, hTK] using hK₂
  · exact hT0
  · exact hT1
  · exact hTK

theorem Hyp30.exists_setup' (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    ∃ X : Setup Γ G, X.vert 0 = α ∧ X.vert 1 = β := by
  obtain ⟨K, -, hKinf, hKsup⟩ := exists_complement_pCoreOf_edgeStab h hαβ
  obtain ⟨X, hX0, hX1, -⟩ := h.exists_setup hαβ hKinf hKsup
  exact ⟨X, hX0, hX1⟩



theorem exists_offLine_adj {ℓ : Line Γ} (hT : Γ.IsTree) {v : V}
    (hv : v ∉ Set.range ℓ.vert) :
    ∃ (m : ℤ) (ρ : V), Γ.Adj (ℓ.vert m) ρ ∧ ρ ∉ Set.range ℓ.vert ∧
      Γ.dist v (ℓ.vert m) = Γ.dist v ρ + 1 := by
  classical
  let d : ℤ → ℕ := fun i => Γ.dist v (ℓ.vert i)
  let M := d 0
  let S : Set ℤ := Set.Icc (-(2 * (M : ℤ))) (2 * (M : ℤ))
  have hSfin : S.Finite := Set.finite_Icc _ _
  have hSne : S.Nonempty := ⟨0, by simp [S]⟩
  obtain ⟨m, -, hmmin⟩ := Set.exists_min_image S d hSfin hSne
  have hdmin : ∀ i : ℤ, d m ≤ d i := by
    intro i
    by_cases hi : i ∈ S
    · exact hmmin i hi
    · have hi' : 2 * (M : ℤ) < i ∨ i < -(2 * (M : ℤ)) := by
        by_contra h
        push Not at h
        apply hi
        change i ∈ Set.Icc (-(2 * (M : ℤ))) (2 * (M : ℤ))
        rw [Set.mem_Icc]
        omega
      have hlarge : (2 * (M : ℤ)) < (i.natAbs : ℤ) := by
        rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
        · rw [Int.natAbs_natCast]
          omega
        · rw [Int.natAbs_neg, Int.natAbs_natCast]
          omega
      have hlarge' : 2 * M < i.natAbs := by exact_mod_cast hlarge
      have hd : Γ.dist (ℓ.vert i) (ℓ.vert 0) = i.natAbs := by
        rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
        · rw [SimpleGraph.dist_comm, Line.dist_eq hT ℓ (show (0 : ℤ) ≤ n by omega)]
          simp
        · rw [Line.dist_eq hT ℓ (show (-(n : ℤ)) ≤ 0 by omega)]
          simp
      have htri : i.natAbs ≤ d i + M := by
        have h := hT.connected.dist_triangle (u := ℓ.vert i) (v := v) (w := ℓ.vert 0)
        rw [hd, SimpleGraph.dist_comm (u := ℓ.vert i) (v := v)] at h
        dsimp [M, d] at h ⊢
        exact h
      have hgt : M < d i := by omega
      exact le_of_lt (lt_of_le_of_lt (hmmin 0 (by simp [S])) hgt)
  have hm1 : d (m - 1) = d m + 1 := by
    have hle : d m ≤ d (m - 1) := hdmin (m - 1)
    have h := IsTree.dist_adj_cases hT (r := v) (ℓ.adj (m - 1))
    rw [show m - 1 + 1 = m by omega] at h
    change Γ.dist v (ℓ.vert m) ≤ Γ.dist v (ℓ.vert (m - 1)) at hle
    change Γ.dist v (ℓ.vert (m - 1)) = Γ.dist v (ℓ.vert m) + 1
    omega
  have hm2 : d (m + 1) = d m + 1 := by
    have hle : d m ≤ d (m + 1) := hdmin (m + 1)
    have h := IsTree.dist_adj_cases hT (r := v) (ℓ.adj m)
    change Γ.dist v (ℓ.vert m) ≤ Γ.dist v (ℓ.vert (m + 1)) at hle
    change Γ.dist v (ℓ.vert (m + 1)) = Γ.dist v (ℓ.vert m) + 1
    omega
  have hdm_ne : d m ≠ 0 := by
    intro h0
    apply hv
    exact ⟨m, (hT.connected.dist_eq_zero_iff.mp h0).symm⟩
  have hdm_pos : 0 < d m := Nat.pos_of_ne_zero hdm_ne
  have hdm_eq : Γ.dist v (ℓ.vert m) = d m - 1 + 1 := by
    have hpos : 0 < Γ.dist v (ℓ.vert m) := hdm_pos
    change Γ.dist v (ℓ.vert m) = Γ.dist v (ℓ.vert m) - 1 + 1
    omega
  obtain ⟨ρ, hρadj, hρdist⟩ := IsTree.exists_adj_dist_succ hT
    (u := v) (v := ℓ.vert m) (n := d m - 1) hdm_eq
  have hρnot : ρ ∉ Set.range ℓ.vert := by
    rintro ⟨j, rfl⟩
    have hdist : Γ.dist (ℓ.vert m) (ℓ.vert j) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hρadj.symm
    have hjm : (j - m).natAbs = 1 := by
      rcases le_total m j with hmj | hjm'
      · rw [Line.dist_eq hT ℓ hmj] at hdist
        have h1 : ((j - m).toNat : ℤ) = 1 := by exact_mod_cast hdist
        rw [Int.ofNat_toNat, max_eq_left (show (0 : ℤ) ≤ j - m by omega)] at h1
        omega
      · rw [SimpleGraph.dist_comm, Line.dist_eq hT ℓ hjm'] at hdist
        have h1 : ((m - j).toNat : ℤ) = 1 := by exact_mod_cast hdist
        rw [Int.ofNat_toNat, max_eq_left (show (0 : ℤ) ≤ m - j by omega)] at h1
        omega
    have hj : j = m + 1 ∨ j = m - 1 := by
      rcases Int.natAbs_eq (j - m) with h | h
      · left; omega
      · right; omega
    rcases hj with hj | hj
    · rw [hj] at hρdist
      change d (m + 1) = d m - 1 at hρdist
      rw [hm2] at hρdist
      omega
    · rw [hj] at hρdist
      change d (m - 1) = d m - 1 at hρdist
      rw [hm1] at hρdist
      omega
  refine ⟨m, ρ, hρadj.symm, hρnot, ?_⟩
  dsimp [d] at hρdist ⊢
  omega

namespace Setup

variable (X : Setup Γ G)

abbrev edgeSylow (i : ℤ) : Subgroup G := pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1))

theorem edgeSylow_zero : X.edgeSylow 0 = X.S := by
  unfold Setup.edgeSylow Setup.S
  congr 2


theorem card_edgeStab_eq (i : ℤ) :
    Nat.card ↥(X.Gi i ⊓ X.Gi (i + 1)) = Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) := by
  obtain ⟨g, -, hg | hg⟩ :=
    X.hyp.edgeTrans (X.vert i) (X.vert (i + 1)) (X.vert 0) (X.vert 1) (X.adj i) (X.adj 0)
  · have h0 : X.Gi 0 = conjSub g (X.Gi i) := by
      rw [Setup.Gi, Setup.Gi, ← hg.1, stabilizer_smul_eq_conjSub]
    have h1 : X.Gi 1 = conjSub g (X.Gi (i + 1)) := by
      rw [Setup.Gi, Setup.Gi, ← hg.2, stabilizer_smul_eq_conjSub]
    rw [h0, h1, ← conjSub_inf]
    exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulEquiv.injective _)).symm
  · have h0 : X.Gi 0 = conjSub g (X.Gi (i + 1)) := by
      rw [Setup.Gi, Setup.Gi, ← hg.2, stabilizer_smul_eq_conjSub]
    have h1 : X.Gi 1 = conjSub g (X.Gi i) := by
      rw [Setup.Gi, Setup.Gi, ← hg.1, stabilizer_smul_eq_conjSub]
    rw [h0, h1, inf_comm, ← conjSub_inf]
    exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulEquiv.injective _)).symm

theorem card_edgeSylow_eq (i : ℤ) : Nat.card ↥(X.edgeSylow i) = Nat.card ↥(X.edgeSylow 0) := by
  obtain ⟨g, -, hg | hg⟩ :=
    X.hyp.edgeTrans (X.vert i) (X.vert (i + 1)) (X.vert 0) (X.vert 1) (X.adj i) (X.adj 0)
  · have h0 : X.Gi 0 = conjSub g (X.Gi i) := by
      rw [Setup.Gi, Setup.Gi, ← hg.1, stabilizer_smul_eq_conjSub]
    have h1 : X.Gi 1 = conjSub g (X.Gi (i + 1)) := by
      rw [Setup.Gi, Setup.Gi, ← hg.2, stabilizer_smul_eq_conjSub]
    have hconj : X.edgeSylow 0 = conjSub g (X.edgeSylow i) := by
      unfold Setup.edgeSylow
      have h01 : X.Gi (0 + 1) = X.Gi 1 := by congr 1
      rw [h01, h0, h1, ← conjSub_inf, pCoreOf_conjSub]
    rw [hconj]
    exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulEquiv.injective _)).symm
  · have h0 : X.Gi 0 = conjSub g (X.Gi (i + 1)) := by
      rw [Setup.Gi, Setup.Gi, ← hg.2, stabilizer_smul_eq_conjSub]
    have h1 : X.Gi 1 = conjSub g (X.Gi i) := by
      rw [Setup.Gi, Setup.Gi, ← hg.1, stabilizer_smul_eq_conjSub]
    have hconj : X.edgeSylow 0 = conjSub g (X.edgeSylow i) := by
      unfold Setup.edgeSylow
      have h01 : X.Gi (0 + 1) = X.Gi 1 := by congr 1
      rw [h01, h0, h1, inf_comm, ← conjSub_inf, pCoreOf_conjSub]
    rw [hconj]
    exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulEquiv.injective _)).symm

theorem odd_card_K : Odd (Nat.card ↥X.K) :=
  odd_card_of_complement X.hyp (X.adj 0) X.K_le_inf X.K_inf X.K_sup

theorem isSylowTwoOf_edgeSylow (i : ℤ) :
    IsSylowTwoOf (X.edgeSylow i) (X.Gi i ⊓ X.Gi (i + 1)) :=
  isSylowTwoOf_pCoreOf_edgeStab X.hyp (X.adj i)

theorem isPGroup_edgeSylow (i : ℤ) : IsPGroup 2 (X.edgeSylow i) :=
  (X.isSylowTwoOf_edgeSylow i).2.1

theorem edgeSylow_le_L (i : ℤ) : X.edgeSylow i ≤ X.L i :=
  le_oTwoPrime_of_isPGroup (X.isPGroup_edgeSylow i) ((X.isSylowTwoOf_edgeSylow i).1.trans inf_le_left)

theorem K_inf_edgeSylow (i : ℤ) : X.K ⊓ X.edgeSylow i = ⊥ := by
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Finite ↥(X.K ⊓ X.edgeSylow i) :=
    finite_of_le_stabilizer X.hyp (H := X.K ⊓ X.edgeSylow i)
      (inf_le_left.trans (X.K_le_Gi 0))
  have h2 : IsPGroup 2 ↥(X.K ⊓ X.edgeSylow i) :=
    (X.isPGroup_edgeSylow i).to_le inf_le_right
  have hodd : Odd (Nat.card ↥(X.K ⊓ X.edgeSylow i)) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hn0 : n = 0 := by
    by_contra hn0
    have heven : Even (2 ^ n) := by
      rw [show n = (n - 1) + 1 by omega, pow_succ]
      exact even_two.mul_left _
    rw [hn] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]

theorem K_sup_edgeSylow (i : ℤ) :
    X.K ⊔ X.edgeSylow i = X.Gi i ⊓ X.Gi (i + 1) := by
  have hKle : X.K ≤ X.Gi i ⊓ X.Gi (i + 1) := le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1))
  have hSle : X.edgeSylow i ≤ X.Gi i ⊓ X.Gi (i + 1) := (X.isSylowTwoOf_edgeSylow i).1
  have hSnorm0 : X.K ≤ Subgroup.normalizer (X.edgeSylow 0 : Set G) :=
    (le_inf (X.K_le_Gi 0) (X.K_le_Gi 1)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1))
  have hSnorm : X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) :=
    hKle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
  have hbase : Nat.card ↥X.K * Nat.card ↥(X.edgeSylow 0) =
      Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) := by
    rw [X.edgeSylow_zero]
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      X.S X.K (by rwa [X.edgeSylow_zero] at hSnorm0)
      (by rw [disjoint_iff, inf_comm, X.K_inf])
    rw [sup_comm, X.K_sup] at h
    rw [mul_comm (Nat.card ↥X.K) (Nat.card ↥X.S), ← h]
  have hcard : Nat.card ↥X.K * Nat.card ↥(X.edgeSylow i) =
      Nat.card ↥(X.Gi i ⊓ X.Gi (i + 1)) := by
    rw [X.card_edgeSylow_eq i, X.card_edgeStab_eq i, ← hbase]
  have hsupcard : Nat.card ↥(X.K ⊔ X.edgeSylow i) =
      Nat.card ↥(X.Gi i ⊓ X.Gi (i + 1)) := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.edgeSylow i) X.K hSnorm (by rw [disjoint_iff, inf_comm, X.K_inf_edgeSylow i])
    rw [sup_comm] at h
    rw [h, mul_comm, hcard]
  haveI : Finite ↥(X.Gi i ⊓ X.Gi (i + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi i ⊓ X.Gi (i + 1)) inf_le_left
  exact Subgroup.eq_of_le_of_card_ge (sup_le hKle hSle) (le_of_eq hsupcard.symm)

theorem edgeSylow_eq_vertexSylow (i : ℤ) :
    X.edgeSylow i = vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert i)) (X.vert (i + 1)) := by
  unfold Setup.edgeSylow
  rw [edgeSylow_eq_pCoreOf_edge X.hyp (X.adj i)
    (X.hyp.isLocL2_oTwoPrime (X.vert i)) (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))]
  exact edgeSylow_eq_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert i)) (X.adj i)

theorem isSylowTwoOf_edgeSylow_L (i : ℤ) :
    IsSylowTwoOf (X.edgeSylow i) (X.L i) := by
  rw [X.edgeSylow_eq_vertexSylow i]
  exact isSylowTwoOf_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert i)) (X.adj i)

theorem exists_torusSylow (i : ℤ) :
    ∃ (S : Sylow 2 (X.L i)) (K' : Subgroup (X.L i)),
      (S : Subgroup (X.L i)).map (X.L i).subtype = X.edgeSylow i ∧
      K'.map (X.L i).subtype = X.K ⊓ X.L i ∧
      K' ⊓ (S : Subgroup (X.L i)) = ⊥ ∧
      K' ⊔ (S : Subgroup (X.L i)) =
        Subgroup.normalizer ((S : Subgroup (X.L i)) : Set (X.L i)) :=
  exists_edgeTorusSylow X.hyp (X.adj i) (le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1)))
    (X.K_inf_edgeSylow i) (X.K_sup_edgeSylow i)

theorem torus_fixed (i : ℤ) (hn : 2 ≤ X.n i) {k : G} (hk : k ∈ X.Ki i) (hk1 : k ≠ 1) :
    ∀ a : V, Γ.Adj (X.vert i) a →
      (k • a = a ↔ a = X.vert (i - 1) ∨ a = X.vert (i + 1)) := by
  classical
  let N := X.L i
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) N := X.hyp.isLocL2_oTwoPrime (X.vert i)
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := X.exists_torusSylow i
  have hkN : k ∈ N := hk.2
  let kN : N := ⟨k, hkN⟩
  have hkK' : kN ∈ K' := by
    have h : (k : G) ∈ K'.map N.subtype := by
      rw [hKmap]
      exact ⟨hk.1, hkN⟩
    rw [Subgroup.mem_map] at h
    obtain ⟨y, hy, hyk⟩ := h
    have hyk' : y = kN := Subtype.ext hyk
    simpa [hyk'] using hy
  let kK : K' := ⟨kN, hkK'⟩
  have hkK1 : kK ≠ 1 := by
    intro h
    apply hk1
    have := congrArg (fun z : K' => ((z : N) : G)) h
    simpa [kK, kN] using this
  have hfix := hN.torus_fixes_two X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
    (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1 S K' hKS hsup kK hkK1
  have hfix' : Set.ncard {a : V | Γ.Adj (X.vert i) a ∧ k • a = a} = 2 := by
    simpa [kK, kN] using hfix
  have hleft_adj : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := X.adj (i - 1)
    rw [show i - 1 + 1 = i by omega] at h
    exact h.symm
  have hleft_fix : k • X.vert (i - 1) = X.vert (i - 1) := X.K_fix k hk.1 (i - 1)
  have hright_fix : k • X.vert (i + 1) = X.vert (i + 1) := X.K_fix k hk.1 (i + 1)
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hsub : ({X.vert (i - 1), X.vert (i + 1)} : Set V) ⊆
      {a : V | Γ.Adj (X.vert i) a ∧ k • a = a} := by
    intro a ha
    rcases ha with ha | ha
    · subst ha
      exact ⟨hleft_adj, hleft_fix⟩
    · subst ha
      exact ⟨X.adj i, hright_fix⟩
  have hpair : ({X.vert (i - 1), X.vert (i + 1)} : Set V).ncard = 2 := Set.ncard_pair hne
  have ht : {a : V | Γ.Adj (X.vert i) a ∧ k • a = a}.Finite :=
    (X.hyp.finite_neighborSet (X.vert i)).subset (fun a ha => by
      simpa [SimpleGraph.mem_neighborSet] using ha.1)
  have hset : {a : V | Γ.Adj (X.vert i) a ∧ k • a = a} =
      ({X.vert (i - 1), X.vert (i + 1)} : Set V) := by
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ ht).symm
    rw [hfix', hpair]
  intro a ha
  have hmem : a ∈ {b : V | Γ.Adj (X.vert i) b ∧ k • b = b} ↔
      a = X.vert (i - 1) ∨ a = X.vert (i + 1) := by
    rw [hset]
    simp
  exact ⟨fun h => hmem.mp ⟨ha, h⟩, fun h => (hmem.mpr h).2⟩


theorem Z_le_Q_of_le_Gi (i j k : ℤ) (h : X.Z i ≤ X.Gi j)
    (hk : k = i ∨ (min i j < k ∧ k < max i j)) : X.Z i ≤ X.Q k := by
  rcases hk with hk | hk
  · subst k
    exact X.Z_le_Q i
  · have hZi : X.Z i ≤ X.Gi i := X.Z_le_Gi i
    have hZmin : X.Z i ≤ X.Gi (min i j) := by
      rcases le_total i j with hij | hji
      · rwa [min_eq_left hij]
      · rwa [min_eq_right hji]
    have hZmax : X.Z i ≤ X.Gi (max i j) := by
      rcases le_total i j with hij | hji
      · rwa [max_eq_right hij]
      · rwa [max_eq_left hji]
    have hZk : X.Z i ≤ X.Gi k := by
      intro z hz
      exact X.mem_Gi_of_between (hZmin hz) (hZmax hz) (le_of_lt hk.1) (le_of_lt hk.2)
    have hZkm : X.Z i ≤ X.Gi (k - 1) := by
      intro z hz
      exact X.mem_Gi_of_between (hZmin hz) (hZmax hz) (by omega) (by omega)
    have hZkp : X.Z i ≤ X.Gi (k + 1) := by
      intro z hz
      exact X.mem_Gi_of_between (hZmin hz) (hZmax hz) (by omega) (by omega)
    have hZ2 : IsPGroup 2 ↥(X.Z i) :=
      (pCoreOf_isPGroup' (X.Gi i)).to_le (X.Z_le_Q i)
    have hleft : Γ.Adj (X.vert k) (X.vert (k - 1)) := by
      have h := X.adj (k - 1)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm
    have hne : X.vert (k - 1) ≠ X.vert (k + 1) := by
      intro h
      have := X.vert_injective h
      omega
    have := le_pCoreOf_of_isPGroup_fixes_two X.hyp hZ2 hZk hleft (X.adj k) hne
      (fun y hy => MulAction.mem_stabilizer_iff.mp (hZkm hy))
      (fun y hy => MulAction.mem_stabilizer_iff.mp (hZkp hy))
    exact this


theorem two_le_n (h0 : 2 ≤ X.n 0) (h1 : 2 ≤ X.n 1) (i : ℤ) : 2 ≤ X.n i := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' i
  · rw [hm, show 2 * m = 0 + 2 * m by omega, X.n_add]
    exact h0
  · rw [hm, show 2 * m + 1 = 1 + 2 * m by omega, X.n_add]
    exact h1

theorem torus_ne_bot (i : ℤ) (hn : 2 ≤ X.n i) : X.Ki i ≠ ⊥ := by
  classical
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := X.exists_torusSylow i
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hcyc := hN.torus_cyclic X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
    (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1 S K' hKS hsup
  have hcard : Nat.card ↥K' = 2 ^ X.n i - 1 := hcyc.2
  have hpow : 4 ≤ 2 ^ X.n i := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n i := Nat.pow_le_pow_right (by norm_num) hn
  intro hbot
  have hK'bot : K' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxmap : (x : G) ∈ K'.map (X.L i).subtype := Subgroup.mem_map_of_mem _ hx
    rw [hKmap] at hxmap
    have hxbot : (x : G) ∈ X.K ⊓ X.L i := hxmap
    rw [show X.K ⊓ X.L i = X.Ki i from rfl, hbot] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  rw [hK'bot] at hcard
  simp at hcard
  omega

theorem mem_range_of_fixed_K (h0 : 2 ≤ X.n 0) (h1 : 2 ≤ X.n 1) :
    ∀ v : V, (∀ k ∈ X.K, k • v = v) → v ∈ Set.range X.vert := by
  intro v hv
  by_contra hvT
  obtain ⟨m, ρ, hρadj, hρnot, hdist⟩ :=
    exists_offLine_adj X.hyp.isTree (ℓ := X.line) hvT
  have hKρ : ∀ k ∈ X.K, k • ρ = ρ := by
    intro k hk
    have hkv : k • v = v := hv k hk
    have hkTm : k • X.vert m = X.vert m := X.K_fix k hk m
    have hkdist : Γ.dist v (k • ρ) = Γ.dist v ρ := by
      calc Γ.dist v (k • ρ) = Γ.dist (k • v) (k • ρ) := by rw [hkv]
        _ = Γ.dist v ρ := IsTree.dist_smul X.hyp.isTree X.hyp.adj_smul k v ρ
    have hkadj : Γ.Adj (k • ρ) (X.vert m) := by
      rw [← hkTm]
      exact (X.hyp.adj_smul k ρ (X.vert m)).2 hρadj.symm
    have hd1 : Γ.dist v ρ + 1 = Γ.dist v (X.line.vert m) := hdist.symm
    have hd2 : Γ.dist v (k • ρ) + 1 = Γ.dist v (X.line.vert m) := by
      rw [hkdist]
      exact hdist.symm
    exact IsTree.eq_of_dist_succ X.hyp.isTree (r := v) (v := X.line.vert m)
      hkadj hρadj.symm hd2 hd1
  have hn : 2 ≤ X.n m := X.two_le_n h0 h1 m
  have hne : X.Ki m ≠ ⊥ := X.torus_ne_bot m hn
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hkG : (k : G) ∈ X.Ki m := k.2
  have hk1G : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hfixρ : (k : G) • ρ = ρ := hKρ (k : G) hkG.1
  have hcases := (X.torus_fixed m hn hkG hk1G ρ hρadj).mp hfixρ
  rcases hcases with h | h
  · exact hρnot ⟨m - 1, h.symm⟩
  · exact hρnot ⟨m + 1, h.symm⟩


theorem exists_adjacent_fix_move (X : Setup Γ G) {c : G} {j : ℤ}
    (hcj : c ∈ X.Gi j) (hcT : c ∉ X.GT) :
    ∃ k : ℤ, (c • X.vert k = X.vert k ∧ c • X.vert (k + 1) ≠ X.vert (k + 1)) ∨
      (c • X.vert k = X.vert k ∧ c • X.vert (k - 1) ≠ X.vert (k - 1)) := by
  classical
  have hcj' : c • X.vert j = X.vert j := MulAction.mem_stabilizer_iff.mp hcj
  have hnotall : ¬ ∀ i : ℤ, c • X.vert i = X.vert i := by
    intro h
    apply hcT
    rw [Setup.GT, Fan86.mem_fixSet]
    rintro v ⟨i, rfl⟩
    exact h i
  push Not at hnotall
  obtain ⟨l, hl⟩ := hnotall
  rcases lt_or_gt_of_ne (fun (h : j = l) => hl (h ▸ hcj')) with hjl | hlj
  · let Sf : Finset ℤ := (Finset.Icc j l).filter (fun i => c • X.vert i = X.vert i)
    have hjS : j ∈ Sf := by
      change j ∈ (Finset.Icc j l).filter (fun i => c • X.vert i = X.vert i)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, le_of_lt hjl⟩, hcj'⟩
    have hSfne : Sf.Nonempty := ⟨j, hjS⟩
    let k := Sf.max' hSfne
    have hkSf : k ∈ Sf := Finset.max'_mem _ _
    have hkfix : c • X.vert k = X.vert k := (Finset.mem_filter.mp hkSf).2
    have hlSf : l ∉ Sf := by
      rw [show Sf = (Finset.Icc j l).filter (fun i => c • X.vert i = X.vert i) from rfl]
      simp only [Finset.mem_filter, Finset.mem_Icc, not_and]
      intro _
      exact hl
    have hk_ge : j ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkSf).1).1
    have hk_le : k ≤ l := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkSf).1).2
    have hk_lt : k < l := by
      rcases lt_or_eq_of_le hk_le with h | h
      · exact h
      · exfalso
        exact hlSf (h ▸ hkSf)
    have hk1 : c • X.vert (k + 1) ≠ X.vert (k + 1) := by
      intro h
      have hmem : k + 1 ∈ Sf := by
        simp [Sf]
        exact ⟨⟨by omega, by omega⟩, h⟩
      have := Finset.le_max' Sf (k + 1) hmem
      omega
    exact ⟨k, Or.inl ⟨hkfix, hk1⟩⟩
  · let Sf : Finset ℤ := (Finset.Icc l j).filter (fun i => c • X.vert i = X.vert i)
    have hjS : j ∈ Sf := by
      change j ∈ (Finset.Icc l j).filter (fun i => c • X.vert i = X.vert i)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_of_lt hlj, le_rfl⟩, hcj'⟩
    have hSfne : Sf.Nonempty := ⟨j, hjS⟩
    let k := Sf.min' hSfne
    have hkSf : k ∈ Sf := Finset.min'_mem _ _
    have hkfix : c • X.vert k = X.vert k := (Finset.mem_filter.mp hkSf).2
    have hlSf : l ∉ Sf := by
      rw [show Sf = (Finset.Icc l j).filter (fun i => c • X.vert i = X.vert i) from rfl]
      simp only [Finset.mem_filter, Finset.mem_Icc, not_and]
      intro _
      exact hl
    have hk_le : l ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkSf).1).1
    have hk_le_j : k ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkSf).1).2
    have hl_lt : l < k := by
      rcases lt_or_eq_of_le hk_le with h | h
      · exact h
      · exfalso
        exact hlSf (h ▸ hkSf)
    have hk1 : c • X.vert (k - 1) ≠ X.vert (k - 1) := by
      intro h
      have hmem : k - 1 ∈ Sf := by
        simp [Sf]
        exact ⟨⟨by omega, by omega⟩, h⟩
      have := Finset.min'_le Sf (k - 1) hmem
      omega
    exact ⟨k, Or.inr ⟨hkfix, hk1⟩⟩


theorem torus_swap_contradiction (X : Setup Γ G) (h0 : 2 ≤ X.n 0) (h1 : 2 ≤ X.n 1)
    {k : ℤ} {c : G} (hck : c ∈ X.Gi k)
    (hcK : c ∈ Subgroup.centralizer (X.K : Set G))
    (hswap : c • X.vert (k - 1) = X.vert (k + 1) ∧
      c • X.vert (k + 1) = X.vert (k - 1)) : False := by
  classical
  have hn : 2 ≤ X.n k := X.two_le_n h0 h1 k
  haveI : Finite ↥(X.Gi k) := X.hyp.finite_stab (X.vert k)
  have hordpos : 0 < orderOf c := by
    rw [Subgroup.orderOf_coe (H := X.Gi k) (a := ⟨c, hck⟩)]
    exact orderOf_pos (⟨c, hck⟩ : X.Gi k)
  obtain ⟨s, m, hm_odd, hmul⟩ := Nat.exists_eq_two_pow_mul_odd hordpos.ne'
  let d : G := c ^ m
  have hc2a : c ^ 2 • X.vert (k - 1) = X.vert (k - 1) := by
    rw [pow_two, mul_smul, hswap.1, hswap.2]
  have hc2b : c ^ 2 • X.vert (k + 1) = X.vert (k + 1) := by
    rw [pow_two, mul_smul, hswap.2, hswap.1]
  have hc2pow_a : ∀ t : ℕ, (c ^ 2) ^ t • X.vert (k - 1) = X.vert (k - 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', mul_smul, ih, hc2a]
  have hc2pow_b : ∀ t : ℕ, (c ^ 2) ^ t • X.vert (k + 1) = X.vert (k + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', mul_smul, ih, hc2b]
  obtain ⟨t, ht⟩ := hm_odd
  have hda : d • X.vert (k - 1) = X.vert (k + 1) := by
    calc d • X.vert (k - 1) = c ^ m • X.vert (k - 1) := rfl
      _ = c ^ (2 * t + 1) • X.vert (k - 1) := by rw [ht]
      _ = ((c ^ 2) ^ t * c) • X.vert (k - 1) := by rw [pow_succ, pow_mul]
      _ = (c ^ 2) ^ t • (c • X.vert (k - 1)) := by rw [mul_smul]
      _ = (c ^ 2) ^ t • X.vert (k + 1) := by rw [hswap.1]
      _ = X.vert (k + 1) := hc2pow_b t
  have hdb : d • X.vert (k + 1) = X.vert (k - 1) := by
    calc d • X.vert (k + 1) = c ^ m • X.vert (k + 1) := rfl
      _ = c ^ (2 * t + 1) • X.vert (k + 1) := by rw [ht]
      _ = ((c ^ 2) ^ t * c) • X.vert (k + 1) := by rw [pow_succ, pow_mul]
      _ = (c ^ 2) ^ t • (c • X.vert (k + 1)) := by rw [mul_smul]
      _ = (c ^ 2) ^ t • X.vert (k - 1) := by rw [hswap.2]
      _ = X.vert (k - 1) := hc2pow_a t
  have hd2 : d ^ 2 ^ s = 1 := by
    rw [show d = c ^ m from rfl, ← pow_mul, mul_comm, ← hmul, pow_orderOf_eq_one]
  have hdGk : d ∈ X.Gi k := (X.Gi k).pow_mem hck m
  have hdK : d ∈ Subgroup.centralizer (X.K : Set G) :=
    (Subgroup.centralizer (X.K : Set G)).pow_mem hcK m
  have hdL : d ∈ X.L k := by
    have hz : IsPGroup 2 (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_two hd2
    have hzle : Subgroup.zpowers d ≤ X.Gi k := Subgroup.zpowers_le.mpr hdGk
    exact le_oTwoPrime_of_isPGroup hz hzle (Subgroup.mem_zpowers d)
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := X.exists_torusSylow k
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    apply X.torus_ne_bot k hn
    rw [show X.Ki k = X.K ⊓ X.L k from rfl, ← hKmap, hbot]
    simp
  let dN : X.L k := ⟨d, hdL⟩
  have hdcent : dN ∈ Subgroup.centralizer (K' : Set (X.L k)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzK : (z : G) ∈ X.K := by
      have hzmap : (z : G) ∈ K'.map (X.L k).subtype := Subgroup.mem_map_of_mem _ hz
      rw [hKmap] at hzmap
      exact hzmap.1
    apply Subtype.ext
    have hcomm : (z : G) * d = d * (z : G) :=
      Subgroup.mem_centralizer_iff.mp hdK (z : G) hzK
    simpa [dN] using hcomm
  have hcent := (X.hyp.isLocL2_oTwoPrime (X.vert k)).torus_centralizer X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert k)) (X.hyp.valency (X.vert k)).2
    (X.hyp.valency (X.vert k)).1 S K' hKS hsup hK'ne
  have hdKQ : dN ∈ K' ⊔ (X.Q k).subgroupOf (X.L k) := hcent hdcent
  have hQL : X.Q k ≤ X.L k :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi k))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi k))
  have hdKQ' : d ∈ (X.K ⊓ X.L k) ⊔ X.Q k := by
    have h := Subgroup.mem_map_of_mem (X.L k).subtype hdKQ
    rwa [Subgroup.map_sup, hKmap, Subgroup.map_subgroupOf_eq_of_le hQL] at h
  have hleft_adj : Γ.Adj (X.vert k) (X.vert (k - 1)) := by
    have h := X.adj (k - 1)
    rw [show k - 1 + 1 = k by omega] at h
    exact h.symm
  have hQleft : ∀ x ∈ X.Q k, x • X.vert (k - 1) = X.vert (k - 1) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert k)).Q_fixes_neighbors X.hyp.adj_smul
      (X.hyp.finite_stab (X.vert k)) (X.hyp.valency (X.vert k)).2
      (X.hyp.valency (X.vert k)).1 (X.vert (k - 1)) hleft_adj
  have hQright : ∀ x ∈ X.Q k, x • X.vert (k + 1) = X.vert (k + 1) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert k)).Q_fixes_neighbors X.hyp.adj_smul
      (X.hyp.finite_stab (X.vert k)) (X.hyp.valency (X.vert k)).2
      (X.hyp.valency (X.vert k)).1 (X.vert (k + 1)) (X.adj k)
  have hfixleft : d • X.vert (k - 1) = X.vert (k - 1) := by
    have hsub : (X.K ⊓ X.L k) ⊔ X.Q k ≤ MulAction.stabilizer G (X.vert (k - 1)) := by
      apply sup_le
      · intro x hx
        exact MulAction.mem_stabilizer_iff.mpr (X.K_fix x hx.1 (k - 1))
      · intro x hx
        exact MulAction.mem_stabilizer_iff.mpr (hQleft x hx)
    exact MulAction.mem_stabilizer_iff.mp (hsub hdKQ')
  have hfixright : d • X.vert (k + 1) = X.vert (k + 1) := by
    have hsub : (X.K ⊓ X.L k) ⊔ X.Q k ≤ MulAction.stabilizer G (X.vert (k + 1)) := by
      apply sup_le
      · intro x hx
        exact MulAction.mem_stabilizer_iff.mpr (X.K_fix x hx.1 (k + 1))
      · intro x hx
        exact MulAction.mem_stabilizer_iff.mpr (hQright x hx)
    exact MulAction.mem_stabilizer_iff.mp (hsub hdKQ')
  have hne : X.vert (k - 1) ≠ X.vert (k + 1) := by
    intro h
    have := X.vert_injective h
    omega
  exact hne (by rw [← hfixleft, hda])


theorem swap_of_perm_pair {c : G} {a b : V} (hne : a ≠ b)
    (ha : c • a = a ∨ c • a = b) (hb : c • b = a ∨ c • b = b) (hmove : c • b ≠ b) :
    c • a = b ∧ c • b = a := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exfalso
      have h : c • a = c • b := by rw [ha, hb]
      exact hne (MulAction.injective c h)
    · exact absurd hb hmove
  · rcases hb with hb | hb
    · exact ⟨ha, hb⟩
    · exfalso
      have h : c • a = c • b := by rw [ha, hb]
      exact hne (MulAction.injective c h)

theorem centralizer_K_le_GT (h0 : 2 ≤ X.n 0) (h1 : 2 ≤ X.n 1) (j : ℤ) :
    Subgroup.centralizer (X.K : Set G) ⊓ X.Gi j ≤ X.GT := by
  intro c hc
  by_contra hcT
  have hcj : c ∈ X.Gi j := hc.2
  have hcK : c ∈ Subgroup.centralizer (X.K : Set G) := hc.1
  have hcnormK : c ∈ Subgroup.normalizer (X.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      have h := Subgroup.mem_centralizer_iff.mp hcK x hx
      have heq : c⁻¹ * x * c = x := by
        calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [h]
          _ = x := by group
      rwa [heq]
    · intro hx
      have hconj : ∀ y ∈ X.K, c * y * c⁻¹ = y := by
        intro y hy
        have h := Subgroup.mem_centralizer_iff.mp hcK y hy
        calc c * y * c⁻¹ = (c * y) * c⁻¹ := rfl
          _ = (y * c) * c⁻¹ := by rw [← h]
          _ = y := by group
      have heq : x = c⁻¹ * x * c := by
        calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
          _ = c⁻¹ * x * c := by rw [hconj (c⁻¹ * x * c) hx]
      rwa [heq]
  obtain ⟨k, hk | hk⟩ := X.exists_adjacent_fix_move hcj hcT
  ·
    have hfixk : c • X.vert k = X.vert k := hk.1
    have hmove : c • X.vert (k + 1) ≠ X.vert (k + 1) := hk.2
    have hck : c ∈ X.Gi k := MulAction.mem_stabilizer_iff.mpr hfixk
    have hn : 2 ≤ X.n k := X.two_le_n h0 h1 k
    let K' : Subgroup G := X.Ki k
    have hK'ne : K' ≠ ⊥ := X.torus_ne_bot k hn
    have hK'left : K' ≤ MulAction.stabilizer G (X.vert (k - 1)) := fun z hz =>
      MulAction.mem_stabilizer_iff.mpr (X.K_fix z hz.1 (k - 1))
    have hK'right : K' ≤ MulAction.stabilizer G (X.vert (k + 1)) := fun z hz =>
      MulAction.mem_stabilizer_iff.mpr (X.K_fix z hz.1 (k + 1))
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK'ne
    have hzG : (z : G) ∈ K' := z.2
    have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hmem_iff : ∀ a : V, Γ.Adj (X.vert k) a →
        ((∀ y ∈ K', y • a = a) ↔ a = X.vert (k - 1) ∨ a = X.vert (k + 1)) := by
      intro a ha
      constructor
      · intro hfix
        exact (X.torus_fixed k hn hzG hz1G a ha).mp (hfix (z : G) hzG)
      · rintro (rfl | rfl)
        · exact hK'left
        · exact hK'right
    have hcK'norm : c ∈ Subgroup.normalizer (K' : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hLconj : conjSub c (X.L k) = X.L k :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (le_normalizer_oTwoPrime (X.Gi k) hck)
      have hKconj : conjSub c X.K = X.K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hcnormK
      change conjSub c (X.K ⊓ X.L k) = X.K ⊓ X.L k
      rw [conjSub_inf, hKconj, hLconj]
    have hperm_left : c • X.vert (k - 1) = X.vert (k - 1) ∨
        c • X.vert (k - 1) = X.vert (k + 1) := by
      have hfixed : ∀ y ∈ K', y • (c • X.vert (k - 1)) = c • X.vert (k - 1) := by
        intro y hy
        have hy' : c⁻¹ * y * c ∈ K' := (Subgroup.mem_normalizer_iff''.mp hcK'norm y).mp hy
        calc y • (c • X.vert (k - 1)) = (y * c) • X.vert (k - 1) := by rw [mul_smul]
          _ = (c * (c⁻¹ * y * c)) • X.vert (k - 1) := by congr 1; group
          _ = c • ((c⁻¹ * y * c) • X.vert (k - 1)) := by rw [mul_smul]
          _ = c • X.vert (k - 1) := by rw [hK'left hy']
      have hadj : Γ.Adj (X.vert k) (c • X.vert (k - 1)) := by
        rw [← hfixk]
        exact (X.hyp.adj_smul c (X.vert k) (X.vert (k - 1))).2
          (by simpa using (X.adj (k - 1)).symm)
      exact (hmem_iff (c • X.vert (k - 1)) hadj).mp hfixed
    have hperm_right : c • X.vert (k + 1) = X.vert (k - 1) ∨
        c • X.vert (k + 1) = X.vert (k + 1) := by
      have hfixed : ∀ y ∈ K', y • (c • X.vert (k + 1)) = c • X.vert (k + 1) := by
        intro y hy
        have hy' : c⁻¹ * y * c ∈ K' := (Subgroup.mem_normalizer_iff''.mp hcK'norm y).mp hy
        calc y • (c • X.vert (k + 1)) = (y * c) • X.vert (k + 1) := by rw [mul_smul]
          _ = (c * (c⁻¹ * y * c)) • X.vert (k + 1) := by congr 1; group
          _ = c • ((c⁻¹ * y * c) • X.vert (k + 1)) := by rw [mul_smul]
          _ = c • X.vert (k + 1) := by rw [hK'right hy']
      have hadj : Γ.Adj (X.vert k) (c • X.vert (k + 1)) := by
        rw [← hfixk]
        exact (X.hyp.adj_smul c (X.vert k) (X.vert (k + 1))).2 (X.adj k)
      exact (hmem_iff (c • X.vert (k + 1)) hadj).mp hfixed
    have hne : X.vert (k - 1) ≠ X.vert (k + 1) := by
      intro h
      have := X.vert_injective h
      omega
    obtain ⟨hswap1, hswap2⟩ := swap_of_perm_pair (c := c) hne
      hperm_left hperm_right hmove
    exact X.torus_swap_contradiction h0 h1 hck hcK ⟨hswap1, hswap2⟩
  ·
    have hfixk : c • X.vert k = X.vert k := hk.1
    have hmove : c • X.vert (k - 1) ≠ X.vert (k - 1) := hk.2
    have hck : c ∈ X.Gi k := MulAction.mem_stabilizer_iff.mpr hfixk
    have hn : 2 ≤ X.n k := X.two_le_n h0 h1 k
    let K' : Subgroup G := X.Ki k
    have hK'ne : K' ≠ ⊥ := X.torus_ne_bot k hn
    have hK'left : K' ≤ MulAction.stabilizer G (X.vert (k - 1)) := fun z hz =>
      MulAction.mem_stabilizer_iff.mpr (X.K_fix z hz.1 (k - 1))
    have hK'right : K' ≤ MulAction.stabilizer G (X.vert (k + 1)) := fun z hz =>
      MulAction.mem_stabilizer_iff.mpr (X.K_fix z hz.1 (k + 1))
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK'ne
    have hzG : (z : G) ∈ K' := z.2
    have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hmem_iff : ∀ a : V, Γ.Adj (X.vert k) a →
        ((∀ y ∈ K', y • a = a) ↔ a = X.vert (k - 1) ∨ a = X.vert (k + 1)) := by
      intro a ha
      constructor
      · intro hfix
        exact (X.torus_fixed k hn hzG hz1G a ha).mp (hfix (z : G) hzG)
      · rintro (rfl | rfl)
        · exact hK'left
        · exact hK'right
    have hcK'norm : c ∈ Subgroup.normalizer (K' : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hLconj : conjSub c (X.L k) = X.L k :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (le_normalizer_oTwoPrime (X.Gi k) hck)
      have hKconj : conjSub c X.K = X.K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hcnormK
      change conjSub c (X.K ⊓ X.L k) = X.K ⊓ X.L k
      rw [conjSub_inf, hKconj, hLconj]
    have hperm_left : c • X.vert (k - 1) = X.vert (k - 1) ∨
        c • X.vert (k - 1) = X.vert (k + 1) := by
      have hfixed : ∀ y ∈ K', y • (c • X.vert (k - 1)) = c • X.vert (k - 1) := by
        intro y hy
        have hy' : c⁻¹ * y * c ∈ K' := (Subgroup.mem_normalizer_iff''.mp hcK'norm y).mp hy
        calc y • (c • X.vert (k - 1)) = (y * c) • X.vert (k - 1) := by rw [mul_smul]
          _ = (c * (c⁻¹ * y * c)) • X.vert (k - 1) := by congr 1; group
          _ = c • ((c⁻¹ * y * c) • X.vert (k - 1)) := by rw [mul_smul]
          _ = c • X.vert (k - 1) := by rw [hK'left hy']
      have hadj : Γ.Adj (X.vert k) (c • X.vert (k - 1)) := by
        rw [← hfixk]
        exact (X.hyp.adj_smul c (X.vert k) (X.vert (k - 1))).2
          (by simpa using (X.adj (k - 1)).symm)
      exact (hmem_iff (c • X.vert (k - 1)) hadj).mp hfixed
    have hperm_right : c • X.vert (k + 1) = X.vert (k - 1) ∨
        c • X.vert (k + 1) = X.vert (k + 1) := by
      have hfixed : ∀ y ∈ K', y • (c • X.vert (k + 1)) = c • X.vert (k + 1) := by
        intro y hy
        have hy' : c⁻¹ * y * c ∈ K' := (Subgroup.mem_normalizer_iff''.mp hcK'norm y).mp hy
        calc y • (c • X.vert (k + 1)) = (y * c) • X.vert (k + 1) := by rw [mul_smul]
          _ = (c * (c⁻¹ * y * c)) • X.vert (k + 1) := by congr 1; group
          _ = c • ((c⁻¹ * y * c) • X.vert (k + 1)) := by rw [mul_smul]
          _ = c • X.vert (k + 1) := by rw [hK'right hy']
      have hadj : Γ.Adj (X.vert k) (c • X.vert (k + 1)) := by
        rw [← hfixk]
        exact (X.hyp.adj_smul c (X.vert k) (X.vert (k + 1))).2 (X.adj k)
      exact (hmem_iff (c • X.vert (k + 1)) hadj).mp hfixed
    have hne : X.vert (k - 1) ≠ X.vert (k + 1) := by
      intro h
      have := X.vert_injective h
      omega
    have hperm_right' : c • X.vert (k + 1) = X.vert (k + 1) ∨
        c • X.vert (k + 1) = X.vert (k - 1) := by
      rcases hperm_right with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hperm_left' : c • X.vert (k - 1) = X.vert (k + 1) ∨
        c • X.vert (k - 1) = X.vert (k - 1) := by
      rcases hperm_left with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨hswap1, hswap2⟩ := swap_of_perm_pair (c := c) (Ne.symm hne)
      hperm_right' hperm_left' hmove
    exact X.torus_swap_contradiction h0 h1 hck hcK ⟨hswap2, hswap1⟩


theorem edgeSylow_transitive (i : ℤ) :
    ∀ a b : V, Γ.Adj (X.vert (i + 1)) a → a ≠ X.vert i →
      Γ.Adj (X.vert (i + 1)) b → b ≠ X.vert i →
      ∃ s ∈ X.edgeSylow i, s • a = b := by
  classical
  let S := X.edgeSylow i
  let Q := X.Q (i + 1)
  haveI : Finite ↥S :=
    finite_of_le_stabilizer X.hyp (H := S) ((X.isSylowTwoOf_edgeSylow i).1.trans inf_le_right)
  haveI : Finite ↥Q := finite_of_le_stabilizer X.hyp (H := Q) (X.Q_le_Gi (i + 1))
  have hSle : S ≤ X.Gi (i + 1) := (X.isSylowTwoOf_edgeSylow i).1.trans inf_le_right
  have hSleGi : S ≤ X.Gi i := (X.isSylowTwoOf_edgeSylow i).1.trans inf_le_left
  have hQleS : Q ≤ S := by
    change Q ≤ pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1))
    rw [inf_comm, edgeSylow_eq_pCoreOf_edge X.hyp (X.adj i).symm
      (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.hyp.isLocL2_oTwoPrime (X.vert i)),
      edgeSylow_eq_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
        (X.adj i).symm]
    exact pCoreOf_le_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.vert i)
  have hQfix : ∀ a : V, Γ.Adj (X.vert (i + 1)) a → ∀ q ∈ Q, q • a = a :=
    (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))).Q_fixes_neighbors X.hyp.adj_smul
      (X.hyp.finite_stab (X.vert (i + 1))) (X.hyp.valency (X.vert (i + 1))).2
      (X.hyp.valency (X.vert (i + 1))).1
  have hS_eq' : S = vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.vert i) := by
    change pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)) = _
    rw [inf_comm]
    rw [edgeSylow_eq_pCoreOf_edge X.hyp (X.adj i).symm
      (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.hyp.isLocL2_oTwoPrime (X.vert i))]
    exact edgeSylow_eq_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
      (X.adj i).symm
  have hcard : Nat.card ↥S = Nat.card ↥Q * 2 ^ X.n (i + 1) := by
    have hrel := relIndex_pCoreOf_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
      (X.vert i)
    have h := Subgroup.relIndex_mul_card (H := X.Q (i + 1))
      (K := vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.vert i))
    rw [inf_eq_left.mpr (pCoreOf_le_vertexSylowMap X.hyp
      (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.vert i))] at h
    rw [hrel] at h
    calc Nat.card ↥S
        = Nat.card ↥(vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
            (X.vert i)) := by rw [hS_eq']
      _ = 2 ^ X.n (i + 1) * Nat.card ↥Q := h.symm
      _ = Nat.card ↥Q * 2 ^ X.n (i + 1) := mul_comm _ _
  intro a b ha hab hb hbb
  let Ω : Set V := {x : V | Γ.Adj (X.vert (i + 1)) x ∧ x ≠ X.vert i}
  have hΩcard : Ω.ncard = 2 ^ X.n (i + 1) := by
    have hset : Ω = Γ.neighborSet (X.vert (i + 1)) \ {X.vert i} := by
      ext x
      simp [Ω, SimpleGraph.mem_neighborSet]
    rw [hset, Set.ncard_sdiff_singleton_of_mem (by
      rw [SimpleGraph.mem_neighborSet]; exact (X.adj i).symm)]
    have h3 : (Γ.neighborSet (X.vert (i + 1))).ncard = 2 ^ X.n (i + 1) + 1 := by
      rw [← Nat.card_coe_set_eq, (X.hyp.valency (X.vert (i + 1))).2]
    rw [h3, Nat.add_sub_cancel]
  have hstab : ∀ x ∈ Ω, MulAction.stabilizer ↥S x = Q.subgroupOf S := by
    intro x hx
    ext s
    constructor
    · intro hs
      have hsfix : (s : G) • x = x := MulAction.mem_stabilizer_iff.mp hs
      have hfixi : (s : G) • X.vert i = X.vert i :=
        MulAction.mem_stabilizer_iff.mp (hSleGi s.2)
      obtain ⟨n, hn⟩ := (X.isPGroup_edgeSylow i) (s : ↥S)
      have hn' : (s : G) ^ 2 ^ n = 1 := by
        have := congrArg (fun z : ↥S => (z : G)) hn
        simpa using this
      have h2 : IsPGroup 2 (Subgroup.zpowers (s : G)) := isPGroup_zpowers_of_pow_two hn'
      have hzle : Subgroup.zpowers (s : G) ≤ X.Gi (i + 1) :=
        Subgroup.zpowers_le.mpr (hSle s.2)
      have hPleX : Subgroup.zpowers (s : G) ≤ MulAction.stabilizer G x :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hsfix)
      have hPleI : Subgroup.zpowers (s : G) ≤ MulAction.stabilizer G (X.vert i) :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hfixi)
      have hmem := le_pCoreOf_of_isPGroup_fixes_two X.hyp h2 hzle hx.1 (X.adj i).symm hx.2
        (fun y hy => MulAction.mem_stabilizer_iff.mp (hPleX hy))
        (fun y hy => MulAction.mem_stabilizer_iff.mp (hPleI hy))
      rw [Subgroup.mem_subgroupOf]
      exact hmem (Subgroup.mem_zpowers (s : G))
    · intro hs
      rw [Subgroup.mem_subgroupOf] at hs
      rw [MulAction.mem_stabilizer_iff]
      exact hQfix x hx.1 (s : G) hs
  have horbit : ∀ x ∈ Ω, (MulAction.orbit ↥S x : Set V) = Ω := by
    intro x hx
    haveI : Finite ↥(MulAction.orbit ↥S x) := by
      have hfin : (MulAction.orbit ↥S x : Set V).Finite := by
        simpa [MulAction.orbit] using Set.finite_range (fun s : ↥S => s • x)
      exact hfin.to_subtype
    letI : Fintype ↥S := Fintype.ofFinite _
    letI : Fintype ↥(MulAction.orbit ↥S x) := Fintype.ofFinite _
    letI : Fintype ↥(MulAction.stabilizer ↥S x) := Fintype.ofFinite _
    have hcard_orbit : Nat.card ↥(MulAction.orbit ↥S x) * Nat.card ↥(MulAction.stabilizer ↥S x) =
        Nat.card ↥S := by
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥S) x
      simpa only [Nat.card_eq_fintype_card] using h
    have hstabcard : Nat.card ↥(MulAction.stabilizer ↥S x) = Nat.card ↥Q := by
      rw [hstab x hx]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleS).toEquiv
    have horbcard : Nat.card ↥(MulAction.orbit ↥S x) = Ω.ncard := by
      have h := hcard_orbit
      rw [hstabcard, hcard, mul_comm (Nat.card ↥Q) (2 ^ X.n (i + 1))] at h
      have h2 : Nat.card ↥(MulAction.orbit ↥S x) = 2 ^ X.n (i + 1) :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos h
      rw [h2, hΩcard]
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ ?_
    · intro y hy
      rcases hy with ⟨s, rfl⟩
      refine ⟨?_, ?_⟩
      · have hs : (s : G) • X.vert (i + 1) = X.vert (i + 1) :=
          MulAction.mem_stabilizer_iff.mp (hSle s.2)
        rw [← hs]
        exact (X.hyp.adj_smul (s : G) (X.vert (i + 1)) x).2 hx.1
      · intro h
        apply hx.2
        have hs : (s : G) • X.vert i = X.vert i :=
          MulAction.mem_stabilizer_iff.mp (hSleGi s.2)
        have hsx : (s : G) • x = X.vert i := h
        calc x = (s : G)⁻¹ • ((s : G) • x) := by simp
          _ = (s : G)⁻¹ • X.vert i := congrArg (fun y => (s : G)⁻¹ • y) hsx
          _ = X.vert i := by
            rw [← hs, ← mul_smul, inv_mul_cancel, one_smul]
            exact hs.symm
    · have hΩ : (MulAction.orbit ↥S x).ncard = Ω.ncard := by
        rw [← Nat.card_coe_set_eq, horbcard]
      exact le_of_eq hΩ.symm
    · exact (X.hyp.finite_neighborSet (X.vert (i + 1))).subset (fun y hy => by
        simpa [SimpleGraph.mem_neighborSet] using hy.1)
  have haΩ : a ∈ Ω := ⟨ha, hab⟩
  have hbΩ : b ∈ Ω := ⟨hb, hbb⟩
  have hb_orbit : b ∈ MulAction.orbit ↥S a := by rw [horbit a haΩ]; exact hbΩ
  rcases hb_orbit with ⟨s, hs⟩
  exact ⟨s, s.2, hs⟩


theorem exists_torusSylow_right (i : ℤ) :
    ∃ (S : Sylow 2 (X.L (i + 1))) (K' : Subgroup (X.L (i + 1))),
      (S : Subgroup (X.L (i + 1))).map (X.L (i + 1)).subtype = X.edgeSylow i ∧
      K'.map (X.L (i + 1)).subtype = X.K ⊓ X.L (i + 1) ∧
      K' ⊓ (S : Subgroup (X.L (i + 1))) = ⊥ ∧
      K' ⊔ (S : Subgroup (X.L (i + 1))) =
        Subgroup.normalizer ((S : Subgroup (X.L (i + 1))) : Set (X.L (i + 1))) := by
  have hKle' : X.K ≤ X.Gi (i + 1) ⊓ X.Gi i :=
    le_inf (X.K_le_Gi (i + 1)) (X.K_le_Gi i)
  have hKinf' : X.K ⊓ pCoreOf 2 (X.Gi (i + 1) ⊓ X.Gi i) = ⊥ := by
    rw [inf_comm (X.Gi (i + 1)) (X.Gi i)]
    exact X.K_inf_edgeSylow i
  have hKsup' : X.K ⊔ pCoreOf 2 (X.Gi (i + 1) ⊓ X.Gi i) = X.Gi (i + 1) ⊓ X.Gi i := by
    rw [inf_comm (X.Gi (i + 1)) (X.Gi i)]
    exact X.K_sup_edgeSylow i
  simpa [Setup.edgeSylow, inf_comm] using
    exists_edgeTorusSylow X.hyp (X.adj i).symm hKle' hKinf' hKsup'


theorem exists_conj_mem_pCoreOf (i : ℤ) {x y : G} (hxS : x ∈ X.edgeSylow i)
    (hyS : y ∈ X.edgeSylow i) (hxQ : x ∉ X.Q (i + 1)) (hyQ : y ∉ X.Q (i + 1)) :
    ∃ k ∈ X.K ⊓ X.L (i + 1), k * x * k⁻¹ * y⁻¹ ∈ X.Q (i + 1) := by
  classical
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := X.exists_torusSylow_right i
  obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp (by rw [hSmap]; exact hxS)
  obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp (by rw [hSmap]; exact hyS)
  have hxQ' : (x' : G) ∉ X.Q (i + 1) := by
    intro h
    exact hxQ (by rw [show (x' : G) = x from hx'eq] at h; exact h)
  have hyQ' : (y' : G) ∉ X.Q (i + 1) := by
    intro h
    exact hyQ (by rw [show (y' : G) = y from hy'eq] at h; exact h)
  have hN : IsLocL2 Γ G (X.vert (i + 1)) (X.n (i + 1)) (X.L (i + 1)) :=
    X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))
  have htrans := hN.torus_transitive_on_sylow X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert (i + 1))) (X.hyp.valency (X.vert (i + 1))).2
    (X.hyp.valency (X.vert (i + 1))).1 S K' hKS hsup hx' hy' hxQ' hyQ'
  obtain ⟨k, hkQ⟩ := htrans
  refine ⟨(k : X.L (i + 1)), ?_, ?_⟩
  · have : ((k : X.L (i + 1)) : G) ∈ K'.map (X.L (i + 1)).subtype :=
      Subgroup.mem_map_of_mem _ k.2
    rwa [hKmap] at this
  · have hmem : (k * x' * k⁻¹ * (y')⁻¹) ∈
        (X.Q (i + 1)).subgroupOf (X.L (i + 1)) := hkQ
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    rw [show (x' : G) = x from hx'eq, show (y' : G) = y from hy'eq] at hmem
    exact hmem


theorem Q_le_edgeSylow (i : ℤ) : X.Q (i + 1) ≤ X.edgeSylow i := by
  obtain ⟨S, K', hSmap, -⟩ := X.exists_torusSylow_right i
  have hN : IsLocL2 Γ G (X.vert (i + 1)) (X.n (i + 1)) (X.L (i + 1)) :=
    X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))
  have hle := hN.pCoreOf_subgroupOf_le_sylow S
  intro q hq
  have hqL : q ∈ X.L (i + 1) :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (i + 1)))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi (i + 1))) hq
  have hq' : (⟨q, hqL⟩ : X.L (i + 1)) ∈ (X.Q (i + 1)).subgroupOf (X.L (i + 1)) := by
    rw [Subgroup.mem_subgroupOf]
    exact hq
  have hqS : (⟨q, hqL⟩ : X.L (i + 1)) ∈ S := hle hq'
  rw [← hSmap]
  exact Subgroup.mem_map_of_mem _ hqS

end Setup

end CFSG.Quasithin.St84
