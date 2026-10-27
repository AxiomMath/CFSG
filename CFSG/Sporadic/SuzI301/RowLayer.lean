module

public import CFSG.Sporadic.SuzI301.RowBasic

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271 CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301


private theorem Q1_le_suzM : Q1 ≤ suzM := fun _ hg =>
  (invE_le_centM (by norm_num) (Q_le_invE hg)).2

private theorem t1_mem_Q1 : suzInv 1 ∈ Q1 := coord_qVec.t_mem

private theorem t1_mem_suzM : suzInv 1 ∈ suzM := Q1_le_suzM t1_mem_Q1

private theorem commute_t1_of_mem_Q1 {q : Equiv.Perm (Fin 1782)} (hq : q ∈ Q1) :
    Commute q (suzInv 1) :=
  ((coord_qVec.forall_comm_iff t1_mem_Q1).2 (Subgroup.mem_zpowers _) q hq).symm

private theorem commute_dP_t1 : Commute dP (suzInv 1) :=
  Subgroup.mem_centralizer_singleton_iff.1 (invE_le_centM (by norm_num) gens_mem.1).1

private theorem mem_invE_of_commute {g : Equiv.Perm (Fin 1782)} (hgM : g ∈ suzM)
    (hg : Commute g (suzInv 1)) : g ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num)]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hg, hgM⟩

private theorem commute_t1_of_conj {g : Equiv.Perm (Fin 1782)} (h1 : g * suzInv 1 * g⁻¹ ∈ Q1)
    (h2 : ∀ q ∈ Q1, g⁻¹ * q * g ∈ Q1) : Commute g (suzInv 1) := by
  have hz : g * suzInv 1 * g⁻¹ ∈ Subgroup.zpowers (suzInv 1) := by
    refine (coord_qVec.forall_comm_iff h1).1 fun y hy => ?_
    have hc : g⁻¹ * y * g * suzInv 1 = suzInv 1 * (g⁻¹ * y * g) := commute_t1_of_mem_Q1 (h2 y hy)
    calc g * suzInv 1 * g⁻¹ * y = g * (suzInv 1 * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * suzInv 1) * g⁻¹ := by rw [hc]
      _ = y * (g * suzInv 1 * g⁻¹) := by group
  rcases CFSG.LocalAnalysis.GorensteinLyons.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two
    coord_qVec.orderOf_t hz with h | h
  · refine absurd ?_ (suzInv_ne_one (i := 1) (by norm_num))
    calc suzInv 1 = g⁻¹ * (g * suzInv 1 * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · show g * suzInv 1 = suzInv 1 * g
    calc g * suzInv 1 = g * suzInv 1 * g⁻¹ * g := by group
      _ = suzInv 1 * g := by rw [h]

private theorem commute_t1_of_mem_normalizer {g : ↥suzM}
    (hg : g ∈ Subgroup.normalizer ((Q1.subgroupOf suzM : Subgroup ↥suzM) : Set ↥suzM)) :
    Commute (g : Equiv.Perm (Fin 1782)) (suzInv 1) :=
  commute_t1_of_conj
    (Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 hg ⟨suzInv 1, t1_mem_suzM⟩).1
      (Subgroup.mem_subgroupOf.2 t1_mem_Q1)))
    fun q hq => Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff''.1 hg
      ⟨q, Q1_le_suzM hq⟩).1 (Subgroup.mem_subgroupOf.2 hq))

private theorem kappa_rho1_dP (d' : ↥(invE 1)) (hd : (d' : Equiv.Perm (Fin 1782)) = dP) :
    kappa (rho1 d') = tabP (mat64 (sD ())) := by
  obtain ⟨hD, -, -, -, hrep⟩ := conj_qVec_facts
  have hrepD : Rep 64 (mat64 (sD ())) (tabP (mat64 (sD ()))) := hrep _ List.mem_cons_self
  refine Equiv.ext fun v => Fin.ext ?_
  obtain ⟨hlt, a, ha, hconj⟩ := hD v v.2
  have h1 : rho1 d' (bitVec v) = bitVec (mat64 (sD ()))[(v : ℕ)]! := by
    change coord_qVec.rho invE_le d' (bitVec v) = _
    rw [← coord_qVec.psi_q v.2, coord_qVec.rho_psi invE_le d' (coord_qVec.q_mem v.2), hd, hconj,
      coord_qVec.psi_eq hlt ha]
  rw [kappa_apply, h1, bitEquiv_symm_bitVec hlt]
  exact hrepD v

private theorem kappa_rho1_mem_closure (c : ↥(invE 1)) :
    kappa (rho1 c) ∈ Subgroup.closure (Set.range fun j : Fin 10 => tabP matTabs[(j : ℕ)]!) := by
  set S₀ : Set (Equiv.Perm (Fin 1782)) := {g | g ∈ (invInnerChain 1).original.toList} with hS₀
  have htop : Subgroup.closure (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : rho1.range.map kappa ≤
      Subgroup.closure (Set.range fun j : Fin 10 => tabP matTabs[(j : ℕ)]!) := by
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_map, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk, hrep⟩ := gen_rep hg
    exact Subgroup.subset_closure ⟨⟨k, hk⟩,
      CFSG.RankThree.Native.permOfArr_eq_of_rep (tabRep_gen hk g hrep).2⟩
  exact hle ⟨rho1 c, ⟨c, rfl⟩, rfl⟩

private theorem pow_48_eq_one {h : Equiv.Perm (Fin 1782)} (hh : h ∈ invE 1)
    (hd : Commute h dP) : h ^ 48 = 1 := by
  have hcd : Commute (⟨h, hh⟩ : ↥(invE 1)) ⟨dP, gens_mem.1⟩ := Subtype.ext hd.eq
  have hk : Commute (kappa (rho1 ⟨h, hh⟩)) (tabP (mat64 (sD ()))) := by
    rw [← kappa_rho1_dP ⟨dP, gens_mem.1⟩ rfl]
    exact (hcd.map rho1).map kappa
  have h12 := omega_cent_facts _ (kappa_rho1_mem_closure _) hk
  have hker : (⟨h, hh⟩ : ↥(invE 1)) ^ 12 ∈ rho1.ker :=
    MonoidHom.mem_ker.2 (kappa_injective (by rw [map_pow, map_pow, h12, map_one]))
  rw [ker_rho1] at hker
  have hQ : h ^ 12 ∈ coord_qVec.Q := Subgroup.mem_subgroupOf.1 hker
  have h2 := orderOf_dvd_of_mem_zpowers (coord_qVec.sq_mem_zpowers hQ)
  rw [coord_qVec.orderOf_t] at h2
  rw [show (48 : ℕ) = 12 * 2 * 2 by norm_num, pow_mul, pow_mul]
  exact orderOf_dvd_iff_pow_eq_one.1 h2

private theorem card_eq_of_pow_48 {G : Type*} [Group G] [Finite G] (hG : ∀ g : G, g ^ 48 = 1) :
    Nat.card G = 2 ^ (Nat.card G).factorization 2 * 3 ^ (Nat.card G).factorization 3 := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hsupp : (Nat.card G).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    haveI := Fact.mk hpp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
    have h48 : p ∣ 2 ^ 4 * 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one (hG g)
    rcases (Nat.Prime.dvd_mul hpp).1 h48 with h | h
    · exact Finset.mem_insert.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
        (hpp.dvd_of_dvd_pow h)))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
        ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h)))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (by norm_num)]

private theorem isSolvable_of_pow_48 {G : Type*} [Group G] [Finite G]
    (hG : ∀ g : G, g ^ 48 = 1) : Group.IsSolvable G := by
  haveI := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [Fintype.card_eq_nat_card]; exact card_eq_of_pow_48 hG)

private theorem glaPLayer_eq_bot_of_isSolvable {X : Subgroup ↥suzM} [Group.IsSolvable X] :
    GLAPLayer 3 X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun J hJ g hg => ?_)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val
    (CFSG.HardMathSupport.Solomon.Coordinator.hom_eq_one_of_solvable Nat.prime_three hJ
      (MonoidHom.id X) g hg)

theorem isSolvable_of_commute {H : Subgroup ↥suzM}
    (hH : ∀ g ∈ H, Commute (g : Equiv.Perm (Fin 1782)) dP ∧
      Commute (g : Equiv.Perm (Fin 1782)) (suzInv 1)) : Group.IsSolvable H :=
  isSolvable_of_pow_48 fun g => by
    obtain ⟨hd, ht⟩ := hH g g.2
    have h := pow_48_eq_one (mem_invE_of_commute (g : ↥suzM).2 ht) hd
    apply Subtype.ext
    apply Subtype.ext
    simpa using h

private theorem glaPLayer_eq_bot_of_commute {H : Subgroup ↥suzM}
    (hH : ∀ g ∈ H, Commute (g : Equiv.Perm (Fin 1782)) dP ∧
      Commute (g : Equiv.Perm (Fin 1782)) (suzInv 1)) : GLAPLayer 3 H = ⊥ := by
  haveI : Group.IsSolvable H := isSolvable_of_commute hH
  exact glaPLayer_eq_bot_of_isSolvable

private theorem mem_R0_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ Q1 ⊓ Subgroup.centralizer {dP} ↔
      ∃ v < 64, ∃ a < 2, (mat64 (sD ()))[v]! = v ∧ g = qVec v * suzInv 1 ^ a := by
  constructor
  · rintro ⟨hgQ, hgd⟩
    obtain ⟨v, hv, a, ha, rfl⟩ := coord_qVec.mem_Q_iff.1 hgQ
    exact ⟨v, hv, a, ha, (r0_facts.1 v hv a ha).1
      (Subgroup.mem_centralizer_singleton_iff.1 hgd).symm, rfl⟩
  · rintro ⟨v, hv, a, ha, hfix, rfl⟩
    exact ⟨coord_qVec.mem_Q_iff.2 ⟨v, hv, a, ha, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ((r0_facts.1 v hv a ha).2 hfix).symm.eq⟩

private theorem rowR0Of_eq (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    rowR0Of x (Q1.subgroupOf suzM) = (Q1 ⊓ Subgroup.centralizer {dP}).subgroupOf suzM := by
  ext g
  constructor
  · rintro ⟨hgQ, hgx⟩
    refine Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hgQ,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hx]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hgx)
  · intro hg
    obtain ⟨hgQ, hgd⟩ := Subgroup.mem_subgroupOf.1 hg
    refine ⟨Subgroup.mem_subgroupOf.2 hgQ, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext ?_)⟩
    show (g : Equiv.Perm (Fin 1782)) * x = x * g
    rw [hx]
    exact Subgroup.mem_centralizer_singleton_iff.1 hgd

private def r0Equiv (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    ↥(rowR0Of x (Q1.subgroupOf suzM)) ≃* ↥(Q1 ⊓ Subgroup.centralizer {dP}) :=
  (MulEquiv.subgroupCongr (rowR0Of_eq x hx)).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans Q1_le_suzM))

private theorem card_R0 :
    Nat.card ↥(Q1 ⊓ Subgroup.centralizer {dP}) =
      ((Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v).card * 2 := by
  set F := (Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v with hF
  have hmemF : ∀ {v : ℕ}, v ∈ F ↔ v < 64 ∧ (mat64 (sD ()))[v]! = v := by
    intro v
    rw [hF, Finset.mem_filter, Finset.mem_range]
  let f : ↥(F ×ˢ Finset.range 2) → ↥(Q1 ⊓ Subgroup.centralizer {dP}) := fun p =>
    ⟨qVec p.1.1 * suzInv 1 ^ p.1.2, mem_R0_iff.2 ⟨p.1.1, (hmemF.1 (Finset.mem_product.1 p.2).1).1,
      p.1.2, Finset.mem_range.1 (Finset.mem_product.1 p.2).2,
      (hmemF.1 (Finset.mem_product.1 p.2).1).2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨v, a⟩, hva⟩ ⟨⟨w, b⟩, hwb⟩ h
      have h' : qVec v * suzInv 1 ^ a = qVec w * suzInv 1 ^ b := congrArg Subtype.val h
      obtain ⟨hv, ha⟩ := Finset.mem_product.1 hva
      obtain ⟨hw, hb⟩ := Finset.mem_product.1 hwb
      obtain ⟨rfl, rfl⟩ := coord_qVec.inj v (hmemF.1 hv).1 w (hmemF.1 hw).1 a
        (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) h'
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨v, hv, a, ha, hfix, rfl⟩ := mem_R0_iff.1 hg
      exact ⟨⟨(v, a), Finset.mem_product.2 ⟨hmemF.2 ⟨hv, hfix⟩, Finset.mem_range.2 ha⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_finsetCard, Finset.card_product,
    Finset.card_range]

private theorem exists_fixed
    (hF : ((Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v).card = 16) :
    ∃ v < 64, v ≠ 0 ∧ (mat64 (sD ()))[v]! = v := by
  by_contra hcon
  push Not at hcon
  have hsub : ((Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v) ⊆ {0} := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_range] at hv
    exact Finset.mem_singleton.2 (by_contra fun h0 => hcon v hv.1 h0 hv.2)
  have h := Finset.card_le_card hsub
  rw [hF, Finset.card_singleton] at h
  omega

private theorem isExtraspecial_R0 (h0 : ∃ v < 64, v ≠ 0 ∧ (mat64 (sD ()))[v]! = v) :
    IsExtraspecialPGroup 2 ↥(Q1 ⊓ Subgroup.centralizer {dP}) := by
  have hmem : ∀ {v : ℕ}, v < 64 → (mat64 (sD ()))[v]! = v →
      qVec v ∈ Q1 ⊓ Subgroup.centralizer {dP} :=
    fun hv hfix => mem_R0_iff.2 ⟨_, hv, 0, by norm_num, hfix, by rw [pow_zero, mul_one]⟩
  have hncomm : ∀ {v w : ℕ}, v < 64 → w < 64 → (gammaBit v w + gammaBit w v) % 2 = 1 →
      ∀ a : ℕ, qVec v * suzInv 1 ^ a * qVec w ≠ qVec w * (qVec v * suzInv 1 ^ a) := by
    intro v w hv hw hvw a h
    have e := coord_qVec.commutator_eq hv hw a 0
    rw [hvw, pow_one, pow_zero, mul_one, h] at e
    exact coord_qVec.t_ne (e.symm.trans (by group))
  refine (CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall
    (coord_qVec.isPGroup_Q.to_le inf_le_left)
    ⟨t1_mem_Q1, Subgroup.mem_centralizer_singleton_iff.2 commute_dP_t1.symm.eq⟩
    coord_qVec.orderOf_t ?_ ?_ ?_ ?_).1
  · intro g hg
    refine ⟨fun hc => ?_, fun hz y hy => (coord_qVec.forall_comm_iff hg.1).2 hz y hy.1⟩
    obtain ⟨v, hv, a, ha, hfix, rfl⟩ := mem_R0_iff.1 hg
    by_cases hv0 : v = 0
    · subst hv0
      rw [coord_qVec.q_zero, one_mul]
      exact pow_mem (Subgroup.mem_zpowers _) a
    · obtain ⟨w, hw, hwfix, hvw⟩ := r0_facts.2 v hv hv0 hfix
      exact absurd (hc _ (hmem hw hwfix)) (hncomm hv hw hvw a)
  · intro g hg y hy
    exact coord_qVec.commutator_mem_zpowers hg.1 hy.1
  · intro g hg
    exact coord_qVec.sq_mem_zpowers hg.1
  · obtain ⟨v, hv, hv0, hfix⟩ := h0
    obtain ⟨w, hw, hwfix, hvw⟩ := r0_facts.2 v hv hv0 hfix
    refine ⟨qVec v, hmem hv hfix, qVec w, hmem hw hwfix, ?_⟩
    have := hncomm hv hw hvw 0
    rwa [pow_zero, mul_one] at this

theorem row_K (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    rowKOf Row.suz.prime x (Q1.subgroupOf suzM) = ⊥ := by
  refine glaPLayer_eq_bot_of_commute fun g hg => ⟨?_, ?_⟩
  · have hgx := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le Row.suz.prime
      (Subgroup.centralizer ({x} : Set ↥suzM)) (Subgroup.mem_inf.1 hg).1
    rw [← hx]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hgx)
  · exact commute_t1_of_mem_normalizer (Subgroup.mem_inf.1 hg).2

theorem row_hK (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    RowK .suz Row.suz.prime (rowKOf Row.suz.prime x (Q1.subgroupOf suzM)) :=
  row_K x hx

theorem row_hR0 (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    Nat.card (rowR0Of x (Q1.subgroupOf suzM)) = 2 ^ Row.suz.r0exp := by
  rw [Nat.card_congr (r0Equiv x hx).toEquiv, card_R0, r0_card]
  rfl

theorem row_hR0t (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    IsExtraSpec2 (rowR0Of x (Q1.subgroupOf suzM)) := by
  obtain ⟨h2, hc, hf, hz⟩ := CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv
    (r0Equiv x hx).symm (isExtraspecial_R0 (exists_fixed r0_card))
  exact ⟨h2, hc.trans hf.symm, hf, hz⟩

theorem row_hK6 (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    rowKOf Row.suz.prime x (Q1.subgroupOf suzM) =
      GLAPLayer Row.suz.prime (Subgroup.centralizer ({x} : Set ↥suzM) ⊓
        Subgroup.centralizer (centerOf (rowR0Of x (Q1.subgroupOf suzM)) : Set ↥suzM)) := by
  have htR : (⟨suzInv 1, t1_mem_suzM⟩ : ↥suzM) ∈ rowR0Of x (Q1.subgroupOf suzM) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 t1_mem_Q1,
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
    show suzInv 1 * (x : Equiv.Perm (Fin 1782)) = x * suzInv 1
    rw [hx]
    exact commute_dP_t1.eq.symm
  have htc : (⟨suzInv 1, t1_mem_suzM⟩ : ↥suzM) ∈
      centerOf (rowR0Of x (Q1.subgroupOf suzM)) := by
    refine Subgroup.mem_map.2 ⟨⟨_, htR⟩, Subgroup.mem_center_iff.2 fun h =>
      Subtype.ext (Subtype.ext ?_), rfl⟩
    exact (commute_t1_of_mem_Q1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 h.2).1)).eq
  rw [row_K x hx]
  refine (glaPLayer_eq_bot_of_commute fun g hg => ⟨?_, ?_⟩).symm
  · rw [← hx]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1)
  · exact (congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 _ htc)).symm

private theorem t1_mem_centerOf_R0 (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    (⟨suzInv 1, t1_mem_suzM⟩ : ↥suzM) ∈ centerOf (rowR0Of x (Q1.subgroupOf suzM)) := by
  have htR : (⟨suzInv 1, t1_mem_suzM⟩ : ↥suzM) ∈ rowR0Of x (Q1.subgroupOf suzM) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 t1_mem_Q1,
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
    show suzInv 1 * (x : Equiv.Perm (Fin 1782)) = x * suzInv 1
    rw [hx]
    exact commute_dP_t1.eq.symm
  refine Subgroup.mem_map.2 ⟨⟨_, htR⟩, Subgroup.mem_center_iff.2 fun h =>
    Subtype.ext (Subtype.ext ?_), rfl⟩
  exact (commute_t1_of_mem_Q1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 h.2).1)).eq

theorem row_solvN (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set ↥suzM) ⊓
      Subgroup.normalizer ((Q1.subgroupOf suzM : Subgroup ↥suzM) : Set ↥suzM)) :=
  isSolvable_of_commute fun g hg => ⟨by
      rw [← hx]
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1),
    commute_t1_of_mem_normalizer (Subgroup.mem_inf.1 hg).2⟩

theorem row_solvZ (x : ↥suzM) (hx : (x : Equiv.Perm (Fin 1782)) = dP) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set ↥suzM) ⊓
      Subgroup.centralizer (centerOf (rowR0Of x (Q1.subgroupOf suzM)) : Set ↥suzM)) :=
  isSolvable_of_commute fun g hg => ⟨by
      rw [← hx]
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1),
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 _
      (t1_mem_centerOf_R0 x hx))).symm⟩

end CFSG.Sporadic.SuzI301
