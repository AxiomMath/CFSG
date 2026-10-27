module

public import CFSG.LocalAnalysis.StandardType.PhanELocalReal
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_eq_zero_of_smul_add_smul {u v : Fin 4 → K}
    (huv : finrank K ↥(Submodule.span K {u, v}) = 2) {a b : K}
    (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have h1 : a • u = b • v := CharTwo.add_eq_zero.mp h
  have hle_v (ha : a ≠ 0) :
      Submodule.span K ({u, v} : Set (Fin 4 → K)) ≤ Submodule.span K {v} := by
    have hu_mem : u ∈ Submodule.span K {v} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨a⁻¹ * b, ?_⟩
      calc (a⁻¹ * b) • v = a⁻¹ • (b • v) := smul_assoc a⁻¹ b v
        _ = a⁻¹ • (a • u) := by rw [← h1]
        _ = (a⁻¹ * a) • u := (smul_assoc a⁻¹ a u).symm
        _ = u := by rw [inv_mul_cancel₀ ha, one_smul]
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxu | hxv
    · rw [hxu]; exact hu_mem
    · rw [hxv]; exact Submodule.mem_span_singleton_self v
  have hle_u (hb : b ≠ 0) :
      Submodule.span K ({u, v} : Set (Fin 4 → K)) ≤ Submodule.span K {u} := by
    have hv_mem : v ∈ Submodule.span K {u} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨b⁻¹ * a, ?_⟩
      calc (b⁻¹ * a) • u = b⁻¹ • (a • u) := smul_assoc b⁻¹ a u
        _ = b⁻¹ • (b • v) := by rw [h1]
        _ = (b⁻¹ * b) • v := (smul_assoc b⁻¹ b v).symm
        _ = v := by rw [inv_mul_cancel₀ hb, one_smul]
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxu | hxv
    · rw [hxu]; exact Submodule.mem_span_singleton_self u
    · rw [hxv]; exact hv_mem
  constructor
  · by_contra ha
    have hfin : finrank K ↥(Submodule.span K ({u, v} : Set (Fin 4 → K))) ≤ 1 :=
      le_trans (Submodule.finrank_mono (hle_v ha)) (finrank_span_singleton_le_one v)
    omega
  · by_contra hb
    have hfin : finrank K ↥(Submodule.span K ({u, v} : Set (Fin 4 → K))) ≤ 1 :=
      le_trans (Submodule.finrank_mono (hle_u hb)) (finrank_span_singleton_le_one u)
    omega
private theorem plh_inf_span_pair_eq_bot {u v : Fin 4 → K}
    {S : Submodule K (Fin 4 → K)} (huS : u ∉ S) (hvS : v ∉ S ⊔ Submodule.span K {u}) :
    S ⊓ Submodule.span K ({u, v} : Set (Fin 4 → K)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxspan⟩ := hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxspan
  have hb0 : b = 0 := by
    by_contra hb
    apply hvS
    have hvu : v = b⁻¹ • x - (b⁻¹ * a) • u := by
      rw [← hab, smul_add, ← smul_assoc, ← smul_assoc]
      simp only [smul_eq_mul]
      rw [inv_mul_cancel₀ hb, one_smul]
      abel
    rw [hvu]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_left hxS))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)))
  rw [hb0, zero_smul, add_zero] at hab
  have ha0 : a = 0 := by
    by_contra ha
    apply huS
    rw [show u = a⁻¹ • x by rw [← hab, smul_smul, inv_mul_cancel₀ ha, one_smul]]
    exact S.smul_mem _ hxS
  rw [ha0, zero_smul] at hab
  exact hab.symm

private theorem plh_finrank_sup_span_eq_three {u : Fin 4 → K} (hu0 : u ≠ 0)
    {S : Submodule K (Fin 4 → K)} (hS : finrank K S = 2) (huS : u ∉ S) :
    finrank K ↥(S ⊔ Submodule.span K {u}) = 3 := by
  have hdisj : S ⊓ Submodule.span K {u} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxKu⟩ := hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxKu
    rw [← ha] at hxS
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul] at ha
      exact ha.symm
    · exfalso
      exact huS (by
        rw [show u = a⁻¹ • (a • u) by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]]
        exact S.smul_mem _ hxS)
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span K {u})
  rw [hdisj, finrank_bot, add_zero, hS, finrank_span_singleton hu0] at hfr
  omega
private theorem plh_finrank_inf_sgS_sup_le_two (hK : Nat.card K = (2 ^ f) ^ 2)
    {u : Fin 4 → K} (hu0 : u ≠ 0) (hu_real : sgv K f 4 u = u)
    {L : Submodule K (Fin 4 → K)} (hL2 : finrank K L = 2)
    (hLdisj : L ⊓ sgS K f 4 L = ⊥) (huL : u ∉ L) :
    finrank K ↥((L ⊔ Submodule.span K {u}) ⊓
      sgS K f 4 (L ⊔ Submodule.span K {u})) ≤ 2 := by
  have hsup3 : finrank K ↥(L ⊔ Submodule.span K {u}) = 3 :=
    plh_finrank_sup_span_eq_three hu0 hL2 huL
  by_contra hle
  have hge : 3 ≤ finrank K ↥((L ⊔ Submodule.span K {u}) ⊓
      sgS K f 4 (L ⊔ Submodule.span K {u})) := by omega
  have hinf_eq : finrank K ↥((L ⊔ Submodule.span K {u}) ⊓
      sgS K f 4 (L ⊔ Submodule.span K {u})) = 3 := by
    have hmono := Submodule.finrank_mono
      (inf_le_left : (L ⊔ Submodule.span K {u}) ⊓ sgS K f 4 (L ⊔ Submodule.span K {u}) ≤
        L ⊔ Submodule.span K {u})
    rw [hsup3] at hmono
    omega
  have hsup_le_sgS : L ⊔ Submodule.span K {u} ≤ sgS K f 4 (L ⊔ Submodule.span K {u}) := by
    have heq : (L ⊔ Submodule.span K {u}) ⊓ sgS K f 4 (L ⊔ Submodule.span K {u}) =
        L ⊔ Submodule.span K {u} :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hinf_eq, hsup3])
    calc L ⊔ Submodule.span K {u}
        = (L ⊔ Submodule.span K {u}) ⊓ sgS K f 4 (L ⊔ Submodule.span K {u}) := heq.symm
      _ ≤ sgS K f 4 (L ⊔ Submodule.span K {u}) := inf_le_right
  have hLsup_le : L ⊔ sgS K f 4 L ≤ sgS K f 4 (L ⊔ Submodule.span K {u}) :=
    sup_le (le_trans le_sup_left hsup_le_sgS) (sgS_mono le_sup_left)
  have hfr_LsL : finrank K ↥(L ⊔ sgS K f 4 L) = 4 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hLdisj), hL2, finrank_sgS hK L, hL2]
  have hfr_sgS : finrank K ↥(sgS K f 4 (L ⊔ Submodule.span K {u})) = 3 := by
    rw [finrank_sgS hK, hsup3]
  have hmono := Submodule.finrank_mono hLsup_le
  rw [hfr_LsL, hfr_sgS] at hmono
  omega
private noncomputable def plh_realVecs (T : Submodule K (Fin 4 → K)) :
    Finset (Fin 4 → K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact (Finset.univ : Finset (Fin 4 → K)).filter fun v => sgv K f 4 v = v ∧ v ∈ T
private theorem plh_realVecs_mem (T : Submodule K (Fin 4 → K)) (v : Fin 4 → K) :
    v ∈ plh_realVecs (K := K) (f := f) T ↔ sgv K f 4 v = v ∧ v ∈ T := by
  classical
  simp [plh_realVecs, Finset.mem_filter]
private theorem plh_realVecs_card (hK : Nat.card K = (2 ^ f) ^ 2)
    (T : Submodule K (Fin 4 → K)) (hT : sgS K f 4 T = T) :
    (plh_realVecs (K := K) (f := f) T).card = (2 ^ f) ^ finrank K T := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h1 : (plh_realVecs (K := K) (f := f) T).card =
      Nat.card {v : Fin 4 → K // sgv K f 4 v = v ∧ v ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    rw [plh_realVecs_mem (K := K) (f := f) T v, Finset.mem_filter]
    simp
  rw [h1]
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun v : Fin 4 → K => and_comm))).trans
    (card_real_eq (K := K) f hK T hT)
private theorem plh_realVecs_card_le (hK : Nat.card K = (2 ^ f) ^ 2)
    (T : Submodule K (Fin 4 → K)) :
    (plh_realVecs (K := K) (f := f) T).card ≤
      (2 ^ f) ^ finrank K ↥(T ⊓ sgS K f 4 T) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h1 : (plh_realVecs (K := K) (f := f) T).card =
      Nat.card {v : Fin 4 → K // sgv K f 4 v = v ∧ v ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    rw [plh_realVecs_mem (K := K) (f := f) T v, Finset.mem_filter]
    simp
  rw [h1]
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun v : Fin 4 → K => and_comm))).trans_le
    (card_real_le (K := K) f hK T)
theorem exists_real_plane (hK : Nat.card K = (2 ^ f) ^ 2)
    (Rs Ls : Finset (Submodule K (Fin 4 → K)))
    (hR : ∀ R ∈ Rs, finrank K R = 2 ∧ sgS K f 4 R = R)
    (hL : ∀ L ∈ Ls, finrank K L = 2 ∧ L ⊓ sgS K f 4 L = ⊥)
    (hcountA : Rs.card * (2 ^ f) ^ 2 + 1 < (2 ^ f) ^ 4)
    (hcountB : Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) + Ls.card * (2 ^ f) ^ 2 + 2 ^ f < (2 ^ f) ^ 4) :
    ∃ u v : Fin 4 → K, sgv K f 4 u = u ∧ sgv K f 4 v = v ∧
      finrank K ↥(Submodule.span K {u, v}) = 2 ∧
      (∀ R ∈ Rs, R ⊓ Submodule.span K {u, v} = ⊥) ∧
      (∀ L ∈ Ls, L ⊓ Submodule.span K {u, v} = ⊥) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set Rl : Finset (Fin 4 → K) := plh_realVecs (K := K) (f := f) ⊤ with hRl
  have hRl_card : Rl.card = (2 ^ f) ^ 4 := by
    rw [hRl, plh_realVecs_card (K := K) (f := f) hK ⊤ sgS_top, finrank_top,
      Module.finrank_fin_fun]
  have hmem_Rl : ∀ v : Fin 4 → K, v ∈ Rl ↔ sgv K f 4 v = v := by
    intro v
    rw [hRl, plh_realVecs_mem (K := K) (f := f) ⊤ v]
    simp
  set BadA : Finset (Fin 4 → K) :=
    Rs.biUnion (fun R => plh_realVecs (K := K) (f := f) R) ∪ {0} with hBadA
  have hBadA_le : BadA.card ≤ Rs.card * (2 ^ f) ^ 2 + 1 := by
    rw [hBadA]
    have h1 : (Rs.biUnion (fun R => plh_realVecs (K := K) (f := f) R)).card
        ≤ Rs.card * (2 ^ f) ^ 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro R hRmem
      rw [plh_realVecs_card (K := K) (f := f) hK R (hR R hRmem).2, (hR R hRmem).1]
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_singleton]
    exact Nat.add_le_add_right h1 1
  have hltA : BadA.card < Rl.card := by
    rw [hRl_card]
    exact lt_of_le_of_lt hBadA_le hcountA
  obtain ⟨u, huRl, huBadA⟩ := Finset.exists_mem_notMem_of_card_lt_card hltA
  have hu_real : sgv K f 4 u = u := (hmem_Rl u).mp huRl
  have hu0 : u ≠ 0 := by
    intro h0
    apply huBadA
    rw [hBadA]
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h0)
  have hu_notin_R : ∀ R ∈ Rs, u ∉ R := by
    intro R hRmem huR
    apply huBadA
    rw [hBadA]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨R, hRmem, (plh_realVecs_mem (K := K) (f := f) R u).mpr ⟨hu_real, huR⟩⟩)
  set Ku : Submodule K (Fin 4 → K) := Submodule.span K {u} with hKu
  have hKu_stab : sgS K f 4 Ku = Ku := by
    rw [hKu, sgS_span_singleton hK, hu_real]
  have hKu_dim : finrank K Ku = 1 := by rw [hKu, finrank_span_singleton hu0]
  set A1 : Finset (Fin 4 → K) := plh_realVecs (K := K) (f := f) Ku with hA1
  have hA1_card : A1.card = 2 ^ f := by
    rw [hA1, plh_realVecs_card (K := K) (f := f) hK Ku hKu_stab, hKu_dim, pow_one]
  have hRsup_stab : ∀ R ∈ Rs, sgS K f 4 (R ⊔ Ku) = R ⊔ Ku := by
    intro R hRmem
    rw [sgS_sup hK, (hR R hRmem).2, hKu_stab]
  have hRsup_dim : ∀ R ∈ Rs, finrank K ↥(R ⊔ Ku) = 3 := by
    intro R hRmem
    rw [hKu]
    exact plh_finrank_sup_span_eq_three hu0 (hR R hRmem).1 (hu_notin_R R hRmem)
  have hu_notin_L : ∀ L ∈ Ls, u ∉ L := by
    intro L hLmem huL
    have hu_sgSL : u ∈ sgS K f 4 L := by
      rw [mem_sgS, hu_real]
      exact huL
    have hmem : u ∈ L ⊓ sgS K f 4 L := ⟨huL, hu_sgSL⟩
    rw [(hL L hLmem).2] at hmem
    exact hu0 ((Submodule.mem_bot K).mp hmem)
  have hLsup_dim : ∀ L ∈ Ls, finrank K ↥(L ⊔ Ku) = 3 := by
    intro L hLmem
    rw [hKu]
    exact plh_finrank_sup_span_eq_three hu0 (hL L hLmem).1 (hu_notin_L L hLmem)
  have hLsup_inf_dim : ∀ L ∈ Ls,
      finrank K ↥((L ⊔ Ku) ⊓ sgS K f 4 (L ⊔ Ku)) ≤ 2 := by
    intro L hLmem
    rw [hKu]
    exact plh_finrank_inf_sgS_sup_le_two (f := f) hK hu0 hu_real (hL L hLmem).1
      (hL L hLmem).2 (hu_notin_L L hLmem)
  set A2 : Finset (Fin 4 → K) :=
    Rs.biUnion (fun R => plh_realVecs (K := K) (f := f) (R ⊔ Ku) \ A1) with hA2
  set A3 : Finset (Fin 4 → K) :=
    Ls.biUnion (fun L => plh_realVecs (K := K) (f := f) (L ⊔ Ku)) with hA3
  set BadB : Finset (Fin 4 → K) := (A1 ∪ A2) ∪ A3 with hBadB
  have hA2_le : A2.card ≤ Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) := by
    rw [hA2]
    apply Finset.card_biUnion_le_card_mul
    intro R hRmem
    have hsub : A1 ⊆ plh_realVecs (K := K) (f := f) (R ⊔ Ku) := by
      rw [hA1]
      intro x hx
      rw [plh_realVecs_mem] at hx ⊢
      exact ⟨hx.1, Submodule.mem_sup_right hx.2⟩
    have hcard2 : (plh_realVecs (K := K) (f := f) (R ⊔ Ku)).card = (2 ^ f) ^ 3 := by
      rw [plh_realVecs_card (K := K) (f := f) hK (R ⊔ Ku) (hRsup_stab R hRmem),
        hRsup_dim R hRmem]
    calc (plh_realVecs (K := K) (f := f) (R ⊔ Ku) \ A1).card
        = (2 ^ f) ^ 3 - 2 ^ f := by
          rw [Finset.card_sdiff_of_subset hsub, hcard2, hA1_card]
      _ ≤ (2 ^ f) ^ 3 - 2 ^ f := le_refl _
  have hA3_le : A3.card ≤ Ls.card * (2 ^ f) ^ 2 := by
    rw [hA3]
    apply Finset.card_biUnion_le_card_mul
    intro L hLmem
    exact le_trans (plh_realVecs_card_le (K := K) (f := f) hK (L ⊔ Ku))
      (pow_le_pow_right' (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) (hLsup_inf_dim L hLmem))
  have hBadB_le : BadB.card ≤ Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) +
      Ls.card * (2 ^ f) ^ 2 + 2 ^ f := by
    rw [hBadB]
    have h2 : ((A1 ∪ A2) ∪ A3).card ≤ (A1 ∪ A2).card + A3.card := Finset.card_union_le _ _
    have h1 : (A1 ∪ A2).card ≤ A1.card + A2.card := Finset.card_union_le _ _
    have hA1_le : A1.card ≤ 2 ^ f := le_of_eq hA1_card
    omega
  have hltB : BadB.card < Rl.card := by
    rw [hRl_card]
    exact lt_of_le_of_lt hBadB_le hcountB
  obtain ⟨v, hvRl, hvBadB⟩ := Finset.exists_mem_notMem_of_card_lt_card hltB
  have hv_real : sgv K f 4 v = v := (hmem_Rl v).mp hvRl
  have hA1_sub : A1 ⊆ BadB := by
    rw [hBadB]
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hA2_sub : A2 ⊆ BadB := by
    rw [hBadB]
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hA3_sub : A3 ⊆ BadB := by
    rw [hBadB]
    intro x hx
    exact Finset.mem_union_right _ hx
  have hv_notin_Ku : v ∉ Ku := by
    intro hv
    refine hvBadB (hA1_sub ?_)
    rw [hA1, plh_realVecs_mem]
    exact ⟨hv_real, hv⟩
  have hv_notin_Rsup : ∀ R ∈ Rs, v ∉ R ⊔ Ku := by
    intro R hRmem hvR
    refine hvBadB (hA2_sub ?_)
    rw [hA2]
    apply Finset.mem_biUnion.mpr
    refine ⟨R, hRmem, ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [plh_realVecs_mem]
      exact ⟨hv_real, hvR⟩
    · intro hvA1
      apply hv_notin_Ku
      rw [hA1, plh_realVecs_mem] at hvA1
      exact hvA1.2
  have hv_notin_Lsup : ∀ L ∈ Ls, v ∉ L ⊔ Ku := by
    intro L hLmem hvL
    refine hvBadB (hA3_sub ?_)
    rw [hA3]
    apply Finset.mem_biUnion.mpr
    exact ⟨L, hLmem,
      (plh_realVecs_mem (K := K) (f := f) (L ⊔ Ku) v).mpr ⟨hv_real, hvL⟩⟩
  have hv0 : v ≠ 0 := by
    intro hvz
    exact hv_notin_Ku (by rw [hvz]; exact Submodule.zero_mem Ku)
  have hspan_eq : Submodule.span K ({u, v} : Set (Fin 4 → K)) =
      Submodule.span K {u} ⊔ Submodule.span K {v} := by
    rw [show ({u, v} : Set (Fin 4 → K)) = {u} ∪ {v} by ext x; simp [or_comm],
      Submodule.span_union]
  have hne : Submodule.span K {u} ≠ Submodule.span K {v} := by
    intro heq
    apply hv_notin_Ku
    rw [hKu]
    exact heq.symm ▸ Submodule.mem_span_singleton_self v
  have huv2 : finrank K ↥(Submodule.span K {u, v}) = 2 := by
    have hdisj : Disjoint (Submodule.span K {u}) (Submodule.span K {v}) :=
      disjoint_iff.mpr (inf_eq_bot_of_ne_pts (finrank_span_singleton hu0)
        (finrank_span_singleton hv0) hne)
    rw [hspan_eq, finrank_sup_of_disjoint hdisj, finrank_span_singleton hu0,
      finrank_span_singleton hv0]
  refine ⟨u, v, hu_real, hv_real, huv2, ?_, ?_⟩
  · intro R hRmem
    exact plh_inf_span_pair_eq_bot (hu_notin_R R hRmem)
      (by simpa [hKu] using hv_notin_Rsup R hRmem)
  · intro L hLmem
    exact plh_inf_span_pair_eq_bot (hu_notin_L L hLmem)
      (by simpa [hKu] using hv_notin_Lsup L hLmem)
theorem realPlane_point (hK : Nat.card K = (2 ^ f) ^ 2) {u v : Fin 4 → K}
    (hu : sgv K f 4 u = u) (hv : sgv K f 4 v = v)
    (huv : finrank K ↥(Submodule.span K {u, v}) = 2) {lam : K} (hlam : sg K f lam ≠ lam) :
    finrank K ↥(Submodule.span K {u + lam • v}) = 1 ∧
      sgS K f 4 (Submodule.span K {u + lam • v}) ≠ Submodule.span K {u + lam • v} ∧
      Submodule.span K {u + lam • v} ⊔ sgS K f 4 (Submodule.span K {u + lam • v}) =
        Submodule.span K {u, v} := by
  have hsgw : sgv K f 4 (u + lam • v) = u + (sg K f lam) • v := by
    rw [map_add, map_smulₛₗ, hu, hv]
    rfl
  have hw_ne : u + lam • v ≠ 0 := by
    intro hzero
    have hu_mem : u ∈ Submodule.span K {v} := by
      rw [Submodule.mem_span_singleton]
      exact ⟨lam, (CharTwo.add_eq_zero.mp hzero).symm⟩
    have hle : Submodule.span K ({u, v} : Set (Fin 4 → K)) ≤ Submodule.span K {v} := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxu | hxv
      · rw [hxu]; exact hu_mem
      · rw [hxv]; exact Submodule.mem_span_singleton_self v
    have hfin : finrank K ↥(Submodule.span K ({u, v} : Set (Fin 4 → K))) ≤ 1 :=
      le_trans (Submodule.finrank_mono hle) (finrank_span_singleton_le_one v)
    omega
  have hw'_ne : u + (sg K f lam) • v ≠ 0 := by
    have h' : sgv K f 4 (u + (sg K f lam) • v) = u + lam • v := by
      rw [← hsgw, sgv_sgv hK]
    intro hz
    rw [hz, map_zero] at h'
    exact hw_ne h'.symm
  have hne : sgS K f 4 (Submodule.span K {u + lam • v}) ≠
      Submodule.span K {u + lam • v} := by
    rw [sgS_span_singleton hK, hsgw]
    intro heq
    have hmem : u + (sg K f lam) • v ∈ Submodule.span K {u + lam • v} :=
      heq ▸ Submodule.mem_span_singleton_self (u + (sg K f lam) • v)
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h : c • u + (c * lam) • v = u + (sg K f lam) • v := by
      calc c • u + (c * lam) • v = c • (u + lam • v) := by rw [smul_add, smul_smul]
        _ = u + (sg K f lam) • v := hc
    have hrel : (c + 1) • u + (c * lam + sg K f lam) • v = 0 := by
      have h2 : c • u + (c * lam) • v + (u + (sg K f lam) • v) = 0 := by
        rw [h]
        exact CharTwo.add_self_eq_zero _
      rw [← h2]
      simp only [add_smul, one_smul]
      abel
    obtain ⟨hc1, hclam⟩ := plh_eq_zero_of_smul_add_smul huv hrel
    have hc_eq : c = 1 := CharTwo.add_eq_zero.mp hc1
    have : sg K f lam = lam := by
      have hcl := CharTwo.add_eq_zero.mp hclam
      rw [hc_eq] at hcl
      simpa using hcl.symm
    exact hlam this
  refine ⟨?_, hne, ?_⟩
  · rw [finrank_span_singleton hw_ne]
  · rw [sgS_span_singleton hK, hsgw]
    have hne' : Submodule.span K {u + (sg K f lam) • v} ≠
        Submodule.span K {u + lam • v} := by
      intro heq
      exact hne (by rw [sgS_span_singleton hK, hsgw]; exact heq)
    have hle : Submodule.span K {u + lam • v} ⊔
        Submodule.span K {u + (sg K f lam) • v} ≤
        Submodule.span K ({u, v} : Set (Fin 4 → K)) := by
      rw [sup_le_iff]
      constructor
      · exact (Submodule.span_singleton_le_iff_mem (u + lam • v)
          (Submodule.span K ({u, v} : Set (Fin 4 → K)))).mpr
          ((Submodule.mem_span_pair).mpr ⟨1, lam, by simp⟩)
      · exact (Submodule.span_singleton_le_iff_mem (u + (sg K f lam) • v)
          (Submodule.span K ({u, v} : Set (Fin 4 → K)))).mpr
          ((Submodule.mem_span_pair).mpr ⟨1, sg K f lam, by simp⟩)
    have hfr : finrank K ↥(Submodule.span K {u + lam • v} ⊔
        Submodule.span K {u + (sg K f lam) • v}) = 2 :=
      finrank_sup_of_ne_pts (finrank_span_singleton hw_ne)
        (finrank_span_singleton hw'_ne) hne'.symm
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, huv])

end CFSG.ClassicalInvolution.Phan.PhanE

end
