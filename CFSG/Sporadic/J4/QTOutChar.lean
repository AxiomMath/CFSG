module

public import CFSG.Sporadic.J4.QTOutCheck
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open scoped Pointwise

@[expose] def Zc : ℕ → Set J
  | 0 => {1}
  | k + 1 => {x | x ∈ P0 ∧ ∀ y ∈ P0, x * y * x⁻¹ * y⁻¹ ∈ Zc k}

@[expose] def ZE (L : List ℕ) : Set J := {x | ∃ c ∈ L, x = eta uJ 11 c}

theorem Zc_invariant (α : MulAut J) (hα : ∀ x, α x ∈ P0 ↔ x ∈ P0) :
    ∀ k x, α x ∈ Zc k ↔ x ∈ Zc k := by
  intro k
  induction k with
  | zero =>
    intro x
    simp only [Zc, Set.mem_singleton_iff]
    constructor
    · intro h
      exact α.injective (by rw [h, map_one])
    · intro h
      rw [h, map_one]
  | succ k ih =>
    intro x
    simp only [Zc, Set.mem_ofPred_eq]
    refine and_congr (hα x) ?_
    constructor
    · intro h y hy
      have h1 := h (α y) ((hα y).2 hy)
      have h2 : α (x * y * x⁻¹ * y⁻¹) = α x * α y * (α x)⁻¹ * (α y)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [← h2] at h1
      exact (ih _).1 h1
    · intro h y hy
      have hy' : α.symm y ∈ P0 := (hα _).1 (by simpa using hy)
      have h1 := (ih _).2 (h _ hy')
      have h2 : α (x * α.symm y * x⁻¹ * (α.symm y)⁻¹) = α x * y * (α x)⁻¹ * y⁻¹ := by
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [h2] at h1
      exact h1

theorem eta_mem_P0 (c : ℕ) : eta uJ 11 c ∈ P0 := Eg_le_P0 (eta_mem_Eg 11 le_rfl c)

theorem lt_xor {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11) : c ^^^ d < 2 ^ 11 :=
  Nat.xor_lt_two_pow hc hd

section WithFacts

variable (hM : MatFacts)
include hM

theorem eta_inv_self (c : ℕ) : (eta uJ 11 c)⁻¹ = eta uJ 11 c :=
  inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) c)

theorem comm_eta_right {x : J} {t : List ℕ} (hx : Acts x t) {c : ℕ} (hc : c < 2 ^ 11) :
    x * eta uJ 11 c * x⁻¹ * (eta uJ 11 c)⁻¹ = eta uJ 11 (actT t c ^^^ c) := by
  rw [hx.2 c hc, eta_inv_self hM, eta_xor (elem_uJ hM) le_rfl]

theorem comm_eta_left {y : J} {t : List ℕ} (hy : Acts y t) {c : ℕ} (hc : c < 2 ^ 11) :
    eta uJ 11 c * y * (eta uJ 11 c)⁻¹ * y⁻¹ = eta uJ 11 (c ^^^ actT t c) := by
  have h1 : y * (eta uJ 11 c)⁻¹ * y⁻¹ = eta uJ 11 (actT t c) := by
    rw [eta_inv_self hM]
    exact hy.2 c hc
  calc eta uJ 11 c * y * (eta uJ 11 c)⁻¹ * y⁻¹
      = eta uJ 11 c * (y * (eta uJ 11 c)⁻¹ * y⁻¹) := by group
    _ = eta uJ 11 (c ^^^ actT t c) := by rw [h1, eta_xor (elem_uJ hM) le_rfl]

theorem mem_ZE_iff {L : List ℕ} (hL : ∀ c ∈ L, c < 2 ^ 11) {d : ℕ} (hd : d < 2 ^ 11) :
    eta uJ 11 d ∈ ZE L ↔ d ∈ L := by
  constructor
  · rintro ⟨c, hc, h⟩
    have := eta_inj hM d hd c (hL c hc) h
    rw [this]; exact hc
  · intro h
    exact ⟨d, h, rfl⟩

variable (hF : J4Facts)
include hF

theorem Zc_step {k : ℕ} {L L' : List ℕ} (hL : ∀ c ∈ L, c < 2 ^ 11) (hL' : ∀ c ∈ L', c < 2 ^ 11)
    (h0 : Zc k = ZE L) (hstep : ucsStep L L' = true) : Zc (k + 1) = ZE L' := by
  unfold ucsStep at hstep
  simp only [Bool.and_eq_true] at hstep
  obtain ⟨⟨hIn, hOut⟩, hFaith⟩ := hstep
  ext x
  simp only [Zc, Set.mem_ofPred_eq, h0]
  constructor
  · rintro ⟨hx, hcomm⟩
    obtain ⟨t, ht, hxt⟩ := table_of_mem hM x hx
    have h1 : ∀ j < 11, (actT t (2 ^ j) ^^^ 2 ^ j) ∈ L := by
      intro j hj
      have hj' : 2 ^ j < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hj
      have hy : eta uJ 11 (2 ^ j) ∈ P0 := eta_mem_P0 _
      have h2 := hcomm _ hy
      rw [comm_eta_right hM hxt hj'] at h2
      exact (mem_ZE_iff hM hL (lt_xor (actT_lt hxt.1 _) hj')).1 h2
    have htid : t = idT := by
      unfold stepFaithful at hFaith
      rw [List.all_eq_true] at hFaith
      have h3 := hFaith t ht
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true',
        List.mem_range] at h3
      rcases h3 with h3 | ⟨j, hj, hnot⟩
      · exact h3
      · have h5 := List.contains_iff_mem.2 (h1 j hj)
        rw [hnot] at h5
        exact absurd h5 (by decide)
    subst htid
    have hxE : x ∈ Eg uJ 11 := by
      refine centralizer_Hj hM hF x (P0_le_Hj hx) (fun y hy => ?_)
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hxt.2 c hc
      rw [actT_idT hc] at this
      calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
        _ = eta uJ 11 c * x := by rw [this]
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hxE
    refine ⟨c, ?_, rfl⟩
    by_contra hcL'
    unfold stepOut at hOut
    rw [List.all_eq_true] at hOut
    have h4 := hOut c (List.mem_range.2 hc)
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h4
    rcases h4 with h4 | ⟨t', ht', hnot⟩
    · exact hcL' (List.contains_iff_mem.1 h4)
    · obtain ⟨f, hf, rfl⟩ : ∃ f < 1024, seqT (pcSeq f) = t' := by
        unfold tabL at ht'
        simpa [List.mem_map, List.mem_range] using ht'
      have hy : Kel f ∈ P0 := Kel_mem_P0 hf
      have h2 := hcomm _ hy
      rw [comm_eta_left hM (Acts_Kel hM hf) hc] at h2
      have h5 := List.contains_iff_mem.2
        ((mem_ZE_iff hM hL (lt_xor hc (actT_lt (Acts_Kel hM hf).1 _))).1 h2)
      rw [hnot] at h5
      exact absurd h5 (by decide)
  · rintro ⟨c, hc, rfl⟩
    refine ⟨eta_mem_P0 c, fun y hy => ?_⟩
    have hc2 : c < 2 ^ 11 := hL' c hc
    obtain ⟨t, ht, hyt⟩ := table_of_mem hM y hy
    rw [comm_eta_left hM hyt hc2]
    unfold stepIn at hIn
    rw [List.all_eq_true] at hIn
    have h5 := hIn c hc
    rw [List.all_eq_true] at h5
    have h6 := h5 t ht
    exact ⟨_, List.contains_iff_mem.1 h6, rfl⟩

theorem Zc_eq : ∀ k ≤ 4, Zc k = ZE (ucsMasks.getD k []) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ucs_zero]
    ext x
    simp only [Zc, Set.mem_singleton_iff, ZE, List.mem_singleton, exists_eq_left, Set.mem_ofPred_eq]
    rw [eta_zero]
  | succ k ih =>
    intro hk
    have hk' : k < 4 := by omega
    have hlt : ∀ i, ∀ c ∈ ucsMasks.getD i [], c < 2 ^ 11 := by
      intro i c hc
      by_cases hi : i < ucsMasks.length
      · rw [List.getD_eq_getElem _ _ hi] at hc
        exact ucs_lt _ (List.getElem_mem hi) c hc
      · rw [List.getD_eq_default _ _ (by omega)] at hc
        simp at hc
    exact Zc_step hM hF (hlt k) (hlt (k + 1)) (ih (by omega)) (ucs_steps k hk')

end WithFacts

noncomputable abbrev Csub : Subgroup J := P0 ⊓ Subgroup.centralizer (Zc 4)

theorem pcSeq_zero : pcSeq 0 = [] := by
  unfold pcSeq
  simp [Nat.zero_testBit]

theorem Kel_zero : Kel 0 = 1 := by
  unfold Kel
  rw [pcSeq_zero]
  simp

theorem tabE_inj {e e' : ℕ} (he : e < 1024) (he' : e' < 1024)
    (h : seqT (pcSeq e) = seqT (pcSeq e')) : e = e' := by
  have hnd := tabL_nodup
  unfold tabL at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 he) (List.mem_range.2 he') h

theorem seqT_pcSeq_zero : seqT (pcSeq 0) = idT := by
  unfold seqT
  rw [pcSeq_zero]
  simp

theorem Zc4_sub_Eg (hM : MatFacts) (hF : J4Facts) : Zc 4 ⊆ Eg uJ 11 := by
  intro x hx
  rw [Zc_eq hM hF 4 le_rfl] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact eta_mem_Eg 11 le_rfl c

theorem Eg_le_Csub (hM : MatFacts) (hF : J4Facts) : Eg uJ 11 ≤ Csub := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Eg_le_P0 hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Eg_comm (elem_uJ hM) (Zc4_sub_Eg hM hF hz) hx

theorem fixesZ4_of_comm (hM : MatFacts) (hF : J4Facts) {x : J} {t : List ℕ} (hxt : Acts x t)
    (hx : x ∈ Subgroup.centralizer (Zc 4)) : fixesZ4 t = true := by
  unfold fixesZ4
  rw [List.all_eq_true]
  intro w hw
  have hwlt : w < 2 ^ 11 := by
    have hwL : w ∈ ucsMasks.getD 4 [] := hw
    have hlen : 4 < ucsMasks.length := by rw [ucs_length]; norm_num
    rw [List.getD_eq_getElem _ _ hlen] at hwL
    exact ucs_lt _ (List.getElem_mem hlen) w hwL
  have hz : eta uJ 11 w ∈ Zc 4 := by
    rw [Zc_eq hM hF 4 le_rfl]
    exact ⟨w, hw, rfl⟩
  have h1 := (Subgroup.mem_centralizer_iff.1 hx) _ hz
  have h2 : x * eta uJ 11 w * x⁻¹ = eta uJ 11 w := by
    rw [← h1]; group
  rw [hxt.2 w hwlt] at h2
  have := eta_inj hM _ (actT_lt hxt.1 w) _ hwlt h2
  simpa using this

theorem mem_Csub (hM : MatFacts) (hF : J4Facts) {x : J} (hx : x ∈ Csub) :
    x ∈ Eg uJ 11 ∨ ∃ c < 2 ^ 11, x = eta uJ 11 c * Kel eT := by
  obtain ⟨c, hc, e, he, rfl⟩ := exists_eta_mul_Kel hM hF (Subgroup.mem_inf.1 hx).1
  have hxt := Acts_eta_mul_Kel hM (c := c) he
  have hfix := fixesZ4_of_comm hM hF hxt (Subgroup.mem_inf.1 hx).2
  have hmem : seqT (pcSeq e) ∈ tabL := by
    unfold tabL
    exact List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩
  rcases fixesZ4_cases _ hmem hfix with h | h
  · left
    have : e = 0 := tabE_inj he (by norm_num) (by rw [h, seqT_pcSeq_zero])
    subst this
    rw [Kel_zero, mul_one]
    exact eta_mem_Eg 11 le_rfl c
  · right
    have : e = eT := tabE_inj he eT_lt (by rw [h]; rfl)
    subst this
    exact ⟨c, hc, rfl⟩

theorem Kel_eT_mem_Csub (hM : MatFacts) (hF : J4Facts) : Kel eT ∈ Csub := by
  refine Subgroup.mem_inf.2 ⟨Kel_mem_P0 eT_lt, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Zc_eq hM hF 4 le_rfl] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwlt : w < 2 ^ 11 := by
    have hlen : 4 < ucsMasks.length := by rw [ucs_length]; norm_num
    have hwL : w ∈ ucsMasks.getD 4 [] := hw
    rw [List.getD_eq_getElem _ _ hlen] at hwL
    exact ucs_lt _ (List.getElem_mem hlen) w hwL
  have hK := Acts_Kel hM eT_lt
  have h1 := hK.2 w hwlt
  have hfix : actT (seqT (pcSeq eT)) w = w := by
    have := tET_fixes
    unfold fixesZ4 at this
    rw [List.all_eq_true] at this
    have h3 : actT tET w = w := by simpa using this w hw
    exact h3
  rw [hfix] at h1
  calc eta uJ 11 w * Kel eT = (Kel eT * eta uJ 11 w * (Kel eT)⁻¹) * Kel eT := by rw [h1]
    _ = Kel eT * eta uJ 11 w := by group

theorem relIndex_Eg_Csub_le (hM : MatFacts) (hF : J4Facts) : (Eg uJ 11).relIndex Csub ≤ 2 := by
  let t0 : Csub := ⟨Kel eT, Kel_eT_mem_Csub hM hF⟩
  have hsurj : Function.Surjective
      (fun b : Bool => (QuotientGroup.mk (if b then t0 else 1) :
        Csub ⧸ (Eg uJ 11).subgroupOf Csub)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rcases mem_Csub hM hF x.2 with hx | ⟨c, hc, hxc⟩
    · refine ⟨false, ?_⟩
      show (QuotientGroup.mk 1 : Csub ⧸ (Eg uJ 11).subgroupOf Csub) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      simpa using (Eg uJ 11).inv_mem hx
    · refine ⟨true, ?_⟩
      show (QuotientGroup.mk t0 : Csub ⧸ (Eg uJ 11).subgroupOf Csub) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (Kel eT)⁻¹ * (x : J) ∈ Eg uJ 11
      rw [hxc]
      obtain ⟨t, -, ht⟩ := table_of_mem hM (Kel eT)⁻¹ (P0.inv_mem (Kel_mem_P0 eT_lt))
      have h1 : (Kel eT)⁻¹ * (eta uJ 11 c * Kel eT) = (Kel eT)⁻¹ * eta uJ 11 c * (Kel eT)⁻¹⁻¹ := by
        group
      rw [h1, ht.2 c hc]
      exact eta_mem_Eg 11 le_rfl _
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Subgroup.relIndex, Subgroup.index]
  simpa using this

theorem relIndex_Eg_Csub_ne_zero : (Eg uJ 11).relIndex Csub ≠ 0 := by
  have h := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := Csub)
  have hpos : 0 < Nat.card Csub := Nat.card_pos
  rw [← h] at hpos
  exact (Nat.pos_of_mul_pos_right hpos).ne'

theorem eta_char (hM : MatFacts) (hF : J4Facts) (α : MulAut J) (hα : ∀ x, α x ∈ P0 ↔ x ∈ P0)
    (x : J) : α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11 := by
  classical
  let φ : J →* J := MulEquiv.toMonoidHom α
  set A' : Subgroup J := (Eg uJ 11).map φ with hA'
  have hmemA' : ∀ y, y ∈ A' ↔ ∃ x ∈ Eg uJ 11, α x = y := fun y => Subgroup.mem_map
  have hA'le : A' ≤ Csub := by
    intro y hy
    obtain ⟨x0, hx0, rfl⟩ := (hmemA' y).1 hy
    refine Subgroup.mem_inf.2 ⟨(hα x0).2 (Eg_le_P0 hx0), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : α.symm z ∈ Zc 4 := by
      rw [← Zc_invariant α hα 4]
      simpa using hz
    have hz'E := Zc4_sub_Eg hM hF hz'
    have hc := Eg_comm (elem_uJ hM) hz'E hx0
    calc z * α x0 = α (α.symm z) * α x0 := by simp
      _ = α (α.symm z * x0) := by rw [map_mul]
      _ = α (x0 * α.symm z) := by rw [hc]
      _ = α x0 * z := by rw [map_mul]; simp
  have hcard : Nat.card A' = 2 ^ 11 := by
    rw [hA', Subgroup.card_map_of_injective (f := φ) α.injective, card_Eg_uJ hM]
  have hle : A' ≤ Eg uJ 11 := by
    by_contra hnle
    obtain ⟨a, haA, haE⟩ : ∃ a ∈ A', a ∉ Eg uJ 11 := by
      by_contra hcon
      apply hnle
      intro y hy
      by_contra hyE
      exact hcon ⟨y, hy, hyE⟩
    rcases mem_Csub hM hF (hA'le haA) with h | ⟨c, hc, hac⟩
    · exact haE h
    · have hxt : Acts a tET := by
        rw [hac]
        exact Acts_eta_mul_Kel hM eT_lt
      have hfix := fixCount_le tET tET_inv.1 tET_inv.2.1 tET_inv.2.2
      have hcomm : ∀ y ∈ A', a * y = y * a := by
        intro y hy
        obtain ⟨a0, ha0, rfl⟩ := (hmemA' a).1 haA
        obtain ⟨y0, hy0, rfl⟩ := (hmemA' y).1 hy
        rw [← map_mul, ← map_mul, Eg_comm (elem_uJ hM) ha0 hy0]
      have h1 := card_inf_le hM hcomm hxt hfix
      have h2 : (Eg uJ 11).relIndex A' ≤ 2 :=
        le_trans (Subgroup.relIndex_le_of_le_right hA'le relIndex_Eg_Csub_ne_zero)
          (relIndex_Eg_Csub_le hM hF)
      have h3 := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := A')
      have h4 := Nat.mul_le_mul h2 h1
      rw [h3, hcard] at h4
      omega
  have heq : A' = Eg uJ 11 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_Eg_uJ hM])
  constructor
  · intro h
    rw [← heq, hmemA'] at h
    obtain ⟨x', hx', hxx'⟩ := h
    rw [← α.injective hxx']
    exact hx'
  · intro h
    rw [← heq]
    exact (hmemA' _).2 ⟨x, h, rfl⟩

end CFSG.Sporadic.J4.QT
