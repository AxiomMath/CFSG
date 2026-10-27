module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Def
public import CFSG.LocalAnalysis.StandardType.PhanELocalSel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K]

private lemma plh_Vsub_mono {n c c' : ℕ} (h : c ≤ c') :
    Vsub (K := K) n c ≤ Vsub (K := K) n c' := by
  intro v hv j hj
  exact hv j (le_trans h hj)

private lemma plh_e0_mem_Vsub1 : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ Vsub (K := K) 4 1 := by
  intro j hj
  exact Pi.single_eq_of_ne' (M := fun _ => K) (i := 0) (i' := j)
    (by rintro rfl; omega) (1 : K)

private lemma plh_e0_ne_zero : (Pi.single 0 (1 : K) : Fin 4 → K) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h 0)

private lemma plh_Vsub_one_eq_span_e0 :
    Vsub (K := K) 4 1 = K ∙ (Pi.single 0 (1 : K) : Fin 4 → K) :=
  eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_Vsub (K := K) (n := 4) (by norm_num : 1 ≤ 4)) plh_e0_mem_Vsub1 plh_e0_ne_zero

private lemma plh_finrank_fin4 : finrank K (Fin 4 → K) = 4 := by simp

private lemma plh_ne_top_of_finrank_eq_three {T : Submodule K (Fin 4 → K)}
    (h : finrank K T = 3) : T ≠ ⊤ := by
  intro htop
  have h4 : finrank K T = 4 := by
    rw [htop, finrank_top, plh_finrank_fin4]
  omega

private lemma plh_exists_plane (L H' : Submodule K (Fin 4 → K))
    (hL : finrank K L = 2) (hH' : finrank K H' = 3)
    (hLV2 : L ⊓ Vsub 4 2 = ⊥) (hH'V1 : H' ⊓ Vsub 4 1 = ⊥)
    (hQ : 16 ≤ Nat.card K) :
    ∃ H3 : Submodule K (Fin 4 → K), finrank K H3 = 3 ∧ L ≤ H3 ∧
      H3 ⊓ Vsub 4 1 = ⊥ ∧ ¬ (H' ⊓ Vsub 4 2) ≤ H3 ∧ (H' ⊓ Vsub 4 2) ⊓ H3 = ⊥ ∧
      H3 ≠ H' := by
  have he0V1 : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ Vsub 4 1 := plh_e0_mem_Vsub1
  have he0V2 : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ Vsub 4 2 :=
    plh_Vsub_mono (K := K) (n := 4) (by norm_num : 1 ≤ 2) he0V1
  have he0ne : (Pi.single 0 (1 : K) : Fin 4 → K) ≠ 0 := plh_e0_ne_zero
  have hnotV2H' : ¬ Vsub 4 2 ≤ H' := by
    intro hle
    have he0H' : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ H' := hle he0V2
    have : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ H' ⊓ Vsub 4 1 :=
      Submodule.mem_inf.mpr ⟨he0H', he0V1⟩
    rw [hH'V1] at this
    exact he0ne (by simpa using this)
  have hV2H'sup : H' ⊔ Vsub 4 2 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hle : finrank K ↥(H' ⊔ Vsub 4 2) ≤ 4 := by
      have := Submodule.finrank_le (H' ⊔ Vsub 4 2)
      rwa [plh_finrank_fin4] at this
    have hgt : 3 < finrank K ↥(H' ⊔ Vsub 4 2) := by
      have hlt : H' < H' ⊔ Vsub 4 2 := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        exact hnotV2H' (heq.symm ▸ le_sup_right)
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rwa [hH'] at this
    rw [plh_finrank_fin4]
    omega
  have ha'fin : finrank K ↥(H' ⊓ Vsub 4 2) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq H' (Vsub 4 2)
    rw [hV2H'sup, finrank_top, plh_finrank_fin4, hH',
      finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num : 2 ≤ 4)] at h
    omega
  obtain ⟨u, hune, huspan⟩ :=
    CFSG.ClassicalInvolution.Phan.exists_eq_span_of_finrank_eq_one
      (L := H' ⊓ Vsub 4 2) ha'fin
  have hu'mem : u ∈ H' ⊓ Vsub 4 2 := by
    rw [huspan]
    exact Submodule.mem_span_singleton_self u
  have huV2 : u ∈ Vsub 4 2 := (Submodule.mem_inf.mp hu'mem).2
  have huL : u ∉ L := by
    intro huL
    have : u ∈ L ⊓ Vsub 4 2 := Submodule.mem_inf.mpr ⟨huL, huV2⟩
    rw [hLV2] at this
    exact hune (by simpa using this)
  have he0L : (Pi.single 0 (1 : K) : Fin 4 → K) ∉ L := by
    intro hmem
    have : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ L ⊓ Vsub 4 2 :=
      Submodule.mem_inf.mpr ⟨hmem, he0V2⟩
    rw [hLV2] at this
    exact he0ne (by simpa using this)
  have hfinLV1 : finrank K ↥(L ⊔ Vsub 4 1) = 3 := by
    rw [plh_Vsub_one_eq_span_e0,
      Submodule.finrank_sup_span_singleton (K := K) he0L, hL]
  have hfinLa' : finrank K ↥(L ⊔ (H' ⊓ Vsub 4 2)) = 3 := by
    rw [huspan, Submodule.finrank_sup_span_singleton (K := K) huL, hL]
  let S : Finset (Submodule K (Fin 4 → K)) :=
    insert (L ⊔ Vsub 4 1) (insert (L ⊔ (H' ⊓ Vsub 4 2)) {H'})
  obtain ⟨w, hw⟩ := exists_notMem_of_card_lt S
    (by
      intro T hT
      dsimp only [S] at hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact plh_ne_top_of_finrank_eq_three hfinLV1
      · exact plh_ne_top_of_finrank_eq_three hfinLa'
      · exact plh_ne_top_of_finrank_eq_three hH')
    (by
      have hcard : S.card ≤ 3 := by
        dsimp only [S]
        exact Finset.card_le_three
      omega)
  have hw1 : w ∉ L ⊔ Vsub 4 1 :=
    hw _ (Finset.mem_insert.mpr (Or.inl rfl))
  have hw2 : w ∉ L ⊔ (H' ⊓ Vsub 4 2) :=
    hw _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl))))
  have hw3 : w ∉ H' :=
    hw _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self H')))))
  have hwL : w ∉ L := fun h => hw1 (Submodule.mem_sup_left h)
  let H3 : Submodule K (Fin 4 → K) := L ⊔ (K ∙ w)
  have hLH3 : L ≤ H3 := le_sup_left
  have hH3fin : finrank K H3 = 3 := by
    change finrank K ↥(L ⊔ (K ∙ w)) = 3
    rw [Submodule.finrank_sup_span_singleton (K := K) hwL, hL]
  have he0H3 : (Pi.single 0 (1 : K) : Fin 4 → K) ∉ H3 := by
    intro he0H3
    change (Pi.single 0 (1 : K) : Fin 4 → K) ∈ L ⊔ (K ∙ w) at he0H3
    obtain ⟨l, hl, y, hy, hsum⟩ := Submodule.mem_sup.mp he0H3
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hc : c = 0
    · have he0L' : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ L := by
        rw [← hsum, hc, zero_smul, add_zero]
        exact hl
      have : (Pi.single 0 (1 : K) : Fin 4 → K) ∈ L ⊓ Vsub 4 2 :=
        Submodule.mem_inf.mpr ⟨he0L', he0V2⟩
      rw [hLV2] at this
      exact he0ne (by simpa using this)
    · have hcw : c • w = (Pi.single 0 (1 : K) : Fin 4 → K) - l := by
        rw [eq_sub_iff_add_eq]
        simpa [add_comm] using hsum
      have hweq : w = c⁻¹ • ((Pi.single 0 (1 : K) : Fin 4 → K) - l) := by
        rw [← hcw, smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hmem : (Pi.single 0 (1 : K) : Fin 4 → K) - l ∈ Vsub 4 1 ⊔ L := by
        rw [Submodule.mem_sup]
        exact ⟨(Pi.single 0 (1 : K) : Fin 4 → K), he0V1, -l,
          Submodule.neg_mem L hl, by rw [sub_eq_add_neg]⟩
      have hwm : w ∈ Vsub 4 1 ⊔ L := by
        rw [hweq]
        exact Submodule.smul_mem _ _ hmem
      exact hw1 (by simpa [sup_comm] using hwm)
  have huH3 : u ∉ H3 := by
    intro huH3
    change u ∈ L ⊔ (K ∙ w) at huH3
    obtain ⟨l, hl, y, hy, hsum⟩ := Submodule.mem_sup.mp huH3
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hc : c = 0
    · have huL' : u ∈ L := by
        rw [← hsum, hc, zero_smul, add_zero]
        exact hl
      exact huL huL'
    · have hcw : c • w = u - l := by
        rw [eq_sub_iff_add_eq]
        simpa [add_comm] using hsum
      have hweq : w = c⁻¹ • (u - l) := by
        rw [← hcw, smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hmem : u - l ∈ L ⊔ (H' ⊓ Vsub 4 2) := by
        rw [Submodule.mem_sup]
        exact ⟨-l, Submodule.neg_mem L hl, u, hu'mem,
          by rw [sub_eq_add_neg]; exact add_comm (-l) u⟩
      have hwm : w ∈ L ⊔ (H' ⊓ Vsub 4 2) := by
        rw [hweq]
        exact Submodule.smul_mem _ _ hmem
      exact hw2 hwm
  have hH3V1 : H3 ⊓ Vsub 4 1 = ⊥ := by
    rw [plh_Vsub_one_eq_span_e0]
    exact disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem he0H3)
  have hnota' : ¬ (H' ⊓ Vsub 4 2) ≤ H3 := fun hle => huH3 (hle hu'mem)
  have ha'H3 : (H' ⊓ Vsub 4 2) ⊓ H3 = ⊥ := by
    rw [huspan]
    exact disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem huH3).symm
  have hH3ne : H3 ≠ H' := by
    intro heq
    have hwH3 : w ∈ H3 := by
      change w ∈ L ⊔ (K ∙ w)
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    rw [heq] at hwH3
    exact hw3 hwH3
  exact ⟨H3, hH3fin, hLH3, hH3V1, hnota', ha'H3, hH3ne⟩

theorem adm1111_fibreConn (hQ : 16 ≤ Nat.card K) : AdmFibreConn (Adm1111 (K := K)) := by
  intro p L H L' H' hp hp'
  have hA : AdmCh Adm1111 p L H := hp
  have hE : AdmCh Adm1111 p L' H' := hp'
  obtain ⟨hflag, hpV3, hLV2, _⟩ := hp
  obtain ⟨hflag', _, _, hH'V1⟩ := hp'
  obtain ⟨H3, hH3fin, hLH3, hH3V1, hnota', ha'H3, hH3ne⟩ :=
    plh_exists_plane L H' hflag.L2 hflag'.H3 hLV2 hH'V1 hQ
  let L3 : Submodule K (Fin 4 → K) := H3 ⊓ H'
  have hH3H'top : H3 ⊔ H' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hle : finrank K ↥(H3 ⊔ H') ≤ 4 := by
      have := Submodule.finrank_le (H3 ⊔ H')
      rwa [plh_finrank_fin4] at this
    have hgt : 3 < finrank K ↥(H3 ⊔ H') := by
      have hlt : H' < H3 ⊔ H' := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        have hH3le : H3 ≤ H' := by rw [heq]; exact le_sup_left
        exact hH3ne (Submodule.eq_of_le_of_finrank_eq hH3le (by rw [hH3fin, hflag'.H3]))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rwa [hflag'.H3] at this
    rw [plh_finrank_fin4]
    omega
  have hL3fin : finrank K L3 = 2 := by
    change finrank K ↥(H3 ⊓ H') = 2
    have h := Submodule.finrank_sup_add_finrank_inf_eq H3 H'
    rw [hH3H'top, finrank_top, plh_finrank_fin4, hH3fin, hflag'.H3] at h
    omega
  have hpL3 : p ≤ L3 := by
    change p ≤ H3 ⊓ H'
    exact le_inf (le_trans hflag.pL hLH3) (le_trans hflag'.pL hflag'.LH)
  have hL3V2 : L3 ⊓ Vsub 4 2 = ⊥ := by
    change (H3 ⊓ H') ⊓ Vsub 4 2 = ⊥
    have hsub : (H3 ⊓ H') ⊓ Vsub 4 2 ≤ (H' ⊓ Vsub 4 2) ⊓ H3 := by
      intro x hx
      obtain ⟨hxH3H', hxV2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨hxH3, hxH'⟩ := Submodule.mem_inf.mp hxH3H'
      exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxH', hxV2⟩, hxH3⟩
    exact le_bot_iff.mp (hsub.trans (le_of_eq ha'H3))
  have hB : AdmCh Adm1111 p L H3 :=
    ⟨⟨hflag.p1, hflag.L2, hH3fin, hflag.pL, hLH3⟩, hpV3, hLV2, hH3V1⟩
  have hC : AdmCh Adm1111 p L3 H3 :=
    ⟨⟨hflag.p1, hL3fin, hH3fin, hpL3, inf_le_left⟩, hpV3, hL3V2, hH3V1⟩
  have hD : AdmCh Adm1111 p L3 H' :=
    ⟨⟨hflag.p1, hL3fin, hflag'.H3, hpL3, inf_le_right⟩, hpV3, hL3V2, hH'V1⟩
  let R : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) →
      Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) → Prop :=
    fun a b => AdmCh Adm1111 p a.1 a.2 ∧ AdmCh Adm1111 p b.1 b.2 ∧
      (a.2 = b.2 ∨ a.1 = b.1)
  have hAB : R (L, H) (L, H3) := ⟨hA, hB, Or.inr rfl⟩
  have hBC : R (L, H3) (L3, H3) := ⟨hB, hC, Or.inl rfl⟩
  have hCD : R (L3, H3) (L3, H') := ⟨hC, hD, Or.inr rfl⟩
  have hDE : R (L3, H') (L', H') := ⟨hD, hE, Or.inl rfl⟩
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single hAB) hBC) hCD) hDE

end CFSG.ClassicalInvolution.Phan.PhanE

end
