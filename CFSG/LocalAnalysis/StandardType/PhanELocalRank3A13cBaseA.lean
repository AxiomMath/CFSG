module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cT
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cNonrat

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private lemma plh_sgS_le_Vtail {Y : Submodule K (Fin 4 → K)} (hY : Y ≤ Vtail) :
    sgS K f 4 Y ≤ Vtail := by
  intro v hv
  show v 0 = 0
  have hv' : sgv K f 4 v ∈ Y := hv
  have h0 : (sgv K f 4 v) 0 = 0 := hY hv'
  have h1 : sg K f (v 0) = 0 := h0
  exact (sg K f).map_eq_zero_iff.mp h1

private lemma plh_inf_eq_bot_iff {A B : Submodule K (Fin 4 → K)} (hA : finrank K A = 1) :
    A ⊓ B = ⊥ ↔ ¬ A ≤ B := by
  constructor
  · intro h hle
    have hAle : A ≤ ⊥ := by
      rw [← h]
      exact le_inf le_rfl hle
    have hbot : A = ⊥ := le_bot_iff.mp hAle
    have hfin : finrank K A = 0 := by rw [hbot, finrank_bot]
    omega
  · intro h
    by_contra hne
    have hle1 : finrank K ↥(A ⊓ B) ≤ 1 := by
      rw [← hA]
      exact Submodule.finrank_mono inf_le_left
    have hne1 : finrank K ↥(A ⊓ B) ≠ 1 := by
      intro heq
      have hAB : A ≤ B := by
        have he : A ⊓ B = A :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hA])
        rw [← he]
        exact inf_le_right
      exact h hAB
    have h0 : finrank K ↥(A ⊓ B) = 0 := by omega
    exact hne (Submodule.finrank_eq_zero.mp h0)

private lemma plh_okL_iff (hK : Nat.card K = (2 ^ f) ^ 2) {p L : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) :
    (D13c (K := K) f).okL p L ↔ ¬ sgS K f 4 p ≤ L := by
  have h1 : p ⊓ sgS K f 4 L = ⊥ ↔ ¬ p ≤ sgS K f 4 L := plh_inf_eq_bot_iff hp
  have h2 : L ⊓ sgS K f 4 p = ⊥ ↔ ¬ sgS K f 4 p ≤ L := by
    rw [inf_comm]
    exact plh_inf_eq_bot_iff (by rw [finrank_sgS (K := K) (f := f) (n := 4) hK p, hp])
  have h3 : p ≤ sgS K f 4 L ↔ sgS K f 4 p ≤ L := by
    constructor
    · intro hle
      have := sgS_mono (K := K) (f := f) (n := 4) hle
      rwa [sgS_sgS (K := K) (f := f) (n := 4) hK L] at this
    · intro hle
      have := sgS_mono (K := K) (f := f) (n := 4) hle
      rwa [sgS_sgS (K := K) (f := f) (n := 4) hK p] at this
  show (p ⊓ sgS K f 4 L = ⊥ ∧ L ⊓ sgS K f 4 p = ⊥) ↔ ¬ sgS K f 4 p ≤ L
  rw [h1, h3, h2]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem nonrat_of_okL (hK : Nat.card K = (2 ^ f) ^ 2) {p L : Submodule K (Fin 4 → K)}
    (hpL : p ≤ L) (hp : finrank K p = 1) (hok : (D13c (K := K) f).okL p L) :
    sgS K f 4 p ≠ p := by
  intro h
  have hle : sgS K f 4 p ≤ L := by
    rw [h]
    exact hpL
  exact (plh_okL_iff f hK hp).mp hok hle

private lemma plh_nonrat_of_sup (hK : Nat.card K = (2 ^ f) ^ 2)
    {x y : Submodule K (Fin 4 → K)} (hx : BPt x) (hxy : BAdj (D13c (K := K) f) x y) :
    sgS K f 4 x ≠ x :=
  nonrat_of_okL f hK le_sup_left hx.2 hxy.2.1

private lemma plh_nonrat_of_sup' (hK : Nat.card K = (2 ^ f) ^ 2)
    {x y : Submodule K (Fin 4 → K)} (hy : BPt y) (hxy : BAdj (D13c (K := K) f) x y) :
    sgS K f 4 y ≠ y :=
  nonrat_of_okL f hK le_sup_right hy.2 hxy.2.2

theorem badj_a3_13c (hK : Nat.card K = (2 ^ f) ^ 2) {u t : Submodule K (Fin 4 → K)}
    (hu : BPt u) (ht : BPt t) (hnu : sgS K f 4 u ≠ u) (hnt : sgS K f 4 t ≠ t)
    (htu : ¬ t ≤ u ⊔ sgS K f 4 u) : BAdj (D13c (K := K) f) u t := by
  obtain ⟨huV, hu1⟩ := hu
  obtain ⟨htV, ht1⟩ := ht
  have hut : u ≠ t := by
    intro h
    apply htu
    rw [← h]
    exact le_sup_left
  have hsup : finrank K ↥(u ⊔ t) = 2 := finrank_sup_of_ne_pts hu1 ht1 hut
  have hspu : finrank K ↥(sgS K f 4 u) = 1 := by
    rw [finrank_sgS (K := K) (f := f) (n := 4) hK u, hu1]
  have hsupu : finrank K ↥(u ⊔ sgS K f 4 u) = 2 := finrank_sup_of_ne_pts hu1 hspu hnu.symm
  have hnu_le : ¬ sgS K f 4 u ≤ u ⊔ t := by
    intro hle
    have hle' : u ⊔ sgS K f 4 u ≤ u ⊔ t := sup_le le_sup_left hle
    have heq : u ⊔ sgS K f 4 u = u ⊔ t :=
      Submodule.eq_of_le_of_finrank_eq hle' (by rw [hsupu, hsup])
    apply htu
    rw [heq]
    exact le_sup_right
  have hok1 : (D13c (K := K) f).okL u (u ⊔ t) := (plh_okL_iff f hK hu1).mpr hnu_le
  have hst1 : finrank K ↥(sgS K f 4 t) = 1 := by
    rw [finrank_sgS (K := K) (f := f) (n := 4) hK t, ht1]
  have hsupt : finrank K ↥(t ⊔ sgS K f 4 t) = 2 := finrank_sup_of_ne_pts ht1 hst1 hnt.symm
  have hnt_le : ¬ sgS K f 4 t ≤ u ⊔ t := by
    intro hle
    have hle' : t ⊔ sgS K f 4 t ≤ u ⊔ t := sup_le le_sup_right hle
    have heq : t ⊔ sgS K f 4 t = u ⊔ t :=
      Submodule.eq_of_le_of_finrank_eq hle' (by rw [hsupt, hsup])
    apply hnu_le
    have h1 : sgS K f 4 (t ⊔ sgS K f 4 t) = sgS K f 4 (u ⊔ t) := by rw [heq]
    rw [sgS_sup (K := K) (f := f) (n := 4) hK, sgS_sgS (K := K) (f := f) (n := 4) hK,
      sgS_sup (K := K) (f := f) (n := 4) hK] at h1
    calc sgS K f 4 u ≤ sgS K f 4 u ⊔ sgS K f 4 t := le_sup_left
      _ = sgS K f 4 t ⊔ t := h1.symm
      _ = t ⊔ sgS K f 4 t := sup_comm _ _
      _ = u ⊔ t := heq
  have hok2 : (D13c (K := K) f).okL t (u ⊔ t) := (plh_okL_iff f hK ht1).mpr hnt_le
  exact ⟨hut, hok1, hok2⟩

private lemma plh_two_mul_pow_lt (hQ : 2 < Nat.card K) :
    2 * Nat.card K ^ 2 < Nat.card K ^ 3 := by
  have hpos : 0 < Nat.card K := by omega
  calc 2 * Nat.card K ^ 2 < Nat.card K * Nat.card K ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hQ (pow_pos hpos 2)
    _ = Nat.card K ^ 3 := by ring

private lemma plh_pow_two_lt_three (hQ : 2 < Nat.card K) :
    Nat.card K ^ 2 < Nat.card K ^ 3 := by
  have hpos : 0 < Nat.card K := by omega
  calc Nat.card K ^ 2 < 2 * Nat.card K ^ 2 := by
        have := pow_pos hpos 2
        nlinarith
    _ < Nat.card K ^ 3 := plh_two_mul_pow_lt hQ

private lemma plh_sum_vol (s : Finset (Submodule K (Fin 4 → K)))
    (h : ∀ T ∈ s, finrank K T = 2) :
    ∑ T ∈ s, Nat.card K ^ finrank K T = s.card * Nat.card K ^ 2 :=
  Finset.sum_const_nat fun T hT => by rw [h T hT]

private lemma plh_card_three {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 := by
  have h1 : ({a, b, c} : Finset α).card ≤ ({b, c} : Finset α).card + 1 :=
    Finset.card_insert_le a {b, c}
  have h2 : ({b, c} : Finset α).card ≤ ({c} : Finset α).card + 1 :=
    Finset.card_insert_le b {c}
  have h3 : ({c} : Finset α).card = 1 := by simp
  omega

private lemma plh_card_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h1 : ({a, b, c, d} : Finset α).card ≤ ({b, c, d} : Finset α).card + 1 :=
    Finset.card_insert_le a {b, c, d}
  have h2 : ({b, c, d} : Finset α).card ≤ ({c, d} : Finset α).card + 1 :=
    Finset.card_insert_le b {c, d}
  have h3 : ({c, d} : Finset α).card ≤ ({d} : Finset α).card + 1 :=
    Finset.card_insert_le c {d}
  have h4 : ({d} : Finset α).card = 1 := by simp
  omega

theorem a13c_link (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ p L : Submodule K (Fin 4 → K), BFl p L → (D13c (K := K) f).okL p L →
      ∃ L₂ L₃ : Submodule K (Fin 4 → K), L₂ ≠ L₃ ∧ BFl p L₂ ∧ BFl p L₃ ∧
        (D13c (K := K) f).okL p L₂ ∧ (D13c (K := K) f).okL p L₃ := by
  classical
  intro p L hpL hok
  obtain ⟨hpLle, hLV, hp1, -⟩ := hpL
  have hpV : p ≤ Vtail := le_trans hpLle hLV
  have hnu : sgS K f 4 p ≠ p := nonrat_of_okL f hK hpLle hp1 hok
  have hsp1 : finrank K ↥(sgS K f 4 p) = 1 := by
    rw [finrank_sgS (K := K) (f := f) (n := 4) hK p, hp1]
  set P : Submodule K (Fin 4 → K) := p ⊔ sgS K f 4 p with hP
  have hPV : P ≤ Vtail := by
    rw [hP]
    exact sup_le hpV (plh_sgS_le_Vtail f hpV)
  have hP2 : finrank K P = 2 := by
    rw [hP]
    exact finrank_sup_of_ne_pts hp1 hsp1 hnu.symm
  have hQ16 : 16 ≤ Nat.card K := by
    rw [hK, pow_two]
    calc 16 = 4 * 4 := by norm_num
      _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq hq
  have hQ : 2 < Nat.card K := by omega
  have hlt1 : Nat.card K ^ finrank K P <
      Nat.card K ^ finrank K (Vtail : Submodule K (Fin 4 → K)) := by
    rw [hP2, finrank_Vtail]
    exact plh_pow_two_lt_three hQ
  obtain ⟨m₂, hm₂V, hm₂⟩ := exists_mem_notMem_affine_of_sum_lt (K := K) (V := Fin 4 → K)
    Vtail ({P} : Finset (Submodule K (Fin 4 → K))) (fun T => T) (fun _ => 0)
    (by intro T hT; rw [Finset.mem_singleton] at hT; rw [hT]; exact hPV)
    (by intro T _; exact Vtail.zero_mem)
    (by rw [Finset.sum_singleton]; exact hlt1)
  have hm₂P : m₂ ∉ P := by
    have := hm₂ P (Finset.mem_singleton_self P)
    simpa using this
  have hm₂p : m₂ ∉ p := fun h => hm₂P (Submodule.mem_sup_left h)
  have hm₂0 : m₂ ≠ 0 := by
    intro h
    rw [h] at hm₂P
    exact hm₂P P.zero_mem
  have hL₂V : p ⊔ K ∙ m₂ ≤ Vtail :=
    sup_le hpV ((Submodule.span_singleton_le_iff_mem _ _).mpr hm₂V)
  have hL₂2 : finrank K ↥(p ⊔ K ∙ m₂) = 2 := by
    rw [finrank_sup_of_disjoint (Submodule.disjoint_span_singleton_of_notMem hm₂p),
      hp1, finrank_span_singleton hm₂0]
  have hL₂ok : (D13c (K := K) f).okL p (p ⊔ K ∙ m₂) := by
    refine (plh_okL_iff f hK hp1).mpr ?_
    intro hle
    have hle' : P ≤ p ⊔ K ∙ m₂ := by
      rw [hP]
      exact sup_le le_sup_left hle
    have heq : P = p ⊔ K ∙ m₂ :=
      Submodule.eq_of_le_of_finrank_eq hle' (by rw [hP2, hL₂2])
    have hm₂L : m₂ ∈ p ⊔ K ∙ m₂ :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self m₂)
    rw [← heq] at hm₂L
    exact hm₂P hm₂L
  let L₂ : Submodule K (Fin 4 → K) := p ⊔ K ∙ m₂
  have hSvol : ∑ T ∈ ({P, L₂} : Finset (Submodule K (Fin 4 → K))),
      Nat.card K ^ finrank K T = ({P, L₂} : Finset (Submodule K (Fin 4 → K))).card
        * Nat.card K ^ 2 :=
    plh_sum_vol _ (by
      intro T hT
      rw [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact hP2
      · exact hL₂2)
  have hvol2 : ∑ T ∈ ({P, L₂} : Finset (Submodule K (Fin 4 → K))),
      Nat.card K ^ finrank K T < Nat.card K ^ finrank K (Vtail : Submodule K (Fin 4 → K)) := by
    rw [hSvol, finrank_Vtail]
    calc ({P, L₂} : Finset (Submodule K (Fin 4 → K))).card * Nat.card K ^ 2
          ≤ 2 * Nat.card K ^ 2 := Nat.mul_le_mul_right _ Finset.card_le_two
      _ < Nat.card K ^ 3 := plh_two_mul_pow_lt hQ
  obtain ⟨m₃, hm₃V, hm₃⟩ := exists_mem_notMem_affine_of_sum_lt (K := K) (V := Fin 4 → K)
    Vtail ({P, L₂} : Finset (Submodule K (Fin 4 → K))) (fun T => T) (fun _ => 0)
    (by
      intro T hT
      rw [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact hPV
      · exact hL₂V)
    (by intro T _; exact Vtail.zero_mem)
    hvol2
  have hm₃P : m₃ ∉ P := by
    have := hm₃ P (Finset.mem_insert_self P {L₂})
    simpa using this
  have hm₃L₂ : m₃ ∉ L₂ := by
    have := hm₃ L₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self L₂))
    simpa using this
  have hm₃p : m₃ ∉ p := fun h => hm₃P (Submodule.mem_sup_left h)
  have hm₃0 : m₃ ≠ 0 := by
    intro h
    rw [h] at hm₃P
    exact hm₃P P.zero_mem
  have hL₃V : p ⊔ K ∙ m₃ ≤ Vtail :=
    sup_le hpV ((Submodule.span_singleton_le_iff_mem _ _).mpr hm₃V)
  have hL₃2 : finrank K ↥(p ⊔ K ∙ m₃) = 2 := by
    rw [finrank_sup_of_disjoint (Submodule.disjoint_span_singleton_of_notMem hm₃p),
      hp1, finrank_span_singleton hm₃0]
  have hL₃ok : (D13c (K := K) f).okL p (p ⊔ K ∙ m₃) := by
    refine (plh_okL_iff f hK hp1).mpr ?_
    intro hle
    have hle' : P ≤ p ⊔ K ∙ m₃ := by
      rw [hP]
      exact sup_le le_sup_left hle
    have heq : P = p ⊔ K ∙ m₃ :=
      Submodule.eq_of_le_of_finrank_eq hle' (by rw [hP2, hL₃2])
    have hm₃L : m₃ ∈ p ⊔ K ∙ m₃ :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self m₃)
    rw [← heq] at hm₃L
    exact hm₃P hm₃L
  have hne : L₂ ≠ p ⊔ K ∙ m₃ := by
    intro heq
    have hm₃L₃ : m₃ ∈ p ⊔ K ∙ m₃ :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self m₃)
    rw [← heq] at hm₃L₃
    exact hm₃L₂ hm₃L₃
  exact ⟨L₂, p ⊔ K ∙ m₃, hne, ⟨le_sup_left, hL₂V, hp1, hL₂2⟩,
    ⟨le_sup_left, hL₃V, hp1, hL₃2⟩, hL₂ok, hL₃ok⟩

private lemma plh_exists_nonrat_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (s : Finset (Submodule K (Fin 4 → K)))
    (hs : ∀ x ∈ s, BPt x ∧ sgS K f 4 x ≠ x) (hcard : s.card ≤ 6) :
    ∃ t, BPt t ∧ sgS K f 4 t ≠ t ∧ ∀ x ∈ s, ¬ t ≤ x ⊔ sgS K f 4 x := by
  classical
  have hSle : ∀ T ∈ s.image (fun x => x ⊔ sgS K f 4 x), T ≤ Vtail ∧ finrank K T = 2 := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨⟨hxV, hx1⟩, hxnt⟩ := hs x hx
    exact ⟨sup_le hxV (plh_sgS_le_Vtail f hxV),
      finrank_sup_of_ne_pts hx1 (by rw [finrank_sgS (K := K) (f := f) (n := 4) hK x]; exact hx1)
        hxnt.symm⟩
  have hcard' : (s.image (fun x => x ⊔ sgS K f 4 x)).card ≤ 6 :=
    le_trans Finset.card_image_le hcard
  obtain ⟨t, htV, ht1, htnt, hT⟩ :=
    exists_nonrat_point_avoid f hK hq (s.image (fun x => x ⊔ sgS K f 4 x)) hSle hcard'
  exact ⟨t, ⟨htV, ht1⟩, htnt,
    fun x hx => hT (x ⊔ sgS K f 4 x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

theorem a13c_nbr (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (∀ u v : Submodule K (Fin 4 → K), (∃ L, BFl u L ∧ (D13c (K := K) f).okL u L) →
      (∃ L, BFl v L ∧ (D13c (K := K) f).okL v L) →
      ∃ t, BPt t ∧ BAdj (D13c (K := K) f) u t ∧ BAdj (D13c (K := K) f) v t) ∧
    (∀ a b c d : Submodule K (Fin 4 → K), BPt a → BPt b → BPt c → BPt d →
      BAdj (D13c (K := K) f) a b → BAdj (D13c (K := K) f) b c → BAdj (D13c (K := K) f) c d →
      BAdj (D13c (K := K) f) d a →
      ∃ t, BPt t ∧ BAdj (D13c (K := K) f) a t ∧ BAdj (D13c (K := K) f) b t ∧
        BAdj (D13c (K := K) f) c t ∧ BAdj (D13c (K := K) f) d t) ∧
    (∀ u c d : Submodule K (Fin 4 → K), (∃ L, BFl u L ∧ (D13c (K := K) f).okL u L) →
      BPt c → BPt d → BAdj (D13c (K := K) f) c d →
      ∃ t, BPt t ∧ BAdj (D13c (K := K) f) u t ∧ BAdj (D13c (K := K) f) c t ∧
        BAdj (D13c (K := K) f) d t) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨Lu, huBFl, huok⟩ := hu
    obtain ⟨Lv, hvBFl, hvok⟩ := hv
    obtain ⟨hu_le, huV, hu1, -⟩ := huBFl
    obtain ⟨hv_le, hvV, hv1, -⟩ := hvBFl
    have hnu : sgS K f 4 u ≠ u := nonrat_of_okL f hK hu_le hu1 huok
    have hnv : sgS K f 4 v ≠ v := nonrat_of_okL f hK hv_le hv1 hvok
    have hs : ∀ x ∈ ({u, v} : Finset (Submodule K (Fin 4 → K))),
        BPt x ∧ sgS K f 4 x ≠ x := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨le_trans hu_le huV, hu1⟩, hnu⟩
      · exact ⟨⟨le_trans hv_le hvV, hv1⟩, hnv⟩
    have hcard : ({u, v} : Finset (Submodule K (Fin 4 → K))).card ≤ 6 := by
      have h2 : ({u, v} : Finset (Submodule K (Fin 4 → K))).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨w, hwBPt, hwnt, hw⟩ := plh_exists_nonrat_avoid f hK hq {u, v} hs hcard
    exact ⟨w, hwBPt,
      badj_a3_13c f hK ⟨le_trans hu_le huV, hu1⟩ hwBPt hnu hwnt (hw u (by simp)),
      badj_a3_13c f hK ⟨le_trans hv_le hvV, hv1⟩ hwBPt hnv hwnt (hw v (by simp))⟩
  · intro a b c d ha hb hc hd hab hbc hcd hda
    have hna : sgS K f 4 a ≠ a := plh_nonrat_of_sup f hK ha hab
    have hnb : sgS K f 4 b ≠ b := plh_nonrat_of_sup' f hK hb hab
    have hnc : sgS K f 4 c ≠ c := plh_nonrat_of_sup' f hK hc hbc
    have hnd : sgS K f 4 d ≠ d := plh_nonrat_of_sup' f hK hd hcd
    have hs : ∀ x ∈ ({a, b, c, d} : Finset (Submodule K (Fin 4 → K))),
        BPt x ∧ sgS K f 4 x ≠ x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨ha, hna⟩
      · exact ⟨hb, hnb⟩
      · exact ⟨hc, hnc⟩
      · exact ⟨hd, hnd⟩
    have hcard : ({a, b, c, d} : Finset (Submodule K (Fin 4 → K))).card ≤ 6 := by
      have := plh_card_four a b c d
      omega
    obtain ⟨w, hwBPt, hwnt, hw⟩ := plh_exists_nonrat_avoid f hK hq {a, b, c, d} hs hcard
    exact ⟨w, hwBPt,
      badj_a3_13c f hK ha hwBPt hna hwnt (hw a (by simp)),
      badj_a3_13c f hK hb hwBPt hnb hwnt (hw b (by simp)),
      badj_a3_13c f hK hc hwBPt hnc hwnt (hw c (by simp)),
      badj_a3_13c f hK hd hwBPt hnd hwnt (hw d (by simp))⟩
  · intro u c d hu hc hd hcd
    obtain ⟨Lu, huBFl, huok⟩ := hu
    obtain ⟨hu_le, huV, hu1, -⟩ := huBFl
    have hnu : sgS K f 4 u ≠ u := nonrat_of_okL f hK hu_le hu1 huok
    have hnc : sgS K f 4 c ≠ c := plh_nonrat_of_sup f hK hc hcd
    have hnd : sgS K f 4 d ≠ d := plh_nonrat_of_sup' f hK hd hcd
    have hs : ∀ x ∈ ({u, c, d} : Finset (Submodule K (Fin 4 → K))),
        BPt x ∧ sgS K f 4 x ≠ x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨le_trans hu_le huV, hu1⟩, hnu⟩
      · exact ⟨hc, hnc⟩
      · exact ⟨hd, hnd⟩
    have hcard : ({u, c, d} : Finset (Submodule K (Fin 4 → K))).card ≤ 6 := by
      have := plh_card_three u c d
      omega
    obtain ⟨w, hwBPt, hwnt, hw⟩ := plh_exists_nonrat_avoid f hK hq {u, c, d} hs hcard
    exact ⟨w, hwBPt,
      badj_a3_13c f hK ⟨le_trans hu_le huV, hu1⟩ hwBPt hnu hwnt (hw u (by simp)),
      badj_a3_13c f hK hc hwBPt hnc hwnt (hw c (by simp)),
      badj_a3_13c f hK hd hwBPt hnd hwnt (hw d (by simp))⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
