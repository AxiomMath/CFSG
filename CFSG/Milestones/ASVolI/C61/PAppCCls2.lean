module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCls2
public import CFSG.Milestones.ASVolI.C61.PAppCCls1

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Mate
open CFSG.QuasithinUnique.AppC.Mate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : Cfg T M H S L) (m : Mate S T M₀ x)
include C m

omit m in
theorem V_comm {a b : G} (ha : a ∈ conjR (blockU L) x) (hb : b ∈ conjR (blockU L) x) :
    a * b = b * a :=
  B2F.isElemAbelian_comm (V_elem (x := x) C) ha hb

omit m in
theorem V_sq {a : G} (ha : a ∈ conjR (blockU L) x) : a ^ 2 = 1 := (V_elem (x := x) C).2 a ha

omit m in
theorem pf_ne_one {v : G} (hπ : C.P.pf v = swap 0 1) : v ≠ 1 := by
  intro h
  rw [h, C.P.pf_eq (one_mem _)] at hπ
  have h1 : C.P.π ⟨1, one_mem _⟩ = 1 := map_one C.P.π
  rw [h1] at hπ
  exact absurd hπ.symm (by decide)

theorem X'_spec {v : G} (hv : v ∈ conjR (blockU L) x) (hπ : C.P.pf v = swap 0 1) :
    IsElemAbelian 2 ((blockU L ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ blockD S L) ∧
      Nat.card ↥((blockU L ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ blockD S L) =
        8 * Nat.card ↥(blockD S L) := by
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := C.hSN (Mate.V_le_S (m := m) C hv)
  have hcomm : ∀ a ∈ blockU L ⊓ Subgroup.centralizer ({v} : Set G), ∀ d ∈ blockD S L,
      a * d = d * a := fun a ha d hd => C.U_comm_D ha.1 hd
  refine ⟨B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left C.hU)
    (Mate.D_elem (m := m) C) hcomm, ?_⟩
  have h := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : (blockU L ⊓ Subgroup.centralizer ({v} : Set G)) ⊓ blockD S L = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ blockU L ⊓ blockD S L := ⟨hy.1.1, hy.2⟩
    rwa [C.U_inf_D] at this
  rw [hinf, Subgroup.card_bot, mul_one] at h
  have hc := C.P.card_fix_set ({v} : Set G) (Set.singleton_subset_iff.2 hvN)
  have hset : Nat.card {w : evenWeight 5 // ∀ y ∈ ({v} : Set G), vact (C.P.pf y) w = w} = 8 := by
    rw [← card_vfix_t1]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    simp [hπ]
  rw [hset] at hc
  rw [h, hc]

theorem Yv_isMax {v : G} (hv : v ∈ conjR (blockU L) x) (hπ : C.P.pf v = swap 0 1) :
    IsMaxElemAbelian S (Yv S L v) ∧ (Yv S L v ⊓ pCoreOf 2 H).relIndex (Yv S L v) = 2 := by
  have hvS : v ∈ S := Mate.V_le_S (m := m) C hv
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := C.hSN hvS
  have hv2 : v ^ 2 = 1 := V_sq (x := x) C hv
  obtain ⟨hXe, hXc⟩ := Mate.X'_spec (m := m) C hv hπ
  set X' := (blockU L ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ blockD S L with hX'
  have hXQ : X' ≤ pCoreOf 2 H :=
    sup_le (inf_le_left.trans C.hUQ) (C.D_le_Q)
  have hXv : ∀ a ∈ X', a * v = v * a := by
    intro a ha
    have hle : X' ≤ Subgroup.centralizer ({v} : Set G) := by
      refine sup_le inf_le_right fun d hd => ?_
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (Mate.D_comm_V (m := m) C hd hv).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) v (Set.mem_singleton v)).symm
  have hzp : Subgroup.zpowers v ≤ Subgroup.centralizer (X' : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hXv)
  have hcomm2 : ∀ a ∈ X', ∀ b ∈ Subgroup.zpowers v, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hzp hb) a ha
  have hzpe : IsElemAbelian 2 (Subgroup.zpowers v) :=
    B2F.isElemAbelian_mono (Subgroup.zpowers_le.2 hv) (V_elem (x := x) C)
  have hYe : IsElemAbelian 2 (Yv S L v) :=
    B2F.isElemAbelian_sup_of_commute hXe hzpe hcomm2
  have hinf : X' ⊓ Subgroup.zpowers v = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rcases eq_one_or_of_mem_zpowers hv2 hy.2 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      have hvQ : v ∈ pCoreOf 2 H := hXQ (h ▸ hy.1)
      have := C.pf_eq_one_of_mem_Q hvQ
      rw [hπ] at this
      exact absurd this (by decide)
  have hcardz : Nat.card ↥(Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hv2 (pf_ne_one C hπ)
  have hY := B2F.card_sup_mul_card_inf_of_commute hcomm2
  rw [hinf, Subgroup.card_bot, mul_one, hcardz, hXc] at hY
  have hYcard : Nat.card ↥(Yv S L v) = 16 * Nat.card ↥(blockD S L) := by
    show Nat.card ↥(X' ⊔ Subgroup.zpowers v) = _
    omega
  have hYS : Yv S L v ≤ S :=
    sup_le (hXQ.trans C.hQS) ((Subgroup.zpowers_le.2 hvS))
  have hmax : IsMaxElemAbelian S (Yv S L v) :=
    ⟨hYS, hYe, fun B hBS hBe => by
      obtain ⟨-, hcard, hle, -⟩ := C.aU_spec hBe hBS
      have h1 := hcard.trans (Subgroup.card_le_of_le hle)
      rw [C.card_Q] at h1
      omega⟩
  refine ⟨hmax, ?_⟩
  have hYN : Yv S L v ≤ Subgroup.normalizer (L : Set G) := hYS.trans C.hSN
  have h1 := C.P.card_im_mul hYN
  have hKQ : Yv S L v ⊓ Subgroup.centralizer (blockU L : Set G) = Yv S L v ⊓ pCoreOf 2 H := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      exact ⟨haA, by rw [← C.hQ]; exact ⟨C.hSH (hYS haA), haC⟩⟩
    · rintro ⟨haA, haQ⟩
      exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩
  rw [hKQ] at h1
  have hge : 8 * Nat.card ↥(blockD S L) ≤ Nat.card ↥(Yv S L v ⊓ pCoreOf 2 H) := by
    rw [← hXc]
    exact Subgroup.card_le_of_le (le_inf (le_sup_left : X' ≤ Yv S L v) hXQ)
  have hne : C.P.im (Yv S L v) ≠ ⊥ := by
    intro hbot
    have hv' : swap (0 : Fin 5) 1 ∈ C.P.im (Yv S L v) :=
      (C.P.mem_im_pf hYN).2 ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v), hπ⟩
    rw [hbot] at hv'
    exact absurd (Subgroup.mem_bot.1 hv') (by decide)
  have hlt : 1 < Nat.card ↥(C.P.im (Yv S L v)) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hdpos : 0 < Nat.card ↥(blockD S L) := Nat.card_pos
  rw [hYcard] at h1
  have hKle : Nat.card ↥(Yv S L v ⊓ pCoreOf 2 H) ≤ 8 * Nat.card ↥(blockD S L) := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul hlt hcon
    linarith
  have hKeq : Nat.card ↥(Yv S L v ⊓ pCoreOf 2 H) = 8 * Nat.card ↥(blockD S L) :=
    le_antisymm hKle hge
  have hidx := C5.card_eq_card_mul_relIndex
    (inf_le_left : Yv S L v ⊓ pCoreOf 2 H ≤ Yv S L v)
  rw [hYcard, hKeq] at hidx
  have h8 : 8 * Nat.card ↥(blockD S L) * 2 =
      8 * Nat.card ↥(blockD S L) * (Yv S L v ⊓ pCoreOf 2 H).relIndex (Yv S L v) := by
    rw [← hidx]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h8).symm

theorem fix_mem {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 0 1) {w : G} (hw : w ∈ conjR (blockU L) x)
    (hπ : C.P.pf w = swap 0 1) {u : G} (hu : u ∈ blockU L) (hc : w * u = u * w) : u ∈ A := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans C.hSN
  have hwN := C.hSN (Mate.V_le_S (m := m) C hw)
  have h1 : vact (C.P.pf w) (C.P.bf u) = C.P.bf u := (C.P.comm_iff hwN hu).1 hc
  have : u ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyN := hAN hy
    have hpy : C.P.pf y ∈ C.P.im A := (C.P.mem_im_pf hAN).2 ⟨y, hy, rfl⟩
    rcases (hty _).1 hpy with h | h
    · exact C.Q_comm_U (C.mem_Q_of_pf_eq_one (hA.1 hy) h) hu
    · exact (C.P.comm_iff hyN hu).2 (by rw [h, ← hπ]; exact h1)
  exact Mate.fixU_le_of_isMax (m := m) C hA this

theorem Yv_le {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 0 1) {v : G} (hv : v ∈ conjR (blockU L) x)
    (hπ : C.P.pf v = swap 0 1) : Yv S L v ≤ A := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans C.hSN
  have hD := Mate.D_le_of_isMax (m := m) C hA
  have hvA : v ∈ A := by
    have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im A := (hty _).2 (Or.inr rfl)
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 ht1
    obtain ⟨v', hv', u', hu', d', hd', rfl, hpv'⟩ :=
      Mate.exists_vud (m := m) C (hA.1 haA) (by rw [hpa]; exact t1_mem_Eset)
    have hvu : v' * u' ∈ A := by
      have := mul_mem haA (inv_mem (hD hd'))
      simpa [mul_assoc] using this
    have hpv'1 : C.P.pf v' = swap 0 1 := by rw [hpv', hpa]
    have hcom : v' * u' = u' * v' :=
      comm_of_sq (hA.2.1.2 _ hvu) (V_sq (x := x) C hv') (C.hU.2 u' hu')
    have hu'A : u' ∈ A := Mate.fix_mem (m := m) C hA hty hv' hpv'1 hu' hcom
    have hv'A : v' ∈ A := by
      have := mul_mem hvu (inv_mem hu'A)
      simpa [mul_assoc] using this
    have hwV : v * v'⁻¹ ∈ conjR (blockU L) x := by
      refine mul_mem hv (inv_mem hv')
    have hvS := Mate.V_le_S (m := m) C hv
    have hv'S := Mate.V_le_S (m := m) C hv'
    have hw1 : C.P.pf (v * v'⁻¹) = 1 := by
      rw [C.P.pf_mul (C.hSN hvS) (inv_mem (C.hSN hv'S)), C.P.pf_inv (C.hSN hv'S), hπ, hpv'1,
        mul_inv_cancel]
    have hwQ := C.mem_Q_of_pf_eq_one (mul_mem hvS (inv_mem hv'S)) hw1
    have hwU : v * v'⁻¹ ∈ blockU L := Mate.V_inf_Q_le_U (m := m) C hwV hwQ
    have hwC : v * v'⁻¹ ∈ Subgroup.centralizer (conjR (blockU L) x : Set G) := by
      have : v * v'⁻¹ ∈ blockU L ⊓ conjR (blockU L) x := ⟨hwU, hwV⟩
      rw [← (Mate.cent_U_V (m := m) C).1] at this
      exact this.2
    have hcw : v' * (v * v'⁻¹) = (v * v'⁻¹) * v' := Subgroup.mem_centralizer_iff.1 hwC v' hv'
    have hwA : v * v'⁻¹ ∈ A := Mate.fix_mem (m := m) C hA hty hv' hpv'1 hwU hcw
    have := mul_mem hwA hv'A
    simpa [mul_assoc] using this
  refine sup_le (sup_le (fun u hu => ?_) hD) (Subgroup.zpowers_le.2 hvA)
  exact Mate.fix_mem (m := m) C hA hty hv hπ hu.1 (Subgroup.mem_centralizer_iff.1 hu.2 v (Set.mem_singleton v))

theorem eq_Yv_of_type_t1 {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 0 1) {v : G} (hv : v ∈ conjR (blockU L) x)
    (hπ : C.P.pf v = swap 0 1) : A = Yv S L v := by
  have hle := Mate.Yv_le (m := m) C hA hty hv hπ
  have hcard : Nat.card ↥A ≤ Nat.card ↥(Yv S L v) := by
    rw [Mate.card_eq_Q (m := m) C hA, Mate.card_eq_Q (m := m) C (Mate.Yv_isMax (m := m) C hv hπ).1]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end Mate

end CFSG.QuasithinUnique.burnsideC56_P.AppC
