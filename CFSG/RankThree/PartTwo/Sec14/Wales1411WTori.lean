module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WDefs
import CFSG.RankThree.PartTwo.Sec14.Wales1411WPoint
import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

open CFSG.GH74.GLS.Stage2.Bender.Thm1.L64 (commutator_le_left_of_le_normalizer
  le_commutator_sup_inf_centralizer)
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

theorem mem_normalizer_of_map_conj_le {S : Subgroup M} {n : M}
    (h : S.map (MulAut.conj n).toMonoidHom ≤ S) : n ∈ Subgroup.normalizer (S : Set M) :=
  Subgroup.mem_normalizer_fintype fun s hs => h ⟨s, hs, rfl⟩

theorem map_conj_eq_self {S : Subgroup M} {n : M} (hn : n ∈ Subgroup.normalizer (S : Set M)) :
    S.map (MulAut.conj n).toMonoidHom = S := by
  refine le_antisymm ?_ fun s hs => ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn s).mp hs
  · refine ⟨n⁻¹ * s * n, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) s).mp hs
    simpa using this

theorem le_normalizer_commutator {S E : Subgroup M}
    (hES : E ≤ Subgroup.normalizer (S : Set M)) :
    E ≤ Subgroup.normalizer ((⁅S, E⁆ : Subgroup M) : Set M) := by
  intro ε hε
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_commutator, map_conj_eq_self (hES hε),
    map_conj_eq_self (Subgroup.le_normalizer hε)]

theorem invTwo_map_conj {E H U : Subgroup M} (hU : InvTwo E H U) {n : M}
    (hn : n ∈ H ⊓ Subgroup.normalizer (E : Set M)) :
    InvTwo E H (U.map (MulAut.conj n).toMonoidHom) := by
  obtain ⟨hUH, hEU, hU2⟩ := hU
  refine ⟨?_, ?_, hU2.map _⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hnH := (Subgroup.mem_inf.mp hn).1
    exact mul_mem (mul_mem hnH (hUH hu)) (inv_mem hnH)
  · intro ε hε
    refine mem_normalizer_of_map_conj_le ?_
    have hε' : n⁻¹ * ε * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (Subgroup.mem_inf.mp hn).2) ε).mp hε
      simpa using this
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hu' : (n⁻¹ * ε * n) * u * (n⁻¹ * ε * n)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hEU hε') u).mp hu
    refine ⟨_, hu', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem maximal_invTwo_map_conj {E H S : Subgroup M} (hS : Maximal (InvTwo E H) S) {n : M}
    (hn : n ∈ H ⊓ Subgroup.normalizer (E : Set M)) :
    Maximal (InvTwo E H) (S.map (MulAut.conj n).toMonoidHom) := by
  refine ⟨invTwo_map_conj hS.prop hn, fun U hU hle => ?_⟩
  have hninv : n⁻¹ ∈ H ⊓ Subgroup.normalizer (E : Set M) := inv_mem hn
  have hU' := invTwo_map_conj hU hninv
  have hSU : S ≤ U.map (MulAut.conj n⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj n⁻¹).toMonoidHom) hle
    rwa [Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one] at this
  have := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) (hS.2 hU' hSU)
  rwa [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one] at this

theorem sup_le_of_commutator_le {E H R V Q : Subgroup M} (hE3 : IsPGroup 3 E)
    (hEH : E ≤ Subgroup.normalizer (H : Set M)) (hR : Maximal (InvTwo E H) R)
    (hV2 : IsPGroup 2 V) (hEV : E ≤ Subgroup.normalizer (V : Set M)) (hRV : ⁅R, E⁆ ≤ V)
    (hQ2 : IsPGroup 2 Q) (hRQ : R ⊓ Subgroup.centralizer (E : Set M) ≤ Q)
    (hQC : Q ≤ H ⊓ Subgroup.centralizer (E : Set M))
    (hQB : Q ≤ Subgroup.normalizer ((V ⊓ H : Subgroup M) : Set M)) :
    V ⊓ H ⊔ Q ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRH, hER, hR2⟩ := hR.prop
  have hB2 : IsPGroup 2 ↥(V ⊓ H) := hV2.to_le inf_le_left
  have hEB : E ≤ Subgroup.normalizer ((V ⊓ H : Subgroup M) : Set M) :=
    Late.le_normalizer_inf hEV hEH
  have hEQ : E ≤ Subgroup.normalizer (Q : Set M) := by
    intro ε hε
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have hqε : ε * q = q * ε :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQC hq)).2 ε hε
    rw [hqε, mul_inv_cancel_right]
    exact hq
  have hinv : InvTwo E H (V ⊓ H ⊔ Q) :=
    ⟨sup_le inf_le_right ((hQC.trans inf_le_left)), le_normalizer_sup_of_le hEB hEQ,
      IsPGroup.to_sup_of_normal_left' hB2 hQ2 hQB⟩
  refine hR.2 hinv ?_
  have hR3 : ¬ 3 ∣ Nat.card R := not_three_dvd_card_of_isPGroup hR2
  refine (le_commutator_sup_inf_centralizer Nat.prime_three hE3 hER hR3).trans (sup_le ?_ ?_)
  · exact (le_inf hRV ((commutator_le_left_of_le_normalizer hER).trans hRH)).trans le_sup_left
  · exact hRQ.trans le_sup_right

theorem exists_conj_of_commutator_le {E H S T V : Subgroup M} (hE3 : IsPGroup 3 E)
    (hEH : E ≤ Subgroup.normalizer (H : Set M))
    (hS : Maximal (InvTwo E H) S) (hT : Maximal (InvTwo E H) T)
    (hV2 : IsPGroup 2 V) (hEV : E ≤ Subgroup.normalizer (V : Set M))
    (hCV : H ⊓ Subgroup.centralizer (E : Set M) ≤ Subgroup.normalizer (V : Set M))
    (hSV : ⁅S, E⁆ ≤ V) (hTV : ⁅T, E⁆ ≤ V) :
    ∃ x ∈ H ⊓ Subgroup.centralizer (E : Set M), T = S.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := H ⊓ Subgroup.centralizer (E : Set M) with hC
  set B := V ⊓ H with hB
  have hCB : C ≤ Subgroup.normalizer (B : Set M) :=
    Late.le_normalizer_inf hCV (inf_le_left.trans Subgroup.le_normalizer)
  set D := C ⊓ Subgroup.normalizer (B : Set M) with hD
  have hpart : ∀ R : Subgroup M, Maximal (InvTwo E H) R → ⁅R, E⁆ ≤ V →
      R ⊓ Subgroup.centralizer (E : Set M) ≤ D ∧
      IsPGroup 2 ↥(R ⊓ Subgroup.centralizer (E : Set M)) ∧
      (∀ Q : Subgroup M, R ⊓ Subgroup.centralizer (E : Set M) ≤ Q → Q ≤ D → IsPGroup 2 Q →
        Q = R ⊓ Subgroup.centralizer (E : Set M)) ∧
      R = B ⊔ R ⊓ Subgroup.centralizer (E : Set M) := by
    intro R hR hRV
    have hRC : R ⊓ Subgroup.centralizer (E : Set M) ≤ C :=
      inf_le_inf_right _ hR.prop.1
    have hRD : R ⊓ Subgroup.centralizer (E : Set M) ≤ D := le_inf hRC (hRC.trans hCB)
    have hR2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer (E : Set M)) :=
      hR.prop.2.2.to_le inf_le_left
    have hle := fun Q (h1 : R ⊓ Subgroup.centralizer (E : Set M) ≤ Q) (h2 : Q ≤ D)
        (h3 : IsPGroup 2 Q) =>
      sup_le_of_commutator_le hE3 hEH hR hV2 hEV hRV h3 h1 (h2.trans inf_le_left)
        (h2.trans inf_le_right)
    refine ⟨hRD, hR2, fun Q h1 h2 h3 => le_antisymm ?_ h1, ?_⟩
    · exact le_inf ((le_sup_right.trans (hle Q h1 h2 h3)))
        ((h2.trans inf_le_left).trans inf_le_right)
    · refine le_antisymm ?_ (hle _ le_rfl hRD hR2)
      have hR3 : ¬ 3 ∣ Nat.card R := not_three_dvd_card_of_isPGroup hR.prop.2.2
      refine (le_commutator_sup_inf_centralizer Nat.prime_three hE3 hR.prop.2.1 hR3).trans
        (sup_le_sup_right ?_ _)
      exact le_inf hRV ((commutator_le_left_of_le_normalizer hR.prop.2.1).trans hR.prop.1)
  obtain ⟨hSD, hS2, hSmax, hSeq⟩ := hpart S hS hSV
  obtain ⟨hTD, hT2, hTmax, hTeq⟩ := hpart T hT hTV
  obtain ⟨x, hx, hxS⟩ := exists_mem_map_conj_eq_of_maximal_pGroup hTD hT2
    (fun Q h1 h2 h3 => hTmax Q h1 h2 h3) hSD hS2 (fun Q h1 h2 h3 => hSmax Q h1 h2 h3)
  refine ⟨x, (Subgroup.mem_inf.mp hx).1, ?_⟩
  rw [hTeq, ← hxS]
  conv_rhs => rw [hSeq]
  rw [Subgroup.map_sup, map_conj_eq_self (Subgroup.mem_inf.mp hx).2]

theorem etrans2_of_tori {N E : Subgroup M} (U : M → Subgroup M) (hE3 : IsPGroup 3 E)
    (hcomm : ∀ m : M, ∀ ε ∈ E, ⁅m, ε⁆ ∈ N)
    (hU2 : ∀ e ∈ E, IsPGroup 2 (U e))
    (hUE : ∀ e ∈ E, E ≤ Subgroup.normalizer (U e : Set M))
    (hUC : ∀ e ∈ E, Subgroup.centralizer (E : Set M) ≤ Subgroup.normalizer (U e : Set M))
    (h1 : ∀ W : Subgroup M, W ≤ N → IsPGroup 2 W → E ≤ Subgroup.normalizer (W : Set M) →
      W ≠ ⊥ → ∃ e ∈ E, W ≤ U e)
    (h2 : ∀ e ∈ E, ∀ e' ∈ E, ∀ W W' : Subgroup M, W ≠ ⊥ → W' ≠ ⊥ → W ≤ U e → W' ≤ U e' →
      E ≤ Subgroup.normalizer (W : Set M) → E ≤ Subgroup.normalizer (W' : Set M) →
      ∃ n ∈ (W ⊔ W') ⊓ Subgroup.normalizer (E : Set M),
        (U e).map (MulAut.conj n).toMonoidHom = U e') :
    ETrans2 M E := by
  intro S T hS hT
  set H := S ⊔ T with hH
  have hEH : E ≤ Subgroup.normalizer (H : Set M) := le_normalizer_sup_of_le hS.prop.2.1 hT.prop.2.1
  have hCN : H ⊓ Subgroup.centralizer (E : Set M) ≤ Subgroup.normalizer (E : Set M) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hcm : ∀ R : Subgroup M, Maximal (InvTwo E H) R →
      ⁅R, E⁆ ≤ N ∧ ⁅R, E⁆ ≤ R ∧ IsPGroup 2 ↥(⁅R, E⁆ : Subgroup M) ∧
        E ≤ Subgroup.normalizer ((⁅R, E⁆ : Subgroup M) : Set M) := by
    intro R hR
    have hRR := commutator_le_left_of_le_normalizer hR.prop.2.1
    exact ⟨Subgroup.commutator_le.mpr fun r _ ε hε => hcomm r ε hε, hRR,
      hR.prop.2.2.to_le hRR, le_normalizer_commutator hR.prop.2.1⟩
  obtain ⟨hSN, hSS, hS2, hES⟩ := hcm S hS
  obtain ⟨hTN, hTT, hT2, hET⟩ := hcm T hT
  have hfin : ∀ (V : Subgroup M), IsPGroup 2 V → E ≤ Subgroup.normalizer (V : Set M) →
      Subgroup.centralizer (E : Set M) ≤ Subgroup.normalizer (V : Set M) →
      ⁅S, E⁆ ≤ V → ⁅T, E⁆ ≤ V →
      ∃ n ∈ H ⊓ Subgroup.normalizer (E : Set M), T = S.map (MulAut.conj n).toMonoidHom := by
    intro V hV2 hEV hCV hSV hTV
    obtain ⟨x, hx, hxT⟩ := exists_conj_of_commutator_le hE3 hEH hS hT hV2 hEV
      (inf_le_right.trans hCV) hSV hTV
    exact ⟨x, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hCN hx⟩, hxT⟩
  by_cases hS0 : ⁅S, E⁆ = ⊥
  · by_cases hT0 : ⁅T, E⁆ = ⊥
    · refine hfin ⊥ IsPGroup.of_bot ?_ ?_ hS0.le hT0.le
      · intro ε _
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_bot, Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro h
          have := congrArg (fun y => ε⁻¹ * y * ε) h
          simpa [mul_assoc] using this
      · intro ε _
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_bot, Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro h
          have := congrArg (fun y => ε⁻¹ * y * ε) h
          simpa [mul_assoc] using this
    · obtain ⟨e', he'E, he'⟩ := h1 _ hTN hT2 hET hT0
      exact hfin (U e') (hU2 e' he'E) (hUE e' he'E) (hUC e' he'E) (hS0 ▸ bot_le) he'
  · obtain ⟨e, he, hSe⟩ := h1 _ hSN hS2 hES hS0
    by_cases hT0 : ⁅T, E⁆ = ⊥
    · exact hfin (U e) (hU2 e he) (hUE e he) (hUC e he) hSe (hT0 ▸ bot_le)
    · obtain ⟨e', he', hTe'⟩ := h1 _ hTN hT2 hET hT0
      obtain ⟨n, hn, hnU⟩ := h2 e he e' he' _ _ hS0 hT0 hSe hTe' hES hET
      have hnH : n ∈ H ⊓ Subgroup.normalizer (E : Set M) :=
        Subgroup.mem_inf.mpr ⟨sup_le_sup hSS hTT (Subgroup.mem_inf.mp hn).1,
          (Subgroup.mem_inf.mp hn).2⟩
      have hS' := maximal_invTwo_map_conj hS hnH
      have hS'V : ⁅S.map (MulAut.conj n).toMonoidHom, E⁆ ≤ U e' := by
        have hEn : E.map (MulAut.conj n).toMonoidHom = E :=
          map_conj_eq_self (Subgroup.mem_inf.mp hnH).2
        calc ⁅S.map (MulAut.conj n).toMonoidHom, E⁆
            = ⁅S.map (MulAut.conj n).toMonoidHom, E.map (MulAut.conj n).toMonoidHom⁆ := by
              rw [hEn]
          _ = (⁅S, E⁆).map (MulAut.conj n).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
          _ ≤ (U e).map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hSe
          _ = U e' := hnU
      obtain ⟨x, hx, hxT⟩ := exists_conj_of_commutator_le hE3 hEH hS' hT (hU2 e' he')
        (hUE e' he') (inf_le_right.trans (hUC e' he')) hS'V hTe'
      refine ⟨x * n, mul_mem (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hCN hx⟩) hnH,
        ?_⟩
      rw [hxT, Late.map_conj_map_conj]

end CFSG.RankThree.PartTwo.Sec14.Wales1411W
