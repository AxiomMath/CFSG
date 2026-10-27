module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Track
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Background.RonanF13Hall
import CFSG.Quasithin.Recognition.Stroth.Str83Reflection
import CFSG.Quasithin.Recognition.Stroth.Str83G5Reg
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.ClassicalInvolution.Balance.BootstrapFunctor

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Frame (L1 L2 S : Subgroup G) (a f : ℕ) : Prop where
  hF : F112HypW L1 L2 S
  hS : (S ⊓ L1) ⊔ (S ⊓ L2) = S
  hN : bigB L1 L2 S ≤ normalizer (S : Set G)
  ha : 1 ≤ a
  hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)
  hf : 2 ≤ f
  hL2 : IsL2Quot f (oTwoQuot ↥L2)

theorem exists_frame {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (hS : (S ⊓ L1) ⊔ (S ⊓ L2) = S)
    (hN : bigB L1 L2 S ≤ normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hB2 : VBig L2) (hL2 : VL2 L2) :
    ∃ f, Frame L1 L2 S a f := by
  obtain ⟨f, hf⟩ := hL2
  exact ⟨f, hF, hS, hN, ha, hSz, two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hf, hf⟩

structure Track (L1 L2 S : Subgroup G) : Type where
  D1 : Subgroup G
  D2 : Subgroup G
  hD1hall : RonanF13.HallTwoPrime D1 (borelOf L1 S)
  hD2hall : RonanF13.HallTwoPrime D2 (borelOf L2 S)
  hD1sup : borelOf L1 S = (S ⊓ L1) ⊔ D1
  hD2sup : borelOf L2 S = (S ⊓ L2) ⊔ D2
  hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x
  hBsplit : bigB L1 L2 S = S ⊔ D1 ⊔ D2
  hHall : RonanF13.HallTwoPrime (D1 ⊔ D2) (bigB L1 L2 S)
  hdelta₁ : ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1, (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1
  hdelta₂ : ∀ d ∈ D1, ∃ δ ∈ D2, ∀ l ∈ L2, (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2
  x₁ : G
  x₂ : G
  hx₁inv : ∀ d ∈ D1, x₁ * d * x₁⁻¹ = d⁻¹
  hx₂inv : ∀ d ∈ D2, x₂ * d * x₂⁻¹ = d⁻¹
  hx₁cent : ∀ h ∈ D1 ⊔ D2, (∀ l ∈ L1, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → x₁ * h * x₁⁻¹ = h
  hx₂cent : ∀ h ∈ D1 ⊔ D2, (∀ l ∈ L2, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x₂ * h * x₂⁻¹ = h
  track : TrackData (P1 L1 L2 S) (P2 L1 L2 S) (D1 ⊔ D2) x₁ x₂

theorem Frame.nonempty_track {L1 L2 S : Subgroup G} {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : Nonempty (Track L1 L2 S) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, -, hN, ha, hSz, hf, hL2⟩ := hfr
  obtain ⟨D1, D2, hD1hall, hD2hall, hD1sup, hD2sup, hcomm, hBsplit, hdelta₁⟩ :=
    str83_exists_cartan_delta hF.1 ha hSz
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 := BenderType.linear f hf (Classical.choice hL2)
  have hKB : D1 ⊔ D2 ≤ bigB L1 L2 S := by
    rw [hBsplit]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hodd : Odd (Nat.card ↥(D1 ⊔ D2)) :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.odd_card_sup_of_le_normalizer
      (fun x hx => (Subgroup.centralizer_le_normalizer _)
        (Subgroup.mem_centralizer_iff.mpr fun z hz => (hcomm x hx z hz).symm))
      hD1hall.2.1 hD2hall.2.1
  have hHall : RonanF13.HallTwoPrime (D1 ⊔ D2) (bigB L1 L2 S) := by
    have hsup : (D1 ⊔ D2) ⊔ S = bigB L1 L2 S := by
      rw [hBsplit, sup_assoc S D1 D2, sup_comm S]
    obtain ⟨n, hn⟩ := hF.1.h1.pgroup.exists_card_eq
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer (hKB.trans hN)
    rw [C5.card_eq_card_mul_relIndex (le_sup_left : D1 ⊔ D2 ≤ (D1 ⊔ D2) ⊔ S), hn] at h1
    have h3 : (D1 ⊔ D2).relIndex ((D1 ⊔ D2) ⊔ S) * Nat.card ↥((D1 ⊔ D2) ⊓ S) = 2 ^ n := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(D1 ⊔ D2)))
      rw [← h1]
      ring
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h3)
    exact ⟨hKB, hodd, j, by rw [← hsup]; exact hj⟩
  have hdelta₂ : ∀ d ∈ D1, ∃ δ ∈ D2, ∀ l ∈ L2,
      (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
    intro d hd
    have hF' : F112HypW L2 L1 S := F112HypW.symm hF
    have hR' : Hyp111R L2 L1 S := Hyp111R.of_hyp111 rankOneListedFacts hF'.1
    have hD1B : D1 ≤ bigB L2 L1 S := by
      rw [bigB_comm]
      exact hD1hall.1.trans (le_sup_left.trans le_sup_left)
    exact exists_commutator_lift hF'.1 hR' hD2hall hD2sup hD1B
      (fun y hy z hz => (hcomm z hz y hy).symm) hBt2
      (fun Q t ht htQ σ hσQ hσD => BenderType.aut_eq_conj_cartan_linear hBt2 Q ht htQ σ hσQ hσD) hd
  obtain ⟨x₁, hx₁, hx₁B, hx₁map, hx₁inv, hx₁cent⟩ :=
    f112_exists_reflection_left hF hN ha hSz hf hL2 hD1hall hD2hall hD1sup hD2sup hcomm hHall
  obtain ⟨x₂, hx₂, hx₂B, hx₂map, hx₂inv, hx₂cent⟩ :=
    f112_exists_reflection_right hF hN ha hSz hf hL2 hD1hall hD2hall hD1sup hD2sup hcomm hHall
  have hc1 := (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow hD1hall hD1sup hBt1).1
  have hc2 := (card_isCyclic_of_hallTwoPrime hF.1.h2.sylow hD2hall hD2sup hBt2).1
  have hq : 4 ≤ 2 ^ (2 * a + 1) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨⟨d₁, hd₁⟩, hd₁1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot D1).mp (by omega))
  obtain ⟨⟨d₂, hd₂⟩, hd₂1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot D2).mp (by omega))
  have hd₁Q : d₁ ∉ pCoreOf 2 L1 := fun h => hd₁1 (Subtype.ext (Subgroup.disjoint_def.mp
    (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hD1hall.2.1.not_two_dvd_nat
      (pCoreOf_isPGroup 2 L1)) hd₁ h))
  have hd₂Q : d₂ ∉ pCoreOf 2 L2 := fun h => hd₂1 (Subtype.ext (Subgroup.disjoint_def.mp
    (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hD2hall.2.1.not_two_dvd_nat
      (pCoreOf_isPGroup 2 L2)) hd₂ h))
  have T : TrackData (P1 L1 L2 S) (P2 L1 L2 S) (D1 ⊔ D2) x₁ x₂ :=
    trackData_bigB hF.1 ha hSz hf hL2 hKB (mem_sup_left hd₁)
      (F1.borelOf_le L1 S (hD1hall.1 hd₁)) hd₁Q (mem_sup_right hd₂)
      (F1.borelOf_le L2 S (hD2hall.1 hd₂)) hd₂Q
      hx₁ hx₁B (mem_normalizer_iff_map_conj_eq.mpr hx₁map)
      hx₂ hx₂B (mem_normalizer_iff_map_conj_eq.mpr hx₂map)
  exact ⟨⟨D1, D2, hD1hall, hD2hall, hD1sup, hD2sup, hcomm, hBsplit, hHall, hdelta₁, hdelta₂,
    x₁, x₂, hx₁inv, hx₂inv, hx₁cent, hx₂cent, T⟩⟩

private def edgeElt (x₁ x₂ : G) (u : ℤ) : G :=
  if Even u then (x₂ * x₁) ^ (u / 2) else (x₂ * x₁) ^ (u / 2) * x₂

private theorem edgeElt_mem {N : Subgroup G} {x₁ x₂ : G} (h₁ : x₁ ∈ N) (h₂ : x₂ ∈ N) (u : ℤ) :
    edgeElt x₁ x₂ u ∈ N := by
  unfold edgeElt
  split_ifs
  · exact zpow_mem (mul_mem h₂ h₁) _
  · exact mul_mem (zpow_mem (mul_mem h₂ h₁) _) h₂

private theorem map_conj_inf (A B : Subgroup G) (g : G) :
    (A ⊓ B).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊓ B.map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [mem_inf, mem_map_conj_iff]

private theorem map_conj_eq_of_mem {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

private theorem qv_edge {R₁ R₂ : Subgroup G} {x₁ x₂ : G} (h₁ : x₁ ∈ normalizer (R₁ : Set G))
    (h₂ : x₂ ∈ normalizer (R₂ : Set G)) (u : ℤ) :
    qv R₁ R₂ x₁ x₂ u = (trackPar R₁ R₂ u).map (MulAut.conj (edgeElt x₁ x₂ u)).toMonoidHom ∧
      qv R₁ R₂ x₁ x₂ (u + 1) =
        (trackPar R₁ R₂ (u + 1)).map (MulAut.conj (edgeElt x₁ x₂ u)).toMonoidHom := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' u
  · have hp0 : trackPar R₁ R₂ (2 * k) = R₁ := if_pos (even_two_mul k)
    have hp1 : trackPar R₁ R₂ (2 * k + 1) = R₂ := if_neg (Int.not_even_two_mul_add_one k)
    have he : edgeElt x₁ x₂ (2 * k) = (x₂ * x₁) ^ k := by
      rw [edgeElt, if_pos (even_two_mul k), show 2 * k / 2 = k by omega]
    rw [qv, qv, trackElt, trackElt, he, hp0, hp1, show 2 * k / 2 = k by omega,
      show (2 * k + 1) / 2 = k by omega]
    exact ⟨rfl, rfl⟩
  · have hp1 : trackPar R₁ R₂ (2 * k + 1) = R₂ := if_neg (Int.not_even_two_mul_add_one k)
    have hp2 : trackPar R₁ R₂ (2 * k + 1 + 1) = R₁ :=
      if_pos (show Even (2 * k + 1 + 1) from ⟨k + 1, by ring⟩)
    have he : edgeElt x₁ x₂ (2 * k + 1) = (x₂ * x₁) ^ k * x₂ := by
      rw [edgeElt, if_neg (Int.not_even_two_mul_add_one k), show (2 * k + 1) / 2 = k by omega]
    rw [qv, qv, trackElt, trackElt, he, hp1, hp2, show (2 * k + 1) / 2 = k by omega,
      show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_conj_map_conj R₂ x₂ ((x₂ * x₁) ^ k), map_conj_eq_of_mem h₂]
    · rw [zpow_add_one, ← mul_assoc, ← Subgroup.map_conj_map_conj R₁ x₁ ((x₂ * x₁) ^ k * x₂),
        map_conj_eq_of_mem h₁]

private theorem trackPar_inf_succ (P₁ P₂ : Subgroup G) (u : ℤ) :
    trackPar P₁ P₂ u ⊓ trackPar P₁ P₂ (u + 1) = P₁ ⊓ P₂ := by
  unfold trackPar
  by_cases hu : Even u
  · rw [if_pos hu, if_neg fun h => Int.even_add_one.mp h hu]
  · rw [if_neg hu, if_pos (Int.even_add_one.mpr hu), inf_comm]

private theorem qv_zero (R₁ R₂ : Subgroup G) (x₁ x₂ : G) : qv R₁ R₂ x₁ x₂ 0 = R₁ := by
  ext y
  rw [mem_qv_iff, trackElt, trackPar, if_pos (show Even (0 : ℤ) from ⟨0, rfl⟩),
    show (0 : ℤ) / 2 = 0 by norm_num,
    zpow_zero, inv_one, one_mul, mul_one]

private theorem qv_one (R₁ R₂ : Subgroup G) (x₁ x₂ : G) : qv R₁ R₂ x₁ x₂ 1 = R₂ := by
  ext y
  rw [mem_qv_iff, trackElt, trackPar, if_neg Int.not_even_one, show (1 : ℤ) / 2 = 0 by norm_num,
    zpow_zero, inv_one, one_mul, mul_one]

private theorem pCoreOf_bigB {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hN : bigB L1 L2 S ≤ normalizer (S : Set G)) :
    pCoreOf 2 (bigB L1 L2 S) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := F1.isSylowTwoOf_bigB_of_normal (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hN
  exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hSyl)
    (le_pCoreOf_of_le_normalizer 2 hSyl.1 hN hSyl.2.1)

private theorem eq_pCoreOf_sup_of_le {E W K : Subgroup G} (hE : E = pCoreOf 2 E ⊔ K)
    (hKW : K ≤ W) (hWE : W ≤ E) : W = pCoreOf 2 W ⊔ K := by
  refine le_antisymm (fun w hw => ?_) (sup_le (pCoreOf_le 2 W) hKW)
  have hKN : K ≤ normalizer (pCoreOf 2 E : Set G) :=
    (hKW.trans hWE).trans (le_normalizer_pCoreOf 2 E)
  have hwE : w ∈ pCoreOf 2 E ⊔ K := by
    rw [← hE]
    exact hWE hw
  obtain ⟨s, hs, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp hwE
  have hsW : s ∈ W := by
    have := mul_mem hw (inv_mem (hKW hk))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (F7.pCoreOf_inf_le hWE ⟨hs, hsW⟩)) (mem_sup_right hk)

private theorem le_pCoreOf_of_eq_sup {W K X : Subgroup G} (hW : W = pCoreOf 2 W ⊔ K)
    (hK : Odd (Nat.card K)) (hX : IsPGroup 2 X) (hXW : X ≤ W) : X ≤ pCoreOf 2 W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKW : K ≤ W := (le_sup_right : K ≤ pCoreOf 2 W ⊔ K).trans hW.symm.le
  have hKN : K ≤ normalizer (pCoreOf 2 W : Set G) := hKW.trans (le_normalizer_pCoreOf 2 W)
  have hidx : (pCoreOf 2 W).relIndex W = (pCoreOf 2 W).relIndex K := by
    have h := C5.relIndex_sup_eq_of_le_normalizer (A := K) (B := pCoreOf 2 W) hKN
    rwa [sup_comm K (pCoreOf 2 W), ← hW] at h
  have hodd : ¬ 2 ∣ ((pCoreOf 2 W).subgroupOf W).index := by
    intro h2
    have h2' : 2 ∣ (pCoreOf 2 W).relIndex K := by
      rw [← hidx]
      exact h2
    exact (Nat.not_even_iff_odd.mpr hK)
      (even_iff_two_dvd.mpr (h2'.trans (Subgroup.relIndex_dvd_card _ _)))
  have hn : ((pCoreOf 2 W).subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 W)).mpr
      (le_normalizer_pCoreOf 2 W)
  exact F7.le_of_normal_sylow ⟨pCoreOf_le 2 W, pCoreOf_isPGroup 2 W, hodd⟩ hn hXW hX

private theorem relIndex_Q1 {L1 L2 S : Subgroup G} {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (Q1 L1 L2 S).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨hF, -, hB, ha, ⟨e⟩, -, -⟩ := hfr
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨e⟩⟩)
  let Q : Subgroup G := Q1 L1 L2 S
  let P : Subgroup G := P1 L1 L2 S
  let S1 : Subgroup G := S ⊓ L1
  change Q.relIndex S = (2 ^ (2 * a + 1)) ^ 2
  have hS1P : S1 ≤ P := (inf_le_right : S ⊓ L1 ≤ L1).trans le_sup_left
  have hS1N : S1 ≤ normalizer (Q : Set G) := hS1P.trans (le_normalizer_pCoreOf 2 P)
  have hsup : S1 ⊔ Q = S := hS1.symm
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    have h := C5.relIndex_sup_eq_of_le_normalizer (A := S1) (B := Q) hS1N
    rwa [hsup] at h
  rw [hrel, ← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L1 := by
    have h1 : Q ⊓ S1 = L1 ⊓ Q := by
      change Q ⊓ (S ⊓ L1) = L1 ⊓ Q
      rw [inf_comm Q (S ⊓ L1), inf_assoc,
        inf_eq_right.mpr (show L1 ⊓ Q ≤ S from inf_le_right.trans hQ1S)]
    rw [h1]
    exact str86_inf_p1_q1 (L1 := L1) (L2 := L2) (S := S) hF
  rw [hinf]
  exact relIndex_pCoreOf_sylow_sz ha e hF.1.h1.sylow

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

abbrev K : Subgroup G := t.D1 ⊔ t.D2

abbrev Gv (i : ℤ) : Subgroup G := qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i

abbrev Gw (a b : ℤ) : Subgroup G := win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ a b

abbrev Qv (i : ℤ) : Subgroup G := qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ i

abbrev Zv (i : ℤ) : Subgroup G := qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ i

abbrev GT : Subgroup G := ⨅ i : ℤ, t.Gv i

theorem K_inf_eq_bot {a f : ℕ} (hfr : Frame L1 L2 S a f) : t.K ⊓ S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hfr.hF.1.h1.pgroup.exists_card_eq
  apply Subgroup.inf_eq_bot_of_coprime
  rw [hn]
  exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr t.hHall.2.1)

theorem sup_K_eq_bigB : S ⊔ t.K = bigB L1 L2 S :=
  (t.hBsplit.trans (sup_assoc _ _ _)).symm

theorem K_le_Gw (a b : ℤ) : t.K ≤ t.Gw a b := by
  intro h hh
  refine mem_win_iff.mpr fun i _ _ => mem_qv_iff.mpr ?_
  have hτ : trackElt t.x₁ t.x₂ i ∈ normalizer (t.K : Set G) :=
    zpow_mem t.track.tau_mem_normalizer _
  have hh' : (trackElt t.x₁ t.x₂ i)⁻¹ * h * trackElt t.x₁ t.x₂ i ∈ t.K := by
    have := (mem_normalizer_iff.mp (inv_mem hτ) h).mp hh
    rwa [inv_inv] at this
  have hB := t.hHall.1 hh'
  unfold trackPar
  split_ifs
  · exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hB
  · exact (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hB

theorem Qv_eq (i : ℤ) : t.Qv i = pCoreOf 2 (t.Gv i) := by
  have hQ : trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) i =
      pCoreOf 2 (trackPar (P1 L1 L2 S) (P2 L1 L2 S) i) := by
    unfold trackPar
    split_ifs <;> rfl
  show (trackPar _ _ i).map _ = pCoreOf 2 ((trackPar _ _ i).map _)
  rw [hQ, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj _) _]

theorem Zv_eq (i : ℤ) : t.Zv i = omegaOneCenterOf (t.Qv i) := by
  have hZ : trackPar (Z1 L1 L2 S) (Z2 L1 L2 S) i =
      omegaOneCenterOf (trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) i) := by
    unfold trackPar
    split_ifs <;> rfl
  show (trackPar _ _ i).map _ = omegaOneCenterOf ((trackPar _ _ i).map _)
  rw [hZ]
  exact omegaOneCenterOf_map_mulEquiv _ _

private theorem Gw_edge (hF : F112HypW L1 L2 S) (u : ℤ) :
    t.Gw u (u + 1) =
      (bigB L1 L2 S).map (MulAut.conj (edgeElt t.x₁ t.x₂ u)).toMonoidHom := by
  have hP := qv_edge (R₁ := P1 L1 L2 S) (R₂ := P2 L1 L2 S)
    (Subgroup.le_normalizer t.track.x₁_mem) (Subgroup.le_normalizer t.track.x₂_mem) u
  have hF19 : P1 L1 L2 S ⊓ P2 L1 L2 S = bigB L1 L2 S :=
    f112_parabolic_inf_eq_bigB hF
  show win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ u (u + 1) = _
  rw [win_add_one_right (a := u) (b := u) (by omega), win_self, hP.1, hP.2, ← map_conj_inf,
    trackPar_inf_succ, hF19]

private theorem Gw_edge_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (u : ℤ) :
    t.Gw u (u + 1) = pCoreOf 2 (t.Gw u (u + 1)) ⊔ t.K := by
  have hg : edgeElt t.x₁ t.x₂ u ∈ normalizer (t.K : Set G) :=
    edgeElt_mem t.track.x₁_norm t.track.x₂_norm u
  rw [t.Gw_edge hfr.hF u, pCoreOf_map_mulEquiv 2 (MulAut.conj _) _, pCoreOf_bigB hfr.hF hfr.hN,
    ← t.sup_K_eq_bigB, Subgroup.map_sup, map_conj_eq_of_mem hg]

theorem Gw_eq_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) {u w : ℤ}
    (huw : u < w) : t.Gw u w = pCoreOf 2 (t.Gw u w) ⊔ t.K :=
  eq_pCoreOf_sup_of_le (t.Gw_edge_eq_sup hfr u) (t.K_le_Gw u w) (win_mono le_rfl (by omega))

theorem le_pCoreOf_Gw {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {u w : ℤ} (huw : u < w) {X : Subgroup G} (hX : IsPGroup 2 X) (hXw : X ≤ t.Gw u w) :
    X ≤ pCoreOf 2 (t.Gw u w) :=
  le_pCoreOf_of_eq_sup (t.Gw_eq_sup hfr huw) t.hHall.2.1 hX hXw

private theorem relIndex_edge {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (u : ℤ) :
    (t.Qv u).relIndex (pCoreOf 2 (t.Gw u (u + 1))) =
        (trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) u).relIndex S ∧
      (t.Qv (u + 1)).relIndex (pCoreOf 2 (t.Gw u (u + 1))) =
        (trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) (u + 1)).relIndex S := by
  have hQ := qv_edge (R₁ := Q1 L1 L2 S) (R₂ := Q2 L1 L2 S)
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S) t.track.x₁_mem)
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S) t.track.x₂_mem) u
  rw [t.Gw_edge hfr.hF u, pCoreOf_map_mulEquiv 2 (MulAut.conj _) _, pCoreOf_bigB hfr.hF hfr.hN]
  show (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ u).relIndex _ = _ ∧
    (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ (u + 1)).relIndex _ = _
  rw [hQ.1, hQ.2, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact ⟨rfl, rfl⟩

private theorem mem_Qv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {y : G} (hy : y ∈ t.Gw (-1) 1) (h2 : ∃ n, orderOf y = 2 ^ n) : y ∈ t.Qv 0 := by
  have hF19 : P1 L1 L2 S ⊓ P2 L1 L2 S = bigB L1 L2 S :=
    f112_parabolic_inf_eq_bigB hfr.hF
  have hy0 : y ∈ P1 L1 L2 S := by
    have := mem_win_iff.mp hy 0 (by norm_num) (by norm_num)
    rwa [qv_zero] at this
  have hy1 : y ∈ P2 L1 L2 S := by
    have := mem_win_iff.mp hy 1 (by norm_num) le_rfl
    rwa [qv_one] at this
  have hym : t.x₁⁻¹ * y * t.x₁ ∈ P2 L1 L2 S := by
    have := mem_win_iff.mp hy (-1) le_rfl (by norm_num)
    rwa [t.track.mem_qv_neg_iff Subgroup.le_normalizer Subgroup.le_normalizer, neg_neg,
      qv_one] at this
  have hyB : y ∈ bigB L1 L2 S := by
    rw [← hF19]
    exact ⟨hy0, hy1⟩
  have htg : t.x₁⁻¹ * y * t.x₁ ∈ bigB L1 L2 S := by
    rw [← hF19]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem t.track.x₁_mem) hy0) t.track.x₁_mem, hym⟩
  have hx₁B : t.x₁ ∉ bigB L1 L2 S := fun h =>
    t.track.x₁_not_mem ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) h)
  have hE := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hBT1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a hfr.ha (Classical.choice hfr.hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  show y ∈ qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ 0
  rw [qv_zero]
  exact mem_pCoreOf_of_two_arc_left hfr.hF hBT1 hE t.track.x₁_mem hx₁B hyB htg h2

private theorem mem_Qv_one {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {y : G} (hy : y ∈ t.Gw 0 2) (h2 : ∃ n, orderOf y = 2 ^ n) : y ∈ t.Qv 1 := by
  have hF19 : P1 L1 L2 S ⊓ P2 L1 L2 S = bigB L1 L2 S :=
    f112_parabolic_inf_eq_bigB hfr.hF
  have hy0 : y ∈ P1 L1 L2 S := by
    have := mem_win_iff.mp hy 0 le_rfl (by norm_num)
    rwa [qv_zero] at this
  have hy1 : y ∈ P2 L1 L2 S := by
    have := mem_win_iff.mp hy 1 (by norm_num) (by norm_num)
    rwa [qv_one] at this
  have hy2 : t.x₂⁻¹ * y * t.x₂ ∈ P1 L1 L2 S := by
    have := mem_win_iff.mp hy 2 (by norm_num) le_rfl
    rwa [t.track.mem_qv_two_sub_iff Subgroup.le_normalizer Subgroup.le_normalizer, sub_self,
      qv_zero] at this
  have hyB : y ∈ bigB L1 L2 S := by
    rw [← hF19]
    exact ⟨hy0, hy1⟩
  have htg : t.x₂⁻¹ * y * t.x₂ ∈ bigB L1 L2 S := by
    rw [← hF19]
    exact Subgroup.mem_inf.mpr ⟨hy2, mul_mem (mul_mem (inv_mem t.track.x₂_mem) hy1) t.track.x₂_mem⟩
  have hx₂B : t.x₂ ∉ bigB L1 L2 S := fun h =>
    t.track.x₂_not_mem ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) h)
  have hE := eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
    (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hBT2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hfr.hf (Classical.choice hfr.hL2)
  show y ∈ qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ 1
  rw [qv_one]
  exact mem_pCoreOf_of_two_arc_right hfr.hF hBT2 hE t.track.x₂_mem hx₂B hyB htg h2

theorem le_Qv_of_le_Gw {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {u w j : ℤ} (huj : u < j) (hjw : j < w) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXw : X ≤ t.Gw u w) : X ≤ t.Qv j := by
  intro y hy
  have hy' : y ∈ win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (j - 1) (j + 1) :=
    win_mono (by omega) (by omega) (hXw hy)
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hX ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hn
  have h2 (g : G) : ∃ n, orderOf (g⁻¹ * y * g) = 2 ^ n :=
    ⟨n, (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).trans hn⟩
  show y ∈ qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ j
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · rw [show 2 * k - 1 = -1 + 2 * k by ring, show 2 * k + 1 = 1 + 2 * k by ring,
      ← map_win_tau_pow, mem_map_conj_iff] at hy'
    rw [show 2 * k = 0 + 2 * k by ring, ← map_qv_tau_pow, mem_map_conj_iff]
    exact t.mem_Qv_zero hfr hy' (h2 _)
  · rw [show 2 * k + 1 - 1 = 0 + 2 * k by ring, show 2 * k + 1 + 1 = 2 + 2 * k by ring,
      ← map_win_tau_pow, mem_map_conj_iff] at hy'
    rw [show 2 * k + 1 = 1 + 2 * k by ring, ← map_qv_tau_pow, mem_map_conj_iff]
    exact t.mem_Qv_one hfr hy' (h2 _)

theorem Qv_le_Gv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) : t.Qv v ≤ t.Gv (v - 1) ∧ t.Qv v ≤ t.Gv (v + 1) := by
  have hQB : ∀ i, trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) i ≤ bigB L1 L2 S := by
    intro i
    unfold trackPar
    split_ifs
    · exact (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)).trans
        (le_sup_right : S ≤ bigB L1 L2 S)
    · exact (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)).trans
        (le_sup_right : S ≤ bigB L1 L2 S)
  have hBP : ∀ i, bigB L1 L2 S ≤ trackPar (P1 L1 L2 S) (P2 L1 L2 S) i := by
    intro i
    unfold trackPar
    split_ifs
    · exact le_sup_right
    · exact le_sup_right
  have hQ := qv_edge (R₁ := Q1 L1 L2 S) (R₂ := Q2 L1 L2 S)
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S) t.track.x₁_mem)
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S) t.track.x₂_mem)
  have hP := qv_edge (R₁ := P1 L1 L2 S) (R₂ := P2 L1 L2 S)
    (Subgroup.le_normalizer t.track.x₁_mem) (Subgroup.le_normalizer t.track.x₂_mem)
  refine ⟨?_, ?_⟩
  · have h1 := (hQ (v - 1)).2
    rw [sub_add_cancel] at h1
    show qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ v ≤
      qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v - 1)
    rw [h1, (hP (v - 1)).1]
    exact Subgroup.map_mono ((hQB v).trans (hBP (v - 1)))
  · show qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ v ≤
      qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v + 1)
    rw [(hQ v).1, (hP v).2]
    exact Subgroup.map_mono ((hQB v).trans (hBP (v + 1)))

theorem inf_Gv_eq_inf_Qv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) {X : Subgroup G} (hX : IsPGroup 2 X) :
    (X ≤ t.Gw (v - 1) v → X ⊓ t.Gv (v + 1) = X ⊓ t.Qv v) ∧
      (X ≤ t.Gw v (v + 1) → X ⊓ t.Gv (v - 1) = X ⊓ t.Qv v) := by
  have hQ := t.Qv_le_Gv hfr v
  refine ⟨fun hXw => le_antisymm ?_ (inf_le_inf_left X hQ.2),
    fun hXw => le_antisymm ?_ (inf_le_inf_left X hQ.1)⟩
  · refine le_inf inf_le_left (t.le_Qv_of_le_Gw hfr (u := v - 1) (w := v + 1) (by omega)
      (by omega) (hX.to_le inf_le_left) ?_)
    rintro y ⟨hyX, hyv⟩
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ v ∨ i = v + 1 by omega) with h3 | rfl
    · exact mem_win_iff.mp (hXw hyX) i h1 h3
    · exact hyv
  · refine le_inf inf_le_left (t.le_Qv_of_le_Gw hfr (u := v - 1) (w := v + 1) (by omega)
      (by omega) (hX.to_le inf_le_left) ?_)
    rintro y ⟨hyX, hyv⟩
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = v - 1 ∨ v ≤ i by omega) with rfl | h3
    · exact hyv
    · exact mem_win_iff.mp (hXw hyX) i h3 h2

theorem relIndex_Qv_pCoreOf {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) :
    (t.Qv v).relIndex (pCoreOf 2 (t.Gw (v - 1) v)) =
        (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) ∧
      (t.Qv v).relIndex (pCoreOf 2 (t.Gw v (v + 1))) =
        (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) := by
  have hbase : (trackPar (Q1 L1 L2 S) (Q2 L1 L2 S) v).relIndex S =
      if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f := by
    unfold trackPar
    split_ifs
    · exact relIndex_Q1 hfr
    · exact str86_relIndex_q2_s hfr.hF hfr.hN hfr.hf hfr.hL2
  have h := (t.relIndex_edge hfr (v - 1)).2
  rw [sub_add_cancel] at h
  exact ⟨h.trans hbase, (t.relIndex_edge hfr v).1.trans hbase⟩

theorem relIndex_Qv_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) {X : Subgroup G} (hX : IsPGroup 2 X) (hXw : X ≤ t.Gw (v - 1) v ∨ X ≤ t.Gw v (v + 1)) :
    (t.Qv v).relIndex X ≤ if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f := by
  have hne : (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) ≠ 0 := by
    split_ifs <;> positivity
  rcases hXw with hXw | hXw
  · have hP := t.le_pCoreOf_Gw hfr (show v - 1 < v by omega) hX hXw
    rw [← (t.relIndex_Qv_pCoreOf hfr v).1] at hne ⊢
    exact Subgroup.relIndex_le_of_le_right hP hne
  · have hP := t.le_pCoreOf_Gw hfr (show v < v + 1 by omega) hX hXw
    rw [← (t.relIndex_Qv_pCoreOf hfr v).2] at hne ⊢
    exact Subgroup.relIndex_le_of_le_right hP hne

end Track

end CFSG.Quasithin.Stroth.Rq

end
