module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSP
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen2
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixTwoAux

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem Rc_eq_one_or_eq (hR : Nat.card ↥(Rc X) ≤ 2) {r : G} (hr : r ∈ Rc X) (hr1 : r ≠ 1) {ρ : G}
    (hρ : ρ ∈ Rc X) : ρ = 1 ∨ ρ = r := by
  by_cases h1 : ρ = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (eq_of_card_le_two (a := (⟨ρ, hρ⟩ : ↥(Rc X)))
      (b := ⟨r, hr⟩) hR (fun h => h1 (congrArg Subtype.val h))
      (fun h => hr1 (congrArg Subtype.val h))))

theorem mem_Q_of_theta_eq_one (C : Cfg G M X 6) (hR : Nat.card ↥(Rc X) ≤ 2) {s : G} (hsM : s ∈ M)
    (h : C.θ ⟨s, hsM⟩ = 1) : s ∈ CFSG.Open.pCoreOf 2 M := by
  have : s ∈ C.K := C.mem_K.2 ⟨hsM, h⟩
  rwa [C.K_eq_Q hR] at this

@[expose] def commHom (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : ↥A →* ↥A :=
  MonoidHom.mk' (fun a => ⟨(a : G) * t * (a : G)⁻¹ * t⁻¹, by
    have e : (a : G) * t * (a : G)⁻¹ * t⁻¹ = (a : G) * (t * (a : G)⁻¹ * t⁻¹) := by group
    rw [e]
    exact A.mul_mem a.2 (ht _ (A.inv_mem a.2))⟩) (fun a b => by
    apply Subtype.ext
    have hu : (b : G) * t * (b : G)⁻¹ * t⁻¹ ∈ A := by
      have e : (b : G) * t * (b : G)⁻¹ * t⁻¹ = (b : G) * (t * (b : G)⁻¹ * t⁻¹) := by group
      rw [e]
      exact A.mul_mem b.2 (ht _ (A.inv_mem b.2))
    have hv : (a : G) * t * (a : G)⁻¹ * t⁻¹ ∈ A := by
      have e : (a : G) * t * (a : G)⁻¹ * t⁻¹ = (a : G) * (t * (a : G)⁻¹ * t⁻¹) := by group
      rw [e]
      exact A.mul_mem a.2 (ht _ (A.inv_mem a.2))
    have h1 : (a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) =
        ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G) := hA _ a.2 _ hu
    have h2 := hA _ hu _ hv
    show ((a : G) * b) * t * ((a : G) * b)⁻¹ * t⁻¹ =
      ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)
    calc ((a : G) * b) * t * ((a : G) * b)⁻¹ * t⁻¹
        = ((a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)) * (t * (a : G)⁻¹ * t⁻¹) := by group
      _ = (((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)) * (t * (a : G)⁻¹ * t⁻¹) := by rw [h1]
      _ = ((b : G) * t * (b : G)⁻¹ * t⁻¹) * ((a : G) * t * (a : G)⁻¹ * t⁻¹) := by group
      _ = ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) := h2)

theorem mem_ker_commHom (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (a : ↥A) :
    a ∈ (commHom A hA t ht).ker ↔ (a : G) * t = t * (a : G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (a : G) * t * (a : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h
    have h2 : (a : G) * t * (a : G)⁻¹ = t := mul_inv_eq_one.1 h1
    calc (a : G) * t = ((a : G) * t * (a : G)⁻¹) * (a : G) := by group
      _ = t * (a : G) := by rw [h2]
  · intro h
    apply Subtype.ext
    show (a : G) * t * (a : G)⁻¹ * t⁻¹ = 1
    calc (a : G) * t * (a : G)⁻¹ * t⁻¹ = (t * (a : G)) * (a : G)⁻¹ * t⁻¹ := by rw [h]
      _ = 1 := by group

theorem piQ_comm_eq {t : G} (htM : t ∈ M) {i j : Fin 6} (hθ : C.θ ⟨t, htM⟩ = swap i j)
    (y : ↥(CFSG.Open.pCoreOf 2 M))
    (hc : (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    Multiplicative.toAdd (D.piQ ⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hc⟩) =
      barAct (swap i j) (Multiplicative.toAdd (D.piQ y)) - Multiplicative.toAdd (D.piQ y) := by
  have hy' : t * (y : G)⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M htM ((CFSG.Open.pCoreOf 2 M).inv_mem y.2)
  have e : (⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hc⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
      y * ⟨t * (y : G)⁻¹ * t⁻¹, hy'⟩ := Subtype.ext (by
    show (y : G) * t * (y : G)⁻¹ * t⁻¹ = (y : G) * (t * (y : G)⁻¹ * t⁻¹)
    group)
  have hconj := D.piQ_conj ⟨t, htM⟩ y⁻¹ ⟨t * (y : G)⁻¹ * t⁻¹, hy'⟩ rfl
  rw [e, map_mul, toAdd_mul, hconj, hθ, map_inv, toAdd_inv, map_neg]
  calc Multiplicative.toAdd (D.piQ y) + -barAct (swap i j) (Multiplicative.toAdd (D.piQ y))
      = Multiplicative.toAdd (D.piQ y) - barAct (swap i j) (Multiplicative.toAdd (D.piQ y)) :=
        (sub_eq_add_neg _ _).symm
    _ = -(barAct (swap i j) (Multiplicative.toAdd (D.piQ y)) - Multiplicative.toAdd (D.piQ y)) :=
        (neg_sub _ _).symm
    _ = _ := permBar_neg_eq _

theorem piQ_comm_cases {t : G} (htM : t ∈ M) {i j : Fin 6} (hθ : C.θ ⟨t, htM⟩ = swap i j)
    (y : ↥(CFSG.Open.pCoreOf 2 M))
    (hc : (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    Multiplicative.toAdd (D.piQ ⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hc⟩) = 0 ∨
      Multiplicative.toAdd (D.piQ ⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, hc⟩) =
        barInd ({i, j} : Finset (Fin 6)) := by
  rw [piQ_comm_eq D htM hθ y hc]
  exact H2.barAct_swap_sub _

theorem exists_W_comm {t : G} (htM : t ∈ M) {i j : Fin 6} (hij : i ≠ j)
    (hθ : C.θ ⟨t, htM⟩ = swap i j) :
    ∃ w : ↥(CFSG.Open.pCoreOf 2 M), (w : G) ∈ blockU X ∧
      ∃ hc : (w : G) * t * (w : G)⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M,
        Multiplicative.toAdd (D.piQ ⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, hc⟩) =
          barInd ({i, j} : Finset (Fin 6)) := by
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by
    have : ∀ i j : Fin 6, ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by decide
    exact this i j
  obtain ⟨w, hwW, hπw⟩ := D.exists_piQ_eq_uvec_six i k
  have hc : (w : G) * t * (w : G)⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    have e : (w : G) * t * (w : G)⁻¹ * t⁻¹ = (w : G) * (t * (w : G)⁻¹ * t⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 M).mul_mem w.2
      (pCoreOf_normalized M htM ((CFSG.Open.pCoreOf 2 M).inv_mem w.2))
  refine ⟨w, hwW, hc, ?_⟩
  rw [piQ_comm_eq D htM hθ w hc, hπw, barAct_uvec, swap_apply_left,
    swap_apply_of_ne_of_ne hki hkj, sub_eq_add_neg, add_comm]
  rw [neg_uvec_add_uvec i j k]
  exact H4b.uvec_eq_barInd hij

theorem card_le_two_mul_cent (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (t : G)
    (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (y : ↥A)
    (hy : ∀ a : ↥A, commHom A hA t ht a = 1 ∨ commHom A hA t ht a = y) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have h1 := Subgroup.card_ker_mul_card_range (commHom A hA t ht)
  have h2 : Nat.card (commHom A hA t ht).range ≤ 2 := H2.card_range_le_two _ y (by
    rintro _ ⟨a, rfl⟩
    exact hy a)
  have h3 : Nat.card (commHom A hA t ht).ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr
      { toFun := fun a => ⟨((a : ↥A) : G), a.1.2, Subgroup.mem_centralizer_singleton_iff.2
          ((mem_ker_commHom A hA t ht a.1).1 a.2)⟩
        invFun := fun r => ⟨⟨(r : G), r.2.1⟩, (mem_ker_commHom A hA t ht _).2
          (Subgroup.mem_centralizer_singleton_iff.1 r.2.2)⟩
        left_inv := fun a => rfl
        right_inv := fun r => rfl }
  rw [← h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem card_le_four_of_wt_four {A : Type} [Group A] [Finite A]
    (g : A →* Multiplicative (Fin 6 → ZMod 2))
    (hwt : ∀ a : A, a ≠ 1 → vecWt (Multiplicative.toAdd (g a)) = 4) : Nat.card A ≤ 4 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hcoord : ∀ k : Fin 6, 2 * (Finset.univ.filter fun a : A =>
      Multiplicative.toAdd (g a) k = 1).card ≤ Fintype.card A := by
    intro k
    by_cases h : ∃ s : A, Multiplicative.toAdd (g s) k = 1
    · obtain ⟨s, hs⟩ := h
      have h1 : (Finset.univ.filter fun a : A => Multiplicative.toAdd (g a) k = 1).card ≤
          (Finset.univ.filter fun a : A => Multiplicative.toAdd (g a) k = 0).card := by
        refine Finset.card_le_card_of_injOn (fun a => s⁻¹ * a) ?_ ?_
        · intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hs, ha]
          exact neg_add_cancel _
        · intro a _ b _ hab
          exact mul_left_cancel hab
      have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset A))
        (fun a : A => Multiplicative.toAdd (g a) k = 1)
      have h3 : (Finset.univ.filter fun a : A => ¬ Multiplicative.toAdd (g a) k = 1) =
          Finset.univ.filter fun a : A => Multiplicative.toAdd (g a) k = 0 :=
        Finset.filter_congr fun a _ => (zmod_two_eq_zero_iff_ne_one _).symm
      rw [h3, Finset.card_univ] at h2
      omega
    · push Not at h
      have : (Finset.univ.filter fun a : A => Multiplicative.toAdd (g a) k = 1) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun a _ => h a
      rw [this, Finset.card_empty]
      omega
  have hsum : ∑ a : A, vecWt (Multiplicative.toAdd (g a)) =
      ∑ k : Fin 6, (Finset.univ.filter fun a : A => Multiplicative.toAdd (g a) k = 1).card := by
    simp only [vecWt, Finset.card_filter]
    exact Finset.sum_comm
  have hsum2 : ∑ a : A, vecWt (Multiplicative.toAdd (g a)) = 4 * (Fintype.card A - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : A))]
    have h0 : vecWt (Multiplicative.toAdd (g 1)) = 0 := by
      rw [map_one, toAdd_one]
      simp [vecWt]
    rw [h0, zero_add, Finset.sum_congr rfl (fun a ha => hwt a (Finset.ne_of_mem_erase ha)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      smul_eq_mul, mul_comm]
  have hle : ∑ k : Fin 6, 2 * (Finset.univ.filter fun a : A =>
      Multiplicative.toAdd (g a) k = 1).card ≤ ∑ _k : Fin 6, Fintype.card A :=
    Finset.sum_le_sum fun k _ => hcoord k
  rw [← Finset.mul_sum, ← hsum, hsum2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hle
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  rw [Nat.card_eq_fintype_card]
  omega

theorem piQ_eq_one_of_mem_Rc {z : G} (hz : z ∈ CFSG.Open.pCoreOf 2 M) (hR : z ∈ Rc X) :
    D.piQ ⟨z, hz⟩ = 1 := (D.piQ_eq_one_iff ⟨z, hz⟩).2 hR

theorem exists_mem_Rc_of_piQ_eq {z x : G} (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) (h : D.piQ ⟨z, hz⟩ = D.piQ ⟨x, hx⟩) :
    ∃ ρ ∈ Rc X, z = ρ * x := by
  have h1 : D.piQ (⟨z, hz⟩ * (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : z * x⁻¹ ∈ Rc X := (D.piQ_eq_one_iff _).1 h1
  exact ⟨z * x⁻¹, h2, by group⟩

end SixTwoAux

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

section Branch

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
  (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = C.T2 i j)
include hR2 hsurj hQ16 hij hπ hK h

theorem sixTwo_theta_eq_swap {t : G} (htP : t ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) : ∃ htM : t ∈ M, C.θ ⟨t, htM⟩ = swap i j := by
  have hR := hR2.le
  have hT : t ∈ C.T2 i j := by
    rw [← h]
    exact Subgroup.mem_sup_left htP
  obtain ⟨htM, hmem⟩ := C.mem_thetaPre.1 hT
  refine ⟨htM, ?_⟩
  rcases SixS.mem_zpowers_swap hmem with h1 | h1
  · exact absurd (SixTwoAux.mem_Q_of_theta_eq_one C hR htM h1) htQ
  · exact h1

theorem sixTwo_mem_Q_or_mul_inv_mem_Q {t : G} (htP : t ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) {p : G} (hpP : p ∈ CFSG.Open.pCoreOf 2 (CGOf x)) :
    p ∈ CFSG.Open.pCoreOf 2 M ∨ p * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have hR := hR2.le
  obtain ⟨htM, hθt⟩ := D.sixTwo_theta_eq_swap hR2 hsurj hQ16 hx hij hπ hK h htP htQ
  have hT : p ∈ C.T2 i j := by
    rw [← h]
    exact Subgroup.mem_sup_left hpP
  obtain ⟨hpM, hmem⟩ := C.mem_thetaPre.1 hT
  rcases SixS.mem_zpowers_swap hmem with h1 | h1
  · exact Or.inl (SixTwoAux.mem_Q_of_theta_eq_one C hR hpM h1)
  · right
    have hM' : p * t⁻¹ ∈ M := M.mul_mem hpM (M.inv_mem htM)
    refine SixTwoAux.mem_Q_of_theta_eq_one C hR hM' ?_
    have e : (⟨p * t⁻¹, hM'⟩ : ↥M) = ⟨p, hpM⟩ * ⟨t, htM⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, h1, hθt, mul_inv_cancel]

theorem sixTwo_exists_inv :
    ∃ r ∈ Rc X, r ≠ 1 ∧ ∃ t ∈ CFSG.Open.pCoreOf 2 (CGOf x), t ∉ CFSG.Open.pCoreOf 2 M ∧
      t * t = 1 ∧ ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), t * p = p * t := by
  classical
  have hR := hR2.le
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx (Finset.card_pair hij) hπ
  have hPT2 : CFSG.Open.pCoreOf 2 (CGOf x) ≤ C.T2 i j := h ▸ le_sup_left
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT2.trans (C.thetaPre_le_M _)
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := H4b.Q_le_CGOf C hR hx
  have hcons := H4b.twoConstrained_P C hR hx hx1
  have hRb : Rc X ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hR2
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
  have hr1' : r ≠ 1 := fun h' => hr1 (Subtype.ext h')
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf] at hr
    exact hr.1
  have hrc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * r = r * p := fun p hp => by
    have := C.R_central hR p (hPM hp) r hr
    calc p * r = (p * r * p⁻¹) * p := by group
      _ = r * p := by rw [this]
  have hrP : r ∈ CFSG.Open.pCoreOf 2 (CGOf x) := hcons (Subgroup.mem_inf.2 ⟨hQK hrQ,
    Subgroup.mem_centralizer_iff.2 hrc⟩)
  have hrZ : r ∈ H4b.centerP x := Subgroup.mem_inf.2 ⟨hrP, Subgroup.mem_centralizer_iff.2 hrc⟩
  have hlr : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
    rw [SixTwoAux.piQ_eq_one_of_mem_Rc D hrQ hr, toAdd_one, H2.barLen_zero]
    norm_num
  obtain ⟨k, hkK, hkQ⟩ : ∃ k ∈ CGOf x, k * r * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
    by_contra hcon
    push Not at hcon
    exact hK (fun k hk => D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1' hlr (hcon k hk))
  have hkt : k * r * k⁻¹ ∈ H4b.centerP x :=
    (Subgroup.mem_normalizer_iff.1 (H4b.mem_normalizer_centerP hkK) r).1 hrZ
  obtain ⟨hktP, hktc⟩ := Subgroup.mem_inf.1 hkt
  refine ⟨r, hr, hr1', k * r * k⁻¹, hktP, hkQ, ?_, fun p hp => ?_⟩
  · have := Rc_mul_self hR hr
    calc k * r * k⁻¹ * (k * r * k⁻¹) = k * (r * r) * k⁻¹ := by group
      _ = 1 := by rw [this]; group
  · exact (Subgroup.mem_centralizer_iff.1 hktc p hp).symm

theorem sixTwo_comm_values {t : G} (htP : t ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) (htc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), t * p = p * t)
    {r : G} (hrR : r ∈ Rc X) (hr1 : r ≠ 1) :
    (∀ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ = 1 ∨ y * t * y⁻¹ * t⁻¹ = x * r) ∧
      (∃ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ = x * r) ∧
      CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M =
        CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G) := by
  classical
  have hR := hR2.le
  have hQab := C.Q_comm hR
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx (Finset.card_pair hij) hπ
  have hcons := H4b.twoConstrained_P C hR hx hx1
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := H4b.Q_le_CGOf C hR hx
  obtain ⟨htM, hθ⟩ := D.sixTwo_theta_eq_swap hR2 hsurj hQ16 hx hij hπ hK h htP htQ
  have hQn : ∀ a ∈ CFSG.Open.pCoreOf 2 M, t * a * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun a ha => pCoreOf_normalized M htM ha
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have := hrR
    rw [C.S.R_eq_inf] at this
    exact this.1
  have hcQ : ∀ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    intro y hy
    have e : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 M).mul_mem hy (hQn _ ((CFSG.Open.pCoreOf 2 M).inv_mem hy))
  have hA : ∀ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ ≠ x := by
    intro y hy hyx
    have hyK : y ∈ CGOf x := hQK hy
    have ha : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x),
        y * p * y⁻¹ * p⁻¹ ∈ Subgroup.zpowers x := by
      intro p hp
      rcases D.sixTwo_mem_Q_or_mul_inv_mem_Q hR2 hsurj hQ16 hx hij hπ hK h htP htQ hp with h1 | h1
      · have e : y * p * y⁻¹ * p⁻¹ = 1 := by rw [hQab y hy p h1]; group
        rw [e]
        exact Subgroup.one_mem _
      · have e : p = (p * t⁻¹) * t := by group
        rw [e, H2.comm_mul_comm hQab hQn hy h1, hyx]
        exact Subgroup.mem_zpowers x
    have hyP : y ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
      H2.stabSub_le_pCoreOf (K := CGOf x) (fun k hk => mem_centralizer_zpowers_iff.1 hk)
        (exists_two_pow_of_mem_pCoreOf M hx)
        (fun k hk hkc => hcons (Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_centralizer_iff.2 hkc⟩))
        ⟨hyK, ha⟩
    have h1 : y * t * y⁻¹ * t⁻¹ = 1 := by
      rw [← htc y hyP]
      group
    exact hx1 (hyx.symm.trans h1)
  have hvals : ∀ y ∈ CFSG.Open.pCoreOf 2 M,
      y * t * y⁻¹ * t⁻¹ = 1 ∨ y * t * y⁻¹ * t⁻¹ = r ∨ y * t * y⁻¹ * t⁻¹ = r * x := by
    intro y hy
    have hc := hcQ y hy
    rcases SixTwoAux.piQ_comm_cases D htM hθ ⟨y, hy⟩ hc with h0 | h0
    · have h1 : D.piQ ⟨y * t * y⁻¹ * t⁻¹, hc⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 ((D.piQ_eq_one_iff _).1 h1) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · have h1 : D.piQ ⟨y * t * y⁻¹ * t⁻¹, hc⟩ = D.piQ ⟨x, hx⟩ :=
        Multiplicative.toAdd.injective (h0.trans hπ.symm)
      obtain ⟨ρ, hρ, hρe⟩ := SixTwoAux.exists_mem_Rc_of_piQ_eq D hc hx h1
      rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 hρ with h3 | h3
      · exact absurd (by rw [hρe, h3, one_mul]) (hA y hy)
      · exact Or.inr (Or.inr (by rw [hρe, h3]))
  obtain ⟨w, hwW, hwc, hπw⟩ := SixTwoAux.exists_W_comm D htM hij hθ
  have hwQ : (w : G) ∈ CFSG.Open.pCoreOf 2 M := w.2
  have hcw : (w : G) * t * (w : G)⁻¹ * t⁻¹ = r * x := by
    have h1 : D.piQ ⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, hwc⟩ = D.piQ ⟨x, hx⟩ :=
      Multiplicative.toAdd.injective (hπw.trans hπ.symm)
    obtain ⟨ρ, hρ, hρe⟩ := SixTwoAux.exists_mem_Rc_of_piQ_eq D hwc hx h1
    rcases SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 hρ with h3 | h3
    · exact absurd (by rw [hρe, h3, one_mul]) (hA w hwQ)
    · rw [hρe, h3]
  have hrx : r * x = x * r := hQab r hrQ x hx
  have hrr : r * r = 1 := Rc_mul_self hR hrR
  refine ⟨fun y hy => ?_, ⟨w, hwQ, by rw [hcw, hrx]⟩, ?_⟩
  · rcases hvals y hy with h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      have hmul := congrArg Subtype.val
        (map_mul (SixTwoAux.commHom (CFSG.Open.pCoreOf 2 M) hQab t hQn) ⟨y, hy⟩ ⟨(w : G), hwQ⟩)
      have hyw : (y * w) * t * (y * w)⁻¹ * t⁻¹ =
          (y * t * y⁻¹ * t⁻¹) * ((w : G) * t * (w : G)⁻¹ * t⁻¹) := hmul
      refine hA (y * w) ((CFSG.Open.pCoreOf 2 M).mul_mem hy hwQ) ?_
      rw [hyw, h1, hcw, ← mul_assoc, hrr, one_mul]
    · exact Or.inr (by rw [h1, hrx])
  · ext q
    constructor
    · intro hq
      exact ⟨hq.2, Subgroup.mem_centralizer_singleton_iff.2 (htc q hq.1).symm⟩
    · intro hq
      refine ⟨?_, hq.1⟩
      have hqt : q * t = t * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
      refine hcons (Subgroup.mem_inf.2 ⟨hQK hq.1, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩)
      rcases D.sixTwo_mem_Q_or_mul_inv_mem_Q hR2 hsurj hQ16 hx hij hπ hK h htP htQ hp with h1 | h1
      · exact hQab p h1 q hq.1
      · have h2 : (p * t⁻¹) * q = q * (p * t⁻¹) := hQab _ h1 q hq.1
        calc p * q = (p * t⁻¹) * (t * q) := by group
          _ = (p * t⁻¹) * (q * t) := by rw [hqt]
          _ = ((p * t⁻¹) * q) * t := by group
          _ = (q * (p * t⁻¹)) * t := by rw [h2]
          _ = q * p := by group

theorem exists_inv_of_sup_eq_T2 :
    ∃ t ∈ CFSG.Open.pCoreOf 2 (CGOf x), t ∉ CFSG.Open.pCoreOf 2 M ∧ t * t = 1 ∧
      (∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), t * p = p * t) ∧
      ∃ r ∈ Rc X, r ≠ 1 ∧
        (∀ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ = 1 ∨ y * t * y⁻¹ * t⁻¹ = x * r) ∧
        (∃ y ∈ CFSG.Open.pCoreOf 2 M, y * t * y⁻¹ * t⁻¹ = x * r) ∧
        CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M =
          CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨r, hrR, hr1, t, htP, htQ, htt, htc⟩ :=
    D.sixTwo_exists_inv hR2 hsurj hQ16 hx hij hπ hK h
  obtain ⟨h1, h2, h3⟩ :=
    D.sixTwo_comm_values hR2 hsurj hQ16 hx hij hπ hK h htP htQ htc hrR hr1
  exact ⟨t, htP, htQ, htt, htc, r, hrR, hr1, h1, h2, h3⟩

theorem notMem_W_of_sup_eq_T2 (hZ1 : Nat.card ↥(blockZ X) = 1) : x ∉ blockU X := by
  classical
  have hR := hR2.le
  obtain ⟨t, htP, htQ, -, -, r, hrR, hr1, hcomm, -, -⟩ :=
    D.exists_inv_of_sup_eq_T2 hR2 hsurj hQ16 hx hij hπ hK h
  obtain ⟨htM, hθ⟩ := D.sixTwo_theta_eq_swap hR2 hsurj hQ16 hx hij hπ hK h htP htQ
  obtain ⟨w, hwW, hwc, hπw⟩ := SixTwoAux.exists_W_comm D htM hij hθ
  have hcw : (w : G) * t * (w : G)⁻¹ * t⁻¹ = x * r := by
    rcases hcomm w w.2 with h1 | h1
    · exfalso
      have h2 : D.piQ ⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, hwc⟩ = 1 := by
        have : (⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, hwc⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 :=
          Subtype.ext h1
        rw [this, map_one]
      rw [h2, toAdd_one] at hπw
      have h3 := congrArg barLen hπw
      rw [H2.barLen_zero, SixS.barLen_barInd_pair hij] at h3
      omega
    · exact h1
  have hcW : (w : G) * t * (w : G)⁻¹ * t⁻¹ ∈ blockU X := by
    have e : (w : G) * t * (w : G)⁻¹ * t⁻¹ = (w : G) * (t * (w : G)⁻¹ * t⁻¹) := by group
    rw [e]
    exact (blockU X).mul_mem hwW (C.S.W_normalized htM ((blockU X).inv_mem hwW))
  intro hxW
  have hrW : r ∈ blockU X := by
    have e : r = x⁻¹ * (x * r) := by group
    rw [e]
    exact (blockU X).mul_mem ((blockU X).inv_mem hxW) (hcw ▸ hcW)
  have hrC : r ∈ Subgroup.centralizer (X : Set G) := by
    rw [C.S.R_eq_inf] at hrR
    exact hrR.2
  have hrZ : r ∈ blockZ X := ⟨hrW, hrC⟩
  have hbot : blockZ X = ⊥ := Subgroup.card_eq_one.1 hZ1
  rw [hbot, Subgroup.mem_bot] at hrZ
  exact hr1 hrZ

theorem wt_four_of_sup_eq_T2 (Ψ : C.UIso) :
    ∃ hxW : x ∈ blockU X,
      vecWt ((Multiplicative.toAdd (Ψ.ψ.symm ⟨x, hxW⟩) : evenWeight 6) : Fin 6 → ZMod 2) = 4 := by
  classical
  have hR := hR2.le
  obtain ⟨t, htP, htQ, -, -, r, hrR, hr1, hcomm, -, -⟩ :=
    D.exists_inv_of_sup_eq_T2 hR2 hsurj hQ16 hx hij hπ hK h
  obtain ⟨htM, hθ⟩ := D.sixTwo_theta_eq_swap hR2 hsurj hQ16 hx hij hπ hK h htP htQ
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by
    have : ∀ i j : Fin 6, ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by decide
    exact this i j
  have hu₁ : evenWeightPerm (C.θ ⟨t, htM⟩) (pairEW i k) = pairEW j k := by
    rw [hθ]
    apply Subtype.ext
    funext p
    rw [evenWeightPerm_pairEW_apply, pairEW_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hki hkj]
  have hψt : t * ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G) * t⁻¹ =
      ((Ψ.ψ (Multiplicative.ofAdd (pairEW j k)) : ↥(blockU X)) : G) := by
    have := Ψ.equivar ⟨t, htM⟩ (pairEW i k)
    rw [hu₁] at this
    exact this
  have hcw : ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G) * t *
      ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G)⁻¹ * t⁻¹ =
        ((Ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : ↥(blockU X)) : G) := by
    have e : ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G) * t *
        ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G)⁻¹ * t⁻¹ =
        ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G) *
          (t * ((Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) : ↥(blockU X)) : G) * t⁻¹)⁻¹ := by
      group
    rw [e, hψt]
    have h1 : Ψ.ψ (Multiplicative.ofAdd (pairEW i k)) *
        (Ψ.ψ (Multiplicative.ofAdd (pairEW j k)))⁻¹ =
        Ψ.ψ (Multiplicative.ofAdd (pairEW i j)) := by
      rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
      congr 2
      apply Subtype.ext
      funext p
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply,
        pairEW_apply]
      exact (by decide : ∀ a b c : ZMod 2, a + c + -(b + c) = a + b) _ _ _
    exact congrArg Subtype.val h1
  have hne : Multiplicative.ofAdd (pairEW i j) ≠ (1 : Multiplicative (evenWeight 6)) := by
    intro h1
    have h2 : (pairEW i j : evenWeight 6) = 0 := h1
    have h3 := congrFun (congrArg Subtype.val h2) i
    rw [pairEW_apply] at h3
    simp [hij] at h3
  have hψA : ((Ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : ↥(blockU X)) : G) = x * r := by
    rcases hcomm _ (C.S.W_le_Q (Ψ.ψ (Multiplicative.ofAdd (pairEW i k))).2) with h1 | h1
    · exfalso
      rw [hcw] at h1
      apply hne
      apply Ψ.ψ.injective
      rw [map_one]
      exact Subtype.ext h1
    · rw [← h1, hcw]
  have hv₁mem : allOnes 6 ∈ evenWeight 6 := by
    show ∑ _i : Fin 6, (1 : ZMod 2) = 0
    decide
  set v₁ : evenWeight 6 := ⟨allOnes 6, hv₁mem⟩ with hv₁
  have hv₁ne : Multiplicative.ofAdd v₁ ≠ (1 : Multiplicative (evenWeight 6)) := by
    intro h1
    have h2 : v₁ = 0 := h1
    have h3 := congrFun (congrArg Subtype.val h2) ⟨0, by norm_num⟩
    simp [hv₁, allOnes] at h3
  have hz₁Z : ((Ψ.ψ (Multiplicative.ofAdd v₁) : ↥(blockU X)) : G) ∈ blockZ X := by
    have h1 : Ψ.ψ (Multiplicative.ofAdd v₁) ∈ C.β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [Ψ.β_ψ, toAdd_one]
      exact (QuotientAddGroup.eq_zero_iff _).2
        (mem_evenWeightOnes_of_forall_eq (c := 1) fun i => rfl)
    rw [C.β_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hz₁R : ((Ψ.ψ (Multiplicative.ofAdd v₁) : ↥(blockU X)) : G) ∈ Rc X :=
    C.S.blockZ_le_R hz₁Z
  have hz₁1 : ((Ψ.ψ (Multiplicative.ofAdd v₁) : ↥(blockU X)) : G) ≠ 1 := by
    intro h1
    apply hv₁ne
    apply Ψ.ψ.injective
    rw [map_one]
    exact Subtype.ext h1
  have hz₁r : ((Ψ.ψ (Multiplicative.ofAdd v₁) : ↥(blockU X)) : G) = r :=
    (SixTwoAux.Rc_eq_one_or_eq hR hrR hr1 hz₁R).resolve_left hz₁1
  have hxe : x = ((Ψ.ψ (Multiplicative.ofAdd (pairEW i j - v₁)) : ↥(blockU X)) : G) := by
    have e1 : (Ψ.ψ (Multiplicative.ofAdd (pairEW i j - v₁)) : ↥(blockU X)) =
        Ψ.ψ (Multiplicative.ofAdd (pairEW i j)) * (Ψ.ψ (Multiplicative.ofAdd v₁))⁻¹ := by
      rw [← map_inv, ← map_mul, ofAdd_sub, div_eq_mul_inv]
    calc x = (x * r) * r⁻¹ := by group
      _ = ((Ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : ↥(blockU X)) : G) *
          ((Ψ.ψ (Multiplicative.ofAdd v₁) : ↥(blockU X)) : G)⁻¹ := by rw [hψA, hz₁r]
      _ = _ := by rw [e1]; rfl
  have hxW : x ∈ blockU X := hxe ▸ (Ψ.ψ (Multiplicative.ofAdd (pairEW i j - v₁))).2
  refine ⟨hxW, ?_⟩
  have h1 : Ψ.ψ.symm ⟨x, hxW⟩ = Multiplicative.ofAdd (pairEW i j - v₁) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hxe
  rw [h1, toAdd_ofAdd]
  have h2 : (((pairEW i j - v₁ : evenWeight 6)) : Fin 6 → ZMod 2) =
      indVec ({i, j} : Finset (Fin 6)) + allOnes 6 := by
    funext p
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, Pi.add_apply, pairEW_apply, hv₁]
    by_cases hpi : p = i
    · subst hpi
      simp [indVec, allOnes, hij] <;> decide
    · by_cases hpj : p = j
      · subst hpj
        simp [indVec, allOnes, hpi] <;> decide
      · simp [indVec, allOnes, hpi, hpj] <;> decide
  rw [h2, vecWt_add_allOnes, vecWt_indVec, Finset.card_pair hij]

theorem exists_E0_of_sup_eq_T2 :
    ∃ E : Subgroup G, E ≤ CFSG.Open.pCoreOf 2 M ∧
      Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≤ 4 * Nat.card ↥E ∧
      ∀ e ∈ E, e ≠ 1 → ∃ he : e ∈ CFSG.Open.pCoreOf 2 M,
        barLen (Multiplicative.toAdd (D.piQ ⟨e, he⟩)) = 2 ∧ ¬ CGOf e ≤ M := by
  classical
  have hR := hR2.le
  obtain ⟨t, htP, htQ, -, htc, r, hrR, hr1, hcomm, -, hPQ⟩ :=
    D.exists_inv_of_sup_eq_T2 hR2 hsurj hQ16 hx hij hπ hK h
  obtain ⟨htM, hθ⟩ := D.sixTwo_theta_eq_swap hR2 hsurj hQ16 hx hij hπ hK h htP htQ
  obtain ⟨g, hgK, hgM⟩ := SetLike.not_le_iff_exists.1 hK
  set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  set Qs : Subgroup G := CFSG.Open.pCoreOf 2 M with hQs
  set B : Subgroup G := P ⊓ Qs with hB
  have hQab := C.Q_comm hR
  have hQn : ∀ a ∈ Qs, t * a * t⁻¹ ∈ Qs := fun a ha => pCoreOf_normalized M htM ha
  have hPT2 : P ≤ C.T2 i j := h ▸ le_sup_left
  have hPM : P ≤ M := hPT2.trans (C.thetaPre_le_M _)
  have hrQ : r ∈ Qs := by
    have := hrR
    rw [C.S.R_eq_inf] at this
    exact this.1
  have hQB : Nat.card ↥Qs ≤ 2 * Nat.card ↥B := by
    have := SixTwoAux.card_le_two_mul_cent Qs hQab t hQn ⟨x * r, Qs.mul_mem hx hrQ⟩ (fun a => by
      rcases hcomm (a : G) a.2 with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1))
    rw [← hPQ] at this
    exact this
  have hθP : Nat.card ↥((P.subgroupOf M).map C.θ) = 2 := by
    have hswapmem : swap i j ∈ (P.subgroupOf M).map C.θ :=
      Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 htP, hθ⟩
    rw [Nat.card_eq_two_iff' (1 : ↥((P.subgroupOf M).map C.θ))]
    refine ⟨⟨swap i j, hswapmem⟩, ?_, ?_⟩
    · intro h1
      have h2 := congrArg (fun f : Perm (Fin 6) => f i) (congrArg Subtype.val h1)
      simp at h2
      exact hij h2.symm
    · intro y hy
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 y.2
      have hmP : (m : G) ∈ P := Subgroup.mem_subgroupOf.1 hm
      obtain ⟨hmM', hmem⟩ := C.mem_thetaPre.1 (hPT2 hmP)
      rcases SixS.mem_zpowers_swap hmem with h1 | h1
      · exact absurd (Subtype.ext (hmy.symm.trans h1)) hy
      · exact Subtype.ext (hmy.symm.trans h1)
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥B := by
    have h1 := C.card_eq_card_inf_mul hR hPM
    rw [h1, hθP, mul_comm]
  have hBP : B ≤ P := inf_le_left
  have hBQ : B ≤ Qs := inf_le_right
  have hBgP : conjSubgroup g B ≤ P := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ B := mem_conjSubgroup.1 hy
    have := pCoreOf_normalized (CGOf x) hgK (hBP hy')
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  have hcardg : Nat.card ↥(conjSubgroup g B) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hidx : ∀ A : Subgroup G, A ≤ P → Nat.card ↥A = Nat.card ↥B →
      (A.subgroupOf P).index = 2 := by
    intro A hAP hAB
    have h1 := Subgroup.card_mul_index (A.subgroupOf P)
    have h2 : Nat.card ↥(A.subgroupOf P) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    rw [h2, hAB, hPcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hBpos (h1.trans (mul_comm _ _))
  set Dd : Subgroup G := B ⊓ conjSubgroup g B with hDd
  have hDP : Dd ≤ P := inf_le_left.trans hBP
  have hDidx : (Dd.subgroupOf P).index ≤ 4 := by
    have h1 : Dd.subgroupOf P = B.subgroupOf P ⊓ (conjSubgroup g B).subgroupOf P := by
      ext y
      simp only [hDd, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [h1]
    refine Subgroup.index_inf_le.trans ?_
    rw [hidx B hBP rfl, hidx _ hBgP hcardg]
  have hDcard : Nat.card ↥Dd * (Dd.subgroupOf P).index = Nat.card ↥P := by
    have h1 := Subgroup.card_mul_index (Dd.subgroupOf P)
    have h2 : Nat.card ↥(Dd.subgroupOf P) = Nat.card ↥Dd :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
    rwa [h2] at h1
  have hP4 : Nat.card ↥P ≤ 4 * Nat.card ↥Dd := by
    rw [← hDcard]
    exact (Nat.mul_le_mul_left _ hDidx).trans (by rw [mul_comm])
  refine ⟨Dd, inf_le_left.trans hBQ, by show Nat.card ↥Qs ≤ 4 * Nat.card ↥Dd; omega,
    fun e he he1 => ?_⟩
  have heQ : e ∈ Qs := hBQ he.1
  have hgB : g⁻¹ * e * g ∈ B := mem_conjSubgroup.1 he.2
  have hgQ : g⁻¹ * e * g⁻¹⁻¹ ∈ Qs := by
    rw [inv_inv]
    exact hBQ hgB
  have hgM' : g⁻¹ ∉ M := fun hm => hgM (by simpa using M.inv_mem hm)
  have hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨e, heQ⟩)) = 2 := by
    by_contra hl
    exact hgM' (D.mem_M_of_conj_len_ne_two hR hsurj heQ he1 hl hgQ)
  exact ⟨heQ, hl2, fun hC => hgM' (D.mem_M_of_conj_len_two hR hsurj heQ hl2 hC hgQ)⟩

end Branch

theorem false_of_forall_sup_eq_T2 (hR2 : Nat.card ↥(Rc X) = 2)
    (hsurj : Function.Surjective C.θ) (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16)
    (hall : ∀ (y : G) (hy : y ∈ CFSG.Open.pCoreOf 2 M) (a b : Fin 6), a ≠ b →
      Multiplicative.toAdd (D.piQ ⟨y, hy⟩) = barInd {a, b} → ¬ CGOf y ≤ M →
      CFSG.Open.pCoreOf 2 (CGOf y) ⊔ CFSG.Open.pCoreOf 2 M = C.T2 a b)
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M) : False := by
  classical
  have hR := hR2.le
  obtain ⟨E, hEQ, hQE, hE⟩ := D.exists_E0_of_sup_eq_T2 hR2 hsurj hQ16 hx hij hπ hK
    (hall x hx i j hij hπ hK)
  have hEfacts : ∀ e ∈ E, e ≠ 1 → ∃ he : e ∈ CFSG.Open.pCoreOf 2 M, ∃ a b : Fin 6, ∃ hab : a ≠ b,
      ∃ hπe : Multiplicative.toAdd (D.piQ ⟨e, he⟩) = barInd {a, b}, ∃ hKe : ¬ CGOf e ≤ M,
        CFSG.Open.pCoreOf 2 (CGOf e) ⊔ CFSG.Open.pCoreOf 2 M = C.T2 a b := by
    intro e he he1
    obtain ⟨heQ, hl2, hKe⟩ := hE e he he1
    obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨e, heQ⟩))
    rw [hl2] at hIc
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hIc
    exact ⟨heQ, a, b, hab, hI, hKe, hall e heQ a b hab hI hKe⟩
  have hZ : Nat.card ↥(blockZ X) = 1 ∨ Nat.card ↥(blockZ X) = 2 := by
    have h1 := C.card_blockZ_le_two
    have h2 : 0 < Nat.card ↥(blockZ X) := Nat.card_pos
    omega
  rcases hZ with hZ1 | hZ2
  ·
    have hEW : ∀ e ∈ E, e ∈ blockU X → e = 1 := by
      intro e he heW
      by_contra he1
      obtain ⟨heQ, a, b, hab, hI, hKe, hPe⟩ := hEfacts e he he1
      exact D.notMem_W_of_sup_eq_T2 hR2 hsurj hQ16 heQ hab hI hKe hPe hZ1 heW
    have h16 := C.S.sixteen_le_card_blockU
    have hcard : Nat.card ↥E * Nat.card ↥(blockU X) ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M) := by
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective
        (fun p : ↥E × ↥(blockU X) => (⟨(p.1 : G) * (p.2 : G),
          (CFSG.Open.pCoreOf 2 M).mul_mem (hEQ p.1.2) (C.S.W_le_Q p.2.2)⟩ :
            ↥(CFSG.Open.pCoreOf 2 M))) ?_
      intro p p' hpp'
      have h1 : (p.1 : G) * (p.2 : G) = (p'.1 : G) * (p'.2 : G) := congrArg Subtype.val hpp'
      have h2 : (p'.1 : G)⁻¹ * (p.1 : G) = (p'.2 : G) * (p.2 : G)⁻¹ := by
        calc (p'.1 : G)⁻¹ * (p.1 : G)
            = (p'.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
          _ = (p'.1 : G)⁻¹ * ((p'.1 : G) * (p'.2 : G)) * (p.2 : G)⁻¹ := by rw [h1]
          _ = (p'.2 : G) * (p.2 : G)⁻¹ := by group
      have hmemE : (p'.1 : G)⁻¹ * (p.1 : G) ∈ E := E.mul_mem (E.inv_mem p'.1.2) p.1.2
      have hmemW : (p'.1 : G)⁻¹ * (p.1 : G) ∈ blockU X := by
        rw [h2]
        exact (blockU X).mul_mem p'.2.2 ((blockU X).inv_mem p.2.2)
      have h3 : (p'.1 : G)⁻¹ * (p.1 : G) = 1 := hEW _ hmemE hmemW
      have h4 : (p.1 : G) = (p'.1 : G) := (inv_mul_eq_one.1 h3).symm
      have h5 : (p.2 : G) = (p'.2 : G) := by
        have := h1
        rw [h4] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    have h1 : Nat.card ↥E * 16 ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
      (Nat.mul_le_mul_left _ h16).trans hcard
    have hpos : 0 < Nat.card ↥E := Nat.card_pos
    omega
  ·
    obtain ⟨Ψ⟩ := C.nonempty_uIso hZ2
    have hwt : ∀ e ∈ E, e ≠ 1 → ∃ hW : e ∈ blockU X,
        vecWt ((Multiplicative.toAdd (Ψ.ψ.symm ⟨e, hW⟩) : evenWeight 6) : Fin 6 → ZMod 2) = 4 := by
      intro e he he1
      obtain ⟨heQ, a, b, hab, hI, hKe, hPe⟩ := hEfacts e he he1
      exact D.wt_four_of_sup_eq_T2 hR2 hsurj hQ16 heQ hab hI hKe hPe Ψ
    have hEW : E ≤ blockU X := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]
        exact (blockU X).one_mem
      · exact (hwt e he he1).1
    let g : ↥E →* Multiplicative (Fin 6 → ZMod 2) :=
      (AddMonoidHom.toMultiplicative (evenWeight 6).subtype).comp
        ((Ψ.ψ.symm : ↥(blockU X) →* Multiplicative (evenWeight 6)).comp
          (Subgroup.inclusion hEW))
    have hg : ∀ e : ↥E, e ≠ 1 → vecWt (Multiplicative.toAdd (g e)) = 4 := by
      intro e he1
      obtain ⟨hW, hwe⟩ := hwt (e : G) e.2 (fun h' => he1 (Subtype.ext h'))
      exact hwe
    have hle4 := SixTwoAux.card_le_four_of_wt_four g hg
    have hW32 : Nat.card ↥(blockU X) = 32 := by
      rw [WStr.card_blockU_eq C, hZ2, SimsTheoremC.card_altHeart_even (by norm_num) (by decide)]
      norm_num
    have hWQ : Nat.card ↥(blockU X) ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
      Subgroup.card_le_of_le C.S.W_le_Q
    omega

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
