module

public import CFSG.Quasithin.Recognition.St84.Sec45
public import CFSG.Quasithin.Recognition.St84.Sec46
public import CFSG.Quasithin.Recognition.St84.Sec6S5

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

private theorem le_normalizer_Z_of_le_Gi {U : Subgroup G} {i : ℤ} (h : U ≤ X.Gi i) :
    U ≤ Subgroup.normalizer (X.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact X.Z_normal i g (h hg)

private theorem hasB_succ_of_odd (H : X.Sec4Hyp s r) {d : ℕ} (hd : X.HasB 1 d)
    (hodd : Odd (d + 1)) : X.HasB ((d : ℤ) + 1) d := by
  refine (X.hasB_iff_of_even (i := (d : ℤ) + 1) (j := 1) ?_ d).mpr hd
  obtain ⟨k, hk⟩ := hodd
  rw [show (d : ℤ) + 1 - 1 = (d : ℤ) by ring]
  exact ⟨(k : ℤ), by omega⟩

private theorem hasB_two (H : X.Sec4Hyp s r) {d₀ : ℕ} (hd₀ : X.HasB 0 d₀) : X.HasB 2 d₀ := by
  refine (X.hasB_iff_of_even (i := 2) (j := 0) ?_ d₀).mpr hd₀
  exact ⟨1, by norm_num⟩

private theorem hasB_r_sub_two (H : X.Sec4Hyp s r) {d₀ : ℕ} (hd₀ : X.HasB 0 d₀) :
    X.HasB ((r : ℤ) - 2) d₀ := by
  refine (X.hasB_iff_of_even (i := (r : ℤ) - 2) (j := 0) ?_ d₀).mpr hd₀
  obtain ⟨k, hk⟩ := H.even_r
  have hk' : r = 2 * k := by omega
  exact ⟨(k : ℤ) - 1, by omega⟩

private theorem Z_le_centralizer_edgeSylow_pred_iff (H : X.Sec4Hyp s r) (i : ℤ) :
    X.Z i ≤ Subgroup.centralizer (X.edgeSylow (i - 1) : Set G) ↔
      X.Z i ≤ Subgroup.centralizer (X.edgeSylow i : Set G) := by
  obtain ⟨t, -, htact⟩ := X.exists_reflection H i
  have hti : t • X.vert i = X.vert i := by simpa using htact 0
  have hconjZ : conjSub t (X.Z i) = X.Z i := (Z_smul X X hti).symm
  have h1 : conjSub t (X.edgeSylow (i - 1)) = X.edgeSylow i := by
    have h := htact (-1)
    rw [show i + -1 = i - 1 by ring, show i - -1 = i + 1 by ring] at h
    exact X.conjSub_edgeSylow_swap h (by rw [sub_add_cancel]; exact hti)
  have h2 : conjSub t (X.edgeSylow i) = X.edgeSylow (i - 1) :=
    X.conjSub_edgeSylow_swap (by rw [sub_add_cancel]; exact hti) (htact 1)
  constructor
  · intro h
    rw [← h1, conjSub_centralizer, ← hconjZ]
    exact conjSub_mono t h
  · intro h
    rw [← h2, conjSub_centralizer, ← hconjZ]
    exact conjSub_mono t h

private theorem Z_eq_centerOf_L_of_le_centralizer (H : X.Sec4Hyp s r) (i : ℤ)
    (h : X.Z i ≤ Subgroup.centralizer (X.edgeSylow i : Set G)) :
    X.Z i = centerOf (X.L i) :=
  le_antisymm
    (X.le_centerOf_L H.char i (X.Z_le_Gi i)
      (Subgroup.le_centralizer_iff.mpr ((Z_le_centralizer_edgeSylow_pred_iff X H i).mpr h))
      (Subgroup.le_centralizer_iff.mpr h))
    (X.centerOf_L_le_Z H.char i)

private theorem Z_succ_sup_Q_one_eq_edgeSylow (H : X.Sec4Hyp s r) {d : ℕ}
    (hdZb : X.HasB ((d : ℤ) + 1) d) : X.Z ((d : ℤ) + 1) ⊔ X.Q 1 = X.edgeSylow 1 := by
  have hd1 : 1 ≤ d := X.one_le_of_hasB hdZb
  have hZb2 : IsPGroup 2 (X.Z ((d : ℤ) + 1)) :=
    (pCoreOf_isPGroup' (X.Gi ((d : ℤ) + 1))).to_le (X.Z_le_Q ((d : ℤ) + 1))
  have hZbEdge1 : X.Z ((d : ℤ) + 1) ≤ X.edgeSylow 1 :=
    X.le_edgeSylow_of_le_inf 1 hZb2
      (le_inf (hdZb.Z_le_Gi (by omega)) (hdZb.Z_le_Gi (by omega)))
  have hZbNotQ1 : ¬ X.Z ((d : ℤ) + 1) ≤ X.Q 1 := by
    have h := (X.not_Z_le_Q_edge hdZb).2
    have he : (d : ℤ) + 1 - (d : ℤ) = 1 := by ring
    rwa [he] at h
  have hKZb : X.K ≤ Subgroup.normalizer (X.Z ((d : ℤ) + 1) : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi _)
  exact X.sup_Q_eq_edgeSylow_of_left_gen 1 (inf_le_left.trans hKZb) hZbEdge1 hZbNotQ1

private theorem add_one_le_of_Z_one_le_Z_zero (H : X.Sec4Hyp s r) {d₀ d : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd : X.HasB 1 d) (hZ : X.Z 1 ≤ X.Z 0) : d₀ + 1 ≤ d := by
  have h0 : X.fixSet (X.Z 0) = Set.Icc (-(d₀ : ℤ)) (d₀ : ℤ) := by
    simpa using X.fixSet_Z 0 hd₀
  have h1 : X.fixSet (X.Z 1) = Set.Icc (1 - (d : ℤ)) (1 + (d : ℤ)) := by
    simpa using X.fixSet_Z 1 hd
  have hsub : Set.Icc (-(d₀ : ℤ)) (d₀ : ℤ) ⊆ Set.Icc (1 - (d : ℤ)) (1 + (d : ℤ)) := by
    rw [← h0, ← h1]
    intro v hv z hz
    exact hv z (hZ hz)
  have hmem := hsub (Set.left_mem_Icc.mpr (by omega : -(d₀ : ℤ) ≤ (d₀ : ℤ)))
  rw [Set.mem_Icc] at hmem
  omega

private theorem s47_1 (H : X.Sec4Hyp s r) {d₀ d : ℕ} (hd₀ : X.HasB 0 d₀) (hd : X.HasB 1 d)
    (hodd : Odd (d + 1)) (hR : ⁅X.Z 1, X.Z (d + 1)⁆ = ⊥) :
    X.Z 1 = centerOf (X.L 1) ∧ X.Z (d + 1) = centerOf (X.L (d + 1)) ∧ 2 ≤ d ∧
      X.Z 1 ≤ X.Z 0 ∧ d₀ + 1 ≤ d := by
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  have hd2 : 2 ≤ d := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hbc : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
  have hsup1 : X.Z ((d : ℤ) + 1) ⊔ X.Q 1 = X.edgeSylow 1 :=
    Z_succ_sup_Q_one_eq_edgeSylow X H (hasB_succ_of_odd X H hd hodd)
  have hZ1centS1 : X.Z 1 ≤ Subgroup.centralizer (X.edgeSylow 1 : Set G) := by
    rw [← hsup1, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR
    · exact Subgroup.le_centralizer_iff.mp
        (fun z hz => (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2)
  have hZ1eq : X.Z 1 = centerOf (X.L 1) := Z_eq_centerOf_L_of_le_centralizer X H 1 hZ1centS1
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hZ1EdgeD : X.Z 1 ≤ X.edgeSylow (b - 1) :=
    X.le_edgeSylow_of_le_inf (b - 1) ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
      (le_inf (hd.Z_le_Gi (by omega)) (hd.Z_le_Gi (by omega)))
  have hZ1NotQD : ¬ X.Z 1 ≤ X.Q b := by
    rw [hbdef]
    simpa [add_comm] using (X.not_Z_le_Q_edge hd).1
  have hKZ1 : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi 1)
  have hsupD : X.Z 1 ⊔ X.Q b = X.edgeSylow (b - 1) := by
    have hb1' : b - 1 + 1 = b := by ring
    have h := X.sup_Q_eq_edgeSylow_of_gen (b - 1) (inf_le_left.trans hKZ1) hZ1EdgeD
      (by rw [hb1']; exact hZ1NotQD)
    rwa [hb1'] at h
  have hZb_centD : X.Z b ≤ Subgroup.centralizer (X.edgeSylow (b - 1) : Set G) := by
    rw [← hsupD, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR)
    · rw [Subgroup.le_centralizer_iff]
      exact fun z hz => (Subgroup.mem_inf.mp (X.Z_le_center b hz)).2
  have hZb_centE : X.Z b ≤ Subgroup.centralizer (X.edgeSylow b : Set G) :=
    (Z_le_centralizer_edgeSylow_pred_iff X H b).mp hZb_centD
  have hZbeq : X.Z b = centerOf (X.L b) := Z_eq_centerOf_L_of_le_centralizer X H b hZb_centE
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 :=
    X.Z_le_Q_of_lt hd (j := 0) (by omega)
  have hZ1S : X.Z 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact hZ1Q0.trans (X.Q_le_edgeSylow_left 0)
  have hZ1cS : X.Z 1 ≤ Subgroup.centralizer (X.S : Set G) := by
    rw [← X.edgeSylow_zero]
    simpa using (Z_le_centralizer_edgeSylow_pred_iff X H 1).mpr hZ1centS1
  have hZ1_le_centS : X.Z 1 ≤ centerOf X.S := le_inf hZ1S hZ1cS
  have hSylS : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_Gi 0
  have hZ1Z0 : X.Z 1 ≤ X.Z 0 :=
    hZ1_le_centS.trans (X.centerOf_sylow_le_Z H.char 0 hSylS).1
  have hd0le : d₀ + 1 ≤ d := add_one_le_of_Z_one_le_Z_zero X H hd₀ hd hZ1Z0
  have hfinal : X.Z (((d + 1 : ℕ) : ℤ)) = centerOf (X.L (((d + 1 : ℕ) : ℤ))) := by
    have hb' : ((d + 1 : ℕ) : ℤ) = b := hbc.trans hbdef.symm
    rw [hb']
    exact hZbeq
  exact ⟨hZ1eq, hfinal, hd2, hZ1Z0, hd0le⟩

private theorem r_add_one_eq_s_of_hasB_succ (H : X.Sec4Hyp s r) {d : ℕ} (hd : X.HasB 1 d)
    (hodd : Odd (d + 1)) (hr : 2 * d = r) : r + 1 = s := by
  have hdZb : X.HasB ((d : ℤ) + 1) d := hasB_succ_of_odd X H hd hodd
  have hZbne : X.Z ((d : ℤ) + 1) ≠ ⊥ := by
    have hQ : X.Q ((d : ℤ) + 1) ≠ ⊥ := X.Q_ne_bot H.char ((d : ℤ) + 1)
    exact X.Z_ne_bot_of ((d : ℤ) + 1) hQ
  have hZb2 : IsPGroup 2 (X.Z ((d : ℤ) + 1)) :=
    (pCoreOf_isPGroup' (X.Gi ((d : ℤ) + 1))).to_le (X.Z_le_Q ((d : ℤ) + 1))
  have hfixZb : X.Z ((d : ℤ) + 1) ≤ X.arcStab 1 (1 + (r : ℤ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [X.fixSet_Z ((d : ℤ) + 1) hdZb]
    rw [Set.mem_Icc] at hj ⊢
    omega
  have hne : pCoreOf 2 (X.arcStab 1 (1 + (r : ℤ))) ≠ ⊥ := by
    intro hbot
    have hle := X.le_pCoreOf_arcStab_r H hZb2 hfixZb
    rw [hbot] at hle
    exact hZbne (le_bot_iff.mp hle)
  have hreg := X.pCoreOf_arcStab_r H 1 hne
  by_contra hcon
  have hsr : s ≤ r := by have := H.le_r; omega
  have he := (H.ends_even 1 r hsr).1 hreg.2.2.2.2
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := H.even_r
  omega

private theorem s47_2
    (H : X.Sec4Hyp s r) {d₀ d : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd : X.HasB 1 d) (hodd : Odd (d + 1))
    (hR : ⁅X.Z 1, X.Z (d + 1)⁆ = ⊥) (hr : 2 * d = r) :
    r + 1 = s ∧ ∃ d' : ℕ, X.swap.HasB 1 d' ∧ Even (d' + 1) ∧
      ⁅X.swap.Z 1, X.swap.Z ((d' : ℤ) + 1)⁆ = ⊥ := by
  have hRb : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥ := by simpa using hR
  have hr1 : r + 1 = s := r_add_one_eq_s_of_hasB_succ X H hd hodd hr
  have hswap : X.swap.Sec4Hyp s r := Sec4Hyp.swap X H hr1
  have hd₀' : X.swap.HasB 1 d₀ := by
    rw [hasB_swap]; simpa using hd₀
  have hd' : X.swap.HasB 0 d := by
    rw [hasB_swap]; simpa using hd
  by_cases hcomm : ⁅X.swap.Z 1, X.swap.Z ((d₀ : ℤ) + 1)⁆ = ⊥
  · by_cases heven : Even (d₀ + 1)
    · exact ⟨hr1, d₀, hd₀', heven, hcomm⟩
    ·
      have hodd₀ : Odd (d₀ + 1) := Nat.not_even_iff_odd.mp heven
      have h1 := s47_1 X.swap hswap hd' hd₀' hodd₀ (by simpa using hcomm)
      have h2 := s47_1 X H hd₀ hd hodd hRb
      have hZ1 : X.Z 1 = centerOf (X.L 1) := h2.1
      have hZ1le0 : X.Z 1 ≤ centerOf (X.L 0) := by
        have h := h2.2.2.2.1
        have h0 : X.Z 0 = centerOf (X.L 0) := by simpa using h1.1
        rw [← h0]
        exact h
      have hlebot : X.Z 1 ≤ centerOf (X.L 0) ⊓ centerOf (X.L 1) := by
        refine le_inf hZ1le0 ?_
        rw [← hZ1]
      have hbot : centerOf (X.L 0) ⊓ centerOf (X.L 1) = ⊥ := by
        simpa using X.centerOf_L_inf_succ H.char 0
      rw [hbot] at hlebot
      exact absurd (le_bot_iff.mp hlebot) (X.Z_ne_bot_of 1 (X.Q_ne_bot H.char 1))
  ·
    have hCZ := comm_Z_one X.swap hswap hd' hd₀'
    rcases hCZ with hle | ⟨hr1', hevend, hne⟩
    ·
      have hevend : Even d := by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      have hle' : ⁅X.swap.Z 1, X.swap.Z (d₀ + 1)⁆ ≤
          X.swap.Z 1 ⊓ X.swap.Z (d₀ + 1) := by simpa using hle
      have hne' : ⁅X.swap.Z 1, X.swap.Z (d₀ + 1)⁆ ≠ ⊥ := by simpa using hcomm
      have hodd_d : Odd d := s46_odd X.swap hswap hd' hd₀' hle' hne'
      exact absurd hevend (Nat.not_even_iff_odd.mpr hodd_d)
    ·
      have hne' : ⁅X.Z 1, X.Z (1 - (d : ℤ))⁆ ≠ ⊥ := by simpa using hne
      obtain ⟨t, ht, htact⟩ := X.exists_reflection H 1
      have ht1 : t • X.vert 1 = X.vert 1 := by simpa using htact 0
      have hZ1 : conjSub t (X.Z 1) = X.Z 1 := (Z_smul X X ht1).symm
      have htj : t • X.vert (1 - (d : ℤ)) = X.vert ((d : ℤ) + 1) := by
        have h := htact ((1 - (d : ℤ)) - 1)
        rw [show (1 : ℤ) + ((1 - (d : ℤ)) - 1) = 1 - (d : ℤ) by ring,
          show (1 : ℤ) - ((1 - (d : ℤ)) - 1) = (d : ℤ) + 1 by ring] at h
        exact h
      have hZb : conjSub t (X.Z (1 - (d : ℤ))) = X.Z ((d : ℤ) + 1) :=
        (Z_smul X X htj).symm
      have hconj : conjSub t ⁅X.Z 1, X.Z (1 - (d : ℤ))⁆ =
          ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ := by
        rw [← conjSub_commutator, hZ1, hZb]
      have hneB : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ ≠ ⊥ := by
        rw [← hconj]
        exact fun h => hne' (conjSub_eq_bot_iff t |>.mp h)
      exact absurd hRb hneB

private theorem relIndex_sup_eq_relIndex_inf {A B : Subgroup G}
    (hB : A ≤ Subgroup.normalizer (B : Set G)) [Finite ↥A] :
    A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B := by
  let C : Subgroup G := A ⊓ B
  have h1 : C.relIndex A * A.relIndex (A ⊔ B) = C.relIndex (A ⊔ B) :=
    Subgroup.relIndex_mul_relIndex C A (A ⊔ B) inf_le_left le_sup_left
  have h2 : C.relIndex B * B.relIndex (A ⊔ B) = C.relIndex (A ⊔ B) :=
    Subgroup.relIndex_mul_relIndex C B (A ⊔ B) inf_le_right le_sup_right
  have h3 : B.relIndex (A ⊔ B) = C.relIndex A := by
    have h := CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer (D := B) (T := A) hB
    rw [h]
    simpa [C, inf_comm] using (Subgroup.inf_relIndex_right B A).symm
  have h4 : 0 < C.relIndex A := by
    have hcard : 0 < Nat.card ↥A := Nat.card_pos
    have hm := Subgroup.relIndex_mul_card (H := C) (K := A)
    rw [inf_of_le_left (show C ≤ A from inf_le_left)] at hm
    rw [← hm] at hcard
    exact Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hcard; exact absurd hcard (by omega))
  have heq : C.relIndex A * A.relIndex (A ⊔ B) = C.relIndex A * C.relIndex B := by
    calc C.relIndex A * A.relIndex (A ⊔ B) = C.relIndex (A ⊔ B) := h1
      _ = C.relIndex B * B.relIndex (A ⊔ B) := h2.symm
      _ = C.relIndex B * C.relIndex A := by rw [h3]
      _ = C.relIndex A * C.relIndex B := mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_left h4 heq

private theorem arith_Z2G1 {d₀ d : ℕ} (b : ℤ) (hb : b = (d : ℤ) + 1) (hd0 : d₀ = d - 1)
    (hd2 : 2 ≤ d) : (b - 1 - 2).natAbs ≤ d₀ := by
  rw [hd0, hb]; omega

private theorem arith_Z2Gb {d₀ d : ℕ} (b : ℤ) (hb : b = (d : ℤ) + 1) (hd0 : d₀ = d - 1)
    (hd2 : 2 ≤ d) : (d₀ : ℤ) = b - 2 := by
  rw [hd0, hb]; omega

private theorem arith_Zr2 {d₀ d : ℕ} (r : ℕ) (b : ℤ) (hb : b = (d : ℤ) + 1)
    (hd0 : d₀ = d - 1) (hd1 : 1 ≤ d) (hr : 2 * d + 2 = r) :
    b - ((r : ℤ) - 2) = -(d₀ : ℤ) ∧ b + 1 - ((r : ℤ) - 2) = 1 - (d₀ : ℤ) ∧
      (r : ℤ) - 2 - (d₀ : ℤ) = b := by
  rw [hd0, hb]; omega

private theorem Z2_sup_Q (H : X.Sec4Hyp s r) {d₀ d : ℕ} (b : ℤ) (hb : b = (d : ℤ) + 1)
    (hd₀ : X.HasB 0 d₀) (hd0 : d₀ = d - 1) (hd2 : 2 ≤ d) :
    X.Z 2 ⊔ X.Q b = X.edgeSylow (d : ℤ) := by
  have hb0 : (d₀ : ℤ) = b - 2 := arith_Z2Gb b hb hd0 hd2
  have hd2B : X.HasB 2 d₀ := hasB_two X H hd₀
  have hZ2G1 : X.Z 2 ≤ X.Gi (b - 1) :=
    hd2B.Z_le_Gi (arith_Z2G1 b hb hd0 hd2)
  have hZ2Gb : X.Z 2 ≤ X.Gi b := by
    refine hd2B.Z_le_Gi ?_
    rw [← hb0]
    simp
  have hZ22 : IsPGroup 2 (X.Z 2) :=
    (pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)
  have hKZ2 : X.K ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi 2)
  have hZ2NotQb : ¬ X.Z 2 ≤ X.Q b := by
    have h := (X.not_Z_le_Q_edge hd2B).1
    have he : (2 : ℤ) + (d₀ : ℤ) = b := by omega
    rwa [he] at h
  have hZ2Edge : X.Z 2 ≤ X.edgeSylow (b - 1) :=
    X.le_edgeSylow_of_le_inf (b - 1) hZ22
      (le_inf hZ2G1 (by rw [sub_add_cancel]; exact hZ2Gb))
  have hsup : X.Z 2 ⊔ X.Q b = X.edgeSylow (b - 1) := by
    have hb1' : b - 1 + 1 = b := by ring
    have h := X.sup_Q_eq_edgeSylow_of_gen (b - 1) (inf_le_left.trans hKZ2) hZ2Edge
      (by rw [hb1']; exact hZ2NotQb)
    rwa [hb1'] at h
  rw [show b - 1 = (d : ℤ) by rw [hb]; ring] at hsup
  exact hsup

private theorem Zr2_le_edgeSylow (H : X.Sec4Hyp s r) {d₀ d : ℕ} (b : ℤ) (hb : b = (d : ℤ) + 1)
    (hd₀ : X.HasB 0 d₀) (hd0 : d₀ = d - 1) (hd1 : 1 ≤ d) (hr : 2 * d + 2 = r) :
    X.Z ((r : ℤ) - 2) ≤ X.edgeSylow b := by
  obtain ⟨h1, h2, -⟩ := arith_Zr2 r b hb hd0 hd1 hr
  have hdR2B : X.HasB ((r : ℤ) - 2) d₀ := hasB_r_sub_two X H hd₀
  have hd0pos : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  have hZr2Gb : X.Z ((r : ℤ) - 2) ≤ X.Gi b := by
    refine hdR2B.Z_le_Gi ?_
    rw [h1]
    omega
  have hZr2Gb1 : X.Z ((r : ℤ) - 2) ≤ X.Gi (b + 1) := by
    refine hdR2B.Z_le_Gi ?_
    rw [h2]
    omega
  have hZr22 : IsPGroup 2 (X.Z ((r : ℤ) - 2)) :=
    (pCoreOf_isPGroup' (X.Gi ((r : ℤ) - 2))).to_le (X.Z_le_Q _)
  exact X.le_edgeSylow_of_le_inf b hZr22 (le_inf hZr2Gb hZr2Gb1)

private theorem Zr2_sup_Q (H : X.Sec4Hyp s r) {d₀ d : ℕ} (b : ℤ) (hb : b = (d : ℤ) + 1)
    (hd₀ : X.HasB 0 d₀) (hd0 : d₀ = d - 1) (hd1 : 1 ≤ d) (hr : 2 * d + 2 = r) :
    X.Z ((r : ℤ) - 2) ⊔ X.Q b = X.edgeSylow b := by
  obtain ⟨-, -, h3⟩ := arith_Zr2 r b hb hd0 hd1 hr
  have hdR2B : X.HasB ((r : ℤ) - 2) d₀ := hasB_r_sub_two X H hd₀
  have hKZr2 : X.K ≤ Subgroup.normalizer (X.Z ((r : ℤ) - 2) : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi ((r : ℤ) - 2))
  have hZr2NotQb : ¬ X.Z ((r : ℤ) - 2) ≤ X.Q b := by
    have h := (X.not_Z_le_Q_edge hdR2B).2
    rwa [h3] at h
  exact X.sup_Q_eq_edgeSylow_of_left_gen b (inf_le_left.trans hKZr2)
    (Zr2_le_edgeSylow X H b hb hd₀ hd0 hd1 hr) hZr2NotQb

private theorem le_of_odd_card {T E L : Subgroup G} (hT : Odd (Nat.card ↥T))
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) (hEL : E ≤ L) (hTL : T ≤ L) {j : ℕ}
    (hdvd : E.relIndex L ∣ 2 ^ j) : T ≤ E := by
  have h1 : E.relIndex (T ⊔ E) ∣ E.relIndex L :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex E (T ⊔ E) L le_sup_right (sup_le hTL hEL))
  rw [CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hTE] at h1
  have hcop : Nat.Coprime (Nat.card ↥T) (2 ^ j) := (Nat.coprime_two_right.mpr hT).pow_right j
  exact Subgroup.relIndex_eq_one.mp
    ((hcop.coprime_dvd_left (Subgroup.relIndex_dvd_card E T)).eq_one_of_dvd (h1.trans hdvd))

private theorem Ki_le_E (H : X.Sec4Hyp s r) {d₀ d : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd0 : d₀ = d - 1) (hd1 : 1 ≤ d) (hr : 2 * d + 2 = r)
    (hEQ : (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊔ X.Q ((d : ℤ) + 1) = X.L ((d : ℤ) + 1)) :
    X.Ki ((d : ℤ) + 1) ≤ X.Z 2 ⊔ X.Z ((r : ℤ) - 2) := by
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hd0pos : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  have hd2 : 2 ≤ d := by omega
  have hb0 : (d₀ : ℤ) = b - 2 := arith_Z2Gb b hbdef hd0 hd2
  have hd2B : X.HasB 2 d₀ := hasB_two X H hd₀
  have hdR2B : X.HasB ((r : ℤ) - 2) d₀ := hasB_r_sub_two X H hd₀
  have hZ2Gb : X.Z 2 ≤ X.Gi b := by
    refine hd2B.Z_le_Gi ?_
    rw [← hb0]
    simp
  have hZr2Gb : X.Z ((r : ℤ) - 2) ≤ X.Gi b := by
    refine hdR2B.Z_le_Gi ?_
    obtain ⟨h1, -, -⟩ := arith_Zr2 r b hbdef hd0 hd1 hr
    rw [h1]
    omega
  have hZ22 : IsPGroup 2 (X.Z 2) :=
    (pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)
  have hZr22 : IsPGroup 2 (X.Z ((r : ℤ) - 2)) :=
    (pCoreOf_isPGroup' (X.Gi ((r : ℤ) - 2))).to_le (X.Z_le_Q _)
  have hKZ2 : X.K ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi 2)
  have hKZr2 : X.K ≤ Subgroup.normalizer (X.Z ((r : ℤ) - 2) : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi ((r : ℤ) - 2))
  have hE_L : X.Z 2 ⊔ X.Z ((r : ℤ) - 2) ≤ X.L b :=
    sup_le (le_oTwoPrime_of_isPGroup hZ22 hZ2Gb) (le_oTwoPrime_of_isPGroup hZr22 hZr2Gb)
  have hE_normQ : X.Z 2 ⊔ X.Z ((r : ℤ) - 2) ≤
      Subgroup.normalizer (X.Q b : Set G) :=
    hE_L.trans ((X.L_le_Gi b).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi b)))
  haveI hEfin : Finite ↥(X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 2 ⊔ X.Z ((r : ℤ) - 2))
      (hE_L.trans (X.L_le_Gi b))
  have hrel : (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)).relIndex (X.L b) =
      ((X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊓ X.Q b).relIndex (X.Q b) := by
    rw [← hEQ]
    exact relIndex_sup_eq_relIndex_inf hE_normQ
  have hdvd : (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)).relIndex (X.L b) ∣ Nat.card (X.Q b) := by
    rw [hrel]
    have hm := Subgroup.relIndex_mul_card
      (H := (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊓ X.Q b) (K := X.Q b)
    rw [inf_of_le_left (show (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊓ X.Q b ≤ X.Q b from inf_le_right)] at hm
    exact ⟨Nat.card ↥((X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊓ X.Q b), hm.symm⟩
  have hKi_normE : X.Ki b ≤
      Subgroup.normalizer (((X.Z 2 ⊔ X.Z ((r : ℤ) - 2) : Subgroup G) : Set G)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : Subgroup.map (↑(MulAut.conj x)) (X.Z 2) = X.Z 2 := by
      have h := hKZ2 hx.1
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    have h2 : Subgroup.map (↑(MulAut.conj x)) (X.Z ((r : ℤ) - 2)) = X.Z ((r : ℤ) - 2) := by
      have h := hKZr2 hx.1
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    rw [Subgroup.map_sup, h1, h2]
  have hKiodd : Odd (Nat.card ↥(X.Ki b)) := by
    rw [X.card_Ki b]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by have := H.two_le_n b; omega)) odd_one
  haveI hQfin : Finite ↥(X.Q b) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi b)
  have hQ2 : IsPGroup 2 ↥(X.Q b) := pCoreOf_isPGroup' (X.Gi b)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ2
  have hdvd' : (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)).relIndex (X.L b) ∣ 2 ^ j := by
    rw [← hj]
    exact hdvd
  exact le_of_odd_card hKiodd hKi_normE hE_L inf_le_right hdvd'

private theorem commutator_mem_of_centralizes {k : G} {A Q : Subgroup G}
    (hkA : k ∈ Subgroup.centralizer (A : Set G))
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) : ∀ x ∈ A ⊔ Q, ⁅k, x⁆ ∈ Q := by
  intro x hx
  change x ∈ ((A ⊔ Q : Subgroup G) : Set G) at hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ] at hx
  obtain ⟨a, ha, q, hq, rfl⟩ := hx
  have hka : k * a * k⁻¹ = a := by
    have hc := (Subgroup.mem_centralizer_iff.mp hkA) a ha
    calc k * a * k⁻¹ = (a * k) * k⁻¹ := by rw [hc]
      _ = a := by group
  have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hkQ q).mp hq
  have hmid : k * q * k⁻¹ * q⁻¹ ∈ Q := Q.mul_mem hkq (Q.inv_mem hq)
  have hconj : a * (k * q * k⁻¹ * q⁻¹) * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hAQ ha) _).mp hmid
  have heq : k * (a * q) * k⁻¹ * (a * q)⁻¹ = a * (k * q * k⁻¹ * q⁻¹) * a⁻¹ := by
    calc k * (a * q) * k⁻¹ * (a * q)⁻¹
        = (k * a * k⁻¹) * (k * q * k⁻¹) * q⁻¹ * a⁻¹ := by group
      _ = a * (k * q * k⁻¹) * q⁻¹ * a⁻¹ := by rw [hka]
      _ = a * (k * q * k⁻¹ * q⁻¹) * a⁻¹ := by group
  rw [commutatorElement_def, heq]
  exact hconj

private theorem S_eq_Qg_sup_Q_zero (H : X.Sec4Hyp s r) : X.S = X.Qg r ⊔ X.Q 0 := by
  have hrpos : (0 : ℤ) < r := H.longReg.1.1
  have hQgne : X.Qg r ≠ ⊥ := X.Qg_ne_bot H
  have hQgne' : pCoreOf 2 (X.arcStab 0 (0 + (r : ℤ))) ≠ ⊥ := by simpa using hQgne
  have hp := X.pCoreOf_arcStab_r H 0 hQgne'
  have hQg_inf_Q0 : X.Qg r ⊓ X.Q 0 = ⊥ := by simpa using hp.2.1
  have hQg_le_G0 : X.Qg r ≤ X.Gi 0 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab 0 r)).trans (X.arcStab_le_Gi_left hrpos)
  have hKQg : X.K ≤ Subgroup.normalizer (X.Qg r : Set G) := by
    intro x hx
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.arcStab 0 r))
      ((X.K_le_GT.trans (X.GT_le_arcStab 0 (r : ℤ))) hx)
  have hnotQ0 : ¬ X.Qg r ≤ X.Q 0 := by
    intro hle
    have h1 : X.Qg r ⊓ X.Q 0 = X.Qg r := inf_eq_left.mpr hle
    rw [hQg_inf_Q0] at h1
    exact hQgne h1.symm
  have hG1 : X.Qg r ≤ X.Gi 1 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab 0 r)).trans
      (X.arcStab_le_Gi_of_between (by norm_num) (by omega))
  have hQgEdge0 : X.Qg r ≤ X.edgeSylow 0 :=
    X.le_edgeSylow_of_le_inf 0 (pCoreOf_isPGroup' (X.arcStab 0 r))
      (le_inf hQg_le_G0 (by simpa using hG1))
  rw [← X.edgeSylow_zero]
  exact (X.sup_Q_eq_edgeSylow_of_left_gen 0 (inf_le_left.trans hKQg) hQgEdge0 hnotQ0).symm

private theorem Ki_eq_bot_of_fixes {b : ℤ} {k : G}
    (hgen : Subgroup.zpowers k = X.Ki b) (hkGi : ∀ i : ℤ, k ∈ X.Gi i)
    (hodd : Odd (orderOf k)) (hfix0 : ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w)
    (hfix1 : ∀ w : V, Γ.Adj (X.vert 1) w → k • w = w) : X.Ki b = ⊥ := by
  have hcent_norm : Subgroup.centralizer ({k} : Set G) ≤
      Subgroup.normalizer (X.Ki b : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomm : g * k = k * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgk : Subgroup.map (↑(MulAut.conj g) : G →* G) (Subgroup.zpowers k) =
        Subgroup.zpowers k := by
      rw [MonoidHom.map_zpowers]
      have hval : (↑(MulAut.conj g) : G →* G) k = k := by
        show g * k * g⁻¹ = k
        rw [hcomm]; group
      rw [hval]
    rw [← hgen]
    exact hgk
  have hα : ∀ a c : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) c →
      ∃ g ∈ Subgroup.normalizer (X.Ki b : Set G) ⊓ X.Gi 0, g • a = c := by
    intro a c ha hc
    obtain ⟨g, hg, hgac⟩ := X.centralizer_transitive 0 (hkGi (0 - 1)) (hkGi 0) hodd hfix0 a c ha hc
    exact ⟨g, ⟨hcent_norm hg.1, hg.2⟩, hgac⟩
  have hβ : ∀ a c : V, Γ.Adj (X.vert 1) a → Γ.Adj (X.vert 1) c →
      ∃ g ∈ Subgroup.normalizer (X.Ki b : Set G) ⊓ X.Gi 1, g • a = c := by
    intro a c ha hc
    obtain ⟨g, hg, hgac⟩ := X.centralizer_transitive 1 (hkGi (1 - 1)) (hkGi 1) hodd hfix1 a c ha hc
    exact ⟨g, ⟨hcent_norm hg.1, hg.2⟩, hgac⟩
  exact eq_bot_of_normalizer_trans X.hyp (X.adj 0)
    (le_inf (inf_le_left.trans (X.K_le_Gi 0)) (inf_le_left.trans (X.K_le_Gi 1))) hα hβ

private theorem not_Ki_le_Z_two_sup_Z_sub_two (H : X.Sec4Hyp s r) {d : ℕ} (hd : X.HasB 1 d)
    (hr : 2 * d + 2 = r) (b : ℤ) (hb : b = (d : ℤ) + 1) (hdZb : X.HasB b d)
    (hZbc' : X.Z b = centerOf (X.L b)) :
    ¬ X.Ki b ≤ X.Z 2 ⊔ X.Z ((r : ℤ) - 2) := by
  intro hKi_le_E
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  have hrpos : (0 : ℤ) < r := H.longReg.1.1
  obtain ⟨k, hk, hk1, hkord, hgen⟩ := X.exists_generator_Ki b (H.two_le_n b)
  have hkK : k ∈ X.K := hk.1
  have hkL : k ∈ X.L b := hk.2
  have hkGi : ∀ i : ℤ, k ∈ X.Gi i := fun i => X.K_le_Gi i hkK
  have hoddk : Odd (orderOf k) := by
    rw [hkord]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by have := H.two_le_n b; omega)) odd_one
  have hQg_le_Q2 : X.Qg r ≤ X.Q 2 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by omega)
  have hQg_le_Qr2 : X.Qg r ≤ X.Q ((r : ℤ) - 2) :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by omega) (by omega)
  have hQg_le_G0 : X.Qg r ≤ X.Gi 0 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab 0 r)).trans (X.arcStab_le_Gi_left hrpos)
  have hE_cent_Qg : X.Z 2 ⊔ X.Z ((r : ℤ) - 2) ≤
      Subgroup.centralizer (X.Qg r : Set G) := by
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2) q (hQg_le_Q2 hq)
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center ((r : ℤ) - 2) hz)).2) q (hQg_le_Qr2 hq)
  have hk_cent_Qg : k ∈ Subgroup.centralizer (X.Qg r : Set G) := hE_cent_Qg (hKi_le_E hk)
  have hk_cent_Zb : k ∈ Subgroup.centralizer (X.Z b : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzL : z ∈ Subgroup.centralizer (X.L b : Set G) := by
      rw [hZbc'] at hz
      exact (Subgroup.mem_inf.mp hz).2
    exact (hzL k hkL).symm
  have hS_eq : X.S = X.Qg r ⊔ X.Q 0 := S_eq_Qg_sup_Q_zero X H
  have hsupZb : X.Z b ⊔ X.Q 1 = X.edgeSylow 1 := by
    have hdZb' : X.HasB ((d : ℤ) + 1) d := by
      rw [← hb]
      exact hdZb
    rw [hb]
    exact Z_succ_sup_Q_one_eq_edgeSylow X H hdZb'
  have hZbG1 : X.Z b ≤ X.Gi 1 := hdZb.Z_le_Gi (by omega)
  have hcomm0 : ∀ x ∈ X.S, ⁅k, x⁆ ∈ X.Q 0 := by
    intro x hx
    rw [hS_eq] at hx
    exact commutator_mem_of_centralizes hk_cent_Qg
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) (hkGi 0))
      (hQg_le_G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))) x hx
  have hcomm1 : ∀ x ∈ X.edgeSylow 1, ⁅k, x⁆ ∈ X.Q 1 := by
    intro x hx
    rw [← hsupZb] at hx
    exact commutator_mem_of_centralizes hk_cent_Zb
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1) (hkGi 1))
      (hZbG1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))) x hx
  have hfix0 := X.fixes_neighbors_of_centralizes_edgeSylow_left_gen 0 (hkGi 1) (hkGi 0) hoddk
    (fun x hx => hcomm0 x (by rwa [X.edgeSylow_zero] at hx))
  have hfix1 := X.fixes_neighbors_of_centralizes_edgeSylow_left_gen 1 (hkGi 2) (hkGi 1) hoddk
    hcomm1
  have hKi_bot := Ki_eq_bot_of_fixes X hgen hkGi hoddk hfix0 hfix1
  rw [hKi_bot] at hk
  exact hk1 (Subgroup.mem_bot.mp hk)

private theorem s47_3 (H : X.Sec4Hyp s r) {d₀ d : ℕ} (hd₀ : X.HasB 0 d₀) (hd : X.HasB 1 d)
    (hodd : Odd (d + 1)) (hR : ⁅X.Z 1, X.Z (d + 1)⁆ = ⊥) (hr : 2 * d + 2 = r) : False := by
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  have hd2 : 2 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hb : b = (d : ℤ) + 1 := hbdef
  have hbc : ((d + 1 : ℕ) : ℤ) = b := by rw [hb]; push_cast; ring
  obtain ⟨-, hZbc, -, -, hle⟩ := s47_1 X H hd₀ hd hodd hR
  have hZbc' : X.Z b = centerOf (X.L b) := by simpa [hbc] using hZbc
  have hd0 : d₀ = d - 1 := by
    have hb' := X.hasB_zero_bounds H hd₀
    omega
  have hdZb : X.HasB b d := hasB_succ_of_odd X H hd hodd
  have h1 : X.Z 2 ⊔ X.Q b = X.edgeSylow (d : ℤ) := Z2_sup_Q X H b hb hd₀ hd0 hd2
  have h2 : X.Z ((r : ℤ) - 2) ⊔ X.Q b = X.edgeSylow b := Zr2_sup_Q X H b hb hd₀ hd0 hd1 hr
  have hS1 : X.edgeSylow (d : ℤ) = X.edgeSylow (b - 1) := by
    congr 1
    rw [hb]; ring
  have hEQ : (X.Z 2 ⊔ X.Z ((r : ℤ) - 2)) ⊔ X.Q b = X.L b := by
    rw [sup_sup_distrib_right, h1, h2, hS1]
    exact X.edgeSylow_sup_edgeSylow b
  have hKi_le_E : X.Ki b ≤ X.Z 2 ⊔ X.Z ((r : ℤ) - 2) :=
    Ki_le_E X H hd₀ hd0 hd1 hr hEQ
  exact not_Ki_le_Z_two_sup_Z_sub_two X H hd hr b hb hdZb hZbc' hKi_le_E

theorem comm_eq_bot_switch
    (H : X.Sec4Hyp s r) {d : ℕ}
    (hd : X.HasB 1 d) (hodd : Odd (d + 1)) (hR : ⁅X.Z 1, X.Z (d + 1)⁆ = ⊥) :
    r + 1 = s ∧ ∃ d' : ℕ, X.swap.HasB 1 d' ∧ Even (d' + 1) ∧
      ⁅X.swap.Z 1, X.swap.Z ((d' : ℤ) + 1)⁆ = ⊥ := by
  obtain ⟨d₀, hd₀⟩ := X.exists_hasB H 0
  obtain ⟨h2d, hrle⟩ := X.hasB_one_bounds H hd
  rcases Nat.lt_or_ge (2 * d) r with hlt | hge
  ·
    have hr : 2 * d + 2 = r := by
      obtain ⟨k, hk⟩ := H.even_r
      omega
    exact (s47_3 X H hd₀ hd hodd hR hr).elim
  · have hr : 2 * d = r := by omega
    exact s47_2 X H hd₀ hd hodd hR hr

end Setup

end CFSG.Quasithin.St84
