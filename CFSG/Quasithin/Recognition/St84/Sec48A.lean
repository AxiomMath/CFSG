module

public import CFSG.Quasithin.Recognition.St84.Sec4Bounds
public import CFSG.Quasithin.Recognition.St84.Sec4Local
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.St84.Sec6QQuot

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

structure Comm48 (X : Setup Γ G) (s r d : ℕ) : Prop where
  hyp : X.Sec4Hyp s r
  hasB : X.HasB 1 d
  even : Even (d + 1)
  comm : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥

abbrev ZQ (d : ℕ) : Subgroup G := X.Z 1 ⊓ X.Q ((d : ℤ) + 1)

variable {r d : ℕ}

variable {X}

namespace Comm48

private theorem conjSub_reflection_arcStab {i a : ℤ} {t : G}
    (href : ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) :
    conjSub t (X.arcStab a (a + 1)) = X.arcStab (2 * i - a - 1) (2 * i - a) := by
  unfold Setup.arcStab
  rw [conjSub_fixSet]
  congr 1
  ext v
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨i + (i - j), ?_, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (j - i)
      rw [show i + (j - i) = j by ring, show i - (j - i) = 2 * i - j by ring] at h
      rw [h]
      congr 1
      ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨X.vert (i + (i - j)), ⟨i + (i - j), ?_, rfl⟩, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (i - j)
      simpa [show i + (i - j) = 2 * i - j by ring,
        show i - (i - j) = j by ring] using h

private theorem conjSub_reflection_edgeSylow {i : ℤ} {t : G}
    (href : ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) :
    conjSub t (X.edgeSylow (i - 1)) = X.edgeSylow i := by
  have h1 : X.edgeSylow (i - 1) = pCoreOf 2 (X.arcStab (i - 1) ((i - 1) + 1)) := by
    rw [X.arcStab_eq_inf (by omega)]
  have h2 : X.edgeSylow i = pCoreOf 2 (X.arcStab i (i + 1)) := by
    rw [X.arcStab_eq_inf (by omega)]
  rw [h1, h2, ← pCoreOf_conjSub, conjSub_reflection_arcStab (X := X) (a := i - 1) href]
  rw [show 2 * i - (i - 1) - 1 = i by ring, show 2 * i - (i - 1) = i + 1 by ring]

private theorem s48_0_sup_Q (C : X.Comm48 s r d) :
    X.Z 1 ⊔ X.Q ((d : ℤ) + 1) = X.edgeSylow d := by
  have hd : X.HasB 1 d := C.hasB
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  have hZ1d1 : X.Z 1 ≤ X.Gi ((d : ℤ) + 1) := by
    have h := hd.1 (d : ℤ) (by simp)
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hZ1d : X.Z 1 ≤ X.Gi d := by
    have h := hd.1 ((d : ℤ) - 1) (by omega)
    have e : (1 : ℤ) + ((d : ℤ) - 1) = (d : ℤ) := by ring
    rwa [e] at h
  have hZ1edge : X.Z 1 ≤ X.edgeSylow d :=
    X.le_edgeSylow_of_le_inf d ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
      (le_inf hZ1d hZ1d1)
  have hnot : ¬ X.Z 1 ≤ X.Q ((d : ℤ) + 1) := by
    intro h
    apply hd.2.1
    have h' := h.trans ((X.Q_le_Gi_adj (i := (d : ℤ) + 1)).trans inf_le_right)
    have e : (1 : ℤ) + (d : ℤ) + 1 = (d : ℤ) + 2 := by ring
    simpa [e, add_comm, add_left_comm, add_assoc] using h'
  have hK : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 1) = X.Z 1
    exact X.Z_normal 1 k (X.K_le_Gi 1 hk)
  have hS := X.sup_Q_eq_edgeSylow_of_gen (i := d) (A := X.Z 1)
    (inf_le_left.trans hK) hZ1edge hnot
  exact hS

private theorem s48_0_Z_le_centerOf_L (C : X.Comm48 s r d) :
    X.Z ((d : ℤ) + 1) ≤ centerOf (X.L ((d : ℤ) + 1)) := by
  have hS : X.Z 1 ⊔ X.Q ((d : ℤ) + 1) = X.edgeSylow d := s48_0_sup_Q C
  have hZbC : X.edgeSylow d ≤ Subgroup.centralizer (X.Z ((d : ℤ) + 1) : Set G) := by
    rw [← hS]
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hmem : ⁅z, y⁆ ∈ ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ :=
        Subgroup.commutator_mem_commutator hz hy
      have hbot : ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ = ⊥ := C.comm
      have hone : ⁅z, y⁆ = 1 := by simpa [hbot] using hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (X.Z_le_center ((d : ℤ) + 1) hy).2) q hq).symm
  have hZb_edge : X.edgeSylow ((d : ℤ) + 1) ≤
      Subgroup.centralizer (X.Z ((d : ℤ) + 1) : Set G) := by
    obtain ⟨t, ht, href, -⟩ := X.exists_reflection_oTwoRes C.hyp ((d : ℤ) + 1)
    have htGi : t ∈ X.Gi ((d : ℤ) + 1) :=
      X.L_le_Gi ((d : ℤ) + 1) (oTwoRes_le (X.L ((d : ℤ) + 1)) (Subgroup.mem_inf.mp ht).1)
    have hZt : conjSub t (X.Z ((d : ℤ) + 1)) = X.Z ((d : ℤ) + 1) :=
      X.Z_normal ((d : ℤ) + 1) t htGi
    have hedge : conjSub t (X.edgeSylow (((d : ℤ) + 1) - 1)) = X.edgeSylow ((d : ℤ) + 1) :=
      conjSub_reflection_edgeSylow (X := X) (i := (d : ℤ) + 1) href
    rw [show ((d : ℤ) + 1) - 1 = (d : ℤ) by ring] at hedge
    have hconj : conjSub t (X.edgeSylow d) ≤
        Subgroup.centralizer (conjSub t (X.Z ((d : ℤ) + 1)) : Set G) := by
      have h := conjSub_mono t hZbC
      rw [conjSub_centralizer]
      exact h
    rwa [hedge, hZt] at hconj
  exact X.le_centerOf_L C.hyp.char ((d : ℤ) + 1) (X.Z_le_Gi ((d : ℤ) + 1)) (by simpa using hZbC) hZb_edge

end Comm48

variable (X) in
open Comm48 in
theorem s48_0 (C : X.Comm48 s r d) :
    X.Z ((d : ℤ) + 1) = centerOf (X.L ((d : ℤ) + 1)) ∧ X.Z 0 = centerOf (X.L 0) := by
  have hZb_eq : X.Z ((d : ℤ) + 1) = centerOf (X.L ((d : ℤ) + 1)) :=
    le_antisymm (s48_0_Z_le_centerOf_L C) (X.centerOf_L_le_Z C.hyp.char ((d : ℤ) + 1))
  obtain ⟨m, hm⟩ := C.even
  have hb2 : (d : ℤ) + 1 = 2 * (m : ℤ) := by
    have hcast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
    rw [← hcast, hm]
    push_cast
    ring
  have hZtrans : X.Z ((d : ℤ) + 1) = conjSub (X.τ ^ (m : ℤ)) (X.Z 0) := by
    have h := X.Z_add (m : ℤ) 0
    rwa [show (0 : ℤ) + 2 * (m : ℤ) = (d : ℤ) + 1 by omega] at h
  have hLtrans : X.L ((d : ℤ) + 1) = conjSub (X.τ ^ (m : ℤ)) (X.L 0) := by
    have h := X.L_add (m : ℤ) 0
    rwa [show (0 : ℤ) + 2 * (m : ℤ) = (d : ℤ) + 1 by omega] at h
  have hZ0eq : X.Z 0 = centerOf (X.L 0) := by
    refine (conjSub_inj (X.τ ^ (m : ℤ))).mp ?_
    calc conjSub (X.τ ^ (m : ℤ)) (X.Z 0)
        = X.Z ((d : ℤ) + 1) := hZtrans.symm
      _ = centerOf (X.L ((d : ℤ) + 1)) := hZb_eq
      _ = centerOf (conjSub (X.τ ^ (m : ℤ)) (X.L 0)) := by rw [← hLtrans]
      _ = conjSub (X.τ ^ (m : ℤ)) (centerOf (X.L 0)) := centerOf_conjSub _ _
  exact ⟨hZb_eq, hZ0eq⟩

namespace Comm48

private theorem s48_1_Z0_le_Z1 (C : X.Comm48 s r d) : X.Z 0 ≤ X.Z 1 := by
  have h0 : X.Z 0 = centerOf (X.L 0) := (X.s48_0 C).2
  have hSsyl0 : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_Gi 0
  have hSsyl1 : IsSylowTwoOf X.S (X.Gi 1) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hSL0 : X.S ≤ X.L 0 := by
    have h := X.edgeSylow_le_L 0
    simpa [X.edgeSylow_zero] using h
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := by
    rw [h0]
    exact (X.centerOf_L_le_Q_adj C.hyp.char 0).2
  have hQ1S : X.Q 1 ≤ X.S := by
    have h := X.Q_le_edgeSylow (i := 0)
    simpa [X.edgeSylow_zero] using h
  have hZ0S : X.Z 0 ≤ X.S := hZ0Q1.trans hQ1S
  have hZ0C : X.Z 0 ≤ Subgroup.centralizer (X.S : Set G) := by
    refine (Subgroup.le_centralizer_iff).mpr ?_
    rw [h0]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s (hSL0 hs)).symm
  exact (le_inf hZ0S hZ0C).trans (X.centerOf_sylow_le_Z C.hyp.char 1 hSsyl1).1

end Comm48

variable (X) in
open Comm48 in
theorem s48_1 (C : X.Comm48 s r d) :
    X.Z 0 ≤ X.Z 1 ∧ ∀ j : ℤ, Odd j → centerOf (X.L j) = ⊥ := by
  have h0 : X.Z 0 = centerOf (X.L 0) := (X.s48_0 C).2
  have hSsyl0 : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_Gi 0
  have hSL1 : X.S ≤ X.L 1 := by
    have h := (X.isSylowTwoOf_edgeSylow_L_succ 0).1
    simpa [X.edgeSylow_zero] using h
  have hZ1L0 : centerOf (X.L 1) ≤ X.Z 0 := by
    have hQ0 : centerOf (X.L 1) ≤ X.Q 0 := (X.centerOf_L_le_Q_adj C.hyp.char 0).1
    have hS : centerOf (X.L 1) ≤ X.S := hQ0.trans (X.Q_le_edgeSylow_left 0)
    have hC : centerOf (X.L 1) ≤ Subgroup.centralizer (X.S : Set G) := by
      refine (Subgroup.le_centralizer_iff).mpr ?_
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s (hSL1 hs)).symm
    exact (le_inf hS hC).trans (X.centerOf_sylow_le_Z C.hyp.char 0 hSsyl0).1
  have hZ1ZL0 : centerOf (X.L 1) ≤ centerOf (X.L 0) := by
    rwa [h0] at hZ1L0
  have hZ1bot : centerOf (X.L 1) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hmem : z ∈ centerOf (X.L 0) ⊓ centerOf (X.L 1) :=
      Subgroup.mem_inf.mpr ⟨hZ1ZL0 hz, hz⟩
    have hinf := X.centerOf_L_inf_succ C.hyp.char 0
    simp only [zero_add] at hinf
    rw [hinf] at hmem
    exact hmem
  refine ⟨s48_1_Z0_le_Z1 C, ?_⟩
  intro j hj
  obtain ⟨k, hk⟩ := hj
  rw [hk, show 2 * k + 1 = 1 + 2 * k by ring]
  rw [X.L_add k 1, centerOf_conjSub, hZ1bot]
  exact (conjSub_eq_bot_iff (X.τ ^ k)).mpr rfl

namespace Comm48

private theorem s48_2_bounds (C : X.Comm48 s r d) :
    X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r := by
  have hd : X.HasB 1 d := C.hasB
  obtain ⟨d0, hd0⟩ := X.exists_hasB C.hyp 0
  have hZ01 : X.Z 0 ≤ X.Z 1 := (X.s48_1 C).1
  have hZ0b : X.Z 0 ≤ X.Gi ((d : ℤ) + 1) := by
    have h := hd.1 (d : ℤ) (by simp)
    exact hZ01.trans (by simpa [add_comm, add_left_comm, add_assoc] using h)
  have hbmem : ((d : ℤ) + 1) ∈ X.fixSet (X.Z 0) := by
    intro z hz
    exact MulAction.mem_stabilizer_iff.mp (hZ0b hz)
  have hd0ge : d + 1 ≤ d0 := by
    have h := hbmem
    rw [X.fixSet_Z 0 hd0, Set.mem_Icc] at h
    have hz : ((d : ℤ) + 1) ≤ (d0 : ℤ) := by simpa using h.2
    exact_mod_cast hz
  have hb1 := X.hasB_one_bounds C.hyp hd
  have hb0 := X.hasB_zero_bounds C.hyp hd0
  have hd0eq : d0 = d + 1 := by omega
  have hreq : 2 * (d + 1) = r := by omega
  rw [hd0eq] at hd0
  exact ⟨hd0, hreq⟩

private theorem s48_2_Z0_arc (C : X.Comm48 s r d) :
    X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) := by
  have hd0 : X.HasB 0 (d + 1) := (s48_2_bounds C).1
  have hreq : 2 * (d + 1) = r := (s48_2_bounds C).2
  set b : ℤ := (d : ℤ) + 1 with hb
  have hr2 : (r : ℤ) = 2 * b := by
    rw [← hreq, hb]
    push_cast
    ring
  have hZ0_2 : IsPGroup 2 (X.Z 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
  have hZ0ne : X.Z 0 ≠ ⊥ := X.Z_ne_bot_of 0 (X.Q_ne_bot C.hyp.char 0)
  have hK0 : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 0) = X.Z 0
    exact X.Z_normal 0 k (X.K_le_Gi 0 hk)
  have hZ0fix : X.Z 0 ≤ X.arcStab (-b) b := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [X.fixSet_Z 0 hd0]
    rw [Set.mem_Icc] at hj ⊢
    push_cast at hj ⊢
    omega
  have harc_eq : -b + (r : ℤ) = b := by omega
  have hZ0arc : X.Z 0 = pCoreOf 2 (X.arcStab (-b) b) := by
    have hfix : X.Z 0 ≤ X.arcStab (-b) ((-b) + (r : ℤ)) := by
      rw [harc_eq]
      exact hZ0fix
    have hle : X.Z 0 ≤ pCoreOf 2 (X.arcStab (-b) ((-b) + (r : ℤ))) :=
      X.le_pCoreOf_arcStab_r C.hyp hZ0_2 hfix
    have h := X.eq_of_le_pCoreOf_arcStab_r C.hyp hK0 hZ0ne hle
    simpa [harc_eq] using h
  simpa [hb] using hZ0arc

private theorem s48_2_Z0_props (C : X.Comm48 s r d) :
    Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥ := by
  have hZ0arc := s48_2_Z0_arc C
  have hreq : 2 * (d + 1) = r := (s48_2_bounds C).2
  set b : ℤ := (d : ℤ) + 1 with hb
  have hr2 : (r : ℤ) = 2 * b := by
    rw [← hreq, hb]
    push_cast
    ring
  have harc_eq : -b + (r : ℤ) = b := by omega
  have hZ0arc' : X.Z 0 = pCoreOf 2 (X.arcStab (-b) b) := by
    simpa [hb] using hZ0arc
  have hPne' : pCoreOf 2 (X.arcStab (-b) ((-b) + (r : ℤ))) ≠ ⊥ := by
    rw [harc_eq, ← hZ0arc']
    exact X.Z_ne_bot_of 0 (X.Q_ne_bot C.hyp.char 0)
  have hPcard := X.pCoreOf_arcStab_r C.hyp (-b) hPne'
  have hcardP : Nat.card (pCoreOf 2 (X.arcStab (-b) b)) = 2 ^ X.n (-b) := by
    simpa [harc_eq] using hPcard.1
  have hintP : pCoreOf 2 (X.arcStab (-b) b) ⊓ X.Q (-b) = ⊥ := by
    simpa [harc_eq] using hPcard.2.1
  have hintPb : pCoreOf 2 (X.arcStab (-b) b) ⊓ X.Q b = ⊥ := by
    have h := hPcard.2.2.1
    rwa [harc_eq] at h
  have helemP : IsElemAbelian 2 (pCoreOf 2 (X.arcStab (-b) b)) := by
    simpa [harc_eq] using X.isElemAbelian_pCoreOf_arcStab_r C.hyp (-b)
  obtain ⟨m, hm⟩ := C.even
  have hb2 : b = 2 * (m : ℤ) := by
    rw [hb]
    have hcast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
    rw [← hcast, hm]
    push_cast
    ring
  have hn_neg : X.n (-b) = X.n 0 := by
    have h := X.n_add (-(m : ℤ)) 0
    rwa [show (0 : ℤ) + 2 * (-(m : ℤ)) = -b by rw [hb2]; ring] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hZ0arc', hcardP, hn_neg]
  · rw [hZ0arc']
    exact helemP
  · rw [hZ0arc']
    exact hintPb
  · rw [hZ0arc']
    exact hintP

end Comm48

variable (X) in
open Comm48 in
theorem s48_2 (C : X.Comm48 s r d) :
    X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r ∧ X.Z ((d : ℤ) + 1) = X.Qg r ∧
      X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥ := by
  obtain ⟨hd0, hreq⟩ := s48_2_bounds C
  have hZ0arc := s48_2_Z0_arc C
  obtain ⟨hcard, helem, hintb, hintnb⟩ := s48_2_Z0_props C
  set b : ℤ := (d : ℤ) + 1 with hb
  obtain ⟨m, hm⟩ := C.even
  have hb2 : b = 2 * (m : ℤ) := by
    rw [hb]
    have hcast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
    rw [← hcast, hm]
    push_cast
    ring
  have hr2 : (r : ℤ) = 2 * b := by
    rw [← hreq, hb]
    push_cast
    ring
  have hZ0arc' : X.Z 0 = pCoreOf 2 (X.arcStab (-b) b) := by
    simpa [hb] using hZ0arc
  have hZtrans : X.Z b = conjSub (X.τ ^ (m : ℤ)) (X.Z 0) := by
    have h := X.Z_add (m : ℤ) 0
    rwa [show (0 : ℤ) + 2 * (m : ℤ) = b by omega] at h
  have harcConj : conjSub (X.τ ^ (m : ℤ)) (X.arcStab (-b) b) = X.arcStab 0 (r : ℤ) := by
    have h := X.arcStab_add (m : ℤ) (-b) b
    rw [show -b + 2 * (m : ℤ) = 0 by omega,
      show b + 2 * (m : ℤ) = (r : ℤ) by omega] at h
    exact h.symm
  have hZbQg : X.Z b = X.Qg r := by
    rw [hZtrans, hZ0arc']
    unfold Setup.Qg
    rw [← pCoreOf_conjSub, harcConj]
  refine ⟨hd0, hreq, ?_, hZ0arc, hcard, helem, hintb, hintnb⟩
  simpa [hb] using hZbQg

namespace Comm48

private theorem commutator_ZQ_Z_sup (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.ZQ d ⊔ X.Q ((d : ℤ) + 2) = X.edgeSylow ((d : ℤ) + 1) := by
  set b : ℤ := (d : ℤ) + 1 with hb
  have hb1 : b + 1 = (d : ℤ) + 2 := by rw [hb]; ring
  have e2 : (d : ℤ) + 1 + 1 = (d : ℤ) + 2 := by ring
  have hHQb : X.ZQ d ≤ X.Q b := by unfold Setup.ZQ; exact inf_le_right
  have hH2 : IsPGroup 2 (X.ZQ d) :=
    (pCoreOf_isPGroup' (X.Gi b)).to_le hHQb
  have hHGi : X.ZQ d ≤ X.Gi b := hHQb.trans (X.Q_le_Gi b)
  have hHGi1 : X.ZQ d ≤ X.Gi (b + 1) :=
    hHQb.trans ((X.Q_le_Gi_adj b).trans inf_le_right)
  have hHedge : X.ZQ d ≤ X.edgeSylow b :=
    X.le_edgeSylow_of_le_inf b hH2 (le_inf hHGi hHGi1)
  have hK : X.K ≤ Subgroup.normalizer (X.ZQ d : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 1 ⊓ X.Q b) = X.Z 1 ⊓ X.Q b
    rw [conjSub_inf, X.Z_normal 1 k (X.K_le_Gi 1 hk)]
    have hQb : conjSub k (X.Q b) = X.Q b :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi b) (X.K_le_Gi b hk))
    rw [hQb]
  have hHnot : ¬ X.ZQ d ≤ X.Q (b + 1) := by simpa [hb1] using hH
  have hS : X.ZQ d ⊔ X.Q (b + 1) = X.edgeSylow b :=
    X.sup_Q_eq_edgeSylow_of_gen (i := b) (A := X.ZQ d) (inf_le_left.trans hK) hHedge hHnot
  simpa [hb, hb1, e2] using hS

private theorem commutator_ZQ_Z_odd (C : X.Comm48 s r d) : Odd ((d : ℤ) + 2) := by
  obtain ⟨m, hm⟩ := C.even
  refine ⟨(m : ℤ), ?_⟩
  have hm' : (d : ℤ) + 1 = 2 * (m : ℤ) := by
    have hcast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
    rw [← hcast, hm]
    push_cast
    ring
  omega

private theorem commutator_ZQ_Z_le (C : X.Comm48 s r d) :
    ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.Z ((d : ℤ) + 2) := by
  set b : ℤ := (d : ℤ) + 1 with hb
  have hb1 : b + 1 = (d : ℤ) + 2 := by rw [hb]; ring
  have e2 : (d : ℤ) + 1 + 1 = (d : ℤ) + 2 := by ring
  have hHQb : X.ZQ d ≤ X.Q b := by unfold Setup.ZQ; exact inf_le_right
  have hHGi1 : X.ZQ d ≤ X.Gi (b + 1) :=
    hHQb.trans ((X.Q_le_Gi_adj b).trans inf_le_right)
  have hHnormZ : X.ZQ d ≤ Subgroup.normalizer (X.Z (b + 1) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub h (X.Z (b + 1)) = X.Z (b + 1)
    exact X.Z_normal (b + 1) h (hHGi1 hh)
  have hRle : ⁅X.ZQ d, X.Z (b + 1)⁆ ≤ X.Z (b + 1) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hHnormZ
  simpa [hb1, hb, e2] using hRle

private theorem commutator_ZQ_Z_ne (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≠ ⊥ := by
  set b : ℤ := (d : ℤ) + 1 with hb
  have hb1 : b + 1 = (d : ℤ) + 2 := by rw [hb]; ring
  have e2 : (d : ℤ) + 1 + 1 = (d : ℤ) + 2 := by ring
  have hS : X.ZQ d ⊔ X.Q (b + 1) = X.edgeSylow b := by
    simpa [hb1, hb, e2] using commutator_ZQ_Z_sup C hH
  have hodd : Odd (b + 1) := by
    simpa [hb1, e2] using commutator_ZQ_Z_odd C
  by_contra hbot
  have hbot' : ⁅X.ZQ d, X.Z (b + 1)⁆ = ⊥ := by
    rw [show b + 1 = (d : ℤ) + 2 by rw [hb]; ring]
    exact hbot
  have hcent : X.edgeSylow b ≤ Subgroup.centralizer (X.Z (b + 1) : Set G) := by
    rw [← hS]
    refine sup_le ?_ ?_
    · intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hmem : ⁅h, z⁆ ∈ ⁅X.ZQ d, X.Z (b + 1)⁆ :=
        Subgroup.commutator_mem_commutator hh hz
      have hone : ⁅h, z⁆ = 1 := by simpa [hbot'] using hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp (X.Z_le_center (b + 1) hz).2) q hq).symm
  obtain ⟨t, ht, href, -⟩ := X.exists_reflection_oTwoRes C.hyp (b + 1)
  have htGi : t ∈ X.Gi (b + 1) :=
    X.L_le_Gi (b + 1) (oTwoRes_le (X.L (b + 1)) (Subgroup.mem_inf.mp ht).1)
  have hZt : conjSub t (X.Z (b + 1)) = X.Z (b + 1) := X.Z_normal (b + 1) t htGi
  have hedge : conjSub t (X.edgeSylow ((b + 1) - 1)) = X.edgeSylow (b + 1) :=
    conjSub_reflection_edgeSylow (X := X) (i := b + 1) href
  rw [show (b + 1) - 1 = b by ring] at hedge
  have hcentEdge : X.edgeSylow (b + 1) ≤
      Subgroup.centralizer (X.Z (b + 1) : Set G) := by
    rw [← hedge, ← hZt, conjSub_centralizer]
    exact conjSub_mono t hcent
  have hcent' : X.edgeSylow ((b + 1) - 1) ≤
      Subgroup.centralizer (X.Z (b + 1) : Set G) := by
    simpa [show (b + 1) - 1 = b by ring] using hcent
  have hZcenter := X.le_centerOf_L C.hyp.char (b + 1) (X.Z_le_Gi (b + 1)) hcent' hcentEdge
  have hZbot := (X.s48_1 C).2 (b + 1) hodd
  rw [hZbot] at hZcenter
  exact X.Z_ne_bot_of (b + 1) (X.Q_ne_bot C.hyp.char (b + 1))
    (le_bot_iff.mp hZcenter)

end Comm48

variable (X) in
theorem fixes_ball_of_hasB (H : X.Sec4Hyp s r) {i : ℤ} {e : ℕ}
    (hd : X.HasB i e) {w : V} {k : ℕ} (hk : k ≤ min e s)
    (hw : Γ.dist (X.vert i) w = k) :
    ∀ z ∈ X.Z i, z • w = w := by
  have hke : k ≤ e := hk.trans (min_le_left e s)
  have hks : k ≤ s := hk.trans (min_le_right e s)
  have hdist : Γ.dist (X.vert i) (X.vert (i + (k : ℤ))) = k := by
    rw [Line.dist_eq X.hyp.isTree X.line (by omega)]
    rw [show i + (k : ℤ) - i = (k : ℤ) by ring]
    simp
  have hfix : X.Z i ≤ MulAction.stabilizer G (X.vert (i + (k : ℤ))) :=
    hd.1 (k : ℤ) (by simpa using hke)
  have hle := X.Z_fixes_of_dist (i := i) H.sing hks hdist hfix (w := w) (by rw [hw])
  intro z hz
  exact MulAction.mem_stabilizer_iff.mp (hle hz)

namespace Comm48

private theorem s48_3d_HasB_succ (C : X.Comm48 s r d) : X.HasB ((d : ℤ) + 2) d := by
  have hev : Even (((d : ℤ) + 2) - 1) := by
    obtain ⟨m, hm⟩ := C.even
    refine ⟨(m : ℤ), ?_⟩
    push_cast at hm ⊢
    omega
  exact (X.hasB_iff_of_even (i := (d : ℤ) + 2) (j := 1) hev d).mpr C.hasB

private theorem s48_3d_Z1_fixes_small (C : X.Comm48 s r d) (hd2 : 2 ≤ d) {h : G}
    (hh : h ∈ X.ZQ d) {j : ℤ} (hsmall : j = -1 ∨ j = 0 ∨ j = 1) :
    h • X.vert j = X.vert j := by
  have hd : X.HasB 1 d := C.hasB
  have hHZ1 : X.ZQ d ≤ X.Z 1 := by unfold Setup.ZQ; exact inf_le_left
  have hZ1fixv : ∀ v : ℤ, v = -1 ∨ v = 0 ∨ v = 1 → X.Z 1 ≤ X.Gi v := by
    rintro v (rfl | rfl | rfl)
    · have h := hd.1 (-2) (by omega)
      simpa using h
    · have h := hd.1 (-1) (by omega)
      simpa using h
    · have h := hd.1 0 (by omega)
      simpa using h
  exact MulAction.mem_stabilizer_iff.mp (hZ1fixv j hsmall (hHZ1 hh))

private theorem s48_3d_fixes_small_dist (C : X.Comm48 s r d)
    {z : G} (hz : z ∈ X.Z ((d : ℤ) + 2)) {j : ℤ}
    (hsmall : j = -1 ∨ j = 0 ∨ j = 1) :
    Γ.dist (X.vert 1) (z⁻¹ • X.vert j) ≤ 4 := by
  have hdZ' : X.HasB ((d : ℤ) + 2) d := s48_3d_HasB_succ C
  have hline_dist : ∀ a c : ℤ, a ≤ c → Γ.dist (X.vert a) (X.vert c) = (c - a).toNat :=
    fun a c h => Line.dist_eq X.hyp.isTree X.line h
  have hz2 : z⁻¹ • X.vert 2 = X.vert 2 := by
    have hmem : (2 : ℤ) ∈ X.fixSet (X.Z ((d : ℤ) + 2)) := by
      rw [X.fixSet_Z ((d : ℤ) + 2) hdZ', Set.mem_Icc]
      constructor <;> omega
    exact hmem z⁻¹ ((X.Z ((d : ℤ) + 2)).inv_mem hz)
  have hvdist : Γ.dist (X.vert 2) (X.vert j) ≤ 3 := by
    rcases hsmall with rfl | rfl | rfl
    · rw [dist_comm, hline_dist (-1) 2 (by norm_num)]
      norm_num
    · rw [dist_comm, hline_dist 0 2 (by norm_num)]
      norm_num
    · rw [dist_comm, hline_dist 1 2 (by norm_num)]
      norm_num
  have h2v : Γ.dist (X.vert 2) (z⁻¹ • X.vert j) = Γ.dist (X.vert 2) (X.vert j) := by
    calc Γ.dist (X.vert 2) (z⁻¹ • X.vert j)
        = Γ.dist (z⁻¹ • X.vert 2) (z⁻¹ • X.vert j) := by rw [hz2]
      _ = Γ.dist (X.vert 2) (X.vert j) :=
          IsTree.dist_smul X.hyp.isTree X.hyp.adj_smul z⁻¹ (X.vert 2) (X.vert j)
  have htri := X.hyp.isTree.dist_triangle (u := X.vert 1) (v := X.vert 2)
    (w := z⁻¹ • X.vert j)
  have h12 : Γ.dist (X.vert 1) (X.vert 2) = 1 := by
    rw [hline_dist 1 2 (by norm_num)]
    norm_num
  omega

private theorem s48_3d_commutator_fixes_small (C : X.Comm48 s r d) (h4 : 4 ≤ d)
    {h z : G} (hh : h ∈ X.ZQ d) (hz : z ∈ X.Z ((d : ℤ) + 2)) {j : ℤ}
    (hsmall : j = -1 ∨ j = 0 ∨ j = 1) :
    ⁅h, z⁆ • X.vert j = X.vert j := by
  have hd : X.HasB 1 d := C.hasB
  have hHZ1 : X.ZQ d ≤ X.Z 1 := by unfold Setup.ZQ; exact inf_le_left
  have hvfix : h • X.vert j = X.vert j := s48_3d_Z1_fixes_small C (by omega) hh hsmall
  have hdist : Γ.dist (X.vert 1) (z⁻¹ • X.vert j) ≤ 4 :=
    s48_3d_fixes_small_dist C hz hsmall
  have hk : Γ.dist (X.vert 1) (z⁻¹ • X.vert j) ≤ min d s := by
    refine le_min ?_ ?_
    · omega
    · have hs5 : 5 ≤ s := C.hyp.five_le
      omega
  have hhfixu : h • (z⁻¹ • X.vert j) = z⁻¹ • X.vert j :=
    X.fixes_ball_of_hasB C.hyp (i := 1) (e := d) hd
      (w := z⁻¹ • X.vert j) (k := Γ.dist (X.vert 1) (z⁻¹ • X.vert j)) hk rfl h
      (hHZ1 hh)
  have hu : h⁻¹ • (z⁻¹ • X.vert j) = z⁻¹ • X.vert j := by
    simpa [hhfixu] using inv_smul_smul h (z⁻¹ • X.vert j)
  calc ⁅h, z⁆ • X.vert j = (h * z * h⁻¹ * z⁻¹) • X.vert j := by
        rw [commutatorElement_def]
    _ = h • (z • (h⁻¹ • (z⁻¹ • X.vert j))) := by simp only [mul_smul]
    _ = h • (z • (z⁻¹ • X.vert j)) := by rw [hu]
    _ = h • X.vert j := by rw [smul_inv_smul]
    _ = X.vert j := hvfix

private theorem s48_3d_commutator_fixes_large (C : X.Comm48 s r d)
    {h z : G} (hh : h ∈ X.ZQ d) (hz : z ∈ X.Z ((d : ℤ) + 2)) {j : ℤ}
    (hj2 : 2 ≤ j) (hjr : j ≤ (r : ℤ))
    (hRle : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.Z ((d : ℤ) + 2)) :
    ⁅h, z⁆ • X.vert j = X.vert j := by
  have hdZ' : X.HasB ((d : ℤ) + 2) d := s48_3d_HasB_succ C
  have hreq : 2 * (d + 1) = r := (X.s48_2 C).2.1
  have hr : (r : ℤ) = 2 * (d : ℤ) + 2 := by
    rw [← hreq]
    push_cast
    ring
  have hmem : j ∈ X.fixSet (X.Z ((d : ℤ) + 2)) := by
    rw [X.fixSet_Z ((d : ℤ) + 2) hdZ', Set.mem_Icc]
    constructor <;> omega
  exact hmem ⁅h, z⁆ (hRle (Subgroup.commutator_mem_commutator hh hz))

private theorem s48_3d_R_fixes_arc (C : X.Comm48 s r d) (h4 : 4 ≤ d)
    (hRle : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.Z ((d : ℤ) + 2)) :
    ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.arcStab (-1) (r : ℤ) := by
  rw [Subgroup.commutator_le]
  intro h hh z hz
  rw [Setup.arcStab, Fan86.mem_fixSet]
  rintro v ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  by_cases hsmall : j = -1 ∨ j = 0 ∨ j = 1
  · exact s48_3d_commutator_fixes_small C h4 hh hz hsmall
  · have hj2 : 2 ≤ j := by omega
    exact s48_3d_commutator_fixes_large C hh hz hj2 hj.2 hRle

end Comm48

variable (X) in
open Comm48 in
theorem s48_3d (C : X.Comm48 s r d) (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    d = 1 ∨ d = 3 := by
  have hd : X.HasB 1 d := C.hasB
  have hd1 : 1 ≤ d := X.one_le_of_hasB hd
  by_contra hcon
  have hne1 : d ≠ 1 := fun h => hcon (Or.inl h)
  have hne3 : d ≠ 3 := fun h => hcon (Or.inr h)
  have hd5 : 5 ≤ d := by
    obtain ⟨m, hm⟩ := C.even
    omega
  have hRle : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.Z ((d : ℤ) + 2) :=
    commutator_ZQ_Z_le C
  have hRne : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≠ ⊥ := commutator_ZQ_Z_ne C hH
  have hR2 : IsPGroup 2 (↥(⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ : Subgroup G)) :=
    (pCoreOf_isPGroup' (X.Gi ((d : ℤ) + 2))).to_le
      (hRle.trans (X.Z_le_Q ((d : ℤ) + 2)))
  have hRfix : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤ X.arcStab (-1) (r : ℤ) :=
    s48_3d_R_fixes_arc C (by omega) hRle
  have hfix : ⁅X.ZQ d, X.Z ((d : ℤ) + 2)⁆ ≤
      X.arcStab (-1) ((-1) + ((r + 1 : ℕ) : ℤ)) := by
    simpa using hRfix
  have hle := X.le_r_of_fixes C.hyp hR2 hRne hfix
  omega

namespace Comm48

private theorem s48_3e_hS (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h3 : d = 3) :
    X.ZQ d ⊔ X.Q 5 = X.edgeSylow 4 := by
  have hHQb : X.ZQ d ≤ X.Q ((d : ℤ) + 1) := by unfold Setup.ZQ; exact inf_le_right
  have hHQ4 : X.ZQ d ≤ X.Q 4 := by simpa [show (d : ℤ) + 1 = 4 by omega] using hHQb
  have hH2 : IsPGroup 2 (X.ZQ d) :=
    (pCoreOf_isPGroup' (X.Gi ((d : ℤ) + 1))).to_le hHQb
  have hHGi4 : X.ZQ d ≤ X.Gi 4 := hHQ4.trans (X.Q_le_Gi 4)
  have hHGi5 : X.ZQ d ≤ X.Gi 5 := hHQ4.trans (((X.Q_le_Gi_adj 4).trans inf_le_right))
  have hHedge : X.ZQ d ≤ X.edgeSylow 4 :=
    X.le_edgeSylow_of_le_inf 4 hH2 (le_inf hHGi4 hHGi5)
  have hK : X.K ≤ Subgroup.normalizer (X.ZQ d : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    unfold Setup.ZQ
    rw [show (d : ℤ) + 1 = 4 by omega]
    change Subgroup.map (MulAut.conj k).toMonoidHom (X.Z 1 ⊓ X.Q 4) = X.Z 1 ⊓ X.Q 4
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective,
      show (X.Z 1).map (MulAut.conj k).toMonoidHom = X.Z 1 by
        simpa [conjSub] using X.Z_normal 1 k (X.K_le_Gi 1 hk),
      show (X.Q 4).map (MulAut.conj k).toMonoidHom = X.Q 4 by
        simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4) (X.K_le_Gi 4 hk))]
  have hnot : ¬ X.ZQ d ≤ X.Q 5 := by
    have h := hH
    rw [show (d : ℤ) + 2 = 5 by omega] at h
    exact h
  have hS := X.sup_Q_eq_edgeSylow_of_gen (i := 4) (A := X.ZQ d)
    (inf_le_left.trans hK) hHedge hnot
  simpa using hS

private theorem s48_3e_exists_conj (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h3 : d = 3)
    {P : Subgroup G} (hP : IsSylowTwoOf P (X.Gi 5)) (hPne : P ≠ X.edgeSylow 4) :
    ∃ h ∈ X.ZQ d, P = conjSub h (X.edgeSylow 5) := by
  have hS : X.ZQ d ⊔ X.Q 5 = X.edgeSylow 4 := s48_3e_hS C hH h3
  have hHQb : X.ZQ d ≤ X.Q ((d : ℤ) + 1) := by unfold Setup.ZQ; exact inf_le_right
  have hHQ4 : X.ZQ d ≤ X.Q 4 := by simpa [show (d : ℤ) + 1 = 4 by omega] using hHQb
  have hHGi5 : X.ZQ d ≤ X.Gi 5 := hHQ4.trans (((X.Q_le_Gi_adj 4).trans inf_le_right))
  have hQ5N : X.ZQ d ≤ Subgroup.normalizer (X.Q 5 : Set G) :=
    hHGi5.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 5))
  have hS45_5 : IsSylowTwoOf (X.edgeSylow 4) (X.Gi 5) :=
    X.isSylowTwoOf_edgeSylow_Gi_succ 4
  haveI : Finite ↥(X.Gi 5) := X.hyp.finite_stab (X.vert 5)
  obtain ⟨g, hg5, hPconj⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf hS45_5 hP
  set x : V := g • X.vert 4 with hxdef
  have hxadj : Γ.Adj (X.vert 5) x := by
    have h := X.hyp.adj_smul g (X.vert 5) (X.vert 4)
    rw [MulAction.mem_stabilizer_iff.mp hg5] at h
    exact h.mpr (X.adj 4).symm
  by_cases hx4 : x = X.vert 4
  · exfalso
    apply hPne
    rw [hPconj]
    have hg4 : g ∈ X.Gi 4 := MulAction.mem_stabilizer_iff.mpr hx4
    have hgn : g ∈ X.Gi 4 ⊓ X.Gi 5 := ⟨hg4, hg5⟩
    have hnorm : g ∈ Subgroup.normalizer (X.edgeSylow 4 : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4 ⊓ X.Gi 5)) hgn
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  · have h6ne : X.vert 6 ≠ X.vert 4 := fun h => absurd (X.vert_injective h) (by norm_num)
    obtain ⟨s, hsS45, hs6⟩ :=
      X.edgeSylow_transitive_right 5 (X.vert 6) x (X.adj 5) h6ne hxadj hx4
    have hs : s ∈ X.ZQ d ⊔ X.Q 5 := by
      rw [hS]
      exact hsS45
    obtain ⟨h, hh, q, hq, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ5N).mp hs
    have hq6 : q • X.vert 6 = X.vert 6 :=
      X.Q_fixes_neighbors_vert 5 (X.vert 6) (X.adj 5) q hq
    have hh6 : h • X.vert 6 = x := by
      simpa [mul_smul, hq6] using hs6
    have hh5 : h ∈ X.Gi 5 := hHGi5 hh
    have hPpc : P = pCoreOf 2 (MulAction.stabilizer G x ⊓ X.Gi 5) := by
      rw [hPconj]
      change conjSub g (pCoreOf 2 (X.Gi 4 ⊓ X.Gi 5)) =
        pCoreOf 2 (MulAction.stabilizer G x ⊓ X.Gi 5)
      rw [← pCoreOf_conjSub]
      congr 1
      have hgx : conjSub g (X.Gi 4) = MulAction.stabilizer G x := by
        simpa [hxdef, Setup.Gi] using (stabilizer_smul_eq_conjSub g (X.vert 4)).symm
      rw [conjSub_inf, hgx, conjSub_eq_of_mem hg5]
    have hSpc : conjSub h (X.edgeSylow 5) = pCoreOf 2 (MulAction.stabilizer G x ⊓ X.Gi 5) := by
      change conjSub h (pCoreOf 2 (X.Gi 5 ⊓ X.Gi 6)) =
        pCoreOf 2 (MulAction.stabilizer G x ⊓ X.Gi 5)
      rw [← pCoreOf_conjSub]
      congr 1
      have hhx : conjSub h (X.Gi 6) = MulAction.stabilizer G x := by
        simpa [hh6, Setup.Gi] using (stabilizer_smul_eq_conjSub h (X.vert 6)).symm
      rw [conjSub_inf, conjSub_eq_of_mem hh5, hhx, inf_comm]
    exact ⟨h, hh, hPpc.trans hSpc.symm⟩

private theorem s48_3e_center_le_sup (C : X.Comm48 s r d)
    (hR : ⁅X.ZQ d, X.Z 5⁆ ≤ X.Z 4)
    {P : Subgroup G} {h : G} (hh : h ∈ X.ZQ d)
    (hPeq : P = conjSub h (X.edgeSylow 5)) :
    centerOf P ≤ X.Z 4 ⊔ X.Z 6 := by
  have hS56_5 : IsSylowTwoOf (X.edgeSylow 5) (X.Gi 5) :=
    X.isSylowTwoOf_edgeSylow_Gi 5
  have hS56_6 : IsSylowTwoOf (X.edgeSylow 5) (X.Gi 6) :=
    X.isSylowTwoOf_edgeSylow_Gi_succ 5
  intro z hz
  rw [hPeq, centerOf_conjSub] at hz
  rw [CFSG.Quasithin.mem_conjSub] at hz
  have hz5 : h⁻¹ * z * h ∈ X.Z 5 := (X.centerOf_sylow_le_Z C.hyp.char 5 hS56_5).1 hz
  have hz6 : h⁻¹ * z * h ∈ X.Z 6 := (X.centerOf_sylow_le_Z C.hyp.char 6 hS56_6).1 hz
  have hcomm : ⁅h, h⁻¹ * z * h⁆ ∈ X.Z 4 :=
    hR (Subgroup.commutator_mem_commutator hh hz5)
  have heq : z = ⁅h, h⁻¹ * z * h⁆ * (h⁻¹ * z * h) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact (X.Z 4 ⊔ X.Z 6).mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hz6)

private theorem s48_3e_Z5_sup (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h3 : d = 3)
    (hR : ⁅X.ZQ d, X.Z 5⁆ ≤ X.Z 4) :
    X.Z 5 ≤ X.Z 4 ⊔ X.Z 6 := by
  classical
  have hS45_4 : IsSylowTwoOf (X.edgeSylow 4) (X.Gi 4) :=
    X.isSylowTwoOf_edgeSylow_Gi 4
  rw [Setup.Z]
  refine iSup₂_le ?_
  intro P hP
  refine (inf_le_left : centerOf P ⊓ X.Q 5 ≤ centerOf P).trans ?_
  by_cases hP45 : P = X.edgeSylow 4
  · rw [hP45]
    exact ((X.centerOf_sylow_le_Z C.hyp.char 4 hS45_4).1).trans le_sup_left
  · obtain ⟨h, hh, hPeq⟩ := s48_3e_exists_conj C hH h3 hP hP45
    exact s48_3e_center_le_sup C hR hh hPeq

private theorem commutator_ZQ_Z_five_le_arcStab (C : X.Comm48 s r d) (hB1 : X.HasB 1 3)
    (hB5 : X.HasB 5 3) : ⁅X.ZQ d, X.Z 5⁆ ≤ X.arcStab 0 1 := by
  have hHZ1 : X.ZQ d ≤ X.Z 1 := by unfold Setup.ZQ; exact inf_le_left
  have hline_dist : ∀ a c : ℤ, a ≤ c → Γ.dist (X.vert a) (X.vert c) = (c - a).toNat :=
    fun a c h => Line.dist_eq X.hyp.isTree X.line h
  rw [Subgroup.commutator_le]
  intro h hh z hz
  rw [Setup.arcStab, Fan86.mem_fixSet]
  rintro v ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  have hvfix : h • X.vert j = X.vert j := by
    have h1j := hB1.1 (j - 1) (by omega) (hHZ1 hh)
    rw [show (1 : ℤ) + (j - 1) = j by ring] at h1j
    exact MulAction.mem_stabilizer_iff.mp (by simpa [Setup.Gi] using h1j)
  have hz2 : z⁻¹ • X.vert 2 = X.vert 2 := by
    have hmem : (2 : ℤ) ∈ X.fixSet (X.Z 5) := by
      rw [X.fixSet_Z 5 hB5, Set.mem_Icc]
      constructor <;> norm_num
    exact hmem z⁻¹ ((X.Z 5).inv_mem hz)
  have h2j : Γ.dist (X.vert 2) (z⁻¹ • X.vert j) ≤ 2 := by
    calc Γ.dist (X.vert 2) (z⁻¹ • X.vert j)
        = Γ.dist (z⁻¹ • X.vert 2) (z⁻¹ • X.vert j) := by rw [hz2]
      _ = Γ.dist (X.vert 2) (X.vert j) :=
          IsTree.dist_smul X.hyp.isTree X.hyp.adj_smul z⁻¹ (X.vert 2) (X.vert j)
      _ ≤ 2 := by
          rw [dist_comm, hline_dist j 2 (by omega)]
          omega
  have hk : Γ.dist (X.vert 1) (z⁻¹ • X.vert j) ≤ min 3 s := by
    have htri := X.hyp.isTree.dist_triangle (u := X.vert 1) (v := X.vert 2)
      (w := z⁻¹ • X.vert j)
    have h12 : Γ.dist (X.vert 1) (X.vert 2) = 1 := by
      rw [hline_dist 1 2 (by norm_num)]
      norm_num
    exact le_min (by omega) (by have := C.hyp.five_le; omega)
  have hhfix : h • (z⁻¹ • X.vert j) = z⁻¹ • X.vert j :=
    X.fixes_ball_of_hasB C.hyp (i := 1) (e := 3) hB1
      (w := z⁻¹ • X.vert j) (k := Γ.dist (X.vert 1) (z⁻¹ • X.vert j)) hk rfl h
      (hHZ1 hh)
  have hu : h⁻¹ • (z⁻¹ • X.vert j) = z⁻¹ • X.vert j := by
    simpa [hhfix] using inv_smul_smul h (z⁻¹ • X.vert j)
  calc ⁅h, z⁆ • X.vert j = (h * z * h⁻¹ * z⁻¹) • X.vert j := by
        rw [commutatorElement_def]
    _ = h • (z • (h⁻¹ • (z⁻¹ • X.vert j))) := by simp only [mul_smul]
    _ = h • (z • (z⁻¹ • X.vert j)) := by rw [hu]
    _ = h • X.vert j := by rw [smul_inv_smul]
    _ = X.vert j := hvfix

private theorem s48_3e_R_le_Z4 (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h3 : d = 3) :
    ⁅X.ZQ d, X.Z 5⁆ ≤ X.Z ((d : ℤ) + 1) := by
  classical
  have h2r : 2 * (d + 1) = r := (X.s48_2 C).2.1
  have hZb : X.Z ((d : ℤ) + 1) = X.Qg r := (X.s48_2 C).2.2.1
  have hd1 : 1 ≤ d := X.one_le_of_hasB C.hasB
  have hr : r = 8 := by omega
  have hb4 : (d : ℤ) + 1 = 4 := by omega
  have hB1 : X.HasB 1 3 := by simpa [h3] using C.hasB
  have hB5 : X.HasB 5 3 :=
    (X.hasB_iff_of_even (i := 5) (j := 1) (by norm_num) 3).mpr hB1
  have hHQb : X.ZQ d ≤ X.Q ((d : ℤ) + 1) := by unfold Setup.ZQ; exact inf_le_right
  have hHQ4 : X.ZQ d ≤ X.Q 4 := by simpa [hb4] using hHQb
  have hHGi5 : X.ZQ d ≤ X.Gi 5 :=
    hHQ4.trans (((X.Q_le_Gi_adj 4).trans inf_le_right))
  have hHNZ5 : X.ZQ d ≤ Subgroup.normalizer (X.Z 5 : Set G) :=
    fun h hh => mem_normalizer_iff_conjSub.mpr (X.Z_normal 5 h (hHGi5 hh))
  have hRleZ5 : ⁅X.ZQ d, X.Z 5⁆ ≤ X.Z 5 :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hHNZ5
  have hR2 : IsPGroup 2 (↥(⁅X.ZQ d, X.Z 5⁆ : Subgroup G)) :=
    ((pCoreOf_isPGroup' (X.Gi 5)).to_le (X.Z_le_Q 5)).to_le hRleZ5
  have hfix01 : ⁅X.ZQ d, X.Z 5⁆ ≤ X.arcStab 0 1 :=
    commutator_ZQ_Z_five_le_arcStab C hB1 hB5
  have hfix : ⁅X.ZQ d, X.Z 5⁆ ≤ X.arcStab 0 8 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro q hq
    by_cases hj1 : j ≤ 1
    · have hj01 : j ∈ Set.Icc (0 : ℤ) 1 := by rw [Set.mem_Icc]; omega
      have hqarc : q ∈ X.arcStab 0 1 := hfix01 hq
      rw [Setup.arcStab, Fan86.mem_fixSet] at hqarc
      exact hqarc (X.vert j) ⟨j, hj01, rfl⟩
    · have hmem : j ∈ X.fixSet (X.Z 5) := by
        rw [X.fixSet_Z 5 hB5, Set.mem_Icc]
        constructor <;> omega
      exact hmem q (hRleZ5 hq)
  have hfix' : ⁅X.ZQ d, X.Z 5⁆ ≤ X.arcStab 0 (0 + (r : ℤ)) := by
    simpa [hr] using hfix
  have hle := X.le_pCoreOf_arcStab_r C.hyp hR2 hfix'
  have hZ4Qg : X.Z ((d : ℤ) + 1) = pCoreOf 2 (X.arcStab 0 (r : ℤ)) := by
    simpa using hZb
  have hle' : ⁅X.ZQ d, X.Z 5⁆ ≤ pCoreOf 2 (X.arcStab 0 (r : ℤ)) := by
    simpa using hle
  rw [hZ4Qg]
  exact hle'

private theorem s48_3e_Z1_sup (hZ5 : X.Z 5 ≤ X.Z 4 ⊔ X.Z 6) :
    X.Z 1 ≤ X.Z 0 ⊔ X.Z 2 := by
  have h := conjSub_mono (X.τ ^ (-2 : ℤ)) hZ5
  rw [← X.Z_add (-2 : ℤ) 5, conjSub_sup,
    ← X.Z_add (-2 : ℤ) 4, ← X.Z_add (-2 : ℤ) 6] at h
  simpa using h

private theorem s48_3e_H_le_Q5 (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (h3 : d = 3)
    (hZ1 : X.Z 1 ≤ X.Z 0 ⊔ X.Z 2) : X.ZQ d ≤ X.Q 5 := by
  have hB0 : X.HasB 0 4 := by
    have h := (X.s48_2 C).1
    simpa [show d + 1 = 4 by omega] using h
  have hB2 : X.HasB 2 4 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 4).mpr hB0
  have hZ0Q4 : X.Z 0 ⊓ X.Q 4 = ⊥ := by
    have h := (X.s48_2 C).2.2.2.2.2.2.1
    simpa [show (d : ℤ) + 1 = 4 by omega] using h
  have hZ0Q2 : X.Z 0 ≤ X.Q 2 := X.Z_le_Q_of_lt hB0 (j := 2) (by norm_num)
  have hZ2Q4 : X.Z 2 ≤ X.Q 4 := X.Z_le_Q_of_lt hB2 (j := 4) (by norm_num)
  have hZ2Q5 : X.Z 2 ≤ X.Q 5 := X.Z_le_Q_of_lt hB2 (j := 5) (by norm_num)
  have hZ2center : X.Z 2 ≤ centerOf (X.Q 2) := X.Z_le_center 2
  have hZ0NZ2 : X.Z 0 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (X.Z 2 : Set G) := by
      intro c hc
      exact ((Subgroup.mem_inf.mp (hZ2center hc)).2 z (hZ0Q2 hz)).symm
    exact Subgroup.centralizer_le_normalizer (X.Z 2 : Set G) hzC
  rw [Setup.ZQ]
  intro x hx
  obtain ⟨hxZ1, hxQ4'⟩ := Subgroup.mem_inf.mp hx
  have hxQ4 : x ∈ X.Q 4 := by
    simpa [show (d : ℤ) + 1 = 4 by omega] using hxQ4'
  have hxZ0Z2 : x ∈ X.Z 0 ⊔ X.Z 2 := hZ1 hxZ1
  obtain ⟨a, ha, c, hc, hac⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZ0NZ2).mp hxZ0Z2
  have haQ4 : a ∈ X.Q 4 := by
    have hxinv : x * c⁻¹ ∈ X.Q 4 :=
      (X.Q 4).mul_mem hxQ4 ((X.Q 4).inv_mem (hZ2Q4 hc))
    have haeq : a = x * c⁻¹ := by rw [hac]; group
    rw [haeq]
    exact hxinv
  have haBot : a ∈ (⊥ : Subgroup G) := by
    rw [← hZ0Q4]
    exact Subgroup.mem_inf.mpr ⟨ha, haQ4⟩
  have ha1 : a = 1 := Subgroup.mem_bot.mp haBot
  have hxZ2 : x ∈ X.Z 2 := by
    have hxc : x = c := by rw [hac, ha1, one_mul]
    exact hxc ▸ hc
  exact hZ2Q5 hxZ2

end Comm48

variable (X) in
open Comm48 in
theorem s48_3e (C : X.Comm48 s r d)
    (hH : ¬ X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : d ≠ 3 := by
  intro h3
  have hR' := s48_3e_R_le_Z4 C hH h3
  have hR : ⁅X.ZQ d, X.Z 5⁆ ≤ X.Z 4 := by
    simpa [show (d : ℤ) + 1 = 4 by omega] using hR'
  have hZ5 : X.Z 5 ≤ X.Z 4 ⊔ X.Z 6 := s48_3e_Z5_sup C hH h3 hR
  have hZ1 : X.Z 1 ≤ X.Z 0 ⊔ X.Z 2 := s48_3e_Z1_sup hZ5
  have hHle : X.ZQ d ≤ X.Q 5 := s48_3e_H_le_Q5 C hH h3 hZ1
  apply hH
  rw [show (d : ℤ) + 2 = 5 by omega]
  exact hHle

end Setup

end CFSG.Quasithin.St84

end
