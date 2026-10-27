module

public import CFSG.Quasithin.Vol2.Ch6Sec1Prop15
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem17Nat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_pow_mem {P N S₀ : Subgroup G} (hS : IsSylowTwoOf S₀ P)
    (hN : ∀ p ∈ P, ∃ k : ℕ, p ^ 2 ^ k ∈ N) : P ≤ N ⊔ S₀ :=
  (eq_oTwoUpper_sup_of_isSylowTwoOf' hS).le.trans
    (sup_le_sup_right (oTwoUpper_le_of_pow_mem hN) S₀)

omit [Finite G] in
theorem isPGroup_of_forall_pow {X : Subgroup G} (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsPGroup 2 X := by
  intro x
  obtain ⟨k, hk⟩ := h x x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

omit [Finite G] in
theorem comm_mem_swap {W : Subgroup G} {x u : G} (h : x * u * x⁻¹ * u⁻¹ ∈ W) :
    u * x * u⁻¹ * x⁻¹ ∈ W := by
  have := W.inv_mem h
  have e : (x * u * x⁻¹ * u⁻¹)⁻¹ = u * x * u⁻¹ * x⁻¹ := by group
  rwa [e] at this

omit [Finite G] in
theorem mem_centralizer_of_odd {V Z : Subgroup G} (hV : IsElemAbelian 2 V) (hZV : Z ≤ V) {c : G}
    (hc : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ Z) (hcZ : c ∈ Subgroup.centralizer (Z : Set G))
    (ho : Odd (orderOf c)) : c ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  set z := c * v * c⁻¹ * v⁻¹ with hz
  have hzZ : z ∈ Z := hc v hv
  have hz2 : z * z = 1 := by
    have := hV.2 z (hZV hzZ)
    rwa [pow_two] at this
  have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hcZ z hzZ).symm
  have hcv : c * v * c⁻¹ = z * v := by rw [hz]; group
  have hc2 : c ^ 2 ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have e : c ^ 2 * v * (c ^ 2)⁻¹ = v := by
      calc c ^ 2 * v * (c ^ 2)⁻¹ = c * (c * v * c⁻¹) * c⁻¹ := by rw [pow_two]; group
        _ = c * (z * v) * c⁻¹ := by rw [hcv]
        _ = (c * z * c⁻¹) * (c * v * c⁻¹) := by group
        _ = z * (z * v) := by rw [hcv, hcz]; group
        _ = v := by rw [← mul_assoc, hz2, one_mul]
    calc v * c ^ 2 = (c ^ 2 * v * (c ^ 2)⁻¹) * c ^ 2 := by rw [e]
      _ = c ^ 2 * v := by group
  have hcop : Nat.Coprime 2 (orderOf c) := Nat.coprime_two_left.mpr ho
  have hmem : c ∈ Subgroup.centralizer ({v} : Set G) :=
    (Subgroup.zpowers_le.mpr hc2) (A4.mem_zpowers_pow_of_coprime hcop)
  exact Subgroup.mem_centralizer_iff.mp hmem v rfl

omit [Finite G] in
theorem pCoreOf_ne_bot_of_charTwo {X : Subgroup G} (hX : CharTwo X) (h1 : X ≠ ⊥) :
    pCoreOf 2 X ≠ ⊥ := by
  intro h0
  apply h1
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    refine ⟨hx, ?_⟩
    rw [h0]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
  have := hX this
  rwa [h0] at this

omit [Finite G] in
theorem exists_pow_mem_of_le_normalizer {X P : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) {y : G} (hy : y ∈ X ⊔ P) :
    ∃ k : ℕ, y ^ 2 ^ k ∈ X := by
  have hy' : y ∈ (X : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left X P hPX]
    exact hy
  obtain ⟨x, hx, p, hp, rfl⟩ := hy'
  have key : ∀ m : ℕ, ∃ x' ∈ X, (x * p) ^ m = x' * p ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, X.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨x', hx', he⟩ := ih
      have hpm : p ^ m * x * (p ^ m)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hPX (P.pow_mem hp m)) x).mp hx
      refine ⟨x' * (p ^ m * x * (p ^ m)⁻¹), X.mul_mem hx' hpm, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', he⟩ := key (2 ^ k)
  exact ⟨k, by rw [he, hpk, mul_one]; exact hx'⟩

variable {T M L V H : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem isSylowTwoOf (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) : IsSylowTwoOf T H :=
  E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
    hH.1.1 le_top

theorem charTwo_H (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hH' : InH (P : Subgroup G) H := by rw [hP]; exact hH.1
  exact CFSG.Quasithin.charTwo_of_inH h.qtke.2.1 P hH'

theorem le_normalizer_ZS (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    H ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
  (eq_oTwoUpper_sup_of_isSylowTwoOf' (h.isSylowTwoOf hH)).le.trans
    (sup_le (hH.2.2.trans (Subgroup.centralizer_le_normalizer _))
      h.toHyp611Nat.T_le_normalizer_ZS)

theorem le_normalizer_HS (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  have h1 : x ∈ Subgroup.normalizer
      (Subgroup.centralizer (ch6ZS T L V : Set G) : Set G) :=
    F7.normalizer_le_normalizer_centralizer _ (h.le_normalizer_ZS hH hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp
    (Subgroup.le_normalizer hx) y, Subgroup.mem_normalizer_iff.mp h1 y]

theorem eq_sup (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    H = (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔ T := by
  refine le_antisymm ((eq_oTwoUpper_sup_of_isSylowTwoOf' (h.isSylowTwoOf hH)).le.trans
    (sup_le_sup_right (le_inf (oTwoUpper_le H) hH.2.2) T)) (sup_le inf_le_left hH.1.1)

omit [Finite G] in
theorem S_eq_inf (hH : IsInHS T M L V H) :
    ch6S T L V = T ⊓ (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  rw [← inf_assoc, inf_eq_left.mpr hH.1.1]

theorem isSylowIn_S (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    IsSylowIn 2 (ch6S T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  rw [S_eq_inf hH]
  exact A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf hH) inf_le_left (h.le_normalizer_HS hH)

theorem charTwo (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    CharTwo (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (h.charTwo_H hH).inf_centralizer (h.ZS_le.trans (h.toHyp611.le_T.trans hH.1.1)) ?_
  exact h.sylow.1.to_le (h.ZS_le.trans h.toHyp611.le_T)

theorem pCoreOf_le_S (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ ch6S T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.isSylowIn_S hH).le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem centralizerMod_pCoreOf_le (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    centralizerMod (ch6ZS T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
        (pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))) ≤
      pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set HS := H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hHS
  have hZ2 : IsPGroup 2 (ch6ZS T L V) := h.sylow.1.to_le (h.ZS_le.trans h.toHyp611.le_T)
  have hHSZ : HS ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizerMod_le_left _ _ _)
    (le_normalizer_centralizerMod hHSZ Subgroup.le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 HS))
    (isPGroup_of_forall_pow fun d hd => ?_)
  obtain ⟨hdH, -, hdQ⟩ := mem_centralizerMod.mp hd
  exact exists_pow_two_pow_eq_one_of_stability hHSZ hZ2 (h.charTwo hH) hdH hdH.2 hdQ

theorem V_le_pCoreOf (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  refine fun v hv => h.centralizerMod_pCoreOf_le hH (mem_centralizerMod.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩)
  · exact h.toHyp611.le_T.trans hH.1.1 hv
  · exact (h.V_le_S hv).2
  · exact ((h.V_le_S hv).2 : v ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) |>
      Subgroup.centralizer_le_normalizer _
  · intro q hq
    have hqS := h.pCoreOf_le_S hH hq
    exact h.commutator_V_S_le (Subgroup.commutator_mem_commutator hv hqS)

theorem le_normalizer_pCoreOf (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    H ≤ Subgroup.normalizer
      (pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) : Set G) :=
  (h.le_normalizer_HS hH).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem conjClosure_le_pCoreOf (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    conjClosure V H ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) :=
  conjClosure_le fun _ hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_pCoreOf hH hx) v).mp (h.V_le_pCoreOf hH hv)

theorem conjClosure_le_HS (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    conjClosure V H ≤ H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) :=
  (h.conjClosure_le_pCoreOf hH).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem commutator_conjClosure_pCoreOf_le (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    ⁅conjClosure V H, pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))⁆ ≤
      ch6ZS T L V := by
  set HS := H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hHS
  have hC : conjClosure V H ≤ centralizerMod (ch6ZS T L V) HS (pCoreOf 2 HS) := by
    refine conjClosure_le fun x hx v hv => ?_
    have hxN : x ∈ Subgroup.normalizer
        (centralizerMod (ch6ZS T L V) HS (pCoreOf 2 HS) : Set G) :=
      le_normalizer_centralizerMod (h.le_normalizer_ZS hH) (h.le_normalizer_HS hH)
        (h.le_normalizer_pCoreOf hH) hx
    refine (Subgroup.mem_normalizer_iff.mp hxN v).mp (mem_centralizerMod.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩)
    · exact h.toHyp611.le_T.trans hH.1.1 hv
    · exact (h.V_le_S hv).2
    · exact Subgroup.centralizer_le_normalizer _ (h.V_le_S hv).2
    · intro q hq
      exact h.commutator_V_S_le (Subgroup.commutator_mem_commutator hv (h.pCoreOf_le_S hH hq))
  rw [Subgroup.commutator_le]
  intro u hu q hq
  exact (mem_centralizerMod.mp (hC hu)).2.2 q hq

theorem isElemAbelianMod (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    IsElemAbelianMod (conjClosure V H) (ch6ZS T L V) := by
  have hcomm := h.commutator_conjClosure_pCoreOf_le hH
  have hUQ := h.conjClosure_le_pCoreOf hH
  have hUHS := h.conjClosure_le_HS hH
  have hV := h.toHyp611.isElemAbelian
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ conjClosure V H ∧ x ^ 2 ∈ ch6ZS T L V}
      one_mem' := ⟨(conjClosure V H).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        refine ⟨(conjClosure V H).mul_mem hx hy, ?_⟩
        have hc : ⁅y, x⁆ ∈ ch6ZS T L V := hcomm (Subgroup.commutator_mem_commutator hy (hUQ hx))
        have hxc : x * ⁅y, x⁆ = ⁅y, x⁆ * x :=
          (Subgroup.mem_centralizer_iff.mp (hUHS hx).2 _ hc).symm
        have e : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
          simp only [pow_two]
          calc x * y * (x * y) = x * (y * x) * y := by group
            _ = x * (⁅y, x⁆ * x * y) * y := by rw [commutatorElement_def]; group
            _ = (x * ⁅y, x⁆) * x * y * y := by group
            _ = ⁅y, x⁆ * (x * x * (y * y)) := by rw [hxc]; group
        rw [e]
        exact (ch6ZS T L V).mul_mem hc ((ch6ZS T L V).mul_mem hx2 hy2)
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        refine ⟨(conjClosure V H).inv_mem hx, ?_⟩
        rw [inv_pow]
        exact (ch6ZS T L V).inv_mem hx2 }
  have hΩ : conjClosure V H ≤ Ω := by
    refine conjClosure_le fun x hx v hv => ⟨mem_conjClosure hx hv, ?_⟩
    have hv2 : v ^ 2 = 1 := hV.2 v hv
    have e : (x * v * x⁻¹) ^ 2 = x * v ^ 2 * x⁻¹ := by simp only [pow_two]; group
    rw [e, hv2, mul_one, mul_inv_cancel]
    exact (ch6ZS T L V).one_mem
  intro u hu w hw
  exact ⟨hcomm (Subgroup.commutator_mem_commutator hu (hUQ hw)), (hΩ hu).2⟩

theorem conjClosure_eq (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    conjClosure V H = conjClosure V (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  refine le_antisymm ?_ (conjClosure_mono le_rfl inf_le_left)
  set HS := H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hHS
  have hTN : T ≤ Subgroup.normalizer (conjClosure V HS : Set G) :=
    le_normalizer_conjClosure_of_normalizes h.toHyp611.T_le_normalizer
      (hH.1.1.trans (h.le_normalizer_HS hH))
  have hHN : H ≤ Subgroup.normalizer (conjClosure V HS : Set G) :=
    (h.eq_sup hH).le.trans (sup_le (le_normalizer_conjClosure V HS) hTN)
  refine conjClosure_le fun x hx v hv => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hHN hx) v).mp (le_conjClosure V HS hv)

theorem isO2Trivial (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    IsO2Trivial (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
      (centralizerMod (ch6ZS T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V H)) := by
  set HS := H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hHS
  set C := centralizerMod (ch6ZS T L V) HS (conjClosure V H) with hC
  intro P hPHS hPN hP2
  have hZN : HS ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have htop : HS ≤ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => by simp
  have hSP : IsSylowTwoOf (ch6S T L V ⊓ P) P :=
    A4.isSylowTwoOf_inf_normal (h.isSylowIn_S hH) hPHS hPN
  have hPle : P ≤ (P ⊓ C) ⊔ (ch6S T L V ⊓ P) :=
    le_sup_of_pow_mem hSP fun p hp => by
      obtain ⟨k, hk⟩ := hP2 p hp
      exact ⟨k, P.pow_mem hp _, hk⟩
  have hPV : P ≤ centralizerMod (ch6ZS T L V) ⊤ V := by
    refine hPle.trans (sup_le ?_ ?_)
    · rintro x ⟨-, hxC⟩
      obtain ⟨-, hxZ, hxU⟩ := mem_centralizerMod.mp hxC
      exact mem_centralizerMod.mpr ⟨Subgroup.mem_top _, hxZ,
        fun v hv => hxU v (le_conjClosure V H hv)⟩
    · rintro x ⟨hxS, -⟩
      refine mem_centralizerMod.mpr ⟨Subgroup.mem_top _,
        Subgroup.centralizer_le_normalizer _ hxS.2, fun v hv => ?_⟩
      exact comm_mem_swap (h.commutator_V_S_le (Subgroup.commutator_mem_commutator hv hxS))
  have hU : conjClosure V H ≤ centralizerMod (ch6ZS T L V) ⊤ P := by
    rw [h.conjClosure_eq hH]
    refine conjClosure_le fun x hx v hv => ?_
    have hxN : x ∈ Subgroup.normalizer (centralizerMod (ch6ZS T L V) ⊤ P : Set G) :=
      le_normalizer_centralizerMod hZN htop hPN hx
    refine (Subgroup.mem_normalizer_iff.mp hxN v).mp
      (mem_centralizerMod.mpr ⟨Subgroup.mem_top _, ?_, fun p hp => ?_⟩)
    · exact Subgroup.centralizer_le_normalizer _ (h.V_le_S hv).2
    · exact comm_mem_swap ((mem_centralizerMod.mp (hPV hp)).2.2 v hv)
  intro p hp
  refine mem_centralizerMod.mpr ⟨hPHS hp, hZN (hPHS hp), fun u hu => ?_⟩
  exact comm_mem_swap ((mem_centralizerMod.mp (hU hu)).2.2 p hp)

theorem isReducedMod (h : Hyp6116 G T M L V n) (hH : IsInHS T M L V H) :
    IsReducedMod (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) (conjClosure V H)
      (ch6ZS T L V) :=
  ⟨h.ZS_le.trans (le_conjClosure V H), h.conjClosure_le_HS hH,
    inf_le_left.trans (le_normalizer_conjClosure V H),
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _), h.isElemAbelianMod hH,
    h.isO2Trivial hH⟩

theorem pCoreOf_eq_centralizerMod (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n)
    (hH : IsInHS T M L V H) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) =
      centralizerMod (ch6ZS T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set HS := H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hHS
  set C := centralizerMod (ch6ZS T L V) HS (conjClosure V H) with hC
  have hZN : HS ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hV := h.toHyp611.isElemAbelian
  apply le_antisymm
  ·
    intro q hq
    refine mem_centralizerMod.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 HS hq,
      hZN (CFSG.LieType.BorelTits.pCoreOf_le 2 HS hq), fun u hu => ?_⟩
    exact comm_mem_swap (h.commutator_conjClosure_pCoreOf_le hH
      (Subgroup.commutator_mem_commutator hu hq))
  have hCN : C ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    obtain ⟨-, -, hcU⟩ := mem_centralizerMod.mp hc
    have key : ∀ v ∈ V, c * v * c⁻¹ ∈ V := fun v hv => by
      have h1 := h.ZS_le (hcU v (le_conjClosure V H hv))
      have e : c * v * c⁻¹ = (c * v * c⁻¹ * v⁻¹) * v := by group
      rw [e]
      exact V.mul_mem h1 hv
    refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨key v, fun hv => ?_⟩
    have hinj : Function.Injective (fun w : ↥V => (⟨c * w * c⁻¹, key w w.2⟩ : ↥V)) :=
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨c * v * c⁻¹, hv⟩
    have hwv : (w : G) = v := by
      have := congrArg Subtype.val hw
      simpa using this
    rw [← hwv]
    exact w.2
  have hodd : ∀ c ∈ C, Odd (orderOf c) → c ∈ Subgroup.centralizer (V : Set G) := by
    intro c hc ho
    obtain ⟨hcHS, -, hcU⟩ := mem_centralizerMod.mp hc
    exact mem_centralizer_of_odd hV h.ZS_le (fun v hv => hcU v (le_conjClosure V H hv))
      hcHS.2 ho
  set X := oTwoUpper C with hX
  have hXV : X ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.closure_le _).mpr fun c hc => hodd c hc.1 hc.2
  have hXM : X ≤ M := (oTwoUpper_le C).trans (hCN.trans (h.hypE61 h432).normalizer_le)
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod (h.le_normalizer_ZS hH) (h.le_normalizer_HS hH)
      (le_normalizer_conjClosure V H)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    hHC.trans (normalizer_le_normalizer_oTwoUpper C)
  have hP2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hPT : pCoreOf 2 L ≤ T := by
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
        (h.toHyp611.sup_le_normalizer_L.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) hP2
    rw [← h.toHyp611.centralizer_eq] at h1
    exact h1.trans inf_le_left
  have hPX : pCoreOf 2 L ≤ Subgroup.normalizer (X : Set G) := hPT.trans (hH.1.1.trans hHX)
  have hXeq : X = oTwoUpper (X ⊔ pCoreOf 2 L) :=
    eq_oTwoUpper_of_pow_mem le_sup_left
      (fun y hy => exists_pow_mem_of_le_normalizer hP2 hPX hy) (A4.oTwoUpper_oTwoUpper C).symm
  have hLY : L ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
    have hconj : ∀ l ∈ L, ∀ y ∈ X ⊔ pCoreOf 2 L, l * y * l⁻¹ ∈ X ⊔ pCoreOf 2 L := by
      intro l hl y hy
      have hy' : y ∈ (X : Set G) * (pCoreOf 2 L : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left X (pCoreOf 2 L) hPX]
        exact hy
      obtain ⟨x, hx, p, hp, rfl⟩ := hy'
      have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normal (hXM hx)
      have hc : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L :=
        comm_mem_swap (h.commutator_mem_pCoreOf hxL (hXV hx) hl)
      have hlp : l * p * l⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl)
          p).mp hp
      have e : l * (x * p) * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x * (l * p * l⁻¹) := by group
      rw [e]
      exact (X ⊔ pCoreOf 2 L).mul_mem ((X ⊔ pCoreOf 2 L).mul_mem
        (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx)) (Subgroup.mem_sup_right hlp)
    intro l hl
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconj l hl y, fun hy => ?_⟩
    have := hconj l⁻¹ (L.inv_mem hl) _ hy
    simpa [mul_assoc] using this
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXeq]
    exact hLY.trans (normalizer_le_normalizer_oTwoUpper _)
  have hX1 : X = ⊥ := by
    by_contra hne
    have hXch : CharTwo X :=
      (h.charTwo_H hH).of_normal ((oTwoUpper_le C).trans
        ((centralizerMod_le_left _ _ _).trans inf_le_left))
        (Subgroup.normal_subgroupOf_of_le_normalizer hHX)
    have hO := pCoreOf_ne_bot_of_charTwo hXch hne
    have hNX : Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
    have hloc := le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM h432)
      ((sup_le hLX (hH.1.1.trans hHX)).trans hNX)
      ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
    exact hH.2.1 (hHX.trans (hNX.trans hloc))
  have hC2 : IsPGroup 2 C := by
    refine isPGroup_of_forall_pow fun c hc => ?_
    obtain ⟨c₂, c₀, hc₂, hc₀, hcc, hk, ho⟩ := exists_two_part c
    have hc₀C : c₀ ∈ C := Subgroup.zpowers_le.mpr hc hc₀
    have hc₀1 : c₀ = 1 := by
      have : c₀ ∈ X := mem_oTwoUpper_of_odd hc₀C ho
      rw [hX1] at this
      exact Subgroup.mem_bot.mp this
    rw [hcc, hc₀1, mul_one]
    exact hk
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizerMod_le_left _ _ _)
    (inf_le_left.trans hHC) hC2

end Hyp6116

theorem stmt6_1_17 (h432 : Stmt4_3_2) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
      ∀ H : Subgroup G, IsInHS T M L V H →
        (V ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
          IsSylowIn 2 (ch6S T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
          QuasithinUnique.CharTwo (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
          H ≤ Subgroup.normalizer
            ((H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) ∧
          H = (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔ T) ∧
        (IsReducedMod (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) (conjClosure V H)
            (ch6ZS T L V) ∧
          conjClosure V H ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
          ⁅conjClosure V H, pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))⁆ ≤
            ch6ZS T L V) ∧
        pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) =
          centralizerMod (ch6ZS T L V) (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
            (conjClosure V H) ∧
        (∀ s ∈ ch6S T L V, s ∉ Subgroup.centralizer (V : Set G) →
          ∀ Y : Subgroup G, ch6ZS T L V ≤ Y → Y ≤ V →
            ⁅V, Subgroup.zpowers s⁆ = ch6ZS T L V ∧
            Nat.card ↥⁅Y, Subgroup.zpowers s⁆ * Nat.card (ch6ZS T L V) = Nat.card Y) ∧
        ∀ Y : Subgroup G, ch6ZS T L V ≤ Y → Y ≤ V → Y.relIndex V = 2 →
          ∀ S₀ : Subgroup G, S₀ ≤ ch6S T L V → ¬ IsCyclic ↥(autOn S₀ V) →
            ch6ZS T L V = ⁅Y, S₀⁆ := by
  intro G _ _ T M L V n h H hH
  exact ⟨⟨h.V_le_pCoreOf hH, h.isSylowIn_S hH, h.charTwo hH, h.le_normalizer_HS hH,
      h.eq_sup hH⟩,
    ⟨h.isReducedMod hH, h.conjClosure_le_pCoreOf hH, h.commutator_conjClosure_pCoreOf_le hH⟩,
    h.pCoreOf_eq_centralizerMod h432 hH,
    fun s hs hsV Y hZY hYV => ⟨h.commutator_zpowers_eq hs hsV,
      h.card_commutator_mul hs hsV hZY hYV⟩,
    fun Y hZY hYV hY2 S₀ hS₀ hnc => h.ZS_eq_commutator hZY hYV hY2 hS₀ hnc⟩

end CFSG.Quasithin.H13
