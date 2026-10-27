module

public import CFSG.Quasithin.H13.L32ASecSplit
public import CFSG.Quasithin.H13.L32A774a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem v_le_sL {T L V : Subgroup G} : V ≤ sL T L V := v_le_fsuU.trans (le_conjClosure _ _)

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem sL_le_P : sL T L V ≤ pCoreOf 2 L := C.sL_le_pCoreOf_L C.u0_eq

@[expose] def pTwo : Subgroup G where
  carrier := {p | p ∈ pCoreOf 2 L ∧ p ^ 2 ∈ sL T L V}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    have hc := C.comm_mem_v_of_mem_pCoreOf (inv_mem ha.1) hb.1
    rw [show (a * b) ^ 2 = a ^ 2 * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * b ^ 2 by
      simp only [pow_two]; group]
    exact mul_mem (mul_mem ha.2 (v_le_sL hc)) hb.2⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    rw [inv_pow]
    exact inv_mem ha.2⟩

theorem sq_mem_v_of_mem_pTwo {p : G} (hp : p ∈ C.pTwo) : p ^ 2 ∈ V := by
  obtain ⟨hpP, hpS⟩ := hp
  refine C.mem_v_of_comm_mem hpS fun l hl => ?_
  set s := l * p * l⁻¹ * p⁻¹ with hs
  have hsS : s ∈ sL T L V := C.comm_mem_sL_of_mem_pCoreOf hpP hl
  have hps : p * s * p⁻¹ * s⁻¹ ∈ V := C.comm_mem_v_sL hpP hsS
  have hs2 : s ^ 2 ∈ V := C.sq_mem C.u0_eq hsS
  have hc : (p * s * p⁻¹ * s⁻¹) * s = s * (p * s * p⁻¹ * s⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hps)).2 s hsS).symm
  have e : l * p ^ 2 * l⁻¹ * (p ^ 2)⁻¹ = (p * s * p⁻¹ * s⁻¹) * s ^ 2 := by
    have h1 : l * p * l⁻¹ = s * p := by rw [hs]; group
    calc l * p ^ 2 * l⁻¹ * (p ^ 2)⁻¹ = (l * p * l⁻¹) * (l * p * l⁻¹) * (p ^ 2)⁻¹ := by
          simp only [pow_two]; group
      _ = s * p * (s * p) * (p ^ 2)⁻¹ := by rw [h1]
      _ = s * ((p * s * p⁻¹ * s⁻¹) * s) := by group
      _ = s * (s * (p * s * p⁻¹ * s⁻¹)) := by rw [hc]
      _ = (p * s * p⁻¹ * s⁻¹) * s ^ 2 := by
          rw [show s * (s * (p * s * p⁻¹ * s⁻¹)) = s ^ 2 * (p * s * p⁻¹ * s⁻¹) by
            simp only [pow_two]; group]
          exact Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp (C.v_le_centerOf hps)).2 _ (pow_mem hsS 2)
  rw [e]
  exact mul_mem hps hs2

theorem exists_compl_pTwo : ∃ N : Subgroup G, V ≤ N ∧ N ≤ C.pTwo ∧
    (∀ n ∈ N, ∀ l ∈ L, l * n * l⁻¹ * n⁻¹ ∈ V) ∧ N ⊓ sL T L V = V ∧
    ∀ x ∈ C.pTwo, ∃ n ∈ N, ∃ s ∈ sL T L V, x = n * s := by
  obtain ⟨θ, -, hθs, hθ1, -, -, -, -, -, χ, hχk, hχt, hχs, hχe⟩ :=
    C.exists_st C.u0_eq C.vh65 C.l71
  have hLV := C.L_le_normalizer_V
  have hPL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hPn : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hLS : L ≤ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _
  have hSP2 : sL T L V ≤ C.pTwo := fun s hs =>
    ⟨C.sL_le_P hs, v_le_sL (C.sq_mem C.u0_eq hs)⟩
  have hVP2 : V ≤ C.pTwo := v_le_sL.trans hSP2
  have hP2L : L ≤ Subgroup.normalizer (C.pTwo : Set G) :=
    le_normalizer_of_conj_mem' fun l hl p hp => ⟨
      (Subgroup.mem_normalizer_iff.mp (hPn hl) p).mp hp.1, by
        rw [conj_pow]
        exact (Subgroup.mem_normalizer_iff.mp (hLS hl) _).mp hp.2⟩
  have D : SecMod L C.pTwo V θ :=
    { le := hVP2
      normX := hP2L
      normY := hLV
      comm := fun a ha b hb => C.comm_mem_v_of_mem_pCoreOf ha.1 hb.1
      sq := fun a ha => C.sq_mem_v_of_mem_pTwo ha
      surj := hθs
      ker := fun l hl x hx => by
        have hlP : (l : G) ∈ pCoreOf 2 L := by
          rw [C.pCoreOf_eq]
          exact Subgroup.mem_inf.mpr ⟨l.2, (hθ1 l).mp hl⟩
        exact C.comm_mem_v_of_mem_pCoreOf hlP hx.1
      faithful := fun l hl => (hθ1 l).mpr
        (C.mem_centralizer_of_comm_mem C.u0_eq l.2 fun s hs => hl s (hSP2 hs)) }
  obtain ⟨N, hVN, hNP2, hNL, hNS, hgen⟩ :=
    D.exists_compl C.vh63 v_le_sL hSP2 hLS hχk hχt hχs hχe
  refine ⟨N, hVN, hNP2, fun n hn l hl => ?_, hNS, hgen⟩
  rw [← hNS]
  refine Subgroup.mem_inf.mpr ⟨?_, C.comm_mem_sL_of_mem_pCoreOf (hNP2 hn).1 hl⟩
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hl) n).mp hn) (inv_mem hn)

theorem pCoreOf_eq_sL_of (hX : ∀ q ∈ pCoreOf 2 L, (∀ l ∈ L, l * q * l⁻¹ * q⁻¹ ∈ V) → q ∈ V) :
    pCoreOf 2 L = sL T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, -, hNP2, hNL, -, hgen⟩ := C.exists_compl_pTwo
  have hP2S : C.pTwo ≤ sL T L V := by
    intro x hx
    obtain ⟨n, hn, s, hs, rfl⟩ := hgen x hx
    exact mul_mem (v_le_sL (hX n (hNP2 hn).1 (hNL n hn))) hs
  refine le_antisymm (fun p hp => ?_) C.sL_le_P
  by_contra hpS
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨p, hp⟩
  have hk' : p ^ 2 ^ k ∈ sL T L V := by
    have : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  have hex : ∃ m, p ^ 2 ^ m ∈ sL T L V := ⟨k, hk'⟩
  set m := Nat.find hex with hm
  have hmS : p ^ 2 ^ m ∈ sL T L V := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hmS
    exact hpS hmS
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hq : p ^ 2 ^ m' ∈ C.pTwo := ⟨pow_mem hp _, by
    rw [← pow_mul, ← pow_succ]
    rw [hm'] at hmS
    exact hmS⟩
  exact Nat.find_min hex (show m' < m by omega) (hP2S hq)

end Ctx73

end CFSG.Quasithin.H13.L32A
