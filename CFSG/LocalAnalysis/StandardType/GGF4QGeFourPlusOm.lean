module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOne
public import CFSG.LocalAnalysis.StandardType.GGRankOneShared
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

section Om

theorem not_twD4_of_plusMembers (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X Z : Subgroup G} (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hBs4 : p ^ 4 ≤ Nat.card ↥Bs) {f : ℕ} (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) {x z : G} (hxB : x ∈ Bs) (hzB : z ∈ Bs)
    (hXs : CFSG.Assembly.IsSubnormal X (Subgroup.centralizer ({x} : Set G)))
    (hZs : CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)))
    (hBZ : Bs ≤ Subgroup.normalizer (Z : Set G))
    (hmX : GGCentralImage .POmegaMinus 4 f X) (hInnX : GGInnerDiagOn Bs X)
    (hZX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hZperf : commutator ↥Z = ⊤) (hInnZ : GGInnerDiagOn Bs Z)
    (hZZ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (Z : Set G)) = p)
    {r u v r' : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs) (huX : u ∈ ggAutomizer X Bs)
    (hvX : v ∈ ggAutomizer X Bs) (hrZ : r ∈ ggAutomizer Z Bs) (hr'Z : r' ∈ ggAutomizer Z Bs)
    (hr : GGIsReflection p r) (hu : GGIsReflection p u) (hv : GGIsReflection p v)
    (hr' : GGIsReflection p r') (huv : u ≠ v) (huv3 : (u * v) ^ 3 = 1)
    (hru4 : (r * u) ^ 4 = 1) (hru2 : (r * u) ^ 2 ≠ 1) (hrr' : r ≠ r')
    (hrr'3 : (r * r') ^ 3 = 1) :
    ¬ GGHasLabel ⟨.twD, 4, f⟩ (↥Z ⧸ Subgroup.center ↥Z) := by
  intro hlab
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hmZ := ggF4Ends_centralImage_POmegaMinus hZperf hf hlab
  obtain ⟨hX1, hX2, hX3, -⟩ :=
    plusMember_facts_of_image hMp hp hBs hNT hBs4 hf hpq hmX hInnX hZX
  obtain ⟨hZ1, hZ2, -, -⟩ :=
    plusMember_facts_of_image hMp hp hBs hNT hBs4 hf hpq hmZ hInnZ hZZ
  have hbr := (hX3 r hrX u huX hr hu hru4 hru2).mpr (hX2 u huX v hvX hu hv huv huv3)
  have hsr := hZ2 r hrZ r' hr'Z hr hr' hrr' hrr'3
  have heq := ggRankOneIn_eq_of_mem_ggAutomizer (hp.odd_of_ne_two hp2) hBs hxB hzB hXs hZs hBZ
    hrX hrZ (hX1 r hrX hr).1 (hZ1 r hrZ hr).1 hr.1 (GGIsReflection.ne_one hp hr)
  rw [heq, hsr] at hbr
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  generalize 2 ^ f = q at hq hbr
  have hq4 : q + 1 < q ^ 4 := by
    calc q + 1 < q * 4 := by omega
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_left _ (hq.trans (Nat.le_self_pow (by norm_num) q))
      _ = q ^ 4 := by ring
  have hlt : q < q ^ 4 - 1 := by omega
  have h3 : q * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) :=
    calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = q ^ 2 * q := by ring
      _ < q ^ 2 * (q ^ 4 - 1) := mul_lt_mul_of_pos_left hlt (by positivity)
  exact absurd hbr (ne_of_lt h3)

end Om

end CFSG.StandardType

end
