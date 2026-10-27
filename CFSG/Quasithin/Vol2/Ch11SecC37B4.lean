module

public import CFSG.Quasithin.Vol2.Ch11SecC37B3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fix_of_comm_fix {d z k : G} (hk : d * z * d⁻¹ * z⁻¹ = k) (hdk : d * k * d⁻¹ = k)
    (hk2 : k ^ 2 = 1) (hodd : Odd (orderOf d)) : d * z * d⁻¹ = z := by
  have hdz : d * z * d⁻¹ = k * z := by rw [← hk]; group
  have hpow : ∀ j : ℕ, d ^ j * z * (d ^ j)⁻¹ = k ^ j * z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hdkj : d * k ^ j * d⁻¹ = k ^ j := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hdk]
      calc d ^ (j + 1) * z * (d ^ (j + 1))⁻¹ = d * (d ^ j * z * (d ^ j)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
        _ = (d * k ^ j * d⁻¹) * (d * z * d⁻¹) := by rw [ih]; group
        _ = k ^ (j + 1) * z := by rw [hdkj, hdz, pow_succ, mul_assoc]
  have h1 := hpow (orderOf d)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hkm : k ^ orderOf d = 1 := by
    have := congrArg (· * z⁻¹) h1
    simpa using this.symm
  have hk1 : k = 1 := by
    have h4 : orderOf k ∣ Nat.gcd 2 (orderOf d) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk2) (orderOf_dvd_of_pow_eq_one hkm)
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), Nat.dvd_one,
      orderOf_eq_one_iff] at h4
    exact h4
  rw [hdz, hk1, one_mul]

omit [Finite G] in
theorem fix_left_of_fix {x u c : G} (hc : x * c * x⁻¹ = c) (huc : x * (u * c) * x⁻¹ = u * c) :
    x * u * x⁻¹ = u := by
  calc x * u * x⁻¹ = (x * (u * c) * x⁻¹) * (x * c * x⁻¹)⁻¹ := by group
    _ = u := by rw [huc, hc]; group

structure Inp37 : Prop where
  h1102 : Stmt11_0_2
  h1104 : Stmt11_0_4
  h1122 : Stmt11_2_2
  h1134 : Stmt11_3_4
  h1135 : Stmt11_3_5
  h1136 : Stmt11_3_6
  h331 : Stmt3_3_1
  hG16 : ASInputs.AS_G_1_6
  h51 : AsB51
  hAS : FactAStarSylow
  hFPF : FactSL2NatFPF
  hF : SecA.NatFacts
  hSN : FactSL2SylowNormalizer
  hB : FactSL2Borel
  hBS : FactBorelOddSL3
  hBP : FactBorelOddSp4
  hKF : KindModuleFacts
  hTS : FactTorusLineSL3
  hTP : FactTorusLineSp4
  hFC1 : SecB.FactFlagOneCentral

omit [Finite G] in
theorem fixed_of_mem_Z {T L : Subgroup G} {z u c : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hc : c ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)) (hzuc : z = u * c) :
    ∀ p ∈ T ⊓ L, p * u * p⁻¹ = u := by
  intro p hp
  refine fix_left_of_fix (c := c) ?_ ?_
  · rw [Subgroup.mem_centralizer_iff.mp hc p (le_sup_right (a := L) hp.1), mul_inv_cancel_right]
  · rw [← hzuc, Subgroup.mem_centralizer_iff.mp (Z_le_center T hz).2 p hp.1, mul_inv_cancel_right]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem exists_fpf (i : Inp37) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    ∃ d ∈ d0Of D, ∀ u ∈ ⁅VZ T (L ⊔ T), L⁆, (∀ p ∈ T ⊓ L, p * u * p⁻¹ = u) →
      d * u * d⁻¹ = u → u ∈ Subgroup.centralizer (L : Set G) := by
  have hG2 := i.hKF.2.2.2
  have hZL := s.Z_inf_centralizer_L hJ i.hG16 i.hAS i.hFPF i.hF i.h1102 hG2 i.h1122 i.h1104
    i.h1134 i.h1135 i.h1136 i.h331 i.hSN i.hB hD
  have hVL := s.fsuV_inf_centralizer_L hJ i.hG16 i.hAS i.hFPF i.hF i.h1102 hG2 i.h1122 i.h1104
    i.h1134 i.h1135 i.h1136 i.h331 i.hSN i.hB hD
  by_contra hne
  apply s.not_d0_centralizes_Z i.hG16 i.hAS i.hFPF i.hF i.h1102 hG2 i.h1122 i.h1134 i.h1135
    i.h1136 i.h331 i.hSN hD
  intro d hd z hz
  have hdL : d ∈ L := d0Of_le i.h1104 i.h1134 i.h1135 i.h1136 i.hB s.hyp hJ s.hV₁ s.h31 s.hnot
    s.hAT s.hAC hD hd
  have hdN := s.d0Of_le_normalizer i.h1102 i.h1104 i.h1134 i.h1135 i.h1136 i.hB i.hBS i.hBP hJ
    hD hd
  have hA := (s.perDich i.h51 i.h1102 i.hKF i.hTS i.hTP i.h1134 hJ hZL hVL hdL hdN).resolve_right
    fun h => hne ⟨d, hd, h⟩
  obtain ⟨u, hu, c, hc, hzuc⟩ := s.exists_decomp hz
  have hdc : d * c * d⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 d (le_sup_left (b := T) hdL), mul_inv_cancel_right]
  have hk := hA u hu (fixed_of_mem_Z hz hc.2 hzuc)
  have hkz : d * z * d⁻¹ * z⁻¹ = d * u * d⁻¹ * u⁻¹ := by
    rw [hzuc]
    calc d * (u * c) * d⁻¹ * (u * c)⁻¹ = d * u * d⁻¹ * (d * c * d⁻¹) * c⁻¹ * u⁻¹ := by group
      _ = d * u * d⁻¹ * u⁻¹ := by rw [hdc]; group
  have hdk : d * (d * u * d⁻¹ * u⁻¹) * d⁻¹ = d * u * d⁻¹ * u⁻¹ := by
    rw [Subgroup.mem_centralizer_iff.mp hk d hdL, mul_inv_cancel_right]
  have hzW : z ∈ VZ T (L ⊔ T) := Z_le_VZ T (L ⊔ T) hz
  have hkW : d * z * d⁻¹ * z⁻¹ ∈ VZ T (L ⊔ T) :=
    (VZ T (L ⊔ T)).mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_VZ T (L ⊔ T)
      (le_sup_left (b := T) hdL)) z).mp hzW) ((VZ T (L ⊔ T)).inv_mem hzW)
  have hk2 : (d * u * d⁻¹ * u⁻¹) ^ 2 = 1 := hkz ▸ s.vzLT.2.1.2 _ hkW
  have hodd : Odd (orderOf d) := hD.2.1.of_dvd_nat (by
    rw [← Subgroup.orderOf_mk d (d0Of_le_self D hd)]
    exact orderOf_dvd_natCard _)
  exact fix_of_comm_fix hkz hdk hk2 hodd

theorem Z_fix (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {d : G}
    (hdL : d ∈ L) (hfpf : ∀ u ∈ ⁅VZ T (L ⊔ T), L⁆, (∀ p ∈ T ⊓ L, p * u * p⁻¹ = u) →
      d * u * d⁻¹ = u → u ∈ Subgroup.centralizer (L : Set G))
    {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hdz : d * z * d⁻¹ = z) : z = 1 := by
  obtain ⟨u, hu, c, hc, hzuc⟩ := s.exists_decomp hz
  have hdc : d * c * d⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 d (le_sup_left (b := T) hdL), mul_inv_cancel_right]
  have huL := hfpf u hu (fixed_of_mem_Z hz hc.2 hzuc)
    (fix_left_of_fix hdc (hzuc ▸ hdz))
  have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (le_sup_left (b := T)) hc.2
  have : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hz, hzuc ▸ Subgroup.mul_mem _ huL hcL⟩
  rwa [hZL, Subgroup.mem_bot] at this

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
