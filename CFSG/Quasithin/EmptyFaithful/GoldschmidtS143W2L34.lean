module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2NoDih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow

import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2DihB

public section

namespace CFSG.Quasithin

open CFSG.OddStandard.Seitz77.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

namespace S143

namespace InspW2

theorem f4_coords : ∀ a b a' b' : F4, a * b ≠ 0 → a * b' = a' * b → a' * b' = 0 →
    a' = 0 ∧ b' = 0 := by
  decide

theorem f4_add_self : ∀ a : F4, a + a = 0 := by
  decide

theorem unip_involution_central {x y : ↥(unipAll F4)} (hx : orderOf x = 4) (hy : y * y = 1)
    (hxy : x * y = y * x) (z : ↥(unipAll F4)) : y * z = z * y := by
  obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
  obtain ⟨a', b', c', rfl⟩ := exists_ofCoords y
  obtain ⟨a'', b'', c'', rfl⟩ := exists_ofCoords z
  have hab : a * b ≠ 0 := by
    intro h
    have hsq : ofCoords a b c ^ 2 = 1 := by
      rw [pow_two, ofCoords_mul, ← ofCoords_zero, ofCoords_inj, f4_add_self a, f4_add_self b,
        f4_add_self c, h]
      exact ⟨rfl, rfl, by simp⟩
    have h2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hx] at h2
    omega
  rw [ofCoords_mul, ofCoords_mul, ofCoords_inj] at hxy
  have hcomm : a * b' = a' * b := by linear_combination hxy.2.2
  rw [ofCoords_mul, ← ofCoords_zero, ofCoords_inj, f4_add_self a', f4_add_self b',
    f4_add_self c'] at hy
  have hinv : a' * b' = 0 := by simpa using hy.2.2
  obtain ⟨rfl, rfl⟩ := f4_coords a b a' b' hab hcomm hinv
  exact (ofCoords_comm_central a'' b'' c'' c').symm

theorem mem_normalizer_of_mem_centralizer {L : Type*} [Group L] {H : Subgroup L} {g : L}
    (hg : g ∈ Subgroup.centralizer (H : Set L)) : g ∈ Subgroup.normalizer H := by
  have hc : ∀ g' ∈ Subgroup.centralizer (H : Set L), ∀ x ∈ H, g' * x * g'⁻¹ = x := by
    intro g' hg' x hx
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hg' x hx).symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => by rw [hc g hg h hh]; exact hh, fun hh => ?_⟩
  have h1 := hc g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [h2] at h1
  rw [h1]
  exact hh

theorem center_psl34_eq_bot : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcent : (x : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    rw [Subgroup.mem_inf]
    refine ⟨?_, S_le_R x.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at hcent
  exact Subtype.ext hcent

theorem resW_l34 :
    ResW fun L _ => CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 3 2 2 := by
  intro L _ _ _ hF Gc _ _ ρ ž Ŝ Kh hin _
  obtain ⟨e⟩ := nonempty_equiv_of_stated L hF
  have hcard : Nat.card L = 20160 := by rw [Nat.card_congr e.toEquiv, card_S]
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_mulEquiv e center_psl34_eq_bot
  have h6 : 2 ^ 6 ∣ Nat.card L := ⟨315, by rw [hcard]; norm_num⟩
  obtain ⟨w, a, b, hw, hwa, hwb, ha, hb, hab, hab4⟩ := exists_dihedral_in_inn hZ h6 hin
  have hw4 : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have hD : IsPGroup 2 (Subgroup.closure {a, b}) := isPGroup_closure_dihedral ha hb hab4
  have hW : IsPGroup 2 (Subgroup.zpowers w) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    show (g : L) ^ 2 ^ 2 = 1
    have h4 : w ^ ((2 ^ 2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; simpa using hw4
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, h4, one_zpow]
  have hcent : Subgroup.closure ({a, b} : Set L) ≤ Subgroup.centralizer {w} := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hwa.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hwb.symm
  have hwc : w ∈ Subgroup.centralizer (Subgroup.closure ({a, b} : Set L) : Set L) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hcent hh)
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (Subgroup.closure ({a, b} : Set L) :
      Set L) := Subgroup.zpowers_le.mpr (mem_normalizer_of_mem_centralizer hwc)
  obtain ⟨V, hV⟩ := (hD.to_sup_of_normal_left' hW hnorm).exists_le_sylow
  have hwV : w ∈ (V : Subgroup L) := hV (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have haV : a ∈ (V : Subgroup L) :=
    hV (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
  have hbV : b ∈ (V : Subgroup L) :=
    hV (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
  have hZodd : Odd (Nat.card (Subgroup.center L)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  let e' : L ⧸ Subgroup.center L ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans ((QuotientGroup.quotientBot (G := L)).trans e)
  obtain ⟨ι, -, hι, hr, -⟩ := exists_chart hZodd e' V
  rw [← hr] at hwV haV hbV
  obtain ⟨xw, rfl⟩ := hwV
  obtain ⟨xa, rfl⟩ := haV
  obtain ⟨xb, rfl⟩ := hbV
  have hx4 : orderOf xw = 4 := by rw [← orderOf_injective ι hι xw]; exact hw
  have hxa : xa * xa = 1 := hι (by rw [map_mul, ha, map_one])
  have hxwa : xw * xa = xa * xw := hι (by rw [map_mul, map_mul, hwa])
  have hc := unip_involution_central hx4 hxa hxwa xb
  exact hab (by rw [← map_mul, ← map_mul, hc])

end InspW2

end S143

end CFSG.Quasithin
