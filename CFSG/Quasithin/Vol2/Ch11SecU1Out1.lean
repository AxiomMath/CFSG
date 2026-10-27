module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11SecU1Dih

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open A1b

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem oddTorus_of_dihedral (hLn : L.Normal) {b : G} {m : ℕ} [NeZero m] (hm : Odd m)
    (hm3 : 3 ≤ m) (d : ↥(L ⊓ Subgroup.centralizer {b}) ≃* DihedralGroup m) : OddTorus L b := by
  set X := L ⊓ Subgroup.centralizer ({b} : Set G) with hX
  set r := m.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := fun h => by
    have := Nat.minFac_dvd m
    rw [← hr, h] at this
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  have hrodd : Odd r := hrp.odd_of_ne_two hr2
  have hcardX : Nat.card X = 2 * m := by rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := X) r
    (by rw [hcardX]; exact Dvd.dvd.mul_left (Nat.minFac_dvd m) 2)
  set P : Subgroup G := Subgroup.zpowers (y₀ : G) with hP
  have hPcard : Nat.card P = r := by rw [hP, Nat.card_zpowers, Subgroup.orderOf_coe, hy₀]
  have hPX : P ≤ X := Subgroup.zpowers_le.mpr y₀.2
  refine ⟨P, hPX, by rw [hPcard]; exact hrp, by rw [hPcard]; exact hr2, ?_, ?_⟩
  · intro c hc
    have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcP : A1b.conjSub c P ≤ X := by
      intro w hw
      rw [A1b.mem_conjSub_iff] at hw
      have hw' := hPX hw
      refine Subgroup.mem_inf.mpr ⟨by simpa [mul_assoc] using hLn.conj_mem _ hw'.1 c, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hw'.2
      have hcb' : c * b * c⁻¹ = b := by rw [hcb]; group
      calc w * b = c * (c⁻¹ * w * c * b) * c⁻¹ := by
            rw [show c * (c⁻¹ * w * c * b) * c⁻¹ = w * (c * b * c⁻¹) by group, hcb']
        _ = c * (b * (c⁻¹ * w * c)) * c⁻¹ := by rw [h1]
        _ = b * w := by
            rw [show c * (b * (c⁻¹ * w * c)) * c⁻¹ = (c * b * c⁻¹) * w by group, hcb']
    have hcard' : Nat.card (A1b.conjSub c P) = Nat.card P :=
      Nat.card_congr (P.equivMapOfInjective _ (MulAut.conj c).injective).toEquiv.symm
    have hsub : (A1b.conjSub c P).subgroupOf X = P.subgroupOf X := by
      refine eq_of_odd_of_mulEquiv d ?_ ?_
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcP).toEquiv, hcard', hPcard]
        exact hrodd
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcP).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hcard']
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hcP, inf_eq_left.mpr hPX] at hsub
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [← hsub]
      exact ⟨w, hw, rfl⟩
    · intro hw
      rw [← hsub, A1b.mem_conjSub_iff] at hw
      simpa [mul_assoc] using hw
  · intro y hy hy2 _ hPy
    obtain ⟨x, hx, hxy⟩ := not_centralizes_of_mulEquiv hm d (P := P.subgroupOf X)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hPcard]; exact hrodd)
      (fun h => by
        rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def] at h
        have h1 := Subgroup.card_eq_one.mpr (le_bot_iff.mp fun z hz => Subgroup.mem_bot.mpr
          (h hz (hPX hz)))
        rw [hPcard] at h1
        exact hrp.one_lt.ne' h1)
      (y := ⟨y, hy⟩) (by rw [Subgroup.orderOf_mk, hy2])
    apply hxy
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hPy (Subgroup.mem_subgroupOf.mp hx))
    simpa using this.symm

end CFSG.Quasithin.Vol2.Ch11.SecU1
