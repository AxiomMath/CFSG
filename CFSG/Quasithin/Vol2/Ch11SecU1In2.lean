module

public import CFSG.Quasithin.Vol2.Ch11SecU1In1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11SecU1Dih

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.GorensteinWalter A1b

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {p : ℕ}
  [Fact p.Prime]

theorem three_dvd_sq_sub_one (hp5 : 5 ≤ p) : 3 ∣ p ^ 2 - 1 := by
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  have h1 : p ^ 2 % 3 = 1 := by
    rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h <;> simp [Nat.pow_mod, h]
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem inner_torus_of_equiv
    (e : L ≃* PSL2 K) (hLn : L.Normal) (hK : Nat.card K = p ^ 2)
    (hp : Odd p) (hp5 : 5 ≤ p) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) : OddTorus L x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn4, hn, ⟨d⟩⟩ := inner_dihedral_of_equiv e hK hp hp5 hxL hx
  have : NeZero n := ⟨by omega⟩
  set t := e ⟨x, hxL⟩ with ht
  have htx : x = embL e t := (embL_apply e hxL).symm
  have ht2 : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  set C := Subgroup.centralizer ({t} : Set (PSL2 K)) with hC
  set X := L ⊓ Subgroup.centralizer ({x} : Set G) with hX
  have hXmap : X = C.map (embL e) := inf_centralizer_eq_map e hxL
  have hcardX : Nat.card X = p ^ 2 - 1 := by
    rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
    omega
  have hcardC : Nat.card C = Nat.card X := by
    rw [hXmap]
    exact (Subgroup.card_map_of_injective (embL_injective e)).symm
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := C) 3
    (by rw [hcardC, hcardX]; exact three_dvd_sq_sub_one hp5)
  set A₀ : Subgroup (PSL2 K) := Subgroup.zpowers (y₀ : PSL2 K) with hA₀
  have hA₀C : A₀ ≤ C := Subgroup.zpowers_le.mpr y₀.2
  have hA₀card : Nat.card A₀ = 3 := by
    rw [hA₀, Nat.card_zpowers, Subgroup.orderOf_coe, hy₀]
  set P := A₀.map (embL e) with hP
  have hPcard : Nat.card P = 3 := by
    rw [hP, Subgroup.card_map_of_injective (embL_injective e), hA₀card]
  have hPX : P ≤ X := by rw [hXmap]; exact Subgroup.map_mono hA₀C
  refine ⟨P, hPX, by rw [hPcard]; exact Nat.prime_three, by rw [hPcard]; decide, ?_, ?_⟩
  ·
    intro c hc
    have hcP : A1b.conjSub c P ≤ X := by
      intro w hw
      rw [A1b.mem_conjSub_iff] at hw
      have hw' := hPX hw
      refine Subgroup.mem_inf.mpr ⟨by simpa [mul_assoc] using hLn.conj_mem _ hw'.1 c, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hw'.2
      calc w * x = c * (c⁻¹ * w * c * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * w * c * x) * c⁻¹ := by
          rw [show c⁻¹ * x * c = x by
            calc c⁻¹ * x * c = c⁻¹ * (c * x) := by rw [hc]; group
              _ = x := by group]
        _ = c * (x * (c⁻¹ * w * c)) * c⁻¹ := by rw [h1]
        _ = x * w := by
          rw [show c * (x * (c⁻¹ * w * c)) * c⁻¹ = (c * x * c⁻¹) * w by group]
          rw [show c * x * c⁻¹ = x by rw [hc]; group]
    have hcard' : Nat.card (A1b.conjSub c P) = Nat.card P :=
      Nat.card_congr (P.equivMapOfInjective _ (MulAut.conj c).injective).toEquiv.symm
    have hsub : (A1b.conjSub c P).subgroupOf X = P.subgroupOf X := by
      refine eq_of_odd_of_mulEquiv d ?_ ?_
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcP).toEquiv, hcard', hPcard]
        decide
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
  ·
    intro y hy hy2 hyx hPy
    have hy' : y ∈ C.map (embL e) := by
      have h1 : y ∈ X := hy
      rw [hXmap] at h1
      exact h1
    obtain ⟨s, hsC, rfl⟩ := hy'
    have hs2 : orderOf s = 2 := (orderOf_injective _ (embL_injective e) s).symm.trans hy2
    have hst : s ≠ t := fun h => hyx (by rw [h, htx])
    have hcomm : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsC
    have hV := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair
      hs2 ht2 hcomm hst
    refine psl2_no_kleinFour_centralizes_odd_cyclic K ⟨p, 2, Fact.out, hp, by norm_num, hK⟩ A₀ _
      inferInstance (fun h => by simp [h] at hA₀card) (by rw [hA₀card]; decide) hV ?_
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro a ha
      apply embL_injective e
      have := Subgroup.mem_centralizer_singleton_iff.mp (hPy ⟨a, ha, rfl⟩)
      simpa [map_mul] using this
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hA₀C ha))

end CFSG.Quasithin.Vol2.Ch11.SecU1
