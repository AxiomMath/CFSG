module

public import CFSG.Quasithin.Vol2.Ch11SecO6E

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem mem_pCore_of_pow_eq_one {r : ℕ} [Fact r.Prime] {z : X}
    (hz : z ∈ CFSG.fittingSubgroup X) {k : ℕ} (hzk : z ^ r ^ k = 1) : z ∈ CFSG.pCore r X := by
  set F : Subgroup X := CFSG.fittingSubgroup X
  have hD : IsPGroup r (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (z ^ i) ^ r ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
  have hDF : Subgroup.zpowers z ≤ F := Subgroup.zpowers_le.mpr hz
  have hD' : IsPGroup r ((Subgroup.zpowers z).subgroupOf F) := hD.comap_subtype
  obtain ⟨S, hS⟩ := hD'.exists_le_sylow
  have hSn : (S : Subgroup F).Normal := inferInstance
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S hSn
  have hmapn : ((S : Subgroup F).map F.subtype).Normal := inferInstance
  have hle : (S : Subgroup F).map F.subtype ≤ CFSG.pCore r X :=
    le_sSup ⟨hmapn, S.isPGroup'.map _⟩
  exact hle ⟨⟨z, hz⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)), rfl⟩

theorem conj_eq_of_forall_pCore {s : X}
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card (CFSG.fittingSubgroup X) → ∀ z ∈ CFSG.pCore r X,
      (∀ f ∈ CFSG.fittingSubgroup X, z * f = f * z) → z * s = s * z → ∀ y : X, y * z * y⁻¹ = z)
    {z : X} (hzF : z ∈ CFSG.fittingSubgroup X)
    (hzc : ∀ f ∈ CFSG.fittingSubgroup X, z * f = f * z) (hzs : z * s = s * z) (y : X) :
    y * z * y⁻¹ = z := by
  set F : Subgroup X := CFSG.fittingSubgroup X
  set n := Nat.card F with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have hyz : y * z * y⁻¹ ∈ F := Subgroup.Normal.conj_mem inferInstance z hzF y
  set w := y * z * y⁻¹ * z⁻¹ with hw
  have hwF : w ∈ F := Subgroup.mul_mem _ hyz (Subgroup.inv_mem _ hzF)
  have hpart : ∀ r : ℕ, r.Prime → r ∣ n → w ^ (n / r ^ n.factorization r) = 1 := by
    intro r hr hrn
    have : Fact r.Prime := ⟨hr⟩
    set m := n / r ^ n.factorization r
    have hzm : (z ^ m) ^ r ^ n.factorization r = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel (Nat.ordProj_dvd n r)]
      have := pow_card_eq_one' (G := F) (x := ⟨z, hzF⟩)
      exact congrArg Subtype.val this
    have hzr : z ^ m ∈ CFSG.pCore r X :=
      mem_pCore_of_pow_eq_one (Subgroup.pow_mem _ hzF m) hzm
    have h1 := h r hr hrn (z ^ m) hzr (fun f hf => ((Commute.pow_left (hzc f hf)) m).eq)
      ((Commute.pow_left hzs) m).eq y
    have hc : Commute (y * z * y⁻¹) z⁻¹ := (Commute.inv_left (hzc _ hyz)).symm
    rw [hw, hc.mul_pow, inv_pow, conj_pow, h1, mul_inv_cancel]
  have hw1 : w = 1 := by
    by_contra hne
    have hord : orderOf w ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
    set r := (orderOf w).minFac
    have hr : r.Prime := Nat.minFac_prime hord
    have hrw : r ∣ orderOf w := Nat.minFac_dvd _
    have hwn : orderOf w ∣ n := Subgroup.orderOf_dvd_natCard F hwF
    have hrn : r ∣ n := hrw.trans hwn
    have hdvd : orderOf w ∣ n / r ^ n.factorization r := orderOf_dvd_of_pow_eq_one (hpart r hr hrn)
    exact Nat.not_dvd_ordCompl hr hn0 (hrw.trans hdvd)
  calc y * z * y⁻¹ = w * z := by rw [hw]; group
    _ = z := by rw [hw1, one_mul]

omit [Finite X] in
theorem exists_involution {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {F : Subgroup X}
    (hFodd : Odd (Nat.card F)) {ψ : X →* SL(2, ZMod q)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = F) :
    ∃ s : X, s ^ 2 = 1 ∧ s ∉ F ∧ ∀ y : X, y * s * y⁻¹ * s⁻¹ ∈ F := by
  have hc := SecG.SL2.wElt_sq_mem_center (k := ZMod q)
  have hc2 := SecG.SL2.sq_eq_one_of_mem_center hc
  obtain ⟨x, hx⟩ := hψ (SecG.SL2.wElt ^ 2)
  have hx2 : x ^ 2 ∈ F := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hx, hc2]
  set s := x ^ Nat.card F with hs
  have hψs : ψ s = SecG.SL2.wElt ^ 2 := by
    obtain ⟨k, hk⟩ := hFodd
    rw [hs, map_pow, hx, hk, pow_succ, pow_mul, hc2, one_pow, one_mul]
  refine ⟨s, ?_, ?_, fun y => ?_⟩
  · have := pow_card_eq_one' (G := F) (x := ⟨x ^ 2, hx2⟩)
    have h1 : (x ^ 2) ^ Nat.card F = 1 := congrArg Subtype.val this
    rw [hs, ← pow_mul, mul_comm, pow_mul, h1]
  · rw [← hker, MonoidHom.mem_ker, hψs]
    exact wElt_sq_ne_one (p := q) hq2
  · rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hψs,
      Subgroup.mem_center_iff.mp hc (ψ y)]
    group

end CFSG.Quasithin.Vol2.Ch11.O6
