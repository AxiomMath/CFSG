module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSylow
public import CFSG.LocalAnalysis.WeakClosure81.W15Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem fixed_le_of_fixedPointFree (h : Cex15 M V₀ V U S) {x : G}
    (hxU : x ∈ centralizer (U : Set G)) (hfix : ∀ v ∈ V₀, x * v * x⁻¹ = v → v = 1) :
    ∀ v ∈ V, x * v * x⁻¹ = v → v ∈ U := by
  intro v hv hxv
  obtain ⟨w, hw, u, hu, rfl⟩ := h.decomp hv
  have hxu : x * u * x⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hxU u hu).symm
  have hxw : x * w * x⁻¹ = w := by
    have e : x * (w * u) * x⁻¹ = (x * w * x⁻¹) * (x * u * x⁻¹) := by group
    rw [e, hxu] at hxv
    exact mul_right_cancel hxv
  rw [hfix w hw hxw, one_mul]
  exact hu

theorem exists_fixed_mul (h : Cex15 M V₀ V U S) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    {Q : Subgroup G} (hQ : IsPGroup r Q) (hQC : Q ≤ F11.CTilde M V₀ V) {v : G} (hv : v ∈ V) :
    ∃ c ∈ V, (∀ q ∈ Q, q * c * q⁻¹ = c) ∧ ∃ w ∈ V₀, v = w * c := by
  have hH := h.hyp
  have hVM : M ≤ normalizer (V : Set G) := hH.h6.normalizer_eq.symm.le
  let T : Set G := {x : G | x * v⁻¹ ∈ V₀}
  have hT : ∀ q ∈ Q, ∀ x ∈ T, q * x * q⁻¹ ∈ T := by
    intro q hq x hx
    obtain ⟨hqM, hqN, hcomm⟩ := FourteenTwo.mem_cTilde_iff_comm.1 (hQC hq)
    have hx' : x * v⁻¹ ∈ V₀ := hx
    show q * x * q⁻¹ * v⁻¹ ∈ V₀
    have e : q * x * q⁻¹ * v⁻¹ = (q * (x * v⁻¹) * q⁻¹) * (q * v * q⁻¹ * v⁻¹) := by group
    rw [e]
    exact V₀.mul_mem ((Subgroup.mem_normalizer_iff.1 hqN _).1 hx') (hcomm v hv)
  let _ : MulAction Q T :=
    { smul := fun q x => ⟨q * x * q⁻¹, hT q q.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : Q) : G) * (x : G) * ((1 : Q) : G)⁻¹ = x
        simp)
      mul_smul := fun p q x => Subtype.ext (by
        change (↑(p * q) : G) * x * (↑(p * q) : G)⁻¹ = ↑p * (↑q * x * (↑q)⁻¹) * (↑p)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hcard : ¬ r ∣ Nat.card T := by
    have h1 : Nat.card T = Nat.card V₀ := Nat.card_congr
      { toFun := fun x => ⟨x.1 * v⁻¹, x.2⟩
        invFun := fun w => ⟨w.1 * v, by
          show w.1 * v * v⁻¹ ∈ V₀
          simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (hH.isPGroup.to_le hH.h6.le)
    rw [h1, hk]
    intro hdvd
    have h2 : r ∣ 2 := (Fact.out : r.Prime).dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact (Fact.out : r.Prime).one_lt.ne' h3
    · exact hr h3
  obtain ⟨⟨c, hcT⟩, hfix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hQ T hcard
  have hc : c * v⁻¹ ∈ V₀ := hcT
  refine ⟨c, ?_, fun q hq => ?_, ⟨v * c⁻¹, ?_, by group⟩⟩
  · have : c = (c * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem (hH.h6.le hc) hv
  · have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
    exact this
  · have : v * c⁻¹ = (c * v⁻¹)⁻¹ := by group
    rw [this]
    exact V₀.inv_mem hc

theorem inf_centralizer_eq (h : Cex15 M V₀ V U S) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    {Q : Subgroup G} (hQ : IsPGroup r Q) (hQC : Q ≤ F11.CTilde M V₀ V) {x : G} (hxQ : x ∈ Q)
    (hxU : x ∈ centralizer (U : Set G)) (hfix : ∀ v ∈ V₀, x * v * x⁻¹ = v → v = 1) :
    V ⊓ centralizer (Q : Set G) = U := by
  have hle : V ⊓ centralizer (Q : Set G) ≤ U := by
    intro c hc
    refine h.fixed_le_of_fixedPointFree hxU hfix c hc.1 ?_
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hc.2 x hxQ)
  refine le_antisymm hle fun u hu => ?_
  obtain ⟨c, hcV, hcQ, w, hw, hwc⟩ := h.exists_fixed_mul hr hQ hQC (h.le hu)
  have hcC : c ∈ V ⊓ centralizer (Q : Set G) :=
    ⟨hcV, Subgroup.mem_centralizer_iff.2 fun q hq => by
      have := hcQ q hq
      rwa [mul_inv_eq_iff_eq_mul] at this⟩
  have hcU : c ∈ U := hle hcC
  have hwU : w ∈ U := by
    have : w = u * c⁻¹ := by rw [hwc]; group
    rw [this]
    exact U.mul_mem hu (U.inv_mem hcU)
  have hw1 : w = 1 := by
    have : w ∈ U ⊓ V₀ := ⟨hwU, hw⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at this
    exact this
  rw [hwc, hw1, one_mul]
  exact hcC

theorem false_of_fixedPointFree (h : Cex15 M V₀ V U S) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) {x : G}
    (hxU : x ∈ centralizer (U : Set G)) (hxM : x ∈ M) (hx : IsPGroup r (zpowers x))
    (hfix : ∀ v ∈ V₀, x * v * x⁻¹ = v → v = 1) : False := by
  have hH := h.hyp
  have hVM : M ≤ normalizer (V : Set G) := hH.h6.normalizer_eq.symm.le
  have hV₀M : M ≤ normalizer (V₀ : Set G) := hH.normalizer₀.symm.le
  have hxC : x ∈ F11.CTilde M V₀ V := h.centralizer_le_cTilde ⟨hxM, hxU⟩
  obtain ⟨Q, hQ, hxQ'⟩ := exists_isSylowIn_ge r (zpowers_le.2 hxC) hx
  have hxQ : x ∈ Q := hxQ' (mem_zpowers x)
  have hCQ : V ⊓ centralizer (Q : Set G) = U :=
    h.inf_centralizer_eq hr hQ.isPGroup hQ.le hxQ hxU hfix
  have hCM : ((F11.CTilde M V₀ V).subgroupOf M).Normal :=
    cTilde_subgroupOf_normal hH.h6.elemAbelian hVM hV₀M
  have hfrat := frattini_isSylowIn (cTilde_le_M M V₀ V) hCM hQ
  have hnorm : ∀ n ∈ M, n ∈ normalizer (Q : Set G) → ∀ u ∈ U, n * u * n⁻¹ ∈ U := by
    intro n hnM hnQ u hu
    rw [← hCQ]
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hVM hnM) u).1 (h.le hu),
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have hq' : n⁻¹ * q * n⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (inv_mem hnQ) q).1 hq
    have huc : u ∈ V ⊓ centralizer (Q : Set G) := hCQ ▸ hu
    have h1 : (n⁻¹ * q * n⁻¹⁻¹) * u = u * (n⁻¹ * q * n⁻¹⁻¹) :=
      Subgroup.mem_centralizer_iff.1 huc.2 _ hq'
    calc q * (n * u * n⁻¹) = n * ((n⁻¹ * q * n⁻¹⁻¹) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * q * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
      _ = (n * u * n⁻¹) * q := by group
  have hnormU : ∀ n ∈ M, n ∈ normalizer (Q : Set G) → n ∈ normalizer (U : Set G) := by
    intro n hnM hnQ
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hnorm n hnM hnQ u hu, fun hu => ?_⟩
    have := hnorm n⁻¹ (M.inv_mem hnM) (inv_mem hnQ) _ hu
    simpa [mul_assoc] using this
  have hCV : M ⊓ centralizer (V : Set G) ≤ M ⊓ normalizer (U : Set G) :=
    inf_le_inf_left M
      ((Subgroup.centralizer_le h.le).trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hmul : ∀ m ∈ M, ∃ x ∈ M ⊓ normalizer (U : Set G), ∃ c ∈ F11.CTilde M V₀ V, m = x * c := by
    intro m hm
    obtain ⟨y, hy, n, hnM, hnQ, hyn⟩ := hfrat m hm
    refine ⟨n, ⟨hnM, hnormU n hnM hnQ⟩, n⁻¹ * y * n, ?_, ?_⟩
    · have := hCM.conj_mem ⟨y, cTilde_le_M M V₀ V hy⟩ (Subgroup.mem_subgroupOf.2 hy)
        ⟨n⁻¹, M.inv_mem hnM⟩
      simpa using Subgroup.mem_subgroupOf.1 this
    · rw [← hyn]
      group
  have hN := hH.s14c U h.le h.ne_bot hCV hmul
  exact h.not_le ((Subgroup.centralizer_le_normalizer (U : Set G)).trans hN)

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
