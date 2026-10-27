module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.OddModelBC2Struct
import CFSG.Timmesfeld.Transvection.OddModelBC2
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.Transvection.OddPairsModel
import CFSG.ClassicalInvolution.Phan.Parabolic.Generic
import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open CFSG.ClassicalInvolution.Phan (exists_hom_sup_of_normalizes forall_conj_of_gens
  conjAutOfNormalizer coe_conjAutOfNormalizer closure_eq_top_of_le_closure)
open CFSG.ClassicalInvolution.WeakCT (exists_hom_of_le_range)
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

section

local notation "X" γ:max => CFSG.LieType.Universal.Unitary.rootGroup
  (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r + 1) γ
local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2)))

private theorem oddEmb_suElt_prev_last_inr (c : F) :
    oddEmb (unitaryInvolution F 2 n) r
        (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c) =
      suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr))
        (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) c := by
  rw [oddEmb_suElt, sCast_inl, sCast_inr, finCastOdd_cPrevIdx, finCastOdd_cLastIdx]

private theorem oddEmb_suElt_prev_last_inl (c : F) :
    oddEmb (unitaryInvolution F 2 n) r
        (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c) =
      suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr))
        (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c := by
  rw [oddEmb_suElt, sCast_inl, sCast_inl, finCastOdd_cPrevIdx, finCastOdd_cLastIdx]

private theorem oddEmb_suLong_prev (c : F) :
    oddEmb (unitaryInvolution F 2 n) r
        (suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) c) =
      suLong (unitaryInvolution F 2 n) (Sum.inl (bcPrevIdx r hr)) c := by
  rw [oddEmb_suLong, sCast_inl, finCastOdd_cPrevIdx]

private theorem closure_rootGroups_eq_bc2Q0 :
    Subgroup.closure ((X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
      (X (Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
      (X (2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _)) =
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq,
    Subgroup.closure_eq, Subgroup.closure_eq]
  rfl

private theorem closure_rootGroups_eq_bc2Qe1 :
    Subgroup.closure ((X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
      (X (Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
      (X (2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
      (X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _)) =
      bc2Qe1 (unitaryInvolution_involutive hFn) hr := by
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_union,
    Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq]
  rfl

private theorem exists_su3Emb_prev_of_mem {x : SU (unitaryInvolution F 2 n) (2 * r + 1)}
    (hx : x ∈ X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    ∃ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 ∧
      su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcPrevIdx r hr) (heis₃ u v) = x := by
  obtain ⟨u, v, huv, hx'⟩ := (mem_rootGroup_iff_suHeis (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.2.2.1 x).mp hx
  exact ⟨u, v, huv, by rw [su3Emb_suHeis_inl, hx']⟩

private theorem exists_su3Emb_last_of_mem {x : SU (unitaryInvolution F 2 n) (2 * r + 1)}
    (hx : x ∈ X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    ∃ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 ∧
      su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) (heis₃ u v) = x := by
  obtain ⟨u, v, huv, hx'⟩ := (mem_rootGroup_iff_suHeis (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.1 x).mp hx
  exact ⟨u, v, huv, by rw [su3Emb_suHeis_inl, hx']⟩

namespace OddFrameCompatible

variable {hFn hr Ψ₀ θ}

private theorem commute_oddPrevLift_of_mem_gens (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hprev_inr : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
    (hprev_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    {u v : F} (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    {x : SU (unitaryInvolution F 2 n) (2 * r + 1)}
    (hx : x ∈ (X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
      (X (Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
      (X (2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _))
    {y : SU (unitaryInvolution F 2 n) (2 * r)}
    (hy : oddEmb (unitaryInvolution F 2 n) r y = x) :
    Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v)) (Ψ₀ y) := by
  rcases hx with (hx | hx) | hx
  · obtain ⟨c, hxc⟩ := (mem_rootGroup_iff_suElt_odd (unitaryInvolution_involutive hFn)
      (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)))
      (bcPrevIdx_ne_bcLastIdx hr) (toStd_bc2 hr).1 x).mp hx
    have hy' : y = suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c := by
      apply oddEmb_injective r
      rw [hy]
      exact ((oddEmb_suElt_prev_last_inr (hFn := hFn) (hr := hr) c).trans hxc).symm
    rw [hy']
    exact hprev_inr u v huv c
  · obtain ⟨c, hxc⟩ := (mem_rootGroup_iff_suElt_odd (unitaryInvolution_involutive hFn)
      (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
      (bcPrevIdx_ne_bcLastIdx hr) (toStd_bc2 hr).2.2.2.2.1 x).mp hx
    have hy' : y = suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c := by
      apply oddEmb_injective r
      rw [hy]
      exact ((oddEmb_suElt_prev_last_inl (hFn := hFn) (hr := hr) c).trans hxc).symm
    rw [hy']
    exact hprev_inl u v huv c
  · obtain ⟨c, hc0, hxc⟩ := (mem_rootGroup_iff_suLong_odd (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.2.2 x).mp hx
    have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
    have hy' : y = suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) c := by
      apply oddEmb_injective r
      rw [hy]
      exact ((oddEmb_suLong_prev (hr := hr) c).trans hxc).symm
    rw [hy', ← hd.oddPrevLift_suLong_inl hc]
    have hcomm : Commute (heis₃ u v)
        (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) :=
      commutatorElement_eq_one_iff_mul_comm.mp
        (suHeis_comm_suLong (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl))
          (a := Sum.inl (0 : Fin (3 / 2))) (c := Sum.inl (0 : Fin (3 / 2)))
          Sum.inl_ne_inr u v c)
    exact hcomm.map (oddPrevLift hFn hr Ψ₀ θ)

private theorem agree_bc2Q0_heisP_bc2Qe1 (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {φN : ↥(bc2Q0 (unitaryInvolution_involutive hFn) hr) →* H}
    {φT : ↥(X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφN : ∀ (x : ↥(bc2Q0 (unitaryInvolution_involutive hFn) hr))
      (s : SU (unitaryInvolution F 2 n) (2 * r)),
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
        oddEmb (unitaryInvolution F 2 n) r s → φN x = Ψ₀ s)
    (hφT : ∀ (x : ↥(X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
      (s : SU (unitaryInvolution F 2 n) 3),
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcPrevIdx r hr) s → φT x = oddPrevLift hFn hr Ψ₀ θ s)
    (g : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hN : g ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr)
    (hT : g ∈ X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) :
    φN ⟨g, hN⟩ = φT ⟨g, hT⟩ := by
  have hgl : g ∈ X (2 • Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) :=
    heisP_inf_bc2Q0 (unitaryInvolution_involutive hFn) hr ⟨hT, hN⟩
  obtain ⟨c, hc0, hgc⟩ :=
    (mem_rootGroup_iff_suLong_odd (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.2.2 g).mp hgl
  have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
  have hNval : φN ⟨g, hN⟩ = Ψ₀ (suLong (unitaryInvolution F 2 n)
      (Sum.inl (cPrevIdx r hr)) c) := by
    refine hφN ⟨g, hN⟩ _ ?_
    show g = oddEmb (unitaryInvolution F 2 n) r
      (suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) c)
    rw [← hgc, oddEmb_suLong, sCast_inl, finCastOdd_cPrevIdx]
  have hTval : φT ⟨g, hT⟩ = oddPrevLift hFn hr Ψ₀ θ
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) := by
    refine hφT ⟨g, hT⟩ _ ?_
    show g = su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcPrevIdx r hr) (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c)
    rw [← hgc, su3Emb_suLong_inl]
  rw [hNval, hTval]
  exact (hd.oddPrevLift_suLong_inl hc).symm

private theorem conj_bc2Q0_heisP_bc2Qe1 (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hprev_inr : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
    (hprev_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    {φN : ↥(bc2Q0 (unitaryInvolution_involutive hFn) hr) →* H}
    {φT : ↥(X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}
    (hφN : ∀ (x : ↥(bc2Q0 (unitaryInvolution_involutive hFn) hr))
      (s : SU (unitaryInvolution F 2 n) (2 * r)),
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
        oddEmb (unitaryInvolution F 2 n) r s → φN x = Ψ₀ s)
    (hφT : ∀ (x : ↥(X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
      (s : SU (unitaryInvolution F 2 n) 3),
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcPrevIdx r hr) s → φT x = oddPrevLift hFn hr Ψ₀ θ s)
    (hNT : X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ≤
      Subgroup.normalizer (bc2Q0 (unitaryInvolution_involutive hFn) hr : Set _)) :
    ∀ (t : ↥(X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
      (g : ↥(bc2Q0 (unitaryInvolution_involutive hFn) hr)),
      φT t * φN g * (φT t)⁻¹ = φN (conjAutOfNormalizer hNT t g) := by
  have hS0 : Subgroup.closure ((X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
      (X (Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
      (X (2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _)) =
      bc2Q0 (unitaryInvolution_involutive hFn) hr :=
    closure_rootGroups_eq_bc2Q0 (F := F) (n := n) hFn hr
  intro t g
  refine forall_conj_of_gens hNT φN φT (SN := {x : ↥(bc2Q0
      (unitaryInvolution_involutive hFn) hr) |
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
        (X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
          (X (Pi.single (bcPrevIdx r hr) 1 +
            2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
          (X (2 • Pi.single (bcPrevIdx r hr) 1 +
            2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _)})
    (ST := Set.univ) ?_ Subgroup.closure_univ ?_ t g
  · refine closure_eq_top_of_le_closure (fun x hx => ?_) (le_of_eq hS0.symm)
    exact hS0 ▸ Subgroup.subset_closure hx
  · intro t' _ x hx
    obtain ⟨u, v, huv, ht⟩ := (mem_rootGroup_iff_suHeis
      (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.2.2.1 (t' : SU (unitaryInvolution F 2 n) (2 * r + 1))).mp t'.2
    have ht' : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcPrevIdx r hr) (heis₃ u v) = suHeis (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcPrevIdx r hr)) u v :=
      su3Emb_suHeis_inl (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr) u v
    have hφt : φT t' = oddPrevLift hFn hr Ψ₀ θ (heis₃ u v) :=
      hφT t' (heis₃ u v) ((ht'.trans ht).symm)
    obtain ⟨y, hy⟩ := bc2Q0_le_range_oddEmb (unitaryInvolution_involutive hFn) hr x.2
    have hφn : φN x = Ψ₀ y := hφN x y hy.symm
    have hconjx : conjAutOfNormalizer hNT t' x = x := by
      apply Subtype.ext
      rw [coe_conjAutOfNormalizer]
      exact Commute.mul_inv_cancel ((Subgroup.mem_centralizer_iff.mp
        (heisP_le_centralizer (unitaryInvolution_involutive hFn) hr t'.2)
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) x.2).symm)
    rw [hφt, hφn, hconjx, hφn]
    exact Commute.mul_inv_cancel
      (commute_oddPrevLift_of_mem_gens hd hprev_inr hprev_inl huv hx hy)

private theorem exists_hom_bc2Qe1 (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hprev_inr : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
    (hprev_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c))) :
    ∃ φ₁ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr) →* H,
      (∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
        (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr),
        x ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr →
          ∀ y : SU (unitaryInvolution F 2 n) (2 * r),
            oddEmb (unitaryInvolution F 2 n) r y = x → φ₁ ⟨x, hx⟩ = Ψ₀ y) ∧
      (∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
        (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr),
        x ∈ X (Pi.single (bcPrevIdx r hr) 1 +
          Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
          ∀ A : SU (unitaryInvolution F 2 n) 3,
            su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
              (bcPrevIdx r hr) A = x → φ₁ ⟨x, hx⟩ = oddPrevLift hFn hr Ψ₀ θ A) := by
  obtain ⟨φN, hφN⟩ := exists_hom_of_le_range (oddEmb (unitaryInvolution F 2 n) r)
    (oddEmb_injective r) Ψ₀ (bc2Q0 (unitaryInvolution_involutive hFn) hr)
    (bc2Q0_le_range_oddEmb (unitaryInvolution_involutive hFn) hr)
  obtain ⟨φT, hφT⟩ := exists_hom_of_le_range
    (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr))
    (su3Emb_injective (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr))
    (oddPrevLift hFn hr Ψ₀ θ)
    (X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (rootGroup_le_range_su3Emb (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcPrevIdx r hr))
      (toStd_bc2 hr).2.2.2.1)
  have hNT : X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ≤
      Subgroup.normalizer (bc2Q0 (unitaryInvolution_involutive hFn) hr : Set _) :=
    (heisP_le_centralizer (unitaryInvolution_involutive hFn) hr).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨φ, hφN', hφT'⟩ := exists_hom_sup_of_normalizes hNT φN φT
    (agree_bc2Q0_heisP_bc2Qe1 hd hφN hφT)
    (conj_bc2Q0_heisP_bc2Qe1 hd hprev_inr hprev_inl hφN hφT hNT)
  refine ⟨φ, ?_, ?_⟩
  · intro x hx hx0 y hy
    exact (hφN' ⟨x, hx0⟩).trans (hφN ⟨x, hx0⟩ y hy.symm)
  · intro x hx hxP A hA
    exact (hφT' ⟨x, hxP⟩).trans (hφT ⟨x, hxP⟩ A hA.symm)

local notation "heisL" u:max v:max => suHeis (unitaryInvolution F 2 n)
  (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
  (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) u v
local notation "heisP" u:max v:max => suHeis (unitaryInvolution F 2 n)
  (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
  (Sum.inl (bcPrevIdx r hr)) u v

private def bc2RootGroups : Set (SU (unitaryInvolution F 2 n) (2 * r + 1)) :=
  (X (Pi.single (bcPrevIdx r hr) 1) : Set _) ∪
    (X (Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
    (X (2 • Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _) ∪
    (X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) : Set _)

private structure BC2Qe1Clauses {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hFn : Nat.card F = (2 ^ n) ^ 2) {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
    (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H)
    (θ : SU (unitaryInvolution F 2 n) 3 →* H)
    (φ₁ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr) →* H) : Prop where
  onQ0 : ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr),
    x ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr →
      ∀ y : SU (unitaryInvolution F 2 n) (2 * r),
        oddEmb (unitaryInvolution F 2 n) r y = x → φ₁ ⟨x, hx⟩ = Ψ₀ y
  onHeisP : ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr),
    x ∈ CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
      (unitaryInvolution_involutive hFn) (2 * r + 1)
      (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
      ∀ A : SU (unitaryInvolution F 2 n) 3,
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcPrevIdx r hr) A = x → φ₁ ⟨x, hx⟩ = oddPrevLift hFn hr Ψ₀ θ A

private theorem heisP_mem_bc2Qe1 (u v : F) :
    heisP u v ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr := by
  show heisP u v ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr ⊔
    X (Pi.single (bcPrevIdx r hr) 1 +
      Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
  exact Subgroup.mem_sup_right (suHeis_mem (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.2.2.1 u v)

private theorem suElt_prev_two_mem_bc2Q0 (c : F) :
    suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
  show _ ∈ X (Pi.single (bcPrevIdx r hr) 1) ⊔
    X (Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ⊔
    X (2 • Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (suElt_mem
    (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
    (unitaryInvolution_involutive hFn) (bcPrevIdx_ne_bcLastIdx hr)
    (toStd_bc2 hr).2.2.2.2.1 c))

private theorem suElt_prev_two_mem_bc2Qe1 (c : F) :
    suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr :=
  (le_sup_left : bc2Q0 (unitaryInvolution_involutive hFn) hr ≤
    bc2Qe1 (unitaryInvolution_involutive hFn) hr)
    (suElt_prev_two_mem_bc2Q0 (hFn := hFn) c)

private theorem suElt_prev_last_mem_bc2Q0 (c : F) :
    suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) c ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
  show _ ∈ X (Pi.single (bcPrevIdx r hr) 1) ⊔
    X (Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ⊔
    X (2 • Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (suElt_mem
    (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)))
    (unitaryInvolution_involutive hFn) (bcPrevIdx_ne_bcLastIdx hr) (toStd_bc2 hr).1 c))

private theorem suLong_prev_mem_bc2Q0 (c : F) :
    suLong (unitaryInvolution F 2 n) (Sum.inl (bcPrevIdx r hr)) c ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
  show _ ∈ X (Pi.single (bcPrevIdx r hr) 1) ⊔
    X (Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ⊔
    X (2 • Pi.single (bcPrevIdx r hr) 1 +
      2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
  exact Subgroup.mem_sup_right (suLong_mem (unitaryInvolution_involutive hFn)
    (Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.2.2 c)

section Gluing

variable {hNT : CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
      (unitaryInvolution_involutive hFn) (2 * r + 1)
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ≤
    Subgroup.normalizer (bc2Qe1 (unitaryInvolution_involutive hFn) hr : Set _)}
  {φ₁ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr) →* H}
  {φT : ↥(CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F 2 n)
    (unitaryInvolution_involutive hFn) (2 * r + 1)
    (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H}

private theorem agree_bc2Qe1_heisL :
    ∀ (g : SU (unitaryInvolution F 2 n) (2 * r + 1))
      (hN : g ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr)
      (hT : g ∈ X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
      φ₁ ⟨g, hN⟩ = φT ⟨g, hT⟩ := by
  intro g hN hT
  have hbot : g ∈ (⊥ : Subgroup (SU (unitaryInvolution F 2 n) (2 * r + 1))) := by
    rw [← heisL_inf_bc2Qe1 (unitaryInvolution_involutive hFn) hr]
    exact ⟨hT, hN⟩
  have hg1 : g = 1 := Subgroup.mem_bot.mp hbot
  subst hg1
  rw [show (⟨1, hN⟩ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr)) = 1
      from Subtype.ext rfl,
    show (⟨1, hT⟩ : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))) = 1
      from Subtype.ext rfl, map_one, map_one]

private theorem phi_conj_suElt_inr (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁) {u v s : F}
    (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s) :
    φ₁ (conjAutOfNormalizer hNT t x) =
      (oddPrevLift hFn hr Ψ₀ θ
          (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
        Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
          (s * unitaryInvolution F 2 n v)))⁻¹ * φ₁ x := by
  have hmemA : heisP (s * u) (unitaryInvolution F 2 n s * s * v) ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr :=
    heisP_mem_bc2Qe1 (hFn := hFn) (s * u) (unitaryInvolution F 2 n s * s * v)
  have hmemB : suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (s * unitaryInvolution F 2 n v) ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr :=
    suElt_prev_two_mem_bc2Qe1 (hFn := hFn) (s * unitaryInvolution F 2 n v)
  have hform := conj_suHeis_suElt_swap (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcPrevIdx r hr))
    (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) (bcPrevIdx_ne_bcLastIdx hr) s huv
  rw [show Sum.swap (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) =
    Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)) from rfl] at hform
  have hconjval : (conjAutOfNormalizer hNT t x :
      SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      heisL u v *
        suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s *
        (heisL u v)⁻¹ := by
    rw [coe_conjAutOfNormalizer, ht, hx]
  have hmemT : heisL u v *
        suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s *
        (heisL u v)⁻¹ ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr := by
    rw [hform, ← hx]
    exact mul_mem (inv_mem (mul_mem hmemA hmemB)) x.2
  let y : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr) :=
    ⟨heisL u v * suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s *
        (heisL u v)⁻¹, hmemT⟩
  have hsub : conjAutOfNormalizer hNT t x = y := Subtype.ext hconjval
  have hprod : y = (⟨heisP (s * u) (unitaryInvolution F 2 n s * s * v), hmemA⟩ *
      ⟨suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (s * unitaryInvolution F 2 n v), hmemB⟩)⁻¹ * x := by
    apply Subtype.ext
    change heisL u v * suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s *
          (heisL u v)⁻¹ =
        (heisP (s * u) (unitaryInvolution F 2 n s * s * v) *
          suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
            (s * unitaryInvolution F 2 n v))⁻¹ *
          (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
    rw [hx]
    exact hform
  rw [hsub, hprod, map_mul, map_inv, map_mul,
    hc.onHeisP _ hmemA (suHeis_mem (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.2.2.1 (s * u)
      (unitaryInvolution F 2 n s * s * v))
      (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v))
      (su3Emb_suHeis_inl (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr) (s * u)
        (unitaryInvolution F 2 n s * s * v)),
    hc.onQ0 _ hmemB (suElt_prev_two_mem_bc2Q0 (hFn := hFn)
      (s * unitaryInvolution F 2 n v))
      (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
        (s * unitaryInvolution F 2 n v))
      (oddEmb_suElt_prev_last_inl (hFn := hFn) (hr := hr)
        (s * unitaryInvolution F 2 n v))]

private theorem map_conj_suHeis_last_suElt_inr
    (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁)
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s), θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr Ψ₀ θ
              (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
            Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
              (s * unitaryInvolution F 2 n v)))
    {u v s : F} (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) s) :
    θ (heis₃ u v) * φ₁ x * (θ (heis₃ u v))⁻¹ = φ₁ (conjAutOfNormalizer hNT t x) := by
  have hxQ : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
    rw [hx]
    exact suElt_prev_last_mem_bc2Q0 (hFn := hFn) s
  rw [phi_conj_suElt_inr hc huv t ht x hx,
    hc.onQ0 _ x.2 hxQ _
      ((oddEmb_suElt_prev_last_inr (hFn := hFn) (hr := hr) s).trans hx.symm)]
  rw [show θ (heis₃ u v) * Ψ₀ (suElt (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (Sum.inl (cPrevIdx r hr))
        (Sum.inr (cLastIdx r hr)) s) * (θ (heis₃ u v))⁻¹ =
      ⁅θ (heis₃ u v), Ψ₀ (suElt (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (Sum.inl (cPrevIdx r hr))
        (Sum.inr (cLastIdx r hr)) s)⁆ * Ψ₀ (suElt (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (Sum.inl (cPrevIdx r hr))
        (Sum.inr (cLastIdx r hr)) s) by
    rw [commutatorElement_def]; group,
    ← commutatorElement_inv (Ψ₀ (suElt (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) (Sum.inl (cPrevIdx r hr))
        (Sum.inr (cLastIdx r hr)) s)) (θ (heis₃ u v)), hshort s u v huv]

private theorem map_conj_suHeis_last_suElt_inl
    (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁)
    (hlast_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    {u v s : F} (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) s) :
    θ (heis₃ u v) * φ₁ x * (θ (heis₃ u v))⁻¹ = φ₁ (conjAutOfNormalizer hNT t x) := by
  have hxQ : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
    rw [hx]
    exact suElt_prev_two_mem_bc2Q0 (hFn := hFn) s
  have hcomm : Commute (heisL u v)
      (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) s) :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (suHeis_comm_suElt (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcPrevIdx r hr))
        (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (c := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (bcPrevIdx_ne_bcLastIdx hr) Sum.inl_ne_inr Sum.inl_ne_inr u v s)
  have hconjx : conjAutOfNormalizer hNT t x = x := by
    apply Subtype.ext
    rw [coe_conjAutOfNormalizer, ht, hx]
    exact Commute.mul_inv_cancel hcomm
  rw [hconjx, hc.onQ0 _ x.2 hxQ _
    ((oddEmb_suElt_prev_last_inl (hFn := hFn) (hr := hr) s).trans hx.symm)]
  exact Commute.mul_inv_cancel (hlast_inl u v huv s)

private theorem map_conj_suHeis_last_suLong (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁)
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {u v c : F} (hσc : unitaryInvolution F 2 n c = c)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      suLong (unitaryInvolution F 2 n) (Sum.inl (bcPrevIdx r hr)) c) :
    θ (heis₃ u v) * φ₁ x * (θ (heis₃ u v))⁻¹ = φ₁ (conjAutOfNormalizer hNT t x) := by
  have hxQ : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      bc2Q0 (unitaryInvolution_involutive hFn) hr := by
    rw [hx]
    exact suLong_prev_mem_bc2Q0 (hFn := hFn) c
  have hcomm : Commute (heisL u v)
      (suLong (unitaryInvolution F 2 n) (Sum.inl (bcPrevIdx r hr)) c) :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (suHeis_comm_suLong (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcPrevIdx r hr))
        (c := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) Sum.inl_ne_inr u v c)
  have hconjx : conjAutOfNormalizer hNT t x = x := by
    apply Subtype.ext
    rw [coe_conjAutOfNormalizer, ht, hx]
    exact Commute.mul_inv_cancel hcomm
  rw [hconjx, hc.onQ0 _ x.2 hxQ _
    ((oddEmb_suLong_prev (hr := hr) c).trans hx.symm)]
  exact Commute.mul_inv_cancel ((hd.commute_prev c hσc (heis₃ u v)).1.symm)

private theorem phi_conj_suHeis_prev (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁) {u v u' v' : F}
    (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (hu'v' : v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisP u' v') :
    φ₁ (conjAutOfNormalizer hNT t x) =
      Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
        (unitaryInvolution F 2 n u * u')) * φ₁ x := by
  have hmemB : suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (unitaryInvolution F 2 n u * u') ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr :=
    suElt_prev_two_mem_bc2Qe1 (hFn := hFn) (unitaryInvolution F 2 n u * u')
  have hform := conj_suHeis_suHeis (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcPrevIdx r hr))
    (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) (bcPrevIdx_ne_bcLastIdx hr) huv hu'v'
  have hconjval : (conjAutOfNormalizer hNT t x :
      SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      heisL u v * heisP u' v' * (heisL u v)⁻¹ := by
    rw [coe_conjAutOfNormalizer, ht, hx]
  have hmemT : heisL u v * heisP u' v' * (heisL u v)⁻¹ ∈
      bc2Qe1 (unitaryInvolution_involutive hFn) hr := by
    rw [hform, ← hx]
    exact mul_mem hmemB x.2
  have hR : φ₁ (conjAutOfNormalizer hNT t x) =
      Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
        (unitaryInvolution F 2 n u * u')) * φ₁ x := by
    rw [show conjAutOfNormalizer hNT t x = ⟨heisL u v * heisP u' v' * (heisL u v)⁻¹,
        hmemT⟩ from Subtype.ext hconjval]
    rw [show (⟨heisL u v * heisP u' v' * (heisL u v)⁻¹, hmemT⟩ :
        ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr)) =
        ⟨suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
          (unitaryInvolution F 2 n u * u'), hmemB⟩ * x
      from Subtype.ext (by
        change heisL u v * heisP u' v' * (heisL u v)⁻¹ =
          suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
              (unitaryInvolution F 2 n u * u') *
            (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
        rw [hx]
        exact hform)]
    rw [map_mul, hc.onQ0 _ hmemB (suElt_prev_two_mem_bc2Q0 (hFn := hFn)
      (unitaryInvolution F 2 n u * u'))
      (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
        (unitaryInvolution F 2 n u * u'))
      (oddEmb_suElt_prev_last_inl (hFn := hFn) (hr := hr)
        (unitaryInvolution F 2 n u * u'))]
  exact hR

private theorem map_conj_suHeis_last_suHeis_prev
    (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁)
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ =
          Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n u * u')))
    {u v u' v' : F}
    (huv : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (hu'v' : v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0)
    (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
    (ht : (t : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v)
    (x : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr))
    (hx : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisP u' v') :
    θ (heis₃ u v) * φ₁ x * (θ (heis₃ u v))⁻¹ = φ₁ (conjAutOfNormalizer hNT t x) := by
  have hxP : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
    rw [hx]
    exact suHeis_mem (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.2.2.1 u' v'
  rw [phi_conj_suHeis_prev hc huv hu'v' t ht x hx,
    hc.onHeisP _ x.2 hxP _
      ((su3Emb_suHeis_inl (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr) u' v').trans hx.symm)]
  rw [show θ (heis₃ u v) * oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v') *
        (θ (heis₃ u v))⁻¹ =
      ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ *
        oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v') by
    rw [commutatorElement_def]; group,
    hheis u v u' v' huv hu'v']

private theorem conj_bc2Qe1_heisL (hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁)
    (hφT : ∀ (x : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
      (s : SU (unitaryInvolution F 2 n) 3),
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
          (bcLastIdx r (Nat.one_le_of_lt hr)) s → φT x = θ s)
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s), θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr Ψ₀ θ
              (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
            Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
              (s * unitaryInvolution F 2 n v)))
    (hlast_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ =
          Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n u * u'))) :
    ∀ (t : ↥(X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)))
      (g : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr)),
      φT t * φ₁ g * (φT t)⁻¹ = φ₁ (conjAutOfNormalizer hNT t g) := by
  have hS1 : Subgroup.closure (bc2RootGroups (F := F) (n := n) (hFn := hFn) (hr := hr)) =
      bc2Qe1 (unitaryInvolution_involutive hFn) hr :=
    closure_rootGroups_eq_bc2Qe1 (F := F) (n := n) hFn hr
  intro t g
  refine forall_conj_of_gens hNT φ₁ φT (SN := {x : ↥(bc2Qe1
      (unitaryInvolution_involutive hFn) hr) | (x : SU (unitaryInvolution F 2 n)
        (2 * r + 1)) ∈ bc2RootGroups (F := F) (n := n) (hFn := hFn) (hr := hr)})
    (ST := Set.univ) ?_ Subgroup.closure_univ ?_ t g
  · refine closure_eq_top_of_le_closure (fun x hx => ?_) (le_of_eq hS1.symm)
    exact hS1 ▸ Subgroup.subset_closure hx
  · intro t' _ x hx
    obtain ⟨u, v, huv, hA⟩ := exists_su3Emb_last_of_mem (hFn := hFn) (hr := hr) t'.2
    have ht : (t' : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisL u v :=
      hA.symm.trans (su3Emb_suHeis_inl (unitaryInvolution_involutive hFn)
        (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) u v)
    have hφt : φT t' = θ (heis₃ u v) := hφT t' (heis₃ u v) hA.symm
    rw [hφt]
    rcases hx with ((hx1 | hx2) | hx3) | hx4
    · obtain ⟨s, hxs⟩ := (mem_rootGroup_iff_suElt_odd (unitaryInvolution_involutive hFn)
        (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)))
        (bcPrevIdx_ne_bcLastIdx hr) (toStd_bc2 hr).1
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1))).mp hx1
      exact map_conj_suHeis_last_suElt_inr hc hshort huv t' ht x (s := s) hxs.symm
    · obtain ⟨s, hxs⟩ := (mem_rootGroup_iff_suElt_odd (unitaryInvolution_involutive hFn)
        (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
        (bcPrevIdx_ne_bcLastIdx hr) (toStd_bc2 hr).2.2.2.2.1
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1))).mp hx2
      exact map_conj_suHeis_last_suElt_inl hc hlast_inl huv t' ht x (s := s) hxs.symm
    · obtain ⟨c, hc0, hxs⟩ := (mem_rootGroup_iff_suLong_odd
        (unitaryInvolution_involutive hFn) (Sum.inl (bcPrevIdx r hr))
        (toStd_bc2 hr).2.2.2.2.2 (x : SU (unitaryInvolution F 2 n) (2 * r + 1))).mp hx3
      exact map_conj_suHeis_last_suLong hc hd (add_map_eq_zero_iff.1 hc0) t' ht x
        (c := c) hxs.symm
    · obtain ⟨u', v', hu'v', hA'⟩ := exists_su3Emb_prev_of_mem (hFn := hFn) (hr := hr) hx4
      have hx4' : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) = heisP u' v' := by
        rw [← hA']
        exact su3Emb_suHeis_inl (unitaryInvolution_involutive hFn)
          (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr) u' v'
      exact map_conj_suHeis_last_suHeis_prev hc hheis huv hu'v' t' ht x hx4'

end Gluing

theorem exists_hom_bc2U (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hprev_inr : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
    (hprev_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (oddPrevLift hFn hr Ψ₀ θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    (hlast_inl : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 → ∀ c : F,
        Commute (θ (heis₃ u v))
          (Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) c)))
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ =
          Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n u * u')))
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s), θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr Ψ₀ θ
              (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
            Ψ₀ (suElt (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
              (s * unitaryInvolution F 2 n v))) :
    ∃ φ : ↥(bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
        X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) →* H,
      (∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
          (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
            X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
          x ∈ bc2Q0 (unitaryInvolution_involutive hFn) hr →
            ∀ y : SU (unitaryInvolution F 2 n) (2 * r),
              oddEmb (unitaryInvolution F 2 n) r y = x → φ ⟨x, hx⟩ = Ψ₀ y) ∧
      (∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
          (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
            X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
          x ∈ X (Pi.single (bcPrevIdx r hr) 1 +
              Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
            ∀ A : SU (unitaryInvolution F 2 n) 3,
              su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
                  (bcPrevIdx r hr) A = x →
                φ ⟨x, hx⟩ = oddPrevLift hFn hr Ψ₀ θ A) ∧
      ∀ (x : SU (unitaryInvolution F 2 n) (2 * r + 1))
          (hx : x ∈ bc2Qe1 (unitaryInvolution_involutive hFn) hr ⊔
            X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)),
          x ∈ X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) →
            ∀ A : SU (unitaryInvolution F 2 n) 3,
              su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
                  (bcLastIdx r (Nat.one_le_of_lt hr)) A = x → φ ⟨x, hx⟩ = θ A := by
  obtain ⟨φ₁, hφ₁N, hφ₁P⟩ := hd.exists_hom_bc2Qe1 hprev_inr hprev_inl
  obtain ⟨φT, hφT⟩ := exists_hom_of_le_range
    (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)))
    (su3Emb_injective (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))) θ
    (X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1))
    (rootGroup_le_range_su3Emb (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (a := Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
      (toStd_bc2 hr).2.1)
  have hNT := heisL_le_normalizer (unitaryInvolution_involutive hFn) hr
  have hc : BC2Qe1Clauses hFn hr Ψ₀ θ φ₁ := ⟨hφ₁N, hφ₁P⟩
  obtain ⟨φ, hφN', hφT'⟩ := exists_hom_sup_of_normalizes hNT φ₁ φT
    (agree_bc2Qe1_heisL (hFn := hFn))
    (conj_bc2Qe1_heisL (hFn := hFn) hc hφT hd hshort hlast_inl hheis)
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x hx hx0 y hy
    exact (hφN' ⟨x, Subgroup.mem_sup_left hx0⟩).trans
      (hφ₁N x (Subgroup.mem_sup_left hx0) hx0 y hy)
  · intro x hx hxP A hA
    exact (hφN' ⟨x, Subgroup.mem_sup_right hxP⟩).trans
      (hφ₁P x (Subgroup.mem_sup_right hxP) hxP A hA)
  · intro x hx hxL A hA
    exact (hφT' ⟨x, hxL⟩).trans (hφT ⟨x, hxL⟩ A hA.symm)

end OddFrameCompatible

end

end CFSG.Timmesfeld.Transvection
