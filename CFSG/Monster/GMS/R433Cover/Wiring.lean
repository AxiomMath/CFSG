module

public import CFSG.Monster.GMS.R433Cover.Lift
public import CFSG.Monster.GMS.R433Cover.Y432Transport
public import CFSG.Monster.GMS.Facts.Section4
public import CFSG.Monster.Schur.CentralEps

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Monster.GMS
open CFSG.Blueprint.NativeSporadic (B)
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (R433 yGen spiderWord)

theorem equiv_R433_of_isTwoBabyCentralizer {G : Type} [Group G] {a : G}
    (h : IsTwoBabyCentralizer a) {ρ : R433 →* B} (hρ : Function.Surjective ρ) [Finite R433]
    (hcard : Nat.card R433 ≤ 2 * Nat.card B) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < 11)
    (hY : ConjIdentity (marked ρ) Y) (h1 : SpiderIdentity (marked ρ)) :
    Nonempty (Subgroup.centralizer ({a} : Set G) ≃* R433) := by
  obtain ⟨ha2, hperf, φ, hφ, hker⟩ := h
  have hk2 : Nat.card φ.ker = 2 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hker, Nat.card_zpowers,
      ha2]
  obtain ⟨z, hzK, -, hzall⟩ := CFSG.Monster.Schur.exists_ker_elem φ hk2
  have hzc : ∀ x, x * z = z * x := fun x =>
    Subgroup.mem_center_iff.mp (CFSG.Monster.Schur.mem_center_of_mem_ker φ hk2 hzK) x
  have hz2 : z * z = 1 := by
    rw [← sq]; exact CFSG.Monster.Schur.sq_eq_one_of_mem_ker φ hk2 hzK
  have hcardE : Nat.card R433 ≤ Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    rw [CFSG.Monster.Schur.card_eq_mul_card_ker φ hφ, hk2, mul_comm]
    exact hcard
  exact nonempty_mulEquiv_of_cover ⟨hzc, hz2, by simpa using hzK, hzall⟩ hφ hρ hYlt hY h1 hperf
    hcardE

theorem twoBabyUnique_of_surjection (ρ : R433 →* B) (hρ : Function.Surjective ρ) [Finite R433]
    (hcard : Nat.card R433 ≤ 2 * Nat.card B) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < 11)
    (hY : ConjIdentity (marked ρ) Y) (h1 : SpiderIdentity (marked ρ)) : TwoBabyUnique := by
  intro G G' _ _ _ _ a a' ha ha'
  exact ⟨(equiv_R433_of_isTwoBabyCentralizer ha hρ hcard hYlt hY h1).some.trans
    (equiv_R433_of_isTwoBabyCentralizer ha' hρ hcard hYlt hY h1).some.symm⟩

theorem twoBabyUnique_of_native (ρ : R433 →* B) (hρ : Function.Surjective ρ) [Finite R433]
    (hcard : Nat.card R433 ≤ 2 * Nat.card B) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < 10)
    (hid2 : evalWord (yGen 4 3 2) (Y.reverse ++ [0, 4, 6] ++ Y) =
      evalWord (yGen 4 3 2) ([2, 5, 7, 9] ++ f213Word))
    (hid1 : evalWord (yGen 4 3 2)
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten = 1) :
    TwoBabyUnique := by
  obtain ⟨hY, h1⟩ := identities_of_Y432 ρ Y hYlt hid2 hid1
  exact twoBabyUnique_of_surjection ρ hρ hcard (fun c hc => Nat.lt_succ_of_lt (hYlt c hc)) hY h1

end CFSG.Monster.GMS.R433Cover
