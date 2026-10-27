module

public import CFSG.Quasithin.Background.D14Groups
public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.D14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G] {H U : Subgroup G}

theorem le_normalizer_of_isNormalIn {N : Subgroup G} (h : IsNormalIn H U N) :
    H ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
  B6.mem_normalizer_of_forall_mem (fun x hx => h.2 g hg x hx)
    (fun x hx => by simpa using h.2 g⁻¹ (H.inv_mem hg) x hx)

theorem le_normalizer_bot (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp [Subgroup.mem_bot]

theorem exists_pow_mem_of_isPGroup (hU : IsPGroup 2 U) {N L : Subgroup G} (hNU : N ≤ U) :
    ∀ d ∈ N, ∃ j : ℕ, d ^ 2 ^ j ∈ L := by
  intro d hd
  obtain ⟨j, hj⟩ := hU ⟨d, hNU hd⟩
  refine ⟨j, ?_⟩
  have hj' : d ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  rw [hj']
  exact L.one_mem

theorem commutator_le_of_isCentralStep {L N : Subgroup G} (h : IsCentralStep H L N) :
    ⁅oTwoUpper H, N⁆ ≤ L :=
  Subgroup.commutator_le.mpr fun p hp x hx => h p (oTwoUpper_le H hp) x hx

theorem commutator_eq_bot_of_zero (hU : IsPGroup 2 U) {N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : n = 0) : ⁅N, oTwoUpper H⁆ = ⊥ := by
  revert hn
  induction h with
  | bot => exact fun _ => Subgroup.commutator_bot_left _
  | @central N L n hstep hcent _ ih =>
    intro hn
    have hL := ih hn
    have key := A4.commutator_le_of_oTwoUpper (A := oTwoUpper H) (N := ⊥) (B := L) (D := N)
      (le_normalizer_bot _) (le_normalizer_bot _) hstep.2.2.1.le
      (exists_pow_mem_of_isPGroup hU hstep.1.1) (commutator_le_of_isCentralStep hcent)
      (by rw [Subgroup.commutator_comm, hL])
    rw [oTwoUpper_oTwoUpper, Subgroup.commutator_comm] at key
    exact le_bot_iff.mp key
  | noncentral _ _ _ _ => exact fun hn => absurd hn (Nat.succ_ne_zero _)

theorem exists_chiefStep_of_one (hU : IsPGroup 2 U) (hUH : U ≤ H) {N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : n = 1) :
    ∃ K L : Subgroup G, IsChiefStep H U L K ∧ ⁅L, oTwoUpper H⁆ = ⊥ ∧ ⁅N, oTwoUpper H⁆ ≤ K := by
  revert hn
  induction h with
  | bot => exact fun hn => absurd hn (by decide)
  | @central N L n hstep hcent _ ih =>
    intro hn
    obtain ⟨K, L', hKL, hL', hLK⟩ := ih hn
    refine ⟨K, L', hKL, hL', ?_⟩
    have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_isNormalIn hKL.1
    have key := A4.commutator_le_of_oTwoUpper (A := oTwoUpper H) (N := K) (B := L) (D := N)
      ((oTwoUpper_le H).trans hHK) ((hstep.1.1.trans hUH).trans hHK) hstep.2.2.1.le
      (exists_pow_mem_of_isPGroup hU hstep.1.1) (commutator_le_of_isCentralStep hcent)
      (by rw [Subgroup.commutator_comm]; exact hLK)
    rw [oTwoUpper_oTwoUpper, Subgroup.commutator_comm] at key
    exact key
  | @noncentral N L n hstep _ hser _ =>
    intro hn
    refine ⟨N, L, hstep, commutator_eq_bot_of_zero hU hser (Nat.succ.inj hn), ?_⟩
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((oTwoUpper_le H).trans (le_normalizer_of_isNormalIn hstep.1))

theorem commutator_le_of_ne_bot (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hchief : IsChiefSeriesFrom H U U 1)
    {Z : Subgroup G} (hZU : Z ≤ U) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hZ : ⁅Z, oTwoUpper H⁆ ≠ ⊥) : ⁅U, oTwoUpper H⁆ ≤ Z := by
  set P := oTwoUpper H with hP
  obtain ⟨K, L, hstep, hLP, hUK⟩ := exists_chiefStep_of_one hU hUH hchief rfl
  set X := ⁅Z, P⁆ with hX
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := le_normalizer_oTwoUpper H
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := le_normalizer_commutator hHZ hHP
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isNormalIn hstep.2.1
  have hXZ : X ≤ Z :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((oTwoUpper_le H).trans hHZ)
  have hXU : X ≤ U := hXZ.trans hZU
  have hXK : X ≤ K := (Subgroup.commutator_mono hZU le_rfl).trans hUK
  have hXX : X ≤ ⁅X, P⁆ := commutator_le_commutator_commutator (hU.to_le hZU) (hZU.trans hUH) hHZ
  have hXL : ¬ X ≤ L := by
    intro hle
    apply hZ
    rw [eq_bot_iff]
    calc X ≤ ⁅X, P⁆ := hXX
      _ ≤ ⁅L, P⁆ := Subgroup.commutator_mono hle le_rfl
      _ = ⊥ := hLP
  have hnorm : IsNormalIn H U (X ⊔ L) := ⟨sup_le hXU hstep.2.1.1, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_sup hHX hHL hg) x).mp hx⟩
  have hsup : X ⊔ L = K :=
    (hstep.2.2.2 (X ⊔ L) hnorm le_sup_right (sup_le hXK hstep.2.2.1.le)).resolve_left
      fun h => hXL (h ▸ le_sup_left)
  have hKP : ⁅K, P⁆ ≤ X := by
    rw [← hsup]
    exact commutator_sup_le_of ((hXU.trans hUH).trans hHL) Subgroup.le_normalizer
      (by rw [hLP]; exact bot_le)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp ((oTwoUpper_le H).trans hHX))
  calc ⁅U, P⁆ ≤ ⁅⁅U, P⁆, P⁆ := commutator_le_commutator_commutator hU hUH hHU
    _ ≤ ⁅K, P⁆ := Subgroup.commutator_mono hUK le_rfl
    _ ≤ X := hKP
    _ ≤ Z := hXZ

end CFSG.Quasithin.D14
