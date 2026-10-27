module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public noncomputable section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

@[expose] def IsRegularUnipotent
    (u : ModGL τ K) : Prop :=
  u ∈ posUnipotent τ K ∧ ∀ i : Fin τ.rank, ∃ c : K, c ≠ 0 ∧ HasCoord i u c

theorem HasCoord.conj_torus_char
    {i : Fin τ.rank} {y : ModGL τ K}
    {c : K} (h : HasCoord i y c)
    {t : ModGL τ K} (ht : t ∈ torusGroup τ K) {l : Fin τ.rank → Kˣ}
    (hl : ∀ α, IsRoot τ α → ∀ c : K, t * pinnedX τ K α c * t⁻¹ =
      pinnedX τ K α (((∏ j, l j ^ α j : Kˣ) : K) * c)) :
    HasCoord i (t * y * t⁻¹) ((l i : K) * c) := by
  obtain ⟨b, hb, rfl⟩ := h
  have hs : ((∏ j, l j ^ (Pi.single i 1 : Fin τ.rank → ℤ) j : Kˣ) : K) = (l i : K) := by
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  refine ⟨t * b * t⁻¹, torus_conj_mem_rootSpan ht (fun α hα => hα.1) hb, ?_⟩
  have h1 := hl (Pi.single i 1) (isRoot_single τ i) c
  simp only [pinnedX_single] at h1
  rw [hs] at h1
  calc t * (xUnit τ K i c * b) * t⁻¹ = (t * xUnit τ K i c * t⁻¹) * (t * b * t⁻¹) := by group
    _ = xUnit τ K i ((l i : K) * c) * (t * b * t⁻¹) := by rw [h1]

theorem mem_borelGroup_of_conj_regular
    {u g : ModGL τ K} (hu : IsRegularUnipotent u)
    (hg : g ∈ adjointGroup τ K) (h : g⁻¹ * u * g ∈ posUnipotent τ K) :
    g ∈ borelGroup τ K := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb hb'
  · exfalso
    obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w⁻¹ (inv_ne_one.2 hw1)
    set n := canonicalRep (coxeterSystem τ) K w with hn
    obtain ⟨c, hc, hcoord⟩ := hu.2 i
    have hyU : b⁻¹ * u * b ∈ posUnipotent τ K := by
      simpa using conj_mem_posUnipotent_of_mem_borel (inv_mem hb) hu.1
    have hb2 : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
      rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u0, hu0, t, ht, rfl⟩ := hb2
    have hcoord1 : HasCoord i (u0⁻¹ * u * u0) c := hcoord.conj_posUnipotent hu0
    obtain ⟨s, hs, hcoord2⟩ := hcoord1.conj_torus (inv_mem ht)
    have hy : (u0 * t)⁻¹ * u * (u0 * t) = t⁻¹ * (u0⁻¹ * u * u0) * t⁻¹⁻¹ := by group
    have hconj : n⁻¹ * ((u0 * t)⁻¹ * u * (u0 * t)) * n ∈ posUnipotent τ K := by
      have h1 := conj_mem_posUnipotent_of_mem_borel hb' h
      have h2 : b' * ((u0 * t * n * b')⁻¹ * u * (u0 * t * n * b')) * b'⁻¹ =
          n⁻¹ * ((u0 * t)⁻¹ * u * (u0 * t)) * n := by group
      rwa [h2] at h1
    have hyU' : t⁻¹ * (u0⁻¹ * u * u0) * t⁻¹⁻¹ ∈ posUnipotent τ K := by
      rw [← hy]
      exact hyU
    rw [hy] at hconj
    have hpos := pos_of_coord_of_conj_mem (mul_ne_zero hs hc) hcoord2 hyU' hconj
    have := hneg
    omega

theorem torus_eq_one_of_conj_regular
    {u v t : ModGL τ K} [Finite K] (hu : IsRegularUnipotent u)
    (hv : v ∈ posUnipotent τ K) (ht : t ∈ torusGroup τ K) (h : t * u * t⁻¹ = v⁻¹ * u * v) :
    t = 1 := by
  obtain ⟨l, hl⟩ := exists_torus_characters ht
  have hl' : ∀ α, IsRoot τ α → ∀ c : K, t * pinnedX τ K α c * t⁻¹ =
      pinnedX τ K α (((∏ j, l j ^ α j : Kˣ) : K) * c) := fun α hα => (hl α hα).2
  have hone : ∀ i, l i = 1 := by
    intro i
    obtain ⟨c, hc, hcoord⟩ := hu.2 i
    have h1 := hcoord.conj_torus_char ht hl'
    have h2 : HasCoord i (v⁻¹ * u * v) c := hcoord.conj_posUnipotent hv
    rw [h] at h1
    have h3 := HasCoord.unique h1 h2
    apply Units.ext
    have : (l i : K) * c = 1 * c := by rw [h3, one_mul]
    simpa using mul_right_cancel₀ hc this
  have hprod : ∀ α : Fin τ.rank → ℤ, (∏ j, l j ^ α j : Kˣ) = 1 := fun α => by
    simp [hone]
  have htA : t ∈ adjointGroup τ K := borelGroup_le_adjointGroup' (Subgroup.mem_sup_left ht)
  have hcent : adjointGroup τ K ≤ Subgroup.centralizer ({t} : Set (ModGL τ K)) := by
    rw [adjointGroup_eq_rootSpan]
    refine iSup₂_le fun α hα g hg => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hl' α hα c
    rw [hprod α, Units.val_one, one_mul] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hz : (⟨t, htA⟩ : adjointGroup τ K) ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hcent g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact Subtype.ext this
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem mem_posUnipotent_of_commute_regular
    [Finite K] {u g : ModGL τ K}
    (hu : IsRegularUnipotent u) (hg : g ∈ adjointGroup τ K) (hcomm : g * u = u * g) :
    g ∈ posUnipotent τ K := by
  have hcomm' : g⁻¹ * u * g = u := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hB := mem_borelGroup_of_conj_regular hu hg (by rw [hcomm']; exact hu.1)
  have hb2 : g ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
    exact hB
  obtain ⟨v, hv, t, ht, rfl⟩ := hb2
  have h1 : t * u * t⁻¹ = v⁻¹ * u * v := by
    have : v * t * u = u * (v * t) := hcomm
    calc t * u * t⁻¹ = v⁻¹ * (v * t * u) * t⁻¹ := by group
      _ = v⁻¹ * (u * (v * t)) * t⁻¹ := by rw [this]
      _ = v⁻¹ * u * v := by group
  have ht1 := torus_eq_one_of_conj_regular hu hv ht h1
  subst ht1
  simpa using hv

theorem eq_bot_of_commute_regular
    [Finite K] {r s : ℕ} [Fact r.Prime] [CharP K r] (hs : s.Prime)
    (hsr : s ≠ r) {u : ModGL τ K} (hu : IsRegularUnipotent u) {V : Subgroup (ModGL τ K)}
    (hVA : V ≤ adjointGroup τ K) (hVexp : ∀ v ∈ V, v ^ s = 1)
    (hVc : ∀ v ∈ V, v * u = u * v) : V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hvU := mem_posUnipotent_of_commute_regular hu (hVA hv) (hVc v hv)
  have hU : IsPGroup r (posUnipotent τ K) := isPGroup_posUnipotent r
  have hrs : Nat.Coprime s r := (Nat.coprime_primes hs (Fact.out)).2 hsr
  obtain ⟨k, hk⟩ := hU ⟨v, hvU⟩
  have h1 : v ^ (r ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : Nat.Coprime s (r ^ k) := Nat.Coprime.pow_right _ hrs
  have h3 := (pow_gcd_eq_one (a := v)).mpr ⟨hVexp v hv, h1⟩
  rwa [Nat.Coprime.gcd_eq_one h2, pow_one] at h3

end CFSG.SignalizerFunctorTheorem.NonLocalExc
