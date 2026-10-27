module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec4

namespace Item228Census4Proof

theorem map_eq_top_of_commutator_mem {M Q : Type*} [Group M] [Group Q] [IsSimpleGroup Q]
    {C : Subgroup M} (hder : ∀ a b : M, a * b * a⁻¹ * b⁻¹ ∈ C) (ψ : M →* Q)
    (hψ : Function.Surjective ψ) (hQ : ∃ a b : Q, a * b ≠ b * a) : C.map ψ = ⊤ := by
  obtain ⟨a, b, hab⟩ := hQ
  have hnorm : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    have h2 : g * c * g⁻¹ = g * c * g⁻¹ * c⁻¹ * c := by group
    rw [h2]
    exact C.mul_mem (hder g c) hc
  have hn : (C.map ψ).Normal := hnorm.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map ψ) with h | h
  · exfalso
    apply hab
    obtain ⟨g, rfl⟩ := hψ a
    obtain ⟨k, rfl⟩ := hψ b
    have h1 : ψ (g * k * g⁻¹ * k⁻¹) = 1 := by
      have := Subgroup.mem_map_of_mem ψ (hder g k)
      rwa [h, Subgroup.mem_bot] at this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ψ g * ψ k = ψ g * ψ k * (ψ g)⁻¹ * (ψ k)⁻¹ * (ψ k * ψ g) := by group
      _ = ψ k * ψ g := by rw [h1, one_mul]
  · exact h

theorem false_of_commutator_mem {Γ Q : Type*} [Group Γ] [Group Q] [IsSimpleGroup Q]
    {M C : Subgroup Γ} (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hder : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ C) (ψ : M →* Q)
    (hψ : Function.Surjective ψ) (hQ : ∃ a b : Q, a * b ≠ b * a) : False := by
  have htop := map_eq_top_of_commutator_mem (C := C.subgroupOf M)
    (fun a b => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hder a a.2 b b.2) ψ hψ hQ
  obtain ⟨a, b, hab⟩ := hQ
  apply hab
  obtain ⟨c₁, hc₁, rfl⟩ : a ∈ (C.subgroupOf M).map ψ := by rw [htop]; exact Subgroup.mem_top a
  obtain ⟨c₂, hc₂, rfl⟩ : b ∈ (C.subgroupOf M).map ψ := by rw [htop]; exact Subgroup.mem_top b
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hc₁ hc₂
  simpa using hC _ hc₁ _ hc₂

theorem commutator_mul_comm_of_mem_center {G : Type*} [Group G] {a b y : G}
    (ha : a * y * a⁻¹ * y⁻¹ ∈ Subgroup.center G) (hb : b * y * b⁻¹ * y⁻¹ ∈ Subgroup.center G) :
    a * b * a⁻¹ * b⁻¹ * y = y * (a * b * a⁻¹ * b⁻¹) := by
  have hc : ∀ z ∈ Subgroup.center G, ∀ g : G, g * z * g⁻¹ = z := fun z hz g => by
    rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  have hcomm : ∀ z ∈ Subgroup.center G, ∀ g : G, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp hz g
  set z₁ := a * y * a⁻¹ * y⁻¹ with hz₁
  set z₂ := b * y * b⁻¹ * y⁻¹ with hz₂
  have hz₁' := (Subgroup.center G).inv_mem ha
  have hz₂' := (Subgroup.center G).inv_mem hb
  have key : a * b * a⁻¹ * b⁻¹ * y * (a * b * a⁻¹ * b⁻¹)⁻¹ * y⁻¹ =
      (a * b * a⁻¹) * (b⁻¹ * z₂⁻¹ * b⁻¹⁻¹) * (a * b * a⁻¹)⁻¹ *
        ((a * b) * (a⁻¹ * z₁⁻¹ * a⁻¹⁻¹) * (a * b)⁻¹) * (a * z₂ * a⁻¹) * z₁ := by
    rw [hz₁, hz₂]
    group
  rw [hc _ hz₂' b⁻¹, hc _ hz₂' _, hc _ hz₁' a⁻¹, hc _ hz₁' _, hc _ hb a] at key
  have h1 : a * b * a⁻¹ * b⁻¹ * y * (a * b * a⁻¹ * b⁻¹)⁻¹ * y⁻¹ = 1 := by
    rw [key, mul_assoc z₂⁻¹, ← hcomm _ hz₁' z₂]
    group
  rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

variable {K : Type} [Field K]

theorem eq_neg_one_of_sq_eq_one_gl2 (h2 : (2 : K) ≠ 0) {A : GL (Fin 2) K} (hA : A ^ 2 = 1)
    (hA1 : A ≠ 1) (hdA : GeneralLinearGroup.det A = 1) :
    (A : Matrix (Fin 2) (Fin 2) K) = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hdA, Units.val_one]
  rw [Matrix.det_fin_two] at hdet
  have hsq : ∀ i j, ((A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)) i j =
      (1 : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    have := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) i j) hA
    simpa [sq] using this
  have e00 := hsq 0 0
  have e01 := hsq 0 1
  have e10 := hsq 1 0
  have e11 := hsq 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1
  have htr : a + d ≠ 0 := by
    intro htr
    apply h2
    linear_combination -e00 - hdet + a * htr
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hb, hc] at hdet e00 e11
  have hda : d = a := by
    have h1 : a * (a - d) = 0 := by linear_combination e00 - hdet
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h] at hdet
      simp at hdet
    · linear_combination -h
  have ha : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases ha with ha | ha
  · exfalso
    apply hA1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ha, hb, hc, hda] at *
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ha, hb, hc, hda] at *

theorem eq_of_sq_eq_one_gl2 (h2 : (2 : K) ≠ 0) {A B : GL (Fin 2) K} (hA : A ^ 2 = 1)
    (hB : B ^ 2 = 1) (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hdA : GeneralLinearGroup.det A = 1)
    (hdB : GeneralLinearGroup.det B = 1) : A = B :=
  Units.ext ((eq_neg_one_of_sq_eq_one_gl2 h2 hA hA1 hdA).trans
    (eq_neg_one_of_sq_eq_one_gl2 h2 hB hB1 hdB).symm)

variable {p f : ℕ} {π : Bool}

theorem pow_three_eq_one_of_mem_slPi
    (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K) (hz : g ∈ StatedScalars (Fin 3) K) :
    g ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have hdet := ((mem_slPi_iff hπ).mp hg).2
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hdet
  have hc : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  rw [← map_pow, hc, map_one]

theorem centMod_mul_scalar {n : ℕ} (L : Subgroup (GL (Fin n) K)) (x : GL (Fin n) K)
    {z : GL (Fin n) K} (hz : z ∈ StatedScalars (Fin n) K) : centMod L (x * z) = centMod L x := by
  have h : (QuotientGroup.mk (x * z) : GL (Fin n) K ⧸ StatedScalars (Fin n) K) =
      QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  rw [centMod, centMod, h]

theorem centralizer_mul_scalar {n : ℕ} (x : GL (Fin n) K) {z : GL (Fin n) K}
    (hz : z ∈ StatedScalars (Fin n) K) :
    Subgroup.centralizer {x * z} = Subgroup.centralizer {x} := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hzc : ∀ h : GL (Fin n) K, h * z = z * h := commute_of_mem_statedScalars hz
  constructor
  · intro h
    have : g * x * z = x * g * z := by
      rw [mul_assoc, h, mul_assoc, ← hzc g, mul_assoc]
    exact mul_right_cancel this
  · intro h
    rw [← mul_assoc, h, mul_assoc, hzc g, mul_assoc]

theorem commutator_mem_of_mem_centMod {n : ℕ} {L : Subgroup (GL (Fin n) K)} {y a b : GL (Fin n) K}
    (ha : a ∈ centMod L y) (hb : b ∈ centMod L y) :
    a * b * a⁻¹ * b⁻¹ ∈ L ⊓ Subgroup.centralizer {y} := by
  obtain ⟨haL, za, hza, hay⟩ := mem_centMod_iff_scalar.mp ha
  obtain ⟨hbL, zb, hzb, hby⟩ := mem_centMod_iff_scalar.mp hb
  have hZ : StatedScalars (Fin n) K = Subgroup.center (GL (Fin n) K) := by
    rw [StatedScalars, GeneralLinearGroup.center_eq_range_scalar]
  have ha' : a * y * a⁻¹ * y⁻¹ ∈ Subgroup.center (GL (Fin n) K) := by
    rw [hay, mul_inv_cancel_right, ← hZ]
    exact hza
  have hb' : b * y * b⁻¹ * y⁻¹ ∈ Subgroup.center (GL (Fin n) K) := by
    rw [hby, mul_inv_cancel_right, ← hZ]
    exact hzb
  refine Subgroup.mem_inf.mpr
    ⟨L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commutator_mul_comm_of_mem_center ha' hb'

theorem false_of_le_centMod_odd (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h2 : (2 : K) ≠ 0) {x : GL (Fin 3) K}
    (hxH : x ∈ glPi π 3 (p ^ f) K) (hxZ : x ∉ zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) {M : Subgroup (GL (Fin 3) K)}
    (hM : M ≤ centMod (slPi π 3 (p ^ f) K) x) {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (ψ : M →* Q) (hψ : Function.Surjective ψ)
    (hker : ∀ g : M, ψ g = 1 → (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    (hQ : ∃ a b : Q, a * b ≠ b * a)
    (hinv : ∃ t₁ t₂ : Q, t₁ ^ 2 = 1 ∧ t₂ ^ 2 = 1 ∧ t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₁ ≠ t₂) : False := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by
    subst h
    exact hq
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := rank3II_4_10_one hK hq hτ hτ1 hxH hxZ hx3
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact hz.2
  rw [← centMod_mul_scalar _ x hzS] at hM
  set L := slPi π 3 (p ^ f) K with hL
  set C := L ⊓ Subgroup.centralizer {x * z} with hC
  have hder : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ C := fun a ha b hb =>
    commutator_mem_of_mem_centMod (hM ha) (hM hb)
  rcases hcase with ⟨-, ⟨φ⟩, -⟩ | ⟨-, ⟨φ⟩, hcent⟩ | ⟨-, -, -, hcyc, -⟩
  ·
    refine false_of_commutator_mem (C := C) (fun a ha b hb => ?_) hder ψ hψ hQ
    have h := φ.injective (show φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  ·
    rw [hcent] at hM
    let χ : M →* Kˣ := GeneralLinearGroup.det.comp ((glPi π 2 (p ^ f) K).subtype.comp
      (φ.toMonoidHom.comp (Subgroup.inclusion hM)))
    have htop : χ.ker.map ψ = ⊤ := map_eq_top_of_commutator_mem (fun a b => by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (χ a),
        mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]) ψ hψ hQ
    obtain ⟨t₁, t₂, ht₁, ht₂, ht₁1, ht₂1, h12⟩ := hinv
    have hlift : ∀ t : Q, t ^ 2 = 1 → t ≠ 1 → ∃ u ∈ χ.ker, ψ u = t ∧ u ^ 2 = 1 ∧ u ≠ 1 := by
      intro t ht ht1
      obtain ⟨s, hs, rfl⟩ : t ∈ χ.ker.map ψ := by rw [htop]; exact Subgroup.mem_top t
      have hs2 : ψ (s ^ 2) = 1 := by rw [map_pow, ht]
      have hs6 : s ^ 6 = 1 := by
        have hZs := hker (s ^ 2) hs2
        have hLs : ((s ^ 2 : M) : GL (Fin 3) K) ∈ L := (hM (s ^ 2).2).1
        have h3 := pow_three_eq_one_of_mem_slPi hπ hLs hZs
        rw [show s ^ 6 = (s ^ 2) ^ 3 by rw [← pow_mul]]
        apply Subtype.ext
        rw [Subgroup.coe_pow, h3, Subgroup.coe_one]
      refine ⟨s ^ 3, χ.ker.pow_mem hs 3, ?_, ?_, ?_⟩
      · rw [map_pow, show (ψ s) ^ 3 = ψ s ^ 2 * ψ s by group, ht, one_mul]
      · rw [← pow_mul]
        exact hs6
      · intro h1
        apply ht1
        rw [show ψ s = ψ s ^ 3 by rw [show (ψ s) ^ 3 = ψ s ^ 2 * ψ s by group, ht, one_mul],
          ← map_pow, h1, map_one]
    obtain ⟨u₁, hu₁, hψ₁, hu₁2, hu₁1⟩ := hlift t₁ ht₁ ht₁1
    obtain ⟨u₂, hu₂, hψ₂, hu₂2, hu₂1⟩ := hlift t₂ ht₂ ht₂1
    set ι : M →* GL (Fin 2) K := (glPi π 2 (p ^ f) K).subtype.comp
      (φ.toMonoidHom.comp (Subgroup.inclusion hM)) with hι
    have hιi : Function.Injective ι :=
      (Subgroup.subtype_injective _).comp (φ.injective.comp (Subgroup.inclusion_injective hM))
    have hι2 : ∀ u : M, u ^ 2 = 1 → ι u ^ 2 = 1 := fun u hu => by rw [← map_pow, hu, map_one]
    have hι1 : ∀ u : M, u ≠ 1 → ι u ≠ 1 := fun u hu h => hu (hιi (h.trans (map_one ι).symm))
    have heq := eq_of_sq_eq_one_gl2 h2 (hι2 u₁ hu₁2) (hι2 u₂ hu₂2) (hι1 u₁ hu₁1) (hι1 u₂ hu₂1)
      hu₁ hu₂
    exact h12 (hψ₁.symm.trans ((congrArg ψ (hιi heq)).trans hψ₂))
  ·
    refine false_of_commutator_mem (C := C) (fun a ha b hb => ?_) hder ψ hψ hQ
    have h := (@IsCyclic.commGroup C _ hcyc).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h

open CFSG.LocalAnalysis.ComponentInitial in
theorem isSimpleGroup_SL_two_of_charTwo [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)).2.1
  have hP : IsSimpleGroup (LinearFlag.projectiveSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 2 K)).isSimpleGroup
  exact (LinearCover.projectiveSLTwoEquivSL K).symm.isSimpleGroup

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have mono : ∀ {s t : ℕ}, 1 ≤ s → s < t → s * (s ^ 2 - 1) < t * (t ^ 2 - 1) := by
    intro s t hs hst
    have h1 : s ^ 2 < t ^ 2 := Nat.pow_lt_pow_left hst (by norm_num)
    have h2 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rcases Nat.eq_or_lt_of_le h2 with h3 | h3
    · rw [← h3, Nat.sub_self, mul_zero]
      apply Nat.mul_pos (by omega)
      omega
    · exact Nat.mul_lt_mul'' hst (by omega)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (mono ha hab))
  · exact hab
  · exact absurd h.symm (ne_of_lt (mono hb hab))

theorem eq_four_of_dvd_62400 {q : ℕ} (hq0 : 0 < q) (hev : q % 2 = 0) (h3 : q % 3 = 1)
    (h : q * (q ^ 2 - 1) ∣ 62400) : q = 4 := by
  have hle : q ≤ 39 := by
    by_contra hlt
    push Not at hlt
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 : 40 * (40 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    norm_num at h2
    omega
  interval_cases q <;> first | rfl | (exfalso; revert h; decide) | omega

theorem eq_two_of_dvd_62400 {m : ℕ} (hm : 0 < m) (he : Even m)
    (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ 62400) : m = 2 := by
  have h2 : 2 ^ m ∣ 62400 := (Dvd.intro _ rfl).trans h
  have hle : m ≤ 15 := by
    by_contra hlt
    push Not at hlt
    have h1 := Nat.le_of_dvd (by norm_num) h2
    have : 2 ^ 16 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  obtain ⟨r, rfl⟩ := he
  have hr : r ≤ 7 := by omega
  interval_cases r <;> first | rfl | (exfalso; revert h; decide)

theorem card_eq_two_pow_of_le_centralizer_even (hK : PiField true p f K)
    (hq : ModThree true (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) [CharP K 2]
    {x : GL (Fin 3) K} (hxZ : x ∉ StatedScalars (Fin 3) K)
    (hx3 : x ^ 3 ∈ StatedScalars (Fin 3) K) {N Kb : Subgroup (GL (Fin 3) K)} {m : ℕ}
    (hNC : N ≤ slPi true 3 (p ^ f) K ⊓ Subgroup.centralizer {x})
    (hnorm : ∀ g ∈ slPi true 3 (p ^ f) K ⊓ Subgroup.centralizer {x}, ∀ k ∈ N, g * k * g⁻¹ ∈ N)
    (hKbN : Kb ≤ N) [IsSimpleGroup Kb] (hKbnc : ∃ a b : Kb, a * b ≠ b * a)
    (hcard : Nat.card Kb = 2 ^ m * ((2 ^ m) ^ 2 - 1)) (hm : 0 < m) (he : Even m)
    (hU : Kb = N ∨ Nat.card N = 62400) : Nat.card K = 2 ^ m := by
  have := hK.finite
  have hπ : true = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  have hZ := zPi_eq hπ hq' hτ hτ1
  have hxH : x ∈ glPi true 3 (p ^ f) K := mem_glPi_true _ x
  have hxZ' : x ∉ zPi true 3 (p ^ f) K := by
    rw [hZ]
    exact fun h => hxZ h.2
  have hx3' : x ^ 3 ∈ zPi true 3 (p ^ f) K := by
    rw [hZ]
    exact ⟨mem_glPi_true _ _, hx3⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := rank3II_4_10_one hK hq hτ hτ1 hxH hxZ' hx3'
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    rw [hZ] at hz
    exact hz.2
  rw [← centralizer_mul_scalar x hzS] at hNC hnorm
  set L := slPi true 3 (p ^ f) K with hL
  set C := L ⊓ Subgroup.centralizer {x * z} with hC
  have hKbC : Kb ≤ C := hKbN.trans hNC
  have hnc : ¬ ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro h
    obtain ⟨a, b, hab⟩ := hKbnc
    exact hab (Subtype.ext (h _ (hKbC a.2) _ (hKbC b.2)))
  have hqK : Nat.card K = p ^ f := hK.card
  have hq3 : p ^ f % 3 = 1 := hq
  have hev : Nat.card K % 2 = 0 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, ← FiniteField.even_card_iff_char_two]
    exact ringChar.eq K 2
  have hK4 : 4 ≤ Nat.card K := by
    have : 0 < Nat.card K := Nat.card_pos
    omega
  rcases hcase with ⟨-, ⟨φ⟩, -⟩ | ⟨-, ⟨φ⟩, -⟩ | ⟨-, -, -, hcyc, -⟩
  ·
    exfalso
    refine hnc fun a ha b hb => ?_
    have h := φ.injective (show φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  ·
    let θ : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K :=
      C.subtype.comp (φ.symm.toMonoidHom.comp
        ((MonoidHom.codRestrict SpecialLinearGroup.toGL (glPi true 2 (p ^ f) K)
          fun A => mem_glPi_true _ _)))
    have hθi : Function.Injective θ := by
      intro A B hAB
      apply SpecialLinearGroup.toGL_injective
      have h1 := φ.symm.injective (Subtype.ext hAB)
      exact congrArg Subtype.val h1
    set T := θ.range with hT
    have : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := isSimpleGroup_SL_two_of_charTwo hK4
    have hTs : IsSimpleGroup T := (MonoidHom.ofInjective hθi).symm.isSimpleGroup
    have hTC : T ≤ C := by
      rintro _ ⟨A, rfl⟩
      exact (φ.symm _).2
    let χ : Kb →* Kˣ := GeneralLinearGroup.det.comp ((glPi true 2 (p ^ f) K).subtype.comp
      (φ.toMonoidHom.comp (Subgroup.inclusion hKbC)))
    have hχ : χ.ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hKbnc
        apply hab
        apply (MonoidHom.ker_eq_bot_iff χ).mp h
        rw [map_mul, map_mul, mul_comm]
      · exact h
    have hKbT : Kb ≤ T := by
      intro k hk
      have hdet : χ ⟨k, hk⟩ = 1 := by
        have : (⟨k, hk⟩ : Kb) ∈ χ.ker := by rw [hχ]; exact Subgroup.mem_top _
        exact this
      set g : GL (Fin 2) K := (φ ⟨k, hKbC hk⟩ : GL (Fin 2) K) with hg
      have hgdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [← GeneralLinearGroup.val_det_apply]
        exact congrArg Units.val hdet
      refine ⟨⟨g, hgdet⟩, ?_⟩
      change ((φ.symm ⟨SpecialLinearGroup.toGL ⟨g, hgdet⟩, _⟩ : C) : GL (Fin 3) K) = k
      have hgl : (⟨SpecialLinearGroup.toGL ⟨g, hgdet⟩, mem_glPi_true _ _⟩ :
          glPi true 2 (p ^ f) K) = φ ⟨k, hKbC hk⟩ := by
        apply Subtype.ext
        apply Units.ext
        rfl
      rw [hgl, MulEquiv.symm_apply_apply]
    have hTN : T ≤ N := by
      have hnormT : (N.subgroupOf T).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hnorm g (hTC g.2) n hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf T) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hKbnc
        apply hab
        have h0 : ∀ c : Kb, (c : GL (Fin 3) K) = 1 := fun c => by
          have : (⟨c, hKbT c.2⟩ : T) ∈ N.subgroupOf T :=
            Subgroup.mem_subgroupOf.mpr (hKbN c.2)
          rw [h, Subgroup.mem_bot] at this
          exact congrArg Subtype.val this
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, h0 a, h0 b]
      · intro t ht
        have : (⟨t, ht⟩ : T) ∈ N.subgroupOf T := by rw [h]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
    have hTcard : Nat.card T = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hθi).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 2) (by norm_num)]
      simp
    rcases hU with hKN | hN62
    ·
      have hKbTeq : Kb = T := le_antisymm hKbT (hKN ▸ hTN)
      have h1 : 2 ^ m * ((2 ^ m) ^ 2 - 1) = Nat.card K * (Nat.card K ^ 2 - 1) := by
        rw [← hcard, ← hTcard, hKbTeq]
      exact (eq_of_mul_sq_sub_one_eq (Nat.one_le_two_pow) (by omega) h1).symm
    ·
      have hTd : Nat.card K * (Nat.card K ^ 2 - 1) ∣ 62400 := by
        rw [← hTcard, ← hN62]
        exact Subgroup.card_dvd_of_le hTN
      have hKbd : 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ 62400 := by
        rw [← hcard, ← hN62]
        exact Subgroup.card_dvd_of_le hKbN
      rw [eq_four_of_dvd_62400 (by omega) hev (by rw [hqK]; exact hq3) hTd,
        eq_two_of_dvd_62400 hm he hKbd]
      norm_num
  ·
    exfalso
    refine hnc fun a ha b hb => ?_
    have h := (@IsCyclic.commGroup C _ hcyc).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h

end Item228Census4Proof

end CFSG.RankThree.PartTwo.Sec21
