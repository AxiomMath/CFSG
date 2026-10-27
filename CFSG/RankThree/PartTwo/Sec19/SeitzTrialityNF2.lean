module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section SL2

theorem sl2_cube_quad {F : Type*} [Field F] {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (x : Matrix (Fin 2) (Fin 2) F) ^ 2 + (x : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by
  have hM3 : (x : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) F =>
      (y : Matrix (Fin 2) (Fin 2) F)) hx3
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := x.2
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM] at hM3 hdet ⊢
  rw [Matrix.det_fin_two_of] at hdet
  have e00 := congrFun (congrFun hM3 0) 0
  have e01 := congrFun (congrFun hM3 0) 1
  have e10 := congrFun (congrFun hM3 1) 0
  have e11 := congrFun (congrFun hM3 1) 1
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hb : b * ((a + d) ^ 2 - 1) = 0 := by linear_combination e01 + b * hdet
  have hc : c * ((a + d) ^ 2 - 1) = 0 := by linear_combination e10 + c * hdet
  have ha : ((a + d) ^ 2 - 1) * a = 1 + (a + d) := by
    linear_combination e00 + (2 * a + d) * hdet
  have hd : ((a + d) ^ 2 - 1) * d = 1 + (a + d) := by
    linear_combination e11 + (a + 2 * d) * hdet
  by_cases ht : a + d + 1 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination a * ht - hdet
    · linear_combination b * ht
    · linear_combination c * ht
    · linear_combination d * ht - hdet
  · exfalso
    have hsq : (a + d) ^ 2 - 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at ha
      exact ht (by linear_combination -ha)
    have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hsq
    have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_right hsq
    have h1a : (a + d - 1) * a = 1 := by
      apply mul_left_cancel₀ ht
      linear_combination ha
    have h1d : (a + d - 1) * d = 1 := by
      apply mul_left_cancel₀ ht
      linear_combination hd
    have had : a = d := by
      have : (a + d - 1) * (a - d) = 0 := by linear_combination h1a - h1d
      have hne : a + d - 1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1a
        exact zero_ne_one h1a
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
    subst had
    subst hb0
    subst hc0
    have ha2 : a * a = 1 := by linear_combination hdet
    have ha3 : a * a * a = 1 := by linear_combination e00
    have ha1 : a = 1 := by linear_combination ha3 - a * ha2
    subst ha1
    apply hx1
    apply Subtype.ext
    rw [hM, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem aux_three_zero {R : Type*} [Ring R] {G H : R} (hc : Commute H G) (hG3 : G ^ 3 = 1)
    (hG : G ^ 2 + G + 1 = 0) (hH : H ^ 2 + H + 1 = 0)
    (hU : (H * G) ^ 2 + H * G + 1 = 0) (hV : (H * G ^ 2) ^ 2 + H * G ^ 2 + 1 = 0) :
    (3 : R) = 0 := by
  have hG2 : G ^ 2 = -G - 1 := by
    rw [add_assoc] at hG
    rw [eq_neg_of_add_eq_zero_left hG]; noncomm_ring
  have hH2 : H ^ 2 = -H - 1 := by
    rw [add_assoc] at hH
    rw [eq_neg_of_add_eq_zero_left hH]; noncomm_ring
  have key1 : (H * G) ^ 2 = H ^ 2 * G ^ 2 := hc.mul_pow 2
  have hG4 : (G ^ 2) ^ 2 = G := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hG3, one_mul]
  have key2 : (H * G ^ 2) ^ 2 = H ^ 2 * G := by
    rw [(hc.pow_right 2).mul_pow 2, hG4]
  have hU' : (-H - 1) * (-G - 1) + H * G + 1 = 0 := by
    have := hU
    rw [key1, hH2, hG2] at this
    exact this
  have hV' : (-H - 1) * G + H * (-G - 1) + 1 = 0 := by
    have := hV
    rw [key2, hH2, hG2] at this
    exact this
  calc (3 : R) = ((-H - 1) * (-G - 1) + H * G + 1) + ((-H - 1) * G + H * (-G - 1) + 1) := by
        noncomm_ring
        simp
    _ = 0 := by rw [hU', hV', add_zero]

theorem sl2_commuting_cube_one {F : Type*} [Field F] (h3 : (3 : F) ≠ 0)
    {g h : Matrix.SpecialLinearGroup (Fin 2) F} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hh3 : h ^ 3 = 1)
    (hgh : g * h = h * g) : h ∈ Subgroup.zpowers g := by
  by_contra hnot
  have hh1 : h ≠ 1 := fun e => hnot (e ▸ Subgroup.one_mem _)
  have hhg : h ≠ g := fun e => hnot (e ▸ Subgroup.mem_zpowers g)
  have hhg2 : h ≠ g ^ 2 := fun e => hnot (e ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2)
  have hgi : g⁻¹ = g ^ 2 := inv_eq_of_mul_eq_one_right ((pow_succ' g 2).symm.trans hg3)
  have hg2i : (g ^ 2)⁻¹ = g := inv_eq_of_mul_eq_one_right ((pow_succ g 2).symm.trans hg3)
  have hcomm : Commute h g := hgh.symm
  have hu3 : (h * g) ^ 3 = 1 := by rw [hcomm.mul_pow, hh3, hg3, one_mul]
  have hv3 : (h * g ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow, hh3, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hg3,
      one_pow, one_mul]
  have hu1 : h * g ≠ 1 := fun e => hhg2 (by rw [eq_inv_of_mul_eq_one_left e, hgi])
  have hv1 : h * g ^ 2 ≠ 1 := fun e => hhg (by rw [eq_inv_of_mul_eq_one_left e, hg2i])
  have hG := sl2_cube_quad hg3 hg1
  have hH := sl2_cube_quad hh3 hh1
  have hU := sl2_cube_quad hu3 hu1
  have hV := sl2_cube_quad hv3 hv1
  have hG3' : (g : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) F =>
      (y : Matrix (Fin 2) (Fin 2) F)) hg3
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hc'' : (h : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) F =>
      (y : Matrix (Fin 2) (Fin 2) F)) hgh.symm
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hc' : Commute (h : Matrix (Fin 2) (Fin 2) F) (g : Matrix (Fin 2) (Fin 2) F) := hc''
  have key := aux_three_zero hc' hG3' hG hH
    (by simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using hU)
    (by simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using hV)
  apply h3
  have h3m : Matrix.scalar (Fin 2) (3 : F) = 0 := by
    rw [map_ofNat (Matrix.scalar (Fin 2)) 3]
    exact key
  have := congrFun (congrFun h3m 0) 0
  simpa [Matrix.scalar_apply] using this

theorem zpowers_of_commuting_cube_one_of_iso {G : Type*} [Group G] {F : Type*} [Field F]
    (h3 : (3 : F) ≠ 0) (H : Subgroup G) (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F) {g h : G}
    (hg : g ∈ H) (hh : h ∈ H) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hh3 : h ^ 3 = 1)
    (hgh : g * h = h * g) : h ∈ Subgroup.zpowers g := by
  set g' : H := ⟨g, hg⟩ with hg'def
  set h' : H := ⟨h, hh⟩ with hh'def
  have hg3' : g' ^ 3 = 1 := Subtype.ext (by simpa [g'] using hg3)
  have hg1' : g' ≠ 1 := fun h1 => hg1 (by simpa [g'] using congrArg Subtype.val h1)
  have hh3' : h' ^ 3 = 1 := Subtype.ext (by simpa [h'] using hh3)
  have hgh' : g' * h' = h' * g' := Subtype.ext (by simpa [g', h'] using hgh)
  have key := sl2_commuting_cube_one h3 (g := e g') (h := e h')
    (by rw [← map_pow, hg3', map_one])
    (fun h1 => hg1' (e.injective (h1.trans (map_one e).symm)))
    (by rw [← map_pow, hh3', map_one])
    (by rw [← map_mul, ← map_mul, hgh'])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
  have hk' : g' ^ k = h' := e.injective (by rw [map_zpow]; exact hk)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [g', h'] using congrArg Subtype.val hk'⟩

theorem no_plane_in_sl2 {G : Type*} [Group G] {F : Type*} [Field F] (h3 : (3 : F) ≠ 0)
    (H : Subgroup G) (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) F) {E : Subgroup G}
    (hEH : E ≤ H) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcube : ∀ x ∈ E, x ^ 3 = 1)
    (hc : Nat.card E = 3 ^ 2) : False := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hne : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    have hall : ∀ x ∈ E, x = 1 := fun x hx => by_contra (fun h => hcon ⟨x, hx, h⟩)
    have : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)⟩, ⟨1⟩⟩
    omega
  obtain ⟨x, hxE, hx1⟩ := hne
  have hsub : ¬ (E : Set G) ⊆ (Subgroup.zpowers x : Set G) := by
    intro hsub
    have hle : E ≤ Subgroup.zpowers x := hsub
    haveI : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by
      rw [card_zpowers_of_cube_one (hcube x hxE) hx1]; norm_num)
    have := Subgroup.card_le_of_le hle
    rw [card_zpowers_of_cube_one (hcube x hxE) hx1, hc] at this
    omega
  obtain ⟨y, hyE, hyx⟩ := Set.not_subset.mp hsub
  exact hyx (zpowers_of_commuting_cube_one_of_iso h3 H e (hEH hxE) (hEH hyE) (hcube x hxE) hx1
    (hcube y hyE) (hcomm x hxE y hyE))

end SL2

section Field

theorem three_ne_zero_of_cube {X : Type} [Field X] [Finite X] (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) : (3 : X) ≠ 0 := by
  have hchar : CharP X 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := n * 3) (by omega) (by rw [hX, pow_mul])
  intro h
  have h' : ((3 : ℕ) : X) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff X 2] at h'
  omega

theorem three_ne_zero_fixSubfield {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (h3 : (3 : X) ≠ 0) :
    (3 : fixSubfield σ) ≠ 0 := by
  intro h
  apply h3
  have h1 : (fixSubfield σ).subtype (3 : fixSubfield σ) = (fixSubfield σ).subtype 0 := by rw [h]
  rw [map_ofNat, map_zero] at h1
  exact h1

end Field

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem asub_commutator_eq (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) : ⁅Asub σ, Asub σ⁆ = Asub σ := by
  have hσ3 := sigma_pow_three σ n hX hσ
  have hK4 := four_le_card_of_cube n hn hX
  exact (Subgroup.isPerfect_iff).mp (KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4).1

theorem centralizer_comm_le_asub (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {b : C0 σ} (hb : b ∈ Bsub σ) (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) :
    ⁅Subgroup.centralizer {b}, Subgroup.centralizer {b}⁆ ≤ Asub σ := by
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hK := KS11Lie6Proof.d4ThreeBCent_holds X (2 ^ n) σ hX hσ h3 b hb hb3 hb1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact hK.1 x hx y hy


theorem bsub_le_normalizer_asub : Bsub σ ≤ Subgroup.normalizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ)) := by
  intro b hb
  have hb' : ∀ h ∈ Asub σ, h * b = b * h := fun h hh => Subgroup.mem_centralizer_iff.mp hb h hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : b * h * b⁻¹ = h := by rw [← hb' h hh]; group
    rw [this]; exact hh
  · intro hh
    have hx : (b * h * b⁻¹) * b = b * (b * h * b⁻¹) := hb' _ hh
    have h2 : h = b * h * b⁻¹ := by
      calc h = b⁻¹ * ((b * h * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hx]
        _ = b * h * b⁻¹ := by group
    rw [h2]
    exact hh

theorem mem_sup_AB_decomp {e : C0 σ} (he : e ∈ Asub σ ⊔ Bsub σ) :
    ∃ a ∈ Asub σ, ∃ b ∈ Bsub σ, e = a * b := by
  have h1 := Subgroup.coe_mul_of_left_le_normalizer_right (Bsub σ) (Asub σ) (bsub_le_normalizer_asub σ)
  rw [sup_comm] at he
  have he' : e ∈ ((Bsub σ ⊔ Asub σ : Subgroup (C0 σ)) : Set (C0 σ)) := he
  rw [h1] at he'
  obtain ⟨b, hb, a, ha, rfl⟩ := he'
  refine ⟨a, ha, b, hb, ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp hb a ha).symm


theorem sl2_nontrivial (F : Type*) [Field F] : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
  ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, fun h => by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp at this⟩⟩

theorem sup_AB_ne_top (hAB : TrialityABFacts σ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    Asub σ ⊔ Bsub σ ≠ ⊤ := by
  intro htop
  haveI := isSimpleGroup_C0 σ n hn hX hσ
  obtain ⟨eA⟩ := hAB.sl2A
  obtain ⟨eB⟩ := hAB.sl2B
  haveI := sl2_nontrivial X
  haveI := sl2_nontrivial (fixSubfield σ)
  have hAne : Asub σ ≠ ⊥ := by
    have : Nontrivial (Asub σ) := eA.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  have hBne : Bsub σ ≠ ⊥ := by
    have : Nontrivial (Bsub σ) := eB.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  have hAnormal : (Asub σ).Normal := by
    constructor
    intro a ha g
    have hg : g ∈ Asub σ ⊔ Bsub σ := by rw [htop]; exact Subgroup.mem_top g
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_AB_decomp σ hg
    have hb'c : ∀ h ∈ Asub σ, h * b' = b' * h := fun h hh => Subgroup.mem_centralizer_iff.mp hb' h hh
    have : a' * b' * a * (a' * b')⁻¹ = a' * a * a'⁻¹ := by
      have e1 : b' * a * b'⁻¹ = a := by rw [← hb'c a ha]; group
      calc a' * b' * a * (a' * b')⁻¹ = a' * (b' * a * b'⁻¹) * a'⁻¹ := by group
        _ = a' * a * a'⁻¹ := by rw [e1]
    rw [this]
    exact mul_mem (mul_mem ha' ha) (inv_mem ha')
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Asub σ) with h | h
  · exact hAne h
  · apply hBne
    rw [eq_bot_iff]
    intro b hb
    have hcomm : ∀ g : C0 σ, g * b = b * g := fun g => by
      have hg : g ∈ Asub σ := by rw [h]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_iff.mp hb g hg
    have h1 : (MulAut.conj b : MulAut (C0 σ)) = 1 := by
      refine MulEquiv.ext fun g => ?_
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (hcomm g).symm
    have := conj_injective_C0 σ n hn hX hσ (a₁ := b) (a₂ := 1) (by rw [map_one]; exact h1)
    rw [this]
    exact Subgroup.one_mem _


theorem asub_ne_bot (hAB : TrialityABFacts σ) : Asub σ ≠ ⊥ := by
  obtain ⟨eA⟩ := hAB.sl2A
  haveI := sl2_nontrivial X
  have : Nontrivial (Asub σ) := eA.toEquiv.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem normalizer_AB_eq (hAB : TrialityABFacts σ) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    Subgroup.normalizer ((Asub σ ⊔ Bsub σ : Subgroup (C0 σ)) : Set (C0 σ)) = Asub σ ⊔ Bsub σ := by
  haveI := isSimpleGroup_C0 σ n hn hX hσ
  rcases hAB.max _ (Subgroup.le_normalizer) with h | h
  · exact h
  · exfalso
    have hnormal : (Asub σ ⊔ Bsub σ : Subgroup (C0 σ)).Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Asub σ ⊔ Bsub σ) with h' | h'
    · exact asub_ne_bot σ hAB (eq_bot_iff.mpr (h' ▸ le_sup_left))
    · exact sup_AB_ne_top σ hAB n hn hX hσ h'

theorem centralizer_le_AB (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {b : C0 σ}
    (hb : b ∈ Bsub σ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    Subgroup.centralizer {b} ≤ Asub σ ⊔ Bsub σ := by
  have hn1 : 1 ≤ n := by omega
  set C : Subgroup (C0 σ) := Subgroup.centralizer ({b} : Set (C0 σ)) with hC
  have hAC : Asub σ ≤ C := fun a ha => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hb a ha
  have hcomm_eq : ⁅C, C⁆ = Asub σ := le_antisymm
    (centralizer_comm_le_asub σ n hn1 hX hσ hb hb3 hb1)
    (by
      calc Asub σ = ⁅Asub σ, Asub σ⁆ := (asub_commutator_eq σ n hn1 hX hσ).symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC hAC)
  have hCC : ⁅C, C⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hCnorm : ∀ c ∈ C, ∀ x ∈ ⁅C, C⁆, c * x * c⁻¹ ∈ ⁅C, C⁆ := by
    intro c hc x hx
    have h2 : ⁅c, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hc (hCC hx)
    have h1 : c * x * c⁻¹ = ⁅c, x⁆ * x := by rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem h2 hx
  have hCnormA : ∀ c ∈ C, ∀ h : C0 σ, h ∈ Asub σ ↔ c * h * c⁻¹ ∈ Asub σ := by
    intro c hc h
    rw [← hcomm_eq]
    constructor
    · intro hh; exact hCnorm c hc h hh
    · intro hh
      have := hCnorm c⁻¹ (inv_mem hc) _ hh
      simpa [mul_assoc] using this
  have hCnormB : ∀ c ∈ C, ∀ h : C0 σ, h ∈ Bsub σ ↔ c * h * c⁻¹ ∈ Bsub σ := by
    intro c hc h
    have hA1 : ∀ a, a ∈ Asub σ → c⁻¹ * a * c ∈ Asub σ := fun a ha => by
      have := (hCnormA c⁻¹ (inv_mem hc) a).mp ha
      simpa using this
    have hA2 : ∀ a, a ∈ Asub σ → c * a * c⁻¹ ∈ Asub σ := fun a ha => (hCnormA c hc a).mp ha
    constructor
    · intro hh
      rw [Bsub, Subgroup.mem_centralizer_iff]
      intro a ha
      have e1 : (c⁻¹ * a * c) * h = h * (c⁻¹ * a * c) := Subgroup.mem_centralizer_iff.mp hh _ (hA1 a ha)
      calc a * (c * h * c⁻¹) = c * ((c⁻¹ * a * c) * h) * c⁻¹ := by group
        _ = c * (h * (c⁻¹ * a * c)) * c⁻¹ := by rw [e1]
        _ = c * h * c⁻¹ * a := by group
    · intro hh
      rw [Bsub, Subgroup.mem_centralizer_iff]
      intro a ha
      have e1 : (c * a * c⁻¹) * (c * h * c⁻¹) = (c * h * c⁻¹) * (c * a * c⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hh _ (hA2 a ha)
      have e2 : c * (a * h) * c⁻¹ = c * (h * a) * c⁻¹ := by
        calc c * (a * h) * c⁻¹ = (c * a * c⁻¹) * (c * h * c⁻¹) := by group
          _ = (c * h * c⁻¹) * (c * a * c⁻¹) := e1
          _ = c * (h * a) * c⁻¹ := by group
      have := mul_left_cancel (mul_right_cancel e2)
      exact this
  have hCN : C ≤ Subgroup.normalizer ((Asub σ ⊔ Bsub σ : Subgroup (C0 σ)) : Set (C0 σ)) := by
    intro c hc
    refine Subgroup.inf_normalizer_le_normalizer_sup (Asub σ) (Bsub σ) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_normalizer_iff]; exact hCnormA c hc
    · rw [Subgroup.mem_normalizer_iff]; exact hCnormB c hc
  rw [← normalizer_AB_eq σ hAB n hn1 hX hσ]
  exact hCN


theorem plane_in_AB (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n))
    {E : Subgroup (C0 σ)} (hE : CFSG.IsElementaryAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hle : E ≤ Asub σ ⊔ Bsub σ) :
    ∃ a b : C0 σ, a ∈ Asub σ ∧ b ∈ Bsub σ ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      E = Subgroup.closure {a, b} := by
  have hn1 : 1 ≤ n := by omega
  have h3 : (3 : X) ≠ 0 := three_ne_zero_of_cube n hn1 hX
  have h3k := three_ne_zero_fixSubfield σ h3
  obtain ⟨eA, -⟩ := hAB.sl2A
  obtain ⟨eB⟩ := hAB.sl2B
  have hcomm := elemAb_comm hE
  have hcube := elemAb_cube hE
  have hdec : ∀ e ∈ E, ∃ a ∈ Asub σ, ∃ b ∈ Bsub σ, e = a * b :=
    fun e he => mem_sup_AB_decomp σ (hle he)
  have hABcomm : ∀ a ∈ Asub σ, ∀ b ∈ Bsub σ, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  have huniq : ∀ a ∈ Asub σ, ∀ a' ∈ Asub σ, ∀ b ∈ Bsub σ, ∀ b' ∈ Bsub σ,
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a ha a' ha' b hb b' hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ Asub σ ⊓ Bsub σ := Subgroup.mem_inf.mpr
      ⟨(Asub σ).mul_mem ((Asub σ).inv_mem ha') ha,
        h1 ▸ (Bsub σ).mul_mem hb' ((Bsub σ).inv_mem hb)⟩
    rw [hAB.inf_bot, Subgroup.mem_bot] at h2
    have haa : a = a' := (inv_mul_eq_one.mp h2).symm
    subst haa
    exact ⟨rfl, mul_left_cancel h⟩
  have hF3 : ∀ a ∈ Asub σ, ∀ b ∈ Bsub σ, a * b ∈ E → a ^ 3 = 1 ∧ b ^ 3 = 1 := by
    intro a ha b hb hab
    have h1 : (a * b) ^ 3 = 1 := hcube _ hab
    have hc' : Commute a b := hABcomm a ha b hb
    rw [hc'.mul_pow] at h1
    exact huniq (a ^ 3) (pow_mem ha 3) 1 (one_mem _) (b ^ 3) (pow_mem hb 3) 1 (one_mem _)
      (by rw [h1, mul_one])
  have hF4 : ∀ a ∈ Asub σ, ∀ b ∈ Bsub σ, ∀ a' ∈ Asub σ, ∀ b' ∈ Bsub σ, a * b ∈ E → a' * b' ∈ E →
      a * a' = a' * a ∧ b * b' = b' * b := by
    intro a ha b hb a' ha' b' hb' hab hab'
    have h := hcomm _ hab _ hab'
    have e1 : (a * b) * (a' * b') = (a * a') * (b * b') := by
      calc (a * b) * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [(hABcomm a' ha' b hb).symm]
        _ = (a * a') * (b * b') := by group
    have e2 : (a' * b') * (a * b) = (a' * a) * (b' * b) := by
      calc (a' * b') * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [(hABcomm a ha b' hb').symm]
        _ = (a' * a) * (b' * b) := by group
    exact huniq _ (mul_mem ha ha') _ (mul_mem ha' ha) _ (mul_mem hb hb') _ (mul_mem hb' hb)
      (by rw [← e1, ← e2]; exact h)
  have hH1 : ∃ a ∈ Asub σ, ∃ b ∈ Bsub σ, a * b ∈ E ∧ a ≠ 1 := by
    by_contra hcon
    have hEB : E ≤ Bsub σ := by
      intro e he
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec e he
      have : a = 1 := by_contra (fun h => hcon ⟨a, ha, b, hb, he, h⟩)
      rw [this, one_mul]
      exact hb
    exact no_plane_in_sl2 h3k (Bsub σ) eB hEB hcomm hcube hc
  have hH2 : ∃ a ∈ Asub σ, ∃ b ∈ Bsub σ, a * b ∈ E ∧ b ≠ 1 := by
    by_contra hcon
    have hEA : E ≤ Asub σ := by
      intro e he
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec e he
      have : b = 1 := by_contra (fun h => hcon ⟨a, ha, b, hb, he, h⟩)
      rw [this, mul_one]
      exact ha
    exact no_plane_in_sl2 h3 (Asub σ) eA hEA hcomm hcube hc
  obtain ⟨a, ha, b₁, hb₁, hab₁, ha1⟩ := hH1
  obtain ⟨a₂, ha₂, b, hb, hab₂, hb1⟩ := hH2
  have ha3 : a ^ 3 = 1 := (hF3 a ha b₁ hb₁ hab₁).1
  have hb3 : b ^ 3 = 1 := (hF3 a₂ ha₂ b hb hab₂).2
  have hAparts : ∀ a' ∈ Asub σ, ∀ b' ∈ Bsub σ, a' * b' ∈ E → a' ∈ Subgroup.zpowers a := by
    intro a' ha' b' hb' hae
    have hc1 := (hF4 a' ha' b' hb' a ha b₁ hb₁ hae hab₁).1
    exact zpowers_of_commuting_cube_one_of_iso h3 (Asub σ) eA ha ha' ha3 ha1
      (hF3 a' ha' b' hb' hae).1 hc1.symm
  have hBparts : ∀ a' ∈ Asub σ, ∀ b' ∈ Bsub σ, a' * b' ∈ E → b' ∈ Subgroup.zpowers b := by
    intro a' ha' b' hb' hae
    have hc1 := (hF4 a' ha' b' hb' a₂ ha₂ b hb hae hab₂).2
    exact zpowers_of_commuting_cube_one_of_iso h3k (Bsub σ) eB hb hb' hb3 hb1
      (hF3 a' ha' b' hb' hae).2 hc1.symm
  let f : Subgroup.zpowers a × Subgroup.zpowers b → C0 σ := fun p => (p.1 : C0 σ) * (p.2 : C0 σ)
  have hPc := card_zpowers_of_cube_one ha3 ha1
  have hQc := card_zpowers_of_cube_one hb3 hb1
  haveI : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  haveI : Finite (Subgroup.zpowers b) := Nat.finite_of_card_ne_zero (by rw [hQc]; norm_num)
  have hsub : (E : Set (C0 σ)) ⊆ Set.range f := by
    intro e he
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec e he
    exact ⟨(⟨a', hAparts a' ha' b' hb' he⟩, ⟨b', hBparts a' ha' b' hb' he⟩), rfl⟩
  have hrange : Nat.card (Set.range f) ≤ 3 ^ 2 := by
    have h1 := Finite.card_range_le f
    rw [Nat.card_prod, hPc, hQc] at h1
    omega
  have hEq : (E : Set (C0 σ)) = Set.range f :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hrange.trans (by rw [← hc]; exact le_of_eq rfl)) (Set.toFinite _)
  have haE : a ∈ E := by
    have : a ∈ Set.range f := ⟨(⟨a, Subgroup.mem_zpowers a⟩, ⟨1, one_mem _⟩), by simp [f]⟩
    rw [← hEq] at this
    exact this
  have hbE : b ∈ E := by
    have : b ∈ Set.range f := ⟨(⟨1, one_mem _⟩, ⟨b, Subgroup.mem_zpowers b⟩), by simp [f]⟩
    rw [← hEq] at this
    exact this
  refine ⟨a, b, ha, hb, ha3, hb3, ha1, hb1, le_antisymm ?_ ?_⟩
  · intro e he
    have he' : e ∈ Set.range f := by rw [← hEq]; exact he
    obtain ⟨⟨u, v⟩, rfl⟩ := he'
    refine mul_mem (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) u.2)
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) v.2)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact haE
    · rw [Set.mem_singleton_iff.mp hx]; exact hbE

theorem inner_Y_case (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n))
    {E₀ : Subgroup (C0 σ)} (hE : CFSG.IsElementaryAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 2)
    {y : C0 σ} (hyE : y ∈ E₀) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hY : ∃ g : C0 σ, g * y * g⁻¹ ∈ Bsub σ) :
    ∃ g a b : C0 σ, a ∈ Asub σ ∧ b ∈ Bsub σ ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      E₀.map (MulAut.conj g).toMonoidHom = Subgroup.closure {a, b} := by
  obtain ⟨g, hg⟩ := hY
  have hE₁ : CFSG.IsElementaryAbelian 3 (E₀.map (MulAut.conj g).toMonoidHom) :=
    isElementaryAbelian_map_three hE (MulAut.conj g)
  have hc₁ : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hc
  have hb₀E : g * y * g⁻¹ ∈ E₀.map (MulAut.conj g).toMonoidHom := ⟨y, hyE, rfl⟩
  have hb₀3 : (g * y * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3]
    group
  have hb₀1 : g * y * g⁻¹ ≠ 1 := fun h => hy1 (by
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, h]
    group)
  have hle : E₀.map (MulAut.conj g).toMonoidHom ≤ Asub σ ⊔ Bsub σ := fun e he =>
    centralizer_le_AB σ hAB n hn hX hσ hg hb₀3 hb₀1 (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (elemAb_comm hE₁ _ hb₀E e he).symm)
  obtain ⟨a, b, ha, hb, ha3, hb3, ha1, hb1, hEab⟩ := plane_in_AB σ hAB n hn hX hσ hE₁ hc₁ hle
  exact ⟨g, a, b, ha, hb, ha3, hb3, ha1, hb1, hEab⟩

end Model

end CFSG.RankThree.PartTwo.Sec19
