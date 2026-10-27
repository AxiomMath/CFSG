module

public import CFSG.Quasithin.Background.A3Structure36BSL2
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem exists_sl2_surjection_of_case34 {X : Type} [Group X] (h : A36Case3 X ∨ A36Case4 X) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ χ₀ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r),
      Function.Surjective χ₀ ∧ χ₀.ker = CFSG.fittingSubgroup X := by
  rcases h with ⟨p, hp, hp3, -, -, e, ψ, hψ, hker, -⟩ | ⟨-, -, ⟨e⟩, -⟩
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    exact ⟨p, hp, by omega, ψ, hψ, hker⟩
  · refine ⟨5, Nat.prime_five, le_rfl,
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup X)),
      e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

section PureGroupTheory

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_normal_complement_of_central_two_part {F₁ K₀ : Subgroup Y} [hF : F₁.Normal]
    (hKF : K₀ ≤ F₁) (hKc : K₀ ≤ Subgroup.center Y) (hK2 : IsPGroup 2 K₀)
    (hodd : Odd (K₀.relIndex F₁)) :
    ∃ W : Subgroup Y, W.Normal ∧ W ≤ F₁ ∧ K₀ ⊓ W = ⊥ ∧ K₀ ⊔ W = F₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ : Subgroup ↥F₁ := K₀.subgroupOf F₁ with hN₀
  have hN₀2 : IsPGroup 2 N₀ := A4.isPGroup_subgroupOf_of_le hKF hK2
  have hN₀idx : ¬ 2 ∣ N₀.index := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  let P : Sylow 2 ↥F₁ := IsPGroup.toSylow hN₀2 hN₀idx
  have hPc : ∀ x ∈ (P : Subgroup ↥F₁), ∀ g : ↥F₁, g * x = x * g := by
    intro x hx g
    have hx' : (x : Y) ∈ K₀ := hx
    exact Subtype.ext (by simpa using (Subgroup.mem_center_iff.mp (hKc hx') (g : Y)))
  have hnorm : Subgroup.normalizer (P : Set ↥F₁) ≤ Subgroup.centralizer (P : Set ↥F₁) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hPc x hx g).symm
  obtain ⟨K', hK'n, -, -, -, hKchar, -, hsup, hinf, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hnorm
  refine ⟨K'.map F₁.subtype, ?_, Subgroup.map_subtype_le K', ?_, ?_⟩
  · have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic K'
    rw [Subgroup.normalizer_eq_top_iff.mpr hF] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (by simpa using h1))
  · rw [eq_bot_iff]
    rintro x ⟨hxK, y, hy, rfl⟩
    have hyN : y ∈ N₀ := hxK
    have : y ∈ K' ⊓ (P : Subgroup ↥F₁) := ⟨hy, hyN⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  · have h1 := congrArg (Subgroup.map F₁.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
    have hP' : (P : Subgroup ↥F₁).map F₁.subtype = K₀ := by
      show N₀.map F₁.subtype = K₀
      exact Subgroup.map_subgroupOf_eq_of_le hKF
    rw [hP'] at h1
    rw [sup_comm]
    exact h1

theorem eq_bot_of_central_two_part (hl2 : L2MultiplierFact) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hperf : Group.IsPerfect Y) (χ : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hχ : Function.Surjective χ) {K₀ W : Subgroup Y} [hW : W.Normal]
    (hKc : K₀ ≤ Subgroup.center Y) (hKW : K₀ ⊓ W = ⊥) (hker : χ.ker = K₀ ⊔ W) : K₀ = ⊥ := by
  have hr2 : r ≠ 2 := by omega
  have hWker : W ≤ χ.ker := hker ▸ le_sup_right
  let π : Y →* Y ⧸ W := QuotientGroup.mk' W
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective W
  let f : (Y ⧸ W) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) := QuotientGroup.lift W χ hWker
  have hfπ : ∀ y, f (π y) = χ y := fun y => rfl
  have hf : Function.Surjective f := fun s => by
    obtain ⟨y, rfl⟩ := hχ s
    exact ⟨π y, hfπ y⟩
  have hperfX : Group.IsPerfect (Y ⧸ W) := inferInstance
  have hkerf : f.ker = K₀.map π := by
    rw [QuotientGroup.ker_lift, hker, Subgroup.map_sup]
    have : W.map π = ⊥ := QuotientGroup.map_mk'_self W
    rw [this, sup_bot_eq]
  have hKcX : f.ker ≤ Subgroup.center (Y ⧸ W) := by
    rw [hkerf]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hπ z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hKc hk) y)]
  have hcenter := CFSG.LocalCores.comap_center_eq_of_perfect hperfX f hf hKcX
  let g : (Y ⧸ W) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r) :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)))).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = Subgroup.center (Y ⧸ W) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcenter]
  have hPSL : IsPSL 2 r 1 ((Y ⧸ W) ⧸ Subgroup.center (Y ⧸ W)) :=
    A36B.isPSL_two_of_mulEquiv hr h5
      ((QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg))
  have hcard := hl2 r hr h5 (Y ⧸ W) hperfX (Subgroup.center (Y ⧸ W)) le_rfl hPSL
  have hrel : f.ker.relIndex (Subgroup.center (Y ⧸ W)) = 2 := by
    rw [Subgroup.relIndex_ker, ← hcenter, Subgroup.map_comap_eq_self_of_surjective hf]
    exact A36B.card_center_sl2 hr hr2
  have hmul : 2 * Nat.card f.ker = Nat.card (Subgroup.center (Y ⧸ W)) := by
    have := Subgroup.relIndex_mul_card f.ker (Subgroup.center (Y ⧸ W))
    rwa [hrel, inf_eq_left.mpr hKcX] at this
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hker1 : Nat.card f.ker = 1 := by omega
  have hkerbot : f.ker = ⊥ := (Subgroup.card_eq_one.mp hker1)
  rw [hkerf] at hkerbot
  have hK₀W : K₀ ≤ W := by
    intro k hk
    have : π k ∈ K₀.map π := Subgroup.mem_map_of_mem π hk
    rw [hkerbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).mp this
  rw [eq_bot_iff, ← hKW]
  exact le_inf le_rfl hK₀W

end PureGroupTheory

theorem sl2_coe_eq_neg_one_of_sq_field {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) K) = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  have hsq : (A : Matrix (Fin 2) (Fin 2) K) * A = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hA, Matrix.SpecialLinearGroup.coe_one]
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have htr : A 0 0 + A 1 1 ≠ 0 := by
    intro h0
    apply h2
    linear_combination -e00 - hdet + A 0 0 * h0
  have hβ : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hγ : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hβ, hγ] at hdet e00 e11
  have hαδ : A 0 0 = A 1 1 := by
    have h1 : A 0 0 * (A 0 0 - A 1 1) = 0 := by linear_combination e00 - hdet
    have hα0 : A 0 0 ≠ 0 := by
      intro h
      rw [h] at e00
      simp at e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hα0)
  have hα : A 0 0 = 1 ∨ A 0 0 = -1 := by
    have : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hα with h1 | h1
  · exfalso
    apply hA1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hβ, hγ, ← hαδ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hβ, hγ, ← hαδ]

theorem sl2_coe_eq_neg_one_of_sq {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod r)) = -1 := by
  have := Fact.mk hr
  exact sl2_coe_eq_neg_one_of_sq_field (CFSG.SectionRank.Ccomm.two_ne_zero_zmod hr2) A hA hA1

section Rank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_two_of_elemAbelian {L E : Subgroup G} {L' : Type} [Group L'] [Finite L'] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (ψ : ↥L →* L') (hψ : Function.Injective ψ)
    (χ₀ : L' →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hodd : ∀ x ∈ χ₀.ker, Odd (orderOf x)) (hEL : E ≤ L) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 := by
  let χ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) := χ₀.comp ψ
  let Φ : ↥E → ↥({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))) := fun e =>
    ⟨(χ ⟨e, hEL e.2⟩ : Matrix (Fin 2) (Fin 2) (ZMod r)), by
      by_cases h1 : χ ⟨e, hEL e.2⟩ = 1
      · left
        rw [h1]
        rfl
      · right
        have hsq : χ ⟨e, hEL e.2⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨(e : G), hEL e.2⟩ : ↥L) ^ 2 = 1 := Subtype.ext (hE.2 e e.2)
          rw [this, map_one]
        exact sl2_coe_eq_neg_one_of_sq hr hr2 _ hsq h1⟩
  have hΦ : Function.Injective Φ := by
    intro e e' h
    have h' := congrArg Subtype.val h
    have hχ : χ ⟨e, hEL e.2⟩ = χ ⟨e', hEL e'.2⟩ := Subtype.ext h'
    set u : ↥L := (⟨(e : G), hEL e.2⟩ : ↥L)⁻¹ * ⟨(e' : G), hEL e'.2⟩ with hu
    have hu2 : u ^ 2 = 1 := by
      apply Subtype.ext
      have hmem : ((e : G)⁻¹ * (e' : G)) ∈ E := E.mul_mem (E.inv_mem e.2) e'.2
      simpa [hu] using hE.2 _ hmem
    have hχu : χ u = 1 := by
      rw [hu, map_mul, map_inv, hχ, inv_mul_cancel]
    have hψu : (ψ u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
    have hψker : ψ u ∈ χ₀.ker := hχu
    have hord : orderOf (ψ u) = 1 := by
      have h1 : orderOf (ψ u) ∣ 2 := orderOf_dvd_of_pow_eq_one hψu
      have h2 := hodd _ hψker
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (by decide)
    have hψ1 : ψ u = 1 := orderOf_eq_one_iff.mp hord
    have hu1 : u = 1 := hψ (by rw [hψ1, map_one])
    have : (⟨(e : G), hEL e.2⟩ : ↥L) = ⟨(e' : G), hEL e'.2⟩ := by
      rw [hu, inv_mul_eq_one] at hu1
      exact hu1
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  calc Nat.card E ≤ Nat.card ↥({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = ({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))).ncard := Nat.card_coe_set_eq _
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem lemma_1_2_1_five_of_strong_sq (hl2 : L2MultiplierFact) {H L : Subgroup G} (hL : L ∈ cComp H)
    (hstrong : A36Strong (modO2Image H L)) (hZ : pCoreOf 2 L ≤ centerOf L)
    (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection hL
  have hperf : Group.IsPerfect ↥L := A36A.isPerfect_of_mem_cComp hL
  have hKc : ψ.ker ≤ Subgroup.center ↥L := by
    rw [hker]
    intro x hx
    have hxG : (x : G) ∈ pCoreOf 2 L := by
      exact ⟨x, hx, rfl⟩
    have hxc := (hZ hxG).2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hxc (g : G) g.2))
  have hqs : CFSG.IsQuasisimple ↥(modO2Image H L) → CFSG.IsQuasisimple ↥L := fun h =>
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf ψ hψ hKc).mpr h
  have hcase : A36Case3 ↥(modO2Image H L) ∨ A36Case4 ↥(modO2Image H L) → False := by
    intro h34
    obtain ⟨r, hr, h5, χ₀, hχ₀, hχ₀ker⟩ := exists_sl2_surjection_of_case34 h34
    have hr2 : r ≠ 2 := by omega
    have hFO := hstrong.2.1.1
    have hFodd : Odd (Nat.card ↥χ₀.ker) := by
      rw [hχ₀ker, hFO]
      exact A312.odd_card_oddCore _
    have hodd : ∀ x ∈ χ₀.ker, Odd (orderOf x) := fun x hx =>
      Odd.of_dvd_nat hFodd (Subgroup.orderOf_dvd_natCard _ hx)
    have hK₀ : ψ.ker = ⊥ := by
      let χ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) := χ₀.comp ψ
      have hχ : Function.Surjective χ := hχ₀.comp hψ
      have hKF : ψ.ker ≤ χ.ker := fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        simp [χ, hx]
      have hK2 : IsPGroup 2 ψ.ker := by
        rw [hker]
        exact CFSG.pCore_isPGroup
      have hrel : Odd (ψ.ker.relIndex χ.ker) := by
        rw [Subgroup.relIndex_ker, ← MonoidHom.comap_ker χ₀ ψ,
          Subgroup.map_comap_eq_self_of_surjective hψ]
        exact hFodd
      obtain ⟨W, hWn, -, hKW, hsup⟩ :=
        exists_normal_complement_of_central_two_part (F₁ := χ.ker) hKF hKc hK2 hrel
      exact eq_bot_of_central_two_part hl2 hr h5 hperf χ hχ hKc hKW hsup.symm
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hK₀
    obtain ⟨E, hEL, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two L
    have hle := card_le_two_of_elemAbelian hr hr2 ψ hinj χ₀ hodd hEL hE
    rw [hEcard] at hle
    have h4 : 2 ^ 2 ≤ 2 ^ CFSG.Open.pRank 2 L := Nat.pow_le_pow_right (by norm_num) hm
    omega
  rcases hstrong.1 with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact hqs hc.1
  · exact hqs hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

theorem lemma_1_2_1_five_of_a3 (hl2 : L2MultiplierFact) {H L : Subgroup G}
    (h36 : A36Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hL : L ∈ cComp H)
    (hZ : pCoreOf 2 L ≤ centerOf L) (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L :=
  lemma_1_2_1_five_of_strong_sq hl2 hL (h36 _ (modO2Image_mem_cComp hL)) hZ hm

theorem lemma_1_2_1_five (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (hl2 : L2MultiplierFact)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    (hZ : pCoreOf 2 L ≤ centerOf L) (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L :=
  lemma_1_2_1_five_of_a3 hl2 (h36 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH)) hL hZ hm

end Rank

end CFSG.Quasithin
