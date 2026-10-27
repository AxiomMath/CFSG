module

public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Gen
public import CFSG.RankThree.SubgroupLists.PointLocalSL2

public section

namespace CFSG.Quasithin.H13.Ch9.Sp4B

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem heis_zero : heis (0 : K) 0 0 = 1 :=
  Units.ext (by rw [coe_heis, heisMat_zero, Units.val_one])

theorem heis_mul_self [CharP K 2] (α β γ : K) : heis α β γ * heis α β γ = 1 := by
  rw [heis_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    zero_add, sub_self, heis_zero]

theorem heis_inj {α β γ α' β' γ' : K} (h : heis α β γ = heis α' β' γ') :
    α = α' ∧ β = β' ∧ γ = γ' := by
  have e1 := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1)) h
  have e2 := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1)) h
  have e3 := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0)) h
  simp only [coe_heis, heisMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂] at e1 e2 e3
  simp at e1 e2 e3
  exact ⟨e1, e2, e3⟩

theorem spForm_heis_mulVec_self [CharP K 2] (α β γ : K) {u : V₄ → K}
    (hu : u (Sum.inr 0) = 1) :
    spForm 2 K ((heis α β γ : Matrix V₄ V₄ K) *ᵥ u) u = γ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [heis_mulVec, spForm_apply]
  simp [Fin.sum_univ_two, spE, hu, Pi.single_apply]
  linear_combination (α * u (Sum.inl 1) + β * u (Sum.inr 1)) * h2

theorem conj_heis [CharP K 2] {l : GL V₄ K} (hl : l ∈ StatedSp 2 K)
    (he : (l : Matrix V₄ V₄ K) *ᵥ spE = spE) (α β γ : K) :
    l * heis α β γ * l⁻¹ =
      heis (α * spBlock ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) 0 0 +
          β * spBlock ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) 1 0)
        (α * spBlock ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) 0 1 +
          β * spBlock ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) 1 1) γ := by
  have he' : ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE := by
    conv_lhs => rw [← he]
    rw [gl_inv_mulVec_mulVec]
  have he1 : (l : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by rw [one_smul]; exact he
  have he1' : ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by
    rw [one_smul]; exact he'
  have hH : IsHeisAt spE (l * heis α β γ * l⁻¹) := by
    have := (isHeisAt_heis α β γ).conj hl
    rwa [he] at this
  obtain ⟨α', β', γ', hy⟩ := exists_eq_heis_of_isHeisAt hH
  have hpar : ∀ v : V₄ → K, v (Sum.inr 0) = 0 →
      α * (((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inl 1) +
        β * (((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 1) =
      α' * v (Sum.inl 1) + β' * v (Sum.inr 1) := by
    intro v hv
    have e1 := heis_conj_param hl he1 he1' α β γ hv
    have e2 := heis_mulVec_of_mem α' β' γ' hv
    rw [← hy, e1] at e2
    have := congrFun e2 (Sum.inl 0)
    simpa [spE] using this
  have hv1 := hpar (Pi.single (Sum.inl 1) 1) (by simp)
  have hv3 := hpar (Pi.single (Sum.inr 1) 1) (by simp)
  rw [mulVec_inl_one_of_lineStab he1' (by simp), mulVec_inr_one_of_lineStab he1' (by simp)]
    at hv1 hv3
  simp [-Matrix.coe_units_inv] at hv1 hv3
  have hγ : γ' = γ := by
    set f : V₄ → K := Pi.single (Sum.inr 0) 1 with hf
    have hf0 : f (Sum.inr 0) = 1 := by simp [hf]
    have h1 := spForm_heis_mulVec_self α' β' γ' hf0
    rw [← hy, gl_mulVec_mul, gl_mulVec_mul] at h1
    set u := ((l⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ f with hu
    have hfu : f = (l : Matrix V₄ V₄ K) *ᵥ u := by rw [hu, gl_mulVec_inv_mulVec]
    have h1' : spForm 2 K ((l : Matrix V₄ V₄ K) *ᵥ ((heis α β γ : Matrix V₄ V₄ K) *ᵥ u))
        ((l : Matrix V₄ V₄ K) *ᵥ u) = γ' := by
      rw [← hfu]
      exact h1
    rw [spForm_mulVec hl] at h1'
    have hu0 : u (Sum.inr 0) = 1 := by
      rw [← spForm_spE_left u, ← he', hu, spForm_mulVec (inv_mem hl), spForm_spE_left, hf0]
    rw [spForm_heis_mulVec_self α β γ hu0] at h1'
    exact h1'.symm
  rw [hy, hγ, ← hv1, ← hv3]

omit [Field K] in
theorem of_eq3 {Q : K → K → K → Prop} {a b c a' b' c' : K} (h : Q a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : Q a' b' c' := by
  subst ha hb hc
  exact h

theorem heis_all [Fintype K] (hK : Fintype.card K = 4) (Q : K → K → K → Prop)
    (hmul : ∀ a b c a' b' c', Q a b c → Q a' b' c' →
      Q (a + a') (b + b') (c + c' + a * b' - a' * b))
    (hinv : ∀ a b c, Q a b c → Q (-a) (-b) (-c))
    (hconj : ∀ a b c, Q a b c → ∀ m : SL(2, K),
      Q (a * (m : Matrix (Fin 2) (Fin 2) K) 0 0 + b * (m : Matrix (Fin 2) (Fin 2) K) 1 0)
        (a * (m : Matrix (Fin 2) (Fin 2) K) 0 1 + b * (m : Matrix (Fin 2) (Fin 2) K) 1 1) c)
    {a₀ b₀ c₀ : K} (h₀ : Q a₀ b₀ c₀) (hne : a₀ ≠ 0 ∨ b₀ ≠ 0) : ∀ a b c, Q a b c := by
  have := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hall : ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → Q a b c₀ := by
    intro a b hab
    have hu : (![a₀, b₀] : Fin 2 → K) ≠ 0 := by
      intro h
      rcases hne with h' | h'
      · exact h' (by simpa using congrFun h 0)
      · exact h' (by simpa using congrFun h 1)
    have hv : (![a, b] : Fin 2 → K) ≠ 0 := by
      intro h
      rcases hab with h' | h'
      · exact h' (by simpa using congrFun h 0)
      · exact h' (by simpa using congrFun h 1)
    obtain ⟨m, hm⟩ := exists_sl2_vecMul_eq hu hv
    have e0 := congrFun hm 0
    have e1 := congrFun hm 1
    simp [vecMul, dotProduct, Fin.sum_univ_two] at e0 e1
    exact of_eq3 (hconj a₀ b₀ c₀ h₀ m) e0 e1 rfl
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_card_four hK
  have hμ' : 1 + μ ≠ 0 := by
    intro h
    apply hμ1
    linear_combination h - h2
  have hZ1 : ∀ β : K, β ≠ 0 → Q 0 0 (β - c₀) := by
    intro β hβ
    have h3 := hmul _ _ _ _ _ _ (hmul _ _ _ _ _ _ (hall 1 0 (Or.inl one_ne_zero))
      (hall 0 β (Or.inr hβ))) (hinv _ _ _ (hall 1 β (Or.inl one_ne_zero)))
    exact of_eq3 h3 (by ring) (by ring) (by linear_combination c₀ * h2)
  have hZ2 : Q 0 0 (-c₀) := by
    have h3 := hmul _ _ _ _ _ _ (hmul _ _ _ _ _ _ (hall 1 0 (Or.inl one_ne_zero))
      (hall μ 0 (Or.inl hμ0))) (hinv _ _ _ (hall (1 + μ) 0 (Or.inl hμ')))
    exact of_eq3 h3 (by ring) (by ring) (by linear_combination c₀ * h2)
  have hZ : ∀ β : K, Q 0 0 β := by
    intro β
    by_cases hβ : β = 0
    · subst hβ
      exact of_eq3 (hmul _ _ _ _ _ _ hZ2 (hinv _ _ _ hZ2)) (by ring) (by ring) (by ring)
    · exact of_eq3 (hmul _ _ _ _ _ _ (hZ1 β hβ) (hinv _ _ _ hZ2)) (by ring) (by ring)
        (by ring)
  intro a b c
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact hZ c
  · have hab' : a ≠ 0 ∨ b ≠ 0 := by tauto
    exact of_eq3 (hmul _ _ _ _ _ _ (hall a b hab') (hZ (c - c₀))) (by ring) (by ring) (by ring)

theorem commute_of_fix_spE [Fintype K] (hK : Fintype.card K = 4) {Lb Wb : Subgroup (GL V₄ K)}
    (hLS : Lb ≤ StatedSp 2 K) (hWS : Wb ≤ StatedSp 2 K) (hperf : ⁅Lb, Lb⁆ = Lb)
    (h60 : ∀ N : Subgroup (GL V₄ K), N ≤ Lb → Lb ≤ Subgroup.normalizer (N : Set (GL V₄ K)) →
      IsPGroup 2 N → 60 ≤ N.relIndex Lb)
    (hW2 : IsPGroup 2 Wb) (hW16 : Nat.card Wb ≤ 16)
    (hLW : Lb ≤ Subgroup.normalizer (Wb : Set (GL V₄ K)))
    (hL : ∀ l ∈ Lb, ∃ c : K, (l : Matrix V₄ V₄ K) *ᵥ spE = c • spE)
    (hW : ∀ w ∈ Wb, (w : Matrix V₄ V₄ K) *ᵥ spE = spE) :
    ∀ w ∈ Wb, ∀ l ∈ Lb, w * l = l * w := by
  have := charP_two_of_card_four hK
  set P := lineStabE (StatedSp 2 K) with hP
  have hLP : Lb ≤ P := fun l hl => ⟨hLS hl, hL l hl⟩
  have hWP : Wb ≤ P := fun w hw => ⟨hWS hw, 1, by rw [one_smul]; exact hW w hw⟩
  set f := spBlockHom (le_refl (StatedSp 2 K)) with hf
  have hLe : ∀ l ∈ Lb, (l : Matrix V₄ V₄ K) *ᵥ spE = spE := by
    intro l hl
    have h1 := eq_one_of_perfect hperf ((scalarHomE (StatedSp 2 K)).comp
      (Subgroup.inclusion hLP)) ⟨l, hl⟩
    have h3 := congrArg (fun u : Kˣ => (u : K)) h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, scalarHomE_apply, Units.val_one] at h3
    have h2 := mulVec_spE_eq (⟨l, hLP hl⟩ : ↥P)
    simp only at h2
    rw [h2]
    change (l : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) • spE = spE at *
    rw [show (l : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) = 1 from h3, one_smul]
  set fL := f.comp (Subgroup.inclusion hLP) with hfL
  have hkerL : IsPGroup 2 fL.ker := by
    rintro ⟨⟨k, hk⟩, hker⟩
    refine ⟨1, ?_⟩
    have hb : spBlock (k : Matrix V₄ V₄ K) = 1 := by
      have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
        (MonoidHom.mem_ker.mp hker)
      simpa [hfL, hf, coe_spBlockHom] using this
    have hk2 := eq_heis_of_fix (hLS hk) (hLe k hk) hb
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_two, hk2, heis_mul_self]
  have hsurj : Function.Surjective fL :=
    surjective_of_isPGroup_ker h60 fL hkerL (by rw [card_sl2_of_card_four hK])
  set fW := f.comp (Subgroup.inclusion hWP) with hfW
  have hN : fW.range = ⊥ := by
    refine eq_bot_of_isPGroup_two (hW2.of_surjective fW.rangeRestrict
      fW.rangeRestrict_surjective) ?_
    rintro m _ ⟨w, rfl⟩
    obtain ⟨l, rfl⟩ := hsurj m
    have hlw : (l : GL V₄ K) * w * (l : GL V₄ K)⁻¹ ∈ Wb :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) w).mp w.2
    refine ⟨⟨_, hlw⟩, ?_⟩
    rw [hfW, hfL, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
  have hWb : ∀ w ∈ Wb, spBlock (w : Matrix V₄ V₄ K) = 1 := by
    intro w hw
    have h1 : fW ⟨w, hw⟩ ∈ fW.range := ⟨_, rfl⟩
    rw [hN, Subgroup.mem_bot] at h1
    have h2 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h1
    simpa [hfW, hf, coe_spBlockHom] using h2
  have hWh : ∀ w ∈ Wb, ∃ a b c : K, w = heis a b c := fun w hw =>
    ⟨_, _, _, eq_heis_of_fix (hWS hw) (hW w hw) (hWb w hw)⟩
  set Q : K → K → K → Prop := fun a b c => heis a b c ∈ Wb with hQ
  have hmul : ∀ a b c a' b' c', Q a b c → Q a' b' c' →
      Q (a + a') (b + b') (c + c' + a * b' - a' * b) := by
    intro a b c a' b' c' h h'
    have := Wb.mul_mem h h'
    rwa [heis_mul] at this
  have hinv : ∀ a b c, Q a b c → Q (-a) (-b) (-c) := by
    intro a b c h
    have := Wb.inv_mem h
    rwa [heis_inv] at this
  have hconj : ∀ a b c, Q a b c → ∀ m : SL(2, K),
      Q (a * (m : Matrix (Fin 2) (Fin 2) K) 0 0 + b * (m : Matrix (Fin 2) (Fin 2) K) 1 0)
        (a * (m : Matrix (Fin 2) (Fin 2) K) 0 1 + b * (m : Matrix (Fin 2) (Fin 2) K) 1 1) c := by
    intro a b c h m
    obtain ⟨l, hl⟩ := hsurj m⁻¹
    have hm : spBlock (((l : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        (m : Matrix (Fin 2) (Fin 2) K) := by
      have h1 : fL l⁻¹ = m := by rw [map_inv, hl, inv_inv]
      have h3 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h1
      rw [hfL, MonoidHom.comp_apply, hf, coe_spBlockHom] at h3
      exact h3
    have hc := (Subgroup.mem_normalizer_iff.mp (hLW l.2) _).mp h
    rw [conj_heis (hLS l.2) (hLe l l.2), hm] at hc
    exact hc
  have hab : ∀ a b c, Q a b c → a = 0 ∧ b = 0 := by
    intro a b c h
    by_contra hne
    have hne' : a ≠ 0 ∨ b ≠ 0 := by tauto
    have hall := heis_all hK Q hmul hinv hconj h hne'
    have hinj : Function.Injective (fun x : K × K × K => (⟨heis x.1 x.2.1 x.2.2,
        hall x.1 x.2.1 x.2.2⟩ : ↥Wb)) := by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ he
      obtain ⟨h1, h2, h3⟩ := heis_inj (congrArg Subtype.val he)
      exact Prod.ext h1 (Prod.ext h2 h3)
    have hc := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, hK] at hc
    omega
  intro w hw l hl
  obtain ⟨a, b, c, rfl⟩ := hWh w hw
  obtain ⟨rfl, rfl⟩ := hab a b c hw
  have h1 := conj_spTrans (hLS hl) spE (-c)
  rw [hLe l hl, ← heis_zero_zero] at h1
  calc heis 0 0 c * l = l * heis 0 0 c * l⁻¹ * l := by rw [h1]
    _ = l * heis 0 0 c := by group

end CFSG.Quasithin.H13.Ch9.Sp4B
