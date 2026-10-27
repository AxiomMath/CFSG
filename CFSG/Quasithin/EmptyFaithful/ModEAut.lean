module

public import CFSG.Quasithin.EmptyFaithful.ModEGrp
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.Quasithin.ModE

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem ga_eq : ga = m12A1 := by decide +kernel

theorem gb_eq : gb = m12B1 := by decide +kernel

theorem gs_eq : gs = m12Sigma := by decide +kernel

section Model

theorem ga_mem : ga ∈ autModel := by
  rw [ga_eq, autModel_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem gb_mem : gb ∈ autModel := by
  rw [gb_eq, autModel_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem gs_mem : gs ∈ autModel := by
  rw [gs_eq, autModel_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem lt_getD_mem (k : ℕ) : lt.getD k 1 ∈ autModel := by
  by_cases hk : k < 6
  · interval_cases k
    · exact ga_mem
    · exact gb_mem
    · exact gs_mem
    · exact autModel.inv_mem ga_mem
    · exact autModel.inv_mem gb_mem
    · exact autModel.inv_mem gs_mem
  · rw [List.getD_eq_default _ _ (by simp only [lt, List.length_cons, List.length_nil]; omega)]
    exact autModel.one_mem

theorem foldl_mem (w : List ℕ) (acc : P24) (hacc : acc ∈ autModel) :
    w.foldl (fun a k => a * lt.getD k 1) acc ∈ autModel := by
  induction w generalizing acc with
  | nil => exact hacc
  | cons k w ih =>
    rw [List.foldl_cons]
    exact ih _ (autModel.mul_mem hacc (lt_getD_mem k))

theorem wP_mem (w : List ℕ) : wP w ∈ autModel := by
  rw [wP]
  exact foldl_mem w 1 autModel.one_mem

theorem T0_le_autModel : T0 ≤ autModel := by
  rw [T0, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact wP_mem _
  · exact wP_mem _
  · exact wP_mem _

theorem g3P_mem_autModel : g3P ∈ autModel := wP_mem _

theorem lt_inv_getD : ∀ k < 6, lt.getD ((k + 3) % 6) 1 = (lt.getD k 1)⁻¹ := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact (inv_inv _).symm
  · exact (inv_inv _).symm
  · exact (inv_inv _).symm

theorem ysK_exists : ∀ c ∈ ysK, ∃ y, (∃ g ∈ autModel, y = g * z0P * g⁻¹) ∧ pk y = c := by
  have hmem : ∀ x ∈ lt, x ∈ autModel := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [← List.getD_eq_getElem _ 1 hi]
    exact lt_getD_mem i
  have h := chainC_spec lt rfl autModel hmem lt_inv_getD z0P tabC [zk]
    (by rw [pk_lt]; exact chainC0)
    (by
      intro c hc
      refine ⟨z0P, ⟨1, autModel.one_mem, by simp⟩, ?_⟩
      rw [pk_z0P]
      exact (List.mem_singleton.1 hc).symm)
  intro c hc
  rw [ysK_eq] at hc
  exact h c hc

@[expose] def cls0 : Set P24 := {y | ∃ g ∈ autModel, y = g * z0P * g⁻¹}

@[expose] def C0 : Subgroup P24 := autModel ⊓ Subgroup.centralizer {z0P}

theorem mem_C0 {g : P24} : g ∈ C0 ↔ g ∈ autModel ∧ g * z0P = z0P * g := by
  rw [C0, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h2 z0P rfl).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact h2.symm⟩

theorem card_cls0_ge : 495 ≤ Nat.card cls0 := by
  classical
  have hex := ysK_exists
  let ι : {c : ℕ // c ∈ ysK.toFinset} → cls0 := fun c =>
    ⟨Classical.choose (hex c.1 (List.mem_toFinset.1 c.2)),
      (Classical.choose_spec (hex c.1 (List.mem_toFinset.1 c.2))).1⟩
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    have h1 := (Classical.choose_spec (hex a.1 (List.mem_toFinset.1 a.2))).2
    have h2 := (Classical.choose_spec (hex b.1 (List.mem_toFinset.1 b.2))).2
    have h3 : Classical.choose (hex a.1 (List.mem_toFinset.1 a.2)) =
        Classical.choose (hex b.1 (List.mem_toFinset.1 b.2)) := congrArg Subtype.val hab
    rw [← h1, ← h2, h3]
  have h := Nat.card_le_card_of_injective ι hι
  have e : Nat.card {c : ℕ // c ∈ ysK.toFinset} = 495 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup (nodupB_iff.1 ysK_nodup), ysK_len]
  rw [e] at h
  exact h

theorem card_C0_le : Nat.card C0 ≤ 384 := by
  classical
  let Cg : Subgroup autModel := C0.subgroupOf autModel
  have hC0le : C0 ≤ autModel := inf_le_left
  have h1 : Nat.card Cg = Nat.card C0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC0le).toEquiv
  let h : (autModel ⧸ Cg) → cls0 := Quotient.lift
    (fun g : autModel => (⟨(g : P24) * z0P * (g : P24)⁻¹, g, g.2, rfl⟩ : cls0)) (by
      intro a b hab
      apply Subtype.ext
      have hab' : a⁻¹ * b ∈ Cg := QuotientGroup.leftRel_apply.1 hab
      have hc : (((a⁻¹ * b : autModel)) : P24) * z0P = z0P * (((a⁻¹ * b : autModel)) : P24) :=
        (mem_C0.1 (Subgroup.mem_subgroupOf.1 hab')).2
      have hc' : ((a : P24)⁻¹ * (b : P24)) * z0P = z0P * ((a : P24)⁻¹ * (b : P24)) := hc
      show (a : P24) * z0P * (a : P24)⁻¹ = (b : P24) * z0P * (b : P24)⁻¹
      have e1 : (b : P24) = (a : P24) * ((a : P24)⁻¹ * (b : P24)) := by group
      calc (a : P24) * z0P * (a : P24)⁻¹
          = (a : P24) * (z0P * ((a : P24)⁻¹ * (b : P24)) * ((a : P24)⁻¹ * (b : P24))⁻¹) * (a : P24)⁻¹ := by
            group
        _ = (a : P24) * (((a : P24)⁻¹ * (b : P24)) * z0P * ((a : P24)⁻¹ * (b : P24))⁻¹) * (a : P24)⁻¹ := by
            rw [← hc']
        _ = (b : P24) * z0P * (b : P24)⁻¹ := by group)
  have hsurj : Function.Surjective h := by
    rintro ⟨y, g, hg, rfl⟩
    exact ⟨(QuotientGroup.mk ⟨g, hg⟩ : autModel ⧸ Cg), rfl⟩
  have h2 : Nat.card cls0 ≤ Nat.card (autModel ⧸ Cg) := Nat.card_le_card_of_surjective h hsurj
  have h3 := Subgroup.card_mul_index Cg
  rw [card_autModel, h1] at h3
  have h4 : Cg.index = Nat.card (autModel ⧸ Cg) := rfl
  have h5 := card_cls0_ge
  have h6 : 495 ≤ Cg.index := by rw [h4]; exact h5.trans h2
  have h7 : Nat.card C0 * 495 ≤ Nat.card C0 * Cg.index := Nat.mul_le_mul_left _ h6
  have h8 : Nat.card C0 * 495 ≤ 384 * 495 := h7.trans (h3.trans (by norm_num)).le
  exact Nat.le_of_mul_le_mul_right h8 (by norm_num)

theorem fac_190080 : (190080 : ℕ).factorization 2 = 7 := by
  have h : (190080 : ℕ) = 2 ^ 7 * 1485 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 1485 by norm_num)]
  rfl

theorem fac_384 : (384 : ℕ).factorization 2 = 7 := by
  have h : (384 : ℕ) = 2 ^ 7 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  rfl

theorem exists_conj_T0 {T : Subgroup P24} (hT : T ≤ autModel) (hcard : Nat.card T = 128) :
    ∃ c ∈ autModel, ∀ x : P24, x ∈ T ↔ c⁻¹ * x * c ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card autModel).factorization 2 = 7 := by rw [card_autModel, fac_190080]
  have hc1 : Nat.card (T.subgroupOf autModel) = 2 ^ (Nat.card autModel).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, hcard, hfac]
    norm_num
  have hc2 : Nat.card (T0.subgroupOf autModel) = 2 ^ (Nat.card autModel).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_autModel).toEquiv, card_T0, hfac]
    norm_num
  let P : Sylow 2 autModel := Sylow.ofCard (T.subgroupOf autModel) hc1
  let Q : Sylow 2 autModel := Sylow.ofCard (T0.subgroupOf autModel) hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autModel Q P
  refine ⟨(g : P24), g.2, fun x => ?_⟩
  by_cases hx : x ∈ autModel
  · have key : (⟨x, hx⟩ : autModel) ∈ (P : Subgroup autModel) ↔
        g⁻¹ * (⟨x, hx⟩ : autModel) * g ∈ (Q : Subgroup autModel) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have e1 : (⟨x, hx⟩ : autModel) ∈ (P : Subgroup autModel) ↔ x ∈ T := Iff.rfl
    have e2 : g⁻¹ * (⟨x, hx⟩ : autModel) * g ∈ (Q : Subgroup autModel) ↔
        (g : P24)⁻¹ * x * (g : P24) ∈ T0 := Iff.rfl
    rw [← e1, ← e2]
    exact key
  · constructor
    · intro h
      exact absurd (hT h) hx
    · intro h
      exfalso
      apply hx
      have h1 := T0_le_autModel h
      have h2 := autModel.mul_mem (autModel.mul_mem g.2 h1) (autModel.inv_mem g.2)
      simpa [mul_assoc] using h2

theorem core_four (G₂ A : Subgroup P24) (z : P24) (hG₂ : G₂ ≤ autModel) (hTG : T0 ≤ G₂)
    (hcardG : Nat.card G₂ = 384) (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzT : z ∈ T0)
    (hzc : ∀ t ∈ T0, t * z = z * t) (hG₂z : ∀ g ∈ G₂, g * z = z * g) (hAG : A ≤ G₂)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hAn : ∀ g ∈ G₂, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hA16 : 16 ≤ Nat.card A) : False := by
  have hz : z = z0P := eq_z0P_of_central hz1 hz2 hzT hzc
  have hG₂z' : ∀ g ∈ G₂, g * z0P = z0P * g := fun g hg => hz ▸ hG₂z g hg
  have hG₂C : G₂ ≤ C0 := fun g hg => mem_C0.2 ⟨hG₂ hg, hG₂z' g hg⟩
  have hGC : G₂ = C0 := Subgroup.eq_of_le_of_card_ge hG₂C (by rw [hcardG]; exact card_C0_le)
  have hg3 : g3P ∈ G₂ := by
    rw [hGC]
    exact mem_C0.2 ⟨g3P_mem_autModel, g3P_comm⟩
  have hAT : ∀ a ∈ A, a ∈ T0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let N : Subgroup G₂ := A.subgroupOf G₂
    have hNn : N.Normal := ⟨fun n hn g => by
      have h1 := hAn g g.2 n (Subgroup.mem_subgroupOf.1 hn)
      exact Subgroup.mem_subgroupOf.2 (by simpa using h1)⟩
    have hNp : IsPGroup 2 N := fun x => ⟨1, by
      have h1 := hAsq x (Subgroup.mem_subgroupOf.1 x.2)
      have hx2 : x * x = 1 := Subtype.ext (Subtype.ext h1)
      rw [pow_one, pow_two]
      exact hx2⟩
    have hfac : (Nat.card G₂).factorization 2 = 7 := by rw [hcardG, fac_384]
    have hcard0 : Nat.card (T0.subgroupOf G₂) = 2 ^ (Nat.card G₂).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv, card_T0, hfac]
      norm_num
    let P₀ : Sylow 2 G₂ := Sylow.ofCard (T0.subgroupOf G₂) hcard0
    have hle := @IsPGroup.le_sylow_of_normal 2 G₂ _ N hNn hNp P₀
    intro a ha
    have h1 : (⟨a, hAG ha⟩ : G₂) ∈ N := Subgroup.mem_subgroupOf.2 ha
    exact Subgroup.mem_subgroupOf.1 (hle h1)
  have hqg : ∀ a ∈ A, pk a ∈ qgK := by
    intro a ha
    refine mem_qgK_of (hAT a ha) (hAT _ (hAn g3P hg3 a ha)) (hAT _ ?_)
    have := hAn g3P⁻¹ (G₂.inv_mem hg3) a ha
    simpa using this
  have hx : ∃ x ∈ A, x ≠ 1 ∧ x ≠ z0P := by
    by_contra hcon
    push Not at hcon
    have hsub : (A : Set P24) ⊆ {1, z0P} := fun a ha => by
      by_cases h1 : a = 1
      · exact Or.inl h1
      · exact Or.inr (hcon a ha h1)
    have h2 : Nat.card A ≤ 2 := by
      have e : Nat.card A = (A : Set P24).ncard := (Nat.card_coe_set_eq (A : Set P24)).symm
      rw [e]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  obtain ⟨x, hxA, hx1, hxz⟩ := hx
  have h12 := card_le_twelve A hxA hx1 hxz hqg hAsq (fun a ha => hAab x hxA a ha)
  omega

theorem conc_four (T G₂ A : Subgroup P24) (z : P24) (hT : T ≤ autModel) (hTcard : Nat.card T = 128)
    (hG₂ : G₂ ≤ autModel) (hTG : T ≤ G₂) (hidx : T.relIndex G₂ = 3) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzT : z ∈ T) (hzc : ∀ t ∈ T, t * z = z * t) (hG₂z : ∀ g ∈ G₂, g * z = z * g) (hAG : A ≤ G₂)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hAn : ∀ g ∈ G₂, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hA16 : 16 ≤ Nat.card A) : False := by
  obtain ⟨c, hc, hconj⟩ := exists_conj_T0 hT hTcard
  let φ : P24 →* P24 :=
    { toFun := fun x => c⁻¹ * x * c
      map_one' := by group
      map_mul' := fun x y => by group }
  have hφ : ∀ x, φ x = c⁻¹ * x * c := fun x => rfl
  have hφinj : Function.Injective φ := by
    intro x y h
    have h' : c⁻¹ * x * c = c⁻¹ * y * c := h
    exact mul_left_cancel (mul_right_cancel h')
  have hcard384 : Nat.card G₂ = 384 := by
    have h1 := Subgroup.index_mul_card (T.subgroupOf G₂)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv, hTcard] at h1
    have h2 : (T.subgroupOf G₂).index = 3 := hidx
    rw [h2] at h1
    omega
  have hmem : ∀ (X : Subgroup P24) (x : P24), x ∈ X.map φ ↔ c * x * c⁻¹ ∈ X := by
    intro X x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : c * φ y * c⁻¹ = y := by rw [hφ]; group
      rw [this]
      exact hy
    · intro hx
      exact ⟨c * x * c⁻¹, hx, by rw [hφ]; group⟩
  refine core_four (G₂.map φ) (A.map φ) (φ z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact autModel.mul_mem (autModel.mul_mem (autModel.inv_mem hc) (hG₂ hy)) hc
  · intro y hy
    rw [hmem]
    refine hTG ((hconj _).2 ?_)
    have : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [this]
    exact hy
  · rw [Subgroup.card_map_of_injective hφinj, hcard384]
  · intro h
    exact hz1 (hφinj (h.trans φ.map_one.symm))
  · rw [← map_mul, hz2, map_one]
  · exact (hconj z).1 hzT
  · intro t ht
    have hxT : c * t * c⁻¹ ∈ T := (hconj _).2 (by
      have : c⁻¹ * (c * t * c⁻¹) * c = t := by group
      rw [this]
      exact ht)
    have h1 := hzc _ hxT
    show t * (c⁻¹ * z * c) = (c⁻¹ * z * c) * t
    calc t * (c⁻¹ * z * c) = c⁻¹ * ((c * t * c⁻¹) * z) * c := by group
      _ = c⁻¹ * (z * (c * t * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * z * c) * t := by group
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [← map_mul, ← map_mul, hG₂z y hy]
  · exact Subgroup.map_mono hAG
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, hAab a' ha' b' hb']
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [← map_mul, hAsq a' ha', map_one]
  · intro g hg a ha
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨a', ha', rfl⟩ := ha
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hAn g' hg' a' ha', rfl⟩
  · rw [Subgroup.card_map_of_injective hφinj]
    exact hA16

end Model

end CFSG.Quasithin.ModE
