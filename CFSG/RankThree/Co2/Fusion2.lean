module

public import CFSG.RankThree.Co2.Fusion
public import CFSG.RankThree.Co2.JOrbits

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

abbrev M : Subgroup G := Subgroup.normalizer (h.JG : Set G)

theorem φ_symm_mem_JG {y : Cr} (hy : y ∈ subW jWords) : ((h.φ.symm y : h.H) : G) ∈ h.JG :=
  (h.mem_JG).2 ⟨y, hy, rfl⟩

theorem mem_Ω_iff {y : Cr} (hy : y ∈ subW jWords) :
    ((h.φ.symm y : h.H) : G) ∈ h.Ω ↔ InOmega y := by
  have key := h.isConj_z_iff (h.φ.symm y)
  rw [MulEquiv.apply_symm_apply] at key
  constructor
  · rintro ⟨-, hz⟩
    rcases key.1 hz with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e.symm)
    · exact Or.inr (Or.inr e.symm)
  · intro hy'
    refine ⟨h.φ_symm_mem_JG hy, key.2 ?_⟩
    rcases hy' with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e.symm)
    · exact Or.inr (Or.inr e.symm)

theorem conj_mem_Ω {m : G} (hm : m ∈ h.M) {t : G} (ht : t ∈ h.Ω) : m * t * m⁻¹ ∈ h.Ω :=
  ⟨(Subgroup.mem_normalizer_iff.1 hm t).1 ht.1, ht.2.trans (isConj_iff.2 ⟨m, rfl⟩)⟩

@[expose] def nG (x : G) : ℕ := Nat.card {t : h.Ω // (t : G) * x ∈ h.Ω}

theorem nG_conj {m : G} (hm : m ∈ h.M) (x : G) : h.nG (m * x * m⁻¹) = h.nG x := by
  have hm' : m⁻¹ ∈ h.M := (h.M).inv_mem hm
  symm
  refine Nat.card_congr
    { toFun := fun t => ⟨⟨m * t * m⁻¹, h.conj_mem_Ω hm t.1.2⟩, ?_⟩
      invFun := fun t => ⟨⟨m⁻¹ * t * m⁻¹⁻¹, h.conj_mem_Ω hm' t.1.2⟩, ?_⟩
      left_inv := fun t => ?_
      right_inv := fun t => ?_ }
  · have := h.conj_mem_Ω hm t.2
    have e : m * (t : G) * m⁻¹ * (m * x * m⁻¹) = m * ((t : G) * x) * m⁻¹ := by group
    rw [e]
    exact this
  · have := h.conj_mem_Ω hm' t.2
    have e : m⁻¹ * (t : G) * m⁻¹⁻¹ * x = m⁻¹ * ((t : G) * (m * x * m⁻¹)) * m⁻¹⁻¹ := by group
    rw [e]
    exact this
  · apply Subtype.ext; apply Subtype.ext
    change m⁻¹ * (m * (t : G) * m⁻¹) * m⁻¹⁻¹ = t
    group
  · apply Subtype.ext; apply Subtype.ext
    change m * (m⁻¹ * (t : G) * m⁻¹⁻¹) * m⁻¹ = t
    group

abbrev liftJ (j : subW jWords) : G := ((h.φ.symm (j : Cr) : h.H) : G)

theorem liftJ_injective : Function.Injective h.liftJ :=
  fun _ _ e => Subtype.ext (h.φ.symm.injective (Subtype.ext e))

theorem liftJ_mul (a b : subW jWords) : h.liftJ a * h.liftJ b = h.liftJ (a * b) :=
  congrArg Subtype.val (map_mul h.φ.symm (a : Cr) b).symm

theorem mem_JG_iff_liftJ {x : G} : x ∈ h.JG ↔ ∃ j, h.liftJ j = x := by
  rw [h.mem_JG]
  exact ⟨fun ⟨j, hj, e⟩ => ⟨⟨j, hj⟩, e⟩, fun ⟨j, e⟩ => ⟨j, j.2, e⟩⟩

theorem nG_eq (y : subW jWords) :
    h.nG (h.liftJ y) = Nat.card {t : subW jWords // InOmega (t : Cr) ∧ InOmega ((t : Cr) * y)} := by
  rw [nG]
  have e1 : Nat.card {t : h.Ω // (t : G) * h.liftJ y ∈ h.Ω} =
      Nat.card ↥{t : G | t ∈ h.Ω ∧ t * h.liftJ y ∈ h.Ω} :=
    Nat.card_congr
      { toFun := fun t => ⟨t.1.1, t.1.2, t.2⟩
        invFun := fun t => ⟨⟨t.1, t.2.1⟩, t.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have e2 : {t : G | t ∈ h.Ω ∧ t * h.liftJ y ∈ h.Ω} =
      h.liftJ '' {j | InOmega (j : Cr) ∧ InOmega ((j : Cr) * y)} := by
    ext t
    constructor
    · rintro ⟨ht, hty⟩
      obtain ⟨j, rfl⟩ := (h.mem_JG_iff_liftJ).1 ht.1
      refine ⟨j, ⟨(h.mem_Ω_iff j.2).1 ht, ?_⟩, rfl⟩
      rw [h.liftJ_mul] at hty
      exact (h.mem_Ω_iff (j * y).2).1 hty
    · rintro ⟨j, ⟨hj, hjy⟩, rfl⟩
      refine ⟨(h.mem_Ω_iff j.2).2 hj, ?_⟩
      rw [h.liftJ_mul]
      exact (h.mem_Ω_iff (j * y).2).2 hjy
  rw [e1, e2, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ h.liftJ_injective,
    ← Nat.card_coe_set_eq]
  rfl

theorem card_Ω : Nat.card h.Ω = 77 := by
  rw [h.card_Ω_eq]
  have e : Nat.card {y : subW jWords // IsConj h.z ((h.φ.symm (y : Cr) : h.H) : G)} =
      Nat.card {y : subW jWords // InOmega (y : Cr)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [← h.mem_Ω_iff y.2]
      exact ⟨fun hz => ⟨h.φ_symm_mem_JG y.2, hz⟩, fun hz => hz.2⟩)
  rw [e]
  exact card_Omega

theorem exists_eleven : ∃ s ∈ h.M, orderOf s = 11 ∧ ∀ v ∈ h.JG, s * v = v * s → v = 1 := by
  have := h.finite
  have hdvd : 11 ∣ Nat.card h.M := by
    have := h.card_Ω_dvd
    rw [h.card_Ω] at this
    exact (Dvd.intro_left 7 rfl).trans this
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 11 hdvd
  have hs' : orderOf (s : G) = 11 := by rwa [Subgroup.orderOf_coe]
  refine ⟨s, s.2, hs', ?_⟩
  rcases centralizes_or_fixed_trivial (V := h.JG) (by norm_num) hs' s.2
      (by rw [h.card_JG]; norm_num) (a := 10) (by
        intro c hc1 hc2
        interval_cases c <;> norm_num) with hc | hc
  · exact (h.not_mem_H_of_prime hs' (by norm_num) (hc h.z h.z_mem_JG)).elim
  · exact hc

@[expose] def orbitM (x : G) : Set G := {y | ∃ m ∈ h.M, m * x * m⁻¹ = y}

theorem orbitM_subset_JG {x : G} (hx : x ∈ h.JG) : h.orbitM x ⊆ h.JG := by
  rintro _ ⟨m, hm, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hm x).1 hx

theorem nG_of_mem_orbitM {x y : G} (hy : y ∈ h.orbitM x) : h.nG y = h.nG x := by
  obtain ⟨m, hm, rfl⟩ := hy
  exact h.nG_conj hm x

theorem orbitM_trans {x y w : G} (hy : y ∈ h.orbitM x) (hw : w ∈ h.orbitM y) :
    w ∈ h.orbitM x := by
  obtain ⟨m, hm, rfl⟩ := hy
  obtain ⟨m', hm', rfl⟩ := hw
  exact ⟨m' * m, (h.M).mul_mem hm' hm, by group⟩

theorem self_mem_orbitM (x : G) : x ∈ h.orbitM x := ⟨1, (h.M).one_mem, by group⟩

theorem dvd_card_orbitM {x : G} (hx : x ∈ h.JG) (hx1 : x ≠ 1) : 11 ∣ Nat.card (h.orbitM x) := by
  have := h.finite
  obtain ⟨s, hsM, hs, hfix⟩ := h.exists_eleven
  set K := Subgroup.zpowers s
  have hKM : K ≤ h.M := by rw [Subgroup.zpowers_le]; exact hsM
  have hcl : ∀ k ∈ K, ∀ y ∈ h.orbitM x, k * y * k⁻¹ ∈ h.orbitM x := fun k hk y hy =>
    h.orbitM_trans hy ⟨k, hKM hk, rfl⟩
  letI : MulAction K (h.orbitM x) :=
    { smul := fun k y => ⟨(k : G) * y * (k : G)⁻¹, hcl k k.2 y y.2⟩
      one_smul := fun y => by apply Subtype.ext; change (1 : G) * y * 1⁻¹ = y; group
      mul_smul := fun k l y => by
        apply Subtype.ext
        change ((k : G) * l) * y * ((k : G) * l)⁻¹ = k * (l * y * (l : G)⁻¹) * (k : G)⁻¹
        group }
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hKp : IsPGroup 11 K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  apply dvd_card_of_no_fixed hKp
  intro y
  refine ⟨⟨s, Subgroup.mem_zpowers s⟩, fun e => ?_⟩
  have e' : s * (y : G) * s⁻¹ = y := congrArg Subtype.val e
  have hyJ : (y : G) ∈ h.JG := h.orbitM_subset_JG hx y.2
  have hy1 := hfix y hyJ (by
    calc s * (y : G) = s * y * s⁻¹ * s := by group
      _ = y * s := by rw [e'])
  obtain ⟨m, -, hm⟩ := y.2
  apply hx1
  calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
    _ = 1 := by rw [hm, hy1]; group

@[expose] def piece (c : ℕ) : Set G :=
  {y | ∃ j ∈ subW jWords, IsConj (rep c) j ∧ ((h.φ.symm j : h.H) : G) = y}

theorem piece_eq (c : ℕ) :
    h.piece c = h.liftJ '' {j | IsConj (rep c) (j : Cr)} := by
  ext y
  constructor
  · rintro ⟨j, hj, hcj, rfl⟩
    exact ⟨⟨j, hj⟩, hcj, rfl⟩
  · rintro ⟨j, hcj, rfl⟩
    exact ⟨j, j.2, hcj, rfl⟩

theorem card_piece (c : ℕ) :
    Nat.card (h.piece c) = Nat.card {j : subW jWords // IsConj (rep c) (j : Cr)} := by
  rw [h.piece_eq, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ h.liftJ_injective, ← Nat.card_coe_set_eq]
  rfl

theorem piece_subset_orbitM {c : ℕ} {x y y' : G} (hy : y ∈ h.piece c) (hy' : y' ∈ h.piece c)
    (hyx : y ∈ h.orbitM x) : y' ∈ h.orbitM x := by
  obtain ⟨j, hj, hcj, rfl⟩ := hy
  obtain ⟨j', hj', hcj', rfl⟩ := hy'
  haveI := h.finite
  obtain ⟨m, hm, e⟩ := exists_normalizer_conj_of_mem_J hj hj' (hcj.symm.trans hcj')
  refine h.orbitM_trans hyx ⟨((h.φ.symm m : h.H) : G), ?_, ?_⟩
  · apply mem_normalizer_of_conj_mem
    intro w hw
    obtain ⟨u, hu, rfl⟩ := (h.mem_JG).1 hw
    rw [h.mem_JG]
    refine ⟨m * u * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm u).1 hu, ?_⟩
    simp
  · rw [← e]
    simp

theorem piece_disjoint {c c' : ℕ} (hc : c < 10) (hc' : c' < 10)
    (hne : classSizes[c]! ≠ classSizes[c']!) {y : G} (hy : y ∈ h.piece c)
    (hy' : y ∈ h.piece c') : False := by
  obtain ⟨j, -, hcj, rfl⟩ := hy
  obtain ⟨j', -, hcj', e⟩ := hy'
  have hjj : j' = j := h.φ.symm.injective (Subtype.ext e)
  rw [hjj] at hcj'
  have hcc := hcj.trans hcj'.symm
  obtain ⟨g, hg⟩ := isConj_iff.1 hcc
  apply hne
  have h1 := card_centralizer_rep hc
  have h2 := card_centralizer_rep hc'
  have hcard : Nat.card (Subgroup.centralizer ({rep c} : Set Cr)) =
      Nat.card (Subgroup.centralizer ({rep c'} : Set Cr)) := by
    rw [← hg]
    exact Nat.card_congr (centralizerConjEquiv g (rep c)).toEquiv
  rw [hcard] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem nG_piece_one_three_five {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5) {y : G}
    (hy : y ∈ h.piece c) : h.nG y = 14 := by
  obtain ⟨j, hj, hcj, rfl⟩ := hy
  refine (h.nG_eq ⟨j, hj⟩).trans (card_pairs_one_three_five _ ?_)
  rcases hc with rfl | rfl | rfl
  · exact Or.inl hcj
  · exact Or.inr (Or.inl hcj)
  · exact Or.inr (Or.inr hcj)

theorem nG_piece_four_six_eight {c : ℕ} (hc : c = 4 ∨ c = 6 ∨ c = 8) {y : G}
    (hy : y ∈ h.piece c) : h.nG y = 2 := by
  obtain ⟨j, hj, hcj, rfl⟩ := hy
  refine (h.nG_eq ⟨j, hj⟩).trans (card_pairs_four_six_eight _ ?_)
  rcases hc with rfl | rfl | rfl
  · exact Or.inl hcj
  · exact Or.inr (Or.inl hcj)
  · exact Or.inr (Or.inr hcj)

theorem mem_Ω_or_piece {y : G} (hy : y ∈ h.JG) (hy1 : y ≠ 1) :
    y ∈ h.Ω ∨ y ∈ h.piece 1 ∨ y ∈ h.piece 3 ∨ y ∈ h.piece 5 ∨ y ∈ h.piece 4 ∨
      y ∈ h.piece 6 ∨ y ∈ h.piece 8 := by
  obtain ⟨j, hj, rfl⟩ := (h.mem_JG).1 hy
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [map_one]; rfl)
  obtain ⟨c, hc, hjc⟩ := exists_isConj_rep j (elemTwo_J.1 j hj) hj1
  have hcj := hjc.symm
  have hpiece : ∀ c', c' = c → ((h.φ.symm j : h.H) : G) ∈ h.piece c' := by
    rintro c' rfl
    exact ⟨j, hj, hcj, rfl⟩
  interval_cases c
  · left
    rw [h.mem_Ω_iff hj]
    left
    rw [rep_zero] at hcj
    obtain ⟨g, hg⟩ := isConj_iff.1 hcj
    rw [← hg, conj_rCr]
  · exact Or.inr (Or.inl (hpiece 1 rfl))
  · left
    rw [h.mem_Ω_iff hj]
    exact Or.inr (Or.inl hcj)
  · exact Or.inr (Or.inr (Or.inl (hpiece 3 rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpiece 4 rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hpiece 5 rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpiece 6 rfl))))))
  · left
    rw [h.mem_Ω_iff hj]
    exact Or.inr (Or.inr hcj)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hpiece 8 rfl))))))
  · exact absurd hcj (not_isConj_rep_nine_of_mem_J hj)

theorem nG_Ω {y : G} (hy : y ∈ h.Ω) : h.nG y = 0 := by
  obtain ⟨j, hj, rfl⟩ := (h.mem_JG).1 hy.1
  exact (h.nG_eq ⟨j, hj⟩).trans (card_pairs_omega _ ((h.mem_Ω_iff hj).1 hy))

theorem piece_finite (c : ℕ) : (h.piece c).Finite := by
  have := h.finite
  exact Set.toFinite _

theorem card_union_of_disjoint {A B : Set G} (hd : ∀ y, y ∈ A → y ∈ B → False)
    (hA : A.Finite) (hB : B.Finite) : Nat.card ↥(A ∪ B) = Nat.card A + Nat.card B := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_union_eq (Set.disjoint_left.2 fun y hA hB => hd y hA hB) hA hB

theorem sizes_ne {c c' : ℕ} (hc : c < 10) (hc' : c' < 10)
    (hne : classSizes[c]! ≠ classSizes[c']!) : ∀ y, y ∈ h.piece c → y ∈ h.piece c' → False :=
  fun _ hy hy' => h.piece_disjoint hc hc' hne hy hy'

theorem pieces_one_three_five {x : G} (hx : x ∈ h.piece 1) :
    h.piece 3 ⊆ h.orbitM x ∧ h.piece 5 ⊆ h.orbitM x := by
  have hxJ : x ∈ h.JG := by
    obtain ⟨j, hj, -, rfl⟩ := hx
    exact h.φ_symm_mem_JG hj
  have hx1 : x ≠ 1 := by
    intro e
    have h14 := h.nG_piece_one_three_five (Or.inl rfl) hx
    rw [e] at h14 hx
    obtain ⟨j, hj, hcj, e'⟩ := hx
    have : j = 1 := (MulEquiv.map_eq_one_iff h.φ.symm).1 (Subtype.ext e')
    rw [this] at hcj
    exact rep_ne_one (by norm_num) (isConj_one_left.1 hcj)
  set O := h.orbitM x
  have hsub : ∀ y ∈ O, y ∈ h.piece 1 ∨ y ∈ h.piece 3 ∨ y ∈ h.piece 5 := by
    intro y hy
    have hyJ := h.orbitM_subset_JG hxJ hy
    have hy1 : y ≠ 1 := by
      obtain ⟨m, -, rfl⟩ := hy
      intro e
      apply hx1
      calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
        _ = 1 := by rw [e]; group
    have hn : h.nG y = 14 := by
      rw [h.nG_of_mem_orbitM hy]
      exact h.nG_piece_one_three_five (Or.inl rfl) hx
    rcases h.mem_Ω_or_piece hyJ hy1 with hΩ | h1 | h3 | h5 | h4 | h6 | h8
    · rw [h.nG_Ω hΩ] at hn; omega
    · exact Or.inl h1
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h5)
    · rw [h.nG_piece_four_six_eight (Or.inl rfl) h4] at hn; omega
    · rw [h.nG_piece_four_six_eight (Or.inr (Or.inl rfl)) h6] at hn; omega
    · rw [h.nG_piece_four_six_eight (Or.inr (Or.inr rfl)) h8] at hn; omega
  have h1O : h.piece 1 ⊆ O := fun y hy => h.piece_subset_orbitM hx hy (h.self_mem_orbitM x)
  have hall : ∀ c, (∃ y ∈ h.piece c, y ∈ O) → h.piece c ⊆ O := by
    rintro c ⟨y, hy, hyO⟩ y' hy'
    exact h.piece_subset_orbitM hy hy' hyO
  have hdvd : 11 ∣ Nat.card O := h.dvd_card_orbitM hxJ hx1
  have hc1 : Nat.card (h.piece 1) = 30 := by
    rw [h.card_piece 1]; exact card_J_class_one
  have hc3 : Nat.card (h.piece 3) = 60 := by
    rw [h.card_piece 3]; exact card_J_class_three
  have hc5 : Nat.card (h.piece 5) = 240 := by
    rw [h.card_piece 5]; exact card_J_class_five
  have d13 := h.sizes_ne (c := 1) (c' := 3) (by norm_num) (by norm_num) (by decide)
  have d15 := h.sizes_ne (c := 1) (c' := 5) (by norm_num) (by norm_num) (by decide)
  have d35 := h.sizes_ne (c := 3) (c' := 5) (by norm_num) (by norm_num) (by decide)
  have fin := h.piece_finite
  by_cases h3 : ∃ y ∈ h.piece 3, y ∈ O <;> by_cases h5 : ∃ y ∈ h.piece 5, y ∈ O
  · exact ⟨hall 3 h3, hall 5 h5⟩
  · exfalso
    push Not at h5
    have hO : O = h.piece 1 ∪ h.piece 3 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr hy
        · exact (h5 y hy hyO).elim
      · rintro (hy | hy)
        · exact h1O hy
        · exact hall 3 h3 hy
    rw [hO, card_union_of_disjoint d13 (fin 1) (fin 3), hc1, hc3] at hdvd
    omega
  · exfalso
    push Not at h3
    have hO : O = h.piece 1 ∪ h.piece 5 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact Or.inl hy
        · exact (h3 y hy hyO).elim
        · exact Or.inr hy
      · rintro (hy | hy)
        · exact h1O hy
        · exact hall 5 h5 hy
    rw [hO, card_union_of_disjoint d15 (fin 1) (fin 5), hc1, hc5] at hdvd
    omega
  · exfalso
    push Not at h3 h5
    have hO : O = h.piece 1 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact hy
        · exact (h3 y hy hyO).elim
        · exact (h5 y hy hyO).elim
      · intro hy
        exact h1O hy
    rw [hO, hc1] at hdvd
    omega

theorem pieces_eight_four_six {x : G} (hx : x ∈ h.piece 8) :
    h.piece 4 ⊆ h.orbitM x ∧ h.piece 6 ⊆ h.orbitM x := by
  have hxJ : x ∈ h.JG := by
    obtain ⟨j, hj, -, rfl⟩ := hx
    exact h.φ_symm_mem_JG hj
  have hx1 : x ≠ 1 := by
    intro e
    rw [e] at hx
    obtain ⟨j, hj, hcj, e'⟩ := hx
    have : j = 1 := (MulEquiv.map_eq_one_iff h.φ.symm).1 (Subtype.ext e')
    rw [this] at hcj
    exact rep_ne_one (by norm_num) (isConj_one_left.1 hcj)
  set O := h.orbitM x
  have hsub : ∀ y ∈ O, y ∈ h.piece 4 ∨ y ∈ h.piece 6 ∨ y ∈ h.piece 8 := by
    intro y hy
    have hyJ := h.orbitM_subset_JG hxJ hy
    have hy1 : y ≠ 1 := by
      obtain ⟨m, -, rfl⟩ := hy
      intro e
      apply hx1
      calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
        _ = 1 := by rw [e]; group
    have hn : h.nG y = 2 := by
      rw [h.nG_of_mem_orbitM hy]
      exact h.nG_piece_four_six_eight (Or.inr (Or.inr rfl)) hx
    rcases h.mem_Ω_or_piece hyJ hy1 with hΩ | h1 | h3 | h5 | h4 | h6 | h8
    · rw [h.nG_Ω hΩ] at hn; omega
    · rw [h.nG_piece_one_three_five (Or.inl rfl) h1] at hn; omega
    · rw [h.nG_piece_one_three_five (Or.inr (Or.inl rfl)) h3] at hn; omega
    · rw [h.nG_piece_one_three_five (Or.inr (Or.inr rfl)) h5] at hn; omega
    · exact Or.inl h4
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr h8)
  have h8O : h.piece 8 ⊆ O := fun y hy => h.piece_subset_orbitM hx hy (h.self_mem_orbitM x)
  have hall : ∀ c, (∃ y ∈ h.piece c, y ∈ O) → h.piece c ⊆ O := by
    rintro c ⟨y, hy, hyO⟩ y' hy'
    exact h.piece_subset_orbitM hy hy' hyO
  have hdvd : 11 ∣ Nat.card O := h.dvd_card_orbitM hxJ hx1
  have hc4 : Nat.card (h.piece 4) = 360 := by
    rw [h.card_piece 4]; exact card_J_class_four
  have hc6 : Nat.card (h.piece 6) = 240 := by
    rw [h.card_piece 6]; exact card_J_class_six
  have hc8 : Nat.card (h.piece 8) = 16 := by
    rw [h.card_piece 8]; exact card_J_class_eight
  have d84 := h.sizes_ne (c := 8) (c' := 4) (by norm_num) (by norm_num) (by decide)
  have d86 := h.sizes_ne (c := 8) (c' := 6) (by norm_num) (by norm_num) (by decide)
  have fin := h.piece_finite
  by_cases h4 : ∃ y ∈ h.piece 4, y ∈ O <;> by_cases h6 : ∃ y ∈ h.piece 6, y ∈ O
  · exact ⟨hall 4 h4, hall 6 h6⟩
  · exfalso
    push Not at h6
    have hO : O = h.piece 8 ∪ h.piece 4 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact Or.inr hy
        · exact (h6 y hy hyO).elim
        · exact Or.inl hy
      · rintro (hy | hy)
        · exact h8O hy
        · exact hall 4 h4 hy
    rw [hO, card_union_of_disjoint d84 (fin 8) (fin 4), hc8, hc4] at hdvd
    omega
  · exfalso
    push Not at h4
    have hO : O = h.piece 8 ∪ h.piece 6 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact (h4 y hy hyO).elim
        · exact Or.inr hy
        · exact Or.inl hy
      · rintro (hy | hy)
        · exact h8O hy
        · exact hall 6 h6 hy
    rw [hO, card_union_of_disjoint d86 (fin 8) (fin 6), hc8, hc6] at hdvd
    omega
  · exfalso
    push Not at h4 h6
    have hO : O = h.piece 8 := by
      ext y
      constructor
      · intro hyO
        rcases hsub y hyO with hy | hy | hy
        · exact (h4 y hy hyO).elim
        · exact (h6 y hy hyO).elim
        · exact hy
      · intro hy
        exact h8O hy
    rw [hO, hc8] at hdvd
    omega

theorem exists_mem_piece {c : ℕ}
    (hpos : 0 < Nat.card {j : subW jWords // IsConj (rep c) (j : Cr)}) : ∃ x, x ∈ h.piece c := by
  rw [← h.card_piece c] at hpos
  obtain ⟨⟨x, hx⟩⟩ := Nat.card_pos_iff.1 hpos |>.1
  exact ⟨x, hx⟩

theorem isConj_of_piece {c : ℕ} {y : G} (hy : y ∈ h.piece c) :
    IsConj ((h.φ.symm (rep c) : h.H) : G) y := by
  obtain ⟨j, -, hcj, rfl⟩ := hy
  exact h.isConj_φ_symm hcj

theorem isConj_of_orbitM {x y : G} (hy : y ∈ h.orbitM x) : IsConj x y := by
  obtain ⟨m, -, rfl⟩ := hy
  exact isConj_iff.2 ⟨m, rfl⟩

theorem fuse_one_three_five :
    IsConj ((h.φ.symm (rep 1) : h.H) : G) ((h.φ.symm (rep 3) : h.H) : G) ∧
      IsConj ((h.φ.symm (rep 1) : h.H) : G) ((h.φ.symm (rep 5) : h.H) : G) := by
  obtain ⟨x, hx⟩ := h.exists_mem_piece (c := 1) (by rw [card_J_class_one]; norm_num)
  obtain ⟨y3, hy3⟩ := h.exists_mem_piece (c := 3) (by rw [card_J_class_three]; norm_num)
  obtain ⟨y5, hy5⟩ := h.exists_mem_piece (c := 5) (by rw [card_J_class_five]; norm_num)
  obtain ⟨h3, h5⟩ := h.pieces_one_three_five hx
  have hx' := h.isConj_of_piece hx
  exact ⟨(hx'.trans (h.isConj_of_orbitM (h3 hy3))).trans (h.isConj_of_piece hy3).symm,
    (hx'.trans (h.isConj_of_orbitM (h5 hy5))).trans (h.isConj_of_piece hy5).symm⟩

theorem fuse_eight_four_six :
    IsConj ((h.φ.symm (rep 8) : h.H) : G) ((h.φ.symm (rep 4) : h.H) : G) ∧
      IsConj ((h.φ.symm (rep 8) : h.H) : G) ((h.φ.symm (rep 6) : h.H) : G) := by
  obtain ⟨x, hx⟩ := h.exists_mem_piece (c := 8) (by rw [card_J_class_eight]; norm_num)
  obtain ⟨y4, hy4⟩ := h.exists_mem_piece (c := 4) (by rw [card_J_class_four]; norm_num)
  obtain ⟨y6, hy6⟩ := h.exists_mem_piece (c := 6) (by rw [card_J_class_six]; norm_num)
  obtain ⟨h4, h6⟩ := h.pieces_eight_four_six hx
  have hx' := h.isConj_of_piece hx
  exact ⟨(hx'.trans (h.isConj_of_orbitM (h4 hy4))).trans (h.isConj_of_piece hy4).symm,
    (hx'.trans (h.isConj_of_orbitM (h6 hy6))).trans (h.isConj_of_piece hy6).symm⟩

end Co2CentHyp

end CFSG.RankThree.Co2
