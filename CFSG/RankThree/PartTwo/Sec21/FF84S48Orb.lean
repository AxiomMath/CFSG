module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48Main

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

@[expose] def S47Swap (b : G) (B : Subgroup G) : Prop :=
  ∀ U ∈ PiStar (Cen b) B 2, ∃ g ∈ Nor B ⊓ Cen b, conjBy g U ≠ U

theorem conjBy_mul (y z : G) (H : Subgroup G) : conjBy (y * z) H = conjBy y (conjBy z H) := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff, mem_conjBy_iff]
  simp [mul_assoc]

theorem conjBy_inj {y : G} {A A' : Subgroup G} (h : conjBy y A = conjBy y A') : A = A' := by
  have := congrArg (conjBy y⁻¹) h
  rwa [conjBy_inv_conjBy, conjBy_inv_conjBy] at this

theorem mem_nor_iff_conjBy {g : G} {M : Subgroup G} : g ∈ Nor M ↔ conjBy g M = M := by
  constructor
  · intro h
    ext y
    rw [mem_conjBy_iff]
    have := Subgroup.mem_normalizer_iff.1 (inv_mem h) y
    simpa using this.symm
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h2 : ∀ y, y ∈ conjBy g M ↔ y ∈ M := fun y => by rw [h]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [← h2 (g * y * g⁻¹), mem_conjBy_iff, e]

theorem nor_sup_pt {H K : Subgroup G} {g : G} (hH : g ∈ Nor H) (hK : g ∈ Nor K) :
    g ∈ Nor (H ⊔ K) := by
  rw [mem_nor_iff_conjBy] at hH hK ⊢
  have : conjBy g (H ⊔ K) = conjBy g H ⊔ conjBy g K := by
    unfold conjBy; rw [Subgroup.map_sup]
  rw [this, hH, hK]

theorem mem_nor_top (g : G) : g ∈ Nor (⊤ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff]; intro h; simp

theorem le_nor_of_comm {T V : Subgroup G} (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hVT : V ≤ T) :
    T ≤ Nor V := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 := hT t ht h (hVT hh)
    have e : t * h * t⁻¹ = h := by rw [h1]; group
    rw [e]; exact hh
  · intro hh
    have h3 := hT t ht (t * h * t⁻¹) (hVT hh)
    have h4 : t * (t * h * t⁻¹) = t * h := by rw [h3]; group
    have e : t * h * t⁻¹ = h := mul_left_cancel h4
    rwa [e] at hh

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂)

include c

theorem card_S_cen {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) {z : G}
    (hz : z ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    EA2 (Op 2 (Nor U) ⊓ Cen z) ∧ Nat.card ↥(Op 2 (Nor U) ⊓ Cen z) = 16 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [S48_CSb c hU]; exact ⟨EA2.of_isElemAb (c.piU hU).1, c.piU_card hU⟩
  · rw [cen_inv, S48_CSb c hU]; exact ⟨EA2.of_isElemAb (c.piU hU).1, c.piU_card hU⟩
  · exact S_card_W c hU (Or.inl rfl)
  · rw [cen_inv]; exact S_card_W c hU (Or.inl rfl)
  · exact S_card_W c hU (Or.inr rfl)
  · rw [cen_inv]; exact S_card_W c hU (Or.inr rfl)

theorem orbit_key {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) {x : G} (hx : x ∈ Nor B) :
    (conjBy x (Op 2 (Nor U)) ⊓ Cen b) ∈ PiStar (Cen b) B 2 ∧
      conjBy x (Op 2 (Nor U)) = Op 2 (Nor (conjBy x (Op 2 (Nor U)) ⊓ Cen b)) := by
  obtain ⟨hEA6, hSPi⟩ := S48_elemab c hU
  set S := Op 2 (Nor U) with hSdef
  set T := conjBy x S with hT
  have hTPi : T ∈ PiStar ⊤ B 2 := piStar_conj (mem_nor_top x) hx hSPi
  have hTEA : EA2 T := (EA2.of_isElemAb hEA6).conj x
  set V := T ⊓ Cen b with hV
  have hBT : B ≤ Nor T := hTPi.2.2.1
  have hBV : B ≤ Nor V := B_nor_inf_cen c hU (mem_b c.sec) hBT
  have hVconj : V = conjBy x (S ⊓ Cen (x⁻¹ * b * x)) := by
    rw [conjBy_inf, conjBy_cen]
    have : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
    rw [this]
  have hVcard : Nat.card V = 16 := by
    have hzmem : x⁻¹ * b * x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := by
      have h3 := c.sec.mono.2.2.1 x⁻¹ (inv_mem hx) b (by simp)
      simpa using h3
    rw [hVconj, card_conjBy]
    exact (card_S_cen c hU hzmem).2
  have hVPi : V ∈ PiStar (Cen b) B 2 := by
    obtain ⟨Z, hZ, hVZ⟩ := exists_piStar_ge (A := B) (X := Cen b) (q := 2) (V := V) inf_le_right
      ((hTEA.mono inf_le_left).isPGroup) hBV
    have hZc := c.piU_card hZ
    have : V = Z := Subgroup.eq_of_le_of_card_ge hVZ (by omega)
    rw [this]; exact hZ
  refine ⟨hVPi, ?_⟩
  obtain ⟨-, hSVPi⟩ := S48_elemab c hVPi
  have hTV : T ≤ Nor V := le_nor_of_comm hTEA.1 inf_le_left
  have hTSV : T ≤ Nor (Op 2 (Nor V)) := hTV.trans (le_nor_op2 _)
  have hsup2 : IsPGroup 2 (T ⊔ Op 2 (Nor V) : Subgroup G) :=
    hTEA.isPGroup.to_sup_of_normal_right' (op2_isPGroup _) hTSV
  have hBsup : B ≤ Nor (T ⊔ Op 2 (Nor V)) := fun g hg =>
    nor_sup_pt (hBT hg) (B_le_nor_S c hVPi hg)
  have h1 : T ⊔ Op 2 (Nor V) = T := hTPi.2.2.2 _ le_sup_left le_top hsup2 hBsup
  have h2 : Op 2 (Nor V) ≤ T := sup_eq_left.1 h1
  exact hSVPi.2.2.2 T h2 le_top hTEA.isPGroup hBT

theorem exists_other {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2) :
    ∃ U' ∈ PiStar (Cen b) B 2, U' ≠ U ∧ PiStar (Cen b) B 2 = {U, U'} := by
  obtain ⟨U₁, U₂, h12, hP⟩ := c.piTwo
  rw [hP] at hU
  rcases hU with rfl | hU
  · exact ⟨U₂, by rw [hP]; simp, h12.symm, hP⟩
  · rw [Set.mem_singleton_iff] at hU
    subst hU
    refine ⟨U₁, by rw [hP]; simp, h12, ?_⟩
    rw [hP]; exact Set.pair_comm _ _

theorem S_inj {U₁ U₂ : Subgroup G} (h1 : U₁ ∈ PiStar (Cen b) B 2) (h2 : U₂ ∈ PiStar (Cen b) B 2)
    (hne : U₁ ≠ U₂) : Op 2 (Nor U₁) ≠ Op 2 (Nor U₂) := by
  intro h
  apply hne
  rw [← S48_CSb c h1, ← S48_CSb c h2, h]

theorem orbit_pair {U₁ U₂ : Subgroup G} (hP : PiStar (Cen b) B 2 = {U₁, U₂}) (h12 : U₁ ≠ U₂)
    {y : G} (hy : y ∈ Nor B) :
    (conjBy y (Op 2 (Nor U₁)) = Op 2 (Nor U₁) ∧ conjBy y (Op 2 (Nor U₂)) = Op 2 (Nor U₂)) ∨
    (conjBy y (Op 2 (Nor U₁)) = Op 2 (Nor U₂) ∧ conjBy y (Op 2 (Nor U₂)) = Op 2 (Nor U₁)) := by
  have hU₁ : U₁ ∈ PiStar (Cen b) B 2 := by rw [hP]; simp
  have hU₂ : U₂ ∈ PiStar (Cen b) B 2 := by rw [hP]; simp
  obtain ⟨hV₁, hT₁⟩ := orbit_key c hU₁ hy
  obtain ⟨hV₂, hT₂⟩ := orbit_key c hU₂ hy
  set V₁ := conjBy y (Op 2 (Nor U₁)) ⊓ Cen b
  set V₂ := conjBy y (Op 2 (Nor U₂)) ⊓ Cen b
  have hne : V₁ ≠ V₂ := by
    intro h
    apply S_inj c hU₁ hU₂ h12
    apply conjBy_inj (y := y)
    rw [hT₁, hT₂, h]
  rw [hP] at hV₁ hV₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hV₁ hV₂
  rcases hV₁ with h1 | h1 <;> rcases hV₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · left
    rw [h1] at hT₁
    rw [h2] at hT₂
    exact ⟨hT₁, hT₂⟩
  · right
    rw [h1] at hT₁
    rw [h2] at hT₂
    exact ⟨hT₁, hT₂⟩
  · exact absurd (h1.trans h2.symm) hne

include c

variable {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include hU

theorem S48_index2 (hsw : S47Swap b B) : (Nor (Op 2 (Nor U)) ⊓ Nor B).relIndex (Nor B) = 2 := by
  obtain ⟨U', hU', hne, hP⟩ := c.exists_other hU
  obtain ⟨g, hg, hgU⟩ := hsw U hU
  have hgN : g ∈ Nor B := hg.1
  set S := Op 2 (Nor U) with hSdef
  have hgS : conjBy g S ≠ S := by
    intro h
    apply hgU
    have hgb : g * b * g⁻¹ = b := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hg.2
      calc g * b * g⁻¹ = b * g * g⁻¹ := by rw [this]
        _ = b := by group
    have e : conjBy g S ⊓ Cen b = conjBy g (S ⊓ Cen b) := by
      rw [conjBy_inf, conjBy_cen, hgb]
    rw [h, S48_CSb c hU] at e
    exact e.symm
  have hmem : ∀ y ∈ Nor B, y ∈ Nor S ⊓ Nor B ↔ conjBy y S = S := fun y hy =>
    ⟨fun h => mem_nor_iff_conjBy.1 h.1, fun h => ⟨mem_nor_iff_conjBy.2 h, hy⟩⟩
  have hle : Nor S ⊓ Nor B ≤ Nor B := inf_le_right
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨g, hgN⟩, fun y => ?_⟩
  have hy := y.2
  have hmem' : ∀ z : ↥(Nor B), z ∈ (Nor S ⊓ Nor B).subgroupOf (Nor B) ↔ conjBy (z : G) S = S := by
    intro z
    rw [Subgroup.mem_subgroupOf]
    exact hmem _ z.2
  rw [hmem', hmem']
  have hmul : conjBy ((y : G) * g) S = conjBy (y : G) (conjBy g S) := conjBy_mul _ _ _
  show Xor (conjBy ((y : G) * g) S = S) (conjBy (y : G) S = S)
  rw [hmul]
  rcases orbit_pair c hP hne.symm hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have : conjBy g S = Op 2 (Nor U') := by
      rcases orbit_pair c hP hne.symm hgN with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact absurd k1 hgS
      · exact k1
    rw [this, h2]
    refine Or.inr ⟨h1, ?_⟩
    intro h
    exact S_inj c hU' hU hne h
  · have : conjBy g S = Op 2 (Nor U') := by
      rcases orbit_pair c hP hne.symm hgN with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact absurd k1 hgS
      · exact k1
    rw [this, h2]
    refine Or.inl ⟨rfl, ?_⟩
    intro h
    exact S_inj c hU' hU hne (h1.symm.trans h)

theorem S48_conj :
    (∃ g ∈ Nor (Op 2 (Nor U)) ⊓ Nor B, conjBy g (Subgroup.zpowers b) = Subgroup.zpowers b₁) ∧
    (∃ g ∈ Nor (Op 2 (Nor U)) ⊓ Nor B, conjBy g (Subgroup.zpowers b) = Subgroup.zpowers b₂) := by
  obtain ⟨U', hU', hne, hP⟩ := c.exists_other hU
  obtain ⟨-, -, -, -, -, ⟨n, hn, hn1, hn2, hn3⟩⟩ := c.sec.mono
  have hn3B : n * (n * n) ∈ B := by
    have hcen : n * (n * n) ∈ CenS B := by
      refine IsoAux.cen_of_gen c.sec.mono.2.1 ?_
      have e1 : (n * n) * b * (n * n)⁻¹ = b₂ := conj_comp hn1 hn2
      have e2 : (n * (n * n)) * b * (n * (n * n))⁻¹ = b := conj_comp e1 hn3
      have f1 : (n * n) * b₁ * (n * n)⁻¹ = b := conj_comp hn2 hn3
      have f2 : (n * (n * n)) * b₁ * (n * (n * n))⁻¹ = b₁ := conj_comp f1 hn1
      have g1 : (n * n) * b₂ * (n * n)⁻¹ = b₁ := conj_comp hn3 hn1
      have g2 : (n * (n * n)) * b₂ * (n * (n * n))⁻¹ = b₂ := conj_comp g1 hn2
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact (IsoAux.commute_of_sg e2).symm
      · exact (IsoAux.commute_of_sg f2).symm
      · exact (IsoAux.commute_of_sg g2).symm
    rwa [c.post.cB] at hcen
  have hnS : n ∈ Nor (Op 2 (Nor U)) := by
    rw [mem_nor_iff_conjBy]
    rcases orbit_pair c hP hne.symm hn with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact k1
    · exfalso
      have h3 : conjBy (n * (n * n)) (Op 2 (Nor U)) = Op 2 (Nor U) :=
        mem_nor_iff_conjBy.1 (B_le_nor_S c hU hn3B)
      rw [conjBy_mul, conjBy_mul, k1, k2, k1] at h3
      exact S_inj c hU' hU hne h3
  have hnH : n ∈ Nor (Op 2 (Nor U)) ⊓ Nor B := ⟨hnS, hn⟩
  refine ⟨⟨n, hnH, ?_⟩, ⟨n * n, mul_mem hnH hnH, ?_⟩⟩
  · rw [conjBy_zpowers, hn1]
  · rw [conjBy_zpowers, conj_comp hn1 hn2]

end S48Ctx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
