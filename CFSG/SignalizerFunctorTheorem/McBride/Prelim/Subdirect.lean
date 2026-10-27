module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

private theorem isDirectProduct_of_subset {S T : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (hT : T ⊆ S) : IsDirectProduct T (sSup T) where
  commute J hJ L hL hne := hK.commute J (hT hJ) L (hT hL) hne
  indep := hK.indep.mono hT
  sSup_eq := rfl

private theorem commute_sSup_of_disjoint {S T₁ T₂ : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (h₁ : T₁ ⊆ S) (h₂ : T₂ ⊆ S) (hd : Disjoint T₁ T₂) :
    ∀ x ∈ sSup T₁, ∀ y ∈ sSup T₂, Commute x y := by
  have key : ∀ J ∈ T₁, ∀ x ∈ J, ∀ y ∈ sSup T₂, Commute x y := by
    intro J hJ x hx y hy
    have : sSup T₂ ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sSup_le fun L hL z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hne : L ≠ J := fun h => Set.disjoint_left.mp hd hJ (h ▸ hL)
      exact (hK.commute L (h₂ hL) J (h₁ hJ) hne z hz x hx).eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  intro x hx y hy
  have : sSup T₁ ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sSup_le fun J hJ z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (key J hJ z hz y hy).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)

private theorem eq_one_of_forall_mem_sSup_diff [Finite G] {S : Set (Subgroup G)}
    {K : Subgroup G} (hK : IsDirectProduct S K) {z : G} (hz : z ∈ K)
    (h : ∀ J ∈ S, z ∈ sSup (S \ {J})) : z = 1 := by
  have h1 : (⟨z, hz⟩ : K) = 1 := by
    refine hK.ext_coord fun J hJ => ?_
    rw [map_one]
    exact (hK.coord_eq_one_iff hJ ⟨z, hz⟩).mpr (h J hJ)
  exact congrArg Subtype.val h1

private theorem disjoint_sSup_of_disjoint [Finite G] {S T₁ T₂ : Set (Subgroup G)}
    {K : Subgroup G} (hK : IsDirectProduct S K) (h₁ : T₁ ⊆ S) (h₂ : T₂ ⊆ S)
    (hd : Disjoint T₁ T₂) : Disjoint (sSup T₁) (sSup T₂) := by
  rw [Subgroup.disjoint_def]
  intro z hz₁ hz₂
  refine eq_one_of_forall_mem_sSup_diff hK (hK.sSup_diff_le T₁ h₁ hz₁) fun J hJ => ?_
  by_cases hJ₁ : J ∈ T₁
  · have hJ₂ : J ∉ T₂ := fun h => Set.disjoint_left.mp hd hJ₁ h
    have hsub : T₂ ⊆ S \ {J} := fun L hL =>
      ⟨h₂ hL, fun h => hJ₂ (Set.mem_singleton_iff.mp h ▸ hL)⟩
    exact sSup_le_sSup hsub hz₂
  · have hsub : T₁ ⊆ S \ {J} := fun L hL =>
      ⟨h₁ hL, fun h => hJ₁ (Set.mem_singleton_iff.mp h ▸ hL)⟩
    exact sSup_le_sSup hsub hz₁

private theorem mem_sSup_union_iff {S T₁ T₂ : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (h₁ : T₁ ⊆ S) (h₂ : T₂ ⊆ S) (hd : Disjoint T₁ T₂) {z : G} :
    z ∈ sSup (T₁ ∪ T₂) ↔ ∃ a ∈ sSup T₁, ∃ b ∈ sSup T₂, a * b = z := by
  rw [sSup_union]
  exact mem_sup_iff_of_commute (commute_sSup_of_disjoint hK h₁ h₂ hd)

private theorem conj_mem_sSup [Finite G] {S T : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (hT : T ⊆ S) {k x : G} (hk : k ∈ K) (hx : x ∈ sSup T) :
    k * x * k⁻¹ ∈ sSup T := by
  have hd : Disjoint T (S \ T) := Set.disjoint_sdiff_right
  have hk' : k ∈ sSup (T ∪ (S \ T)) := by
    rw [Set.union_sdiff_cancel hT, hK.sSup_eq]
    exact hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sSup_union_iff hK hT Set.sdiff_subset hd).mp hk'
  have hbx := commute_sSup_of_disjoint hK hT Set.sdiff_subset hd x hx b hb
  have h1 : b * x * b⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hbx.eq.symm
  have h2 : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ :=
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [h1]
  rw [h2]
  exact mul_mem (mul_mem ha hx) (inv_mem ha)

private theorem mem_projIn_iff_of_isDirectProduct {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) {X : Subgroup G} {x : G} :
    x ∈ projIn S J X ↔ x ∈ J ∧ ∃ l ∈ sSup (S \ {J}), x * l ∈ X :=
  mem_proj_iff (hK.commute_sSup_diff hJ)

private theorem isDirectProduct_insert {S₁ : Set (Subgroup G)} {K₁ X : Subgroup G}
    (h : IsDirectProduct S₁ K₁) (hc : ∀ x ∈ X, ∀ y ∈ K₁, Commute x y) (hd : Disjoint X K₁) :
    IsDirectProduct (insert X S₁) (X ⊔ K₁) where
  commute J hJ L hL hne x hx y hy := by
    rcases hJ with hJ | hJ <;> rcases hL with hL | hL
    · exact absurd (hJ.trans hL.symm) hne
    · subst hJ
      exact hc x hx y (h.le hL hy)
    · subst hL
      exact (hc y hy x (h.le hJ hx)).symm
    · exact h.commute J hJ L hL hne x hx y hy
  indep := by
    intro a ha
    rcases ha with ha | ha
    · subst ha
      refine hd.mono_right (sSup_le fun L hL => ?_)
      rcases hL.1 with hL' | hL'
      · exact absurd hL' hL.2
      · exact h.le hL'
    · rw [Subgroup.disjoint_def]
      intro z hza hz
      have hsub : insert X S₁ \ {a} ⊆ insert X (S₁ \ {a}) := by
        intro L hL
        rcases hL.1 with hL' | hL'
        · exact Or.inl hL'
        · exact Or.inr ⟨hL', hL.2⟩
      have hz' : z ∈ X ⊔ sSup (S₁ \ {a}) := by
        rw [← sSup_insert]
        exact sSup_le_sSup hsub hz
      have hcomm : ∀ x ∈ X, ∀ y ∈ sSup (S₁ \ {a}), Commute x y := fun x hx y hy =>
        hc x hx y (h.sSup_diff_le _ Set.sdiff_subset hy)
      obtain ⟨x, hx, l, hl, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hz'
      have hl1 : l ∈ K₁ := h.sSup_diff_le _ Set.sdiff_subset hl
      have hx1 : x ∈ K₁ := by
        have h2 : x = (x * l) * l⁻¹ := by group
        rw [h2]
        exact mul_mem (h.le ha hza) (inv_mem hl1)
      have hx2 : x = 1 := by
        have : x ∈ X ⊓ K₁ := ⟨hx, hx1⟩
        rw [hd.eq_bot] at this
        exact this
      subst hx2
      rw [one_mul] at hza ⊢
      have : l ∈ a ⊓ sSup (S₁ \ {a}) := ⟨hza, hl⟩
      rw [(h.indep ha).eq_bot] at this
      exact this
  sSup_eq := by rw [sSup_insert, h.sSup_eq]

private theorem eq_bot_or_eq_of_conj_mem {J N : Subgroup G} (hJ : IsSimpleGroup J)
    (hNJ : N ≤ J) (hN : ∀ p ∈ N, ∀ j ∈ J, j * p * j⁻¹ ∈ N) : N = ⊥ ∨ N = J := by
  have hnorm : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff hNJ).mpr fun p j hp hj => hN p hp j hj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, hNJ hx⟩ : J) ∈ N.subgroupOf J := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · right
    refine le_antisymm hNJ fun x hx => ?_
    have hmem : (⟨x, hx⟩ : J) ∈ N.subgroupOf J := by rw [h]; trivial
    exact hmem

private theorem eq_one_of_forall_mul_comm_of_simple {J : Subgroup G} (hJ : IsSimpleGroup J)
    (hnc : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {z : G} (hz : z ∈ J)
    (hc : ∀ t ∈ J, t * z = z * t) : z = 1 := by
  have hZ : Subgroup.center J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hnc
      have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (⟨y, hy⟩ : J)) ⟨x, hx⟩
      exact hxy (congrArg Subtype.val this)
  have : (⟨z, hz⟩ : J) ∈ Subgroup.center J :=
    Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hc t t.2)
  rw [hZ, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

private theorem mem_of_conj_mem_of_isDiagonal [Finite G] {T : Set (Subgroup G)}
    {K X : Subgroup G} (hT : IsDirectProduct T K)
    (hS : ∀ J ∈ T, IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x)
    (hX : IsDiagonal T X) {g : G} (hg : g ∈ K) (hn : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    g ∈ X := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨J₀, hJ₀⟩
  · rw [← hT.sSup_eq, sSup_empty, Subgroup.mem_bot] at hg
    rw [hg]
    exact one_mem _
  have hinj : ∀ J (hJ : J ∈ T) (x : K), (x : G) ∈ X → hT.coord hJ x = 1 → x = 1 := by
    intro J hJ x hxX hx1
    have : (x : G) ∈ X ⊓ sSup (T \ {J}) := ⟨hxX, (hT.coord_eq_one_iff hJ x).mp hx1⟩
    rw [(hX.2 J hJ).1, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hsurj : ∀ J (hJ : J ∈ T), ∀ j ∈ J,
      ∃ x : K, (x : G) ∈ X ∧ ((hT.coord hJ x : J) : G) = j := by
    intro J hJ j hj
    have : j ∈ projIn T J X := by
      rw [(hX.2 J hJ).2]
      exact hj
    exact (hT.mem_projIn_iff hJ).mp this
  obtain ⟨d, hdX, hd⟩ := hsurj J₀ hJ₀ _ (hT.coord hJ₀ ⟨g, hg⟩).2
  have hd' : hT.coord hJ₀ d = hT.coord hJ₀ ⟨g, hg⟩ := Subtype.ext hd
  set e : K := d⁻¹ * ⟨g, hg⟩ with he
  have he1 : hT.coord hJ₀ e = 1 := by
    rw [he, map_mul, map_inv, hd', inv_mul_cancel]
  have hecomm : ∀ x : K, (x : G) ∈ X → e * x * e⁻¹ = x := by
    intro x hxX
    have hxX' : ((e * x * e⁻¹ : K) : G) ∈ X := by
      have : ((e * x * e⁻¹ : K) : G) = (d : G)⁻¹ * (g * x * g⁻¹) * d := by
        rw [he]
        simp [mul_assoc]
      rw [this]
      exact mul_mem (mul_mem (inv_mem hdX) (hn x hxX)) hdX
    have h1 : (e * x * e⁻¹)⁻¹ * x = 1 := by
      refine hinj J₀ hJ₀ _ (mul_mem (inv_mem hxX') hxX) ?_
      have h2 : hT.coord hJ₀ (e * x * e⁻¹) = hT.coord hJ₀ x := by simp [he1]
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    exact inv_mul_eq_one.mp h1
  have hecoord : ∀ J (hJ : J ∈ T), hT.coord hJ e = 1 := by
    intro J hJ
    have hJs := hS J hJ
    refine Subtype.ext ?_
    refine eq_one_of_forall_mul_comm_of_simple hJs.1 hJs.2 (hT.coord hJ e).2 fun t ht => ?_
    obtain ⟨x, hxX, hxt⟩ := hsurj J hJ t ht
    have h1 := congrArg (fun y : K => ((hT.coord hJ y : J) : G)) (hecomm x hxX)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hxt] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have he2 : e = 1 := hT.ext_coord fun J hJ => by rw [map_one]; exact hecoord J hJ
  have h3 : (⟨g, hg⟩ : K) = d := by
    have : d⁻¹ * ⟨g, hg⟩ = 1 := he2
    exact (inv_mul_eq_one.mp this).symm
  have h4 : g = d := congrArg Subtype.val h3
  rw [h4]
  exact hdX

private theorem exists_minimal_block [Finite G] {S : Set (Subgroup G)} {H : Subgroup G}
    (hH : H ⊓ sSup S ≠ ⊥) :
    ∃ T₀ : Set (Subgroup G), T₀ ⊆ S ∧ T₀.Nonempty ∧ H ⊓ sSup T₀ ≠ ⊥ ∧
      ∀ J ∈ T₀, H ⊓ sSup (T₀ \ {J}) = ⊥ := by
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sSup_empty, inf_bot_eq] at hH
    exact hH rfl
  obtain ⟨T₀, ⟨hTS, hTne, hT⟩, hmin⟩ := wellFounded_lt.has_min
    {T : Set (Subgroup G) | T ⊆ S ∧ T.Nonempty ∧ H ⊓ sSup T ≠ ⊥} ⟨S, subset_rfl, hSne, hH⟩
  refine ⟨T₀, hTS, hTne, hT, fun J hJ => ?_⟩
  by_contra hne
  have hne' : (T₀ \ {J}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sSup_empty, inf_bot_eq] at hne
    exact hne rfl
  refine hmin (T₀ \ {J}) ⟨Set.sdiff_subset.trans hTS, hne', hne⟩ ?_
  rw [Set.ssubset_iff_of_subset Set.sdiff_subset]
  exact ⟨J, hJ, fun h => h.2 rfl⟩

private theorem isDiagonal_of_minimal [Finite G] {S : Set (Subgroup G)} {H : Subgroup G}
    (hS : ∀ J ∈ S, IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x)
    (hK : IsDirectProduct S (sSup S)) (hHK : H ≤ sSup S)
    (hH : ∀ J ∈ S, projIn S J H = J) {T₀ : Set (Subgroup G)} (hT₀S : T₀ ⊆ S)
    (hD : H ⊓ sSup T₀ ≠ ⊥) (hmin : ∀ J ∈ T₀, H ⊓ sSup (T₀ \ {J}) = ⊥) :
    IsDiagonal T₀ (H ⊓ sSup T₀) := by
  have hT₀K : IsDirectProduct T₀ (sSup T₀) := isDirectProduct_of_subset hK hT₀S
  refine ⟨inf_le_right, fun J hJ => ⟨?_, ?_⟩⟩
  · refine eq_bot_iff.mpr fun z hz => ?_
    have h1 : z ∈ H ⊓ sSup (T₀ \ {J}) := ⟨(Subgroup.mem_inf.mp hz.1).1, hz.2⟩
    rw [hmin J hJ] at h1
    exact h1
  have hJS : J ∈ S := hT₀S hJ
  obtain ⟨hJsimple, -⟩ := hS J hJS
  have hHJ : ∀ j ∈ J, ∃ l ∈ sSup (S \ {J}), j * l ∈ H := fun j hj =>
    ((mem_projIn_iff_of_isDirectProduct hK hJS).mp (by rw [hH J hJS]; exact hj)).2
  have hnorm : ∀ p ∈ projIn T₀ J (H ⊓ sSup T₀), ∀ j ∈ J,
      j * p * j⁻¹ ∈ projIn T₀ J (H ⊓ sSup T₀) := by
    intro p hp j hj
    obtain ⟨hpJ, l, hl, hpl⟩ := (mem_projIn_iff_of_isDirectProduct hT₀K hJ).mp hp
    obtain ⟨l', hl', hjl'⟩ := hHJ j hj
    have hsub : T₀ \ {J} ⊆ S \ {J} := Set.sdiff_subset_sdiff_left hT₀S
    have hl'K : l' ∈ sSup S := hK.sSup_diff_le _ Set.sdiff_subset hl'
    have hl'' : l' * l * l'⁻¹ ∈ sSup (T₀ \ {J}) :=
      conj_mem_sSup hK (Set.sdiff_subset.trans hT₀S) hl'K hl
    have hjpj : j * p * j⁻¹ ∈ J := mul_mem (mul_mem hj hpJ) (inv_mem hj)
    refine (mem_projIn_iff_of_isDirectProduct hT₀K hJ).mpr ⟨hjpj, l' * l * l'⁻¹, hl'', ?_⟩
    obtain ⟨hplH, hplT⟩ := Subgroup.mem_inf.mp hpl
    have hD' : (j * l') * (p * l) * (j * l')⁻¹ ∈ H ⊓ sSup T₀ :=
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hjl' hplH) (inv_mem hjl'),
        conj_mem_sSup hK hT₀S (hHK hjl') hplT⟩
    have hc1 : Commute p l' := hK.commute_sSup_diff hJS p hpJ l' hl'
    have hc2 : Commute j (l' * l * l'⁻¹) :=
      hK.commute_sSup_diff hJS j hj _ (sSup_le_sSup hsub hl'')
    have heq : (j * l') * (p * l) * (j * l')⁻¹ = (j * p * j⁻¹) * (l' * l * l'⁻¹) :=
      calc (j * l') * (p * l) * (j * l')⁻¹ = j * (l' * p) * (l * l'⁻¹) * j⁻¹ := by group
        _ = j * (p * l') * (l * l'⁻¹) * j⁻¹ := by rw [hc1.eq]
        _ = j * p * ((l' * l * l'⁻¹) * j⁻¹) := by group
        _ = j * p * (j⁻¹ * (l' * l * l'⁻¹)) := by rw [hc2.inv_left.eq]
        _ = (j * p * j⁻¹) * (l' * l * l'⁻¹) := by group
    rw [← heq]
    exact hD'
  rcases eq_bot_or_eq_of_conj_mem hJsimple (projIn_le _ _) hnorm with hbot | heq
  · exfalso
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    have hdsup : d ∈ sSup ({J} ∪ (T₀ \ {J})) := by
      rw [Set.union_sdiff_cancel (Set.singleton_subset_iff.mpr hJ)]
      exact hd.2
    obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sSup_union_iff hT₀K (Set.singleton_subset_iff.mpr hJ)
      Set.sdiff_subset Set.disjoint_sdiff_right).mp hdsup
    rw [sSup_singleton] at hj
    have hjN : j ∈ projIn T₀ J (H ⊓ sSup T₀) :=
      (mem_projIn_iff_of_isDirectProduct hT₀K hJ).mpr ⟨hj, l, hl, hjl ▸ hd⟩
    rw [hbot, Subgroup.mem_bot] at hjN
    rw [hjN, one_mul] at hjl
    have hl1 : l ∈ H ⊓ sSup (T₀ \ {J}) := ⟨hjl ▸ hd.1, hl⟩
    rw [hmin J hJ, Subgroup.mem_bot] at hl1
    exact hd1 (Subtype.ext (hjl ▸ hl1))
  · exact heq

private theorem exists_split [Finite G] {S : Set (Subgroup G)} {H : Subgroup G}
    (hS : ∀ J ∈ S, IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x)
    (hK : IsDirectProduct S (sSup S)) (hHK : H ≤ sSup S)
    (hH : ∀ J ∈ S, projIn S J H = J) {T₀ : Set (Subgroup G)} (hT₀S : T₀ ⊆ S)
    (hdiag : IsDiagonal T₀ (H ⊓ sSup T₀)) :
    H = (H ⊓ sSup T₀) ⊔ (H ⊓ sSup (S \ T₀)) ∧
      ∀ J ∈ S \ T₀, projIn (S \ T₀) J (H ⊓ sSup (S \ T₀)) = J := by
  have hT₀K : IsDirectProduct T₀ (sSup T₀) := isDirectProduct_of_subset hK hT₀S
  have hS'K : IsDirectProduct (S \ T₀) (sSup (S \ T₀)) :=
    isDirectProduct_of_subset hK Set.sdiff_subset
  have hdisj : Disjoint T₀ (S \ T₀) := Set.disjoint_sdiff_right
  have hsplit : ∀ a ∈ sSup T₀, ∀ b ∈ sSup (S \ T₀), a * b ∈ H → a ∈ H ⊓ sSup T₀ := by
    intro a ha b hb hab
    refine mem_of_conj_mem_of_isDiagonal hT₀K (fun J hJ => hS J (hT₀S hJ)) hdiag ha ?_
    intro x hx
    obtain ⟨hxH, hxT⟩ := Subgroup.mem_inf.mp hx
    have hbx := commute_sSup_of_disjoint hK hT₀S Set.sdiff_subset hdisj x hxT b hb
    have h1 : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ :=
      calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hbx.eq.symm]
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem ha hxT) (inv_mem ha)⟩
    rw [← h1]
    exact mul_mem (mul_mem hab hxH) (inv_mem hab)
  have hsup : H = (H ⊓ sSup T₀) ⊔ (H ⊓ sSup (S \ T₀)) := by
    refine le_antisymm (fun h hh => ?_) (sup_le inf_le_left inf_le_left)
    have hh' : h ∈ sSup (T₀ ∪ (S \ T₀)) := by
      rw [Set.union_sdiff_cancel hT₀S]
      exact hHK hh
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sSup_union_iff hK hT₀S Set.sdiff_subset hdisj).mp hh'
    have haD := hsplit a ha b hb hh
    have hbH : b ∈ H := by
      have := mul_mem (inv_mem (Subgroup.mem_inf.mp haD).1) hh
      simpa using this
    exact mul_mem (Subgroup.mem_sup_left haD)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hbH, hb⟩))
  refine ⟨hsup, fun J hJ => ?_⟩
  obtain ⟨hJS, hJT⟩ := hJ
  refine le_antisymm (projIn_le _ _) fun x hx => ?_
  have hxH : x ∈ projIn S J H := by
    rw [hH J hJS]
    exact hx
  obtain ⟨-, l, hl, hxl⟩ := (mem_projIn_iff_of_isDirectProduct hK hJS).mp hxH
  have hsubS : S \ {J} ⊆ T₀ ∪ ((S \ T₀) \ {J}) := by
    intro L hL
    by_cases hLT : L ∈ T₀
    · exact Or.inl hLT
    · exact Or.inr ⟨⟨hL.1, hLT⟩, hL.2⟩
  have hdisj' : Disjoint T₀ ((S \ T₀) \ {J}) := Set.disjoint_of_subset_right Set.sdiff_subset hdisj
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := (mem_sSup_union_iff hK hT₀S
    (Set.sdiff_subset.trans Set.sdiff_subset) hdisj').mp (sSup_le_sSup hsubS hl)
  have hT₀J : T₀ ⊆ S \ {J} := fun L hL =>
    ⟨hT₀S hL, fun h => hJT (Set.mem_singleton_iff.mp h ▸ hL)⟩
  have hcomm : Commute x l₁ := hK.commute_sSup_diff hJS x hx l₁ (sSup_le_sSup hT₀J hl₁)
  have hJ' : J ∈ S \ T₀ := ⟨hJS, hJT⟩
  have hl₂' : l₂ ∈ sSup (S \ T₀) :=
    sSup_le_sSup (Set.sdiff_subset : (S \ T₀) \ {J} ⊆ S \ T₀) hl₂
  have hxl₂ : x * l₂ ∈ sSup (S \ T₀) := mul_mem (le_sSup hJ' hx) hl₂'
  have h1 : l₁ * (x * l₂) ∈ H := by
    have : x * (l₁ * l₂) = l₁ * (x * l₂) := by
      rw [← mul_assoc, hcomm.eq, mul_assoc]
    rw [← this]
    exact hxl
  have hl₁D := (Subgroup.mem_inf.mp (hsplit l₁ hl₁ (x * l₂) hxl₂ h1)).1
  have h2 : x * l₂ ∈ H := by
    have := mul_mem (inv_mem hl₁D) h1
    simpa using this
  exact (mem_projIn_iff_of_isDirectProduct hS'K hJ').mpr
    ⟨hx, l₂, hl₂, Subgroup.mem_inf.mpr ⟨h2, hxl₂⟩⟩

private theorem exists_partition_aux [Finite G] (S : Set (Subgroup G))
    (hS : ∀ J ∈ S, IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x)
    (hK : IsDirectProduct S (sSup S)) (H : Subgroup G) (hHK : H ≤ sSup S)
    (hH : ∀ J ∈ S, projIn S J H = J) :
    ∃ P : Set (Set (Subgroup G)), ∅ ∉ P ∧ ⋃₀ P = S ∧ P.PairwiseDisjoint id ∧
      IsDirectProduct ((fun T => H ⊓ sSup T) '' P) H ∧
      ∀ T ∈ P, IsDiagonal T (H ⊓ sSup T) := by
  induction S using WellFoundedLT.induction generalizing H with
  | _ S ih =>
    by_cases hS0 : S = ∅
    · subst hS0
      have hH0 : H = ⊥ := by rwa [sSup_empty, le_bot_iff] at hHK
      subst hH0
      refine ⟨∅, by simp, by simp, Set.pairwiseDisjoint_empty, ?_, by simp⟩
      rw [Set.image_empty]
      exact ⟨fun J hJ => absurd hJ (Set.notMem_empty J), sSupIndep_empty, sSup_empty⟩
    have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS0
    have hHne : H ⊓ sSup S ≠ ⊥ := by
      obtain ⟨J, hJ⟩ := hSne
      rw [inf_eq_left.mpr hHK]
      intro hH0
      obtain ⟨-, x, hx, y, hy, hxy⟩ := hS J hJ
      have hx1 : x ≠ 1 := fun h => hxy (by rw [h, one_mul, mul_one])
      have hxJ : x ∈ projIn S J H := by
        rw [hH J hJ]
        exact hx
      obtain ⟨-, l, hl, hxl⟩ := (mem_projIn_iff_of_isDirectProduct hK hJ).mp hxJ
      rw [hH0, Subgroup.mem_bot] at hxl
      have hxl' : x ∈ sSup (S \ {J}) := by
        rw [eq_inv_of_mul_eq_one_left hxl]
        exact inv_mem hl
      have : x ∈ J ⊓ sSup (S \ {J}) := Subgroup.mem_inf.mpr ⟨hx, hxl'⟩
      rw [(hK.indep hJ).eq_bot, Subgroup.mem_bot] at this
      exact hx1 this
    obtain ⟨T₀, hT₀S, hT₀ne, hD, hmin⟩ := exists_minimal_block hHne
    have hdiag := isDiagonal_of_minimal hS hK hHK hH hT₀S hD hmin
    obtain ⟨hsup, hproj⟩ := exists_split hS hK hHK hH hT₀S hdiag
    have hdisj : Disjoint T₀ (S \ T₀) := Set.disjoint_sdiff_right
    have hlt : S \ T₀ < S := by
      obtain ⟨J₀, hJ₀⟩ := hT₀ne
      exact (Set.ssubset_iff_of_subset Set.sdiff_subset).mpr ⟨J₀, hT₀S hJ₀, fun h => h.2 hJ₀⟩
    obtain ⟨P', h1, h2, h3, h4, h5⟩ := ih (S \ T₀) hlt (fun J hJ => hS J hJ.1)
      (isDirectProduct_of_subset hK Set.sdiff_subset) (H ⊓ sSup (S \ T₀)) inf_le_right hproj
    have hP'S : ∀ T ∈ P', T ⊆ S \ T₀ := fun T hT => h2 ▸ Set.subset_sUnion_of_mem hT
    have hHT : ∀ T ∈ P', H ⊓ sSup T = (H ⊓ sSup (S \ T₀)) ⊓ sSup T := by
      intro T hT
      rw [inf_assoc, inf_eq_right.mpr (sSup_le_sSup (hP'S T hT))]
    refine ⟨insert T₀ P', ?_, ?_, ?_, ?_, ?_⟩
    · rintro (h | h)
      · exact hT₀ne.ne_empty h.symm
      · exact h1 h
    · rw [Set.sUnion_insert, h2]
      exact Set.union_sdiff_cancel hT₀S
    · refine h3.insert fun T hT _ => ?_
      exact Set.disjoint_of_subset_right (hP'S T hT) hdisj
    · have himg : (fun T => H ⊓ sSup T) '' P' =
          (fun T => (H ⊓ sSup (S \ T₀)) ⊓ sSup T) '' P' := Set.image_congr hHT
      rw [Set.image_insert_eq, himg]
      have hcomm : ∀ x ∈ H ⊓ sSup T₀, ∀ y ∈ H ⊓ sSup (S \ T₀), Commute x y := fun x hx y hy =>
        commute_sSup_of_disjoint hK hT₀S Set.sdiff_subset hdisj x (Subgroup.mem_inf.mp hx).2 y
          (Subgroup.mem_inf.mp hy).2
      have hdis : Disjoint (H ⊓ sSup T₀) (H ⊓ sSup (S \ T₀)) :=
        (disjoint_sSup_of_disjoint hK hT₀S Set.sdiff_subset hdisj).mono inf_le_right inf_le_right
      have := isDirectProduct_insert h4 hcomm hdis
      rwa [← hsup] at this
    · rintro T (rfl | hT)
      · exact hdiag
      · rw [hHT T hT]
        exact h5 T hT

theorem exists_partition_isDiagonal [Finite G] {K H : Subgroup G} (hK : IsSemisimple K)
    (hHK : H ≤ K) (hH : ∀ J ∈ lcal K, projIn (lcal K) J H = J) :
    ∃ P : Set (Set (Subgroup G)), ∅ ∉ P ∧ ⋃₀ P = lcal K ∧ P.PairwiseDisjoint id ∧
      IsDirectProduct ((fun T => H ⊓ sSup T) '' P) H ∧
      ∀ T ∈ P, IsDiagonal T (H ⊓ sSup T) := by
  have hdp := hK.isDirectProduct_lcal
  have hsimple : ∀ J ∈ lcal K, IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
    intro J hJ
    rw [hK.lcal_eq] at hJ
    exact ⟨hJ.2.2.1, hJ.2.2.2⟩
  have hHK' : H ≤ sSup (lcal K) := by
    rw [hdp.sSup_eq]
    exact hHK
  exact exists_partition_aux (lcal K) hsimple ⟨hdp.commute, hdp.indep, rfl⟩ H hHK' hH

theorem eq_of_projIn_eq_of_inf_ne_bot [Finite G] {K H : Subgroup G} (hK : IsSemisimple K)
    (hHK : H ≤ K) (hH : ∀ J ∈ lcal K, projIn (lcal K) J H = J)
    (hint : ∀ J ∈ lcal K, H ⊓ J ≠ ⊥) : H = K := by
  have hdp := hK.isDirectProduct_lcal
  refine le_antisymm hHK ?_
  rw [← hdp.sSup_eq]
  refine sSup_le fun J hJ => ?_
  have hJs : IsSimpleGroup J := by
    have hJ' := hJ
    rw [hK.lcal_eq] at hJ'
    exact hJ'.2.2.1
  have hnorm : ∀ p ∈ H ⊓ J, ∀ j ∈ J, j * p * j⁻¹ ∈ H ⊓ J := by
    intro p hp j hj
    obtain ⟨hpH, hpJ⟩ := Subgroup.mem_inf.mp hp
    have hjmem : j ∈ projIn (lcal K) J H := by
      rw [hH J hJ]
      exact hj
    obtain ⟨-, l, hl, hjl⟩ := (mem_projIn_iff_of_isDirectProduct hdp hJ).mp hjmem
    have hcomm : Commute p l := hdp.commute_sSup_diff hJ p hpJ l hl
    have heq : j * p * j⁻¹ = (j * l) * p * (j * l)⁻¹ :=
      calc j * p * j⁻¹ = j * (p * l) * l⁻¹ * j⁻¹ := by group
        _ = j * (l * p) * l⁻¹ * j⁻¹ := by rw [hcomm.eq]
        _ = (j * l) * p * (j * l)⁻¹ := by group
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hj hpJ) (inv_mem hj)⟩
    rw [heq]
    exact mul_mem (mul_mem hjl hpH) (inv_mem hjl)
  rcases eq_bot_or_eq_of_conj_mem hJs inf_le_right hnorm with h | h
  · exact absurd h (hint J hJ)
  · exact inf_eq_right.mp h

end CFSG.SignalizerFunctorTheorem.McBride
