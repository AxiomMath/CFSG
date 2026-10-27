module

public import CFSG.RankThree.GF2n.Smith81.LinOddBasic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Lin212CondProp.symm {M Q Z B V₁ V₂ : Subgroup G} (h : Lin212CondProp M Q Z B V₁ V₂) :
    Lin212CondProp M Q Z B V₂ V₁ := by
  intro X x hs hne
  obtain ⟨h1, h2, h3, h4, h5⟩ := h X x hs hne
  exact ⟨h1, h3, h2, h4, h5⟩

structure OddSetup (M Q Z B : Subgroup G) (V V' : Subgroup G) : Prop where
  hyp : StrothHyp M Q Z
  ZV : Z ≤ V
  VQ : V ≤ Q
  ZV' : Z ≤ V'
  V'Q : V' ≤ Q
  int : V ⊓ V' = Z
  dec : ∀ q ∈ Q, ∃ a ∈ V, ∃ b ∈ V', q = a * b
  dec' : ∀ q ∈ Q, ∃ a ∈ V', ∃ b ∈ V, q = a * b
  abV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  abV' : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a
  sqV : ∀ v ∈ V, v * v = 1
  sqV' : ∀ v ∈ V', v * v = 1
  normV : ∀ t ∈ Lgen M (LB M Q B), t ∈ Subgroup.normalizer (V : Set G)
  normV' : ∀ t ∈ Lgen M (LB M Q B), t ∈ Subgroup.normalizer (V' : Set G)
  p31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V ∨ v ∈ V')

theorem OddSetup.symm {M Q Z B V V' : Subgroup G} (S : OddSetup M Q Z B V V') :
    OddSetup M Q Z B V' V where
  hyp := S.hyp
  ZV := S.ZV'
  VQ := S.V'Q
  ZV' := S.ZV
  V'Q := S.VQ
  int := by rw [inf_comm]; exact S.int
  dec := S.dec'
  dec' := S.dec
  abV := S.abV'
  abV' := S.abV
  sqV := S.sqV'
  sqV' := S.sqV
  normV := S.normV'
  normV' := S.normV
  p31 := fun v hv hv1 => by rw [S.p31 v hv hv1]; exact or_comm

section Odd

variable [Finite G] {M Q Z B : Subgroup G} {V V' : Subgroup G}

theorem inZClass_of_mem_root {A : Subgroup G} (hA : IsZConjugate Z A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) : InZClass Z a := by
  obtain ⟨g, rfl⟩ := hA
  have h : g⁻¹ * a * g ∈ Z := mem_conjSubgroup.mp haA
  refine ⟨g, g⁻¹ * a * g, h, ?_, by group⟩
  intro h1
  apply ha1
  have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [this, h1]; group

theorem OddSetup.root_le_V (S : OddSetup M Q Z B V V') {A : Subgroup G} (hA : IsZConjugate Z A)
    {a : G} (haA : a ∈ A) (haV : a ∈ V) (haZ : a ∉ Z) : A ≤ V ∧ A ≤ Q ∧ A ≠ Z := by
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have hAQ : A ≤ Q := root_le_Q S.hyp hA haA (S.VQ haV) ha1
  have hAne : A ≠ Z := fun h => haZ (h ▸ haA)
  have hunion : (A : Set G) ⊆ (V : Set G) ∪ (V' : Set G) := by
    intro a' ha'A
    by_cases ha'1 : a' = 1
    · left; rw [ha'1]; exact V.one_mem
    · exact (S.p31 a' (hAQ ha'A) ha'1).mp (inZClass_of_mem_root hA ha'A ha'1)
  rcases SubgroupClass.subset_union.mp hunion with h | h
  · exact ⟨h, hAQ, hAne⟩
  · exfalso
    apply haZ
    rw [← S.int]
    exact ⟨haV, h haA⟩

theorem Z_ne_bot (H : StrothHyp M Q Z) : Z ≠ ⊥ := by
  intro h
  have := H.q4
  rw [h, Subgroup.card_bot] at this
  omega

theorem OddSetup.x_not_mem_QB (S : OddSetup M Q Z B V V') {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) (hQX : Q ⊓ QB X = ⊥) {A : Subgroup G} (hA : IsZConjugate Z A) {a : G}
    (haA : a ∈ A) (haQ : a ∈ Q) (ha1 : a ≠ 1) : x ∉ QB A := by
  intro hxA
  have hX : IsZConjugate Z X := hs.conj
  have hXle := IsZConjugate.le_QB_of_mem S.hyp hA hX hs.ne_one hs.mem hxA
  have hAle := (IsZConjugate.le_QB_iff S.hyp hA hX).mp hXle
  have : a ∈ Q ⊓ QB X := ⟨haQ, hAle haA⟩
  rw [hQX, Subgroup.mem_bot] at this
  exact ha1 this

theorem OddSetup.Z_le_QB (S : OddSetup M Q Z B V V') {A : Subgroup G} (hA : IsZConjugate Z A)
    (hAQ : A ≤ Q) : Z ≤ QB A := by
  rw [IsZConjugate.le_QB_iff S.hyp hA (IsZConjugate.self Z), StrothHyp.QB_Z S.hyp]
  exact hAQ

theorem OddSetup.V_le_QB (S : OddSetup M Q Z B V V') (h4 : Lin212C4Prop M Q Z)
    {A : Subgroup G} (hA : IsZConjugate Z A)
    {a : G} (haA : a ∈ A) (haV : a ∈ V) (haZ : a ∉ Z) : V ≤ QB A := by
  obtain ⟨hAV, hAQ, hAZ⟩ := S.root_le_V hA haA haV haZ
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have hZQA := S.Z_le_QB hA hAQ
  intro v hv
  by_contra hvA
  have hv1 : v ≠ 1 := fun h => hvA (h ▸ (QB A).one_mem)
  have hvQ : v ∈ Q := S.VQ hv
  obtain ⟨g, z, hz, hz1, hvg⟩ := (S.p31 v hvQ hv1).mpr (Or.inl hv)
  have hW : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hvW : v ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, hvg]; simpa [mul_assoc] using hz
  have hWQ : conjSubgroup g Z ≤ Q := root_le_Q S.hyp hW hvW hvQ hv1
  have hvN : v ∈ Subgroup.normalizer (A : Set G) :=
    hA.mem_normalizer_of_commute S.hyp ha1 haA (S.abV v hv a haV)
  have hZQW := S.Z_le_QB hW hWQ
  have hne : QB A ⊓ QB (conjSubgroup g Z) ≠ ⊥ := by
    intro h
    have : Z ≤ ⊥ := h ▸ le_inf hZQA hZQW
    exact Z_ne_bot S.hyp (le_bot_iff.mp this)
  obtain ⟨gA, rfl⟩ := hA
  have h4' := c4_conj h4 S.hyp hW hvW hv1 hvN hvA hne
  have hz' : gA⁻¹ * a * gA ∈ Z := mem_conjSubgroup.mp haA
  have hva1 : v * a ≠ 1 := by
    intro h
    apply hvA
    have : v = a⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (QB (conjSubgroup gA Z)).inv_mem
      (IsZConjugate.le_QB_self S.hyp ⟨gA, rfl⟩ haA)
  have hcl : InZClass Z (v * a) :=
    (S.p31 (v * a) (S.VQ (V.mul_mem hv haV)) hva1).mpr (Or.inl (V.mul_mem hv haV))
  have hcl' : InZClass Z (gA⁻¹ * v * gA * (gA⁻¹ * a * gA)) := by
    have := (inZClass_conj_iff (Z := Z) (v := v * a) gA⁻¹).mpr hcl
    simpa [mul_assoc] using this
  have h1 := h4' _ hz' hcl'
  apply ha1
  have : a = gA * (gA⁻¹ * a * gA) * gA⁻¹ := by group
  rw [this, h1]; group

theorem OddSetup.V_le_conj (S : OddSetup M Q Z B V V') {gA : G}
    (h3 : V ≤ QB (conjSubgroup gA Z)) : V ≤ conjSubgroup gA V ∨ V ≤ conjSubgroup gA V' := by
  have hunion : (V : Set G) ⊆ (conjSubgroup gA V : Set G) ∪ (conjSubgroup gA V' : Set G) := by
    intro v hv
    by_cases hv1 : v = 1
    · left; rw [hv1]; exact (conjSubgroup gA V).one_mem
    · have hvQ : gA⁻¹ * v * gA ∈ Q := by
        have := h3 hv
        rw [QB_conj_eq S.hyp gA] at this
        exact mem_conjSubgroup.mp this
      have hvcl : InZClass Z v := (S.p31 v (S.VQ hv) hv1).mpr (Or.inl hv)
      have hcl : InZClass Z (gA⁻¹ * v * gA) := by
        have := (inZClass_conj_iff (Z := Z) (v := v) gA⁻¹).mpr hvcl
        simpa using this
      have hne : gA⁻¹ * v * gA ≠ 1 := by
        intro h
        apply hv1
        have : v = gA * (gA⁻¹ * v * gA) * gA⁻¹ := by group
        rw [this, h]; group
      rcases (S.p31 _ hvQ hne).mp hcl with h | h
      · left; exact mem_conjSubgroup.mpr h
      · right; exact mem_conjSubgroup.mpr h
  exact SubgroupClass.subset_union.mp hunion

omit [Finite G] in
theorem conjSubgroup_le_conjSubgroup_iff (g : G) {A C : Subgroup G} :
    conjSubgroup g A ≤ conjSubgroup g C ↔ A ≤ C := by
  constructor
  · intro h a ha
    have : g * a * g⁻¹ ∈ conjSubgroup g C :=
      h (by rw [mem_conjSubgroup]; simpa [mul_assoc] using ha)
    rw [mem_conjSubgroup] at this
    simpa [mul_assoc] using this
  · intro h
    exact Subgroup.map_mono h

omit [Finite G] in
theorem conjSubgroup_inv_conj (g : G) (T : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g T) = T := by
  rw [← conjSubgroup_mul]; simp [conjSubgroup_one]

omit [Finite G] in
theorem conjSubgroup_conj_inv (g : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ T) = T := by
  rw [← conjSubgroup_mul]; simp [conjSubgroup_one]

theorem step5_core {W W' V : Subgroup G} (S' : OddSetup M Q Z B W W') {gA : G} {x : G}
    (hAne : conjSubgroup gA Z ≠ Z) (hZV : Z ≤ V) (hVW : conjSubgroup gA⁻¹ V ≤ W)
    (hx'L : gA⁻¹ * x * gA ∈ Lgen M (LB M Q B))
    (hx2 : x * x = 1) (hdim : HasDimOn W Z 1 (gA⁻¹ * x * gA))
    (hZ'in : ∀ z ∈ Z, gA⁻¹ * z * gA ∈ ⁅Q, Subgroup.zpowers (gA⁻¹ * x * gA)⁆) :
    ⁅V, Subgroup.zpowers x⁆ ≤ Z ⊔ conjSubgroup gA Z := by
  set x' : G := gA⁻¹ * x * gA with hx'
  have hx'2 : x' * x' = 1 := by
    have : x' * x' = gA⁻¹ * (x * x) * gA := by rw [hx']; group
    rw [this, hx2]; group
  set Z' : Subgroup G := conjSubgroup gA⁻¹ Z with hZ'
  have hZ'W : Z' ≤ W := le_trans (Subgroup.map_mono hZV) hVW
  have hZW : Z ≤ W := S'.ZV
  have hZ'le : Z' ≤ ⁅W, Subgroup.zpowers x'⁆ ⊔ Z := by
    intro y hy
    have hzmem : gA * y * gA⁻¹ ∈ Z := by
      have := mem_conjSubgroup.mp hy
      simpa using this
    have hy' : y ∈ ⁅Q, Subgroup.zpowers x'⁆ := by
      have := hZ'in _ hzmem
      simpa [mul_assoc] using this
    exact comm_Q_inf_V S'.hyp S'.ZV S'.VQ S'.ZV' S'.V'Q S'.int S'.dec hx'2
      (S'.normV x' hx'L) (S'.normV' x' hx'L) (Subgroup.mem_sup_left hy') (hZ'W hy)
  have hsupZ : Z' ⊔ Z ≤ ⁅W, Subgroup.zpowers x'⁆ ⊔ Z := sup_le hZ'le le_sup_right
  have hZZ' : Z ⊓ Z' = ⊥ := by
    apply inf_conjSubgroup_eq_bot_of_isTI S'.hyp.ti
    intro h
    apply hAne
    have : conjSubgroup gA (conjSubgroup gA⁻¹ Z) = conjSubgroup gA Z := by rw [h]
    rw [conjSubgroup_conj_inv] at this
    exact this.symm
  have hcomm : ∀ a ∈ Z', ∀ c ∈ Z, a * c = c * a := by
    intro a ha c hc
    exact S'.abV a (hZ'W ha) c (S'.ZV hc)
  have hcard1 : Nat.card ↥(Z' ⊔ Z) = Nat.card Z * Nat.card Z := by
    rw [card_sup_of_comm_inf_bot hcomm (by rw [inf_comm]; exact hZZ'), hZ', card_conjSubgroup]
  have hcard2 : Nat.card ↥(⁅W, Subgroup.zpowers x'⁆ ⊔ Z) = Nat.card Z * Nat.card Z := by
    have : Nat.card ↥(⁅W, Subgroup.zpowers x'⁆ ⊔ Z) = Nat.card Z ^ (1 + 1) := hdim
    rw [this]; ring
  have hEq : Z' ⊔ Z = ⁅W, Subgroup.zpowers x'⁆ ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge hsupZ (by rw [hcard1, hcard2])
  have hVx : conjSubgroup gA⁻¹ ⁅V, Subgroup.zpowers x⁆ ≤ Z' ⊔ Z := by
    have h1 : ⁅conjSubgroup gA⁻¹ V, Subgroup.zpowers x'⁆ =
        conjSubgroup gA⁻¹ ⁅V, Subgroup.zpowers x⁆ := by
      have := commutator_zpowers_conj gA⁻¹ V x
      simpa [hx'] using this
    rw [← h1, hEq]
    exact le_trans (Subgroup.commutator_mono hVW le_rfl) le_sup_left
  have hA : Z' ⊔ Z = conjSubgroup gA⁻¹ (Z ⊔ conjSubgroup gA Z) := by
    rw [conjSubgroup_sup, conjSubgroup_inv_conj]
  rw [hA, conjSubgroup_le_conjSubgroup_iff] at hVx
  exact hVx

theorem OddSetup.QB_inf_QB_eq_bot (S : OddSetup M Q Z B V V')
    (hcond : Lin212CondProp M Q Z B V V') {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) (hQX : Q ⊓ QB X = ⊥) (hxL : x ∈ Lgen M (LB M Q B))
    (hcx : ∀ z ∈ Z, ∃ c ∈ Q, c * x * c⁻¹ = x * z) {m : ℕ} (hm : 2 ≤ m)
    (hVz : ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥)
    (hVcard : Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m)
    {A : Subgroup G} (hA : IsZConjugate Z A) {a : G} (haA : a ∈ A) (haV : a ∈ V)
    (haC : a * x = x * a) (haZ : a ∉ Z) : QB A ⊓ QB X = ⊥ := by
  by_contra hne
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  obtain ⟨hAV, hAQ, hAZ⟩ := S.root_le_V hA haA haV haZ
  have h3 := S.V_le_QB hcond.c4 hA haA haV haZ
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    hA.mem_normalizer_of_commute S.hyp ha1 haA haC.symm
  have hxQ := S.x_not_mem_QB hs hQX hA haA (S.VQ haV) ha1
  have hX : IsZConjugate Z X := hs.conj
  have hx2 : x * x = 1 := hs.x_sq
  have hZQA := S.Z_le_QB hA hAQ
  obtain ⟨gA, rfl⟩ := hA
  have hV := S.V_le_conj h3
  obtain ⟨hx'L, hd1, hd2, -, hc7⟩ := cond_conj hcond S.hyp hX hs.mem hs.ne_one hxN hxQ hne
  have hx'2 : (gA⁻¹ * x * gA) * (gA⁻¹ * x * gA) = 1 := by
    have : (gA⁻¹ * x * gA) * (gA⁻¹ * x * gA) = gA⁻¹ * (x * x) * gA := by group
    rw [this, hx2]; group
  have hx'inv : (gA⁻¹ * x * gA)⁻¹ = gA⁻¹ * x * gA := inv_eq_of_mul_eq_one_right hx'2
  have hZ'in : ∀ z ∈ Z, gA⁻¹ * z * gA ∈ ⁅Q, Subgroup.zpowers (gA⁻¹ * x * gA)⁆ := by
    intro z hz
    obtain ⟨c, hcQ, hc⟩ := hcx z hz
    have hzQ : gA⁻¹ * z * gA ∈ Q := by
      have : z ∈ QB (conjSubgroup gA Z) := hZQA hz
      rw [QB_conj_eq S.hyp gA] at this
      exact mem_conjSubgroup.mp this
    have e : (gA⁻¹ * c * gA) * (gA⁻¹ * x * gA) * (gA⁻¹ * c * gA)⁻¹ =
        (gA⁻¹ * x * gA) * (gA⁻¹ * z * gA) := by
      calc _ = gA⁻¹ * (c * x * c⁻¹) * gA := by group
        _ = _ := by rw [hc]; group
    obtain ⟨q', hq'Q, hq'⟩ := hc7 (gA⁻¹ * c * gA) (gA⁻¹ * z * gA) hzQ e
    have h1 : (gA⁻¹ * x * gA) * (gA⁻¹ * z * gA) = q' * (gA⁻¹ * x * gA) * q'⁻¹ := by
      rw [← e]; exact hq'
    have hq : gA⁻¹ * z * gA = ⁅q', gA⁻¹ * x * gA⁆⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
      calc gA⁻¹ * z * gA = (gA⁻¹ * x * gA)⁻¹ * ((gA⁻¹ * x * gA) * (gA⁻¹ * z * gA)) := by group
        _ = (gA⁻¹ * x * gA)⁻¹ * (q' * (gA⁻¹ * x * gA) * q'⁻¹) := by rw [h1]
        _ = (gA⁻¹ * x * gA) * q' * (gA⁻¹ * x * gA)⁻¹ * q'⁻¹ := by
          rw [hx'inv]; group
    rw [hq]
    exact Subgroup.inv_mem _
      (Subgroup.commutator_mem_commutator hq'Q (Subgroup.mem_zpowers _))
  have hAne : conjSubgroup gA Z ≠ Z := hAZ
  have hVx : ⁅V, Subgroup.zpowers x⁆ ≤ Z ⊔ conjSubgroup gA Z := by
    rcases hV with h | h
    · have hVW : conjSubgroup gA⁻¹ V ≤ V := by
        have := (conjSubgroup_le_conjSubgroup_iff gA⁻¹).mpr h
        rwa [conjSubgroup_inv_conj] at this
      exact step5_core S hAne S.ZV hVW hx'L hx2 hd1 hZ'in
    · have hVW : conjSubgroup gA⁻¹ V ≤ V' := by
        have := (conjSubgroup_le_conjSubgroup_iff gA⁻¹).mpr h
        rwa [conjSubgroup_inv_conj] at this
      exact step5_core S.symm hAne S.ZV hVW hx'L hx2 hd2 hZ'in
  have hxNV : x ∈ Subgroup.normalizer (V : Set G) := S.normV x hxL
  have hVxV : ⁅V, Subgroup.zpowers x⁆ ≤ V := commutator_zpowers_le hxNV
  have hc1 : Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊔ Z) =
      Nat.card Z ^ m * Nat.card Z := by
    rw [card_sup_of_comm_inf_bot (fun a ha c hc => S.abV a (hVxV ha) c (S.ZV hc)) hVz, hVcard]
  have hZA : Z ⊓ conjSubgroup gA Z = ⊥ := inf_conjSubgroup_eq_bot_of_isTI S.hyp.ti hAne
  have hc2 : Nat.card ↥(Z ⊔ conjSubgroup gA Z) = Nat.card Z * Nat.card Z := by
    rw [card_sup_of_comm_inf_bot (fun a ha c hc => S.abV a (S.ZV ha) c (hAV hc)) hZA,
      card_conjSubgroup]
  have hle : Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊔ Z) ≤ Nat.card ↥(Z ⊔ conjSubgroup gA Z) :=
    Subgroup.card_le_of_le (sup_le hVx le_sup_left)
  rw [hc1, hc2] at hle
  have hq : 2 ≤ Nat.card Z := by have := S.hyp.q4; omega
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ m := Nat.pow_le_pow_right (by omega) hm
  nlinarith

end Odd
