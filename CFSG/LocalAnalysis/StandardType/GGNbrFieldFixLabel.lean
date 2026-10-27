module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixCore
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRawFieldCycW (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧ (J.subgroupOf S).Normal ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S

theorem ggRawFieldCycW_of_pCyclic {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (h : GGRawPCyclic p R I F) : GGRawFieldCycW p R I F := fun hs hna => by
  obtain ⟨J, S, h1, h2, h3, h4, h5⟩ := h hs hna
  exact ⟨J, S, h1, h2, h3, h4, fun α _ hα => h5 α hα⟩

@[expose] def GGRawFieldNorm : LargeEvenRawCont :=
  fun R _ I F => ∀ f ∈ Subgroup.closure F, ∀ u ∈ I, f * u * f⁻¹ ∈ I

theorem ggRawFieldNorm_of_central {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hc : GGRawFieldCentral R I F) (hi : GGRawInnField p R I F) :
    IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGRawFieldNorm R I F := by
  intro hs hna f hf u hu
  obtain ⟨hmul, -, hconj, -⟩ := hi hs hna
  have h1 : (1 : MulAut R) ∈ I := by simpa using hconj 1
  have h := hc hs hna u⁻¹ 1 h1 f hf
  have h2 := hmul u hu _ h
  have e : u * (u⁻¹ * (1 * f) * u⁻¹⁻¹ * (1 * f)⁻¹) = f * u * f⁻¹ := by group
  rwa [e] at h2

theorem ggFixDer_conj_mem {R : Type} [Group R] (f u : MulAut R) (g : R) :
    g ∈ ggFixDer (u * f * u⁻¹) ↔ u⁻¹ g ∈ ggFixDer f := by
  have hfix : ggFixSub (u * f * u⁻¹) = (ggFixSub f).map (u : R →* R) := by
    ext a
    rw [mem_ggFixSub, Subgroup.mem_map]
    constructor
    · intro ha
      refine ⟨u⁻¹ a, ?_, ?_⟩
      · rw [mem_ggFixSub]
        have h := congrArg (fun x => u⁻¹ x) ha
        simpa [MulAut.mul_apply] using h
      · simp
    · rintro ⟨b, hb, rfl⟩
      rw [mem_ggFixSub] at hb
      simp [MulAut.mul_apply, hb]
  have hder : ggFixDer (u * f * u⁻¹) = (ggFixDer f).map (u : R →* R) := by
    unfold ggFixDer
    rw [hfix, Subgroup.map_commutator]
  rw [hder, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [← hk']
    simpa using hk
  · intro h
    exact ⟨u⁻¹ g, h, by simp⟩

private theorem ggConj_commute {R : Type} [Group R] {φ f u : MulAut R}
    (hφ : φ * (u * f * u⁻¹) = (u * f * u⁻¹) * φ) : (u⁻¹ * φ * u) * f = f * (u⁻¹ * φ * u) :=
  calc u⁻¹ * φ * u * f = u⁻¹ * (φ * (u * f * u⁻¹)) * u := by group
    _ = u⁻¹ * ((u * f * u⁻¹) * φ) * u := by rw [hφ]
    _ = f * (u⁻¹ * φ * u) := by group

theorem ggFixGeom_conj {R : Type} [Group R] {J : Subgroup (MulAut R)} {f u : MulAut R}
    (hu : u ∈ J) {R₀ : Type} [Group R₀] {I₀ : Set (MulAut R₀)} {θ₀ : ggFixDer f ≃* R₀}
    (h : GGFixGeom (J : Set (MulAut R)) f I₀ θ₀) :
    ∃ θ : ggFixDer (u * f * u⁻¹) ≃* R₀, GGFixGeom (J : Set (MulAut R)) (u * f * u⁻¹) I₀ θ := by
  let e : ggFixDer (u * f * u⁻¹) ≃* ggFixDer f :=
    { toFun := fun g => ⟨u⁻¹ (g : R), (ggFixDer_conj_mem f u (g : R)).1 g.2⟩
      invFun := fun k => ⟨u (k : R), by
        rw [ggFixDer_conj_mem]
        simpa using k.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp)
      map_mul' := fun g k => Subtype.ext (by simp) }
  have he : ∀ g : ggFixDer (u * f * u⁻¹), ((e g : ggFixDer f) : R) = u⁻¹ (g : R) :=
    fun _ => rfl
  refine ⟨e.trans θ₀, ?_⟩
  unfold GGFixGeom at h ⊢
  constructor
  · intro φ hφJ hφ
    let φ' : MulAut R := u⁻¹ * φ * u
    have hφ'J : φ' ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu
    have hφ' : φ' * f = f * φ' := ggConj_commute hφ
    obtain ⟨φ₀, hφ₀I₀, hφ₀⟩ := h.1 φ' hφ'J hφ'
    refine ⟨φ₀, hφ₀I₀, ?_⟩
    intro g hg
    have hmem : u⁻¹ g ∈ ggFixDer f := (ggFixDer_conj_mem f u g).1 hg
    calc (e.trans θ₀) ⟨φ g, ggFixDer_map_mem hφ hg⟩
        = θ₀ ⟨φ' (u⁻¹ g), ggFixDer_map_mem hφ' hmem⟩ := by
          rw [MulEquiv.trans_apply]
          congr 1
          apply Subtype.ext
          rw [he]
          dsimp only [φ']
          simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = φ₀ (θ₀ ⟨u⁻¹ g, hmem⟩) := hφ₀ (u⁻¹ g) hmem
      _ = φ₀ ((e.trans θ₀) ⟨g, hg⟩) := by
          rw [MulEquiv.trans_apply]
          have hsub : (⟨u⁻¹ g, hmem⟩ : ggFixDer f) = e ⟨g, hg⟩ := Subtype.ext (by rw [he])
          rw [hsub]
  · intro φ hφJ hφ hfixpt
    let φ' : MulAut R := u⁻¹ * φ * u
    have hφ'J : φ' ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu
    have hφ' : φ' * f = f * φ' := ggConj_commute hφ
    have hfixpt' : ∀ g ∈ ggFixDer f, φ' g = g := by
      intro g hg
      have hgx : u g ∈ ggFixDer (u * f * u⁻¹) := by
        rw [ggFixDer_conj_mem]
        simpa using hg
      have h1 : φ (u g) = u g := hfixpt (u g) hgx
      calc φ' g = u⁻¹ (φ (u g)) := by simp [φ', MulAut.mul_apply]
        _ = u⁻¹ (u g) := by rw [h1]
        _ = g := by simp
    have hφ'1 : φ' = 1 := h.2 φ' hφ'J hφ' hfixpt'
    have hφeq : φ = u * φ' * u⁻¹ := by
      ext n
      simp [φ', MulAut.mul_apply]
    rw [hφeq, hφ'1]
    simp

theorem ggClosure_union_eq_mul {G : Type*} [Group G] {J : Subgroup G} {F : Set G}
    (hnorm : ∀ f ∈ Subgroup.closure F, ∀ u ∈ J, f * u * f⁻¹ ∈ J) :
    ∀ x ∈ Subgroup.closure ((J : Set G) ∪ F), ∃ u ∈ J, ∃ f ∈ Subgroup.closure F, x = u * f := by
  intro x hx
  refine Subgroup.closure_induction (p := fun g _ =>
    ∃ u ∈ J, ∃ f ∈ Subgroup.closure F, g = u * f) ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, Subgroup.one_mem _, by rw [mul_one]⟩
    · exact ⟨1, Subgroup.one_mem _, y, Subgroup.subset_closure hy, by rw [one_mul]⟩
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [mul_one]⟩
  · rintro a b _ _ ⟨u, hu, f, hf, rfl⟩ ⟨v, hv, g, hg, rfl⟩
    exact ⟨u * (f * v * f⁻¹), J.mul_mem hu (hnorm f hf v hv), f * g,
      Subgroup.mul_mem _ hf hg, by group⟩
  · rintro a _ ⟨u, hu, f, hf, rfl⟩
    exact ⟨f⁻¹ * u⁻¹ * (f⁻¹)⁻¹, hnorm f⁻¹ (Subgroup.inv_mem _ hf) u⁻¹ (J.inv_mem hu),
      f⁻¹, Subgroup.inv_mem _ hf, by group⟩

theorem ggRawFieldFix_of_std {p : ℕ} {lab₀ : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (hconj : GGRawFieldConj p R I F) (hnorm : GGRawFieldNorm R I F)
    (hcyc : GGRawFieldCycW p R I F) (h : GGRawFieldFixStd p lab₀ R I F) :
    GGRawFieldFix p lab₀ R I F := by
  intro hs hna x hx hxI hxp
  obtain ⟨J, -, hJ, -, -, -, -⟩ := hcyc hs hna
  subst I
  obtain ⟨u, hu, f, hf, rfl⟩ := ggClosure_union_eq_mul hnorm x hx
  obtain ⟨f', hf', u', hu', hf'p, he⟩ := hconj hs hna u hu f hf hxI hxp
  have hstd := h hs hna f' hf' hf'p
  refine largeEvenRawDatum_mono ?_ hstd
  rintro R₀ _ I₀ F₀ ⟨hs₀, hna₀, θ₀, hgeom⟩
  rw [he]
  obtain ⟨θ, hθ⟩ := ggFixGeom_conj hu' hgeom
  exact ⟨hs₀, hna₀, θ, hθ⟩

theorem ggFixData_of_rawDatum {p r : ℕ} {lab₀ : LargeEvenLabel}
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    {R : Type} [Group R] {I : Set (MulAut R)} {x : MulAut R}
    (h : LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
      (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer x ≃* R₀, GGFixGeom I x I₀ θ₀) :
    GGFixData p r I x := by
  obtain ⟨R₀, inst₀, I₀, F₀, ⟨hs, hna, θ₀, hgeom⟩, -, hlift, hline⟩ :=
    largeEvenRawDatum_exists (hRow₀ _ h)
  exact ⟨R₀, inst₀, I₀, θ₀, hs, hna, hgeom, hlift, hline hs hna⟩

theorem largeEvenLabelAll_fieldFix {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r)
    {lab lab₀ : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hfix : LargeEvenLabelAll lab (GGRawFieldFix p lab₀)) :
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F := by
  refine (largeEvenLabelAll_and hRow (largeEvenLabelAll_and hcyc hfix)).mono ?_
  rintro R _ I F ⟨⟨hInn, hlift, hin⟩, hc, hf⟩ hs hna
  exact ggTorusFieldTransfer hp hr hInn (hin hs hna) (hc hs hna)
    fun x hx hxI hxp => ggFixData_of_rawDatum hRow₀ (hf hs hna x hx hxI hxp)

theorem largeEvenLabelAll_fieldKLevelComp_of_fix {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r)
    {lab lab₀ : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hfix : LargeEvenLabelAll lab (GGRawFieldFix p lab₀)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  largeEvenLabelAll_fieldKLevelComp_of_row hRow
    (largeEvenLabelAll_fieldFix hp hr hRow hRow₀ hcyc hfix)

theorem ggDvd_two_pow_sub_one_iff {p n : ℕ} (hp : p.Prime) (hn : p ∣ n) :
    p ∣ 2 ^ n - 1 ↔ p ∣ 2 ^ (n / p) - 1 := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left m hp.pos, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub Nat.one_le_two_pow, Nat.cast_sub Nat.one_le_two_pow]
  have key : (2 : ZMod p) ^ (p * m) = (2 : ZMod p) ^ m := by
    rw [mul_comm, pow_mul, ZMod.pow_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, key]

theorem ggFieldFixRowLabel_subfield {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hn : p ∣ lab.n) (h : GGFieldFixRowLabel p lab) :
    GGFieldFixRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩ :=
  ⟨(ggDvd_two_pow_sub_one_iff hp hn).mp h.1, h.2⟩

theorem three_le_ggFieldFixRank {p : ℕ} {lab : LargeEvenLabel} (h : GGFieldFixRowLabel p lab) :
    3 ≤ ggFieldFixRank lab := by
  obtain ⟨-, h⟩ := h
  unfold ggFieldFixRank
  rcases h with (h | h | h) | ⟨h | h, hr⟩ | ⟨h, hr, -⟩ | ⟨h, hr⟩ | ⟨h, hr⟩ | ⟨h, -⟩ <;>
    simp [h] <;> omega

theorem ggFieldFixRowLabel_not_triD4 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldFixRowLabel p lab) : ¬ (lab.tag = .triD4 ∧ p = 3) := by
  rintro ⟨ht, -⟩
  obtain ⟨-, h⟩ := h
  rcases h with (h | h | h) | ⟨h | h, hr⟩ | ⟨h, hr, -⟩ | ⟨h, hr⟩ | ⟨h, hr⟩ | ⟨h, -⟩ <;>
    simp [h] at ht

theorem ggFieldFixRowLabel_notD4Three {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldFixRowLabel p lab) : GGNotD4Three p lab := by
  rintro ⟨ht, hr4, hp3⟩
  obtain ⟨-, h⟩ := h
  rcases h with (h | h | h) | ⟨h | h, hr⟩ | ⟨h, hr, hne⟩ | ⟨h, hr⟩ | ⟨h, hr⟩ | ⟨h, -⟩ <;>
    simp [h] at ht
  exact hne ⟨hr4, hp3⟩

theorem largeEvenInLambda2_subfield {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hn : p ∣ lab.n) (h : GGFieldFixRowLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, hm⟩ := hlab
  have hdiv : 1 ≤ lab.n / p := Nat.div_pos (Nat.le_of_dvd hn1 hn) hp.pos
  refine ⟨hdiv, ?_⟩
  obtain ⟨-, h⟩ := h
  dsimp only at hm ⊢
  rcases h with (h | h | h) | ⟨h | h, hr⟩ | ⟨h, hr, -⟩ | ⟨h, hr⟩ | ⟨h, hr⟩ | ⟨h, -⟩ <;>
    rw [h] at hm ⊢ <;> simp only at hm ⊢ <;> first | omega | exact hm

theorem ggFieldKLevel_of_fixKnown {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGFieldFixLabel p lab) (hFix : GGFieldFixKnown S)
    (hRow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldFixRowLabel p lab →
        LargeEvenLabelAll lab (GGNbrWeylRowPlain p (ggFieldFixRank lab)))
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hSl
  obtain ⟨hdvd, hrow⟩ := hS p lab hSl
  have hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p (ggFieldFixRank lab)) :=
    hRow p lab hp hp2 hlab hrow
  have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / p⟩
      (GGNbrWeylRowPlain p (ggFieldFixRank lab)) :=
    hRow p _ hp hp2 (largeEvenInLambda2_subfield hp hlab hdvd hrow)
      (ggFieldFixRowLabel_subfield hp hdvd hrow)
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p (ggFieldFixRank lab)) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab (ggFieldFixRowLabel_notD4Three hrow)).mono fun _ _ _ _ h =>
      ggRawFieldCycW_of_pCyclic h
  have hAll := largeEvenLabelAll_and (hconj p hp hp2 lab hlab (ggFieldFixRowLabel_not_triD4 hrow))
    (largeEvenLabelAll_and (hcen lab hlab) (largeEvenLabelAll_and (hinn p hp hp2 lab hlab)
      (hFix p lab hp hp2 hlab hSl)))
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p ⟨lab.tag, lab.rank, lab.n / p⟩) :=
    (largeEvenLabelAll_and hCyc hAll).mono fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
      ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldKLevelComp_of_fix hp (three_le_ggFieldFixRank hrow) hRK hR₀
    hCyc hFx

theorem ggNbrInnerWeylOn_of_fieldFixKLevel (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) {S T : ℕ → LargeEvenLabel → Prop}
    (hK : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p))
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ S p lab) : GGNbrInnerWeylOn T :=
  (hT.or (ggNbrInnerWeylOn_of_fieldLabelsComp hL hPJ hG hK)).mono fun p lab hr => by
    by_cases h : S p lab
    · exact Or.inr h
    · exact Or.inl ⟨hr, h⟩

end CFSG.StandardType

end
