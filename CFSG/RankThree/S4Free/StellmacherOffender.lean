module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin

section Rel

variable {G : Type*} [Group G]

@[expose] noncomputable def mRel (H K : Subgroup G) : ℕ := padicValNat 2 (H.relIndex K)

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem mRel_inf_add [Finite G] (H K L : Subgroup G) (hHK : H ≤ K) :
    mRel H (K ⊓ L) + mRel K L = mRel H L := by
  unfold mRel
  rw [← padicValNat.mul (relIndex_ne_zero_of_finite H (K ⊓ L)) (relIndex_ne_zero_of_finite K L),
    Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.mpr hHK]

theorem relIndex_eq_two_pow [Finite G] {H K : Subgroup G} (hK : IsPGroup 2 K) :
    H.relIndex K = 2 ^ mRel H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  have hdvd : H.relIndex K ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card H K
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [mRel, hj, padicValNat.prime_pow]

theorem mRel_eq_zero_iff [Finite G] {H K : Subgroup G} (hK : IsPGroup 2 K) :
    mRel H K = 0 ↔ K ≤ H := by
  rw [← Subgroup.relIndex_eq_one, relIndex_eq_two_pow hK]
  constructor
  · intro h
    rw [h, pow_zero]
  · intro h
    exact (Nat.pow_eq_one.mp h).resolve_left (by norm_num)

theorem mRel_pos_iff [Finite G] {H K : Subgroup G} (hK : IsPGroup 2 K) :
    0 < mRel H K ↔ ¬ K ≤ H := by
  rw [Nat.pos_iff_ne_zero, Ne, mRel_eq_zero_iff hK]

theorem mRel_le_of_le_right [Finite G] {H K L : Subgroup G} (hL : IsPGroup 2 L) (hKL : K ≤ L) :
    mRel H K ≤ mRel H L := by
  have hle : H.relIndex K ≤ H.relIndex L :=
    Subgroup.relIndex_le_of_le_right hKL (relIndex_ne_zero_of_finite H L)
  rw [relIndex_eq_two_pow (hL.to_le hKL), relIndex_eq_two_pow hL] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem mRel_le_of_le_left [Finite G] {H K L : Subgroup G} (hL : IsPGroup 2 L) (hHK : H ≤ K) :
    mRel K L ≤ mRel H L := by
  have hle : K.relIndex L ≤ H.relIndex L :=
    Subgroup.relIndex_le_of_le_left hHK (relIndex_ne_zero_of_finite H L)
  rw [relIndex_eq_two_pow hL, relIndex_eq_two_pow hL] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

end Rel

variable {V : Type*} [CommGroup V]

@[expose] def ElemAbOn (B : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  (∀ a ∈ B, ∀ b ∈ B, ∀ u ∈ U, a (b u) = b (a u)) ∧ ∀ a ∈ B, ∀ u ∈ U, a (a u) = u

theorem ElemAbOn.mono {B C : Subgroup (MulAut V)} {U W : Subgroup V} (h : ElemAbOn B U)
    (hCB : C ≤ B) (hWU : W ≤ U) : ElemAbOn C W :=
  ⟨fun a ha b hb u hu => h.1 a (hCB ha) b (hCB hb) u (hWU hu),
    fun a ha u hu => h.2 a (hCB ha) u (hWU hu)⟩

theorem IsElemAbelian2.elemAbOn {B : Subgroup (MulAut V)} (h : IsElemAbelian2 B)
    (U : Subgroup V) : ElemAbOn B U := by
  refine ⟨fun a ha b hb u _ => ?_, fun a ha u _ => ?_⟩
  · change (a * b) u = (b * a) u
    rw [h.1 a ha b hb]
  · change (a ^ 2) u = u
    rw [h.2 a ha]
    rfl

@[expose] def IsOff (S B : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  B ≤ S ∧ ¬ U ≤ fixV B ∧ ElemAbOn B U

noncomputable abbrev dimOn (B : Subgroup (MulAut V)) (U : Subgroup V) : ℕ := mRel (centSub U) B

noncomputable abbrev codimOn (B : Subgroup (MulAut V)) (U : Subgroup V) : ℕ := mRel (fixV B) U

@[expose] def IsMinOff (S B : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  IsOff S B U ∧ ∀ C, IsOff S C U → codimOn B U * dimOn C U ≤ codimOn C U * dimOn B U

@[expose] def AGe (S : Subgroup (MulAut V)) (U : Subgroup V) (e : ℚ) : Prop :=
  ∀ B, IsOff S B U → e * dimOn B U ≤ codimOn B U

@[expose] def AGt (S : Subgroup (MulAut V)) (U : Subgroup V) (e : ℚ) : Prop :=
  ∀ B, IsOff S B U → e * dimOn B U < codimOn B U

@[expose] def ALe (S : Subgroup (MulAut V)) (U : Subgroup V) (e : ℚ) : Prop :=
  ∃ B, IsOff S B U ∧ (codimOn B U : ℚ) ≤ e * dimOn B U

theorem not_ale_iff {S : Subgroup (MulAut V)} {U : Subgroup V} {e : ℚ} :
    ¬ ALe S U e ↔ AGt S U e := by
  unfold ALe AGt
  push Not
  rfl

section Finite

variable [Finite V]

theorem IsOff.dimOn_pos {S B : Subgroup (MulAut V)} {U : Subgroup V} (hS : IsPGroup 2 S)
    (h : IsOff S B U) : 0 < dimOn B U := by
  rw [mRel_pos_iff (hS.to_le h.1)]
  intro hle
  exact h.2.1 fun u hu b hb => hle hb u hu

theorem IsOff.mono {S B C : Subgroup (MulAut V)} {U : Subgroup V} (h : IsOff S B U)
    (hCB : C ≤ B) (hC : ¬ U ≤ fixV C) : IsOff S C U :=
  ⟨hCB.trans h.1, hC, h.2.2.mono hCB le_rfl⟩

theorem isPGroup_subgroup (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V) : IsPGroup 2 U :=
  (isPGroup_two_of_sq_eq_one hV).to_subgroup U

theorem codimOn_eq_add {A A₀ : Subgroup (MulAut V)} (hA₀ : A₀ ≤ A) (U : Subgroup V) :
    codimOn A U = mRel (fixV A) (fixV A₀ ⊓ U) + codimOn A₀ U :=
  (mRel_inf_add (fixV A) (fixV A₀) U (B1.fixV_le_fixV hA₀)).symm

theorem dimOn_eq_add (A : Subgroup (MulAut V)) {U U' : Subgroup V} (hUU' : U ≤ U') :
    dimOn A U' = dimOn (A ⊓ centSub U) U' + dimOn A U := by
  have hle : centSub U' ≤ centSub U := fun g hg u hu => hg u (hUU' hu)
  have h := mRel_inf_add (centSub U') (centSub U) A hle
  rw [inf_comm] at h
  exact h.symm

theorem exists_isMinOff {S B : Subgroup (MulAut V)} {U : Subgroup V} (hS : IsPGroup 2 S)
    (hB : IsOff S B U) : ∃ A, IsMinOff S A U := by
  obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {C | IsOff S C U}
    (fun C => (codimOn C U : ℚ) / dimOn C U) (Set.toFinite _) ⟨B, hB⟩
  refine ⟨A, hA, fun C hC => ?_⟩
  have h := hmin C hC
  have hA0 : (0 : ℚ) < dimOn A U := by exact_mod_cast hA.dimOn_pos hS
  have hC0 : (0 : ℚ) < dimOn C U := by exact_mod_cast hC.dimOn_pos hS
  rw [div_le_div_iff₀ hA0 hC0] at h
  exact_mod_cast h

theorem exists_isMinOff_card {S B : Subgroup (MulAut V)} {U : Subgroup V} (hS : IsPGroup 2 S)
    (hB : IsOff S B U) :
    ∃ A, IsMinOff S A U ∧ ∀ C, IsMinOff S C U → Nat.card A ≤ Nat.card C := by
  obtain ⟨A₀, hA₀⟩ := exists_isMinOff hS hB
  obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {C | IsMinOff S C U} (fun C => Nat.card C)
    (Set.toFinite _) ⟨A₀, hA₀⟩
  exact ⟨A, hA, fun C hC => hmin C hC⟩

theorem codimOn_mul_le_or (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {U U' : Subgroup V}
    (hUU' : U ≤ U') :
    codimOn A U * dimOn A U' ≤ dimOn A U * codimOn A U' ∨
      codimOn (A ⊓ centSub U) U' * dimOn A U' < dimOn (A ⊓ centSub U) U' * codimOn A U' := by
  set A₀ := A ⊓ centSub U with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hUfix : U ≤ fixV A₀ ⊓ U' := fun u hu => ⟨fun g hg => hg.2 u hu, hUU' hu⟩
  have hy : codimOn A U ≤ mRel (fixV A) (fixV A₀ ⊓ U') :=
    mRel_le_of_le_right (isPGroup_subgroup hV _) hUfix
  have hc := codimOn_eq_add hA₀A U'
  have hd := dimOn_eq_add A hUU'
  by_cases h : codimOn A U * dimOn A U' ≤ dimOn A U * codimOn A U'
  · exact Or.inl h
  · right
    push Not at h
    set c := codimOn A U'
    set d := dimOn A U'
    set u := codimOn A U
    set p := dimOn A U
    set x := codimOn A₀ U'
    set q := dimOn A₀ U'
    set y := mRel (fixV A) (fixV A₀ ⊓ U')
    have h1 : x * d + u * d ≤ c * d := by
      rw [hc]
      nlinarith [Nat.mul_le_mul_right d hy]
    have h2 : c * d = q * c + p * c := by
      rw [hd]
      ring
    omega

theorem codimOn_mul_le_of_isMinOff (hV : ∀ v : V, v ^ 2 = 1) {S A : Subgroup (MulAut V)}
    {U U' : Subgroup V} (hS : IsPGroup 2 S) (hA : IsMinOff S A U') (hUU' : U ≤ U') :
    codimOn A U * dimOn A U' ≤ dimOn A U * codimOn A U' := by
  rcases codimOn_mul_le_or hV (A := A) hUU' with h | h
  · exact h
  · exfalso
    set A₀ := A ⊓ centSub U with hA₀
    by_cases hfix : U' ≤ fixV A₀
    ·
      have h0 : dimOn A₀ U' = 0 := by
        rw [mRel_eq_zero_iff (hS.to_le (inf_le_left.trans hA.1.1))]
        exact fun g hg u hu => hfix hu g hg
      rw [h0, zero_mul] at h
      exact Nat.not_lt_zero _ h
    · have hoff : IsOff S A₀ U' := hA.1.mono inf_le_left hfix
      have := hA.2 A₀ hoff
      linarith

theorem ale_of_isMinOff (hV : ∀ v : V, v ^ 2 = 1) {S A T : Subgroup (MulAut V)}
    {U U' : Subgroup V} (hS : IsPGroup 2 S) (hA : IsMinOff S A U') (hUU' : U ≤ U')
    (hU : ¬ U ≤ fixV A) (hAT : A ≤ T) {e : ℚ} (he : (codimOn A U' : ℚ) ≤ e * dimOn A U') :
    ALe T U e := by
  refine ⟨A, ⟨hAT, hU, hA.1.2.2.mono le_rfl hUU'⟩, ?_⟩
  have hd : (0 : ℚ) < dimOn A U' := by exact_mod_cast hA.1.dimOn_pos hS
  have h := codimOn_mul_le_of_isMinOff hV hS hA hUU'
  have h' : (codimOn A U : ℚ) * dimOn A U' ≤ dimOn A U * codimOn A U' := by exact_mod_cast h
  have h2 : (dimOn A U : ℚ) * codimOn A U' ≤ dimOn A U * (e * dimOn A U') :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have h3 : (codimOn A U : ℚ) * dimOn A U' ≤ (e * dimOn A U) * dimOn A U' := by
    linarith
  exact le_of_mul_le_mul_right h3 hd

theorem mem_map_conj_iff {g x : MulAut V} {B : Subgroup (MulAut V)} :
    x ∈ B.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ B := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem centSub_map (g : MulAut V) (Z : Subgroup V) :
    centSub (Z.map g.toMonoidHom) = (centSub Z).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj_iff, mem_centSub, mem_centSub]
  constructor
  · intro h z hz
    have := h (g z) ⟨z, hz, rfl⟩
    simp only [MulAut.mul_apply, MulAut.inv_apply, this]
    simp
  · rintro h _ ⟨z, hz, rfl⟩
    have := h z hz
    simp only [MulAut.mul_apply, MulAut.inv_apply] at this
    have h2 := congrArg g this
    simpa using h2

theorem fixV_map_conj (g : MulAut V) (B : Subgroup (MulAut V)) :
    fixV (B.map (MulAut.conj g).toMonoidHom) = (fixV B).map g.toMonoidHom := by
  ext v
  simp only [mem_fixV, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    refine ⟨g⁻¹ v, fun a ha => ?_, by simp⟩
    have := h (g * a * g⁻¹) ⟨a, ha, rfl⟩
    simp only [MulAut.mul_apply] at this
    have h3 : g (a (g⁻¹ v)) = g (g⁻¹ v) := by simpa using this
    exact g.injective h3
  · rintro ⟨w, hw, rfl⟩ x ⟨a, ha, rfl⟩
    have := hw a ha
    simp only [MulAut.conj_apply, MulAut.mul_apply]
    simp [this]

theorem dimOn_map_conj (g : MulAut V) (B : Subgroup (MulAut V)) (Z : Subgroup V) :
    dimOn (B.map (MulAut.conj g).toMonoidHom) (Z.map g.toMonoidHom) = dimOn B Z := by
  unfold dimOn mRel
  rw [centSub_map, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem codimOn_map_conj (g : MulAut V) (B : Subgroup (MulAut V)) (Z : Subgroup V) :
    codimOn (B.map (MulAut.conj g).toMonoidHom) (Z.map g.toMonoidHom) = codimOn B Z := by
  unfold codimOn mRel
  rw [fixV_map_conj, Subgroup.relIndex_map_map_of_injective _ _ g.injective]

theorem conj_off_facts (h : MulAut V) {A : Subgroup (MulAut V)} {Z : Subgroup V}
    (hA : ElemAbOn A (Z.map h.toMonoidHom)) (hZh : ¬ Z.map h.toMonoidHom ≤ fixV A) :
    ¬ Z ≤ fixV (A.map (MulAut.conj h⁻¹).toMonoidHom) ∧
      ElemAbOn (A.map (MulAut.conj h⁻¹).toMonoidHom) Z ∧
      dimOn (A.map (MulAut.conj h⁻¹).toMonoidHom) Z = dimOn A (Z.map h.toMonoidHom) ∧
      codimOn (A.map (MulAut.conj h⁻¹).toMonoidHom) Z = codimOn A (Z.map h.toMonoidHom) := by
  set B := A.map (MulAut.conj h⁻¹).toMonoidHom with hBdef
  have hAB : B.map (MulAut.conj h).toMonoidHom = A := by
    rw [hBdef, Subgroup.map_map]
    have : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x v
      simp
    rw [this, Subgroup.map_id]
  refine ⟨fun hle => hZh ?_, ⟨fun a ha b hb z hz => ?_, fun a ha z hz => ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ g hg
    have hg' : h⁻¹ * g * h ∈ B := by
      rw [mem_map_conj_iff, inv_inv]
      simpa [mul_assoc] using hg
    have := hle hz _ hg'
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg h this
    simpa using h2
  · rw [mem_map_conj_iff, inv_inv] at ha hb
    have hzh : h z ∈ Z.map h.toMonoidHom := ⟨z, hz, rfl⟩
    have := hA.1 _ ha _ hb (h z) hzh
    simp only [MulAut.mul_apply, MulAut.inv_apply] at this
    have h3 := congrArg h.symm this
    simpa using h3
  · rw [mem_map_conj_iff, inv_inv] at ha
    have hzh : h z ∈ Z.map h.toMonoidHom := ⟨z, hz, rfl⟩
    have := hA.2 _ ha (h z) hzh
    simp only [MulAut.mul_apply, MulAut.inv_apply] at this
    have h3 := congrArg h.symm this
    simpa using h3
  · rw [← dimOn_map_conj h B Z, hAB]
  · rw [← codimOn_map_conj h B Z, hAB]

theorem codimOn_ge_add (hV : ∀ v : V, v ^ 2 = 1) (A : Subgroup (MulAut V)) {U Z : Subgroup V}
    (hZU : Z ≤ U) :
    dimOn A U = dimOn (A ⊓ centSub Z) U + dimOn A Z ∧
      codimOn (A ⊓ centSub Z) U + codimOn A Z ≤ codimOn A U := by
  refine ⟨dimOn_eq_add A hZU, ?_⟩
  have hA₁ : A ⊓ centSub Z ≤ A := inf_le_left
  have hc := codimOn_eq_add hA₁ U
  have hZfix : Z ≤ fixV (A ⊓ centSub Z) ⊓ U := fun z hz => ⟨fun g hg => hg.2 z hz, hZU hz⟩
  have hle : codimOn A Z ≤ mRel (fixV A) (fixV (A ⊓ centSub Z) ⊓ U) :=
    mRel_le_of_le_right (isPGroup_subgroup hV _) hZfix
  omega

theorem mul_dimOn_le_codimOn (hV : ∀ v : V, v ^ 2 = 1) {H S N : Subgroup (MulAut V)}
    {U Z₀ : Subgroup V} (hN : IsPGroup 2 N) (hNS : N ≤ S)
    (hNH : H ≤ Subgroup.normalizer (N : Set (MulAut V))) (hHU : H ≤ stabSub U) (hZU : Z₀ ≤ U)
    (hgen : ∀ W : Subgroup V, (∀ h ∈ H, Z₀.map (h : MulAut V).toMonoidHom ≤ W) → U ≤ W)
    {e : ℚ} (ha : AGe S Z₀ e) {A : Subgroup (MulAut V)} (hAN : A ≤ N) (hA : ElemAbOn A U) :
    e * dimOn A U ≤ codimOn A U := by
  induction hn : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases hfix : U ≤ fixV A
  · have h0 : dimOn A U = 0 := by
      rw [mRel_eq_zero_iff (hN.to_le hAN)]
      exact fun g hg u hu => hfix hu g hg
    rw [h0]
    simp
  ·
    obtain ⟨h, hh, hZh⟩ : ∃ h ∈ H, ¬ Z₀.map (h : MulAut V).toMonoidHom ≤ fixV A := by
      by_contra hall
      push Not at hall
      exact hfix (hgen (fixV A) hall)
    set Zh := Z₀.map (h : MulAut V).toMonoidHom with hZhdef
    have hZhU : Zh ≤ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact ((hHU hh) z).2 (hZU hz)
    set A₁ := A ⊓ centSub Zh with hA₁def
    have hA₁lt : Nat.card A₁ < Nat.card A := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun heq => hZh ?_)
      intro z hz g hg
      exact (heq ▸ hg : g ∈ A₁).2 z hz
    have hIH := ih _ (hn ▸ hA₁lt) (inf_le_left.trans hAN) (hA.mono inf_le_left le_rfl) rfl
    obtain ⟨hBZ, hBel, hdim, hcodim⟩ := conj_off_facts h (hA.mono le_rfl hZhU) hZh
    have hBN : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ N := by
      intro x hx
      rw [mem_map_conj_iff, inv_inv] at hx
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hNH hh)) (h * x * h⁻¹)).mp (hAN hx)
      simpa [mul_assoc] using h1
    have hBe := ha _ ⟨hBN.trans hNS, hBZ, hBel⟩
    rw [hdim, hcodim] at hBe
    obtain ⟨hd, hc⟩ := codimOn_ge_add hV A hZhU
    have hc' : (codimOn A₁ U : ℚ) + codimOn A Zh ≤ codimOn A U := by exact_mod_cast hc
    rw [hd]
    push_cast
    linarith

theorem mul_dimOn_lt_codimOn (hV : ∀ v : V, v ^ 2 = 1) {H S N : Subgroup (MulAut V)}
    {U Z₀ : Subgroup V} (hN : IsPGroup 2 N) (hNS : N ≤ S)
    (hNH : H ≤ Subgroup.normalizer (N : Set (MulAut V))) (hHU : H ≤ stabSub U) (hZU : Z₀ ≤ U)
    (hgen : ∀ W : Subgroup V, (∀ h ∈ H, Z₀.map (h : MulAut V).toMonoidHom ≤ W) → U ≤ W)
    {e : ℚ} (ha : AGt S Z₀ e) {A : Subgroup (MulAut V)} (hAN : A ≤ N) (hA : ElemAbOn A U)
    (hAU : ¬ U ≤ fixV A) :
    e * dimOn A U < codimOn A U := by
  have ha' : AGe S Z₀ e := fun B hB => (ha B hB).le
  obtain ⟨h, hh, hZh⟩ : ∃ h ∈ H, ¬ Z₀.map (h : MulAut V).toMonoidHom ≤ fixV A := by
    by_contra hall
    push Not at hall
    exact hAU (hgen (fixV A) hall)
  set Zh := Z₀.map (h : MulAut V).toMonoidHom with hZhdef
  have hZhU : Zh ≤ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact ((hHU hh) z).2 (hZU hz)
  set A₁ := A ⊓ centSub Zh with hA₁def
  have hIH := mul_dimOn_le_codimOn hV hN hNS hNH hHU hZU hgen ha' (A := A₁)
    (inf_le_left.trans hAN) (hA.mono inf_le_left le_rfl)
  obtain ⟨hBZ, hBel, hdim, hcodim⟩ := conj_off_facts h (hA.mono le_rfl hZhU) hZh
  have hBN : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ N := by
    intro x hx
    rw [mem_map_conj_iff, inv_inv] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hNH hh)) (h * x * h⁻¹)).mp (hAN hx)
    simpa [mul_assoc] using h1
  have hBe := ha _ ⟨hBN.trans hNS, hBZ, hBel⟩
  rw [hdim, hcodim] at hBe
  obtain ⟨hd, hc⟩ := codimOn_ge_add hV A hZhU
  have hc' : (codimOn A₁ U : ℚ) + codimOn A Zh ≤ codimOn A U := by exact_mod_cast hc
  rw [hd]
  push_cast
  linarith

theorem centSub_top : centSub (⊤ : Subgroup V) = ⊥ := by
  ext g
  rw [mem_centSub, Subgroup.mem_bot]
  constructor
  · intro h
    exact MulEquiv.ext fun v => h v (Subgroup.mem_top v)
  · rintro rfl u _
    rfl

theorem dimOn_top (A : Subgroup (MulAut V)) : dimOn A ⊤ = rk A := by
  unfold dimOn mRel rk
  rw [centSub_top, Subgroup.relIndex_bot_left]

theorem codimOn_top (A : Subgroup (MulAut V)) : codimOn A ⊤ = rkIdx (fixV A) := by
  unfold codimOn mRel rkIdx
  rw [Subgroup.relIndex_top_right]

theorem elemAbOn_top_iff {A : Subgroup (MulAut V)} : ElemAbOn A ⊤ ↔ IsElemAbelian2 A := by
  refine ⟨fun h => ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, fun h => IsElemAbelian2.elemAbOn h ⊤⟩
  · exact MulEquiv.ext fun v => h.1 a ha b hb v (Subgroup.mem_top v)
  · exact MulEquiv.ext fun v => h.2 a ha v (Subgroup.mem_top v)

theorem fixV_eq_top_iff {A : Subgroup (MulAut V)} : (⊤ : Subgroup V) ≤ fixV A ↔ A = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    exact MulEquiv.ext fun v => h (Subgroup.mem_top v) a ha
  · rintro rfl
    rw [B1.fixV_bot]

theorem isOff_top_iff {S A : Subgroup (MulAut V)} : IsOff S A ⊤ ↔ IsA2 S A := by
  rw [IsOff, IsA2, elemAbOn_top_iff, fixV_eq_top_iff]

theorem card_mul_card_fixV_mul (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : IsPGroup 2 X) :
    Nat.card X * Nat.card (fixV X) * 2 ^ rkIdx (fixV X) = 2 ^ rk X * Nat.card V := by
  rw [card_eq_two_pow_of_isPGroup hX, B1.card_eq_index_mul X, B1.index_eq_two_pow hV]
  ring

theorem card_mul_card_fixV_le_iff (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hX : IsPGroup 2 X) (hY : IsPGroup 2 Y) :
    Nat.card X * Nat.card (fixV X) ≤ Nat.card Y * Nat.card (fixV Y) ↔
      rk X + rkIdx (fixV Y) ≤ rk Y + rkIdx (fixV X) := by
  have hXw := card_mul_card_fixV_mul hV hX
  have hYw := card_mul_card_fixV_mul hV hY
  have hV0 : 0 < Nat.card V := Nat.card_pos
  have key : Nat.card X * Nat.card (fixV X) * 2 ^ (rkIdx (fixV X) + rkIdx (fixV Y)) =
      2 ^ (rk X + rkIdx (fixV Y)) * Nat.card V := by
    rw [pow_add, ← mul_assoc, hXw, pow_add]
    ring
  have key' : Nat.card Y * Nat.card (fixV Y) * 2 ^ (rkIdx (fixV X) + rkIdx (fixV Y)) =
      2 ^ (rk Y + rkIdx (fixV X)) * Nat.card V := by
    rw [add_comm (rkIdx (fixV X)), pow_add, ← mul_assoc, hYw, pow_add]
    ring
  have hp : 0 < 2 ^ (rkIdx (fixV X) + rkIdx (fixV Y)) := by positivity
  rw [← Nat.mul_le_mul_right_iff hp, key, key', Nat.mul_le_mul_right_iff hV0,
    Nat.pow_le_pow_iff_right (by norm_num)]

theorem isQuadratic_of_isMinOff (hV : ∀ v : V, v ^ 2 = 1) {S A : Subgroup (MulAut V)}
    (hS : IsPGroup 2 S) (hA : IsMinOff S A ⊤) (hle : codimOn A ⊤ ≤ dimOn A ⊤)
    (hmin : ∀ B, IsMinOff S B ⊤ → Nat.card A ≤ Nat.card B) : IsQuadratic A := by
  have hA2 : IsA2 S A := isOff_top_iff.mp hA.1
  have hAp : IsPGroup 2 A := hS.to_le hA2.1
  rw [dimOn_top, codimOn_top] at hle
  set d := rk A
  set c := rkIdx (fixV A)
  have hd : 0 < d := hA2.rk_pos
  have hratio : ∀ B, IsA2 S B → c * rk B ≤ rkIdx (fixV B) * d := by
    intro B hB
    have := hA.2 B (isOff_top_iff.mpr hB)
    rwa [dimOn_top, dimOn_top, codimOn_top, codimOn_top] at this
  have hoff : IsFFStarOffender S A := by
    refine isFFStarOffender_iff.mpr ⟨hA2, fun B hBA => ?_⟩
    rw [card_mul_card_fixV_le_iff hV (hAp.to_le hBA) hAp]
    by_cases hB : B = ⊥
    · subst hB
      rw [rk_bot, B1.fixV_bot]
      have : rkIdx (⊤ : Subgroup V) = 0 := by simp [rkIdx]
      omega
    · have hB2 : IsA2 S B := hA2.mono hBA hB
      have h1 := hratio B hB2
      have hBd : rk B ≤ d := rk_mono hBA
      by_contra hlt
      push Not at hlt
      nlinarith
  refine B1_4_3 hV ⟨hoff, fun B _ hBA => ?_⟩
  obtain ⟨hB2, -, hBle, heq⟩ := hBA
  have hBp : IsPGroup 2 B := hAp.to_le hBle
  have h1 := (card_mul_card_fixV_le_iff hV hBp hAp).mp heq.le
  have h2 := (card_mul_card_fixV_le_iff hV hAp hBp).mp heq.ge
  have hBd : rk B ≤ d := rk_mono hBle
  have hBpos : 0 < rk B := hB2.rk_pos
  have hBmin : IsMinOff S B ⊤ := by
    refine ⟨isOff_top_iff.mpr hB2, fun C hC => ?_⟩
    have hC2 := isOff_top_iff.mp hC
    have hCA := hratio C hC2
    rw [dimOn_top, dimOn_top, codimOn_top, codimOn_top]
    have hBA' : rkIdx (fixV B) * d ≤ c * rk B := by nlinarith
    have hpos := hC2.rk_pos
    have key : rkIdx (fixV B) * rk C * d ≤ rkIdx (fixV C) * rk B * d := by
      nlinarith [Nat.mul_le_mul_right (rk C) hBA', Nat.mul_le_mul_right (rk B) hCA]
    exact Nat.le_of_mul_le_mul_right key hd
  exact Subgroup.eq_of_le_of_card_ge hBle (hmin B hBmin)

end Finite

end CFSG.RankThree.S4Free.Stell
