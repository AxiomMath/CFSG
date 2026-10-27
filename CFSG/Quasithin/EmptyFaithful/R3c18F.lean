module

public import CFSG.Quasithin.EmptyFaithful.R3c18A
public import CFSG.Quasithin.EmptyFaithful.R3c18Fam
public import CFSG.Quasithin.EmptyFaithful.R3c18G
public import CFSG.Quasithin.EmptyFaithful.R3c18Q
public import CFSG.Quasithin.Background.A318PF4Frame
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

theorem pow_two_pow_add_mul {K₀ : Type} [Field K₀] [Finite K₀] {f₀ : ℕ}
    (hK₀ : Nat.card K₀ = 2 ^ f₀) (c : K₀) (n m : ℕ) : c ^ 2 ^ (n + m * f₀) = c ^ 2 ^ n := by
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hq : ∀ x : K₀, x ^ 2 ^ f₀ = x := fun x => by
    rw [← hK₀, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) * f₀ = (n + m * f₀) + f₀ by ring, pow_add, pow_mul, hq, ih]

section BaseChange

set_option linter.unusedSectionVars false

variable {τ : Tag} {K₀ K : Type} [Field K₀] [Field K]

theorem baseChangeGL_mem_adj (ι : K₀ →+* K) {g : ModGL τ K₀} (hg : g ∈ adjointGroup τ K₀) :
    baseChangeGL ι g ∈ adjointGroup τ K := by
  have h : baseChangeGL ι g ∈ (adjointGroup τ K₀).map (baseChangeGL ι) := ⟨g, hg, rfl⟩
  rw [map_baseChangeGL_adjointGroup] at h
  refine (Subgroup.closure_le (adjointGroup τ K)).2 ?_ h
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact (xElement i (ι c)).2
  · exact (yElement i (ι c)).2

@[expose] noncomputable def baseChangeAdj (ι : K₀ →+* K) :
    adjointGroup τ K₀ →* adjointGroup τ K :=
  ((baseChangeGL ι).comp (adjointGroup τ K₀).subtype).codRestrict (adjointGroup τ K)
    fun g => baseChangeGL_mem_adj ι g.2

theorem baseChangeAdj_xElement (ι : K₀ →+* K) (i : Fin τ.rank) (c : K₀) :
    baseChangeAdj ι (xElement i c) = xElement i (ι c) :=
  Subtype.ext (baseChangeGL_xUnit ι i c)

theorem baseChangeAdj_yElement (ι : K₀ →+* K) (i : Fin τ.rank) (c : K₀) :
    baseChangeAdj ι (yElement i c) = yElement i (ι c) :=
  Subtype.ext (baseChangeGL_yUnit ι i c)

end BaseChange

section ReeEmbed

set_option linter.unusedSectionVars false

theorem finiteReeAut_xElement' (t : ReeTag) {K : Type} [Field K] [Finite K] [CharP K t.prime]
    (a : ℕ) (i : Fin t.tag.rank) (c : K) :
    t.finiteReeAut K a (xElement i c) = xElement (t.perm i) (c ^ t.relationExponent a i) := by
  have h := congrArg (fun f : adjointGroup t.tag K →* adjointGroup t.tag K => f (xElement i c))
    (finiteReeAut_toMonoidHom (t := t) (K := K) a)
  exact h.trans (reeEndo_xElement _ a i c)

theorem finiteReeAut_yElement' (t : ReeTag) {K : Type} [Field K] [Finite K] [CharP K t.prime]
    (a : ℕ) (i : Fin t.tag.rank) (c : K) :
    t.finiteReeAut K a (yElement i c) = yElement (t.perm i) (c ^ t.relationExponent a i) := by
  have h := congrArg (fun f : adjointGroup t.tag K →* adjointGroup t.tag K => f (yElement i c))
    (finiteReeAut_toMonoidHom (t := t) (K := K) a)
  exact h.trans (reeEndo_yElement _ a i c)

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime] [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem finiteReeAut_baseChange (ι : K₀ →+* K) {a₀ a : ℕ}
    (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1))
    (g : adjointGroup ReeTag.F4.tag K₀) :
    ReeTag.F4.finiteReeAut K a (baseChangeAdj ι g) =
      baseChangeAdj ι (ReeTag.F4.finiteReeAut K₀ a₀ g) := by
  have hext : (ReeTag.F4.finiteReeAut K a).toMonoidHom.comp (baseChangeAdj ι) =
      (baseChangeAdj ι).comp (ReeTag.F4.finiteReeAut K₀ a₀).toMonoidHom := by
    refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [baseChangeAdj_xElement, finiteReeAut_xElement', finiteReeAut_xElement',
        baseChangeAdj_xElement]
      congr 1
      by_cases hi : i ∈ ReeTag.F4.longSet
      · simp only [ReeTag.relationExponent, hi, ↓reduceIte]
        exact (h0 c).symm
      · simp only [ReeTag.relationExponent, hi, ↓reduceIte]
        exact (h1 c).symm
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [baseChangeAdj_yElement, finiteReeAut_yElement', finiteReeAut_yElement',
        baseChangeAdj_yElement]
      congr 1
      by_cases hi : i ∈ ReeTag.F4.longSet
      · simp only [ReeTag.relationExponent, hi, ↓reduceIte]
        exact (h0 c).symm
      · simp only [ReeTag.relationExponent, hi, ↓reduceIte]
        exact (h1 c).symm
  exact DFunLike.congr_fun hext g

end ReeEmbed

section GammaMap

set_option linter.unusedSectionVars false

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime] [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {ι : K₀ →+* K} {a₀ a : ℕ}

theorem baseChangeGL_mem_reeGamma (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1)) {g : ModGL ReeTag.F4.tag K₀}
    (hg : g ∈ ReeTag.F4.reeGamma K₀ a₀) : baseChangeGL ι g ∈ ReeTag.F4.reeGamma K a := by
  obtain ⟨hg', hF⟩ := mem_reeGamma.1 hg
  refine mem_reeGamma.2 ⟨baseChangeGL_mem_adj ι hg', ?_⟩
  have h := finiteReeAut_baseChange ι h0 h1 ⟨g, hg'⟩
  rw [hF] at h
  exact h

@[expose] noncomputable def reeGammaMap (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1)) :
    ReeTag.F4.reeGamma K₀ a₀ →* ReeTag.F4.reeGamma K a :=
  ((baseChangeGL ι).comp (ReeTag.F4.reeGamma K₀ a₀).subtype).codRestrict
    (ReeTag.F4.reeGamma K a) fun g => baseChangeGL_mem_reeGamma h0 h1 g.2

theorem coe_reeGammaMap (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1)) (g : ReeTag.F4.reeGamma K₀ a₀) :
    ((reeGammaMap h0 h1 g : ReeTag.F4.reeGamma K a) : ModGL ReeTag.F4.tag K) =
      baseChangeGL ι (g : ModGL ReeTag.F4.tag K₀) := rfl

theorem reeGammaMap_injective (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1)) :
    Function.Injective (reeGammaMap h0 h1) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))

theorem reeGammaFieldAut_reeGammaMap (h0 : ∀ c : K₀, ι (c ^ 2 ^ a₀) = (ι c) ^ 2 ^ a)
    (h1 : ∀ c : K₀, ι (c ^ 2 ^ (a₀ + 1)) = (ι c) ^ 2 ^ (a + 1)) (σ : K ≃+* K)
    (hσ : ∀ c : K₀, σ (ι c) = ι c) (g : ReeTag.F4.reeGamma K₀ a₀) :
    ReeTag.F4.reeGammaFieldAut K a σ (reeGammaMap h0 h1 g) = reeGammaMap h0 h1 g := by
  apply Subtype.ext
  rw [coe_reeGammaFieldAut, coe_reeGammaMap, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL]
  congr 2
  exact RingHom.ext hσ

end GammaMap

section Shape

set_option linter.unusedSectionVars false

@[expose] def F4ReeClass : Prop :=
  ∀ {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ {p : ℕ}, p.Prime → 5 ≤ p →
    2 ≤ CFSG.pRank p ↥(ReeTag.F4.reeGamma K a) →
    p ∣ 2 ^ (2 * a + 1) - 1 ∨ p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1

@[expose] def F4ReeRank : Prop :=
  ∀ {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ {p : ℕ}, p.Prime → 5 ≤ p →
    (p ∣ 2 ^ (2 * a + 1) - 1 ∨ p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) →
    2 ≤ CFSG.pRank p ↥(ReeTag.F4.reeGamma K a)

end Shape

section Frame

set_option linter.unusedSectionVars false

@[expose] noncomputable def pFrameF4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hcls : F4ReeClass)
    (hrk : F4ReeRank) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ)
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    PFrame p ↥(ReeTag.F4.reeGamma K a) (K ≃+* K) where
  fld := ReeTag.F4.reeGammaFieldAutHom K a
  fld_inter := fun c hc =>
    (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).2 c hc
  conj_mem := fun α _ _ => by
    obtain ⟨x, β, h⟩ := (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).1 α
    exact ⟨1, MulAut.conj x, ⟨x, rfl⟩, β, by rw [h, inv_one, one_mul, mul_one]; rfl⟩
  sq := fun h2 c hc => by
    have hf1 : 1 ≤ 2 * a + 1 := by omega
    obtain ⟨hpf, k, hk, hkcard⟩ := exists_fixed_subfield hf1 hK c hc
    obtain ⟨f₀, hf₀⟩ := hpf
    have hp0 : 0 < p := hp.pos
    have hdivq : (2 * a + 1) / p = f₀ := by rw [hf₀, Nat.mul_div_cancel_left _ hp0]
    rw [hdivq] at hkcard
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hf₀odd : Odd f₀ := by
      have : Odd (p * f₀) := by rw [← hf₀]; exact ⟨a, rfl⟩
      exact (Nat.odd_mul.1 this).2
    obtain ⟨a₀, ha₀⟩ := hf₀odd
    obtain ⟨m, hm⟩ := hpodd
    have hKk : 2 ^ (2 * a + 1) = (2 ^ f₀) ^ p := by rw [hf₀, mul_comm, pow_mul]
    have h2' : 2 * a + 1 = (2 * m + 1) * (2 * a₀ + 1) := by rw [hf₀, hm, ha₀]
    have haa : a = a₀ + m * f₀ := by rw [ha₀]; nlinarith [h2']
    have hK₀ : Nat.card k = 2 ^ (2 * a₀ + 1) := by rw [hkcard, ha₀]
    have hq0 : 0 < 2 ^ f₀ := pow_pos (by norm_num) _
    have h0 : ∀ x : k, (k.subtype : k →+* K) (x ^ 2 ^ a₀) = ((k.subtype : k →+* K) x) ^ 2 ^ a := by
      intro x
      rw [← map_pow, haa, pow_two_pow_add_mul hkcard x a₀ m]
    have h1 : ∀ x : k, (k.subtype : k →+* K) (x ^ 2 ^ (a₀ + 1)) =
        ((k.subtype : k →+* K) x) ^ 2 ^ (a + 1) := by
      intro x
      rw [← map_pow, show a + 1 = (a₀ + 1) + m * f₀ by rw [haa]; ring,
        pow_two_pow_add_mul hkcard x (a₀ + 1) m]
    have hcl := hcls hK hp hp5 h2
    rw [hKk] at hcl
    have hcl₀ : p ∣ 2 ^ (2 * a₀ + 1) - 1 ∨ p ∣ 2 ^ (2 * a₀ + 1) + 1 ∨
        p ∣ (2 ^ (2 * a₀ + 1)) ^ 2 + 1 := by
      rw [← ha₀]
      rcases hcl with h | h | h
      · refine Or.inl ?_
        have h' : p ∣ ((2 ^ f₀) ^ p) ^ 1 - 1 := by rwa [pow_one]
        simpa using (dvd_pow_sub_one_iff_of_pow hp hq0 1).1 h'
      · exact Or.inr (Or.inl (dvd_add_one_of_dvd_pow_add_one hp h))
      · refine Or.inr (Or.inr ?_)
        have h' : p ∣ ((2 ^ f₀) ^ 2) ^ p + 1 := by rwa [← pow_mul, mul_comm, pow_mul] at h
        exact dvd_add_one_of_dvd_pow_add_one hp h'
    have : CharP k ReeTag.F4.prime := RingHom.charP k.subtype k.subtype.injective ReeTag.F4.prime
    have hrk₀ : 2 ≤ CFSG.pRank p ↥(ReeTag.F4.reeGamma k a₀) := hrk hK₀ hp hp5 hcl₀
    obtain ⟨E₀, hE₀, hE₀el⟩ := exists_sq_of_two_le_pRank hp hrk₀
    refine ⟨E₀.map (reeGammaMap h0 h1), ?_, CFSG.SectionRank.isElemAbelian_map hE₀el _, ?_⟩
    · rw [Subgroup.card_map_of_injective (reeGammaMap_injective h0 h1), hE₀]
    · rintro _ ⟨y, -, rfl⟩
      exact reeGammaFieldAut_reeGammaMap h0 h1 c (fun x => hk _ x.2) y

theorem qLiePRankFam_f4 (hcls : F4ReeClass) (hrk : F4ReeRank) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧
      ReeTitsModel S CFSG.Assembly.LowTwoRank.StatedLieTag.twistedF4 2 f) := by
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hfo, hf3, hm⟩ hS2 hX
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model hm
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hK
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite ↥(ReeTag.F4.reeGamma K a) :=
    Finite.of_equiv ↥S (e.trans (CFSG.Quasithin.A318P.reeFixedEquivGamma a)).toEquiv
  exact pframe_core hC (((pFrameF4 hp hp5 hcls hrk K a ha hK').ofMulEquiv hp.one_lt
    (e.trans (CFSG.Quasithin.A318P.reeFixedEquivGamma a)))) hS2 hX

end Frame

end R3c18

end CFSG.Quasithin
