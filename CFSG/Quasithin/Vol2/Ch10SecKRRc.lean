module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.LargeRee CFSG.RankThree.Chevalley
  CFSG.LieType.Simplicity

section G2


theorem two_le_pRank_G2_of_dvd {S : Type} [Group S] [Finite S] {f r : ℕ} (hr : r.Prime)
    (hrd : r ∣ 2 ^ f - 1) (h : UntwistedChevalleyModel S .G2 (2 ^ f)) :
    2 ≤ CFSG.pRank r S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted h
  obtain ⟨eT, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hTle : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact torusElt_mem_adjointGroup i u
  let g : Kˣ × Kˣ →* (Fin Tag.G2.rank → Kˣ) :=
    { toFun := fun p i => if (i : ℕ) = 0 then p.1 else p.2
      map_one' := by
        funext i
        simp
      map_mul' := fun p q => by
        funext i
        simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
        split_ifs <;> rfl }
  have hg : Function.Injective g := fun p q hpq => by
    have h0 := congrFun hpq ⟨0, by decide⟩
    have h1 := congrFun hpq ⟨1, by decide⟩
    simp only [g, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1
    exact Prod.ext (by simpa using h0) (by simpa using h1)
  let φ : Kˣ × Kˣ →* S :=
    e.toMonoidHom.comp ((Subgroup.inclusion hTle).comp (eT.toMonoidHom.comp g))
  have hφ : Function.Injective φ :=
    e.injective.comp ((Subgroup.inclusion_injective hTle).comp (eT.injective.comp hg))
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  exact two_le_pRank_of_injective_prod hr hcard hcard φ hφ

end G2

section D4


theorem two_le_pRank_3D4_of_dvd {S : Type} [Group S] [Finite S] {f r : ℕ} (hf : 1 ≤ f)
    (hr : r.Prime) (hrd : r ∣ 2 ^ f - 1) (h : TwistedChevalleyModel S .D4 (2 ^ f)) :
    2 ≤ CFSG.pRank r S := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted (by omega) h
  have : CharP K 2 := charP_two_of_natCard (by rw [hK, ← pow_mul])
  have h3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := Fintype.ofFinite K
    have hord : TwistTag.D4.order = 3 := rfl
    have hc : Fintype.card K = 2 ^ f * (2 ^ f * 2 ^ f) := by
      rw [← Nat.card_eq_fintype_card, hK, hord]
      ring
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, ← hc, FiniteField.pow_card]
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ3 : σ' ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  obtain ⟨-, ⟨eT, -⟩, -⟩ := even_triality_faithful_torus_coordinates K σ' hσ3
  obtain ⟨-, -, -, -, -, k₀, hk₀, hk₀card, -⟩ :=
    finite_graph_field_parameter_fields .D4 Nat.prime_two (by omega : 1 ≤ f) K hK
  have hkk : trialityFixedField K σ'.toRingHom = k₀ := SetLike.coe_injective (by
    rw [hk₀]
    ext c
    change σ c = c ↔ c ^ 2 ^ f = c
    rw [hσ])
  have hk : Nat.card (trialityFixedField K σ'.toRingHom) = 2 ^ f := by rw [hkk, hk₀card]
  have hcardk : r ∣ Nat.card (trialityFixedField K σ'.toRingHom)ˣ := by
    rw [Nat.card_units, hk]
    exact hrd
  have hcardK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 _)
  let e' : graphFixedRootGroup .D4 K σ'.toRingHom ≃* S := e
  let φ : Kˣ × (trialityFixedField K σ'.toRingHom)ˣ →* S :=
    e'.toMonoidHom.comp ((Subgroup.inclusion (graphFixedRootTorus_le .D4 K σ'.toRingHom)).comp
      eT.toMonoidHom)
  have hφ : Function.Injective φ :=
    e'.injective.comp ((Subgroup.inclusion_injective
      (graphFixedRootTorus_le .D4 K σ'.toRingHom)).comp eT.injective)
  exact two_le_pRank_of_injective_prod hr hcardK hcardk φ hφ

end D4

section F4


theorem two_le_pRank_2F4_of_dvd {S : Type} [Group S] [Finite S] {p f r : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) (hr : r.Prime) (hrd : r ∣ 2 ^ f - 1) :
    2 ≤ CFSG.pRank r S := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp
  obtain ⟨K, _, _, hK₀, ⟨e₀⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK₀])
  have : CharP K ReeTag.F4.prime := hc
  have hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := by
    rw [hK₀, hf]
    rfl
  have ha : 1 ≤ a := by omega
  have hperf := commutator_reeFixed_F4 a ha hK
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  have e' := (e₀.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K a)).trans
      ((reeFixed ReeTag.F4 K a).equivMapOfInjective _ Subtype.val_injective).symm))).trans
    (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))
  have e : S ≃* reeFixed ReeTag.F4 K a := e'.trans
    ((QuotientGroup.quotientMulEquivOfEq (reeFixed_F4_center_eq_bot a)).trans
      QuotientGroup.quotientBot)
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  let T₀ := reeTorusHom a hK fi_zero_mem_longSet
  let T₁ := reeTorusHom a hK fi_one_mem_longSet
  have hcomm : ∀ u v, Commute (T₀ u) (T₁ v) := fun u v =>
    commute_of_mem_reeTorusPart (reeTorusSub_le_reeTorusPart hK _ ⟨u, rfl⟩)
      (reeTorusSub_le_reeTorusPart hK _ ⟨v, rfl⟩)
  have hchar1 : ∀ k, simpleChar (1 : adjointGroup ReeTag.F4.tag K) k = 1 := fun k => by
    simp [simpleChar]
  have hT₀ : ∀ u, T₀ u = 1 → u = 1 := fun u hu => by
    have h1 : ReeTag.F4.reeTorus a (fi 0) u = 1 := congrArg Subtype.val hu
    have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
    simp only [simpleChar_reeTorus, reeExp_zero_zero, hchar1] at h2
    have h3 : ((u : K)) ^ 2 = 1 ^ 2 := by
      rw [one_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
      exact h2
    exact Units.ext (CharTwo.sq_injective h3)
  have hT₁ : ∀ v, T₁ v = 1 → v = 1 := fun v hv => by
    have h1 : ReeTag.F4.reeTorus a (fi 1) v = 1 := congrArg Subtype.val hv
    have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
    simp only [simpleChar_reeTorus, reeExp_one_zero, hchar1] at h2
    have h3 : v⁻¹ = 1 := Units.ext (by rw [← zpow_neg_one]; exact h2)
    exact inv_eq_one.1 h3
  let Ψ : Kˣ × Kˣ →* reeFixed ReeTag.F4 K a := MonoidHom.noncommCoprod T₀ T₁ hcomm
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ huv
    have h1 : T₀ u * T₁ v = 1 := huv
    have hmem : T₀ u ∈ reeTorusSub a hK fi_zero_mem_longSet ⊓
        reeTorusSub a hK fi_one_mem_longSet :=
      ⟨⟨u, rfl⟩, ⟨v⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left h1).symm⟩⟩
    rw [reeTorusSub_inf hK, Subgroup.mem_bot] at hmem
    have hu := hT₀ u hmem
    rw [hmem, one_mul] at h1
    have hv := hT₁ v h1
    rw [hu, hv]
    rfl
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK₀]
    exact hrd
  exact two_le_pRank_of_injective_prod hr hcard hcard
    (e.symm.toMonoidHom.comp Ψ) (e.symm.injective.comp hΨ)

end F4

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
