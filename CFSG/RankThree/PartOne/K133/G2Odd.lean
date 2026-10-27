module

public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.K133.InnerRed

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.K1214 CFSG.Timmesfeld.ExceptionalOrders

theorem card_le_pow_of_pi_cyclic {ι : Type} [Fintype ι] {M : Type} [CommGroup M] [Finite M] [IsCyclic M]
    {p : ℕ} (hp : p.Prime) (E : Subgroup (ι → M)) (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ Fintype.card ι := by
  classical
  have : Fintype M := Fintype.ofFinite M
  let f : E → (ι → {x : M // x ^ p = 1}) := fun x i =>
    ⟨(x : ι → M) i, by
      have := congrFun (hE x x.2) i
      simpa using this⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  have hM : Nat.card {x : M // x ^ p = 1} ≤ p := by
    have := IsCyclic.card_pow_eq_one_le (α := M) hp.pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  calc Nat.card E ≤ Nat.card (ι → {x : M // x ^ p = 1}) := Nat.card_le_card_of_injective f hf
    _ = Nat.card {x : M // x ^ p = 1} ^ Fintype.card ι := by
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ]
    _ ≤ p ^ Fintype.card ι := Nat.pow_le_pow_left hM _

set_option linter.unusedSectionVars false

theorem exists_injective_G2_split_odd (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) {e : ℕ} (he : p ^ e ∣ Nat.card K - 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* adjointGroup .G2 K,
      Function.Injective Ψ := by
  obtain ⟨-, ⟨φ⟩, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hK hp hp3 hpq
  obtain ⟨ι, hι⟩ := exists_injective_units (K := K) he
  let π₂ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* (Fin Tag.G2.rank → Kˣ) :=
    MonoidHom.pi fun i =>
      ι.comp (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative (ZMod (p ^ e))) i)
  have hπ₂ : Function.Injective π₂ := fun x y h => funext fun i => hι (congrFun h i)
  have hle : torusGroup .G2 K ≤ adjointGroup .G2 K := torusGroup_le_adjointGroup'
  refine ⟨(Subgroup.inclusion hle).comp (φ.toMonoidHom.comp π₂), ?_⟩
  exact (Subgroup.inclusion_injective hle).comp (φ.injective.comp hπ₂)

theorem exists_injective_G2_qplus_odd (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) {e : ℕ}
    (he : p ^ e ∣ Nat.card K + 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* adjointGroup .G2 K,
      Function.Injective Ψ := by
  let K₂ : Type := FiniteField.Extension K ℓ 2
  have hdeg : Module.finrank K K₂ = 2 := FiniteField.finrank_extension K ℓ 2
  let σ : K₂ ≃+* K₂ := (FiniteField.Extension.frob K ℓ 2).toRingEquiv
  have hσ : ∀ c, σ c = c ^ Nat.card K := fun c => FiniteField.Extension.frob_apply K ℓ 2 (x := c)
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φ⟩, -⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hK hp hp3 hpq K₂ hdeg σ hσ
  have hm : Nat.card K + 1 ≠ 0 := Nat.succ_ne_zero _
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_injective_of_dvd hm hm he he
  let ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  have hle : torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g :=
    inf_le_right
  refine ⟨ε.symm.toMonoidHom.comp ((Subgroup.inclusion hle).comp (φ.symm.toMonoidHom.comp Ψ₀)), ?_⟩
  exact ε.symm.injective.comp ((Subgroup.inclusion_injective hle).comp
    (φ.symm.injective.comp hΨ₀))

theorem sylowShape_G2_odd (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hd : p ∣ Nat.card K ^ 2 - 1) :
    SylowShape p 2 ((Nat.card K ^ 2 - 1).factorization p) (adjointGroup .G2 K) := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have hord : (Nat.card (adjointGroup .G2 K)).factorization p =
      2 * (Nat.card K ^ 2 - 1).factorization p := by
    rw [card_adjointGroup_G2]
    exact factorization_ordG2 hp hp5 hQ hpK hd
  rcases dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_split_odd K hK hp (by omega) h1 h2
    exact sylowShape_of_injective hp Ψ hΨ hord
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_qplus_odd K hK hp (by omega) h1 h2
    exact sylowShape_of_injective hp Ψ hΨ hord

theorem card_le_sq_of_sylowShape {X : Type*} [Group X] [Finite X] {p e : ℕ} (hp : p.Prime)
    (hs : SylowShape p 2 e X) (A : Subgroup X) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (IsElementaryAbelian.isPGroup p A)
  obtain ⟨φ⟩ := hs (S : Subgroup X) S.isPGroup' (Sylow.not_dvd_index S)
  let A' : Subgroup (S : Subgroup X) := A.subgroupOf S
  let E : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e))) := A'.map φ.toMonoidHom
  have hE : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have hap : (a : X) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (a : X) (Subgroup.mem_subgroupOf.1 ha)
    have : a ^ p = 1 := Subtype.ext hap
    rw [← map_pow]
    simp [this]
  have hcard : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv
  have := card_le_pow_of_pi_cyclic hp E hE
  rw [hcard] at this
  simpa using this

theorem cyclic_pSubgroups_G2_odd (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hdvd : p ∣ Nat.card (adjointGroup .G2 K)) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) :
    ∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P → IsCyclic P := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hy : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [card_adjointGroup_G2] at hdvd
  have h6 : p ∣ Nat.card K ^ 6 - 1 := by
    unfold ordG2 at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpK
      · exact h
    · exact absurd h hnd
  have hfac : Nat.card K ^ 6 - 1 =
      (Nat.card K ^ 2 - 1) * ((Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1) := by
    have := pow3_sub_one (Nat.card K ^ 2) hy
    rwa [← pow_mul] at this
  rw [hfac] at h6
  have hΦ : p ∣ (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 :=
    ((Nat.Prime.dvd_mul hp).1 h6).resolve_left hnd
  have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hΦfac : (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 =
      (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 - Nat.card K + 1) := by
    zify [hle]
    ring
  rw [hΦfac] at hΦ
  rcases (Nat.Prime.dvd_mul hp).1 hΦ with h | h
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK 1
      (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hp (by omega) h
    exact hcyc
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK (-1)
      (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hle]; ring) hp
      (by omega) h
    exact hcyc

theorem card_le_sq_G2_odd (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (A : Subgroup (adjointGroup .G2 K)) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  by_cases hdvd : p ∣ Nat.card (adjointGroup .G2 K)
  · by_cases hd : p ∣ Nat.card K ^ 2 - 1
    · exact card_le_sq_of_sylowShape hp (sylowShape_G2_odd K hK hp hp5 hpK hd) A hA
    · have hcyc := cyclic_pSubgroups_G2_odd K hK hp hp5 hpK hdvd hd A (IsElementaryAbelian.isPGroup p A)
      have hexp : Monoid.exponent ↥A ∣ p := IsElementaryAbelian.exponent_dvd_p p A
      rw [IsCyclic.exponent_eq_card] at hexp
      have := Nat.le_of_dvd hp.pos hexp
      calc Nat.card A ≤ p := this
        _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  · have hpg : IsPGroup p A := IsElementaryAbelian.isPGroup p A
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [hn, h0]
      simp only [pow_zero]
      exact Nat.one_le_pow _ _ hp.pos
    · exfalso
      apply hdvd
      have h1 : p ∣ Nat.card A := by
        rw [hn]
        exact dvd_pow_self p hpos.ne'
      exact h1.trans (Subgroup.card_subgroup_dvd_card A)

theorem noRankThree_G2_odd (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hin : ∀ E : Subgroup (MulAut (adjointGroup .G2 K)), IsElementaryAbelian p E →
      E ≤ ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K)) :
    NoRankThree p (adjointGroup .G2 K) := by
  have : Fact p.Prime := ⟨hp⟩
  refine noRankThree_of_inner_rank_el hp center_adjointGroup_eq_bot hin ?_
  intro A hA hAc
  have hle := card_le_sq_G2_odd K hK hp hp5 hpK A hA
  rw [hAc] at hle
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartOne.K133
