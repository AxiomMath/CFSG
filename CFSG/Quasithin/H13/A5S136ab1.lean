module

public import CFSG.Quasithin.H13.A5ConfSpor
public import CFSG.Quasithin.H13.NQCatKG68U33
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal
public import CFSG.Quasithin.H13.KGFactA23Cyclic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace ConfAB

variable {G : Type} [Group G] {S : Type} [Group S]

theorem pCore_two_le_center [Finite G] {K : Subgroup G} (hqs : CFSG.IsQuasisimple ↥K) :
    CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (N := CFSG.pCore 2 ↥K)
      CFSG.pCore_normal with hN | hN
  · exfalso
    have : Group.IsPerfect ↥K := hqs.1
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    have hp : IsPGroup 2 ↥K := by
      have h1 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
      rw [hN] at h1
      exact h1.of_equiv Subgroup.topEquiv
    exact Group.IsPerfect.not_isNilpotent ↥K hp.isNilpotent
  · exact hN

@[expose] noncomputable def indHom (K : Subgroup G) (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut S where
  toFun c := MulAut.congr ψ (KG68.quotAut (CFSG.pCore 2 ↥K) (K.normalizerMonoidHom c))
  map_one' := by rw [map_one, KG68.quotAut_one, map_one]
  map_mul' c d := by rw [map_mul, KG68.quotAut_mul, map_mul]

theorem indHom_apply (K : Subgroup G) (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S)
    (c : ↥(Subgroup.normalizer (K : Set G))) (x : ↥K) :
    indHom K ψ c (ψ (x : ↥K ⧸ CFSG.pCore 2 ↥K)) =
      ψ ((K.normalizerMonoidHom c x : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  show ψ (KG68.quotAut _ _ (ψ.symm (ψ (x : ↥K ⧸ CFSG.pCore 2 ↥K)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem mem_centralizer_of_indHom_eq_one [Finite G] {K : Subgroup G} (hqs : CFSG.IsQuasisimple ↥K)
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S) {c : ↥(Subgroup.normalizer (K : Set G))}
    (h : indHom K ψ c = 1) : (c : G) ∈ Subgroup.centralizer (K : Set G) := by
  have h1 : KG68.quotAut (CFSG.pCore 2 ↥K) (K.normalizerMonoidHom c) = 1 :=
    (MulAut.congr ψ).injective (h.trans (map_one _).symm)
  have h2 := KG68.eq_one_of_quotAut_eq_one (pCore_two_le_center hqs)
    (Group.isPerfect_def.mp hqs.1) h1
  exact (ConfSpor.normalizerMonoidHom_eq_one_iff c.2).mp h2

theorem indHom_eq_one_of_mem_centralizer (K : Subgroup G) (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S)
    {c : ↥(Subgroup.normalizer (K : Set G))}
    (h : (c : G) ∈ Subgroup.centralizer (K : Set G)) : indHom K ψ c = 1 := by
  have h1 : K.normalizerMonoidHom c = 1 := (ConfSpor.normalizerMonoidHom_eq_one_iff c.2).mpr h
  show MulAut.congr ψ (KG68.quotAut (CFSG.pCore 2 ↥K) (K.normalizerMonoidHom c)) = 1
  rw [h1, KG68.quotAut_one, map_one]

theorem eq_one_of_mem_center_of_two_pow [Finite G] {K : Subgroup G}
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S) {c : S} (hc : c ∈ Subgroup.center S) {k : ℕ}
    (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : ψ.symm c ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (ψ g)
  have h2 : ψ.symm c ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h3 := KG68.eq_one_of_mem_center_quot h1 h2
  simpa using congrArg ψ h3

theorem exists_conj_of_conf [Finite G] [Finite S] {K X Q : Subgroup G} {a z l : G}
    (hqs : CFSG.IsQuasisimple ↥K) (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S)
    (hinn : ∀ β : S ≃* S, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 S, ∀ t ∈ (P : Subgroup S), β t = t) → Ch1.IsInnerAut β)
    (hconf : Conf1366 K X Q a z l) :
    ∃ (P : Sylow 2 S) (u w : S) (haN : a ∈ Subgroup.normalizer (K : Set G))
      (hzN : z ∈ Subgroup.normalizer (K : Set G)),
      u ∈ KG68.omegaZ (P : Subgroup S) ∧ w ∈ KG68.omegaZ (P : Subgroup S) ∧ u ≠ 1 ∧ w ≠ 1 ∧
      u ≠ w ∧ indHom K ψ ⟨a, haN⟩ = MulAut.conj u ∧ indHom K ψ ⟨z, hzN⟩ = MulAut.conj w := by
  obtain ⟨hKX, hXN, hQ, haQ, hzQ, ha2, hz2, haC, hzC, ha1, hz1, haz, -, -, -, -, -⟩ := hconf
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥K with hNdef
  obtain ⟨PK, hPKQ⟩ := KGL33.exists_sylow_le hKX hXN hQ
  let f : ↥K →* S := ψ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  let Qs : Sylow 2 S := PK.mapSurjective hf
  have hZKs : ∀ c ∈ Subgroup.center S, ∀ k : ℕ, c ^ 2 ^ k = 1 → c = 1 :=
    fun c hc k hk => eq_one_of_mem_center_of_two_pow ψ hc hk
  have key : ∀ c ∈ Q, c ^ 2 = 1 →
      (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G), ∃ g ∈ KG68.omegaZ (Qs : Subgroup S),
        indHom K ψ ⟨c, hcN⟩ = MulAut.conj g := by
    intro c hcQ hc2 hc hcN
    set β := indHom K ψ ⟨c, hcN⟩ with hβ
    have hfix : ∀ t ∈ (Qs : Subgroup S), β t = t := by
      intro t ht
      have ht' : t ∈ (PK : Subgroup ↥K).map f := ht
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ht'
      show indHom K ψ ⟨c, hcN⟩ (ψ (p : ↥K ⧸ N)) = ψ (p : ↥K ⧸ N)
      rw [indHom_apply, ConfSpor.mk_conj_eq hQ.2.1 hcN hcQ (hPKQ p hp) (hc p (hPKQ p hp))]
    have hsq' : β * β = 1 := by
      have h1 : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) *
          ⟨c, hcN⟩ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hc2, Subgroup.coe_one])
      rw [hβ, ← map_mul, h1, map_one]
    have hinv : ∀ x, β (β x) = x := fun x => by
      have := congrArg (fun γ : MulAut S => γ x) hsq'
      simpa using this
    exact ConfSpor.exists_omegaZ_of_inner hZKs Qs β hsq' hfix (hinn β hinv ⟨Qs, hfix⟩)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 haQ)
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hzQ)
  obtain ⟨ga, hga, hγa⟩ := key a haQ ha2 haC haN
  obtain ⟨gz, hgz, hγz⟩ := key z hzQ hz2 hzC hzN
  have hga1 : ga ≠ 1 := by
    rintro rfl
    rw [map_one] at hγa
    exact ha1 (mem_centralizer_of_indHom_eq_one hqs ψ hγa)
  have hgz1 : gz ≠ 1 := by
    rintro rfl
    rw [map_one] at hγz
    exact hz1 (mem_centralizer_of_indHom_eq_one hqs ψ hγz)
  have hgaz : ga ≠ gz := by
    intro h
    have hN' : a * z⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ haN (Subgroup.inv_mem _ hzN)
    have he : (⟨a * z⁻¹, hN'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨a, haN⟩ * (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
    have h1 : indHom K ψ ⟨a * z⁻¹, hN'⟩ = 1 := by
      rw [he, map_mul, map_inv, hγa, hγz, h, mul_inv_cancel]
    exact haz (mem_centralizer_of_indHom_eq_one hqs ψ h1)
  exact ⟨Qs, ga, gz, haN, hzN, hga, hgz, hga1, hgz1, hgaz, hγa, hγz⟩

end ConfAB

open ConfAB in
theorem not_conf1366_of_inner_cyclic {G : Type} [Group G] [Finite G] {K X Q : Subgroup G}
    {a z l : G} (hqs : CFSG.IsQuasisimple ↥K) {S : Type} [Group S] [Finite S]
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S)
    (hinn : ∀ β : S ≃* S, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 S, ∀ t ∈ (P : Subgroup S), β t = t) → Ch1.IsInnerAut β)
    (hcyc : ∀ T : Sylow 2 S, IsCyclic (Subgroup.center ↥(T : Subgroup S))) :
    ¬ Conf1366 K X Q a z l := by
  intro hconf
  obtain ⟨P, u, w, -, -, hu, hw, hu1, hw1, huw, -, -⟩ := exists_conj_of_conf hqs ψ hinn hconf
  have h1mem : (1 : S) ∈ KG68.omegaZ (P : Subgroup S) :=
    KG68.mem_omegaZ_of_commute P (fun t _ => by rw [one_mul, mul_one]) (one_mul 1)
  exact ConfSpor.false_of_three_le (KG68.card_omegaZ_le_two (P : Subgroup S) (hcyc P)) h1mem hu
    hw (Ne.symm hu1) (Ne.symm hw1) huw

open ConfAB in
theorem not_conf1366_of_zcent {G : Type} [Group G] [Finite G] {K X Q : Subgroup G}
    {a z l : G} (hqs : CFSG.IsQuasisimple ↥K) {S : Type} [Group S] [Finite S]
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* S) (hZ : ∀ x : S, (∀ y, x * y = y * x) → x = 1)
    (hinn : ∀ β : S ≃* S, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 S, ∀ t ∈ (P : Subgroup S), β t = t) → Ch1.IsInnerAut β)
    (hlinn : ∀ hlN : l ∈ Subgroup.normalizer (K : Set G), ∃ k : S,
      indHom K ψ ⟨l, hlN⟩ = MulAut.conj k)
    (hZC : ∀ (P : Sylow 2 S) (u w k : S),
      u ∈ (P : Subgroup S) → (∀ t ∈ (P : Subgroup S), u * t = t * u) → u ≠ 1 →
      w ∈ (P : Subgroup S) → (∀ t ∈ (P : Subgroup S), w * t = t * w) →
      Odd (orderOf k) → k * u = u * k → k * w = w * k) :
    ¬ Conf1366 K X Q a z l := by
  intro hconf
  obtain ⟨P, u, w, haN, hzN, hu, hw, hu1, -, -, hγa, hγz⟩ := exists_conj_of_conf hqs ψ hinn hconf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hlN, hlodd, hla, hlz⟩ := hconf
  obtain ⟨k, hk⟩ := hlinn hlN
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => hZ x fun y => ?_
    have := congrArg (fun f : MulAut S => f y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hkodd : Odd (orderOf k) := by
    rw [← orderOf_injective MulAut.conj hconj k, ← hk]
    refine hlodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    have h1 : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf l = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [← map_pow, h1, map_one]
  have hcomm : ∀ (x : G) (hxN : x ∈ Subgroup.normalizer (K : Set G)) (g : S),
      indHom K ψ ⟨x, hxN⟩ = MulAut.conj g →
      ∃ hN : l * x * l⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G),
        indHom K ψ ⟨_, hN⟩ = MulAut.conj (k * g * k⁻¹ * g⁻¹) := by
    intro x hxN g hg
    have hN : l * x * l⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN)
        (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hxN)
    refine ⟨hN, ?_⟩
    have he : (⟨_, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ *
          (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
    rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hk, hg, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul]
  obtain ⟨hNa, hka⟩ := hcomm a haN u hγa
  have hku : k * u = u * k := by
    have h1 := (indHom_eq_one_of_mem_centralizer K ψ (c := ⟨_, hNa⟩) hla).symm.trans hka
    have h2 : k * u * k⁻¹ * u⁻¹ = 1 := hconj (h1.symm.trans (map_one _).symm)
    calc k * u = (k * u * k⁻¹ * u⁻¹) * u * k := by group
      _ = u * k := by rw [h2, one_mul]
  have hkw : k * w = w * k := hZC P u w k hu.1 hu.2.1 hu1 hw.1 hw.2.1 hkodd hku
  obtain ⟨hNz, hkz⟩ := hcomm z hzN w hγz
  have h3 : k * w * k⁻¹ * w⁻¹ = 1 := by rw [hkw]; group
  rw [h3, map_one] at hkz
  exact hlz (mem_centralizer_of_indHom_eq_one hqs ψ hkz)

@[expose] def CaseABTwoList (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ StatedClassicalModel X .PSL n 2 1) ∨
    ChevalleyExceptionalModel X .trialityD4 2 1 ∨ ReeTitsModel X .Tits 2 1 ∨
    StatedClassicalModel X .PSU 3 3 1

theorem isCyclic_center_sylow_of_two {X : Type} [Group X] [Finite X]
    (hD4 : KG68.TrialityTwoSylowCenterCyclic) (hTits : KG68.TitsSylowCenterCyclic)
    (hX : CaseABTwoList X) (T : Sylow 2 X) : IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  rcases hX with ⟨n, hn, h⟩ | h | h | h
  · exact KG68.isCyclic_center_sylow_of_stated_psl_binary hn h T
  · exact hD4 X h T
  · exact hTits X h T
  · exact KG68.isCyclic_center_sylow_psu33 h T

theorem sqtkCharTwoLie_of_two {X : Type} [Group X]
    (hX : (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ StatedClassicalModel X .PSL n 2 1) ∨
      ChevalleyExceptionalModel X .trialityD4 2 1 ∨ ReeTitsModel X .Tits 2 1) :
    Ch1.SQTKCharTwoLie X := by
  rcases hX with ⟨n, hn | hn | hn, h⟩ | h | h
  · subst hn
    exact Or.inl (Or.inl ⟨1, Or.inr (Or.inl ⟨le_rfl, h⟩)⟩)
  · subst hn
    exact Or.inr ⟨4, Or.inl rfl, h⟩
  · subst hn
    exact Or.inr ⟨5, Or.inr rfl, h⟩
  · exact Or.inl (Or.inl ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩)))))⟩)
  · exact Or.inl (Or.inr h)

theorem ConfAB.pCore_two_eq_bot_of_simple {K : Type} [Group K] [Finite K]
    (hqs : CFSG.IsQuasisimple K) (hsimp : IsSimpleGroup K) : CFSG.pCore 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  rcases hsimp.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 K) with h | h
  · exact h
  · exfalso
    have : Group.IsPerfect K := hqs.1
    have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    have hp : IsPGroup 2 K := by
      have h1 : IsPGroup 2 ↥(CFSG.pCore 2 K) := CFSG.pCore_isPGroup
      rw [h] at h1
      exact h1.of_equiv Subgroup.topEquiv
    exact Group.IsPerfect.not_isNilpotent K hp.isNilpotent

theorem not_conf1366_of_two (hEven : Ch1.EvenLieAutInner)
    (hD4 : KG68.TrialityTwoSylowCenterCyclic) (hTits : KG68.TitsSylowCenterCyclic)
    {G : Type} [Group G] [Finite G] {K X Q : Subgroup G} {a z l : G}
    (hqs : CFSG.IsQuasisimple ↥K) (hsimp : IsSimpleGroup ↥K) (hK : CaseABTwoList ↥K) :
    ¬ Conf1366 K X Q a z l := by
  let ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (ConfAB.pCore_two_eq_bot_of_simple hqs hsimp)).trans
      QuotientGroup.quotientBot
  refine not_conf1366_of_inner_cyclic hqs ψ ?_ (isCyclic_center_sylow_of_two hD4 hTits hK)
  intro β hβ hP
  rcases hK with h | h | h | h
  · exact hEven ↥K (sqtkCharTwoLie_of_two (Or.inl h)) β hβ hP
  · exact hEven ↥K (sqtkCharTwoLie_of_two (Or.inr (Or.inl h))) β hβ hP
  · exact hEven ↥K (sqtkCharTwoLie_of_two (Or.inr (Or.inr h))) β hβ hP
  · exact Ch1.oddAutInner_psu3 Nat.prime_three (by norm_num) h β hβ hP

end CFSG.Quasithin.H13.A5
