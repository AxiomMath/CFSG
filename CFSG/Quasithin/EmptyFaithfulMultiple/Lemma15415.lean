module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

universe u

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Helpers

variable {G : Type*} [Group G]

private theorem nonempty_quotient_pCore_of_mulEquiv {K L X : Type*} [Group K] [Group L]
    [Group X] (e : K ≃* L) {φ : L →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker = Open.pCore 2 L) : Nonempty (K ⧸ Open.pCore 2 K ≃* X) := by
  set ψ : K →* X := φ.comp e.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp e.surjective
  have hψker : ψ.ker = Open.pCore 2 K := by
    rw [← MonoidHom.comap_ker, hker, ← map_pCore_mulEquiv 2 e]
    exact Subgroup.comap_map_eq_self_of_injective e.injective _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

private theorem relIndex_eq_three_of_quotientIso [Finite G] {T H : Subgroup G}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hTH : T ≤ H)
    (hq : quasithinO2QuotientIso H (Equiv.Perm (Fin 3))) : T.relIndex H = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hq
  have h6 : (pCoreOf 2 H).relIndex H = 6 := by
    have h1 : (pCoreOf 2 H).subgroupOf H = Open.pCore 2 H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, h1, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hPT : pCoreOf 2 H ≤ T := pCoreOf_two_le_sylow H (hT.toSylow hTi) hTH
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hPT hTH
  rw [h6] at hmul
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hn ▸ Subgroup.relIndex_dvd_card (pCoreOf 2 H) T)
  rw [hk] at hmul
  have hodd : ¬ 2 ∣ T.relIndex H := fun h =>
    hTi (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  have hcop : Nat.Coprime (T.relIndex H) 2 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h6' : T.relIndex H * 2 ^ k = 3 * 2 := by rw [mul_comm, hmul]
  refine Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right ⟨2 ^ k, h6'.symm⟩) ?_
  exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left ⟨2, hmul⟩

private theorem quotientIso_of_concl15412Six [Finite G] {T M Y : Subgroup G}
    (hs : (pCoreOf 2 Y).relIndex Y = 3) (h : Concl15412Six G T M Y) :
    quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) := by
  rcases h with ⟨-, h, -⟩ | ⟨h9, -⟩
  · exact h
  · omega

private theorem pCoreOf_sup_ne_bot {T Y : Subgroup G} (hY : IsYFamily T Y) :
    pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
  rcases hY.1 with h | h
  · exact h.2.2.1
  · exact h.2.2.1.2

private theorem subgroupOf_inf_subgroupOf (H₁ H₂ K : Subgroup G) :
    H₁.subgroupOf K ⊓ H₂.subgroupOf K = (H₁ ⊓ H₂).subgroupOf K :=
  (Subgroup.comap_inf _ _ _).symm

private theorem map_omegaOneCenterOf_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    (omegaOneCenterOf (H.subgroupOf K)).map K.subtype = omegaOneCenterOf H := by
  rw [omegaOneCenterOf, omegaOneOf, MonoidHom.map_closure, omegaOneCenterOf, omegaOneOf]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨⟨hxH, hxC⟩, hx2⟩, rfl⟩
    refine ⟨⟨hxH, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, ?_⟩
    · exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hxC ⟨h, hHK hh⟩ (Subgroup.mem_subgroupOf.mpr hh))
    · simpa using congrArg Subtype.val hx2
  · rintro ⟨⟨hyH, hyC⟩, hy2⟩
    refine ⟨⟨y, hHK hyH⟩, ⟨⟨hyH, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, ?_⟩, rfl⟩
    · exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC h hh)
    · exact Subtype.ext (by simpa using hy2)

private theorem card_omegaOneCenterOf_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card ↥(omegaOneCenterOf (H.subgroupOf K)) = Nat.card ↥(omegaOneCenterOf H) := by
  rw [← map_omegaOneCenterOf_subgroupOf hHK, Subgroup.card_map_of_injective K.subtype_injective]

private theorem isGoldschmidtAmalgam_subgroupOf [Finite G] {T G₁ G₂ : Subgroup G}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hinf : G₁ ⊓ G₂ = T)
    (hq₁ : quasithinO2QuotientIso G₁ (Equiv.Perm (Fin 3)))
    (hq₂ : quasithinO2QuotientIso G₂ (Equiv.Perm (Fin 3)))
    (hO : Open.pCore 2 ↥(G₁ ⊔ G₂) = ⊥) :
    IsGoldschmidtAmalgam (G₁.subgroupOf (G₁ ⊔ G₂)) (G₂.subgroupOf (G₁ ⊔ G₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₁, hφ₁, hk₁⟩ := hq₁
  obtain ⟨φ₂, hφ₂, hk₂⟩ := hq₂
  have hT₀ : T ≤ G₁ ⊔ G₂ := hinf ▸ inf_le_left.trans le_sup_left
  exact
    { gen := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      quotient₁ := nonempty_quotient_pCore_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe le_sup_left) hφ₁ hk₁
      quotient₂ := nonempty_quotient_pCore_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe le_sup_right) hφ₂ hk₂
      sylow := by
        set S : Sylow 2 G := hT.toSylow hTi
        have hS : (S : Subgroup G) ≤ G₁ ⊔ G₂ := hT₀
        refine ⟨S.subtype hS, ?_⟩
        rw [Sylow.coe_subtype, subgroupOf_inf_subgroupOf, hinf]
        rfl
      pCore_eq_bot := hO }

private theorem nonempty_mulEquiv_of_isGoldschmidtAmalgam (hlist : F6.GoldschmidtS3ListCat.{u})
    {D : Type u} [Group D] [Finite D] {A₁ A₂ : Subgroup D} (h : IsGoldschmidtAmalgam A₁ A₂)
    (h₁ : CharTwo A₁) (h₂ : CharTwo A₂) (hm : Nat.card ↥(omegaOneCenterOf (A₁ ⊓ A₂)) = 4) :
    Nonempty (↥A₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  rcases F6.isGoldCaseVICat_of_charTwo (hlist D A₁ A₂ h) h₁ h₂ with h6 | h6
  · exact (F6.isGoldCaseSp42Cat_of_card_omegaOneCenter h.toIsGoldschmidtTriple h6 h₁ hm).2.2.1
  · rw [inf_comm] at hm
    exact (F6.isGoldCaseSp42Cat_of_card_omegaOneCenter h.toIsGoldschmidtTriple.symm h6 h₂ hm).2.2.2

end Helpers

theorem stmt15415_of (hlist : CFSG.Quasithin.F6.GoldschmidtS3ListCat.{0}) {G : Type} [Group G]
    [Finite G] {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (h13 : Stmt15413 G T) (h14 : Stmt15414 G T) : Stmt15415 G T := by
  intro hnot M₁ M₂ Y₁ Y₂ hM₁ hM₂ hY₁ hYM₁ hs₁ hY₂ hYM₂ hs₂
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT, hTi⟩ := hyp.sylow
  obtain ⟨-, -, hU₁, -, -, -, h6₁, -⟩ := (h12 M₁ hM₁).2 Y₁ hY₁ hYM₁
  obtain ⟨-, -, hU₂, -, -, -, h6₂, -⟩ := (h12 M₂ hM₂).2 Y₂ hY₂ hYM₂
  have hq₁ := quotientIso_of_concl15412Six hs₁ h6₁
  have hq₂ := quotientIso_of_concl15412Six hs₂ h6₂
  set G₀ := (Y₁ ⊔ T) ⊔ (Y₂ ⊔ T)
  have hinf : (Y₁ ⊔ T) ⊓ (Y₂ ⊔ T) = T := by
    have hmul := Subgroup.relIndex_mul_relIndex T ((Y₁ ⊔ T) ⊓ (Y₂ ⊔ T)) (Y₁ ⊔ T)
      (le_inf le_sup_right le_sup_right) inf_le_left
    rw [relIndex_eq_three_of_quotientIso hT hTi le_sup_right hq₁] at hmul
    rcases (Nat.dvd_prime Nat.prime_three).mp ⟨_, hmul.symm⟩ with h | h
    · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) (le_inf le_sup_right le_sup_right)
    · rw [h] at hmul
      have h1 : ((Y₁ ⊔ T) ⊓ (Y₂ ⊔ T)).relIndex (Y₁ ⊔ T) = 1 := by omega
      have hle : Y₁ ⊔ T ≤ Y₂ ⊔ T := (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
      exact absurd (hU₁.2 M₂ ⟨hM₂.1, hle.trans hU₂.1.2⟩).symm hne
  have hO : Open.pCore 2 ↥G₀ = ⊥ := by
    by_contra hne'
    have hQ : pCoreOf 2 G₀ ≠ ⊥ := fun h =>
      hne' ((Subgroup.map_eq_bot_iff_of_injective _ G₀.subtype_injective).mp h)
    obtain ⟨M, hM, hNM⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge
      (⟨_, hQ, pCoreOf_isPGroup 2 G₀, rfl⟩ :
        IsTwoLocal (Subgroup.normalizer (pCoreOf 2 G₀ : Set G)))
    have hG₀M := (le_normalizer_pCoreOf 2 G₀).trans hNM
    exact hne ((hU₁.2 M ⟨hM, le_sup_left.trans hG₀M⟩).symm.trans
      (hU₂.2 M ⟨hM, le_sup_right.trans hG₀M⟩))
  have hamalg := isGoldschmidtAmalgam_subgroupOf hT hTi hinf hq₁ hq₂ hO
  have hc₁ : CharTwo ((Y₁ ⊔ T).subgroupOf G₀) :=
    F6.charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
      (charTwo_of_inH hyp.qtke.2.1 (hT.toSylow hTi) ⟨le_sup_right, pCoreOf_sup_ne_bot hY₁⟩)
  have hc₂ : CharTwo ((Y₂ ⊔ T).subgroupOf G₀) :=
    F6.charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
      (charTwo_of_inH hyp.qtke.2.1 (hT.toSylow hTi) ⟨le_sup_right, pCoreOf_sup_ne_bot hY₂⟩)
  have hm : Nat.card ↥(omegaOneCenterOf ((Y₁ ⊔ T).subgroupOf G₀ ⊓ (Y₂ ⊔ T).subgroupOf G₀)) =
      4 := by
    rw [subgroupOf_inf_subgroupOf, hinf,
      card_omegaOneCenterOf_subgroupOf (le_sup_right.trans le_sup_left)]
    exact (h14 hnot).2
  obtain ⟨e⟩ := nonempty_mulEquiv_of_isGoldschmidtAmalgam hlist hamalg hc₁ hc₂ hm
  exact (h13 Y₁ hY₁).false ((Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans e)

end CFSG.Quasithin.EmptyFaithfulMultiple
