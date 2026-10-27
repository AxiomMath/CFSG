module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LJ
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem le_oTwoUpper_sup [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    H ≤ oTwoUpper H ⊔ T := by
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
      (le_normalizer_oTwoUpper H)
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  set f : ↥H →* (↥H ⧸ (oTwoUpper H).subgroupOf H) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := T.subgroupOf H) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((T.subgroupOf H).map f)
  have h1 : ((T.subgroupOf H).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero n)).trans (hn ▸ hdvd)) hT.2.2
  rw [Subgroup.index_eq_one] at h1
  intro x hx
  have hmem : f ⟨x, hx⟩ ∈ (T.subgroupOf H).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t : ↥H)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper H).subgroupOf H := by
    rw [← QuotientGroup.eq]
    exact hteq
  have h4 : x = (t : G) * ((t : G)⁻¹ * x) := by group
  rw [h4, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ht) (Subgroup.mem_subgroupOf.mp h2)

theorem conjQuot_pow_orderOf {H : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : conjQuot H H g hg ^ orderOf g = 1 := by
  ext q
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hk' : g ^ orderOf g * k * (g ^ orderOf g)⁻¹ ∈ H := by
    rw [pow_orderOf_eq_one]
    simpa using hk
  rw [conjQuot_pow_mk hg _ hk hk', MulAut.one_apply]
  congr 2
  simp [pow_orderOf_eq_one]

theorem mem_of_odd_of_mem_map [Finite G] {Kc X : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥Kc →* Q} (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc)
    (hON : pCoreOf 2 Kc ≤ Subgroup.normalizer (X : Set G)) (hXO : oTwoUpper X = X) {g : G}
    (hgK : g ∈ Kc) (hodd : Odd (orderOf g)) (hg : φ ⟨g, hgK⟩ ∈ (X.subgroupOf Kc).map φ) :
    g ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨x, hxK⟩, hx, hxg⟩ := hg
  have hq : x⁻¹ * g ∈ pCoreOf 2 Kc := by
    have h1 : φ ((⟨x, hxK⟩ : ↥Kc)⁻¹ * ⟨g, hgK⟩) = 1 := by
      rw [map_mul, map_inv, hxg, inv_mul_cancel]
    exact hker _ h1
  have hgXO : g ∈ X ⊔ pCoreOf 2 Kc := by
    have e : g = x * (x⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hx hq
  have hmem := mem_oTwoUpper_of_odd hgXO hodd
  rwa [oTwoUpper_sup_eq (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) hON, hXO] at hmem

namespace PairCtx

variable [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

theorem pCoreOf_map_ne_bot (hc : PairCtx H K₁ K₂ φ) {g : G} (hgH : g ∈ H)
    (h₁₂ : K₁.map (MulAut.conj g).toMonoidHom = K₂) {X : Subgroup G} (hXK : X ≤ K₁ ⊔ K₂)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hO : ¬ pCoreOf 2 X ≤ pCoreOf 2 (K₁ ⊔ K₂)) :
    pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) ≠ ⊥ ∧
      pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₂₁ : K₂.map (MulAut.conj g).toMonoidHom = K₁ := by
    rcases hc.fix_or_swap hgH with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans h₁₂) hc.ne
    · exact h2
  have hOK : pCoreOf 2 X ≤ K₁ ⊔ K₂ := (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXK
  have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hgX
  obtain ⟨w, hwO, hwK⟩ := IsConcreteLE.not_le_iff_exists.mp hO
  have hφw : φ ⟨w, hOK hwO⟩ ≠ 1 := by
    intro h
    have h1 : (⟨w, hOK hwO⟩ : ↥(K₁ ⊔ K₂)) ∈ φ.ker := h
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact hwK h1
  have hw'O : g * w * g⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp hgO w).mp hwO
  have hform := hc.app_conj_swap h₁₂ h₂₁ (hOK hwO) (hOK hw'O)
  have hm₁ : ∀ v (hv : v ∈ pCoreOf 2 X), (φ ⟨v, hOK hv⟩).1 ∈
      pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) := fun v hv =>
    map_pCoreOf_le _ hXK ⟨⟨v, hOK hv⟩, hv, rfl⟩
  have hm₂ : ∀ v (hv : v ∈ pCoreOf 2 X), (φ ⟨v, hOK hv⟩).2 ∈
      pCoreOf 2 ((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) := fun v hv =>
    map_pCoreOf_le _ hXK ⟨⟨v, hOK hv⟩, hv, rfl⟩
  have hcases : (φ ⟨w, hOK hwO⟩).1 ≠ 1 ∨ (φ ⟨w, hOK hwO⟩).2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hφw (Prod.ext hcon.1 hcon.2)
  constructor
  · intro hb
    rcases hcases with h | h
    · have := hm₁ w hwO
      rw [hb, Subgroup.mem_bot] at this
      exact h this
    · have := hm₁ _ hw'O
      rw [hb, Subgroup.mem_bot, hform] at this
      exact h ((MulEquiv.map_eq_one_iff _).mp this)
  · intro hb
    rcases hcases with h | h
    · have := hm₂ _ hw'O
      rw [hb, Subgroup.mem_bot, hform] at this
      exact h ((MulEquiv.map_eq_one_iff _).mp this)
    · have := hm₂ w hwO
      rw [hb, Subgroup.mem_bot] at this
      exact h this

end PairCtx

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
