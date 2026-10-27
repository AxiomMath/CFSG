module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Ree

section Transport

variable {G : Type*} [Group G] {U : Type*} [Group U]

theorem ggF4_injective_of_center_eq_bot {ψ : U →* G} (hZ : Subgroup.center U = ⊥)
    (hker : ψ.ker ≤ Subgroup.center U) : Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  exact hker

theorem ggF4_apply_ofInjective_symm {ψ : U →* G} (hψ : Function.Injective ψ) (y : ψ.range) :
    ψ ((MonoidHom.ofInjective hψ).symm y) = y := by
  conv_rhs => rw [← (MonoidHom.ofInjective hψ).apply_symm_apply y]
  rw [MonoidHom.ofInjective_apply]

theorem ggF4_exists_pullAut {ψ : U →* G} (hψ : Function.Injective ψ) {s : G}
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut U, ∀ u, ψ (α u) = s * ψ u * s⁻¹ := by
  set e := MonoidHom.ofInjective hψ
  refine ⟨(MulAut.congr e).symm (ψ.range.normalizerMonoidHom ⟨s, hs⟩), fun u => ?_⟩
  have h1 : ((MulAut.congr e).symm (ψ.range.normalizerMonoidHom ⟨s, hs⟩)) u =
      e.symm (ψ.range.normalizerMonoidHom ⟨s, hs⟩ (e u)) := rfl
  have h2 : ((ψ.range.normalizerMonoidHom ⟨s, hs⟩ (e u) : ψ.range) : G) =
      s * ((e u : ψ.range) : G) * s⁻¹ := rfl
  rw [h1, ggF4_apply_ofInjective_symm, h2, MonoidHom.ofInjective_apply]

theorem ggF4_congr_conj {ψ : U →* G} (hψ : Function.Injective ψ) (u : U) :
    MulAut.congr (MonoidHom.ofInjective hψ) (MulAut.conj u) =
      MulAut.conj (MonoidHom.ofInjective hψ u) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

end Transport

theorem ggF4_two_pow_le_two_of_dvd {f k : ℕ} (hf : Odd f) (hk : 2 ^ k ∣ 2 * f) : 2 ^ k ≤ 2 := by
  by_contra h
  have hk2 : 2 ≤ k := by
    by_contra h'
    interval_cases k <;> simp at h
  have h4 : 4 ∣ 2 * f := (pow_dvd_pow 2 hk2).trans hk
  obtain ⟨j, rfl⟩ := hf
  omega

theorem ggF4_card_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n)]
  exact Nat.card_zmod n

section Aut

theorem ggF4_aut_structure {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {f : ℕ}
    (hf : Odd f) (hK : Nat.card K = 2 ^ f) {G : Type} [Group G] [Finite G]
    (ψ : adjointGroup ReeTag.F4.tag K →* G) (hψ : Function.Injective ψ) :
    ∃ C : Subgroup (MulAut ψ.range),
      (∀ σ : MulAut ψ.range, ∃ i ∈ (MulAut.conj : ψ.range →* MulAut ψ.range).range,
        ∃ c ∈ C, σ = i * c) ∧
      (MulAut.conj : ψ.range →* MulAut ψ.range).range ⊓ C = ⊥ ∧
      ∀ Q : Subgroup (MulAut ψ.range), IsPGroup 2 Q →
        Q ⊓ (MulAut.conj : ψ.range →* MulAut ψ.range).range = ⊥ → Nat.card Q ≤ 2 := by
  classical
  have hf1 : 1 ≤ f := by obtain ⟨j, rfl⟩ := hf; omega
  have : NeZero (2 * f) := ⟨by omega⟩
  set e := MonoidHom.ofInjective hψ
  set Φ := MulAut.congr e
  obtain ⟨hord, hNF, ⟨Θ, hΘ, -, hΘker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf1 K hK
  set φ := ReeTag.F4.finiteExceptionalAut K
  have hΦc : ∀ u, Φ (MulAut.conj u) = MulAut.conj (e u) := ggF4_congr_conj hψ
  have hΘpow : ∀ k : ℕ, Θ (φ ^ k) = Multiplicative.ofAdd (k : ZMod (2 * f)) := fun k =>
    hΘ _ 1 k (by rw [map_one, one_mul])
  have hpow1 : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range → φ ^ k = 1 := by
    intro k hk
    rw [← hΘker, MonoidHom.mem_ker, hΘpow, ofAdd_eq_one,
      ZMod.natCast_eq_zero_iff] at hk
    rw [← hord] at hk
    exact orderOf_dvd_iff_pow_eq_one.mp hk
  refine ⟨(Subgroup.zpowers φ).map Φ.toMonoidHom, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF (Φ.symm σ)
    refine ⟨MulAut.conj (e g), ⟨e g, rfl⟩, Φ (φ ^ (k : ℕ)),
      ⟨φ ^ (k : ℕ), pow_mem (Subgroup.mem_zpowers φ) _, rfl⟩, ?_⟩
    rw [← hΦc, ← map_mul, ← hgk, MulEquiv.apply_symm_apply]
  · rw [eq_bot_iff]
    rintro x ⟨⟨h, rfl⟩, ⟨y, hy, hyx⟩⟩
    obtain ⟨k, rfl⟩ := (isOfFinOrder_of_finite φ).mem_powers_iff_mem_zpowers.2 hy
    have hinn : φ ^ k ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range := by
      refine ⟨e.symm h, ?_⟩
      apply Φ.injective
      rw [hΦc, MulEquiv.apply_symm_apply]
      exact hyx.symm
    have h1 : MulAut.conj h = 1 := by
      rw [← hyx]
      change Φ (φ ^ k) = 1
      rw [hpow1 k hinn, map_one]
    exact h1
  · intro Q hQ hQI
    set ρ : MulAut ψ.range →* Multiplicative (ZMod (2 * f)) := Θ.comp Φ.symm.toMonoidHom
    have hinj : Function.Injective (ρ.comp Q.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro q hq
      have h1 : Φ.symm (q : MulAut ψ.range) ∈ Θ.ker := hq
      rw [hΘker] at h1
      obtain ⟨u, hu⟩ := h1
      have h2 : (q : MulAut ψ.range) ∈ Q ⊓ (MulAut.conj : ψ.range →* MulAut ψ.range).range :=
        ⟨q.2, ⟨e u, by rw [← hΦc, hu, MulEquiv.apply_symm_apply]⟩⟩
      rw [hQI, Subgroup.mem_bot] at h2
      exact (Subgroup.mem_bot).2 (Subtype.ext h2)
    have hdvd : Nat.card Q ∣ 2 * f := by
      have h1 := Subgroup.card_subgroup_dvd_card (ρ.comp Q.subtype).range
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        ggF4_card_multiplicative_zmod] at h1
      exact h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk] at hdvd ⊢
    exact ggF4_two_pow_le_two_of_dvd hf hdvd

theorem ggF4AutInput_holds :
    GGF4AutInput := by
  intro G _ _ n f ψ G₀ hcfg hf
  obtain ⟨-, -, hrange, hker, -, -, -⟩ := hcfg
  subst hrange
  have hf1 : 1 ≤ f := by obtain ⟨j, rfl⟩ := hf; omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have : CharP (GaloisField 2 f) ReeTag.F4.prime := (inferInstance : CharP (GaloisField 2 f) 2)
  exact ggF4_aut_structure (K := GaloisField 2 f) hf hK ψ
    (ggF4_injective_of_center_eq_bot center_adjointGroup_eq_bot hker)

theorem ggF4InnerDiagInput_holds :
    GGF4InnerDiagInput := by
  intro G _ _ n f ψ G₀ hcfg b hb hbI
  obtain ⟨hadm, hrank, hrange, hker, hperf, hlie, hC⟩ := hcfg
  obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_F4 G n f ψ G₀ ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, hperf, hlie⟩
    b hb hbI
  rw [hC, Subgroup.mem_bot] at hbg
  rw [eq_inv_of_mul_eq_one_left hbg]
  exact G₀.inv_mem hg

end Aut

section Embed

variable {U G : Type*} [Group U] [Group G] {χ : U →* G} {R : Subgroup U} {Y : Subgroup G}

theorem ggF4_comap_le_of_le_map (hχ : Function.Injective χ) (hRY : R.map χ = Y) {Q : Subgroup G}
    (hQY : Q ≤ Y) : Q.comap χ ≤ R := by
  intro u hu
  have hu' : χ u ∈ R.map χ := hRY ▸ hQY hu
  obtain ⟨r, hr, hru⟩ := hu'
  rw [← hχ hru]
  exact hr

theorem ggF4_eq_bot_of_map {p : ℕ} (hχ : Function.Injective χ) (hRY : R.map χ = Y)
    {Q : Subgroup G} (hQY : Q ≤ Y) (hYQ : Y ≤ Subgroup.normalizer (Q : Set G))
    (hQ : IsPGroup p Q) (hR : ∀ M : Subgroup R, M.Normal → IsPGroup p M → M = ⊥) : Q = ⊥ := by
  have hQ₁R := ggF4_comap_le_of_le_map hχ hRY hQY
  have hM : ((Q.comap χ).subgroupOf R).Normal := by
    constructor
    intro x hx r
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change χ ((r : U) * x * (r : U)⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    have hrY : χ r ∈ Y := hRY ▸ Subgroup.mem_map_of_mem χ r.2
    exact (Subgroup.mem_normalizer_iff.mp (hYQ hrY) (χ x)).mp hx
  have hMp : IsPGroup p ((Q.comap χ).subgroupOf R) :=
    (hQ.comap_of_injective χ hχ).comap_of_injective R.subtype R.subtype_injective
  have hM1 := hR _ hM hMp
  rw [Subgroup.subgroupOf_eq_bot] at hM1
  have hQ₁ : Q.comap χ = ⊥ := by
    rw [← inf_eq_left.mpr hQ₁R]
    exact disjoint_iff.mp hM1
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ R.map χ := hRY ▸ hQY hx
  obtain ⟨r, -, rfl⟩ := hx'
  have hr : r ∈ Q.comap χ := hx
  rw [hQ₁, Subgroup.mem_bot] at hr
  rw [hr, map_one]
  exact Subgroup.one_mem _

end Embed

section Ree

variable
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem ggF4_finiteReeFixedGroup_eq (m : ℕ) :
    ReeTag.F4.finiteReeFixedGroup K m = reeFixed ReeTag.F4 K m := by
  apply Subgroup.map_injective (adjointGroup ReeTag.F4.tag K).subtype_injective
  rw [← reeFixedGroup_eq_map_reeFixed, ← ReeTag.reeGamma_eq_reeFixedGroup]
  rfl

theorem ggF4_ree_eq_bot_of_normal (m : ℕ) (M : Subgroup (reeFixed ReeTag.F4 K m)) (hM : M.Normal)
    (h2 : IsPGroup 2 M) : M = ⊥ := by
  by_contra hne
  obtain ⟨-, P, hP, hN, -⟩ := holds_reeFixed ReeTag.F4 K m M hne h2
  apply hP
  rw [eq_top_iff, ← Subgroup.normalizer_eq_top_iff.mpr hM]
  exact hN


theorem ggF4_exists_ree_conj {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {G : Type*}
    [Group G] {ψ : adjointGroup ReeTag.F4.tag K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {s : G}
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set G)) (hsG : s ∉ ψ.range) (hs2 : orderOf s = 2) :
    ∃ h : adjointGroup ReeTag.F4.tag K,
      (reeFixed ReeTag.F4 K m).map (ψ.comp (MulAut.conj h).toMonoidHom) =
        ψ.range ⊓ Subgroup.centralizer {s} := by
  have hss : s * s = 1 := by rw [← sq, ← hs2]; exact pow_orderOf_eq_one s
  obtain ⟨α, hα⟩ := ggF4_exists_pullAut hψ hs
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun u => hψ ?_
    rw [sq, MulAut.mul_apply, hα, hα, MulAut.one_apply]
    calc s * (s * ψ u * s⁻¹) * s⁻¹ = (s * s) * ψ u * (s * s)⁻¹ := by group
      _ = ψ u := by rw [hss]; group
  have hαo : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    rintro ⟨u₀, hu₀⟩
    apply hsG
    have hc : (ψ u₀)⁻¹ * s ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h1 := hα u
      rw [← hu₀, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      calc ψ u * ((ψ u₀)⁻¹ * s) = (ψ u₀)⁻¹ * (ψ u₀ * ψ u * (ψ u₀)⁻¹) * s := by group
        _ = (ψ u₀)⁻¹ * (s * ψ u * s⁻¹) * s := by rw [h1]
        _ = (ψ u₀)⁻¹ * s * ψ u := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact ⟨u₀, hc⟩
  obtain ⟨ψ', -, -, hodd, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (by omega) K hK α hα2 hαo
  have hR : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ'.toMonoidHom =
      reeFixed ReeTag.F4 K m := by
    rw [hfix, (hodd m rfl).1, ← ggF4_finiteReeFixedGroup_eq m]
    rfl
  obtain ⟨h₀, hh₀⟩ := (hodd m rfl).2
  refine ⟨h₀⁻¹, ?_⟩
  have hχ : ψ.comp (MulAut.conj h₀⁻¹).toMonoidHom = ψ.comp ψ'.symm.toMonoidHom :=
    MonoidHom.ext fun u => by
      rw [← hh₀]
      simp
  rw [hχ, ← hR, Subgroup.map_map]
  have hcomp : (ψ.comp ψ'.symm.toMonoidHom).comp ψ'.toMonoidHom = ψ :=
    MonoidHom.ext fun u => by simp
  rw [hcomp]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hα u
    rw [show α u = u from hu] at h1
    calc ψ u * s = (s * ψ u * s⁻¹) * s := by rw [← h1]
      _ = s * ψ u := by group
  · rintro ⟨⟨u, rfl⟩, hx⟩
    refine ⟨u, ?_, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    apply hψ
    change ψ (α u) = ψ u
    rw [hα, ← hx']
    group

theorem ggF4_exists_ree_embedding {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {G : Type*}
    [Group G] {ψ : adjointGroup ReeTag.F4.tag K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {s : G}
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set G)) (hsG : s ∉ ψ.range) (hs2 : orderOf s = 2) :
    ∃ χ : adjointGroup ReeTag.F4.tag K →* G, Function.Injective χ ∧
      (reeFixed ReeTag.F4 K m).map χ = ψ.range ⊓ Subgroup.centralizer {s} := by
  obtain ⟨h, hh⟩ := ggF4_exists_ree_conj hK hψ hC hs hsG hs2
  exact ⟨ψ.comp (MulAut.conj h).toMonoidHom, hψ.comp (MulAut.conj h).injective, hh⟩

theorem ggF4GraphFieldCoreInput_holds :
    GGF4GraphFieldCoreInput := by
  intro G _ _ n f ψ G₀ hcfg hf s hs hsG hs2 Q hQY hQ2 hYQ
  obtain ⟨-, -, hrange, hker, -, -, hC⟩ := hcfg
  subst hrange
  obtain ⟨m, rfl⟩ := hf
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 _ (by omega)
  have : CharP (GaloisField 2 (2 * m + 1)) ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 (2 * m + 1)) 2)
  have hψ := ggF4_injective_of_center_eq_bot center_adjointGroup_eq_bot hker
  obtain ⟨χ, hχ, hmap⟩ :=
    ggF4_exists_ree_embedding (K := GaloisField 2 (2 * m + 1)) hK hψ hC hs hsG hs2
  exact ggF4_eq_bot_of_map hχ hmap hQY hYQ hQ2 (ggF4_ree_eq_bot_of_normal m)

end Ree

end CFSG.StandardType
