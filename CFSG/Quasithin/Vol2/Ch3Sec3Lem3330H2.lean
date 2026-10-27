module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330H1
public import CFSG.Quasithin.H13.L32A753f

public section

namespace CFSG.Quasithin.H13.M3330

open CFSG.Open CFSG.Quasithin Orbit
open scoped Pointwise

variable {V : Type} [CommGroup V] [Finite V]

theorem offender_facts
    {e : V ≃* ModQ}
    {X K : Subgroup (MulAut V)}
    (hKe : K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))
    (hX : ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) (hP : B42TypeU33 ↥K)
    {B : Subgroup (MulAut V)} (hBX : B ≤ X) (hB1 : B ≠ ⊥) (hBe : IsElemAbelian2 B) :
    Nat.card B ≤ (fixV B).index ∧
      ((fixV B).index = Nat.card B → Nat.card B = 8 ∧ Nat.card (fixV B) = 8 ∧ ¬ B ≤ K ∧
        ∃ b ∈ B, fixV B = fixV (Subgroup.zpowers b)) := by
  obtain ⟨h1, h2⟩ := L32A.M753.card_le_index_of_equiv e hX hBX hB1 hBe
  refine ⟨h1, fun heq => ?_⟩
  obtain ⟨h8, hf8⟩ := h2 heq
  have hBK : ¬ B ≤ K := fun hle => by
    have hrk := B42U33.rank_le_two hP hle hBe (k := 3) (by rw [h8]; norm_num)
    omega
  obtain ⟨b, hbB, hbK⟩ : ∃ b ∈ B, b ∉ K := by
    by_contra h
    push Not at h
    exact hBK h
  refine ⟨h8, hf8, hBK, b, hbB, ?_⟩
  have hle : fixV B ≤ fixV (Subgroup.zpowers b) := fun v hv x hx =>
    hv x ((Subgroup.zpowers_le.2 hbB) hx)
  have hc := card_fixV_le_eight hKe hX (hBX hbB) hbK (hBe.2 b hbB)
  exact Subgroup.eq_of_le_of_card_ge hle (hc.trans hf8.ge)

omit [Finite V] in
theorem eq_of_normal_offenders {e : V ≃* ModQ} {Tb : Subgroup (MulAut V)}
    (hTb : Tb.map (MulAut.congr e).toMonoidHom = sSubG.map (g2QAct (ZMod 2)))
    {E₁ E₂ : Subgroup (MulAut V)} (hE₁ : E₁ ≤ Tb) (hN₁ : Tb ≤ Subgroup.normalizer (E₁ : Set _))
    (he₁ : IsElemAbelian2 E₁) (h8₁ : Nat.card E₁ = 8) (hf₁ : Nat.card (fixV E₁) = 8)
    (hE₂ : E₂ ≤ Tb) (hN₂ : Tb ≤ Subgroup.normalizer (E₂ : Set _)) (he₂ : IsElemAbelian2 E₂)
    (h8₂ : Nat.card E₂ = 8) (hf₂ : Nat.card (fixV E₂) = 8) : E₁ = E₂ := by
  set ρ := g2QAct (ZMod 2) with hρ
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hρinj : Function.Injective ρ := g2QAct_injective
  have key : ∀ {E : Subgroup (MulAut V)}, E ≤ Tb → Tb ≤ Subgroup.normalizer (E : Set _) →
      IsElemAbelian2 E → Nat.card E = 8 → Nat.card (fixV E) = 8 →
      ∀ l, l ∈ idx ((E.map φ).comap ρ) ↔ l ∈ sE8.getD 2 [] := by
    intro E hE hN he h8 hf
    set F := (E.map φ).comap ρ with hF
    have hER : E.map φ ≤ ρ.range := fun y hy => by
      have : y ∈ Tb.map φ := Subgroup.map_mono hE hy
      rw [hTb] at this
      obtain ⟨s, -, rfl⟩ := this
      exact ⟨s, rfl⟩
    have hFmap : F.map ρ = E.map φ := Subgroup.map_comap_eq_self hER
    have hFS : F ≤ sSubG := fun x hx => by
      have : ρ x ∈ Tb.map φ := Subgroup.map_mono hE hx
      rw [hTb] at this
      obtain ⟨s, hs, hse⟩ := this
      rw [hρinj hse] at hs
      exact hs
    have hF2 : ∀ b ∈ F, b ^ 2 = 1 := fun b hb => by
      obtain ⟨a, ha, hae⟩ := hb
      apply hρinj
      rw [map_pow, ← hae, ← map_pow, he.2 a ha, map_one, map_one]
    have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb => by
      obtain ⟨a', ha', hae⟩ := ha
      obtain ⟨b', hb', hbe⟩ := hb
      apply hρinj
      rw [map_mul, map_mul, ← hae, ← hbe, ← map_mul, ← map_mul, he.1 a' ha' b' hb']
    have hcardF : Nat.card F = 8 := by
      rw [← Subgroup.card_map_of_injective hρinj, hFmap, Subgroup.card_map_of_injective hφinj, h8]
    have hidx8 : (idx F).card = 8 := by rw [← card_eq_idx hFS, hcardF]
    have hNF : ∀ s ∈ sSubG, ∀ x ∈ F, s * x * s⁻¹ ∈ F := by
      intro s hs x hx
      have hsT : ρ s ∈ Tb.map φ := by rw [hTb]; exact ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hte⟩ := hsT
      obtain ⟨a, ha, hae⟩ := hx
      have h1 : t * a * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hN ht) a).mp ha
      refine ⟨t * a * t⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
      change φ t * φ a * (φ t)⁻¹ = ρ s * ρ x * (ρ s)⁻¹
      rw [hte, hae]
    have hfixF : Nat.card (fixV (F.map ρ)) = 8 := by
      rw [hFmap, B1Red.fixV_map_congr',
        Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hf]
    exact idx_eq_of_normal hFS hF2 hFc hidx8 hNF hfixF
  have hS₁ := key hE₁ hN₁ he₁ h8₁ hf₁
  have hS₂ := key hE₂ hN₂ he₂ h8₂ hf₂
  have hFS : ∀ {E : Subgroup (MulAut V)}, E ≤ Tb → (E.map φ).comap ρ ≤ sSubG := by
    intro E hE x hx
    have : ρ x ∈ Tb.map φ := Subgroup.map_mono hE hx
    rw [hTb] at this
    obtain ⟨s, hs, hse⟩ := this
    rw [hρinj hse] at hs
    exact hs
  have hF : (E₁.map φ).comap ρ = (E₂.map φ).comap ρ :=
    eq_of_idx (hFS hE₁) (hFS hE₂) fun l => (hS₁ l).trans (hS₂ l).symm
  have hER : ∀ {E : Subgroup (MulAut V)}, E ≤ Tb → ((E.map φ).comap ρ).map ρ = E.map φ := by
    intro E hE
    refine Subgroup.map_comap_eq_self fun y hy => ?_
    have : y ∈ Tb.map φ := Subgroup.map_mono hE hy
    rw [hTb] at this
    obtain ⟨s, -, rfl⟩ := this
    exact ⟨s, rfl⟩
  have h1 := congrArg (Subgroup.map ρ) hF
  rw [hER hE₁, hER hE₂] at h1
  exact Subgroup.map_injective hφinj h1

omit [Finite V] in
theorem exists_coordT
    {X K Tb : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) (hnat : G2NaturalDerived K ⊤ ⊥ 1)
    (hTbX : Tb ≤ X) (hTb2 : IsPGroup 2 Tb) :
    ∃ e : V ≃* ModQ,
      K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        (∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) ∧
          Tb.map (MulAut.congr e).toMonoidHom ≤ sSubG.map (g2QAct (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀, hKe₀, hX₀⟩ := exists_coord hXN hnat
  set ρ := g2QAct (ZMod 2) with hρ
  have hρinj : Function.Injective ρ := g2QAct_injective
  set P := (Tb.map (MulAut.congr e₀).toMonoidHom).comap ρ with hP
  have hP2 : IsPGroup 2 ↥P := (hTb2.map _).comap_of_injective ρ hρinj
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) Q sylowSub
  let φ : ModQ ≃* ModQ := ρ c
  refine ⟨e₀.trans φ, ?_, ?_, ?_⟩
  · have hD : (g2Derived (ZMod 2)).Normal :=
      Subgroup.normal_of_index_eq_two B45U33.index_g2Derived
    have h1 : K.map (MulAut.congr (e₀.trans φ)).toMonoidHom =
        (K.map (MulAut.congr e₀).toMonoidHom).map (MulAut.conj (ρ c)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
    rw [h1, hKe₀, Subgroup.map_map]
    have h2 : (MulAut.conj (ρ c)).toMonoidHom.comp ρ = ρ.comp (MulAut.conj c).toMonoidHom := by
      ext g v
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [h2, ← Subgroup.map_map]
    congr 1
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hD.conj_mem g' hg' c
    · intro hg
      refine ⟨c⁻¹ * g * c, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := hD.conj_mem g hg c⁻¹
      simpa [mul_assoc] using this
  · intro x hx
    obtain ⟨γ, hγ⟩ := hX₀ x hx
    refine ⟨c * γ * c⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hγ]
    ext v
    rfl
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨γ, hγ⟩ := hX₀ t (hTbX ht)
    have hγP : γ ∈ P := by
      show ρ γ ∈ Tb.map (MulAut.congr e₀).toMonoidHom
      rw [hγ]
      exact ⟨t, ht, rfl⟩
    have h1 : MulAut.conj c • γ ∈ MulAut.conj c • (Q : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hγP)
    rw [← Sylow.coe_subgroup_smul, hc] at h1
    refine ⟨c * γ * c⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hγ]
    ext v
    rfl

theorem map_eq_sSubG
    {e : V ≃* ModQ}
    {X K Tb : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hKe : K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))
    (hX : ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range)
    (hTbS : Tb.map (MulAut.congr e).toMonoidHom ≤ sSubG.map (g2QAct (ZMod 2)))
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf Tb X) (hTbK : ¬ Tb ≤ K) :
    Tb.map (MulAut.congr e).toMonoidHom = sSubG.map (g2QAct (ZMod 2)) := by
  set ρ := g2QAct (ZMod 2) with hρ
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hρinj : Function.Injective ρ := g2QAct_injective
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  set X' := (X.map φ).comap ρ with hX'
  have hXR : X.map φ ≤ ρ.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hX x hx
  have hX'map : X'.map ρ = X.map φ := Subgroup.map_comap_eq_self hXR
  have hcardX : Nat.card X = Nat.card X' := by
    rw [← Subgroup.card_map_of_injective hφinj, ← hX'map, Subgroup.card_map_of_injective hρinj]
  have hDX' : g2Derived (ZMod 2) ≤ X' := by
    intro g hg
    show ρ g ∈ X.map φ
    have : ρ g ∈ K.map φ := by rw [hKe]; exact ⟨g, hg, rfl⟩
    exact Subgroup.map_mono hKX this
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ Tb, t ∉ K := by
    by_contra h
    push Not at h
    exact hTbK h
  obtain ⟨γ, hγ⟩ := hX t (hsyl.1 htT)
  have hγX' : γ ∈ X' := by
    show ρ γ ∈ X.map φ
    rw [hγ]
    exact ⟨t, hsyl.1 htT, rfl⟩
  have hγD : γ ∉ g2Derived (ZMod 2) := by
    intro hγ'
    have h1 : φ t ∈ K.map φ := by
      rw [hKe]
      exact ⟨γ, hγ', hγ⟩
    exact htK ((Subgroup.mem_map_iff_mem hφinj).1 h1)
  have hX'top : Nat.card X' = 12096 := by
    have hdvd : Nat.card (g2Derived (ZMod 2)) ∣ Nat.card X' := Subgroup.card_dvd_of_le hDX'
    have hdvd2 : Nat.card X' ∣ 12096 := by
      rw [← card_g2Two]
      exact Subgroup.card_subgroup_dvd_card X'
    have hD6 : Nat.card (g2Derived (ZMod 2)) = 6048 := by
      have h1 := (g2Derived (ZMod 2)).card_mul_index
      rw [B45U33.index_g2Derived, card_g2Two] at h1
      omega
    have hne : Nat.card X' ≠ 6048 := by
      intro h6
      have := Subgroup.eq_of_le_of_card_ge hDX' (by rw [h6, hD6])
      exact hγD (this ▸ hγX')
    rw [hD6] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hdvd2
    rw [hk] at hm hne
    have hk2 : k * m = 2 := by
      have : 6048 * (k * m) = 6048 * 2 := by rw [← mul_assoc, ← hm]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    have hk1 : k ≠ 1 := fun h1 => hne (by rw [h1, mul_one])
    have hk' : k = 2 := by
      rcases Nat.dvd_prime Nat.prime_two |>.1 (Dvd.intro m hk2) with h | h
      · exact absurd h hk1
      · exact h
    rw [hk, hk']
  have hT64 : Nat.card Tb = 64 := by
    have h2 := hsyl.2.1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    have hmul := Subgroup.card_mul_index (Tb.subgroupOf X)
    have hTbc : Nat.card (Tb.subgroupOf X) = Nat.card Tb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsyl.1).toEquiv
    rw [hTbc, hn, hcardX, hX'top] at hmul
    have hodd := hsyl.2.2
    have hn6 : n ≤ 6 := by
      by_contra hlt
      push Not at hlt
      have h7 : 2 ^ 7 ∣ 12096 := by
        rw [← hmul]
        exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hlt) _
      norm_num at h7
    have hn6' : 6 ≤ n := by
      by_contra hlt
      push Not at hlt
      apply hodd
      have : 2 ^ n * (Tb.subgroupOf X).index = 2 ^ 6 * 189 := by rw [hmul]; norm_num
      have h1 : 2 ^ n * (Tb.subgroupOf X).index = 2 ^ n * (2 ^ (6 - n) * 189) := by
        rw [this, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
      have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
      rw [h2]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [hn, show n = 6 by omega]
    norm_num
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have : Finite (MulAut ModQ) := Finite.of_injective _ DFunLike.coe_injective
  refine Subgroup.eq_of_le_of_card_ge hTbS ?_
  rw [Subgroup.card_map_of_injective hφinj, hT64, Subgroup.card_map_of_injective hρinj,
    card_sSubG]

end CFSG.Quasithin.H13.M3330
