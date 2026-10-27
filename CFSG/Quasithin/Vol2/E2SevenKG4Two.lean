module

public import CFSG.Quasithin.Vol2.E2SevenKG
public import CFSG.Quasithin.Vol2.Ch3E213MP3B
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

section Outer

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem card_le_four_of_le_centralizer_outer (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    {β : PGammaL2 F} (hβ2 : β * β = 1) (hβ : β ∉ (incl F).range) {P : Subgroup (PGammaL2 F)}
    (hP2 : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({β} : Set (PGammaL2 F))) :
    Nat.card P ≤ 4 := by
  have hp2 : p ≠ 2 := by omega
  have hβg : SemidirectProduct.inl β.left = β := Ch3E213M.P3.inl_left_eq hp hF β
  have hinj : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
    SemidirectProduct.inl_injective
  have hg2 : β.left ^ 2 = 1 := by
    apply hinj
    rw [map_pow, hβg, map_one, pow_two, hβ2]
  have hgJ : β.left ∉ pslRange F := by
    rintro ⟨x, hx⟩
    apply hβ
    refine ⟨x, ?_⟩
    rw [incl_apply, hx, hβg]
  have hK : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 le_rfl (by rw [hF, pow_one])
  have hcard : 3 < Nat.card F := by omega
  have hC := card_outer_involution_centralizer hK hcard hg2 hgJ
  have hmap : (Subgroup.centralizer ({β.left} : Set (PGL2 F))).map
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) =
      Subgroup.centralizer ({β} : Set (PGammaL2 F)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      replace hy : y ∈ Subgroup.centralizer ({β.left} : Set (PGL2 F)) := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hβg, ← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨x.left, ?_, Ch3E213M.P3.inl_left_eq hp hF x⟩
      show x.left ∈ Subgroup.centralizer ({β.left} : Set (PGL2 F))
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      apply hinj
      rw [map_mul, map_mul, Ch3E213M.P3.inl_left_eq hp hF x, hβg]
      exact hx
  have hCβ : Nat.card (Subgroup.centralizer ({β} : Set (PGammaL2 F))) =
      2 * outerTorusOrder (Nat.card F) := by
    rw [← hmap, Subgroup.card_map_of_injective SemidirectProduct.inl_injective, hC]
  have hdvd : Nat.card P ∣ 2 * outerTorusOrder (Nat.card F) := by
    rw [← hCβ]
    exact Subgroup.card_dvd_of_le hPC
  have hm4 : outerTorusOrder (Nat.card F) % 4 = 2 :=
    outerTorusOrder_mod_four (by rw [hF]; exact hp.odd_of_ne_two hp2)
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  rw [hk] at hdvd ⊢
  by_contra h
  push Not at h
  have h3 : 3 ≤ k := by
    by_contra h'
    push Not at h'
    interval_cases k <;> simp at h
  have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h3
  have := h8.trans hdvd
  omega

end Outer

section Paired

variable {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F] {p : ℕ}
variable {K₁ K₂ S E : Subgroup Y}

omit [Finite Y] [Finite F] in
theorem normalizerMonoidHom_of_mem {k : Y} (hk : k ∈ K₁) :
    K₁.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ = MulAut.conj (⟨k, hk⟩ : K₁) := by
  ext y
  rfl

theorem paired_inf_of_sylow
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F)
    {t : Y} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : Y, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1) (hS : IsSylowTwoOf S ⊤)
    (htS : t ∈ S) (hK₂ : K₁.map (MulAut.conj t).toMonoidHom = K₂)
    (hSE : S ≤ Subgroup.normalizer (E : Set Y)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : 4 ≤ Nat.card E) (haut : 8 < autCard S K₁) :
    E = (E ⊓ K₁) ⊔ (E ⊓ K₂) ∧ Nat.card (E ⊓ K₁ : Subgroup Y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by have := Ch3E213M.P3.seven_le hp hp8; omega
  obtain ⟨hEN, a, haE, haC, hEeq⟩ :=
    Ch3E213M.P3.exists_eq_sup hp hp8 hF θ hc hd hKn hCK hS htS hK₂ hSE hEc hE2 hE4 haut
  set A₁ := E ⊓ Subgroup.centralizer (K₁ : Set Y) with hA₁
  set A₂ := E ⊓ Subgroup.centralizer (K₂ : Set Y) with hA₂
  have hcent : ∀ z : Y, z ∈ Subgroup.centralizer (K₁ : Set Y) →
      z ∈ Subgroup.centralizer (K₂ : Set Y) → z = 1 := by
    intro z hz₁ hz₂
    apply hCK
    intro k hk
    have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({z} : Set Y) := by
      refine sup_le (fun k hk => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
        (fun k hk => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      · rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hz₁ k hk).symm
      · rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hz₂ k hk).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hk) z rfl)
  have hA : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    exact hcent z (Subgroup.mem_inf.mp hz1).2 (Subgroup.mem_inf.mp hz2).2
  have ha1 : a ≠ 1 := fun h => haC (h ▸ Subgroup.one_mem _)
  have hza2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hE2 a haE) ha1
  have hzaA : Subgroup.zpowers a ⊓ A₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, hzA⟩
    rcases Ch3E213M.P3.eq_one_or_eq_of_mem_zpowers (hE2 a haE) hz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hzA.2 haC
  have hEcard : Nat.card E = 2 * Nat.card A₁ := by
    have h1 := H13.QRC.card_sup_of_commute
      (fun x hx y hy => hEc x (Subgroup.zpowers_le.mpr haE hx) y ((inf_le_left : A₁ ≤ E) hy))
      hzaA
    rw [← hEeq, hza2] at h1
    exact h1
  have htE : t ∈ Subgroup.normalizer (E : Set Y) := hSE htS
  have hconj : A₁.map (MulAut.conj t).toMonoidHom ≤ A₂ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htE x).mp hxE, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ hk
    rw [← hK₂] at hk
    obtain ⟨k, hk, rfl⟩ := hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := Subgroup.mem_centralizer_iff.mp hxC k hk
    calc t * k * t⁻¹ * (t * x * t⁻¹) = t * (k * x) * t⁻¹ := by group
      _ = t * (x * k) * t⁻¹ := by rw [this]
      _ = t * x * t⁻¹ * (t * k * t⁻¹) := by group
  have hA12 : Nat.card A₁ ≤ Nat.card A₂ := by
    have := Subgroup.card_le_of_le hconj
    rwa [Subgroup.card_map_of_injective (MulAut.conj t).injective] at this
  have hA1A2 : Nat.card A₁ * Nat.card A₂ ≤ Nat.card E := by
    rw [← H13.QRC.card_sup_of_commute
      (fun x hx y hy => hEc x ((inf_le_left : A₁ ≤ E) hx) y ((inf_le_left : A₂ ≤ E) hy)) hA]
    exact Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hA1pos : 0 < Nat.card A₁ := Nat.card_pos
  have hA1 : Nat.card A₁ = 2 := by
    have h1 : Nat.card A₂ ≤ 2 := by nlinarith
    omega
  have hA2 : Nat.card A₂ = 2 := by
    have h1 : Nat.card A₂ ≤ 2 := by nlinarith
    omega
  have hE4' : Nat.card E = 4 := by omega
  have hEA : E = A₁ ⊔ A₂ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
    rw [H13.QRC.card_sup_of_commute
      (fun x hx y hy => hEc x ((inf_le_left : A₁ ≤ E) hx) y ((inf_le_left : A₂ ≤ E) hy)) hA,
      hA1, hA2, hE4']
  have hconj' : A₁.map (MulAut.conj t).toMonoidHom = A₂ := by
    refine Subgroup.eq_of_le_of_card_ge hconj ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hA1, hA2]
  set θ₂ : K₂ ≃* PSL2 F :=
    ((K₁.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hK₂)).symm.trans θ with hθ₂
  have hsimp₂ := Ch3E213M.P3.isSimpleGroup_of hp hp8 hF θ₂
  have hcard : Nat.card K₁ = Nat.card K₂ := by
    rw [← hK₂, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hKn' : (K₂ ⊔ K₁).Normal := by rw [sup_comm]; exact hKn
  have hK12 : K₁ ≠ K₂ := by
    intro h
    have hbot : K₁ = ⊥ := by rw [← hd, ← h, inf_idem]
    have h8 := Ch3E213M.P3.eight_dvd_card hp hp8 hF
    rw [← Nat.card_congr θ.toEquiv, hbot, Subgroup.card_bot] at h8
    omega
  have hN12 : ∀ s : Y, s ∈ Subgroup.normalizer (K₁ : Set Y) →
      s ∈ Subgroup.normalizer (K₂ : Set Y) := by
    intro s hs
    rcases H13.QRC.conj_factor_eq_or hc' hKn'
      (fun z hz h => Ch3E213M.P3.eq_one_of_central θ₂ hz h) hcard.symm s with h | h
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    · exfalso
      have h1 : K₁.map (MulAut.conj s).toMonoidHom = K₁ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
      apply hK12
      exact Subgroup.map_injective (MulAut.conj s).injective (h1.trans h.symm)
  have hK₂₁ : K₂.map (MulAut.conj t).toMonoidHom = K₁ := by
    rcases H13.QRC.conj_factor_eq_or hc' hKn'
      (fun z hz h => Ch3E213M.P3.eq_one_of_central θ₂ hz h) hcard.symm t with h | h
    · exfalso
      apply hK12
      exact Subgroup.map_injective (MulAut.conj t).injective (hK₂.trans h.symm)
    · exact h
  obtain ⟨b, hbA, hb1⟩ : ∃ b ∈ A₂, b ≠ 1 := by
    by_contra h
    push Not at h
    have : A₂ = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [this, Subgroup.card_bot] at hA2
    omega
  have hzb : Subgroup.zpowers b = A₂ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbA) ?_
    rw [Nat.card_zpowers, hA2, orderOf_eq_prime (by rw [pow_two]; exact hE2 b hbA.1) hb1]
  have hbN : b ∈ Subgroup.normalizer (K₁ : Set Y) := hEN hbA.1
  have hbK : b ∈ K₁ := by
    obtain ⟨β, hβ⟩ : ∃ β, Ch3E213M.P3.act θ ⟨b, hbN⟩ = β := ⟨_, rfl⟩
    by_cases hβr : β ∈ (incl F).range
    · obtain ⟨x, hx⟩ := hβr
      obtain ⟨k, rfl⟩ := θ.surjective x
      have hkN : (k : Y) ∈ Subgroup.normalizer (K₁ : Set Y) := Subgroup.le_normalizer k.2
      have hk : Ch3E213M.P3.act θ ⟨k, hkN⟩ = β := by
        rw [← hx]
        change (autEquiv θ) (K₁.normalizerMonoidHom ⟨k, hkN⟩) = _
        rw [normalizerMonoidHom_of_mem k.2, autEquiv_conj]
      have hker : (⟨k, hkN⟩ : Subgroup.normalizer (K₁ : Set Y))⁻¹ * ⟨b, hbN⟩ ∈
          (Ch3E213M.P3.act θ).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hk, hβ, inv_mul_cancel]
      rw [Ch3E213M.P3.act_ker, Subgroup.mem_subgroupOf] at hker
      have h1 : (k : Y)⁻¹ * b = 1 := by
        refine hcent _ hker ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h2 := Subgroup.mem_centralizer_iff.mp hbA.2 y hy
        have h3 := hc _ k.2 y hy
        calc y * ((k : Y)⁻¹ * b) = (k : Y)⁻¹ * (k * y * (k : Y)⁻¹) * b := by group
          _ = (k : Y)⁻¹ * (y * k * (k : Y)⁻¹) * b := by rw [h3]
          _ = (k : Y)⁻¹ * (y * b) := by group
          _ = (k : Y)⁻¹ * (b * y) := by rw [h2]
          _ = (k : Y)⁻¹ * b * y := by group
      rw [inv_mul_eq_one] at h1
      rw [← h1]
      exact k.2
    · exfalso
      have hβ2 : β * β = 1 := by
        rw [← hβ, ← map_mul]
        have : (⟨b, hbN⟩ : Subgroup.normalizer (K₁ : Set Y)) * ⟨b, hbN⟩ = 1 :=
          Subtype.ext (hE2 b hbA.1)
        rw [this, map_one]
      have hP2 : IsPGroup 2 (Ch3E213M.P3.autSub θ S) := by
        have h1 : IsPGroup 2 (S.subgroupOf (Subgroup.normalizer (K₁ : Set Y))) :=
          hS.2.1.comap_subtype
        exact h1.map _
      have hPC : Ch3E213M.P3.autSub θ S ≤ Subgroup.centralizer ({β} : Set (PGammaL2 F)) := by
        rintro _ ⟨s, hs, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hβ, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        have hsS : (s : Y) ∈ S := Subgroup.mem_subgroupOf.mp hs
        have hsA : (s : Y) * b * (s : Y)⁻¹ ∈ A₂ := by
          refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hSE hsS) b).mp hbA.1, ?_⟩
          have hsK₂ := hN12 s s.2
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : (s : Y)⁻¹ * y * (s : Y)⁻¹⁻¹ ∈ K₂ :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsK₂) y).mp hy
          rw [inv_inv] at hy'
          have := Subgroup.mem_centralizer_iff.mp hbA.2 _ hy'
          calc y * ((s : Y) * b * (s : Y)⁻¹) =
              (s : Y) * ((s : Y)⁻¹ * y * s * b) * (s : Y)⁻¹ := by group
            _ = (s : Y) * (b * ((s : Y)⁻¹ * y * s)) * (s : Y)⁻¹ := by rw [this]
            _ = (s : Y) * b * (s : Y)⁻¹ * y := by group
        rw [← hzb] at hsA
        rcases Ch3E213M.P3.eq_one_or_eq_of_mem_zpowers (hE2 b hbA.1) hsA with h | h
        · exfalso
          apply hb1
          have := congrArg (fun w => (s : Y)⁻¹ * w * s) h
          simpa [mul_assoc] using this
        · change (s : Y) * b = b * s
          calc (s : Y) * b = (s : Y) * b * (s : Y)⁻¹ * s := by group
            _ = b * s := by rw [h]
      have h4 := card_le_four_of_le_centralizer_outer hp hp5 hF hβ2 hβr hP2 hPC
      rw [Ch3E213M.P3.card_autSub] at h4
      omega
  have hA2K : A₂ ≤ K₁ := by
    rw [← hzb]
    exact Subgroup.zpowers_le.mpr hbK
  have hback : ∀ H : Subgroup Y,
      (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = H := by
    intro H
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨t * x * t⁻¹, ⟨x, hx, rfl⟩, by simp [mul_assoc]⟩
  have hA1K : A₁ ≤ K₂ := by
    have h1 : A₁ = A₂.map (MulAut.conj t⁻¹).toMonoidHom := by rw [← hconj', hback]
    have h2 : K₁.map (MulAut.conj t⁻¹).toMonoidHom = K₂ := by rw [← hK₂₁, hback]
    rw [h1, ← h2]
    exact Subgroup.map_mono hA2K
  have hEK1 : E ⊓ K₁ = A₂ := by
    refine le_antisymm (fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩) (le_inf inf_le_left hA2K)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc x hx.2 y hy).symm
  have hEK2 : E ⊓ K₂ = A₁ := by
    refine le_antisymm (fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩) (le_inf inf_le_left hA1K)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hc y hy x hx.2
  refine ⟨?_, ?_⟩
  · rw [hEK1, hEK2, sup_comm]
    exact hEA
  · rw [hEK1, hA2]

end Paired

section Main

variable {G : Type} [Group G]

private theorem mem_normalizer_subgroupOf_iff₄ {X U : Subgroup G} (hUX : U ≤ X) (y : ↥X) :
    y ∈ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff₄ {X U : Subgroup G} (hUX : U ≤ X) (y : ↥X) :
    y ∈ Subgroup.centralizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    exact congrArg Subtype.val (h ⟨u, hUX hu⟩ (Subgroup.mem_subgroupOf.mpr hu))
  · intro h u hu
    exact Subtype.ext (h u (Subgroup.mem_subgroupOf.mp hu))

theorem autCard_subgroupOf {X T K : Subgroup G} (hTX : T ≤ X) (hKX : K ≤ X) :
    autCard (T.subgroupOf X) (K.subgroupOf X) = autCard T K := by
  unfold autCard
  have hB : T.subgroupOf X ⊓ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf X := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [mem_normalizer_subgroupOf_iff₄ hKX]
  have hC : T.subgroupOf X ⊓ Subgroup.normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) ⊓
      Subgroup.centralizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (T ⊓ Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf X := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [mem_normalizer_subgroupOf_iff₄ hKX, mem_centralizer_subgroupOf_iff₄ hKX]
  rw [hC, hB, Subgroup.relIndex_subgroupOf (inf_le_left.trans hTX)]

theorem kgL2OddTwo_holds : KGL2OddTwo := by
  intro G _ _ X T M K V t p hP _ htT hKX _ hXN hC hKK hcomm _ hp hp8 hK _ _ haut hVO hVab hTV hV4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.1.le
  have hTX : T ≤ X := hP.isSylow.1
  have hTsylM : IsSylowTwoOf T M := isSylowTwoOf_mono hP.isSylow hTM hMX
  have hO2T : pCoreOf 2 M ≤ T := A4.le_of_normal_of_isSylowTwoOf hTsylM
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hVT : V ≤ T := hVO.trans hO2T
  have hVX : V ≤ X := hVT.trans hTX
  have htX : t ∈ X := hTX htT
  have hKtX : cjSub t K ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    exact X.mul_mem (X.mul_mem htX (hKX hk)) (X.inv_mem htX)
  have hLX : K ⊔ cjSub t K ≤ X := sup_le hKX hKtX
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have hF' : Nat.card F = p := by simpa using hF
  let θ : ↥(K.subgroupOf X) ≃* PSL2 F := (Subgroup.subgroupOfEquivOfLe hKX).trans
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
  have hc : ∀ a ∈ K.subgroupOf X, ∀ b ∈ (cjSub t K).subgroupOf X, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hd : K.subgroupOf X ⊓ (cjSub t K).subgroupOf X = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hy
    have : (y : G) ∈ K ⊓ cjSub t K :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
    rw [hKK, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hsup : K.subgroupOf X ⊔ (cjSub t K).subgroupOf X = (K ⊔ cjSub t K).subgroupOf X :=
    (Subgroup.subgroupOf_sup hKX hKtX).symm
  have hKn : (K.subgroupOf X ⊔ (cjSub t K).subgroupOf X).Normal := by
    rw [hsup]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN
  have hCK : ∀ a : ↥X, (∀ k ∈ K.subgroupOf X ⊔ (cjSub t K).subgroupOf X, a * k = k * a) →
      a = 1 := by
    intro a ha
    have h1 : a ∈ Subgroup.centralizer
        (((K ⊔ cjSub t K).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [← hsup] at hk
      exact (ha k hk).symm
    rw [mem_centralizer_subgroupOf_iff₄ hLX] at h1
    have h2 : (a : G) ∈ X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨a.2, h1⟩
    rw [hC, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hS : IsSylowTwoOf (T.subgroupOf X) ⊤ := by
    refine ⟨le_top, hP.isSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm, ?_⟩
    have h3 : ((T.subgroupOf X).subgroupOf ⊤).index = (T.subgroupOf X).index :=
      Subgroup.relIndex_top_right _
    rw [h3]
    exact hP.isSylow.2.2
  have htS : (⟨t, htX⟩ : ↥X) ∈ T.subgroupOf X := Subgroup.mem_subgroupOf.mpr htT
  have hK₂ : (K.subgroupOf X).map (MulAut.conj (⟨t, htX⟩ : ↥X)).toMonoidHom =
      (cjSub t K).subgroupOf X := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_subgroupOf.mp hy
      refine ⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext ?_⟩
      exact hky
  have hSE : T.subgroupOf X ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    fun s hs => (mem_normalizer_subgroupOf_iff₄ hVX s).mpr (hTV (Subgroup.mem_subgroupOf.mp hs))
  have hEc : ∀ x ∈ V.subgroupOf X, ∀ y ∈ V.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    have h := hVab.1.is_comm.comm ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
      ⟨y, Subgroup.mem_subgroupOf.mp hy⟩
    have h' := congrArg Subtype.val h
    simpa using h'
  have hE2 : ∀ x ∈ V.subgroupOf X, x * x = 1 := by
    intro x hx
    apply Subtype.ext
    have := hVab.2 _ (Subgroup.mem_subgroupOf.mp hx)
    simpa [sq] using this
  have hE4 : 4 ≤ Nat.card (V.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
    exact hV4
  have haut' : 8 < autCard (T.subgroupOf X) (K.subgroupOf X) := by
    rw [autCard_subgroupOf hTX hKX]
    exact haut
  obtain ⟨h1, h2⟩ := paired_inf_of_sylow hp hp8 hF' θ hc hd hKn hCK hS htS hK₂ hSE hEc hE2 hE4 haut'
  have hinf : ∀ U : Subgroup G, U ≤ X →
      V.subgroupOf X ⊓ U.subgroupOf X = (V ⊓ U).subgroupOf X := by
    intro U _
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hmap : ∀ U : Subgroup G, U ≤ X →
      (V.subgroupOf X ⊓ U.subgroupOf X).map X.subtype = V ⊓ U := by
    intro U hU
    rw [hinf U hU, Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hVX)]
  refine ⟨?_, ?_⟩
  · have h3 := congrArg (Subgroup.map X.subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hVX, Subgroup.map_sup, hmap K hKX,
      hmap (cjSub t K) hKtX] at h3
    exact h3
  · rw [hinf K hKX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hVX)).toEquiv]
      at h2
    exact h2

end Main

end E2

end CFSG.Quasithin
