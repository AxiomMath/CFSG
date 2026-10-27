module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rB
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

private theorem pCore_two_quotient_eq_bot {P : Type*} [Group P] :
    CFSG.pCore 2 (P ⧸ CFSG.pCore 2 P) = ⊥ := by
  set N : Subgroup P := CFSG.pCore 2 P with hN
  set K : Subgroup P := (CFSG.pCore 2 (P ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := P ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := P) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

section Core

variable {P W : Type} [Group P] [Finite P] [Group W] [Finite W]

theorem uc22s21rd_pCore_le {T : Subgroup P} (hT : IsSylowIn 2 T ⊤) : CFSG.pCore 2 P ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsSylowIn.le_of_normal hT le_top inferInstance CFSG.pCore_isPGroup

theorem uc22s21rd_normal_comap (ρ : P →* W) {R : Subgroup W}
    (hRn : ρ.range ≤ normalizer (R : Set W)) : (R.comap ρ).Normal := by
  refine ⟨fun y hy x => ?_⟩
  change ρ (x * y * x⁻¹) ∈ R
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hRn ⟨x, rfl⟩) (ρ y)).mp hy

theorem uc22s21rd_map_normalizer (ρ : P →* W) {Z : Subgroup P} {g : P}
    (hg : g ∈ normalizer (Z : Set P)) : ρ g ∈ normalizer ((Z.map ρ : Subgroup W) : Set W) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g * z * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg z).mp hz, by simp⟩
  · rintro ⟨z, hz, hzw⟩
    refine ⟨g⁻¹ * z * g, (Subgroup.mem_normalizer_iff''.mp hg z).mp hz, ?_⟩
    rw [map_mul, map_mul, map_inv, hzw]
    group

theorem uc22s21rd_mem_normalizer_inf {A B : Subgroup W} {g : W}
    (hA : g ∈ normalizer (A : Set W)) (hB : g ∈ normalizer (B : Set W)) :
    g ∈ normalizer ((A ⊓ B : Subgroup W) : Set W) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simpa only [Subgroup.mem_inf] using and_congr (hA h) (hB h)

theorem uc22s21rd_inF {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {T : Subgroup P}
    (hT : IsSylowIn 2 T ⊤) (ρ : P →* W) (hker : ρ.ker ≤ CFSG.pCore 2 P) {R : Subgroup W}
    (hRq : IsPGroup q ↥R) (hRn : ρ.range ≤ normalizer (R : Set W)) (hRr : R ≤ ρ.range)
    (hPT : R.comap ρ ⊔ T = ⊤)
    (hirr : ∀ Z : Subgroup W, Z ≤ R → T.map ρ ≤ normalizer (Z : Set W) →
      Z ≤ fratSub R ∨ Z = R) :
    F12.InF 1 (⊤ : Subgroup (P ⧸ CFSG.pCore 2 P)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set πX : P →* P ⧸ CFSG.pCore 2 P := QuotientGroup.mk' (CFSG.pCore 2 P) with hπX
  set Y : Subgroup P := R.comap ρ with hY
  haveI hYn : Y.Normal := uc22s21rd_normal_comap ρ hRn
  have hkerπ : πX.ker = CFSG.pCore 2 P := QuotientGroup.ker_mk' _
  have hkπ : ρ.ker ≤ πX.ker := by
    rw [hkerπ]
    exact hker
  have hπker : ∀ x, x ∈ ρ.ker → πX x = 1 := fun x hx => MonoidHom.mem_ker.mp (hkπ hx)
  have hRY : Y.map ρ = R := by
    rw [hY, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRr
  set RX : Subgroup (P ⧸ CFSG.pCore 2 P) := Y.map πX with hRX
  haveI hRXn : RX.Normal := Subgroup.Normal.map hYn πX (QuotientGroup.mk'_surjective _)
  have hRXq : IsPGroup q ↥RX := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hRq ⟨ρ y, hy⟩
    have hk' : (ρ y) ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    change πX y ^ q ^ k = 1
    rw [← map_pow]
    exact hπker _ (by rw [MonoidHom.mem_ker, map_pow]; exact hk')
  have hQR : IsPGroup 2 ((P ⧸ CFSG.pCore 2 P) ⧸ RX) := by
    refine uc22s21rb_isPGroup_quotient (isPGroup_map πX hT.isPGroup) ?_
    rw [hRX, ← Subgroup.map_sup, hPT, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  refine uc22s21rb_inF_one_frattini hq hq2 hRXq hQR pCore_two_quotient_eq_bot ?_
  intro N hN hNR
  haveI hNc : (N.comap πX).Normal := Subgroup.Normal.comap hN πX
  set Z : Subgroup P := N.comap πX ⊓ Y with hZ
  haveI hZn : Z.Normal := inferInstance
  set Zb : Subgroup W := Z.map ρ with hZb
  have hZbR : Zb ≤ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  have hTZ : T.map ρ ≤ normalizer (Zb : Set W) := by
    rintro _ ⟨t, -, rfl⟩
    exact uc22s21rd_map_normalizer ρ (by rw [Subgroup.normalizer_eq_top_iff.mpr hZn]; trivial)
  rcases hirr Zb hZbR hTZ with hle | heq
  · left
    intro n hn
    obtain ⟨y, hy, rfl⟩ := hNR hn
    have hyZ : y ∈ Z := ⟨hn, hy⟩
    have h2 : ρ y ∈ (fratGen q Y).map ρ := by
      rw [map_fratGen, hRY, ← fratSub_eq_fratGen hq hRq]
      exact hle ⟨y, hyZ, rfl⟩
    have h3 : y ∈ fratGen q Y ⊔ ρ.ker := by
      rw [← Subgroup.comap_map_eq]
      exact h2
    have h4 : πX y ∈ (fratGen q Y ⊔ ρ.ker).map πX := ⟨y, h3, rfl⟩
    have h5 : ρ.ker.map πX = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hkπ
    rw [Subgroup.map_sup, h5, sup_bot_eq, map_fratGen, ← fratSub_eq_fratGen hq hRXq] at h4
    exact h4
  · right
    refine le_antisymm hNR ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ : ρ y ∈ Zb := heq ▸ hy
    have hk : y * z⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzy]
      exact mul_inv_cancel _
    have h1 : πX y = πX (y * z⁻¹) * πX z := by rw [← map_mul]; simp
    rw [h1, hπker _ hk, one_mul]
    exact hz.1

theorem uc22s21rd_unique_max {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {T : Subgroup P}
    (hT : IsSylowIn 2 T ⊤) (ρ : P →* W) (hker : ρ.ker ≤ CFSG.pCore 2 P) {R : Subgroup W}
    (hR0 : R ≠ ⊥) (hRq : IsPGroup q ↥R) (hRn : ρ.range ≤ normalizer (R : Set W))
    (hRr : R ≤ ρ.range) (hPT : R.comap ρ ⊔ T = ⊤)
    (hirr : ∀ Z : Subgroup W, Z ≤ R → T.map ρ ≤ normalizer (Z : Set W) →
      Z ≤ fratSub R ∨ Z = R) :
    ∃ M₀ : Subgroup P, M₀ < ⊤ ∧ ∀ Z : Subgroup P, T ≤ Z → Z < ⊤ → Z ≤ M₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup P := R.comap ρ with hY
  haveI hYn : Y.Normal := uc22s21rd_normal_comap ρ hRn
  have hkerT : ρ.ker ≤ T := hker.trans (uc22s21rd_pCore_le hT)
  have hRY : Y.map ρ = R := by
    rw [hY, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRr
  have hprod : ∀ x : P, ∃ y ∈ Y, ∃ t ∈ T, x = y * t := by
    intro x
    have hx : x ∈ ((Y ⊔ T : Subgroup P) : Set P) := by
      rw [hPT]
      exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hx
    obtain ⟨y, hy, t, ht, rfl⟩ := hx
    exact ⟨y, hy, t, ht, rfl⟩
  have hT2 : IsPGroup 2 ↥(T.map ρ) := isPGroup_map ρ hT.isPGroup
  have hTn : T.map ρ ≤ normalizer (fratSub R : Set W) := by
    rintro _ ⟨t, -, rfl⟩
    exact mem_normalizer_fratSub hq hRq (hRn ⟨t, rfl⟩)
  refine ⟨(fratSub R ⊔ T.map ρ).comap ρ, ?_, ?_⟩
  · refine lt_of_le_of_ne le_top fun htop => ?_
    have hRle : R ≤ fratSub R := by
      intro r hr
      obtain ⟨y, hy, rfl⟩ : r ∈ Y.map ρ := hRY ▸ hr
      have hmem : ρ y ∈ ((fratSub R ⊔ T.map ρ : Subgroup W) : Set W) := by
        have : y ∈ (fratSub R ⊔ T.map ρ).comap ρ := by
          rw [htop]
          exact Subgroup.mem_top y
        exact this
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (fratSub R) (T.map ρ) hTn] at hmem
      obtain ⟨f, hf, tb, htb, hft⟩ := hmem
      have hfR : f ∈ R := fratSub_le R hf
      have htbR : tb ∈ R := by
        have h1 : tb = f⁻¹ * ρ y := by rw [← hft]; group
        rw [h1]
        exact R.mul_mem (R.inv_mem hfR) hr
      haveI : Fact q.Prime := ⟨hq⟩
      have hdisj := IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) (T.map ρ) R hT2 hRq
      have htb1 : tb = 1 := Subgroup.disjoint_def.mp hdisj htb htbR
      have hft' : f * tb = ρ y := hft
      rw [htb1, mul_one] at hft'
      rw [← hft']
      exact hf
    exact (fratSub_lt hR0).ne (le_antisymm (fratSub_le R) hRle)
  · intro Z hTZ hZtop
    have hTnZ : T.map ρ ≤ normalizer (((Z.map ρ ⊓ R : Subgroup W)) : Set W) := by
      rintro _ ⟨t, ht, rfl⟩
      exact uc22s21rd_mem_normalizer_inf
        (uc22s21rd_map_normalizer ρ (Subgroup.le_normalizer (hTZ ht))) (hRn ⟨t, rfl⟩)
    rcases hirr _ inf_le_right hTnZ with hle | heq
    · intro z hz
      obtain ⟨y, hy, t, ht, rfl⟩ := hprod z
      have hyZ : y ∈ Z := by
        have h1 : y = (y * t) * t⁻¹ := by group
        rw [h1]
        exact Z.mul_mem hz (Z.inv_mem (hTZ ht))
      have hfrat : ρ y ∈ fratSub R := hle ⟨⟨y, hyZ, rfl⟩, hy⟩
      rw [Subgroup.mem_comap, map_mul]
      exact Subgroup.mul_mem_sup hfrat ⟨t, ht, rfl⟩
    · exfalso
      have hZtop' : Z = ⊤ := by
        refine eq_top_iff.2 fun x _ => ?_
        obtain ⟨y, hy, t, ht, rfl⟩ := hprod x
        have hρy : ρ y ∈ Z.map ρ ⊓ R := by
          rw [heq]
          exact hy
        obtain ⟨z, hz, hzy⟩ := hρy.1
        have hk : y * z⁻¹ ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzy]
          exact mul_inv_cancel _
        have hyZ : y ∈ Z := by
          have h1 : y = (y * z⁻¹) * z := by group
          rw [h1]
          exact Z.mul_mem (hTZ (hkerT hk)) hz
        exact Z.mul_mem hyZ (hTZ ht)
      exact hZtop.ne hZtop'

end Core

section GLevel

variable {G : Type} [Group G] [Finite G] {W : Type} [Group W] [Finite W]

theorem uc22s21rd_isSylowIn_subgroupOf {X T : Subgroup G} (hT : IsSylowIn 2 T X) :
    IsSylowIn 2 (T.subgroupOf X) ⊤ := by
  have := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2) (H := X) hT.le le_rfl).mpr hT
  rwa [Subgroup.subgroupOf_self] at this

theorem uc22s21rd_le_or_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X T H₁ H₂ : Subgroup G}
    (hTX : IsSylowIn 2 T X) (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hH : F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (ρ : ↥X →* W) (hker : ρ.ker ≤ CFSG.pCore 2 ↥X) {R : Subgroup W} (hR0 : R ≠ ⊥)
    (hRq : IsPGroup q ↥R) (hRn : ρ.range ≤ normalizer (R : Set W)) (hRr : R ≤ ρ.range)
    (hPT : R.comap ρ ⊔ T.subgroupOf X = ⊤)
    (hirr : ∀ Z : Subgroup W, Z ≤ R → (T.subgroupOf X).map ρ ≤ normalizer (Z : Set W) →
      Z ≤ fratSub R ∨ Z = R) :
    X ≤ H₁ ∨ X ≤ H₂ := by
  have hS : IsSylowIn 2 (T.subgroupOf X) ⊤ := uc22s21rd_isSylowIn_subgroupOf hTX
  have hfac := hH (uc22s21rd_inF hq hq2 hS ρ hker hRq hRn hRr hPT hirr)
  obtain ⟨M₀, hM₀, hmax⟩ := uc22s21rd_unique_max hq hq2 hS ρ hker hR0 hRq hRn hRr hPT hirr
  have hfac' : ((H₁.subgroupOf X : Subgroup ↥X) : Set ↥X) *
      ((H₂.subgroupOf X : Subgroup ↥X) : Set ↥X) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true]
    have hp : (p : G) ∈ (X : Set G) := p.2
    rw [hfac] at hp
    obtain ⟨a, ha, b, hb, hab⟩ := hp
    exact ⟨⟨a, ha.2⟩, ha.1, ⟨b, hb.2⟩, hb.1, Subtype.ext hab⟩
  have hT₁' : T.subgroupOf X ≤ H₁.subgroupOf X := fun x hx => hT₁ hx
  have hT₂' : T.subgroupOf X ≤ H₂.subgroupOf X := fun x hx => hT₂ hx
  rcases uc22s21ra_top_of_factor hT₁' hT₂' hM₀ hmax hfac' with h | h
  · exact Or.inl (Subgroup.subgroupOf_eq_top.mp h)
  · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)

end GLevel

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
