module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Alg
import CFSG.Quasithin.EmptyFaithful.S1565M7
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Model

structure IsPairModel {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (L₁ L₂ : Subgroup (MulAut V)) (C : Subgroup V)
    (Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V)
    (Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)) : Prop where
  inj : Function.Injective Φ
  mem_iff : ∀ x : MulAut V, x ∈ L₁ ⊔ L₂ ↔ ∃ g, Φ g = x
  left_mem : ∀ g₁ : ↥(StatedSL 2 K₁), Φ (g₁, 1) ∈ L₁
  right_mem : ∀ g₂ : ↥(StatedSL 2 K₂), Φ (1, g₂) ∈ L₂
  surj : Function.Surjective Θ
  ker : ∀ v : V, Θ v = 1 ↔ v ∈ C
  equiv : ∀ (g : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)) (v : V),
    Θ (Φ g v) = (natAct (StatedSL 2 K₁) g.1 (Θ v).1, natAct (StatedSL 2 K₂) g.2 (Θ v).2)

theorem pairModel_of_realizes {V : Type} [CommGroup V] {L₁ L₂ : Subgroup (MulAut V)}
    {W₁ W₂ C : Subgroup V} {K₁ K₂ : Type} [Field K₁] [Finite K₁] [Field K₂] [Finite K₂]
    {π₁ : ↥(StatedSL 2 K₁) →* ↥L₁} {π₂ : ↥(StatedSL 2 K₂) →* ↥L₂}
    (hπ₁ : (FFModel.nat (StatedSL 2 K₁)).RealizesVia L₁ W₁ C π₁)
    (hπ₂ : (FFModel.nat (StatedSL 2 K₂)).RealizesVia L₂ W₂ C π₂)
    (htop : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ ≤ C)
    (hW₁ : ∀ b ∈ L₂, ∀ x ∈ W₁, b x = x) (hW₂ : ∀ a ∈ L₁, ∀ y ∈ W₂, a y = y)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    ∃ (Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V)
      (Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)),
      IsPairModel L₁ L₂ C Φ Θ := by
  have hinj₁ : Function.Injective π₁ := natural_realizes_injective _ hπ₁
  have hinj₂ : Function.Injective π₂ := natural_realizes_injective _ hπ₂
  have hC₁ : C ≤ W₁ := hπ₁.2.1
  obtain ⟨hsurj₁, hUinv₁, -, β₁, hβs₁, hβk₁, hβe₁⟩ := SzN15.NatReal.of_realizesVia hπ₁
  obtain ⟨hsurj₂, hUinv₂, -, β₂, hβs₂, hβk₂, hβe₂⟩ := SzN15.NatReal.of_realizesVia hπ₂
  obtain ⟨ι₁, hι₁⟩ : ∃ ι₁ : ↥(StatedSL 2 K₁) →* MulAut V,
      ∀ g, ι₁ g = ((π₁ g : ↥L₁) : MulAut V) := ⟨L₁.subtype.comp π₁, fun g => rfl⟩
  obtain ⟨ι₂, hι₂⟩ : ∃ ι₂ : ↥(StatedSL 2 K₂) →* MulAut V,
      ∀ g, ι₂ g = ((π₂ g : ↥L₂) : MulAut V) := ⟨L₂.subtype.comp π₂, fun g => rfl⟩
  have hι₁L : ∀ g, ι₁ g ∈ L₁ := fun g => by rw [hι₁]; exact (π₁ g).2
  have hι₂L : ∀ g, ι₂ g ∈ L₂ := fun g => by rw [hι₂]; exact (π₂ g).2
  have hι₁inj : Function.Injective ι₁ := fun x y hxy =>
    hinj₁ (Subtype.ext (by simpa only [hι₁] using hxy))
  have hι₂inj : Function.Injective ι₂ := fun x y hxy =>
    hinj₂ (Subtype.ext (by simpa only [hι₂] using hxy))
  have hι₁W : ∀ g, ∀ u ∈ W₁, ι₁ g u ∈ W₁ := fun g u hu => by
    rw [hι₁]
    exact hUinv₁ (π₁ g) u hu
  have hι₂W : ∀ g, ∀ u ∈ W₂, ι₂ g u ∈ W₂ := fun g u hu => by
    rw [hι₂]
    exact hUinv₂ (π₂ g) u hu
  have hβe₁' : ∀ (g : ↥(StatedSL 2 K₁)) (u : V) (hu : u ∈ W₁) (hu' : ι₁ g u ∈ W₁),
      β₁ ⟨ι₁ g u, hu'⟩ = natAct (StatedSL 2 K₁) g (β₁ ⟨u, hu⟩) := by
    intro g u hu hu'
    have hu'' : ((π₁ g : ↥L₁) : MulAut V) u ∈ W₁ := hUinv₁ (π₁ g) u hu
    have h := hβe₁ g ⟨u, hu⟩ hu''
    have e : (⟨ι₁ g u, hu'⟩ : ↥W₁) = ⟨((π₁ g : ↥L₁) : MulAut V) u, hu''⟩ :=
      Subtype.ext (congrArg (fun f : MulAut V => f u) (hι₁ g))
    rw [e]
    exact h
  have hβe₂' : ∀ (g : ↥(StatedSL 2 K₂)) (u : V) (hu : u ∈ W₂) (hu' : ι₂ g u ∈ W₂),
      β₂ ⟨ι₂ g u, hu'⟩ = natAct (StatedSL 2 K₂) g (β₂ ⟨u, hu⟩) := by
    intro g u hu hu'
    have hu'' : ((π₂ g : ↥L₂) : MulAut V) u ∈ W₂ := hUinv₂ (π₂ g) u hu
    have h := hβe₂ g ⟨u, hu⟩ hu''
    have e : (⟨ι₂ g u, hu'⟩ : ↥W₂) = ⟨((π₂ g : ↥L₂) : MulAut V) u, hu''⟩ :=
      Subtype.ext (congrArg (fun f : MulAut V => f u) (hι₂ g))
    rw [e]
    exact h
  have hcom : ∀ (g₁ : ↥(StatedSL 2 K₁)) (g₂ : ↥(StatedSL 2 K₂)), Commute (ι₁ g₁) (ι₂ g₂) :=
    fun g₁ g₂ => hcomm _ (hι₁L g₁) _ (hι₂L g₂)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V,
      ∀ g, Φ g = ι₁ g.1 * ι₂ g.2 := ⟨ι₁.noncommCoprod ι₂ hcom, fun g => rfl⟩
  have hint : ∀ x ∈ L₁, x ∈ L₂ → x = 1 := by
    intro x hx₁ hx₂
    have hfix : ∀ v : V, x v = v := by
      intro v
      have hv : v ∈ W₁ ⊔ W₂ := by rw [htop]; trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
      rw [map_mul, hW₁ x hx₂ y hy, hW₂ x hx₁ z hz]
    exact MulEquiv.ext hfix
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g₁, g₂⟩ h
    rw [hΦ] at h
    have h' : ι₁ g₁ * ι₂ g₂ = 1 := h
    have h1 : ι₁ g₁ = 1 := by
      refine hint _ (hι₁L g₁) ?_
      rw [eq_inv_of_mul_eq_one_left h']
      exact L₂.inv_mem (hι₂L g₂)
    have h2 : ι₂ g₂ = 1 := by
      rw [h1, one_mul] at h'
      exact h'
    exact Prod.ext (hι₁inj (h1.trans (map_one ι₁).symm)) (hι₂inj (h2.trans (map_one ι₂).symm))
  have hrange : L₁ ⊔ L₂ ≤ Φ.range := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · obtain ⟨g, hg⟩ := hsurj₁ ⟨a, ha⟩
      refine MonoidHom.mem_range.mpr ⟨(g, 1), ?_⟩
      rw [hΦ]
      show ι₁ g * ι₂ 1 = a
      rw [map_one, mul_one, hι₁, hg]
    · obtain ⟨g, hg⟩ := hsurj₂ ⟨b, hb⟩
      refine MonoidHom.mem_range.mpr ⟨(1, g), ?_⟩
      rw [hΦ]
      show ι₁ 1 * ι₂ g = b
      rw [map_one, one_mul, hι₂, hg]
  obtain ⟨Θ, hΘs, hΘk, hΘf⟩ := exists_theta htop hinf hC₁ β₁ β₂ hβk₁ hβk₂ hβs₁ hβs₂
  have hΘeq : ∀ (g : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)) (v : V),
      Θ (Φ g v) = (natAct (StatedSL 2 K₁) g.1 (Θ v).1, natAct (StatedSL 2 K₂) g.2 (Θ v).2) := by
    intro g v
    have hv : v ∈ W₁ ⊔ W₂ := by rw [htop]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
    have h1 : Φ g (y * z) = ι₁ g.1 y * ι₂ g.2 z := by
      rw [hΦ, MulAut.mul_apply, map_mul, hW₁ _ (hι₂L g.2) y hy, map_mul,
        hW₂ _ (hι₁L g.1) _ (hι₂W g.2 z hz)]
    have e1 := hΘf (ι₁ g.1 y) (hι₁W g.1 y hy) (ι₂ g.2 z) (hι₂W g.2 z hz)
    have e2 := hΘf y hy z hz
    rw [h1, e1, e2]
    exact Prod.ext (hβe₁' g.1 y hy _) (hβe₂' g.2 z hz _)
  refine ⟨Φ, Θ, ⟨hΦinj, fun x => ⟨fun hx => ?_, ?_⟩, fun g₁ => ?_, fun g₂ => ?_, hΘs, hΘk, hΘeq⟩⟩
  · obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hrange hx)
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    rw [hΦ]
    exact Subgroup.mul_mem_sup (hι₁L g.1) (hι₂L g.2)
  · rw [hΦ]
    show ι₁ g₁ * ι₂ 1 ∈ L₁
    rw [map_one, mul_one]
    exact hι₁L g₁
  · rw [hΦ]
    show ι₁ 1 * ι₂ g₂ ∈ L₂
    rw [map_one, one_mul]
    exact hι₂L g₂

variable {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂] {L₁ L₂ : Subgroup (MulAut V)}
  {C : Subgroup V} {Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V}
  {Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)}

theorem IsPairModel.card_V [Finite V] [Finite K₁] [Finite K₂] (hM : IsPairModel L₁ L₂ C Φ Θ) :
    Nat.card V = Nat.card ↥C * (Nat.card K₁ ^ 2 * Nat.card K₂ ^ 2) := by
  rw [card_eq_card_ker_mul_card_range Θ]
  have hker : Θ.ker = C := by
    ext v
    rw [MonoidHom.mem_ker, hM.ker]
  have hrng : Θ.range = ⊤ := MonoidHom.range_eq_top.mpr hM.surj
  rw [hker, hrng, Subgroup.card_top, Nat.card_prod, card_multiplicative_fin_two_fun,
    card_multiplicative_fin_two_fun]

theorem card_subgroup_prod {G H : Type} [Group G] [Group H] (A : Subgroup G) (B : Subgroup H) :
    Nat.card ↥(A.prod B) = Nat.card ↥A * Nat.card ↥B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

theorem IsPairModel.map_fixV_le (hM : IsPairModel L₁ L₂ C Φ Θ)
    (B : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) :
    (fixV (B.map Φ)).map Θ ≤
      (fixNat (B.map (MonoidHom.fst _ _))).prod (fixNat (B.map (MonoidHom.snd _ _))) := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Subgroup.mem_map.mp hg
    have h1 : Φ (a, b) v = v := hv _ (Subgroup.mem_map_of_mem Φ hab)
    have h2 := hM.equiv (a, b) v
    rw [h1] at h2
    exact (congrArg Prod.fst h2).symm
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Subgroup.mem_map.mp hg
    have h1 : Φ (a, b) v = v := hv _ (Subgroup.mem_map_of_mem Φ hab)
    have h2 := hM.equiv (a, b) v
    rw [h1] at h2
    exact (congrArg Prod.snd h2).symm

theorem IsPairModel.card_fixV_le [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (B : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) :
    Nat.card ↥(fixV (B.map Φ)) ≤ Nat.card ↥C *
      (Nat.card ↥(fixNat (B.map (MonoidHom.fst _ _))) *
        Nat.card ↥(fixNat (B.map (MonoidHom.snd _ _)))) := by
  rw [← card_subgroup_prod]
  exact card_le_of_map_le Θ hM.ker _ _ (hM.map_fixV_le B)

theorem IsPairModel.exists_lift (hM : IsPairModel L₁ L₂ C Φ Θ) {A : Subgroup (MulAut V)}
    (hA : A ≤ L₁ ⊔ L₂) :
    ∃ Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)), Al.map Φ = A ∧
      Nat.card ↥Al = Nat.card ↥A ∧ ((∀ a ∈ A, a ^ 2 = 1) → ∀ g ∈ Al, g ^ 2 = 1) := by
  have hAmap : (A.comap Φ).map Φ = A := by
    rw [Subgroup.map_comap_eq]
    refine inf_eq_right.mpr (fun a ha => ?_)
    obtain ⟨g, hg⟩ := (hM.mem_iff a).mp (hA ha)
    exact ⟨g, hg⟩
  refine ⟨A.comap Φ, hAmap, ?_, fun hA2 g hg => ?_⟩
  · have h1 : Nat.card ↥((A.comap Φ).map Φ) = Nat.card ↥(A.comap Φ) :=
      Subgroup.card_map_of_injective hM.inj
    rw [hAmap] at h1
    exact h1.symm
  · apply hM.inj
    rw [map_pow, map_one]
    exact hA2 _ hg

end Model

section Existence

theorem exists_pairModel {V : Type} [CommGroup V] {L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₁ : Nat.card ↥L₁ = 4080) (hL₂ : Nat.card ↥L₂ = 4080) :
    ∃ (K₁ K₂ : Type) (_ : Field K₁) (_ : Field K₂) (_ : Finite K₁) (_ : Finite K₂)
      (Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V)
      (Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)),
      Nat.card K₁ = 16 ∧ Nat.card K₂ = 16 ∧ IsPairModel L₁ L₂ (fixV (L₁ ⊔ L₂)) Φ Θ := by
  obtain ⟨⟨_, _, K₁, _, _, _, π₁₀, hπ₁₀⟩, ⟨_, _, K₂, _, _, _, π₂₀, hπ₂₀⟩, htop, hinf, -, hc₁,
    hc₂⟩ := h
  obtain ⟨π₁, hπ₁⟩ : ∃ π : ↥(StatedSL 2 K₁) →* ↥L₁, (FFModel.nat (StatedSL 2 K₁)).RealizesVia L₁
      (commV L₁ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) π := ⟨π₁₀, hπ₁₀⟩
  obtain ⟨π₂, hπ₂⟩ : ∃ π : ↥(StatedSL 2 K₂) →* ↥L₂, (FFModel.nat (StatedSL 2 K₂)).RealizesVia L₂
      (commV L₂ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) π := ⟨π₂₀, hπ₂₀⟩
  have hfix₂ : fixV (L₁ ⊔ L₂) ≤ fixV L₂ := by
    intro c hc b hb
    exact hc b (Subgroup.mem_sup_right hb)
  have hfix₁ : fixV (L₁ ⊔ L₂) ≤ fixV L₁ := by
    intro c hc a ha
    exact hc a (Subgroup.mem_sup_left ha)
  have hW₁ : ∀ b ∈ L₂, ∀ x ∈ commV L₁ ⊔ fixV (L₁ ⊔ L₂), b x = x := by
    intro b hb x hx
    have hle : commV L₁ ⊔ fixV (L₁ ⊔ L₂) ≤ fixV L₂ := sup_le hc₁ hfix₂
    exact hle hx b hb
  have hW₂ : ∀ a ∈ L₁, ∀ y ∈ commV L₂ ⊔ fixV (L₁ ⊔ L₂), a y = y := by
    intro a ha y hy
    have hle : commV L₂ ⊔ fixV (L₁ ⊔ L₂) ≤ fixV L₁ := sup_le hc₂ hfix₁
    exact hle hy a ha
  have hc₁' : Nat.card K₁ = 16 := by
    refine card_field_eq_sixteen ?_
    rw [← hL₁]
    exact Nat.card_congr (Equiv.ofBijective π₁ ⟨natural_realizes_injective _ hπ₁, hπ₁.1⟩)
  have hc₂' : Nat.card K₂ = 16 := by
    refine card_field_eq_sixteen ?_
    rw [← hL₂]
    exact Nat.card_congr (Equiv.ofBijective π₂ ⟨natural_realizes_injective _ hπ₂, hπ₂.1⟩)
  obtain ⟨Φ, Θ, hM⟩ := pairModel_of_realizes hπ₁ hπ₂ htop.symm hinf hW₁ hW₂ hcomm
  exact ⟨K₁, K₂, inferInstance, inferInstance, inferInstance, inferInstance, Φ, Θ, hc₁', hc₂', hM⟩

end Existence

end CFSG.Quasithin.S146zU.UC2
