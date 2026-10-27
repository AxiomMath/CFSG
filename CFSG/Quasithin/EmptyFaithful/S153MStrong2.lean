module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef
import CFSG.Quasithin.EmptyFaithful.S1565M7
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.Open.MatrixFixedVectors
import CFSG.Quasithin.EmptyFaithful.S146zUC2Alg

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

section Strong2

private theorem card_eq_card_ker_mul_card_range' {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Nat.card G = Nat.card ↥f.ker * Nat.card ↥f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

private theorem card_multiplicative_fin_two_fun (K : Type) [Finite K] :
    Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp

private abbrev FixNat (K : Type) [Field K] (B : Subgroup ↥(StatedSL 2 K)) : Type :=
  {x : Multiplicative (Fin 2 → K) // ∀ g ∈ B, natAct (StatedSL 2 K) g x = x}

private theorem card_natAct_fixed_le' {K : Type} [Field K] [Finite K] (g : ↥(StatedSL 2 K))
    (hg : g ≠ 1) :
    Nat.card {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x} ≤ Nat.card K :=
  (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).le.trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le fun h => hg (Subtype.ext (Units.ext h)))

private theorem card_exp_two_le_field {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B ≤ Nat.card K :=
  CFSG.Quasithin.S146zU.UC2.card_le_field_of_exp_two hK B hB

private theorem card_mul_card_fixNat_le {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B * Nat.card (FixNat K B) ≤ Nat.card K ^ 2 := by
  by_cases hbot : B = ⊥
  · subst hbot
    rw [Subgroup.card_bot, one_mul]
    calc Nat.card (FixNat K ⊥) ≤ Nat.card (Multiplicative (Fin 2 → K)) :=
          Finite.card_subtype_le _
      _ = Nat.card K ^ 2 := card_multiplicative_fin_two_fun K
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hg1 : (a : ↥(StatedSL 2 K)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hfix : Nat.card (FixNat K B) ≤ Nat.card K := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : FixNat K B => (⟨x.1, x.2 (a : ↥(StatedSL 2 K)) a.2⟩ :
          {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x}))
        ?_) (card_natAct_fixed_le' _ hg1)
      intro x y h
      have h1 : (x : Multiplicative (Fin 2 → K)) = (y : Multiplicative (Fin 2 → K)) :=
        congrArg (fun z : {x : Multiplicative (Fin 2 → K) //
          natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x} => (z : Multiplicative (Fin 2 → K))) h
      exact Subtype.ext h1
    calc Nat.card ↥B * Nat.card (FixNat K B) ≤ Nat.card K * Nat.card K :=
          Nat.mul_le_mul (card_exp_two_le_field hK B hB) hfix
      _ = Nat.card K ^ 2 := (sq _).symm

private theorem exists_theta {V M₁ M₂ : Type} [CommGroup V] [Group M₁] [Group M₂]
    {W₁ W₂ C : Subgroup V} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ ≤ C) (hC₁ : C ≤ W₁)
    (β₁ : ↥W₁ →* M₁) (β₂ : ↥W₂ →* M₂) (hk₁ : ∀ u : ↥W₁, β₁ u = 1 ↔ (u : V) ∈ C)
    (hk₂ : ∀ u : ↥W₂, β₂ u = 1 ↔ (u : V) ∈ C) (hs₁ : Function.Surjective β₁)
    (hs₂ : Function.Surjective β₂) :
    ∃ Θ : V →* M₁ × M₂, Function.Surjective Θ ∧ (∀ v, Θ v = 1 ↔ v ∈ C) ∧
      ∀ (x : V) (hx : x ∈ W₁) (y : V) (hy : y ∈ W₂), Θ (x * y) = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥W₁ × ↥W₂ →* V, ∀ p, Ψ p = (p.1 : V) * (p.2 : V) :=
    ⟨W₁.subtype.coprod W₂.subtype, fun p => rfl⟩
  have hΨs : Function.Surjective Ψ := by
    intro v
    have hv : v ∈ W₁ ⊔ W₂ := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hΨ _⟩
  have hker : Ψ.ker ≤ (β₁.prodMap β₂).ker := by
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hΨ] at hxy
    have hxy' : (x : V) * (y : V) = 1 := hxy
    have hx : (x : V) ∈ C := by
      refine hinf ⟨x.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hxy']
      exact W₂.inv_mem y.2
    have hy : (y : V) ∈ C := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact C.inv_mem hx
    rw [MonoidHom.mem_ker]
    exact Prod.ext ((hk₁ x).mpr hx) ((hk₂ y).mpr hy)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : V →* M₁ × M₂, ∀ p, Θ (Ψ p) = (β₁ p.1, β₂ p.2) :=
    ⟨MonoidHom.liftOfSurjective Ψ hΨs ⟨β₁.prodMap β₂, hker⟩, fun p =>
      MonoidHom.liftOfRightInverse_comp_apply Ψ (Function.surjInv hΨs)
        (Function.rightInverse_surjInv hΨs) ⟨β₁.prodMap β₂, hker⟩ p⟩
  have hform : ∀ (x : V) (hx : x ∈ W₁) (y : V) (hy : y ∈ W₂),
      Θ (x * y) = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) := fun x hx y hy => by
    have := hΘ (⟨x, hx⟩, ⟨y, hy⟩)
    rw [hΨ] at this
    exact this
  refine ⟨Θ, ?_, ?_, hform⟩
  · rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := hs₁ a
    obtain ⟨y, rfl⟩ := hs₂ b
    exact ⟨(x : V) * (y : V), hform x x.2 y y.2⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨⟨x, y⟩, rfl⟩ := hΨs v
      rw [hΘ] at hv
      have hx : (x : V) ∈ C := (hk₁ x).mp (congrArg Prod.fst hv)
      have hy : (y : V) ∈ C := (hk₂ y).mp (congrArg Prod.snd hv)
      rw [hΨ]
      exact C.mul_mem hx hy
    · intro hv
      have h1 := hform v (hC₁ hv) 1 W₂.one_mem
      rw [mul_one] at h1
      rw [h1]
      refine Prod.ext ?_ ?_
      · exact (hk₁ ⟨v, hC₁ hv⟩).mpr hv
      · exact map_one β₂

private theorem core_count {V : Type} [CommGroup V] [Finite V]
    {L₁ L₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    {K₁ K₂ : Type} [Field K₁] [Finite K₁] [Field K₂] [Finite K₂] {m₁ m₂ : ℕ}
    (hK₁ : Nat.card K₁ = 2 ^ m₁) (hK₂ : Nat.card K₂ = 2 ^ m₂)
    {π₁ : ↥(StatedSL 2 K₁) →* ↥L₁} {π₂ : ↥(StatedSL 2 K₂) →* ↥L₂}
    (hπ₁ : (FFModel.nat (StatedSL 2 K₁)).RealizesVia L₁ W₁ C π₁)
    (hπ₂ : (FFModel.nat (StatedSL 2 K₂)).RealizesVia L₂ W₂ C π₂)
    (htop : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ ≤ C)
    (hW₁ : ∀ b ∈ L₂, ∀ x ∈ W₁, b x = x) (hW₂ : ∀ a ∈ L₁, ∀ y ∈ W₂, a y = y)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L₁ ⊔ L₂) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V := by
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
  obtain ⟨Al, hAl⟩ : ∃ Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)),
      ∀ g, g ∈ Al ↔ Φ g ∈ A := ⟨A.comap Φ, fun g => Iff.rfl⟩
  have hAAl : Nat.card ↥A ≤ Nat.card ↥Al := by
    refine Nat.card_le_card_of_surjective (fun g : ↥Al => (⟨Φ g, (hAl g).mp g.2⟩ : ↥A)) ?_
    rintro ⟨a, ha⟩
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hrange (hAL ha))
    exact ⟨⟨g, (hAl g).mpr (by rw [hg]; exact ha)⟩, Subtype.ext hg⟩
  have hsqAl : ∀ g ∈ Al, g ^ 2 = 1 := by
    intro g hg
    apply hΦinj
    rw [map_pow, map_one]
    exact hA2 _ ((hAl g).mp hg)
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Subgroup ↥(StatedSL 2 K₁), ∀ x, x ∈ A₁ ↔ ∃ y, (x, y) ∈ Al :=
    ⟨Al.map (MonoidHom.fst _ _), fun x => by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        exact ⟨b, hab⟩
      · rintro ⟨y, hy⟩
        exact ⟨(x, y), hy, rfl⟩⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : Subgroup ↥(StatedSL 2 K₂), ∀ y, y ∈ A₂ ↔ ∃ x, (x, y) ∈ Al :=
    ⟨Al.map (MonoidHom.snd _ _), fun y => by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        exact ⟨a, hab⟩
      · rintro ⟨x, hx⟩
        exact ⟨(x, y), hx, rfl⟩⟩
  have hsq₁ : ∀ x ∈ A₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := (hA₁ x).mp hx
    have := congrArg Prod.fst (hsqAl _ hy)
    simpa using this
  have hsq₂ : ∀ y ∈ A₂, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := (hA₂ y).mp hy
    have := congrArg Prod.snd (hsqAl _ hx)
    simpa using this
  have hAlcard : Nat.card ↥Al ≤ Nat.card ↥A₁ * Nat.card ↥A₂ := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun g : ↥Al =>
      ((⟨g.1.1, (hA₁ _).mpr ⟨g.1.2, g.2⟩⟩ : ↥A₁), (⟨g.1.2, (hA₂ _).mpr ⟨g.1.1, g.2⟩⟩ : ↥A₂))) ?_
    intro g h hgh
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ =>
      ((p.1 : ↥(StatedSL 2 K₁)), (p.2 : ↥(StatedSL 2 K₂)))) hgh
    exact Subtype.ext h1
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
  have hfixΘ : ∀ v ∈ fixV A, (∀ g ∈ A₁, natAct (StatedSL 2 K₁) g (Θ v).1 = (Θ v).1) ∧
      ∀ g ∈ A₂, natAct (StatedSL 2 K₂) g (Θ v).2 = (Θ v).2 := by
    intro v hv
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · obtain ⟨g₂, hg₂⟩ := (hA₁ g).mp hg
      have h1 : Φ (g, g₂) v = v := hv _ ((hAl _).mp hg₂)
      have h2 := hΘeq (g, g₂) v
      rw [h1] at h2
      exact (congrArg Prod.fst h2).symm
    · obtain ⟨g₁, hg₁⟩ := (hA₂ g).mp hg
      have h1 : Φ (g₁, g) v = v := hv _ ((hAl _).mp hg₁)
      have h2 := hΘeq (g₁, g) v
      rw [h1] at h2
      exact (congrArg Prod.snd h2).symm
  have hF : Nat.card ↥(fixV A) ≤
      Nat.card ↥C * (Nat.card (FixNat K₁ A₁) * Nat.card (FixNat K₂ A₂)) := by
    obtain ⟨θF, hθF⟩ : ∃ θF : ↥(fixV A) →*
        Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂), ∀ v, θF v = Θ v :=
      ⟨Θ.comp (fixV A).subtype, fun v => rfl⟩
    have hker : ∀ c : ↥θF.ker, ((c : ↥(fixV A)) : V) ∈ C := by
      intro c
      have h1 : θF (c : ↥(fixV A)) = 1 := c.2
      rw [hθF] at h1
      exact (hΘk _).mp h1
    have hxfix : ∀ x : ↥θF.range,
        (∀ g ∈ A₁, natAct (StatedSL 2 K₁) g
          (x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).1 =
          (x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).1) ∧
        ∀ g ∈ A₂, natAct (StatedSL 2 K₂) g
          (x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).2 =
          (x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).2 := by
      intro x
      obtain ⟨w, hw⟩ := x.2
      have hx : (x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)) = Θ (w : V) := by
        rw [← hw, hθF]
      rw [hx]
      exact hfixΘ (w : V) w.2
    rw [card_eq_card_ker_mul_card_range' θF]
    refine Nat.mul_le_mul ?_ ?_
    · refine Nat.card_le_card_of_injective
        (fun c : ↥θF.ker => (⟨((c : ↥(fixV A)) : V), hker c⟩ : ↥C)) ?_
      intro c d h
      have h1 : ((c : ↥(fixV A)) : V) = ((d : ↥(fixV A)) : V) :=
        congrArg (fun z : ↥C => (z : V)) h
      exact Subtype.ext (Subtype.ext h1)
    · rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective (fun x : ↥θF.range =>
        ((⟨(x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).1, (hxfix x).1⟩ :
            FixNat K₁ A₁),
          (⟨(x : Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)).2, (hxfix x).2⟩ :
            FixNat K₂ A₂))) ?_
      intro x y h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Subtype.ext (Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))
  have hVcard : Nat.card V = Nat.card ↥C * (Nat.card K₁ ^ 2 * Nat.card K₂ ^ 2) := by
    rw [card_eq_card_ker_mul_card_range' Θ]
    have hker : Θ.ker = C := by
      ext v
      rw [MonoidHom.mem_ker, hΘk]
    have hrng : Θ.range = ⊤ := MonoidHom.range_eq_top.mpr hΘs
    rw [hker, hrng, Subgroup.card_top, Nat.card_prod, card_multiplicative_fin_two_fun,
      card_multiplicative_fin_two_fun]
  calc Nat.card ↥A * Nat.card ↥(fixV A)
      ≤ (Nat.card ↥A₁ * Nat.card ↥A₂) *
        (Nat.card ↥C * (Nat.card (FixNat K₁ A₁) * Nat.card (FixNat K₂ A₂))) :=
        Nat.mul_le_mul (hAAl.trans hAlcard) hF
    _ = Nat.card ↥C * ((Nat.card ↥A₁ * Nat.card (FixNat K₁ A₁)) *
        (Nat.card ↥A₂ * Nat.card (FixNat K₂ A₂))) := by ring
    _ ≤ Nat.card ↥C * (Nat.card K₁ ^ 2 * Nat.card K₂ ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (card_mul_card_fixNat_le hK₁ A₁ hsq₁)
          (card_mul_card_fixNat_le hK₂ A₂ hsq₂))
    _ = Nat.card V := hVcard.symm

end Strong2

theorem not_strong_of_twoNat {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (h : TwoNat L₁ L₂ τ)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L₁ ⊔ L₂) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V := by
  have _ := hV
  have _ := hA1
  obtain ⟨⟨_, _, K₁, _, _, hK₁, π₁₀, hπ₁₀⟩, ⟨_, _, K₂, _, _, hK₂, π₂₀, hπ₂₀⟩, htop, hinf, -, hc₁,
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
  exact core_count hK₁ hK₂ hπ₁ hπ₂ htop.symm hinf hW₁ hW₂ hcomm hAL hA2.2

end S153M

end CFSG.Quasithin
