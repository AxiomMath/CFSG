module

public import CFSG.Monster.B.GSide.TwoBCentralizer
public import CFSG.Monster.B.Recog.GenericBlocks
public import CFSG.Monster.B.Recog.GenericGoldschmidtArithOmega
public import CFSG.Monster.B.Recog.GenericGoldschmidtSection
public import CFSG.Monster.B.GSide.TwoDNativeOrderFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

namespace TwoD

open scoped IsMulCommutative in
theorem not_isMulCommutative_of_four_dvd {O : Type*} [Group O] {Ω : Subgroup O}
    (hΩ : IsSimpleGroup Ω) (h4 : 4 ∣ Nat.card Ω) : ¬ IsMulCommutative Ω := by
  intro hc
  have hp : (Nat.card Ω).Prime := IsSimpleGroup.prime_card
  rcases hp.eq_one_or_self_of_dvd 4 h4 with h | h
  · omega
  · rw [← h] at hp
    norm_num at hp

theorem eq_top_of_package {Y : Type} [Group Y] [Finite Y] {t : Y}
    (ht : ∀ g : Y, g * t = t * g) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {Y₀ X W : Subgroup Y} {D₀ : Set Y}
    (htX : t ∈ X) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXY₀ : X ≤ Y₀) (hY₀N : Y₀ ≤ Subgroup.normalizer (X : Set Y))
    (hNY₀ : Subgroup.normalizer (X : Set Y) ≤ Y₀)
    (hWX : W ≤ X) (hW1 : W ≠ ⊥) (htW : t ∉ W) (hD₀X : D₀ ⊆ X)
    (hWD₀ : ∀ w ∈ W, w ≠ 1 → w ∈ D₀) (hWn : ∀ g ∈ Y₀, ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hD₀ : ∀ g : Y, ∀ a ∈ D₀, g * a * g⁻¹ ∈ Y₀ → g ∈ Y₀)
    (T : Sylow 2 Y) (hTY₀ : (T : Subgroup Y) ≤ Y₀) (hT : (Nat.card Y).factorization 2 = 38)
    (hQB1 : ∀ R : Subgroup Y, R ≤ X → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers t ∨ R = W ∨ R = X)
    (hQB1c : ∀ g ∈ Y₀, (∀ x ∈ X, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * t) →
      ∀ x ∈ X, g * x * g⁻¹ = x)
    (hC2 : IsPGroup 2 (Subgroup.centralizer (X : Set Y)))
    {O : Type} [Group O] (ρ : ↥Y₀ →* O) (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥Y₀, ρ g = 1 ↔ ∀ x ∈ X, (g : Y) * x * (g : Y)⁻¹ = x)
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hΩcard : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card Ω)
    (hOY : CFSG.oddCore Y = ⊥) (hGold : GoldschmidtTheorem) :
    Y₀ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : (Subgroup.zpowers t).Normal := TwoB.zpowers_normal_of_central ht
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.zpowers t)) :=
    QuotientGroup.mk'_surjective _
  have hker' : (QuotientGroup.mk' (Subgroup.zpowers t)).ker = Subgroup.zpowers t :=
    QuotientGroup.ker_mk' _
  have hNeq : Subgroup.normalizer (X : Set Y) = Y₀ := le_antisymm hNY₀ hY₀N
  have hSCY := Recog.strongly_closed_of_blocks hXab hX2 hD₀X hXY₀ hY₀N hNY₀ hD₀ T hTY₀ hWX hW1
    hWD₀ hWn
  have hXT : X ≤ T := TwoB.le_sylow_of_le_normalizer
    (TwoB.isPGroup_of_sq ht2 fun x hx => Or.inl (hX2 x hx)) T (hTY₀.trans hY₀N)
  have htT : t ∈ (T : Subgroup Y) := hXT htX
  have hOX : CFSG.oddCore (Y ⧸ Subgroup.zpowers t) = ⊥ :=
    oddCore_eq_bot_iff.2 fun M hM hMo =>
      eq_bot_of_odd_normal_quot ht ht2 (oddCore_eq_bot_iff.1 hOY) M hM hMo
  have hVS : X.map (QuotientGroup.mk' (Subgroup.zpowers t)) ≤
      ((T.mapSurjective hπ : Sylow 2 (Y ⧸ Subgroup.zpowers t)) :
        Subgroup (Y ⧸ Subgroup.zpowers t)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hXT
  have hVab : IsMulCommutative (X.map (QuotientGroup.mk' (Subgroup.zpowers t))) :=
    ⟨⟨fun x y => Subtype.ext (TwoB.map_comm hker'
      (fun q hq r hr => Or.inl (hXab q hq r hr)) x x.2 y y.2)⟩⟩
  have hclosed : ∀ a ∈ X.map (QuotientGroup.mk' (Subgroup.zpowers t)),
      ∀ g : Y ⧸ Subgroup.zpowers t,
        g⁻¹ * a * g ∈ ((T.mapSurjective hπ : Sylow 2 (Y ⧸ Subgroup.zpowers t)) :
          Subgroup (Y ⧸ Subgroup.zpowers t)) →
        g⁻¹ * a * g ∈ X.map (QuotientGroup.mk' (Subgroup.zpowers t)) := by
    rintro _ ⟨x, hx, rfl⟩ g hg
    obtain ⟨g', rfl⟩ := hπ g
    rw [Sylow.coe_mapSurjective, ← map_inv, ← map_mul, ← map_mul,
      TwoB.map_mem_map_iff hker' htT] at hg
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hSCY x hx g' hg, rfl⟩
  have hcen : ∀ s : Y, QuotientGroup.mk' (Subgroup.zpowers t) s ∈
      Subgroup.centralizer ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t)) → s ∈ Y₀ ∧ ∀ x ∈ X, s * x * s⁻¹ = x := by
    intro s hs
    have h1 := TwoB.conj_of_map_mem_centralizer hker' ht ht2 hs
    have h2 := TwoB.conj_of_map_mem_centralizer hker' ht ht2
      (show QuotientGroup.mk' (Subgroup.zpowers t) s⁻¹ ∈ Subgroup.centralizer
          ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
            Set (Y ⧸ Subgroup.zpowers t)) by
        rw [map_inv]
        exact Subgroup.inv_mem _ hs)
    have hsN : s ∈ Subgroup.normalizer (X : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rcases h1 h hh with e | e <;> rw [e]
        · exact hh
        · exact X.mul_mem hh htX
      · intro hh
        have e : h = s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ := by group
        rw [e]
        rcases h2 _ hh with e' | e' <;> rw [e']
        · exact hh
        · exact X.mul_mem hh htX
    have hsY : s ∈ Y₀ := hNeq ▸ hsN
    exact ⟨hsY, hQB1c s hsY h1⟩
  have hC2bar : IsPGroup 2 (Subgroup.centralizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t))) := by
    refine (hC2.map (QuotientGroup.mk' (Subgroup.zpowers t))).to_le ?_
    intro w hw
    obtain ⟨s, rfl⟩ := hπ w
    obtain ⟨-, hsX⟩ := hcen s hw
    refine ⟨s, Subgroup.mem_centralizer_iff.2 fun x hx => ?_, rfl⟩
    calc x * s = s * x * s⁻¹ * s := by rw [hsX x hx]
      _ = s * x := by group
  have hQB1' : ∀ U : Subgroup (Y ⧸ Subgroup.zpowers t),
      U ≤ X.map (QuotientGroup.mk' (Subgroup.zpowers t)) →
      Subgroup.normalizer ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t)) ≤ Subgroup.normalizer (U : Set (Y ⧸ Subgroup.zpowers t)) →
      U = ⊥ ∨ U = X.map (QuotientGroup.mk' (Subgroup.zpowers t)) := by
    intro U hUX hNU
    have htU : t ∈ U.comap (QuotientGroup.mk' (Subgroup.zpowers t)) := by
      show QuotientGroup.mk' (Subgroup.zpowers t) t ∈ U
      rw [(TwoB.map_eq_one_iff hker' ht2).2 (Or.inr rfl)]
      exact U.one_mem
    have hUX' : U.comap (QuotientGroup.mk' (Subgroup.zpowers t)) ≤ X := fun u hu =>
      (TwoB.map_mem_map_iff hker' htX u).1 (hUX hu)
    have hUn : ∀ g ∈ Y₀, ∀ r ∈ U.comap (QuotientGroup.mk' (Subgroup.zpowers t)),
        g * r * g⁻¹ ∈ U.comap (QuotientGroup.mk' (Subgroup.zpowers t)) := by
      intro g hg r hr
      show QuotientGroup.mk' (Subgroup.zpowers t) (g * r * g⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv]
      have hgN := (TwoB.map_mem_normalizer_iff hπ hker' htX g).2 (hNeq ▸ hg)
      exact (Subgroup.mem_normalizer_iff.1 (hNU hgN) _).1 hr
    have hmap : (U.comap (QuotientGroup.mk' (Subgroup.zpowers t))).map
        (QuotientGroup.mk' (Subgroup.zpowers t)) = U :=
      Subgroup.map_comap_eq_self_of_surjective hπ U
    rcases hQB1 _ hUX' hUn with h | h | h | h
    · exfalso
      rw [h] at htU
      exact ht1 (Subgroup.mem_bot.1 htU)
    · left
      rw [← hmap, h, Subgroup.map_eq_bot_iff, hker']
    · exfalso
      rw [h] at htU
      exact htW htU
    · right
      rw [← hmap, h]
  have hmemN : ∀ y : ↥Y₀, QuotientGroup.mk' (Subgroup.zpowers t) (y : Y) ∈
      Subgroup.normalizer ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t)) := fun y =>
    (TwoB.map_mem_normalizer_iff hπ hker' htX y).2 (hNeq ▸ y.2)
  let πY : ↥Y₀ →* ↥(Subgroup.normalizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t))) :=
    ((QuotientGroup.mk' (Subgroup.zpowers t)).comp Y₀.subtype).codRestrict _ hmemN
  have hπYv : ∀ y : ↥Y₀, ((πY y : _) : Y ⧸ Subgroup.zpowers t) =
      QuotientGroup.mk' (Subgroup.zpowers t) (y : Y) := fun _ => rfl
  have hπY : Function.Surjective πY := by
    rintro ⟨n, hn⟩
    have hn' := hn
    rw [TwoB.normalizer_map_eq hπ hker' htX hNeq] at hn'
    obtain ⟨y, hy, hyn⟩ := hn'
    exact ⟨⟨y, hy⟩, Subtype.ext hyn⟩
  have hkerle : πY.ker ≤ ρ.ker := by
    intro y hy
    have h1 : QuotientGroup.mk' (Subgroup.zpowers t) (y : Y) = 1 := congrArg Subtype.val hy
    rw [TwoB.map_eq_one_iff hker' ht2] at h1
    rw [MonoidHom.mem_ker, hker]
    intro x hx
    rcases h1 with h1 | h1 <;> rw [h1]
    · group
    · rw [← ht x, mul_inv_cancel_right]
  let ρbar : ↥(Subgroup.normalizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t))) →* O :=
    (QuotientGroup.lift πY.ker ρ hkerle).comp
      (QuotientGroup.quotientKerEquivOfSurjective πY hπY).symm.toMonoidHom
  have hρbar : ∀ y : ↥Y₀, ρbar (πY y) = ρ y := by
    intro y
    show QuotientGroup.lift πY.ker ρ hkerle
      ((QuotientGroup.quotientKerEquivOfSurjective πY hπY).symm (πY y)) = ρ y
    have e : (QuotientGroup.quotientKerEquivOfSurjective πY hπY).symm (πY y) =
        (y : ↥Y₀ ⧸ πY.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [e]
    rfl
  have hρbar' : Function.Surjective ρbar := by
    intro o
    obtain ⟨y, rfl⟩ := hρ o
    exact ⟨πY y, hρbar y⟩
  have hkerbar : ρbar.ker = (Subgroup.centralizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t))).subgroupOf (Subgroup.normalizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t))) := by
    ext n
    obtain ⟨y, rfl⟩ := hπY n
    rw [MonoidHom.mem_ker, hρbar, hker, Subgroup.mem_subgroupOf, hπYv]
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      calc x * (y : Y) = (y : Y) * x * (y : Y)⁻¹ * y := by rw [h x hx]
        _ = (y : Y) * x := by group
    · intro h
      exact (hcen y h).2
  have hv2 : (Nat.card (Y ⧸ Subgroup.zpowers t)).factorization 2 = 37 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers t)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact ht2) ht1] at h1
    rw [h1, Nat.factorization_mul Nat.card_pos.ne' two_ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at hT
    omega
  have hAr := Recog.hAr_of_card_omega8 hv2 (n₀ := Nat.card Ω) hΩcard
  have hkerbar' : ∀ g, ρbar g = 1 ↔ (g : Y ⧸ Subgroup.zpowers t) ∈ Subgroup.centralizer
      ((X.map (QuotientGroup.mk' (Subgroup.zpowers t)) : Subgroup _) :
        Set (Y ⧸ Subgroup.zpowers t)) := fun g => by
    rw [← MonoidHom.mem_ker, hkerbar, Subgroup.mem_subgroupOf]
  have hΩnab : ¬ IsMulCommutative Ω :=
    not_isMulCommutative_of_four_dvd hΩ ((Dvd.intro (2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7) (by ring)).trans
      hΩcard)
  have hV := Recog.normal_of_goldschmidt_conclusion_of_section (T.mapSurjective hπ) hVS
    (hGold _ (T.mapSurjective hπ) _ hVS hVab hclosed) hclosed hOX hC2bar hQB1' ρbar hρbar'
    hkerbar' Ω hΩ hΩnab hΩmin hAr
  have hXnorm : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : QuotientGroup.mk' (Subgroup.zpowers t) (g * x * g⁻¹) ∈
        X.map (QuotientGroup.mk' (Subgroup.zpowers t)) := by
      rw [map_mul, map_mul, map_inv]
      exact hV.conj_mem _ ⟨x, hx, rfl⟩ _
    exact (TwoB.map_mem_map_iff hker' htX _).1 h1
  rw [← hNeq, Subgroup.normalizer_eq_top_iff.2 hXnorm]

theorem centralizer_le_range_gen
    {S G : Type} [Group S] [Group G] [Finite G] {Φ : S →* G}
    (hinj : Function.Injective Φ) {d : G}
    (hCent : ∀ m ∈ Φ.range, Subgroup.centralizer {m * d * m⁻¹} ≤ Φ.range)
    (hD : ∀ y ∈ Φ.range, IsConj d y → y ∈ dZero Φ.range d)
    (hnorm : ∀ X : Subgroup G, X ≤ Φ.range → (∃ a ∈ X, a ∈ dZero Φ.range d) →
      Subgroup.normalizer (X : Set G) ≤ Φ.range)
    (P₁ P₂ : S → Prop) (hP₁ : ∀ a, P₁ a → Φ a ∈ dZero Φ.range d)
    (hP₂ : ∀ a, P₂ a → a * a = 1 ∧ Subgroup.centralizer {Φ a} ≤ Φ.range)
    (hInv : ∀ s : S, s * s = 1 → ∃ a, P₁ a ∧ a * s = s * a)
    {t : S} (ht2 : t * t = 1) (ht1 : t ≠ 1) (X₀ W₀ : Subgroup S)
    (htX₀ : t ∈ X₀) (hX₀ab : ∀ x ∈ X₀, ∀ y ∈ X₀, x * y = y * x) (hX₀2 : ∀ x ∈ X₀, x * x = 1)
    (hW₀X₀ : W₀ ≤ X₀) (htW₀ : t ∉ W₀) (hW₀ : ∀ w ∈ W₀, w ≠ 1 → P₂ w)
    (ha₀ : ∃ a ∈ X₀, P₁ a) (hab : ∃ a ∈ W₀, ∃ b ∈ W₀, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hW₀n : ∀ g ∈ Subgroup.centralizer {t}, ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀)
    (hNX : Subgroup.centralizer {t} ≤ Subgroup.normalizer (X₀ : Set S))
    (hQB1 : ∀ R : Subgroup S, R ≤ X₀ →
      (∀ g ∈ Subgroup.centralizer {t}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers t ∨ R = W₀ ∨ R = X₀)
    (hQB1c : ∀ g ∈ Subgroup.centralizer {t},
      (∀ x ∈ X₀, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * t) → ∀ x ∈ X₀, g * x * g⁻¹ = x)
    (hC2 : IsPGroup 2 (Subgroup.centralizer (X₀ : Set S)))
    {O : Type} [Group O] (ρ : ↥(Subgroup.centralizer {t}) →* O) (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥(Subgroup.centralizer {t}),
      ρ g = 1 ↔ ∀ x ∈ X₀, (g : S) * x * (g : S)⁻¹ = x)
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hΩcard : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card Ω)
    (hORD : Nat.card (Subgroup.centralizer {t} : Subgroup S) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7)
    (hOt : CFSG.oddCore (Subgroup.centralizer {t}) = ⊥) (hGold : GoldschmidtTheorem) :
    Subgroup.centralizer {Φ t} ≤ Φ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCiff : ∀ s : S, Φ s ∈ Subgroup.centralizer {Φ t} ↔ s ∈ Subgroup.centralizer {t} :=
    fun s => TwoB.map_mem_centralizer_map_iff hinj
  have hX₀C : X₀ ≤ Subgroup.centralizer {t} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hX₀ab x hx t htX₀)
  have hInvG : ∀ x ∈ Φ.range, x * x = 1 → ∃ a ∈ dZero Φ.range d, a * x = x * a := by
    rintro _ ⟨s, rfl⟩ hs2
    obtain ⟨a, ha, has⟩ := hInv s (hinj (by rw [map_mul, hs2, map_one]))
    exact ⟨Φ a, hP₁ a ha, by rw [← map_mul, has, map_mul]⟩
  have hblock : ∀ a, (P₁ a ∨ P₂ a) → ∀ g : G, g * Φ a * g⁻¹ ∈ Φ.range → g ∈ Φ.range := by
    intro a ha g hg
    rcases ha with ha | ha
    · obtain ⟨m, hm, hma⟩ := hP₁ a ha
      refine mem_of_conj_mem_dZero hCent ⟨m, hm, hma⟩ (hD _ hg ?_)
      rw [← hma]
      exact isConj_iff.2 ⟨g * m, by group⟩
    · obtain ⟨ha2, haC⟩ := hP₂ a ha
      exact Recog.mem_of_conj_mem_of_block_of_class hCent hD hInvG
        (by rw [← map_mul, ha2, map_one]) haC hg
  set C := Subgroup.centralizer {Φ t} with hCdef
  set tY : C := ⟨Φ t, mem_centralizer_singleton_self _⟩ with htYdef
  set Y₀ : Subgroup C := Φ.range.subgroupOf C with hY₀def
  set XY : Subgroup C := (X₀.map Φ).subgroupOf C with hXYdef
  set WY : Subgroup C := (W₀.map Φ).subgroupOf C with hWYdef
  set D₀ : Set C := {y | ∃ a ∈ X₀, (P₁ a ∨ P₂ a) ∧ (y : G) = Φ a} with hD₀def
  have hY₀ : ∀ y : C, y ∈ Y₀ → ∃ s, s ∈ Subgroup.centralizer {t} ∧ Φ s = (y : G) := by
    intro y hy
    obtain ⟨s, hs⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨s, (hCiff s).1 (by rw [hs]; exact y.2), hs⟩
  have hmk : ∀ x ∈ X₀, Φ x ∈ C := fun x hx => (hCiff x).2 (hX₀C hx)
  have htC : ∀ g : C, g * tY = tY * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have htC2 : tY * tY = 1 := Subtype.ext (show Φ t * Φ t = 1 by rw [← map_mul, ht2, map_one])
  have htC1 : tY ≠ 1 := fun h => ht1 (hinj ((congrArg Subtype.val h).trans (map_one Φ).symm))
  have hmemXY : ∀ x (hx : x ∈ X₀), (⟨Φ x, hmk x hx⟩ : C) ∈ XY := fun x hx =>
    Subgroup.mem_subgroupOf.2 ⟨x, hx, rfl⟩
  have hXYmem : ∀ y : C, y ∈ XY → ∃ x ∈ X₀, Φ x = (y : G) := fun y hy =>
    Subgroup.mem_subgroupOf.1 hy
  have htX : tY ∈ XY := hmemXY t htX₀
  have hXab : ∀ x ∈ XY, ∀ y ∈ XY, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', hxx'⟩ := hXYmem x hx
    obtain ⟨y', hy', hyy'⟩ := hXYmem y hy
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hxx', ← hyy', ← map_mul, hX₀ab x' hx' y' hy', map_mul]
  have hX2 : ∀ x ∈ XY, x * x = 1 := by
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := hXYmem x hx
    apply Subtype.ext
    show (x : G) * x = 1
    rw [← hxx', ← map_mul, hX₀2 x' hx', map_one]
  have hXY₀ : XY ≤ Y₀ := fun y hy => by
    obtain ⟨x, -, hx⟩ := hXYmem y hy
    exact Subgroup.mem_subgroupOf.2 ⟨x, hx⟩
  have hY₀N : Y₀ ≤ Subgroup.normalizer (XY : Set C) := by
    intro g hg
    obtain ⟨s, hs, hsg⟩ := hY₀ g hg
    have hsN := hNX hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hXYmem y hy
      refine Subgroup.mem_subgroupOf.2 ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.1 hsN x).1 hx,
        ?_⟩
      show Φ (s * x * s⁻¹) = (g : G) * y * (g : G)⁻¹
      rw [map_mul, map_mul, map_inv, hsg, hxy]
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hXYmem _ hy
      refine Subgroup.mem_subgroupOf.2 ⟨s⁻¹ * x * s, ?_, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 hsN (s⁻¹ * x * s)).2
          (by rwa [show s * (s⁻¹ * x * s) * s⁻¹ = x by group])
        exact h'
      · show Φ (s⁻¹ * x * s) = (y : G)
        rw [map_mul, map_mul, map_inv, hsg, hxy]
        show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g = y
        group
  obtain ⟨a₀, ha₀X, ha₀⟩ := ha₀
  have hNY₀ : Subgroup.normalizer (XY : Set C) ≤ Y₀ := by
    intro g hg
    have hgN : (g : G) ∈ Subgroup.normalizer ((X₀.map Φ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hhC : h ∈ C := by
          obtain ⟨q, hq, rfl⟩ := hh
          exact hmk q hq
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mem_normalizer_iff.1 hg ⟨h, hhC⟩).1 (Subgroup.mem_subgroupOf.2 hh))
      · intro hh
        have hhC : (g : G) * h * (g : G)⁻¹ ∈ C := by
          obtain ⟨q, hq, hq'⟩ := hh
          rw [← hq']
          exact hmk q hq
        have hhC' : h ∈ C := by
          have h3 := C.mul_mem (C.mul_mem (C.inv_mem g.2) hhC) g.2
          rwa [show (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * g = h by group] at h3
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mem_normalizer_iff.1 hg ⟨h, hhC'⟩).2 (Subgroup.mem_subgroupOf.2 hh))
    exact Subgroup.mem_subgroupOf.2 (hnorm _ (Subgroup.map_le_range Φ X₀)
      ⟨Φ a₀, ⟨a₀, ha₀X, rfl⟩, hP₁ a₀ ha₀⟩ hgN)
  obtain ⟨wa, hwa, wb, hwb, hwa1, hwb1, hwab⟩ := hab
  have hWX : WY ≤ XY := fun y hy => by
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_subgroupOf.1 hy
    exact Subgroup.mem_subgroupOf.2 ⟨w, hW₀X₀ hw, hwy⟩
  have hW1 : WY ≠ ⊥ := by
    intro h
    have hmem : (⟨Φ wa, hmk wa (hW₀X₀ hwa)⟩ : C) ∈ WY := Subgroup.mem_subgroupOf.2 ⟨wa, hwa, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hwa1 (hinj ((congrArg Subtype.val hmem).trans (map_one Φ).symm))
  have htW : tY ∉ WY := by
    intro h
    obtain ⟨w, hw, hwt⟩ := Subgroup.mem_subgroupOf.1 h
    exact htW₀ (hinj hwt ▸ hw)
  have hD₀X : D₀ ⊆ XY := by
    rintro y ⟨a, ha, -, hy⟩
    exact Subgroup.mem_subgroupOf.2 ⟨a, ha, hy.symm⟩
  have hWD₀ : ∀ w ∈ WY, w ≠ 1 → w ∈ D₀ := by
    intro w hw hw1
    obtain ⟨w', hw', hww'⟩ := Subgroup.mem_subgroupOf.1 hw
    have hw'1 : w' ≠ 1 := fun h => hw1 (Subtype.ext (by rw [← hww', h, map_one]; rfl))
    exact ⟨w', hW₀X₀ hw', Or.inr (hW₀ w' hw' hw'1), hww'.symm⟩
  have hWn : ∀ g ∈ Y₀, ∀ w ∈ WY, g * w * g⁻¹ ∈ WY := by
    intro g hg w hw
    obtain ⟨s, hs, hsg⟩ := hY₀ g hg
    obtain ⟨w', hw', hww'⟩ := Subgroup.mem_subgroupOf.1 hw
    refine Subgroup.mem_subgroupOf.2 ⟨s * w' * s⁻¹, hW₀n s hs w' hw', ?_⟩
    show Φ (s * w' * s⁻¹) = (g : G) * w * (g : G)⁻¹
    rw [map_mul, map_mul, map_inv, hsg, hww']
  have hD₀Y : ∀ g : C, ∀ a ∈ D₀, g * a * g⁻¹ ∈ Y₀ → g ∈ Y₀ := by
    rintro g y ⟨a, -, ha, hy⟩ hgy
    have h1 := Subgroup.mem_subgroupOf.1 hgy
    have h2 : (g : G) * Φ a * (g : G)⁻¹ ∈ Φ.range := by
      rw [← hy]
      exact h1
    exact Subgroup.mem_subgroupOf.2 (hblock a ha g h2)
  have : Finite S := Finite.of_injective Φ hinj
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.centralizer {t} : Subgroup S)) := inferInstance
  have hP : Nat.card P = 2 ^ 38 := by
    rw [P.card_eq_multiplicity, hORD, show 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 =
      2 ^ 38 * (3 ^ 5 * 5 ^ 2 * 7) by ring,
      Recog.GoldschmidtArith.factorization_two_pow_mul_odd _ (by decide)]
  obtain ⟨P₀, hP₀def⟩ : ∃ P₀ : Subgroup G,
      P₀ = ((P : Subgroup _).map (Subgroup.centralizer {t}).subtype).map Φ := ⟨_, rfl⟩
  have hP₀card : Nat.card P₀ = 2 ^ 38 := by
    rw [hP₀def, Subgroup.card_map_of_injective hinj,
      Subgroup.card_map_of_injective (Subgroup.centralizer {t}).subtype_injective, hP]
  have hP₀le : P₀ ≤ C ⊓ Φ.range := by
    rw [hP₀def]
    rintro y ⟨s, ⟨s', -, rfl⟩, rfl⟩
    exact ⟨(hCiff _).2 s'.2, ⟨_, rfl⟩⟩
  have hP₀2 : IsPGroup 2 P₀ := hP₀def ▸ (P.isPGroup'.map _).map Φ
  have hP₀max : ∀ Q : Subgroup G, Q ≤ C ⊓ Φ.range → IsPGroup 2 Q → P₀ ≤ Q → Q = P₀ := by
    intro Q hQ hQ2 hPQ
    have hQ'2 : IsPGroup 2 ((Q.comap Φ).subgroupOf (Subgroup.centralizer {t})) :=
      (hQ2.comap_of_injective Φ hinj).comap_of_injective _
        (Subgroup.centralizer {t}).subtype_injective
    have hPQ' : (P : Subgroup _) ≤ (Q.comap Φ).subgroupOf (Subgroup.centralizer {t}) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact hPQ (hP₀def ▸ ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
    have hQP := P.is_maximal' hQ'2 hPQ'
    refine le_antisymm (fun y hy => ?_) hPQ
    obtain ⟨s, hs⟩ := (hQ hy).2
    have hsC : s ∈ Subgroup.centralizer {t} := (hCiff s).1 (by rw [hs]; exact (hQ hy).1)
    have hsQ : (⟨s, hsC⟩ : Subgroup.centralizer {t}) ∈
        (Q.comap Φ).subgroupOf (Subgroup.centralizer {t}) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      show Φ s ∈ Q
      rw [hs]
      exact hy
    rw [hQP] at hsQ
    rw [hP₀def, ← hs]
    exact ⟨s, ⟨_, hsQ, rfl⟩, rfl⟩
  have hX₀P : X₀.subgroupOf (Subgroup.centralizer {t}) ≤ (P : Subgroup _) := by
    refine TwoB.le_sylow_of_le_normalizer
      (TwoB.isPGroup_of_sq (Q := X₀.subgroupOf (Subgroup.centralizer {t})) (z := 1) (mul_one 1)
        fun x hx => Or.inl (Subtype.ext (hX₀2 _ hx))) P fun g _ => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hNX g.2) h
  have hwP : Φ a₀ ∈ P₀ := by
    rw [hP₀def]
    exact ⟨a₀, ⟨⟨a₀, hX₀C ha₀X⟩, hX₀P (Subgroup.mem_subgroupOf.2 ha₀X), rfl⟩, rfl⟩
  have hmaxY : ∀ Q : Subgroup G, Q ≤ C → IsPGroup 2 Q → P₀ ≤ Q → Q = P₀ :=
    fun Q hQY hQ hPQ => Recog.eq_of_le_isPGroup_of_block hP₀le hP₀max hwP
      (hblock a₀ (Or.inl ha₀)) hQY hQ hPQ
  have hP₀C : IsPGroup 2 (P₀.subgroupOf C) := hP₀2.comap_of_injective _ C.subtype_injective
  obtain ⟨T, hT⟩ := hP₀C.exists_le_sylow
  have hTeq : (T : Subgroup C) = P₀.subgroupOf C := by
    have h := hmaxY ((T : Subgroup C).map C.subtype) (Subgroup.map_subtype_le _)
      (T.isPGroup'.map _) (fun y hy => ⟨⟨y, (hP₀le hy).1⟩, hT (Subgroup.mem_subgroupOf.2 hy), rfl⟩)
    refine le_antisymm (fun y hy => ?_) hT
    rw [Subgroup.mem_subgroupOf, ← h]
    exact ⟨y, hy, rfl⟩
  have hTY : (T : Subgroup C) ≤ Y₀ := by
    rw [hTeq]
    intro y hy
    exact Subgroup.mem_subgroupOf.2 (hP₀le (Subgroup.mem_subgroupOf.1 hy)).2
  have hT38 : (Nat.card C).factorization 2 = 38 := by
    have h1 := T.card_eq_multiplicity
    have h2 : Nat.card T = 2 ^ 38 := by
      rw [show Nat.card T = Nat.card (T : Subgroup C) from rfl, hTeq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun y hy => (hP₀le hy).1).toEquiv, hP₀card]
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hpull : ∀ R : Subgroup C, (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ g ∈ Subgroup.centralizer {t}, ∀ s ∈ (R.map C.subtype).comap Φ,
        g * s * g⁻¹ ∈ (R.map C.subtype).comap Φ := by
    intro R hRn g hg s hs
    obtain ⟨r, hr, hrs⟩ := hs
    have hgY : (⟨Φ g, (hCiff g).2 hg⟩ : C) ∈ Y₀ := Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩
    refine ⟨_, hRn _ hgY r hr, ?_⟩
    show Φ g * (r : G) * (Φ g)⁻¹ = Φ (g * s * g⁻¹)
    rw [map_mul, map_mul, map_inv]
    congr 2
  have hQB1Y : ∀ R : Subgroup C, R ≤ XY → (∀ g ∈ Y₀, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers tY ∨ R = WY ∨ R = XY := by
    intro R hRX hRn
    have hRX₀ : (R.map C.subtype).comap Φ ≤ X₀ := by
      intro s hs
      obtain ⟨r, hr, hrs⟩ := hs
      obtain ⟨q, hq, hqr⟩ := hXYmem r (hRX hr)
      have e : q = s := hinj (hqr.trans hrs)
      exact e ▸ hq
    have hRR := TwoB.eq_subgroupOf_map_comap (hRX.trans hXY₀)
    rcases hQB1 _ hRX₀ (hpull R hRn) with h | h | h | h
    · left
      rw [hRR, h, Subgroup.map_bot, Subgroup.bot_subgroupOf]
    · right
      left
      rw [hRR, h, MonoidHom.map_zpowers]
      exact TwoB.zpowers_subgroupOf _ (by rw [← map_mul, ht2, map_one])
    · right
      right
      left
      rw [hRR, h]
    · right
      right
      right
      rw [hRR, h]
  have hQB1cY : ∀ g ∈ Y₀, (∀ x ∈ XY, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * tY) →
      ∀ x ∈ XY, g * x * g⁻¹ = x := by
    intro g hg hgx x hx
    obtain ⟨s, hs, hsg⟩ := hY₀ g hg
    have hs' : ∀ x ∈ X₀, s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x * t := by
      intro x' hx'
      rcases hgx _ (hmemXY x' hx') with h | h
      · left
        apply hinj
        rw [map_mul, map_mul, map_inv, hsg]
        exact congrArg Subtype.val h
      · right
        apply hinj
        rw [map_mul, map_mul, map_inv, hsg, map_mul]
        exact congrArg Subtype.val h
    obtain ⟨x', hx', hxx'⟩ := hXYmem x hx
    apply Subtype.ext
    show (g : G) * x * (g : G)⁻¹ = x
    rw [← hsg, ← hxx', ← map_inv, ← map_mul, ← map_mul, hQB1c s hs hs' x' hx']
  have hC2Y : IsPGroup 2 (Subgroup.centralizer (XY : Set C)) := by
    have hle : (Subgroup.centralizer (XY : Set C)).map C.subtype ≤
        (Subgroup.centralizer (X₀ : Set S)).map Φ := by
      rintro _ ⟨g, hg, rfl⟩
      have ha₀g : (g : G) ∈ Subgroup.centralizer {Φ a₀} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          ((Subgroup.mem_centralizer_iff.1 hg) _ (hmemXY a₀ ha₀X)).symm
      obtain ⟨s, hs⟩ := centralizer_le_of_mem_dZero hCent (hP₁ a₀ ha₀) ha₀g
      refine ⟨s, Subgroup.mem_centralizer_iff.2 fun x hx => hinj ?_, hs⟩
      rw [map_mul, map_mul, hs]
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hg) _ (hmemXY x hx))
    have h1 : IsPGroup 2 ((Subgroup.centralizer (XY : Set C)).map C.subtype) :=
      (hC2.map Φ).to_le hle
    exact h1.of_equiv (Subgroup.equivMapOfInjective _ _ C.subtype_injective).symm
  let e : ↥(Subgroup.centralizer {t}) →* ↥Y₀ :=
    { toFun := fun s => ⟨⟨Φ (s : S), (hCiff s).2 s.2⟩, Subgroup.mem_subgroupOf.2 ⟨s, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact map_one Φ
      map_mul' := fun s s' => by
        apply Subtype.ext
        apply Subtype.ext
        exact map_mul Φ (s : S) (s' : S) }
  have he : Function.Bijective e := by
    refine ⟨fun s s' h => Subtype.ext (hinj (congrArg (fun y : ↥Y₀ => ((y : C) : G)) h)),
      fun y => ?_⟩
    obtain ⟨s, hs, hsy⟩ := hY₀ y y.2
    exact ⟨⟨s, hs⟩, Subtype.ext (Subtype.ext hsy)⟩
  let eY : ↥(Subgroup.centralizer {t}) ≃* ↥Y₀ := MulEquiv.ofBijective e he
  have heY : ∀ s : ↥(Subgroup.centralizer {t}), (((eY s : ↥Y₀) : C) : G) = Φ (s : S) :=
    fun _ => rfl
  let ρY : ↥Y₀ →* O := ρ.comp eY.symm.toMonoidHom
  have hρY : Function.Surjective ρY := fun o => by
    obtain ⟨s, rfl⟩ := hρ o
    exact ⟨eY s, by simp [ρY]⟩
  have hkerY : ∀ g : ↥Y₀, ρY g = 1 ↔ ∀ x ∈ XY, (g : C) * x * (g : C)⁻¹ = x := by
    intro g
    obtain ⟨s, rfl⟩ := eY.surjective g
    rw [show ρY (eY s) = ρ s by simp [ρY], hker]
    constructor
    · intro h x hx
      obtain ⟨x', hx', hxx'⟩ := hXYmem x hx
      apply Subtype.ext
      show (((eY s : ↥Y₀) : C) : G) * x * (((eY s : ↥Y₀) : C) : G)⁻¹ = x
      rw [heY, ← hxx', ← map_inv, ← map_mul, ← map_mul, h x' hx']
    · intro h x hx
      apply hinj
      have h' := congrArg Subtype.val (h _ (hmemXY x hx))
      rw [map_mul, map_mul, map_inv]
      exact h'
  have hwbX : wb ∈ X₀ := hW₀X₀ hwb
  have hwaX : wa ∈ X₀ := hW₀X₀ hwa
  have hwab1 : wa * wb ≠ 1 := fun h => hwab (by
    have h' := hX₀2 wb hwbX
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left h'])
  have hOY := oddCore_centralizer_map_eq_bot_gen hinj (hX₀2 wa hwaX) (hX₀2 wb hwbX) hwa1 hwb1
    hwab (hX₀ab wa hwaX wb hwbX) (hX₀ab wa hwaX t htX₀) (hX₀ab wb hwbX t htX₀)
    (hP₂ wa (hW₀ wa hwa hwa1)).2 (hP₂ wb (hW₀ wb hwb hwb1)).2
    (hP₂ _ (hW₀ _ (W₀.mul_mem hwa hwb) hwab1)).2 hOt
  have key := eq_top_of_package (Y := C) (t := tY) htC htC2 htC1 (Y₀ := Y₀) (X := XY)
    (W := WY) (D₀ := D₀) htX hXab hX2 hXY₀ hY₀N hNY₀ hWX hW1 htW hD₀X hWD₀ hWn hD₀Y T hTY
    hT38 hQB1Y hQB1cY hC2Y ρY hρY hkerY Ω hΩ hΩmin hΩcard hOY hGold
  intro g hg
  have hgY : (⟨g, hg⟩ : C) ∈ Y₀ := key ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hgY

end TwoD

theorem centralizer_le_range_of_twoD
    {G : Type} [Group G] [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem)
    (t₀ : Shat) (X₀ W₀ : Subgroup Shat)
    (hN1 : orderOf t₀ = 2 ∧ rankS t₀ = 2168 ∧ t₀ ∈ X₀ ∧ t₀ ∉ W₀)
    (hN2 : (∀ x ∈ X₀, x * x = 1) ∧ (∀ x ∈ X₀, ∀ y ∈ X₀, x * y = y * x) ∧ W₀ ≤ X₀)
    (hN3 : ∃ a ∈ X₀, IsConj (cV0 : Shat) a)
    (hN4 : ∀ x ∈ W₀, x ≠ 1 → orderOf x = 2 ∧ rankS x = 2048)
    (hN4a : ∃ a ∈ W₀, ∃ b ∈ W₀, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hN4b : ∀ g ∈ Subgroup.centralizer {t₀}, ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀)
    (hN6 : Subgroup.centralizer {t₀} ≤ Subgroup.normalizer (X₀ : Set Shat))
    (hN7 : ∀ R : Subgroup Shat, R ≤ X₀ →
      (∀ g ∈ Subgroup.centralizer {t₀}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers t₀ ∨ R = W₀ ∨ R = X₀)
    (hN8 : ∀ g ∈ Subgroup.centralizer {t₀},
      (∀ x ∈ X₀, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * t₀) → ∀ x ∈ X₀, g * x * g⁻¹ = x)
    (hN9 : IsPGroup 2 (Subgroup.centralizer (X₀ : Set Shat)))
    {O : Type} [Group O] (ρ : ↥(Subgroup.centralizer {t₀}) →* O) (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥(Subgroup.centralizer {t₀}),
      ρ g = 1 ↔ ∀ x ∈ X₀, (g : Shat) * x * (g : Shat)⁻¹ = x)
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hΩcard : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card Ω)
    (hN11 : Nat.card (Subgroup.centralizer {t₀} : Subgroup Shat) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7)
    (hN12 : CFSG.oddCore ↥(Subgroup.centralizer {t₀} : Subgroup Shat) = ⊥)
    (hN13 : ∀ s : Shat, s * s = 1 → ∃ a, IsConj (cV0 : Shat) a ∧ a * s = s * a) :
    Subgroup.centralizer {Φ t₀} ≤ Φ.range := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  obtain ⟨-, -, -, -, hnorm, -⟩ := completion_fusion hd ψ Φ hΦ hDM
  have hΓ2B := centralizer_le_range_of_rankS_eq_2048 hd ψ Φ hΦ hDM hGold
  obtain ⟨ht, -, htX, htW⟩ := hN1
  obtain ⟨hX2, hXab, hWX⟩ := hN2
  have hsq : ∀ a : Shat, orderOf a = 2 → a * a = 1 := fun a ha => by
    rw [← sq, ← ha, pow_orderOf_eq_one]
  refine TwoD.centralizer_le_range_gen hinj (completion_centralizer hd ψ Φ hΦ).2.2
    (fun y hy hdy => hDM ▸ (⟨hdy, hy⟩ : y ∈ conjugatesOf d ∩ (Φ.range : Set G))) hnorm
    (fun a => IsConj (cV0 : Shat) a) (fun a => orderOf a = 2 ∧ rankS a = 2048)
    (fun a ha => ?_) (fun a ha => ⟨hsq a ha.1, hΓ2B a ha.1 ha.2⟩) hN13 (hsq t₀ ht)
    (fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)) X₀ W₀ htX hXab hX2 hWX
    htW hN4 hN3 hN4a hN4b hN6 hN7 hN8 hN9 ρ hρ hker Ω hΩ hΩmin hΩcard hN11 hN12 hGold
  obtain ⟨g, rfl⟩ := isConj_iff.1 ha
  exact ⟨Φ g, ⟨g, rfl⟩, by rw [map_mul, map_mul, map_inv, hΦc]⟩

theorem centralizer_le_range_of_rankS_eq_2168
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem)
    (t₀ : Shat) (X₀ W₀ : Subgroup Shat)
    (hN1 : orderOf t₀ = 2 ∧ rankS t₀ = 2168 ∧ t₀ ∈ X₀ ∧ t₀ ∉ W₀)
    (hN2 : (∀ x ∈ X₀, x * x = 1) ∧ (∀ x ∈ X₀, ∀ y ∈ X₀, x * y = y * x) ∧ W₀ ≤ X₀)
    (hN3 : ∃ a ∈ X₀, IsConj (cV0 : Shat) a)
    (hN4 : ∀ x ∈ W₀, x ≠ 1 → orderOf x = 2 ∧ rankS x = 2048)
    (hN4a : ∃ a ∈ W₀, ∃ b ∈ W₀, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hN4b : ∀ g ∈ Subgroup.centralizer {t₀}, ∀ w ∈ W₀, g * w * g⁻¹ ∈ W₀)
    (hN6 : Subgroup.centralizer {t₀} ≤ Subgroup.normalizer (X₀ : Set Shat))
    (hN7 : ∀ R : Subgroup Shat, R ≤ X₀ →
      (∀ g ∈ Subgroup.centralizer {t₀}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      R = ⊥ ∨ R = Subgroup.zpowers t₀ ∨ R = W₀ ∨ R = X₀)
    (hN8 : ∀ g ∈ Subgroup.centralizer {t₀},
      (∀ x ∈ X₀, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * t₀) → ∀ x ∈ X₀, g * x * g⁻¹ = x)
    (hN9 : IsPGroup 2 (Subgroup.centralizer (X₀ : Set Shat)))
    {O : Type} [Group O] (ρ : ↥(Subgroup.centralizer {t₀}) →* O) (hρ : Function.Surjective ρ)
    (hker : ∀ g : ↥(Subgroup.centralizer {t₀}),
      ρ g = 1 ↔ ∀ x ∈ X₀, (g : Shat) * x * (g : Shat)⁻¹ = x)
    (Ω : Subgroup O) (hΩ : IsSimpleGroup Ω)
    (hΩmin : ∀ R : Subgroup O, R.Normal → R ≠ ⊥ → Ω ≤ R)
    (hΩcard : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card Ω)
    (hN11 : Nat.card (Subgroup.centralizer {t₀} : Subgroup Shat) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7)
    (hN12 : CFSG.oddCore ↥(Subgroup.centralizer {t₀} : Subgroup Shat) = ⊥)
    (hN13 : ∀ s : Shat, s * s = 1 → ∃ a, IsConj (cV0 : Shat) a ∧ a * s = s * a) :
    ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range := by
  intro s hs hrk
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_rankS_eq hN1.1 hs (hN1.2.1.trans hrk.symm))
  rw [map_mul, map_mul, map_inv]
  exact centralizer_conj_le_range (centralizer_le_range_of_twoD hd ψ Φ hΦ hDM hGold t₀ X₀ W₀
    hN1 hN2 hN3 hN4 hN4a hN4b hN6 hN7 hN8 hN9 ρ hρ hker Ω hΩ hΩmin hΩcard hN11 hN12
    hN13) ⟨g, rfl⟩

theorem centralizer_le_range_of_twoD_native
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem) :
    Subgroup.centralizer {Φ t2DS} ≤ Φ.range :=
  centralizer_le_range_of_twoD hd ψ Φ hΦ hDM hGold t2DS T9S A8S t2DS_spec T9S_elemAb
    exists_twoA_mem_T9S rankS_A8S exists_two_mem_A8S
    (conj_mem_A8S_of_le_normalizer centralizer_t2DS_le_normalizer) centralizer_t2DS_le_normalizer
    eq_of_invariant_T9S eq_of_conj_eq_or_mul_t2DS isPGroup_centralizer_T9S
    (rhoPlus centralizer_t2DS_le_normalizer) (rhoPlus_surjective centralizer_t2DS_le_normalizer)
    (rhoPlus_eq_one_iff centralizer_t2DS_le_normalizer) OmegaPlus isSimpleGroup_OmegaPlus
    le_OmegaPlus_of_normal dvd_natCard_OmegaPlus natCard_centralizer_t2DS
    oddCore_centralizer_t2DS exists_twoA_commute

theorem centralizer_le_range_of_rankS_eq_2168_of_gold
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) (hGold : GoldschmidtTheorem)
    {s : Shat} (hs : orderOf s = 2) (hrk : rankS s = 2168) :
    Subgroup.centralizer {Φ s} ≤ Φ.range := by
  obtain ⟨g, rfl⟩ :=
    isConj_iff.1 (isConj_of_rankS_eq t2DS_spec.1 hs (t2DS_spec.2.1.trans hrk.symm))
  rw [map_mul, map_mul, map_inv]
  exact centralizer_conj_le_range
    (centralizer_le_range_of_twoD_native hd ψ Φ hΦ hDM hGold) ⟨g, rfl⟩

end CFSG.Monster.B.GSide
