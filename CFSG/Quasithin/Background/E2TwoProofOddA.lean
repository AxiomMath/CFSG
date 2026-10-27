module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Goldschmidt.Steps.G3bL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6
open scoped MatrixGroups

namespace E2P

section Four

variable {G : Type} [Group G] [Finite G]

theorem fixes_of_fixes_four {V : Subgroup G} (hV : IsKleinFour ↥V) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hg3 : g ^ 3 = 1) {a : G} (ha : a ∈ V)
    (ha1 : a ≠ 1) (hga : g * a * g⁻¹ = a) : ∀ x ∈ V, g * x * g⁻¹ = x := by
  classical
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥V)
    rw [hV.exponent_two, pow_two] at h
    exact congrArg Subtype.val h
  have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    calc x * y = (x * y)⁻¹ := (hinv _ (V.mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv x hx, hinv y hy]
  have hmem : ∀ x ∈ V, g * x * g⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hcard : Nat.card ↥V = 4 := hV.card_four
  obtain ⟨b, hbV, hb1, hba⟩ : ∃ b ∈ V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hle : (V : Set G) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    have h2 : Nat.card ↥V ≤ 2 := by
      have := Set.ncard_le_ncard hle (Set.toFinite _)
      rw [Set.ncard_pair (Ne.symm ha1)] at this
      rwa [← Nat.card_coe_set_eq] at this
    omega
  have hV4 : ∀ x ∈ V, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨hx1, hxa, hxb, hxab⟩ := hcon
    have hab1 : a * b ≠ 1 := fun h => hba (by
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, inv_eq_of_mul_eq_one_right (hsq a ha)])
    have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
    have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
    have hsub : ({1, a, b, a * b, x} : Set G) ⊆ V := by
      intro y hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact ha
      · exact hbV
      · exact V.mul_mem ha hbV
      · exact hx
    have h5 : ({1, a, b, a * b, x} : Set G).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
        Set.ncard_pair (Ne.symm hxab)]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨habb.symm, Ne.symm hxb⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hba.symm, haba.symm, Ne.symm hxa⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨ha1.symm, hb1.symm, hab1.symm, Ne.symm hx1⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h5, ← Nat.card_coe_set_eq] at this
    change 5 ≤ Nat.card ↥V at this
    omega
  have hgb : g * b * g⁻¹ = b := by
    rcases hV4 _ (hmem b hbV) with h | h | h | h
    · exfalso
      apply hb1
      have e : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [e, h]
      group
    · exfalso
      apply hba
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h, hga]
        _ = a := by group
    · exact h
    · exfalso
      have h2 : g * (a * b) * g⁻¹ = b := by
        calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = a * (a * b) := by rw [hga, h]
          _ = b := by rw [← mul_assoc, hsq a ha, one_mul]
      have h3 : b = a * b := by
        calc b = g ^ 3 * b * (g ^ 3)⁻¹ := by rw [hg3]; group
          _ = g * (g * (g * b * g⁻¹) * g⁻¹) * g⁻¹ := by
            rw [pow_succ, pow_succ, pow_one]
            group
          _ = g * (g * (a * b) * g⁻¹) * g⁻¹ := by rw [h]
          _ = g * b * g⁻¹ := by rw [h2]
          _ = a * b := h
      apply ha1
      calc a = a * b * b⁻¹ := by group
        _ = 1 := by rw [← h3, mul_inv_cancel]
  intro x hx
  rcases hV4 x hx with rfl | rfl | rfl | rfl
  · group
  · exact hga
  · exact hgb
  · calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = a * b := by rw [hga, hgb]

end Four

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem exists_psl2_galois_equiv {p f : ℕ} [Fact p.Prime] {L : Type} [Group L]
    (h : IsPSL 2 p f L) :
    0 < f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (L ≃* GH74.GLS.IVK.L2 F) ∧ Nonempty (L ≃* PSL(2, GaloisField p f)) := by
  obtain ⟨⟨-, hf, -⟩, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hf0 : 0 < f := hf
  refine ⟨hf0, F, hF, hFin, hcard, ⟨e⟩, ⟨e.trans ?_⟩⟩
  exact (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F p f hf0 hcard) (Fin 2))

namespace ASHyp

variable (hX : ASHyp K T M)
include hX

theorem center_eq_bot : Subgroup.center ↥K = ⊥ := by
  have := hX.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX.nonab
    have hb : b ∈ Subgroup.center ↥K := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem exists_central_inf : ∃ a ∈ T ⊓ K, a ≠ 1 ∧ ∀ t ∈ T, t * a = a * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := hX.minPar.isSylow.2.1
  have hnil : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hn : ((T ⊓ K).subgroupOf T).Normal := by
    refine ⟨fun x hx t => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hX.le_normalizer_inf t.2) _).mp hx
  have hne : (T ⊓ K).subgroupOf T ≠ ⊥ := by
    intro h
    apply hX.inf_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥T) ∈ (T ⊓ K).subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxS, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  refine ⟨(x : X), Subgroup.mem_subgroupOf.mp hxS, fun h1 => hx1 ?_, fun t ht => ?_⟩
  · ext
    simpa using h1
  · have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem le_normalizer_centralizer {a : X} (ha : ∀ t ∈ T, t * a = a * t) :
    T ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer {a} : Subgroup X) : Set X) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK := Subgroup.mem_normalizer_iff.mp (hX.mem_normalizer_K t) x
  have hta : t * a * t⁻¹ = a := by rw [ha t ht, mul_inv_cancel_right]
  have hta' : t⁻¹ * a * t = a := by
    calc t⁻¹ * a * t = t⁻¹ * (t * a * t⁻¹) * t := by rw [hta]
      _ = a := by group
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxK, hxa⟩
    refine ⟨hK.mp hxK, ?_⟩
    calc t * x * t⁻¹ * a = t * x * (t⁻¹ * a * t) * t⁻¹ := by group
      _ = t * (x * a) * t⁻¹ := by rw [hta']; group
      _ = t * (a * x) * t⁻¹ := by rw [hxa]
      _ = (t * a * t⁻¹) * (t * x * t⁻¹) := by group
      _ = a * (t * x * t⁻¹) := by rw [hta]
  · rintro ⟨hxK, hxa⟩
    refine ⟨hK.mpr hxK, ?_⟩
    calc x * a = t⁻¹ * ((t * x * t⁻¹) * (t * a * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * x * t⁻¹) * a) * t := by rw [hta]
      _ = t⁻¹ * (a * (t * x * t⁻¹)) * t := by rw [hxa]
      _ = (t⁻¹ * a * t) * x := by group
      _ = a * x := by rw [hta']

end ASHyp

theorem ASHyp.false_of_psl2_three_mod_eight
    (hX : ASHyp K T M) {p f : ℕ}
    [Fact p.Prime] (hp : Odd p) (h : IsPSL 2 p f ↥K) (h11 : 11 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) : False := by
  obtain ⟨hf, F, hF, hFin, hcard, ⟨e₀⟩, ⟨e⟩⟩ := exists_psl2_galois_equiv h
  have hS := hX.isSylow_inf
  set S : Sylow 2 ↥K := toSylow2 hS with hSdef
  have hSc : (S : Subgroup ↥K) = (T ⊓ K).subgroupOf K := toSylow2_coe hS
  have hK4 := Goldschmidt.G3b.sylow_isKleinFour_of_mulEquiv e hp hf h8 S
  have hC := Goldschmidt.G3b.centralizer_sylow_of_mulEquiv e hp hf h8 S
  obtain ⟨eA⟩ := Goldschmidt.G3b.normalizer_sylow_mulEquiv_of_mulEquiv e hp hf h8 S
  have h12 : Nat.card (Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K)) = 12 := by
    rw [Nat.card_congr eA.toEquiv, Goldschmidt.G3b.card_alternatingGroup_four']
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h12]; norm_num)
  have hg3 : (g : ↥K) ^ 3 = 1 := by
    rw [← Subgroup.orderOf_coe] at hg
    rw [← hg]
    exact pow_orderOf_eq_one _
  obtain ⟨a, haS, ha1, haT⟩ := hX.exists_central_inf
  set a' : ↥K := ⟨a, haS.2⟩ with ha'
  have ha'S : a' ∈ (S : Subgroup ↥K) := by rw [hSc]; exact haS
  have ha'1 : a' ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
  have hS2 : ∀ x ∈ (S : Subgroup ↥K), x * x = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥(S : Subgroup ↥K))
    rw [hK4.exponent_two, pow_two] at h
    exact congrArg Subtype.val h
  have ha'2 : orderOf a' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hS2 a' ha'S) ha'1
  have hmove : g.1 * a' * g.1⁻¹ ≠ a' := by
    intro hfix
    have hcen := fixes_of_fixes_four hK4 g.2 hg3 ha'S ha'1 hfix
    have hgC : g.1 ∈ Subgroup.centralizer ((S : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hcen x hx
      calc x * g.1 = (g.1 * x * g.1⁻¹) * g.1 := by rw [this]
        _ = g.1 * x := by group
    rw [hC] at hgC
    have hg2 : g.1 * g.1 = 1 := hS2 _ hgC
    have hdvd : orderOf g.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    rw [Subgroup.orderOf_coe, hg] at hdvd
    omega
  set Y₁ := K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) with hY₁
  set Y₂ := K ⊓ Subgroup.centralizer ({a} : Set X) with hY₂
  have hSY₂ : T ⊓ K ≤ Y₂ := by
    intro x hx
    refine ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxS : (⟨x, hx.2⟩ : ↥K) ∈ (S : Subgroup ↥K) := by rw [hSc]; exact hx
    have hinv : ∀ y ∈ (S : Subgroup ↥K), y⁻¹ = y := fun y hy =>
      inv_eq_of_mul_eq_one_right (hS2 y hy)
    have h : (⟨x, hx.2⟩ : ↥K) * a' = a' * ⟨x, hx.2⟩ := by
      calc (⟨x, hx.2⟩ : ↥K) * a' = (⟨x, hx.2⟩ * a')⁻¹ :=
            (hinv _ ((S : Subgroup ↥K).mul_mem hxS ha'S)).symm
        _ = a'⁻¹ * (⟨x, hx.2⟩ : ↥K)⁻¹ := mul_inv_rev _ _
        _ = a' * ⟨x, hx.2⟩ := by rw [hinv _ ha'S, hinv _ hxS]
    exact congrArg Subtype.val h
  have hFL : GH74.GLS.IVK.L2Field F := by
    refine ⟨?_, ?_⟩
    · rw [hcard]
      exact hp.pow
    · rw [hcard]
      omega
  have hcoat := GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hFL (by rw [hcard]; exact h11)
    e₀ ha'2
  have hY₂map : (Subgroup.centralizer ({a'} : Set ↥K)).map K.subtype = Y₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hy
      exact congrArg Subtype.val this
    · rintro ⟨hxK, hxa⟩
      refine ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxa)
  have hY₂ne : Y₂ ≠ K := by
    intro hY
    apply hcoat.1
    rw [eq_top_iff]
    intro y _
    have : (y : X) ∈ Y₂ := by rw [hY]; exact y.2
    rw [← hY₂map] at this
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← Subtype.ext hzy]
  have hgY₁ : (g.1 : X) ∈ Y₁ := by
    refine ⟨g.1.2, ?_⟩
    have h1 := (mem_normalizer_map_iff_of_injective (f := K.subtype) K.subtype_injective).mpr
      (show g.1 ∈ Subgroup.normalizer (((T ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K) from
        hSc ▸ g.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
  have hgen : K ≤ Y₁ ⊔ Y₂ := by
    have hle : Subgroup.centralizer ({a'} : Set ↥K) ≤ (Y₁ ⊔ Y₂).subgroupOf K := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right (hY₂map ▸ ⟨y, hy, rfl⟩)
    have hne : (Y₁ ⊔ Y₂).subgroupOf K ≠ Subgroup.centralizer ({a'} : Set ↥K) := by
      intro heq
      have hg' : g.1 ∈ (Y₁ ⊔ Y₂).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hgY₁)
      rw [heq, Subgroup.mem_centralizer_singleton_iff] at hg'
      apply hmove
      rw [hg', mul_inv_cancel_right]
    rcases hcoat.le_iff.mp hle with h1 | h1
    · intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ (Y₁ ⊔ Y₂).subgroupOf K := by rw [h1]; trivial
      exact this
    · exact absurd h1 hne
  exact hX.false_of_pair inf_le_left inf_le_left
    (le_inf inf_le_right Subgroup.le_normalizer) hSY₂ hX.normalizer_ne hY₂ne
    hX.le_normalizer_normalizer (hX.le_normalizer_centralizer haT) hgen

end E2P

end CFSG.Quasithin
