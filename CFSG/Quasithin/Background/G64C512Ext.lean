module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.G64Linear
public import CFSG.Quasithin.Background.G64Sym
public import CFSG.Quasithin.Background.G6Transvection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem le_normalizer_zpowers {M : Type*} [Group M] {S : Subgroup M} {k : M}
    (h : ∀ s ∈ S, s * k * s⁻¹ ∈ Subgroup.zpowers k) :
    S ≤ Subgroup.normalizer (Subgroup.zpowers k : Set M) := by
  refine Setup.le_normalizer_of_map_conj_le fun s hs => ?_
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
  exact h s hs

theorem mem_normalizer_zpowers_iff {M : Type*} [Group M] [Finite M] {g k : M} :
    g ∈ Subgroup.normalizer (Subgroup.zpowers k : Set M) ↔ g * k * g⁻¹ ∈ Subgroup.zpowers k := by
  constructor
  · intro hg
    exact (Subgroup.mem_normalizer_iff.1 hg k).1 (Subgroup.mem_zpowers k)
  · intro hg
    have hle : (Subgroup.zpowers k).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers k := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem eq_mul_conj {M : Type*} [Group M] {a k : M} (ha : a ^ 2 = 1) (hk : k ^ 3 = 1)
    (hak : a * k * a⁻¹ * k = 1) : k = a * (k * a * k⁻¹) := by
  have ha' : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ha]
  have h1 : a * k * a = k⁻¹ := by
    have := eq_inv_of_mul_eq_one_left hak
    rwa [ha'] at this
  have h2 : k⁻¹ * k⁻¹ = k := by
    rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ]
    exact hk
  calc k = k⁻¹ * k⁻¹ := h2.symm
    _ = (a * k * a) * k⁻¹ := by rw [h1]
    _ = a * (k * a * k⁻¹) := by group

theorem false_of_two_factors {M : Type*} [Group M] [Finite M] {X K K₁ K₂ S : Subgroup M}
    {a t k : M} (hK : K = K₁ ⊔ K₂) (hdis : K₁ ⊓ K₂ = ⊥)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (haK₁ : a ∈ K₁) (ha1 : a ≠ 1)
    (htX : t ∈ X) (ht2 : t ^ 2 = 1) (hX : X = K ⊔ Subgroup.zpowers t)
    (hKX : X ≤ Subgroup.normalizer (K : Set M))
    (ht : K₁.map (MulAut.conj t).toMonoidHom = K₂) (hkK₁ : k ∈ K₁) (hk1 : k ≠ 1)
    (hS : IsSylowTwoOf S X) (hSk : S ≤ Subgroup.normalizer (Subgroup.zpowers k : Set M)) :
    False := by
  have hK₁K : K₁ ≤ K := hK ▸ le_sup_left
  have hK₂K : K₂ ≤ K := hK ▸ le_sup_right
  have hKn : K ≤ Subgroup.normalizer (K₁ : Set M) := by
    rw [hK]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hcomm x hx y hy, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h := hcomm _ hx y hy
      have : x = y * x * y⁻¹ := by
        calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h]
          _ = y * x * y⁻¹ := by group
      rw [this]
      exact hx
  have htK : t ∉ K := by
    intro htK
    have h1 : K₁.map (MulAut.conj t).toMonoidHom = K₁ :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKn htK))
    rw [h1] at ht
    have : a ∈ K₁ ⊓ K₂ := ⟨haK₁, ht ▸ haK₁⟩
    rw [hdis, Subgroup.mem_bot] at this
    exact ha1 this
  have hKXle : K ≤ X := hX ▸ le_sup_left
  have hzt : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set M) := by
    rw [Subgroup.zpowers_le]
    exact hKX htX
  have hmemX : ∀ x ∈ X, x ∈ K ∨ ∃ κ ∈ K, x = t * κ := by
    intro x hx
    rw [hX, sup_comm] at hx
    have hx' : x ∈ ((Subgroup.zpowers t ⊔ K : Subgroup M) : Set M) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzt] at hx'
    obtain ⟨y, hy, κ, hκ, rfl⟩ := hx'
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rcases Int.emod_two_eq_zero_or_one z with h0 | h1
    · left
      have : t ^ z = 1 := by
        rw [(Int.mul_ediv_add_emod z 2).symm, h0, add_zero, zpow_mul]
        norm_cast
        rw [ht2, one_zpow]
      show t ^ z * κ ∈ K
      rw [this, one_mul]
      exact hκ
    · right
      have : t ^ z = t := by
        rw [(Int.mul_ediv_add_emod z 2).symm, h1, zpow_add, zpow_mul]
        norm_cast
        rw [ht2, one_zpow, one_mul, pow_one]
      exact ⟨κ, hκ, by show t ^ z * κ = t * κ; rw [this]⟩
  have hidx : K.relIndex X = 2 := by
    have hdvd : K.relIndex X ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨t, htX, fun b hb => ?_⟩
      rcases hmemX b hb with h | ⟨κ, hκ, rfl⟩
      · exact Or.inr h
      · left
        have hκ' : t * κ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hKX htX) κ).1 hκ
        have ht' : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
        rw [ht'] at hκ'
        rw [show t * κ * t = t * κ * t from rfl]
        exact hκ'
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd (hKXle.trans_eq rfl |>.antisymm ((Subgroup.relIndex_eq_one).1 h1) ▸ htX)
        htK
    · exact h2
  obtain ⟨σ, hσS, hσK⟩ : ∃ σ ∈ S, σ ∉ K := by
    by_contra hcon
    push Not at hcon
    have hmul := Subgroup.relIndex_mul_relIndex S K X hcon hKXle
    apply hS.2.2
    change 2 ∣ S.relIndex X
    rw [← hmul, hidx]
    exact Dvd.intro_left _ rfl
  obtain ⟨κ, hκ, rfl⟩ := (hmemX σ (hS.1 hσS)).resolve_left hσK
  have hk' : (t * κ) * k * (t * κ)⁻¹ ∈ Subgroup.zpowers k :=
    (Subgroup.mem_normalizer_iff.1 (hSk hσS) k).1 (Subgroup.mem_zpowers k)
  have hzk : Subgroup.zpowers k ≤ K₁ := by rw [Subgroup.zpowers_le]; exact hkK₁
  have h1 : (t * κ) * k * (t * κ)⁻¹ ∈ K₁ := hzk hk'
  have h2 : (t * κ) * k * (t * κ)⁻¹ ∈ K₂ := by
    have hκk : κ * k * κ⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.1 (hKn hκ) k).1 hkK₁
    rw [← ht]
    refine ⟨κ * k * κ⁻¹, hκk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have : (t * κ) * k * (t * κ)⁻¹ ∈ K₁ ⊓ K₂ := ⟨h1, h2⟩
  rw [hdis, Subgroup.mem_bot] at this
  apply hk1
  have := congrArg (fun z => (t * κ)⁻¹ * z * (t * κ)) this
  simpa [mul_assoc] using this

theorem card_statedSL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 2 K) = 6 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have htop : StatedSL 2 K = ⊤ := by
    rw [eq_top_iff]
    intro A _
    apply Subgroup.subset_closure
    rcases eq_zero_or_eq_one_of_card_two hK (A : Matrix (Fin 2) (Fin 2) K).det with h0 | h1
    · exact absurd h0 (A.isUnit.map Matrix.detMonoidHom).ne_zero
    · exact h1
  rw [htop, Subgroup.card_top, Matrix.card_GL_field, Fin.prod_univ_two,
    ← Nat.card_eq_fintype_card, hK]
  norm_num

theorem card_sup_le {M : Type*} [CommGroup M] [Finite M] (A B : Subgroup M) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p : A × B => (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2
    p.2.2⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

theorem card_commV_le_four {V : Type*} [CommGroup V] [Finite V] {a k : MulAut V}
    (hak : k = a * (k * a * k⁻¹)) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    Nat.card (commV (Subgroup.zpowers k)) ≤ 4 := by
  set b := k * a * k⁻¹ with hb
  have hle : commV (Subgroup.zpowers k) ≤
      commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b) := by
    have hk : Subgroup.zpowers k ≤ Subgroup.closure {a, b} := by
      rw [Subgroup.zpowers_le, hak]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    refine (G6.commV_mono hk).trans (G6.commV_closure_le ?_)
    intro x hx v
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
    · exact Subgroup.mem_sup_right (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
  have hb2 : Nat.card (commV (Subgroup.zpowers b)) = 2 := by
    rw [hb, G6.card_commV_zpowers_conj, htr]
  calc Nat.card (commV (Subgroup.zpowers k))
      ≤ Nat.card ↥(commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b)) :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card (commV (Subgroup.zpowers a)) * Nat.card (commV (Subgroup.zpowers b)) :=
        card_sup_le _ _
    _ = 4 := by rw [htr, hb2]

theorem le_normalizer_of_binaryNaturalSL {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {n : ℕ} (hX : BinaryNaturalSL X ⊤ ⊥ n 1)
    (hn : 2 ≤ n) {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X) {k : MulAut V} (hkX : k ∈ X)
    (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (hkV : Nat.card (commV (Subgroup.zpowers k)) ≤ 4)
    (hSk : S ≤ Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V))) :
    X ≤ Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V)) := by
  have hXtop := BinaryNaturalSL.eq_top hX
  have hcard := BinaryNaturalSL.card_eq hX
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    have hn2 : n = 2 := by omega
    subst hn2
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hX
    have hX6 : Nat.card X = 6 := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL_two (by simpa using hK)]
    have hk3' : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    have hzle : Subgroup.zpowers k ≤ X := by rw [Subgroup.zpowers_le]; exact hkX
    have hidx : ((Subgroup.zpowers k).subgroupOf X).index = 2 := by
      have hmul := Subgroup.card_mul_index ((Subgroup.zpowers k).subgroupOf X)
      rw [hX6, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv,
        Nat.card_zpowers, hk3'] at hmul
      omega
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hzle).1 hnorm
  ·
    exfalso
    have hV8 : 8 ≤ Nat.card V := by
      rw [hcard]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have hC : fixV (Subgroup.zpowers k) ≠ ⊥ := by
      intro hC
      have htop := commV_sup_fixV_of_pow_three hV hk3
      rw [hC, sup_bot_eq] at htop
      have : Nat.card (commV (Subgroup.zpowers k)) = Nat.card V := by
        rw [htop, Subgroup.card_top]
      omega
    rw [hXtop] at hS
    exact false_of_sylow_normalizes hV hS hk3 hk1 hSk hC

theorem normalizer_le_of_permModel {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}
    {n : ℕ}
    (hn5 : 5 ≤ n) (hn8 : n ≤ 8) {Z : Subgroup (G6.PermMod n)}
    (hZ : Z ≤ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) (hfaith : (permModel n Z).Faithful)
    (hX : (permModel n Z).Realizes X ⊤ ⊥) {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X)
    {a k : MulAut V} (haX : a ∈ X) (hkX : k ∈ X) (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1)
    (hak : k = a * (k * a * k⁻¹)) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hSk : S ≤ Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V))) :
    X ⊓ Subgroup.normalizer (S : Set (MulAut V)) ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V)) := by
  classical
  obtain ⟨π, hπ⟩ := hX
  have hinj : Function.Injective π := FFModel.RealizesVia.injective_of_faithful hfaith hπ
  set θ : ↥X ≃* Equiv.Perm (Fin n) := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm with hθ
  have hbX : k * a * k⁻¹ ∈ X := X.mul_mem (X.mul_mem hkX haX) (X.inv_mem hkX)
  have hbtr : Nat.card (commV (Subgroup.zpowers (k * a * k⁻¹))) = 2 := by
    rw [G6.card_commV_zpowers_conj, htr]
  have hsa := isSwap_of_realization hn5 hZ hπ hinj haX htr
  have hsb := isSwap_of_realization hn5 hZ hπ hinj hbX hbtr
  change (θ ⟨a, haX⟩).IsSwap at hsa
  change (θ ⟨k * a * k⁻¹, hbX⟩).IsSwap at hsb
  set c := θ ⟨k, hkX⟩ with hc
  have hck : (⟨k, hkX⟩ : X) = ⟨a, haX⟩ * ⟨k * a * k⁻¹, hbX⟩ := Subtype.ext hak
  have hcab : c = θ ⟨a, haX⟩ * θ ⟨k * a * k⁻¹, hbX⟩ := by rw [hc, hck, map_mul]
  have hc1 : c ≠ 1 := by
    intro h
    apply hk1
    have : (⟨k, hkX⟩ : X) = 1 := θ.injective (by rw [← hc, h, map_one])
    exact congrArg Subtype.val this
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← map_pow]
    have : (⟨k, hkX⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  have hcs : (c.support).card ≤ 4 := by
    obtain ⟨x, y, hxy, hx⟩ := hsa
    obtain ⟨z, w, hzw, hz⟩ := hsb
    rw [hcab, hx, hz]
    calc (Equiv.swap x y * Equiv.swap z w).support.card
        ≤ ((Equiv.swap x y).support ⊔ (Equiv.swap z w).support).card :=
          Finset.card_le_card (Equiv.Perm.support_mul_le _ _)
      _ ≤ (Equiv.swap x y).support.card + (Equiv.swap z w).support.card :=
          Finset.card_union_le _ _
      _ = 4 := by rw [Equiv.Perm.card_support_swap hxy, Equiv.Perm.card_support_swap hzw]
  have hc3c : c.IsThreeCycle := isThreeCycle_of_pow_three hc1 hc3 hcs
  set S' : Subgroup (Equiv.Perm (Fin n)) := (S.subgroupOf X).map θ.toMonoidHom with hS'
  have hS'p : IsPGroup 2 S' := by
    refine IsPGroup.map ?_ θ.toMonoidHom
    exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hS'i : ¬ 2 ∣ S'.index := by
    have hidx : S'.index = (S.subgroupOf X).index := Subgroup.index_map_equiv _ θ
    rw [hidx]
    exact hS.2.2
  have hmemS' : ∀ x : X, θ x ∈ S' ↔ (x : MulAut V) ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := θ.injective hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hS'k : S' ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (Equiv.Perm (Fin n))) := by
    refine le_normalizer_zpowers fun σ hσ => ?_
    obtain ⟨s, hs, rfl⟩ := hσ
    have h1 : (s : MulAut V) * k * (s : MulAut V)⁻¹ ∈ Subgroup.zpowers k :=
      (Subgroup.mem_normalizer_iff.1 (hSk hs) k).1 (Subgroup.mem_zpowers k)
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨z, ?_⟩
    have h2 : (⟨k, hkX⟩ : X) ^ z = s * ⟨k, hkX⟩ * s⁻¹ := Subtype.ext (by simpa using hz)
    rw [hc, ← map_zpow, h2]
    simp [map_mul]
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with h | h | h | h
  · exact absurd (false_of_three_cycle (Or.inl h) hS'p hS'i hc3c hS'k) not_false
  · exact absurd (false_of_three_cycle (Or.inr (Or.inl h)) hS'p hS'i hc3c hS'k) not_false
  · subst h
    have hN := normalizer_le_of_three_cycle hS'p hS'i hc3c hS'k
    rintro g ⟨hgX, hgS⟩
    have hθg : θ ⟨g, hgX⟩ ∈ Subgroup.normalizer (S' : Set (Equiv.Perm (Fin 7))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro σ
      obtain ⟨x, rfl⟩ := θ.surjective σ
      rw [← map_inv, ← map_mul, ← map_mul, hmemS', hmemS']
      exact (Subgroup.mem_normalizer_iff.1 hgS x)
    have h1 := hN hθg
    rw [mem_normalizer_zpowers_iff] at h1
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 h1
    rw [mem_normalizer_zpowers_iff]
    refine Subgroup.mem_zpowers_iff.2 ⟨z, ?_⟩
    have h2 : (⟨k, hkX⟩ : X) ^ z = ⟨g, hgX⟩ * ⟨k, hkX⟩ * ⟨g, hgX⟩⁻¹ := by
      apply θ.injective
      rw [map_zpow, ← hc, hz, map_mul, map_mul, map_inv]
    have := congrArg Subtype.val h2
    simpa using this
  · exact absurd (false_of_three_cycle (Or.inr (Or.inr h)) hS'p hS'i hc3c hS'k) not_false

theorem sup_le_normalizer_left {M : Type*} [Group M] {K₁ K₂ : Subgroup M}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set M) := by
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hcomm x hx y hy, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h := hcomm _ hx y hy
    have : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h]
        _ = y * x * y⁻¹ := by group
    rw [this]
    exact hx

theorem normalizer_sylow_le_of_conclusion {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {a : MulAut V} (hC : Conclusion X a)
    (haX : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) {S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X) {k : MulAut V} (hkX : k ∈ X) (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1)
    (hak : a * k * a⁻¹ * k = 1)
    (hSk : S ≤ Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V))) :
    X ⊓ Subgroup.normalizer (S : Set (MulAut V)) ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V)) := by
  obtain ⟨s, Ks, hs2, hKs, hindep, hcomm, hcommV, -, ⟨hs0, ha0⟩, -, -, htype, h3, -⟩ := hC
  have hk := eq_mul_conj ha2 hk3 hak
  set K := conjClosure (Subgroup.zpowers a) X with hKdef
  have hkK : k ∈ K := by
    rw [hk]
    exact K.mul_mem (le_conjClosure _ _ (Subgroup.mem_zpowers a))
      (mem_conjClosure hkX (Subgroup.mem_zpowers a))
  rcases h3 with ⟨rfl, hXK⟩ | ⟨rfl, -, t, htX, -, ht2, hXt, hswap⟩
  ·
    have hK1 : Ks 0 = X := by
      rw [hXK, ← hKs, iSup_unique]
      rfl
    have hV1 : commV (Ks 0) = ⊤ := by
      rw [← hcommV, iSup_unique]
      rfl
    have ht := htype 0
    rw [hV1, hK1] at ht
    rcases ht with ⟨n, hn2, -, hnat⟩ | ⟨n, hn5, hn8, hsym⟩ | ⟨n, hn, hcore⟩
    · exact inf_le_left.trans (le_normalizer_of_binaryNaturalSL hV hnat hn2 hS hkX hk1 hk3
        (card_commV_le_four hk htr) hSk)
    · exact normalizer_le_of_permModel hn5 hn8 le_rfl (symDn_faithful hn5) hsym hS haX hkX hk1 hk3
        hk htr hSk
    · have hn5 : 5 ≤ n := by omega
      have hn8 : n ≤ 8 := by omega
      exact normalizer_le_of_permModel hn5 hn8 bot_le (symCore_faithful (by omega)) hcore hS haX
        hkX hk1 hk3 hk htr hSk
  ·
    exfalso
    have hK2 : K = Ks 0 ⊔ Ks 1 := by rw [← hKs, G6.iSup_fin_two]
    have hdis : Ks 0 ⊓ Ks 1 = ⊥ :=
      disjoint_iff.1 (hindep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
    have hcomm01 : ∀ x ∈ Ks 0, ∀ y ∈ Ks 1, x * y = y * x := hcomm 0 1 (by decide)
    have ha0' : a ∈ Ks 0 := ha0
    have hKn : K ≤ Subgroup.normalizer (Ks 0 : Set (MulAut V)) :=
      hK2 ▸ sup_le_normalizer_left hcomm01
    have hkK₁ : k ∈ Ks 0 := by
      rw [hk]
      refine (Ks 0).mul_mem ha0' ?_
      exact (Subgroup.mem_normalizer_iff.1 (hKn hkK) a).1 ha0'
    exact false_of_two_factors hK2 hdis hcomm01 ha0' ha1 htX ht2 hXt
      (le_normalizer_conjClosure (Subgroup.zpowers a) X) (hswap 0 1 (by decide)) hkK₁ hk1 hS hSk

end CFSG.Quasithin.G64
