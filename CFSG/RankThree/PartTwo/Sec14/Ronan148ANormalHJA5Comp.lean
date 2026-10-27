module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AConjComp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JGen
import CFSG.RankThree.PartTwo.Sec14.Ronan148AInnerCenter
import CFSG.RankThree.PartTwo.Sec14.Ronan148VA5Inner
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrderTools
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec5.Items52
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

private def a5c1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5c2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5c3 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a5t : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private abbrev a5Kl (x : alternatingGroup (Fin 5)) : Prop :=
  x = 1 ∨ x = a5c1 ∨ x = a5c2 ∨ x = a5c3

private theorem a5Kl_mul :
    ∀ x y : alternatingGroup (Fin 5), a5Kl x → a5Kl y → a5Kl (x * y) := by
  decide +kernel

private theorem a5Kl_inv : ∀ x : alternatingGroup (Fin 5), a5Kl x → a5Kl x⁻¹ := by
  decide +kernel

private theorem a5Kl_conj :
    ∀ m : alternatingGroup (Fin 5), a5Kl m → a5Kl (a5t * m * a5t⁻¹) := by
  decide +kernel

private theorem a5Kl_sq : ∀ m : alternatingGroup (Fin 5), a5Kl m → m ^ 2 = 1 := by
  decide +kernel

private theorem a5_conj_t :
    ∀ g : alternatingGroup (Fin 5), g ^ 3 = 1 → g ≠ 1 →
      ∃ s : alternatingGroup (Fin 5), s * a5t * s⁻¹ = g := by
  decide +kernel

private theorem a5c1_ne_one : a5c1 ≠ 1 := by decide +kernel

private theorem a5t_pow_three : a5t ^ 3 = 1 := by decide +kernel

private theorem a5t_ne_one : a5t ≠ 1 := by decide +kernel

private def a5KlSub : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | a5Kl x}
  mul_mem' := fun {a b} ha hb => a5Kl_mul a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {x} hx => a5Kl_inv x hx

private theorem a5KlSub_isPGroup : IsPGroup 2 a5KlSub := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact a5Kl_sq _ g.2

theorem exists_two_subgroup_of_a5 {X : Type} [Group X] {K : Subgroup X}
    (φ : ↥K ≃* alternatingGroup (Fin 5)) {j : X} (hjK : j ∈ K) (hj3 : j ^ 3 = 1)
    (hj1 : j ≠ 1) :
    ∃ T : Subgroup X, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ j ∈ Subgroup.normalizer (T : Set X) := by
  set g := φ ⟨j, hjK⟩ with hg
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← map_pow]
    have : (⟨j, hjK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hj3)
    rw [this, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply hj1
    have : (⟨j, hjK⟩ : ↥K) = 1 := φ.injective (by rw [← hg, h, map_one])
    simpa using congrArg Subtype.val this
  obtain ⟨s, hs⟩ := a5_conj_t g hg3 hg1
  set ψ : alternatingGroup (Fin 5) →* X := K.subtype.comp φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := K.subtype_injective.comp φ.symm.injective
  set T := a5KlSub.map (ψ.comp (MulAut.conj s).toMonoidHom) with hT
  have hφg : φ.symm g = ⟨j, hjK⟩ := by rw [hg, MulEquiv.symm_apply_apply]
  have hψj : ∀ y, j * ψ y * j⁻¹ = ψ (g * y * g⁻¹) := by
    intro y
    simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, hφg, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  have hfwd : ∀ x ∈ T, j * x * j⁻¹ ∈ T := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨a5t * m * a5t⁻¹, a5Kl_conj m hm, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [hψj, ← hs]
    congr 1
    group
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, -, rfl⟩
    exact (φ.symm (s * m * s⁻¹)).2
  · intro hbot
    have hmem : ψ (s * a5c1 * s⁻¹) ∈ T := ⟨a5c1, Or.inr (Or.inl rfl), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply a5c1_ne_one
    have h2 : s * a5c1 * s⁻¹ = 1 := hψinj (by rw [hmem, map_one])
    calc a5c1 = s⁻¹ * (s * a5c1 * s⁻¹) * s := by group
      _ = 1 := by rw [h2]; group
  · exact IsPGroup.map a5KlSub_isPGroup _
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd x, fun hx => ?_⟩
    have h1 := hfwd _ (hfwd _ hx)
    have hjjj : j * j * j = 1 := by rw [← pow_three', hj3]
    have e : j * (j * (j * x * j⁻¹) * j⁻¹) * j⁻¹ = x := by
      calc j * (j * (j * x * j⁻¹) * j⁻¹) * j⁻¹ = (j * j * j) * x * (j * j * j)⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
        _ = x := by rw [hjjj, one_mul, inv_one, mul_one]
    rwa [e] at h1

theorem not_mem_centralizer_of_a5 {X : Type} [Group X] {K : Subgroup X}
    (φ : ↥K ≃* alternatingGroup (Fin 5)) {x : X} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    x ∉ Subgroup.centralizer (K : Set X) := by
  intro hC
  have hz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC g g.2)
  rw [Ronan148V.inner_a5_center_eq_bot φ, Subgroup.mem_bot] at hz
  exact hx1 (congrArg Subtype.val hz)

theorem exists_three_of_a5 {X : Type} [Group X] {K : Subgroup X}
    (φ : ↥K ≃* alternatingGroup (Fin 5)) :
    ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 ∧ k ∉ Subgroup.centralizer (K : Set X) := by
  set k : X := ((φ.symm a5t : ↥K) : X) with hk
  have hk1 : k ≠ 1 := by
    intro h
    apply a5t_ne_one
    have : φ.symm a5t = 1 := Subtype.ext h
    simpa using congrArg φ this
  refine ⟨k, (φ.symm a5t).2, hk1, ?_, not_mem_centralizer_of_a5 φ (φ.symm a5t).2 hk1⟩
  have : (φ.symm a5t) ^ 3 = 1 := by rw [← map_pow, a5t_pow_three, map_one]
  simpa using congrArg Subtype.val this

theorem eq_one_of_mem_zpowers_centralizer {X : Type} [Group X] {u : X} {K : Subgroup X}
    (hu3 : u ^ 3 = 1) (huZ : u ∉ Subgroup.centralizer (K : Set X)) {w : X}
    (hw : w ∈ Subgroup.zpowers u) (hwC : w ∈ Subgroup.centralizer (K : Set X)) : w = 1 := by
  by_contra hw1
  have hu1 : u ≠ 1 := fun h1 => huZ (h1 ▸ Subgroup.one_mem _)
  have hcard : Nat.card (Subgroup.zpowers u) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
  have : Finite (Subgroup.zpowers u) := Nat.finite_of_card_ne_zero (by omega)
  have heq := Ronan148J.zpowers_eq_of_card_three hcard hw hw1
  exact huZ ((Subgroup.zpowers_le.mpr hwC) (heq ▸ Subgroup.mem_zpowers u))

theorem isElemAbelian_zpowers_sup {X : Type*} [Group X] {u₁ u₂ : X} (h12 : u₁ * u₂ = u₂ * u₁)
    (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ∧
      ∀ x ∈ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂,
        ∃ a ∈ Subgroup.zpowers u₁, ∃ b ∈ Subgroup.zpowers u₂, x = a * b := by
  have hUV : ∀ a ∈ Subgroup.zpowers u₁, ∀ b ∈ Subgroup.zpowers u₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute u₁ u₂ from h12).zpow_zpow k l).eq
  have hmem : ∀ x ∈ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂,
      ∃ a ∈ Subgroup.zpowers u₁, ∃ b ∈ Subgroup.zpowers u₂, x = a * b := by
    intro x hx
    rw [← Ronan148J.commProdHom_range hUV] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨a, a.2, b, b.2, Ronan148J.commProdHom_apply hUV _⟩
  have hpow3 : ∀ {u : X}, u ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers u, a ^ 3 = 1 := by
    intro u hu a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hmem⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x.1 x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y.1 y.2
    change (x : X) * y = y * x
    rw [hx, hy]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    obtain ⟨l', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have h12' : Commute u₁ u₂ := h12
    have c1 : Commute (u₁ ^ k * u₂ ^ l) (u₁ ^ k' * u₂ ^ l') :=
      ((Commute.zpow_zpow_self u₁ k k').mul_right (h12'.zpow_zpow k l')).mul_left
        ((h12'.symm.zpow_zpow l k').mul_right (Commute.zpow_zpow_self u₂ l l'))
    exact c1.eq
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    rw [Commute.mul_pow (hUV a ha b hb) 3, hpow3 hu₁3 a ha, hpow3 hu₂3 b hb, one_mul]

theorem mem_centralizer_sup {X : Type*} [Group X] {H₁ H₂ : Subgroup X} {x : X}
    (h₁ : x ∈ Subgroup.centralizer (H₁ : Set X)) (h₂ : x ∈ Subgroup.centralizer (H₂ : Set X)) :
    x ∈ Subgroup.centralizer ((H₁ ⊔ H₂ : Subgroup X) : Set X) := by
  have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({x} : Set X) := by
    refine sup_le (fun h hh => ?_) (fun h hh => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp h₁ h hh
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp h₂ h hh
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

variable {G : Type} [Group G] [Finite G]

theorem false_of_four_commuting148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal]
    {K₁ K₂ K₃ K₄ T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h₁₂ : K₂ ≤ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (h₁₃ : K₃ ≤ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (h₁₄ : K₄ ≤ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (h₂₃ : K₃ ≤ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (h₂₄ : K₄ ≤ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (h₃₄ : K₄ ≤ Subgroup.centralizer (K₃ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {u₁ u₂ u₃ u₄ : ↥(Y ⊔ A) ⧸ ker148 A Y} (hu₁ : u₁ ∈ K₁) (hu₂ : u₂ ∈ K₂) (hu₃ : u₃ ∈ K₃)
    (hu₄ : u₄ ∈ K₄) (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1) (hu₃3 : u₃ ^ 3 = 1)
    (hu₄3 : u₄ ^ 3 = 1)
    (hu₁Z : u₁ ∉ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hu₂Z : u₂ ∉ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hu₃Z : u₃ ∉ Subgroup.centralizer (K₃ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hu₄Z : u₄ ∉ Subgroup.centralizer (K₄ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTK : T ≤ K₁)
    (hu₁T : u₁ ∈ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have hsymm : ∀ {U V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)},
      U ≤ Subgroup.centralizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      V ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun hUV v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hUV hu) v hv).symm
  have hu₁2 : u₁ ∈ Subgroup.centralizer (K₂ : Set _) := hsymm h₁₂ hu₁
  have hu₂1 : u₂ ∈ Subgroup.centralizer (K₁ : Set _) := h₁₂ hu₂
  have hu₃1 : u₃ ∈ Subgroup.centralizer (K₁ : Set _) := h₁₃ hu₃
  have hu₃2 : u₃ ∈ Subgroup.centralizer (K₂ : Set _) := h₂₃ hu₃
  have hu₄1 : u₄ ∈ Subgroup.centralizer (K₁ : Set _) := h₁₄ hu₄
  have hu₄2 : u₄ ∈ Subgroup.centralizer (K₂ : Set _) := h₂₄ hu₄
  have hu₃4 : u₃ ∈ Subgroup.centralizer (K₄ : Set _) := hsymm h₃₄ hu₃
  have h12 : u₁ * u₂ = u₂ * u₁ := Subgroup.mem_centralizer_iff.mp hu₂1 u₁ hu₁
  have h34 : u₃ * u₄ = u₄ * u₃ := (Subgroup.mem_centralizer_iff.mp hu₃4 u₄ hu₄).symm
  have hu₁ne : u₁ ≠ 1 := fun h1 => hu₁Z (h1 ▸ Subgroup.one_mem _)
  have hu₃ne : u₃ ≠ 1 := fun h1 => hu₃Z (h1 ▸ Subgroup.one_mem _)
  have hu₂n : u₂ ∉ Subgroup.zpowers u₁ := fun hm =>
    hu₂Z ((Subgroup.zpowers_le.mpr hu₁2) hm)
  have hu₄n : u₄ ∉ Subgroup.zpowers u₃ := fun hm =>
    hu₄Z ((Subgroup.zpowers_le.mpr hu₃4) hm)
  obtain ⟨hE₁, hmem₁⟩ := isElemAbelian_zpowers_sup h12 hu₁3 hu₂3
  obtain ⟨hE₂, -⟩ := isElemAbelian_zpowers_sup h34 hu₃3 hu₄3
  have hE₁9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine h12 hu₁3 hu₁ne hu₂3 hu₂n
  have hE₂9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine h34 hu₃3 hu₃ne hu₄3 hu₄n
  have hE₁J : Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ≤ K₁ ⊔ K₂ :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hu₁))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hu₂))
  have hE₁T : Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ≤
      Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    sup_le (Subgroup.zpowers_le.mpr hu₁T) (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTK hu₂1)))
  have hE₂C : Subgroup.zpowers u₃ ⊔ Subgroup.zpowers u₄ ≤
      Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_centralizer_sup hu₃1 hu₃2))
      (Subgroup.zpowers_le.mpr (mem_centralizer_sup hu₄1 hu₄2))
  have hint : (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ⊓
      (Subgroup.zpowers u₃ ⊔ Subgroup.zpowers u₄) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem₁ x hx₁
    have hxC := hE₂C hx₂
    have hxK₁ : a * b ∈ Subgroup.centralizer (K₁ : Set _) :=
      Subgroup.centralizer_le (le_sup_left : K₁ ≤ K₁ ⊔ K₂) hxC
    have hxK₂ : a * b ∈ Subgroup.centralizer (K₂ : Set _) :=
      Subgroup.centralizer_le (le_sup_right : K₂ ≤ K₁ ⊔ K₂) hxC
    have hbK₁ : b ∈ Subgroup.centralizer (K₁ : Set _) := Subgroup.zpowers_le.mpr hu₂1 hb
    have haK₂ : a ∈ Subgroup.centralizer (K₂ : Set _) := Subgroup.zpowers_le.mpr hu₁2 ha
    have haK₁ : a ∈ Subgroup.centralizer (K₁ : Set _) := by
      have := Subgroup.mul_mem _ hxK₁ (Subgroup.inv_mem _ hbK₁)
      rwa [mul_inv_cancel_right] at this
    have hbK₂ : b ∈ Subgroup.centralizer (K₂ : Set _) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haK₂) hxK₂
      rwa [inv_mul_cancel_left] at this
    rw [eq_one_of_mem_zpowers_centralizer hu₁3 hu₁Z ha haK₁,
      eq_one_of_mem_zpowers_centralizer hu₂3 hu₂Z hb hbK₂, one_mul]
    exact Subgroup.one_mem _
  exact false_of_commuting_twoLocal148 h hT hT2 (hTK.trans le_sup_left) hE₁J hE₁T hE₁ hE₂C hE₂
    hint (by rw [hE₁9, hE₂9])

theorem le_normalizer_of_a5_component148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J K Aq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJ : IsComponent J) (hK : IsComponent K) (hKJ : K ≠ J)
    (hAJ : Aq ≤ Subgroup.normalizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hA3 : ∀ a ∈ Aq, a ^ 3 = 1) (φJ : ↥J ≃* alternatingGroup (Fin 5))
    (φK : ↥K ≃* alternatingGroup (Fin 5)) :
    Aq ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  obtain ⟨j, hjJ, hj1, hj3, hjZ⟩ := exists_three_of_a5 φJ
  obtain ⟨T, hTJ, hT, hT2, hjT⟩ := exists_two_subgroup_of_a5 φJ hjJ hj3 hj1
  obtain ⟨k, hkK, -, hk3, hkZ⟩ := exists_three_of_a5 φK
  intro a ha
  by_contra hn
  have ha3 : a ^ 3 = 1 := hA3 a ha
  have hJa : ∀ b ∈ Aq, J.map (MulAut.conj b).toMonoidHom = J := fun b hb =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAJ hb)
  have h₃ : K.map (MulAut.conj a).toMonoidHom ≠ K := fun h3 =>
    hn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3)
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      K₃ = K.map (MulAut.conj a).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨K₄, hK₄⟩ : ∃ K₄ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      K₄ = K.map (MulAut.conj (a * a)).toMonoidHom := ⟨_, rfl⟩
  have hK₃c : IsComponent K₃ := by rw [hK₃]; exact Res2LBal.isComponent_conj hK a
  have hK₄c : IsComponent K₄ := by rw [hK₄]; exact Res2LBal.isComponent_conj hK (a * a)
  have hinj : ∀ (H₁ H₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) (x : ↥(Y ⊔ A) ⧸ ker148 A Y),
      H₁.map (MulAut.conj x).toMonoidHom = H₂.map (MulAut.conj x).toMonoidHom → H₁ = H₂ :=
    fun H₁ H₂ x hx => Subgroup.map_injective (MulAut.conj x).injective hx
  have haaa : a * a * (a * a) = a := by
    calc a * a * (a * a) = (a * a * a) * a := by simp only [mul_assoc]
      _ = a := by rw [← pow_three', ha3, one_mul]
  have h₃' : K₃ ≠ K := by rw [hK₃]; exact h₃
  have h₄ : K₄ ≠ K := by
    rw [hK₄]
    intro h4
    apply h₃
    calc K.map (MulAut.conj a).toMonoidHom
        = K.map (MulAut.conj (a * a * (a * a))).toMonoidHom := by rw [haaa]
      _ = (K.map (MulAut.conj (a * a)).toMonoidHom).map (MulAut.conj (a * a)).toMonoidHom :=
          (Res2LBal.map_conj_map_conj K _ _).symm
      _ = K := by rw [h4, h4]
  have h₃₄ : K₄ ≠ K₃ := by
    rw [hK₄, hK₃]
    intro h43
    apply h₃
    apply hinj _ _ a
    rw [Res2LBal.map_conj_map_conj, h43]
  have h₃J : K₃ ≠ J := by
    rw [hK₃]
    intro h3J
    apply hKJ
    apply hinj _ _ a
    rw [h3J, hJa a ha]
  have h₄J : K₄ ≠ J := by
    rw [hK₄]
    intro h4J
    apply hKJ
    apply hinj _ _ (a * a)
    rw [h4J, hJa (a * a) (Aq.mul_mem ha ha)]
  have hcomm : ∀ {U V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, IsComponent U → IsComponent V →
      U ≠ V → V ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun hU hV hUV _ hx => Res2LBal.mem_centralizer_of_mem_of_ne hU hV hUV hx
  have hk3' : ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y, (x * k * x⁻¹) ^ 3 = 1 := fun x => by
    rw [conj_pow, hk3, mul_one, mul_inv_cancel]
  have hm₃ : a * k * a⁻¹ ∈ K₃ := by rw [hK₃]; exact Res2LBal.conj_mem_map hkK a
  have hm₄ : a * a * k * (a * a)⁻¹ ∈ K₄ := by rw [hK₄]; exact Res2LBal.conj_mem_map hkK (a * a)
  have hz₃ : a * k * a⁻¹ ∉ Subgroup.centralizer (K₃ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hK₃]; exact conj_not_mem_centralizer_map hkZ a
  have hz₄ : a * a * k * (a * a)⁻¹ ∉
      Subgroup.centralizer (K₄ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hK₄]; exact conj_not_mem_centralizer_map hkZ (a * a)
  exact false_of_four_commuting148 h (hcomm hJ hK hKJ.symm) (hcomm hJ hK₃c h₃J.symm)
    (hcomm hJ hK₄c h₄J.symm) (hcomm hK hK₃c h₃'.symm) (hcomm hK hK₄c h₄.symm)
    (hcomm hK₃c hK₄c h₃₄.symm) hjJ hkK hm₃ hm₄ hj3 hk3 (hk3' a) (hk3' (a * a)) hjZ hkZ hz₃ hz₄
    hT hT2 hTJ hjT

theorem exists_inner_a5_of_normalizer {Q : Type} [Group Q] [Finite Q] {Aq K : Subgroup Q}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hAK : Aq ≤ Subgroup.normalizer (K : Set Q)) (φ : ↥K ≃* alternatingGroup (Fin 5)) :
    ∃ k₀ ∈ K, k₀ ∈ Aq ∧ k₀ ≠ 1 ∧ k₀ ^ 3 = 1 ∧
      Aq ⊓ Subgroup.centralizer (K : Set Q) ⊔ Subgroup.zpowers k₀ = Aq := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 Aq := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
  have h60 : Nat.card K = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3K : 3 ∣ Nat.card K := by rw [h60]; norm_num
  obtain ⟨k₀, hk₀K, hk₀1, hk₀3, hk₀C⟩ := Ronan148J.exists_pow_eq_one_mem_centralizer hAp hAK h3K
  have hk₀A : k₀ ∈ Aq := hF3 k₀ hk₀C hk₀3
  have hZ : Subgroup.center ↥K = ⊥ := Ronan148V.inner_a5_center_eq_bot φ
  refine ⟨k₀, hk₀K, hk₀A, hk₀1, hk₀3,
    le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr hk₀A)) ?_⟩
  intro a ha
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : MulAut ↥K, ρ = K.normalizerMonoidHom ⟨a, hAK ha⟩ := ⟨_, rfl⟩
  have hρapp : ∀ z : ↥K, ((ρ z : ↥K) : Q) = a * z * a⁻¹ := fun z => by
    rw [hρdef]
    rfl
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρdef, ← map_pow]
    have h3 : (⟨a, hAK ha⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA3 a ha)
    rw [h3, map_one]
  have hinn : CFSG.RankThree.PartTwo.KFacts.IsInnerAut ρ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.isInnerAut_of_alt (β' := Fin 5) (by simp) φ hρ3
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hinn
  have hconj : ∀ z ∈ K, a * z * a⁻¹ = (w : Q) * z * (w : Q)⁻¹ := by
    intro z hz
    rw [← hρapp ⟨z, hz⟩, ← hw]
    rfl
  have hinvK : ∀ {b : Q}, b ∈ Aq → ∀ z ∈ K, b⁻¹ * z * b ∈ K := by
    intro b hb z hz
    have := (Subgroup.mem_normalizer_iff.mp (hAK (Aq.inv_mem hb)) z).mp hz
    rwa [inv_inv] at this
  have hcen : ∀ e ∈ K, (∀ z ∈ K, e * z * e⁻¹ = z) → e = 1 := by
    intro e he hez
    have hz : (⟨e, he⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hez g g.2
      show (g : Q) * e = e * g
      calc (g : Q) * e = e * g * e⁻¹ * e := by rw [h1]
        _ = e * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hwC : (w : Q) ∈ Subgroup.centralizer (Aq : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hwbK : b * (w : Q) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK hb) w).mp w.2
    have he : (w : Q)⁻¹ * (b * w * b⁻¹) = 1 := by
      refine hcen _ (K.mul_mem (K.inv_mem w.2) hwbK) fun z hz => ?_
      have hz' := hinvK hb z hz
      have hab : a * b = b * a := hAab a ha b hb
      have h1 : b * (w : Q) * b⁻¹ * z * (b * (w : Q) * b⁻¹)⁻¹ =
          b * ((w : Q) * (b⁻¹ * z * b) * (w : Q)⁻¹) * b⁻¹ := by group
      have h2 : b * (a * (b⁻¹ * z * b) * a⁻¹) * b⁻¹ = (b * a * b⁻¹) * z * (b * a * b⁻¹)⁻¹ := by
        group
      have h3 : b * a * b⁻¹ = a := by
        calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [hab]
          _ = a := by group
      calc (w : Q)⁻¹ * (b * w * b⁻¹) * z * ((w : Q)⁻¹ * (b * w * b⁻¹))⁻¹
          = (w : Q)⁻¹ * (b * (w : Q) * b⁻¹ * z * (b * (w : Q) * b⁻¹)⁻¹) * w := by group
        _ = (w : Q)⁻¹ * (b * ((w : Q) * (b⁻¹ * z * b) * (w : Q)⁻¹) * b⁻¹) * w := by rw [h1]
        _ = (w : Q)⁻¹ * (b * (a * (b⁻¹ * z * b) * a⁻¹) * b⁻¹) * w := by rw [hconj _ hz']
        _ = (w : Q)⁻¹ * ((b * a * b⁻¹) * z * (b * a * b⁻¹)⁻¹) * w := by rw [h2]
        _ = (w : Q)⁻¹ * (a * z * a⁻¹) * w := by rw [h3]
        _ = (w : Q)⁻¹ * ((w : Q) * z * (w : Q)⁻¹) * w := by rw [hconj z hz]
        _ = z := by group
    have h4 : b * (w : Q) * b⁻¹ = w := by
      calc b * (w : Q) * b⁻¹ = (w : Q) * ((w : Q)⁻¹ * (b * w * b⁻¹)) := by group
        _ = w := by rw [he, mul_one]
    calc b * (w : Q) = b * (w : Q) * b⁻¹ * b := by group
      _ = (w : Q) * b := by rw [h4]
  have hw3 : (w : Q) ^ 3 = 1 := by
    refine hcen _ (K.pow_mem w.2 3) fun z hz => ?_
    have hK1 : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hAK ha) x).mp hx
    calc (w : Q) ^ 3 * z * ((w : Q) ^ 3)⁻¹
        = (w : Q) * ((w : Q) * ((w : Q) * z * (w : Q)⁻¹) * (w : Q)⁻¹) * (w : Q)⁻¹ := by
          simp only [pow_three', mul_inv_rev, mul_assoc]
      _ = (w : Q) * ((w : Q) * (a * z * a⁻¹) * (w : Q)⁻¹) * (w : Q)⁻¹ := by rw [← hconj z hz]
      _ = (w : Q) * (a * (a * z * a⁻¹) * a⁻¹) * (w : Q)⁻¹ := by rw [← hconj _ (hK1 z hz)]
      _ = a * (a * (a * z * a⁻¹) * a⁻¹) * a⁻¹ := by rw [← hconj _ (hK1 _ (hK1 z hz))]
      _ = a ^ 3 * z * (a ^ 3)⁻¹ := by simp only [pow_three', mul_inv_rev, mul_assoc]
      _ = z := by rw [hA3 a ha]; group
  have hwA : (w : Q) ∈ Aq := hF3 _ hwC hw3
  have hwk : (w : Q) ∈ Subgroup.zpowers k₀ := by
    by_contra hn
    have h9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine (hAab k₀ hk₀A _ hwA) hk₀3 hk₀1 hw3 hn
    have hle : Subgroup.zpowers k₀ ⊔ Subgroup.zpowers (w : Q) ≤ K :=
      sup_le (Subgroup.zpowers_le.mpr hk₀K) (Subgroup.zpowers_le.mpr w.2)
    have hd := Subgroup.card_dvd_of_le hle
    rw [h9, h60] at hd
    norm_num at hd
  have haw : a * (w : Q)⁻¹ ∈ Aq ⊓ Subgroup.centralizer (K : Set Q) := by
    refine Subgroup.mem_inf.mpr ⟨Aq.mul_mem ha (Aq.inv_mem hwA), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : (w : Q)⁻¹ * z * w ∈ K := K.mul_mem (K.mul_mem (K.inv_mem w.2) hz) w.2
    have h1 := hconj _ hz'
    have h2 : (w : Q) * ((w : Q)⁻¹ * z * w) * (w : Q)⁻¹ = z := by group
    rw [h2] at h1
    calc z * (a * (w : Q)⁻¹) = a * ((w : Q)⁻¹ * z * w) * a⁻¹ * (a * (w : Q)⁻¹) := by rw [h1]
      _ = a * (w : Q)⁻¹ * z := by group
  have hsplit : a = a * (w : Q)⁻¹ * w := by group
  rw [hsplit]
  exact Subgroup.mul_mem_sup haw hwk

theorem isPerfect_of_le_commutator_of_isTripleCover {Q : Type} [Group Q] [Finite Q]
    {Z Aq : Subgroup Q} (hT : Sec4.IsTripleCover ↥Z (alternatingGroup (Fin 6)))
    (hAp : IsPGroup 3 Aq) (hAZ : Aq ≤ Subgroup.normalizer (Z : Set Q))
    (hle : Z ≤ ⁅Z, Aq⁆) : Group.IsPerfect ↥Z := by
  obtain ⟨-, hsup, -⟩ := quasisimple_commutator_of_isTripleCover_A6 hT
  have hDeq : (commutator ↥Z).map Z.subtype = ⁅Z, Z⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hZc3 : Nat.card ↥((Subgroup.center ↥Z).map Z.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Z.subtype_injective]
    exact hT.1
  have hAZc : Aq ≤ Subgroup.normalizer
      (((Subgroup.center ↥Z).map Z.subtype : Subgroup Q) : Set Q) := by
    rw [Sec14.map_subtype_center_eq]
    exact (le_inf hAZ (hAZ.trans (Sec5.normalizer_le_normalizer_centralizer _))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAc := Sec14.Res6Order.le_centralizer_of_card_three hAp hZc3 hAZc
  have hAD : Aq ≤ Subgroup.normalizer ((⁅Z, Z⁆ : Subgroup Q) : Set Q) := by
    intro a ha
    have h1 := hAZ ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [Subgroup.map_commutator, h1]
  have hcomm : ⁅Z, Aq⁆ ≤ ⁅Z, Z⁆ := by
    rw [Subgroup.commutator_le]
    intro z hz a ha
    have hz' : (⟨z, hz⟩ : ↥Z) ∈ (commutator ↥Z ⊔ Subgroup.center ↥Z : Subgroup ↥Z) := by
      rw [hsup]
      exact Subgroup.mem_top _
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hz'
    obtain ⟨k, hk, w, hw, hkw⟩ := hz'
    have hzkw : z = (k : Q) * (w : Q) := by
      have := congrArg Subtype.val hkw
      simpa using this.symm
    have hkD : (k : Q) ∈ ⁅Z, Z⁆ := hDeq ▸ ⟨k, hk, rfl⟩
    have hwa : (w : Q) * a = a * (w : Q) :=
      (Subgroup.mem_centralizer_iff.mp (hAc ha) (w : Q) ⟨w, hw, rfl⟩)
    have hka : (k : Q) * (a * (k : Q)⁻¹ * a⁻¹) ∈ ⁅Z, Z⁆ :=
      Subgroup.mul_mem _ hkD ((Subgroup.mem_normalizer_iff.mp (hAD ha) _).mp
        (Subgroup.inv_mem _ hkD))
    rw [hzkw, commutatorElement_def]
    have e : (k : Q) * (w : Q) * a * ((k : Q) * (w : Q))⁻¹ * a⁻¹ =
        (k : Q) * (a * (k : Q)⁻¹ * a⁻¹) := by
      calc (k : Q) * (w : Q) * a * ((k : Q) * (w : Q))⁻¹ * a⁻¹
          = (k : Q) * ((w : Q) * a) * (w : Q)⁻¹ * (k : Q)⁻¹ * a⁻¹ := by group
        _ = (k : Q) * (a * (w : Q)) * (w : Q)⁻¹ * (k : Q)⁻¹ * a⁻¹ := by rw [hwa]
        _ = (k : Q) * (a * (k : Q)⁻¹ * a⁻¹) := by group
    rw [e]
    exact hka
  exact Subgroup.isPerfect_iff.mpr
    (le_antisymm (Subgroup.commutator_le_self Z) (hle.trans hcomm))

section Frame

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_deltaZero_le_commutator {LB : Subgroup G → Subgroup G} {W : Subgroup G}
    (hWY : W ≤ Y) :
    img148 A Y (deltaZero A LB W) ≤ ⁅img148 A Y (deltaZero A LB W), img148 A Y A⁆ := by
  have hDM : deltaZero A LB W ≤ Y ⊔ A := ((deltaZero_le W).trans hWY).trans le_sup_left
  have hle : deltaZero A LB W ≤ ⁅deltaZero A LB W, A⁆ := by
    refine sSup_le fun Q hQ => ?_
    rw [hQ.1.2]
    exact Subgroup.commutator_mono (le_deltaZero hQ.1 hQ.2) le_rfl
  calc img148 A Y (deltaZero A LB W) ≤ img148 A Y ⁅deltaZero A LB W, A⁆ := img148_mono hle
    _ = ⁅img148 A Y (deltaZero A LB W), img148 A Y A⁆ :=
        Item148PtRes.img148_commutator hDM le_sup_right

theorem le_img148_of_isPerfect148 (hA : Late.IsE27 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {P : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hP : Group.IsPerfect ↥P) : P ≤ img148 A Y Y := by
  refine Sec14.le_of_isPerfect_of_le_sup (img148_isE27 hA).1.1 (img148_le_normalizer hAY) hP ?_
  intro x _
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) x
  rw [← img148_sup le_sup_left le_sup_right]
  exact mem_img148_iff.mpr ⟨m, m.2, m.2, rfl⟩

theorem le_img148_deltaZero_of_a5_point (h142 : Concl142S14) {L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hY : Y ∈ scriptY A) {a : G}
    (haΩ : Subgroup.zpowers a ∈ omegaA A) {K Bq : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (φ : ↥K ≃* alternatingGroup (Fin 5))
    (hKa : K ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({a} : Set G)))
    (hBK : Bq ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {k₀ : ↥(Y ⊔ A) ⧸ ker148 A Y} (hk₀K : k₀ ∈ K) (hk₀1 : k₀ ≠ 1) (hk₀3 : k₀ ^ 3 = 1)
    (hAeq : Bq ⊔ Subgroup.zpowers k₀ = img148 A Y A) :
    K ≤ img148 A Y (deltaZero A (lB A) Y) := by
  set H : Subgroup ↥K := (img148 A Y (deltaZero A (lB A) Y)).subgroupOf K with hH
  set k' : ↥K := ⟨k₀, hk₀K⟩ with hk'
  have hk'1 : k' ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  have hk'3 : k' ^ 3 = 1 := Subtype.ext (by simp [hk', hk₀3])
  have htop : H = ⊤ := by
    refine Ronan148J.eq_top_of_forall_commutator_le_a5 φ hk'1 hk'3 fun V hV3 hkV => ?_
    set W : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) := V.map K.subtype with hW
    have hWK : W ≤ K := Subgroup.map_subtype_le V
    have hW3 : ¬ 3 ∣ Nat.card W := by
      rwa [hW, Subgroup.card_map_of_injective K.subtype_injective]
    have hkW : k₀ ∈ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨k' * v * k'⁻¹, (Subgroup.mem_normalizer_iff.mp hkV v).mp hv, rfl⟩
      · rintro ⟨v, hv, hveq⟩
        have hxK : x ∈ K := by
          have h1 : k₀⁻¹ * (k₀ * x * k₀⁻¹) * k₀ ∈ K :=
            K.mul_mem (K.mul_mem (K.inv_mem hk₀K) (hveq ▸ v.2)) hk₀K
          simpa [mul_assoc] using h1
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        have h2 : k' * ⟨x, hxK⟩ * k'⁻¹ = v := Subtype.ext hveq.symm
        exact (Subgroup.mem_normalizer_iff.mp hkV ⟨x, hxK⟩).mpr (by rw [h2]; exact hv)
    have hBW : Bq ≤ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp (hBK hx) w (hWK hw)
    have hAW : img148 A Y A ≤ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [← hAeq]
      exact sup_le hBW (Subgroup.zpowers_le.mpr hkW)
    have hc := Ronan148J.commutator_le_img148_deltaZero_of_point h142 hS hY haΩ W
      (hWK.trans hKa) hW3 hAW
    have hkA : Subgroup.zpowers k₀ ≤ img148 A Y A := hAeq ▸ le_sup_right
    intro x hx
    have hxm : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ ⁅W, Subgroup.zpowers k₀⁆ := by
      have hmap : (⁅V, Subgroup.zpowers k'⁆).map K.subtype = ⁅W, Subgroup.zpowers k₀⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    exact hc (Subgroup.commutator_mono le_rfl hkA hxm)
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ H := htop ▸ Subgroup.mem_top _
  exact this

end Frame

theorem isComponent_of_le_normalizer_inf_centralizer {Γ : Type*} [Group Γ] [Finite Γ]
    {H J Z : Subgroup Γ} (hH : H.Normal) (hHE : ∀ K : Subgroup Γ, IsComponent K → K ≤ H)
    (hJ : IsComponent J) (hZq : IsQuasisimple ↥Z)
    (hZC : Z ≤ H ⊓ Subgroup.centralizer (J : Set Γ))
    (hCZ : H ⊓ Subgroup.centralizer (J : Set Γ) ≤ Subgroup.normalizer (Z : Set Γ)) :
    IsComponent Z := by
  set C := H ⊓ Subgroup.centralizer (J : Set Γ) with hCdef
  have hZn : (Z.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr hCZ
  by_cases hall : ∀ K : Subgroup Γ, IsComponent K → Z ≤ Subgroup.centralizer (K : Set Γ)
  ·
    have hZE : Z ≤ Subgroup.centralizer ((CFSG.layer Γ : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun K hK => Subgroup.le_centralizer_iff.mp (hall K hK)
    haveI : (CFSG.layer Γ).Characteristic := CFSG.LocalCores.layer_characteristic
    haveI := hH
    set N := H ⊓ Subgroup.centralizer ((CFSG.layer Γ : Subgroup Γ) : Set Γ) with hN
    have hNn : N.Normal := inferInstance
    have hZN : Z ≤ N := le_inf (hZC.trans inf_le_left) hZE
    have hJE : J ≤ CFSG.layer Γ := le_sSup hJ
    have hNC : N ≤ C := le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hJE))
    have hZNn : (Z.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).mpr (hNC.trans hCZ)
    exact ⟨hZq, Subgroup.IsSubnormal.trans hZN hZNn.isSubnormal hNn.isSubnormal⟩
  push Not at hall
  obtain ⟨K, hK, hZK⟩ := hall
  have hKJ : K ≠ J := by
    rintro rfl
    exact hZK (hZC.trans inf_le_right)
  have hKC' : K ≤ Subgroup.centralizer (J : Set Γ) := by
    rcases CFSG.LocalCores.distinct_components_commute hK hJ with h | h
    · exact absurd h hKJ
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hKC : K ≤ C := le_inf (hHE K hK) hKC'
  rcases CFSG.LocalCores.component_normal_subgroup (CFSG.LocalCores.component_overgroup hK hKC)
      hZn with h | h
  · have hKZ : K ≤ Z := CFSG.LocalCores.le_of_subgroupOf_le hKC h
    have hK' := CFSG.LocalCores.component_overgroup hK hKZ
    have htop : IsComponent (⊤ : Subgroup ↥Z) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hZq,
        Subgroup.IsSubnormal.top⟩
    rcases CFSG.LocalCores.distinct_components_commute hK' htop with h' | h'
    · have hKZeq : K = Z := le_antisymm hKZ (Subgroup.subgroupOf_eq_top.mp h')
      exact hKZeq ▸ hK
    · exfalso
      apply hZK
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : (⟨k, hKZ hk⟩ : ↥Z) ∈ K.subgroupOf Z := Subgroup.mem_subgroupOf.mpr hk
      have h2 := Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h' hk') ⟨z, hz⟩ (Subgroup.mem_top _)
      exact (congrArg Subtype.val h2).symm
  · exfalso
    apply hZK
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hKC h
    rw [inf_eq_left.mpr hZC, Subgroup.commutator_comm] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1

theorem zpowers_mem_omegaA_of_ncard_twelve {A : Subgroup G} (hA : Late.IsE27 A)
    (h12 : (omegaA A).ncard = 12) {d u : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdΩ : Subgroup.zpowers d ∉ omegaA A) (huA : u ∈ A) (hu1 : u ≠ 1)
    (hud : Subgroup.zpowers u ≠ Subgroup.zpowers d) : Subgroup.zpowers u ∈ omegaA A := by
  set T := {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} with hTdef
  have hΩT : omegaA A ⊆ T := fun F hF => ⟨hF.1, hF.2.1⟩
  have hdT : Subgroup.zpowers d ∈ T :=
    ⟨Subgroup.zpowers_le.mpr hdA, Sec13.card_zpowers_eq_three hA.1 hdA hd1⟩
  have huT : Subgroup.zpowers u ∈ T :=
    ⟨Subgroup.zpowers_le.mpr huA, Sec13.card_zpowers_eq_three hA.1 huA hu1⟩
  by_contra huΩ
  have hsub : omegaA A ⊆ T \ {Subgroup.zpowers d, Subgroup.zpowers u} := by
    intro F hF
    refine ⟨hΩT hF, ?_⟩
    rintro (rfl | rfl)
    · exact hdΩ hF
    · exact huΩ hF
  have hpair : ({Subgroup.zpowers d, Subgroup.zpowers u} : Set (Subgroup G)) ⊆ T := by
    rintro F (rfl | rfl)
    · exact hdT
    · exact huT
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_sdiff_add_ncard_of_subset hpair
  rw [Set.ncard_pair (Ne.symm hud)] at h2
  have h3 := Item148PtRes.ncard_subgroups_card_three_le (A := A) hA.2
  rw [← hTdef] at h3
  omega

theorem exists_tripleCover_A6_le_of_j2
    {Γ : Type} [Group Γ] [Finite Γ] {Z : Subgroup Γ} (φZ : ↥Z ≃* CFSG.Blueprint.NativeSporadic.J2) :
    IsQuasisimple ↥Z ∧
      ∃ U : Subgroup Γ, U ≤ Z ∧ Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)) := by
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hZs : IsSimpleGroup ↥Z := MulEquiv.isSimpleGroup φZ
  have hZcard : Nat.card ↥Z = 604800 := by
    rw [Nat.card_congr φZ.toEquiv, CFSG.Sporadic.J2.card_J2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Z) := Sylow.nonempty
  have hPne : (P : Subgroup ↥Z) ≠ ⊥ := P.ne_bot_of_dvd_card (by rw [hZcard]; norm_num)
  have : Nontrivial ↥(P : Subgroup ↥Z) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have := P.isPGroup'.center_nontrivial
  obtain ⟨z₀, hz₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥(P : Subgroup ↥Z)))
  set z : ↥Z := ((z₀ : ↥(P : Subgroup ↥Z)) : ↥Z) with hz
  have hz1 : z ≠ 1 := by
    intro h0
    apply hz₀
    apply Subtype.ext
    apply Subtype.ext
    exact h0
  have hzP : ∃ P' : Sylow 3 ↥Z, z ∈ (P' : Subgroup ↥Z) ∧
      (P' : Subgroup ↥Z) ≤ Subgroup.centralizer ({z} : Set ↥Z) := by
    refine ⟨P, (z₀ : ↥(P : Subgroup ↥Z)).2, fun p hp => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp z₀.2 ⟨p, hp⟩
    exact congrArg Subtype.val this
  have hU0 := KFacts.KS14.j2_centralizer_isTripleCover Sec4.Sporadic.rank3II_4_15 ⟨φZ⟩ hz1 hzP
  have hnc : ∃ a b : ↥Z, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.centralizer ({z} : Set ↥Z) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcon g z
    have h1 := Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hU0
    rw [htop, Subgroup.card_top, hZcard] at h1
    norm_num at h1
  refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
    (Subgroup.centralizer ({z} : Set ↥Z)).map Z.subtype, Subgroup.map_subtype_le _, ?_⟩
  exact KFacts.KS14.isTripleCover_congr
    ((Subgroup.centralizer ({z} : Set ↥Z)).equivMapOfInjective _ Z.subtype_injective) hU0

theorem exists_noncentral_of_tripleCover_le {Γ : Type} [Group Γ] [Finite Γ]
    {U : Subgroup Γ} (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) :
    ∃ u ∈ U, u ^ 3 = 1 ∧ u ∉ Subgroup.centralizer (U : Set Γ) := by
  obtain ⟨u, hu3, huZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hU
  refine ⟨u, u.2, by simpa using congrArg Subtype.val hu3, fun hC => huZ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC g g.2)

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
