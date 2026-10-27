module

public import CFSG.Quasithin.Vol2.Ch5Sec1M23L34Orb
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.M23.M23Group

namespace M23Perm

theorem nonempty_mulEquiv_H0 {Γ : Type} [Group Γ] {L : Subgroup Γ}
    (hL : IsSporadic .M23 ↥L) : Nonempty (↥L ≃* ↥H0) := by
  obtain ⟨e₀⟩ := hL
  exact ⟨(e₀ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M23).trans
    (MulEquiv.subgroupCongr CFSG.Sporadic.Mathieu.nativeM23_eq)⟩

theorem card_centralizerIn_H0 :
    ∀ u ∈ H0, orderOf u = 2 →
      Nat.card (CFSG.Sporadic.Schreier.centralizerIn H0 u) = 2688 := by
  have h := CFSG.GH74.Generic.S45.LAlt.m23_class_card
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq] at h
  exact h

theorem l34_facts
    {Γ : Type} [Group Γ] [Finite Γ] {L A : Subgroup Γ} (e : ↥L ≃* ↥H0) (hAL : A ≤ L)
    (hA : IsSL3Ch5 2 (ModO2 A)) :
    IsSimpleGroup ↥A ∧ Nat.card A = 20160 ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
      Fintype.card Ω = 8 → IsEmpty (↥A ≃* ↥(alternatingGroup Ω)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : Nat.card L = 10200960 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_M23]
  have hAd : Nat.card A ∣ 10200960 := hLc ▸ Subgroup.card_dvd_of_le hAL
  have hAq := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥A)
  rcases hA with hL3 | ⟨F, _, _, hF, ⟨eF⟩⟩
  swap
  ·
    exfalso
    have : Fintype F := Fintype.ofFinite F
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 60480 := by
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hF]
      decide
    have h1 : 60480 ∣ Nat.card ↥A := by
      rw [hAq, ← hSL, ← Nat.card_congr eF.toEquiv]
      exact Dvd.intro _ rfl
    have := h1.trans hAd
    norm_num at this
  have hY : StatedClassicalModel (ModO2 A) .PSL 3 2 2 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL3
  obtain ⟨hc, -, hAlt⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated _ hY
  have hs : IsSimpleGroup (ModO2 A) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hY).2
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥A)).exists_card_eq
  have hc' : Nat.card (↥A ⧸ CFSG.pCore 2 ↥A) = 20160 := hc
  rw [hc', hk] at hAq
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have h4 : 80640 ∣ Nat.card ↥A := by
      rw [hAq]
      have : 2 ^ k = 4 * 2 ^ (k - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this]
      exact ⟨2 ^ (k - 2), by ring⟩
    have := h4.trans hAd
    norm_num at this
  have hbot : CFSG.pCore 2 ↥A = ⊥ := by
    interval_cases k
    · exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
    · exfalso
      set N := CFSG.pCore 2 ↥A with hN
      have hN2 : Nat.card N = 2 := by rw [hk, pow_one]
      obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).mp hN2
      have hNn : N.Normal := CFSG.pCore_normal
      have hcen : ∀ a : ↥A, a * (y : ↥A) = (y : ↥A) * a := by
        intro a
        have hmem : a * (y : ↥A) * a⁻¹ ∈ N := hNn.conj_mem _ y.2 a
        have hne : (⟨a * (y : ↥A) * a⁻¹, hmem⟩ : ↥N) ≠ 1 := by
          intro h
          apply hy1
          have h' : a * (y : ↥A) * a⁻¹ = 1 := congrArg Subtype.val h
          apply Subtype.ext
          calc (y : ↥A) = a⁻¹ * (a * (y : ↥A) * a⁻¹) * a := by group
            _ = 1 := by rw [h']; group
        have h1 : a * (y : ↥A) * a⁻¹ = (y : ↥A) := congrArg Subtype.val (hy _ hne)
        calc a * (y : ↥A) = (a * (y : ↥A) * a⁻¹) * a := by group
          _ = (y : ↥A) * a := by rw [h1]
      have hy2 : (y : ↥A) ^ 2 = 1 := by
        have h := pow_card_eq_one' (G := ↥N) (x := y)
        rw [hN2] at h
        have := congrArg Subtype.val h
        simpa using this
      have hy1' : (y : ↥A) ≠ 1 := fun h => hy1 (Subtype.ext h)
      set f : ↥A →* Equiv.Perm (Fin 23) :=
        H0.subtype.comp (e.toMonoidHom.comp (Subgroup.inclusion hAL)) with hf
      have hfi : Function.Injective f := by
        intro a b hab
        have h1 : e (Subgroup.inclusion hAL a) = e (Subgroup.inclusion hAL b) :=
          Subtype.ext hab
        exact Subgroup.inclusion_injective hAL (e.injective h1)
      have hτH : f y ∈ H0 := (e (Subgroup.inclusion hAL y)).2
      have hτ : orderOf (f y) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [← map_pow, hy2, map_one]
        · intro h
          exact hy1' (hfi (by rw [h, map_one]))
      have hcard := card_centralizerIn_H0 _ hτH hτ
      have hle : f.range ≤ CFSG.Sporadic.Schreier.centralizerIn H0 (f y) := by
        rintro _ ⟨a, rfl⟩
        rw [CFSG.Sporadic.Schreier.mem_centralizerIn]
        refine ⟨(e (Subgroup.inclusion hAL a)).2, ?_⟩
        rw [← map_mul, ← map_mul, hcen a]
      have h1 := Subgroup.card_le_of_le hle
      rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv, hAq] at h1
      norm_num at h1
  let ψ : ModO2 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨ψ.isSimpleGroup_congr.mp hs, ?_, fun Ω _ _ hΩ =>
    ⟨fun f => (hAlt Ω (by omega)).false (ψ.trans f)⟩⟩
  rw [← Nat.card_congr ψ.toEquiv, hc]

theorem exists_two_point_stabilizer
    {Γ : Type} [Group Γ] [Finite Γ] {L A : Subgroup Γ}
    (hL : IsSporadic .M23 ↥L) (hAL : A ≤ L) (hA : IsSL3Ch5 2 (ModO2 A)) :
    ∃ (e : ↥L ≃* ↥H0) (x y : Fin 23), x ≠ y ∧
      ∀ l : ↥L, (l : Γ) ∈ A ↔ e l • x = x ∧ e l • y = y := by
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_H0 hL
  obtain ⟨hs, hc, h8⟩ := l34_facts e hAL hA
  set A' : Subgroup ↥H0 := (A.subgroupOf L).map e.toMonoidHom with hA'
  let ι : ↥A ≃* ↥A' := (Subgroup.subgroupOfEquivOfLe hAL).symm.trans
    ((A.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have : IsSimpleGroup ↥A' := ι.isSimpleGroup_congr.mp hs
  have hc' : Nat.card A' = 20160 := by rw [← Nat.card_congr ι.toEquiv, hc]
  have h8' : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], Fintype.card Ω = 8 →
      IsEmpty (↥A' ≃* ↥(alternatingGroup Ω)) := fun Ω _ _ hΩ =>
    ⟨fun f => (h8 Ω hΩ).false (ι.trans f)⟩
  obtain ⟨x, y, hxy, hx, hy, -⟩ := orbit_structure hc' h8'
  have hmem : ∀ l : ↥L, e l ∈ A' ↔ (l : Γ) ∈ A := fun l => by
    rw [hA', Subgroup.mem_map_equiv, e.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hle : A' ≤ fixingSubgroup ↥H0 ((({x, y} : Finset (Fin 23))) : Set (Fin 23)) := by
    intro g hg
    rw [mem_fixingSubgroup_iff]
    intro p hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hx g hg
    · exact hy g hg
  have hcard : Nat.card (fixingSubgroup ↥H0 ((({x, y} : Finset (Fin 23))) : Set (Fin 23))) =
      20160 := by
    have h := card_fixingSubgroup ({x, y} : Finset (Fin 23))
      (by rw [Finset.card_pair hxy]; norm_num)
    rw [Finset.card_pair hxy, show Nat.descFactorial 23 2 = 506 by decide] at h
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hc'])
  refine ⟨e, x, y, hxy, fun l => ?_⟩
  rw [← hmem, heq, mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨h x (by simp), h y (by simp)⟩
  · rintro ⟨h1, h2⟩ p hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact h1
    · exact h2

theorem mem_normalizer_iff_of_corr {Γ : Type} [Group Γ] {L Q : Subgroup Γ} (e : ↥L ≃* ↥H0)
    (hQL : Q ≤ L) {Q' : Subgroup ↥H0} (hQ : ∀ l : ↥L, (l : Γ) ∈ Q ↔ e l ∈ Q') {r : Γ}
    (hrL : r ∈ Subgroup.normalizer (L : Set Γ)) {m : ↥H0}
    (hm : ∀ l l' : ↥L, (l' : Γ) = r * l * r⁻¹ → e l' = m * e l * m⁻¹) :
    r ∈ Subgroup.normalizer (Q : Set Γ) ↔ m ∈ Subgroup.normalizer (Q' : Set ↥H0) := by
  have hconj : ∀ l : ↥L, ((l : Γ) ∈ Q ↔ e l ∈ Q') ∧
      (r * l * r⁻¹ ∈ Q ↔ m * e l * m⁻¹ ∈ Q') := by
    intro l
    refine ⟨hQ l, ?_⟩
    have hl' : r * l * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL l).mp l.2
    rw [← hm l ⟨_, hl'⟩ rfl]
    exact hQ ⟨_, hl'⟩
  constructor
  · intro hr
    rw [Subgroup.mem_normalizer_iff]
    intro q
    have h := hconj (e.symm q)
    rw [e.apply_symm_apply] at h
    rw [← h.1, ← h.2]
    exact Subgroup.mem_normalizer_iff.mp hr _
  · intro hm'
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ L
    · have h := hconj ⟨g, hg⟩
      rw [h.1, h.2]
      exact Subgroup.mem_normalizer_iff.mp hm' _
    · have hg' : r * g * r⁻¹ ∉ L := fun h => hg ((Subgroup.mem_normalizer_iff.mp hrL g).mpr h)
      exact ⟨fun h => absurd (hQL h) hg, fun h => absurd (hQL h) hg'⟩

theorem intertwine_self {Γ : Type} [Group Γ] {L : Subgroup Γ} (e : ↥L ≃* ↥H0) (l₀ : ↥L) :
    ∀ l l' : ↥L, (l' : Γ) = l₀ * l * (l₀ : Γ)⁻¹ → e l' = e l₀ * e l * (e l₀)⁻¹ := by
  intro l l' h
  have : l' = l₀ * l * l₀⁻¹ := Subtype.ext (by simp [h])
  rw [this, map_mul, map_mul, map_inv]

theorem fix_or_swap {g : ↥H0} {x y : Fin 23} (hxy : x ≠ y) (hx : g • x = x ∨ g • x = y)
    (hy : g • y = x ∨ g • y = y) : (g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x) := by
  have hinj : g • x ≠ g • y := fun h => hxy (MulAction.injective g h)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hinj
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hx.trans hy.symm) hinj

theorem fix_or_swap_of_mem_normalizer
    {x y : Fin 23} (hxy : x ≠ y)
    {m : ↥H0} (hm : m ∈ Subgroup.normalizer ((MulAction.stabilizer ↥H0 x ⊓
      MulAction.stabilizer ↥H0 y : Subgroup ↥H0) : Set ↥H0)) :
    (m • x = x ∧ m • y = y) ∨ (m • x = y ∧ m • y = x) := by
  have key : ∀ p : Fin 23, (p = x ∨ p = y) → m • p = x ∨ m • p = y := by
    intro p hp
    by_contra h
    push Not at h
    obtain ⟨g, hgx, hgy, hgp⟩ := exists_fix_two_move hxy h.1 h.2
    have hg : g ∈ MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y :=
      Subgroup.mem_inf.mpr ⟨hgx, hgy⟩
    have h1 : m⁻¹ * g * m ∈ MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) g).mp hg
      rwa [inv_inv] at this
    have h2 : (m⁻¹ * g * m) • p = p := by
      rcases hp with rfl | rfl
      · exact (Subgroup.mem_inf.mp h1).1
      · exact (Subgroup.mem_inf.mp h1).2
    apply hgp
    rw [mul_smul, mul_smul] at h2
    have h3 := congrArg (m • ·) h2
    simp only [smul_inv_smul] at h3
    exact h3
  rcases key x (Or.inl rfl) with h1 | h1 <;> rcases key y (Or.inr rfl) with h2 | h2
  all_goals first
    | exact fix_or_swap hxy (Or.inl h1) (Or.inl h2)
    | exact fix_or_swap hxy (Or.inl h1) (Or.inr h2)
    | exact fix_or_swap hxy (Or.inr h1) (Or.inl h2)
    | exact fix_or_swap hxy (Or.inr h1) (Or.inr h2)

theorem conj_smul_eq_iff {m g : ↥H0} {p q : Fin 23} (h : m • q = p) :
    (m * g * m⁻¹) • p = p ↔ g • q = q := by
  have hq : m⁻¹ • p = q := by rw [← h, inv_smul_smul]
  rw [mul_smul, mul_smul, hq, ← h]
  exact ⟨fun h' => MulAction.injective m h', fun h' => by rw [h']⟩

theorem mem_normalizer_stab2_of_perm {x y : Fin 23} {m : ↥H0}
    (hm : (m • x = x ∧ m • y = y) ∨ (m • x = y ∧ m • y = x)) :
    m ∈ Subgroup.normalizer ((MulAction.stabilizer ↥H0 x ⊓
      MulAction.stabilizer ↥H0 y : Subgroup ↥H0) : Set ↥H0) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [conj_smul_eq_iff h1, conj_smul_eq_iff h2]
  · rw [conj_smul_eq_iff h2, conj_smul_eq_iff h1]
    exact and_comm

theorem mem_normalizer_stab_of_perm {x y z : Fin 23} {m : ↥H0}
    (hm : (m • x = x ∧ m • y = y) ∨ (m • x = y ∧ m • y = x)) (hz : m • z = z) :
    m ∈ Subgroup.normalizer ((MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y ⊓
      MulAction.stabilizer ↥H0 z : Subgroup ↥H0) : Set ↥H0) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [conj_smul_eq_iff hz]
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [conj_smul_eq_iff h1, conj_smul_eq_iff h2]
  · rw [conj_smul_eq_iff h2, conj_smul_eq_iff h1, and_comm (a := g • y = y)]

end M23Perm

open M23Perm in
theorem m23_l34_relIndex_normalizer
    {Γ : Type} [Group Γ] [Finite Γ] {L A : Subgroup Γ}
    (hL : IsSporadic .M23 ↥L) (hAL : A ≤ L) (hA : IsSL3Ch5 2 (ModO2 A)) :
    A.relIndex (L ⊓ Subgroup.normalizer (A : Set Γ)) = 2 := by
  classical
  obtain ⟨e, x, y, hxy, hAe⟩ := exists_two_point_stabilizer hL hAL hA
  have hAA : ∀ l : ↥L, (l : Γ) ∈ A ↔
      e l ∈ MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y := fun l => by
    rw [hAe l, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  obtain ⟨g, hgx, hgy⟩ := exists_swap hxy
  set s : ↥L := e.symm g with hs
  have hes : e s = g := e.apply_symm_apply g
  have hsN : (s : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
    refine (mem_normalizer_iff_of_corr e hAL hAA (Subgroup.le_normalizer s.2)
      (intertwine_self e s)).mpr ?_
    rw [hes]
    exact mem_normalizer_stab2_of_perm (Or.inr ⟨hgx, hgy⟩)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨s, Subgroup.mem_inf.mpr ⟨s.2, hsN⟩⟩, fun b => ?_⟩
  obtain ⟨hbL, hbN⟩ := Subgroup.mem_inf.mp b.2
  set l : ↥L := ⟨b, hbL⟩ with hl
  have hmN := (mem_normalizer_iff_of_corr e hAL hAA (Subgroup.le_normalizer hbL)
    (intertwine_self e l)).mp hbN
  have hb : b ∈ A.subgroupOf (L ⊓ Subgroup.normalizer (A : Set Γ)) ↔
      e l • x = x ∧ e l • y = y := by
    rw [Subgroup.mem_subgroupOf]
    exact hAe l
  have hbs : b * ⟨s, Subgroup.mem_inf.mpr ⟨s.2, hsN⟩⟩ ∈
      A.subgroupOf (L ⊓ Subgroup.normalizer (A : Set Γ)) ↔ e l • y = x ∧ e l • x = y := by
    rw [Subgroup.mem_subgroupOf]
    have h := hAe (l * s)
    rw [map_mul, hes, mul_smul, mul_smul, hgx, hgy] at h
    exact h
  rw [hb, hbs]
  rcases fix_or_swap_of_mem_normalizer hxy hmN with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨⟨h1, h2⟩, fun h => hxy (h.1.symm.trans h2)⟩
  · exact Or.inl ⟨⟨h2, h1⟩, fun h => hxy (h.1.symm.trans h1)⟩

end CFSG.Quasithin.H13
