module

public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_pow_mem {K : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ K) (hb : x ^ b ∈ K) : x ∈ K := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [this]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem exists_mem_L₁Of_cube [Finite G] {L V W : Subgroup G} {l : G} (hl : l ∈ L)
    (hlW : l ∈ normalizer (W : Set G)) (hl3 : l ^ 3 ∈ centralizer (V : Set G))
    (hlc : l ∉ centralizer (W : Set G)) (hWV : W ≤ V)
    (hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G))) :
    ∃ e : ℕ, l ^ 2 ^ e ∈ L₁Of L W ∧ (l ^ 2 ^ e) ^ 3 = 1 ∧
      l ^ 2 ^ e ∉ centralizer (W : Set G) := by
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hym : (l ^ 2 ^ e) ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hCVW : centralizer (V : Set G) ≤ centralizer (W : Set G) := Subgroup.centralizer_le hWV
  refine ⟨e, subset_closure ⟨⟨pow_mem hl _, pow_mem hlW _⟩, m, hm, hym⟩, ?_, ?_⟩
  ·
    have hmem : (l ^ 2 ^ e) ^ 3 ∈ L ⊓ centralizer (V : Set G) := by
      refine ⟨pow_mem (pow_mem hl _) _, ?_⟩
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_mem hl3 _
    obtain ⟨k, hk⟩ := hCL ⟨_, hmem⟩
    have hk' : ((l ^ 2 ^ e) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : ((l ^ 2 ^ e) ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    have hcop : Nat.Coprime (2 ^ k) m := (Nat.coprime_two_left.2 hm).pow_left k
    have h1 : orderOf ((l ^ 2 ^ e) ^ 3) ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  · intro h
    exact hlc (mem_of_pow_mem_of_pow_mem (Nat.Coprime.pow_left e (by norm_num : Nat.Coprime 2 3))
      h (hCVW hl3))

theorem center_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hna : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((mem_center_iff.1 (h ▸ mem_top b) a))

theorem o2Z_le_pCoreOf_of_center_eq_bot {L : Subgroup G}
    (hcen : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : A6.o2Z L ≤ pCoreOf 2 L := by
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y' = 1 := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y' ∈ Subgroup.center _ := hy'
    rw [hcen] at this
    exact (mem_bot).1 this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact coe_mem_pCoreOf_iff.2 h1

theorem mem_normalizer_of_forall_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    exact this ▸ hy

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), g ∈ normalizer (K : Set G) →
      ∀ y ∈ ⁅H, K⁆, g * y * g⁻¹ ∈ ⁅H, K⁆ := by
    intro g hH hK y hy
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro h hh k hk
      change g * ⁅h, k⁆ * g⁻¹ ∈ ⁅H, K⁆
      have e : g * ⁅h, k⁆ * g⁻¹ = ⁅g * h * g⁻¹, g * k * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.1 hH h).1 hh)
        ((mem_normalizer_iff.1 hK k).1 hk)
    exact hle hy
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key g hH hK y
  · intro h
    have := key g⁻¹ (inv_mem hH) (inv_mem hK) _ h
    simpa [mul_assoc] using this

theorem X_facts_L₂ {T L V₂ : Subgroup G} (hTL : T ≤ normalizer (L : Set G))
    (hT2 : T ≤ normalizer (V₂ : Set G)) :
    L₁Of L V₂ ≤ L ∧ L₁Of L V₂ ≤ normalizer (V₂ : Set G) ∧
      T ≤ normalizer (L₁Of L V₂ : Set G) ∧ oTwoRes (L₁Of L V₂) = L₁Of L V₂ := by
  refine ⟨(oTwoRes_le _).trans inf_le_left, (oTwoRes_le _).trans inf_le_right, ?_, ?_⟩
  · intro t ht
    exact normalizer_le_normalizer_oTwoRes _ (mem_normalizer_inf (hTL ht) (le_normalizer (hT2 ht)))
  · refine le_antisymm (oTwoRes_le _) ?_
    rw [L₁Of, oTwoRes, closure_le]
    rintro x ⟨hx, m, hm, hxm⟩
    exact subset_closure ⟨subset_closure ⟨hx, m, hm, hxm⟩, m, hm, hxm⟩

theorem X_facts_L₂plus {T L V₂ : Subgroup G} (hTL : T ≤ normalizer (L : Set G))
    (hT2 : T ≤ normalizer (V₂ : Set G)) :
    oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ ≤ L ∧ oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ ≤ normalizer (V₂ : Set G) ∧
      T ≤ normalizer (oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ : Set G) ∧
      oTwoRes (oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆) = oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ := by
  obtain ⟨h1, h2, h3, -⟩ := X_facts_L₂ hTL hT2
  have hle : ⁅L₁Of L V₂, T ⊓ L⁆ ≤ L₁Of L V₂ := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    rw [commutatorElement_def, show x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.1 (h3 ht.1) x⁻¹).1 (inv_mem hx))
  have hTLn : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (le_normalizer ht) (hTL ht)
  refine ⟨(oTwoRes_le _).trans (hle.trans h1), (oTwoRes_le _).trans (hle.trans h2), ?_, ?_⟩
  · intro t ht
    refine normalizer_le_normalizer_oTwoRes _ ?_
    exact mem_normalizer_commutator (h3 ht) (hTLn ht)
  · refine le_antisymm (oTwoRes_le _) ?_
    rw [oTwoRes, closure_le]
    rintro x ⟨hx, m, hm, hxm⟩
    exact subset_closure ⟨subset_closure ⟨hx, m, hm, hxm⟩, m, hm, hxm⟩

theorem core15_of [Finite G] (h1332 : Stmt13_3_2) {T L V V₂ X : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hzv : V ⊓ centralizer (L : Set G) = ⊥)
    (hV2 : A6.IsV2 T V V₂) (hq1 : ¬ pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G))
    (hXL : X ≤ L) (hXN : X ≤ normalizer (V₂ : Set G)) (hXT : T ≤ normalizer (X : Set G))
    (hXres : oTwoRes X = X) (hXact : ∃ x ∈ X, x ^ 3 = 1 ∧ x ∉ centralizer (V₂ : Set G))
    (hXker : IsPGroup 2 ↥(X ⊓ centralizer (V₂ : Set G))) (hXZ : ¬ X ≤ A6.o2Z L)
    (hgen : ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
      Nat.card V₃ = 8 → autOn (X ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V) :
    Core15 G T L V V₂ X := by
  obtain ⟨-, ⟨hTL, -⟩, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, hTV, hfsu, -, -⟩ := hVall V hV
  exact ⟨hH, hV, hzv, hV2, hTL, hTV, hfsu.quasisimple, hq1, hXL, hXN, hXT, hXres, hXact, hXker,
    hXZ, hgen⟩

end CFSG.Quasithin.H13.U3
