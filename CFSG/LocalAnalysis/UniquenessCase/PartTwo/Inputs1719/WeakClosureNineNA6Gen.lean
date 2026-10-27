module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6

open CFSG.Quasithin CFSG.Open Subgroup

structure ModelFacts {Y : Type} [Group Y] (G L₀ T₀ : Subgroup Y) : Prop where
  T₀_le : T₀ ≤ G
  L₀_le : L₀ ≤ G
  sylow : IsSylowIn 2 T₀ G
  sup_eq : L₀ ⊔ T₀ = G
  normal : ∀ g ∈ G, ∀ x ∈ L₀, g * x * g⁻¹ ∈ L₀
  three_dvd : 3 ∣ Nat.card L₀
  le_of_normal : ∀ K : Subgroup Y, K ≤ G → (∀ g ∈ G, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K ≠ ⊥ →
    L₀ ≤ K
  cent : ∀ g ∈ G, (∀ x ∈ L₀, g * x = x * g) → g = 1
  sq_mem : ∀ x ∈ G, x * x ∈ L₀
  pair : ∀ x ∈ T₀, orderOf x = 2 → ∃ m ∈ G, ∃ n ∈ G, m * x * m⁻¹ ∈ T₀ ∧ n * x * n⁻¹ ∈ T₀ ∧
    (m * x * m⁻¹) * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * (m * x * m⁻¹)
  table : ∀ A : Subgroup Y, A ≤ T₀ → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    ∃ (K Z : Subgroup Y) (p : ℕ), K ≤ G ∧ A ≤ K ∧ TwoPTwo K (K ⊓ T₀) Z p ∧ Nat.card Z = p ∧
      CFSG.Quasithin.coreIn (T₀ ⊓ centralizer (A : Set Y)) T₀ ≤ K ⊓ T₀ ∧
      (∀ R : Subgroup Y, A ≤ R → R ≤ K ⊓ T₀ →
        ¬ K ⊔ (T₀ ⊓ normalizer ((K ⊓ T₀ : Subgroup Y) : Set Y)) ≤ normalizer (R : Set Y)) ∧
      (p = 3 ∨ ∀ H : Subgroup Y, T₀ ≤ H → H ≤ G → H = T₀ ∨ H = G)
  close : ∀ E : Subgroup Y, E ≤ T₀ → T₀ ≤ normalizer (E : Set Y) → IsElemAbelian 2 E →
    4 ≤ Nat.card E → ∃ K Z : Subgroup Y, K ≤ G ∧ TwoPTwo K (K ⊓ T₀) Z 3 ∧ Nat.card Z = 3 ∧
      E ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (E : Set Y) ≤ K ∧ K ⊔ T₀ = G

section Transport

variable {X Y : Type} [Group X] [Group Y] {ι : X →* Y}

theorem mem_normalizer_map {R : Subgroup X} {k : X}
    (hk : k ∈ normalizer (R : Set X)) : ι k ∈ normalizer ((R.map ι : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff] at hk ⊢
  intro y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨k * r * k⁻¹, (hk r).mp hr, by simp [map_mul, map_inv]⟩
  · rintro ⟨r, hr, hry⟩
    refine ⟨k⁻¹ * r * k, (hk _).mpr (by simpa [mul_assoc] using hr), ?_⟩
    rw [map_mul, map_mul, map_inv, hry]
    group

theorem mem_normalizer_of_map (hι : Function.Injective ι) {H : Subgroup X} {t : X}
    (ht : ι t ∈ normalizer ((H.map ι : Subgroup Y) : Set Y)) : t ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff] at ht ⊢
  intro h
  rw [← mem_map_iff_mem hι (K := H), ← mem_map_iff_mem hι (K := H) (x := t * h * t⁻¹),
    map_mul, map_mul, map_inv]
  exact ht (ι h)

theorem isSylowIn_of_map (hι : Function.Injective ι) {p : ℕ} {P H : Subgroup X}
    (h : IsSylowIn p (P.map ι) (H.map ι)) : IsSylowIn p P H :=
  ⟨(map_le_map_iff_of_injective hι).mp h.le,
    h.isPGroup.of_equiv (P.equivMapOfInjective ι hι).symm,
    by rw [← relIndex_map_map_of_injective P H hι]; exact h.not_dvd_relIndex⟩

theorem twoPTwo_of_map (hι : Function.Injective ι) {K S Z : Subgroup X} {p : ℕ}
    (h : TwoPTwo (K.map ι) (S.map ι) (Z.map ι) p) : TwoPTwo K S Z p where
  prime := h.prime
  odd := h.odd
  oTwoPTwo := by
    set e := K.equivMapOfInjective ι hι
    have h1 := CFSG.Quasithin.E1.oTwoPTwo_map_mulEquiv e p
    rw [h.oTwoPTwo] at h1
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ (CFSG.Quasithin.E1.oTwoPTwo ↥K p).map e.toMonoidHom := h1 ▸ mem_top _
    rw [mem_map_equiv] at hx
    simpa using hx
  sylowTwo := isSylowIn_of_map hι h.sylowTwo
  sylowP := isSylowIn_of_map hι h.sylowP

theorem pCoreOf_map (hι : Function.Injective ι) (p : ℕ) (K : Subgroup X) :
    (pCoreOf p K).map ι = pCoreOf p (K.map ι) := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p (K.equivMapOfInjective ι hι),
    map_map, map_map]
  rfl

end Transport

theorem irred_of_prime_card {G : Type} [Group G] {S Z : Subgroup G} (hZ : (Nat.card Z).Prime) :
    IrredOnFrattiniQuot S Z := by
  have : Fact (Nat.card Z).Prime := ⟨hZ⟩
  have hne : Z ≠ ⊥ := by
    rintro rfl
    simp at hZ
    exact Nat.not_prime_one hZ
  have hfr : nineFrattini Z = ⊥ := by
    unfold nineFrattini
    have hco : IsCoatom (⊥ : Subgroup Z) := by
      refine ⟨?_, fun H hH => ?_⟩
      · intro h
        have h1 : Nat.card (⊤ : Subgroup Z) = 1 := by rw [← h, card_bot]
        rw [card_top] at h1
        exact hZ.one_lt.ne' h1
      · rcases eq_bot_or_eq_top_of_prime_card H with h | h
        · exact absurd h hH.ne'
        · exact h
    rw [eq_bot_iff.mpr (frattini_le_coatom hco), Subgroup.map_bot]
  refine ⟨?_, fun W _ hW2 _ => ?_⟩
  · rw [hfr]
    exact bot_lt_iff_ne_bot.mpr hne
  · rw [hfr]
    have hfin : Finite Z := Nat.finite_of_card_ne_zero hZ.ne_zero
    have hd : Nat.card W ∣ Nat.card Z := card_dvd_of_le hW2
    rcases (Nat.dvd_prime hZ).mp hd with h | h
    · exact Or.inl (eq_bot_of_card_eq W h)
    · exact Or.inr (eq_of_le_of_card_ge hW2 h.ge)

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem exists_eq_map_conj {P Q : Subgroup X} (hP : IsSylowIn 2 P ⊤) (hQ : IsSylowIn 2 Q ⊤) :
    ∃ g : X, P = Q.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : ¬ 2 ∣ P.index := by rw [← relIndex_top_right]; exact hP.not_dvd_relIndex
  have hQ' : ¬ 2 ∣ Q.index := by rw [← relIndex_top_right]; exact hQ.not_dvd_relIndex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hQ.isPGroup.toSylow hQ') (hP.isPGroup.toSylow hP')
  refine ⟨g, ?_⟩
  have h1 : ((g • hQ.isPGroup.toSylow hQ' : Sylow 2 X) : Subgroup X) = P := by
    rw [hg, IsPGroup.toSylow_coe]
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
  ext x
  rw [← h1, mem_smul_pointwise_iff_exists, mem_map]
  simp [MulAut.smul_def]

theorem exists_conj_mem {T : Subgroup X} (hT : IsSylowIn 2 T ⊤) {x : X}
    (hx : IsPGroup 2 (zpowers x)) : ∃ g : X, g⁻¹ * x * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hxS⟩ := exists_isSylowIn_ge 2 le_top hx
  obtain ⟨g, rfl⟩ := exists_eq_map_conj hS hT
  obtain ⟨t, ht, htx⟩ := hxS (mem_zpowers x)
  refine ⟨g, ?_⟩
  rw [← htx]
  simpa [MulAut.conj_apply, mul_assoc] using ht

end Sylow

section Reduction

variable {X Y : Type} [Group X] [Group Y]

theorem ModelFacts.commutator_mem {G L₀ T₀ : Subgroup Y} (hM : ModelFacts G L₀ T₀) {x y : Y}
    (hx : x ∈ G) (hy : y ∈ G) : x * y * x⁻¹ * y⁻¹ ∈ L₀ := by
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ := by
    group
  rw [e]
  refine L₀.mul_mem (L₀.mul_mem (hM.sq_mem _ (G.mul_mem hx hy)) ?_)
    (L₀.inv_mem (hM.sq_mem _ hy))
  exact hM.normal _ (G.inv_mem hy) _ (L₀.inv_mem (hM.sq_mem _ hx))

end Reduction

end CFSG.LocalAnalysis.WeakClosure81.NFA6
