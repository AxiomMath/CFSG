module

public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion
public import CFSG.GH74.ThompsonOrderFormula

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Finite G] {K : Type*} [Group K]

theorem fusion_transfer {T M₁ M₂ : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hT₁ : T ≤ M₁)
    (hT₂ : T ≤ M₂)
    (hAG : ∀ D : Subgroup G, IsAGMember T D →
      Subgroup.normalizer (D : Set G) ≤ M₁ ∨ Subgroup.normalizer (D : Set G) ≤ M₂)
    (φ : G → K) (H : Subgroup K)
    (hφ₁ : ∀ a ∈ M₁, ∀ b ∈ M₁, φ (a * b) = φ a * φ b)
    (hφ₂ : ∀ a ∈ M₂, ∀ b ∈ M₂, φ (a * b) = φ a * φ b)
    (hH₁ : ∀ a ∈ M₁, φ a ∈ H) (hH₂ : ∀ a ∈ M₂, φ a ∈ H)
    {x : G} (hx : x ∈ T) {g : G} (hg : g⁻¹ * x * g ∈ T) :
    ∃ k ∈ H, k⁻¹ * φ x * k = φ (g⁻¹ * x * g) := by
  have hone : φ 1 = 1 := by
    have h11 : φ 1 * φ 1 = φ 1 := by rw [← hφ₁ 1 M₁.one_mem 1 M₁.one_mem, mul_one]
    simpa using h11
  have hinv₁ : ∀ a ∈ M₁, φ a⁻¹ = (φ a)⁻¹ := fun a ha => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hφ₁ _ (M₁.inv_mem ha) _ ha, inv_mul_cancel, hone]
  have hinv₂ : ∀ a ∈ M₂, φ a⁻¹ = (φ a)⁻¹ := fun a ha => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hφ₂ _ (M₂.inv_mem ha) _ ha, inv_mul_cancel, hone]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {P : Subgroup G} {c : G}, AlperinDecomposition 2 T P c →
      ∀ y ∈ P, ∃ k ∈ H, k⁻¹ * φ y * k = φ (c⁻¹ * y * c) := by
    intro P c hc
    induction hc with
    | one => intro y hy; exact ⟨1, H.one_mem, by simp⟩
    | @step c n Q hc' hQ hPQ hn ih =>
      intro y hy
      obtain ⟨k, hk, hkeq⟩ := ih y hy
      have hy'Q : c⁻¹ * y * c ∈ Q := hPQ ⟨y, hy, by simp⟩
      have hconj : (c * n)⁻¹ * y * (c * n) = n⁻¹ * (c⁻¹ * y * c) * n := by group
      rw [hconj]
      have step_j : ∀ (Mj : Subgroup G), (∀ a ∈ Mj, ∀ b ∈ Mj, φ (a * b) = φ a * φ b) →
          (∀ a ∈ Mj, φ a⁻¹ = (φ a)⁻¹) → (∀ a ∈ Mj, φ a ∈ H) → T ≤ Mj → n ∈ Mj →
          ∃ k' ∈ H, k'⁻¹ * φ y * k' = φ (n⁻¹ * (c⁻¹ * y * c) * n) := by
        intro Mj hφ hinv hH' hTj hnj
        have hy'M : c⁻¹ * y * c ∈ Mj := hTj (hQ.1 hy'Q)
        refine ⟨k * φ n, H.mul_mem hk (hH' n hnj), ?_⟩
        calc (k * φ n)⁻¹ * φ y * (k * φ n) = (φ n)⁻¹ * (k⁻¹ * φ y * k) * φ n := by group
          _ = (φ n)⁻¹ * φ (c⁻¹ * y * c) * φ n := by rw [hkeq]
          _ = φ (n⁻¹ * (c⁻¹ * y * c) * n) := by
            rw [hφ _ (Mj.mul_mem (Mj.inv_mem hnj) hy'M) n hnj, hφ _ (Mj.inv_mem hnj) _ hy'M,
              hinv n hnj]
      by_cases hQ1 : Q = ⊥
      · rw [hQ1, Subgroup.mem_bot] at hy'Q
        have hy1 : y = 1 := by
          have : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
          rw [hy'Q] at this
          simpa using this
        subst hy1
        refine ⟨1, H.one_mem, ?_⟩
        simp [hone]
      · rcases hAG Q (isAGMember_of_isAlperinSubgroup hT hQ hQ1) with h | h
        · exact step_j M₁ hφ₁ hinv₁ hH₁ hT₁ (h hn)
        · exact step_j M₂ hφ₂ hinv₂ hH₂ hT₂ (h hn)
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 G := hT.2.1.toSylow hT2
  have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
  have hg' : g⁻¹ * x * g ∈ (S : Subgroup G) := hg
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg')
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  obtain ⟨k, hk, hkeq⟩ := key hc x (Subgroup.mem_zpowers x)
  exact ⟨k, hk, by rw [hkeq, hcg x (Subgroup.mem_zpowers x)]⟩

section Thompson

open CFSG.GH74 CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']

theorem thompsonPairCount_eq_of_hom {t u : G} {t' u' : G'} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : ¬ IsConj t u) (hcl : ∀ x : G, orderOf x = 2 → IsConj t x ∨ IsConj u x)
    (ht' : orderOf t' = 2) (hu' : orderOf u' = 2) (htu' : ¬ IsConj t' u')
    (hcl' : ∀ x : G', orderOf x = 2 → IsConj t' x ∨ IsConj u' x)
    {w : G} (hw : w = t ∨ w = u) {w' : G'} (hw' : w' = t' ∨ w' = u')
    (ψ : Subgroup.centralizer ({w} : Set G) →* G') (hψ : Function.Injective ψ)
    (hψr : ψ.range = Subgroup.centralizer ({w'} : Set G'))
    (hψw : ∀ hmem : w ∈ Subgroup.centralizer ({w} : Set G), ψ ⟨w, hmem⟩ = w')
    (hψc : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
      (IsConj t (x : G) ↔ IsConj t' (ψ x))) :
    thompsonPairCount t u w = thompsonPairCount t' u' w' := by
  have hG := (thompson_two_involution_class_order_formula ht hu htu hcl).2 w hw
  have hG' := (thompson_two_involution_class_order_formula ht' hu' htu' hcl').2 w' hw'
  have hordψ : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (ψ x) = orderOf (x : G) := by
    intro x
    rw [orderOf_injective ψ hψ x, Subgroup.orderOf_coe]
  have hcls : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
      (IsConj u (x : G) ↔ IsConj u' (ψ x)) := by
    intro x hx
    have hx' : orderOf (ψ x) = 2 := by rw [hordψ]; exact hx
    constructor
    · intro h
      rcases hcl' (ψ x) hx' with h' | h'
      · exact absurd (((hψc x hx).mpr h').trans h.symm) htu
      · exact h'
    · intro h'
      rcases hcl (x : G) hx with h | h
      · exact absurd (((hψc x hx).mp h).trans h'.symm) htu'
      · exact h
  let f : thompsonPairs t u w → thompsonPairs t' u' w' := fun p =>
    ⟨(ψ ⟨p.1.1, (hG p.1 p.2).1⟩, ψ ⟨p.1.2, (hG p.1 p.2).2⟩), by
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 p.2
      have o1 : orderOf p.1.1 = 2 := by rw [← orderOf_eq_of_isConj h1]; exact ht
      have o2 : orderOf p.1.2 = 2 := by rw [← orderOf_eq_of_isConj h2]; exact hu
      refine mem_thompsonPairs.2 ⟨(hψc ⟨p.1.1, _⟩ o1).mp h1, (hcls ⟨p.1.2, _⟩ o2).mp h2, ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have hab : (⟨p.1.1, (hG p.1 p.2).1⟩ * ⟨p.1.2, (hG p.1 p.2).2⟩ :
          Subgroup.centralizer ({w} : Set G)) ^ k = ⟨w, by
            rw [Subgroup.mem_centralizer_singleton_iff]⟩ :=
        Subtype.ext hk
      rw [← hψw (by rw [Subgroup.mem_centralizer_singleton_iff]), ← hab, map_zpow, map_mul]⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · have h := congrArg Subtype.val hpq
      simp only [f, Prod.mk.injEq] at h
      have e1 := hψ h.1
      have e2 := hψ h.2
      exact Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2))
    · obtain ⟨q, hq⟩ := q
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 hq
      obtain ⟨hq1, hq2⟩ := hG' q hq
      have hq1' : q.1 ∈ ψ.range := by rw [hψr]; exact hq1
      have hq2' : q.2 ∈ ψ.range := by rw [hψr]; exact hq2
      obtain ⟨a, ha⟩ := hq1'
      obtain ⟨b, hb⟩ := hq2'
      have o1 : orderOf (ψ a) = 2 := by rw [ha, ← orderOf_eq_of_isConj h1]; exact ht'
      have o2 : orderOf (ψ b) = 2 := by rw [hb, ← orderOf_eq_of_isConj h2]; exact hu'
      have oa : orderOf (a : G) = 2 := by rw [← hordψ]; exact o1
      have ob : orderOf (b : G) = 2 := by rw [← hordψ]; exact o2
      have hconj1 : IsConj t (a : G) := (hψc a oa).mpr (by rw [ha]; exact h1)
      have hconj2 : IsConj u (b : G) := (hcls b ob).mpr (by rw [hb]; exact h2)
      have hmem : ((a : G), (b : G)) ∈ thompsonPairs t u w := by
        refine mem_thompsonPairs.2 ⟨hconj1, hconj2, ?_⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have hw0 : w ∈ Subgroup.centralizer ({w} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
        have : ψ ((a * b) ^ k) = ψ ⟨w, hw0⟩ := by
          rw [hψw hw0, map_zpow, map_mul, ha, hb]
          exact hk
        have := hψ this
        exact congrArg Subtype.val this
      refine ⟨⟨((a : G), (b : G)), hmem⟩, ?_⟩
      apply Subtype.ext
      simp only [f]
      exact Prod.ext ha hb
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem card_eq_of_two_class_data {t u : G} {t' u' : G'} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : ¬ IsConj t u) (hcl : ∀ x : G, orderOf x = 2 → IsConj t x ∨ IsConj u x)
    (ht' : orderOf t' = 2) (hu' : orderOf u' = 2) (htu' : ¬ IsConj t' u')
    (hcl' : ∀ x : G', orderOf x = 2 → IsConj t' x ∨ IsConj u' x)
    (φt : Subgroup.centralizer ({t} : Set G) →* G') (hφt : Function.Injective φt)
    (hφtr : φt.range = Subgroup.centralizer ({t'} : Set G'))
    (hφtt : ∀ h : t ∈ Subgroup.centralizer ({t} : Set G), φt ⟨t, h⟩ = t')
    (hφtc : ∀ x : Subgroup.centralizer ({t} : Set G), orderOf (x : G) = 2 →
      (IsConj t (x : G) ↔ IsConj t' (φt x)))
    (φu : Subgroup.centralizer ({u} : Set G) →* G') (hφu : Function.Injective φu)
    (hφur : φu.range = Subgroup.centralizer ({u'} : Set G'))
    (hφuu : ∀ h : u ∈ Subgroup.centralizer ({u} : Set G), φu ⟨u, h⟩ = u')
    (hφuc : ∀ x : Subgroup.centralizer ({u} : Set G), orderOf (x : G) = 2 →
      (IsConj t (x : G) ↔ IsConj t' (φu x))) :
    Nat.card G = Nat.card G' := by
  obtain ⟨hcard, -⟩ := thompson_two_involution_class_order_formula ht hu htu hcl
  obtain ⟨hcard', -⟩ := thompson_two_involution_class_order_formula ht' hu' htu' hcl'
  have e1 : Nat.card (Subgroup.centralizer ({u} : Set G)) =
      Nat.card (Subgroup.centralizer ({u'} : Set G')) := by
    have := Nat.card_congr (MonoidHom.ofInjective hφu).toEquiv
    rwa [hφur] at this
  have e2 : Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Nat.card (Subgroup.centralizer ({t'} : Set G')) := by
    have := Nat.card_congr (MonoidHom.ofInjective hφt).toEquiv
    rwa [hφtr] at this
  have r1 := thompsonPairCount_eq_of_hom ht hu htu hcl ht' hu' htu' hcl' (w := t) (Or.inl rfl)
    (w' := t') (Or.inl rfl) φt hφt hφtr hφtt hφtc
  have r2 := thompsonPairCount_eq_of_hom ht hu htu hcl ht' hu' htu' hcl' (w := u) (Or.inr rfl)
    (w' := u') (Or.inr rfl) φu hφu hφur hφuu hφuc
  rw [hcard, hcard', e1, e2, r1, r2]

end Thompson

end CFSG.Quasithin
