module

public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.SeitzReduction.RankOneLemmaS

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open TableB

namespace F4AutRefl

theorem ggIsTransvection_ggExtAut {G : Type} [Group G] {p : ℕ}
    {Bs B₀ C₀ : Subgroup G} (μ : ↥B₀ × ↥C₀ ≃* ↥Bs) {ψ : MulAut ↥B₀}
    (h : GGIsTransvection p ψ) : GGIsTransvection p (ggExtAut μ ψ) := by
  have hfix : Nat.card {b : ↥Bs // ggExtAut μ ψ b = b} =
      Nat.card {b : ↥B₀ // ψ b = b} * Nat.card ↥C₀ := by
    rw [← Nat.card_prod]
    refine (Nat.card_congr (Equiv.subtypeEquiv μ.symm.toEquiv fun b => ?_)).trans
      (Nat.card_congr Equiv.prodSubtypeFstEquivSubtypeProd)
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply,
      ggExtAut_apply]
    constructor
    · intro h
      exact congrArg Prod.fst (μ.injective h)
    · intro h
      rw [h]
  have hcard : Nat.card ↥Bs = Nat.card ↥B₀ * Nat.card ↥C₀ := by
    rw [← Nat.card_prod]
    exact Nat.card_congr μ.toEquiv.symm
  refine ⟨?_, fun b => ?_⟩
  · rw [hfix, hcard, ← h.1]
    ring
  · obtain ⟨q, rfl⟩ := μ.surjective b
    have e1 : (μ q)⁻¹ * ggExtAut μ ψ (μ q) = μ (q.1⁻¹ * ψ q.1, 1) := by
      rw [ggExtAut_apply, ← map_inv, ← map_mul]
      congr 1
      ext <;> simp
    rw [e1, ggExtAut_apply]
    simp only
    rw [h.2 q.1]

theorem ggFramePair_of_quotient {G S : Type} [Group G] [Finite G] [Group S] {p : ℕ}
    (hp : Odd p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹)
    (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    (hcard : Nat.card Bs = p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (f : ↥X →* S) (hf : Function.Surjective f)
    (hker : ∀ x : ↥X, f x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G))
    (hcore : ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E = p ^ 4 →
      ∃ r ∈ ggInduced ⊤ E, ∃ r' ∈ ggInduced ⊤ E, GGIsReflection p r ∧ GGIsReflection p r' ∧
        4 ∣ orderOf (r * r')) :
    ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs, GGIsReflection p c₁ ∧
      GGIsReflection p c₂ ∧ 4 ∣ orderOf (c₁ * c₂) := by
  have hZp : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ p = 1 → z = 1 :=
    fun z hzX hzC hzp =>
      (CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one (hZ2 z hzX hzC) hp).symm.trans hzp
  have hB₀ : IsElemAbelian p (Bs ⊓ X) := hBs.mono inf_le_left
  obtain ⟨μ, hμ⟩ := exists_mulEquiv_prod_of_split (Bs := Bs) (B₀ := Bs ⊓ X)
    (C₀ := Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left inf_le_left
    (fun y hy c hc => hBs.comm hy.1 hc.1) (fun y hy hyC => hZp y hy.2 hyC.2 (hBs.2 y hy.1))
    (exists_mul_split_of_inner hp hBs hSC hinner hZ2)
  have h1 : Nat.card Bs =
      Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr μ.toEquiv.symm
  have hB₀X : Bs ⊓ X ≤ X := inf_le_right
  have hinj : Function.Injective (f.comp (Subgroup.inclusion hB₀X)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hZp _ y.2.2 (hker _ hy) (hB₀.2 _ y.2))
  let e : ↥(Bs ⊓ X) ≃* ↥(f.comp (Subgroup.inclusion hB₀X)).range := MonoidHom.ofInjective hinj
  have he : ∀ b, (e b : S) = f (Subgroup.inclusion hB₀X b) := fun b => rfl
  have hE : IsElemAbelian p (f.comp (Subgroup.inclusion hB₀X)).range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
        show x * y = y * x from Subtype.ext (hB₀.comm x.2 y.2)]
    · obtain ⟨x, rfl⟩ := hz
      rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB₀.2 _ x.2), map_one]
  have hc : Nat.card ↥(Bs ⊓ X) = Nat.card (f.comp (Subgroup.inclusion hB₀X)).range :=
    Nat.card_congr e.toEquiv
  have hEcard : Nat.card (f.comp (Subgroup.inclusion hB₀X)).range = p ^ 4 := by
    rw [← hc]
    rw [h1] at hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  obtain ⟨r, hr, r', hr', hrr, hrr', h4⟩ := hcore _ hE hEcard
  have hA := ggAutomizer_eq_map_ggExtAut μ hμ
  have hA' := ggAutomizer_top_eq_map_congr f hf hB₀X e he
    (mem_normalizer_of_image_mem_normalizer hB₀ hB₀X f hker hZp)
  have hrA : r ∈ ggAutomizer ⊤ (f.comp (Subgroup.inclusion hB₀X)).range :=
    Subgroup.subset_closure hr
  have hr'A : r' ∈ ggAutomizer ⊤ (f.comp (Subgroup.inclusion hB₀X)).range :=
    Subgroup.subset_closure hr'
  rw [hA'] at hrA hr'A
  obtain ⟨ψ, hψ, rfl⟩ := hrA
  obtain ⟨ψ', hψ', rfl⟩ := hr'A
  refine ⟨ggExtAut μ ψ, by rw [hA]; exact ⟨ψ, hψ, rfl⟩, ggExtAut μ ψ',
    by rw [hA]; exact ⟨ψ', hψ', rfl⟩, (ggIsReflection_ggExtAut_iff μ ψ).2
      ((ggIsReflection_congr_iff e ψ).1 hrr), (ggIsReflection_ggExtAut_iff μ ψ').2
      ((ggIsReflection_congr_iff e ψ').1 hrr'), ?_⟩
  have ho := orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective (ψ * ψ')
  rw [← map_mul (ggExtAut μ), orderOf_injective (ggExtAut μ) (ggExtAut_injective μ), ← ho,
    map_mul]
  exact h4

theorem ggRankUpper_of_quotient {G S : Type} [Group G] [Group S] {p : ℕ}
    (hp : Odd p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹)
    (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    (f : ↥X →* S) (hker : ∀ x : ↥X, f x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G))
    (hrk : ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E ≤ p ^ 4) :
    Nat.card Bs ≤ p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  have hZp : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ p = 1 → z = 1 :=
    fun z hzX hzC hzp =>
      (CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one (hZ2 z hzX hzC) hp).symm.trans hzp
  have hB₀ : IsElemAbelian p (Bs ⊓ X) := hBs.mono inf_le_left
  obtain ⟨μ, -⟩ := exists_mulEquiv_prod_of_split (Bs := Bs) (B₀ := Bs ⊓ X)
    (C₀ := Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left inf_le_left
    (fun y hy c hc => hBs.comm hy.1 hc.1) (fun y hy hyC => hZp y hy.2 hyC.2 (hBs.2 y hy.1))
    (exists_mul_split_of_inner hp hBs hSC hinner hZ2)
  have h1 : Nat.card Bs =
      Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr μ.toEquiv.symm
  have hB₀X : Bs ⊓ X ≤ X := inf_le_right
  have hinj : Function.Injective (f.comp (Subgroup.inclusion hB₀X)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hZp _ y.2.2 (hker _ hy) (hB₀.2 _ y.2))
  let e : ↥(Bs ⊓ X) ≃* ↥(f.comp (Subgroup.inclusion hB₀X)).range := MonoidHom.ofInjective hinj
  have hE : IsElemAbelian p (f.comp (Subgroup.inclusion hB₀X)).range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
        show x * y = y * x from Subtype.ext (hB₀.comm x.2 y.2)]
    · obtain ⟨x, rfl⟩ := hz
      rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB₀.2 _ x.2), map_one]
  have hc : Nat.card ↥(Bs ⊓ X) = Nat.card (f.comp (Subgroup.inclusion hB₀X)).range :=
    Nat.card_congr e.toEquiv
  rw [h1, hc]
  exact Nat.mul_le_mul_right _ (hrk _ hE)

theorem ggRankLower_of_quotient {G S : Type} [Group G] [Finite G] [Group S] {p : ℕ}
    (hpp : p.Prime) (hp : Odd p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹)
    (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    (f : ↥X →* S) (hf : Function.Surjective f)
    (hker : ∀ x : ↥X, f x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G))
    (hT : GGNoTransvection p Bs)
    (hcore : ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E ≤ p ^ 3 →
      (∀ g ∈ Subgroup.centralizer (E : Set S), g ^ p = 1 → g ∈ E) →
        ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection p φ) :
    p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card Bs := by
  have hsq : ∀ {y : G}, y ^ 2 = 1 → y ^ p = y :=
    fun hy => CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one hy hp
  have hZp : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ p = 1 → z = 1 :=
    fun z hzX hzC hzp => (hsq (hZ2 z hzX hzC)).symm.trans hzp
  have hB₀ : IsElemAbelian p (Bs ⊓ X) := hBs.mono inf_le_left
  obtain ⟨μ, hμ⟩ := exists_mulEquiv_prod_of_split (Bs := Bs) (B₀ := Bs ⊓ X)
    (C₀ := Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left inf_le_left
    (fun y hy c hc => hBs.comm hy.1 hc.1) (fun y hy hyC => hZp y hy.2 hyC.2 (hBs.2 y hy.1))
    (exists_mul_split_of_inner hp hBs hSC hinner hZ2)
  have h1 : Nat.card Bs =
      Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr μ.toEquiv.symm
  have hB₀X : Bs ⊓ X ≤ X := inf_le_right
  have hinj : Function.Injective (f.comp (Subgroup.inclusion hB₀X)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hZp _ y.2.2 (hker _ hy) (hB₀.2 _ y.2))
  let e : ↥(Bs ⊓ X) ≃* ↥(f.comp (Subgroup.inclusion hB₀X)).range := MonoidHom.ofInjective hinj
  have he : ∀ b, (e b : S) = f (Subgroup.inclusion hB₀X b) := fun b => rfl
  have hE : IsElemAbelian p (f.comp (Subgroup.inclusion hB₀X)).range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
        show x * y = y * x from Subtype.ext (hB₀.comm x.2 y.2)]
    · obtain ⟨x, rfl⟩ := hz
      rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB₀.2 _ x.2), map_one]
  have hc : Nat.card ↥(Bs ⊓ X) = Nat.card (f.comp (Subgroup.inclusion hB₀X)).range :=
    Nat.card_congr e.toEquiv
  have hA := ggAutomizer_eq_map_ggExtAut μ hμ
  have hA' := ggAutomizer_top_eq_map_congr f hf hB₀X e he
    (mem_normalizer_of_image_mem_normalizer hB₀ hB₀X f hker hZp)
  rw [h1, hc]
  refine Nat.mul_le_mul_right _ ?_
  by_contra hlt
  push Not at hlt
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Finite (f.comp (Subgroup.inclusion hB₀X)).range :=
    Nat.finite_of_card_ne_zero (by rw [← hc]; exact Nat.card_pos.ne')
  have hE3 : Nat.card (f.comp (Subgroup.inclusion hB₀X)).range ≤ p ^ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hE.isPGroup
    rw [hk] at hlt ⊢
    have : k < 4 := (Nat.pow_lt_pow_iff_right hpp.one_lt).1 hlt
    exact Nat.pow_le_pow_right hpp.pos (by omega)
  have hSCE : ∀ s ∈ Subgroup.centralizer
      ((f.comp (Subgroup.inclusion hB₀X)).range : Set S), s ^ p = 1 →
        s ∈ (f.comp (Subgroup.inclusion hB₀X)).range := by
    intro s hs hsp
    obtain ⟨x, rfl⟩ := hf s
    have hxpC : ((x ^ p : ↥X) : G) ∈ Subgroup.centralizer (X : Set G) :=
      hker _ (by rw [map_pow, hsp])
    have hzp : (x ^ p) ^ p = x ^ p := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hsq (hZ2 _ (x ^ p).2 hxpC))
    obtain ⟨y, hyd⟩ : ∃ y : ↥X, y = x * (x ^ p)⁻¹ := ⟨_, rfl⟩
    have hyp : y ^ p = 1 := by
      rw [hyd, ((Commute.self_pow x p).inv_right).mul_pow, inv_pow, hzp, mul_inv_cancel]
    have hfy : f y = f x := by
      rw [hyd, map_mul, map_inv, map_pow, hsp, inv_one, mul_one]
    have hcen : ∀ w : ↥X, (w : G) ∈ Subgroup.centralizer (X : Set G) → ∀ z : ↥X, z * w = w * z :=
      fun w hw z => Subtype.ext (Subgroup.mem_centralizer_iff.mp hw z z.2)
    have hyB₀ : ∀ h ∈ Bs ⊓ X, h * (y : G) = y * h := by
      intro h hh
      set hX : ↥X := ⟨h, hh.2⟩ with hhX
      have hmemE : f hX ∈ (f.comp (Subgroup.inclusion hB₀X)).range := ⟨⟨h, hh⟩, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hs (f hX) hmemE
      have hfw : f (hX⁻¹ * (y * hX * y⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hfy, ← hcomm]
        group
      obtain ⟨w, hwd⟩ : ∃ w : ↥X, w = hX⁻¹ * (y * hX * y⁻¹) := ⟨_, rfl⟩
      rw [← hwd] at hfw
      have hwC := hker w hfw
      have hyw : y * hX * y⁻¹ = hX * w := by rw [hwd]; group
      have hiter : ∀ k : ℕ, y ^ k * hX * (y ^ k)⁻¹ = hX * w ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hwk : y * w ^ k * y⁻¹ = w ^ k := by
            rw [(Commute.pow_right (hcen w hwC y) k).eq, mul_inv_cancel_right]
          calc y ^ (k + 1) * hX * (y ^ (k + 1))⁻¹ = y * (y ^ k * hX * (y ^ k)⁻¹) * y⁻¹ := by
                group
            _ = (y * hX * y⁻¹) * (y * w ^ k * y⁻¹) := by rw [ih]; group
            _ = hX * w ^ (k + 1) := by rw [hyw, hwk, pow_succ']; group
      have hwp : w ^ p = 1 := by
        have h2 := hiter p
        rw [hyp, one_mul, inv_one, mul_one] at h2
        exact (mul_eq_left.mp h2.symm)
      have hw2 : w ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZ2 _ w.2 hwC)
      have hw1 : w = 1 :=
        (CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one hw2 hp).symm.trans hwp
      rw [hw1, mul_one] at hyw
      have h3 := congrArg Subtype.val hyw
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhX] at h3
      calc h * (y : G) = (y * h * (y : G)⁻¹) * y := by rw [h3]
        _ = y * h := by group
    have hyC : (y : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨h, hh, c, hcC, rfl⟩ := exists_mul_split_of_inner hp hBs hSC hinner hZ2 b hb
      have hyc : c * (y : G) = y * c := (Subgroup.mem_centralizer_iff.mp hcC.2 y y.2).symm
      calc h * c * (y : G) = h * (y * c) := by rw [mul_assoc, hyc]
        _ = (h * y) * c := by group
        _ = (y * h) * c := by rw [hyB₀ h hh]
        _ = y * (h * c) := by group
    have hyBs : (y : G) ∈ Bs := hSC _ hyC (by rw [← Subgroup.coe_pow, hyp]; rfl)
    exact ⟨⟨y, hyBs, y.2⟩, hfy⟩
  obtain ⟨φ, hφ, hφT⟩ := hcore _ hE hE3 hSCE
  have hφA : φ ∈ ggAutomizer ⊤ (f.comp (Subgroup.inclusion hB₀X)).range :=
    Subgroup.subset_closure hφ
  rw [hA'] at hφA
  obtain ⟨ψ, hψ, rfl⟩ := hφA
  have hψT : GGIsTransvection p ψ :=
    GGIsTransvection.of_mulEquiv e.symm (fun x => by simp [MulAut.congr_apply]) hφT
  have hmem : ggExtAut μ ψ ∈ ggAutomizer X Bs := by rw [hA]; exact ⟨ψ, hψ, rfl⟩
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hmem
  exact hT _ ⟨g, Subgroup.mem_top g, hgN, hg⟩ (ggIsTransvection_ggExtAut μ hψT)

end F4AutRefl

end CFSG.StandardType
