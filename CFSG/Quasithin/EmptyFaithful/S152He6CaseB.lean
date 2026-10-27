module

public import CFSG.Quasithin.EmptyFaithful.S152He6Core
public import CFSG.Quasithin.EmptyFaithful.S152He3Chief

public section

namespace CFSG.Quasithin.He6

open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

@[expose] def FamPSL (G : Type*) [Group G] : Prop :=
  (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ Nonempty (G ≃* PSL(2, ZMod p)))

@[expose] def FamPSLne7 (G : Type*) [Group G] : Prop :=
  (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Nonempty (G ≃* PSL(2, ZMod p)))

@[expose] def AutL2SylowInner : Prop :=
  ∀ (G : Type) [Group G], FamPSL G → ∀ α : MulAut G,
    (∃ S : Sylow 2 G, ∀ s ∈ (S : Subgroup G), α s = s) → ∃ l : G, ∀ g : G, α g = l * g * l⁻¹

section Basic

variable {W : Type} [CommGroup W]

@[expose] def conjAutOn (A : Subgroup (MulAut W)) (z : MulAut W)
    (h : ∀ x, x ∈ A ↔ z * x * z⁻¹ ∈ A) : MulAut ↥A where
  toFun x := ⟨z * x * z⁻¹, (h x).1 x.2⟩
  invFun x := ⟨z⁻¹ * x * z, by
    have := (h (z⁻¹ * (x : MulAut W) * z)).2
    have e : z * (z⁻¹ * (x : MulAut W) * z) * z⁻¹ = x := by group
    rw [e] at this
    exact this x.2⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by
    show z * ((x : MulAut W) * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹)
    group)

theorem eq_one_of_central {A : Subgroup (MulAut W)} (hA : IsSimpleGroup ↥A) (hp : ⁅A, A⁆ = A)
    {a : MulAut W} (ha : a ∈ A) (hc : ∀ x ∈ A, a * x = x * a) : a = 1 := by
  let N : Subgroup (MulAut W) :=
    { carrier := {a | a ∈ A ∧ ∀ x ∈ A, a * x = x * a}
      one_mem' := ⟨A.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
        refine ⟨A.mul_mem haA hbA, fun x hx => ?_⟩
        calc a * b * x = a * (b * x) := by group
          _ = a * (x * b) := by rw [hb x hx]
          _ = (a * x) * b := by group
          _ = (x * a) * b := by rw [ha x hx]
          _ = x * (a * b) := by group
      inv_mem' := by
        rintro a ⟨haA, ha⟩
        refine ⟨A.inv_mem haA, fun x hx => ?_⟩
        have := ha x hx
        calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * x) * a⁻¹ := by rw [this]
          _ = x * a⁻¹ := by group }
  have hNA : N ≤ A := fun a ha => ha.1
  have hNn : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have : g * n * g⁻¹ = n := by
      have := hn.2 g hg
      calc g * n * g⁻¹ = (g * n) * g⁻¹ := rfl
        _ = (n * g) * g⁻¹ := by rw [← this]
        _ = n := by group
    rw [this]
    exact hn
  rcases eq_bot_or_eq_of_normal hA hNA hNn with h | h
  · have haN : a ∈ N := ⟨ha, hc⟩
    rw [h, Subgroup.mem_bot] at haN
    exact haN
  · exfalso
    have hab : ⁅A, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_def]
      have hxN : x ∈ N := by rw [h]; exact hx
      have := hxN.2 y hy
      rw [this]
      group
    exact ne_bot_of_simple hA (hp.symm.trans hab)

end Basic

namespace PairData

variable {W : Type} [CommGroup W] [Finite W] (P : PairData W)

omit [Finite W] in
theorem central_eq_one {k : MulAut W} (hk : k ∈ P.A ⊔ P.A')
    (hc : ∀ k' ∈ P.A ⊔ P.A', k * k' = k' * k) : k = 1 := by
  obtain ⟨a, ha, a', ha', rfl⟩ := mem_sup_of_commute P.comm hk
  have hA : a = 1 := by
    refine eq_one_of_central P.simpA P.perfA ha fun x hx => ?_
    have h1 := hc x (Subgroup.mem_sup_left hx)
    have h2 := P.comm x hx a' ha'
    calc a * x = a * x * a' * a'⁻¹ := by group
      _ = a * (x * a') * a'⁻¹ := by group
      _ = a * (a' * x) * a'⁻¹ := by rw [h2]
      _ = (a * a') * x * a'⁻¹ := by group
      _ = x * (a * a') * a'⁻¹ := by rw [h1]
      _ = x * a * (a' * a'⁻¹) := by group
      _ = x * a := by group
  have hA' : a' = 1 := by
    refine eq_one_of_central P.simpA' P.perfA' ha' fun x hx => ?_
    have h1 := hc x (Subgroup.mem_sup_right hx)
    have h2 := P.comm a ha x hx
    calc a' * x = a⁻¹ * a * a' * x := by group
      _ = a⁻¹ * ((a * a') * x) := by group
      _ = a⁻¹ * (x * (a * a')) := by rw [h1]
      _ = a⁻¹ * (x * a) * a' := by group
      _ = a⁻¹ * (a * x) * a' := by rw [← h2]
      _ = x * a' := by group
  rw [hA, hA']
  group

omit [Finite W] in
theorem sup_normal {x : MulAut W} (hx : x ∈ P.Xb) {k : MulAut W} (hk : k ∈ P.A ⊔ P.A') :
    x * k * x⁻¹ ∈ P.A ⊔ P.A' := by
  obtain ⟨a, ha, a', ha', rfl⟩ := mem_sup_of_commute P.comm hk
  have e : x * (a * a') * x⁻¹ = (x * a * x⁻¹) * (x * a' * x⁻¹) := by group
  rw [e]
  rcases P.norm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((h1 a).1 ha))
      (Subgroup.mem_sup_right ((h2 a').1 ha'))
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((h1 a).1 ha))
      (Subgroup.mem_sup_left ((h2 a').1 ha'))

theorem exists_two_pow_mem {Ω : Type*} [Group Ω] {Kb Tb : Subgroup Ω}
    (hn : ∀ s ∈ Tb, ∀ k ∈ Kb, s * k * s⁻¹ ∈ Kb) (hT2 : IsPGroup 2 Tb) {x k s : Ω} (hk : k ∈ Kb)
    (hs : s ∈ Tb) (hx : x = k * s) : ∃ m : ℕ, x ^ 2 ^ m ∈ Kb := by
  obtain ⟨m, hm⟩ := hT2 ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have key : ∀ n : ℕ, ∃ k' ∈ Kb, (k * s) ^ n = k' * s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, Kb.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', h⟩ := ih
      have hsn : s ^ n ∈ Tb := Tb.pow_mem hs n
      have hconj : (s ^ n) * k * (s ^ n)⁻¹ ∈ Kb := hn _ hsn k hk
      refine ⟨k' * ((s ^ n) * k * (s ^ n)⁻¹), Kb.mul_mem hk' hconj, ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨k', hk', h⟩ := key (2 ^ m)
  refine ⟨m, ?_⟩
  rw [hx, h, hsm, mul_one]
  exact hk'

omit [Finite W] in
theorem caseB_mem (hAut : AutL2SylowInner) {Tb : Subgroup (MulAut W)} {τ : MulAut W}
    (hAX : P.A ≤ P.Xb) (hA'X : P.A' ≤ P.Xb) (hTX : Tb ≤ P.Xb) (hT2 : IsPGroup 2 Tb)
    (hconj2 : ∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S →
      ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb)
    (hXKT : ∀ x ∈ P.Xb, ∃ k ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = k * s)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ P.Xb → (Q.subgroupOf P.Xb).Normal → IsPGroup 2 Q →
      Q = ⊥)
    (hτ : τ ∈ Tb) (hτA : ∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A')
    (hfam : FamPSL ↥P.A) {z : MulAut W} (hzT : z ∈ Tb) (hzc : ∀ s ∈ Tb, s * z = z * s) :
    z ∈ P.A ⊔ P.A' := by
  have hzX : z ∈ P.Xb := hTX hzT
  obtain ⟨a₀, ha₀2, ha₀1⟩ : ∃ a₀ : ↥P.A, a₀ * a₀ = 1 ∧ a₀ ≠ 1 := by
    rcases hfam with ⟨f, -, -, ⟨e⟩⟩ | ⟨p, hp, -, ⟨e⟩⟩
    · obtain ⟨x, hx2, hx1⟩ := exists_involution_psl2 (GaloisField 2 f)
      refine ⟨e.symm x, ?_, fun h => hx1 (e.symm.injective (by rw [h]; simp))⟩
      rw [← map_mul, hx2, map_one]
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx2, hx1⟩ := exists_involution_psl2 (ZMod p)
      refine ⟨e.symm x, ?_, fun h => hx1 (e.symm.injective (by rw [h]; simp))⟩
      rw [← map_mul, hx2, map_one]
  have ha₀ord : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq]; exact ha₀2) ha₀1
  have hz2 : IsPGroup 2 (Subgroup.zpowers a₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₀ord, pow_one])
  obtain ⟨SA, hSA⟩ := hz2.exists_le_sylow
  have ha₀S : a₀ ∈ (SA : Subgroup ↥P.A) := hSA (Subgroup.mem_zpowers a₀)
  set Sm : Subgroup (MulAut W) := (SA : Subgroup ↥P.A).map P.A.subtype with hSm
  have hSmX : Sm ≤ P.Xb := by
    rintro _ ⟨x, -, rfl⟩
    exact hAX x.2
  have hSm2 : IsPGroup 2 Sm := (SA.isPGroup' (p := 2)).map P.A.subtype
  obtain ⟨g, hgX, hgT⟩ := hconj2 Sm hSmX hSm2
  have hmemSm : ∀ s ∈ (SA : Subgroup ↥P.A), ((s : ↥P.A) : MulAut W) ∈ Sm :=
    fun s hs => ⟨s, hs, rfl⟩
  obtain ⟨s₁, hs₁T, hs₁A, hs₁1⟩ : ∃ s ∈ Tb, s ∈ P.A ∧ s ≠ 1 := by
    set a₁ : MulAut W := (a₀ : MulAut W) with ha₁
    have ha₁A : a₁ ∈ P.A := a₀.2
    have ha₁1 : a₁ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    have hs₀T : g * a₁ * g⁻¹ ∈ Tb := hgT _ (hmemSm a₀ ha₀S)
    have hs₀1 : g * a₁ * g⁻¹ ≠ 1 := by
      intro h
      apply ha₁1
      calc a₁ = g⁻¹ * (g * a₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rcases P.norm g hgX with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact ⟨_, hs₀T, (h1 a₁).1 ha₁A, hs₀1⟩
    · have hs₀A' : g * a₁ * g⁻¹ ∈ P.A' := (h1 a₁).1 ha₁A
      refine ⟨τ⁻¹ * (g * a₁ * g⁻¹) * τ, ?_, ?_, ?_⟩
      · exact Tb.mul_mem (Tb.mul_mem (Tb.inv_mem hτ) hs₀T) hτ
      · rw [hτA]
        have : τ * (τ⁻¹ * (g * a₁ * g⁻¹) * τ) * τ⁻¹ = g * a₁ * g⁻¹ := by group
        rw [this]
        exact hs₀A'
      · intro h
        apply hs₀1
        calc g * a₁ * g⁻¹ = τ * (τ⁻¹ * (g * a₁ * g⁻¹) * τ) * τ⁻¹ := by group
          _ = 1 := by rw [h]; group
  have hzn : (∀ x, x ∈ P.A ↔ z * x * z⁻¹ ∈ P.A) ∧ (∀ x, x ∈ P.A' ↔ z * x * z⁻¹ ∈ P.A') := by
    rcases P.norm z hzX with h | ⟨h1, -⟩
    · exact h
    · exfalso
      have hz1 : z * s₁ * z⁻¹ = s₁ := by
        have := hzc s₁ hs₁T
        calc z * s₁ * z⁻¹ = (z * s₁) * z⁻¹ := rfl
          _ = (s₁ * z) * z⁻¹ := by rw [← this]
          _ = s₁ := by group
      have : s₁ ∈ P.A ⊓ P.A' := ⟨hs₁A, by rw [← hz1]; exact (h1 s₁).1 hs₁A⟩
      rw [P.inf_eq_bot, Subgroup.mem_bot] at this
      exact hs₁1 this
  set z' : MulAut W := g⁻¹ * z * g with hz'
  have hz'n : ∀ x, x ∈ P.A ↔ z' * x * z'⁻¹ ∈ P.A := by
    intro x
    have e1 : g * (z' * x * z'⁻¹) * g⁻¹ = z * (g * x * g⁻¹) * z⁻¹ := by
      rw [hz']; group
    rcases P.norm g hgX with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rw [h1 (z' * x * z'⁻¹), e1, ← hzn.1, ← h1 x]
    · rw [h1 (z' * x * z'⁻¹), e1, ← hzn.2, ← h1 x]
  have hz'S : ∀ s ∈ (SA : Subgroup ↥P.A), conjAutOn P.A z' hz'n s = s := by
    intro s hs
    apply Subtype.ext
    have hgsT : g * (s : MulAut W) * g⁻¹ ∈ Tb := hgT _ (hmemSm s hs)
    have hcomm := hzc _ hgsT
    show z' * (s : MulAut W) * z'⁻¹ = s
    calc z' * (s : MulAut W) * z'⁻¹ = g⁻¹ * (z * (g * (s : MulAut W) * g⁻¹) * z⁻¹) * g := by
          rw [hz']; group
      _ = g⁻¹ * ((g * (s : MulAut W) * g⁻¹) * z * z⁻¹) * g := by rw [← hcomm]
      _ = s := by group
  obtain ⟨l, hl⟩ := hAut ↥P.A hfam (conjAutOn P.A z' hz'n) ⟨SA, hz'S⟩
  have hl' : ∀ x ∈ P.A, z' * x * z'⁻¹ = (l : MulAut W) * x * (l : MulAut W)⁻¹ := by
    intro x hx
    have := congrArg Subtype.val (hl ⟨x, hx⟩)
    exact this
  have hlA : (l : MulAut W) ∈ P.A := l.2
  set m : MulAut W := g * (l : MulAut W) * g⁻¹ with hm
  have hzm : ∀ x ∈ P.A, z * (g * x * g⁻¹) * z⁻¹ = m * (g * x * g⁻¹) * m⁻¹ := by
    intro x hx
    have := hl' x hx
    calc z * (g * x * g⁻¹) * z⁻¹ = g * (z' * x * z'⁻¹) * g⁻¹ := by rw [hz']; group
      _ = g * ((l : MulAut W) * x * (l : MulAut W)⁻¹) * g⁻¹ := by rw [this]
      _ = m * (g * x * g⁻¹) * m⁻¹ := by rw [hm]; group
  have hτc : z * τ = τ * z := (hzc τ hτ).symm
  have hτc' : z * τ⁻¹ = τ⁻¹ * z := (hzc τ⁻¹ (Tb.inv_mem hτ)).symm
  have hA_of_A' : ∀ m' ∈ P.A', (∀ y ∈ P.A', z * y * z⁻¹ = m' * y * m'⁻¹) →
      (τ⁻¹ * m' * τ ∈ P.A ∧ ∀ x ∈ P.A, z * x * z⁻¹ = (τ⁻¹ * m' * τ) * x * (τ⁻¹ * m' * τ)⁻¹) := by
    intro m' hm' hy
    refine ⟨?_, ?_⟩
    · rw [hτA]
      have : τ * (τ⁻¹ * m' * τ) * τ⁻¹ = m' := by group
      rw [this]
      exact hm'
    · intro x hx
      have hyA' : τ * x * τ⁻¹ ∈ P.A' := (hτA x).1 hx
      have := hy _ hyA'
      calc z * x * z⁻¹ = τ⁻¹ * (z * (τ * x * τ⁻¹) * z⁻¹) * τ := by
            calc z * x * z⁻¹ = (z * τ⁻¹) * (τ * x * τ⁻¹) * (z * τ⁻¹)⁻¹ := by group
              _ = (τ⁻¹ * z) * (τ * x * τ⁻¹) * (τ⁻¹ * z)⁻¹ := by rw [hτc']
              _ = τ⁻¹ * (z * (τ * x * τ⁻¹) * z⁻¹) * τ := by group
        _ = τ⁻¹ * (m' * (τ * x * τ⁻¹) * m'⁻¹) * τ := by rw [this]
        _ = (τ⁻¹ * m' * τ) * x * (τ⁻¹ * m' * τ)⁻¹ := by group
  have hA'_of_A : ∀ m' ∈ P.A, (∀ x ∈ P.A, z * x * z⁻¹ = m' * x * m'⁻¹) →
      (τ * m' * τ⁻¹ ∈ P.A' ∧
        ∀ y ∈ P.A', z * y * z⁻¹ = (τ * m' * τ⁻¹) * y * (τ * m' * τ⁻¹)⁻¹) := by
    intro m' hm' hx
    refine ⟨(hτA m').1 hm', ?_⟩
    intro y hy
    have hxA : τ⁻¹ * y * τ ∈ P.A := by
      rw [hτA]
      have : τ * (τ⁻¹ * y * τ) * τ⁻¹ = y := by group
      rw [this]
      exact hy
    have := hx _ hxA
    calc z * y * z⁻¹ = τ * (z * (τ⁻¹ * y * τ) * z⁻¹) * τ⁻¹ := by
          calc z * y * z⁻¹ = (z * τ) * (τ⁻¹ * y * τ) * (z * τ)⁻¹ := by group
            _ = (τ * z) * (τ⁻¹ * y * τ) * (τ * z)⁻¹ := by rw [hτc]
            _ = τ * (z * (τ⁻¹ * y * τ) * z⁻¹) * τ⁻¹ := by group
      _ = τ * (m' * (τ⁻¹ * y * τ) * m'⁻¹) * τ⁻¹ := by rw [this]
      _ = (τ * m' * τ⁻¹) * y * (τ * m' * τ⁻¹)⁻¹ := by group
  obtain ⟨l₁, hl₁A, hl₁, l₂, hl₂A', hl₂⟩ : ∃ l₁ ∈ P.A, (∀ x ∈ P.A, z * x * z⁻¹ = l₁ * x * l₁⁻¹) ∧
      ∃ l₂ ∈ P.A', ∀ y ∈ P.A', z * y * z⁻¹ = l₂ * y * l₂⁻¹ := by
    rcases P.norm g hgX with ⟨h1, -⟩ | ⟨h1, -⟩
    ·
      have hmA : m ∈ P.A := (h1 (l : MulAut W)).1 hlA
      have hAin : ∀ x ∈ P.A, z * x * z⁻¹ = m * x * m⁻¹ := by
        intro x hx
        have hx₀ : g⁻¹ * x * g ∈ P.A := by
          rw [h1]
          have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
          rw [this]
          exact hx
        have := hzm _ hx₀
        have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [e] at this
        exact this
      obtain ⟨hm'A', hm'⟩ := hA'_of_A m hmA hAin
      exact ⟨m, hmA, hAin, _, hm'A', hm'⟩
    ·
      have hmA' : m ∈ P.A' := (h1 (l : MulAut W)).1 hlA
      have hA'in : ∀ y ∈ P.A', z * y * z⁻¹ = m * y * m⁻¹ := by
        intro y hy
        have hy₀ : g⁻¹ * y * g ∈ P.A := by
          rw [h1]
          have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
          rw [this]
          exact hy
        have := hzm _ hy₀
        have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [e] at this
        exact this
      obtain ⟨hm'A, hm'⟩ := hA_of_A' m hmA' hA'in
      exact ⟨_, hm'A, hm', m, hmA', hA'in⟩
  set u : MulAut W := l₁ * l₂ with hu
  have huX : u ∈ P.Xb := P.Xb.mul_mem (hAX hl₁A) (hA'X hl₂A')
  have hcX : u⁻¹ * z ∈ P.Xb := P.Xb.mul_mem (P.Xb.inv_mem huX) hzX
  have hzuA : ∀ x ∈ P.A, z * x * z⁻¹ = u * x * u⁻¹ := by
    intro x hx
    have hl2x : l₂ * x * l₂⁻¹ = x := by
      rw [← P.comm x hx l₂ hl₂A']
      group
    calc z * x * z⁻¹ = l₁ * x * l₁⁻¹ := hl₁ x hx
      _ = l₁ * (l₂ * x * l₂⁻¹) * l₁⁻¹ := by rw [hl2x]
      _ = u * x * u⁻¹ := by rw [hu]; group
  have hzuA' : ∀ y ∈ P.A', z * y * z⁻¹ = u * y * u⁻¹ := by
    intro y hy
    have hw : l₂ * y * l₂⁻¹ ∈ P.A' :=
      P.A'.mul_mem (P.A'.mul_mem hl₂A' hy) (P.A'.inv_mem hl₂A')
    have hl1w : l₁ * (l₂ * y * l₂⁻¹) * l₁⁻¹ = l₂ * y * l₂⁻¹ := by
      rw [P.comm l₁ hl₁A _ hw]
      group
    calc z * y * z⁻¹ = l₂ * y * l₂⁻¹ := hl₂ y hy
      _ = l₁ * (l₂ * y * l₂⁻¹) * l₁⁻¹ := hl1w.symm
      _ = u * y * u⁻¹ := by rw [hu]; group
  have hcomm_gen : ∀ k : MulAut W, z * k * z⁻¹ = u * k * u⁻¹ → (u⁻¹ * z) * k = k * (u⁻¹ * z) := by
    intro k hk
    have e : z * k = (u * k * u⁻¹) * z := by
      rw [← hk]
      group
    calc (u⁻¹ * z) * k = u⁻¹ * (z * k) := by group
      _ = u⁻¹ * ((u * k * u⁻¹) * z) := by rw [e]
      _ = k * (u⁻¹ * z) := by group
  have hnK : ∀ x ∈ P.Xb, ∀ k ∈ P.A ⊔ P.A', x * k * x⁻¹ ∈ P.A ⊔ P.A' := fun x hx k hk =>
    P.sup_normal hx hk
  have hcom : ∀ k ∈ P.A ⊔ P.A', (u⁻¹ * z) * k = k * (u⁻¹ * z) := by
    intro k hk
    obtain ⟨a, ha, a'', ha'', rfl⟩ := mem_sup_of_commute P.comm hk
    have h1 := hcomm_gen a (hzuA a ha)
    have h2 := hcomm_gen a'' (hzuA' a'' ha'')
    calc (u⁻¹ * z) * (a * a'') = ((u⁻¹ * z) * a) * a'' := by group
      _ = (a * (u⁻¹ * z)) * a'' := by rw [h1]
      _ = a * ((u⁻¹ * z) * a'') := by group
      _ = a * (a'' * (u⁻¹ * z)) := by rw [h2]
      _ = (a * a'') * (u⁻¹ * z) := by group
  have hc1 : u⁻¹ * z = 1 :=
    eq_one_of_commute_of_two_pow152 hO2 hnK
      (fun x hx => by
        obtain ⟨k, hk, s, hs, hxs⟩ := hXKT x hx
        exact exists_two_pow_mem (fun s hs k hk => hnK s (hTX hs) k hk) hT2 hk hs hxs)
      (fun k hk hc => P.central_eq_one hk hc) _ hcX hcom
  have hzu : z = u := by
    have : z = u * (u⁻¹ * z) := by group
    rw [this, hc1, mul_one]
  rw [hzu, hu]
  exact (P.A ⊔ P.A').mul_mem (Subgroup.mem_sup_left hl₁A) (Subgroup.mem_sup_right hl₂A')

end PairData

theorem exists_central_of_normal {Ω : Type*} [Group Ω] [Finite Ω] {Tb Vb : Subgroup Ω}
    (hT2 : IsPGroup 2 Tb) (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb)
    (hne : Vb ≠ ⊥) : ∃ v ∈ Vb, v ≠ 1 ∧ ∀ s ∈ Tb, s * v = v * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : Fact (IsPGroup 2 ↥Tb) := ⟨hT2⟩
  have hnorm : (Vb.subgroupOf Tb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVT]
    exact fun h g hh hg => hVn g hg h hh
  have hnt : Nontrivial ↥(Vb.subgroupOf Tb) := by
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one Vb).resolve_left hne
    refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨⟨x, hVT hx⟩, hx⟩, ?_⟩
    intro h
    apply hx1
    have := congrArg (fun y : ↥(Vb.subgroupOf Tb) => ((y : ↥Tb) : Ω)) h
    simpa using this.symm
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (N := Vb.subgroupOf Tb) (p := 2)
  refine ⟨(((x : ↥Tb)) : Ω), x.2, ?_, ?_⟩
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · intro s hs
    have := Subgroup.mem_center_iff.1 hxc ⟨s, hs⟩
    exact congrArg Subtype.val this

namespace PairData

variable {W : Type} [CommGroup W] [Finite W] (P : PairData W)

theorem trans_false (hAut : AutL2SylowInner) (hfam : FamPSL ↥P.A)
    {Tb Vb : Subgroup (MulAut W)} {τ : MulAut W}
    (hAX : P.A ≤ P.Xb) (hA'X : P.A' ≤ P.Xb) (hTX : Tb ≤ P.Xb) (hT2 : IsPGroup 2 Tb)
    (hconj2 : ∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S →
      ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb)
    (hXKT : ∀ x ∈ P.Xb, ∃ k ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = k * s)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ P.Xb → (Q.subgroupOf P.Xb).Normal → IsPGroup 2 Q →
      Q = ⊥)
    (hτ : τ ∈ Tb) (hτA : ∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A')
    (hτA' : ∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A)
    (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb) (hVne : Vb ≠ ⊥)
    (hz : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 2) : False := by
  by_cases hK : Vb ⊓ (P.A ⊔ P.A') = ⊥
  · obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal hT2 hVT hVn hVne
    have hvK := P.caseB_mem hAut hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hfam (hVT hvV) hvc
    have : v ∈ Vb ⊓ (P.A ⊔ P.A') := ⟨hvV, hvK⟩
    rw [hK, Subgroup.mem_bot] at this
    exact hv1 this
  · exact P.trans_caseA_false hT2 hVT hVn hτ (fun x hx => (hτA x).1 hx)
      (fun x hx => (hτA' x).1 hx) hK hz

theorem famPSL_of_ne7 {G : Type*} [Group G] (h : FamPSLne7 G) : FamPSL G := by
  rcases h with h | ⟨p, hp, hp5, -, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, hp5, e⟩

theorem shape_false (hAut : AutL2SylowInner) (hfam : FamPSLne7 ↥P.A) (hfam' : FamPSLne7 ↥P.A')
    {Tb Vb : Subgroup (MulAut W)} {τ : MulAut W}
    (hAX : P.A ≤ P.Xb) (hA'X : P.A' ≤ P.Xb) (hTX : Tb ≤ P.Xb) (hT2 : IsPGroup 2 Tb)
    (hconj2 : ∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S →
      ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb)
    (hXKT : ∀ x ∈ P.Xb, ∃ k ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = k * s)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ P.Xb → (Q.subgroupOf P.Xb).Normal → IsPGroup 2 Q →
      Q = ⊥)
    (hτ : τ ∈ Tb) (hτA : ∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A')
    (hτA' : ∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A)
    (hVT : Vb ≤ Tb) (hVn : ∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb) (hVne : Vb ≠ ⊥)
    (hz : ∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 4) : False := by
  by_cases hK : Vb ⊓ (P.A ⊔ P.A') = ⊥
  · obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal hT2 hVT hVn hVne
    have hvK := P.caseB_mem hAut hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA (famPSL_of_ne7 hfam)
      (hVT hvV) hvc
    have : v ∈ Vb ⊓ (P.A ⊔ P.A') := ⟨hvV, hvK⟩
    rw [hK, Subgroup.mem_bot] at this
    exact hv1 this
  · exact P.shape_caseA_false hT2 hVT hVn hτ (fun x hx => (hτA x).1 hx)
      (fun x hx => (hτA' x).1 hx) hK hz hfam hfam'

end PairData

end CFSG.Quasithin.He6
