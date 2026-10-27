module

public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Background.F1Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.Quasithin.H13.Ch3Sec3

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

section Abstract

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem le_sup_of_two_pow {X K S : Subgroup Ω} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hS : IsSylowTwoOf S X) : X ≤ K ⊔ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hp : IsPGroup 2 (↥X ⧸ K.subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 x x.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hKS : K ≤ K ⊔ S := le_sup_left
  have hd1 : (K ⊔ S).relIndex X ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_of_le_left X hKS
  have hd2 : (K ⊔ S).relIndex X ∣ S.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exact absurd ((hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)).trans hd2) hS.2.2
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj

omit [Finite Ω] in
theorem mem_normalizer_subgroupOf_iff {K P : Subgroup Ω} (hPK : P ≤ K) (k : ↥K) :
    k ∈ Subgroup.normalizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (k : Ω) ∈ Subgroup.normalizer (P : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ K
    · have := h ⟨x, hx⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have hx' : (k : Ω) * x * (k : Ω)⁻¹ ∉ K := by
        intro hk
        apply hx
        have := K.mul_mem (K.mul_mem (K.inv_mem k.2) hk) k.2
        simpa [mul_assoc] using this
      exact ⟨fun h1 => absurd (hPK h1) hx, fun h1 => absurd (hPK h1) hx'⟩
  · intro h x
    have := h x
    simpa [Subgroup.mem_subgroupOf] using this

omit [Finite Ω] in
theorem le_normalizer_of_commute {A B : Subgroup Ω} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set Ω) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have e : b * a * b⁻¹ = a := by
      rw [← h a ha b hb]
      group
    rw [e]
    exact ha
  · intro hx
    have e := h _ hx b hb
    have : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * ((b * a * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [e]
        _ = b * a * b⁻¹ := by group
    rw [this]
    exact hx

omit [Finite Ω] in
theorem rankOne_of_isRankOneSylow {K P : Subgroup Ω} (hK : IsRankOneSylow ↥K)
    (hP : IsSylowTwoOf P K) :
    K ⊓ Subgroup.normalizer (P : Set Ω) ≠ K ∧
      ∀ Y : Subgroup Ω, P ≤ Y → Y ≤ K → Y ≠ K → Y ≤ Subgroup.normalizer (P : Set Ω) := by
  have hP2 : IsPGroup 2 ↥(P.subgroupOf K) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  obtain ⟨hne, hmax, -⟩ := hK (P.subgroupOf K) hP2 hP.2.2
  refine ⟨fun heq => hne ?_, fun Y hPY hYK hYne => ?_⟩
  · rw [eq_top_iff]
    intro k _
    rw [mem_normalizer_subgroupOf_iff hP.1]
    have : (k : Ω) ∈ K ⊓ Subgroup.normalizer (P : Set Ω) := by
      rw [heq]
      exact k.2
    exact this.2
  · have hle : P.subgroupOf K ≤ Y.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPY (Subgroup.mem_subgroupOf.mp hx))
    have hYne' : Y.subgroupOf K ≠ ⊤ := by
      intro htop
      apply hYne
      refine le_antisymm hYK fun k hk => ?_
      have : (⟨k, hk⟩ : ↥K) ∈ Y.subgroupOf K := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    intro y hy
    have h1 := hmax (Y.subgroupOf K) hle hYne' (Subgroup.mem_subgroupOf.mpr hy :
      (⟨y, hYK hy⟩ : ↥K) ∈ Y.subgroupOf K)
    exact (mem_normalizer_subgroupOf_iff hP.1 ⟨y, hYK hy⟩).mp h1

theorem isSylowTwoOf_inf_of_normal {X K S : Subgroup Ω} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal hS hKX hXK

theorem le_normalizer_of_rankOne {X K S : Subgroup Ω} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hS : IsSylowTwoOf S X) (hK : IsRankOneSylow ↥K) :
    X ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Ω) : Set Ω) ≠ X ∧
      ∀ Y : Subgroup Ω, S ≤ Y → Y ≤ X → Y ≠ X →
        Y ≤ X ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Ω) : Set Ω) := by
  obtain ⟨hne, hmax⟩ := rankOne_of_isRankOneSylow hK (isSylowTwoOf_inf_of_normal hKX hXK hS)
  have hXKS := le_sup_of_two_pow hKX hXK h2 hS
  have hSN : S ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Ω) : Set Ω) := fun s hs =>
    mem_normalizer_inf (Subgroup.le_normalizer hs) (hXK (hS.1 hs))
  refine ⟨fun heq => hne ?_, fun Y hSY hYX hYne => ?_⟩
  · refine le_antisymm inf_le_left (le_inf le_rfl fun k hk => ?_)
    have : k ∈ X ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Ω) : Set Ω) := by
      rw [heq]
      exact hKX hk
    exact this.2
  have hYK : Y ⊓ K ≠ K := by
    intro heq
    apply hYne
    refine le_antisymm hYX (hXKS.trans (sup_le ?_ hSY))
    exact heq ▸ inf_le_left
  have hYKN := hmax (Y ⊓ K) (inf_le_inf_right K hSY) inf_le_right hYK
  intro y hy
  refine ⟨hYX hy, ?_⟩
  have hy' : y ∈ (K : Set Ω) * (S : Set Ω) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S (hS.1.trans hXK)]
    exact hXKS (hYX hy)
  obtain ⟨k, hk, s, hs, rfl⟩ := hy'
  have hkY : k ∈ Y := by
    have := Y.mul_mem hy (Y.inv_mem (hSY hs))
    simpa using this
  exact Subgroup.mul_mem _ (hYKN ⟨hkY, hk⟩) (hSN hs)

omit [Finite Ω] in
theorem mem_normalizer_of_map_conj_eq {B : Subgroup Ω} {s : Ω}
    (h : B.map (MulAut.conj s).toMonoidHom = B) : s ∈ Subgroup.normalizer (B : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [← h]
    exact ⟨b, hb, rfl⟩
  · intro hb
    rw [← h] at hb
    obtain ⟨b', hb', he⟩ := hb
    have : b' = b := by
      have he' : s * b' * s⁻¹ = s * b * s⁻¹ := he
      simpa using he'
    exact this ▸ hb'

omit [Finite Ω] in
theorem map_conj_inf_of_mem {S K : Subgroup Ω} {s : Ω} (hs : s ∈ S) :
    (S ⊓ K).map (MulAut.conj s).toMonoidHom = S ⊓ K.map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]
  congr 1
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)
  · intro x hx
    refine ⟨s⁻¹ * x * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem le_of_proj {Y K₁ K₂ P₁ : Subgroup Ω} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hP₁ : IsSylowTwoOf P₁ K₁) (hP₁Y : P₁ ≤ Y)
    (hne₁ : K₁ ⊓ Subgroup.normalizer (P₁ : Set Ω) ≠ K₁)
    (hmax₁ : ∀ Z : Subgroup Ω, P₁ ≤ Z → Z ≤ K₁ → Z ≠ K₁ → Z ≤ Subgroup.normalizer (P₁ : Set Ω))
    (hproj : ∀ a ∈ K₁, ∃ b ∈ K₂, a * b ∈ Y) : K₁ ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : K₁ ≤ Subgroup.normalizer ((Y ⊓ K₁ : Subgroup Ω) : Set Ω) := by
    intro k hk
    obtain ⟨b, hb, hkb⟩ := hproj k hk
    have key : ∀ y ∈ Y ⊓ K₁, k * y * k⁻¹ ∈ Y ⊓ K₁ := by
      intro y hy
      have hby : b * y * b⁻¹ = y := by
        rw [← hc y hy.2 b hb]
        group
      have e : k * y * k⁻¹ = (k * b) * y * (k * b)⁻¹ := by
        calc k * y * k⁻¹ = k * (b * y * b⁻¹) * k⁻¹ := by rw [hby]
          _ = (k * b) * y * (k * b)⁻¹ := by group
      refine ⟨?_, K₁.mul_mem (K₁.mul_mem hk hy.2) (K₁.inv_mem hk)⟩
      rw [e]
      exact Y.mul_mem (Y.mul_mem hkb hy.1) (Y.inv_mem hkb)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key y
    · intro hy
      have hk' : k⁻¹ ∈ K₁ := K₁.inv_mem hk
      obtain ⟨b', hb', hkb'⟩ := hproj k⁻¹ hk'
      have hby : b' * (k * y * k⁻¹) * b'⁻¹ = k * y * k⁻¹ := by
        rw [← hc _ hy.2 b' hb']
        group
      have e : y = (k⁻¹ * b') * (k * y * k⁻¹) * (k⁻¹ * b')⁻¹ := by
        calc y = k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ := by group
          _ = k⁻¹ * (b' * (k * y * k⁻¹) * b'⁻¹) * k⁻¹⁻¹ := by rw [hby]
          _ = (k⁻¹ * b') * (k * y * k⁻¹) * (k⁻¹ * b')⁻¹ := by group
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Y.mul_mem (Y.mul_mem hkb' hy.1) (Y.inv_mem hkb')
      · have := K₁.mul_mem (K₁.mul_mem hk' hy.2) hk
        simpa [mul_assoc] using this
  by_contra hKY
  have hYK : Y ⊓ K₁ ≠ K₁ := fun h => hKY (h ▸ inf_le_left)
  have hle := hmax₁ (Y ⊓ K₁) (le_inf hP₁Y hP₁.1) inf_le_right hYK
  have hPS : IsSylowTwoOf P₁ (Y ⊓ K₁) := by
    refine ⟨le_inf hP₁Y hP₁.1, hP₁.2.1, fun h => hP₁.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex P₁ (Y ⊓ K₁) K₁ (le_inf hP₁Y hP₁.1) inf_le_right
    have h3 : 2 ∣ P₁.relIndex K₁ := by
      rw [← this]
      exact Dvd.dvd.mul_right h _
    exact h3
  have hPO : pCoreOf 2 (Y ⊓ K₁) = P₁ := by
    refine le_antisymm (pCoreOf_le_of_isSylowTwoOf hPS) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPS.1
      (fun x hx => hle hx) hP₁.2.1
  apply hne₁
  refine le_antisymm inf_le_left (le_inf le_rfl ?_)
  rw [← hPO]
  exact hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem le_normalizer_of_rankOne_prod {X K K₁ K₂ S : Subgroup Ω} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hS : IsSylowTwoOf S X) (hK : K = K₁ ⊔ K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = ⊥) (hK₁ : IsRankOneSylow ↥K₁) (hK₂ : IsRankOneSylow ↥K₂)
    (hperm : ∀ s ∈ S, (K₁.map (MulAut.conj s).toMonoidHom = K₁ ∧
      K₂.map (MulAut.conj s).toMonoidHom = K₂) ∨
      (K₁.map (MulAut.conj s).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj s).toMonoidHom = K₁))
    (hswap : ∃ s ∈ S, K₁.map (MulAut.conj s).toMonoidHom = K₂) :
    S ≤ Subgroup.normalizer (((S ⊓ K₁) ⊔ (S ⊓ K₂) : Subgroup Ω) : Set Ω) ∧
    X ⊓ Subgroup.normalizer (((S ⊓ K₁) ⊔ (S ⊓ K₂) : Subgroup Ω) : Set Ω) ≠ X ∧
      ∀ Y : Subgroup Ω, S ≤ Y → Y ≤ X → Y ≠ X →
        Y ≤ X ⊓ Subgroup.normalizer (((S ⊓ K₁) ⊔ (S ⊓ K₂) : Subgroup Ω) : Set Ω) := by
  set P₁ := S ⊓ K₁ with hP₁def
  set P₂ := S ⊓ K₂ with hP₂def
  set P := P₁ ⊔ P₂ with hPdef
  have hK₁K : K₁ ≤ K := hK ▸ le_sup_left
  have hK₂K : K₂ ≤ K := hK ▸ le_sup_right
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hK₂N₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set Ω) := le_normalizer_of_commute hc
  have hKn₁ : K ≤ Subgroup.normalizer (K₁ : Set Ω) := hK ▸ sup_le Subgroup.le_normalizer hK₂N₁
  have hK₁N₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set Ω) := le_normalizer_of_commute hc'
  have hKn₂ : K ≤ Subgroup.normalizer (K₂ : Set Ω) := hK ▸ sup_le hK₁N₂ Subgroup.le_normalizer
  have hSK := isSylowTwoOf_inf_of_normal hKX hXK hS
  have hS₁ : IsSylowTwoOf P₁ K₁ := by
    have := isSylowTwoOf_inf_of_normal hK₁K hKn₁ hSK
    rwa [inf_assoc, inf_eq_right.mpr hK₁K] at this
  have hS₂ : IsSylowTwoOf P₂ K₂ := by
    have := isSylowTwoOf_inf_of_normal hK₂K hKn₂ hSK
    rwa [inf_assoc, inf_eq_right.mpr hK₂K] at this
  obtain ⟨hne₁, hmax₁⟩ := rankOne_of_isRankOneSylow hK₁ hS₁
  obtain ⟨hne₂, hmax₂⟩ := rankOne_of_isRankOneSylow hK₂ hS₂
  have hXKS := le_sup_of_two_pow hKX hXK h2 hS
  have hSP : S ≤ Subgroup.normalizer (P : Set Ω) := by
    intro s hs
    apply mem_normalizer_of_map_conj_eq
    rw [hPdef, Subgroup.map_sup, map_conj_inf_of_mem hs, map_conj_inf_of_mem hs]
    rcases hperm s hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂, sup_comm]
  have hPK₁ : P ⊓ K₁ ≤ P₁ := by
    rintro x ⟨hxP, hxK⟩
    have hP₂N : P₂ ≤ Subgroup.normalizer (P₁ : Set Ω) :=
      le_normalizer_of_commute fun a ha b hb => hc a ha.2 b hb.2
    have hx' : x ∈ (P₁ : Set Ω) * (P₂ : Set Ω) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left P₁ P₂ hP₂N]
      exact hxP
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    have hab' : x = a * b := hab.symm
    have hbK₁ : b ∈ K₁ := by
      have := K₁.mul_mem (K₁.inv_mem ha.2) (hab' ▸ hxK)
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ K₁ ⊓ K₂ := ⟨hbK₁, hb.2⟩
      rw [hinf] at this
      exact this
    rw [hab', hb1, mul_one]
    exact ha
  refine ⟨hSP, fun heq => ?_, fun Y hSY hYX hYne => ?_⟩
  · apply hne₁
    refine le_antisymm inf_le_left (le_inf le_rfl fun k hk => ?_)
    have hkP : k ∈ Subgroup.normalizer (P : Set Ω) := by
      have : k ∈ X ⊓ Subgroup.normalizer (P : Set Ω) := by
        rw [heq]
        exact hKX (hK₁K hk)
      exact this.2
    have hk' := mem_normalizer_inf hkP (Subgroup.le_normalizer hk)
    have heq' : P ⊓ K₁ = P₁ := le_antisymm hPK₁ (le_inf le_sup_left inf_le_right)
    rwa [heq'] at hk'
  obtain ⟨s₀, hs₀, hs₀K⟩ := hswap
  have hK₁ne : K₁ ≠ K₂ := by
    intro heq
    apply hne₁
    have : K₁ = ⊥ := by rw [← hinf, ← heq, inf_idem]
    rw [this]
    exact inf_le_left.antisymm bot_le
  have hs₀K' : K₂.map (MulAut.conj s₀).toMonoidHom = K₁ := by
    rcases hperm s₀ hs₀ with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact absurd (h₁.symm.trans hs₀K) hK₁ne
    · exact h₂
  have hYs : Y.map (MulAut.conj s₀).toMonoidHom = Y := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact Y.mul_mem (Y.mul_mem (hSY hs₀) hy) (Y.inv_mem (hSY hs₀))
    · intro y hy
      refine ⟨s₀⁻¹ * y * s₀, Y.mul_mem (Y.mul_mem (Y.inv_mem (hSY hs₀)) hy) (hSY hs₀), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hfin : K₁ ≤ Y → K₂ ≤ Y → False := fun h₁ h₂ =>
    hYne (le_antisymm hYX (hXKS.trans (sup_le (hK ▸ sup_le h₁ h₂) hSY)))
  let Q₁ : Subgroup Ω :=
    { carrier := {a | a ∈ K₁ ∧ ∃ b ∈ K₂, a * b ∈ Y}
      one_mem' := ⟨K₁.one_mem, 1, K₂.one_mem, by simp⟩
      mul_mem' := by
        rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
        refine ⟨K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
        have e : a * a' * (b * b') = (a * b) * (a' * b') := by
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
            _ = (a * b) * (a' * b') := by group
        rw [e]
        exact Y.mul_mem hab hab'
      inv_mem' := by
        rintro a ⟨ha, b, hb, hab⟩
        refine ⟨K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          have := congrArg (·⁻¹) (hc a ha b hb)
          simp only [mul_inv_rev] at this
          rw [mul_inv_rev]
          exact this.symm
        rw [e]
        exact Y.inv_mem hab }
  let Q₂ : Subgroup Ω :=
    { carrier := {b | b ∈ K₂ ∧ ∃ a ∈ K₁, b * a ∈ Y}
      one_mem' := ⟨K₂.one_mem, 1, K₁.one_mem, by simp⟩
      mul_mem' := by
        rintro b b' ⟨hb, a, ha, hba⟩ ⟨hb', a', ha', hba'⟩
        refine ⟨K₂.mul_mem hb hb', a * a', K₁.mul_mem ha ha', ?_⟩
        have e : b * b' * (a * a') = (b * a) * (b' * a') := by
          calc b * b' * (a * a') = b * (b' * a) * a' := by group
            _ = b * (a * b') * a' := by rw [hc' b' hb' a ha]
            _ = (b * a) * (b' * a') := by group
        rw [e]
        exact Y.mul_mem hba hba'
      inv_mem' := by
        rintro b ⟨hb, a, ha, hba⟩
        refine ⟨K₂.inv_mem hb, a⁻¹, K₁.inv_mem ha, ?_⟩
        have e : b⁻¹ * a⁻¹ = (b * a)⁻¹ := by
          have := congrArg (·⁻¹) (hc' b hb a ha)
          simp only [mul_inv_rev] at this
          rw [mul_inv_rev]
          exact this.symm
        rw [e]
        exact Y.inv_mem hba }
  have hQ₁ : Q₁ ≤ Subgroup.normalizer (P₁ : Set Ω) := by
    refine hmax₁ Q₁ (fun x hx => ⟨hx.2, 1, K₂.one_mem, by simpa using hSY hx.1⟩)
      (fun x hx => hx.1) fun heq => ?_
    have hK₁Y : K₁ ≤ Y := le_of_proj hc hS₁ (inf_le_left.trans hSY) hne₁ hmax₁
      fun a ha => (heq ▸ ha : a ∈ Q₁).2
    refine hfin hK₁Y ?_
    rw [← hs₀K, ← hYs]
    exact Subgroup.map_mono hK₁Y
  have hQ₂ : Q₂ ≤ Subgroup.normalizer (P₂ : Set Ω) := by
    refine hmax₂ Q₂ (fun x hx => ⟨hx.2, 1, K₁.one_mem, by simpa using hSY hx.1⟩)
      (fun x hx => hx.1) fun heq => ?_
    have hK₂Y : K₂ ≤ Y := le_of_proj hc' hS₂ (inf_le_left.trans hSY) hne₂ hmax₂
      fun b hb => (heq ▸ hb : b ∈ Q₂).2
    refine hfin ?_ hK₂Y
    rw [← hs₀K', ← hYs]
    exact Subgroup.map_mono hK₂Y
  have hcentP₂ : ∀ a ∈ K₁, a ∈ Subgroup.normalizer (P₂ : Set Ω) := fun a ha =>
    le_normalizer_of_commute (A := P₂) (B := K₁) (fun b hb a ha => hc' b hb.2 a ha) ha
  have hcentP₁ : ∀ b ∈ K₂, b ∈ Subgroup.normalizer (P₁ : Set Ω) := fun b hb =>
    le_normalizer_of_commute (A := P₁) (B := K₂) (fun a ha b hb => hc a ha.2 b hb) hb
  have hYKP : ∀ y ∈ Y, y ∈ K → y ∈ Subgroup.normalizer (P : Set Ω) := by
    intro y hy hyK
    rw [hK] at hyK
    have hy' : y ∈ (K₁ : Set Ω) * (K₂ : Set Ω) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K₁ K₂ hK₂N₁]
      exact hyK
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    have haQ : a ∈ Q₁ := ⟨ha, b, hb, hy⟩
    have hbQ : b ∈ Q₂ := ⟨hb, a, ha, by rw [← hc a ha b hb]; exact hy⟩
    exact Subgroup.mul_mem _ (mem_normalizer_sup (hQ₁ haQ) (hcentP₂ a ha))
      (mem_normalizer_sup (hcentP₁ b hb) (hQ₂ hbQ))
  intro y hy
  refine ⟨hYX hy, ?_⟩
  have hy' : y ∈ (K : Set Ω) * (S : Set Ω) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S (hS.1.trans hXK)]
    exact hXKS (hYX hy)
  obtain ⟨k, hk, s, hs, rfl⟩ := hy'
  have hkY : k ∈ Y := by
    have := Y.mul_mem hy (Y.inv_mem (hSY hs))
    simpa using this
  exact Subgroup.mul_mem _ (hYKP k hkY hk) (hSP hs)

end Abstract

section Internal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoPhi_le_of_isMaxSubgroupIn {H N : Subgroup G} (hN : IsMaxSubgroupIn H N)
    (hO : pCoreOf 2 H ≤ N) : oTwoPhi H ≤ N := by
  set P := CFSG.Open.pCore 2 ↥H with hP
  have : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π := QuotientGroup.mk' P with hπ
  have hNH : N ≤ H := hN.1.le
  have hmem : ∀ n h : ↥H, (n : G) ∈ N → π n = π h → (h : G) ∈ N := by
    intro n h hn he
    have h1 : n⁻¹ * h ∈ P := QuotientGroup.eq.mp he
    have h2 : ((n⁻¹ * h : ↥H) : G) ∈ N := hO ⟨_, h1, rfl⟩
    have := N.mul_mem hn h2
    simpa using this
  have hcoatom : IsCoatom ((N.subgroupOf H).map π) := by
    refine ⟨fun htop => ?_, fun K hK => ?_⟩
    · apply hN.1.ne
      refine le_antisymm hNH fun h hh => ?_
      have : π ⟨h, hh⟩ ∈ (N.subgroupOf H).map π := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, he⟩ := this
      exact hmem n ⟨h, hh⟩ (Subgroup.mem_subgroupOf.mp hn) he
    · obtain ⟨q, hqK, hqN⟩ := IsConcreteLE.exists_of_lt hK
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective P q
      have hhN : (h : G) ∉ N := fun hh => hqN ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      set K' := (K.comap π).map H.subtype with hK'
      have hNK' : N < K' := by
        refine lt_of_le_of_ne (fun n hn => ?_) fun heq => hhN (heq ▸ ⟨h, hqK, rfl⟩)
        exact ⟨⟨n, hNH hn⟩, hK.le ⟨⟨n, hNH hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩, rfl⟩
      have hK'H := hN.2 K' hNK' (Subgroup.map_subtype_le _)
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P x
      have hy : (y : G) ∈ K' := hK'H.symm ▸ y.2
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
  have hΦ := frattini_le_coatom hcoatom
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨n, hn, he⟩ := hΦ hh
  exact hmem n h (Subgroup.mem_subgroupOf.mp hn) he

omit [Finite G] in
theorem exists_isUniqueMaxOver_of_autOn {H T V : Subgroup G} {B : Subgroup (MulAut ↥V)}
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hTH : T ≤ H) (hOT : pCoreOf 2 H ≤ T)
    (hC : H ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi H) (hBH : B ≤ autOn H V)
    (hBne : B ≠ autOn H V) (hTB : autOn T V ≤ B)
    (hmax : ∀ Y : Subgroup (MulAut ↥V), autOn T V ≤ Y → Y ≤ autOn H V → Y ≠ autOn H V → Y ≤ B) :
    ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
  set N := preimageAut H V B with hNdef
  have hmemN : ∀ h (hh : h ∈ H), conjAct V ⟨h, hHV hh⟩ ∈ B → h ∈ N := by
    intro h hh hB
    exact ⟨hh, ⟨h, hHV hh⟩, hB, rfl⟩
  have hNmem : ∀ x (hx : x ∈ N), conjAct V ⟨x, hHV hx.1⟩ ∈ B := by
    rintro x ⟨hxH, ⟨y, hy⟩, hyB, rfl⟩
    exact hyB
  have hNH : N ≤ H := inf_le_left
  have hCN : H ⊓ Subgroup.centralizer (V : Set G) ≤ N := by
    intro c hc
    refine hmemN c hc.1 ?_
    have : conjAct V ⟨c, hHV hc.1⟩ = 1 := by
      ext v
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply, MulAut.one_apply]
      have h := Subgroup.mem_centralizer_iff.mp hc.2 (v : G) v.2
      change c * (v : G) * c⁻¹ = v
      rw [← h, mul_inv_cancel_right]
    rw [this]
    exact B.one_mem
  have hcorr : ∀ Y : Subgroup G, Y ≤ H → H ⊓ Subgroup.centralizer (V : Set G) ≤ Y →
      autOn Y V = autOn H V → Y = H := by
    intro Y hYH hCY heq
    refine le_antisymm hYH fun h hh => ?_
    have hmemH : conjAct V ⟨h, hHV hh⟩ ∈ autOn H V :=
      ⟨⟨h, hHV hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    rw [← heq] at hmemH
    obtain ⟨y, hy, hyh⟩ := hmemH
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hc : (y : G)⁻¹ * h ∈ H ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨H.mul_mem (H.inv_mem (hYH hyY)) hh, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hyh
      simp only [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h1
      calc v * ((y : G)⁻¹ * h) = (y : G)⁻¹ * ((y : G) * v * (y : G)⁻¹) * h := by group
        _ = (y : G)⁻¹ * (h * v * h⁻¹) * h := by rw [h1]
        _ = (y : G)⁻¹ * h * v := by group
    have := Y.mul_mem hyY (hCY hc)
    simpa using this
  have hle : ∀ Y : Subgroup G, T ≤ Y → Y ≤ H → Y ≠ H →
      H ⊓ Subgroup.centralizer (V : Set G) ≤ Y → Y ≤ N := by
    intro Y hTY hYH hYne hCY y hy
    have hsub : ∀ {A B : Subgroup G}, A ≤ B → autOn A V ≤ autOn B V := fun hAB =>
      Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hx))
    have hYB := hmax (autOn Y V) (hsub hTY) (hsub hYH)
      (fun heq => hYne (hcorr Y hYH hCY heq))
    exact hmemN y (hYH hy) (hYB ⟨⟨y, hHV (hYH hy)⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
  have hNne : N ≠ H := by
    intro heq
    apply hBne
    refine le_antisymm hBH fun φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := hφ
    have hgN : (g : G) ∈ N := by
      rw [heq]
      exact Subgroup.mem_subgroupOf.mp hg
    exact hNmem g hgN
  have hTN : T ≤ N := fun t ht =>
    hmemN t (hTH ht) (hTB ⟨⟨t, hHV (hTH ht)⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
  have hNmax : IsMaxSubgroupIn H N := by
    refine ⟨lt_of_le_of_ne hNH hNne, fun K hNK hKH => ?_⟩
    by_contra hKne
    exact hNK.not_ge (hle K (hTN.trans hNK.le) hKH hKne (hCN.trans hNK.le))
  refine ⟨N, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hNmax, hTN⟩, fun M hM => ?_⟩⟩
  obtain ⟨hMmax, hTM⟩ := hM
  have hCM : H ⊓ Subgroup.centralizer (V : Set G) ≤ M :=
    hC.trans (oTwoPhi_le_of_isMaxSubgroupIn hMmax (hOT.trans hTM))
  have hMN := hle M hTM hMmax.1.le hMmax.1.ne hCM
  by_contra hMne
  exact hNmax.1.ne (hMmax.2 N (lt_of_le_of_ne hMN hMne) hNmax.1.le)

end Internal

end CFSG.Quasithin.H13.Ch3Sec3
