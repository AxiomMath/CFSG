module

public import CFSG.Quasithin.Vol2.Ch11SecBE111Main

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def SolvSimpSolv (Y : Type) [Group Y] : Prop :=
  ∃ M N : Subgroup Y, M.Normal ∧ N.Normal ∧ N ≤ M ∧ Group.IsSolvable ↥N ∧
    (∃ k : ℕ, derivedSeries Y k ≤ M) ∧
    ∀ N' : Subgroup Y, N ≤ N' → N' ≤ M → (N'.subgroupOf M).Normal → N' = N ∨ N' = M

theorem solvable_of_le_solvable {Y : Type} [Group Y] {X N : Subgroup Y} (hXN : X ≤ N)
    (hN : Group.IsSolvable ↥N) : Group.IsSolvable ↥X :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXN)
    (Subgroup.inclusion_injective hXN)

theorem solvable_of_inf_eq_bot {Y : Type} [Group Y] {X M : Subgroup Y} {k : ℕ}
    (hk : derivedSeries Y k ≤ M) (hXM : X ⊓ M = ⊥) : Group.IsSolvable ↥X := by
  refine ⟨⟨k, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : Y) ∈ derivedSeries Y k := by
    have := map_derivedSeries_le_derivedSeries X.subtype k
    exact this ⟨x, hx, rfl⟩
  have h2 : (x : Y) ∈ X ⊓ M := ⟨x.2, hk h1⟩
  rw [hXM, Subgroup.mem_bot] at h2
  exact Subtype.ext (by simpa using h2)

theorem SolvSimpSolv.isSimpleGroup {Y : Type} [Group Y] [Finite Y] (h : SolvSimpSolv Y)
    {X : Subgroup Y} (hXn : X.Normal) (hX1 : X ≠ ⊥)
    (hmin : ∀ N : Subgroup Y, N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (hnab : ∃ a b : ↥X, a * b ≠ b * a) : IsSimpleGroup ↥X := by
  obtain ⟨M, N, hMn, hNn, hNM, hNs, ⟨k, hk⟩, hsimp⟩ := h
  have : X.Normal := hXn
  have : M.Normal := hMn
  have : N.Normal := hNn
  have hXns : ¬ Group.IsSolvable ↥X := by
    intro hs
    have : CFSG.IsMinimalNormal X := ⟨fun K hK hKN => hmin K hK hKN⟩
    have hc := CFSG.minimalNormal_solvable_isMulCommutative X
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (hc.is_comm.comm a b)
  have hXN : X ⊓ N = ⊥ := by
    rcases hmin (X ⊓ N) inferInstance inf_le_left with h1 | h1
    · exact h1
    · exfalso
      exact hXns (solvable_of_le_solvable (inf_eq_left.mp h1) hNs)
  have hXM : X ≤ M := by
    rcases hmin (X ⊓ M) inferInstance inf_le_left with h1 | h1
    · exact absurd (solvable_of_inf_eq_bot hk h1) hXns
    · exact inf_eq_left.mp h1
  have hXNM : X ⊔ N = M := by
    have hle : X ⊔ N ≤ M := sup_le hXM hNM
    have hnorm : ((X ⊔ N).subgroupOf M).Normal := by
      have : (X ⊔ N).Normal := inferInstance
      infer_instance
    rcases hsimp (X ⊔ N) le_sup_right hle hnorm with h1 | h1
    · exfalso
      have : X ≤ N := h1 ▸ le_sup_left
      have h2 : X ≤ X ⊓ N := le_inf le_rfl this
      rw [hXN] at h2
      exact hX1 (le_bot_iff.mp h2)
    · exact h1
  have hnt : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  refine @IsSimpleGroup.mk _ _ hnt (fun X' hX' => ?_)
  set X'' : Subgroup Y := X'.map X.subtype with hX''
  have hX''X : X'' ≤ X := Subgroup.map_subtype_le X'
  have hX''n : ∀ x ∈ X, ∀ y ∈ X'', x * y * x⁻¹ ∈ X'' := by
    rintro x hx y ⟨y', hy', rfl⟩
    exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hX'.conj_mem y' hy' ⟨x, hx⟩, rfl⟩
  set N'' : Subgroup Y := X'' ⊔ N with hN''
  have hN''M : N'' ≤ M := sup_le (hX''X.trans hXM) hNM
  have hXnorm : X ≤ Subgroup.normalizer (N'' : Set Y) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' : y ∈ (↑N'' : Set Y) := hy
      rw [hN'', Subgroup.mul_normal] at hy'
      obtain ⟨a, ha, n, hn, rfl⟩ := hy'
      have e : x * (a * n) * x⁻¹ = (x * a * x⁻¹) * (x * n * x⁻¹) := by group
      rw [e]
      exact N''.mul_mem (Subgroup.mem_sup_left (hX''n x hx a ha))
        (Subgroup.mem_sup_right (hNn.conj_mem n hn x))
    · intro hy
      have hy' : x * y * x⁻¹ ∈ (↑N'' : Set Y) := hy
      rw [hN'', Subgroup.mul_normal] at hy'
      obtain ⟨a, ha, n, hn, hyx⟩ := hy'
      have hyx' : a * n = x * y * x⁻¹ := hyx
      have : y = (x⁻¹ * a * x) * (x⁻¹ * n * x) := by
        have e1 : (x⁻¹ * a * x) * (x⁻¹ * n * x) = x⁻¹ * (a * n) * x := by group
        rw [e1, hyx']; group
      rw [this]
      refine N''.mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · have := hX''n x⁻¹ (X.inv_mem hx) a ha
        simpa using this
      · have := hNn.conj_mem n hn x⁻¹
        simpa using this
  have hMnorm : M ≤ Subgroup.normalizer (N'' : Set Y) := by
    rw [← hXNM]
    refine sup_le hXnorm ?_
    intro n hn
    exact Subgroup.le_normalizer (Subgroup.mem_sup_right hn)
  have hnorm'' : (N''.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN''M).mpr hMnorm
  rcases hsimp N'' le_sup_right hN''M hnorm'' with h1 | h1
  ·
    left
    have h2 : X'' ≤ X ⊓ N := le_inf hX''X (h1 ▸ le_sup_left)
    rw [hXN] at h2
    have h3 : X'' = ⊥ := le_bot_iff.mp h2
    exact (Subgroup.map_eq_bot_iff_of_injective X' X.subtype_injective).mp h3
  ·
    right
    rw [eq_top_iff]
    intro x _
    have hxM : (x : Y) ∈ N'' := by rw [h1]; exact hXM x.2
    have hxM' : (x : Y) ∈ (↑N'' : Set Y) := hxM
    rw [hN'', Subgroup.mul_normal] at hxM'
    obtain ⟨a, ha, n, hn, hxa⟩ := hxM'
    have hxa' : a * n = (x : Y) := hxa
    have hnX : n ∈ X := by
      have : n = a⁻¹ * (x : Y) := by rw [← hxa']; group
      rw [this]
      exact X.mul_mem (X.inv_mem (hX''X ha)) x.2
    have hn1 : n = 1 := by
      have : n ∈ X ⊓ N := ⟨hnX, hn⟩
      rw [hXN, Subgroup.mem_bot] at this
      exact this
    rw [hn1, mul_one] at hxa'
    obtain ⟨y, hy, hyx⟩ := ha
    have : y = x := Subtype.ext (hyx.trans hxa')
    rw [← this]
    exact hy

theorem subgroupOf_comap_eq {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) (M : Subgroup Y)
    (N'' : Subgroup Z) :
    ((N''.comap π) ⊓ M).subgroupOf M = (N''.subgroupOf (M.map π)).comap (π.subgroupMap M) := by
  ext x
  simp [Subgroup.mem_subgroupOf, MonoidHom.subgroupMap_apply_coe]

theorem SolvSimpSolv.quotient {Y : Type} [Group Y] (N₁ : Subgroup Y) [N₁.Normal]
    (h : SolvSimpSolv Y) : SolvSimpSolv (Y ⧸ N₁) := by
  obtain ⟨M, N, hMn, hNn, hNM, hNs, ⟨k, hk⟩, hsimp⟩ := h
  set π := QuotientGroup.mk' N₁ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N₁
  have : M.Normal := hMn
  have : N.Normal := hNn
  refine ⟨M.map π, N.map π, Subgroup.Normal.map hMn π hπs, Subgroup.Normal.map hNn π hπs,
    Subgroup.map_mono hNM, ?_, ⟨k, ?_⟩, ?_⟩
  · exact Group.isSolvable_of_surjective (f := π.subgroupMap N)
      (MonoidHom.subgroupMap_surjective π N)
  · rw [← map_derivedSeries_eq hπs k]
    exact Subgroup.map_mono hk
  · intro N'' hN''1 hN''2 hnorm
    set Ñ : Subgroup Y := (N''.comap π) ⊓ M with hÑ
    have hNÑ : N ≤ Ñ := fun n hn => ⟨hN''1 ⟨n, hn, rfl⟩, hNM hn⟩
    have hÑM : Ñ ≤ M := inf_le_right
    have hÑn : (Ñ.subgroupOf M).Normal := by
      rw [hÑ, subgroupOf_comap_eq]
      exact Subgroup.Normal.comap hnorm _
    have hmap : Ñ.map π = N'' := by
      apply le_antisymm
      · rintro _ ⟨m, hm, rfl⟩
        exact hm.1
      · intro y hy
        obtain ⟨m, hmM, rfl⟩ := hN''2 hy
        exact ⟨m, ⟨hy, hmM⟩, rfl⟩
    rcases hsimp Ñ hNÑ hÑM hÑn with h1 | h1
    · left; rw [← hmap, h1]
    · right; rw [← hmap, h1]

theorem exists_derivedSeries_le_of_solvable {Y : Type} [Group Y] (M : Subgroup Y) [M.Normal]
    [Group.IsSolvable (Y ⧸ M)] : ∃ k : ℕ, derivedSeries Y k ≤ M := by
  obtain ⟨k, hk⟩ := (inferInstance : Group.IsSolvable (Y ⧸ M)).solvable
  refine ⟨k, ?_⟩
  have h1 := map_derivedSeries_eq (QuotientGroup.mk'_surjective M) k
  rw [hk, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

theorem SolvSimpSolv.sup_two {Y : Type} [Group Y] [Finite Y] (h : SolvSimpSolv Y)
    {N T : Subgroup Y} [N.Normal] (hN1 : N ≠ ⊥)
    (hmin : ∀ K : Subgroup Y, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    (hnab : ∃ a b : ↥N, a * b ≠ b * a) (hT : IsPGroup 2 T) : SolvSimpSolv ↥(N ⊔ T) := by
  have hsN : IsSimpleGroup ↥N := h.isSimpleGroup inferInstance hN1 hmin hnab
  set Z := N ⊔ T with hZ
  have hNZ : N ≤ Z := le_sup_left
  set M₀ : Subgroup ↥Z := N.subgroupOf Z with hM₀
  have : M₀.Normal := inferInstance
  have hqsolv : Group.IsSolvable (↥Z ⧸ M₀) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2q : IsPGroup 2 (↥Z ⧸ M₀) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M₀ q
      obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT (x : Y) x.2
      refine ⟨e, ?_⟩
      have hxD : x ^ 2 ^ e ∈ M₀ := by
        rw [hM₀, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact he
      exact (QuotientGroup.eq_one_iff _).mpr hxD
    have := h2q.isNilpotent
    infer_instance
  refine ⟨M₀, ⊥, inferInstance, inferInstance, bot_le, inferInstance,
    exists_derivedSeries_le_of_solvable M₀, ?_⟩
  intro N' _ hN'M _
  rename_i hnorm
  have hN'N : ∀ x ∈ N', ((x : ↥Z) : Y) ∈ N := fun x hx => hN'M hx
  set N₀ : Subgroup Y := N'.map Z.subtype with hN₀
  have hN₀N : N₀ ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN'N x hx
  have hconj : ∀ g ∈ N, ∀ y ∈ N₀, g * y * g⁻¹ ∈ N₀ := by
    intro g hg y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hgZ : g ∈ Z := hNZ hg
    have hg' : (⟨g, hgZ⟩ : ↥Z) ∈ M₀ := Subgroup.mem_subgroupOf.mpr hg
    set m : ↥M₀ := ⟨⟨g, hgZ⟩, hg'⟩ with hm
    set x' : ↥M₀ := ⟨x, Subgroup.mem_subgroupOf.mpr (hN'N x hx)⟩ with hx'def
    have hx' : x' ∈ N'.subgroupOf M₀ := Subgroup.mem_subgroupOf.mpr hx
    have := hnorm.conj_mem x' hx' m
    rw [Subgroup.mem_subgroupOf] at this
    exact ⟨_, this, rfl⟩
  set N₁ : Subgroup ↥N := N₀.subgroupOf N with hN₁
  have hN₁n : N₁.Normal := ⟨fun y hy g => hconj g g.2 y hy⟩
  rcases hsN.eq_bot_or_eq_top_of_normal N₁ with h1 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxN : (⟨(x : Y), hN'N x hx⟩ : ↥N) ∈ N₁ :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    rw [h1, Subgroup.mem_bot] at hxN
    have : (x : Y) = 1 := congrArg Subtype.val hxN
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  · right
    apply le_antisymm hN'M
    intro m hm
    have hmN : (m : Y) ∈ N := Subgroup.mem_subgroupOf.mp hm
    have : (⟨(m : Y), hmN⟩ : ↥N) ∈ N₁ := by rw [h1]; trivial
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_subgroupOf.mp this
    have : x = m := Subtype.ext hxm
    rw [← this]
    exact hx

@[expose] def E111CoreMultiQnC (Q : GrpPred) (C : (G : Type) → [Group G] → Prop) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G),
    ASInputs.E111Hyp G n → SecAll G Q → C G →
    (∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → ASInputs.E111Hyp G' n →
      SecAll G' Q → C G' → E1.InE n (⊤ : Subgroup G')) →
    E111Reduced G X T → ¬ IsSimpleGroup ↥X → E1.InEFor n ⊤ T

theorem inE_of_e111Hyp_QC {Q : GrpPred} {C : (G : Type) → [Group G] → Prop} (hQ : IsoInv Q)
    (hCq : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], C G → C (G ⧸ N))
    (hCs : ∀ (G : Type) [Group G] [Finite G] (N T : Subgroup G) [N.Normal], C G → N ≠ ⊥ →
      (∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) → (∃ a b : ↥N, a * b ≠ b * a) →
      IsPGroup 2 T → C ↥(N ⊔ T))
    {n : ℕ} (hn : 1 ≤ n) (hMulti : E111CoreMultiQnC Q C n) :
    ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ k → ASInputs.E111Hyp G n →
      SecAll G Q → C G → E1.InE n (⊤ : Subgroup G) := by
  intro k
  induction k with
  | zero =>
    intro G _ _ h _ _
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ k ih =>
    intro G _ _ hk hH hK hCl
    have hIH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
        ASInputs.E111Hyp G' n → SecAll G' Q → C G' → E1.InE n (⊤ : Subgroup G') :=
      fun G' _ _ hlt hH' hK' hC' => ih G' (by omega) hH' hK' hC'
    by_cases hsub : Subsingleton G
    · refine E1.inE_of_odd ?_
      rw [Subgroup.card_top, Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩]
      exact odd_one
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsec := (e111Hyp_iff_secAll n).mp hH
    intro T hT
    have hquot : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → (∀ Ω : Set (Subgroup G),
        E1.IsInvColl ⊤ Ω → N ≤ E1.eGen n ⊤ T Ω ⊔
          (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G))) → E1.InEFor n ⊤ T := by
      intro N hN hN1 hNM
      have : N.Normal := hN
      have hlt : Nat.card (G ⧸ N) < Nat.card G := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN1
        have h3 := Nat.card_pos (α := G ⧸ N)
        nlinarith
      have hHq : ASInputs.E111Hyp (G ⧸ N) n :=
        (e111Hyp_iff_secAll n).mpr (secAll_quotient (isoInv_e111Prop n) N hsec)
      exact E1.inEFor_of_quotient (hIH _ hlt hHq (secAll_quotient hQ N hK) (hCq G N hCl)) hT hNM
    have hTM : ∀ Ω : Set (Subgroup G), E1.IsInvColl ⊤ Ω → T ≤ E1.eGen n ⊤ T Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) := fun Ω hΩ x hx =>
      Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ hx⟩
    by_cases hsol : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
        (∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) ∧ Group.IsSolvable ↥N
    ·
      obtain ⟨N, hN, hN1, hmin, hNs⟩ := hsol
      have : N.Normal := hN
      have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => hmin K hK hKN⟩
      obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
      have hNp : IsPGroup r N := CFSG.IsElementaryAbelian.isPGroup r N
      refine hquot N hN hN1 fun Ω hΩ => ?_
      by_cases hr2 : r = 2
      · subst hr2
        exact (hT.le_of_normal le_top (Subgroup.normal_subgroupOf) hNp).trans (hTM Ω hΩ)
      · exact E1.normal_pGroup_le hr hr2 hT hNp hΩ
          ((E1.eGen_mono hn ⊤ T Ω).trans le_sup_left)
          (fun x hx => Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩)
    obtain ⟨N, hN, -, hN1, hNmin⟩ := CFSG.exists_minimal_normal_le (⊤ : Subgroup G) inferInstance
      (bot_ne_top : (⊥ : Subgroup G) ≠ ⊤).symm
    have : N.Normal := hN
    have hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := fun K hK hKN => by
      by_cases hK1 : K = ⊥
      · exact Or.inl hK1
      · exact Or.inr (hNmin K hK hKN hK1)
    have hNns : ¬ Group.IsSolvable ↥N := fun h => hsol ⟨N, hN, hN1, hmin, h⟩
    have hnab : ∃ a b : ↥N, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      exact hNns (Group.isSolvable_of_comm hc)
    by_cases hNT : N ⊔ T = ⊤
    ·
      have hC : Subgroup.centralizer (N : Set G) = ⊥ := by
        by_contra hC1
        have hCn : (Subgroup.centralizer (N : Set G)).Normal := inferInstance
        obtain ⟨N', hN', hN'C, hN'1, hN'min⟩ := CFSG.exists_minimal_normal_le _ hCn hC1
        have hmin' : ∀ K : Subgroup G, K.Normal → K ≤ N' → K = ⊥ ∨ K = N' := fun K hK hKN => by
          by_cases hK1 : K = ⊥
          · exact Or.inl hK1
          · exact Or.inr (hN'min K hK hKN hK1)
        have : N'.Normal := hN'
        have hinf : N' ⊓ N = ⊥ := by
          rcases hmin (N' ⊓ N) inferInstance inf_le_right with h | h
          · exact h
          · exfalso
            apply hNns
            refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
            have hb : (b : G) ∈ N' := (h ▸ inf_le_left : N ≤ N') b.2
            exact (Subgroup.mem_centralizer_iff.mp (hN'C hb) a a.2)
        have hN'2 : IsPGroup 2 ↥N' := by
          intro x
          obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT.2.1 (x : G) (hNT ▸ Subgroup.mem_top _)
          refine ⟨e, Subtype.ext ?_⟩
          have hxe : (x : G) ^ 2 ^ e ∈ N' ⊓ N := ⟨N'.pow_mem x.2 _, he⟩
          rw [hinf, Subgroup.mem_bot] at hxe
          simpa using hxe
        have := hN'2.isNilpotent
        exact hsol ⟨N', hN', hN'1, hmin', inferInstance⟩
      have hR : E111Reduced G N T := ⟨hN, hN1, hmin, hnab, hC, hT, hNT⟩
      by_cases hNs : IsSimpleGroup ↥N
      · exact inEFor_of_reduced_simple hn hR hNs hH
      · exact hMulti G N T hH hK hCl hIH hR hNs
    ·
      refine hquot N hN hN1 fun Ω hΩ => ?_
      set Y := N ⊔ T with hY
      have hYlt : Nat.card ↥Y < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hNT ((Subgroup.card_eq_iff_eq_top Y).mp h)
      have hHY : ASInputs.E111Hyp ↥Y n :=
        (e111Hyp_iff_secAll n).mpr (secAll_sup_of_normal (isoInv_e111Prop n) hT.2.1 hsec)
      have hInEY : E1.InE n Y := (E1.inE_subgroupOf n Y).mpr
        (hIH _ hYlt hHY (secAll_sup_of_normal hQ hT.2.1 hK)
          (hCs G N T hCl hN1 hmin hnab hT.2.1))
      have hTY : IsSylowIn 2 T Y := by
        refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
        have := Subgroup.relIndex_mul_relIndex T Y ⊤ le_sup_right le_top
        rw [← this]
        exact Dvd.dvd.mul_right h2 _
      exact le_sup_left.trans (le_of_inEFor_sub hT le_sup_right (hInEY T hTY) hΩ)

theorem solvSimpSolv_of_hom {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z)
    (hker : Group.IsSolvable ↥f.ker) (Ks : Subgroup Z) [Ks.Normal] (hKs : IsSimpleGroup ↥Ks)
    (hKsf : Ks ≤ f.range) (hZ : ∃ k : ℕ, derivedSeries Z k ≤ Ks) : SolvSimpSolv Y := by
  obtain ⟨k, hk⟩ := hZ
  refine ⟨Ks.comap f, f.ker, inferInstance, inferInstance, ?_, hker, ⟨k, ?_⟩, ?_⟩
  · intro y hy
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hy]
    exact Ks.one_mem
  · intro y hy
    exact hk (map_derivedSeries_le_derivedSeries f k ⟨y, hy, rfl⟩)
  · intro N' hN'1 hN'2 hnorm
    set M₀ : Subgroup Y := Ks.comap f with hM₀
    set N'' : Subgroup Z := N'.map f with hN''
    have hN''K : N'' ≤ Ks := by
      rintro _ ⟨x, hx, rfl⟩
      exact hN'2 hx
    have hconj : ∀ g ∈ Ks, ∀ y ∈ N'', g * y * g⁻¹ ∈ N'' := by
      intro g hg y hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨m, rfl⟩ := hKsf hg
      have hm : m ∈ M₀ := hg
      set m' : ↥M₀ := ⟨m, hm⟩
      set x' : ↥M₀ := ⟨x, hN'2 hx⟩
      have hx' : x' ∈ N'.subgroupOf M₀ := Subgroup.mem_subgroupOf.mpr hx
      have := hnorm.conj_mem x' hx' m'
      rw [Subgroup.mem_subgroupOf] at this
      exact ⟨_, this, by simp [m', x']⟩
    set N₁ : Subgroup ↥Ks := N''.subgroupOf Ks with hN₁
    have hN₁n : N₁.Normal := ⟨fun y hy g => hconj g g.2 y hy⟩
    rcases hKs.eq_bot_or_eq_top_of_normal N₁ with h1 | h1
    · left
      apply le_antisymm _ hN'1
      intro x hx
      have hxK : (⟨f x, hN'2 hx⟩ : ↥Ks) ∈ N₁ := Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hxK
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hxK)
    · right
      apply le_antisymm hN'2
      intro y hy
      have hyK : (⟨f y, hy⟩ : ↥Ks) ∈ N₁ := by rw [h1]; trivial
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.mp hyK
      have hker' : x⁻¹ * y ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      have := N'.mul_mem hx (hN'1 hker')
      simpa using this

theorem e111CoreMultiQnC_sss (Q : GrpPred) (n : ℕ) : E111CoreMultiQnC Q SolvSimpSolv n := by
  intro G _ _ X T _ _ hS _ hR hns
  obtain ⟨hXn, hX1, hmin, hnab, -, -, -⟩ := hR
  exact absurd (hS.isSimpleGroup hXn hX1 hmin hnab) hns

theorem e111ForQnC_sss {Q : GrpPred} (hQ : IsoInv Q) {n : ℕ} (hn : 1 ≤ n)
    (G : Type) [Group G] [Finite G] (hH : ASInputs.E111Hyp G n) (hK : SecAll G Q)
    (hS : SolvSimpSolv G) : E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞) := by
  have h := inE_of_e111Hyp_QC hQ (fun G _ _ N _ h => h.quotient N)
    (fun G _ _ N T _ h hN1 hmin hnab hT => h.sup_two hN1 hmin hnab hT) hn
    (e111CoreMultiQnC_sss Q n) (Nat.card G) G le_rfl hH hK hS
  rw [E1.nParam_le_iff (by omega)]
  exact h

end CFSG.Quasithin.E2.E22N
