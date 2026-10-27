module

public import CFSG.Quasithin.EmptyFaithful.S146zUF3Triv
public import CFSG.Quasithin.EmptyFaithful.S146zUEPkg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace S146zU

namespace UF3

section Dict

variable {G : Type} [Group G]

theorem card_tildeOf_relIndex {V₁ X : Subgroup G} (hV₁X : V₁ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V₁ : Set G)) :
    Nat.card ↥(tildeOf V₁ X) = V₁.relIndex X := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (T := V₁)
    (H := X) le_rfl hV₁X hXN
  have h2 : secImg (Subgroup.normalizer (V₁ : Set G)) V₁ V₁ = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  exact h1

theorem card_subM_relIndex {V₁ IH J : Subgroup G} (hV₁J : V₁ ≤ J) (hJI : J ≤ IH)
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) :
    Nat.card ↥(subM V₁ IH J) = V₁.relIndex J := by
  have h1 : Nat.card ↥(subM V₁ IH J) = Nat.card ↥(tildeOf V₁ J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tildeOf_le_tildeOf V₁ hJI)).toEquiv
  rw [h1]
  exact card_tildeOf_relIndex hV₁J (hJI.trans hIHN)

theorem tildeHom_mem_subM_iff {V₁ IH J : Subgroup G} (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hV₁J : V₁ ≤ J) (u : ↥IH) : tildeHom hIHN u ∈ subM V₁ IH J ↔ (u : G) ∈ J :=
  modMk_mem_subM_iff hIHN hV₁J u.2

theorem commutator_le_of_le_normalizer' {U P : Subgroup G}
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) : ⁅U, P⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro u hu p hp
  have hu' : p * u⁻¹ * p⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hPU hp) u⁻¹).mp (U.inv_mem hu)
  have : ⁅u, p⁆ = u * (p * u⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact U.mul_mem hu hu'

section Mod

attribute [local instance] commGroupOfFact

variable {V₁ IH H : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

theorem commV_zpowers_le_subM (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    {J : Subgroup G} (hV₁J : V₁ ≤ J) {b : G} (hb : b ∈ H) (hJ : ⁅IH, Subgroup.zpowers b⁆ ≤ J) :
    commV (Subgroup.zpowers (actH hV₁ hIH ⟨b, hb⟩)) ≤ subM V₁ IH J := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x', hx', v, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  obtain ⟨u, rfl⟩ := tildeHom_surjective hIHN v
  set y : ↥H := (⟨b, hb⟩ : ↥H) ^ k with hy
  have hyb : (y : G) = b ^ k := by simp [hy]
  have hxy : actH hV₁ hIH ⟨b, hb⟩ ^ k = actH hV₁ hIH y := (map_zpow _ _ _).symm
  have hyu : (y : G) * u * (y : G)⁻¹ ∈ IH := (Subgroup.mem_normalizer_iff.mp (hIH y.2) u).mp u.2
  show (actH hV₁ hIH ⟨b, hb⟩ ^ k) (tildeHom hIHN u) * (tildeHom hIHN u)⁻¹ ∈ subM V₁ IH J
  rw [hxy, actH_tildeHom hV₁ hIH hIHN y u ⟨_, hyu⟩ rfl, ← map_inv, ← map_mul,
    tildeHom_mem_subM_iff hIHN hV₁J]
  have hmem : ⁅(u : G), b ^ k⁆ ∈ J :=
    hJ (Subgroup.commutator_mem_commutator u.2 (Subgroup.zpow_mem_zpowers b k))
  have e : (y : G) * u * (y : G)⁻¹ * (u : G)⁻¹ = (⁅(u : G), b ^ k⁆)⁻¹ := by
    rw [hyb, commutatorElement_def]; group
  show (y : G) * u * (y : G)⁻¹ * (u : G)⁻¹ ∈ J
  rw [e]
  exact J.inv_mem hmem

end Mod

end Dict

section Offender

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))]

theorem offender_of_data (h : HypF91 T V L V₁ Vp H) (hV₁N : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hUN : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G))
    {A D A₁ : Subgroup G} (hAH : A ≤ H) (hAel : IsElemAbelian 2 A) (hAQ : ¬ A ≤ pCoreOf 2 H)
    (hrank : mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) ≤
      2 * mIdx A (A ⊓ pCoreOf 2 H))
    (hcard : Nat.card A₁ = 2) (hDU : D ≤ conjClosure Vp H) (hV₁D : V₁ ≤ D)
    (hAD : ⁅A, D⁆ ≤ A₁)
    (heq : mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) =
        2 * mIdx A (A ⊓ pCoreOf 2 H) →
      mIdx (conjClosure Vp H) D = mIdx A (A ⊓ pCoreOf 2 H) ∧ ⁅A, D⁆ = A₁ ∧
        A₁ ≤ conjClosure Vp H) :
    ∃ A' : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H))),
      A' ≤ (actH hV₁N hUN).range ∧ A' ≠ ⊥ ∧ IsElemAbelian2 A' ∧
      Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) ≤
        Nat.card A' * Nat.card A' * Nat.card ↥(fixV A') ∧
      (Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) =
          Nat.card A' * Nat.card A' * Nat.card ↥(fixV A') →
        ∃ (D' : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
          (c : ↥(tildeOf V₁ (conjClosure Vp H))),
          Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) = Nat.card A' * Nat.card D' ∧
          ∀ a ∈ A', ∀ d ∈ D', a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c) := by
  classical
  have hŨ : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) := Fact.out
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hUH : conjClosure Vp H ≤ H := hUQ.trans (pCoreOf_le 2 H)
  have hUV₁ : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) := hUH.trans hV₁N
  have hUp : IsPGroup 2 (conjClosure Vp H) := h.isPGroup_conjClosure
  have hAp : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAel
  have hn := HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) hAH
  have hBt : IsElemAbelian 2 (tildeOf V₁ A) := isElemAbelian_secImg hAel
  have hmap := autOn_tilde_eq_map_actH hV₁N hUN hAH
  have hA2 : IsElemAbelian2 (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H))) :=
    isElemAbelian2_autOn hŨ hBt hn
  have c1 := h.card_autOn_tilde hAH
  have c2 := card_fixV_autOn_eq hŨ hn
  have c3 := h.relIndex_tilde_fixV hAH
  have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := centralizerMod V₁ (conjClosure Vp H) A) hUp
  have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := A ⊓ pCoreOf 2 H) hAp
  have hmul := Subgroup.relIndex_mul_card (tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ A : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))
    (tildeOf V₁ (conjClosure Vp H))
  rw [inf_eq_left.mpr (inf_le_left : tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ A : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) ≤
      tildeOf V₁ (conjClosure Vp H))] at hmul
  have hcardY : Nat.card ↥(tildeOf V₁ (conjClosure Vp H)) =
      2 ^ mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) *
        Nat.card ↥(fixV (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H)))) := by
    rw [c2, ← e1, ← c3]
    exact hmul.symm
  have hF : 0 < Nat.card ↥(fixV (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H)))) :=
    Nat.card_pos
  have hA'card : Nat.card ↥(autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H))) =
      2 ^ mIdx A (A ⊓ pCoreOf 2 H) := by rw [c1, e2]
  refine ⟨autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H)), ?_, ?_, hA2, ?_, ?_⟩
  · rw [hmap]
    exact Subgroup.map_le_range _ _
  · obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
    have haH : a ∈ H := hAH haA
    have hne : actH hV₁N hUN ⟨a, haH⟩ ≠ 1 := fun h1 => by
      have h2 : (a : G) ∈ pCoreOf 2 H :=
        (actH_eq_one_iff_mem_pCoreOf h hV₁N hUN hUV₁ ⟨a, haH⟩).mp h1
      exact haQ h2
    intro hbot
    rw [hmap] at hbot
    have hmem : actH hV₁N hUN ⟨a, haH⟩ ∈
        (A.subgroupOf H).map (actH hV₁N hUN) :=
      ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne hmem
  · rw [hcardY, hA'card]
    calc 2 ^ mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) *
          Nat.card ↥(fixV (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H))))
        ≤ 2 ^ (2 * mIdx A (A ⊓ pCoreOf 2 H)) *
          Nat.card ↥(fixV (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H)))) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos hrank)
      _ = 2 ^ mIdx A (A ⊓ pCoreOf 2 H) * 2 ^ mIdx A (A ⊓ pCoreOf 2 H) *
          Nat.card ↥(fixV (autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H)))) := by
        rw [two_mul, pow_add]
  · intro hEq
    rw [hcardY, hA'card] at hEq
    have hm : mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) =
        2 * mIdx A (A ⊓ pCoreOf 2 H) := by
      have h1 : 2 ^ mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) A) =
          2 ^ mIdx A (A ⊓ pCoreOf 2 H) * 2 ^ mIdx A (A ⊓ pCoreOf 2 H) :=
        Nat.eq_of_mul_eq_mul_right hF hEq
      rw [← pow_add] at h1
      have := Nat.pow_right_injective (le_refl 2) h1
      omega
    obtain ⟨hD1, -, hD3⟩ := heq hm
    obtain ⟨a₁, ha₁1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A₁)).mp hcard
    have ha₁ : ∀ x ∈ A₁, x = 1 ∨ x = (a₁ : G) := fun x hx => by
      by_cases hx1 : (⟨x, hx⟩ : ↥A₁) = 1
      · exact Or.inl (by simpa using congrArg Subtype.val hx1)
      · exact Or.inr (by simpa using congrArg Subtype.val (huniq _ hx1))
    refine ⟨subM V₁ (conjClosure Vp H) D, tildeHom hUV₁ ⟨(a₁ : G), hD3 a₁.2⟩, ?_, ?_⟩
    · have hDsub := card_subM_relIndex hV₁D hDU hUV₁
      have hY := card_tildeOf_relIndex (hV₁D.trans hDU) hUV₁
      have hmulidx := Subgroup.relIndex_mul_relIndex V₁ D (conjClosure Vp H) hV₁D hDU
      have e3 := HypF98.relIndex_eq_two_pow_mIdx (Y := D) hUp
      rw [hA'card]
      calc Nat.card ↥(tildeOf V₁ (conjClosure Vp H))
          = V₁.relIndex (conjClosure Vp H) := hY
        _ = V₁.relIndex D * D.relIndex (conjClosure Vp H) := hmulidx.symm
        _ = V₁.relIndex D * 2 ^ mIdx A (A ⊓ pCoreOf 2 H) := by rw [e3, hD1]
        _ = 2 ^ mIdx A (A ⊓ pCoreOf 2 H) * Nat.card ↥(subM V₁ (conjClosure Vp H) D) := by
          rw [hDsub, mul_comm]
    · intro a ha d hd
      rw [hmap] at ha
      obtain ⟨⟨a₀, ha₀H⟩, ha₀A, rfl⟩ := ha
      have ha₀A' : a₀ ∈ A := Subgroup.mem_subgroupOf.mp ha₀A
      obtain ⟨u, rfl⟩ := tildeHom_surjective hUV₁ d
      have hu : (u : G) ∈ D := (tildeHom_mem_subM_iff hUV₁ hV₁D u).mp hd
      have hv : a₀ * (u : G) * a₀⁻¹ ∈ conjClosure Vp H :=
        (Subgroup.mem_normalizer_iff.mp (hUN ha₀H) u).mp u.2
      have h1 := actH_tildeHom hV₁N hUN hUV₁ ⟨a₀, ha₀H⟩ u ⟨_, hv⟩ rfl
      have hcomm : a₀ * (u : G) * a₀⁻¹ * (u : G)⁻¹ ∈ A₁ := by
        have := hAD (Subgroup.commutator_mem_commutator ha₀A' hu)
        rwa [commutatorElement_def] at this
      show (actH hV₁N hUN ⟨a₀, ha₀H⟩) (tildeHom hUV₁ u) * (tildeHom hUV₁ u)⁻¹ = 1 ∨
        (actH hV₁N hUN ⟨a₀, ha₀H⟩) (tildeHom hUV₁ u) * (tildeHom hUV₁ u)⁻¹ =
          tildeHom hUV₁ ⟨(a₁ : G), hD3 a₁.2⟩
      rw [h1, ← map_inv, ← map_mul]
      rcases ha₁ _ hcomm with h2 | h2
      · left
        have : (⟨a₀ * (u : G) * a₀⁻¹, hv⟩ * u⁻¹ : ↥(conjClosure Vp H)) = 1 :=
          Subtype.ext (by simpa using h2)
        rw [this, map_one]
      · right
        congr 1
        exact Subtype.ext (by simpa using h2)

end Offender

section Setting

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem Z_le_uOfL22 (T M : Subgroup G) : quasithinOmegaOneCenter T ≤ uOfL22 T M :=
  (le_conjClosure _ _ : quasithinOmegaOneCenter T ≤ VZ T M).trans (le_conjClosure _ _)

theorem hNT_of_nt (S : Setting146 G T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))]
    (hnt : ∀ x ∈ (actH hZN hUN).range, x ≠ 1 → 4 ≤ Nat.card ↥(commV (Subgroup.zpowers x))) :
    ∀ b ∈ mcOf T, b ∉ pCoreOf 2 (mcOf T) →
      2 ≤ mIdx (⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T)
        (quasithinOmegaOneCenter T) := by
  intro b hb hbQ
  have hZU := Z_le_uOfL22 T M
  have hUZ := uOfL22_le_normalizer_Z S
  have hJU : ⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T ≤ uOfL22 T M :=
    sup_le (commutator_le_of_le_normalizer' (Subgroup.zpowers_le.mpr (hUN hb))) hZU
  have hx1 : actH hZN hUN ⟨b, hb⟩ ≠ 1 := fun h =>
    hbQ ((actH_Z_U_eq_one_iff S hZN hUN ⟨b, hb⟩).mp h)
  have h4 := hnt _ ⟨⟨b, hb⟩, rfl⟩ hx1
  have hle := commV_zpowers_le_subM hZN hUN hUZ
    (J := ⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T) le_sup_right hb le_sup_left
  have hcard := card_subM_relIndex (le_sup_right : quasithinOmegaOneCenter T ≤
    ⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T) hJU hUZ
  have h5 := h4.trans ((Subgroup.card_le_of_le hle).trans hcard.le)
  have hJp : IsPGroup 2 ↥(⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T) :=
    (B2F.isPGroup_of_isElemAbelian (isElemAbelian_uOfL22 S)).to_le hJU
  rw [HypF98.relIndex_eq_two_pow_mIdx hJp] at h5
  by_contra hlt
  have h6 : mIdx (⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T)
      (quasithinOmegaOneCenter T) ≤ 1 := by omega
  have h7 := Nat.pow_le_pow_right (two_pos : 0 < 2) h6
  omega

theorem hgeom_of_pkg (S : Setting146 G T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))]
    {A D A₁ : Subgroup G} (P : GeomPkg T M A D A₁) :
    ∃ A' : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))),
      A' ≤ (actH hZN hUN).range ∧ A' ≠ ⊥ ∧ IsElemAbelian2 A' ∧
      Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) ≤
        Nat.card A' * Nat.card A' * Nat.card ↥(fixV A') ∧
      (Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) =
          Nat.card A' * Nat.card A' * Nat.card ↥(fixV A') →
        ∃ (D' : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))
          (c : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))),
          Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) =
            Nat.card A' * Nat.card D' ∧
          ∀ a ∈ A', ∀ d ∈ D', a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c) := by
  have : Fact (IsElemAbelian 2
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T)))) :=
    ⟨(Fact.out : IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))⟩
  exact offender_of_data (hypF91_mcOf S) hZN hUN P.le_mcOf P.isElemAbelian P.not_le_pCoreOf
    P.rank_le P.card_A₁ P.D_le P.Z_le_D P.commutator_D_le P.eq_case

theorem hgeom_of_UE (S : Setting146 G T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))] :
    (∀ x ∈ (actH hZN hUN).range, x ≠ 1 → 4 ≤ Nat.card ↥(commV (Subgroup.zpowers x))) →
      ∃ A : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))),
        A ≤ (actH hZN hUN).range ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
        Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) ≤
          Nat.card A * Nat.card A * Nat.card ↥(fixV A) ∧
        (Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) =
            Nat.card A * Nat.card A * Nat.card ↥(fixV A) →
          ∃ (D : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)))
            (c : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))),
            Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) =
              Nat.card A * Nat.card D ∧
            ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c) := fun hnt => by
  obtain ⟨A, D, A₁, P⟩ := geom_package S (hNT_of_nt S hZN hUN hnt)
  exact hgeom_of_pkg S hZN hUN P

end Setting

end UF3

end S146zU

end CFSG.Quasithin
