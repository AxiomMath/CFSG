module

public import CFSG.Quasithin.Background.A3Structure313Core
public import CFSG.Quasithin.Background.A3Structure312

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

abbrev oddCoreSub {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore ↥H).map H.subtype

@[expose] def A313Statement {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ∃ p r : ℕ, p.Prime ∧ 3 < p ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L) ∧
    (∃ (N : Subgroup ↥(B ⊔ oddCoreSub L)) (_ : N.Normal),
      N = (oddCoreSub L).subgroupOf (B ⊔ oddCoreSub L) ∧
        IsSL2 r (↥(B ⊔ oddCoreSub L) ⧸ N)) ∧
    (r = p ∨ (r = 5 ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5))) ∧
    ((CFSG.IsQuasisimple ↥B ∧ IsSL2 r ↥B) ∨
      (¬ CFSG.IsQuasisimple ↥B ∧
        ((L = B ⊔ oddCoreSub L ∧ oddCoreSub B < oddCoreSub L ∧ r = 5 ∧ p = 5) ∨
         (B ⊔ oddCoreSub L < L ∧
          IsExt ↥L (fun V _ => IsElemAbelianOfRank p 2 V) (fun Y _ => IsSL2 p Y) ∧
          5 < p ∧ r = 5 ∧ oddCoreSub B = oddCoreSub L))))

namespace A313

variable {G : Type} [Group G]

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm,
    (CFSG.oddCore_eq_piCore Y).trans (CFSG.pPrimeCore_eq_piCore Y 2).symm]
  exact CFSG.pPrimeCore_map_iso 2 e

theorem map_oddCoreSub_subgroupOf {B L : Subgroup G} (hBL : B ≤ L) :
    ((CFSG.oddCore ↥(B.subgroupOf L)).map (B.subgroupOf L).subtype).map L.subtype =
      oddCoreSub B := by
  let eB : ↥(B.subgroupOf L) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL
  show _ = (CFSG.oddCore ↥B).map B.subtype
  rw [← oddCore_map_mulEquiv eB, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem imgOdd_eq_top_iff {B L : Subgroup G} (hBL : B ≤ L) :
    imgOdd (B.subgroupOf L) = ⊤ ↔ L = B ⊔ oddCoreSub L := by
  have hOLL : oddCoreSub L ≤ L := Subgroup.map_subtype_le _
  constructor
  · intro h
    refine le_antisymm (fun l hl => ?_) (sup_le hBL hOLL)
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥L) (⟨l, hl⟩ : ↥L) ∈ imgOdd (B.subgroupOf L) := by
      rw [h]
      trivial
    obtain ⟨b, hb, hbl⟩ := h1
    have h2 : b⁻¹ * ⟨l, hl⟩ ∈ CFSG.oddCore ↥L :=
      (QuotientGroup.eq (s := CFSG.oddCore ↥L)).mp hbl
    have h3 : (b : G)⁻¹ * l ∈ oddCoreSub L := ⟨b⁻¹ * ⟨l, hl⟩, h2, rfl⟩
    have : l = (b : G) * ((b : G)⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hb h3
  · intro hLB
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥L) z
    have hl' : l ∈ (↑(B ⊔ oddCoreSub L) : Set G) := by
      rw [← hLB]
      exact hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B (oddCoreSub L)
      (hBL.trans (A312.le_normalizer_oddCoreSub L))] at hl'
    obtain ⟨b, hb, o, ho, hbo⟩ := hl'
    refine ⟨⟨b, hBL hb⟩, hb, ?_⟩
    show QuotientGroup.mk (⟨b, hBL hb⟩ : ↥L) = QuotientGroup.mk ⟨l, hl⟩
    rw [QuotientGroup.eq]
    obtain ⟨y, hy, hyo⟩ := ho
    have : (⟨b, hBL hb⟩ : ↥L)⁻¹ * ⟨l, hl⟩ = y := by
      apply Subtype.ext
      show b⁻¹ * l = (y : G)
      have hyo' : (y : G) = o := hyo
      have hbo' : b * o = l := hbo
      rw [hyo', ← hbo']
      group
    rw [this]
    exact hy

theorem case34_of_not_quasisimple {L : Subgroup G} (h : A36Strong L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) : A36Case3 ↥L ∨ A36Case4 ↥L := by
  obtain ⟨hconcl, -, -⟩ := h
  rcases hconcl with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact absurd hc.1 hnq
  · exact absurd hc.1 hnq
  · exact Or.inl h3
  · exact Or.inr h4

theorem mod_five_of_sq {p : ℕ} (h : p ^ 2 % 5 = 1) : p % 5 = 1 ∨ p % 5 = 4 := by
  have h1 := Nat.pow_mod p 2 5
  have h2 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : p % 5 <;> simp_all

theorem ne_five_of_sq {p : ℕ} (h : p ^ 2 % 5 = 1) : p ≠ 5 := by
  rintro rfl
  norm_num at h

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

end A313

theorem a313 (hmult : L2MultiplierFact) {G : Type} [Group G] (hG : SQTKHyp G)
    (h36 : A36Statement G) (h312 : A312Refined G) {T B L : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hL : L ∈ cComp (⊤ : Subgroup G))
    (hBL : B < L) (hnq : ¬ CFSG.IsQuasisimple ↥L) : A313Statement B L := by
  have : Finite G := hG.finite
  obtain ⟨L₀, hL₀, hBL₀, huniq, hcases⟩ := h312 T hT B hB
  have hLL₀ : L = L₀ := huniq L hL hBL.le
  subst hLL₀
  have hnonq : A312Nonquasi B L := by
    rcases hcases with h | ⟨hq, -⟩ | ⟨-, h⟩
    · exact absurd h hBL.ne
    · exact absurd hq hnq
    · exact h
  have h36L := h36 L hL
  have hcase := A313.case34_of_not_quasisimple h36L hnq
  obtain ⟨p₀, hp₀, hp₀3, hΛ⟩ := A312.exists_isSL2_oddCore h36L hnq
  have hcom := h36L.2.1
  have hr5₀ : 5 ≤ p₀ := A313.five_le_of_prime hp₀ hp₀3
  set B' : Subgroup ↥L := B.subgroupOf L with hB'
  have hB'top : B' ≠ ⊤ := by
    intro h
    apply hBL.ne
    refine le_antisymm hBL.le (fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥L) ∈ B' := by rw [h]; trivial
    exact this
  have hOLnorm := A312.normal_subgroupOf_sup_oddCoreSub hBL.le
  let eB : ↥B' ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL.le
  have hqB : CFSG.IsQuasisimple ↥B' ↔ CFSG.IsQuasisimple ↥B :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eB,
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm⟩
  unfold A312Nonquasi at hnonq
  dsimp only at hnonq
  rcases hnonq with ⟨hOL, hLB, p₁, hp₁, hp₁2, hpSL₁⟩ |
    ⟨hOL, ⟨p₂, hp₂, hp₂5, hp₂8, hpSL₂⟩, N, hNn, hNeq, hN5⟩
  ·
    have htop : A313.imgOdd B' = ⊤ := (A313.imgOdd_eq_top_iff hBL.le).mpr hLB
    have hM : IsSL2 p₀ ↥(A313.imgOdd B') :=
      IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
    have hcore := A313.core hmult hcom hcase hp₀ hp₀3 hΛ hB'top hp₀ hr5₀ hM (Or.inl ⟨htop, rfl⟩)
    refine ⟨p₀, p₀, hp₀, hp₀3, hΛ, ⟨_, hOLnorm, rfl,
      IsSL2.of_mulEquiv (A312.quotEquivImage hBL.le).symm hM⟩, Or.inl rfl, ?_⟩
    rcases hcore with ⟨hq, hsl⟩ | ⟨hnq', hcs⟩
    · exact Or.inl ⟨hqB.mp hq, IsSL2.of_mulEquiv eB hsl⟩
    · refine Or.inr ⟨fun h => hnq' (hqB.mpr h), ?_⟩
      rcases hcs with ⟨-, hlt, hr5', hp5⟩ | ⟨hntop, -⟩
      · refine Or.inl ⟨hLB, ?_, hr5', hp5⟩
        rw [← A313.map_oddCoreSub_subgroupOf hBL.le]
        exact lt_of_le_of_ne (Subgroup.map_mono hlt.le) fun h =>
          hlt.ne (Subgroup.map_injective L.subtype_injective h)
      · exact absurd htop hntop
  ·
    subst hNeq
    have hpp : p₂ = p₀ := A313.IsSL2.eq_of_isSL2 hp₂ hp₀ hpSL₂ hΛ
    subst hpp
    have hM : IsSL2 5 ↥(A313.imgOdd B') := IsSL2.of_mulEquiv (A312.quotEquivImage hBL.le) hN5
    have hp0ne : p₂ ≠ 5 := A313.ne_five_of_sq hp₂5
    have hntop : A313.imgOdd B' ≠ ⊤ := by
      intro htop
      have hM' : IsSL2 p₂ ↥(A313.imgOdd B') :=
        IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
      exact hp0ne (A313.IsSL2.eq_of_isSL2 hp₀ Nat.prime_five hM' hM)
    have hcore := A313.core hmult hcom hcase hp₀ hp₀3 hΛ hB'top (r := 5) Nat.prime_five le_rfl
      hM (Or.inr ⟨hntop, rfl, hp0ne⟩)
    refine ⟨p₂, 5, hp₀, hp₀3, hΛ, ⟨_, hNn, rfl, hN5⟩,
      Or.inr ⟨rfl, A313.mod_five_of_sq hp₂5, hp₂8⟩, ?_⟩
    rcases hcore with ⟨hq, hsl⟩ | ⟨hnq', hcs⟩
    · exact Or.inl ⟨hqB.mp hq, IsSL2.of_mulEquiv eB hsl⟩
    · refine Or.inr ⟨fun h => hnq' (hqB.mpr h), ?_⟩
      rcases hcs with ⟨htop, -⟩ | ⟨-, hE, hp5, hr5', heq⟩
      · exact absurd htop hntop
      · refine Or.inr ⟨?_, hE, hp5, hr5', ?_⟩
        · refine lt_of_le_of_ne (sup_le hBL.le (Subgroup.map_subtype_le _)) fun h => ?_
          exact hntop ((A313.imgOdd_eq_top_iff hBL.le).mpr h.symm)
        · rw [← A313.map_oddCoreSub_subgroupOf hBL.le, heq]

end CFSG.Quasithin
