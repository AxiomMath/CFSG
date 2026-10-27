module

public import CFSG.Quasithin.EmptyFaithful.SBc4H31Elem
public import CFSG.Quasithin.EmptyFaithful.R3c2Star
public import CFSG.Quasithin.EmptyFaithful.S153H31

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input31Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L →
      ∀ d : G, d ∈ I → d ∈ Subgroup.centralizer (Yp : Set G) →
        d ∈ Subgroup.centralizer (blockU L : Set G) → (∃ k : ℕ, d ^ 2 ^ k = 1) →
        ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L) → d ∈ Subgroup.centralizer (L : Set G)

@[expose] def Input31QleYp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L →
      (IsAltBlockType L 6 ∨ IsG2Block L ∨ IsC134Case 3 I (Sgp153 T V₁) L) → blockU L ≤ Yp

@[expose] def Input31Hyperplane : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L →
      (IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) →
        blockU L ≤ ⨆ (W : Subgroup G) (_ : W ≤ blockU L ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
          W ⊓ Yp ≠ ⊥ ∧ ∀ W' : Subgroup G, W' ≤ W → L ≤ Subgroup.normalizer (W' : Set G) →
            W' = ⊥ ∨ W' = W), W

namespace SBc4

section Facts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem perfect_of_ctx (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : ⁅L, L⁆ = L := by
  have hY : Yp ≤ L := c.c27.Yp_le
  have hLY : ⁅L, Yp⁆ = L := c.conc.2.2.2.1
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer) ?_
  calc L = ⁅L, Yp⁆ := hLY.symm
    _ ≤ ⁅L, L⁆ := Subgroup.commutator_mono le_rfl hY

omit [Finite G] in
theorem blockU_ne_bot_of_short {L : Subgroup G} (h : IsShort2 L) : blockU L ≠ ⊥ :=
  ne_bot_of_gt h.2.2.2.2.1

omit [Finite G] in
theorem simple_of_surjective_alt {L : Subgroup G} {m : ℕ} (hm : 5 ≤ m)
    (α : ↥L →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup (by simpa using hm)
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).isSimpleGroup

theorem simple_of_isPSL_star (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hker : L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L)
    (hP : IsPSL 3 2 1 ↥(Star153 T I L)) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hLI : L ≤ I := S153H.le_I_of_ctx31 c
  set φ := R3c2.actL T I L hLI with hφ
  have hrange : φ.range = Star153 T I L := R3c2.range_actL T I L hLI
  have hkerφ : φ.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, R3c2.actL_eq_one_iff T I L hLI l]
    constructor
    · intro hl
      have h1 : (l : G) ∈ pCoreOf 2 L := hker ▸ ⟨l.2, hl⟩
      rw [pCoreOf_two_eq'] at h1
      obtain ⟨x, hx, hxl⟩ := h1
      have : x = l := Subtype.ext hxl
      rwa [this] at hx
    · intro hl
      have h1 : (l : G) ∈ L ⊓ Subgroup.centralizer (UI153 T I : Set G) := by
        rw [hker, pCoreOf_two_eq']
        exact ⟨l, hl, rfl⟩
      exact h1.2
  have hs : IsSimpleGroup ↥(Star153 T I L) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hP).2
  exact ((QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))).isSimpleGroup

theorem c134Q_le_blockU (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : c134Q I L ≤ blockU L := by
  have hLI : L ≤ I := S153H.le_I_of_ctx31 c
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hperf := perfect_of_ctx c
  have hEI : pCoreOf 2 I ≤ I := pCoreOf_le 2 I
  have hE2 : IsPGroup 2 ↥(pCoreOf 2 I) := pCoreOf_isPGroup 2 I
  have hLE : ⁅L, pCoreOf 2 I⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp (hEI.trans hIL)
  have hEL : ⁅L, pCoreOf 2 I⁆ ≤ pCoreOf 2 I := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hLI.trans (le_normalizer_pCoreOf 2 I))
  have hN2 : IsPGroup 2 ↥(⁅L, pCoreOf 2 I⁆ : Subgroup G) := hE2.to_le hEL
  have hP : ⁅L, pCoreOf 2 I⁆ ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 hLE (Subgroup.normalizer_commutator_ge_left L _) hN2
  have := commutator_le_Q hIL hperf hEI hP
  rw [Subgroup.commutator_comm] at this
  exact this

omit [Finite G] in
theorem ne_bot_of_surjective_multiplicative {Q : Subgroup G} {A : Type*} [AddCommGroup A]
    [Nontrivial A] (β : ↥Q →* Multiplicative A) (hβ : Function.Surjective β) : Q ≠ ⊥ := by
  intro hQ
  have h1 : Subsingleton ↥Q := by
    rw [hQ]
    infer_instance
  have hs : Subsingleton (Multiplicative A) := hβ.subsingleton
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  exact hab (Multiplicative.ofAdd.injective (hs.elim _ _))

theorem outcome31_simple (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (h : Outcome31 T V₁ I L) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨hcases, hker⟩ := h
  rcases hcases with hA | hG | ⟨hP, -⟩
  · obtain ⟨-, α, hα, hker', -⟩ := hA
    exact simple_of_surjective_alt (by norm_num) α hα hker'
  · obtain ⟨-, hpsu, -⟩ := hG
    exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hpsu).2
  · exact simple_of_isPSL_star c hker hP

theorem blockU_ne_bot_of_outcome31 (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (h : Outcome31 T V₁ I L) :
    blockU L ≠ ⊥ := by
  obtain ⟨hcases, -⟩ := h
  rcases hcases with hA | hG | ⟨-, h1 | h2 | h3⟩
  · exact blockU_ne_bot_of_short hA.1
  · exact blockU_ne_bot_of_short hG.1
  · change IsC134Case1 I (Sgp153 T V₁) L at h1
    exact blockU_ne_bot_of_short h1.1.1
  · change IsC134Case2 I (Sgp153 T V₁) L at h2
    obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum⟩, -⟩ := h2
    obtain ⟨-, -, β, hβs, -, -⟩ := hsum
    have hQ : c134Q I L ≠ ⊥ := ne_bot_of_surjective_multiplicative β hβs
    exact fun hb => hQ (le_bot_iff.1 (hb ▸ c134Q_le_blockU c))
  · change IsC134Case3 I (Sgp153 T V₁) L at h3
    obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum1, -⟩, -⟩ := h3
    obtain ⟨-, -, β, hβs, -, -⟩ := hsum1
    have hZ : centerOf (c134Q I L) ≠ ⊥ := ne_bot_of_surjective_multiplicative β hβs
    refine fun hb => hZ (le_bot_iff.1 ?_)
    exact (inf_le_left : centerOf (c134Q I L) ≤ c134Q I L).trans ((c134Q_le_blockU c).trans hb.le)

end Facts

section CentQ

variable {G : Type} [Group G] [Finite G]

theorem input31CentQ_of_cover (hR : Input31Cover) : Input31CentQ := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hDQ x hx
  have hLI : L ≤ I := S153H.le_I_of_ctx31 c
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hperf := perfect_of_ctx c
  have hsimple := outcome31_simple c hout
  have hQne := blockU_ne_bot_of_outcome31 c hout
  have hxI : x ∈ I := hx.1
  have hxY : x ∈ Subgroup.centralizer (Yp : Set G) := hx.2
  have hxQ : x ∈ Subgroup.centralizer (blockU L : Set G) := hDQ hx
  have hQP : blockU L ≤ pCoreOf 2 L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L)
  have hZP : centerOf (blockU L) ≤ pCoreOf 2 L := inf_le_left.trans hQP
  have hZ2 : IsPGroup 2 ↥(centerOf (blockU L)) := (pCoreOf_isPGroup 2 L).to_le hZP
  have hcomm : ∀ y ∈ Subgroup.zpowers x, ⁅L, Subgroup.zpowers y⁆ ≤ centerOf (blockU L) := by
    intro y hy
    have hyI : y ∈ I := Subgroup.zpowers_le.2 hxI hy
    have hyQ : y ∈ Subgroup.centralizer (blockU L : Set G) :=
      Subgroup.zpowers_le.2 hxQ hy
    refine commutator_le_centerOf_Q hIL hperf hsimple hQne ?_ ?_
    · exact Subgroup.zpowers_le.2 hyI
    · exact Subgroup.zpowers_le.2 hyQ
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  set x₂ : G := x ^ m with hx₂
  set xo : G := x ^ 2 ^ a with hxo
  have hx₂mem : x₂ ∈ Subgroup.zpowers x := Subgroup.pow_mem _ (Subgroup.mem_zpowers x) m
  have hxomem : xo ∈ Subgroup.zpowers x := Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hx₂two : ∃ k : ℕ, x₂ ^ 2 ^ k = 1 := by
    refine ⟨a, ?_⟩
    rw [hx₂, ← pow_mul, mul_comm, ← hnm]
    exact pow_orderOf_eq_one x
  have hxoodd : Odd (orderOf xo) := by
    have h1 : xo ^ m = 1 := by
      rw [hxo, ← pow_mul, ← hnm]
      exact pow_orderOf_eq_one x
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hx₂L : x₂ ∈ Subgroup.centralizer (L : Set G) := by
    refine hR G T Mc M V₁ V₂ Yp I L t c hout x₂ ?_ ?_ ?_ hx₂two (hcomm x₂ hx₂mem)
    · exact Subgroup.zpowers_le.2 hxI hx₂mem
    · exact Subgroup.zpowers_le.2 hxY hx₂mem
    · exact Subgroup.zpowers_le.2 hxQ hx₂mem
  have hxoL : xo ∈ Subgroup.centralizer (L : Set G) := by
    refine mem_centralizer_of_odd hZ2 ?_ (hcomm xo hxomem) hxoodd
    exact Subgroup.centralizer_le (fun z hz => hz.1) (Subgroup.zpowers_le.2 hxQ hxomem)
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_left.2 hm).symm
  have hcopZ : IsCoprime (m : ℤ) ((2 ^ a : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨u, v, huv⟩ := hcopZ
  have hxeq : x = x₂ ^ u * xo ^ v := by
    have h2 : (m : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v = 1 := by rw [← huv]; ring
    have h1 : x = x ^ ((m : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v) := by rw [h2, zpow_one]
    rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hx₂L u) (Subgroup.zpow_mem _ hxoL v)

end CentQ

section NotCentQ

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem centralizes_of_le_Yp {Q Yp I : Subgroup G} (h : Q ≤ Yp) :
    I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (Q : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun q hq => Subgroup.mem_centralizer_iff.mp hx.2 q (h hq)

omit [Finite G] in
theorem comm_of_injective {V : Subgroup G} {A : Type*} [AddCommGroup A]
    (β : ↥V →* Multiplicative A) (hinj : Function.Injective β) :
    ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hx y hy
  have h : (⟨x, hx⟩ : ↥V) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    hinj (by rw [map_mul, map_mul]; exact mul_comm _ _)
  exact congrArg Subtype.val h

theorem blockU_comm_of_case12 (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (h : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) :
    ∀ x : G, x ∈ blockU L → ∀ y : G, y ∈ blockU L → x * y = y * x := by
  have hLI : L ≤ I := S153H.le_I_of_ctx31 c
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hle : blockU L ≤ c134Q I L :=
    Subgroup.commutator_mono_left (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L))
  have heq : blockU L = c134Q I L := le_antisymm hle (c134Q_le_blockU c)
  rw [heq]
  rcases h with h1 | h2
  · change IsC134Case1 I (Sgp153 T V₁) L at h1
    obtain ⟨-, n, F, hF, hFin, hcard, -, α, hα, hker, β, hβ, hβker, -⟩ := h1
    refine comm_of_injective β ((MonoidHom.ker_eq_bot_iff β).1 ?_)
    rw [hβker]
    exact Subgroup.bot_subgroupOf _
  · change IsC134Case2 I (Sgp153 T V₁) L at h2
    obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum⟩, -⟩ := h2
    obtain ⟨-, -, β, hβs, hβker, -⟩ := hsum
    refine comm_of_injective β ((MonoidHom.ker_eq_bot_iff β).1 ?_)
    rw [hβker]
    exact Subgroup.bot_subgroupOf _

end NotCentQ

end SBc4

end CFSG.Quasithin
