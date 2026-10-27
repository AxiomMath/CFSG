module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem519
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsFin

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

section NatMod

variable {G : Type} [Group G] {L W : Subgroup G} {n : ℕ}

theorem IsNatModCh5.inf_centralizer_eq_bot [Finite G] (h : IsNatModCh5 L W n) :
    W ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hLN : L ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (h.1 hg) x).mp hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff.mp hx.2 g hg, mul_assoc, mul_inv_cancel, mul_one]
    exact hx.2
  rcases h.irreducible _ inf_le_left hLN with hb | he
  · exact hb
  · exfalso
    apply h.not_le_centralizer
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← he] at hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2 g hg).symm

end NatMod

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem inf_centralizer_le_T (h : Hyp5_0_1 G T M L n) {W : Subgroup G}
    (hLTW : L ⊔ T ≤ Subgroup.normalizer (W : Set G)) (hWL : ⁅W, L⁆ ≠ ⊥) :
    (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := h.inf_centralizer_le (le_sup_left.trans hLTW) hWL
  have hP : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (W : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ h.T_le_normalizer
    have hx' : x ∈ (L : Set G) * (T : Set G) := by rw [← hset]; exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨j, hj⟩ := h.sylow.1 ⟨t, ht⟩
    have htj : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (h.T_le_normalizer ht) (2 ^ j)
    rw [htj, mul_one] at he
    have hmem : (l * t) ^ 2 ^ j ∈ pCoreOf 2 L := by
      refine hC ⟨?_, Subgroup.pow_mem _ hxC _⟩
      rw [he]; exact hl'
    obtain ⟨i, hi⟩ := pCoreOf_isPGroup 2 L ⟨_, hmem⟩
    refine ⟨j + i, Subtype.ext ?_⟩
    have hi' : ((l * t) ^ 2 ^ j) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hi']
  exact (le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_centralizer hLTW) hP).trans
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right))

theorem conjClosure_sup_eq (h : Hyp5_0_1 G T M L n) :
    conjClosure (quasithinOmegaOneCenter T) (L ⊔ T) =
      conjClosure (quasithinOmegaOneCenter T) L := by
  refine le_antisymm (conjClosure_le fun g hg y hy => ?_) (conjClosure_mono le_rfl le_sup_left)
  have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ h.T_le_normalizer
  have hg' : g ∈ (L : Set G) * (T : Set G) := by rw [← hset]; exact hg
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hg'
  have hty : t * y * t⁻¹ = y := by
    rw [Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hy).2 t ht, mul_assoc,
      mul_inv_cancel, mul_one]
  have e : l * t * y * (l * t)⁻¹ = l * (t * y * t⁻¹) * l⁻¹ := by group
  rw [e, hty]
  exact mem_conjClosure hl hy

end Hyp5_0_1

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isNatModCh5 {L T V₁ : Subgroup G} {k : ℕ} (hV₁ : IsNatModCh5 L V₁ k)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ V₁) (hz1 : z ≠ 1)
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) : T ≤ Subgroup.normalizer (V₁ : Set G) := by
  have key : ∀ t ∈ T, V₁ ≤ conjSub t V₁ := by
    intro t ht
    have hLJ : L ≤ Subgroup.normalizer ((conjSub t V₁ ⊓ V₁ : Subgroup G) : Set G) := by
      intro l hl
      apply mem_normalizer_of_forall_conj_mem'
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp (hV₁.1 hl) x).mp hx.2⟩
      rw [mem_conjSub]
      have h1 : t⁻¹ * x * t ∈ V₁ := mem_conjSub.mp hx.1
      have h2 : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l).mp hl
        simpa using this
      have h3 := (Subgroup.mem_normalizer_iff.mp (hV₁.1 h2) _).mp h1
      have e : t⁻¹ * (l * x * l⁻¹) * t = (t⁻¹ * l * t) * (t⁻¹ * x * t) * (t⁻¹ * l * t)⁻¹ := by
        group
      rw [e]
      exact h3
    rcases hV₁.irreducible _ inf_le_right hLJ with hb | he
    · exfalso
      have hzJ : z ∈ conjSub t V₁ ⊓ V₁ := by
        refine Subgroup.mem_inf.mpr ⟨?_, hz⟩
        rw [mem_conjSub]
        have htz : t⁻¹ * z * t = z := by
          rw [Subgroup.mem_centralizer_iff.mp hzT t⁻¹ (T.inv_mem ht)]
          group
        rw [htz]
        exact hz
      rw [hb, Subgroup.mem_bot] at hzJ
      exact hz1 hzJ
    · exact he.symm.le.trans inf_le_left
  intro t ht
  apply mem_normalizer_of_forall_conj_mem'
  intro x hx
  have h1 := key t⁻¹ (T.inv_mem ht) hx
  rw [mem_conjSub, inv_inv] at h1
  exact h1

theorem isPerfect_of_isSimpleGroup_of_center_eq_bot {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hZ : Subgroup.center Q = ⊥) : Group.IsPerfect Q := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with hb | ht
  · exfalso
    have hc : Subgroup.center Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hmem : ⁅y, x⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    rw [hc] at hZ
    obtain ⟨a, b, hab⟩ := exists_pair_ne Q
    have ha : a ∈ (⊤ : Subgroup Q) := Subgroup.mem_top a
    have hb' : b ∈ (⊤ : Subgroup Q) := Subgroup.mem_top b
    rw [hZ, Subgroup.mem_bot] at ha hb'
    exact hab (ha.trans hb'.symm)
  · exact ht

end Fixed

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem center_K_eq_bot
    : Subgroup.center (O2Q (oTwoUpper H)) = ⊥ := by
  have := h.isSimple_K
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [card_of_lieModel_L34 h.l34]
  norm_num

theorem isQuasisimple_K
    : CFSG.IsQuasisimple (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) := by
  have := h.isSimple_K
  have := isPerfect_of_isSimpleGroup_of_center_eq_bot h.center_K_eq_bot
  exact isQuasisimple_of_isSimpleGroup_of_isPerfect

theorem conjClosure_K_eq : conjClosure (oTwoUpper H) T = oTwoUpper H := by
  apply le_antisymm _ (le_conjClosure _ T)
  exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (h.T_le_Mp ht) z).mp hz

theorem normalizer_T_le
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨⟨hmax, -, -⟩, -⟩ := h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34
  have h3 := ((h331 G T hh.simple hh.nonabelian hh.qtke hh.sylow).2 (oTwoUpper H) hmax
    h.isQuasisimple_K).2.2.2.1
  rwa [h.conjClosure_K_eq] at h3

theorem exists_isZ1Choice
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1) (h519 : Stmt5_1_19)
    (h520 : Stmt5_1_20) (hF : L2TorusFact) (hFix : L2ModFixTwoFact) (hSum : L4NatSumFact)
    (hnot : ¬ Concl5_1_14_four T L V B D n) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D)
    (h3 : Nat.card D₃ = 3) : ∃ Z₁ : Subgroup G, IsZ1Choice T L Z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hD₃M, -⟩ := h520 G T M L V H B D n h.hyp h.notation59 h.module h.l34 hnot D₃ hD₃ h3
  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdBorel : d ∈ borelL T L := h.notation59.2.1.1 (hD₃ hdD₃)
  have hdL : d ∈ L := hdBorel.1
  have hdT : d ∉ Subgroup.normalizer (T : Set G) := by
    intro hdN
    apply hD₃M
    rw [← zpowers_eq_of_card_prime Nat.prime_three h3 hdD₃ hd1]
    exact Subgroup.zpowers_le.mpr (h.normalizer_T_le h5114 h331 hdN)
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.2
  obtain ⟨-, hVZel, hVZred⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (hh.isSylowTwoOf le_sup_right) h.charTwo_LT (le_refl (quasithinOmegaOneCenter T))
  rw [hh.conjClosure_sup_eq] at hVZel hVZred
  set VZ := conjClosure (quasithinOmegaOneCenter T) L with hVZdef
  have hZVZ : quasithinOmegaOneCenter T ≤ VZ := le_conjClosure _ L
  have hTVZ : T ≤ Subgroup.normalizer (VZ : Set G) := le_sup_right.trans hVZred.2.1
  have hLVZ : L ≤ Subgroup.normalizer (VZ : Set G) := le_sup_left.trans hVZred.2.1
  have hred := h.module.isTwoReducedIn
  have hVne : V ≠ ⊥ := by
    intro hb
    apply h.module.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp
  obtain ⟨z₀, -, hz₀1, hz₀Z⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl
    (hh.V_le_T h.module) (le_sup_right.trans hred.2.1) hVne
  have hVZL : ⁅VZ, L⁆ ≠ ⊥ := by
    intro hb
    have hC : VZ ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have : z₀ ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hz₀Z, hC (hZVZ hz₀Z)⟩
    rw [hZL, Subgroup.mem_bot] at this
    exact hz₀1 this
  have hVZmod : IsCh5Module T L VZ :=
    ⟨hVZred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hVZred).2, hVZL⟩
  have hVZT : VZ ≤ T := hh.V_le_T hVZmod
  have hZsub : ∀ x ∈ VZ, x ∈ Subgroup.centralizer (T : Set G) → x ∈ quasithinOmegaOneCenter T :=
    fun x hx hxC => mem_quasithinOmegaOneCenter_iff.mpr ⟨hVZT hx, hxC, hVZel.2 x hx⟩
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_inf T).trans inf_le_right
  have hnotZ : ¬ Concl5_1_14_four T L VZ B D n := by
    rintro ⟨-, -, hDB⟩
    apply hD₃M
    rw [hDB] at hD₃
    exact hD₃.trans ((h.notation59.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H))
  rcases h519 G T M L VZ H B D n h.hyp h.notation59 hVZmod h.l34 hnotZ D₃ hD₃ h3 with
    ⟨-, ⟨hn2, hsum⟩ | ⟨hn24, hnat⟩⟩ | ⟨hn48, horth, -⟩ | ⟨-, -, -, -, hD₃M', -⟩
  ·
    subst hn2
    have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (VZ : Set G) := by
      have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
          (hh.sup_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L))
          (pCoreOf_isPGroup 2 L)
      rw [← hh.centralizer_eq_pCoreOf hVZmod] at h1
      exact h1.trans inf_le_right
    have hkerVZ : ∀ W : Subgroup G, W ≤ VZ → IsNatModCh5 L W 2 →
        L ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (VZ : Set G) := by
      intro W _ hW
      have hWne : W ≠ ⊥ := by
        intro hb
        apply hW.not_le_centralizer
        rw [hb]
        intro l _
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hw
        rw [hw, one_mul, mul_one]
      have hWL : ⁅W, L⁆ ≠ ⊥ := by rw [hW.commutator_eq]; exact hWne
      exact (hh.inf_centralizer_le hW.1 hWL).trans hO2
    obtain ⟨V₁, hz₀V₁, hV₁nat, hV₁irr⟩ :=
      hSum G L VZ (T ⊓ L) z₀ hsum
        (fun a ha b hb => congrArg Subtype.val (hVZel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hkerVZ hS
        (hZVZ hz₀Z) (Subgroup.centralizer_le (fun x hx => hx.1) (hZC hz₀Z))
    have hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G) :=
      le_normalizer_of_isNatModCh5 hV₁nat hh.T_le_normalizer hz₀V₁ hz₀1 (hZC hz₀Z)
    have hV₁ne : ⁅V₁, L⁆ ≠ ⊥ := by
      rw [hV₁nat.commutator_eq]
      intro hb
      rw [hb, Subgroup.mem_bot] at hz₀V₁
      exact hz₀1 hz₀V₁
    have hcard := hFix G L T V₁ 2 d (Or.inl ⟨hV₁nat, Or.inl rfl⟩) hT2 hh.T_le_normalizer hTV₁ hS
      (hh.inf_centralizer_le_T (sup_le hV₁nat.1 hTV₁) hV₁ne) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T ⊓ V₁ = V₁ ⊓ Subgroup.centralizer (T : Set G) := by
      refine le_antisymm (fun x hx => ⟨hx.2, hZC hx.1⟩) (fun x hx => ⟨?_, hx.1⟩)
      exact hZsub x (hV₁irr.1 hx.1) hx.2
    refine ⟨quasithinOmegaOneCenter T ⊓ V₁, inf_le_left, by rw [heq]; exact hcard,
      Or.inr ⟨hsum, V₁, hV₁irr, rfl⟩⟩
  ·
    set W := ⁅VZ, L⁆ with hWdef
    have hWV : W ≤ VZ := by
      rw [hWdef, Subgroup.commutator_le]
      intro v hv l hl
      have : l * v⁻¹ * l⁻¹ ∈ VZ :=
        (Subgroup.mem_normalizer_iff.mp (hLVZ hl) v⁻¹).mp (VZ.inv_mem hv)
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact VZ.mul_mem hv this
    have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_commutator_of hTVZ hh.T_le_normalizer
    have hZW : quasithinOmegaOneCenter T ≤ W := by
      intro z hz
      have hzVZ := hZVZ hz
      have hnorm := h.norm_eq_one h5114 hF hD₃ h3 hD₃M hz hdD₃ hd1
      have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
      have hzb : z * (d * z * d⁻¹) ∈ W := by
        have hc : ⁅z, d⁆ ∈ W := Subgroup.commutator_mem_commutator hzVZ hdL
        have e : ⁅z, d⁆ = z * (d * z * d⁻¹) := by
          rw [commutatorElement_def, hzi]; group
        rwa [e] at hc
      have hc : d ^ 2 * z * (d ^ 2)⁻¹ ∈ W := by
        rw [eq_inv_of_mul_eq_one_right hnorm]
        exact W.inv_mem hzb
      have hd2 : d⁻¹ ^ 2 ∈ L := L.pow_mem (L.inv_mem hdL) 2
      have := (Subgroup.mem_normalizer_iff.mp (hnat.1 hd2) _).mp hc
      have e : d⁻¹ ^ 2 * (d ^ 2 * z * (d ^ 2)⁻¹) * (d⁻¹ ^ 2)⁻¹ = z := by group
      rwa [e] at this
    have hWne : ⁅W, L⁆ ≠ ⊥ := by rw [hnat.commutator_eq]; exact hVZL
    have hcard := hFix G L T W n d (Or.inl ⟨hnat, hn24⟩) hT2 hh.T_le_normalizer hTW hS
      (hh.inf_centralizer_le_T (sup_le hnat.1 hTW) hWne) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T = W ⊓ Subgroup.centralizer (T : Set G) :=
      le_antisymm (fun x hx => ⟨hZW hx, hZC hx⟩) (fun x hx => hZsub x (hWV hx.1) hx.2)
    exact ⟨quasithinOmegaOneCenter T, le_rfl, by rw [heq]; exact hcard, Or.inl rfl⟩
  ·
    have hcard := hFix G L T VZ n d (Or.inr ⟨horth, hn48⟩) hT2 hh.T_le_normalizer hTVZ hS
      (hh.inf_centralizer_le_T hVZred.2.1 hVZL) hdBorel hord hdT
    have heq : quasithinOmegaOneCenter T = VZ ⊓ Subgroup.centralizer (T : Set G) :=
      le_antisymm (fun x hx => ⟨hZVZ hx, hZC hx⟩) (fun x hx => hZsub x hx.1 hx.2)
    exact ⟨quasithinOmegaOneCenter T, le_rfl, by rw [heq]; exact hcard, Or.inl rfl⟩
  · exact absurd hD₃M' hD₃M

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13
