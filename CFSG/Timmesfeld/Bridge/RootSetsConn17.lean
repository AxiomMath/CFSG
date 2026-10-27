module

public import CFSG.Timmesfeld.Bridge.RootSetsConn16
public import CFSG.Timmesfeld.Bridge.OddTranspPairL2

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

@[expose] def mcore (D : Set G) (x : G) (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {u | ∃ d ∈ D, d ∈ P ∧ ∃ e ∈ D, e ∈ P ∧ d * e ∈ qcore D x P ∧ u = d * e}

theorem mcore_le_qcore {x : G} {P : Subgroup G} : mcore D x P ≤ qcore D x P :=
  (Subgroup.closure_le _).2 fun _ ⟨_, _, _, _, _, _, hq, hu⟩ => hu ▸ hq

theorem zcore_le_qcore {x : G} {P : Subgroup G} : zcore D x P ≤ qcore D x P :=
  Subgroup.map_mono inf_le_right

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem commute_of_mem_P (hC : ConnCex D) (h : Step6 D a b c x z P) {p q : G} (hp : p ∈ P)
    (hq : q ∈ P) : Commute p q := by
  have h1 : P ≤ Subgroup.centralizer {y | y ∈ D ∧ y ∈ P} := by
    conv_lhs => rw [h.hPL]
    rw [Subgroup.closure_le]
    intro l hl
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l' hl'
    exact (h.commute_of_mem hC hl'.1 hl.1 hl'.2 hl.2).eq
  have h2 : P ≤ Subgroup.centralizer (P : Set G) := by
    conv_lhs => rw [h.hPL]
    rw [Subgroup.closure_le]
    intro l hl
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro p' hp'
    exact (Subgroup.mem_centralizer_iff.1 (h1 hp') l hl).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hq) p hp

theorem mul_self_of_mem_P (hC : ConnCex D) (h : Step6 D a b c x z P) {p : G} (hp : p ∈ P) :
    p * p = 1 := by
  have hD := hC.setting.root
  rw [h.hPL] at hp
  induction hp using Subgroup.closure_induction with
  | mem y hy => exact hD.mul_self_eq_one hy.1
  | one => exact one_mul 1
  | mul y w hy hw ihy ihw =>
    rw [← h.hPL] at hy hw
    rw [show y * w * (y * w) = y * (w * y) * w by group, ← (h.commute_of_mem_P hC hy hw).eq,
      show y * (y * w) * w = y * y * (w * w) by group, ihy, ihw, one_mul]
  | inv y hy ihy => rw [← mul_inv_rev, ihy, inv_one]

theorem conj_mem_mcore (hB : OddTranspBender) (h3 : Step6ThreeProductHyp) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) {m : G}
    (hm : m ∈ mcore D x P) : g * m * g⁻¹ ∈ mcore D x P := by
  have hN := hC.setting.normal
  have hP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hg p
  have hle : mcore D x P ≤ (mcore D x P).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, hd, hdP, e, he, heP, hq, rfl⟩
    show g * (d * e) * g⁻¹ ∈ mcore D x P
    rw [show g * (d * e) * g⁻¹ = g * d * g⁻¹ * (g * e * g⁻¹) by group]
    exact Subgroup.subset_closure ⟨_, hN g d hd, (hP d).1 hdP, _, hN g e he, (hP e).1 heP,
      h.conj_mul_mem_qcore hB h3 hC hg hd he hdP heP hq, rfl⟩
  exact hle hm

theorem commutator_le_mcore (hC : ConnCex D) (h : Step6 D a b c x z P) {t : G} (ht : t ∈ D)
    (htP : t ∈ P) :
    ⁅CFSG.pCore 2 (lsub D x P), Subgroup.zpowers (⟨t, mem_lsub_of_mem ht htP⟩ : lsub D x P)⁆ ≤
      (mcore D x P).comap (lsub D x P).subtype := by
  rw [Subgroup.commutator_le]
  intro q hq y hy
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  rcases h.commutatorElement_eq hC ht htP hq hy with h1 | ⟨ℓ, hℓ, hℓP, hq', heq⟩
  · rw [h1]
    exact one_mem _
  · rw [heq]
    exact Subgroup.subset_closure ⟨ℓ, hℓ, hℓP, t, ht, htP, hq', rfl⟩

theorem zcore_le_mcore (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    zcore D x P ≤ mcore D x P := by
  have := hC.setting.finite
  obtain ⟨SK, hmemS, a', b', c', n, hK⟩ := h.exists_thirdKindHyp hB hC
  rintro _ ⟨w, hw, rfl⟩
  have hle : (⨆ v ∈ lclass D x P ∩ (SK : Set (lsub D x P)),
      ⁅CFSG.pCore 2 (lsub D x P), Subgroup.zpowers v⁆) ≤
        (mcore D x P).comap (lsub D x P).subtype := by
    refine iSup₂_le fun v hv => ?_
    have hvD : (v : G) ∈ D := classIn_subset_of_normal hC.setting.normal _ h.hx hv.1
    exact h.commutator_le_mcore hC hvD (h.mem_of_mem_isPGroup hC SK.isPGroup' hmemS hvD hv.2)
  exact hle (OddTransp.oddTranspCenterSup _ _ _ _ _ _ _ hK (h.commutator_eq_top hC)
    ⟨hw.2, hw.1⟩)

theorem zStar_eq_pCore (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    zStar (lsub D x P) = CFSG.pCore 2 (lsub D x P) := by
  have := hC.setting.finite
  refine le_antisymm ?_ OddTransp.pCore_le_zStar
  rw [← h.solvableRadical_eq_pCore hB hC]
  exact OddTransp.zStar_le_solvableRadical

theorem nonempty_zStar_mulEquiv (hB : OddTranspBender) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {K : Type*} [Group K]
    (e : lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* K) :
    Nonempty (lsub D x P ⧸ zStar (lsub D x P) ≃* K) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    ((h.solvableRadical_eq_pCore hB hC).trans (h.zStar_eq_pCore hB hC).symm)).symm.trans e⟩

theorem isBenderGroup_zStar (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    CFSG.BenderSuzuki.IsBenderGroup (lsub D x P ⧸ zStar (lsub D x P)) := by
  rcases h.isBenderGroup hB hC with ⟨n, hn, f⟩ | ⟨n, hn, f⟩ | ⟨n, hn, f⟩
  · exact .isPSL2 n hn (h.nonempty_zStar_mulEquiv hB hC f).some
  · exact .isSuzuki n hn (h.nonempty_zStar_mulEquiv hB hC f).some
  · exact .isPSU3 n hn (h.nonempty_zStar_mulEquiv hB hC f).some

theorem commute_of_mem_commutator_top (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∀ p ∈ ⁅CFSG.pCore 2 (lsub D x P), (⊤ : Subgroup (lsub D x P))⁆,
      ∀ q ∈ ⁅CFSG.pCore 2 (lsub D x P), (⊤ : Subgroup (lsub D x P))⁆, Commute p q := by
  have hQ : (CFSG.pCore 2 (lsub D x P)).Normal := CFSG.pCore_normal
  intro p hp q hq
  exact h.pCore_commute hB h3 hC (Subgroup.commutator_le_left _ _ hp)
    (Subgroup.commutator_le_left _ _ hq)

theorem exists_eq_mul_of_mem (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) {p : G} (hp : p ∈ P) (hpQ : p ∉ qcore D x P) :
    ∃ d ∈ D, d ∈ P ∧ ∃ w ∈ zcore D x P, p = d * w := by
  have := hC.setting.finite
  obtain ⟨SK, hmemS, a', b', c', n, hK⟩ := h.exists_thirdKindHyp hB hC
  set s : lsub D x P := ⟨p, h.le_lsub hp⟩ with hs
  have hsQ : s ∉ CFSG.pCore 2 (lsub D x P) := fun hmem => hpQ ⟨s, hmem, rfl⟩
  have hs2 : orderOf s = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hsQ (h1 ▸ one_mem _)
    rw [pow_two]
    exact Subtype.ext (h.mul_self_of_mem_P hC hp)
  obtain ⟨d, ⟨hdE, hdS⟩, w, hw, hsdw⟩ := hK.exists_mul_of_involution (h.isBenderGroup_zStar hB hC)
    (h.commute_of_mem_commutator_top hB h3 hC) (hmemS s hp) hs2 hsQ
  have hdD : (d : G) ∈ D := classIn_subset_of_normal hC.setting.normal _ h.hx hdE
  exact ⟨d, hdD, h.mem_of_mem_isPGroup hC SK.isPGroup' hmemS hdD hdS, w, ⟨w, ⟨hw.2, hw.1⟩, rfl⟩,
    congrArg Subtype.val hsdw⟩

theorem center_le_sup (hB : OddTranspBender) (h3 : Step6ThreeProductHyp) (hC : ConnCex D)
    (h : Step6 D a b c x z P)
    (hL2 : ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.PSL2Model m))
    {α β : G} (hα : α ∈ D) (hβ : β ∈ D) (hαP : α ∈ P) (hβP : β ∈ P)
    (hαβ : α * β ∉ qcore D x P) :
    CFSG.pCore 2 (lsub D x P) ⊓ Subgroup.center (lsub D x P) ≤
      ⁅CFSG.pCore 2 (lsub D x P), Subgroup.zpowers (⟨α, mem_lsub_of_mem hα hαP⟩ : lsub D x P)⁆ ⊔
        ⁅CFSG.pCore 2 (lsub D x P),
          Subgroup.zpowers (⟨β, mem_lsub_of_mem hβ hβP⟩ : lsub D x P)⁆ := by
  have := hC.setting.finite
  obtain ⟨SK, hmemS, a', b', c', n, hK⟩ := h.exists_thirdKindHyp hB hC
  have hmem : ∀ {u : G} (hu : u ∈ D) (huP : u ∈ P),
      (⟨u, mem_lsub_of_mem hu huP⟩ : lsub D x P) ∈ lclass D x P ∩ (SK : Set (lsub D x P)) :=
    fun hu huP => ⟨h.mem_lclass hC hu huP, hmemS ⟨_, mem_lsub_of_mem hu huP⟩ huP⟩
  obtain ⟨m, hm, ⟨e⟩⟩ := hL2
  refine OddTransp.oddTranspCenterPairPSL2 _ _ _ _ _ _ _ hK
    ⟨m, hm, h.nonempty_zStar_mulEquiv hB hC e⟩ ?_ (h.commute_of_mem_commutator_top hB h3 hC) _
    (hmem hα hαP) _ (hmem hβ hβP) ?_
  · obtain ⟨e, he, f, hf, heP, hfP, hef, hefD⟩ := h.hLL
    exact ⟨_, hmem he heP, _, hmem hf hfP, fun h' => hef (congrArg Subtype.val h'),
      h.mem_lclass hC hefD (P.mul_mem heP hfP)⟩
  · intro hmem
    apply hαβ
    refine ⟨_, hmem, ?_⟩
    change α⁻¹ * β = α * β
    rw [hC.setting.root.inv_eq hα]

theorem mem_of_commute_of_mul_not_mem (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P)
    (hL2 : ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.PSL2Model m))
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hPS : P ≤ S) {e₁ e₂ : G} (he₁ : e₁ ∈ D)
    (he₂ : e₂ ∈ D) (he₁P : e₁ ∈ P) (he₂P : e₂ ∈ P) (h12 : e₁ * e₂ ∉ qcore D x P) {s : G}
    (hs : s ∈ D) (hsS : s ∈ S) (hs₁ : Commute s e₁) (hs₂ : Commute s e₂) : s ∈ P := by
  classical
  have := hC.setting.finite
  have hN := hC.setting.normal
  suffices key : ∀ n : ℕ, ∀ s ∈ D, s ∈ S → Commute s e₁ → Commute s e₂ →
      {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ¬ Commute s ℓ}.ncard = n → s ∈ P from
    key _ s hs hsS hs₁ hs₂ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hsS hs₁ hs₂ hn
  have hconj : ∀ ℓ ∈ D, ℓ ∈ P → s * ℓ * s⁻¹ ∈ P := by
    intro ℓ hℓ hℓP
    by_cases hsℓ : Commute s ℓ
    · rw [hsℓ.eq, mul_inv_cancel_right]
      exact hℓP
    have hs'D : s * ℓ * s⁻¹ ∈ D := hN s ℓ hℓ
    have hs'S : s * ℓ * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS (hPS hℓP)) (S.inv_mem hsS)
    have hℓ₁ : Commute ℓ e₁ := h.commute_of_mem hC hℓ he₁ hℓP he₁P
    have hℓ₂ : Commute ℓ e₂ := h.commute_of_mem hC hℓ he₂ hℓP he₂P
    have hc₁ : Commute (s * ℓ * s⁻¹) e₁ := (hs₁.mul_left hℓ₁).mul_left hs₁.inv_left
    have hc₂ : Commute (s * ℓ * s⁻¹) e₂ := (hs₂.mul_left hℓ₂).mul_left hs₂.inv_left
    have hsub : {ℓ' | ℓ' ∈ D ∧ ℓ' ∈ P ∧ ¬ Commute (s * ℓ * s⁻¹) ℓ'} ⊂
        {ℓ' | ℓ' ∈ D ∧ ℓ' ∈ P ∧ ¬ Commute s ℓ'} := by
      refine ⟨fun ℓ' hℓ' => ⟨hℓ'.1, hℓ'.2.1, fun hc => hℓ'.2.2 ?_⟩, fun hsup => ?_⟩
      · exact ((hc.mul_left (h.commute_of_mem hC hℓ hℓ'.1 hℓP hℓ'.2.1)).mul_left hc.inv_left)
      · have := (hsup ⟨hℓ, hℓP, hsℓ⟩).2.2
        exact this (commute_conj_of_isPGroup hC hS2 hs hℓ hsS (hPS hℓP)).symm
    have hlt := Set.ncard_lt_ncard hsub (Set.toFinite _)
    exact ih _ (hn ▸ hlt) _ hs'D hs'S hc₁ hc₂ rfl
  have hsN : s ∈ Subgroup.normalizer (P : Set G) := h.mem_normalizer_of_conj_mem_L hC hconj
  by_contra hsP
  have hcomm : ∀ {e : G} (he : e ∈ D) (heP : e ∈ P), Commute s e →
      ⁅CFSG.pCore 2 (lsub D x P), Subgroup.zpowers (⟨e, mem_lsub_of_mem he heP⟩ : lsub D x P)⁆ ≤
        (Subgroup.centralizer ({s} : Set G)).comap (lsub D x P).subtype :=
    fun he heP hse w hw => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (h.commute_of_mem_commutator hB h3 hC hs hsN he heP hse hw).eq.symm
  have hz := sup_le (hcomm he₁ he₁P hs₁) (hcomm he₂ he₂P hs₂)
    (h.center_le_sup hB h3 hC hL2 he₁ he₂ he₁P he₂P h12 ⟨h.z_mem_pCore hC, h.z_mem_center⟩)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hz
  exact h.hz1 (congrArg Subtype.val
    (h.eq_one_of_commute_center hC hs hsN hsP h.z_mem_center hz.symm))

end Step6

end CFSG.Timmesfeld.Bridge
