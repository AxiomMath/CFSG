module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57Alt5
public import CFSG.Quasithin.H13.A7BlkOff
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223F7Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.H13.A7Blk
open scoped Pointwise commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem exists_swap_of_alt7 {X Q₁ A : Subgroup G}
    (hX : IsShort2 X) (D : AltData X) (hUQ : blockU X ≤ Q₁)
    (hQN : Q₁ ≤ Subgroup.normalizer (X : Set G)) (hA : IsMaxElemAbelian Q₁ A)
    (hAc : ¬ A ≤ Subgroup.centralizer (blockU X : Set G)) :
    ∃ (g : ↥(Subgroup.normalizer (X : Set G))) (a b : Fin 7), a ≠ b ∧ (g : G) ∈ A ∧
      D.act g = Equiv.swap a b := by
  have hV : IsElemAbelian 2 (blockV X) := isElemAbelian_blockV hX
  have hVU : blockV X = blockU X := C1.commutator_blockU hX
  have hVQ : blockV X ≤ Q₁ := hVU ▸ hUQ
  have hQNV : Q₁ ≤ Subgroup.normalizer (blockV X : Set G) := fun q hq =>
    mem_normalizer_blockV (hQN hq)
  have hAcV : ¬ A ≤ Subgroup.centralizer (blockV X : Set G) := hVU ▸ hAc
  have hoff := offenderImages_isFFStarOffender hV hVQ hQNV
    (B := autI hV A) ⟨A, ⟨hA, hAcV⟩, rfl⟩
  have hoff' : IsFFStarOffender (autI hV A) (autI hV A) :=
    ⟨le_rfl, hoff.2.1, hoff.2.2.1, hoff.2.2.2⟩
  obtain ⟨B', hB'le, -, hB'off⟩ := exists_offender_perm D hX (hA.1.trans hQN) hoff'
  obtain ⟨a, b, hab, hsw⟩ := swap_mem_of_isOffG hB'off
  obtain ⟨g, hgA, hg⟩ := (mem_img D).mp (hB'le hsw)
  exact ⟨g, a, b, hab, hgA, hg⟩

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_act_eq_one {X : Subgroup G} (D : AltData X)
    {g : ↥(Subgroup.normalizer (X : Set G))} (hg : D.act g = 1) {k : G} (hk : k ∈ X) :
    ⁅k, (g : G)⁆ ∈ pCoreOf 2 X := by
  have h1 := permAct_spec D.α D.surj D.ker (by norm_num) (by norm_num) g ⟨k, hk⟩
  have h2 : D.α (conjAct X g ⟨k, hk⟩) = D.α ⟨k, hk⟩ := by
    apply Subtype.ext
    rw [h1]
    have : D.act g = 1 := hg
    change ((D.act g : Equiv.Perm (Fin 7))) * _ * ((D.act g : Equiv.Perm (Fin 7)))⁻¹ = _
    rw [this]
    simp
  have hq := mem_blockQ_of_ker D (k := conjAct X g ⟨k, hk⟩ * ⟨k, hk⟩⁻¹)
    (by rw [map_mul, map_inv, h2]; simp)
  have e : (((conjAct X g ⟨k, hk⟩ * ⟨k, hk⟩⁻¹ : ↥X)) : G) = (g : G) * k * (g : G)⁻¹ * k⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Setup.coe_conjAct_apply]
  rw [e] at hq
  have : ⁅k, (g : G)⁆ = ((g : G) * k * (g : G)⁻¹ * k⁻¹)⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact (pCoreOf 2 X).inv_mem hq

theorem mul_mul_inv_eq_of_act_eq_one {X : Subgroup G} (hX : IsShort2 X) (D : AltData X)
    {g : ↥(Subgroup.normalizer (X : Set G))} (hg : D.act g = 1) {u : G} (hu : u ∈ blockU X) :
    (g : G) * u * (g : G)⁻¹ = u := by
  have hVU : blockV X = blockU X := C1.commutator_blockU hX
  have huV : u ∈ blockV X := hVU ▸ hu
  have h := theta_conj D hX g ⟨u, huV⟩
  have hg' : D.act g = 1 := hg
  rw [hg'] at h
  have h' : theta D hX ⟨(g : G) * u * (g : G)⁻¹, conj_mem_blockV g.2 huV⟩ = theta D hX ⟨u, huV⟩ :=
    Multiplicative.toAdd.injective h
  exact congrArg Subtype.val ((theta D hX).injective h')

theorem false_of_centralizes_alt7 {I X : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hX : IsShort2 X) (hXI : X ≤ I)
    (hr : 2 ≤ CFSG.Open.pRank 3 X) {p : G} (hpI : p ∈ I) (hp3 : orderOf p = 3)
    (hpc : ∀ x ∈ X, x * p = p * x) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEX, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) X
  have hcomm : ∀ e ∈ E, Commute e p := fun e he => hpc e (hEX he)
  have hpE : p ∉ E := by
    intro hpE
    have hpO : p ∈ pCoreOf 2 X := by
      refine hX.2.1 ⟨hEX hpE, ?_⟩
      show p ∈ Subgroup.centralizer (pCoreOf 2 X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hpc h (pCoreOf_le 2 X hh)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨p, hpO⟩
    have hdvd : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hp3] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  obtain ⟨hE', hcard'⟩ := exists_elemAbelian_sup_zpowers hE hp3 hcomm hpE
  have hle : E ⊔ Subgroup.zpowers p ≤ I :=
    sup_le (hEX.trans hXI) (Subgroup.zpowers_le.2 hpI)
  have h3r : CFSG.Open.pRank 3 X + 1 ≤ CFSG.Open.pRank 3 I :=
    le_pRank Nat.prime_three hle hE' (by rw [hcard', hEcard, pow_succ])
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) = CFSG.Open.pRank 3 I :=
    pRank_top_subtype (p := 3) I
  omega

theorem eq_one_of_act_eq_one {I X P : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hX : IsShort2 X) (hXI : X ≤ I)
    (hr : 2 ≤ CFSG.Open.pRank 3 X) (D : AltData X) (hPI : P ≤ I) (hP3 : IsElemAbelian 3 P) {p : G}
    (hp : p ∈ P) (hpN : p ∈ Subgroup.normalizer (X : Set G))
    (hρ : D.act ⟨p, hpN⟩ = 1) : p = 1 := by
  by_contra hne
  have hp3 : p ^ 3 = 1 := hP3.2 p hp
  have hord : orderOf p = 3 := orderOf_eq_prime hp3 hne
  have hzp : ∀ a ∈ Subgroup.zpowers p,
      ∃ ha : a ∈ Subgroup.normalizer (X : Set G), D.act ⟨a, ha⟩ = 1 := by
    intro a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨Subgroup.zpow_mem _ hpN m, ?_⟩
    have : (⟨p ^ m, Subgroup.zpow_mem _ hpN m⟩ : ↥(Subgroup.normalizer (X : Set G))) =
        (⟨p, hpN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ m := rfl
    rw [this, map_zpow, hρ, one_zpow]
  have hcent := le_centralizer_of_odd_order_acts_trivially (A := Subgroup.zpowers p) hX
    (Subgroup.zpowers_le.2 hpN)
    (by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      obtain ⟨haN, hρa⟩ := hzp a ha
      exact commutator_mem_pCoreOf_of_act_eq_one D hρa hx)
    (fun a ha => by
      obtain ⟨haN, hρa⟩ := hzp a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := mul_mul_inv_eq_of_act_eq_one hX D hρa hu
      calc u * a = (a * u * a⁻¹) * a := by rw [this]
        _ = a * u := by group)
    (fun a ha => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact ⟨3, by decide, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hp3, one_zpow]⟩)
  exact false_of_centralizes_alt7 hrank hX hXI hr (hPI hp) hord
    (fun x hx => Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_zpowers p)) x hx)

omit [Finite G] in
theorem false_of_act_swap {X Q₁ P : Subgroup G} (D : AltData X)
    (hPN : P ≤ Subgroup.normalizer (X : Set G)) (hQ2 : IsPGroup 2 Q₁)
    (hPQ : P ≤ Subgroup.normalizer (Q₁ : Set G)) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)
    (hinj : ∀ p ∈ P, ∀ hp : p ∈ Subgroup.normalizer (X : Set G), D.act ⟨p, hp⟩ = 1 → p = 1)
    {g : ↥(Subgroup.normalizer (X : Set G))} (hg : (g : G) ∈ Q₁) {a b : Fin 7} (hab : a ≠ b)
    (hgs : D.act g = Equiv.swap a b) : False := by
  let ρP : ↥(P.subgroupOf (Subgroup.normalizer (X : Set G))) →* Equiv.Perm (Fin 7) :=
    D.act.comp (P.subgroupOf (Subgroup.normalizer (X : Set G))).subtype
  let ρQ : ↥(Q₁.subgroupOf (Subgroup.normalizer (X : Set G))) →* Equiv.Perm (Fin 7) :=
    D.act.comp (Q₁.subgroupOf (Subgroup.normalizer (X : Set G))).subtype
  have hρinj : Function.Injective ρP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hinj (x : G) (Subgroup.mem_subgroupOf.1 x.2) x.1.2 hx
  have hYcard : Nat.card ρP.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, hP9]
  have hY3 : IsPGroup 3 ρP.range :=
    (hP3.comap_subtype (K := Subgroup.normalizer (X : Set G))).of_surjective ρP.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ρP)
  have hJ2 : IsPGroup 2 ρQ.range :=
    (hQ2.comap_subtype (K := Subgroup.normalizer (X : Set G))).of_surjective ρQ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ρQ)
  have hconj : ∀ y ∈ ρP.range, ∀ z ∈ ρQ.range, y * z * y⁻¹ ∈ ρQ.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨w, rfl⟩
    have hx : (x.1 : G) ∈ P := Subgroup.mem_subgroupOf.1 x.2
    have hw : (w.1 : G) ∈ Q₁ := Subgroup.mem_subgroupOf.1 w.2
    have hmem : (x.1 * w.1 * x.1⁻¹ : ↥(Subgroup.normalizer (X : Set G))) ∈
        Q₁.subgroupOf (Subgroup.normalizer (X : Set G)) := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      have := (Subgroup.mem_normalizer_iff.1 (hPQ hx) (w.1 : G)).1 hw
      simpa using this
    refine ⟨⟨x.1 * w.1 * x.1⁻¹, hmem⟩, ?_⟩
    simp [ρP, ρQ, map_mul, map_inv]
  have hYJ : ρP.range ≤ Subgroup.normalizer (ρQ.range : Set (Equiv.Perm (Fin 7))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hconj y hy z hz, fun hz => ?_⟩
    have := hconj y⁻¹ (ρP.range.inv_mem hy) _ hz
    simpa [mul_assoc] using this
  have hswap : Equiv.swap a b ∈ ρQ.range :=
    ⟨⟨g, Subgroup.mem_subgroupOf.2 hg⟩, hgs⟩
  exact false_of_swap_normalized_by_nine hYcard hY3 hJ2 hYJ ⟨a, b, hab, hswap⟩

namespace Core57

variable {I S K H Mc : Subgroup G} (c : Core57 I S K H Mc)
include c

theorem le_normalizer_of_alt7 {X : Subgroup G} (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X)
    {α : ↥X →* alternatingGroup (Fin 7)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥X) : I ≤ Subgroup.normalizer (X : Set G) := by
  intro t ht
  by_contra hnot
  have hX₂ : IsBlock2 I (conjByElt t X) := IsBlock2.conjByElt_of_mem hX ht
  have hne : X ≠ conjByElt t X := fun h =>
    hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm := mul_comm_of_commutator_bot
    (distinctBlocksCommuteStatement I X (conjByElt t X) c.charTwo hX hX₂ hne)
  have hr : 2 ≤ CFSG.Open.pRank 3 X :=
    C1GN.le_pRank_three_of_alt_quotient α hα hker C1GN.two_le_pRank_alt7
  have h3' : 3 ∣ Nat.card (conjByElt t X) := by rw [card_conjByElt]; exact h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjByElt t X)) 3 h3'
  have hy' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  exact false_of_centralizes_alt7 c.rank hX.1 hX.2.1 hr (hX₂.2.1 y.2) hy'
    (fun x hx => hcomm x hx y y.2)

theorem false_of_alt7 {X : Subgroup G} (hX : IsBlock2 I X)
    (h7 : IsAltType X 7) : False := by
  obtain ⟨-, hgen, hns, hV2, h3⟩ := alt_block_facts hX.1 (Or.inr rfl) h7
  have hXMc : ¬ X ≤ Mc :=
    not_le_of_block distinctBlocksCommuteStatement c.charTwo c.rank c.sylow hX h3 c.S_Mc c.P1
      c.K_solv hgen hns hV2
  have cfg := c.blkCfg hX h3
  obtain ⟨α, hα, hαk, -⟩ := id h7
  have hIN : I ≤ Subgroup.normalizer (X : Set G) := c.le_normalizer_of_alt7 hX h3 hα hαk
  have hUO : blockU X ≤ pCoreOf 2 X := fun u hu => (hX.1.2.2.1.1 hu).1
  have hUQ₁ : blockU X ≤ pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) :=
    hUO.trans cfg.pCoreOf_le_pCoreOf_sup_inf
  obtain ⟨A, hAmax, hAc⟩ := c.exists_isMaxElemAbelian hX h3 hXMc
    (fun A hA => (hA.1.trans ((pCoreOf_sup_le c.sylow c.K_le).trans c.sylow.1)).trans hIN)
  have hQ₁N : pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G))) ≤
      Subgroup.normalizer (X : Set G) := cfg.pCoreOf_sup_le_S₁.trans inf_le_right
  obtain ⟨D⟩ := nonempty_altData h7
  obtain ⟨g, a, b, hab, hgA, hg⟩ := exists_swap_of_alt7 hX.1 D hUQ₁ hQ₁N hAmax hAc
  obtain ⟨P, hPK, hP3, hP9⟩ := c.three
  have hr : 2 ≤ CFSG.Open.pRank 3 X :=
    C1GN.le_pRank_three_of_alt_quotient α hα hαk C1GN.two_le_pRank_alt7
  exact false_of_act_swap D (hPK.trans cfg.K_normX) (pCoreOf_isPGroup 2 _)
    (hPK.trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _)))
    (isPGroup_three_of_isElemAbelian hP3) hP9
    (fun p hp hpN hρ => eq_one_of_act_eq_one c.rank hX.1 hX.2.1 hr D (hPK.trans c.K_le) hP3 hp hpN
      hρ) (hAmax.1 hgA) hab hg

end Core57

end S15223

end CFSG.Quasithin
