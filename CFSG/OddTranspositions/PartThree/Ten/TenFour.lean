module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
public import CFSG.OddTranspositions.PartThree.Ten.SwapImage
import CFSG.GroupTheory.ConjOrbitCommutator
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
import CFSG.OddTranspositions.O4Minus5Pair
import CFSG.OddTranspositions.BlockGraph
import CFSG.Timmesfeld.Bridge.OddTranspGenL2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem conj_mem_tenBase (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) {h l : G}
    (hh : h ∈ Halpha D hC.alpha) (hl : l ∈ tenBase hC e) : h * l * h⁻¹ ∈ tenBase hC e := by
  rw [tenBase_eq, comap_base_eq_ker] at hl ⊢
  obtain ⟨l', hl', rfl⟩ := hl
  exact ⟨⟨h, hh⟩ * l' * ⟨h, hh⟩⁻¹, (MonoidHom.normal_ker _).conj_mem l' hl' ⟨h, hh⟩, rfl⟩

omit [Finite G] in
theorem mem_tenBase_iff (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (x : Halpha D hC.alpha) :
    (x : G) ∈ tenBase hC e ↔ (tenHom hC e x).right = 1 := by
  rw [tenBase_eq, comap_base_eq_ker]
  change (Halpha D hC.alpha).subtype x ∈ _ ↔ _
  rw [Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _), MonoidHom.mem_ker,
    MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right]

theorem not_mem_tenBase_of_mem_DalphaStar {hC : HypothesisC D} {f n : ℕ} (h : TenHyp hC f n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) {v : G}
    (hv : v ∈ DalphaStar D hC.alpha) : v ∉ tenBase hC e := by
  intro hvL
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hv
  have hsw : tenHom hC e ⟨v, hvH⟩ ∈ WreathEndgame.swapSet f n := by
    rw [← tenHom_image_DstarH hC h.two_le h.five_le e]
    exact ⟨⟨v, hvH⟩, hv, rfl⟩
  obtain ⟨i, j, hij, hright, -, -⟩ := hsw
  have h1 := (mem_tenBase_iff hC e ⟨v, hvH⟩).mp hvL
  rw [hright] at h1
  exact hij (Equiv.swap_eq_one_iff.mp h1)

theorem exists_mem_Halpha_image_eq (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {γ γ' : Set G} (hγ : γ ∈ Dalpha D β)
    (hγ' : γ' ∈ Dalpha D β) :
    ∃ h ∈ Halpha D β, (fun y => h * y * h⁻¹) '' γ = γ' := by
  classical
  have hN := hC.setup.normal
  have htrans : ∀ {X Y : Set G}, X ∈ blockClass Y → Y ∈ blockClass hC.alpha →
      X ∈ blockClass hC.alpha := by
    rintro X Y ⟨k, rfl⟩ ⟨k', rfl⟩
    exact ⟨k * k', (mul_smul k k' hC.alpha).symm⟩
  have hγα : γ ∈ blockClass hC.alpha := htrans hγ.1 hβ
  have hγα' : γ' ∈ blockClass hC.alpha := htrans hγ'.1 hβ
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  have hinv : ∀ S : Set G,
      (fun y => g⁻¹ * y * g) '' ((fun y => g * y * g⁻¹) '' S) = S := by
    intro S
    rw [Set.image_image]
    have : (fun y => g⁻¹ * (g * y * g⁻¹) * g) = id := by
      funext y
      simp only [id]
      group
    rw [this, Set.image_id]
  have hback : ∀ δ ∈ Dalpha D ((fun y => g * y * g⁻¹) '' hC.alpha),
      (fun y => g⁻¹ * y * g) '' δ ∈ Dalpha D hC.alpha := by
    intro δ hδ
    have h0 := Dalpha.conj hN hδ g⁻¹
    simp only [inv_inv] at h0
    rwa [hinv] at h0
  have hαne : hC.alpha.Nonempty := hC.isBlock_alpha.nonempty
  obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hαne hγα
  obtain ⟨c', hc'⟩ := nonempty_of_mem_blockClass hαne hγα'
  have hc₀ : g⁻¹ * c * g ∈ DalphaStar D hC.alpha :=
    ⟨_, hback γ hγ, ⟨c, hc, rfl⟩⟩
  have hc₀' : g⁻¹ * c' * g ∈ DalphaStar D hC.alpha :=
    ⟨_, hback γ' hγ', ⟨c', hc', rfl⟩⟩
  obtain ⟨h₀, hh₀, hh₀c⟩ := hC.Halpha_transitive _ hc₀ _ hc₀'
  refine ⟨g * h₀ * g⁻¹, ?_, ?_⟩
  ·
    exact Subgroup.closure_induction
      (p := fun z _ => g * z * g⁻¹ ∈ Halpha D ((fun y => g * y * g⁻¹) '' hC.alpha))
      (fun x hx => Subgroup.subset_closure (DalphaStar.conj hN hx g))
      (by simp)
      (fun x z _ _ hx hz => by
        rw [show g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) by group]
        exact Subgroup.mul_mem _ hx hz)
      (fun x _ hx => by
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ hx)
      hh₀
  ·
    have hcc : (g * h₀ * g⁻¹) * c * (g * h₀ * g⁻¹)⁻¹ = c' := by
      have : g * (h₀ * (g⁻¹ * c * g) * h₀⁻¹) * g⁻¹ = g * (g⁻¹ * c' * g) * g⁻¹ := by
        rw [hh₀c]
      calc (g * h₀ * g⁻¹) * c * (g * h₀ * g⁻¹)⁻¹
          = g * (h₀ * (g⁻¹ * c * g) * h₀⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * c' * g) * g⁻¹ := this
        _ = c' := by group
    have hcl : (fun y => (g * h₀ * g⁻¹) * y * (g * h₀ * g⁻¹)⁻¹) '' γ ∈ blockClass hC.alpha := by
      obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hγα
      rw [hk]
      rw [Set.image_image, mem_blockClass_iff]
      exact ⟨g * h₀ * g⁻¹ * k, by
        ext y
        simp only [Set.mem_image]
        constructor <;> rintro ⟨z, hz, rfl⟩ <;> exact ⟨z, hz, by group⟩⟩
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hcl hγα' ⟨c', ⟨c, hc, hcc⟩, hc'⟩

theorem TenHyp.not_o4PairData {hC : HypothesisC D} {f n : ℕ} (h : TenHyp hC f n) :
    ¬ O4PairData G D := by
  rintro ⟨φ, -⟩
  have hG : Nat.card G = 15600 := (Nat.card_congr φ.toEquiv).trans card_PSigmaL225
  obtain ⟨e⟩ := h.iso
  have hle : Nat.card (L2Wreath f n) ≤ Nat.card G := by
    calc Nat.card (L2Wreath f n)
        = Nat.card (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
          (Nat.card_congr e.toEquiv).symm
      _ ≤ Nat.card (Halpha D hC.alpha) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      _ ≤ Nat.card G := Subgroup.card_le_card_group _
  have hL2 : 60 ≤ Nat.card (CFSG.Theory.Comparator.PSL2Model f) := by
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by have := h.two_le; omega)]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    have h15 : 15 ≤ (2 ^ f) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
      omega
    nlinarith
  have hW : 60 ^ 5 ≤ Nat.card (L2Wreath f n) := by
    rw [SemidirectProduct.card, Nat.card_perm, Nat.card_fin, Nat.card_fun, Nat.card_fin]
    have h1 : 60 ^ 5 ≤ Nat.card (CFSG.Theory.Comparator.PSL2Model f) ^ n :=
      (Nat.pow_le_pow_left hL2 5).trans (Nat.pow_le_pow_right (by omega) h.five_le)
    have h2 : 1 ≤ n.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    nlinarith
  omega

theorem exists_base_commutator_sq_ne_one {f n : ℕ} (hf : 2 ≤ f) {x : L2Wreath f n}
    (hx : x.right ≠ 1) :
    ∃ y : Fin n → CFSG.Theory.Comparator.PSL2Model f,
      (x * SemidirectProduct.inl y * x⁻¹ * (SemidirectProduct.inl y)⁻¹) ^ 2 ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x.right i ≠ i := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hx (Equiv.ext hall)
  have hi' : x.right⁻¹ i ≠ i := by
    intro h
    apply hi
    have := congrArg x.right h
    simpa using this.symm
  obtain ⟨t, ht⟩ : ∃ t : CFSG.Theory.Comparator.PSL2Model f, orderOf t = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card (CFSG.Theory.Comparator.PSL2Model f) := by
      rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)]
      refine Dvd.dvd.mul_left ?_ _
      rw [← pow_mul, mul_comm, pow_mul]
      have : (2 ^ 2) ^ f % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have hpos : 1 ≤ (2 ^ 2) ^ f := Nat.one_le_pow _ _ (by norm_num)
      omega
    exact exists_prime_orderOf_dvd_card' 3 h3
  set a := x.left with ha
  set σ := x.right with hσ
  set y : Fin n → CFSG.Theory.Comparator.PSL2Model f := Pi.mulSingle i t with hy
  refine ⟨y, fun hsq => ?_⟩
  have hx : x = SemidirectProduct.inl a * SemidirectProduct.inr σ :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  set z : Fin n → CFSG.Theory.Comparator.PSL2Model f :=
    a * permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f) σ y * a⁻¹ * y⁻¹ with hz
  have hw : x * SemidirectProduct.inl y * x⁻¹ * (SemidirectProduct.inl y)⁻¹ =
      (SemidirectProduct.inl z : L2Wreath f n) := by
    have hinr : (SemidirectProduct.inr σ : L2Wreath f n)⁻¹ = SemidirectProduct.inr σ⁻¹ :=
      (map_inv _ _).symm
    calc x * SemidirectProduct.inl y * x⁻¹ * (SemidirectProduct.inl y)⁻¹
        = SemidirectProduct.inl a *
            (SemidirectProduct.inr σ * SemidirectProduct.inl y * (SemidirectProduct.inr σ)⁻¹) *
            (SemidirectProduct.inl a)⁻¹ * (SemidirectProduct.inl y)⁻¹ := by
          rw [hx]
          group
      _ = SemidirectProduct.inl a *
            SemidirectProduct.inl (permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f) σ y) *
            (SemidirectProduct.inl a)⁻¹ * (SemidirectProduct.inl y)⁻¹ := by
          rw [hinr, SemidirectProduct.inl_aut]
      _ = (SemidirectProduct.inl z : L2Wreath f n) := by
          simp only [hz, map_mul, map_inv]
  rw [hw, ← map_pow, ← map_one (SemidirectProduct.inl :
      (Fin n → CFSG.Theory.Comparator.PSL2Model f) →* L2Wreath f n)] at hsq
  have hz2 : z ^ 2 = 1 := SemidirectProduct.inl_injective hsq
  have hzi := congrFun hz2 i
  have hyi : y i = t := by
    rw [hy]
    exact Pi.mulSingle_eq_same (M := fun _ => CFSG.Theory.Comparator.PSL2Model f) i t
  have hyσ : y (σ⁻¹ i) = 1 := by
    rw [hy]
    exact Pi.mulSingle_eq_of_ne (M := fun _ => CFSG.Theory.Comparator.PSL2Model f) hi' t
  have hperm : permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f) σ y i = y (σ⁻¹ i) := rfl
  simp only [hz, Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, hperm, hyσ, hyi,
    mul_one, mul_inv_cancel, one_mul] at hzi
  have h2 : t ^ 2 = 1 := by
    have : (t⁻¹ ^ 2)⁻¹ = 1 := by rw [hzi, inv_one]
    rwa [inv_pow, inv_inv] at this
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [ht] at hdvd
  norm_num at hdvd

theorem commutator_closure_ne_bot (h3 : TenThree) {hC : HypothesisC D} {f n : ℕ}
    (h : TenHyp hC f n) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ⁅Subgroup.closure β, Subgroup.closure β⁆ ≠ ⊥ := by
  intro hB
  obtain ⟨e⟩ := h.iso
  obtain ⟨v, hvβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  have hvD : v ∈ DalphaStar D hC.alpha := ⟨β, hβ, hvβ⟩
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hvD
  set v' : Halpha D hC.alpha := ⟨v, hvH⟩ with hv'
  have hright : (tenHom hC e v').right ≠ 1 := fun h1 =>
    not_mem_tenBase_of_mem_DalphaStar h e hvD ((mem_tenBase_iff hC e v').mpr h1)
  obtain ⟨y, hy⟩ := exists_base_commutator_sq_ne_one h.two_le hright
  obtain ⟨l', hl'⟩ := tenHom_surjective hC e (SemidirectProduct.inl y)
  have hlL : (l' : G) ∈ tenBase hC e := (mem_tenBase_iff hC e l').mpr (by rw [hl']; rfl)
  have hw : (l' : G) * v * (l' : G)⁻¹ ∈ β := by
    rw [h3 G D hC f n h e β hβ v hvβ]
    exact ⟨l', hlL, rfl⟩
  have hcomm : v * ((l' : G) * v * (l' : G)⁻¹) = ((l' : G) * v * (l' : G)⁻¹) * v := by
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.subset_closure hvβ)
      (Subgroup.subset_closure hw)
    rw [hB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hvv : v * v = 1 :=
    hC.setup.oddT.mul_self_eq_one (DalphaStar_subset hC.isBlock_alpha hvD)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hsq : (v * (l' : G) * v⁻¹ * (l' : G)⁻¹) ^ 2 = 1 := by
    rw [hvinv, pow_two]
    calc v * ↑l' * v * (↑l')⁻¹ * (v * ↑l' * v * (↑l')⁻¹)
        = v * (↑l' * v * (↑l')⁻¹) * (v * (↑l' * v * (↑l')⁻¹)) := by group
      _ = v * (↑l' * v * (↑l')⁻¹) * ((↑l' * v * (↑l')⁻¹) * v) := by rw [hcomm]
      _ = v * (↑l' * (v * v) * (↑l')⁻¹) * v := by group
      _ = 1 := by rw [hvv, mul_one, mul_inv_cancel, mul_one, hvv]
  apply hy
  have hsqH : (v' * l' * v'⁻¹ * l'⁻¹) ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have := congrArg (tenHom hC e) hsqH
  simpa [map_mul, map_inv, map_pow, hl'] using this

theorem commutator_closure_le_blockKernel (h3 : TenThree) (h87 : Theorem8_7) {hC : HypothesisC D}
    {f n : ℕ} (h : TenHyp hC f n) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ⁅Subgroup.closure β, Subgroup.closure β⁆ ≤ blockKernel hC.alpha := by
  classical
  obtain ⟨e⟩ := h.iso
  have hN := hC.setup.normal
  have hLH : tenBase hC e ≤ Halpha D hC.alpha := by
    rw [tenBase_eq]
    exact Subgroup.map_subtype_le _
  obtain ⟨v, hvβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  have hvD : v ∈ DalphaStar D hC.alpha := ⟨β, hβ, hvβ⟩
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hvD
  have hBL : ⁅Subgroup.closure β, Subgroup.closure β⁆ ≤ tenBase hC e := by
    refine CFSG.GroupTheory.commutator_closure_le_of_forall_eq_conj hLH
      (fun _ hh _ hl => conj_mem_tenBase hC e hh hl) hvH ?_
    intro x hx
    rw [h3 G D hC f n h e β hβ v hvβ] at hx
    exact hx
  have hfixα : ∀ b ∈ ⁅Subgroup.closure β, Subgroup.closure β⁆,
      (fun y => b * y * b⁻¹) '' hC.alpha = hC.alpha := by
    intro b hb
    have hbc := Halpha_le_centralizer D hC.alpha (hLH (hBL hb))
    have hfix : ∀ a ∈ hC.alpha, b * a * b⁻¹ = a := fun a ha => by
      rw [(Subgroup.mem_centralizer_iff.mp hbc a ha).symm, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      show b * a * b⁻¹ ∈ hC.alpha
      rw [hfix a ha]
      exact ha
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  have hfixD : ∀ b ∈ ⁅Subgroup.closure β, Subgroup.closure β⁆, ∀ γ ∈ Dalpha D hC.alpha,
      (fun y => b * y * b⁻¹) '' γ = γ := by
    intro b hb γ hγ
    obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
    exact CFSG.GroupTheory.image_conj_eq_of_eq_conjOrbit (h3 G D hC f n h e γ hγ c hc) (hBL hb)
  have hcentB : ∀ x ∈ Halpha D β, ∀ b ∈ ⁅Subgroup.closure β, Subgroup.closure β⁆,
      x * b = b * x := by
    intro x hx b hb
    have hbβ : b ∈ Subgroup.closure β := Subgroup.commutator_le_self _ hb
    have hcl : Subgroup.closure β ≤ Subgroup.centralizer (Halpha D β : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer D β hz) y hy).symm
    exact Subgroup.mem_centralizer_iff.mp (hcl hbβ) x hx
  have hfixConj : ∀ b x : G, x * b = b * x → ∀ δ : Set G, (fun y => b * y * b⁻¹) '' δ = δ →
      (fun y => b * y * b⁻¹) '' ((fun y => x * y * x⁻¹) '' δ) = (fun y => x * y * x⁻¹) '' δ := by
    intro b x hxb δ hδ
    have hfun : (fun y => b * (x * y * x⁻¹) * b⁻¹) = (fun y => x * (b * y * b⁻¹) * x⁻¹) := by
      funext y
      have hb' : b⁻¹ * x⁻¹ = x⁻¹ * b⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hxb]
      calc b * (x * y * x⁻¹) * b⁻¹ = (b * x) * y * (x⁻¹ * b⁻¹) := by group
        _ = (x * b) * y * (b⁻¹ * x⁻¹) := by rw [hxb, hb']
        _ = x * (b * y * b⁻¹) * x⁻¹ := by group
    rw [Set.image_image, hfun, ← Set.image_image (fun y => x * y * x⁻¹), hδ]
  have hsymm : ∀ {X Y : Set G}, X ∈ Dalpha D Y → Y ⊆ D → Y ∈ Dalpha D X :=
    fun hX hY => ⟨mem_blockClass_comm.mpr hX.1, hY, hX.2.2.1.symm,
      fun a ha b hb => (hX.2.2.2 b hb a ha).symm⟩
  have hαβ : hC.alpha ∈ Dalpha D β := hsymm hβ hC.isBlock_alpha.subset
  have hβcl : β ∈ blockClass hC.alpha := hβ.1
  intro b hb
  rw [mem_blockKernel_iff]
  intro δ hδ
  rcases h87 G D hC h.rad h.not_o4PairData β hβcl δ hδ with hδβ | hδβ | ⟨γ, hγβ, hγδ⟩
  ·
    rw [← hδβ]
    exact hfixD b hb β hβ
  ·
    obtain ⟨x, hx, hxδ⟩ := exists_mem_Halpha_image_eq hC hβcl hαβ hδβ
    rw [← hxδ]
    exact hfixConj b x (hcentB x hx b hb) _ (hfixα b hb)
  ·
    obtain ⟨x, hx, hxγ⟩ := exists_mem_Halpha_image_eq hC hβcl hαβ hγβ
    have hδsub : δ ⊆ D := subset_of_mem_blockClass hN hC.isBlock_alpha hδ
    have hδγ : δ ∈ Dalpha D γ := hsymm hγδ hδsub
    set δ' := (fun y => x⁻¹ * y * x) '' δ with hδ'def
    have hδ' : δ' ∈ Dalpha D hC.alpha := by
      have h0 := Dalpha.conj hN hδγ x⁻¹
      simp only [inv_inv] at h0
      have hγα : (fun y => x⁻¹ * y * x) '' γ = hC.alpha := by
        rw [← hxγ, Set.image_image]
        have : (fun y => x⁻¹ * (x * y * x⁻¹) * x) = id := by
          funext y
          simp only [id]
          group
        rw [this, Set.image_id]
      rwa [hγα] at h0
    have hδeq : δ = (fun y => x * y * x⁻¹) '' δ' := by
      rw [hδ'def, Set.image_image]
      have : (fun y => x * (x⁻¹ * y * x) * x⁻¹) = id := by
        funext y
        simp only [id]
        group
      rw [this, Set.image_id]
    rw [hδeq]
    exact hfixConj b x (hcentB x hx b hb) δ' (hfixD b hb δ' hδ')

theorem tenFour_of_tenThree (h3 : TenThree) (h87 : Theorem8_7) : TenFour :=
  fun _ _ _ _ _ _ _ h _ hβ =>
    ⟨commutator_closure_ne_bot h3 h hβ, commutator_closure_le_blockKernel h3 h87 h hβ⟩

end CFSG.OddTranspositions.PartThree

end
