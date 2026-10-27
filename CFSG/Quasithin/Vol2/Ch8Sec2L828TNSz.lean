module

public import CFSG.Quasithin.EmptyFaithful.S1565L6
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.H13.L828N

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

@[expose] def E3_828 : Prop :=
  ∀ (n : ℕ) (X : Type) [Group X] [Finite X], IsSz n X →
    (∀ (A : Type) [Group A] [Finite A] (N : Subgroup A) [N.Normal], Nonempty (↥N ≃* X) →
        (∀ a : A, (∀ m ∈ N, a * m = m * a) → a = 1) → Odd (Nat.card (A ⧸ N))) ∧
    ∀ S : Sylow 2 X,
      (∃ Z : Subgroup X, Z ≤ (S : Subgroup X) ∧ Nat.card ↥Z = 2 ^ n ∧ (∀ z ∈ Z, z ^ 2 = 1) ∧
        (∀ s ∈ (S : Subgroup X), s ^ 2 = 1 → s ∈ Z) ∧
        ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 →
          ∃ g ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), g * z * g⁻¹ = z') ∧
      (∀ g : X, g ∉ Subgroup.normalizer ((S : Subgroup X) : Set X) →
        (S : Subgroup X) ⊓ (S : Subgroup X).map (MulAut.conj g).toMonoidHom = ⊥) ∧
      IsCyclic (↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) ⧸
        (S : Subgroup X).subgroupOf (Subgroup.normalizer ((S : Subgroup X) : Set X)))

theorem isSz_of_mulEquiv {n : ℕ} {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsSz n X) : IsSz n X' := by
  obtain ⟨-, a, ha, K, hF, hFin, hf, hK, ⟨θ⟩⟩ := h
  exact ⟨rfl, a, ha, K, hF, hFin, hf, hK, ⟨e.symm.trans θ⟩⟩

theorem szEnd_eq_top (hE3 : E3_828) {X : Type} [Group X] [Finite X] {n : ℕ}
    (Y₀ : Subgroup X) [Y₀.Normal] (hY : IsSz n ↥Y₀)
    (hC : ∀ x : X, (∀ y ∈ Y₀, x * y = y * x) → x = 1)
    (T₀ : Subgroup X) (hT₂ : IsPGroup 2 ↥T₀) (hXY : ∀ x : X, ∃ y ∈ Y₀, ∃ t ∈ T₀, x = y * t) :
    Y₀ = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (X ⧸ Y₀)) := (hE3 n ↥Y₀ hY).1 X Y₀ ⟨MulEquiv.refl _⟩ hC
  have hpi : IsPGroup 2 (X ⧸ Y₀) := by
    refine hT₂.of_surjective ((QuotientGroup.mk' Y₀).comp T₀.subtype) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y₀ q
    obtain ⟨y, hy, t, ht, rfl⟩ := hXY x
    refine ⟨⟨t, ht⟩, ?_⟩
    show ((t : X) : X ⧸ Y₀) = ((y * t : X) : X ⧸ Y₀)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpi
  rw [hm] at hodd
  have hm0 : m = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, h⟩)
  have hidx : Y₀.index = 1 := by
    show Nat.card (X ⧸ Y₀) = 1
    rw [hm, hm0, pow_zero]
  exact Subgroup.index_eq_one.mp hidx

theorem szEnd_card_V (hE3 : E3_828) {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSz n X)
    (T₀ : Subgroup X) (hT₂ : IsPGroup 2 ↥T₀) (hT₀ : ¬ 2 ∣ T₀.index)
    (M₀ : Subgroup X) (hTM : T₀ ≤ M₀) (hM₀ : ∀ B : Subgroup X, T₀ ≤ B → B ≠ ⊤ → B ≤ M₀)
    (V₀ : Subgroup X) (hVT : V₀ ≤ T₀) (hV2 : CFSG.Open.IsElemAbelian 2 V₀)
    (hVM : ∀ m ∈ M₀, ∀ v ∈ V₀, m * v * m⁻¹ ∈ V₀) (hV1 : V₀ ≠ ⊥) :
    Nat.card ↥V₀ = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hb⟩ := hE3 n X hX
  have hST : ((hT₂.toSylow hT₀ : Sylow 2 X) : Subgroup X) = T₀ := rfl
  obtain ⟨⟨Z, -, hZcard, -, hZmax, hZtrans⟩, -, -⟩ := hb (hT₂.toSylow hT₀)
  rw [hST] at hZmax hZtrans
  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hX
    omega
  have hsimple : IsSimpleGroup X := isSimpleGroup_of_psl2_or_sz (Or.inr hX)
  have hT_ne_top : T₀ ≠ ⊤ := by
    intro htop
    have hX2 : IsPGroup 2 X := by
      have h2 : IsPGroup 2 ↥(⊤ : Subgroup X) := by
        rw [← htop]
        exact hT₂
      exact h2.of_equiv Subgroup.topEquiv
    have hcard : Nat.card X = 2 := (hX2.isSimpleGroup_iff_card_eq).mp hsimple
    have hle : Nat.card ↥Z ≤ Nat.card X := Subgroup.card_le_card_group Z
    rw [hZcard, hcard] at hle
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    exact absurd (h8.trans hle) (by norm_num)
  have hV0 : ∃ v ∈ V₀, v ≠ 1 := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩
  have hNne : Subgroup.normalizer ((T₀ : Subgroup X) : Set X) ≠ ⊤ := by
    intro htop
    have hnorm : T₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hsimple.eq_bot_or_eq_top_of_normal T₀ with h | h
    · exact hV1 (le_bot_iff.mp (hVT.trans h.le))
    · exact hT_ne_top h
  have hNM : Subgroup.normalizer ((T₀ : Subgroup X) : Set X) ≤ M₀ :=
    hM₀ _ Subgroup.le_normalizer hNne
  have hVZ : V₀ ≤ Z := fun v hv => hZmax v (hVT hv) (hV2.2 v hv)
  have hZV : Z ≤ V₀ := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact V₀.one_mem
    · obtain ⟨v, hv, hv1⟩ := hV0
      obtain ⟨g, hg, hgz⟩ := hZtrans v (hVZ hv) z hz hv1 hz1
      rw [← hgz]
      exact hVM g (hNM hg) v hv
  rw [le_antisymm hVZ hZV, hZcard]

theorem szEnd_dihedral (hE3 : E3_828) {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSz n X)
    (V₀ I₀ P₀ : Subgroup X) (hVI : V₀ ≤ I₀) (hV2 : CFSG.Open.IsElemAbelian 2 V₀)
    (hV8 : 8 ≤ Nat.card ↥V₀) (hPI : P₀ ≤ I₀) [(P₀.subgroupOf I₀).Normal]
    (hP2 : IsPGroup 2 ↥P₀) (eI : ↥I₀ ⧸ P₀.subgroupOf I₀ ≃* DihedralGroup 5) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hb⟩ := hE3 n X hX
  have hPne : P₀ ≠ ⊥ := by
    intro hP
    have hbot : P₀.subgroupOf I₀ = ⊥ := by
      rw [hP, Subgroup.bot_subgroupOf]
    have hidx : (P₀.subgroupOf I₀).index = Nat.card ↥I₀ := by
      rw [hbot, Subgroup.index_bot]
    have h1 : Nat.card (↥I₀ ⧸ P₀.subgroupOf I₀) = Nat.card (DihedralGroup 5) :=
      Nat.card_congr eI.toEquiv
    have h2 : Nat.card (↥I₀ ⧸ P₀.subgroupOf I₀) = Nat.card ↥I₀ := hidx
    rw [DihedralGroup.nat_card, h2] at h1
    have hdvd : Nat.card ↥V₀ ∣ 10 := by
      have := Subgroup.card_dvd_of_le hVI
      rwa [h1] at this
    have hV2P : IsPGroup 2 ↥V₀ := by
      refine isPGroup_iff_orderOf_dvd_pow.mpr ?_
      intro g
      refine ⟨1, orderOf_dvd_of_pow_eq_one ?_⟩
      exact Subtype.ext (by simpa using hV2.2 g.1 g.2)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hV2P
    rw [hj] at hdvd hV8
    have hj3 : j ≤ 3 := by
      by_contra h
      have h16 : 16 ≤ 2 ^ j := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h10 : 2 ^ j ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have key : ∀ i : ℕ, i ≤ 3 → 8 ≤ 2 ^ i → ¬ 2 ^ i ∣ 10 := by decide
    exact key j hj3 hV8 hdvd
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  obtain ⟨-, hc, hd⟩ := hb S
  have hIN : I₀ ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    intro i hi
    by_contra hni
    apply hPne
    apply eq_bot_iff.mpr
    intro p hp
    have hconj : i⁻¹ * p * i ∈ P₀ := by
      have hpI : p ∈ I₀ := hPI hp
      have hmemsub : (⟨p, hpI⟩ : ↥I₀) ∈ P₀.subgroupOf I₀ := Subgroup.mem_subgroupOf.mpr hp
      have h1 := Subgroup.Normal.conj_mem (inferInstance : (P₀.subgroupOf I₀).Normal)
        ⟨p, hpI⟩ hmemsub ⟨i⁻¹, I₀.inv_mem hi⟩
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [mul_assoc] using h2
    have hmem : p ∈ (S : Subgroup X) ⊓ (S : Subgroup X).map (MulAut.conj i).toMonoidHom := by
      refine ⟨hPS hp, i⁻¹ * p * i, hPS hconj, ?_⟩
      show i * (i⁻¹ * p * i) * i⁻¹ = p
      group
    rw [hc i hni] at hmem
    exact hmem
  have hcommI : ∀ a b : ↥I₀, ((⁅a, b⁆ : ↥I₀) : X) ∈ (S : Subgroup X) := by
    intro a b
    let ψ : ↥I₀ →* ↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) ⧸
        (S : Subgroup X).subgroupOf (Subgroup.normalizer ((S : Subgroup X) : Set X)) :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion hIN)
    have hcomm : ∀ x y : ↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) ⧸
        (S : Subgroup X).subgroupOf (Subgroup.normalizer ((S : Subgroup X) : Set X)),
        x * y = y * x := isMulCommutative_iff.mp inferInstance
    have h1 : ψ ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
    have h2 := (QuotientGroup.eq_one_iff (Subgroup.inclusion hIN ⁅a, b⁆)).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  let φ : ↥I₀ →* DihedralGroup 5 :=
    eI.toMonoidHom.comp (QuotientGroup.mk' (P₀.subgroupOf I₀))
  have hφ : Function.Surjective φ := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨a, ha⟩ := hφ (DihedralGroup.r 1)
  obtain ⟨b, hb'⟩ := hφ (DihedralGroup.sr 0)
  have hφc : φ ⁅a, b⁆ = DihedralGroup.r 2 := by
    rw [map_commutatorElement, ha, hb']
    decide
  have h5 : orderOf (DihedralGroup.r 2 : DihedralGroup 5) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · decide
    · decide
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨((⁅a, b⁆ : ↥I₀) : X), hcommI a b⟩
  have hord : orderOf (⁅a, b⁆ : ↥I₀) = 2 ^ k :=
    ((Subgroup.orderOf_coe _).symm.trans (Subgroup.orderOf_mk _ (hcommI a b)).symm).trans hk
  have hdvd : orderOf (φ ⁅a, b⁆) ∣ orderOf (⁅a, b⁆ : ↥I₀) := orderOf_map_dvd φ _
  rw [hφc, h5, hord] at hdvd
  have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
  norm_num at h52

theorem s828N_szEnd (hE3 : E3_828) {X : Type} [Group X] [Finite X] {n : ℕ}
    (Y₀ : Subgroup X) [Y₀.Normal] (hY : IsSz n ↥Y₀)
    (hC : ∀ x : X, (∀ y ∈ Y₀, x * y = y * x) → x = 1)
    (T₀ : Subgroup X) (hT₂ : IsPGroup 2 ↥T₀) (hT₀ : ¬ 2 ∣ T₀.index)
    (hXY : ∀ x : X, ∃ y ∈ Y₀, ∃ t ∈ T₀, x = y * t)
    (M₀ : Subgroup X) (hTM : T₀ ≤ M₀) (hM₀ : ∀ B : Subgroup X, T₀ ≤ B → B ≠ ⊤ → B ≤ M₀)
    (V₀ : Subgroup X) (hVT : V₀ ≤ T₀) (hV2 : CFSG.Open.IsElemAbelian 2 V₀)
    (hVM : ∀ m ∈ M₀, ∀ v ∈ V₀, m * v * m⁻¹ ∈ V₀) (hV1 : V₀ ≠ ⊥)
    (I₀ P₀ : Subgroup X) (hVI : V₀ ≤ I₀) (hPI : P₀ ≤ I₀) [(P₀.subgroupOf I₀).Normal]
    (hP2 : IsPGroup 2 ↥P₀) (eI : ↥I₀ ⧸ P₀.subgroupOf I₀ ≃* DihedralGroup 5) : False := by
  have hYtop : Y₀ = ⊤ := szEnd_eq_top hE3 Y₀ hY hC T₀ hT₂ hXY
  have hX : IsSz n X :=
    isSz_of_mulEquiv ((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv) hY
  have hCard := szEnd_card_V hE3 hX T₀ hT₂ hT₀ M₀ hTM hM₀ V₀ hVT hV2 hVM hV1
  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hX
    omega
  have hV8 : 8 ≤ Nat.card ↥V₀ := by
    rw [hCard]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  exact szEnd_dihedral hE3 hX V₀ I₀ P₀ hVI hV2 hV8 hPI hP2 eI

end CFSG.Quasithin.H13.L828N
