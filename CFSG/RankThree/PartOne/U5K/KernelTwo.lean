module

public import CFSG.RankThree.PartOne.U5K.Kernel
public import CFSG.RankThree.PartOne.U5K.Perfect
public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

section CommI

variable {G : Type} [Group G] (I : Subgroup G)

@[expose] def commI : Subgroup G := (commutator ↥I).map I.subtype

variable {I}

theorem commI_le : commI I ≤ I := Subgroup.map_subtype_le _

theorem mem_commI {x : G} : x ∈ commI I ↔ ∃ j ∈ commutator ↥I, (j : G) = x := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem conj_mem_commI {m x : G} (hm : m ∈ Subgroup.normalizer (I : Set G)) (hx : x ∈ commI I) :
    m * x * m⁻¹ ∈ commI I := by
  obtain ⟨j, hj, rfl⟩ := mem_commI.1 hx
  have h1 : (I.normalizerMonoidHom ⟨m, hm⟩ j : ↥I) ∈ commutator ↥I := by
    have := Subgroup.characteristic_iff_map_eq.1 (inferInstance : (commutator ↥I).Characteristic)
      (I.normalizerMonoidHom ⟨m, hm⟩)
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hj
  refine mem_commI.2 ⟨_, h1, rfl⟩

end CommI

section Facts

variable {G : Type} [Group G] {f : ℕ} {I : Subgroup G}

theorem isPerfect_quotient (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) (hf : 1 ≤ f) :
    Group.IsPerfect (↥I ⧸ Subgroup.center ↥I) := by
  have := u5_isPerfect f hf
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isPerfect_commI (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) (hf : 1 ≤ f) :
    Group.IsPerfect ↥(commI I) := by
  have := isPerfect_commutator (isPerfect_quotient e hf)
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.equivMapOfInjective (commutator ↥I) I.subtype I.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ _).surjective

theorem commI_ne_bot (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) (hf : 1 ≤ f) :
    commI I ≠ ⊥ := by
  intro h
  have hq := isPerfect_quotient e hf
  have h1 : commutator ↥I = ⊥ := by
    have : (commutator ↥I).map I.subtype = ⊥ := h
    exact (Subgroup.map_eq_bot_iff_of_injective (commutator ↥I) I.subtype_injective).1 this
  have h2 : Subgroup.center ↥I = ⊤ := (commutator_eq_bot_iff_center_eq_top ↥I).1 h1
  have hs := u5_isSimpleGroup f hf
  have : Subsingleton (↥I ⧸ Subgroup.center ↥I) := by
    rw [h2]
    exact QuotientGroup.subsingleton_quotient_top
  have h3 : Subsingleton (projSU 5 2 f) := e.toEquiv.symm.subsingleton
  exact not_subsingleton _ h3

theorem kerG_le_centralizer_commI (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) :
    kerG I e ≤ Subgroup.centralizer (commI I : Set G) := by
  intro c hc
  obtain ⟨hcN, hc1⟩ := mem_kerG.1 hc
  set α := I.normalizerMonoidHom ⟨c, hcN⟩ with hα
  have hz : ∀ x : ↥I, α x * x⁻¹ ∈ Subgroup.center ↥I := by
    intro x
    have h1 := U5Act_apply I e ⟨c, hcN⟩ x
    rw [hc1] at h1
    have h2 : ((α x : ↥I) : ↥I ⧸ Subgroup.center ↥I) = (x : ↥I ⧸ Subgroup.center ↥I) :=
      e.injective (by rw [← h1]; rfl)
    have := (QuotientGroup.eq_iff_div_mem).1 h2
    simpa [div_eq_mul_inv] using this
  have hfix := fixed_of_trivial_mod_center α hz
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_commI.1 hg
  have h3 : α j = j := hfix hj
  have h4 : c * (j : G) * c⁻¹ = (j : G) := congrArg Subtype.val h3
  calc (j : G) * c = (c * (j : G) * c⁻¹) * c := by rw [h4]
    _ = c * (j : G) := by group

theorem normal_two_le_zOf (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) (hf : 1 ≤ f)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ commI I) (hK₀2 : IsPGroup 2 K₀)
    (hnorm : ∀ x ∈ commI I, ∀ k ∈ K₀, x * k * x⁻¹ ∈ K₀) : K₀ ≤ zOf I := by
  classical
  have hq := isPerfect_quotient e hf
  have hsup := commutator_sup_center_eq_top hq
  have hsurj : ∀ q : projSU 5 2 f, ∃ j ∈ commutator ↥I, e (QuotientGroup.mk j) = q := by
    intro q
    obtain ⟨x, rfl⟩ := e.surjective q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y ∈ commutator ↥I ⊔ Subgroup.center ↥I := hsup ▸ Subgroup.mem_top y
    obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
    refine ⟨j, hj, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]
  set W : Subgroup (projSU 5 2 f) :=
    ((K₀.subgroupOf I).map (QuotientGroup.mk' (Subgroup.center ↥I))).map e.toMonoidHom with hW
  have hWmem : ∀ w, w ∈ W ↔ ∃ (k : G) (hk : k ∈ I), k ∈ K₀ ∧
      e (QuotientGroup.mk ⟨k, hk⟩) = w := by
    intro w
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, y.2, hy, rfl⟩
    · rintro ⟨k, hk, hkK, rfl⟩
      exact ⟨_, ⟨⟨k, hk⟩, hkK, rfl⟩, rfl⟩
  have hWnormal : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    obtain ⟨k, hk, hkK, rfl⟩ := (hWmem w).1 hw
    obtain ⟨j, hj, rfl⟩ := hsurj g
    have hjc : (j : G) ∈ commI I := mem_commI.2 ⟨j, hj, rfl⟩
    have hk' : (j : G) * k * (j : G)⁻¹ ∈ K₀ := hnorm _ hjc k hkK
    have hI : (j : G) * k * (j : G)⁻¹ ∈ I := commI_le (hK₀ hk')
    refine (hWmem _).2 ⟨(j : G) * k * (j : G)⁻¹, hI, hk', ?_⟩
    have : (⟨(j : G) * k * (j : G)⁻¹, hI⟩ : ↥I) = j * ⟨k, hk⟩ * j⁻¹ := rfl
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hW2 : IsPGroup 2 W := by
    intro w
    obtain ⟨k, hk, hkK, hw⟩ := (hWmem w).1 w.2
    obtain ⟨n, hn⟩ := hK₀2 ⟨k, hkK⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 : (⟨k, hk⟩ : ↥I) ^ 2 ^ n = 1 := Subtype.ext (by simpa using h1)
    have h3 : (w : projSU 5 2 f) ^ 2 ^ n = 1 := by
      rw [← hw, ← map_pow, ← QuotientGroup.mk_pow, h2]
      simp
    simpa using h3
  have hW1 : W = ⊥ := by
    have := hWnormal
    exact u5_normal_two_eq_bot f hf W hW2
  intro k hk
  have hkI : k ∈ I := commI_le (hK₀ hk)
  have hmem : e (QuotientGroup.mk ⟨k, hkI⟩) ∈ W := (hWmem _).2 ⟨k, hkI, hk, rfl⟩
  rw [hW1] at hmem
  have h1 : (QuotientGroup.mk ⟨k, hkI⟩ : ↥I ⧸ Subgroup.center ↥I) = 1 :=
    e.injective ((Subgroup.mem_bot.1 hmem).trans (map_one e).symm)
  have h2 : (⟨k, hkI⟩ : ↥I) ∈ Subgroup.center ↥I := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨⟨k, hkI⟩, h2, rfl⟩

end Facts

theorem ker_not_dvd_two_of_max {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {I E A : Subgroup G} {f : ℕ} (hf : 1 ≤ f) (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hEel : IsElementaryAbelian p E) (hEN : E ≤ Subgroup.normalizer (I : Set G)) (hAE : A ≤ E)
    (hodp : ¬ p ∣ Nat.card (U5Act I e).ker) (hchar : IsCharacteristicPType G 2)
    (h1511 : ∀ M ∈ maximalTwoLocalsContaining (A : Set G), M ≤ Subgroup.normalizer (I : Set G)) :
    ¬ 2 ∣ Nat.card (U5Act I e).ker := by
  classical
  intro hdvd2
  have : Fact p.Prime := ⟨hp⟩
  have hCperf := isPerfect_commI e hf
  have hEp : IsPGroup p E := by
    have := hEel
    exact IsElementaryAbelian.isPGroup p ↥E
  have hodpCg : ¬ p ∣ Nat.card (kerG I e) := by rw [card_kerG]; exact hodp
  obtain ⟨sylow, hsyl⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      p hp E (kerG I e) hEp hodpCg (le_normalizer_kerG hEN) 2 Nat.prime_two
  set Q : Subgroup G := (sylow : Subgroup ↥(kerG I e)).map (kerG I e).subtype with hQ
  have hQ2 : IsPGroup 2 Q := sylow.isPGroup'.map _
  have hQC : Q ≤ kerG I e := Subgroup.map_subtype_le _
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Nat.card Q = 1 := by rw [h]; exact Subgroup.card_bot
    have h2 : Nat.card Q = 2 ^ (Nat.card (kerG I e)).factorization 2 := by
      rw [hQ, Subgroup.card_map_of_injective (kerG I e).subtype_injective,
        Sylow.card_eq_multiplicity]
    rw [h2] at h1
    have hdvdCg : 2 ∣ Nat.card (kerG I e) := by rw [card_kerG]; exact hdvd2
    have hpos : 0 < (Nat.card (kerG I e)).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hdvdCg
    have := Nat.one_lt_pow hpos.ne' Nat.one_lt_two
    omega
  have hI'Q : commI I ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((Subgroup.mem_centralizer_iff.1 (kerG_le_centralizer_commI e (hQC hq)) x hx)).symm
  have hM0loc : IsPLocal 2 (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQne, hQ2, rfl⟩
  have hI'M0 : commI I ≤ Subgroup.normalizer (Q : Set G) :=
    hI'Q.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨M₁, hM0M1, hM1max⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hM0loc
  have hM1A : M₁ ∈ maximalTwoLocalsContaining (A : Set G) :=
    ⟨hM1max, fun a ha => hM0M1 (hsyl (hAE ha))⟩
  have hM1N : M₁ ≤ Subgroup.normalizer (I : Set G) := h1511 M₁ hM1A
  have hI'M1 : commI I ≤ M₁ := hI'M0.trans hM0M1
  set Rg : Subgroup G := inSubgroup (CFSG.pCore 2) M₁ with hRg
  have hRg2 : IsPGroup 2 Rg := (CFSG.pCore_isPGroup (p := 2) (G := ↥M₁)).map M₁.subtype
  have hM1Rg : M₁ ≤ Subgroup.normalizer (Rg : Set G) :=
    Subgroup.le_normalizer.trans
      (Sec15Final.normalizer_le_normalizer_map_subtype_of_characteristic inferInstance)
  have hRgM1 : Rg ≤ M₁ := Subgroup.map_subtype_le _
  have hI'norm : ∀ m ∈ M₁, ∀ x ∈ commI I, m * x * m⁻¹ ∈ commI I := fun m hm x hx =>
    conj_mem_commI (hM1N hm) hx
  have hRgnorm : ∀ m ∈ M₁, ∀ r ∈ Rg, m * r * m⁻¹ ∈ Rg := fun m hm r hr =>
    (Subgroup.mem_normalizer_iff.1 (hM1Rg hm) r).1 hr
  have hcomm_mem : ∀ x ∈ commI I, ∀ r ∈ Rg, x * r * x⁻¹ * r⁻¹ ∈ commI I ⊓ Rg := by
    intro x hx r hr
    refine ⟨?_, ?_⟩
    · have h1 := hI'norm r (hRgM1 hr) x⁻¹ ((commI I).inv_mem hx)
      have : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
      rw [this]
      exact (commI I).mul_mem hx h1
    · exact Rg.mul_mem (hRgnorm x (hI'M1 hx) r hr) (Rg.inv_mem hr)
  have hK₀Z : commI I ⊓ Rg ≤ zOf I := by
    refine normal_two_le_zOf e hf (K₀ := commI I ⊓ Rg) inf_le_left
      (hRg2.to_le inf_le_right) ?_
    intro x hx k hk
    exact ⟨hI'norm x (hI'M1 hx) k hk.1, hRgnorm x (hI'M1 hx) k hk.2⟩
  have hcommZ : ⁅commI I, Rg⁆ ≤ zOf I :=
    Subgroup.commutator_le.2 fun x hx r hr => hK₀Z (hcomm_mem x hx r hr)
  have hZcent : ∀ H : Subgroup G, H ≤ zOf I → ⁅H, commI I⁆ = ⊥ := by
    intro H hH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨hzI, hzc⟩ := mem_zOf_iff.1 (hH hz)
    exact hzc x (commI_le hx)
  have hrot : ⁅⁅commI I, commI I⁆, Rg⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (hZcent _ hcommZ) ?_
    rw [Subgroup.commutator_comm Rg (commI I)]
    exact hZcent _ hcommZ
  have hperf : ⁅commI I, commI I⁆ = commI I := Subgroup.isPerfect_iff.1 hCperf
  rw [hperf] at hrot
  have hcen : commI I ≤ Subgroup.centralizer (Rg : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hrot
  have hI'Rg : commI I ≤ Rg := by
    intro x hx
    have hxM : x ∈ M₁ := hI'M1 hx
    have hchM := hchar M₁ hM1max.1
    have hcent : (⟨x, hxM⟩ : ↥M₁) ∈
        Subgroup.centralizer ((CFSG.pCore 2 ↥M₁ : Subgroup ↥M₁) : Set ↥M₁) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzR : (z : G) ∈ Rg := ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hcen hx) (z : G) hzR)
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ CFSG.pCore 2 ↥M₁, (z : G) = x := ⟨⟨x, hxM⟩, hchM hcent, rfl⟩
    exact ⟨z, hz, hzx⟩
  have hI'2 : IsPGroup 2 (commI I) := hRg2.to_le hI'Rg
  have hne := commI_ne_bot e hf
  have hnil : Group.IsNilpotent ↥(commI I) := hI'2.isNilpotent
  have hnt : Nontrivial ↥(commI I) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isNilpotent (G := ↥(commI I)) hnil

end CFSG.RankThree.PartOne.U5K
