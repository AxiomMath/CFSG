module

public import CFSG.Quasithin.Vol2.Ch12Sec5O2P
public import CFSG.Quasithin.H13.A6S13821g

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Hat7

open Equiv

theorem isCycle_of_orderOf_seven {g : Perm (Fin 7)} (hg : orderOf g = 7) :
    g.IsCycle ∧ g.support = Finset.univ := by
  have hsupp : g.support.card ≤ 7 := by
    simpa using Finset.card_le_univ g.support
  have h1 : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by rw [hg]; norm_num) (by rw [hg]; omega)
  refine ⟨h1, ?_⟩
  have h2 : g.support.card = 7 := by rw [← h1.orderOf, hg]
  exact Finset.eq_univ_of_card _ (by simp [h2])

theorem mem_zpowers_of_commute {g σ : Perm (Fin 7)} (hg : orderOf g = 7) (hc : Commute σ g) :
    σ ∈ Subgroup.zpowers g := by
  obtain ⟨h1, h2⟩ := isCycle_of_orderOf_seven hg
  obtain ⟨hc', hmem⟩ := (h1.commute_iff).1 hc
  have he : Perm.ofSubtype (σ.subtypePerm hc') = σ :=
    Perm.ofSubtype_subtypePerm _ fun x _ => by rw [h2]; exact Finset.mem_univ x
  rwa [he] at hmem

theorem eq_one_of_commute {σ g h : Perm (Fin 7)} (hg : orderOf g = 7) (hh : orderOf h = 3)
    (hσg : Commute σ g) (hσh : Commute σ h) : σ = 1 := by
  by_contra hσ
  have hmem := mem_zpowers_of_commute hg hσg
  have hσ7 : orderOf σ = 7 := by
    have hd : orderOf σ ∣ 7 := by
      have := orderOf_dvd_of_mem_zpowers hmem
      rwa [hg] at this
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.1 h1) hσ
    · exact h7
  have hh' := orderOf_dvd_of_mem_zpowers (mem_zpowers_of_commute hσ7 hσh.symm)
  rw [hh, hσ7] at hh'
  norm_num at hh'

theorem eq_of_fix {Q : Type} [Group Q] [Finite Q] (hQ : IsHatA7 Q) {L₀ : Subgroup Q}
    (hs : IsSimpleGroup ↥L₀) (hc : Nat.card L₀ = 168) (φ : MulAut Q)
    (hφ : ∀ l ∈ L₀, φ l = l) (x : Q) : φ x = x := by
  classical
  obtain ⟨hq, hZ3, ⟨e⟩⟩ := hQ
  set Z := Subgroup.center Q with hZ
  have hZφ : Z.map φ.toMonoidHom = Z :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance φ
  set φ' : (Q ⧸ Z) ≃* (Q ⧸ Z) := QuotientGroup.congr Z Z φ hZφ with hφ'
  have hφ'mk : ∀ y : Q, φ' (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
  set ψ : MulAut ↥(alternatingGroup (Fin 7)) := e.symm.trans (φ'.trans e) with hψ
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 ψ
  have hfix : ∀ l ∈ L₀, ψ (e (QuotientGroup.mk l)) = e (QuotientGroup.mk l) := by
    intro l hl
    rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hφ'mk,
      hφ l hl]
  have hcomm : ∀ l ∈ L₀, Commute σ ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 7))) :
      Perm (Fin 7)) := by
    intro l hl
    have h1 := hfix l hl
    rw [← hσ] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    show σ * _ = _ * σ
    calc σ * ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
        = σ * ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) * σ⁻¹ *
          σ := by group
      _ = _ := by rw [h2]
  have hL₀Z : ∀ l ∈ L₀, l ∈ Z → l = 1 := by
    intro l hl hlZ
    have hn : (Z.subgroupOf L₀).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have : ((g * n * g⁻¹ : ↥L₀) : Q) = (n : Q) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [Subgroup.mem_center_iff.1 hn (g : Q)]
        group
      rw [this]
      exact hn
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn with hb | ht
    · have : (⟨l, hl⟩ : ↥L₀) ∈ Z.subgroupOf L₀ := hlZ
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hle : L₀ ≤ Z := fun y hy => by
        have : (⟨y, hy⟩ : ↥L₀) ∈ Z.subgroupOf L₀ := ht ▸ Subgroup.mem_top _
        exact this
      have := Subgroup.card_le_of_le hle
      rw [hc, hZ3] at this
      omega
  have h7 : ∃ g : ↥L₀, orderOf g = 7 := exists_prime_orderOf_dvd_card' 7 (by rw [hc]; norm_num)
  have h3 : ∃ g : ↥L₀, orderOf g = 3 := exists_prime_orderOf_dvd_card' 3 (by rw [hc]; norm_num)
  obtain ⟨g₇, hg₇⟩ := h7
  obtain ⟨g₃, hg₃⟩ := h3
  have hord : ∀ (g : ↥L₀) (p : ℕ), p.Prime → orderOf g = p →
      orderOf ((e (QuotientGroup.mk (g : Q)) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
        p := by
    intro g p hp hg
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have hd : orderOf (QuotientGroup.mk (g : Q) : Q ⧸ Z) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, ← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one]
      rfl
    rcases (Nat.dvd_prime hp).1 hd with h1 | hpe
    · exfalso
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      have := hL₀Z _ g.2 h1
      have hg1 : g = 1 := Subtype.ext this
      rw [hg1, orderOf_one] at hg
      exact hp.one_lt.ne hg
    · exact hpe
  have hσ1 : σ = 1 := eq_one_of_commute (hord g₇ 7 (by norm_num) hg₇)
    (hord g₃ 3 Nat.prime_three hg₃) (hcomm _ g₇.2) (hcomm _ g₃.2)
  have hψ1 : ∀ a, ψ a = a := fun a => by
    rw [← hσ, hσ1, map_one]
    rfl
  have hmod : ∀ y : Q, y⁻¹ * φ y ∈ Z := by
    intro y
    have h1 := hψ1 (e (QuotientGroup.mk y))
    rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hφ'mk,
      EmbeddingLike.apply_eq_iff_eq, QuotientGroup.eq] at h1
    have h2 := Subgroup.inv_mem _ h1
    rwa [mul_inv_rev, inv_inv] at h2
  let zH : Q →* ↥Z :=
    { toFun := fun y => ⟨y⁻¹ * φ y, hmod y⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have hc := Subgroup.mem_center_iff.1 (hmod a) (b⁻¹)
        calc b⁻¹ * a⁻¹ * (φ a * φ b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by group
          _ = (a⁻¹ * φ a) * b⁻¹ * φ b := by rw [hc]
          _ = a⁻¹ * φ a * (b⁻¹ * φ b) := by group }
  have hker : commutator Q ≤ zH.ker := Abelianization.commutator_subset_ker zH
  rw [hq.1.commutator_eq_top] at hker
  have hx := hker (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have hx' : x⁻¹ * φ x = 1 := congrArg Subtype.val hx
  rw [inv_mul_eq_one] at hx'
  exact hx'.symm

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
@[expose] def conjK (K : Subgroup G) {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun k := ⟨c * k * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc k).mp k.2⟩
  invFun k := ⟨c⁻¹ * k * c, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) k).mp k.2
    simpa using this⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] noncomputable def autQ (K : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  QuotientGroup.congr _ _ (conjK K hc) (CFSG.pCore_map_iso 2 (conjK K hc))

theorem cent_of_inner {K L₁ : Subgroup G} (hHat : IsHatA7 (↥K ⧸ CFSG.pCore 2 ↥K)) (hLK : L₁ ≤ K)
    (eL : (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hO : pCoreOf 2 L₁ ≤ pCoreOf 2 K) {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G))
    (hcL : ∀ x ∈ L₁, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L₁) :
    ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set ρ : ↥L₁ →* ↥K ⧸ CFSG.pCore 2 ↥K := π.comp (Subgroup.inclusion hLK) with hρ
  set L₀ := ρ.range with hL₀
  have hker : ρ.ker = CFSG.pCore 2 ↥L₁ := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← A6.A6L74.mem_pCoreOf_iff, ← A6.A6L74.mem_pCoreOf_iff]
    constructor
    · intro hx
      have hW : L₁ ⊓ pCoreOf 2 K ≤ pCoreOf 2 L₁ :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
            LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLK hl)⟩)
          ((LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right)
      exact hW ⟨x.2, hx⟩
    · intro hx
      exact hO hx
  let eL₀ : ↥L₀ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans eL)
  have hs : IsSimpleGroup ↥L₀ :=
    @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1 eL₀
  have hc168 : Nat.card ↥L₀ = 168 := by
    rw [Nat.card_congr eL₀.toEquiv, card_sl_three_zmod_two]
  have hfix := eq_of_fix hHat hs hc168 (autQ K hc) (by
    rintro _ ⟨l, rfl⟩
    rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply]
    show QuotientGroup.mk (conjK K hc (Subgroup.inclusion hLK l)) = _
    rw [QuotientGroup.eq, ← A6.A6L74.mem_pCoreOf_iff]
    have h1 := hcL l l.2
    have h2 := Subgroup.inv_mem _ (hO h1)
    have hlN : (l : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      Subgroup.inv_mem _ (LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLK l.2))
    have h3 := (Subgroup.mem_normalizer_iff.mp hlN _).mp h2
    have e : (((conjK K hc (Subgroup.inclusion hLK l))⁻¹ * Subgroup.inclusion hLK l : ↥K) : G) =
        (l : G)⁻¹ * (c * (l : G) * c⁻¹ * (l : G)⁻¹)⁻¹ * (l : G)⁻¹⁻¹ := by
      simp only [conjK, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inclusion]
      group
    rw [e]
    exact h3)
  intro k hk
  have h1 := hfix (π ⟨k, hk⟩)
  rw [hπ, QuotientGroup.mk'_apply] at h1
  change QuotientGroup.mk (conjK K hc ⟨k, hk⟩) = _ at h1
  rw [eq_comm, QuotientGroup.eq, ← A6.A6L74.mem_pCoreOf_iff] at h1
  have hkN : (k : G) ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
  have h2 := (Subgroup.mem_normalizer_iff.mp hkN _).mp h1
  have e : (k : G) * (((⟨k, hk⟩ : ↥K)⁻¹ * conjK K hc ⟨k, hk⟩ : ↥K) : G) * (k : G)⁻¹ =
      c * k * c⁻¹ * k⁻¹ := by
    simp [conjK, mul_assoc]
  rwa [e] at h2

theorem card_of_isHatA7 {Q : Type} [Group Q] [Finite Q] (h : IsHatA7 Q) : Nat.card Q = 7560 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  rw [(Subgroup.center Q).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv, hZ,
    S152V.card_alternatingGroup_seven']

theorem pCoreOf_le_of_hat7 {K L₁ : Subgroup G} (hHat : IsHatA7 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hLK : L₁ ≤ K)
    (eL : (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    pCoreOf 2 L₁ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set ρ : ↥L₁ →* ↥K ⧸ CFSG.pCore 2 ↥K := π.comp (Subgroup.inclusion hLK) with hρ
  have hQ := card_of_isHatA7 hHat
  have hkerle : ρ.ker ≤ CFSG.pCore 2 ↥L₁ := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← A6.A6L74.mem_pCoreOf_iff] at hx
    rw [← A6.A6L74.mem_pCoreOf_iff]
    have hW : L₁ ⊓ pCoreOf 2 K ≤ pCoreOf 2 L₁ :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
          LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLK hl)⟩)
        ((LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right)
    exact hW ⟨x.2, hx⟩
  have h1 : Nat.card ↥L₁ = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [ρ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have h2 : Nat.card ↥L₁ = 168 * Nat.card (CFSG.pCore 2 ↥L₁) := by
    rw [(CFSG.pCore 2 ↥L₁).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eL.toEquiv,
      card_sl_three_zmod_two]
  have h3 : Nat.card ρ.range ∣ 7560 := hQ ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L₁))
  have hkd : Nat.card ρ.ker ∣ 2 ^ m := hm ▸ Subgroup.card_dvd_of_le hkerle
  obtain ⟨w, hw, hwe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkd
  have h4 : Nat.card ρ.range * 2 ^ w = 168 * 2 ^ m := by rw [← hwe, ← h1, h2, hm]
  have h5 : Nat.card ρ.range = 168 * 2 ^ (m - w) := by
    have : 2 ^ m = 2 ^ (m - w) * 2 ^ w := by rw [← pow_add, Nat.sub_add_cancel hw]
    rw [this, ← mul_assoc] at h4
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h4
  have hmw : m = w := by
    by_contra hne
    have h6 : 168 * 2 ∣ 168 * 2 ^ (m - w) :=
      Nat.mul_dvd_mul_left 168 (dvd_pow_self 2 (by omega))
    rw [← h5] at h6
    have := h6.trans h3
    norm_num at this
  have hkeq : ρ.ker = CFSG.pCore 2 ↥L₁ :=
    Subgroup.eq_of_le_of_card_ge hkerle (by rw [hm, hwe, hmw])
  intro x hx
  have hxL : x ∈ L₁ := LieType.BorelTits.pCoreOf_le 2 L₁ hx
  have hy : (⟨x, hxL⟩ : ↥L₁) ∈ ρ.ker := hkeq ▸ (A6.A6L74.mem_pCoreOf_iff _).1 hx
  rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ← A6.A6L74.mem_pCoreOf_iff] at hy
  exact hy

theorem inf_le_pCoreOf (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    oTwoUpper F.P ⊓ li L F.V1 ≤ pCoreOf 2 (li L F.V1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := li L F.V1 with hL₁
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  have hL₁M : L₁ ≤ mi T L F.V1 :=
    (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
  have hMP : mi T L F.V1 ≤ Subgroup.normalizer (oTwoUpper F.P : Set G) :=
    S125Pm.mi_le_normalizer h1222 F hH
  set N₀ : Subgroup ↥L₁ := (oTwoUpper F.P ⊓ L₁).subgroupOf L₁ with hN₀
  have hN₀n : N₀.Normal := by
    rw [hN₀, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hMP (hL₁M hl), Subgroup.le_normalizer hl⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) with hπ
  have hs : IsSimpleGroup (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1 eL
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (N₀.map π)
      (hN₀n.map π (QuotientGroup.mk'_surjective _)) with hb | ht
  · intro x hx
    have h1 : π ⟨x, hx.2⟩ ∈ N₀.map π := ⟨⟨x, hx.2⟩, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← A6.A6L74.mem_pCoreOf_iff] at h1
    exact h1
  · exfalso
    have h168 : Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 168 := by
      rw [Nat.card_congr eL.toEquiv, card_sl_three_zmod_two]
    have h1 : 7 ∣ Nat.card N₀ := by
      have := N₀.card_map_dvd π
      rw [ht, Subgroup.card_top, h168] at this
      exact (by norm_num : 7 ∣ 168).trans this
    have hN₀c : Nat.card N₀ = Nat.card ↥(oTwoUpper F.P ⊓ L₁) := by
      rw [← Subgroup.card_map_of_injective L₁.subtype_injective, hN₀,
        Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    have h2 : Nat.card ↥(oTwoUpper F.P ⊓ L₁) ∣ Nat.card F.P :=
      Subgroup.card_dvd_of_le (inf_le_left.trans (oTwoUpper_le _))
    rw [← hN₀c, S125O2P.card_P h1222 F hH] at h2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH.hyp.sylow.1
    rw [hn] at h2
    have h3 := h1.trans h2
    have hcop : Nat.Coprime 7 (3 * 2 ^ n) :=
      Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right n (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd hcop h3
    norm_num at this

theorem commutator_mem (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K : Subgroup G} (hO : pCoreOf 2 (li L F.V1) ≤ pCoreOf 2 K) {y l : G}
    (hy : y ∈ oTwoUpper F.P) (hl : l ∈ li L F.V1) : y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 K := by
  have hL₁M : li L F.V1 ≤ mi T L F.V1 :=
    (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
  have hML : mi T L F.V1 ≤ Subgroup.normalizer (li L F.V1 : Set G) :=
    S125K6.le_normalizer_li (inf_le_left.trans (sup_le Subgroup.le_normalizer hH.hyp.normalizes))
      inf_le_right
  have hMP := S125Pm.mi_le_normalizer h1222 F hH
  have hPM : F.P ≤ mi T L F.V1 := inf_le_left.trans inf_le_left
  have hyM : y ∈ mi T L F.V1 := hPM ((oTwoUpper_le _) hy)
  refine hO (inf_le_pCoreOf h1222 F hH ⟨?_, ?_⟩)
  · have h1 : l * y⁻¹ * l⁻¹ ∈ oTwoUpper F.P :=
      (Subgroup.mem_normalizer_iff.mp (hMP (hL₁M hl)) _).mp (Subgroup.inv_mem _ hy)
    have := Subgroup.mul_mem _ hy h1
    rwa [show y * (l * y⁻¹ * l⁻¹) = y * l * y⁻¹ * l⁻¹ by group] at this
  · have h1 : y * l * y⁻¹ ∈ li L F.V1 := (Subgroup.mem_normalizer_iff.mp (hML hyM) l).mp hl
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hl)

theorem not_P_le_normalizer (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ¬ F.P ≤ Subgroup.normalizer (T : Set G) := by
  intro hle
  have hf := S125Ex.Facts125.of h1222 hH
  set r : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.reflection 5 (ZMod 2) 1 le_rfl (by norm_num)
    with hrdef
  have hr : r ∈ S125Pm.q234 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic.reflection_mem_parabolic
      (n := 5) (j := 1) le_rfl (by norm_num)
  set u : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2)
    with hudef
  have hu : u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 2) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular
      (show (0 : Fin 5) < 1 by decide) 1
  obtain ⟨x, hx⟩ := S125Pm.phi_surjective F hf.normalizes hf.T_le r
  obtain ⟨y, hy⟩ := S125Pm.phi_surjective F hf.normalizes hf.T_le u
  have hxP : (x : G) ∈ F.P :=
    (S125Pm.mem_P_iff (hLV := hf.normalizes) (hTV := hf.T_le) F x).2 (hx ▸ hr)
  have hyT : (y : G) ∈ T :=
    (S125Pm.mem_T_iff (hLV := hf.normalizes) (hTV := hf.T_le) h1222 F hH y).2 (hy ▸ hu)
  have hxy : ((x * y * x⁻¹ : ↥(L ⊔ T)) : G) ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (hle hxP) _).mp hyT
    simpa using this
  have h1 := (S125Pm.mem_T_iff (hLV := hf.normalizes) (hTV := hf.T_le) h1222 F hH _).1 hxy
  rw [map_mul, map_mul, map_inv, hx, hy] at h1
  have hrr : r * r = 1 := Matrix.SpecialLinearGroup.ext _ _ (fun i j => by
    fin_cases i <;> fin_cases j <;> decide)
  rw [inv_eq_of_mul_eq_one_right hrr] at h1
  have h2 := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.1 h1).1 1 0
    (by decide)
  revert h2
  decide

theorem orderThree_mem_of_hat7 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H K : Subgroup G} (hSQ : SQTKGroup ↥H) (hKc : K ∈ cComp H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7))) :
    ∀ x ∈ H, orderOf x = 3 → x ∈ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hSQ' := SQTKHyp.of_sqtkGroup ↥H hSQ
  have hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := hHat.1
  have hLc := subgroupOf_mem_cComp hKc
  obtain ⟨e₀⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.quotPCore_subgroupOf_equiv (L := K) hKH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr : 1 < CFSG.Open.pRank 3 (K.subgroupOf H) := by
    rw [CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq (L := K) hKH Nat.prime_three
      (by norm_num)]
    have := (A6.A6Hat7.threeRank2_hat7 hHat).pRank_two_le
    omega
  have hconc := a318 hF hSQ (h36 _ hSQ') (h38 _ hSQ') hLc hQ' Nat.prime_three (by norm_num) hr
  have hLmap : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set ρ : ↥K →* PStar 3 ↥H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp (Subgroup.inclusion hKH) with hρ
  have hρrange : ρ.range = starImage 3 (K.subgroupOf H) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKH k, k.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hO2 : CFSG.pCore 2 ↥K ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have hxO : (x : G) ∈ pCoreOf 2 K := (A6.A6L74.mem_pCoreOf_iff (H := K) x).2 hx
    set O : Subgroup ↥H := (pCoreOf 2 K).subgroupOf H with hOdef
    have hOn : O.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((LieType.BorelTits.pCoreOf_le 2 K).trans hKH)).mpr
      (hHK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    have hO3 : Nat.Coprime 3 (Nat.card O) := by
      have h2 : IsPGroup 2 O := ((LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((LieType.BorelTits.pCoreOf_le 2 K).trans hKH)).symm)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hle : O ≤ CFSG.pPrimeCore 3 ↥H := le_sSup ⟨hOn, hO3⟩
    exact hle hxO
  set ψ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(starImage 3 (K.subgroupOf H)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ((MonoidHom.codRestrict ρ _ fun k => by
      rw [← hρrange]; exact ⟨k, rfl⟩)) (fun x hx => by
        apply Subtype.ext
        exact (MonoidHom.mem_ker.mp (hO2 hx))) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hρrange] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨(k : ↥K ⧸ CFSG.pCore 2 ↥K), rfl⟩
  have hnt : ¬ Subsingleton ↥(starImage 3 (K.subgroupOf H)) := by
    intro hsub
    have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [A6.A6Hat7.card_of_isHat_alt7 hHat]
      norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K ⧸ CFSG.pCore 2 ↥K) 3 h3
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) g
    have hk1 : ψ (QuotientGroup.mk' _ k) = 1 := Subsingleton.elim _ _
    have hρk : ρ k = 1 := congrArg Subtype.val hk1
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hρk
    have hcop := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
    have hord : orderOf (⟨Subgroup.inclusion hKH k, hρk⟩ : ↥(CFSG.pPrimeCore 3 ↥H)) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 ↥H) := orderOf_dvd_natCard _
    have h3k : 3 ∣ orderOf k := by
      have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) k
      rw [hg] at h1
      exact h1
    have h3' : 3 ∣ orderOf (⟨Subgroup.inclusion hKH k, hρk⟩ : ↥(CFSG.pPrimeCore 3 ↥H)) := by
      rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hKH) k]
      exact h3k
    exact absurd (Nat.Coprime.coprime_dvd_right (h3'.trans hord) hcop) (by norm_num)
  have hcard := A6.A6Hat7.card_quotient_hat7 hHat ψ hψs hnt
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · have h1' : K = oPrimeResidualOf 3 H := by
      rw [← CFSG.Quasithin.Vol2.Ch11.SecA.map_oPrimeResidualOf_top, ← h1, hLmap]
    intro x hx h3x
    rw [h1']
    exact S125O2P.mem_oPrimeResidualOf_of_orderOf hx h3x
  · exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    exact A6.A6Hat7.not_case2_of_card_hat7 hcard s q hmod hPSL
  · rcases h3 with h | h
    · have hK : K = thetaOf H := by rw [← hLmap, h, R3c2.map_thetaOf_top]
      intro x hx h3x
      rw [hK]
      exact Subgroup.subset_closure ⟨hx, h3x⟩
    · exfalso
      obtain ⟨s, q, x, hSL, -⟩ := h
      exact A6.A6Hat7.not_isSLEps3_of_card_hat7 hcard s q hSL

theorem false_of_hat7 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hHat : IsHatA7 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hSQ : SQTKGroup ↥(Subgroup.normalizer (F.V1 : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian (S125O2P.pCoreOf_G1_ne_bot F)
  have hPK : oTwoUpper F.P ≤ K₁ := S125O2P.oTwoUpper_P_le_of_three h1222 F hH
    (orderThree_mem_of_hat7 hF h36 h38 hSQ hK hK₁n hHat)
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  have hO := pCoreOf_le_of_hat7 hHat hLK eL
  have hOT : pCoreOf 2 K₁ ≤ T := S125Cfg.pCoreOf_le_T h1222 F hH hK₁n hKG
  have hkey : ∀ t ∈ T, ∀ y ∈ oTwoUpper F.P, t * y * t⁻¹ * y⁻¹ ∈ pCoreOf 2 K₁ := by
    intro t ht y hy
    obtain ⟨b, hb, hbx⟩ := S125K1.l1_inner h1222 F hH ht
    have hbK : b ∈ K₁ := hLK hb
    have hcN : b⁻¹ * t ∈ Subgroup.normalizer (K₁ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hbK)) (hK₁n (hTG₁ ht))
    have hc := cent_of_inner hHat hLK eL hO hcN hbx y (hPK hy)
    have hby := commutator_mem h1222 F hH hO hy hb
    have hbO : b ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 K₁ hbK
    have h1 := (Subgroup.mem_normalizer_iff.mp hbO _).mp hc
    have e : t * y * t⁻¹ * y⁻¹ =
        (b * ((b⁻¹ * t) * y * (b⁻¹ * t)⁻¹ * y⁻¹) * b⁻¹) * (y * b * y⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hby)
  apply not_P_le_normalizer h1222 F hH
  have hSP : QuasithinUnique.IsSylowTwoOf T F.P :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (S125Cfg.T_le_P h1222 F hH)
  rw [CFSG.Quasithin.eq_oTwoUpper_sup_of_isSylowTwoOf hSP]
  refine sup_le (fun y hy => S125St.mem_normalizer_of_conj_le fun t ht => ?_)
    Subgroup.le_normalizer
  have h1 := hOT (hkey t⁻¹ (Subgroup.inv_mem _ ht) y hy)
  have e : y * t * y⁻¹ = t * (t⁻¹ * y * t⁻¹⁻¹ * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ ht h1

end S125Hat7

end CFSG.Quasithin.H13
