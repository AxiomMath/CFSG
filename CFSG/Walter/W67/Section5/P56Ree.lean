module

public import CFSG.Walter.W67.Section5.P56Ward
public import CFSG.Walter.ReeOrder.WardLocal.Statements

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Sec56

structure TFacts (T : Subgroup G) (r : ℕ) (J : G) : Prop where
  card : Nat.card T = r ^ 3
  card_center : Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = r
  center_inf_J : J ∈ Subgroup.normalizer (T : Set G) →
    T ⊓ Subgroup.centralizer (T : Set G) ⊓ Subgroup.centralizer ({J} : Set G) = ⊥
  exists_pow_three_ne_one : ∃ y ∈ T, y ^ 3 ≠ 1
  card_abelian_le : ∀ A : Subgroup G, A ≤ T → IsMulCommutative A → Nat.card A ≤ r ^ 2

theorem card_abelian_le_of_ward
    {L : Type} [Group L] [Finite L] (hW : Ward.ReeTypeHyp L)
    (P : Sylow 3 L) {A : Subgroup L} (hAP : A ≤ P) (hAc : IsMulCommutative A) :
    Nat.card A ≤ hW.q ^ 2 := by
  obtain ⟨hPcard, -, -, hZcard, P₁, W, hP₁P, hPN, -, hP₁card, -, hCP, -⟩ :=
    WardLocal.ward_two_three hW P
  set Z := (Subgroup.center (P : Subgroup L)).map (P : Subgroup L).subtype with hZdef
  by_cases h : ∃ a ∈ A, a ∈ P₁ ∧ a ∉ Z
  · obtain ⟨a, haA, haP₁, haZ⟩ := h
    have hAC : A ≤ (P : Subgroup L) ⊓ Subgroup.centralizer ({a} : Set L) := fun b hb =>
      Subgroup.mem_inf.mpr ⟨hAP hb, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAc.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩))⟩
    rw [hCP a haP₁ haZ] at hAC
    exact (Subgroup.card_le_of_le hAC).trans (le_of_eq hP₁card)
  · push Not at h
    have hAN : A ≤ Subgroup.normalizer (P₁ : Set L) := hAP.trans hPN
    have e := Sec52.card_sup_mul_card_inf hAN
    have i1 : Nat.card (A ⊔ P₁ : Subgroup L) ≤ Nat.card (P : Subgroup L) :=
      Subgroup.card_le_of_le (sup_le hAP hP₁P)
    have i2 : Nat.card (P₁ ⊓ A : Subgroup L) ≤ Nat.card Z :=
      Subgroup.card_le_of_le fun a ha => h a (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp ha).1
    rw [hPcard] at i1
    rw [hZcard] at i2
    rw [hP₁card] at e
    have hq : 0 < hW.q := by
      rw [Ward.ReeTypeHyp.q]
      exact pow_pos hW.fact_prime.out.pos _
    have : hW.q ^ 2 * Nat.card A ≤ hW.q ^ 2 * hW.q ^ 2 := by
      rw [← e]
      calc Nat.card (A ⊔ P₁ : Subgroup L) * Nat.card (P₁ ⊓ A : Subgroup L)
          ≤ hW.q ^ 3 * hW.q := Nat.mul_le_mul i1 i2
        _ = hW.q ^ 2 * hW.q ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)

theorem exists_conj_of_card_le_two {D : Subgroup G} {J t : G} (hJD : J ∈ D) (htD : t ∈ D)
    (hoJ : orderOf J = 2) (hot : orderOf t = 2)
    (hD : ∀ W : Subgroup G, W ≤ D → IsPGroup 2 W → Nat.card W ≤ 2) :
    ∃ d ∈ D, d * t * d⁻¹ = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J₁ : D := ⟨t, htD⟩
  set J₂ : D := ⟨J, hJD⟩
  have hoJ₁ : orderOf J₁ = 2 := by rw [Subgroup.orderOf_mk, hot]
  have hoJ₂ : orderOf J₂ = 2 := by rw [Subgroup.orderOf_mk, hoJ]
  have hS : ∀ y : D, orderOf y = 2 → ∃ S : Sylow 2 D, (S : Subgroup D) = Subgroup.zpowers y := by
    intro y hy
    have hp : IsPGroup 2 (Subgroup.zpowers y) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hy, pow_one]
    obtain ⟨S, hSle⟩ := hp.exists_le_sylow
    refine ⟨S, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [Nat.card_zpowers, hy]
    have := hD ((S : Subgroup D).map D.subtype) (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  obtain ⟨S₁, hS₁⟩ := hS J₁ hoJ₁
  obtain ⟨S₂, hS₂⟩ := hS J₂ hoJ₂
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D S₁ S₂
  have hmem : d * J₁ * d⁻¹ ∈ Subgroup.zpowers J₂ := by
    rw [← hS₂, ← hd, Sylow.coe_subgroup_smul, hS₁]
    exact ⟨J₁, Subgroup.mem_zpowers J₁, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hoJ₂ hmem with h1 | h1
  · exfalso
    have : J₁ = 1 := by
      have := congrArg (fun z => d⁻¹ * z * d) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hoJ₁
    exact absurd hoJ₁ (by norm_num)
  · refine ⟨d, d.2, ?_⟩
    have := congrArg Subtype.val h1
    simpa using this

end Sec56

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.exists_ree
    (s : Std G) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {x : G}
    (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) (h9 : 9 ≤ s.f) :
    s.J ∈ s.L (Subgroup.zpowers x) ∧ 3 ∣ s.f ∧ Odd (s.f / 3) ∧
    ∃ hL : JRGroup (s.L (Subgroup.zpowers x)), hL.q = 3 ^ (s.f / 3) ∧ hL.R3 ∧
      Nonempty (Ward.ReeTypeHyp (s.L (Subgroup.zpowers x))) := by
  set X := Subgroup.zpowers x with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hox]
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have heX : s.eX X = 3 := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXcard]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr hXE hX1
  rw [heX] at hediv
  have hm3 : 3 ≤ s.f / 3 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hLS := s.L_spec X hXE hX1
  obtain ⟨K', hK'jr, -⟩ := hLS.jr
  have hfpos : 0 < s.f / s.eX X := by rw [heX]; omega
  obtain ⟨hL, hLp, hLf, -, -⟩ := hJR G s.p_ne_two hfpos hK'jr
  have hq : hL.q = 3 ^ (s.f / 3) := by rw [JRGroup.q, hLp, hLf, heX, hp]
  have h5 : 5 < hL.q := by
    rw [hq]
    calc 5 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (s.f / 3) := Nat.pow_le_pow_right (by norm_num) hm3
  obtain ⟨⟨⟨m, hmodd, hm⟩, -⟩, -, hR3, -⟩ := hR _ hL (by omega)
  have hmf : m = s.f / 3 := by
    rw [hq] at hm
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hm).symm
  refine ⟨hK'jr.J_mem, hediv, hmf ▸ hmodd, hL, hq, hR3, ?_⟩
  exact (hL.toJTHyp h5).nonempty_reeTypeHyp_of_three (by
    change hL.p = 3
    rw [hLp, hp])

theorem not_four_dvd {m : ℕ} (hm : Odd m) : ¬ 4 ∣ (3 ^ m) ^ 3 * (3 ^ m - 1) := by
  obtain ⟨j, rfl⟩ := hm
  have h1 : 3 ^ (2 * j + 1) % 4 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  intro h
  have hcop : Nat.Coprime 4 ((3 ^ (2 * j + 1)) ^ 3) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (by norm_num))
  have h2 := hcop.dvd_of_dvd_mul_left h
  have h3 : 1 ≤ 3 ^ (2 * j + 1) := Nat.one_le_pow _ _ (by norm_num)
  generalize 3 ^ (2 * j + 1) = y at h1 h2 h3
  omega

theorem _root_.CFSG.Walter.W67.Std.tfacts_of_nine
    (s : Std G) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {x : G}
    (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) (h9 : 9 ≤ s.f) {T : Subgroup G}
    (hTL : T ≤ s.L (Subgroup.zpowers x)) (hTcard : Nat.card T = (3 ^ (s.f / 3)) ^ 3) :
    Sec56.TFacts T (3 ^ (s.f / 3)) s.J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, -, hmodd, hL, hLq, hR3, ⟨hW⟩⟩ := s.exists_ree h26i hJR hR hp hxE hox h9
  have hr3 : 3 < hL.q := by
    rw [hLq]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (s.f / 3) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 (s.L (Subgroup.zpowers x))) := inferInstance
  have hP₀c : Nat.card (P₀ : Subgroup (s.L (Subgroup.zpowers x))) = hL.q ^ 3 := by
    have h := hR3 hr3 P₀
    simp only at h
    exact h.1
  have hTsub : Nat.card (T.subgroupOf (s.L (Subgroup.zpowers x))) =
      3 ^ (Nat.card (s.L (Subgroup.zpowers x))).factorization 3 := by
    rw [← Sylow.card_eq_multiplicity P₀, hP₀c, hLq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hTcard]
  set P : Sylow 3 (s.L (Subgroup.zpowers x)) := Sylow.ofCard _ hTsub with hPdef
  have hmemP : ∀ y : s.L (Subgroup.zpowers x),
      y ∈ (P : Subgroup (s.L (Subgroup.zpowers x))) ↔ (y : G) ∈ T := fun y => by
    rw [hPdef, Sylow.coe_ofCard, Subgroup.mem_subgroupOf]
  have hR3P := hR3 hr3 P
  simp only at hR3P
  obtain ⟨hPc, -, hZc, -, -, hZ₂cl, -, hZ₂c, W, -, hWc, hPW, hNP, hWt⟩ := hR3P
  set Z : Subgroup (s.L (Subgroup.zpowers x)) :=
    (Subgroup.center (P : Subgroup (s.L (Subgroup.zpowers x)))).map
      (P : Subgroup (s.L (Subgroup.zpowers x))).subtype with hZdef
  have hmemZ : ∀ z : s.L (Subgroup.zpowers x), z ∈ Z ↔
      z ∈ (P : Subgroup (s.L (Subgroup.zpowers x))) ∧
        ∀ p ∈ (P : Subgroup (s.L (Subgroup.zpowers x))), p * z = z * p := by
    intro z
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, fun p hp => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨p, hp⟩)
    · rintro ⟨hz, hzc⟩
      refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun p => Subtype.ext (hzc p p.2), rfl⟩
  have hZT : Z.map (s.L (Subgroup.zpowers x)).subtype =
      T ⊓ Subgroup.centralizer (T : Set G) := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzP, hzc⟩ := (hmemZ z).mp hz
      refine Subgroup.mem_inf.mpr ⟨(hmemP z).mp hzP, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro t ht
      exact congrArg Subtype.val (hzc ⟨t, hTL ht⟩ ((hmemP _).mpr ht))
    · intro hg
      obtain ⟨hgT, hgC⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hTL hgT⟩, (hmemZ _).mpr ⟨(hmemP _).mpr hgT, fun p hp => ?_⟩, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC p ((hmemP p).mp hp))
  have hcardZT : Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) =
      3 ^ (s.f / 3) := by
    rw [← hZT, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZc, hLq]
  have hWq : hW.q = 3 ^ (s.f / 3) := by
    have h1 := (WardLocal.ward_two_three hW P).1
    rw [hPc, hLq] at h1
    exact (Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h1).symm
  refine ⟨hTcard, hcardZT, ?_, ?_, ?_⟩
  ·
    intro hJT
    set J' : s.L (Subgroup.zpowers x) := ⟨s.J, hJL⟩ with hJ'def
    have hoJ' : orderOf J' = 2 := by rw [Subgroup.orderOf_mk, s.orderOf_J]
    have hJ'N : J' ∈ Subgroup.normalizer
        ((P : Subgroup (s.L (Subgroup.zpowers x))) : Set (s.L (Subgroup.zpowers x))) := by
      apply Sec53.mem_normalizer_of_conj_le
      intro y hy
      rw [hmemP] at hy ⊢
      exact (Subgroup.mem_normalizer_iff.mp hJT y).mp hy
    have h2W : 2 ∣ Nat.card W := by
      rw [hWc, hLq]
      exact (Nat.Odd.sub_odd (Odd.pow (by decide : Odd 3)) odd_one).two_dvd
    obtain ⟨⟨t, htW⟩, hot⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
    rw [Subgroup.orderOf_mk] at hot
    have hWN : W ≤ Subgroup.normalizer
        ((P : Subgroup (s.L (Subgroup.zpowers x))) : Set (s.L (Subgroup.zpowers x))) := by
      rw [hNP]
      exact le_sup_right
    have hDcard : Nat.card (Subgroup.normalizer
        ((P : Subgroup (s.L (Subgroup.zpowers x))) : Set (s.L (Subgroup.zpowers x)))) =
        (3 ^ (s.f / 3)) ^ 3 * (3 ^ (s.f / 3) - 1) := by
      rw [hNP, Sec54.card_sup_eq_mul hWN hPW, hPc, hWc, hLq]
    have hD2 : ∀ W' : Subgroup (s.L (Subgroup.zpowers x)), W' ≤ Subgroup.normalizer
        ((P : Subgroup (s.L (Subgroup.zpowers x))) : Set (s.L (Subgroup.zpowers x))) →
        IsPGroup 2 W' → Nat.card W' ≤ 2 := by
      intro W' hW'D hW'2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW'2
      have hdvd := Subgroup.card_dvd_of_le hW'D
      rw [hk, hDcard] at hdvd
      rw [hk]
      by_contra hk2
      push Not at hk2
      have hk2' : 2 ≤ k := by
        by_contra h
        push Not at h
        interval_cases k <;> simp at hk2
      exact not_four_dvd hmodd ((pow_dvd_pow 2 hk2').trans hdvd)
    obtain ⟨d, hdD, hdt⟩ := Sec56.exists_conj_of_card_le_two hJ'N (hWN htW) hoJ' hot hD2
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgZ, hgJ⟩ := Subgroup.mem_inf.mp hg
    rw [← hZT] at hgZ
    obtain ⟨z, hz, rfl⟩ := hgZ
    rw [Subgroup.mem_bot]
    have hzJ : z * J' = J' * z := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgJ)
    obtain ⟨hzP, hzc⟩ := (hmemZ z).mp hz
    set z' := d⁻¹ * z * d with hz'def
    have hz'Z : z' ∈ Z := by
      refine (hmemZ _).mpr ⟨?_, fun p hp => ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ hdD) z).mp hzP
        simpa [hz'def, mul_assoc] using this
      · have hp' : d * p * d⁻¹ ∈ (P : Subgroup (s.L (Subgroup.zpowers x))) :=
          (Subgroup.mem_normalizer_iff.mp hdD p).mp hp
        have h1 := hzc _ hp'
        calc p * z' = d⁻¹ * ((d * p * d⁻¹) * z) * d := by rw [hz'def]; group
          _ = d⁻¹ * (z * (d * p * d⁻¹)) * d := by rw [h1]
          _ = z' * p := by rw [hz'def]; group
    have hz't : z' ∈ Subgroup.centralizer ({t} : Set (s.L (Subgroup.zpowers x))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ht' : t = d⁻¹ * J' * d := by rw [← hdt]; group
      rw [ht', hz'def]
      calc d⁻¹ * z * d * (d⁻¹ * J' * d) = d⁻¹ * (z * J') * d := by group
        _ = d⁻¹ * (J' * z) * d := by rw [hzJ]
        _ = d⁻¹ * J' * d * (d⁻¹ * z * d) := by group
    have hz'1 : z' ∈ Z ⊓ Subgroup.centralizer ({t} : Set (s.L (Subgroup.zpowers x))) :=
      Subgroup.mem_inf.mpr ⟨hz'Z, hz't⟩
    rw [(hWt t htW hot).2, Subgroup.mem_bot] at hz'1
    have hz1 : z = 1 := by
      have := congrArg (fun w => d * w * d⁻¹) hz'1
      simpa [hz'def, mul_assoc] using this
    rw [hz1]
    rfl
  ·
    by_contra h
    push Not at h
    have hle : (P : Subgroup (s.L (Subgroup.zpowers x))) ≤
        (Subgroup.upperCentralSeries (P : Subgroup (s.L (Subgroup.zpowers x))) 2).map
          (P : Subgroup (s.L (Subgroup.zpowers x))).subtype := by
      rw [hZ₂cl]
      intro p hp
      apply Subgroup.subset_closure
      refine ⟨hp, Subtype.ext ?_⟩
      simpa using h p ((hmemP p).mp hp)
    have h1 := Subgroup.card_le_of_le hle
    rw [hPc, hZ₂c] at h1
    have h2 : hL.q ^ 2 < hL.q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  ·
    intro A hAT hAc
    have hAL : A ≤ s.L (Subgroup.zpowers x) := hAT.trans hTL
    have hA'P : A.subgroupOf (s.L (Subgroup.zpowers x)) ≤
        (P : Subgroup (s.L (Subgroup.zpowers x))) := fun y hy =>
      (hmemP y).mpr (hAT (Subgroup.mem_subgroupOf.mp hy))
    have hA'c : IsMulCommutative (A.subgroupOf (s.L (Subgroup.zpowers x))) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have h1 : ((a : s.L (Subgroup.zpowers x)) : G) * ((b : s.L (Subgroup.zpowers x)) : G) =
          ((b : s.L (Subgroup.zpowers x)) : G) * ((a : s.L (Subgroup.zpowers x)) : G) :=
        congrArg Subtype.val (hAc.is_comm.comm ⟨((a : s.L (Subgroup.zpowers x)) : G), a.2⟩
          ⟨((b : s.L (Subgroup.zpowers x)) : G), b.2⟩)
      exact Subtype.ext (Subtype.ext h1)
    have h1 := Sec56.card_abelian_le_of_ward hW P hA'P hA'c
    rw [hWq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv] at h1
    exact h1

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.mem_normalizer_L (s : Std G) {X : Subgroup G}
    (hXE : X ≤ s.fr.E) (hX1 : X ≠ ⊥) {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) :
    y ∈ Subgroup.normalizer ((s.L X : Subgroup G) : Set G) := by
  have hLS := s.L_spec X hXE hX1
  apply Sec53.mem_normalizer_of_conj_le
  intro z hz
  exact Subgroup.mem_subgroupOf.mp (hLS.normal.2.conj_mem ⟨z, hLS.normal.1 hz⟩
    (Subgroup.mem_subgroupOf.mpr hz) ⟨y, hy⟩)

theorem inf_centralizer_le_L
    (h26i : S_lemma_2_6_i) (hJR : S_IsJRSubgroup_nonempty_jrGroup)
    (hR : RFacts) (hp : s.p = 3) {Q : Subgroup G} (hQ3 : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ Q, b * y = y * b → y = 1)
    (hJQ : s.J ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3) (h9 : 9 ≤ s.f) :
    Q ⊓ Subgroup.centralizer ({x} : Set G) ≤ s.L (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers x with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hox]
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have heX : s.eX X = 3 := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXcard]
  obtain ⟨hJL, -⟩ := s.exists_ree h26i hJR hR hp hxE hox h9
  have hLS := s.L_spec X hXE hX1
  obtain ⟨K', hK'jr, hK'eq⟩ := hLS.jr
  have hK'K : K' = s.KX X := hK'eq (by
    rw [heX, hp]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (s.f / 3) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)))
  have hKXL : s.KX X ≤ s.L X := hK'K ▸ (hK'jr.K_le.trans inf_le_left)
  have hJx : s.J ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.fr.E_le_H hxE)).symm
  have hCxN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef, ← Sec52.centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hJ2 : ¬ 3 ∣ Nat.card (Subgroup.zpowers s.J) := by
    rw [Nat.card_zpowers, s.orderOf_J]
    norm_num
  have hQx3 : IsPGroup 3 (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
    hQ3.to_le inf_le_left
  have hJN : Subgroup.zpowers s.J ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Sec54.mem_normalizer_inf hJQ (Subgroup.le_normalizer hJx))
  have := Sec56.le_of_coprime_trivial (Q := Q ⊓ Subgroup.centralizer ({x} : Set G))
    (M := Q ⊓ Subgroup.centralizer ({x} : Set G) ⊓ s.L X) (R₀ := Subgroup.zpowers s.J) hQx3
    inf_le_left hJ2 hJN
    (fun j hj => Sec54.mem_normalizer_inf (hJN hj)
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hJL) hj))
    (fun y hy => Sec54.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (s.mem_normalizer_L hXE hX1 (hCxN (Subgroup.mem_inf.mp hy).2)))
    (fun j hj y hy => by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (hJN hj) y).mp hy) (Subgroup.inv_mem _ hy), ?_⟩
      have hjL : j ∈ s.L X := Subgroup.zpowers_le.mpr hJL hj
      have h1 : y * j⁻¹ * y⁻¹ ∈ s.L X := (Subgroup.mem_normalizer_iff.mp
        (s.mem_normalizer_L hXE hX1 (hCxN (Subgroup.mem_inf.mp hy).2)) j⁻¹).mp
        (Subgroup.inv_mem _ hjL)
      rw [show j * y * j⁻¹ * y⁻¹ = j * (y * j⁻¹ * y⁻¹) by group]
      exact Subgroup.mul_mem _ hjL h1)
    (fun y hy hyJ => by
      obtain ⟨hyQ, hyx⟩ := Subgroup.mem_inf.mp hy
      have hyH : y ∈ s.H := Subgroup.mem_centralizer_singleton_iff.mpr
        (hyJ s.J (Subgroup.mem_zpowers _)).symm
      have hyP : y ∈ f5.P₁ := by
        rw [← f5.inf_H_eq_P₁ hp hQ3 hP₁Q hBQ hfpf]
        exact Subgroup.mem_inf.mpr ⟨hyQ, hyH⟩
      refine Subgroup.mem_inf.mpr ⟨hy, hKXL (Subgroup.mem_inf.mpr ⟨f5.P₁_le hyP, ?_⟩)⟩
      rw [hXdef, Sec52.centralizer_zpowers_eq]
      exact hyx)
  exact this.trans inf_le_right

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.eq_of_inf_ne_bot_nine
    (s : Std G) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {x : G}
    (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) (h9 : 9 ≤ s.f) {T T' : Subgroup G}
    (hTL : T ≤ s.L (Subgroup.zpowers x)) (hT'L : T' ≤ s.L (Subgroup.zpowers x))
    (hTc : Nat.card T = (3 ^ (s.f / 3)) ^ 3) (hT'c : Nat.card T' = (3 ^ (s.f / 3)) ^ 3)
    (hne : T ⊓ T' ≠ ⊥) : T = T' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hL, hLq, hR3, ⟨hW⟩⟩ := s.exists_ree h26i hJR hR hp hxE hox h9
  have hr3 : 3 < hL.q := by
    rw [hLq]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (s.f / 3) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 (s.L (Subgroup.zpowers x))) := inferInstance
  have hP₀c : Nat.card (P₀ : Subgroup (s.L (Subgroup.zpowers x))) = hL.q ^ 3 := by
    have h := hR3 hr3 P₀
    simp only at h
    exact h.1
  have hsub : ∀ T₁ : Subgroup G, T₁ ≤ s.L (Subgroup.zpowers x) →
      Nat.card T₁ = (3 ^ (s.f / 3)) ^ 3 → Nat.card (T₁.subgroupOf (s.L (Subgroup.zpowers x))) =
        3 ^ (Nat.card (s.L (Subgroup.zpowers x))).factorization 3 := fun T₁ h1 h2 => by
    rw [← Sylow.card_eq_multiplicity P₀, hP₀c, hLq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv, h2]
  set P := Sylow.ofCard _ (hsub T hTL hTc) with hPdef
  set P' := Sylow.ofCard _ (hsub T' hT'L hT'c) with hP'def
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (s.L (Subgroup.zpowers x)) P P'
  have hTI := (WardLocal.ward_two_three hW P).2.1 g
  have hP' : (P' : Subgroup (s.L (Subgroup.zpowers x))) =
      MulAut.conj g • (P : Subgroup (s.L (Subgroup.zpowers x))) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  rw [← hP'] at hTI
  rcases hTI with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyT'⟩ := Subgroup.mem_inf.mp hy
    have : (⟨y, hTL hyT⟩ : s.L (Subgroup.zpowers x)) ∈
        (P : Subgroup _) ⊓ (P' : Subgroup _) := by
      rw [hPdef, hP'def, Sylow.coe_ofCard, Sylow.coe_ofCard]
      exact Subgroup.mem_inf.mpr ⟨hyT, hyT'⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · have hle : (P : Subgroup (s.L (Subgroup.zpowers x))) ≤ P' := by
      rw [← h]
      exact inf_le_right
    have heq : (P : Subgroup (s.L (Subgroup.zpowers x))) = P' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hPdef, hP'def, Sylow.coe_ofCard,
        Sylow.coe_ofCard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'L).toEquiv, hTc, hT'c])
    rw [hPdef, hP'def, Sylow.coe_ofCard, Sylow.coe_ofCard] at heq
    have := congrArg (fun H => H.map (s.L (Subgroup.zpowers x)).subtype) heq
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left hTL, inf_of_le_left hT'L]
      at this
    exact this

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.exists_le_sylow_nine
    (s : Std G) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) {x : G}
    (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) (h9 : 9 ≤ s.f) {Q : Subgroup G}
    (hQL : Q ≤ s.L (Subgroup.zpowers x)) (hQ3 : IsPGroup 3 Q) :
    ∃ T : Subgroup G, Q ≤ T ∧ T ≤ s.L (Subgroup.zpowers x) ∧
      Nat.card T = (3 ^ (s.f / 3)) ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hL, hLq, hR3, -⟩ := s.exists_ree h26i hJR hR hp hxE hox h9
  have hr3 : 3 < hL.q := by
    rw [hLq]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (s.f / 3) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  have hQ'3 : IsPGroup 3 (Q.subgroupOf (s.L (Subgroup.zpowers x))) :=
    hQ3.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
  obtain ⟨P, hP⟩ := hQ'3.exists_le_sylow
  have hPc : Nat.card (P : Subgroup (s.L (Subgroup.zpowers x))) = hL.q ^ 3 := by
    have h := hR3 hr3 P
    simp only at h
    exact h.1
  refine ⟨(P : Subgroup _).map (s.L (Subgroup.zpowers x)).subtype, ?_, Subgroup.map_subtype_le _,
    ?_⟩
  · intro y hy
    exact ⟨⟨y, hQL hy⟩, hP (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hPc, hLq]

end Frame5

end CFSG.Walter.W67
