module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF79JL5
public import CFSG.RankThree.PartTwo.Sec21.FF79KOneSix


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 L14 L41

variable {G : Type} [Group G] [Finite G]

theorem le_cenS_of_normal {J : Subgroup G} (hq : CFSG.IsQuasisimple ↥J) {W : Subgroup G}
    (hWJ : W ≤ J) (hn : ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) {t : G} (htJ : t ∈ J)
    (htW : t ∉ W) : W ≤ CenS J := by
  have hI : (W.subgroupOf J).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn h h.2 x hx⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hI with htop | hcen
  · exfalso
    apply htW
    have : (⟨t, htJ⟩ : ↥J) ∈ W.subgroupOf J := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  · intro z hz
    have hz' := hcen (show (⟨z, hWJ hz⟩ : ↥J) ∈ W.subgroupOf J from hz)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hz' ⟨g, hg⟩
    exact congrArg Subtype.val this

theorem not_mem_of_isPGroup_two {N : Subgroup G} (hN : IsPGroup 2 N) {t : G}
    (ht : orderOf t = 3) : t ∉ N := by
  intro htN
  obtain ⟨k, hk⟩ := hN ⟨t, htN⟩
  have h1 : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := ht ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem isPGroup_conjBy {p : ℕ} {V : Subgroup G} (hV : IsPGroup p V) (g : G) :
    IsPGroup p (conjBy g V) := hV.of_equiv ((MulAut.conj g).subgroupMap V)

theorem conjBy_cenS (g : G) (H : Subgroup G) : CenS (conjBy g H) = conjBy g (CenS H) := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    show g⁻¹ * z * g ∈ CenS H
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_centralizer_iff.mp hz (g * h * g⁻¹) ⟨h, hh, by simp⟩
    calc h * (g⁻¹ * z * g) = g⁻¹ * ((g * h * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * h * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * z * g * h := by group
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * c * g⁻¹) = g * (h * c) * g⁻¹ := by group
      _ = g * (c * h) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * (g * h * g⁻¹) := by group

theorem conjBy_closure_pair {n b b₁ : G} (h1 : n * b * n⁻¹ = b₁) (h2 : n * b₁ * n⁻¹ = b) :
    conjBy n (Subgroup.closure {b, b₁}) = Subgroup.closure {b, b₁} := by
  show (Subgroup.closure {b, b₁}).map (MulAut.conj n).toMonoidHom = _
  rw [MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h1, h2]
  rw [Set.pair_comm]

namespace Setup14

variable {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B)
include S

theorem X_le_cenS_gen : Opp 3 (Cen b) ≤ CenS J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc := S.J_le_cen
  set X := Opp 3 (Cen b) with hXdef
  obtain ⟨t, ht, hto⟩ := S.exists_order3
  have hW : X ⊓ J ≤ CenS J := by
    refine le_cenS_of_normal S.hq inf_le_right (fun j hj w hw => ?_) ht.2 ?_
    · exact ⟨Opp_conj_mem (hJc hj) hw.1, J.mul_mem (J.mul_mem hj hw.2) (J.inv_mem hj)⟩
    · intro htX
      have h3 := Subgroup.orderOf_dvd_natCard X htX.1
      rw [hto] at h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Opp_coprime 3 _) h3
  intro x hx
  have hxc : x ∈ Cen b := Opp_le 3 _ hx
  have hcomm := centralizes_of_comm_central S.hq.1 (t := x) (fun j hj => by
    have hjc : j ∈ Cen b := hJc hj
    have hc : x * j * x⁻¹ * j⁻¹ ∈ X ⊓ J := by
      refine ⟨?_, J.mul_mem (S.hJn x hxc j hj) (J.inv_mem hj)⟩
      have h2 := X.mul_mem hx (Opp_conj_mem hjc (X.inv_mem hx))
      simpa [mul_assoc] using h2
    exact ⟨hc.2, hW hc⟩)
  rw [Subgroup.mem_centralizer_iff]
  exact hcomm

theorem c0_mem_X {c : G} (hc : c ∈ Cen b ⊓ CenS J) {N : ℕ} (hN : ¬ 3 ∣ N) (hcN : c ^ N = 1) :
    c ∈ Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, x, hx, rfl⟩ := S.C0_decomp c hc
  have hxc : x ∈ Cen b := Opp_le 3 _ hx
  have hbx : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  have hcm : Commute (b ^ i) x := hbx.zpow_left i
  rw [hcm.mul_pow] at hcN
  have hy : (b ^ i) ^ N ∈ Opp 3 (Cen b) := by
    have : (b ^ i) ^ N = (x ^ N)⁻¹ := eq_inv_of_mul_eq_one_left hcN
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hx N)
  have hb3 : b ^ 3 = 1 := S.hyp.ord ▸ pow_orderOf_eq_one b
  have hbi3 : (b ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hy3 : ((b ^ i) ^ N) ^ 3 = 1 := by rw [pow_right_comm, hbi3, one_pow]
  have hy1 : (b ^ i) ^ N = 1 := by
    have d1 : orderOf ((b ^ i) ^ N) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have d2 : orderOf ((b ^ i) ^ N) ∣ Nat.card (Opp 3 (Cen b)) :=
      (Subgroup.orderOf_mk _ hy).symm ▸ Subgroup.orderOf_dvd_natCard _ hy
    have := Nat.eq_one_of_dvd_coprimes (Opp_coprime 3 (Cen b)) d1 d2
    exact orderOf_eq_one_iff.mp this
  have hbi : b ^ i = 1 := by
    rw [← zpow_natCast, ← zpow_mul] at hy1
    have h1 : ((orderOf b : ℕ) : ℤ) ∣ i * N := orderOf_dvd_iff_zpow_eq_one.mpr hy1
    rw [S.hyp.ord] at h1
    have h3 : (3 : ℤ) ∣ i := by
      rcases Int.prime_three.dvd_or_dvd h1 with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hN
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [S.hyp.ord]; exact h3)
  rw [hbi, one_mul]
  exact hx

theorem two_group_cen_le {Vs : Subgroup G} (hV : IsPGroup 2 Vs)
    (hJ : ∀ j ∈ J, ∀ z ∈ Vs, j * z * j⁻¹ ∈ Vs) : Vs ⊓ Cen b ≤ Opp 3 (Cen b) := by
  obtain ⟨t₀, ht₀, ht₀o⟩ := S.exists_order3
  have hW : Vs ⊓ J ≤ CenS J := by
    refine le_cenS_of_normal S.hq inf_le_right (fun j hj w hw => ?_) ht₀.2
      (fun h => not_mem_of_isPGroup_two hV ht₀o h.1)
    exact ⟨hJ j hj w hw.1, J.mul_mem (J.mul_mem hj hw.2) (J.inv_mem hj)⟩
  intro t ht
  have htJ : t ∈ CenS J := by
    have hcomm := centralizes_of_comm_central S.hq.1 (t := t) (fun j hj => by
      have hc : t * j * t⁻¹ * j⁻¹ ∈ Vs ⊓ J := by
        refine ⟨?_, J.mul_mem (S.hJn t ht.2 j hj) (J.inv_mem hj)⟩
        have h2 := Vs.mul_mem ht.1 (hJ j hj t⁻¹ (Vs.inv_mem ht.1))
        simpa [mul_assoc] using h2
      exact ⟨hc.2, hW hc⟩)
    rw [Subgroup.mem_centralizer_iff]
    exact hcomm
  obtain ⟨k, hk⟩ := hV ⟨t, ht.1⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine S.c0_mem_X ⟨ht.2, htJ⟩ (N := 2 ^ k) (fun h => ?_) hk'
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

end Setup14

theorem opp_cenS_pair {b : G} {J B : Subgroup G} (S : Setup14 5 b J B) (hCA : FF79KCentAlpha)
    {α : G} (hα : α ∈ B ⊓ J) (hαo : orderOf α = 3) :
    Opp 3 (CenS (Subgroup.closure {b, α})) = Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbA : b ∈ Subgroup.closure {b, α} := Subgroup.subset_closure (by simp)
  have hαA : α ∈ Subgroup.closure {b, α} := Subgroup.subset_closure (by simp)
  have hAcen : CenS (Subgroup.closure {b, α}) ≤ Cen b :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  have hXJ := S.X_le_cenS_gen
  apply le_antisymm
  · set Y := Opp 3 (CenS (Subgroup.closure {b, α})) with hY
    have hYle : Y ≤ CenS (Subgroup.closure {b, α}) := Opp_le 3 _
    have hjA : ∀ j ∈ J ⊓ Cen α, j ∈ CenS (Subgroup.closure {b, α}) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hle : Subgroup.closure {b, α} ≤ Cen j := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (S.J_le_cen hj.1)).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hj.2).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    obtain ⟨-, hY5⟩ := hCA G 5 J (B ⊓ J) (Or.inr rfl) S.hq S.hyp.model S.hB0 α hα hαo Y
      (hYle.trans (hAcen.trans S.cen_le_nor))
      (hYle.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hαA)))
      (Opp_coprime 3 _) (fun j hj y hy => Opp_conj_mem (hjA j hj) hy)
    intro y hy
    refine S.c0_mem_X ⟨hAcen (hYle hy), hY5 rfl hy⟩ (N := Nat.card Y) ?_ ?_
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Opp_coprime 3 _)
    · have := pow_card_eq_one' (G := ↥Y) (x := (⟨y, hy⟩ : ↥Y))
      have h := congrArg Subtype.val this
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
  · refine le_Opp_of_normalized ?_ (fun h hh x hx => Opp_conj_mem (hAcen hh) hx)
      (Opp_coprime 3 _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxc : x ∈ Cen b := Opp_le 3 _ hx
    have hxα : x ∈ Cen α := by
      have := Subgroup.mem_centralizer_iff.mp (hXJ hx) α hα.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
    have hle : Subgroup.closure {b, α} ≤ Cen x := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxα).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem ff79_4_1_of
    (hK : FF79KTypeLn) (h14k : FF79KCenterJ ∧ FF79KAutCentP ∧ FF79KCentAlpha) : FF79_4_1 := by
  obtain ⟨hCJ, -, hCA⟩ := h14k
  intro G _ _ b J B b₁ b₂ h
  by_contra hodd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := setup14 hK hCJ (Or.inr rfl) h.hyp h.sylB
  have hXJ := S.X_le_cenS_gen
  obtain ⟨-, -, -, -, ⟨n₁, -, hn1b, hn1b1, -⟩, -⟩ := h.mono
  have hb₁J : b₁ ∈ J := h.hb₁.2
  have hb₁o : orderOf b₁ = 3 := by
    rw [← hn1b, ← h.hyp.ord]
    exact orderOf_injective (MulAut.conj n₁).toMonoidHom (MulAut.conj n₁).injective b
  have hXn : conjBy n₁ (Opp 3 (Cen b)) = Opp 3 (Cen b) := by
    have e : conjBy n₁ (Opp 3 (CenS (Subgroup.closure {b, b₁}))) =
        Opp 3 (CenS (Subgroup.closure {b, b₁})) := by
      rw [conjBy_Opp, ← conjBy_cenS, conjBy_closure_pair hn1b hn1b1]
    rwa [opp_cenS_pair S hCA h.hb₁ hb₁o] at e
  obtain ⟨V, hV⟩ := exists_sylowOf_p (p := 2) (Opp 3 (Cen b))
  have hVX : V ≤ Opp 3 (Cen b) := hV.1
  have hVne : V ≠ ⊥ := by
    intro hbot
    have h2 : 2 ∣ Nat.card (Opp 3 (Cen b)) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have hpos : 0 < ((Nat.card (Opp 3 (Cen b))).factorization 2) :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have hc := isSylowOf_card_p hV
    rw [hbot, Subgroup.card_bot] at hc
    have : 2 ^ 1 ≤ 2 ^ ((Nat.card (Opp 3 (Cen b))).factorization 2) :=
      Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hVJ : ∀ j ∈ J, ∀ y ∈ V, j * y * j⁻¹ = y := by
    intro j hj y hy
    have := Subgroup.mem_centralizer_iff.mp (hXJ (hVX hy)) j hj
    rw [this]
    group
  have hJV : J ≤ Nor V := fun j hj =>
    mem_nor_of_forall (fun y hy => by rw [hVJ j hj y hy]; exact hy)
  have hVs2 : IsPGroup 2 (Op 2 (Nor V)) := Op_isPGroup _
  have hVV : V ≤ Op 2 (Nor V) := by
    refine le_Op_of_normalized (fun y hy => mem_nor_of_forall (fun z hz =>
      V.mul_mem (V.mul_mem hy hz) (V.inv_mem hy))) (fun g hg x hx => ?_) hV.2.1
    exact ((Subgroup.mem_set_normalizer_iff.mp hg) x).mp hx
  have hJV' : ∀ j ∈ J, ∀ z ∈ Op 2 (Nor V), j * z * j⁻¹ ∈ Op 2 (Nor V) :=
    fun j hj z hz => Op_conj_mem (hJV hj) hz
  have hJVs : J ≤ Nor (Op 2 (Nor V)) := fun j hj => mem_nor_of_forall (hJV' j hj)
  have hT : Op 2 (Nor V) ⊓ Cen b ≤ V := by
    have hTX : Op 2 (Nor V) ⊓ Cen b ≤ Opp 3 (Cen b) := S.two_group_cen_le hVs2 hJV'
    have hTp : IsPGroup 2 ↥(Op 2 (Nor V) ⊓ Cen b) := hVs2.to_inf_left
    have hVT : V ≤ Op 2 (Nor V) ⊓ Cen b := le_inf hVV (hVX.trans (Opp_le 3 _))
    obtain ⟨k, hk, hkT⟩ := exists_conj_le_sylowOf_p hV hTX hTp
    have hle : conjBy k (Op 2 (Nor V) ⊓ Cen b) ≤ V := by
      rintro _ ⟨y, hy, rfl⟩
      exact hkT y hy
    have hcard := Subgroup.card_le_of_le hle
    rw [card_conjBy] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hVT hcard) ▸ le_rfl
  obtain ⟨m, hm, hmb⟩ : ∃ m ∈ Nor V, m * b * m⁻¹ = b₁ := by
    have hQX : conjBy n₁ V ≤ Opp 3 (Cen b) := by
      intro z hz
      rw [← hXn]
      exact Subgroup.map_mono hVX hz
    obtain ⟨k, hk, hkQ⟩ := exists_conj_le_sylowOf_p hV hQX (isPGroup_conjBy hV.2.1 n₁)
    refine ⟨k * n₁, mem_nor_of_forall (fun y hy => ?_), ?_⟩
    · have := hkQ (n₁ * y * n₁⁻¹) ⟨y, hy, rfl⟩
      simpa [mul_assoc] using this
    · have hkc : b₁ * k = k * b₁ :=
        Subgroup.mem_centralizer_iff.mp (hXJ hk) b₁ hb₁J
      calc k * n₁ * b * (k * n₁)⁻¹ = k * (n₁ * b * n₁⁻¹) * k⁻¹ := by group
        _ = b₁ := by rw [hn1b, ← hkc]; group
  have hT1 : Op 2 (Nor V) ⊓ Cen b₁ ≤ V := by
    rintro u ⟨hu, hu1⟩
    have hw : m⁻¹ * u * m ∈ Op 2 (Nor V) ⊓ Cen b := by
      refine ⟨by simpa using Op_conj_mem ((Nor V).inv_mem hm) hu, ?_⟩
      have hb : u * b₁ = b₁ * u := Subgroup.mem_centralizer_singleton_iff.mp hu1
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e : b = m⁻¹ * b₁ * m := by rw [← hmb]; group
      calc m⁻¹ * u * m * b = m⁻¹ * (u * (m * b * m⁻¹)) * m := by group
        _ = m⁻¹ * (u * b₁) * m := by rw [hmb]
        _ = m⁻¹ * (b₁ * u) * m := by rw [hb]
        _ = b * (m⁻¹ * u * m) := by rw [e]; group
    have := ((Subgroup.mem_set_normalizer_iff.mp hm) (m⁻¹ * u * m)).mp (hT hw)
    simpa [mul_assoc] using this
  have hEq : V = Op 2 (Nor V) :=
    ff79_1_6_holds G J (Op 2 (Nor V)) V (ff79_JL5_holds G b J h.hyp) hVs2 hJVs hVV hJV b₁ hb₁J
      hb₁o hT1
  have hchar : IsCharacteristicP 2 ↥(Nor V) := h.char2 (Nor V) ⟨V, hVne, hV.2.1, rfl⟩
  have hbc : ∀ y ∈ V, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (Opp_le 3 _ (hVX hy))
  have hbN : b ∈ Nor V := mem_nor_of_forall (fun y hy => by
    rw [← hbc y hy]
    simpa using hy)
  have hbV : b ∈ Op 2 (Nor V) :=
    mem_Op_of_centralizes hchar hbN (fun z hz => (hbc z (hEq ▸ hz)).symm)
  exact not_mem_of_isPGroup_two hVs2 h.hyp.ord hbV

end CFSG.RankThree.PartTwo.Sec21.FF79
