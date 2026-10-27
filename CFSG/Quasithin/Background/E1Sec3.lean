module

public import CFSG.Quasithin.Background.E1Sections
public import CFSG.Quasithin.Background.E1Util

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique

section Series

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem oTwoPTwo_eq_top_of_series [Finite Q] {p : ℕ} [Fact p.Prime] {N₂ N₂p : Subgroup Q}
    [N₂.Normal] [N₂p.Normal] (h2 : IsPGroup 2 N₂)
    (hp : ∀ x ∈ N₂p, ∃ k : ℕ, x ^ p ^ k ∈ N₂) (hq : ∀ q : Q, ∃ k : ℕ, q ^ 2 ^ k ∈ N₂p) :
    oTwoPTwo Q p = ⊤ := by
  have hN2 : N₂ ≤ CFSG.Open.pCore 2 Q := CFSG.LieType.BorelTits.le_pCore 2 inferInstance h2
  have hpg : IsPGroup p (N₂p.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨k, hk⟩ := hp x hx
    refine ⟨k, Subtype.ext ?_⟩
    show (y : Q ⧸ CFSG.Open.pCore 2 Q) ^ p ^ k = 1
    rw [← hxy, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hN2 hk)
  have hnorm : (N₂p.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hle2 : N₂p.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q)) ≤
      CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) :=
    CFSG.LieType.BorelTits.le_pCore p hnorm hpg
  have hM : N₂p ≤ oTwoP Q p := fun x hx => hle2 (Subgroup.mem_map_of_mem _ hx)
  have h2g : IsPGroup 2 (⊤ : Subgroup (Q ⧸ oTwoP Q p)) := by
    intro y
    obtain ⟨q, hq'⟩ := QuotientGroup.mk_surjective (y : Q ⧸ oTwoP Q p)
    obtain ⟨k, hk⟩ := hq q
    refine ⟨k, Subtype.ext ?_⟩
    show (y : Q ⧸ oTwoP Q p) ^ 2 ^ k = 1
    rw [← hq', ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hM hk
  have hle3 : (⊤ : Subgroup (Q ⧸ oTwoP Q p)) ≤ CFSG.Open.pCore 2 (Q ⧸ oTwoP Q p) :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance h2g
  refine eq_top_iff.mpr fun x _ => ?_
  exact hle3 (Subgroup.mem_top _)

theorem exists_pow_mem_pCore_of_oTwoP_eq_top {p : ℕ} [Fact p.Prime] (h : oTwoP Q p = ⊤)
    (q : Q) : ∃ k : ℕ, q ^ p ^ k ∈ CFSG.Open.pCore 2 Q := by
  have hq : q ∈ oTwoP Q p := by rw [h]; exact Subgroup.mem_top q
  have hq' : (QuotientGroup.mk' (CFSG.Open.pCore 2 Q) q) ∈
      CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) := hq
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p) ⟨_, hq'⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  simpa using congrArg Subtype.val hk

end Series

section Aux

variable {G : Type*} [Group G]

private theorem le_normalizer_sup' {K S₁ S₂ : Subgroup G}
    (h₁ : K ≤ Subgroup.normalizer (S₁ : Set G)) (h₂ : K ≤ Subgroup.normalizer (S₂ : Set G)) :
    K ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
  intro g hg
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁ hg)
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]

theorem le_normalizer_inf_of_le_normalizer {K N : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    K ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro w
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hKN hk) w]
  constructor
  · rintro ⟨hwK, hwX⟩
    exact ⟨K.mul_mem (K.mul_mem hk hwK) (K.inv_mem hk), hwX⟩
  · rintro ⟨hwK, hwX⟩
    refine ⟨?_, hwX⟩
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) hwK) hk
    simpa [mul_assoc] using this

theorem mul_pow_eq_of_mem_normalizer {O : Subgroup G} {a o : G}
    (ha : a ∈ Subgroup.normalizer (O : Set G)) (ho : o ∈ O) (m : ℕ) :
    ∃ o' ∈ O, (a * o) ^ m = a ^ m * o' := by
  induction m with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨o', ho', h⟩ := ih
    have h1 : a⁻¹ * o' * a ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) o').mp ho'
      simpa [mul_assoc] using this
    refine ⟨(a⁻¹ * o' * a) * o, O.mul_mem h1 ho, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem pow_relIndex_mem {P Z : Subgroup G} (hZP : Z ≤ Subgroup.normalizer (P : Set G)) {z : G}
    (hz : z ∈ Z) : z ^ P.relIndex Z ∈ P := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hZP
  have h1 : ((⟨z, hz⟩ : Z) : Z ⧸ P.subgroupOf Z) ^ Nat.card (Z ⧸ P.subgroupOf Z) = 1 :=
    pow_card_eq_one'
  have e : Nat.card (Z ⧸ P.subgroupOf Z) = P.relIndex Z := rfl
  rw [e, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

end Aux

section PreO2

variable {G : Type*} [Group G]

theorem le_normalizer_preO2 (K Y : Subgroup G) [Y.Normal] :
    K ≤ Subgroup.normalizer (preO2 K Y : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hkb : QuotientGroup.mk' Y k ∈ K.map (QuotientGroup.mk' Y) := Subgroup.mem_map_of_mem _ hk
  have h1 := Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K.map (QuotientGroup.mk' Y)) hkb)
    (QuotientGroup.mk' Y z)
  simp only [preO2, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
  constructor
  · rintro ⟨hz, hz2⟩
    exact ⟨K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), h1.mp hz2⟩
  · rintro ⟨hz, hz2⟩
    refine ⟨?_, h1.mpr hz2⟩
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk
    simpa [mul_assoc] using this

theorem inf_le_preO2 (K Y : Subgroup G) [Y.Normal] : K ⊓ Y ≤ preO2 K Y := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).mpr hy.2
  show QuotientGroup.mk' Y y ∈ pCoreOf 2 (K.map (QuotientGroup.mk' Y))
  rw [h1]
  exact Subgroup.one_mem _

theorem preO2_le (K Y : Subgroup G) [Y.Normal] : preO2 K Y ≤ K := inf_le_left

end PreO2

section Main

variable {G : Type*} [Group G] [Finite G]

theorem ten_three_data {T X Y K H : Subgroup G} [Y.Normal]
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hYX : Y ≤ X) (hXH : X ≤ H)
    (hT : IsSylowIn 2 T H) (hK : K ∈ sFamily T X Y) {p : ℕ} (hp : p.Prime)
    (h : oTwoP ↥((K ⊓ X).map (QuotientGroup.mk' Y)) p = ⊤) :
    ∃ R : Subgroup G, R = (K ⊓ X) ⊔ preO2 K Y ∧ R ≤ K ∧
      K ≤ Subgroup.normalizer (R : Set G) ∧ preO2 K Y ≤ R ∧
      (∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ T ⊓ preO2 K Y) ∧ (∀ q ∈ K, ∃ k : ℕ, q ^ 2 ^ k ∈ R) := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' Y with hπ
  have hK' := hK
  obtain ⟨hKle, hTK, hEq, hmin⟩ := hK
  obtain ⟨hK1, -, -⟩ := ten_one hTX hYX hK'
  set Xb : Subgroup (G ⧸ Y) := (K ⊓ X).map π with hXb
  set Kb : Subgroup (G ⧸ Y) := K.map π with hKb
  set Db : Subgroup (G ⧸ Y) := pCoreOf 2 Xb with hDb
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hKX : K ≤ Subgroup.normalizer (X : Set G) :=
    hKle.trans (sup_le Subgroup.le_normalizer hTX)
  have hKKX : K ≤ Subgroup.normalizer ((K ⊓ X : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le_normalizer hKX
  have hKbXb : Kb ≤ Subgroup.normalizer (Xb : Set (G ⧸ Y)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.le_normalizer_map π ⟨k, hKKX hk, rfl⟩
  have hXbKb : Xb ≤ Kb := Subgroup.map_mono inf_le_left
  have hKb_eq : Kb = Xb ⊔ T.map π := by
    have := congrArg (Subgroup.map π) hK1
    rwa [Subgroup.map_sup] at this
  have hTb2 : IsPGroup 2 (T.map π) := hT2.map π
  have hTbK : T.map π ≤ Kb := Subgroup.map_mono hTK
  have h3 : ∀ x ∈ Kb, ∃ k : ℕ, x ^ 2 ^ k ∈ Xb := fun x hx =>
    exists_pow_mem_of_mem_sup hTb2 (hTbK.trans hKbXb) (hKb_eq ▸ hx)
  have h4 : ∀ x ∈ Xb, ∃ k : ℕ, x ^ p ^ k ∈ Db := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_pow_mem_pCore_of_oTwoP_eq_top h ⟨x, hx⟩
    exact ⟨k, ⟨_, hk, by simp⟩⟩
  have hXbN : Xb ≤ Subgroup.normalizer (Db : Set (G ⧸ Y)) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Xb)
  have hDbX : Db ≤ Xb := CFSG.LieType.BorelTits.pCoreOf_le 2 Xb
  have hD2 : IsPGroup 2 Db := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Xb
  have hpi : PiNum p (Nat.card Kb) := by
    obtain ⟨m, hm⟩ := exists_relIndex_eq_prime_pow (p := p) hXbN h4
    have e1 := Subgroup.relIndex_mul_card Db Xb
    rw [inf_eq_left.mpr hDbX] at e1
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hD2
    have e2 : Xb.relIndex (T.map π ⊔ Xb) = Xb.relIndex (T.map π) :=
      B6.relIndex_sup_eq_of_le_normalizer (hTbK.trans hKbXb)
    obtain ⟨b, hb⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hTb2 Xb
    have hKb_eq' : Kb = T.map π ⊔ Xb := by rw [hKb_eq, sup_comm]
    have e4 : Xb.relIndex Kb = 2 ^ b := by rw [hKb_eq', e2, hb]
    have e3 := Subgroup.relIndex_mul_card Xb Kb
    rw [inf_eq_left.mpr hXbKb, e4] at e3
    rw [← e3, ← e1, hm, ha]
    exact (piNum_two_pow p b).mul ((piNum_prime_pow hp m).mul (piNum_two_pow p a))
  have hXbsolv : Group.IsSolvable Xb :=
    isSolvable_of_pow_mem (p := p) hDbX hXbN h4
      (hN := isSolvable_of_isPGroup_two hD2)
  have hKbsolv : Group.IsSolvable Kb :=
    isSolvable_of_pow_mem (p := 2) hXbKb hKbXb h3 (hN := hXbsolv)
  have hZ2 : IsTwoClosed (preO2 K Y) := ten_two hT hXH hK'
  have hZsolv : Group.IsSolvable (preO2 K Y) := isSolvable_of_isTwoClosed hZ2
  have hKYsolv : Group.IsSolvable (K ⊓ Y : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_preO2 K Y)) (Subgroup.inclusion_injective _)
  have hKsolv : Group.IsSolvable K := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : K ⊓ Y ≤ K))
      (π.subgroupMap K) ?_
    intro k hk
    have hk1 : π k = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    exact ⟨⟨k, k.2, (QuotientGroup.eq_one_iff _).mp hk1⟩, rfl⟩
  obtain ⟨K₀, hK₀K, hTK₀, hK₀pi, hK₀idx⟩ := exists_hall_two_p hp hTK hT2 hKsolv
  have hKK₀ : K ≤ K₀ ⊔ (K ⊓ Y) := by
    set L := K₀ ⊔ (K ⊓ Y) with hL
    have hLK : L ≤ K := sup_le hK₀K inf_le_left
    have d1 : L.relIndex K ∣ K₀.relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_left
    have d2 : L.relIndex K ∣ (K ⊓ Y).relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_right
    have e : (K ⊓ Y).relIndex K = Nat.card Kb := by
      rw [Subgroup.inf_relIndex_left]
      have := Subgroup.relIndex_ker (K := K) π
      rwa [QuotientGroup.ker_mk'] at this
    rw [e] at d2
    have hone : L.relIndex K = 1 := by
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have h1 := hK₀idx q hq (hqd.trans d1)
      have h2 := hpi q hq (hqd.trans d2)
      rcases h2 with h2 | h2
      · exact h1.1 h2
      · exact h1.2 h2
    exact (Subgroup.relIndex_eq_one.mp hone)
  have hK₀eq : K₀ = K := by
    refine hmin K₀ (hK₀K.trans hKle) hTK₀ ?_ hK₀K
    refine le_antisymm ?_ ?_
    · rw [hEq]
      exact sup_le (hKK₀.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right)))
        le_sup_right
    · exact sup_le (hK₀K.trans hKle) (le_sup_right.trans hEq.ge)
  have hKpi : PiNum p (Nat.card K) := by
    rw [← hK₀eq]
    exact hK₀pi
  obtain ⟨hPsyl, hKP, -⟩ := ten_two_core hT hXH hK'
  set Z := preO2 K Y with hZ
  set P := T ⊓ Z with hP
  set R := (K ⊓ X) ⊔ Z with hR
  have hZK : Z ≤ K := preO2_le K Y
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_preO2 K Y
  have hPZ : P ≤ Z := inf_le_right
  have hPK : P ≤ K := hPZ.trans hZK
  have hRK : R ≤ K := sup_le inf_le_left hZK
  have hZpi : PiNum p (Nat.card Z) := hKpi.of_dvd (Subgroup.card_dvd_of_le hZK)
  obtain ⟨b, hb⟩ : ∃ b : ℕ, P.relIndex Z = p ^ b := by
    have e := Subgroup.relIndex_mul_card P Z
    rw [inf_eq_left.mpr hPZ] at e
    have hdvd : P.relIndex Z ∣ Nat.card Z := Dvd.intro _ e
    have hpos : P.relIndex Z ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hodd : ¬ 2 ∣ P.relIndex Z := hPsyl.not_dvd_relIndex
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdd => ?_)⟩
    rcases (hZpi.of_dvd hdvd) d hd hdd with h2 | h2
    · exact absurd (h2 ▸ hdd) hodd
    · exact h2
  have h5 : Db ≤ pCoreOf 2 Kb :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hDbX.trans hXbKb)
      (hKbXb.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Xb))
      hD2
  have hA1 : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ P := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (K ⊓ X) Z
      (hZK.trans hKKX)] at hx
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    obtain ⟨k, hk⟩ := h4 (π a) (Subgroup.mem_map_of_mem _ ha)
    have haZ : a ^ p ^ k ∈ Z := by
      refine ⟨K.pow_mem ha.1 _, ?_⟩
      show π (a ^ p ^ k) ∈ pCoreOf 2 Kb
      rw [map_pow]
      exact h5 hk
    obtain ⟨z', hz', hz''⟩ := mul_pow_eq_of_mem_normalizer (O := Z) (hKZ ha.1) hz (p ^ k)
    have hxZ : (a * z) ^ p ^ k ∈ Z := by
      rw [hz'']
      exact Z.mul_mem haZ hz'
    have h6 := pow_relIndex_mem (P := P) (hZK.trans hKP) hxZ
    refine ⟨k + b, ?_⟩
    rw [hb] at h6
    rwa [pow_add, pow_mul]
  have hA2 : ∀ q ∈ K, ∃ k : ℕ, q ^ 2 ^ k ∈ R := by
    intro q hq
    obtain ⟨j, hj⟩ := exists_pow_mem_of_mem_sup hT2 (hTK.trans hKKX) (hK1 ▸ hq)
    exact ⟨j, Subgroup.mem_sup_left hj⟩
  have hRn : K ≤ Subgroup.normalizer (R : Set G) := le_normalizer_sup' hKKX hKZ
  exact ⟨R, rfl, hRK, hRn, le_sup_right, hA1, hA2⟩

theorem ten_three {T X Y K H : Subgroup G} [Y.Normal]
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hYX : Y ≤ X) (hXH : X ≤ H)
    (hT : IsSylowIn 2 T H) (hK : K ∈ sFamily T X Y) {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (h : oTwoP ↥((K ⊓ X).map (QuotientGroup.mk' Y)) p = ⊤) : oTwoPTwo ↥K p = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, -, hRK, hRn, -, hA1, hA2⟩ := ten_three_data hTX hYX hXH hT hK hp h
  obtain ⟨-, hKP, -⟩ := ten_two_core hT hXH hK
  have hT2 : IsPGroup 2 T := hT.isPGroup
  set P := T ⊓ preO2 K Y with hP
  have hPK : P ≤ K := inf_le_right.trans (preO2_le K Y)
  have hPn : (P.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
  have hRn' : (R.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr hRn
  have hP2 : IsPGroup 2 (P.subgroupOf K) :=
    (hT2.to_le (inf_le_left : P ≤ T)).of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  refine oTwoPTwo_eq_top_of_series (p := p) (N₂ := P.subgroupOf K) (N₂p := R.subgroupOf K) hP2
    (fun x hx => ?_) (fun q => ?_)
  · obtain ⟨k, hk⟩ := hA1 x (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
  · obtain ⟨k, hk⟩ := hA2 q q.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩

end Main

end E1

end CFSG.Quasithin
