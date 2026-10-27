module

public import CFSG.Quasithin.Vol2.Ch1Five
public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Star

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436

variable {G : Type} [Group G] [Finite G]

@[expose] def Step436KZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting436Sp4 G T M L n I H K t →
      ∃ KZ ∈ cComp (Subgroup.centralizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)),
        sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ

omit [Finite G] in
theorem centralizer_normal_normalizer (Z : Subgroup G) :
    ((Subgroup.centralizer (Z : Set G)).subgroupOf (Subgroup.normalizer (Z : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).2
    fun _ hg => A4.mem_normalizer_centralizer hg

omit [Finite G] in
theorem cComp_normalizer {Z KZ : Subgroup G} (hKZ : KZ ∈ cComp (Subgroup.centralizer (Z : Set G))) :
    KZ ∈ cComp (Subgroup.normalizer (Z : Set G)) :=
  cComp_mem_of_subnormal (A3.subnormal_of_normal (Subgroup.centralizer_le_normalizer _)
    (centralizer_normal_normalizer Z)) hKZ

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem four_le_two_pow : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) s.sk.base.hyp.two_le

theorem exists_odd_prime_dvd : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 := by
  have h4 := s.four_le_two_pow
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := s.sk.base.hyp.two_le; omega)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  omega

theorem exists_elt_Y₁ {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    ∃ y : G, y ∈ Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) ∧
      y ∉ Subgroup.centralizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) ∧
      orderOf y = p ∧ y ∈ Subgroup.normalizer (v432 T M L : Set G) ∧
      y ∈ Subgroup.normalizer (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) ∧
      (∀ k ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
        y * k * y⁻¹ * k⁻¹ ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)) ∧
      (∀ k ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
        y⁻¹ * k * y * k⁻¹ ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y₁, Y₂, hY₁N, hY₁P, -, hY₁c, hreg, hY₁K₂, -⟩ := s.concl.torus
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y₁) p (hY₁c ▸ hpn)
  have hyN : (y : G) ∈ Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) :=
    (hY₁N y.2).2
  refine ⟨y, hyN, fun hyc => ?_, by rw [Subgroup.orderOf_coe, hy], ?_, ?_,
    fun k hk => hY₁K₂ y y.2 k hk, fun k hk => by simpa using hY₁K₂ _ (inv_mem y.2) k hk⟩
  · obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp s.Z_ne_bot
    have hyz : (y : G) * z * (y : G)⁻¹ = z := by
      rw [← (Subgroup.mem_centralizer_iff.mp hyc) z hz, mul_inv_cancel_right]
    rcases hreg y y.2 z hz hyz with h | h
    · have : orderOf (y : G) = 1 := by rw [h, orderOf_one]
      rw [Subgroup.orderOf_coe, hy] at this
      exact hp.one_lt.ne' this
    · exact hz1 (Subtype.ext h)
  ·
    have h1 : H ⊓ M ⊓ K ≤ Subgroup.normalizer (perfectCore (H ⊓ M ⊓ K) : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
    have h2 := (h1.trans (normalizer_le_normalizer_pCoreOf 2 _)) (hY₁P y.2)
    rwa [← s.concl.V_eq] at h2
  · exact (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _))
      (hY₁N y.2)

theorem exists_elt_K₂ {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    ∃ a ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L), orderOf a = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y₁, Y₂, -, -, -, -, -, -, -, hY₂K, -, hY₂c, -⟩ := s.concl.torus
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y₂) p (hY₂c ▸ hpn)
  exact ⟨a, hY₂K a.2, by rw [Subgroup.orderOf_coe, ha]⟩

theorem dvd_card_modO2 {KZ : Subgroup G}
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) : p ∣ Nat.card (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haK, ha⟩ := s.exists_elt_K₂ hp hpn
  set a' : ↥KZ := ⟨a, hK₂ haK⟩ with ha'
  have ha'o : orderOf a' = p := by rw [← Subgroup.orderOf_coe, ha]
  set b : ↥KZ ⧸ CFSG.pCore 2 ↥KZ := QuotientGroup.mk a' with hb
  have hbp : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one (by
    rw [hb, ← QuotientGroup.mk_pow, ← ha'o, pow_orderOf_eq_one, QuotientGroup.mk_one])
  have hb1 : orderOf b ≠ 1 := by
    intro h1
    have hb1 : b = 1 := orderOf_eq_one_iff.mp h1
    have hmem : a' ∈ CFSG.pCore 2 ↥KZ := (QuotientGroup.eq_one_iff a').mp hb1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥KZ)) ⟨a', hmem⟩
    have hk' : a' ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := ha'o ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hbo : orderOf b = p := ((Nat.dvd_prime hp).mp hbp).resolve_left hb1
  exact hbo ▸ orderOf_dvd_natCard b

theorem KZ_normal (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : Lemma122A) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)))
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ) :
    (KZ.subgroupOf (Subgroup.normalizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))).Normal := by
  set Z := sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hZ
  have hyp := s.sk.base.hyp
  have hH : pCoreOf 2 (Subgroup.normalizer (Z : Set G)) ≠ ⊥ := s.inH_GZ.2
  have hKZ' := cComp_normalizer hKZ
  rcases lemma_1_2_1_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 hH hKZ' with h | ⟨h2, -⟩
  · exact h
  · exfalso
    obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
    obtain ⟨y, hyN, hyC, hyo, -⟩ := s.exists_elt_Y₁ hp hpn
    have hcl := h122 G hyp.simple hyp.qtke hyp.nonabelian _ KZ hH hKZ' p hp hp2 h2
      (s.dvd_card_modO2 hK₂ hp hp2 hpn)
    have hy : y ∈ Subgroup.closure {x : G | x ∈ Subgroup.normalizer (Z : Set G) ∧
        ∃ k : ℕ, orderOf x = p ^ k} := Subgroup.subset_closure ⟨hyN, 1, by rw [pow_one, hyo]⟩
    rw [hcl] at hy
    have hle : conjClosure KZ (Subgroup.normalizer (Z : Set G)) ≤
        Subgroup.centralizer (Z : Set G) := conjClosure_le fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer hg) k).mp
        (le_of_mem_cComp hKZ hk)
    exact hyC (hle hy)

theorem KZ_quasisimple (h36 : A36ForSQTK) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)))
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ) :
    CFSG.IsQuasisimple (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := by
  classical
  set P := H ⊓ M ⊓ K with hP
  set S := T ⊓ H ⊓ K with hS
  set V := v432 T M L with hV
  set Z := sp4Z P S V with hZ
  set K₂ := sp4K₂ K P S V with hK₂def
  set Q₁ := sp4Q₁ K P S V with hQ₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := s.sk.base.hyp
  have hH : pCoreOf 2 (Subgroup.normalizer (Z : Set G)) ≠ ⊥ := s.inH_GZ.2
  have hKZ' := cComp_normalizer hKZ
  have hstrong := lemma_1_2_1_four_strong hyp.qtke hyp.simple hyp.nonabelian h36 hH hKZ'
  obtain ⟨e⟩ := modO2_mulEquiv hKZ'
  have hqs : CFSG.IsQuasisimple ↥(modO2Image (Subgroup.normalizer (Z : Set G)) KZ) →
      CFSG.IsQuasisimple (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := fun h =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h
  have hcase : A36Case3 ↥(modO2Image (Subgroup.normalizer (Z : Set G)) KZ) ∨
      A36Case4 ↥(modO2Image (Subgroup.normalizer (Z : Set G)) KZ) → False := by
    intro h34
    obtain ⟨r, hr, h5, χ₀, -, hχ₀ker⟩ := exists_sl2_surjection_of_case34 h34
    have hr2 : r ≠ 2 := by omega
    have hFodd : Odd (Nat.card ↥χ₀.ker) := by
      rw [hχ₀ker, hstrong.2.1.1]
      exact A312.odd_card_oddCore _
    obtain ⟨ψ, -, hψker⟩ := exists_modO2_surjection hKZ'
    have hVKZ : V ≤ KZ := s.concl.V_le_K₂.trans hK₂
    let f : ↥V →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) :=
      χ₀.comp (ψ.comp (Subgroup.inclusion hVKZ))
    have hf2 : ∀ v : ↥V, f v ^ 2 = 1 := fun v => by
      rw [← map_pow]
      have : v ^ 2 = 1 := Subtype.ext (s.concl.V_sq v v.2)
      rw [this, map_one]
    have hker : ∀ v : ↥V, f v = 1 → (v : G) ∈ Q₁ := by
      intro v hv
      set w := ψ (Subgroup.inclusion hVKZ v) with hw
      have hwk : w ∈ χ₀.ker := hv
      have hw2 : w ^ 2 = 1 := by
        rw [hw, ← map_pow]
        have : Subgroup.inclusion hVKZ v ^ 2 = 1 := Subtype.ext (s.concl.V_sq v v.2)
        rw [this, map_one]
      have hwo : orderOf w = 1 := by
        have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
        have h2 : Odd (orderOf w) := Odd.of_dvd_nat hFodd (by
          have := Subgroup.orderOf_dvd_natCard χ₀.ker hwk
          exact this)
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at h2
          exact absurd h2 (by decide)
      have hw1 : Subgroup.inclusion hVKZ v ∈ ψ.ker := orderOf_eq_one_iff.mp hwo
      rw [hψker] at hw1
      have hvO : (v : G) ∈ pCoreOf 2 KZ := by
        exact ⟨_, hw1, rfl⟩
      have hle : K₂ ⊓ pCoreOf 2 KZ ≤ Q₁ := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
          ((pCoreOf_isPGroup 2 KZ).to_le inf_le_right)
        intro k hk
        exact mem_normalizer_inf (Subgroup.le_normalizer hk)
          (le_normalizer_pCoreOf 2 KZ (hK₂ hk))
      exact hle ⟨s.concl.V_le_K₂ v.2, hvO⟩
    have hrange : Nat.card ↥f.range ≤ 2 := by
      let Φ : ↥f.range → ↥({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))) := fun g =>
        ⟨(g : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)), by
          obtain ⟨v, hv⟩ := g.2
          by_cases h1 : (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) = 1
          · left
            rw [h1]
            rfl
          · right
            have hsq : (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) ^ 2 = 1 := by
              rw [← hv]
              exact hf2 v
            exact sl2_coe_eq_neg_one_of_sq hr hr2 _ hsq h1⟩
      have hΦ : Function.Injective Φ := by
        intro g g' h
        have h' : ((g : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
            Matrix (Fin 2) (Fin 2) (ZMod r)) = (g' : Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
          congrArg (fun x : ↥({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))) =>
            (x : Matrix (Fin 2) (Fin 2) (ZMod r))) h
        exact Subtype.ext (Subtype.ext h')
      calc Nat.card ↥f.range ≤ Nat.card ↥({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))) :=
            Nat.card_le_card_of_injective Φ hΦ
        _ = ({1, -1} : Set (Matrix (Fin 2) (Fin 2) (ZMod r))).ncard := Nat.card_coe_set_eq _
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    have hkerc : Nat.card ↥f.ker ≤ Nat.card ↥(V ⊓ Q₁) := by
      let ι : ↥f.ker → ↥(V ⊓ Q₁) := fun v => ⟨((v : ↥V) : G), (v : ↥V).2, hker v v.2⟩
      have hι : Function.Injective ι := by
        intro v v' h
        have h' : ((v : ↥V) : G) = ((v' : ↥V) : G) :=
          congrArg (fun x : ↥(V ⊓ Q₁) => (x : G)) h
        exact Subtype.ext (Subtype.ext h')
      exact Nat.card_le_card_of_injective ι hι
    have hcardV : Nat.card ↥V = Nat.card ↥f.range * Nat.card ↥f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have hidx := Subgroup.relIndex_mul_card (V ⊓ Q₁) V
    rw [s.concl.index_V, inf_right_comm, inf_idem] at hidx
    have hpos : 0 < Nat.card ↥(V ⊓ Q₁) := Nat.card_pos
    have h4 := s.four_le_two_pow
    have : 2 ^ n * Nat.card ↥(V ⊓ Q₁) ≤ 2 * Nat.card ↥(V ⊓ Q₁) := by
      calc 2 ^ n * Nat.card ↥(V ⊓ Q₁) = Nat.card ↥V := hidx
        _ = Nat.card ↥f.range * Nat.card ↥f.ker := hcardV
        _ ≤ 2 * Nat.card ↥(V ⊓ Q₁) := Nat.mul_le_mul hrange hkerc
    nlinarith
  rcases hstrong.1 with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact hqs hc.1
  · exact hqs hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

end Setting436Sp4

end CFSG.Quasithin.H13.Ch4
