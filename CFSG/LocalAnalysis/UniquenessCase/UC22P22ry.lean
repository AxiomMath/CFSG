module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)

section L2

variable {X : Type} [Group X] {n : ℕ}

theorem uc22p22r_L2_card [Finite X] (h : IsL2 X n) : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨-, F, _, _, hFcard, _, ⟨e⟩⟩ := uc22p22g_isL2_psl h
  rw [Nat.card_congr (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula, hFcard]

theorem uc22p22r_L2_card_normalizer [Finite X] (h : IsL2 X n) (U : Sylow 2 X) :
    Nat.card (normalizer ((U : Subgroup X) : Set X)) * (2 ^ n + 1) = Nat.card X := by
  obtain ⟨-, F, _, _, hFcard, _, ⟨e⟩⟩ := uc22p22g_isL2_psl h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' : Sylow 2 (CFSG.GorensteinWalter.PSL2 F) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective U with hU'
  have hN : (normalizer ((U : Subgroup X) : Set X)).map e.toMonoidHom =
      normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) : Set (CFSG.GorensteinWalter.PSL2 F)) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    rfl
  have hcard1 : Nat.card (normalizer ((U : Subgroup X) : Set X)) =
      Nat.card (normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) : Set (CFSG.GorensteinWalter.PSL2 F))) := by
    rw [← hN, Subgroup.card_map_of_injective e.injective]
  have hsyl : Nat.card (Sylow 2 (CFSG.GorensteinWalter.PSL2 F)) = 2 ^ n + 1 := by
    rw [← Nat.card_congr (CFSG.GorensteinWalter.psl2ProjectiveLineEquivSylow F hFcard),
      CFSG.GorensteinWalter.PSL2ProjectiveLine, Projectivization.card_of_finrank_two _ _ (by simp), hFcard]
  have h3 : (normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) :
      Set (CFSG.GorensteinWalter.PSL2 F))).index = 2 ^ n + 1 := by
    rw [← hsyl, U'.card_eq_index_normalizer]
    rfl
  rw [hcard1, ← h3, mul_comm, Subgroup.index_mul_card, Nat.card_congr e.toEquiv]

theorem uc22p22r_dvd_succ {p : ℕ} (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : p ∣ 2 ^ n + 1 := by
  have h1 : (p : ℤ) ∣ -1 - 2 ^ n := Int.modEq_iff_dvd.1 hpn
  have h2 : (p : ℤ) ∣ ((2 ^ n + 1 : ℕ) : ℤ) := by
    have : ((2 ^ n + 1 : ℕ) : ℤ) = -(-1 - 2 ^ n) := by push_cast; ring
    rw [this]
    exact h1.neg_right
  exact Int.natCast_dvd_natCast.1 h2

theorem uc22p22r_L2_exists_orderOf [Finite X] (h : IsL2 X n) {p : ℕ} (hp : p.Prime)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : ∃ x : X, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  have hdvd : p ∣ Nat.card X := by
    rw [uc22p22r_L2_card h, h2]
    exact ((uc22p22r_dvd_succ hpn).mul_right _).mul_left _
  exact exists_prime_orderOf_dvd_card' p hdvd

theorem uc22p22r_L2_pElt_normalizer [Finite X] (h : IsL2 X n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (U : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((U : Subgroup X) : Set X)) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x = 1 := by
  have h1 := uc22p22r_L2_card_normalizer h U
  rw [uc22p22r_L2_card h] at h1
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  have hN : Nat.card (normalizer ((U : Subgroup X) : Set X)) = 2 ^ n * (2 ^ n - 1) := by
    rw [h2] at h1
    have h3 : (2 ^ n + 1) * Nat.card (normalizer ((U : Subgroup X) : Set X)) =
        (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1)) := by
      rw [mul_comm, h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  have hord : orderOf (⟨x, hx⟩ : normalizer ((U : Subgroup X) : Set X)) ∣ 2 ^ n * (2 ^ n - 1) :=
    hN ▸ orderOf_dvd_natCard _
  have hpk : orderOf (⟨x, hx⟩ : normalizer ((U : Subgroup X) : Set X)) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxk))
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hpk
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hjeq
    exact congrArg Subtype.val hjeq
  · exfalso
    have hpd : p ∣ 2 ^ n * (2 ^ n - 1) := (dvd_pow_self p (Nat.succ_ne_zero j)).trans (hjeq ▸ hord)
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h3 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
    · exact uc22p22g_not_dvd_pred hp hp2 hpn h3

end L2

section Pair

variable {G : Type} [Group G] {K L : Subgroup G}

theorem uc22p22r_le_normalizer_of_comm [Finite G] (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) :
    K ≤ normalizer (L : Set G) := by
  intro a ha
  apply Subgroup.mem_normalizer_fintype
  intro b hb
  rw [hcomm a ha b hb, mul_inv_cancel_right]
  exact hb

theorem uc22p22r_mem_sup_iff [Finite G] (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) {x : G} :
    x ∈ K ⊔ L ↔ ∃ a ∈ K, ∃ b ∈ L, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K L
    (uc22p22r_le_normalizer_of_comm hcomm), Set.mem_mul]
  rfl

theorem uc22p22r_mem_of_comm_left [Finite G] (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hZ : Subgroup.center ↥K = ⊥) {y : G} (hy : y ∈ K ⊔ L) (hyc : ∀ k ∈ K, y * k = k * y) : y ∈ L := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (uc22p22r_mem_sup_iff hcomm).1 hy
  have haZ : (⟨a, ha⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : G) * a = a * k
    have h1 := hyc k k.2
    have h2 := hcomm k k.2 b hb
    calc (k : G) * a = k * a * b * b⁻¹ := by group
      _ = a * b * k * b⁻¹ := by rw [mul_assoc (k : G) a b, ← h1]
      _ = a * (b * k) * b⁻¹ := by group
      _ = a * (k * b) * b⁻¹ := by rw [h2]
      _ = a * k := by group
  rw [hZ, Subgroup.mem_bot] at haZ
  have ha1 : a = 1 := congrArg Subtype.val haZ
  rw [ha1, one_mul]
  exact hb

theorem uc22p22r_inf_eq_bot_of_comm (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hZ : Subgroup.center ↥K = ⊥) : K ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxL⟩
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x hxL)
  rw [hZ, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem uc22p22r_sup_le_normalizer_left [Finite G] (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) :
    K ⊔ L ≤ normalizer (K : Set G) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (uc22p22r_mem_sup_iff hcomm).1 hx
  apply Subgroup.mem_normalizer_fintype
  intro k hk
  have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
    have h1 := hcomm k hk b hb
    calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
      _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = a * k * a⁻¹ := by group
  rw [e]
  exact K.mul_mem (K.mul_mem ha hk) (K.inv_mem ha)

theorem uc22p22r_inf_centralizer_eq_bot [Finite G] (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hZK : Subgroup.center ↥K = ⊥) (hZL : Subgroup.center ↥L = ⊥) :
    (K ⊔ L) ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzX, hzC⟩
  have hzc : ∀ y ∈ K ⊔ L, y * z = z * y := fun y hy => (Subgroup.mem_centralizer_iff.1 hzC) y hy
  have hzL : z ∈ L :=
    uc22p22r_mem_of_comm_left hcomm hZK hzX fun k hk => (hzc k (le_sup_left (a := K) hk)).symm
  have h1 : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hzc y (le_sup_right (b := L) y.2))
  rw [hZL, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem uc22p22r_conj_eq_or [Finite G] (hKs : IsSimpleGroup ↥K) (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hZ : Subgroup.center ↥K = ⊥) (hcard : Nat.card L = Nat.card K) (hXn : (K ⊔ L).Normal) (g : G) :
    K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = L := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'card : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKX : ∀ x ∈ K ⊔ L, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.1 (uc22p22r_sup_le_normalizer_left hcomm hx) k).1 hk
  have hK'X : K' ≤ K ⊔ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact hXn.conj_mem k (le_sup_left (b := L) hk) g
  have hK'n : ∀ x ∈ K ⊔ L, ∀ y ∈ K', x * y * x⁻¹ ∈ K' := by
    rintro x hx _ ⟨k, hk, rfl⟩
    have hx' : g⁻¹ * x * g ∈ K ⊔ L := by
      have := hXn.conj_mem x hx g⁻¹
      simpa using this
    refine ⟨g⁻¹ * x * g * k * (g⁻¹ * x * g)⁻¹, hKX _ hx' k hk, ?_⟩
    show g * (g⁻¹ * x * g * k * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * k * g⁻¹) * x⁻¹
    group
  haveI := hKs
  haveI hN : ((K' ⊓ K).subgroupOf K).Normal := by
    constructor
    intro y hy k
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact ⟨hK'n _ (le_sup_left (b := L) k.2) _ hy.1, K.mul_mem (K.mul_mem k.2 hy.2) (K.inv_mem k.2)⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top ((K' ⊓ K).subgroupOf K) with h | h
  · right
    have hc : ∀ y ∈ K', ∀ k ∈ K, y * k = k * y := by
      intro y hy k hk
      have h1 : y * k * y⁻¹ * k⁻¹ ∈ K' ⊓ K := by
        refine ⟨?_, K.mul_mem (hKX y (hK'X hy) k hk) (K.inv_mem hk)⟩
        have h2 : k * y⁻¹ * k⁻¹ ∈ K' := hK'n k (le_sup_left (b := L) hk) _ (K'.inv_mem hy)
        have e : y * k * y⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by group
        rw [e]
        exact K'.mul_mem hy h2
      have h2 : (⟨_, h1.2⟩ : ↥K) ∈ (K' ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.2 h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : y * k * y⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h2
      calc y * k = y * k * y⁻¹ * k⁻¹ * (k * y) := by group
        _ = k * y := by rw [h3, one_mul]
    have hle : K' ≤ L := fun y hy => uc22p22r_mem_of_comm_left hcomm hZ (hK'X hy) (hc y hy)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hK'card])
  · left
    have hle : K ≤ K' := by
      intro k hk
      have h1 : (⟨k, hk⟩ : ↥K) ∈ (K' ⊓ K).subgroupOf K := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 h1).1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hK'card])).symm

end Pair

section PElements

variable {G : Type} [Group G] {p : ℕ}

theorem uc22p22r_pElementSubgroup_normal :
    (CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup G)).Normal := by
  constructor
  intro x hx g
  have h1 : (CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤
      CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨y, ⟨-, k, hk⟩, rfl⟩
    refine ⟨Subgroup.mem_top _, k, ?_⟩
    show orderOf (MulAut.conj g y) = p ^ k
    rw [MulEquiv.orderOf_eq, hk]
  exact h1 ⟨x, hx, rfl⟩

theorem uc22p22r_le_pElementSubgroup {K : Subgroup G} (hKs : IsSimpleGroup ↥K) {z : G} (hzK : z ∈ K)
    (hzo : orderOf z = p) (hz1 : z ≠ 1) : K ≤ CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
  set P := CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup G) with hP
  haveI : P.Normal := uc22p22r_pElementSubgroup_normal
  haveI := hKs
  have hzP : z ∈ P := Subgroup.subset_closure ⟨Subgroup.mem_top z, 1, by rw [hzo, pow_one]⟩
  haveI hN : (P.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  rcases Subgroup.Normal.eq_bot_or_eq_top (P.subgroupOf K) with h | h
  · exfalso
    have h1 : (⟨z, hzK⟩ : ↥K) ∈ P.subgroupOf K := Subgroup.mem_subgroupOf.2 hzP
    rw [h, Subgroup.mem_bot] at h1
    exact hz1 (congrArg Subtype.val h1)
  · intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) ∈ P.subgroupOf K := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1

theorem uc22p22r_exists_pElt_not_mem {X : Subgroup G}
    (hX : X ≤ CFSG.RankThree.PartOne.pElementSubgroup p ⊤)
    (hne : X ≠ CFSG.RankThree.PartOne.pElementSubgroup p ⊤) :
    ∃ y : G, y ∉ X ∧ ∃ k : ℕ, orderOf y = p ^ k := by
  by_contra hcon
  apply hne
  refine le_antisymm hX ?_
  unfold CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.closure_le]
  rintro y ⟨-, k, hk⟩
  by_contra hy
  exact hcon ⟨y, hy, k, hk⟩

theorem uc22p22r_mem_of_pElt [Finite G] {X : Subgroup G} (hZ : X ⊓ centralizer (X : Set G) = ⊥)
    (hF1 : ∀ c ∈ centralizer (X : Set G), (∃ k : ℕ, c ^ (p ^ k) = 1) → c = 1)
    {x : G} (hx : x ∈ X ⊔ centralizer (X : Set G)) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x ∈ X := by
  have hle : centralizer (X : Set G) ≤ normalizer (X : Set G) := by
    intro c hc
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have h1 : y * c = c * y := Subgroup.mem_centralizer_iff.1 hc y hy
    rw [← h1, mul_inv_cancel_right]
    exact hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X _ hle, Set.mem_mul] at hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hx
  have hac : Commute a c := Subgroup.mem_centralizer_iff.1 hc a ha
  have h1 : a ^ (p ^ k) * c ^ (p ^ k) = 1 := by rw [← hac.mul_pow]; exact hxk
  have h2 : c ^ (p ^ k) ∈ X ⊓ centralizer (X : Set G) := by
    refine ⟨?_, Subgroup.pow_mem _ hc _⟩
    rw [eq_inv_of_mul_eq_one_right h1]
    exact X.inv_mem (X.pow_mem ha _)
  rw [hZ, Subgroup.mem_bot] at h2
  rw [hF1 c hc ⟨k, h2⟩, mul_one]
  exact ha

variable {n : ℕ}

theorem uc22p22r_eq_one_of_norm_sylow [Finite G] {K : Subgroup G} (hK : IsL2 ↥K n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    {a : G} (haK : a ∈ K) (haP : ∀ y ∈ P, a * y * a⁻¹ ∈ P) (hap : a ^ p = 1) : a = 1 := by
  obtain ⟨U, hU⟩ := hP
  have hmemU : ∀ y : ↥K, y ∈ (U : Subgroup ↥K) ↔ (y : G) ∈ P := by
    intro y
    rw [← hU]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'
  have hn : (⟨a, haK⟩ : ↥K) ∈ normalizer ((U : Subgroup ↥K) : Set ↥K) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    rw [SetLike.mem_coe, hmemU] at hy ⊢
    exact haP _ hy
  have h1 := uc22p22r_L2_pElt_normalizer hK hp hp2 hpn U hn (k := 1) (Subtype.ext (by simpa using hap))
  exact congrArg Subtype.val h1

theorem uc22p22r_eq_one_of_pElt_normalizer [Finite G] {K L : Subgroup G}
    (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) (hK : IsL2 ↥K n) (hL : IsL2 ↥L n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) {S : Subgroup G} (hSK : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K)
    (hSL : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ L) L) {x : G} (hxX : x ∈ K ⊔ L)
    (hxS : x ∈ normalizer (S : Set G)) (hxp : x ^ p = 1) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (uc22p22r_mem_sup_iff hcomm).1 hxX
  have hab : Commute a b := hcomm a ha b hb
  have hKL : K ⊓ L = ⊥ := uc22p22r_inf_eq_bot_of_comm hcomm (uc22p22g_center_bot hK)
  have h1 : a ^ p * b ^ p = 1 := by rw [← hab.mul_pow]; exact hxp
  have hap : a ^ p = 1 := by
    have h3 : a ^ p ∈ K ⊓ L := by
      refine ⟨K.pow_mem ha p, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact L.inv_mem (L.pow_mem hb p)
    rw [hKL, Subgroup.mem_bot] at h3
    exact h3
  have hbp : b ^ p = 1 := by
    rw [hap, one_mul] at h1
    exact h1
  have hxK : ∀ y ∈ K, a * b * y * (a * b)⁻¹ = a * y * a⁻¹ := fun y hy => by
    have h2 := hcomm y hy b hb
    calc a * b * y * (a * b)⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ := by group
      _ = a * (y * b) * b⁻¹ * a⁻¹ := by rw [h2]
      _ = a * y * a⁻¹ := by group
  have hxL : ∀ y ∈ L, a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := fun y hy => by
    have h2 := hcomm a ha (b * y * b⁻¹) (L.mul_mem (L.mul_mem hb hy) (L.inv_mem hb))
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = b * y * b⁻¹ * a * a⁻¹ := by rw [h2]
      _ = b * y * b⁻¹ := by group
  have ha1 : a = 1 := by
    refine uc22p22r_eq_one_of_norm_sylow hK hp hp2 hpn hSK ha (fun y hy => ?_) hap
    refine ⟨?_, K.mul_mem (K.mul_mem ha hy.2) (K.inv_mem ha)⟩
    rw [← hxK y hy.2]
    exact (Subgroup.mem_normalizer_iff.1 hxS y).1 hy.1
  have hb1 : b = 1 := by
    refine uc22p22r_eq_one_of_norm_sylow hL hp hp2 hpn hSL hb (fun y hy => ?_) hbp
    refine ⟨?_, L.mul_mem (L.mul_mem hb hy.2) (L.inv_mem hb)⟩
    rw [← hxL y hy.2]
    exact (Subgroup.mem_normalizer_iff.1 hxS y).1 hy.1
  rw [ha1, hb1, one_mul]

end PElements

section Tools

variable {G : Type} [Group G]

theorem uc22p22r_map_conj_mul (K : Subgroup G) (g h : G) :
    K.map (MulAut.conj (g * h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem uc22p22r_map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

theorem uc22p22r_inv_mul_mem_normalizer {K L : Subgroup G}
    (hconj : ∀ g : G, K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = L)
    {g h : G} (hg : g ∉ normalizer (K : Set G)) (hh : h ∉ normalizer (K : Set G)) :
    g⁻¹ * h ∈ normalizer (K : Set G) := by
  have hgL : K.map (MulAut.conj g).toMonoidHom = L :=
    (hconj g).resolve_left fun h' => hg (Subgroup.mem_normalizer_iff_map_conj_eq.2 h')
  have hhL : K.map (MulAut.conj h).toMonoidHom = L :=
    (hconj h).resolve_left fun h' => hh (Subgroup.mem_normalizer_iff_map_conj_eq.2 h')
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show K.map (MulAut.conj (g⁻¹ * h)).toMonoidHom = K
  rw [uc22p22r_map_conj_mul, hhL, ← hgL, ← uc22p22r_map_conj_mul, inv_mul_cancel, uc22p22r_map_conj_one]

theorem uc22p22r_normalizer_normal {K L : Subgroup G}
    (hconj : ∀ g : G, K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = L) :
    (normalizer (K : Set G)).Normal := by
  constructor
  intro h hh g
  by_cases hg : g ∈ normalizer (K : Set G)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg)
  · have hgh : g * h ∉ normalizer (K : Set G) := fun h' => hg (by
      have := Subgroup.mul_mem _ h' (Subgroup.inv_mem _ hh)
      rwa [mul_inv_cancel_right] at this)
    have h1 := uc22p22r_inv_mul_mem_normalizer hconj (g := (g * h)⁻¹) (h := g⁻¹)
      (fun h' => hgh (by simpa using Subgroup.inv_mem _ h')) (fun h' => hg (by simpa using Subgroup.inv_mem _ h'))
    rwa [inv_inv] at h1

theorem uc22p22r_comm_inner {n : ℕ} {K : Subgroup G} (hK : IsL2 ↥K n) {g h : G}
    (hg : g ∈ normalizer (K : Set G)) (hh : h ∈ normalizer (K : Set G)) :
    ∃ k ∈ K, ∀ x ∈ K, g * h * g⁻¹ * h⁻¹ * x * (g * h * g⁻¹ * h⁻¹)⁻¹ = k * x * k⁻¹ := by
  set φ := K.normalizerMonoidHom with hφ
  have hcomm := uc22p22g_outer_comm hK (QuotientGroup.mk (φ ⟨g, hg⟩)) (QuotientGroup.mk (φ ⟨h, hh⟩))
  have hmem : φ (⟨g, hg⟩ * ⟨h, hh⟩ * ⟨g, hg⟩⁻¹ * ⟨h, hh⟩⁻¹) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
    rw [← QuotientGroup.eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
    group
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h2 := congrArg (fun σ : MulAut ↥K => ((σ ⟨x, hx⟩ : ↥K) : G)) hk
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [h2]
  simp [φ]
  group

theorem uc22p22r_mem_of_inner [Finite G] {K L : Subgroup G} (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    {c k l : G} (hk : k ∈ K) (hl : l ∈ L) (hkx : ∀ x ∈ K, c * x * c⁻¹ = k * x * k⁻¹)
    (hlx : ∀ x ∈ L, c * x * c⁻¹ = l * x * l⁻¹) :
    c ∈ (K ⊔ L) ⊔ centralizer ((K ⊔ L : Subgroup G) : Set G) := by
  have hdK : ∀ x ∈ K, x * (l⁻¹ * k⁻¹ * c) = l⁻¹ * k⁻¹ * c * x := by
    intro x hx
    have h1 : c * x = k * x * k⁻¹ * c := by
      calc c * x = c * x * c⁻¹ * c := by group
        _ = k * x * k⁻¹ * c := by rw [hkx x hx]
    have h2 : l⁻¹ * x = x * l⁻¹ := by
      have h3 := hcomm x hx l hl
      calc l⁻¹ * x = l⁻¹ * (x * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * x) * l⁻¹ := by rw [h3]
        _ = x * l⁻¹ := by group
    calc x * (l⁻¹ * k⁻¹ * c) = x * l⁻¹ * k⁻¹ * c := by group
      _ = l⁻¹ * x * k⁻¹ * c := by rw [h2]
      _ = l⁻¹ * k⁻¹ * (k * x * k⁻¹ * c) := by group
      _ = l⁻¹ * k⁻¹ * (c * x) := by rw [h1]
      _ = l⁻¹ * k⁻¹ * c * x := by group
  have hdL : ∀ x ∈ L, x * (l⁻¹ * k⁻¹ * c) = l⁻¹ * k⁻¹ * c * x := by
    intro x hx
    have h1 : c * x = l * x * l⁻¹ * c := by
      calc c * x = c * x * c⁻¹ * c := by group
        _ = l * x * l⁻¹ * c := by rw [hlx x hx]
    have hy : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    have h2 : k⁻¹ * (l * x * l⁻¹) = l * x * l⁻¹ * k⁻¹ := by
      have h3 := hcomm k hk _ hy
      calc k⁻¹ * (l * x * l⁻¹) = k⁻¹ * (l * x * l⁻¹ * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * (l * x * l⁻¹)) * k⁻¹ := by rw [h3]
        _ = l * x * l⁻¹ * k⁻¹ := by group
    calc x * (l⁻¹ * k⁻¹ * c) = l⁻¹ * (l * x * l⁻¹ * k⁻¹) * c := by group
      _ = l⁻¹ * (k⁻¹ * (l * x * l⁻¹)) * c := by rw [h2]
      _ = l⁻¹ * k⁻¹ * (l * x * l⁻¹ * c) := by group
      _ = l⁻¹ * k⁻¹ * (c * x) := by rw [h1]
      _ = l⁻¹ * k⁻¹ * c * x := by group
  have hdC : l⁻¹ * k⁻¹ * c ∈ centralizer ((K ⊔ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (uc22p22r_mem_sup_iff hcomm).1 hx
    rw [mul_assoc, hdL b hb, ← mul_assoc, hdK a ha, mul_assoc]
  have e : c = k * l * (l⁻¹ * k⁻¹ * c) := by group
  rw [e]
  exact Subgroup.mul_mem _ (le_sup_left (b := centralizer ((K ⊔ L : Subgroup G) : Set G))
    (Subgroup.mul_mem _ (le_sup_left (b := L) hk) (le_sup_right (a := K) hl))) (le_sup_right (a := K ⊔ L) hdC)

theorem uc22p22r_eigen {Q : Type} [Group Q] (hQ : ∀ x y : Q, x * y = y * x) {p : ℕ} (hp : p.Prime)
    (τ : MulAut Q) (hτ : ∀ x, τ (τ x) = x) {a : Q} (ha : orderOf a = p) :
    ∃ b : Q, orderOf b = p ∧ (τ b = b ∨ τ b = b⁻¹) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h : τ a * a = 1
  · exact ⟨a, ha, Or.inr (eq_inv_of_mul_eq_one_left h)⟩
  · refine ⟨τ a * a, orderOf_eq_prime ?_ h, Or.inl ?_⟩
    · have hc : Commute (τ a) a := hQ _ _
      rw [hc.mul_pow, ← map_pow, ← ha, pow_orderOf_eq_one, map_one, one_mul]
    · rw [map_mul, hτ, hQ]

end Tools

section Lifts

variable {G : Type} [Group G]

theorem uc22p22r_card_comap_mk (N : Subgroup G) [N.Normal] (E : Subgroup (G ⧸ N)) :
    Nat.card ↥(E.comap (QuotientGroup.mk' N)) = Nat.card ↥N * Nat.card ↥E :=
  QuotientGroup.card_preimage_mk N E

theorem uc22p22r_exists_invariant_lift [Finite G] {T S N : Subgroup G} (hT2 : IsPGroup 2 T) (hSN : S ≤ N)
    (hTN : T ≤ normalizer (N : Set G)) (hTS : T ≤ normalizer (S : Set G)) [hn : (S.subgroupOf N).Normal]
    (hodd : ¬ 2 ∣ Nat.card (↥N ⧸ S.subgroupOf N)) {p : ℕ} (hp : p.Prime) :
    ∃ P : Subgroup G, S ≤ P ∧ P ≤ N ∧ T ≤ normalizer (P : Set G) ∧
      Nat.card P = Nat.card S * p ^ (Nat.card (↥N ⧸ S.subgroupOf N)).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ₀ : ↥T →* MulAut ↥N := N.normalizerMonoidHom.comp (Subgroup.inclusion hTN)
  have hρ₀ : ∀ (t : ↥T) (x : ↥N), ((ρ₀ t x : ↥N) : G) = (t : G) * x * (t : G)⁻¹ := by
    intro t x
    simp [ρ₀]
  have hρ₀S : ∀ t : ↥T, (S.subgroupOf N).map (ρ₀ t).toMonoidHom = S.subgroupOf N := by
    intro t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ S := hy
      show ((ρ₀ t y : ↥N) : G) ∈ S
      rw [hρ₀]
      exact (Subgroup.mem_normalizer_iff.1 (hTS t.2) _).1 hy'
    · intro hx
      have hx' : (x : G) ∈ S := hx
      refine ⟨(ρ₀ t)⁻¹ x, ?_, by simp⟩
      show (((ρ₀ t)⁻¹ x : ↥N) : G) ∈ S
      have h1 : ((ρ₀ t⁻¹ x : ↥N) : G) = (t : G)⁻¹ * x * (t : G) := by
        rw [hρ₀]
        simp
      have h2 : (ρ₀ t)⁻¹ x = ρ₀ t⁻¹ x := by rw [map_inv]
      rw [h2, h1]
      have := (Subgroup.mem_normalizer_iff.1 (hTS (T.inv_mem t.2)) _).1 hx'
      simpa using this
  let θ : ↥T →* MulAut (↥N ⧸ S.subgroupOf N) := quotAutHom (S.subgroupOf N) ρ₀ hρ₀S
  have hθ : ∀ (t : ↥T) (x : ↥N), θ t (QuotientGroup.mk x) = QuotientGroup.mk (ρ₀ t x) :=
    fun t x => quotAutHom_mk _ _ _ t x
  obtain ⟨Ps, hPs⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 2 p hT2 hodd θ
  set q₀ : ↥N →* ↥N ⧸ S.subgroupOf N := QuotientGroup.mk' (S.subgroupOf N) with hq₀
  set Bt : Subgroup ↥N := (Ps : Subgroup (↥N ⧸ S.subgroupOf N)).comap q₀ with hBt
  refine ⟨Bt.map N.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro s hs
    refine ⟨⟨s, hSN hs⟩, ?_, rfl⟩
    show q₀ ⟨s, hSN hs⟩ ∈ (Ps : Subgroup (↥N ⧸ S.subgroupOf N))
    rw [hq₀, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (by exact hs)]
    exact Subgroup.one_mem _
  · intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨ρ₀ ⟨t, ht⟩ β, ?_, hρ₀ ⟨t, ht⟩ β⟩
    show q₀ (ρ₀ ⟨t, ht⟩ β) ∈ (Ps : Subgroup (↥N ⧸ S.subgroupOf N))
    rw [hq₀, QuotientGroup.mk'_apply, ← hθ, ← hPs ⟨t, ht⟩]
    exact ⟨_, hβ, rfl⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hBt, hq₀, uc22p22r_card_comap_mk,
      Ps.card_eq_multiplicity, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]

end Lifts

section Fixed

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_fixSub_inv {A : Subgroup H} {g : H} (hg : g ∈ normalizer (A : Set H)) {w : Vmod}
    (hw : w ∈ fixSub ρ A) : ρ g w ∈ fixSub ρ A := by
  intro a ha
  have h1 : g⁻¹ * a * g ∈ A := (Subgroup.mem_normalizer_iff''.1 hg a).1 ha
  have e : a * g = g * (g⁻¹ * a * g) := by group
  calc ρ a (ρ g w) = ρ (a * g) w := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * (g⁻¹ * a * g)) w := by rw [e]
    _ = ρ g (ρ (g⁻¹ * a * g) w) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g w := by rw [hw _ h1]

theorem uc22p22r_exists_fixed_ne_zero [Finite Vmod] {p : ℕ} (hp : p.Prime) {P : Subgroup H} (hP : IsPGroup p P)
    {Z : Submodule (ZMod 2) Vmod} (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ P Z) (hZ1 : ¬ Nat.card ↥Z ≡ 1 [MOD p]) :
    ∃ w ∈ Z, w ≠ 0 ∧ ∀ g ∈ P, ρ g w = w := by
  haveI : Fact p.Prime := ⟨hp⟩
  let _ : MulAction ↥P ↥Z :=
    { smul := fun g z => ⟨ρ g z, hZ g g.2 z z.2⟩
      one_smul := fun z => Subtype.ext (by
        show ρ ((1 : ↥P) : H) z = z
        rw [Subgroup.coe_one, map_one, Module.End.one_apply])
      mul_smul := fun g g' z => Subtype.ext (by
        show ρ ((g * g' : ↥P) : H) z = ρ g (ρ g' z)
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) }
  have hcongr := hP.card_modEq_card_fixedPoints ↥Z
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints ↥P ↥Z = {0} := by
    ext v
    constructor
    · intro hv
      by_contra hv0
      have hv0' : (v : Vmod) ≠ 0 := fun h => hv0 (Subtype.ext h)
      obtain ⟨g, hg, hgv⟩ := hcon v v.2 hv0'
      exact hgv (congrArg Subtype.val (hv ⟨g, hg⟩))
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      intro g
      exact Subtype.ext (map_zero (ρ g))
  have h1 : Nat.card ↑({0} : Set ↥Z) = 1 := Nat.card_unique
  rw [hfix, h1] at hcongr
  exact hZ1 hcongr

end Fixed

end CFSG.LocalAnalysis.UniquenessCase.UC22
