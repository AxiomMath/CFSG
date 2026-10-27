module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] noncomputable def Step148PointHJd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
      ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
        d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → b ∈ Subgroup.closure {b', d} →
        Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer
            ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) →
        (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
        (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
            CFSG.Blueprint.NativeSporadic.ON ∨
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
          IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
        Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

namespace Item148HJ

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_subgroupOf {C X : Subgroup G} (g : ↥C)
    (hg : (g : G) ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hg y

theorem exists_commute_of_commutator_mem {u : G} (hu : u ^ 3 = 1) {M K : Subgroup G}
    (hKM : K ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (hK3 : ¬ 3 ∣ Nat.card K) {m : G} (hm : m ∈ M) (hmu : ⁅m, u⁆ ∈ K) :
    ∃ c ∈ M, c * u = u * c ∧ c⁻¹ * m ∈ K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G₁ := M ⊔ Subgroup.zpowers u with hG₁
  have hMG : M ≤ G₁ := le_sup_left
  have huG : u ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hKG : K ≤ G₁ := hKM.trans hMG
  have hG₁K : G₁ ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hMK (Subgroup.zpowers_le.mpr huK)
  set N := K.subgroupOf G₁ with hNdef
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hG₁K
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rwa [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv]
  set u₁ : ↥G₁ := ⟨u, huG⟩ with hu₁
  have hu₁3 : u₁ ^ 3 = 1 := Subtype.ext (by simpa using hu)
  have hPp : IsPGroup 3 (Subgroup.zpowers u₁) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hu₁3, one_zpow, OneMemClass.coe_one]
  have key := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hN3
    (Subgroup.zpowers u₁) hPp
  set m₁ : ↥G₁ := ⟨m, hMG hm⟩ with hm₁def
  have hcomm : QuotientGroup.mk' N m₁ * QuotientGroup.mk' N u₁ =
      QuotientGroup.mk' N u₁ * QuotientGroup.mk' N m₁ := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hmu
  have hm₁ : QuotientGroup.mk' N m₁ ∈ Subgroup.centralizer
      (((Subgroup.zpowers u₁).map (QuotientGroup.mk' N) : Subgroup (↥G₁ ⧸ N)) :
        Set (↥G₁ ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [map_zpow]
    exact Commute.zpow_left hcomm.symm k
  rw [← key] at hm₁
  obtain ⟨c₁, hc₁, hc₁m⟩ := hm₁
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hNdef,
    Subgroup.mem_subgroupOf] at hc₁m
  have hcK : (c₁ : G)⁻¹ * m ∈ K := by simpa using hc₁m
  refine ⟨c₁, ?_, ?_, hcK⟩
  · have hc : (c₁ : G) = m * ((c₁ : G)⁻¹ * m)⁻¹ := by group
    rw [hc]
    exact mul_mem hm (inv_mem (hKM hcK))
  · have h := Subgroup.mem_centralizer_iff.mp hc₁ u₁ (Subgroup.mem_zpowers u₁)
    exact (congrArg Subtype.val h).symm

theorem sup_zpowers_eq_of_isHyperplane {A B : Subgroup G} (hB : IsHyperplane A B) {u : G}
    (huA : u ∈ A) (huB : u ∉ B) : B ⊔ Subgroup.zpowers u = A := by
  have hle : B ⊔ Subgroup.zpowers u ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr huA)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers u)
  have h2 := Subgroup.card_dvd_of_le hle
  rw [hk, hB.2, mul_comm 3] at h2
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos h2
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · exfalso
    rw [mul_one] at hk
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers u) hk.le
    have hu : u ∈ B ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    rw [← heq] at hu
    exact huB hu
  · refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hk, hB.2, mul_comm]

omit [Finite G] in
theorem le_of_eq_commutator_of_sup {A B N J Q : Subgroup G} {u : G}
    (hAB : B ⊔ Subgroup.zpowers u = A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (huA : u ∈ A) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) (hJu : J ≤ Subgroup.centralizer ({u} : Set G))
    (hQB : Q ≤ Subgroup.centralizer (B : Set G)) (hQ : Q ≤ N ⊔ J) (hQA : Q = ⁅Q, A⁆) :
    Q ≤ N := by
  have hBA : B ≤ A := hAB ▸ le_sup_left
  have hZB : Subgroup.zpowers u ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hAab u huA x (hBA hx), mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have h1 : u⁻¹ * (u * x * u⁻¹) * u = u * x * u⁻¹ := by
        rw [mul_assoc, hAab _ (hBA hx) u huA, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : x = u⁻¹ * (u * x * u⁻¹) * u := by group
      rw [h2, h1]
      exact hx
  have hZN : Subgroup.zpowers u ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (hAN huA)
  have hJZ : J ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers148]
    exact hJu
  have hc := commutator_sup_le148 hZN hJN hJZ
  rw [hQA, Subgroup.commutator_le]
  intro q hq a ha
  have ha' : a ∈ ((B : Set G) * (Subgroup.zpowers u : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left B _ hZB, hAB]
    exact ha
  obtain ⟨x, hx, y, hy, rfl⟩ := ha'
  have hqx : q * x = x * q := (Subgroup.mem_centralizer_iff.mp (hQB hq) x hx).symm
  have key : ⁅q, x * y⁆ = x * ⁅q, y⁆ * x⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc q * (x * y) * q⁻¹ * (x * y)⁻¹ = (q * x) * y * q⁻¹ * y⁻¹ * x⁻¹ := by group
      _ = (x * q) * y * q⁻¹ * y⁻¹ * x⁻¹ := by rw [hqx]
      _ = x * (q * y * q⁻¹ * y⁻¹) * x⁻¹ := by group
  rw [key]
  have hqy : ⁅q, y⁆ ∈ N := hc (Subgroup.commutator_mem_commutator (hQ hq) hy)
  exact (Subgroup.mem_normalizer_iff.mp (hAN (hBA hx)) _).mp hqy

theorem centralizer_inf_le_of_mem_hyperplane {A B : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hB : IsHyperplane A B)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) (hb1 : b ≠ 1) (hb'1 : b' ≠ 1)
    (hne : Subgroup.zpowers b ≠ Subgroup.zpowers b') :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({b'} : Set G) ≤
      Subgroup.centralizer (B : Set G) := by
  have h3 : Nat.card (Subgroup.zpowers b) = 3 := Sec13.card_zpowers_eq_three hA (hB.1 hb) hb1
  have h3' : Nat.card (Subgroup.zpowers b') = 3 :=
    Sec13.card_zpowers_eq_three hA (hB.1 hb') hb'1
  have h9 : Nat.card B = 9 := by have := hB.2; omega
  have hH : IsHyperplane B (Subgroup.zpowers b) :=
    ⟨Subgroup.zpowers_le.mpr hb, by rw [h9, h3]⟩
  have hb'z : b' ∉ Subgroup.zpowers b := by
    intro hm
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hm) (by rw [h3, h3'])).symm
  have hBeq := sup_zpowers_eq_of_isHyperplane hH hb' hb'z
  intro g hg
  obtain ⟨hgb, hgb'⟩ := Subgroup.mem_inf.mp hg
  have hle : B ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← hBeq]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgb').symm
  exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem le_pPrimeCoreOf_of_coprime {Y Cb N J R Q : Subgroup G} {u : G} (hu3 : u ^ 3 = 1)
    (hNCb : N ≤ Cb) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hCbN : Cb ≤ Subgroup.normalizer (N : Set G))
    (hCbNJ : Cb ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G))
    (huY : u ∈ Subgroup.normalizer (Y : Set G)) (huCb : u ∈ Cb) (hJCb : J ≤ Cb)
    (hJu : J ≤ Subgroup.centralizer ({u} : Set G))
    (hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hR3 : Nat.Coprime 3 (Nat.card R)) (hQR : Q ≤ R) (hQ : Q ≤ Y ⊓ Cb) (hQNJ : Q ≤ N ⊔ J) :
    Q ≤ pPrimeCoreOf 3 (Y ⊓ Cb) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set YC := Y ⊓ Cb with hYC
  set M := YC ⊓ (N ⊔ J) with hM
  set K₀ := M ⊓ N with hK₀
  have hYCM : YC ≤ Subgroup.normalizer (M : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (inf_le_right.trans hCbNJ)
  have huYC : u ∈ Subgroup.normalizer (YC : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huY, Subgroup.le_normalizer huCb⟩
  have huM : u ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huYC, hCbNJ huCb⟩
  have huK : u ∈ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huM, hCbN huCb⟩
  have hMCb : M ≤ Cb := inf_le_left.trans inf_le_right
  have hMK : M ≤ Subgroup.normalizer (K₀ : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hMCb.trans hCbN)
  have hK3 : ¬ 3 ∣ Nat.card K₀ := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
      (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hZN : Subgroup.zpowers u ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (hCbN huCb)
  have hJZ : J ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers148]
    exact hJu
  have hc := commutator_sup_le148 hZN (hJCb.trans hCbN) hJZ
  have hMu : ∀ m ∈ M, ⁅m, u⁆ ∈ K₀ := by
    intro m hm
    refine Subgroup.mem_inf.mpr ⟨?_, hc (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mp hm).2 (Subgroup.mem_zpowers u))⟩
    have h1 : u * m⁻¹ * u⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp huM _).mp (inv_mem hm)
    have h2 : ⁅m, u⁆ = m * (u * m⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hm h1
  set N₀ := N.subgroupOf Cb with hN₀
  have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNCb).mpr hCbN
  have hRM : R ⊓ M ≤ Cb := inf_le_right.trans hMCb
  set U := ((R ⊓ M).subgroupOf Cb).map (QuotientGroup.mk' N₀) with hU
  have hUN : (U.comap (QuotientGroup.mk' N₀)).map Cb.subtype = (R ⊓ M) ⊔ N := by
    rw [hU, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hRM, hN₀, Subgroup.map_subgroupOf_eq_of_le hNCb]
  have hMnorm : M ≤ Subgroup.normalizer (((R ⊓ M) ⊔ N : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨c, hcM, hcu, hcm⟩ :=
      exists_commute_of_commutator_mem hu3 inf_le_left hMK huK hK3 hm (hMu m hm)
    have hcC : c ∈ Cb := hMCb hcM
    have hmC : m ∈ Cb := hMCb hm
    have hcR : c ∈ Subgroup.normalizer (R : Set G) :=
      hR (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcM).1,
        Subgroup.mem_centralizer_singleton_iff.mpr hcu⟩)
    have hcRM : (⟨c, hcC⟩ : ↥Cb) ∈
        Subgroup.normalizer (((R ⊓ M).subgroupOf Cb : Subgroup ↥Cb) : Set ↥Cb) :=
      mem_normalizer_subgroupOf ⟨c, hcC⟩
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨hcR, hYCM (Subgroup.mem_inf.mp hcM).1⟩)
    have hπcm : QuotientGroup.mk' N₀ (⟨m, hmC⟩ : ↥Cb) = QuotientGroup.mk' N₀ ⟨c, hcC⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN₀,
        Subgroup.mem_subgroupOf]
      simpa using inv_mem (Subgroup.mem_inf.mp hcm).2
    have h1 : QuotientGroup.mk' N₀ (⟨m, hmC⟩ : ↥Cb) ∈
        Subgroup.normalizer (U : Set (↥Cb ⧸ N₀)) := by
      rw [hπcm]
      exact Subgroup.le_normalizer_map (QuotientGroup.mk' N₀) ⟨_, hcRM, rfl⟩
    have h2 : (⟨m, hmC⟩ : ↥Cb) ∈ Subgroup.normalizer
        ((U.comap (QuotientGroup.mk' N₀) : Subgroup ↥Cb) : Set ↥Cb) :=
      Subgroup.le_normalizer_comap (QuotientGroup.mk' N₀) h1
    rw [← hUN]
    exact Subgroup.le_normalizer_map Cb.subtype ⟨_, h2, rfl⟩
  have hU3 : ¬ 3 ∣ Nat.card U := fun h => by
    have h' := h.trans (Subgroup.card_map_dvd _ (QuotientGroup.mk' N₀))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv] at h'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR3
      (h'.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hW3 : Nat.Coprime 3 (Nat.card (M ⊓ ((R ⊓ M) ⊔ N) : Subgroup G)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    have h3' := h3.trans (Subgroup.card_dvd_of_le inf_le_right)
    rw [← hUN, Subgroup.card_map_of_injective Cb.subtype_injective] at h3'
    refine not_dvd_card_comap (QuotientGroup.mk' N₀) hU3 ?_ h3'
    rw [QuotientGroup.ker_mk', hN₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNCb).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
  have hOM : pPrimeCoreOf 3 M ≤ pPrimeCoreOf 3 YC :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 M).trans inf_le_left)
      (hYCM.trans (normalizer_le_normalizer_pPrimeCoreOf 3 M)) (coprime_card_pPrimeCoreOf 3 M)
  have hQM : Q ≤ M := le_inf hQ hQNJ
  exact ((le_inf hQM ((le_inf hQR hQM).trans le_sup_left)).trans
    (le_pPrimeCoreOf inf_le_left (Late.le_normalizer_inf Subgroup.le_normalizer hMnorm)
      hW3)).trans hOM

end General

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_delta_eq {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Q X : Subgroup G}
    (hB : IsHyperplane A B) (hQ : Q ∈ scriptQZero A (lB A))
    (hQB : Q ≤ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B)
    (hΔ : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G)) :
    Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X := by
  have hD := h.toSec13Data
  have hbA : b ∈ A := hB.1 hb
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) :=
    hQB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hQΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hQ.1 hQb
  rw [hΔ, sup_right_comm] at hQΔ
  rw [hQ.2]
  exact (Subgroup.commutator_mono hQΔ le_rfl).trans (commutator_sup_le148 (hAC.trans hCX)
    (((pPrimeCoreOf_le 3 _).trans hCAb).trans hCX) (pPrimeCoreOf_le 3 _))

theorem false_of_hjCase_i {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY A) (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hbΩ : Subgroup.zpowers b ∉ omegaA A)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {b' : G}
    (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) {X : Subgroup G}
    (hΔ : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hXeq : X = lB A (Subgroup.closure {b, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    False := by
  have hD := h.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hbA : b ∈ A := hB.1 hb
  have hb'A : b' ∈ A := (zpowers_mem_omegaA_iff.mp hb'Ω).1
  have hQNX := le_sup_of_delta_eq h hB hQ (hQY.trans inf_le_right) hb hΔ hCX
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  set J := lB A (Subgroup.closure {b, b'}) with hJ
  have hAC : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx b hbA)
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hJB' : J ≤ Subgroup.centralizer ((Subgroup.closure {b, b'} : Subgroup G) : Set G) :=
    lB_le_centralizer A _
  have hJb : J ≤ Cb := hJB'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
    (Subgroup.subset_closure (Set.mem_insert b {b'}))))
  have hJb' : J ≤ Subgroup.centralizer ({b'} : Set G) := hJB'.trans (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))))
  have hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ N := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn hX]
    exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
  have hJX : J ≤ X := by
    rw [hXeq]
    exact le_sup_left
  have hNX : N ⊔ X = N ⊔ J := by
    refine le_antisymm ?_ (sup_le le_sup_left (hJX.trans le_sup_right))
    rw [hXeq]
    exact sup_le le_sup_left (sup_le le_sup_right (hθX.trans le_sup_left))
  have hCbNJ : Cb ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) := by
    rw [← hNX]
    exact hCX
  have hQNJ : Q ≤ N ⊔ J := by
    rw [← hNX]
    exact hQNX
  have hQCb : Q ≤ Cb :=
    hQY.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)))
  have hQYC : Q ≤ Y ⊓ Cb := le_inf (hQY.trans inf_le_left) hQCb
  have hb'B : b' ∈ B := by
    by_contra hb'B
    apply hQb
    have hQN : Q ≤ N := le_of_eq_commutator_of_sup
      (sup_zpowers_eq_of_isHyperplane hB hb'A hb'B) hAab hb'A (hAC.trans hCbN)
      (hJb.trans hCbN) hJb' (hQY.trans inf_le_right) hQNJ hQ.2
    exact (le_inf hQN hQYC).trans (inf_le_pPrimeCoreOf148 (inf_le_right.trans hCbN) hN3)
  have hb'1 : b' ≠ 1 := by
    rintro rfl
    have h1 := (zpowers_mem_omegaA_iff.mp hb'Ω).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  have hne : Subgroup.zpowers b ≠ Subgroup.zpowers b' := fun he => hbΩ (he ▸ hb'Ω)
  have hCB : Cb ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    centralizer_inf_le_of_mem_hyperplane hD.isElemAbelian hD.card_eq hB hb hb'B hb1 hb'1 hne
  have hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
    (le_sSup ⟨hQ, hQY⟩ : Q ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G))).trans
      (hYB B hB)
  apply hQb
  refine le_pPrimeCoreOf_of_coprime (hD.isElemAbelian.2 b' hb'A) (pPrimeCoreOf_le 3 Cb) hN3
    hCbN hCbNJ (hY.2 hb'A) (hAC hb'A) hJb hJb' ?_ (coprime_card_pPrimeCoreOf 3 _) hQR hQYC hQNJ
  intro g hg
  obtain ⟨hgYC, hgb'⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hgY, hgb⟩ := Subgroup.mem_inf.mp hgYC
  exact le_normalizer_pPrimeCoreOf 3 _
    (Subgroup.mem_inf.mpr ⟨hgY, hCB (Subgroup.mem_inf.mpr ⟨hgb, hgb'⟩)⟩)

end Item148HJ

theorem step148PointHJ_of (hd : Step148PointHJd) : Step148PointHJ := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb hHJ
  obtain ⟨b', d, Lb, hb'Ω, hLb, hJ2, hdA, hd1, hdc, hbbd, X, hΔ, hCX, hcase⟩ := hHJ
  rcases hcase with ⟨hX, hXeq, -⟩ | ⟨hbd, h𝒳, htype⟩
  · exact (Item148HJ.false_of_hjCase_i h hY hYB hB hQ hQY hb hb1 hbΩ hQb hb'Ω hΔ hCX hX
      hXeq).elim
  · exact hd G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
      hdc hbbd hbd X hΔ hCX h𝒳 htype
      (Item148HJ.le_sup_of_delta_eq h hB hQ (hQY.trans inf_le_right) hb hΔ hCX)

end CFSG.RankThree.PartTwo.Sec14
