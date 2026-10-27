module

public import CFSG.Quasithin.MS93.S4ASL3
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.MS93.ASGroup
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Perfect

theorem eq_top_of_pow_mem_of_isPerfect {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (N : Subgroup Γ) [N.Normal] (hq : ∀ g : Γ, ∃ k : ℕ, g ^ 2 ^ k ∈ N) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Γ ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hq g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  by_contra hne
  have : Nontrivial (Γ ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (Γ ⧸ N) hp.isNilpotent

theorem isPerfect_statedSL_three (F : Type) [Field F] : Group.IsPerfect ↥(StatedSL 3 F) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) F

end Perfect

section Comm

variable {G : Type} [Group G]

theorem S4A.commutator_sup_le_of {A B H N : Subgroup G} (hA : ⁅A, H⁆ ≤ N) (hB : ⁅B, H⁆ ≤ N)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    ⁅A ⊔ B, H⁆ ≤ N := by
  have hABN : A ⊔ B ≤ Subgroup.normalizer (N : Set G) := sup_le hAN hBN
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have key : ∀ x ∈ A ⊔ B, ⁅x, y⁆ ∈ N := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact hA (Subgroup.commutator_mem_commutator hz hy)
      · exact hB (Subgroup.commutator_mem_commutator hz hy)
    | one => simp
    | mul a b ha hb iha ihb =>
      have haN : a ∈ Subgroup.normalizer (N : Set G) :=
        hABN (by rw [Subgroup.sup_eq_closure]; exact ha)
      have hrw : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp ihb) iha
    | inv a ha iha =>
      have haN : a ∈ Subgroup.normalizer (N : Set G) :=
        hABN (by rw [Subgroup.sup_eq_closure]; exact ha)
      have hrw : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hrw]
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem haN) _).mp (N.inv_mem iha)
  exact key x hx

theorem le_normalizer_of_commutator_le {A P : Subgroup G} (h : ⁅A, P⁆ ≤ P) :
    A ≤ Subgroup.normalizer (P : Set G) := by
  exact Subgroup.le_normalizer_iff_commutator_le_right.mpr h

end Comm

section TwoCoreL

variable {G : Type} [Group G]

noncomputable abbrev pCoreL (L : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥L).map L.subtype

theorem pCoreL_le (L : Subgroup G) : pCoreL L ≤ L := Subgroup.map_subtype_le _

theorem le_normalizer_pCoreL {L M : Subgroup G} (hN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (pCoreL L : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ pCoreL L, m * x * m⁻¹ ∈ pCoreL L := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmL : ∀ z : ↥L, m * (z : G) * m⁻¹ ∈ L := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hN hm) z).1 z.2
    have hmL' : ∀ z : ↥L, m⁻¹ * (z : G) * m⁻¹⁻¹ ∈ L := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hm)) z).1 z.2
    let σ : ↥L ≃* ↥L :=
      { toFun := fun z => ⟨m * z * m⁻¹, hmL z⟩
        invFun := fun z => ⟨m⁻¹ * z * m⁻¹⁻¹, hmL' z⟩
        left_inv := fun z => Subtype.ext (by simp [mul_assoc])
        right_inv := fun z => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun z w => Subtype.ext (by simp [mul_assoc]) }
    have hσ := CFSG.pCore_map_iso 2 σ
    have hmem : σ y ∈ CFSG.pCore 2 ↥L := by
      rw [← hσ]
      exact ⟨y, hy, rfl⟩
    exact ⟨σ y, hmem, rfl⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem commutator_le_pCoreL_of_quasisimple {L K : Subgroup G}
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) (hne : ¬ L ≤ K ⊔ pCoreL L) :
    ⁅K, L⁆ ≤ pCoreL L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set K' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (K.subgroupOf L).map π with hK'
  have hKn : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLK
  have hK'n : K'.Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  have hK'top : K' ≠ ⊤ := by
    intro htop
    apply hne
    intro l hl
    have : π ⟨l, hl⟩ ∈ K' := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
    have hl' : l = (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [hl']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) ⟨_, hkl, rfl⟩
  have hcen : K' ≤ Subgroup.center _ := le_center_of_isQuasisimple hQ hK'top
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have hkK : π ⟨k, hKL hk⟩ ∈ Subgroup.center _ :=
    hcen ⟨⟨k, hKL hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hc : π ⁅(⟨k, hKL hk⟩ : ↥L), ⟨l, hl⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hkK _).symm
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  exact ⟨_, hc, rfl⟩

end TwoCoreL

section Structure

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem conj_eq_of_natural_of_eq_one {K V : Subgroup G} {F : Type} [Field F]
    {φ : ↥K →* ↥(StatedSL 3 F)} (hnat : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {a : ↥K}
    (ha : φ a = 1) {u : G} (hu : u ∈ V) : (a : G) * u * (a : G)⁻¹ = u := by
  refine (conj_eq_iff_of_natural hnat a ⟨u, hu⟩).mpr ?_
  rw [ha]
  simp

theorem exists_mem_L_eq (h : PUHyp M T L) {F : Type} [Field F] [Finite F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : Function.Surjective φ) (y : ↥(StatedSL 3 F)) :
    ∃ ℓ : ↥M, (ℓ : G) ∈ L ∧ φ ℓ = y := by
  have := isPerfect_statedSL_three F
  set N : Subgroup ↥(StatedSL 3 F) := (L.subgroupOf M).map φ with hN
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hNn : N.Normal := hLn.map φ hφ
  have htop : N = ⊤ := by
    refine eq_top_of_pow_mem_of_isPerfect N fun g => ?_
    obtain ⟨m, rfl⟩ := hφ g
    have hmLT : (m : G) ∈ ((L ⊔ T : Subgroup G) : Set G) := by
      rw [← h.eq_sup]
      exact m.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T (h.le.trans h.le_normalizer)] at hmLT
    obtain ⟨l, hl, t, ht, hlt⟩ := hmLT
    obtain ⟨k, hk⟩ := h.isPGroup ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have hlM : l ∈ M := h.L_le hl
    have htM : t ∈ M := h.le ht
    have hm : m = ⟨l, hlM⟩ * ⟨t, htM⟩ := Subtype.ext hlt.symm
    have hlN : φ ⟨l, hlM⟩ ∈ N := ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have ht1 : (⟨t, htM⟩ : ↥M) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have hmod : ∀ n : ℕ, (φ m) ^ n * ((φ ⟨t, htM⟩) ^ n)⁻¹ ∈ N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hm, map_mul] at ih ⊢
        have hconj := hNn.conj_mem _ ih (φ ⟨l, hlM⟩ * φ ⟨t, htM⟩)
        have hrw : (φ ⟨l, hlM⟩ * φ ⟨t, htM⟩) ^ (n + 1) * ((φ ⟨t, htM⟩) ^ (n + 1))⁻¹ =
            φ ⟨l, hlM⟩ * (φ ⟨t, htM⟩ * ((φ ⟨l, hlM⟩ * φ ⟨t, htM⟩) ^ n *
              ((φ ⟨t, htM⟩) ^ n)⁻¹) * (φ ⟨t, htM⟩)⁻¹) := by
          group
        rw [hrw]
        refine N.mul_mem hlN ?_
        have := hNn.conj_mem _ ih (φ ⟨t, htM⟩)
        exact this
    have := hmod (2 ^ k)
    rwa [← map_pow φ ⟨t, htM⟩, ht1, map_one, inv_one, mul_one] at this
  have hy : y ∈ N := htop ▸ Subgroup.mem_top y
  obtain ⟨ℓ, hℓ, rfl⟩ := hy
  exact ⟨ℓ, Subgroup.mem_subgroupOf.mp hℓ, rfl⟩

theorem pCoreOf_le_centralizer_Uq (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  have hX : Xq M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)).trans inf_le_right
  exact (Subgroup.le_centralizer_iff.mp hX).trans (Subgroup.centralizer_le h.Uq_le_Xq)

theorem commutator_centralizer_Uq_le (h : PUHyp M T L) {F : Type} [Field F] [Finite F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : Function.Surjective φ)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) ⊥ φ false 1) :
    ⁅M ⊓ Subgroup.centralizer (Uq M T L : Set G), L⁆ ≤ pCoreL L := by
  set U := Uq M T L with hU
  set C := M ⊓ Subgroup.centralizer (U : Set G) with hC
  set K := L ⊓ Subgroup.centralizer (U : Set G) with hK
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := le_normalizer_Uq h.le_normalizer
  have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf (h.L_le.trans (Subgroup.le_normalizer))
      (le_normalizer_centralizer (h.L_le.trans hMU))
  have hLK : L ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer (h.L_le.trans hMU))
  have hCLK : ⁅C, L⁆ ≤ K := by
    refine le_inf ?_ ((Subgroup.le_normalizer_iff_commutator_le_left.mp hLC).trans inf_le_right)
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans h.le_normalizer)
  have hOL : pCoreL L ≤ pCoreOf 2 M := map_pCore_le_pCoreOf h.L_le h.le_normalizer
  have hne : ¬ L ≤ K ⊔ pCoreL L := by
    intro hle
    have hcent : L ≤ Subgroup.centralizer (U : Set G) :=
      hle.trans (sup_le inf_le_right (hOL.trans (pCoreOf_le_centralizer_Uq h)))
    have hcard := CFSG.SectionRank.OddCover.card_statedSL_three (K := F)
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h1 : 1 < Nat.card ↥(StatedSL 3 F) := by
      rw [hcard]
      have e2 : 4 ≤ Nat.card F ^ 2 := by nlinarith
      have e3 : 8 ≤ Nat.card F ^ 3 := by nlinarith
      calc 1 < 8 * 3 * 7 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul e3 (by omega)) (by omega)
    have : Nontrivial ↥(StatedSL 3 F) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(StatedSL 3 F))
    obtain ⟨ℓ, hℓL, rfl⟩ := exists_mem_L_eq h hφ y
    apply hy
    refine eq_one_of_isSumOfNaturalModulesVia hnat fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp (hcent hℓL) v hv
    rw [← this, mul_inv_cancel_right]
  have hKL : ⁅K, L⁆ ≤ pCoreL L :=
    commutator_le_pCoreL_of_quasisimple h.quasisimple inf_le_left hLK hne
  have hn₁ : L ≤ Subgroup.normalizer (pCoreL L : Set G) :=
    le_normalizer_pCoreL Subgroup.le_normalizer
  have hn₃ : C ≤ Subgroup.normalizer (pCoreL L : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreL h.le_normalizer)
  have h3 := three_subgroups_le (N := pCoreL L) (H₁ := L) (H₂ := L) (H₃ := C) hn₁ hn₁ hn₃
    (by rw [Subgroup.commutator_comm L C]; exact (Subgroup.commutator_mono hCLK le_rfl).trans hKL)
    ((Subgroup.commutator_mono hCLK le_rfl).trans hKL)
  rw [h.perfect, Subgroup.commutator_comm] at h3
  exact h3

theorem sup_eq_top_of_index {H : Type*} [Group H] {A B : Subgroup H} {a : ℕ}
    (hA : A.index = 2 ^ a) (hB : ¬ 2 ∣ B.index) : A ⊔ B = ⊤ := by
  have h1 : (A ⊔ B).index ∣ 2 ^ a := hA ▸ Subgroup.index_dvd_of_le le_sup_left
  have h2 : (A ⊔ B).index ∣ B.index := Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj'
    exact Subgroup.index_eq_one.mp hj'
  · exfalso
    apply hB
    rw [hj', pow_succ] at h2
    exact (Dvd.intro_left _ rfl).trans h2

theorem sup_pCoreOf_eq_of_natural (h : PUHyp M T L) {F : Type} [Field F] [Finite F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : Function.Surjective φ)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L) ⊥ φ false 1) :
    M = L ⊔ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Uq M T L with hU
  set O := pCoreOf 2 M with hO
  set C := M ⊓ Subgroup.centralizer (U : Set G) with hC
  set N := L ⊔ O with hN
  have hOM : O ≤ M := pCoreOf_le' M
  have hNM : N ≤ M := sup_le h.L_le hOM
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN]
    exact (le_inf h.le_normalizer (le_normalizer_pCoreOf M)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L O)
  have hOC : O ≤ C := le_inf hOM (pCoreOf_le_centralizer_Uq h)
  have hMC : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer (le_normalizer_Uq
      h.le_normalizer))
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  obtain ⟨P, ⟨hPC, hP2, hPidx⟩, hOP⟩ := EscapingLocal.exists_isSylowTwoOf_ge hOC hO2
  have hCL : ⁅C, L⁆ ≤ O :=
    (commutator_centralizer_Uq_le h hφ hnat).trans (map_pCore_le_pCoreOf h.L_le h.le_normalizer)
  have hNC : ⁅N, C⁆ ≤ O := by
    refine S4A.commutator_sup_le_of ?_ ?_ (h.L_le.trans (le_normalizer_pCoreOf M))
      (hOM.trans (le_normalizer_pCoreOf M))
    · rw [Subgroup.commutator_comm]
      exact hCL
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_left.trans (le_normalizer_pCoreOf M))
  have hidx : ∃ a : ℕ, (N.subgroupOf C).index = 2 ^ a := by
    set N' := N.subgroupOf M with hN'
    have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hMN
    have h1 : (N.subgroupOf C).index = N'.relIndex (C.subgroupOf M) := by
      rw [hN', Subgroup.relIndex_subgroupOf (inf_le_left : C ≤ M)]
      rfl
    have h2 : N'.relIndex (C.subgroupOf M) ∣ N'.index := Subgroup.relIndex_dvd_index_of_normal _ _
    have h3 : N'.index = N'.relIndex (T.subgroupOf M) := by
      rw [← Subgroup.relIndex_sup_right, ← Subgroup.relIndex_top_right]
      congr 1
      symm
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ L ⊔ T := h.eq_sup ▸ x.2
      have hle : L ⊔ T ≤ (T.subgroupOf M ⊔ N').map M.subtype := by
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_of_le_left h.le, inf_of_le_left hNM]
        exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
      obtain ⟨y, hy, hyx⟩ := hle hx
      rwa [Subtype.ext hyx] at hy
    have h4 : ∃ a : ℕ, N'.relIndex (T.subgroupOf M) = 2 ^ a := by
      have hT : IsPGroup 2 ↥(T.subgroupOf M) :=
        h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
      exact hT.index (N'.subgroupOf (T.subgroupOf M))
    obtain ⟨a, ha⟩ := h4
    rw [h1]
    rw [h3, ha] at h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact ⟨j, hj⟩
  obtain ⟨a, ha⟩ := hidx
  have htop := sup_eq_top_of_index ha hPidx
  have hCNP : C ≤ (N ⊓ C) ⊔ P := by
    intro c hc
    have hmem : (⟨c, hc⟩ : ↥C) ∈ N.subgroupOf C ⊔ P.subgroupOf C := htop ▸ Subgroup.mem_top _
    have := Subgroup.mem_map_of_mem C.subtype hmem
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hPC] at this
    exact this
  have hNCP : N ⊓ C ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_commutator_le ((Subgroup.commutator_mono inf_le_left hPC).trans
      (hNC.trans hOP))
  have hCP : C ≤ Subgroup.normalizer (P : Set G) := hCNP.trans (sup_le hNCP Subgroup.le_normalizer)
  have hPO : P ≤ O :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPC hCP hP2).trans
      (pCoreOf_le_pCoreOf_of_le_normalizer inf_le_left hMC)
  have hCN : C ≤ N := hCNP.trans (sup_le inf_le_left (hPO.trans le_sup_right))
  refine le_antisymm (fun m hm => ?_) hNM
  obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφ (φ ⟨m, hm⟩)
  have hc : φ (ℓ⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hℓ, inv_mul_cancel]
  have hcC : (ℓ : G)⁻¹ * m ∈ C := by
    refine ⟨M.mul_mem (M.inv_mem ℓ.2) hm, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have := conj_eq_of_natural_of_eq_one hnat hc hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc u * ((ℓ : G)⁻¹ * m) = ((ℓ : G)⁻¹ * m) * u * ((ℓ : G)⁻¹ * m)⁻¹ * ((ℓ : G)⁻¹ * m) := by
          rw [this]
      _ = ((ℓ : G)⁻¹ * m) * u := by group
  have hm' : m = (ℓ : G) * ((ℓ : G)⁻¹ * m) := by group
  rw [hm']
  exact N.mul_mem (le_sup_left (a := L) hℓL) (hCN hcC)

end Structure

section S41

variable {G : Type} [Group G]

theorem sq_eq_one_of_mem_omegaOneCenterOf {K : Subgroup G} {x : G}
    (hx : x ∈ omegaOneCenterOf K) : x ^ 2 = 1 := by
  have hle : omegaOneCenterOf K ≤ Subgroup.centralizer (K : Set G) :=
    (PU.omegaOneCenterOf_le_centerOf K).trans inf_le_right
  have hleK : omegaOneCenterOf K ≤ K := PU.omegaOneCenterOf_le K
  have key : ∀ y ∈ omegaOneCenterOf K, y ^ 2 = 1 := by
    intro y hy
    have hy' := hy
    unfold omegaOneCenterOf omegaOneOf at hy'
    induction hy' using Subgroup.closure_induction with
    | mem z hz => exact hz.2
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        Subgroup.mem_centralizer_iff.mp (hle hb) a (hleK ha)
      rw [Commute.mul_pow hab 2, iha ha, ihb hb, one_mul]
    | inv a ha iha => rw [inv_pow, iha ha, inv_one]
  exact key x hx

variable [Finite G]

theorem s41_holds : S41 := by
  intro G _ _ M T L h hfull
  obtain ⟨hX, -, n, F, _, _, φ, -, hφ, hnat⟩ := hfull
  have hML := sup_pCoreOf_eq_of_natural h hφ hnat
  have hZM : Zq M L ≤ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine (le_of_eq hML).trans (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.mp inf_le_right
    · exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans
        ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right))
  have hZT : Zq M L ≤ omegaOneCenterOf T := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨h.pCore_le (Xq_le_pCoreOf M hx.1), ?_⟩,
      sq_eq_one_of_mem_omegaOneCenterOf hx.1⟩
    exact Subgroup.centralizer_le h.le (hZM hx)
  have hXZ : Xq M = Z0q M T := by
    refine le_antisymm ?_ h.Z0q_le_Xq
    rw [hX]
    refine sup_le (hZT.trans ?_) (Uq_le_Z0q h.L_le)
    exact le_normalClosureIn ((PU.omegaOneCenterOf_le T).trans h.le)
  refine ⟨hML, hZM, hXZ, le_antisymm ?_ (Subgroup.commutator_mono le_rfl h.L_le)⟩
  rw [← hXZ, hX]
  refine S4A.commutator_sup_le_of ?_ ?_ (Zq_le.trans (le_normalizer_Uq h.le_normalizer))
    ((Uq_le h.L_le).trans (le_normalizer_Uq h.le_normalizer))
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZM]
    exact bot_le
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_Uq h.le_normalizer)

end S41

end CFSG.Quasithin.MS93
