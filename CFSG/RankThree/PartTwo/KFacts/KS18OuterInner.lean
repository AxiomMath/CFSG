module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterCore

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {Y : Type} [Group Y]

theorem card_eq_card_map_mul_card_inf_ker {H : Type*} [Group H] (f : Y →* H) (A : Subgroup Y) :
    Nat.card A = Nat.card (A.map f) * Nat.card ↥(A ⊓ f.ker) := by
  have h := Subgroup.relIndex_mul_card f.ker A
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h.symm

section Action

variable (L : Subgroup Y) [L.Normal] {P : Type} [Group P] (ψ : L ⧸ Subgroup.center L ≃* P)

theorem actOn_of_mem {l : Y} (hl : l ∈ L) :
    actOn L ψ l = MulAut.conj (ψ ((⟨l, hl⟩ : L) : L ⧸ Subgroup.center L)) := by
  ext p
  obtain ⟨q, rfl⟩ := ψ.surjective p
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rw [actOn_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 2

theorem actOn_of_mem_centralizer {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y)) :
    actOn L ψ c = 1 := by
  ext p
  obtain ⟨q, rfl⟩ := ψ.surjective p
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rw [actOn_apply, MulAut.one_apply]
  congr 2
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, ← Subgroup.mem_centralizer_iff.mp hc _ m.2, mul_inv_cancel_right]

theorem actOn_eq_one_iff (hL : commutator L = ⊤) {y : Y} :
    actOn L ψ y = 1 ↔ y ∈ Subgroup.centralizer (L : Set Y) :=
  ⟨mem_centralizer_of_actOn_eq_one hL ψ, actOn_of_mem_centralizer L ψ⟩

theorem inf_ker_actOn (hL : commutator L = ⊤) (E : Subgroup Y) :
    E ⊓ (actOn L ψ).ker = E ⊓ Subgroup.centralizer (L : Set Y) := by
  ext y
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, actOn_eq_one_iff L ψ hL]

theorem card_map_actOn_mul (hL : commutator L = ⊤) (E : Subgroup Y) :
    Nat.card (E.map (actOn L ψ)) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) =
      Nat.card E := by
  rw [card_eq_card_map_mul_card_inf_ker (actOn L ψ) E, inf_ker_actOn L ψ hL]

end Action

section E9

variable {k : Type} [Field k] {X L E : Subgroup Y} [L.Normal]
  (ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k)

theorem actOn_mem_range_conj
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c) {x : Y}
    (hx : x ∈ X) :
    actOn L ψ x ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  obtain ⟨l, hl, c, hc, rfl⟩ := hXLC x hx
  rw [map_mul, actOn_of_mem_centralizer L ψ hc, mul_one, actOn_of_mem L ψ hl]
  exact ⟨_, rfl⟩

theorem map_actOn_le_range
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hEX : E ≤ X) :
    E.map (actOn L ψ) ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  rintro _ ⟨e, he, rfl⟩
  exact actOn_mem_range_conj ψ hXLC (hEX he)

theorem card_comap_conj_map_actOn (hk : Nat.card k = 4)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hEX : E ≤ X) :
    Nat.card ((E.map (actOn L ψ)).comap
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))) =
      Nat.card (E.map (actOn L ψ)) := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self (map_actOn_le_range ψ hXLC hEX)]
  exact (Subgroup.card_map_of_injective (L34.conj_injective hk)).symm

theorem card_map_actOn_le (hk : Nat.card k = 4)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) :
    Nat.card (E.map (actOn L ψ)) ≤ 9 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ((E.map (actOn L ψ)).comap
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))) :=
    (hE3.map _).comap_of_injective _ (L34.conj_injective hk)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd := Subgroup.card_subgroup_dvd_card ((E.map (actOn L ψ)).comap
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)))
  rw [hn, L34.card_projectiveSL hk] at hdvd
  have hn2 : n ≤ 2 := by
    by_contra h
    have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h27.trans hdvd
    norm_num at this
  rw [← card_comap_conj_map_actOn ψ hk hXLC hEX, hn]
  calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 9 := by norm_num

theorem three_le_card_inf_centralizer (ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k)
    (hk : Nat.card k = 4) (hL : commutator L = ⊤)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27) :
    3 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) := by
  have h1 := card_map_actOn_mul L ψ hL E
  have h2 := card_map_actOn_le ψ hk hXLC hEX hE3
  rw [hE27] at h1
  nlinarith

theorem exists_E9 (hk : Nat.card k = 4) (hL : commutator L = ⊤)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27)
    (hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3) :
    ∃ E9 : Subgroup (projectiveSL 3 k), Nat.card E9 = 9 ∧
      ∀ g ∈ E9, ∃ e ∈ E, actOn L ψ e = MulAut.conj g := by
  refine ⟨(E.map (actOn L ψ)).comap MulAut.conj, ?_, fun g hg => hg⟩
  have h1 := card_map_actOn_mul L ψ hL E
  have h2 := card_map_actOn_le ψ hk hXLC hEX hE3
  rw [hE27] at h1
  rw [card_comap_conj_map_actOn ψ hk hXLC hEX]
  nlinarith

end E9

section Cyclic

variable {X : Subgroup Y} [X.Normal] {t : Y}

theorem comm_quotient_of_sup_zpowers (h : X ⊔ Subgroup.zpowers t = ⊤) (a b : Y ⧸ X) :
    a * b = b * a := by
  have htop : (⊤ : Subgroup (Y ⧸ X)) = Subgroup.zpowers (QuotientGroup.mk' X t) := by
    rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective X), ← h,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top b)
  exact zpow_mul_comm _ i j

theorem commutator_le_of_sup_zpowers (h : X ⊔ Subgroup.zpowers t = ⊤) : commutator Y ≤ X := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    comm_quotient_of_sup_zpowers h (a : Y ⧸ X)]
  group

theorem perfectResidual_le_commutator (h : X ⊔ Subgroup.zpowers t = ⊤) :
    CFSG.perfectResidual Y ≤ ⁅X, X⁆ := by
  unfold CFSG.perfectResidual
  refine (iInf_le _ 2).trans ?_
  rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, derivedSeries_one]
  exact Subgroup.commutator_mono (commutator_le_of_sup_zpowers h)
    (commutator_le_of_sup_zpowers h)

theorem eq_bot_of_le_centralizer_of_sup [Finite Y] (hO : CFSG.pCore 2 Y = ⊥)
    (h : X ⊔ Subgroup.zpowers t = ⊤) {R : Subgroup Y} (hR : IsPGroup 2 R)
    (hRX : R ≤ Subgroup.centralizer (X : Set Y)) : R = ⊥ :=
  eq_bot_of_le_centralizer_of_nilpotent hO (comm_quotient_of_sup_zpowers h) hR hRX

end Cyclic

variable {k : Type} [Field k]

theorem outer_involution_of_inner [Finite Y] (hk : Nat.card k = 4) (hO : CFSG.pCore 2 Y = ⊥)
    {X L E : Subgroup Y} {t : Y} [L.Normal] (hX : X.Normal) (hL : commutator L = ⊤)
    (ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k)
    (hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c)
    (hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)))
    (hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3)
    (hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y))
    (htX : t ∉ X) (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (hEX : E ≤ X) (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  have := hX
  exact outer_involution_of_act hk hX hL ψ (exists_E9 ψ hk hL hXLC hEX hE3 hE27 hEC) hEX hCX
    (fun R hR hRL hRE => eq_bot_of_le_centralizer_of_sup hO hYt hR (hKX R hR hRL hRE)) htX ht2
    hEt

end CFSG.RankThree.PartTwo.KFacts.KS18
