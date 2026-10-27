module

public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace TableB

section Rank

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem le_pRank_of_le {p : ℕ} (hp : 1 < p) {H E : Subgroup G} {k : ℕ} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hk : Nat.card E = p ^ k) : k ≤ CFSG.Assembly.pRank p H :=
  CFSG.SectionRank.le_pRank hp hEH hE hk

theorem pRank_le_card {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    CFSG.Assembly.pRank p H ≤ Nat.card G := by
  refine csSup_le ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun y hy => by
    rw [Subgroup.mem_bot.mp hy, one_pow]⟩, by simp⟩ ?_
  rintro j ⟨E', -, -, hj⟩
  calc j ≤ p ^ j := (Nat.lt_pow_self hp).le
    _ = Nat.card E' := hj.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group E'

theorem le_twoLocalRank {p : ℕ} (hp : 1 < p) {H : Subgroup G} (hH : IsTwoLocal H) {k : ℕ}
    (hk : k ≤ CFSG.Assembly.pRank p H) : k ≤ LargeEvenTwoLocalRank p G :=
  hk.trans (le_csSup ⟨Nat.card G, by rintro j ⟨H', -, rfl⟩; exact pRank_le_card hp H'⟩
    ⟨H, hH, rfl⟩)

theorem card_le_of_twoLocal {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hH : IsTwoLocal H)
    (hEH : E ≤ H) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ LargeEvenTwoLocalRank p G := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos
    (le_twoLocalRank hp.one_lt hH (le_pRank_of_le hp.one_lt hEH hE hk))

omit [Finite G] in
theorem isElemAbelian_sup {p : ℕ} {A C : Subgroup G} (hA : IsElemAbelian p A)
    (hC : IsElemAbelian p C) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    IsElemAbelian p (A ⊔ C) := CFSG.Open.IsElemAbelian.sup_of_commute hA hC hAC

omit [Finite G] in
theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) (f : H →* G) : IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

end Rank

end TableB

@[expose] def GGTorusLift (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∃ U E : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set L') ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ ψ.ker = ⊥

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ggQuotHom {L : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) : L →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' _)

omit [Finite G] in
theorem ggQuotHom_apply {L : Subgroup G} {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (l : L) : ggQuotHom θ l = θ (l : L ⧸ Subgroup.center L) :=
  rfl

omit [Finite G] in
theorem ggQuotHom_surjective {L : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) : Function.Surjective (ggQuotHom θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem ker_ggQuotHom {L : Subgroup G} {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) :
    (ggQuotHom θ).ker = Subgroup.center L := by
  ext l
  rw [MonoidHom.mem_ker, ggQuotHom_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem succ_le_twoLocalRank_of_torusLift {p r : ℕ} (hp : p.Prime) {x : G} {L : Subgroup G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hlift : GGTorusLift p r R) : r + 1 ≤ LargeEvenTwoLocalRank p G := by
  have := Fact.mk hp
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker⟩ := hlift L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  rw [ker_ggQuotHom] at hEker
  have hxC : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hXC : ∀ y ∈ Subgroup.zpowers x, ∀ l ∈ L, l * y = y * l := by
    intro y hy l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hxC l hl) k)
  have hXcent : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => hXC y hy l hl
  have hEG : IsElemAbelian p (E.map L.subtype) := isElemAbelian_map hE L.subtype
  have hX : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hEX : ∀ a ∈ E.map L.subtype, ∀ c ∈ Subgroup.zpowers x, a * c = c * a := by
    rintro _ ⟨e, -, rfl⟩ c hc
    exact hXC c hc e e.2
  have hE' := isElemAbelian_sup hEG hX hEX
  have hdisj : Disjoint (E.map L.subtype) (Subgroup.zpowers x) := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hXe
    have hec : e ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hXC _ hXe l l.2)
    have : e ∈ E ⊓ Subgroup.center L := ⟨he, hec⟩
    rw [hEker, Subgroup.mem_bot] at this
    rw [this]
    rfl
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer ((E.map L.subtype : Subgroup G) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨e, -, rfl⟩ := hg
        exact hXC y hy e e.2)
  have hcard : Nat.card (E.map L.subtype ⊔ Subgroup.zpowers x : Subgroup G) = p ^ (r + 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hXN hdisj,
      ← Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv, hEcard,
      Nat.card_zpowers, orderOf_eq_prime hx hx1, pow_succ]
  have hUne : U.map L.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : E.map L.subtype ⊔ Subgroup.zpowers x ≤
      Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
    refine sup_le ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)) ?_
    exact fun y hy => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨u, -, rfl⟩ := hg
        exact hXC y hy u u.2)
  exact le_twoLocalRank hp.one_lt hTL (le_pRank_of_le hp.one_lt hle hE' hcard)

theorem pow_le_card_range_ggBeta {p r : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hlift : GGTorusLift p r R) : p ^ r ≤ Nat.card (ggBeta L θ hBN).range := by
  have h1 := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ
    hlift
  have h2 := card_range_ggBeta_mul L θ hp hS hL hBN
  rw [hS.1.2.1] at h2
  have h3 : p ^ (r + 1) ≤ Nat.card (ggBeta L θ hBN).range * p := by
    rw [h2]
    exact Nat.pow_le_pow_right hp.pos h1
  rw [pow_succ] at h3
  exact Nat.le_of_mul_le_mul_right h3 hp.pos

end Main

end CFSG.StandardType
