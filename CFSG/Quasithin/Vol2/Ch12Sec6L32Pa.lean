module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open (pCoreOf quasithinGenFitting)
open CFSG.Quasithin CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

section Perfect

variable {Q : Type*} [Group Q]

theorem commutator_mul_central {z w a b : Q} (hza : Commute z a) (hzb : Commute z b)
    (hzw : Commute z w) (hwa : Commute w a) (hwb : Commute w b) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = (a * w * b * a⁻¹) * (b⁻¹ * w⁻¹) := by
        have h : Commute z (a * w * b * a⁻¹) :=
          ((hza.mul_right hzw).mul_right hzb).mul_right hza.inv_right
        rw [h.eq, mul_inv_cancel_right]
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by
        rw [show a * w = w * a from hwa.eq.symm]
        group
    _ = a * b * a⁻¹ * b⁻¹ := by
        have h : Commute w (a * b * a⁻¹ * b⁻¹) :=
          ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
        rw [h.eq, mul_inv_cancel_right]

theorem commute_of_conj_mul_inv_central {L : Subgroup Q} (hL : ⁅L, L⁆ = L) {x : Q}
    (hc : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ L) (hz : ∀ l ∈ L, ∀ m ∈ L, Commute (x * l * x⁻¹ * l⁻¹) m) :
    ∀ l ∈ L, Commute x l := by
  have key : ⁅L, L⁆ ≤ L ⊓ Subgroup.centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · rw [← hL]
      exact Subgroup.commutator_mem_commutator ha hb
    · show ⁅a, b⁆ ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ea : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
      have eb : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      have hconj : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      have h1 : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
        rw [hconj, ea, eb]
        exact commutator_mul_central (hz a ha a ha) (hz a ha b hb) (hz a ha _ (hc b hb))
          (hz b hb a ha) (hz b hb b hb)
      calc ⁅a, b⁆ * x = x * ⁅a, b⁆ * x⁻¹ * x := by rw [h1]
        _ = x * ⁅a, b⁆ := by group
  intro l hl
  rw [← hL] at hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (key hl).2).symm

end Perfect

section Dichotomy

variable {V : Type} [CommGroup V]

theorem le_or_le_centralizer {L H : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L)
    (hLH : L ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hHL : H ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    L ≤ H ∨ H ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
  have hN : (H.subgroupOf L).Normal := by
    constructor
    intro n hn l
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hLH l.2) n).mp hn
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (H.subgroupOf L) with
    h | h
  · right
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    have hc : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ L := fun l hl => by
      have := (Subgroup.mem_normalizer_iff.mp (hHL hx) l).mp hl
      exact L.mul_mem this (L.inv_mem hl)
    have hcH : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ H := fun l hl => by
      have := (Subgroup.mem_normalizer_iff.mp (hLH hl) x).mp hx
      have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
      rw [e]
      refine H.mul_mem hx ?_
      have := (Subgroup.mem_normalizer_iff.mp (hLH hl) x⁻¹).mp (H.inv_mem hx)
      exact this
    have hz : ∀ l ∈ L, ∀ m ∈ L, Commute (x * l * x⁻¹ * l⁻¹) m := by
      intro l hl m hm
      have h1 : (⟨_, hc l hl⟩ : ↥L) ∈ H.subgroupOf L := hcH l hl
      have h2 := Subgroup.mem_center_iff.mp (h h1) ⟨m, hm⟩
      exact (congrArg Subtype.val h2).symm
    intro l hl
    exact (commute_of_conj_mul_inv_central hperf hc hz l hl).eq.symm
  · left
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this

end Dichotomy

section FF

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem eq_one_of_pow_two_pow_of_noInv {S : Subgroup (MulAut V)}
    (hS : ∀ y ∈ S, y ^ 2 = 1 → y = 1) {x : MulAut V} (hx : x ∈ S) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 := by
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    refine hS _ (S.pow_mem hx _) ?_
    rw [← pow_mul, ← pow_succ]
    exact hk

theorem not_isPGroup_of_isQuasisimple {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ IsPGroup 2 ↥L := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥L := h2.isNilpotent
  have : Group.IsPerfect ↥L := hq.1
  have hbot : (⊤ : Subgroup ↥L) = ⊥ := by
    have key : ∀ n, derivedSeries ↥L n = ⊤ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [derivedSeries_succ, ih, ← commutator_def ↥L, Group.IsPerfect.commutator_eq_top]
    obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := ↥L)
    rw [← key n, hn]
  have := FFL.nontrivial_of_isQuasisimple hq
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥L
  exact hab (by
    have ha : a ∈ (⊥ : Subgroup ↥L) := hbot ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥L) := hbot ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb])

variable {Γ L : Subgroup (MulAut V)}

theorem ffJ_facts (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hq : CFSG.IsQuasisimple ↥L) (hLΓ : L ≤ Γ)
    (hΓL : Γ ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : ∀ x ∈ Γ, x ∈ Subgroup.centralizer (L : Set (MulAut V)) → x ^ 2 = 1 → x = 1)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    L ≤ ffJ Γ ∧ B53Hyp (ffJ Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJΓ := FFL.ffJ_le Γ
  have hCS : ∀ y ∈ Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)), y ^ 2 = 1 → y = 1 :=
    fun y hy => hC y hy.1 hy.2
  have hLJ : L ≤ ffJ Γ := by
    rcases le_or_le_centralizer hq (hLΓ.trans (FFL.le_normalizer_ffJ Γ)) (hJΓ.trans hΓL) with
      h | h
    · exact h
    · exfalso
      obtain ⟨A, hA⟩ := hoff
      obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
      have haJ : a ∈ ffJ Γ := B19.le_ffJ hA haA
      exact ha1 (Subtype.ext (hC a (hJΓ haJ) (h haJ) (hA.2.2.1.2 a haA)))
  refine ⟨hLJ, ?_, (FFL.ffJ_ffJ Γ).symm, ?_⟩
  · have hP := pCoreOf_le 2 (ffJ Γ)
    rcases le_or_le_centralizer hq (hLJ.trans (le_normalizer_pCoreOf 2 _))
      ((hP.trans hJΓ).trans hΓL) with h | h
    · exact absurd ((pCoreOf_isPGroup 2 (ffJ Γ)).to_le h) (not_isPGroup_of_isQuasisimple hq)
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (ffJ Γ)) ⟨x, hx⟩
      rw [Subgroup.mem_bot]
      exact eq_one_of_pow_two_pow_of_noInv hCS ⟨hJΓ (hP hx), h hx⟩
        (by simpa using congrArg Subtype.val hk)
  · obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := G64.isQuotientOfSQTKCat_of_le hJΓ hQ
    exact ⟨Y, inferInstance, inferInstance, N, inferInstance, G64.sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

theorem false_of_two_dvd {X : Subgroup (MulAut V)} (hXΓ : X ≤ Γ)
    (hXC : X ≤ Subgroup.centralizer (L : Set (MulAut V)))
    (hC : ∀ x ∈ Γ, x ∈ Subgroup.centralizer (L : Set (MulAut V)) → x ^ 2 = 1 → x = 1)
    (h2 : 2 ∣ Nat.card ↥X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2
  have h1 : ((x : MulAut V)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have h3 := hC _ (hXΓ x.2) (hXC x.2) h1
  have : x = 1 := Subtype.ext h3
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem two_dvd_card_of_factorList {X : Type} [Group X] (h : B56FactorList X) :
    2 ∣ Nat.card X := by
  rcases h with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | he | ⟨m, K, _, _, hm, -, hK, ⟨e⟩⟩
  · have := Fintype.ofFinite K
    rw [Nat.card_congr e.toEquiv, FFL.card_statedSL_two, ← Nat.card_eq_fintype_card, hK]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · have := Fintype.ofFinite K
    rw [Nat.card_congr e.toEquiv, FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hK]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _

theorem fstar_ffJ_eq (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hq : CFSG.IsQuasisimple ↥L) (hLΓ : L ≤ Γ)
    (hΓL : Γ ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : ∀ x ∈ Γ, x ∈ Subgroup.centralizer (L : Set (MulAut V)) → x ^ 2 = 1 → x = 1)
    (hcard : 360 < Nat.card ↥L) (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    L ≤ ffJ Γ ∧ quasithinGenFitting (ffJ Γ) = L ∧ B51Conclusion (ffJ Γ) L := by
  obtain ⟨hLJ, hB⟩ := ffJ_facts hQ hq hLΓ hΓL hC hoff
  have hJΓ := FFL.ffJ_le Γ
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := FFL.nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hJ1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLJ))
  have hdich : ∀ X ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (X : Set (MulAut V)) →
      L ≤ X ∨ X ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun X hX hJX =>
    le_or_le_centralizer hq (hLJ.trans hJX) ((hX.trans hJΓ).trans hΓL)
  have hcardle : ∀ {X : Subgroup (MulAut V)}, L ≤ X → Nat.card ↥L ≤ Nat.card ↥X :=
    fun h => Subgroup.card_le_of_le h
  rcases h56 V hV (ffJ Γ) hJ1 hB with ⟨hqF, hconc, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hcomm, h₁, h₂, -⟩ |
      ⟨G₁, G₂, t, hG, -, hcomm, ⟨e⟩, -, -, -, -, -, -, ht₁, -, -, -⟩ |
      ⟨G₁, G₂, hsup, -, hcomm, -, ⟨e⟩, -, -, -⟩
  ·
    have hF := quasithinGenFitting_le (ffJ Γ)
    have hJF : ffJ Γ ≤ Subgroup.normalizer (quasithinGenFitting (ffJ Γ) : Set (MulAut V)) :=
      le_normalizer_quasithinGenFitting _
    have hLF : L ≤ quasithinGenFitting (ffJ Γ) := by
      rcases hdich _ hF hJF with h | h
      · exact h
      · intro l hl
        exact centralizer_quasithinGenFitting_le (ffJ Γ) ⟨hLJ hl,
          Subgroup.mem_centralizer_iff.2 fun y hy =>
            ((Subgroup.mem_centralizer_iff.1 (h hy)) l hl).symm⟩
    have hFL := FFL.eq_of_isQuasisimple hq hqF hLF ((hF.trans hJΓ).trans hΓL)
    rw [hFL] at hconc
    exact ⟨hLJ, hFL, hconc⟩
  ·
    exfalso
    have h6 : Nat.card ↥(ffJ Γ) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := hcardle hLJ
    omega
  ·
    exfalso
    have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
    have hn₁ : ffJ Γ ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
      hsup.symm.le.trans (FFL.sup_le_normalizer hcomm)
    have hn₂ : ffJ Γ ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
      hsup.symm.le.trans ((sup_comm G₁ G₂).le.trans (FFL.sup_le_normalizer hcomm'))
    have hG₁J : G₁ ≤ ffJ Γ := le_sup_left.trans hsup.le
    have hG₂J : G₂ ≤ ffJ Γ := le_sup_right.trans hsup.le
    rcases hdich G₁ hG₁J hn₁ with hL₁ | hC₁
    · rcases hdich G₂ hG₂J hn₂ with hL₂ | hC₂
      · exact hL1 (le_bot_iff.mp (hinf ▸ le_inf hL₁ hL₂))
      · exact false_of_two_dvd (hG₂J.trans hJΓ) hC₂ hC (two_dvd_card_of_factorList h₂)
    · exact false_of_two_dvd (hG₁J.trans hJΓ) hC₁ hC (two_dvd_card_of_factorList h₁)
  ·
    exfalso
    have hG₁J : G₁ ≤ ffJ Γ := (le_sup_left.trans le_sup_left).trans hG.symm.le
    have hn : ffJ Γ ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
      rw [hG]
      refine sup_le (FFL.sup_le_normalizer hcomm) ?_
      rw [Subgroup.zpowers_le]
      exact ht₁
    have h360 : Nat.card ↥G₁ = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    rcases hdich G₁ hG₁J hn with hL₁ | hC₁
    · have := hcardle hL₁
      omega
    · exact false_of_two_dvd (hG₁J.trans hJΓ) hC₁ hC (by rw [h360]; norm_num)
  ·
    exfalso
    have hn₁ : ffJ Γ ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
      hsup.symm.le.trans (FFL.sup_le_normalizer hcomm)
    have hG₁J : G₁ ≤ ffJ Γ := le_sup_left.trans hsup.le
    have h168 : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e.toEquiv]
      rw [FFL.card_statedSL_three, ZMod.card]
      norm_num
    rcases hdich G₁ hG₁J hn₁ with hL₁ | hC₁
    · have := hcardle hL₁
      omega
    · exact false_of_two_dvd (hG₁J.trans hJΓ) hC₁ hC (by rw [h168]; norm_num)

end FF

end CFSG.Quasithin.H13.L1232
