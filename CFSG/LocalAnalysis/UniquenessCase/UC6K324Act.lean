module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Red
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

@[expose] def K324Simple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → CFSG.Open.IsKGroup S →
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 → ¬ 125 ∣ Nat.card S →
    ∀ s : S, orderOf s = 5 → ∀ Y : Subgroup S, Y ≤ centralizer ({s} : Set S) →
      (Y.subgroupOf (centralizer ({s} : Set S))).Normal → IsAlt ↥Y 6 → False

section Tools

variable {G : Type*} [Group G]

theorem isElemAbelian_zpowers {p : ℕ} {u : G} (hu : orderOf u = p) :
    CFSG.Open.IsElemAbelian p (zpowers u) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 b.2
    change (a : G) * b = b * a
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self u i j).eq
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu, pow_orderOf_eq_one,
      one_zpow]

theorem card_sup_of_normal_of_inf_eq_bot [Finite G] {N P : Subgroup G} [N.Normal]
    (h : N ⊓ P = ⊥) : Nat.card ↥(N ⊔ P) = Nat.card N * Nat.card P := by
  have h1 := Subgroup.relIndex_mul_card N (N ⊔ P)
  have h2 := Subgroup.relIndex_mul_card N P
  rw [Subgroup.relIndex_sup_left, inf_eq_left.2 le_sup_left] at h1
  rw [h, Subgroup.card_bot, mul_one] at h2
  rw [← h1, h2, mul_comm]

theorem exists_centralizer_of_conj_mem [Finite G] {p : ℕ} [Fact p.Prime] {R : Subgroup G}
    [R.Normal] (hR : ¬ p ∣ Nat.card R) {z : G} (hz : IsPGroup p (zpowers z)) {m : G}
    (hm : (z * m * z⁻¹)⁻¹ * m ∈ R) : ∃ c ∈ centralizer ({z} : Set G), c⁻¹ * m ∈ R := by
  have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p R hR (zpowers z) hz
  have hzm : QuotientGroup.mk' R z * QuotientGroup.mk' R m =
      QuotientGroup.mk' R m * QuotientGroup.mk' R z := by
    have h1 : QuotientGroup.mk' R (z * m * z⁻¹) = QuotientGroup.mk' R m :=
      (QuotientGroup.eq).2 hm
    rw [map_mul, map_mul, map_inv] at h1
    calc QuotientGroup.mk' R z * QuotientGroup.mk' R m
        = QuotientGroup.mk' R z * QuotientGroup.mk' R m * (QuotientGroup.mk' R z)⁻¹ *
            QuotientGroup.mk' R z := by group
      _ = QuotientGroup.mk' R m * QuotientGroup.mk' R z := by rw [h1]
  have hmem : QuotientGroup.mk' R m ∈ centralizer
      (((zpowers z).map (QuotientGroup.mk' R) : Subgroup (G ⧸ R)) : Set (G ⧸ R)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (QuotientGroup.mk' R z) (QuotientGroup.mk' R m) from hzm)
      k).eq
  rw [← h] at hmem
  obtain ⟨c, hc, hcm⟩ := hmem
  have hc' : c ∈ centralizer ((zpowers z : Subgroup G) : Set G) := hc
  refine ⟨c, ?_, (QuotientGroup.eq).1 hcm⟩
  rw [mem_centralizer_iff] at hc' ⊢
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  exact hc' w (mem_zpowers w)

theorem pPrimeCore_map_conjNormal (p : ℕ) (M : Subgroup G) [M.Normal] (g : G) :
    (CFSG.pPrimeCore p ↥M).map ((MulAut.conjNormal (H := M) g : ↥M ≃* ↥M) : ↥M →* ↥M) =
      CFSG.pPrimeCore p ↥M :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance (MulAut.conjNormal g)

@[expose] noncomputable def quotConj (p : ℕ) (M : Subgroup G) [M.Normal] :
    G →* MulAut (↥M ⧸ CFSG.pPrimeCore p ↥M) where
  toFun g :=
    QuotientGroup.congr _ _ (MulAut.conjNormal (H := M) g) (pPrimeCore_map_conjNormal p M g)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H m =>
      rw [QuotientGroup.congr_mk, map_one]
      rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H m =>
      rw [QuotientGroup.congr_mk, map_mul]
      rfl

theorem quotConj_mk (p : ℕ) (M : Subgroup G) [M.Normal] (g : G) (m : ↥M) :
    quotConj p M g (m : ↥M ⧸ CFSG.pPrimeCore p ↥M) =
      ((MulAut.conjNormal (H := M) g m : ↥M) : ↥M ⧸ CFSG.pPrimeCore p ↥M) :=
  rfl

theorem quotConj_coe (p : ℕ) (M : Subgroup G) [M.Normal] (m : ↥M) :
    quotConj p M (m : G) = MulAut.conj (m : ↥M ⧸ CFSG.pPrimeCore p ↥M) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotConj_mk, MulAut.conj_apply]
    have hy : (MulAut.conjNormal (H := M) (m : G) y : ↥M) = m * y * m⁻¹ := Subtype.ext (by simp)
    rw [hy]
    rfl

end Tools

theorem alt6_facts {G : Type} [Group G] [Finite G] {X : Subgroup G} (h : IsAlt ↥X 6) :
    IsSimpleGroup ↥X ∧ Nat.card X = 360 ∧ (∃ a b : ↥X, a * b ≠ b * a) ∧
      ∃ P : Subgroup G, P ≤ X ∧ CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 2 := by
  obtain ⟨φ⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨φ.isSimpleGroup, ?_, ?_, ?_⟩
  · rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine ⟨φ.symm ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      φ.symm ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact absurd (φ.symm.injective h) (by decide)
  · have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = 2 := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]
      exact Insp.pRank_three_alternating_six
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup ↥X)
    refine ⟨E.map X.subtype, map_subtype_le E, CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
    rw [Subgroup.card_map_of_injective X.subtype_injective, hEc, hrk]

theorem k324_of_simple (hS : K324Simple) (hO : KOutP) : K324 := by
  intro G _ _ hK hrk E hE _ hEc Z _ hZc hX h3
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := centralizer (Z : Set G) with hC
  set X := (genFittingLayer ↥C).map C.subtype with hXdef
  obtain ⟨hXs, hX360, hnab, P, hPX, hP, hPc⟩ := alt6_facts hX
  obtain ⟨φ⟩ := hX
  have h125 : ¬ 125 ∣ Nat.card G := by
    intro hdvd
    have hE' := hE.card_eq
    rw [hEc, Subgroup.card_top] at hE'
    have hv : (Nat.card G).factorization 5 = 2 := by
      have h1 : 5 ^ (Nat.card G).factorization 5 = 5 ^ 2 := by rw [← hE']; norm_num
      exact Nat.pow_right_injective (by norm_num) h1
    have h53 : 5 ^ 3 ∣ Nat.card G := by norm_num; exact hdvd
    have h3le : 3 ≤ (Nat.card G).factorization 5 :=
      (Nat.prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h53
    omega
  have hPc' : Nat.card P = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by rw [hPc, hrk]
  have h3X : 3 ∣ Nat.card X := by rw [hX360]; norm_num
  have h5X : 5 ∣ Nat.card X := by rw [hX360]; norm_num
  have hXC : X ≤ C := map_subtype_le _
  have hXnC : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hc x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hLn : (genFittingLayer ↥C).Normal := CFSG.ComponentClassification.Layer.normal ↥C
    exact ⟨⟨c, hc⟩ * x' * ⟨c, hc⟩⁻¹, hLn.conj_mem x' hx' _, by simp⟩
  have hZX : ∀ a ∈ Z, ∀ x ∈ X, a * x = x * a := fun a ha x hx =>
    mem_centralizer_iff.1 (hXC hx) a ha
  have hXcen : ∀ b ∈ X, (∀ x ∈ X, b * x = x * b) → b = 1 := by
    intro b hb hbc
    have hcen : (⟨b, hb⟩ : X) ∈ center ↥X :=
      mem_center_iff.2 fun g => Subtype.ext (hbc g g.2).symm
    haveI := hXs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥X) with h | h
    · rw [h, mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · exfalso
      obtain ⟨a, c, hac⟩ := hnab
      have h1 : a ∈ center ↥X := by rw [h]; exact mem_top _
      exact hac (mem_center_iff.1 h1 c).symm
  set N := normalClosure (Z : Set G) with hN
  have hXN : X ≤ N := le_of_dvd_card hXs hPX hP hPc' (fun x _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : N.Normal)]
    exact mem_top x) h3
  set M := normalClosure (X : Set G) with hM
  set R₀ := CFSG.pPrimeCore 3 ↥M with hR₀
  set RG := R₀.map M.subtype with hRG
  haveI hRGn : RG.Normal := normal_map_pPrimeCore 3 M
  haveI hSs : IsSimpleGroup (↥M ⧸ R₀) := isSimpleGroup_normalClosure_quot hXs hPX hP hPc' h3X
  have hXM : X ≤ M := le_normalClosure
  have hRGmem : ∀ m : ↥M, (m : G) ∈ RG ↔ m ∈ R₀ := fun m =>
    Subgroup.mem_map_iff_mem M.subtype_injective
  have hRGM : RG ≤ M := map_subtype_le _
  have hXR : ∀ x ∈ X, x ∈ RG → x = 1 := fun x hx hxR =>
    eq_one_of_mem_pPrimeCore hXs h3X hx ((hRGmem ⟨x, hXM hx⟩).1 hxR)
  set ι : ↥X →* ↥M ⧸ R₀ := (QuotientGroup.mk' R₀).comp (Subgroup.inclusion hXM) with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact Subtype.ext (hXR x x.2 ((hRGmem _).2 hx))
  set Xb := ι.range with hXb
  have hXbalt : IsAlt ↥Xb 6 := ⟨(MonoidHom.ofInjective hιinj).symm.trans φ⟩
  have hXbcard : Nat.card Xb = 360 := by
    rw [← hX360]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
  have hS3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ R₀)) ≤ 2 :=
    (pRank_normalClosure_quot_le 3 X).trans hrk.le
  have hKS : CFSG.Open.IsKGroup (↥M ⧸ R₀) := (hK.subgroup M).quotient R₀
  have hSdvd : Nat.card (↥M ⧸ R₀) ∣ Nat.card G :=
    (Subgroup.card_quotient_dvd_card R₀).trans (Subgroup.card_subgroup_dvd_card M)
  have h125S : ¬ 125 ∣ Nat.card (↥M ⧸ R₀) := fun h => h125 (h.trans hSdvd)
  have h5S : 5 ∣ Nat.card (↥M ⧸ R₀) :=
    (show 5 ∣ Nat.card Xb by rw [hXbcard]; norm_num).trans (Subgroup.card_subgroup_dvd_card Xb)
  have hSnab : ∀ w : ↥M ⧸ R₀, (∀ t, w * t = t * w) → w = 1 := by
    intro w hw
    have hcen : w ∈ center (↥M ⧸ R₀) := mem_center_iff.2 fun t => (hw t).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥M ⧸ R₀)) with h | h
    · rw [h, mem_bot] at hcen
      exact hcen
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      apply hιinj
      have h1 : ι a ∈ center (↥M ⧸ R₀) := by rw [h]; exact mem_top _
      rw [map_mul, map_mul, mem_center_iff.1 h1 (ι b)]
  obtain ⟨z, hzZ⟩ : ∃ z : G, Z = zpowers z := by
    haveI : IsCyclic Z := isCyclic_of_prime_card hZc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
    refine ⟨g, le_antisymm (fun x hx => ?_) (zpowers_le.2 g.2)⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact mem_zpowers_iff.2 ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hzo : orderOf z = 5 := by rw [← Nat.card_zpowers, ← hzZ, hZc]
  have hzp : IsPGroup 5 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hzZ' : z ∈ Z := hzZ ▸ mem_zpowers z
  have hzX : ∀ x ∈ X, z * x = x * z := hZX z hzZ'
  set α := quotConj 3 M z with hα
  have hα5 : α ^ 5 = 1 := by rw [hα, ← map_pow, ← hzo, pow_orderOf_eq_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hZker : Z ≤ (quotConj 3 M).ker := by
      rw [hzZ, zpowers_le, MonoidHom.mem_ker]
      exact h1
    have hNker : N ≤ (quotConj 3 M).ker := normalClosure_le_normal hZker
    obtain ⟨a, b, hab⟩ := hnab
    have hker : quotConj 3 M (a : G) = 1 := hNker (hXN a.2)
    have ha : ((a : G) : G) = ((⟨a, hXM a.2⟩ : ↥M) : G) := rfl
    rw [ha, quotConj_coe] at hker
    have hcen : ∀ t : ↥M ⧸ R₀, ι a * t = t * ι a := by
      intro t
      have h2 := congrArg (fun f : MulAut (↥M ⧸ R₀) => f t) hker
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      have hιa : ι a = ((⟨a, hXM a.2⟩ : ↥M) : ↥M ⧸ R₀) := rfl
      calc ι a * t = ι a * t * (ι a)⁻¹ * ι a := by group
        _ = t * ι a := by rw [hιa, h2]
    apply hab
    apply hιinj
    have h0 : ι a = 1 := hSnab _ hcen
    rw [map_mul, map_mul, h0, one_mul, mul_one]
  have hαo : orderOf α = 5 := orderOf_eq_prime hα5 hα1
  have hZXinf : ∀ a ∈ Z, a ∈ X → a = 1 := fun a ha haX =>
    hXcen a haX fun x hx => hZX a ha x hx
  obtain ⟨y, hyX, hyo⟩ : ∃ y ∈ X, orderOf y = 5 := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5X
    exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  have hR5 : ¬ 5 ∣ Nat.card RG := by
    intro h5
    set P5 := Z ⊔ zpowers y with hP5
    have hcomm : ∀ a ∈ Z, ∀ b ∈ zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a y from hZX a ha y hyX) k).eq
    have hZel : CFSG.Open.IsElemAbelian 5 Z := by rw [hzZ]; exact isElemAbelian_zpowers hzo
    have hP5el : CFSG.Open.IsElemAbelian 5 P5 :=
      hZel.sup_of_commute (isElemAbelian_zpowers hyo) hcomm
    have hyZ : y ∉ Z := fun h => by
      rw [hZXinf y h hyX, orderOf_one] at hyo
      omega
    have hP5card : 25 ∣ Nat.card P5 := by
      obtain ⟨k, hk⟩ := hP5el.isPGroup.exists_card_eq
      have hlt : Nat.card Z < Nat.card P5 := by
        by_contra hle
        push Not at hle
        have heq : Z = P5 := eq_of_le_of_card_ge le_sup_left hle
        have hmem : y ∈ P5 := mem_sup_right (mem_zpowers y)
        rw [← heq] at hmem
        exact hyZ hmem
      rw [hZc, hk] at hlt
      have hk2 : 2 ≤ k := by
        by_contra h2
        push Not at h2
        interval_cases k <;> norm_num at hlt
      rw [hk, show (25 : ℕ) = 5 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 5 hk2
    by_cases hbot : RG ⊓ P5 = ⊥
    · apply h125
      have hc := card_sup_of_normal_of_inf_eq_bot hbot
      have h1 : 125 ∣ Nat.card ↥(RG ⊔ P5) := by
        rw [hc, show (125 : ℕ) = 5 * 25 by norm_num]
        exact Nat.mul_dvd_mul h5 hP5card
      exact h1.trans (Subgroup.card_subgroup_dvd_card _)
    · obtain ⟨w, hw, hw1⟩ : ∃ w ∈ RG ⊓ P5, w ≠ 1 := by
        by_contra h0
        push Not at h0
        exact hbot (eq_bot_iff.2 fun w hw => (mem_bot).2 (h0 w hw))
      have hyC : zpowers y ≤ centralizer (Z : Set G) :=
        zpowers_le.2 (mem_centralizer_iff.2 fun a ha => hZX a ha y hyX)
      have hzN : zpowers y ≤ normalizer (Z : Set G) :=
        hyC.trans (Subgroup.centralizer_le_normalizer _)
      have hwP5 : w ∈ ((Z : Set G) * (zpowers y : Set G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Z (zpowers y) hzN]
        exact (mem_inf.1 hw).2
      obtain ⟨a, ha, b, hb, hab0⟩ := hwP5
      have hab : a * b = w := hab0
      have hwR : w ∈ RG := (mem_inf.1 hw).1
      have hbX : b ∈ X := (zpowers_le.2 hyX) hb
      have hbc : ∀ x ∈ X, b * x = x * b := by
        intro x hx
        have hbw : b = a⁻¹ * w := by rw [← hab]; group
        have hxa : a * x = x * a := hZX a ha x hx
        have hxa' : a * x⁻¹ = x⁻¹ * a := by
          calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
            _ = x⁻¹ * (a * x) * x⁻¹ := by rw [hxa]
            _ = x⁻¹ * a := by group
        have h1 : x * w⁻¹ * x⁻¹ ∈ RG := hRGn.conj_mem _ (RG.inv_mem hwR) x
        have h2 : w * (x * w⁻¹ * x⁻¹) ∈ RG := RG.mul_mem hwR h1
        have h3' : a⁻¹ * (w * (x * w⁻¹ * x⁻¹)) * a⁻¹⁻¹ ∈ RG := hRGn.conj_mem _ h2 a⁻¹
        have e : b * x * b⁻¹ * x⁻¹ = a⁻¹ * (w * (x * w⁻¹ * x⁻¹)) * a⁻¹⁻¹ := by
          rw [hbw]
          calc a⁻¹ * w * x * (a⁻¹ * w)⁻¹ * x⁻¹ = a⁻¹ * w * x * w⁻¹ * (a * x⁻¹) := by group
            _ = a⁻¹ * w * x * w⁻¹ * (x⁻¹ * a) := by rw [hxa']
            _ = a⁻¹ * (w * (x * w⁻¹ * x⁻¹)) * a⁻¹⁻¹ := by group
        have hcomR : b * x * b⁻¹ * x⁻¹ ∈ RG := e ▸ h3'
        have hcomX : b * x * b⁻¹ * x⁻¹ ∈ X :=
          X.mul_mem (X.mul_mem (X.mul_mem hbX hx) (X.inv_mem hbX)) (X.inv_mem hx)
        have h4 := hXR _ hcomX hcomR
        calc b * x = b * x * b⁻¹ * x⁻¹ * (x * b) := by group
          _ = x * b := by rw [h4, one_mul]
      have hb1 : b = 1 := hXcen b hbX hbc
      rw [hb1, mul_one] at hab
      subst hab
      have hZR : Z ≤ RG := by
        have hwo : orderOf a = 5 := by
          have hdvd : orderOf a ∣ 5 := by
            rw [← hZc]
            exact Subgroup.orderOf_dvd_natCard Z ha
          rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.1 h1) hw1
          · exact h1
        have hle : zpowers a ≤ Z := zpowers_le.2 ha
        have heq : zpowers a = Z :=
          eq_of_le_of_card_ge hle (by rw [hZc, Nat.card_zpowers, hwo])
        rw [← heq, zpowers_le]
        exact hwR
      have hNR : N ≤ RG := normalClosure_le_normal hZR
      have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hyo; omega
      exact hy1 (hXR y hyX (hNR (hXN hyX)))
  have hXbfix : ∀ t ∈ Xb, α t = t := by
    intro t ht
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ht
    have hx : (MulAut.conjNormal (H := M) z (Subgroup.inclusion hXM x) : ↥M) =
        Subgroup.inclusion hXM x := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_inclusion]
      rw [hzX x x.2]
      group
    rw [hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hα, quotConj_mk, hx]
  have hfixnorm : ∀ t : ↥M ⧸ R₀, α t = t → ∀ u ∈ Xb, t * u * t⁻¹ ∈ Xb := by
    intro t ht u hu
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hu
    rw [hα, quotConj_mk, QuotientGroup.eq] at ht
    have hmG : (z * (m : G) * z⁻¹)⁻¹ * m ∈ RG := by
      have h1 := (hRGmem _).2 ht
      simpa [MulAut.conjNormal_apply] using h1
    obtain ⟨c, hc, hcm⟩ := exists_centralizer_of_conj_mem hR5 hzp hmG
    have hcM : c ∈ M := by
      have e : c = m * (c⁻¹ * m)⁻¹ := by group
      rw [e]
      exact M.mul_mem m.2 (M.inv_mem (hRGM hcm))
    have hcC : c ∈ C := by
      rw [hC, hzZ, mem_centralizer_iff]
      intro a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      have hzc : z * c = c * z := mem_centralizer_iff.1 hc z (Set.mem_singleton z)
      exact (Commute.zpow_left (show Commute z c from hzc) k).eq
    have hmc : ((m : ↥M) : ↥M ⧸ R₀) = ((⟨c, hcM⟩ : ↥M) : ↥M ⧸ R₀) := by
      rw [QuotientGroup.eq, ← hRGmem]
      have e : ((m⁻¹ * ⟨c, hcM⟩ : ↥M) : G) = (c⁻¹ * m)⁻¹ := by simp
      rw [e]
      exact RG.inv_mem hcm
    rw [hmc]
    refine MonoidHom.mem_range.2 ⟨⟨c * x * c⁻¹, hXnC c hcC x x.2⟩, ?_⟩
    rw [hι, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
  by_cases hinn : α ∈ (MulAut.conj : (↥M ⧸ R₀) →* MulAut (↥M ⧸ R₀)).range
  ·
    obtain ⟨s, hs⟩ := hinn
    have hs5 : s ^ 5 = 1 := by
      have h1 : MulAut.conj (s ^ 5) = 1 := by rw [map_pow, hs, hα5]
      apply hSnab
      intro t
      have h2 := congrArg (fun f : MulAut (↥M ⧸ R₀) => f t) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc s ^ 5 * t = s ^ 5 * t * (s ^ 5)⁻¹ * s ^ 5 := by group
        _ = t * s ^ 5 := by rw [h2]
    have hs1 : s ≠ 1 := fun h => hα1 (by rw [← hs, h, map_one])
    have hso : orderOf s = 5 := orderOf_eq_prime hs5 hs1
    have hXbC : Xb ≤ centralizer ({s} : Set (↥M ⧸ R₀)) := by
      intro u hu
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h1 := hXbfix u hu
      rw [← hs, MulAut.conj_apply] at h1
      calc w * u = w * u * w⁻¹ * w := by group
        _ = u * w := by rw [h1]
    refine hS _ hSs hKS hS3 h125S s hso Xb hXbC ⟨fun n hn g => ?_⟩ hXbalt
    rw [mem_subgroupOf] at hn ⊢
    have hg : α g = g := by
      have hgc := mem_centralizer_iff.1 g.2 s (Set.mem_singleton s)
      rw [← hs, MulAut.conj_apply]
      calc s * (g : ↥M ⧸ R₀) * s⁻¹ = (g : ↥M ⧸ R₀) * s * s⁻¹ := by rw [hgc]
        _ = g := by group
    have h1 := hfixnorm g hg n hn
    simpa using h1
  ·
    have hzM : z ∉ M := by
      intro hz
      apply hinn
      refine ⟨((⟨z, hz⟩ : ↥M) : ↥M ⧸ R₀), ?_⟩
      rw [hα]
      exact (quotConj_coe 3 M ⟨z, hz⟩).symm
    have hMZ : M ⊓ Z = ⊥ := by
      have hdvd : Nat.card ↥(M ⊓ Z) ∣ 5 := hZc ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : M ⊓ Z = Z := eq_of_le_of_card_ge inf_le_right (by rw [h1, hZc])
        have hz' : z ∈ Z := hzZ'
        rw [← heq] at hz'
        exact hzM (mem_inf.1 hz').1
    have h25 : ¬ 25 ∣ Nat.card (↥M ⧸ R₀) := by
      intro h25
      apply h125
      have hc := card_sup_of_normal_of_inf_eq_bot hMZ
      have h1 : 25 ∣ Nat.card M := h25.trans (Subgroup.card_quotient_dvd_card R₀)
      have h2 : 125 ∣ Nat.card ↥(M ⊔ Z) := by
        rw [hc, hZc, show (125 : ℕ) = 25 * 5 by norm_num]
        exact Nat.mul_dvd_mul_right h1 5
      exact h2.trans (Subgroup.card_subgroup_dvd_card _)
    set yb := ι ⟨y, hyX⟩ with hyb
    have hybo : orderOf yb = 5 := by rw [hyb, orderOf_injective ι hιinj, Subgroup.orderOf_mk, hyo]
    have hfac : (Nat.card (↥M ⧸ R₀)).factorization 5 = 1 := by
      have h1 : 1 ≤ (Nat.card (↥M ⧸ R₀)).factorization 5 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_five Nat.card_pos.ne' h5S
      have h2 : (Nat.card (↥M ⧸ R₀)).factorization 5 < 2 := by
        by_contra h
        push Not at h
        exact h25 (by
          have := (Nat.prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h
          simpa using this)
      omega
    have hT : CFSG.ABGLocalTools.IsSylowOf 5 (zpowers yb) ⊤ :=
      CFSG.ABGLocalTools.isSylowOf_of_card le_top
        (by rw [Nat.card_zpowers, hybo, Subgroup.card_top, hfac, pow_one])
    have hrk5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥M ⧸ R₀)) ≤ 3 := by
      refine CFSG.SectionRank.pRank_le (by norm_num) fun E' _ hE' => ?_
      obtain ⟨k, hk⟩ := hE'.isPGroup.exists_card_eq
      have hdvd : 5 ^ k ∣ Nat.card (↥M ⧸ R₀) := hk ▸ Subgroup.card_subgroup_dvd_card E'
      have hk1 : k ≤ 1 := by
        by_contra h
        push Not at h
        exact h25 ((show (25 : ℕ) = 5 ^ 2 by norm_num) ▸ (Nat.pow_dvd_pow 5 h).trans hdvd)
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hαT : ∀ t ∈ zpowers yb, α t = t := fun t ht =>
      hXbfix t ((zpowers_le.2 (MonoidHom.mem_range.2 ⟨⟨y, hyX⟩, rfl⟩)) ht)
    exact hinn (hO _ hSs hKS 5 Nat.prime_five le_rfl h5S hrk5 _ hT α hαo hαT)

end CFSG.LocalAnalysis.UniquenessCase.UCK
