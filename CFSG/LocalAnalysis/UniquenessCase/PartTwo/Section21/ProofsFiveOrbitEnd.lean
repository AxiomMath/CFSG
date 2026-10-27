module

public import CFSG.GroupTheory.CyclicDiagonal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveDiagonal
import CFSG.GroupTheory.CommutingElementaryAbelian
import CFSG.GroupTheory.CoprimeLiftElementaryAbelian
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

@[expose] def orbitImage (M : Subgroup G) (a : G) (K : Subgroup G) : Subgroup (Bar2 M) :=
  ⨆ i : Fin (orderOf a), barImage M (conjugatePower a K i)

private theorem conjugatePower_zero (a : G) (L : Subgroup G) : conjugatePower a L 0 = L := by
  ext x
  rw [conjugatePower, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxy' : y = x := by simpa using hxy
    rwa [← hxy']
  · intro hx
    exact ⟨x, hx, by simp⟩

private theorem conjugatePower_self {L : Subgroup G} {a : G} {r : ℕ} (ha : a ^ r = 1) :
    conjugatePower a L r = L := by
  rw [conjugatePower_mod a L ha r, Nat.mod_self, conjugatePower_zero]

private theorem card_bar2_map_conj {M : Subgroup G} (g : G) :
    Nat.card (Bar2 (M.map (MulAut.conj g).toMonoidHom)) = Nat.card (Bar2 M) :=
  (Nat.card_congr (CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv
    (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).toEquiv).symm

private theorem center_bar2_map_conj_eq_bot {M : Subgroup G} {g : G}
    (hZ : Subgroup.center (Bar2 M) = ⊥) :
    Subgroup.center (Bar2 (M.map (MulAut.conj g).toMonoidHom)) = ⊥ := by
  refine Subgroup.eq_bot_of_card_le
    (H := Subgroup.center (Bar2 (M.map (MulAut.conj g).toMonoidHom))) ?_
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map (MulAut.conj g) M, hZ]
  simp

private theorem shape_bar2_map_conj {M : Subgroup G} {g : G}
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 M) (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 M) q) ∨ IsJ1 (Bar2 M)) :
    (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 (M.map (MulAut.conj g).toMonoidHom)) (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧
        IsL2Odd (Bar2 (M.map (MulAut.conj g).toMonoidHom)) q) ∨
      IsJ1 (Bar2 (M.map (MulAut.conj g).toMonoidHom)) := by
  let ee : Bar2 M ≃* Bar2 (M.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv
      (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  rcases hshape with ⟨k, hk1, hk⟩ | ⟨q, hq, hq5, hqL⟩ | hJ
  · exact Or.inl ⟨k, hk1, CFSG.Blueprint.LieModel.of_mulEquiv ee hk⟩
  · exact Or.inr (Or.inl ⟨q, hq, hq5, CFSG.Blueprint.LieModel.of_mulEquiv ee hqL⟩)
  · obtain ⟨f⟩ := hJ
    exact Or.inr (Or.inr ⟨ee.symm.trans f⟩)

private theorem not_dvd_card_pCore_two {M : Subgroup G} :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hn]
  intro h
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h32

private theorem exists_elemAbelian_order_nine_lift {M : Subgroup G} {a : G} (ha : a ∈ M)
    {E : Subgroup (Bar2 M)} (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hEimage : E ≤ (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :
    ∃ E' : Subgroup G, E' ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ M ∧
      IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have himage : E ≤ (Subgroup.centralizer
      (Subgroup.zpowers (⟨a, ha⟩ : ↥M) : Set ↥M)).map q := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hEimage
  obtain ⟨E₁, hE₁e, -, hE₁card, hE₁cent⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_centralizer_lift (G := ↥M) (p := 3)
      (A := Subgroup.zpowers (⟨a, ha⟩ : ↥M)) (N := CFSG.pCore 2 ↥M)
      not_dvd_card_pCore_two hE himage
  have hE₁cent' : E₁ ≤ Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hE₁cent
    exact hE₁cent
  refine ⟨E₁.map M.subtype, ?_, hE₁e.map M.subtype, ?_⟩
  · refine le_inf ?_ (Subgroup.map_subtype_le E₁)
    have h1 : E₁.map M.subtype ≤ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.map_mono hE₁cent').trans (map_centralizer_coe_le_centralizer ha)
    have h1' : E₁.map M.subtype ≤
        Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact h1
    exact h1'.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G))
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hE₁card, hEcard]

private theorem center_barImage_eq_bot {M L : Subgroup G} (hL : L ∈ calC M)
    (hZ : Subgroup.center (Bar2 L) = ⊥) : Subgroup.center ↥(barImage M L) = ⊥ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  refine Subgroup.eq_bot_of_card_le (H := Subgroup.center ↥(barImage M L)) ?_
  have hcard : Nat.card (Subgroup.center (Bar2 L)) =
      Nat.card (Subgroup.center ↥(barImage M L)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [← hcard, hZ]
  simp

private theorem exists_not_commute_of_orbitDiagonalHom {B : Subgroup G} {b : G} {r : ℕ}
    (hb : b ^ r = 1) (hcomm : ConjugatesCommute b B r) (hr : 0 < r)
    (hZ : Subgroup.center B = ⊥) {y : ↥B} (hyord : orderOf y = 3) :
    ∃ v ∈ B, ¬ Commute (orbitDiagonalHom b B r hb hcomm y) v := by
  by_contra hcon
  push Not at hcon
  have hycent : y ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    exact (commute_of_commute_orbitDiagonalHom b B r hb hcomm hr v.2 (hcon v v.2)).symm
  have hy1 : y = 1 := by simpa [hZ] using hycent
  have hone : orderOf y = 1 := by rw [hy1]; exact orderOf_one
  omega

private theorem orbitDiagonalHom_mem_orbitImage {M L : Subgroup G} {a : G} (hLM : L ≤ M)
    (haM : a ∈ M) {r : ℕ}
    (hb : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) ^ r = 1)
    (hcomm : ConjugatesCommute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩)
      (barImage M L) r) (hr : r = orderOf a) {y : ↥(barImage M L)} :
    orbitDiagonalHom (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) (barImage M L) r
      hb hcomm y ∈ orbitImage M a L := by
  subst hr
  change (List.ofFn (orbitDiagonalFactor
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) (orderOf a) y)).prod ∈ orbitImage M a L
  refine Subgroup.list_prod_mem (K := orbitImage M a L) fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ x).1 hx
  refine Subgroup.mem_iSup_of_mem i ?_
  rw [barImage_conjugatePower hLM haM (i : ℕ)]
  exact orbitDiagonalFactor_mem_conjugatePower _ _ _ _ i

theorem exists_three_diagonal {M L : Subgroup G} {a : G} (hL : L ∈ calC M) (haM : a ∈ M)
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haL : a ∉ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (Bar2 L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 L)) :
    ∃ u : Bar2 M, orderOf u = 3 ∧
      u ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ∧
      u ∈ orbitImage M a L ∧ ∃ v ∈ barImage M L, ¬ Commute u v := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let abar : ↥M := ⟨a, haM⟩
  have hqord : q abar ^ orderOf a = 1 := mk_pow_orderOf_eq_one haM
  have hcc : ConjugatesCommute (q abar) (barImage M L) (orderOf a) :=
    conjugatesCommute_barImage hL haM hr haL
  let δ : ↥(barImage M L) →* Bar2 M :=
    orbitDiagonalHom (q abar) (barImage M L) (orderOf a) hqord hcc
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  have hZbar : Subgroup.center ↥(barImage M L) = ⊥ := center_barImage_eq_bot hL hZ
  have hker : δ.ker = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hZbar]
    exact orbitDiagonalHom_ker_le_center (q abar) (barImage M L) (orderOf a) hqord hcc hr.pos
  have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).mp hker
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 L) 3 h3
  let y' : ↥(barImage M L) := e y
  have hy'ord : orderOf y' = 3 := by
    rw [show orderOf y' = orderOf y from orderOf_injective e.toMonoidHom e.injective y, hyord]
  let u : Bar2 M := δ y'
  have huord : orderOf u = 3 := by
    rw [show orderOf u = orderOf y' from orderOf_injective δ hinj y', hy'ord]
  refine ⟨u, huord, ?_, ?_, ?_⟩
  · rw [← centralizer_mk_eq_map_centralizer_bar2 haM hr hr2]
    exact orbitDiagonalHom_mem_centralizer (q abar) (barImage M L) (orderOf a) hqord hcc y'
  · exact orbitDiagonalHom_mem_orbitImage hLM haM hqord hcc rfl
  · exact exists_not_commute_of_orbitDiagonalHom hqord hcc hr.pos hZbar hy'ord

private theorem exists_three_of_centralizes_barImage {M L : Subgroup G} {a : G}
    (hL : L ∈ calC M) (haM : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (hZB : Subgroup.center ↥(barImage M L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 L))
    (hcent : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ ∈
      Subgroup.centralizer (barImage M L : Set (Bar2 M))) :
    ∃ u : Bar2 M, orderOf u = 3 ∧
      u ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ∧
      u ∈ barImage M L ∧ ∃ v ∈ barImage M L, ¬ Commute u v := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 L) 3 h3
  let y' : ↥(barImage M L) := e y
  have hy'ord : orderOf y' = 3 := by
    rw [show orderOf y' = orderOf y from orderOf_injective e.toMonoidHom e.injective y, hyord]
  let u : Bar2 M := y'
  have huord : orderOf u = 3 := by
    rw [show orderOf u = orderOf y' from Subgroup.orderOf_coe y', hy'ord]
  refine ⟨u, huord, ?_, y'.2, ?_⟩
  · rw [← centralizer_mk_eq_map_centralizer_bar2 haM hr hr2]
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (y' : Bar2 M) * (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨a, haM⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨a, haM⟩ * (y' : Bar2 M)
    exact Subgroup.mem_centralizer_iff.mp hcent y' y'.2
  · by_contra hcon
    push Not at hcon
    have hy'cent : y' ∈ Subgroup.center ↥(barImage M L) := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      exact (hcon v v.2).symm
    have hy'1 : y' = 1 := by simpa [hZB] using hy'cent
    have hone : orderOf y' = 1 := by rw [hy'1]; exact orderOf_one
    omega

private theorem exists_mulAut_of_mem_normalizer {M L' : Subgroup G} {a : G}
    (hL'M : L' ≤ M) (haM : a ∈ M) (haN : a ∈ Subgroup.normalizer (L' : Set G)) :
    ∃ θ : MulAut ↥(barImage M L'), θ ^ orderOf a = 1 ∧
      ∀ b : ↥(barImage M L'),
        ((θ b : ↥(barImage M L')) : Bar2 M) =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) * (b : Bar2 M) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩)⁻¹ := by
  classical
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let abar : ↥M := ⟨a, haM⟩
  have hqord : q abar ^ orderOf a = 1 := mk_pow_orderOf_eq_one haM
  have hnorm : q abar ∈ Subgroup.normalizer (barImage M L' : Set (Bar2 M)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : conjugatePower a L' 1 = L' := by
      rw [conjugatePower]
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
    have h2 := barImage_conjugatePower hL'M haM 1
    rw [h1] at h2
    simpa [conjugatePower, q, abar] using h2.symm
  let θ : MulAut ↥(barImage M L') :=
    Subgroup.normalizerMonoidHom (barImage M L') ⟨q abar, hnorm⟩
  refine ⟨θ, ?_, ?_⟩
  · have harg : (⟨q abar, hnorm⟩ :
        ↥(Subgroup.normalizer (barImage M L' : Set (Bar2 M)))) ^ orderOf a = 1 := by
      apply Subtype.ext
      show (q abar) ^ orderOf a = 1
      exact hqord
    change (Subgroup.normalizerMonoidHom (barImage M L') ⟨q abar, hnorm⟩) ^ orderOf a = 1
    rw [← map_pow, harg, map_one]
  · intro b
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe (barImage M L')
      ⟨q abar, hnorm⟩ b
    simpa [θ, q, abar] using h

private theorem centralizes_of_aut_eq_one {M L' : Subgroup G} {a : G} (haM : a ∈ M)
    {θ : MulAut ↥(barImage M L')} (hθ1 : θ = 1)
    (hθcoe : ∀ b : ↥(barImage M L'),
      ((θ b : ↥(barImage M L')) : Bar2 M) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) * (b : Bar2 M) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩)⁻¹) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ ∈
      Subgroup.centralizer (barImage M L' : Set (Bar2 M)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hfix := congrArg (fun f : MulAut ↥(barImage M L') => f ⟨b, hb⟩) hθ1
  have hcoe := hθcoe ⟨b, hb⟩
  have hb' : b = (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) * b *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩)⁻¹ := by
    rw [← hcoe]
    simpa using (congrArg Subtype.val hfix).symm
  have hqb : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) * b =
      b * (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩) := by
    have h := congrArg (fun x => x * (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩)) hb'
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  exact hqb.symm

private theorem exists_conj_of_kOut {M L' : Subgroup G} {a : G} (hL' : L' ∈ calC M)
    {θ : MulAut ↥(barImage M L')} (hθr : θ ^ orderOf a = 1)
    (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2) (hKOut : KOddOutInner)
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 L') (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L') q) ∨ IsJ1 (Bar2 L')) :
    ∃ (e : Bar2 L' ≃* ↥(barImage M L')) (g : Bar2 L'),
      MulAut.conj g = (MulAut.congr e).symm θ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL'
  let θ' : MulAut (Bar2 L') := (MulAut.congr e).symm θ
  have hθ'r : θ' ^ orderOf a = 1 := by
    rw [show θ' ^ orderOf a =
      (MulAut.congr e).symm.toMonoidHom (θ ^ orderOf a) from
      (map_pow ((MulAut.congr e).symm).toMonoidHom θ (orderOf a)).symm, hθr, map_one]
  have hdvd : orderOf θ' ∣ orderOf a := orderOf_dvd_of_pow_eq_one hθ'r
  have hodd : Odd (orderOf θ') := (hr.odd_of_ne_two hr2).of_dvd_nat hdvd
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hKOut (Bar2 L') hshape θ' hodd)
  exact ⟨e, g, hg⟩

private theorem pow_eq_one_of_conj_pow_eq_one {Q : Type*} [Group Q] {g : Q} {r : ℕ}
    {θ : MulAut Q} (hg : MulAut.conj g = θ) (hθr : θ ^ r = 1)
    (hZ : Subgroup.center Q = ⊥) : g ^ r = 1 := by
  have hmem : g ^ r ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : MulAut.conj (g ^ r) = 1 := by rw [map_pow, hg, hθr]
    have hw : MulAut.conj (g ^ r) w = w := by rw [h1]; rfl
    rw [MulAut.conj_apply] at hw
    have hw' : (g ^ r) * w = w * (g ^ r) := by
      have h := congrArg (fun x => x * (g ^ r)) hw
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    exact hw'.symm
  simpa [hZ] using hmem

private theorem aut_eq_one_of_conj {M L' : Subgroup G} {a : G}
    {e : Bar2 L' ≃* ↥(barImage M L')} {θ : MulAut ↥(barImage M L')} {g : Bar2 L'}
    (hg : MulAut.conj g = (MulAut.congr e).symm θ) (hθr : θ ^ orderOf a = 1)
    (hr : (orderOf a).Prime) (hZ' : Subgroup.center (Bar2 L') = ⊥)
    (hr' : ¬ orderOf a ∣ Nat.card (Bar2 L')) : θ = 1 := by
  by_contra hθ1
  let θ' : MulAut (Bar2 L') := (MulAut.congr e).symm θ
  have hg' : MulAut.conj g = θ' := hg
  have hθ'r : θ' ^ orderOf a = 1 := by
    rw [show θ' ^ orderOf a =
      (MulAut.congr e).symm.toMonoidHom (θ ^ orderOf a) from
      (map_pow ((MulAut.congr e).symm).toMonoidHom θ (orderOf a)).symm, hθr, map_one]
  have hgne : g ≠ 1 := by
    intro hg1
    apply hθ1
    have hθ'1 : θ' = 1 := by rw [← hg', hg1, map_one]
    have hθeq : θ = (MulAut.congr e) θ' := by
      rw [show θ' = (MulAut.congr e).symm θ from rfl]
      exact (MulEquiv.apply_symm_apply (MulAut.congr e) θ).symm
    rw [hθeq, hθ'1, map_one]
  have hgr : g ^ orderOf a = 1 := pow_eq_one_of_conj_pow_eq_one hg' hθ'r hZ'
  have hdvdg : orderOf g ∣ orderOf a := orderOf_dvd_of_pow_eq_one hgr
  have hordg : orderOf g = orderOf a := by
    rcases (Nat.dvd_prime hr).mp hdvdg with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hgne
    · exact h
  exact absurd (hordg ▸ orderOf_dvd_natCard g) hr'

theorem exists_three_of_mem_normalizer {M L' : Subgroup G} {a : G}
    (hL' : L' ∈ calC M) (haM : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (haN : a ∈ Subgroup.normalizer (L' : Set G))
    (hZ' : Subgroup.center (Bar2 L') = ⊥) (h3' : 3 ∣ Nat.card (Bar2 L'))
    (hr' : ¬ orderOf a ∣ Nat.card (Bar2 L')) (hKOut : KOddOutInner)
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 L') (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L') q) ∨ IsJ1 (Bar2 L')) :
    ∃ u : Bar2 M, orderOf u = 3 ∧
      u ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ∧
      u ∈ orbitImage M a L' ∧ ∃ v ∈ barImage M L', ¬ Commute u v := by
  classical
  have hL'M : L' ≤ M := CFSG.Quasithin.A3.subnormal_le hL'.1
  obtain ⟨θ, hθr, hθcoe⟩ := exists_mulAut_of_mem_normalizer hL'M haM haN
  by_cases hθ1 : θ = 1
  · have hcent := centralizes_of_aut_eq_one haM hθ1 hθcoe
    obtain ⟨u, huord, huC, huB, hv⟩ :=
      exists_three_of_centralizes_barImage hL' haM hr hr2
        (center_barImage_eq_bot hL' hZ') h3' hcent
    refine ⟨u, huord, huC, ?_, hv⟩
    refine Subgroup.mem_iSup_of_mem ⟨0, hr.pos⟩ ?_
    rw [show conjugatePower a L' 0 = L' from conjugatePower_zero a L']
    exact huB
  · obtain ⟨e, g, hg⟩ := exists_conj_of_kOut hL' hθr hr hr2 hKOut hshape
    exact absurd (aut_eq_one_of_conj hg hθr hr hZ' hr') hθ1

theorem commute_orbitImage_of_not_mem_range {M L L' : Subgroup G} {a : G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (haM : a ∈ M)
    (hne : L' ∉ Set.range (fun i : Fin (orderOf a) => conjugatePower a L i)) :
    ∀ x ∈ orbitImage M a L, ∀ y ∈ orbitImage M a L', x * y = y * x := by
  classical
  have hrpos : 0 < orderOf a := orderOf_pos a
  have hself : conjugatePower a L' (orderOf a) = L' :=
    conjugatePower_self (pow_orderOf_eq_one a)
  have hdistinct : ∀ i j : Fin (orderOf a),
      conjugatePower a L i ≠ conjugatePower a L' j := by
    intro i j hij
    apply hne
    have hm := congrArg (fun K : Subgroup G =>
      K.map (MulAut.conj (a ^ (orderOf a - (j : ℕ)))).toMonoidHom) hij
    rw [← conjugatePower_add a L (orderOf a - (j : ℕ)) i,
      ← conjugatePower_add a L' (orderOf a - (j : ℕ)) j] at hm
    rw [Nat.sub_add_cancel (le_of_lt j.isLt), hself] at hm
    refine ⟨⟨((orderOf a - (j : ℕ)) + (i : ℕ)) % orderOf a, Nat.mod_lt _ hrpos⟩, ?_⟩
    rw [← hm]
    exact (conjugatePower_mod a L (pow_orderOf_eq_one a) _).symm
  have hmain : orbitImage M a L ≤
      Subgroup.centralizer (orbitImage M a L' : Set (Bar2 M)) := by
    refine iSup_le fun i => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : orbitImage M a L' ≤ Subgroup.centralizer ({x} : Set (Bar2 M)) := by
      refine iSup_le fun j => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (uc22p22l_barImage_commute (conjugatePower_mem_calC hL haM i)
        (conjugatePower_mem_calC hL' haM j) (hdistinct i j) x hx y hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hmain hx) y hy).symm

private theorem facts_of_mem_conjSetOf {D : Data G} {Ch : Choice2011 G} (e : Ctx215 D Ch)
    {L' : Subgroup G} (hL' : L' ∈ conjSetOf D.M e.L)
    (hZ : Subgroup.center (Bar2 e.L) = ⊥)
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 e.L) (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 e.L) q) ∨ IsJ1 (Bar2 e.L))
    (h3 : 3 ∣ Nat.card (Bar2 e.L)) (hr : ¬ orderOf e.a ∣ Nat.card (Bar2 e.L)) :
    L' ∈ calC D.M ∧ Subgroup.center (Bar2 L') = ⊥ ∧
      3 ∣ Nat.card (Bar2 L') ∧ ¬ orderOf e.a ∣ Nat.card (Bar2 L') ∧
      ((∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 L') (2 ^ k)) ∨
        (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L') q) ∨ IsJ1 (Bar2 L')) := by
  obtain ⟨g, hgM, rfl⟩ := hL'
  exact ⟨uc22p2214_calC_of_mem_conjSetOf e.hL ⟨g, hgM, rfl⟩,
    center_bar2_map_conj_eq_bot hZ,
    by rw [card_bar2_map_conj]; exact h3,
    by rw [card_bar2_map_conj]; exact hr,
    shape_bar2_map_conj (M := e.L) (g := g) hshape⟩

private theorem exists_three_of_mem_calC {M L' : Subgroup G} {a : G}
    (hL' : L' ∈ calC M) (haM : a ∈ M) (hr : (orderOf a).Prime) (hr2 : orderOf a ≠ 2)
    (hZ' : Subgroup.center (Bar2 L') = ⊥) (h3' : 3 ∣ Nat.card (Bar2 L'))
    (hr' : ¬ orderOf a ∣ Nat.card (Bar2 L')) (hKOut : KOddOutInner)
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 L') (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L') q) ∨ IsJ1 (Bar2 L')) :
    ∃ u : Bar2 M, orderOf u = 3 ∧
      u ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ∧
      u ∈ orbitImage M a L' ∧ ∃ v ∈ barImage M L', ¬ Commute u v := by
  by_cases haN : a ∈ Subgroup.normalizer (L' : Set G)
  · exact exists_three_of_mem_normalizer hL' haM hr hr2 haN hZ' h3' hr' hKOut hshape
  · exact exists_three_diagonal hL' haM hr hr2 haN hZ' h3'

private theorem not_mem_center_of_not_commute {M L' : Subgroup G} {a : G} {u : Bar2 M}
    (hu : u ∈ orbitImage M a L')
    (hv : ∃ v ∈ barImage M L', ¬ Commute u v) :
    (⟨u, hu⟩ : ↥(orbitImage M a L')) ∉ Subgroup.center (orbitImage M a L') := by
  obtain ⟨v, hvB, hv⟩ := hv
  intro hc
  have hvJ : v ∈ orbitImage M a L' := by
    refine Subgroup.mem_iSup_of_mem ⟨0, orderOf_pos a⟩ ?_
    rw [show conjugatePower a L' 0 = L' from conjugatePower_zero a L']
    exact hvB
  have hcomm : Commute u v := (congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hc ⟨v, hvJ⟩)).symm
  exact hv hcomm

private theorem exists_elemAbelian_nine_of_pair {M L L' : Subgroup G} {a : G} (haM : a ∈ M)
    {u₁ u₂ : Bar2 M} (hu₁ord : orderOf u₁ = 3)
    (hu₁C : u₁ ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
    (hu₁J : u₁ ∈ orbitImage M a L) (hu₂ord : orderOf u₂ = 3)
    (hu₂C : u₂ ∈ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
    (hu₂J : u₂ ∈ orbitImage M a L')
    (hcomm : ∀ x ∈ orbitImage M a L, ∀ y ∈ orbitImage M a L', x * y = y * x)
    (hv₂ : ∃ v ∈ barImage M L', ¬ Commute u₂ v) :
    ∃ E₉ : Subgroup (Bar2 M), IsElemAbelian 3 E₉ ∧ Nat.card ↥E₉ = 9 ∧
      E₉ ≤ (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J₁ : Subgroup (Bar2 M) := orbitImage M a L
  let J₂ : Subgroup (Bar2 M) := orbitImage M a L'
  let E : Subgroup (Bar2 M) := Subgroup.zpowers u₁
  have hcardE : Nat.card E = 3 := by
    rw [show Nat.card E = orderOf u₁ from Nat.card_zpowers u₁, hu₁ord]
  have hE : IsElemAbelian 3 E :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isElemAbelian_of_card_prime
      Nat.prime_three hcardE
  let u : ↥J₂ := ⟨u₂, hu₂J⟩
  have huord : orderOf u = 3 := by
    rw [← Subgroup.orderOf_coe u, hu₂ord]
  have hucent : u ∉ Subgroup.center J₂ :=
    not_mem_center_of_not_commute hu₂J hv₂
  obtain ⟨hE₉, hcard₉⟩ :=
    CFSG.GroupTheory.sup_zpowers_isElemAbelian_of_commute (H := J₁) (K := J₂) (E := E)
      hcomm hE (Subgroup.zpowers_le.mpr hu₁J) huord hucent
  have hE₉C : E ⊔ Subgroup.zpowers (u : Bar2 M) ≤
      (Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
    sup_le (Subgroup.zpowers_le.mpr hu₁C) (Subgroup.zpowers_le.mpr hu₂C)
  have hcard₉' : Nat.card ↥(E ⊔ Subgroup.zpowers (u : Bar2 M)) = 9 := by
    rw [hcard₉, hcardE]
  exact ⟨E ⊔ Subgroup.zpowers (u : Bar2 M), hE₉, hcard₉', hE₉C⟩

private theorem exists_elemAbelian_nine_of_not_mem_range {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (ha : e.a ∈ D.M) {L' : Subgroup G} (hL'C : L' ∈ calC D.M)
    (hZ : Subgroup.center (Bar2 e.L) = ⊥) (h3 : 3 ∣ Nat.card (Bar2 e.L))
    (hZ' : Subgroup.center (Bar2 L') = ⊥) (h3' : 3 ∣ Nat.card (Bar2 L'))
    (hr' : ¬ orderOf e.a ∣ Nat.card (Bar2 L')) (hKOut : KOddOutInner)
    (hshape' : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 L') (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L') q) ∨ IsJ1 (Bar2 L'))
    (hnot : L' ∉ Set.range (fun i : Fin (orderOf e.a) => conjugatePower e.a e.L i)) :
    ∃ E₉ : Subgroup (Bar2 D.M), IsElemAbelian 3 E₉ ∧ Nat.card ↥E₉ = 9 ∧
      E₉ ≤ (Subgroup.centralizer ({(⟨e.a, ha⟩ : ↥D.M)} : Set ↥D.M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
  obtain ⟨u₁, hu₁ord, hu₁C, hu₁J, -⟩ :=
    exists_three_diagonal e.hL ha e.ha_prime e.ha_ne_two e.ha_not_mem hZ h3
  obtain ⟨u₂, hu₂ord, hu₂C, hu₂J, hv₂⟩ :=
    exists_three_of_mem_calC hL'C ha e.ha_prime e.ha_ne_two hZ' h3' hr' hKOut hshape'
  exact exists_elemAbelian_nine_of_pair ha hu₁ord hu₁C hu₁J hu₂ord hu₂C hu₂J
    (commute_orbitImage_of_not_mem_range e.hL hL'C ha hnot) hv₂

private theorem two_le_pRank_of_elemAbelian_nine {M : Subgroup G} {a : G} (ha : a ∈ M)
    {E : Subgroup (Bar2 M)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hEimage : E ≤ (Subgroup.centralizer ({(⟨a, ha⟩ : ↥M)} : Set ↥M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ M) := by
  obtain ⟨E', hE'le, hE'elem, hE'card⟩ :=
    exists_elemAbelian_order_nine_lift ha hE hcard hEimage
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE'le hE'elem
    (k := 2) (by rw [hE'card]; norm_num)

theorem Ctx215.conjSetOf_eq {D : Data G} {Ch : Choice2011 G} (e : Ctx215 D Ch)
    (hKOut : KOddOutInner) (hZ : Subgroup.center (Bar2 e.L) = ⊥)
    (hshape : (∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 e.L) (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 e.L) q) ∨ IsJ1 (Bar2 e.L))
    (h3 : 3 ∣ Nat.card (Bar2 e.L)) (hr : ¬ orderOf e.a ∣ Nat.card (Bar2 e.L))
    (hrank3 : CFSG.Open.pRank 3
      (Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ⊓ D.M) ≤ 1) :
    conjSetOf D.M e.L = Set.range (fun i : Fin (orderOf e.a) => conjugatePower e.a e.L i) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha : e.a ∈ D.M := e.hBM (e.hle e.haB)
  refine Set.Subset.antisymm ?_ ?_
  · rintro L' hL'
    by_contra hnot
    obtain ⟨hL'C, hZ', h3', hr', hshape'⟩ :=
      facts_of_mem_conjSetOf e hL' hZ hshape h3 hr
    obtain ⟨E₉, hE₉, hcard₉, hle₉⟩ :=
      exists_elemAbelian_nine_of_not_mem_range e ha hL'C hZ h3 hZ' h3' hr' hKOut hshape' hnot
    have h2 := two_le_pRank_of_elemAbelian_nine ha hE₉ hcard₉ hle₉
    omega
  · rintro K ⟨i, rfl⟩
    exact ⟨e.a ^ (i : ℕ), D.M.pow_mem ha i, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
