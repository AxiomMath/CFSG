module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge
import CFSG.RankThree.PartTwo.Sec4.Census.OmegaIsoCols

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  localRank projImage orthogonalPlus orthogonalMinus plusQuadForm minusQuadForm)
open CFSG.RankThree.PartTwo.Census (le_localRank_of_le_normalizer localRank_eq_of_mulEquiv)
open scoped commutatorElement

namespace RankOmegaF4

section Witness

theorem exists_isElemAbelian_of_witness {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {n : ℕ} (Z A : Fin n → G) (h3 : ∀ i, Z i ^ 3 = 1)
    (h1 : ∀ i, ¬ Commute (Z i) (A i)) (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i))
    (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i)) (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) :
    ∃ E : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n ∧
      E ≤ (Subgroup.closure (Set.range Z)).map π := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ i, ∀ g ∈ Subgroup.zpowers (Z i), Commute g (A i) → g = 1 := by
    intro i g hg hc
    rcases CFSG.SectionRank.eq_one_or_of_mem_zpowers_three (h3 i) hg with h | h | h
    · exact h
    · exact absurd (h ▸ hc) (h1 i)
    · exact absurd (h ▸ hc) (h2 i)
  have hcent : ∀ i j, i ≠ j → Subgroup.zpowers (Z j) ≤ Subgroup.centralizer {A i} := by
    intro i j hij
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hZA i j hij).eq.symm
  have hker : ∀ i, ∀ g : G, π g = 1 → Commute g (A i) := fun i g hg =>
    (Subgroup.mem_center_iff.1 (hπ (MonoidHom.mem_ker.2 hg)) (A i)).symm
  let ϕ : ∀ i, Subgroup.zpowers (Z i) →* Q := fun i => π.comp (Subgroup.zpowers (Z i)).subtype
  have hϕcomm : Pairwise fun i j => ∀ (x : Subgroup.zpowers (Z i)) (y : Subgroup.zpowers (Z j)),
      Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change Commute (π (x : G)) (π (y : G))
    rw [← ha, ← hb]
    exact ((hZZ i j hij).zpow_zpow a b).map π
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (key i _ x.2 (hker i _ hx)))
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), (ϕ j).range) ≤
        (Subgroup.centralizer {A i}).map π := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hcent i j (Ne.symm hj) y.2, rfl⟩
    obtain ⟨r, hr, hrx⟩ := hle hg
    change π r = π (x : G) at hrx
    have hc : Commute (x : G) (A i) := by
      have hxr : (x : G) = r * (r⁻¹ * x) := by group
      rw [hxr]
      have hrc : Commute r (A i) := (Subgroup.mem_centralizer_iff.1 hr (A i) rfl).symm
      exact hrc.mul_left (hker i _ (by rw [map_mul, map_inv, hrx, inv_mul_cancel]))
    have hx1 : x = 1 := Subtype.ext (key i _ x.2 hc)
    change ϕ i x ∈ (⊥ : Subgroup Q)
    rw [hx1, map_one]
    exact one_mem _
  have hord : ∀ i, Nat.card (Subgroup.zpowers (Z i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h3 i) fun h => (h1 i) (h ▸ Commute.one_left _)
  set Φ := MonoidHom.noncommPiCoprod ϕ hϕcomm
  have hΦ : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (hcomm := hϕcomm) hind hϕinj
  have hcomm : ∀ a b : (∀ i, Subgroup.zpowers (Z i)), a * b = b * a := by
    intro a b
    funext i
    obtain ⟨x, hx⟩ := (a i).2
    obtain ⟨y, hy⟩ := (b i).2
    exact Subtype.ext (by
      change (a i : G) * (b i : G) = (b i : G) * (a i : G)
      rw [← hx, ← hy]
      exact (Commute.zpow_zpow_self _ _ _).eq)
  have hpow : ∀ a : (∀ i, Subgroup.zpowers (Z i)), a ^ 3 = 1 := by
    intro a
    funext i
    apply Subtype.ext
    change ((a i : G)) ^ 3 = 1
    obtain ⟨x, hx⟩ := (a i).2
    rw [← hx, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h3 i,
      _root_.one_zpow]
  refine ⟨Φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Q) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_pi,
      Finset.prod_congr rfl fun i _ => hord i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    have hZi : Z i ∈ Subgroup.closure (Set.range Z) :=
      Subgroup.subset_closure (Set.mem_range_self i)
    exact ⟨x, Subgroup.zpowers_le.2 hZi x.2, rfl⟩

theorem isElemAbelian_subgroupOf {Q : Type*} [Group Q] {p : ℕ} {E H : Subgroup Q}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem le_localRank_of_le {Q : Type} [Group Q] {H : Subgroup Q} [Finite H] {p k : ℕ}
    (hp : p.Prime) {P E : Subgroup Q} (hPH : P ≤ H) (hEH : E ≤ H) (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hE : CFSG.Assembly.IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEP : E ≤ Subgroup.normalizer (P : Set Q)) : k ≤ localRank p H := by
  refine le_localRank_of_le_normalizer hp (P := P.subgroupOf H) (E := E.subgroupOf H) ?_
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm) (isElemAbelian_subgroupOf hE) ?_ ?_
  · rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hP (hd.eq_bot_of_le hPH)
  · rw [← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hEP (Subgroup.mem_subgroupOf.1 hx)) h

theorem le_localRank_of_witness {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {H : Subgroup Q} [Finite H] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPc : ¬ P ≤ Subgroup.center G) (hZP : ∀ i, Z i ∈ Subgroup.normalizer (P : Set G))
    (hZH : ∀ i, π (Z i) ∈ H) (hPH : P.map π ≤ H) : n ≤ localRank 3 H := by
  obtain ⟨E, hE, hc, hEZ⟩ := exists_isElemAbelian_of_witness π hπ Z A h3 h1 h2 hZA hZZ
  have hZ : Subgroup.closure (Set.range Z) ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 hZP)
  have hZH' : (Subgroup.closure (Set.range Z)).map π ≤ H :=
    Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 hZH))
  refine le_localRank_of_le Nat.prime_three hPH (hEZ.trans hZH') ?_ (hP2.map π) hE hc
    (hEZ.trans ((Subgroup.map_mono hZ).trans (Subgroup.le_normalizer_map π)))
  intro h
  exact hPc (((Subgroup.map_eq_bot_iff P).1 h).trans hπ)

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {t : G} (ht : t ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  rintro ⟨g, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change (t ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ht,
    _root_.one_zpow]

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g t : G} (h : Commute g t) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  rintro _ ⟨k, rfl⟩
  exact (Commute.zpow_left h.symm k).eq

theorem le_localRank_of_witness_involution {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {H : Subgroup Q} [Finite H] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {t : G} (ht : t ^ 2 = 1)
    (htc : t ∉ Subgroup.center G) (hZt : ∀ i, Commute (Z i) t) (hZH : ∀ i, π (Z i) ∈ H)
    (htH : π t ∈ H) : n ≤ localRank 3 H :=
  le_localRank_of_witness π hπ Z A h3 h1 h2 hZA hZZ (isPGroup_zpowers_of_sq ht)
    (fun h => htc (h (Subgroup.mem_zpowers t))) (fun i => mem_normalizer_zpowers (hZt i)) hZH
    (by rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]; exact htH)

theorem le_pRank_of_witness {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {H : Subgroup Q} [Finite H] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) (hZH : ∀ i, π (Z i) ∈ H) :
    n ≤ CFSG.pRank 3 H := by
  obtain ⟨E, hE, hc, hEZ⟩ := exists_isElemAbelian_of_witness π hπ Z A h3 h1 h2 hZA hZZ
  have hEH : E ≤ H := hEZ.trans
    (Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 hZH)))
  obtain ⟨hcomm, hpow⟩ := isElemAbelian_subgroupOf (H := H) hE
  refine CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) (E.subgroupOf H)
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hpow x x.2, Subgroup.coe_one]) } ?_
  rw [← hc]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv

theorem mem_normalizer_sup_of_commute {G : Type*} [Group G] {g a b : G} (ha : Commute g a)
    (hb : Commute g b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer {g} :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ha.eq.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hb.eq.symm))
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh))

theorem mem_normalizer_sup_zpowers {G : Type*} [Group G] {g a b : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha' : g⁻¹ * a * g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb' : g⁻¹ * b * g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  set P := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have h1 : P ≤ P.comap (MulAut.conj g).toMonoidHom :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  have h2 : P ≤ P.comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · change g⁻¹ * a * g⁻¹⁻¹ ∈ P
      rwa [inv_inv]
    · change g⁻¹ * b * g⁻¹⁻¹ ∈ P
      rwa [inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 hh, fun hh => ?_⟩
  have h3 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ ∈ P := h2 hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h3

end Witness

section FieldTwo

@[expose] noncomputable def f2 : ZMod 2 ≃+* GaloisField 2 1 :=
  (GaloisField.equivZmodP 2).symm.toRingEquiv

theorem eq_zero_or_eq_one_f2 (x : GaloisField 2 1) : x = 0 ∨ x = 1 :=
  CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one x

theorem eq_one_of_irreducible {b c : GaloisField 2 1}
    (h : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
    rw [← map_one f2, ← map_add, show (1 : ZMod 2) + 1 = 0 by decide, map_zero]
  have hc : c = 1 := (eq_zero_or_eq_one_f2 c).resolve_left fun hc => h 0 (by rw [hc]; ring)
  refine ⟨(eq_zero_or_eq_one_f2 b).resolve_left fun hb => h 1 ?_, hc⟩
  rw [hb, hc]
  linear_combination h11

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def toF2 : GL ι (ZMod 2) →* GL ι (GaloisField 2 1) :=
  GeneralLinearGroup.map f2.toRingHom

theorem coe_toF2 (A : GL ι (ZMod 2)) :
    ((toF2 A : GL ι (GaloisField 2 1)) : Matrix ι ι (GaloisField 2 1)) =
      (A : Matrix ι ι (ZMod 2)).map f2 :=
  rfl

theorem toF2_injective : Function.Injective (toF2 (ι := ι)) := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun g : GL ι (GaloisField 2 1) => (g : Matrix ι ι (GaloisField 2 1))) h
  simp only [coe_toF2] at h'
  ext i j
  exact f2.injective (congrFun (congrFun h' i) j)

@[expose] noncomputable def projF2 : GL ι (ZMod 2) →* ProjGenLinGroup ι (GaloisField 2 1) :=
  ProjGenLinGroup.mk.comp toF2

theorem ker_projF2_le : (projF2 (ι := ι)).ker ≤ Subgroup.center (GL ι (ZMod 2)) := by
  intro x hx
  rw [MonoidHom.mem_ker, projF2, MonoidHom.comp_apply] at hx
  have hc : toF2 x ∈ Subgroup.center (GL ι (GaloisField 2 1)) := ProjGenLinGroup.mk_eq_one.1 hx
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply toF2_injective
  rw [map_mul, map_mul]
  exact hc _

theorem finite_projGenLinGroup : Finite (ProjGenLinGroup ι (GaloisField 2 1)) :=
  Finite.of_surjective _ ProjGenLinGroup.mk_surjective

theorem mulVec_toF2 (A : GL ι (ZMod 2)) (w : ι → ZMod 2) :
    ((toF2 A : GL ι (GaloisField 2 1)) : Matrix ι ι (GaloisField 2 1)) *ᵥ (f2 ∘ w) =
      f2 ∘ ((A : Matrix ι ι (ZMod 2)) *ᵥ w) := by
  funext i
  rw [coe_toF2]
  exact (RingHom.map_mulVec f2.toRingHom (A : Matrix ι ι (ZMod 2)) w i).symm

theorem plusQuadForm_comp_f2 {m : ℕ} (u : Fin m ⊕ Fin m → ZMod 2) :
    plusQuadForm m (f2 ∘ u) = f2 (plusQuadForm m u) := by
  simp [plusQuadForm, map_sum, map_mul]

theorem minusQuadForm_comp_f2 {m : ℕ} (u : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    minusQuadForm m (1 : GaloisField 2 1) 1 (f2 ∘ u) = f2 (minusQuadForm m 1 1 u) := by
  simp only [minusQuadForm, Function.comp_apply, map_add, map_sum, map_mul, map_pow, map_one]

theorem toF2_mem_orthogonalPlus {m : ℕ} {A : GL (Fin m ⊕ Fin m) (ZMod 2)}
    (hA : ∀ v, plusQuadForm m ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) *ᵥ v) =
      plusQuadForm m v) :
    toF2 A ∈ orthogonalPlus m (GaloisField 2 1) := by
  refine Subgroup.subset_closure fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w, f2 ∘ w = v := ⟨f2.symm ∘ v, by funext i; simp⟩
  rw [mulVec_toF2, plusQuadForm_comp_f2, plusQuadForm_comp_f2, hA]

theorem toF2_mem_orthogonalMinus {m : ℕ} {A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hA : ∀ v, minusQuadForm m (1 : ZMod 2) 1
      ((A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        minusQuadForm m 1 1 v) :
    toF2 A ∈ orthogonalMinus m (GaloisField 2 1) 1 1 := by
  refine Subgroup.subset_closure fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w, f2 ∘ w = v := ⟨f2.symm ∘ v, by funext i; simp⟩
  rw [mulVec_toF2, minusQuadForm_comp_f2, minusQuadForm_comp_f2, hA]

theorem projF2_commutatorElement_mem {O : Subgroup (GL ι (GaloisField 2 1))}
    {a b : GL ι (ZMod 2)} (ha : toF2 a ∈ O) (hb : toF2 b ∈ O) :
    projF2 ⁅a, b⁆ ∈ projImage ⁅O, O⁆ :=
  ⟨⁅toF2 a, toF2 b⁆, Subgroup.commutator_mem_commutator ha hb, by
    simp only [projF2, MonoidHom.comp_apply, map_commutatorElement]⟩

@[expose] def unitOfCube (M : Matrix ι ι (ZMod 2)) (h : M * (M * M) = 1) : GL ι (ZMod 2) :=
  ⟨M, M * M, h, (mul_assoc M M M).trans h⟩

@[expose] def unitOfSq (M : Matrix ι ι (ZMod 2)) (h : M * M = 1) : GL ι (ZMod 2) :=
  ⟨M, M, h, h⟩

end FieldTwo

section Plus

@[expose] def encPlus : Fin 4 ⊕ Fin 4 → Fin 8 := Sum.elim ![0, 1, 2, 3] ![4, 5, 6, 7]

@[expose] def matPlus (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  M.submatrix encPlus encPlus

@[expose] def pLg₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 1, 0, 0, 1, 0, 0, 0;
       1, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRg₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![0, 1, 0, 0, 0, 0, 0, 0;
       1, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pLs₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 1, 0, 0;
       0, 1, 0, 0, 1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRs₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       1, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pLg₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 1, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRg₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 1, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 1, 0]) (by decide +kernel)

@[expose] def pLs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 1;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 1, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pX₁₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pX₂₀ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       1, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 1, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def plusZ : Fin 4 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLg₁, pRg₁, pLg₂, pRg₂]

@[expose] def plusA : Fin 4 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLs₁, pRs₁, pLs₂, pRs₂]

@[expose] def plusZ₃ : Fin 3 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLg₁, pLg₂, pRg₂]

@[expose] def plusA₃ : Fin 3 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLs₁, pLs₂, pRs₂]

theorem plus_relations :
    (∀ i, plusZ i ^ 3 = 1) ∧ (∀ i, plusZ i * plusA i ≠ plusA i * plusZ i) ∧
      (∀ i, plusZ i ^ 2 * plusA i ≠ plusA i * plusZ i ^ 2) ∧
      (∀ i j, i ≠ j → plusZ j * plusA i = plusA i * plusZ j) ∧
      (∀ i j, i ≠ j → plusZ i * plusZ j = plusZ j * plusZ i) ∧
      (∀ i, ⁅plusA i, plusZ i⁆ = plusZ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem plus₃_relations :
    (∀ i, plusZ₃ i ^ 3 = 1) ∧ (∀ i, plusZ₃ i * plusA₃ i ≠ plusA₃ i * plusZ₃ i) ∧
      (∀ i, plusZ₃ i ^ 2 * plusA₃ i ≠ plusA₃ i * plusZ₃ i ^ 2) ∧
      (∀ i j, i ≠ j → plusZ₃ j * plusA₃ i = plusA₃ i * plusZ₃ j) ∧
      (∀ i j, i ≠ j → plusZ₃ i * plusZ₃ j = plusZ₃ j * plusZ₃ i) ∧
      (∀ i, ⁅plusA₃ i, plusZ₃ i⁆ = plusZ₃ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem plus_involution :
    ⁅pX₁₂, pX₂₀⁆ = pRs₁ ∧ pRs₁ ^ 2 = 1 ∧ pRs₁ * pRg₁ ≠ pRg₁ * pRs₁ ∧
      ∀ i, plusZ₃ i * pRs₁ = pRs₁ * plusZ₃ i := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem isometry_plusZ (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    plusQuadForm 4 ((plusZ i : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
      plusQuadForm 4 v := by
  refine OmegaIsoCols.plus_of_cols _ ?_ ?_ v <;> revert i <;> decide +kernel

theorem isometry_plusA (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    plusQuadForm 4 ((plusA i : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
      plusQuadForm 4 v := by
  refine OmegaIsoCols.plus_of_cols _ ?_ ?_ v <;> revert i <;> decide +kernel

theorem isometry_pX (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    plusQuadForm 4 ((pX₁₂ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
        plusQuadForm 4 v ∧
      plusQuadForm 4 ((pX₂₀ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
        plusQuadForm 4 v := by
  refine ⟨OmegaIsoCols.plus_of_cols _ ?_ ?_ v, OmegaIsoCols.plus_of_cols _ ?_ ?_ v⟩ <;>
    decide +kernel

theorem projF2_plusZ_mem (i : Fin 4) : projF2 (plusZ i) ∈ projOmegaPlus 4 (GaloisField 2 1) := by
  rw [← plus_relations.2.2.2.2.2 i]
  exact projF2_commutatorElement_mem (toF2_mem_orthogonalPlus (isometry_plusA i))
    (toF2_mem_orthogonalPlus (isometry_plusZ i))

theorem projF2_plusZ₃_mem (i : Fin 3) :
    projF2 (plusZ₃ i) ∈ projOmegaPlus 4 (GaloisField 2 1) := by
  fin_cases i
  · exact projF2_plusZ_mem 0
  · exact projF2_plusZ_mem 2
  · exact projF2_plusZ_mem 3

end Plus

section Minus

@[expose] def encMinus : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → Fin 8 :=
  Sum.elim ![0, 1, 2] (Sum.elim ![3, 4, 5] ![6, 7])

@[expose] def matMinus (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  M.submatrix encMinus encMinus

@[expose] def mLg : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 1, 0, 1, 0, 0, 0;
       0, 1, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mRg : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mOm : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 1, 1]) (by decide +kernel)

@[expose] def mLs : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 1, 0, 0;
       0, 0, 1, 0, 1, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mRs : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mCj : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₁ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 0, 1;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₂ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 1, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 1, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₃ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 1, 1;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 1, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def minusZ : Fin 3 → GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) := ![mLg, mRg, mOm]

@[expose] def minusA : Fin 3 → GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) := ![mLs, mRs, mCj]

theorem minus_relations :
    (∀ i, minusZ i ^ 3 = 1) ∧ (∀ i, minusZ i * minusA i ≠ minusA i * minusZ i) ∧
      (∀ i, minusZ i ^ 2 * minusA i ≠ minusA i * minusZ i ^ 2) ∧
      (∀ i j, i ≠ j → minusZ j * minusA i = minusA i * minusZ j) ∧
      (∀ i j, i ≠ j → minusZ i * minusZ j = minusZ j * minusZ i) ∧
      (∀ i, ⁅minusA i, minusZ i⁆ = minusZ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem minus_fourGroup :
    mE₁ ^ 2 = 1 ∧ mE₂ ^ 2 = 1 ∧ mE₁ * mE₂ = mE₂ * mE₁ ∧ ⁅mOm, mE₂⁆ = mE₁ ∧
      ⁅mOm, mE₃⁆ = mE₂ ∧ mE₁ * mOm ≠ mOm * mE₁ ∧ mOm * mE₁ * mOm⁻¹ = mE₂ ∧
      mOm * mE₂ * mOm⁻¹ = mE₁ * mE₂ ∧ mOm⁻¹ * mE₁ * mOm = mE₁ * mE₂ ∧
      mOm⁻¹ * mE₂ * mOm = mE₁ ∧ mLg * mE₁ = mE₁ * mLg ∧ mLg * mE₂ = mE₂ * mLg ∧
      mRg * mE₁ = mE₁ * mRg ∧ mRg * mE₂ = mE₂ * mRg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem isometry_minusZ (i : Fin 3) (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) :
    minusQuadForm 3 (1 : ZMod 2) 1
      ((minusZ i : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        minusQuadForm 3 1 1 v := by
  refine OmegaIsoCols.minus_of_cols _ ?_ ?_ v <;> revert i <;> decide +kernel

theorem isometry_minusA (i : Fin 3) (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) :
    minusQuadForm 3 (1 : ZMod 2) 1
      ((minusA i : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        minusQuadForm 3 1 1 v := by
  refine OmegaIsoCols.minus_of_cols _ ?_ ?_ v <;> revert i <;> decide +kernel

theorem isometry_mE (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) :
    minusQuadForm 3 (1 : ZMod 2) 1
        ((mE₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        minusQuadForm 3 1 1 v ∧
      minusQuadForm 3 (1 : ZMod 2) 1
        ((mE₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        minusQuadForm 3 1 1 v := by
  refine ⟨OmegaIsoCols.minus_of_cols _ ?_ ?_ v, OmegaIsoCols.minus_of_cols _ ?_ ?_ v⟩ <;>
    decide +kernel

theorem projF2_minusZ_mem (i : Fin 3) :
    projF2 (minusZ i) ∈ projOmegaMinus 3 (GaloisField 2 1) 1 1 := by
  rw [← minus_relations.2.2.2.2.2 i]
  exact projF2_commutatorElement_mem (toF2_mem_orthogonalMinus (isometry_minusA i))
    (toF2_mem_orthogonalMinus (isometry_minusZ i))

end Minus

section F4

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem three_le_localRank_adjointQuotient_F4
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    3 ≤ localRank 3 (AdjointQuotient .F4 K) := by
  obtain ⟨hf, hZA, hZZ⟩ := RootWitness.charTwo_facts witnessF4_check witnessF4_orthoCheck
    ![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] (by decide) (K := K)
  have h11 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero K 2
  have ht : witnessF4.elemA K (Fin.last 3) ^ 2 = 1 := by
    rw [RootWitness.elemA, conj_pow, sq, ← (rootOperatorFamily _).eltElement_add, h11,
      (rootOperatorFamily _).eltElement_zero, mul_one, mul_inv_cancel]
  have htc : witnessF4.elemA K (Fin.last 3) ∉ Subgroup.center (adjointGroup .F4 K) := fun h =>
    (hf (Fin.last 3)).2.1 (Subgroup.mem_center_iff.1 h (witnessF4.elemZ K (Fin.last 3)))
  have h := le_localRank_of_witness_involution
    (H := (⊤ : Subgroup (AdjointQuotient .F4 K)))
    (QuotientGroup.mk' (Subgroup.center (adjointGroup .F4 K))) (QuotientGroup.ker_mk' _).le
    (fun i : Fin 3 => witnessF4.elemZ K i.castSucc) (fun i : Fin 3 => witnessF4.elemA K i.castSucc)
    (fun i => (hf _).1) (fun i => (hf _).2.1) (fun i => (hf _).2.2)
    (fun i j hij => hZA _ _ fun h => hij (Fin.castSucc_injective _ h))
    (fun i j hij => hZZ _ _ fun h => hij (Fin.castSucc_injective _ h))
    ht htc (fun i => hZA _ _ (Fin.castSucc_lt_last i).ne') (fun _ => Subgroup.mem_top _)
    (Subgroup.mem_top _)
  rwa [localRank_eq_of_mulEquiv Subgroup.topEquiv Nat.prime_three] at h

end F4

end RankOmegaF4

open RankOmegaF4

theorem localRank_omega8PlusTwo [Finite (projOmegaPlus 4 (GaloisField 2 1))] :
    3 ≤ localRank 3 (projOmegaPlus 4 (GaloisField 2 1)) := by
  obtain ⟨h3, h1, h2, hZA, hZZ, -⟩ := plus₃_relations
  obtain ⟨ht, ht2, htc, hZt⟩ := plus_involution
  refine le_localRank_of_witness_involution projF2 ker_projF2_le plusZ₃ plusA₃ h3 h1 h2 hZA hZZ
    ht2 (fun h => htc (Subgroup.mem_center_iff.1 h pRg₁).symm) hZt projF2_plusZ₃_mem ?_
  rw [← ht]
  exact projF2_commutatorElement_mem (toF2_mem_orthogonalPlus fun v => (isometry_pX v).1)
    (toF2_mem_orthogonalPlus fun v => (isometry_pX v).2)

theorem three_lt_pRank_omegaPlus : 3 < CFSG.pRank 3 (projOmegaPlus 4 (GaloisField 2 1)) := by
  have : Finite (ProjGenLinGroup (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) := finite_projGenLinGroup
  obtain ⟨h3, h1, h2, hZA, hZZ, -⟩ := plus_relations
  have h := le_pRank_of_witness projF2 ker_projF2_le plusZ plusA h3 h1 h2 hZA hZZ
    projF2_plusZ_mem
  omega

theorem localRank_omega8MinusTwo (b c : GaloisField 2 1)
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    [Finite (projOmegaMinus 3 (GaloisField 2 1) b c)] :
    3 ≤ localRank 3 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible hbc
  obtain ⟨h3, h1, h2, hZA, hZZ, -⟩ := minus_relations
  obtain ⟨h11, h22, h12, hE₁, hE₂, hE₁c, hc₁, hc₂, hc₁', hc₂', hL₁, hL₂, hR₁, hR₂⟩ :=
    minus_fourGroup
  have hP : Subgroup.map projF2 (Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂) ≤
      projOmegaMinus 3 (GaloisField 2 1) 1 1 := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [← hE₁]
      exact projF2_commutatorElement_mem (toF2_mem_orthogonalMinus (isometry_minusZ 2))
        (toF2_mem_orthogonalMinus fun v => (isometry_mE v).1)
    · rw [← hE₂]
      exact projF2_commutatorElement_mem (toF2_mem_orthogonalMinus (isometry_minusZ 2))
        (toF2_mem_orthogonalMinus fun v => (isometry_mE v).2)
  have hmem₁ : mE₁ ∈ Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hmem₂ : mE₂ ∈ Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine le_localRank_of_witness projF2 ker_projF2_le minusZ minusA h3 h1 h2 hZA hZZ
    (IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_sq h11) (isPGroup_zpowers_of_sq h22)
      (Subgroup.zpowers_le.2 (mem_normalizer_zpowers h12)))
    (fun h => hE₁c (Subgroup.mem_center_iff.1 (h hmem₁) mOm).symm) (fun i => ?_)
    projF2_minusZ_mem hP
  fin_cases i
  · exact mem_normalizer_sup_of_commute hL₁ hL₂
  · exact mem_normalizer_sup_of_commute hR₁ hR₂
  · refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · change mOm * mE₁ * mOm⁻¹ ∈ _
      rw [hc₁]
      exact hmem₂
    · change mOm * mE₂ * mOm⁻¹ ∈ _
      rw [hc₂]
      exact mul_mem hmem₁ hmem₂
    · change mOm⁻¹ * mE₁ * mOm ∈ _
      rw [hc₁']
      exact mul_mem hmem₁ hmem₂
    · change mOm⁻¹ * mE₂ * mOm ∈ _
      rw [hc₂']
      exact hmem₁

theorem localRank_f4Two
    [Finite (CFSGIndex.lie f4TwoIndex).Group] :
    3 ≤ localRank 3 (CFSGIndex.lie f4TwoIndex).Group := by
  have hm : UntwistedChevalleyModel (CFSGIndex.lie f4TwoIndex).Group .F4 (2 ^ 1) :=
    CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 CFSG.Assembly.RankThreeEven.primePowerTwo
      f4TwoIndex.2 rfl (MulEquiv.refl _)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 2 := CFSG.SectionRank.charP_of_natCard_eq_pow hK
  rw [localRank_eq_of_mulEquiv e Nat.prime_three]
  exact three_le_localRank_adjointQuotient_F4

structure RankThree46Sporadic : Prop where
  sporadic : ∀ s ∈ sporadics42not46, ∀ [Finite (CFSGIndex.sporadic s).Group],
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group

theorem RankThree46Open.of_sporadic
    (h : RankThree46Sporadic) : RankThree46Open :=
  ⟨h.sporadic, localRank_omega8PlusTwo, localRank_omega8MinusTwo, localRank_f4Two⟩

structure TwoCoverRanksOpen' : Prop where
  alternating : ∀ n : ℕ, 6 ≤ n → n ≤ 12 → NoRankThreeDoubleCover (alternatingGroup (Fin n))
  hs : NoRankThreeDoubleCover (Spor .HS)
  ru : NoRankThreeDoubleCover (Spor .Ru)
  m22 : NoRankThreeDoubleCover (Spor .M22)
  psu42 : NoRankThreeDoubleCover (projSU 4 2 1)
  psl34 : ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
    CFSG.pRank 2 J = 3 → IsCyclic (Subgroup.center J) ∧ Nat.card (Subgroup.center J) = 4
  g24 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  sz8 : ∀ hm : (TauCeti.LieTypeIndex.suzuki 1).Valid,
    NoRankThreeTwoCover (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group
  sp62 : NoRankThreeDoubleCover (projSp 3 (GaloisField 2 1))

theorem TwoCoverRanksOpen.of_open' (h : TwoCoverRanksOpen') : TwoCoverRanksOpen where
  alternating := h.alternating
  hs := h.hs
  ru := h.ru
  m22 := h.m22
  psu42 := h.psu42
  psl34 := h.psl34
  g24 := h.g24
  sz8 := h.sz8
  sp62 := h.sp62
  omegaPlus := three_lt_pRank_omegaPlus

end CFSG.RankThree.PartTwo.Sec4.Census
