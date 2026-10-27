module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma zpow_eq_one_or_self_of_sq_eq_one {G : Type*} [Group G] {a z : G}
    (ha : a ^ 2 = 1) (hz : z ∈ Subgroup.zpowers a) : z = 1 ∨ z = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have ha' : a ^ (2 : ℤ) = 1 := by simpa using ha
  rw [zpow_eq_zpow_emod k (n := (2 : ℤ)) ha']
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

private lemma padicValNat_prod_finset {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

private lemma padicValNat_prod_fintype {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h : ∀ i, f i ≠ 0) : padicValNat 2 (∏ i, f i) = ∑ i, padicValNat 2 (f i) := by
  simpa using padicValNat_prod_finset (Finset.univ : Finset ι) f (fun i _ => h i)

private lemma finsum_mem_eq_subtype_sum {α : Type*} {s : Set α} [Fintype s] (f : α → ℕ) :
    ∑ᶠ i ∈ s, f i = ∑ i : s, f i.1 := by
  rw [finsum_mem_eq_toFinset_sum f s]
  simp [Set.toFinset]

private lemma odd_prod_finset {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {x : G} :
    x ∈ H ⊔ K ↔ ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  constructor
  · intro h
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro w (hw | hw)
      · exact ⟨w, hw, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, w, hw, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [hcomm y₂ hy₂ z₁ hz₁]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
      simpa [mul_inv_rev] using (congrArg Inv.inv (hcomm y hy z hz)).symm
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact H.mul_mem_sup hy hz

private theorem open_isSubnormal_map {G K : Type*} [Group G] [Group K] (f : G →* K)
    {L M : Subgroup G} (h : CFSG.Open.IsSubnormal L M) :
    CFSG.Open.IsSubnormal (L.map f) (M.map f) := by
  induction h with
  | refl => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hle hnormal _ ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_mono hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hle)]
    rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
    rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
    exact ⟨m * h * m⁻¹, hnormal h m hh hm, by simp⟩

private theorem open_isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.Open.IsQuasisimple H) : CFSG.Open.IsQuasisimple G := by
  have : Group.IsPerfect H := ⟨h.1⟩
  have : IsSimpleGroup (H ⧸ Subgroup.center H) := h.2
  have hperfect : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨hperfect.commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
      (Subgroup.map_center_eq e)).isSimpleGroup⟩

theorem s15_Lin_exists_ne_one_mem_fixV {W : Type*} [CommGroup W] [Finite W]
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 P) (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W}
    (hU : U ≠ ⊥) (hPU : ∀ x ∈ P, ∀ u ∈ U, x u ∈ U) : ∃ u ∈ U, u ≠ 1 ∧ u ∈ fixV P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥P ↥U :=
    { smul := fun x u => ⟨x.1 u.1, hPU x.1 x.2 u.1 u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun x y u => Subtype.ext (MulAut.mul_apply W x.1 y.1 u.1) }
  have hU2 : IsPGroup 2 ↥U := (isPGroup_two_of_sq_eq_one hW).to_subgroup U
  have h2dvd : 2 ∣ Nat.card ↥U := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hU (Subgroup.card_eq_one.mp hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hfix1 : (1 : ↥U) ∈ MulAction.fixedPoints ↥P ↥U := by
    intro x
    apply Subtype.ext
    show x.1 (1 : W) = 1
    exact map_one x.1
  obtain ⟨y, hy, hy1⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥U h2dvd hfix1
  refine ⟨y.1, y.2, ?_, ?_⟩
  · intro h; exact hy1 (Subtype.ext h).symm
  · rw [mem_fixV]
    intro x hx
    have h := congrArg Subtype.val (hy ⟨x, hx⟩)
    change x y.1 = y.1 at h
    exact h

theorem s15_Lin_commSub_commSub_eq_of_no_two_quotient {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : ∀ N : Subgroup X, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤) :
    commSub (commSub ⊤ X) X = commSub ⊤ X := by
  classical
  let U : Subgroup W := commSub ⊤ X
  let U' : Subgroup W := commSub U X
  have hU'le : U' ≤ U := commSub_mono le_top le_rfl
  let K : Subgroup ↥U := U'.subgroupOf U
  let gen : (x : X) → W → U := fun x w =>
    ⟨x.1 w * w⁻¹, Subgroup.subset_closure ⟨x.1, x.2, w, trivial, rfl⟩⟩
  let φ : X →* (W → ↥U ⧸ K) :=
    { toFun := fun x w => QuotientGroup.mk' K (gen x w)
      map_one' := by
        funext w
        show QuotientGroup.mk' K (gen 1 w) = 1
        change (gen 1 w : ↥U ⧸ K) = 1
        rw [QuotientGroup.eq_one_iff]
        have h1 : gen 1 w = 1 := by
          apply Subtype.ext
          simp [gen]
        rw [h1]
        exact Subgroup.one_mem K
      map_mul' := by
        intro x y
        funext w
        show QuotientGroup.mk' K (gen (x * y) w) =
          QuotientGroup.mk' K (gen x w) * QuotientGroup.mk' K (gen y w)
        have key : QuotientGroup.mk' K (gen (x * y) w) =
            QuotientGroup.mk' K (gen y w * gen x w) := by
          apply Quotient.sound
          show QuotientGroup.leftRel K (gen (x * y) w) (gen y w * gen x w)
          rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
          have hgen : x.1 (gen y w).1 * ((gen y w).1)⁻¹ ∈ U' :=
            Subgroup.subset_closure ⟨x.1, x.2, (gen y w).1, (gen y w).2, rfl⟩
          have hval : ((gen (x * y) w) * (gen y w * gen x w)⁻¹ : U).1 =
              x.1 (gen y w).1 * ((gen y w).1)⁻¹ := by
            simp only [gen, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul,
              map_inv]
            group
          have h1 : ((gen (x * y) w) * (gen y w * gen x w)⁻¹ : U).1 ∈ U' := by
            rw [hval]; exact hgen
          have h2 : (((gen (x * y) w) * (gen y w * gen x w)⁻¹ : U).1)⁻¹ ∈ U' :=
            U'.inv_mem h1
          have hEq : (((gen (x * y) w) * (gen y w * gen x w)⁻¹ : U).1)⁻¹ =
              ((gen (x * y) w)⁻¹ * (gen y w * gen x w) : U).1 := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [mul_inv_rev, inv_inv]
            exact mul_comm ((gen y w * gen x w).1) ((gen (x * y) w).1)⁻¹
          rwa [hEq] at h2
        rw [key, map_mul]
        exact mul_comm _ _ }
  have hφ2 : ∀ x : X, φ x ^ 2 = 1 := by
    intro x
    funext w
    show (QuotientGroup.mk' K (gen x w)) ^ 2 = 1
    have hsq : (gen x w) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      exact hW _
    rw [← map_pow, hsq, map_one]
  have hP : IsPGroup 2 φ.range := by
    refine isPGroup_two_of_sq_eq_one (fun g => ?_)
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp g.2
    apply Subtype.ext
    change (g.1) ^ 2 = 1
    rw [← hx]
    simpa using hφ2 x
  have hidx : ∃ n : ℕ, φ.ker.index = 2 ^ n := by
    refine ⟨rk φ.range, ?_⟩
    rw [Subgroup.index_ker, card_eq_two_pow_of_isPGroup hP]
  have hker : φ.ker = ⊤ := hX φ.ker (inferInstance : φ.ker.Normal) hidx
  have hUle' : U ≤ U' := by
    show commSub ⊤ X ≤ commSub U X
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    have hxker : (⟨x, hx⟩ : X) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top _
    have hw : QuotientGroup.mk' K (gen ⟨x, hx⟩ w) = 1 := by
      have h := congrFun (MonoidHom.mem_ker.mp hxker) w
      exact h
    have hmem : gen ⟨x, hx⟩ w ∈ K := (QuotientGroup.eq_one_iff _).mp hw
    simpa using Subgroup.mem_subgroupOf.mp hmem
  show U' = U
  exact le_antisymm hU'le hUle'

theorem s15_Lin_eq_bot_of_commSub_top_eq_bot {W : Type*} [CommGroup W]
    {X : Subgroup (MulAut W)} (h : commSub ⊤ X = ⊥) : X = ⊥ := by
  have hfix : ⊤ ≤ fixV X := commSub_eq_bot_iff.mp h
  rw [← le_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  ext w
  simpa using hfix trivial x hx

theorem s15_Lin_isPGroup_two_of_acts_trivially {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {C : Subgroup W} {K : Subgroup (MulAut W)} (hKC : K ≤ centSub C)
    (hKq : ∀ x ∈ K, ∀ w : W, x w * w⁻¹ ∈ C) : IsPGroup 2 K := by
  rintro ⟨x, hx⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hx2 : x ^ 2 = 1 := by
    ext w
    set c : W := x w * w⁻¹ with hcdef
    have hc : c ∈ C := by rw [hcdef]; exact hKq x hx w
    have hxc : x c = c := (mem_centSub.mp (hKC hx)) c hc
    have hc2 : c * c = 1 := by
      have h := hW c
      rwa [pow_two] at h
    have hcw : x w = c * w := by rw [hcdef]; group
    show x (x w) = w
    calc x (x w) = x (c * w) := by rw [hcw]
      _ = x c * x w := map_mul x _ _
      _ = c * x w := by rw [hxc]
      _ = c * (c * w) := by rw [← hcw]
      _ = (c * c) * w := by rw [← mul_assoc]
      _ = w := by rw [hc2, one_mul]
  simpa using hx2

theorem s15_Lin_commSub_top_iSup {W : Type*} [CommGroup W] {ι : Sort*}
    (X : ι → Subgroup (MulAut W)) : commSub ⊤ (⨆ i, X i) = ⨆ i, commSub ⊤ (X i) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    have hC : ∀ w : W, x w * w⁻¹ ∈ ⨆ i, commSub ⊤ (X i) := by
      refine Subgroup.iSup_induction X
        (C := fun x => ∀ w : W, x w * w⁻¹ ∈ ⨆ i, commSub ⊤ (X i)) hx ?_ ?_ ?_
      · intro j y hy w
        exact Subgroup.mem_iSup_of_mem j
          (Subgroup.subset_closure ⟨y, hy, w, trivial, rfl⟩)
      · intro w
        simp
      · intro a b ha hb w
        have hamap : ∀ u ∈ (⨆ i, commSub ⊤ (X i)),
            a u ∈ (⨆ i, commSub ⊤ (X i)) := by
          intro u hu
          have h1 : a u * u⁻¹ ∈ (⨆ i, commSub ⊤ (X i)) := ha u
          rw [show a u = (a u * u⁻¹) * u by group]
          exact (⨆ i, commSub ⊤ (X i)).mul_mem h1 hu
        have hkey : (a * b) w * w⁻¹ =
            a (b w * w⁻¹) * (a w * w⁻¹) := by
          rw [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [hkey]
        exact (⨆ i, commSub ⊤ (X i)).mul_mem (hamap _ (hb w)) (ha w)
    exact hC w
  · exact iSup_le fun i => commSub_mono le_rfl (le_iSup X i)

theorem s15_Lin_rk_sSup_eq_finsum {W : Type*} [CommGroup W] [Finite W]
    {𝓤 : Set (Subgroup W)} (h : sSupIndep 𝓤) : rk ↥(sSup 𝓤) = ∑ᶠ U ∈ 𝓤, rk ↥U := by
  classical
  haveI : Fintype 𝓤 := (Set.toFinite 𝓤).fintype
  let H : 𝓤 → Subgroup W := Subtype.val
  have hind : iSupIndep H := (sSupIndep_iff 𝓤).mp h
  have hcomm : Pairwise fun i j : 𝓤 => ∀ x y : W, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  let φ := Subgroup.noncommPiCoprod hcomm
  have hφinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = sSup 𝓤 := by
    rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']
  have hcard : Nat.card ↥(sSup 𝓤) = ∏ i : 𝓤, Nat.card ↥(H i) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm.trans
      (Nat.card_pi (β := fun i : 𝓤 => ↥(H i)))
  rw [rk, hcard,
    padicValNat_prod_fintype (fun i : 𝓤 => Nat.card ↥(H i)) (fun i => Nat.card_pos.ne')]
  rw [finsum_mem_eq_subtype_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rk]

theorem s15_Lin_exists_hyperplane {W : Type*} [CommGroup W] [Finite W]
    {A B : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hBA : B < A) :
    ∃ E : Subgroup (MulAut W), B ≤ E ∧ E < A ∧ E3.mQuot A E = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set (Subgroup (MulAut W)) := {E | B ≤ E ∧ E < A}
  obtain ⟨E, hE⟩ := (Set.toFinite S).exists_maximal ⟨B, le_rfl, hBA⟩
  obtain ⟨hES, hEmax0⟩ := hE
  obtain ⟨hBE, hEltA⟩ := hES
  have hEmax : ∀ F : Subgroup (MulAut W), B ≤ F → F < A → E ≤ F → F ≤ E :=
    fun F hBF hFA hEF => hEmax0 ⟨hBF, hFA⟩ hEF
  have hsubset : (E : Set (MulAut W)) ⊂ (A : Set (MulAut W)) := by
    rw [Set.ssubset_def]
    refine ⟨fun x hx => hEltA.1 hx, ?_⟩
    intro hAE
    exact hEltA.2 fun x hx => hAE hx
  obtain ⟨a, haA, haE⟩ := Set.exists_of_ssubset hsubset
  let E' : Subgroup (MulAut W) := E ⊔ Subgroup.zpowers a
  have hE'E : E ≤ E' := le_sup_left
  have haE' : a ∈ E' := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hE'A : E' ≤ A := by
    apply sup_le hEltA.1
    rw [Subgroup.zpowers_le]
    exact haA
  have hZA : Subgroup.zpowers a ≤ A := le_sup_right.trans hE'A
  have hnotlt : ¬ E' < A := by
    intro hlt
    have hFE : E' ≤ E := hEmax E' (hBE.trans le_sup_left) hlt hE'E
    exact haE (hFE haE')
  have hAE' : A ≤ E' := by
    by_contra h
    exact hnotlt ⟨hE'A, h⟩
  have hE'Aeq : E' = A := le_antisymm hE'A hAE'
  have hrel : E.relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨a, haA, fun b hb => ?_⟩
    have hb' : b ∈ E ⊔ Subgroup.zpowers a := by
      change b ∈ E'
      exact hE'Aeq.symm ▸ hb
    obtain ⟨y, hyE, z, hz, hyz⟩ :=
      (mem_sup_of_commute (H := E) (K := Subgroup.zpowers a)
        (fun x hx y hy => hA.1 x (hEltA.1 hx) y (hZA hy))).mp hb'
    obtain hz1 | hza := zpow_eq_one_or_self_of_sq_eq_one (hA.2 a haA) hz
    · rw [hz1] at hyz
      have hbE : b ∈ E := by
        rw [← hyz]
        simpa using hyE
      refine Or.inr ⟨hbE, ?_⟩
      intro hbaE
      have ha : a ∈ E := by
        have h1 : b⁻¹ * (b * a) ∈ E := E.mul_mem (E.inv_mem hbE) hbaE
        rwa [inv_mul_cancel_left] at h1
      exact haE ha
    · rw [hza] at hyz
      have hbaE : b * a ∈ E := by
        rw [← hyz]
        have haa : a * a = 1 := by simpa [pow_two] using hA.2 a haA
        rw [mul_assoc, haa, mul_one]
        exact hyE
      refine Or.inl ⟨hbaE, ?_⟩
      intro hbE
      have ha : a ∈ E := by
        have h1 : y⁻¹ * b ∈ E := E.mul_mem (E.inv_mem hyE) hbE
        rw [← hyz] at h1
        rwa [inv_mul_cancel_left] at h1
      exact haE ha
  refine ⟨E, hBE, hEltA, ?_⟩
  show padicValNat 2 (E.relIndex A) = 1
  rw [hrel, padicValNat_self]

theorem s15_Lin_map_eq_iff_mem_stabSub {W : Type*} [CommGroup W] [Finite W] (U : Subgroup W)
    (e : MulAut W) : U.map e.toMonoidHom = U ↔ e ∈ stabSub U := by
  constructor
  · intro h
    rw [mem_stabSub]
    intro u
    constructor
    · intro heu
      have h1 : e u ∈ U.map e.toMonoidHom := by rwa [h]
      obtain ⟨t, ht, htu⟩ := Subgroup.mem_map.mp h1
      have htu' : t = u := e.injective htu
      rwa [htu'] at ht
    · intro hu
      have h1 : e u ∈ U.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hu
      rwa [h] at h1
  · intro h
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (mem_stabSub.mp h u).mpr hu
    · intro hx
      refine ⟨e.symm x, (mem_stabSub.mp h (e.symm x)).mp ?_, by simp⟩
      simpa using hx

theorem s15_Lin_rk_map {W : Type*} [CommGroup W] (U : Subgroup W) (e : MulAut W) :
    rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem s15_Lin_relIndex_centralizer_le {E F : Subgroup G} {v : G}
    (h : ∀ e ∈ E, v⁻¹ * (e⁻¹ * v * e) ∈ F) :
    (centralizer ({v} : Set G)).relIndex E ≤ Nat.card F := by
  classical
  let C : Subgroup G := centralizer ({v} : Set G)
  let φ : ↥E → ↥F := fun e =>
    ⟨v⁻¹ * (e.1 * v * e.1⁻¹), by simpa using h e.1⁻¹ (E.inv_mem e.2)⟩
  have hφ : ∀ a b : ↥E, QuotientGroup.leftRel (C.subgroupOf E) a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    apply Subtype.ext
    have hv : a.1 * v * a.1⁻¹ = b.1 * v * b.1⁻¹ := by
      have hc : a.1⁻¹ * b.1 * v = v * (a.1⁻¹ * b.1) :=
        Subgroup.mem_centralizer_singleton_iff.mp hab
      have key : b.1 * v * b.1⁻¹ = a.1 * v * a.1⁻¹ := by
        calc b.1 * v * b.1⁻¹
            = a.1 * (a.1⁻¹ * b.1 * v) * b.1⁻¹ := by group
          _ = a.1 * (v * (a.1⁻¹ * b.1)) * b.1⁻¹ := by rw [hc]
          _ = a.1 * v * a.1⁻¹ := by group
      exact key.symm
    show v⁻¹ * (a.1 * v * a.1⁻¹) = v⁻¹ * (b.1 * v * b.1⁻¹)
    rw [hv]
  let ψ : ↥E ⧸ (C.subgroupOf E) → ↥F := Quotient.lift φ hφ
  have hψ : Function.Injective ψ := by
    intro q q' hq
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective q'
    change φ a = φ b at hq
    apply Quotient.sound
    show QuotientGroup.leftRel (C.subgroupOf E) a b
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hv : a.1 * v * a.1⁻¹ = b.1 * v * b.1⁻¹ :=
      mul_left_cancel (Subtype.ext_iff.mp hq)
    have hc : b.1⁻¹ * a.1 ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcv : (b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹ = v := by
        have h := congrArg (fun x => b.1⁻¹ * x * b.1) hv
        have h1 : b.1⁻¹ * (a.1 * v * a.1⁻¹) * b.1 =
            (b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹ := by group
        have h2 : b.1⁻¹ * (b.1 * v * b.1⁻¹) * b.1 = v := by group
        rwa [h1, h2] at h
      calc (b.1⁻¹ * a.1) * v
          = ((b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹) * (b.1⁻¹ * a.1) := by group
        _ = v * (b.1⁻¹ * a.1) := by rw [hcv]
    have h : a.1⁻¹ * b.1 = (b.1⁻¹ * a.1)⁻¹ := by group
    change a.1⁻¹ * b.1 ∈ C
    rw [h]
    exact C.inv_mem hc
  show (C.subgroupOf E).index ≤ Nat.card F
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective ψ hψ

theorem s15_Lin_odd_card_of_isNilpotent {H : Type*} [Group H] [Finite H]
    (hn : Group.IsNilpotent H)
    (hN : ∀ N : Subgroup H, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤) :
    Odd (Nat.card H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2dvd : 2 ∣ Nat.card H :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨e⟩ := (Group.isNilpotent_of_finite_tfae (G := H)).out 1 5 |>.mp hn
  have hp2mem : (2 : ℕ) ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
  let p₂ : (Nat.card H).primeFactors := ⟨2, hp2mem⟩
  haveI : Fact (Nat.Prime (p₂ : ℕ)) := ⟨by simpa [p₂] using Nat.prime_two⟩
  let P₀ : Sylow (p₂ : ℕ) H := Classical.arbitrary _
  let Fam : (Nat.card H).primeFactors → Type _ := fun p => ∀ P : Sylow p H, (↑P : Subgroup H)
  let Gfam : Sylow (p₂ : ℕ) H → Type _ := fun P => (↑P : Subgroup H)
  let π : H →* Gfam P₀ :=
    (Pi.evalMonoidHom Gfam P₀).comp ((Pi.evalMonoidHom Fam p₂).comp (e.symm : H →* _))
  have hπ : Function.Surjective π := by
    intro y
    refine ⟨e (Pi.mulSingle p₂ (Pi.mulSingle P₀ y)), ?_⟩
    simp [π, Pi.mulSingle_eq_same]
  have hfact : Nat.card ↥(↑P₀ : Subgroup H) = 2 ^ (Nat.card H).factorization 2 := by
    have h := Sylow.card_eq_multiplicity P₀
    simpa [p₂] using h
  have hidx : ∃ n : ℕ, π.ker.index = 2 ^ n := by
    refine ⟨(Nat.card H).factorization 2, ?_⟩
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top, hfact]
  have hker : π.ker = ⊤ := hN π.ker (inferInstance : π.ker.Normal) hidx
  have hcard1 : Nat.card ↥(↑P₀ : Subgroup H) = 1 := by
    have hi := Subgroup.index_ker π
    rw [hker, Subgroup.index_top, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top] at hi
    exact hi.symm
  have hpos : 0 < (Nat.card H).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2dvd
  have h2le : 2 ≤ Nat.card ↥(↑P₀ : Subgroup H) := by
    rw [hfact]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.card H).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem s15_Lin_odd_card_iSup {A : Type*} [Group A] [Finite A] {ι : Type*}
    (K : ι → Subgroup A) (hodd : ∀ i, Odd (Nat.card (K i)))
    (hcomm : ∀ i j, K i ≠ K j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y) :
    Odd (Nat.card ↥(⨆ i, K i)) := by
  classical
  haveI : Fintype (Set.range K) := (Set.toFinite (Set.range K)).fintype
  let H : Set.range K → Subgroup A := Subtype.val
  have hcomm' : Pairwise fun i j : Set.range K =>
      ∀ x y : A, x ∈ H i → y ∈ H j → Commute x y := by
    rintro ⟨Si, hi⟩ ⟨Sj, hj⟩ hij x y hx hy
    obtain ⟨i, rfl⟩ := hi
    obtain ⟨j, rfl⟩ := hj
    have hne : K i ≠ K j := by
      rintro h
      exact hij (Subtype.ext h)
    exact hcomm i j hne x hx y hy
  let φ := Subgroup.noncommPiCoprod hcomm'
  have hrange : φ.range = ⨆ i : Set.range K, H i := by
    rw [Subgroup.noncommPiCoprod_range]
  have hsup : (⨆ i : Set.range K, H i) = ⨆ i : ι, K i := by
    simpa [H] using iSup_range' (fun S : Subgroup A => S) K
  have hcard_eq : Nat.card ↥(⨆ i : ι, K i) = Nat.card ↥φ.range := by
    rw [← hsup, ← hrange]
  have hodd' : ∀ i : Set.range K, Odd (Nat.card ↥(H i)) := by
    rintro ⟨S, ⟨j, rfl⟩⟩
    exact hodd j
  have hprod_odd : Odd (∏ i : Set.range K, Nat.card ↥(H i)) :=
    odd_prod_finset Finset.univ _ (fun i _ => hodd' i)
  have hdvd : Nat.card ↥(⨆ i : ι, K i) ∣ ∏ i : Set.range K, Nat.card ↥(H i) := by
    rw [hcard_eq, ← Nat.card_pi]
    exact Subgroup.card_range_dvd φ
  exact Odd.of_dvd_nat hprod_odd hdvd

theorem s15_Lin_exists_component_or_isNilpotent {A : Type} [Group A] [Finite A]
    {H : Subgroup A} (hF : Fstar H = H) :
    (∃ C : Subgroup A, CFSG.Open.IsComponentOf C H) ∨ Group.IsNilpotent ↥H := by
  have htop : CFSG.Open.genFittingFStar ↥H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    change Fstar H = (⊤ : Subgroup ↥H).map H.subtype
    rw [hF, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  by_cases hc : ∃ L : Subgroup ↥H, CFSG.Open.IsComponentOf L ⊤
  · obtain ⟨L, hL⟩ := hc
    refine Or.inl ⟨L.map H.subtype, ?_⟩
    refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
    · have hsn := open_isSubnormal_map H.subtype hL.2.1
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hsn
    · exact open_isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm hL.2.2
  · have hset : {L : Subgroup ↥H | CFSG.Open.IsComponentOf L ⊤} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro L hL
      exact hc ⟨L, hL⟩
    have hlayer : CFSG.Open.genFittingLayer ↥H = ⊥ := by
      rw [CFSG.Open.genFittingLayer.eq_sSup, hset, sSup_empty]
    have hfit : CFSG.fittingSubgroup ↥H = ⊤ := by
      have hsup := CFSG.Open.genFittingFStar.eq_sup ↥H
      rw [htop, hlayer, sup_bot_eq] at hsup
      exact hsup.symm
    have hnil : Group.IsNilpotent (⊤ : Subgroup ↥H) :=
      hfit ▸ (inferInstance : Group.IsNilpotent (CFSG.fittingSubgroup ↥H))
    letI : Group.IsNilpotent (⊤ : Subgroup ↥H) := hnil
    exact Or.inr (Group.nilpotent_of_mulEquiv Subgroup.topEquiv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
