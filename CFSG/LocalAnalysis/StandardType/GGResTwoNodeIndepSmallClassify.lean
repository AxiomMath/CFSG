module

public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.OrderBound
public import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.GGRCLinWeyl
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSimilarity
public import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement

namespace ZS

theorem natCard_orthogonalGroup_five {V : Type} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] {Q : QuadraticForm (ZMod 5) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 5) V = 5) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 18720000 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 5) (V := V)
    (Q := Q) (n := 2) (by rw [ZMod.ringChar_zmod_n]; norm_num) hQ (by omega)
  have hcardZ : Nat.card (ZMod 5) = 5 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcardZ] at h
  rw [show (2 : ℕ) = 1 + 1 by norm_num] at h
  rw [Finset.prod_Icc_succ_top (by norm_num)] at h
  norm_num at h
  have hOeq : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      Nat.card {x : V ≃ₗ[ZMod 5] V // ∀ m, Q (x m) = Q m} :=
    Nat.card_congr (Equiv.subtypeEquivRight
      (fun x => TauCeti.QuadraticMap.mem_orthogonalGroup_iff))
  rw [hOeq]
  exact_mod_cast h

theorem commutator_index_orthogonalGroup_five {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NeZero (2 : K)]
    (hodd : Odd (Nat.card K)) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 5) :
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 4 := by
  have : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne 2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hSO : (QuadraticMap.specialOrthogonalWithin Q).index = 2 :=
    TauCeti.QuadraticMap.index_specialOrthogonalWithin hQ'
  have hrel : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).relIndex
      (QuadraticMap.specialOrthogonalWithin Q) = 2 :=
    CFSG.ClassicalGroups.Orthogonal.commutator_relIndex_specialOrthogonalWithin_five
      hodd Q hQ hdim
  have hle : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤
      QuadraticMap.specialOrthogonalWithin Q := by
    intro g hg
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
    have hker := Abelianization.commutator_subset_ker (QuadraticMap.orthogonalDet Q) hg
    simpa only [MonoidHom.mem_ker, QuadraticMap.orthogonalDet_apply] using hker
  have h := Subgroup.relIndex_mul_index hle
  rw [hrel, hSO] at h
  omega

theorem monomial_closure {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (f : Module.Basis (Fin n) (ZMod p) V) (S : Set (V ≃ₗ[ZMod p] V))
    (hS : ∀ a ∈ S, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) :
    ∀ a ∈ Subgroup.closure S, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) := by
  let M : Subgroup (V ≃ₗ[ZMod p] V) :=
    { carrier := {a | ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)}
      one_mem' := ⟨1, fun _ => 1, fun _ => one_ne_zero, fun i => by simp⟩
      mul_mem' := by
        rintro a b ⟨σ, c, hc, ha⟩ ⟨τ, d, hd, hb⟩
        refine ⟨σ * τ, fun i => d i * c (τ i), fun i => mul_ne_zero (hd _) (hc _), ?_⟩
        intro i
        rw [LinearEquiv.mul_apply, hb i, map_smul, ha (τ i), smul_smul]
        simp
      inv_mem' := by
        rintro a ⟨σ, c, hc, ha⟩
        refine ⟨σ.symm, fun i => (c (σ.symm i))⁻¹, fun i => inv_ne_zero (hc _), ?_⟩
        intro i
        have h := ha (σ.symm i)
        rw [Equiv.apply_symm_apply] at h
        have hf : f i = (c (σ.symm i))⁻¹ • a (f (σ.symm i)) := by
          rw [h, smul_smul, inv_mul_cancel₀ (hc _), one_smul]
        rw [hf, map_smul]
        simp }
  exact fun a ha => (Subgroup.closure_le M).mpr (fun x hx => hS x hx) ha

theorem monomial_reindex {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (f : Module.Basis (Fin n) (ZMod p) V) (e : Fin n ≃ Fin p)
    (h : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin p)) (c : Fin p → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a ((f.reindex e) i) = c i • (f.reindex e) (σ i) := by
  intro a ha
  obtain ⟨σ, c, hc, hσc⟩ := h a ha
  refine ⟨e.symm.trans (σ.trans e), fun i => c (e.symm i), fun i => hc _, ?_⟩
  intro i
  have hσ' : (e.symm.trans (σ.trans e)) i = e (σ (e.symm i)) := by
    simp only [Equiv.trans_apply]
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hσ', Equiv.symm_apply_apply, hσc]


private theorem linWeyl_of_monomial_basis {p n : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (f : Module.Basis (Fin n) (ZMod p) V) (hn : n = p) (hp4 : 4 ≤ p)
    (hirr : AbsIrred p A) (hgen : ReflGen p A)
    (hPm1 : ∀ f : Module.Basis (Fin p) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin p)) (c : Fin p → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin p) (ZMod p) V,
        ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin p)) (c : Fin p → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i))
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) :
    LinWeyl p A := by
  let e : Fin n ≃ Fin p := finCongr hn
  have hmon' := monomial_reindex f e hmon
  obtain ⟨b', hb'⟩ := hPm1 (f.reindex e) hmon'
  have hgen' : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := by
    have h := hgen
    rw [ReflGen] at h
    apply le_antisymm
    · conv_lhs => rw [h]
      apply Subgroup.closure_mono
      intro t ht
      exact ⟨ht.1, ht.2⟩
    · refine (Subgroup.closure_le (K := A)).mpr ?_
      intro r hr
      exact hr.1
  exact CFSG.StandardType.ggRC_linWeyl_of_monomial_pm1 (p := p) (by omega) hp4
    b' A hirr hgen' hb'

theorem linWeyl_of_smallDim_p5_p7 {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hUse : UseInput) (hp : p = 5 ∨ p = 7)
    (hdim : Module.finrank (ZMod p) V = p)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : AbsIrred p A) (hgen : ReflGen p A)
    (hNT : ∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧
      ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card A ≤ p ^ p * (6 * (p - 1) * Nat.factorial p))
    (hPm1 : ∀ f : Module.Basis (Fin p) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin p)) (c : Fin p → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin p) (ZMod p) V,
        ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin p)) (c : Fin p → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i)) :
    LinWeyl p A := by
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod p] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hdim3 : 3 ≤ Module.finrank (ZMod p) V := by
    rw [hdim]
    rcases hp with rfl | rfl <;> norm_num
  have hp4 : 4 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hfamily : Family p A := hUse p V A hp2 hdim3 hgen hirr
  rcases hfamily with hW | hSL | ⟨Q, hQ, hA⟩ | ⟨Q, c, hQ, hc, hA⟩
    | ⟨f, i₀, i₁, ζ, m, hi, hm, hζ, hA⟩
    | ⟨f, i₀, i₁, ζ, m, hi, hm, hζ, hA⟩
    | ⟨k, hadm, hdimk, hord, hcen, hdmax, hone, hmodel⟩
    | ⟨hpne5, hdim4, _hcard4, hneg, hdmax, hone⟩
  · exact hW
  ·
    have hpow : p ^ (p * (p - 1) / 2) ≤ Nat.card A :=
      pow_le_card_of_sl_le (p := p) (V := V) (n := p) hdim A
        (fun g hg => (hSL g).mpr (Or.inl hg))
    have hle : p ^ (p * (p - 1) / 2) ≤ p ^ p * (6 * (p - 1) * Nat.factorial p) :=
      le_trans hpow hcard
    rcases hp with rfl | rfl <;> norm_num at hle
  ·
    rcases hp with rfl | rfl
    · have hAO : A = TauCeti.QuadraticMap.orthogonalGroup Q := by
        ext g
        simpa only [IsIsom, TauCeti.QuadraticMap.mem_orthogonalGroup_iff] using hA g
      have hAcard : Nat.card A = 18720000 := by
        rw [hAO]
        exact natCard_orthogonalGroup_five hQ (by simpa using hdim)
      have hbound : Nat.card A ≤ 9000000 := by
        norm_num at hcard ⊢
        exact hcard
      omega
    · have hGG : GGOrthType A := ggOrthType_of_orth hQ hA
      have hpow := pow_le_card_of_ggOrthType (p := 7) (U := V) (n := 7) (by norm_num)
        (by simpa using hdim) (by norm_num) hGG
      have h8 : 8 * Nat.card A ≤ 8 * (7 ^ 7 * (6 * (7 - 1) * Nat.factorial 7)) :=
        Nat.mul_le_mul_left 8 hcard
      have hle := le_trans hpow h8
      norm_num at hle
  ·
    rcases hp with rfl | rfl
    · have hdim5 : Module.finrank (ZMod 5) V = 5 := by simpa using hdim
      have h2z : (2 : ZMod 5) ≠ 0 := by
        intro h
        have hdvd : (5 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 5).mp h
        exact (by norm_num : ¬ (5 : ℕ) ∣ 2) hdvd
      have : NeZero (2 : ZMod 5) := ⟨h2z⟩
      have : Invertible (2 : ZMod 5) := invertibleOfNonzero h2z
      have hodd : Odd (Nat.card (ZMod 5)) := by
        rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num
      obtain ⟨a, -, hQa⟩ := CFSG.ClassicalGroups.Orthogonal.PolarNondegOn.exists_map_eq
        (K := ZMod 5) (V := V) (Q := Q) (S := ⊤) h2z
        (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ)
        (by rw [finrank_top, hdim5]; norm_num) c
      let r : V ≃ₗ[ZMod 5] V := CFSG.ClassicalGroups.Orthogonal.reflect Q a
      have hrClass : r ∈ ClassRefl 5 Q c :=
        (mem_classRefl_iff (p := 5) (U := V) (by norm_num) hQ hc r).mpr ⟨a, hQa, rfl⟩
      have hrRefl : IsRefl 5 r := hrClass.1
      let O : Subgroup (V ≃ₗ[ZMod 5] V) := TauCeti.QuadraticMap.orthogonalGroup Q
      let Ω : Subgroup O := commutator O
      have hOcard : Nat.card O = 18720000 := natCard_orthogonalGroup_five hQ hdim5
      have hΩindex : Ω.index = 4 :=
        commutator_index_orthogonalGroup_five (K := ZMod 5) (V := V) hodd hQ hdim5
      have hΩcard : Nat.card Ω = 4680000 := by
        have h := Subgroup.index_mul_card Ω
        rw [hΩindex, hOcard] at h
        omega
      let B : Subgroup (V ≃ₗ[ZMod 5] V) := Ω.map O.subtype
      have hBcard : Nat.card B = Nat.card Ω :=
        Subgroup.card_map_of_injective O.subtype_injective
      have hBcomm : B = ⁅O, O⁆ := Subgroup.map_subtype_commutator O
      have hBA : B ≤ A := by
        rw [hBcomm, hA]
        refine Subgroup.commutator_le.mpr ?_
        intro g hg h hh
        simpa only [commutatorElement_def] using
          commutator_mem_closure_classRefl (p := 5) (U := V) (by norm_num) (by omega) hQ hc
            (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg)
            (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hh)
      have hBneA : B ≠ A := by
        intro hEq
        have hrA : r ∈ A := by
          rw [hA]
          exact Subgroup.subset_closure hrClass
        have hrB : r ∈ B := by rw [hEq]; exact hrA
        have hBdet : ∀ b ∈ B, LinearEquiv.det b = 1 := by
          intro b hb
          rw [hBcomm] at hb
          have htop : ⁅O, O⁆ ≤ ⁅(⊤ : Subgroup (V ≃ₗ[ZMod 5] V)), ⊤⁆ :=
            Subgroup.commutator_mono le_top le_top
          have hker : ⁅(⊤ : Subgroup (V ≃ₗ[ZMod 5] V)), ⊤⁆ ≤
              (LinearEquiv.det : (V ≃ₗ[ZMod 5] V) →* (ZMod 5)ˣ).ker := by
            simpa only [commutator_def] using
              Abelianization.commutator_subset_ker
                (LinearEquiv.det : (V ≃ₗ[ZMod 5] V) →* (ZMod 5)ˣ)
          exact htop.trans hker hb
        have h1 : LinearEquiv.det r = 1 := hBdet r hrB
        have h2 : LinearEquiv.det r = -1 :=
          det_eq_neg_one_of_isRefl (p := 5) (U := V) (by norm_num) hrRefl
        rw [h2] at h1
        have hne : (-1 : (ZMod 5)ˣ) ≠ 1 := by
          intro h
          have h' : ((-1 : (ZMod 5)ˣ) : ZMod 5) = ((1 : (ZMod 5)ˣ) : ZMod 5) :=
            congrArg Units.val h
          have : Fact (2 < 5) := ⟨by norm_num⟩
          exact ZMod.neg_one_ne_one (by simpa using h')
        exact hne h1
      have hBlt : B < A := lt_of_le_of_ne hBA hBneA
      have hBpos : 0 < Nat.card B := Nat.card_pos
      have hApos : 0 < Nat.card A := Nat.card_pos
      have hdvd : Nat.card B ∣ Nat.card A := Subgroup.card_dvd_of_le hBA
      have hltcard : Nat.card B < Nat.card A := Subgroup.card_lt_of_lt hBlt
      obtain ⟨k, hk⟩ := hdvd
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k
          · rw [Nat.mul_zero] at hk
            omega
          · rw [Nat.mul_one] at hk
            omega
        · exact h
      have hAge : 2 * Nat.card B ≤ Nat.card A := by
        calc 2 * Nat.card B = Nat.card B * 2 := by ring
          _ ≤ Nat.card B * k := Nat.mul_le_mul_left _ hk2
          _ = Nat.card A := hk.symm
      have hAge' : 9360000 ≤ Nat.card A := by
        rw [hBcard, hΩcard] at hAge
        norm_num at hAge ⊢
        exact hAge
      have hbound : Nat.card A ≤ 9000000 := by
        norm_num at hcard ⊢
        exact hcard
      omega
    · have hGG : GGOrthType A := ggOrthType_of_orthClass (p := 7) (U := V) (by norm_num)
        (by omega) hQ hc hA
      have hpow := pow_le_card_of_ggOrthType (p := 7) (U := V) (n := 7) (by norm_num)
        (by simpa using hdim) (by norm_num) hGG
      have h8 : 8 * Nat.card A ≤ 8 * (7 ^ 7 * (6 * (7 - 1) * Nat.factorial 7)) :=
        Nat.mul_le_mul_left 8 hcard
      have hle := le_trans hpow h8
      norm_num at hle
  ·
    refine linWeyl_of_monomial_basis (p := p) f ?_ hp4 hirr hgen hPm1 ?_
    · have h1 := Module.finrank_eq_card_basis f
      rw [Fintype.card_fin] at h1
      exact h1.symm.trans hdim
    · rw [hA]
      change ∀ a ∈ Subgroup.closure (Set.range (permMap p f) ∪
        {diagMap p f (pairUnit p i₀ i₁ ζ)}), _
      refine monomial_closure f (Set.range (permMap p f) ∪
        {diagMap p f (pairUnit p i₀ i₁ ζ)}) ?_
      intro a ha
      rcases ha with ⟨σ, rfl⟩ | ha
      · exact ⟨σ, fun _ => 1, fun _ => one_ne_zero, fun i => by simp [permMap_apply_basis]⟩
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨1, fun i => ((pairUnit p i₀ i₁ ζ i : (ZMod p)ˣ) : ZMod p),
          fun i => Units.ne_zero _, fun i => by simp [diagMap_apply_basis]⟩
  ·
    refine linWeyl_of_monomial_basis (p := p) f ?_ hp4 hirr hgen hPm1 ?_
    · have h1 := Module.finrank_eq_card_basis f
      rw [Fintype.card_fin] at h1
      exact h1.symm.trans hdim
    · rw [hA]
      change ∀ a ∈ Subgroup.closure (Set.range (permMap p f) ∪
        {diagMap p f (fun i => if i = i₀ then -1 else 1),
          diagMap p f (pairUnit p i₀ i₁ ζ)}), _
      refine monomial_closure f (Set.range (permMap p f) ∪
        {diagMap p f (fun i => if i = i₀ then -1 else 1),
          diagMap p f (pairUnit p i₀ i₁ ζ)}) ?_
      intro a ha
      rcases ha with ⟨σ, rfl⟩ | ha
      · exact ⟨σ, fun _ => 1, fun _ => one_ne_zero, fun i => by simp [permMap_apply_basis]⟩
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact ⟨1, fun i => ((if i = i₀ then -1 else 1 : (ZMod p)ˣ) : ZMod p),
            fun i => Units.ne_zero _, fun i => by simp [diagMap_apply_basis]⟩
        · exact ⟨1, fun i => ((pairUnit p i₀ i₁ ζ i : (ZMod p)ˣ) : ZMod p),
            fun i => Units.ne_zero _, fun i => by simp [diagMap_apply_basis]⟩
  ·
    rcases hp with rfl | rfl
    · have hdeg5 : k.deg = 5 := by omega
      have hdeg_ne : ∀ j : ExcRow, j ≠ ExcRow.K5 → j.deg ≠ 5 := by
        intro j hj
        cases j <;> first | exact (hj rfl).elim | norm_num [ExcRow.deg]
      have hk : k = ExcRow.K5 := by
        by_contra hne
        exact hdeg_ne k hne hdeg5
      subst hk
      simp only [ExcRow.ord] at hord
      norm_num at hord
      have hdim5 : Module.finrank (ZMod 5) V = 5 := by simpa using hdim
      let b : Module.Basis (Fin 5) (ZMod 5) V := Module.finBasisOfFinrankEq (ZMod 5) V hdim5
      let e1 := Matrix.GeneralLinearGroup.toLin' (b := b)
      let e2 := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) V
      have hVcard : Nat.card (V ≃ₗ[ZMod 5] V) = 226614960000000000 := by
        have hV : Nat.card (V ≃ₗ[ZMod 5] V) = Nat.card (GL (Fin 5) (ZMod 5)) :=
          (Nat.card_congr ((e1.trans e2).toEquiv)).symm
        rw [hV, Matrix.card_GL_field]
        norm_num [Fin.prod_univ_five]
      have hdvd : Nat.card A ∣ Nat.card (V ≃ₗ[ZMod 5] V) :=
        Subgroup.card_subgroup_dvd_card A
      rw [hord, hVcard] at hdvd
      exact ((by norm_num : ¬ (51840 ∣ 226614960000000000)) hdvd).elim
    · have hdeg : ∀ j : ExcRow, j.deg ≠ 7 := by
        intro j
        cases j <;> simp [ExcRow.deg]
      have hval : k.deg = 7 := by omega
      exact (hdeg k hval).elim
  ·
    rcases hp with rfl | rfl
    · exact (hpne5 rfl).elim
    · exfalso; omega

end ZS

end CFSG.StandardType

end
