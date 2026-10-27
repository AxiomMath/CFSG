module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaEqTransvection
public import CFSG.LocalAnalysis.StandardType.GGOmegaCentralizerTransvection

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.AUTSL

@[expose] def GGGraphInvConjBy {d : ℕ} {K : Type} [Field K] (Φ : QuadraticForm K (Fin d → K))
    (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K) : Prop :=
  ∀ g : matrixDerived Φ, ∃ h : s * (g : GL (Fin d) K) * s⁻¹ ∈ matrixDerived Φ,
    α g = ⟨s * (g : GL (Fin d) K) * s⁻¹, h⟩

private theorem ggOmW6cA_conjBy_val_eq {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s) {g : matrixDerived Φ} (hg : α g = g) :
    s * (g : GL (Fin d) K) * s⁻¹ = (g : GL (Fin d) K) := by
  obtain ⟨h, hh⟩ := hconj g
  have h2 : (α g : GL (Fin d) K) = (g : GL (Fin d) K) := congrArg Subtype.val hg
  rw [hh] at h2
  simpa using h2

theorem ggGraphInv_fixSubgroup_eq_of_conjBy {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s) :
    ggFixSubgroup α =
      (Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ matrixDerived Φ).subgroupOf
        (matrixDerived Φ) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, g.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := ggOmW6cA_conjBy_val_eq Φ α s hconj hg
    have h3 : s * (g : GL (Fin d) K) = (g : GL (Fin d) K) * s := by
      have h4 := congrArg (· * s) h
      simpa [mul_assoc] using h4
    exact h3.symm
  · intro hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hg
    obtain ⟨hgs, -⟩ := hg
    obtain ⟨h, hh⟩ := hconj g
    apply Subtype.ext
    rw [hh]
    show s * (g : GL (Fin d) K) * s⁻¹ = (g : GL (Fin d) K)
    rw [← hgs, mul_assoc, mul_inv_cancel, mul_one]

theorem ggGraphInv_conjBy_commute {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s) (b : matrixDerived Φ) (hb : α b = b) :
    s * (b : GL (Fin d) K) = (b : GL (Fin d) K) * s := by
  have h := ggOmW6cA_conjBy_val_eq Φ α s hconj hb
  have h3 : s * (b : GL (Fin d) K) = (b : GL (Fin d) K) * s := by
    have h4 := congrArg (· * s) h
    simpa [mul_assoc] using h4
  exact h3

theorem ggGraphInv_odd_orderOf {C : Type} [Group C] {b : C} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hb1 : b ≠ 1) (hbp : b ^ p = 1) : Odd (orderOf b) := by
  have hdvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hbp
  rcases hp.eq_one_or_self_of_dvd (orderOf b) hdvd with h1 | hp_eq
  · exact absurd ((orderOf_eq_one_iff).mp h1) hb1
  · rw [hp_eq]
    exact (hp.eq_two_or_odd').resolve_left hp2

theorem ggGraphInv_component_false_of_solvable {G : Type} [Group G] {X L : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hL : IsComponentOf L X) : False := by
  have hLX : L ≤ X := hL.1
  have hcomm : commutator ↥L = ⊤ := hL.2.2.1
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hsimple
  haveI : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLX)
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hcomm
  haveI : Nontrivial ↥L :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact Group.IsPerfect.not_isSolvable ↥L inferInstance

private theorem ggOmW6cA_inner_range_normal (C : Type) [Group C] :
    ((MulAut.conj : C →* MulAut C).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc⟩ := hn
  rw [← hc]
  refine ⟨g c, ?_⟩
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private theorem ggOmW6cA_card_quotient_inner_le (C : Type) [Group C] [Finite C]
    (C' : Subgroup (MulAut C))
    (hsup : ∀ α : MulAut C, ∃ i ∈ (MulAut.conj : C →* MulAut C).range, ∃ c ∈ C', α = i * c)
    (hcard : Nat.card C' ≤ 2) :
    Nat.card (MulAut C ⧸ (MulAut.conj : C →* MulAut C).range) ≤ 2 := by
  haveI hIn : ((MulAut.conj : C →* MulAut C).range).Normal := ggOmW6cA_inner_range_normal C
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)).comp C'.subtype) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨i, hi, c, hc, ha⟩ := hsup a
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)) c =
      (QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)) a
    have hi1 : (QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)) i = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff i).mpr hi
    rw [ha, map_mul, hi1, one_mul]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hcard

private theorem ggOmW6cA_index_subgroupOf_le_card_quotient (C : Type) [Group C] [Finite C]
    (S : Subgroup (MulAut C)) :
    (((MulAut.conj : C →* MulAut C).range).subgroupOf S).index ≤
      Nat.card (MulAut C ⧸ (MulAut.conj : C →* MulAut C).range) := by
  haveI hIn : ((MulAut.conj : C →* MulAut C).range).Normal := ggOmW6cA_inner_range_normal C
  have hker : MonoidHom.ker
      ((QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)).comp S.subtype) =
      ((MulAut.conj : C →* MulAut C).range).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)) (x : MulAut C) = 1 ↔
      (x : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range
    rw [QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff (x : MulAut C)
  rw [Subgroup.index_eq_card]
  calc Nat.card (S ⧸ ((MulAut.conj : C →* MulAut C).range).subgroupOf S)
      = Nat.card (MonoidHom.range
          ((QuotientGroup.mk' ((MulAut.conj : C →* MulAut C).range)).comp S.subtype)) := by
        rw [← hker]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    _ ≤ Nat.card (MulAut C ⧸ (MulAut.conj : C →* MulAut C).range) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective

theorem ggGraphInv_outTwoPartLeTwo_of_mul {C : Type} [Group C] [Finite C]
    (C' : Subgroup (MulAut C))
    (hsup : ∀ α : MulAut C, ∃ i ∈ (MulAut.conj : C →* MulAut C).range, ∃ c ∈ C', α = i * c)
    (hcard : Nat.card C' ≤ 2) :
    GGOutTwoPartLeTwo C := by
  intro S _hS
  exact (ggOmW6cA_index_subgroupOf_le_card_quotient C S).trans
    (ggOmW6cA_card_quotient_inner_le C C' hsup hcard)

private lemma ggOmW6cD_mem_matrixOrthogonal_iff {d : ℕ} {K : Type} [Field K]
    (Q : QuadraticForm K (Fin d → K)) (A : GL (Fin d) K) :
    A ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Q ↔ A ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff]
  constructor
  · intro h v
    rw [matrixLinearEquiv_apply]
    exact h v
  · intro h v
    exact h v

private lemma ggOmW6cD_conj_val {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (u : matrixDerived Φ) (w : Fin d → K) (hw : Φ w ≠ 0)
    (α : MulAut (matrixDerived Φ))
    (hα : α = MulAut.conj u * reflAut Φ w hw) :
    ∀ g : matrixDerived Φ,
      (α g).val = ((u : GL (Fin d) K) * reflMat Φ w hw) * (g : GL (Fin d) K)
        * ((u : GL (Fin d) K) * reflMat Φ w hw)⁻¹ := by
  intro g
  rw [hα]
  simp only [MulAut.mul_apply, MulAut.conj_apply, reflAut_apply_val, Subgroup.coe_mul,
    Subgroup.coe_inv]
  group

private lemma ggOmW6cD_sq_comm_of_involution {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hα2 : α * α = 1)
    (hval : ∀ g : matrixDerived Φ, (α g).val = s * (g : GL (Fin d) K) * s⁻¹) :
    ∀ g : matrixDerived Φ,
      (s * s) * (g : GL (Fin d) K) = (g : GL (Fin d) K) * (s * s) := by
  intro g
  have hαα : α (α g) = g := by
    have h1 := congrArg (fun φ : MulAut (matrixDerived Φ) => φ g) hα2
    simpa [MulAut.mul_apply] using h1
  have h1 : (g : GL (Fin d) K) = s * ((α g : matrixDerived Φ) : GL (Fin d) K) * s⁻¹ := by
    calc (g : GL (Fin d) K) = ((α (α g) : matrixDerived Φ) : GL (Fin d) K) := by rw [hαα]
      _ = s * ((α g : matrixDerived Φ) : GL (Fin d) K) * s⁻¹ := hval (α g)
  have h2 : ((α g : matrixDerived Φ) : GL (Fin d) K) = s * (g : GL (Fin d) K) * s⁻¹ :=
    hval g
  have hg : (g : GL (Fin d) K) = (s * s) * (g : GL (Fin d) K) * (s * s)⁻¹ := by
    conv_lhs => rw [h1, h2]
    group
  conv_rhs => rw [hg]
  group

private lemma ggOmW6cD_sq_eq_one {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (Fin d → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h5 : 5 ≤ Module.finrank K (Fin d → K)) (s : GL (Fin d) K)
    (hsO : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    (hcomm : ∀ g : matrixDerived Φ,
      (s * s) * (g : GL (Fin d) K) = (g : GL (Fin d) K) * (s * s)) :
    s * s = 1 := by
  have hsIso : s ∈ matrixIsometries Φ := (ggOmW6cD_mem_matrixOrthogonal_iff Φ s).1 hsO
  have hs2Iso : s * s ∈ matrixIsometries Φ := mul_mem hsIso hsIso
  have hzO : matrixLinearIso (s * s) ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := hs2Iso
  have h3 : 3 ≤ Module.finrank K (Fin d → K) := le_trans (by norm_num) h5
  have hnexc : ¬ CFSG.RankThree.PartOne.KCOrthogonal.SmallFixedException Φ := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  have hzc : ∀ y ∈ CFSG.RankThree.Classical2.orthDerived Φ,
      matrixLinearIso (s * s) * y = y * matrixLinearIso (s * s) := by
    intro y hy
    rw [← CFSG.RankThree.PartOne.AUTSL.map_matrixDerived_linearIso] at hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    rw [← hgy]
    show matrixLinearIso (s * s) * matrixLinearIso (g : GL (Fin d) K) =
      matrixLinearIso (g : GL (Fin d) K) * matrixLinearIso (s * s)
    rw [← map_mul, ← map_mul, hcomm ⟨g, hg⟩]
  have hz1 : matrixLinearIso (s * s) = 1 :=
    LayerCores.OrthRegular.eq_one_of_commute_orthDerived hΦ h3 hnexc hzO hzc
  exact matrixLinearIso.injective (by rw [hz1, map_one])

private lemma ggOmW6cD_conjBy_of_val_eq {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (h : ∀ g : matrixDerived Φ, (α g).val = s * (g : GL (Fin d) K) * s⁻¹) :
    GGGraphInvConjBy Φ α s := by
  intro g
  refine ⟨?_, ?_⟩
  · rw [← h g]
    exact (α g).2
  · exact Subtype.ext (h g)

theorem ggGraphInv_graph_lift {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (Fin d → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ d) (u : matrixDerived Φ) (w : Fin d → K) (hw : Φ w ≠ 0)
    (hRΩ : CFSG.RankThree.PartOne.AUTSL.reflMat Φ w hw ∉ CFSG.Open.StatedOmega ⇑Φ)
    (α : MulAut (matrixDerived Φ)) (hα2 : α * α = 1)
    (hα : α = MulAut.conj u * CFSG.RankThree.PartOne.AUTSL.reflAut Φ w hw) :
    ∃ s : GL (Fin d) K,
      s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ ∧
      s ∉ CFSG.Open.StatedOmega ⇑Φ ∧ s * s = 1 ∧ GGGraphInvConjBy Φ α s := by
  let s : GL (Fin d) K := (u : GL (Fin d) K) * reflMat Φ w hw
  have hval : ∀ g : matrixDerived Φ, (α g).val = s * (g : GL (Fin d) K) * s⁻¹ :=
    ggOmW6cD_conj_val Φ u w hw α hα
  have hsO : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ := by
    rw [ggOmW6cD_mem_matrixOrthogonal_iff]
    exact mul_mem (matrixDerived_le_isometries Φ u.2) (reflMat_mem_isometries (Q := Φ) w hw)
  have hsΩ : s ∉ CFSG.Open.StatedOmega ⇑Φ := by
    intro hmem
    apply hRΩ
    have hu : (u : GL (Fin d) K) ∈ CFSG.Open.StatedOmega ⇑Φ := by
      rw [← matrixDerived_eq_statedOmega]
      exact u.2
    have h2 : (u : GL (Fin d) K)⁻¹ * s ∈ CFSG.Open.StatedOmega ⇑Φ :=
      mul_mem (inv_mem hu) hmem
    have heq : (u : GL (Fin d) K)⁻¹ * s = reflMat Φ w hw := by
      change (u : GL (Fin d) K)⁻¹ * ((u : GL (Fin d) K) * reflMat Φ w hw) =
        reflMat Φ w hw
      group
    rwa [heq] at h2
  have hfin : Module.finrank K (Fin d → K) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h5 : 5 ≤ Module.finrank K (Fin d → K) := by rw [hfin]; omega
  have hcomm := ggOmW6cD_sq_comm_of_involution Φ α s hα2 hval
  have hs2 : s * s = 1 := ggOmW6cD_sq_eq_one Φ hΦ h5 s hsO hcomm
  have hconj : GGGraphInvConjBy Φ α s := ggOmW6cD_conjBy_of_val_eq Φ α s hval
  exact ⟨s, hsO, hsΩ, hs2, hconj⟩

private theorem ggOmW6cE_fixed_eq_centralizer {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s) :
    ggFixSubgroup α =
      (Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓
        CFSG.Open.StatedOmega ⇑Φ).subgroupOf (matrixDerived Φ) := by
  rw [ggGraphInv_fixSubgroup_eq_of_conjBy Φ α s hconj]
  have h : Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ matrixDerived Φ =
      Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓
        CFSG.Open.StatedOmega ⇑Φ := by
    rw [matrixDerived_eq_statedOmega Φ]
  rw [h]

private theorem ggOmW6cE_b_ne_one {d : ℕ} {K : Type} [Field K] (b : GL (Fin d) K)
    (h8 : 8 ≤ d)
    (hfin : Module.finrank K
      (LinearMap.ker (Matrix.toLin' (b : Matrix (Fin d) (Fin d) K) - LinearMap.id)) = 2) :
    b ≠ 1 := by
  intro hb
  have htop : LinearMap.ker
      (Matrix.toLin' (b : Matrix (Fin d) (Fin d) K) - LinearMap.id) = ⊤ := by
    rw [hb]
    change LinearMap.ker
      (Matrix.toLin' (1 : Matrix (Fin d) (Fin d) K) - LinearMap.id) = ⊤
    rw [Matrix.toLin'_one]
    change LinearMap.ker (LinearMap.id - LinearMap.id) = ⊤
    rw [sub_self, LinearMap.ker_zero]
  have hle1 : Module.finrank K
      (LinearMap.ker (Matrix.toLin' (b : Matrix (Fin d) (Fin d) K) - LinearMap.id)) ≤
      Module.finrank K (⊤ : Submodule K (Fin d → K)) :=
    Submodule.finrank_mono le_top
  have hle2 : Module.finrank K (⊤ : Submodule K (Fin d → K)) ≤
      Module.finrank K
        (LinearMap.ker (Matrix.toLin' (b : Matrix (Fin d) (Fin d) K) - LinearMap.id)) :=
    Submodule.finrank_mono (le_of_eq htop.symm)
  have htoprank : Module.finrank K (⊤ : Submodule K (Fin d → K)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  omega

private theorem ggOmW6cE_not_isPGroup_of_odd {G : Type} [Group G]
    (H : Subgroup G) (x : G) (hx : x ∈ H) (hx1 : x ≠ 1) (hodd : Odd (orderOf x)) :
    ¬ IsPGroup 2 ↥H := by
  intro hP
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
  have hxH1 : (⟨x, hx⟩ : H) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext_iff.mp h)
  have hoddH : Odd (orderOf (⟨x, hx⟩ : H)) := by
    rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : H)]
    simpa using hodd
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero] at hn
    exact hxH1 (orderOf_eq_one_iff.mp hn)
  · exact absurd (Nat.even_pow.mpr ⟨even_two, hn0⟩)
      (Nat.not_even_iff_odd.mpr (hn ▸ hoddH))

private theorem ggOmW6cE_normal_two_subgroup_bot {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s)
    (hcore : CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedOmega ⇑Φ) = ⊥)
    (N : Subgroup (matrixDerived Φ)) (hNle : N ≤ ggFixSubgroup α)
    (hNp : IsPGroup 2 N)
    (hNnorm : ∀ y ∈ N, ∀ z ∈ ggFixSubgroup α, z * y * z⁻¹ ∈ N) :
    N = ⊥ := by
  let G := matrixDerived Φ
  let CΩ := Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedOmega ⇑Φ
  have hfix : ggFixSubgroup α = CΩ.subgroupOf G := ggOmW6cE_fixed_eq_centralizer Φ α s hconj
  have hN'le : N.map G.subtype ≤ CΩ := by
    rintro x ⟨n, hnN, rfl⟩
    have hmem := hfix ▸ hNle hnN
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hN'p : IsPGroup 2 (N.map G.subtype) := hNp.map G.subtype
  have hN'norm : ((N.map G.subtype).subgroupOf CΩ).Normal := by
    refine ⟨fun n hn z => ?_⟩
    have hn' : (n : GL (Fin d) K) ∈ N.map G.subtype := Subgroup.mem_subgroupOf.mp hn
    rcases hn' with ⟨m, hmN, hmeq⟩
    have hzG : (z : GL (Fin d) K) ∈ G := by
      have hzΩ : (z : GL (Fin d) K) ∈ CFSG.Open.StatedOmega ⇑Φ := z.2.2
      change (z : GL (Fin d) K) ∈ matrixDerived Φ
      rw [matrixDerived_eq_statedOmega Φ]
      exact hzΩ
    let zg : G := ⟨(z : GL (Fin d) K), hzG⟩
    have hzgf : zg ∈ ggFixSubgroup α := by
      rw [hfix]
      exact Subgroup.mem_subgroupOf.mpr (by simpa [zg] using z.2)
    have hmem := hNnorm m hmN zg hzgf
    have hiso : ((z * n * z⁻¹ : CΩ) : GL (Fin d) K) =
        G.subtype (zg * m * zg⁻¹) := by
      rw [map_mul, map_mul, map_inv, hmeq]
      rfl
    rw [Subgroup.mem_subgroupOf, hiso]
    exact Subgroup.mem_map_of_mem G.subtype hmem
  have hle := CFSG.LieType.BorelTits.le_pCoreOf 2 hN'le hN'norm hN'p
  rw [hcore] at hle
  have hN'bot : N.map G.subtype = ⊥ := le_bot_iff.mp hle
  refine (Subgroup.eq_bot_iff_forall N).mpr fun n hn => ?_
  have hmem : G.subtype n ∈ N.map G.subtype := Subgroup.mem_map_of_mem G.subtype hn
  rw [hN'bot] at hmem
  have h1 : (n : GL (Fin d) K) = 1 := Subgroup.mem_bot.mp hmem
  exact Subtype.ext (by simpa using h1)

private theorem ggOmW6cE_double_centralizer_bot {d : ℕ} {K : Type} [Field K]
    (Φ : QuadraticForm K (Fin d → K)) (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hconj : GGGraphInvConjBy Φ α s)
    (hcent : CFSG.Open.StatedOmega ⇑Φ ⊓ Subgroup.centralizer
      ((Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedOmega ⇑Φ :
        Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)) = ⊥) :
    Subgroup.centralizer ((ggFixSubgroup α : Subgroup (matrixDerived Φ)) :
      Set (matrixDerived Φ)) = ⊥ := by
  let G := matrixDerived Φ
  let CΩ := Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedOmega ⇑Φ
  have hfix : ggFixSubgroup α = CΩ.subgroupOf G := ggOmW6cE_fixed_eq_centralizer Φ α s hconj
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxGL : (x : GL (Fin d) K) ∈ CFSG.Open.StatedOmega ⇑Φ ⊓
      Subgroup.centralizer ((CΩ : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)) := by
    refine ⟨?_, ?_⟩
    · have hGΩ : matrixDerived Φ ≤ CFSG.Open.StatedOmega ⇑Φ :=
        le_of_eq (matrixDerived_eq_statedOmega Φ)
      exact hGΩ x.2
    · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have hzG : z ∈ G := by
        have hzΩ : z ∈ CFSG.Open.StatedOmega ⇑Φ := hz.2
        change z ∈ matrixDerived Φ
        rw [matrixDerived_eq_statedOmega Φ]
        exact hzΩ
      let zg : G := ⟨z, hzG⟩
      have hzgf : zg ∈ ggFixSubgroup α := by
        rw [hfix]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [zg] using hz)
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) zg hzgf
      have hcoe := congrArg (fun t : G => (t : GL (Fin d) K)) hcomm
      simpa [zg, G] using hcoe
  rw [hcent] at hxGL
  have h1 : (x : GL (Fin d) K) = 1 := Subgroup.mem_bot.mp hxGL
  exact Subtype.ext (by simpa using h1)

theorem ggGraphInv_three_conclusions_of_transvection {d : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (Φ : QuadraticForm K (Fin d → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ d)
    (b : GL (Fin d) K) (hb : b ∈ CFSG.Open.StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (α : MulAut (matrixDerived Φ)) (s : GL (Fin d) K)
    (hsO : s ∈ CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ)
    (hsΩ : s ∉ CFSG.Open.StatedOmega ⇑Φ) (hs2 : s * s = 1) (hsb : s * b = b * s)
    (hsC : ∀ g ∈ Subgroup.centralizer ({b} : Set (GL (Fin d) K)) ⊓
        CFSG.Open.StatedOmega ⇑Φ, s * g = g * s)
    (hconj : GGGraphInvConjBy Φ α s) :
    Nat.card K = 2 ∧ GGGraphInvFixClauses α := by
  haveI : Fintype K := Fintype.ofFinite K
  have hb' : b ∈ matrixDerived Φ := by
    rw [matrixDerived_eq_statedOmega Φ]
    exact hb
  obtain ⟨hKcard, hfin, v, _, hΦv, htrans⟩ :=
    CFSG.StandardType.ClassicalBlocks.eq_transvection_of_centralizes Φ hΦ
      (by simpa using h8) b hb hodd s hsO hsΩ hs2 hsb hsC
  obtain ⟨_, _, _, hcore, hdouble, _⟩ :=
    CFSG.StandardType.ClassicalBlocks.centralizer_transvection Φ hΦ
      (by simpa using h8) s v hΦv htrans
  have hb1 : b ≠ 1 := ggOmW6cE_b_ne_one b h8 hfin
  have hbCΩ : b ∈ Subgroup.centralizer ({s} : Set (GL (Fin d) K)) ⊓
      CFSG.Open.StatedOmega ⇑Φ := by
    refine ⟨?_, hb⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hsb
  have hbG : (⟨b, hb'⟩ : matrixDerived Φ) ∈ ggFixSubgroup α := by
    rw [ggOmW6cE_fixed_eq_centralizer Φ α s hconj]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hbCΩ)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact hKcard
  · refine ⟨?_, ?_, ?_⟩
    · intro N hNle hNp hNnorm
      exact ggOmW6cE_normal_two_subgroup_bot Φ α s hconj hcore N hNle hNp hNnorm
    · have hbG1 : (⟨b, hb'⟩ : matrixDerived Φ) ≠ 1 := by
        intro h
        exact hb1 (Subtype.ext_iff.mp h)
      have hoddG : Odd (orderOf (⟨b, hb'⟩ : matrixDerived Φ)) := by
        rw [← Subgroup.orderOf_coe (⟨b, hb'⟩ : matrixDerived Φ)]
        simpa using hodd
      exact ggOmW6cE_not_isPGroup_of_odd (ggFixSubgroup α) ⟨b, hb'⟩ hbG hbG1 hoddG
    · exact ggOmW6cE_double_centralizer_bot Φ α s hconj hdouble

end CFSG.StandardType
