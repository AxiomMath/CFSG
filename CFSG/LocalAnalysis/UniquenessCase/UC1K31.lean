module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

namespace K31

open CFSG.Open

theorem pRank_top_le_one_of_isCyclic {T : Type*} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : IsCyclic T) : CFSG.Open.pRank p (⊤ : Subgroup T) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  haveI hT : IsCyclic T := h
  haveI hEcyc : IsCyclic E := Subgroup.isCyclic_of_le (le_top : E ≤ ⊤)
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hE.2 (x : T) x.2)
  have hcard : Nat.card E ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  simpa using Nat.le_of_dvd hp.pos hcard

theorem isCyclic_of_isPGroup_pRank_le_one {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hT : IsPGroup p T) (h : CFSG.pRank p T ≤ 1) :
    IsCyclic T := by
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp hT).1 h with
    hc | ⟨h2, -⟩
  · exact hc
  · exact absurd h2 hp2

variable {G : Type*} [Group G] [Finite G]

theorem isCyclic_of_pRank_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) (h : CFSG.Open.pRank p X ≤ 1) : IsCyclic X := by
  have h' : CFSG.pRank p ↥X ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact h
  exact isCyclic_of_isPGroup_pRank_le_one hp hp2 hX h'

theorem pRank_subgroupOf_eq {p : ℕ} (hp : 1 < p) {H K : Subgroup G} (hHK : H ≤ K) :
    CFSG.Open.pRank p (H.subgroupOf K) = CFSG.Open.pRank p H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H.subgroupOf K),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (Subgroup.subgroupOfEquivOfLe hHK)

end K31

namespace K31

variable {G : Type*} [Group G]

theorem isCyclic_quotient_subgroupOf_of_le {A B C : Subgroup G} (hBC : B ≤ C)
    [(A.subgroupOf C).Normal] [(A.subgroupOf B).Normal]
    (hC : IsCyclic (↥C ⧸ A.subgroupOf C)) :
    IsCyclic (↥B ⧸ A.subgroupOf B) := by
  let φ : ↥B →* ↥C ⧸ A.subgroupOf C :=
    (QuotientGroup.mk' (A.subgroupOf C)).comp (Subgroup.inclusion hBC)
  have hker : φ.ker = A.subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker]
    show ((QuotientGroup.mk' (A.subgroupOf C)) (Subgroup.inclusion hBC x)) = 1 ↔
      x ∈ A.subgroupOf B
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    rfl
  have hr : IsCyclic φ.range := by
    haveI := hC
    exact Subgroup.isCyclic_of_le le_top
  haveI : IsCyclic (↥B ⧸ φ.ker) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange φ)).mpr hr
  exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hker)
    (QuotientGroup.quotientMulEquivOfEq hker).surjective

theorem isCyclic_quotient_of_le {H : Type*} [Group H] {A A' : Subgroup H} [A.Normal]
    [A'.Normal] (h : A ≤ A') (hcyc : IsCyclic (H ⧸ A)) : IsCyclic (H ⧸ A') := by
  let f : H ⧸ A →* H ⧸ A' :=
    QuotientGroup.map (N := A) A' (MonoidHom.id H) (by simpa using h)
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective (N := A) A' (MonoidHom.id H)
      (by simpa using (QuotientGroup.mk'_surjective A')) (by simpa using h)
  exact isCyclic_of_surjective f hf

end K31

open K31

namespace K31

variable {G : Type*} [Group G] [Finite G]

theorem k31_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q S X : Subgroup G} (hP : IsPGroup p P)
    (hQP : Q ≤ P) (hSP : S ≤ P) [(Q.subgroupOf P).Normal] [(S.subgroupOf P).Normal]
    (hPS : IsCyclic (↥P ⧸ S.subgroupOf P)) (hXP : X ≤ P) (hRX : Q ⊓ S ≤ X)
    (hPQX : P = Q ⊔ X) (hXle : CFSG.Open.pRank p X ≤ 1) :
    CFSG.Open.pRank p P ≤ 2 := by
  have hXp : IsPGroup p X := hP.to_le hXP
  have hXcyc : IsCyclic X := isCyclic_of_pRank_le_one hp hp2 hXp hXle
  haveI hX'cyc : IsCyclic (X.subgroupOf P) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hXP)).mpr hXcyc
  have hQXs : Q.subgroupOf P ⊔ X.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQP hXP, ← hPQX, Subgroup.subgroupOf_self]
  have hcommP_Q : _root_.commutator ↥P ≤ Q.subgroupOf P :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hQXs
      (inferInstance : IsMulCommutative (X.subgroupOf P))
  have hcommP_S : _root_.commutator ↥P ≤ S.subgroupOf P :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := S.subgroupOf P)).mp
      (inferInstance : IsMulCommutative (↥P ⧸ S.subgroupOf P))
  have hRS_le : Q.subgroupOf P ⊓ S.subgroupOf P ≤ X.subgroupOf P := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRX ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2⟩
  have hcommP : _root_.commutator ↥P ≤ X.subgroupOf P :=
    (le_inf hcommP_Q hcommP_S).trans hRS_le
  haveI : (X.subgroupOf P).Normal :=
    Subgroup.Normal.of_commutator_le (G := ↥P) (H := X.subgroupOf P) hcommP
  have hPnS : P ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := S) (K := P) hSP
  have hQnS : Q ≤ Subgroup.normalizer (S : Set G) := hQP.trans hPnS
  haveI hSnQ : (S.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQnS
  have hScycQ : IsCyclic (↥Q ⧸ S.subgroupOf Q) :=
    isCyclic_quotient_subgroupOf_of_le (A := S) (B := Q) (C := P) hQP hPS
  have hSXQ : S.subgroupOf Q ≤ X.subgroupOf Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRX ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
  have hSXQ' : S.subgroupOf Q ≤ (X.subgroupOf P).comap (Subgroup.inclusion hQP) := by
    simpa using hSXQ
  have hg : Function.Surjective
      ((QuotientGroup.mk' (X.subgroupOf P)).comp (Subgroup.inclusion hQP)) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range]
    have h1 : (Q.subgroupOf P ⊔ X.subgroupOf P).map
        (QuotientGroup.mk' (X.subgroupOf P)) = ⊤ := by
      rw [hQXs]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  haveI : IsCyclic (↥Q ⧸ S.subgroupOf Q) := hScycQ
  have hXcycP : IsCyclic (↥P ⧸ X.subgroupOf P) :=
    isCyclic_of_surjective
      (QuotientGroup.map (N := S.subgroupOf Q) (X.subgroupOf P)
        (Subgroup.inclusion hQP) hSXQ')
      (QuotientGroup.map_surjective_of_surjective (N := S.subgroupOf Q) (X.subgroupOf P)
        (Subgroup.inclusion hQP) hg hSXQ')
  have hXpRank : CFSG.Open.pRank p (X.subgroupOf P) ≤ 1 := by
    rw [pRank_subgroupOf_eq hp.one_lt hXP]
    exact hXle
  have hquotRank : CFSG.Open.pRank p (⊤ : Subgroup (↥P ⧸ X.subgroupOf P)) ≤ 1 :=
    pRank_top_le_one_of_isCyclic hp hXcycP
  have hsub := CFSG.HardMathSupport.Timmesfeld.Proving.pRank_le_pRank_inf_add_pRank_map
    (G := ↥P) hp (⊤ : Subgroup ↥P) (X.subgroupOf P)
  have htop : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := by
    have h1 : (⊤ : Subgroup ↥P) ⊓ X.subgroupOf P = X.subgroupOf P :=
      inf_eq_right.mpr le_top
    have h2 : (⊤ : Subgroup ↥P).map (QuotientGroup.mk' (X.subgroupOf P)) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [h1, h2] at hsub
    omega
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact htop

end K31

open K31

variable {G : Type*} [Group G] [Finite G]

theorem k31 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q S X : Subgroup G} (hP : IsPGroup p P) (hrank : 3 ≤ CFSG.Open.pRank p P)
    (hQP : Q ≤ P) (hSP : S ≤ P) [(Q.subgroupOf P).Normal] [(S.subgroupOf P).Normal]
    (hPS : IsCyclic (↥P ⧸ S.subgroupOf P)) (hXP : X ≤ P) (hRX : Q ⊓ S ≤ X)
    (hPQX : P = Q ⊔ X) :
    1 < CFSG.Open.pRank p X := by
  by_contra hcon
  simp only [not_lt] at hcon
  have hP2 := k31_aux hp hp2 hP hQP hSP hPS hXP hRX hPQX hcon
  omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
