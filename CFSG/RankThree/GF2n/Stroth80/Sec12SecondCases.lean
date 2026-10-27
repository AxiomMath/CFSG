module

public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCfg
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondGrp
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxGrp
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondSL2
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondOrders
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X]

theorem ConfigSatz.exists_ctx {N : Subgroup X} (hS : ConfigSatz N) :
    ∃ B₂ : Subgroup X, ∃ _ : Ctx (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂,
      StrothConclusion (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂ := by
  obtain ⟨g, hgV, hgQ⟩ := hS.1.toHyp79.exists_opposite
  exact ⟨conjSubgroup g (cen N), ⟨hS.1, ⟨g, rfl⟩, hgQ, hgV⟩,
    hS.2 _ ⟨hS.1, ⟨g, rfl⟩, hgQ, hgV⟩⟩

@[expose] def Stroth4iStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → StrothCi M Q Z B t → StrothCii M Q Z B t

private theorem card_UT3_eq (R : Type*) [CommRing R] :
    Nat.card (CFSG.GH74.GLS.Bg.TwoGroups.UT3 R) = Nat.card R ^ 3 := by
  have e : CFSG.GH74.GLS.Bg.TwoGroups.UT3 R ≃ R × R × R :=
    { toFun := fun u => (u.a, u.b, u.c)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem secondCfg_cases {N : Subgroup X} {k : ℕ} (hk : k = 4 ∨ k = 8) (hS : ConfigSatz N)
    (hW : Width N (cen N) k) (hgen : k = 4 → StrothGenByBStatement)
    (hCi : k = 4 → Stroth4iStatement) :
    ∃ B₂ : Subgroup X, ∃ hc : Ctx (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N
        (cen N) B₂,
      (k = 4 ∧ QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
          (IsSLModel 2 (Nat.card (cen N) ^ 3)) ∧
        CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
          (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂))) ∨
      (∃ m : ℕ, 2 ≤ m ∧ 2 * m = k ∧
        CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
          (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) ∧
        (QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
            (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaPlus m (Nat.card (cen N)))) ∨
          QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
            (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaMinus m (Nat.card (cen N)))))) ∨
      CaseVI (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
        (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) := by
  obtain ⟨B₂, hc, hconc⟩ := hS.exists_ctx
  refine ⟨B₂, hc, ?_⟩
  obtain ⟨hcases, -⟩ := hconc
  have hq : 2 ≤ Nat.card (cen N) := le_trans (by norm_num) hS.1.q4
  have hinj : ∀ a b : ℕ, Nat.card (cen N) ^ a = Nat.card (cen N) ^ b → a = b :=
    fun a b hab => Nat.pow_right_injective hq hab
  have hN : Nat.card N = Nat.card (cen N) ^ (2 * k + 1) := hW
  have hk' : 2 < k := by omega
  have hii : ∀ t : X, StrothCii (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
      B₂ t → CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
        (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) →
      ∃ m : ℕ, 2 ≤ m ∧ 2 * m = k ∧
        CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
          (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) ∧
        (QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
            (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaPlus m (Nat.card (cen N)))) ∨
          QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
            (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaMinus m (Nat.card (cen N))))) := by
    rintro t ⟨m, hm2, hm, -, hsum⟩ hCT
    have := hinj _ _ (hN.symm.trans hm)
    refine ⟨m, hm2, by omega, hCT, ?_⟩
    rcases hsum with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with ⟨k0, hk0, ⟨e⟩⟩ | ⟨h5, -⟩ | ⟨h9, hS3, hCT⟩ |
    ⟨-, (⟨hNoA2, t, htL, htQ, hCT, (hi | hii' | hiii | hiv | hv)⟩ | hVI)⟩
  · exfalso
    have hk00 : k0 ≠ 0 := by
      rintro rfl
      have := hS.1.q4
      rw [hk0] at this
      simp at this
    have hcard : Nat.card N = Nat.card (cen N) ^ 3 := by
      rw [Nat.card_congr e.toEquiv, card_UT3_eq, GaloisField.card 2 k0 hk00, hk0]
    have := hinj _ _ (hN.symm.trans hcard)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans h5)
    omega
  · have := hinj _ _ (hN.symm.trans h9)
    exact Or.inl ⟨by omega, hS3, hCT⟩
  · right
    left
    have hk4 : k = 4 := by
      have := hinj _ _ (hN.symm.trans hi.1)
      omega
    have hNoA2' : NoA2 N (cen N) (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) :=
      hNoA2 B₂ hc.conj hc.le hc.ne
    have hgenB := hgen hk4 X _ N (cen N) B₂ hc k hW hk' hNoA2'
    have hCii := hCi hk4 X _ N (cen N) B₂ hc k t ⟨hW, hk', hNoA2', hgenB, htL, htQ⟩ hi
    exact hii t hCii hCT
  · right
    left
    exact hii t hii' hCT
  · exfalso
    have := hinj _ _ (hN.symm.trans hiii.1)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans hiv.1)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans hv.1)
    omega
  · exact Or.inr (Or.inr hVI)

section Bridge

variable {G : Type} [Group G] [Finite G] {M Q Z S R : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem normal_bar_subgroupOf (hSn : (S.subgroupOf M).Normal) :
    ((bar M Q S).subgroupOf (bar M Q (H0 M Z))).Normal :=
  (bar_normal hSn).subgroupOf _

theorem centralizer_bar_trivial (hSM : S ≤ M) (hSH : S ≤ H0 M Z) (hCT : CentTrivial M Q Z S)
    (h : ↥(bar M Q (H0 M Z))) (hc : ∀ s ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)),
      h * s = s * h) : h = 1 := by
  obtain ⟨h', hh', hhm⟩ := h.2
  have hhH : (h' : G) ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hh'
  have hcomm : ∀ x ∈ S, ⁅(h' : G), x⁆ ∈ Q := by
    intro x hx
    have hxM : x ∈ M := hSM hx
    have hmem : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈ bar M Q S :=
      ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hmemH : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈
        bar M Q (H0 M Z) :=
      ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr (hSH hx), rfl⟩
    have h1 : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩, hmemH⟩ :
        ↥(bar M Q (H0 M Z))) ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) := hmem
    have h2 := congrArg Subtype.val (hc _ h1)
    have h3 : (QuotientGroup.mk' (Q.subgroupOf M) h') *
        QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ =
        QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ * QuotientGroup.mk' (Q.subgroupOf M) h' := by
      rw [hhm]
      exact h2
    have h4 : QuotientGroup.mk' (Q.subgroupOf M) ⁅h', (⟨x, hxM⟩ : ↥M)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h3
    have h5 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h4)
    simpa [commutatorElement_def] using h5
  have hhQ := hCT _ hhH hcomm
  apply Subtype.ext
  rw [← hhm]
  exact (QuotientGroup.eq_one_iff h').mpr (Subgroup.mem_subgroupOf.mpr hhQ)

theorem equiv_subgroupOf_bar (hQS : Q ≤ S) (hSM : S ≤ M) (hSH : S ≤ H0 M Z) :
    ∃ _ : (Q.subgroupOf S).Normal, Nonempty (↥S ⧸ Q.subgroupOf S ≃*
      ↥((bar M Q S).subgroupOf (bar M Q (H0 M Z)))) := by
  obtain ⟨hn, ⟨e⟩⟩ := quotMulEquivBar (M := M) hQS hSM
  have hle : bar M Q S ≤ bar M Q (H0 M Z) := Subgroup.map_mono fun x hx => hSH hx
  exact ⟨hn, ⟨e.trans (Subgroup.subgroupOfEquivOfLe hle).symm⟩⟩

theorem perfect_bar_subgroupOf (hQR : Q ≤ R) (hRM : R ≤ M) (hRH : R ≤ H0 M Z)
    (hperf : QuotSat R Q (fun X _ => Group.IsPerfect X)) :
    ⁅(bar M Q R).subgroupOf (bar M Q (H0 M Z)), (bar M Q R).subgroupOf (bar M Q (H0 M Z))⁆ =
      (bar M Q R).subgroupOf (bar M Q (H0 M Z)) := by
  obtain ⟨hn, hp⟩ := hperf
  obtain ⟨hn', ⟨e⟩⟩ := quotMulEquivBar (M := M) hQR hRM
  have hle : bar M Q R ≤ bar M Q (H0 M Z) := Subgroup.map_mono fun x hx => hRH hx
  haveI : Group.IsPerfect ↥(bar M Q R) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  haveI : Group.IsPerfect ↥((bar M Q R).subgroupOf (bar M Q (H0 M Z))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Subgroup.isPerfect_iff.mp inferInstance

theorem le_of_subgroupOf_bar_le (hQS : Q ≤ S) (hSM : S ≤ M) (hRM : R ≤ M)
    (hRH : R ≤ H0 M Z)
    (h : (bar M Q R).subgroupOf (bar M Q (H0 M Z)) ≤ (bar M Q S).subgroupOf (bar M Q (H0 M Z))) :
    R ≤ S := by
  intro x hx
  have hxM : x ∈ M := hRM hx
  have hmemR : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈ bar M Q R :=
    ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hmemH : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr (hRH hx), rfl⟩
  have h1 := h (show (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩, hmemH⟩ :
    ↥(bar M Q (H0 M Z))) ∈ (bar M Q R).subgroupOf (bar M Q (H0 M Z)) from hmemR)
  exact (mk_mem_bar_iff_sec4 hQS ⟨x, hxM⟩).mp (Subgroup.mem_subgroupOf.mp h1)

@[expose] def IsSimpleProd2 (X : Type) [Group X] : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), IsSimpleGroup A ∧ IsSimpleGroup B ∧
    (∃ x y : A, x * y ≠ y * x) ∧ (∃ x y : B, x * y ≠ y * x) ∧
    Group.IsSolvable (Outer A) ∧ Group.IsSolvable (Outer B) ∧ Nonempty (X ≃* A × B)

@[expose] def IsSimpleProd3 (X : Type) [Group X] : Prop :=
  ∃ (A B C : Type) (_ : Group A) (_ : Group B) (_ : Group C), IsSimpleGroup A ∧ IsSimpleGroup B ∧
    IsSimpleGroup C ∧ (∃ x y : A, x * y ≠ y * x) ∧ (∃ x y : B, x * y ≠ y * x) ∧
    (∃ x y : C, x * y ≠ y * x) ∧ Group.IsSolvable (Outer A) ∧ Group.IsSolvable (Outer B) ∧
    Group.IsSolvable (Outer C) ∧ Nonempty (X ≃* A × (B × C))

theorem quotSat_mono {P P' : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X], P X → P' X) {S N : Subgroup G} (h : QuotSat S N P) :
    QuotSat S N P' := by
  obtain ⟨hn, h'⟩ := h
  exact ⟨hn, hP _ h'⟩

theorem solvable_centralizer_of_centTrivial (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hCT : CentTrivial M Q Z S) :
    Group.IsSolvable ↥(Subgroup.centralizer (((bar M Q S).subgroupOf (bar M Q (H0 M Z)) :
      Subgroup _) : Set ↥(bar M Q (H0 M Z)))) := by
  have : Subgroup.centralizer (((bar M Q S).subgroupOf (bar M Q (H0 M Z)) : Subgroup _) :
      Set ↥(bar M Q (H0 M Z))) = ⊥ := by
    refine eq_bot_iff.mpr fun h hh => ?_
    rw [Subgroup.mem_bot]
    exact centralizer_bar_trivial hSM hSH hCT h fun s hs =>
      (Subgroup.mem_centralizer_iff.mp hh s hs).symm
  rw [this]
  infer_instance

theorem le_of_perfect_prod2 (hQS : Q ≤ S) (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hSn : (S.subgroupOf M).Normal) (hCT : CentTrivial M Q Z S) (hQR : Q ≤ R) (hRM : R ≤ M)
    (hRH : R ≤ H0 M Z) (hperf : QuotSat R Q (fun X _ => Group.IsPerfect X))
    (hS : QuotSat S Q IsSimpleProd2) : R ≤ S := by
  obtain ⟨hn, A, B, _, _, hAs, hBs, hAn, hBn, hAo, hBo, ⟨e⟩⟩ := hS
  obtain ⟨hn', ⟨e'⟩⟩ := equiv_subgroupOf_bar (M := M) (Z := Z) hQS hSM hSH
  haveI := normal_bar_subgroupOf (M := M) (Q := Q) (Z := Z) hSn
  have hC := solvable_centralizer_of_centTrivial hSM hSH hCT
  have hRp := perfect_bar_subgroupOf (M := M) (Z := Z) hQR hRM hRH hperf
  exact le_of_subgroupOf_bar_le hQS hSM hRM hRH
    (perfect_le_of_prod _ _ hC hAn hBn hAo hBo (e'.symm.trans e) hRp)

theorem le_of_perfect_prod3 (hQS : Q ≤ S) (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hSn : (S.subgroupOf M).Normal) (hCT : CentTrivial M Q Z S) (hQR : Q ≤ R) (hRM : R ≤ M)
    (hRH : R ≤ H0 M Z) (hperf : QuotSat R Q (fun X _ => Group.IsPerfect X))
    (hS : QuotSat S Q IsSimpleProd3) : R ≤ S := by
  obtain ⟨hn, A, B, C, _, _, _, hAs, hBs, hCs, hAn, hBn, hCn, hAo, hBo, hCo, ⟨e⟩⟩ := hS
  obtain ⟨hn', ⟨e'⟩⟩ := equiv_subgroupOf_bar (M := M) (Z := Z) hQS hSM hSH
  haveI := normal_bar_subgroupOf (M := M) (Q := Q) (Z := Z) hSn
  have hC := solvable_centralizer_of_centTrivial hSM hSH hCT
  have hRp := perfect_bar_subgroupOf (M := M) (Z := Z) hQR hRM hRH hperf
  exact le_of_subgroupOf_bar_le hQS hSM hRM hRH
    (perfect_le_of_prod3 _ _ hC hAn hBn hCn hAo hBo hCo (e'.symm.trans e) hRp)

theorem le_of_perfect_outer (hQS : Q ≤ S) (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hSn : (S.subgroupOf M).Normal)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (((bar M Q S).subgroupOf
      (bar M Q (H0 M Z)) : Subgroup _) : Set ↥(bar M Q (H0 M Z)))))
    (hQR : Q ≤ R) (hRM : R ≤ M) (hRH : R ≤ H0 M Z)
    (hperf : QuotSat R Q (fun X _ => Group.IsPerfect X))
    (hS : QuotSat S Q (fun X _ => Group.IsSolvable (Outer X))) : R ≤ S := by
  obtain ⟨hn, hO⟩ := hS
  obtain ⟨hn', ⟨e'⟩⟩ := equiv_subgroupOf_bar (M := M) (Z := Z) hQS hSM hSH
  haveI := normal_bar_subgroupOf (M := M) (Q := Q) (Z := Z) hSn
  haveI := hO
  have hRp := perfect_bar_subgroupOf (M := M) (Z := Z) hQR hRM hRH hperf
  have hO' : Group.IsSolvable (Outer ↥((bar M Q S).subgroupOf (bar M Q (H0 M Z)))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e'
  exact le_of_subgroupOf_bar_le hQS hSM hRM hRH (perfect_le_of_outer _ _ hC hO' hRp)

theorem mk_comm_iff (a b : ↥M) :
    (QuotientGroup.mk' (Q.subgroupOf M) a * QuotientGroup.mk' (Q.subgroupOf M) b =
      QuotientGroup.mk' (Q.subgroupOf M) b * QuotientGroup.mk' (Q.subgroupOf M) a) ↔
      ⁅(a : G), (b : G)⁆ ∈ Q := by
  constructor
  · intro h
    have h4 : QuotientGroup.mk' (Q.subgroupOf M) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
    have h5 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h4)
    simpa [commutatorElement_def] using h5
  · intro h
    have h4 : (⁅a, b⁆ : ↥M) ∈ Q.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h)
    have h5 : QuotientGroup.mk' (Q.subgroupOf M) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h4
    rw [map_commutatorElement] at h5
    exact commutatorElement_eq_one_iff_mul_comm.mp h5

theorem solvable_centralizer_of_centDvd (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hq : Even (Nat.card Z)) (hCD : CentDvd M Q Z S) :
    Group.IsSolvable ↥(Subgroup.centralizer (((bar M Q S).subgroupOf (bar M Q (H0 M Z)) :
      Subgroup _) : Set ↥(bar M Q (H0 M Z)))) := by
  obtain ⟨C, hQC, hCH, hCiff, hCdvd⟩ := hCD
  have hCM : C ≤ M := fun x hx => (hCH hx).1
  let ψ : ↥C →* ↥(bar M Q (H0 M Z)) :=
    { toFun := fun c => ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hCM c.2⟩,
        ⟨⟨c, hCM c.2⟩, Subgroup.mem_subgroupOf.mpr (hCH c.2), rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact (QuotientGroup.mk' (Q.subgroupOf M)).map_one
      map_mul' := fun a b => by
        apply Subtype.ext
        exact (QuotientGroup.mk' (Q.subgroupOf M)).map_mul (⟨a, hCM a.2⟩ : ↥M)
          (⟨b, hCM b.2⟩ : ↥M) }
  have hker : ψ.ker = Q.subgroupOf C := by
    ext c
    constructor
    · intro hc
      have h1 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hCM c.2⟩ : Mbar M Q) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (N := Q.subgroupOf M) ⟨c, hCM c.2⟩).mp h1))
    · intro hc
      refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
      exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) ⟨c, hCM c.2⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc))
  have hrange : ψ.range = Subgroup.centralizer (((bar M Q S).subgroupOf (bar M Q (H0 M Z)) :
      Subgroup _) : Set ↥(bar M Q (H0 M Z))) := by
    ext h
    constructor
    · rintro ⟨c, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
      obtain ⟨x, hx, hxs⟩ := (Subgroup.mem_subgroupOf.mp hs)
      have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
      have hcomm := ((hCiff c).mp c.2).2 x hxS
      apply Subtype.ext
      show (s : Mbar M Q) * QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hCM c.2⟩ =
        QuotientGroup.mk' (Q.subgroupOf M) ⟨c, hCM c.2⟩ * (s : Mbar M Q)
      rw [← hxs]
      exact (mk_comm_iff (M := M) (Q := Q) x ⟨c, hCM c.2⟩).mpr (by
        rw [← commutatorElement_inv]
        exact Q.inv_mem hcomm)
    · intro hh
      obtain ⟨h', hh', hhm⟩ := h.2
      have hhH : (h' : G) ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hh'
      have hcomm : ∀ x ∈ S, ⁅(h' : G), x⁆ ∈ Q := by
        intro x hx
        have hxM : x ∈ M := hSM hx
        have hmem : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈ bar M Q S :=
          ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
        have hmemH : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) ∈
            bar M Q (H0 M Z) := ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr (hSH hx), rfl⟩
        have h1 : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩, hmemH⟩ :
            ↥(bar M Q (H0 M Z))) ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) := hmem
        have h2 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ : Mbar M Q) * (h : Mbar M Q) =
            (h : Mbar M Q) * QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ :=
          congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hh _ h1)
        rw [← hhm] at h2
        exact (mk_comm_iff (M := M) (Q := Q) h' ⟨x, hxM⟩).mp h2.symm
      refine ⟨⟨h', (hCiff h').mpr ⟨hhH, hcomm⟩⟩, ?_⟩
      apply Subtype.ext
      exact hhm
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hcard
  have hQcard : Nat.card (Q.subgroupOf C) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  rw [hQcard] at hcard
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hdvd : Nat.card ↥(Subgroup.centralizer (((bar M Q S).subgroupOf
      (bar M Q (H0 M Z)) : Subgroup _) : Set ↥(bar M Q (H0 M Z)))) ∣ Nat.card Z - 1 := by
    have h1 : Nat.card Q * Nat.card ↥(Subgroup.centralizer (((bar M Q S).subgroupOf
        (bar M Q (H0 M Z)) : Subgroup _) : Set ↥(bar M Q (H0 M Z)))) ∣
        Nat.card Q * (Nat.card Z - 1) := hcard ▸ hCdvd
    exact Nat.dvd_of_mul_dvd_mul_left hQpos h1
  have hodd1 : Odd (Nat.card Z - 1) := by
    obtain ⟨r, hr⟩ := hq
    have hpos : 0 < Nat.card Z := Nat.card_pos
    exact ⟨r - 1, by omega⟩
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Odd.of_dvd_nat hodd1 hdvd)

theorem outer_solvable_of_subsingleton (X : Type) [Group X] [Subsingleton X] :
    Group.IsSolvable (Outer X) := by
  haveI : Subsingleton (MulAut X) := ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
  exact Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

theorem outer_solvable_statedSL {K : Type} [Field K] [Finite K]
    (hq : ∃ a : ℕ, 2 ≤ a ∧ Nat.card K = 2 ^ a) (n : ℕ) :
    Group.IsSolvable (Outer (StatedSL n K)) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · haveI : Subsingleton (StatedSL 0 K) :=
        ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => i.elim0))⟩
      exact outer_solvable_of_subsingleton _
    · haveI : Subsingleton (SL(1, K)) := ⟨fun A B => by
        apply Subtype.ext
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst hi hj
        have hA := A.det_coe
        have hB := B.det_coe
        rw [Matrix.det_unique] at hA hB
        exact hA.trans hB.symm⟩
      haveI : Subsingleton (StatedSL 1 K) :=
        (specialLinearGroupEquivStatedSL 1 K).symm.injective.subsingleton
      exact outer_solvable_of_subsingleton _
    · exact (isSLModel_two_facts hq ⟨K, inferInstance, inferInstance, rfl,
        ⟨MulEquiv.refl _⟩⟩).2.2.1
  · have h1 :=
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux.outer_solvable_SL_quotient
      (K := K) (n := n) hn (Z₀ := ⊥) bot_le
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      ((QuotientGroup.quotientBot).trans (specialLinearGroupEquivStatedSL n K))

theorem false_of_caseVI (hQS : Q ≤ S) (hSM : S ≤ M) (hSH : S ≤ H0 M Z)
    (hSn : (S.subgroupOf M).Normal) (hq : ∃ a : ℕ, 2 ≤ a ∧ Nat.card Z = 2 ^ a)
    (hZQ : Nat.card Z < Nat.card Q) (hVI : CaseVI M Q Z S) (hQR : Q ≤ R) (hRM : R ≤ M)
    (hRH : R ≤ H0 M Z) (hperf : QuotSat R Q (fun X _ => Group.IsPerfect X))
    (hirr : ∀ A : Subgroup G, Z ≤ A → A ≤ Q → (∀ r ∈ R, conjSubgroup r A = A) →
      A = Z ∨ A = Q) : False := by
  obtain ⟨n, K, _, _, hK, φ, hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup, hact1,
    -, ⟨x, hxM, hx⟩, hCD⟩ := hVI
  have hKq : ∃ a : ℕ, 2 ≤ a ∧ Nat.card K = 2 ^ a := by
    obtain ⟨a, ha, hZa⟩ := hq
    exact ⟨a, ha, hK.trans hZa⟩
  haveI hn : (Q.subgroupOf S).Normal := hker ▸ φ.normal_ker
  have hSout : QuotSat S Q (fun X _ => Group.IsSolvable (Outer X)) := by
    refine ⟨hn, ?_⟩
    haveI := outer_solvable_statedSL hKq n
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)).symm
  have hC := solvable_centralizer_of_centDvd hSM hSH (by
    obtain ⟨a, ha, hZa⟩ := hq
    rw [hZa]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)) hCD
  have hRS : R ≤ S := le_of_perfect_outer hQS hSM hSH hSn hC hQR hRM hRH hperf hSout
  have hinv : ∀ r ∈ R, conjSubgroup r V₁ = V₁ := fun r hr =>
    conjSubgroup_eq_self_iff.mpr (hact1.1 (hRS hr))
  have hcard : Nat.card V₂ = Nat.card V₁ := by
    rw [← hx]
    exact card_conjSubgroup x V₁
  rcases hirr V₁ hZV₁ hV₁Q hinv with h | h
  ·
    have hV₂ : V₂ = Q := by
      rw [← hsup, h]
      exact (sup_eq_right.mpr hZV₂).symm
    rw [hV₂, h] at hcard
    omega
  · have hV₂ : V₂ = Z := by
      rw [← hinf, h]
      exact (inf_eq_right.mpr hV₂Q).symm
    rw [hV₂, h] at hcard
    omega

end Bridge

section Models

variable {q : ℕ}

theorem isSimpleProd2_of_sl_omegaMinus_two (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) {X : Type}
    [Group X] (h : IsProdOf (IsSLModel 2 q) (IsOmegaMinus 2 q) X) : IsSimpleProd2 X := by
  obtain ⟨A, B, _, _, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨hAs, hAn, hAo, -⟩ := isSLModel_two_facts hq hA
  obtain ⟨hBs, hBn, hBo, -⟩ := isOmegaMinus_two_facts hq hB
  exact ⟨A, B, _, _, hAs, hBs, hAn, hBn, hAo, hBo, ⟨e⟩⟩

theorem isSimpleProd3_of_sl_omegaPlus_two (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) {X : Type}
    [Group X] (h : IsProdOf (IsSLModel 2 q) (IsOmegaPlus 2 q) X) : IsSimpleProd3 X := by
  obtain ⟨A, B, _, _, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨B₁, B₂, _, _, hB₁, hB₂, ⟨e'⟩⟩ := isOmegaPlus_two_split hq hB
  obtain ⟨hAs, hAn, hAo, -⟩ := isSLModel_two_facts hq hA
  obtain ⟨hB₁s, hB₁n, hB₁o, -⟩ := isSLModel_two_facts hq hB₁
  obtain ⟨hB₂s, hB₂n, hB₂o, -⟩ := isSLModel_two_facts hq hB₂
  exact ⟨A, B₁, B₂, _, _, _, hAs, hB₁s, hB₂s, hAn, hB₁n, hB₂n, hAo, hB₁o, hB₂o,
    ⟨e.trans (MulEquiv.prodCongr (MulEquiv.refl A) e')⟩⟩

theorem isSimpleProd2_of_sl_omegaPlus_four (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) {X : Type}
    [Group X] (h : IsProdOf (IsSLModel 2 q) (IsOmegaPlus 4 q) X) : IsSimpleProd2 X := by
  obtain ⟨A, B, _, _, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨hAs, hAn, hAo, -⟩ := isSLModel_two_facts hq hA
  obtain ⟨hBs, hBn, hBo, -⟩ := isOmegaPlus_four_facts hq hB
  exact ⟨A, B, _, _, hAs, hBs, hAn, hBn, hAo, hBo, ⟨e⟩⟩

theorem isSimpleProd2_of_sl_omegaMinus_four (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) {X : Type}
    [Group X] (h : IsProdOf (IsSLModel 2 q) (IsOmegaMinus 4 q) X) : IsSimpleProd2 X := by
  obtain ⟨A, B, _, _, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨hAs, hAn, hAo, -⟩ := isSLModel_two_facts hq hA
  obtain ⟨hBs, hBn, hBo, -⟩ := isOmegaMinus_four_facts hq hB
  exact ⟨A, B, _, _, hAs, hBs, hAn, hBn, hAo, hBo, ⟨e⟩⟩

end Models

section Master

variable {X : Type} [Group X] [Finite X]

theorem ConfigSatz.card_cen {N : Subgroup X} (hS : ConfigSatz N) :
    ∃ a : ℕ, 2 ≤ a ∧ Nat.card (cen N) = 2 ^ a := by
  obtain ⟨a, -, ha, -⟩ := hS.1.cp
  refine ⟨a, ?_, ha⟩
  by_contra hlt
  have h4 := hS.1.q4
  rw [ha] at h4
  interval_cases a <;> simp at h4

theorem secondCfg_le {N R : Subgroup X} {k : ℕ} (hk : k = 4 ∨ k = 8) (hS : ConfigSatz N)
    (hW : Width N (cen N) k) (hgen : k = 4 → StrothGenByBStatement)
    (hCi : k = 4 → Stroth4iStatement)
    (hNR : N ≤ R) (hRC : R ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X))
    (hperf : QuotSat R N (fun X _ => Group.IsPerfect X))
    (hirr : ∀ A : Subgroup X, cen N ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) →
      A = cen N ∨ A = N) :
    ∃ S : Subgroup X, N ≤ S ∧ S ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X) ∧ R ≤ S ∧
      ((k = 4 ∧ QuotSat S N (IsSLModel 2 (Nat.card (cen N) ^ 3))) ∨
        ∃ m : ℕ, 2 ≤ m ∧ 2 * m = k ∧
          (QuotSat S N (IsProdOf (IsSLModel 2 (Nat.card (cen N)))
              (IsOmegaPlus m (Nat.card (cen N)))) ∨
            QuotSat S N (IsProdOf (IsSLModel 2 (Nat.card (cen N)))
              (IsOmegaMinus m (Nat.card (cen N)))))) := by
  obtain ⟨B₂, hc, hcases⟩ := secondCfg_cases hk hS hW hgen hCi
  haveI := hc.normal_Q_in_M
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hQS : N ≤ Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
      (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) :=
    sec39_Q_le_LB.trans (le_Lgen _)
  have hSM := Lgen_le (M := Subgroup.normalizer ((cen N : Subgroup X) : Set X)) hc.LB_le_M
  have hSH := hc.Lgen_le_H0_sec4x
  have hSn := Lgen_normal (M := Subgroup.normalizer ((cen N : Subgroup X) : Set X)) hc.LB_le_M
  have hRM : R ≤ Subgroup.normalizer ((cen N : Subgroup X) : Set X) :=
    hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hRH : R ≤ H0 (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) (cen N) :=
    fun x hx => ⟨hRM hx, hRC hx⟩
  have hqq : 2 ≤ Nat.card (cen N) := le_trans (by norm_num) hS.1.q4
  have hZQ : Nat.card (cen N) < Nat.card N := by
    rw [show Nat.card N = Nat.card (cen N) ^ (2 * k + 1) from hW]
    calc Nat.card (cen N) = Nat.card (cen N) ^ 1 := (pow_one _).symm
      _ < Nat.card (cen N) ^ (2 * k + 1) := Nat.pow_lt_pow_right hqq (by omega)
  have hSC : Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
      (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) ≤
      Subgroup.centralizer ((cen N : Subgroup X) : Set X) := fun x hx => (hSH hx).2
  rcases hcases with ⟨hk4, hS3, hCT⟩ | ⟨m, hm2, hmk, hCT, hQ⟩ | hVI
  · refine ⟨_, hQS, hSC, ?_, Or.inl ⟨hk4, hS3⟩⟩
    have hq3 : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) ^ 3 = 2 ^ a' :=
      ⟨3 * a, by omega, by rw [haq, ← pow_mul, mul_comm]⟩
    have hOut := quotSat_mono (fun X _ h => (isSLModel_two_facts hq3 h).2.2.1) hS3
    exact le_of_perfect_outer hQS hSM hSH hSn
      (solvable_centralizer_of_centTrivial hSM hSH hCT) hNR hRM hRH hperf hOut
  · refine ⟨_, hQS, hSC, ?_, Or.inr ⟨m, hm2, hmk, hQ⟩⟩
    have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
    have hm : m = 2 ∨ m = 4 := by omega
    rcases hm with rfl | rfl
    · rcases hQ with hQp | hQm
      · exact le_of_perfect_prod3 hQS hSM hSH hSn hCT hNR hRM hRH hperf
          (quotSat_mono (fun X _ h => isSimpleProd3_of_sl_omegaPlus_two hqa h) hQp)
      · exact le_of_perfect_prod2 hQS hSM hSH hSn hCT hNR hRM hRH hperf
          (quotSat_mono (fun X _ h => isSimpleProd2_of_sl_omegaMinus_two hqa h) hQm)
    · rcases hQ with hQp | hQm
      · exact le_of_perfect_prod2 hQS hSM hSH hSn hCT hNR hRM hRH hperf
          (quotSat_mono (fun X _ h => isSimpleProd2_of_sl_omegaPlus_four hqa h) hQp)
      · exact le_of_perfect_prod2 hQS hSM hSH hSn hCT hNR hRM hRH hperf
          (quotSat_mono (fun X _ h => isSimpleProd2_of_sl_omegaMinus_four hqa h) hQm)
  · exact (false_of_caseVI hQS hSM hSH hSn ⟨a, ha2, haq⟩ hZQ hVI hNR hRM hRH hperf hirr).elim

end Master

end CFSG.RankThree.GF2n.Stroth80
