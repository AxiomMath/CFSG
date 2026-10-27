module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullTorus2
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTclNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTidRange
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTker

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 Matrix
  CFSG.ClassicalInvolution.Phan Multiplicative

theorem qTwoLMDivF_rigid_scalar {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} (hm : 4 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {g1 g2 : GL (Fin m) F0} {b : ↥Bs}
    (h1 : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = g1 * (s : GL (Fin m) F0) * g1⁻¹ ∧ ρ b (π s) = π s')
    (h2 : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = g2 * (s : GL (Fin m) F0) * g2⁻¹ ∧ ρ b (π s) = π s') :
    ∃ z : F0, ((g2 * g1⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun _ => z) := by
  classical
  let f : Su F0 2 1 m → Su F0 2 1 m := fun s => Classical.choose (h1 s)
  have hf : ∀ s, (f s : GL (Fin m) F0) = g1 * (s : GL (Fin m) F0) * g1⁻¹ ∧
      ρ b (π s) = π (f s) := fun s => Classical.choose_spec (h1 s)
  have hf_inj : Function.Injective f := by
    intro s s' h
    have h1s := (hf s).1
    have h1s' := (hf s').1
    have h3 : g1 * (s : GL (Fin m) F0) * g1⁻¹ = g1 * (s' : GL (Fin m) F0) * g1⁻¹ := by
      rw [← h1s, ← h1s', congrArg Subtype.val h]
    apply Subtype.ext
    have h4 := congrArg (fun x : GL (Fin m) F0 => g1⁻¹ * x * g1) h3
    simpa [mul_assoc] using h4
  let e : Su F0 2 1 m ≃ Su F0 2 1 m := Equiv.ofBijective f hf_inj.bijective_of_finite
  refine qTwoLMDivCoordInner_rigid hU.card hm π hU.π_ker (k := g2 * g1⁻¹) ?_
  intro s
  obtain ⟨s2, hs2, hπ2⟩ := h2 (e.symm s)
  have hey : (f (e.symm s) : GL (Fin m) F0) = (s : GL (Fin m) F0) :=
    congrArg Subtype.val (e.apply_symm_apply s)
  have hy : ((e.symm s : Su F0 2 1 m) : GL (Fin m) F0) = g1⁻¹ * (s : GL _ F0) * g1 := by
    have h1s := (hf (e.symm s)).1
    rw [hey] at h1s
    calc ((e.symm s : Su F0 2 1 m) : GL (Fin m) F0)
        = g1⁻¹ * (g1 * ((e.symm s : Su F0 2 1 m) : GL (Fin m) F0) * g1⁻¹) * g1 := by group
      _ = g1⁻¹ * (s : GL (Fin m) F0) * g1 := by rw [← h1s]
  have hπy : π (e.symm s) = (ρ b)⁻¹ (π s) := by
    have hfe : f (e.symm s) = s := e.apply_symm_apply s
    have h1s := (hf (e.symm s)).2
    rw [hfe] at h1s
    rw [← h1s]
    exact (MulEquiv.symm_apply_apply (ρ b) _).symm
  refine ⟨s2, ?_, ?_⟩
  · rw [hs2, hy]; group
  · rw [← hπ2, hπy]
    exact MulEquiv.apply_symm_apply (ρ b) _

noncomputable def qTwoLMDivF_rep {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (b : ↥Bs) : GL (Fin m) F0 :=
  Classical.choose (hU.diag b)

theorem qTwoLMDivF_rep_diag {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (b : ↥Bs) :
    ggIsDiagMat (qTwoLMDivF_rep hU b) :=
  (Classical.choose_spec (hU.diag b)).1

theorem qTwoLMDivF_rep_act {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (b : ↥Bs) :
    ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = qTwoLMDivF_rep hU b * (s : GL (Fin m) F0) *
        (qTwoLMDivF_rep hU b)⁻¹ ∧ ρ b (π s) = π s' :=
  (Classical.choose_spec (hU.diag b)).2

noncomputable def qTwoLMDivF_coord {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) (b : ↥Bs) : Fin m → Multiplicative (ZMod 3) :=
  Classical.choose (hδ.surj_diag (qTwoLMDivF_rep hU b) (qTwoLMDivF_rep_diag hU b))

theorem qTwoLMDivF_coord_spec {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) (b : ↥Bs) :
    δ (qTwoLMDivF_coord hU hF0 hδ b) = qTwoLMDivF_rep hU b :=
  Classical.choose_spec (hδ.surj_diag (qTwoLMDivF_rep hU b) (qTwoLMDivF_rep_diag hU b))

theorem qTwoLMDivF_rep_mul_act {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (b b' : ↥Bs) :
    ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = (qTwoLMDivF_rep hU b * qTwoLMDivF_rep hU b') *
        (s : GL (Fin m) F0) * (qTwoLMDivF_rep hU b * qTwoLMDivF_rep hU b')⁻¹ ∧
        ρ (b * b') (π s) = π s' := by
  intro s
  obtain ⟨s1, hs1, hπ1⟩ := qTwoLMDivF_rep_act hU b' s
  obtain ⟨s2, hs2, hπ2⟩ := qTwoLMDivF_rep_act hU b s1
  refine ⟨s2, ?_, ?_⟩
  · rw [hs2, hs1]; group
  · rw [map_mul, MulAut.mul_apply, hπ1, hπ2]

theorem qTwoLMDivF_coord_mul {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} (hm : 4 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) (b b' : ↥Bs) :
    qTwoLMDivF_coord hU hF0 hδ (b * b') /
        (qTwoLMDivF_coord hU hF0 hδ b * qTwoLMDivF_coord hU hF0 hδ b') ∈
      Subgroup.zpowers (qTwoLMDivF_oneVec m) := by
  obtain ⟨z, hz⟩ := qTwoLMDivF_rigid_scalar hm hU (qTwoLMDivF_rep_mul_act hU b b')
    (qTwoLMDivF_rep_act hU (b * b'))
  have hz' : ((δ (qTwoLMDivF_coord hU hF0 hδ (b * b') /
      (qTwoLMDivF_coord hU hF0 hδ b * qTwoLMDivF_coord hU hF0 hδ b')) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun _ => z) := by
    rw [map_div, map_mul, qTwoLMDivF_coord_spec, qTwoLMDivF_coord_spec, qTwoLMDivF_coord_spec]
    exact hz
  exact (hδ.scalar _).mp ⟨z, hz'⟩

theorem qTwoLMDivF_coord_one {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} (hm : 4 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) :
    qTwoLMDivF_coord hU hF0 hδ 1 ∈ Subgroup.zpowers (qTwoLMDivF_oneVec m) := by
  have htriv : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = (1 : GL (Fin m) F0) * (s : GL (Fin m) F0) *
        (1 : GL (Fin m) F0)⁻¹ ∧ ρ 1 (π s) = π s' := by
    intro s
    exact ⟨s, by rw [one_mul, inv_one, mul_one], by rw [map_one, MulAut.one_apply]⟩
  obtain ⟨z, hz⟩ := qTwoLMDivF_rigid_scalar hm hU htriv (qTwoLMDivF_rep_act hU 1)
  have hz' : ((δ (qTwoLMDivF_coord hU hF0 hδ 1) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun _ => z) := by
    rw [qTwoLMDivF_coord_spec]
    simpa using hz
  exact (hδ.scalar _).mp ⟨z, hz'⟩

@[expose] noncomputable def qTwoLMDivF_phi {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} (hm : 4 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) : ↥Bs →* QTwoQm m where
  toFun b := QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b)
  map_one' := (QuotientGroup.eq_one_iff _).mpr (qTwoLMDivF_coord_one hm hU hF0 hδ)
  map_mul' := fun b b' => by
    show (QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ (b * b')) : QTwoQm m) =
      QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b) *
        QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b')
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_iff_div_mem).mpr (qTwoLMDivF_coord_mul hm hU hF0 hδ b b')

theorem qTwoLMDivF_phi_apply {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {m : ℕ} (hm : 4 ≤ m) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hδ : QTwoDivFullTorus hF0 δ) (b : ↥Bs) :
    qTwoLMDivF_phi hm hU hF0 hδ b = QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b) :=
  rfl

end CFSG.StandardType.QTwo

end
