module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U3
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U7Norm
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

private lemma p9u8a_ker_le_projU_ker (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) :
    φ.ker ≤ (InndiagSU.projU 1 m F).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  haveI : ((LargeEvenScalars (Fin m) F).subgroupOf
      (LargeEvenSUGroup (Fin m) F (2 ^ 1))).Normal :=
    LargeEvenScalars.normal.subgroupOf _
  haveI : ((LargeEvenScalars (Fin m) F).subgroupOf (unitarySU 2 1 F m)).Normal :=
    LargeEvenScalars.normal.subgroupOf _
  obtain ⟨c, hc⟩ := hφker g hg
  have hc_ne_zero : c ≠ 0 := by
    have hunit : IsUnit (diagonal (fun _ : Fin m => c) : Matrix (Fin m) (Fin m) F) := by
      rw [← hc]
      exact Units.isUnit (g : GL (Fin m) F)
    have hvec : IsUnit (fun _ : Fin m => c) := Matrix.isUnit_diagonal.mp hunit
    haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    exact isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp hvec (Classical.arbitrary (Fin m)))
  let u : Fˣ := Units.mk0 c hc_ne_zero
  have hu : Matrix.GeneralLinearGroup.scalar (Fin m) u = (g : GL (Fin m) F) := by
    apply Units.ext
    rw [hc]
    rfl
  have hscalar : (g : GL (Fin m) F) ∈ LargeEvenScalars (Fin m) F := by
    rw [CFSG.Assembly.largeEvenScalars_def]
    exact ⟨u, hu⟩
  change QuotientGroup.mk' ((LargeEvenScalars (Fin m) F).subgroupOf
    (LargeEvenSUGroup (Fin m) F (2 ^ 1))) g = 1
  exact (@QuotientGroup.eq_one_iff (↥(unitarySU 2 1 F m)) _
    ((LargeEvenScalars (Fin m) F).subgroupOf (LargeEvenSUGroup (Fin m) F (2 ^ 1)))
    (LargeEvenScalars.normal.subgroupOf _) g).mpr (Subgroup.mem_subgroupOf.mpr hscalar)

private noncomputable def p9u8a_proj_lift (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) :
    L →* LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1)) :=
  (QuotientGroup.lift φ.ker (InndiagSU.projU 1 m F) (p9u8a_ker_le_projU_ker h hm hφker)).comp
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.toMonoidHom

private lemma p9u8a_proj_lift_apply (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    (s : ↥(unitarySU 2 1 F m)) :
    p9u8a_proj_lift h hm hφs hφker (φ s) = InndiagSU.projU 1 m F s := by
  unfold p9u8a_proj_lift
  rw [MonoidHom.comp_apply]
  change (QuotientGroup.lift φ.ker (InndiagSU.projU 1 m F) _)
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ s)) = _
  have hsymm : (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ s) =
      QuotientGroup.mk s := by
    rw [MulEquiv.symm_apply_eq]
    change φ s = QuotientGroup.kerLift φ (QuotientGroup.mk s)
    rw [QuotientGroup.kerLift_mk]
  rw [hsymm, QuotientGroup.lift_mk]

private lemma p9u8a_proj_lift_surjective (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) :
    Function.Surjective (p9u8a_proj_lift h hm hφs hφker) := by
  intro r
  obtain ⟨s, rfl⟩ := InndiagSU.projU_surjective (n := 1) (d := m) (K := F) r
  exact ⟨φ s, p9u8a_proj_lift_apply h hm hφs hφker s⟩

private lemma p9u8a_proj_lift_ker (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) :
    (p9u8a_proj_lift h hm hφs hφker).ker = Subgroup.center L := by
  apply le_antisymm
  · intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨s, rfl⟩ := hφs l
    have hproj : InndiagSU.projU 1 m F s = 1 := by
      rw [← p9u8a_proj_lift_apply h hm hφs hφker s]
      exact hl
    have hscalar := TableBUI.mem_scalars_of_projU_eq_one hproj
    have hscalar_center : (s : GL (Fin m) F) ∈ Subgroup.center (GL (Fin m) F) :=
      TableB.scalars_le_center hscalar
    rw [Subgroup.mem_center_iff]
    intro l'
    obtain ⟨s', rfl⟩ := hφs l'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hscalar_center) (s' : GL (Fin m) F)
  · intro l hl
    rw [MonoidHom.mem_ker]
    have hmem : p9u8a_proj_lift h hm hφs hφker l ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l', rfl⟩ := p9u8a_proj_lift_surjective h hm hφs hφker r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl l']
    haveI : Finite F := h.finite
    have hK : Nat.card F = (2 ^ 1) ^ 2 := by
      rw [h.card]
      norm_num
    have hd : 3 ≤ m := by omega
    have hdq : (m, 2 ^ 1) ≠ (3, 2) := by
      intro h3
      have : m = 3 := congrArg Prod.fst h3
      omega
    have hbot := TableBUE.center_proj_eq_bot (n := 1) (d := m) (K := F) hK hd hdq
    rw [hbot] at hmem
    exact hmem

private lemma p9u8a_induced_aut (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    (β : MulAut L) :
    ∃ ω : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))),
      ∀ l : L, ω (p9u8a_proj_lift h hm hφs hφker l) =
        p9u8a_proj_lift h hm hφs hφker (β l) := by
  let π := p9u8a_proj_lift h hm hφs hφker
  have hπs := p9u8a_proj_lift_surjective h hm hφs hφker
  have hπker := p9u8a_proj_lift_ker h hm hφs hφker
  let e : (L ⧸ π.ker) ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1)) :=
    QuotientGroup.quotientKerEquivOfSurjective π hπs
  let βq : MulAut (L ⧸ π.ker) :=
    QuotientGroup.congr π.ker π.ker β (by
      rw [hπker, Subgroup.map_center_eq β, ← hπker])
  let ω : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) :=
    MulAut.congr e βq
  have he_all : ∀ l : L, e (QuotientGroup.mk l) = π l := by
    intro l
    change QuotientGroup.kerLift π (QuotientGroup.mk l) = π l
    exact QuotientGroup.kerLift_mk π l
  have hω : ∀ l : L, ω (π l) = π (β l) := by
    intro l
    have hbq : βq (QuotientGroup.mk l) = QuotientGroup.mk (β l) :=
      QuotientGroup.congr_mk π.ker π.ker β _ l
    change MulAut.congr e βq (e (QuotientGroup.mk l)) = π (β l)
    rw [show MulAut.congr e βq (e (QuotientGroup.mk l)) =
      e (βq (QuotientGroup.mk l)) from by
      change (e.symm.trans (βq.trans e)) (e (QuotientGroup.mk l)) =
        e (βq (QuotientGroup.mk l))
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]]
    rw [hbq, he_all (β l)]
  exact ⟨ω, hω⟩

private lemma p9u8a_sigmaB (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    (β : MulAut L) {B : GL (Fin m) F}
    (hB : B ∈ UnitaryHigher.primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F m))
    {τ : F ≃+* F}
    {ω : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1)))}
    (hω : ∀ l : L, ω (p9u8a_proj_lift h hm hφs hφker l) =
      p9u8a_proj_lift h hm hφs hφker (β l))
    (hsl : InndiagSU.IsSemilin (InndiagSU.projU 1 m F) ω B τ) :
    ∃ σB : ↥(unitarySU 2 1 F m) →* ↥(unitarySU 2 1 F m),
      (∀ s, (σB s : GL (Fin m) F) = B * UnitaryHigher.glAut τ (s : GL (Fin m) F) * B⁻¹) ∧
      (∀ s, (β (φ s))⁻¹ * (φ (σB s)) ∈ Subgroup.center L) := by
  let σB : ↥(unitarySU 2 1 F m) →* ↥(unitarySU 2 1 F m) :=
    { toFun := fun s => ⟨B * UnitaryHigher.glAut τ (s : GL (Fin m) F) * B⁻¹,
        InndiagSU.semilin_mem h hB τ s⟩
      map_one' := by
        apply Subtype.ext
        simp [map_one, MulAut.one_apply]
      map_mul' := fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul]
        group }
  have hσB : ∀ s, (σB s : GL (Fin m) F) =
      B * UnitaryHigher.glAut τ (s : GL (Fin m) F) * B⁻¹ := fun _ => rfl
  have hπeq : ∀ s, p9u8a_proj_lift h hm hφs hφker (β (φ s)) =
      p9u8a_proj_lift h hm hφs hφker (φ (σB s)) := by
    intro s
    rw [← hω (φ s), p9u8a_proj_lift_apply h hm hφs hφker s]
    rw [show p9u8a_proj_lift h hm hφs hφker (φ (σB s)) =
      InndiagSU.projU 1 m F (σB s) from p9u8a_proj_lift_apply h hm hφs hφker (σB s)]
    apply hsl
    exact (hσB s).symm
  have hker : ∀ s, (β (φ s))⁻¹ * (φ (σB s)) ∈ Subgroup.center L := by
    intro s
    rw [← p9u8a_proj_lift_ker h hm hφs hφker]
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv]
    rw [hπeq s]
    exact inv_mul_cancel _
  exact ⟨σB, hσB, hker⟩

private lemma p9u8a_semilin_extend (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    (β : MulAut L) {B : GL (Fin m) F} {τ : F ≃+* F}
    {σB : ↥(unitarySU 2 1 F m) →* ↥(unitarySU 2 1 F m)}
    (hσB : ∀ s, (σB s : GL (Fin m) F) =
      B * UnitaryHigher.glAut τ (s : GL (Fin m) F) * B⁻¹)
    (hker : ∀ s, (β (φ s))⁻¹ * (φ (σB s)) ∈ Subgroup.center L) :
    InndiagSU.IsSemilin φ β B τ := by
  have hperf : commutator (↥(unitarySU 2 1 F m)) = ⊤ := by
    haveI : Finite F := h.finite
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := h.charP
    have hK : Nat.card F = (2 ^ 1) ^ 2 := by
      rw [h.card]
      norm_num
    have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) (n := m)
      hK (by omega) (by
        intro h3
        exact absurd (congrArg Prod.fst h3) (by omega))
    exact hperf.commutator_eq_top
  let α1 : ↥(unitarySU 2 1 F m) →* L := β.toMonoidHom.comp φ
  let α2 : ↥(unitarySU 2 1 F m) →* L := φ.comp σB
  have heq : α1 = α2 := CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperf α1 α2 hker
  intro u v huv
  have hf : β (φ u) = φ (σB u) := congrArg (fun f => f u) heq
  have hvu : σB u = v := by
    apply Subtype.ext
    rw [hσB u]
    exact huv.symm
  rw [hf, hvu]

theorem P9_U8a_exists_isSemilin (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    (β : MulAut L) :
    ∃ g ∈ UnitaryHigher.primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F m),
      ∃ τ : F ≃+* F, InndiagSU.IsSemilin φ β g τ := by
  obtain ⟨ω, hω⟩ := p9u8a_induced_aut h hm hφs hφker β
  obtain ⟨B, hB, hsl⟩ := InndiagSU.exists_isSemilin (h := h) (by omega : 3 ≤ m) (by
    intro h3
    exact absurd (h3.1) (by omega)) ω
  let τ : F ≃+* F := InndiagSU.fieldFactorU h (by omega : 3 ≤ m) (by
    intro h3
    exact absurd (h3.1) (by omega)) ω
  obtain ⟨σB, hσB, hker⟩ := p9u8a_sigmaB h hm hφs hφker β hB hω hsl
  exact ⟨B, hB, τ, p9u8a_semilin_extend h hm hφs hφker β hσB hker⟩
private lemma p9u8a_units_map_mod_ne_zero (h : UnitaryFieldData 2 1 F) (τ : F ≃+* F)
    {k : ℤ} (hcard : Nat.card Fˣ = 3) (h3 : ∀ c : Fˣ, c ^ 3 = 1)
    (hmod : ∀ c : Fˣ, c ^ k = c ^ (k % 3))
    (hk : ∀ c : Fˣ, Units.map τ.toMonoidHom c = c ^ k) : k % 3 ≠ 0 := by
  haveI : Finite F := h.finite
  intro h0
  have hkill : ∀ c : Fˣ, Units.map τ.toMonoidHom c = 1 := by
    intro c
    rw [hk c, hmod c, h0]
    simp
  have hthis : ∀ c : Fˣ, c = 1 := by
    intro c
    apply Units.ext
    apply τ.injective
    have hc := hkill c
    have h1 : (Units.map τ.toMonoidHom c : F) = 1 := by
      rw [hc]
      rfl
    change τ (c : F) = τ (1 : F)
    rw [map_one]
    exact h1
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have h2 : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card h2 1
  exact hc (hthis c)

private lemma p9u8a_units_map (h : UnitaryFieldData 2 1 F) (τ : F ≃+* F) :
    ∃ e : ℤˣ, ∀ c : Fˣ, Units.map τ.toMonoidHom c = c ^ (e : ℤ) := by
  haveI : Finite F := h.finite
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hcyc : IsCyclic Fˣ := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card hcard
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic (Units.map τ.toMonoidHom)
  have h3 : ∀ c : Fˣ, c ^ 3 = 1 := by
    intro c
    rw [← hcard]
    exact pow_card_eq_one' (x := c)
  have hmod : ∀ c : Fˣ, c ^ k = c ^ (k % 3) := by
    intro c
    have h3z : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact h3 c
    exact zpow_eq_zpow_emod (x := c) k h3z
  have hk0 := p9u8a_units_map_mod_ne_zero h τ hcard h3 hmod hk
  have hk1or2 : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hge : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    omega
  rcases hk1or2 with h1 | h2
  · refine ⟨1, fun c => ?_⟩
    rw [hk c, hmod c, h1]
    simp
  · refine ⟨-1, fun c => ?_⟩
    rw [hk c, hmod c, h2]
    have hneg : ((↑(-1 : ℤˣ) : ℤ)) = (-1 : ℤ) := rfl
    rw [hneg, zpow_neg_one (x := c)]
    have hc3 : c ^ 3 = 1 := h3 c
    calc c ^ 2 = c ^ 3 * c⁻¹ := by group
      _ = 1 * c⁻¹ := by rw [hc3]
      _ = c⁻¹ := by rw [one_mul]

theorem P9_U8a_exists_perm_zpow (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L))) :
    ∃ (σ : Equiv.Perm (Fin m)) (e : ℤˣ), ∀ (a : ↥A) (t : Fin m → Fˣ),
      ι a = QuotientGroup.mk t →
        ι (ggConjAut A hβ a) = QuotientGroup.mk (fun i => t (σ.symm i) ^ (e : ℤ)) := by
  obtain ⟨g, hg, τ, hsl⟩ := P9_U8a_exists_isSemilin h hm hφs hφker β
  obtain ⟨σ, hσ⟩ := P9_U7a_perm_of_normalizes h (by omega : 3 ≤ m) hφker hdiag ι hι hinner hβ hg hsl
  obtain ⟨e, he⟩ := p9u8a_units_map h τ
  refine ⟨σ, e, fun a t ht => ?_⟩
  rw [hσ a t ht]
  congr 1
  funext i
  exact he (t (σ.symm i))

end CFSG.StandardType.FrameRoute

end
