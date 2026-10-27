module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoSl2Gen
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LieType.Universal.Unitary.RootGroupCard
public import CFSG.LieType.Steinberg.CentralExt.SUPosLift
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal
open CFSG.LieType.Universal.Symplectic
open CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg.CentralExt.SUClosed

theorem irgSS_sp_card (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum 1 F).roots) :
    Nat.card ((Symplectic.rootDatum 1 F).rootGroup β) = Nat.card F := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
  let f : F → (Symplectic.rootDatum 1 F).rootGroup β := fun c =>
    ⟨SpExtras.elt r c, (SpExtras.mem_rootGroup_iff (F := F) hr).2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => SpExtras.elt_injective r (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨c, hc⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr).1 x.2
    exact ⟨c, Subtype.ext hc.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem irgSS_sp_card_neg (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum 1 F).roots) :
    Nat.card ((Symplectic.rootDatum 1 F).rootGroup (-β)) = Nat.card F := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
  have hr' : stdVec (CFSG.SeitzReduction.F4Pilot.negIdx r) =
      Symplectic.toStd 1 (-β) := by
    rw [CFSG.SeitzReduction.F4Pilot.stdVec_negIdx, hr, SpExtras.toStd_neg']
  let f : F → (Symplectic.rootDatum 1 F).rootGroup (-β) := fun c =>
    ⟨SpExtras.elt (CFSG.SeitzReduction.F4Pilot.negIdx r) c,
      (SpExtras.mem_rootGroup_iff (F := F) hr').2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => SpExtras.elt_injective _ (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨c, hc⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr').1 x.2
    exact ⟨c, Subtype.ext hc.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem irgSS_sp_inf (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum 1 F).roots) :
    (Symplectic.rootDatum 1 F).rootGroup β ⊓
      (Symplectic.rootDatum 1 F).rootGroup (-β) = ⊥ := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
  have hr' : stdVec (CFSG.SeitzReduction.F4Pilot.negIdx r) =
      Symplectic.toStd 1 (-β) := by
    rw [CFSG.SeitzReduction.F4Pilot.stdVec_negIdx, hr, SpExtras.toStd_neg']
  cases r with
  | difference i j hij => exact absurd (Subsingleton.elim i j) hij
  | positiveSum i j hij => exact absurd (Subsingleton.elim i j) hij.ne
  | negativeSum i j hij => exact absurd (Subsingleton.elim i j) hij.ne
  | positiveLong i =>
    rw [eq_bot_iff]
    rintro x ⟨hx, hy⟩
    obtain ⟨a, rfl⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr).1 hx
    obtain ⟨b, hb⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr').1 hy
    rw [Subgroup.mem_bot]
    change SpExtras.elt (.positiveLong i) a = SpExtras.elt (.negativeLong i) b at hb
    have h := congrFun
      (congrFun (congrArg (SpExtras.mat 1 F) hb) (Sum.inl i)) (Sum.inr i)
    rw [SpExtras.mat_elt_positiveLong, SpExtras.mat_elt_negativeLong] at h
    have h0 : Matrix.transvection (Sum.inr i) (Sum.inl i) b (Sum.inl i) (Sum.inr i) = 0 := by
      simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Sum.inl_ne_inr,
        Sum.inr_ne_inl]
    have h1 : Matrix.transvection (Sum.inl i) (Sum.inr i) a (Sum.inl i) (Sum.inr i) = a := by
      simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Sum.inl_ne_inr,
        Sum.inr_ne_inl]
    rw [h1, h0] at h
    rw [h, SpExtras.elt_zero]
  | negativeLong i =>
    rw [eq_bot_iff]
    rintro x ⟨hx, hy⟩
    obtain ⟨a, rfl⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr).1 hx
    obtain ⟨b, hb⟩ := (SpExtras.mem_rootGroup_iff (F := F) hr').1 hy
    rw [Subgroup.mem_bot]
    change SpExtras.elt (.negativeLong i) a = SpExtras.elt (.positiveLong i) b at hb
    have h := congrFun
      (congrFun (congrArg (SpExtras.mat 1 F) hb) (Sum.inr i)) (Sum.inl i)
    rw [SpExtras.mat_elt_positiveLong, SpExtras.mat_elt_negativeLong] at h
    have h0 : Matrix.transvection (Sum.inl i) (Sum.inr i) b (Sum.inr i) (Sum.inl i) = 0 := by
      simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Sum.inl_ne_inr,
        Sum.inr_ne_inl]
    have h1 : Matrix.transvection (Sum.inr i) (Sum.inl i) a (Sum.inr i) (Sum.inl i) = a := by
      simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Sum.inl_ne_inr,
        Sum.inr_ne_inl]
    rw [h1, h0] at h
    rw [h, SpExtras.elt_zero]

theorem irgSS_psu_exists_longPos {F : Type} [Field F] {γ : Fin 1 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots (Unitary.isFiniteType_cartan 2) (Unitary.divisible 2)) :
    ∃ i, IsLongPos (n := 2) γ i := by
  rcases short_or_long (n := 2) (by norm_num : Even 2) hγ with hs | hl
  · obtain ⟨⟨i, j⟩, hij, -, -, hji, -⟩ := hs
    fin_cases i <;> fin_cases j <;> simp_all
  · exact hl

theorem irgSS_neg_longPos {F : Type} [Field F] {n : ℕ} {γ : Fin (n / 2) → ℤ} {i : Fin n}
    (hri : Fin.rev i ≠ Fin.rev (Fin.rev i)) (hl : IsLongPos γ i) :
    IsLongPos (-γ) (Fin.rev i) := by
  refine ⟨hri, ?_⟩
  have hneg : Unitary.toStd n (-γ) = -Unitary.toStd n γ := by
    have h := Unitary.SUExtras.toStd_add' (n := n) (-γ) γ
    rw [neg_add_cancel, Unitary.SUExtras.toStd_zero'] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [hneg, Unitary.SUExtras.weight_rev', smul_neg, hl.2]

theorem irgSS_psu_rootGroup_eq_long {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {γ : Fin 1 → ℤ} {i : Fin 2}
    (hl : IsLongPos (n := 2) γ i) :
    Unitary.rootGroup σ hσ 2 γ = (Unitary.longRootHom σ hl.1).range := by
  refine le_antisymm ?_ ?_
  · unfold Unitary.rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun ha =>
        iSup_le fun _ => iSup_le fun hba => iSup_le fun hw => ?_
      exfalso
      rw [← hl.2] at hw
      obtain ⟨rfl, hbi⟩ := Unitary.SUExtras.eq_of_weight_sub_eq_two_smul hl.1 hw
      exact hba hbi
    · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hw => ?_
      rw [← hl.2] at hw
      have h2 : Unitary.weight 2 a - Unitary.weight 2 (Fin.rev a) =
          2 • Unitary.weight 2 i := by
        rw [Unitary.SUExtras.weight_rev', sub_neg_eq_add, ← two_nsmul]
        exact hw
      obtain ⟨rfl, -⟩ := Unitary.SUExtras.eq_of_weight_sub_eq_two_smul hl.1 h2
      exact le_rfl
    · refine iSup_le fun _ => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun hk => iSup_le fun _ => ?_
      exact absurd hk.symm (rev_ne_self_of_even (n := 2) (by norm_num) k)
  · rintro _ ⟨c, rfl⟩
    exact Unitary.SUExtras.longRootHom_mem hσ hl.1 hl.2 c

theorem irgSS_psu_card {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {γ : Fin 1 → ℤ} {i : Fin 2}
    (hl : IsLongPos (n := 2) γ i) :
    Nat.card (Unitary.rootGroup (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hF) 2 γ) = 2 ^ f := by
  rw [irgSS_psu_rootGroup_eq_long
      (hσ := unitaryInvolution_involutive hF) hl,
    Unitary.card_longRootHom_range,
    CFSG.LieType.Steinberg.card_traceZero (F := F) (p := 2) (f := f) hF]

theorem irgSS_psu_card_neg {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {γ : Fin 1 → ℤ} {i : Fin 2}
    (hl : IsLongPos (n := 2) γ i) :
    Nat.card (Unitary.rootGroup (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hF) 2 (-γ)) = 2 ^ f := by
  have hri : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hl.1.symm
  rw [irgSS_psu_rootGroup_eq_long (hσ := unitaryInvolution_involutive hF)
      (irgSS_neg_longPos (F := F) hri hl),
    Unitary.card_longRootHom_range,
    CFSG.LieType.Steinberg.card_traceZero (F := F) (p := 2) (f := f) hF]

theorem irgSS_longRootHom_inf {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {i : Fin n}
    (hi : i ≠ Fin.rev i) (hri : Fin.rev i ≠ Fin.rev (Fin.rev i)) :
    (Unitary.longRootHom σ hi).range ⊓ (Unitary.longRootHom σ hri).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨c, rfl⟩, ⟨d, hd⟩⟩
  rw [Subgroup.mem_bot]
  have hm : Unitary.SUExtras.mat σ n (Unitary.longRootHom σ hri d) =
      Unitary.SUExtras.mat σ n (Unitary.longRootHom σ hi c) :=
    congrArg (Unitary.SUExtras.mat σ n) hd
  have hoff : Unitary.SUExtras.mat σ n (Unitary.longRootHom σ hri d) i
      (Fin.rev i) = 0 := by
    rw [Unitary.SUExtras.mat_apply, Unitary.coe_longRootHom]
    simp [Unitary.longRootMatrix, Matrix.one_apply, Matrix.single_apply, hi, hi.symm]
  have hon : Unitary.SUExtras.mat σ n (Unitary.longRootHom σ hi c) i (Fin.rev i) =
      (c.toAdd : F) := by
    rw [Unitary.SUExtras.mat_apply, Unitary.coe_longRootHom,
      Unitary.SUExtras.longRootMatrix_apply hi]
  have hcF : (c.toAdd : F) = 0 := by
    have h := congrFun (congrFun hm i) (Fin.rev i)
    rw [hoff, hon] at h
    exact h.symm
  have hc1 : c = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hcF
  rw [hc1]
  exact map_one (Unitary.longRootHom σ hi)

theorem irgSS_psu_inf {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {γ : Fin 1 → ℤ} {i : Fin 2}
    (hl : IsLongPos (n := 2) γ i) :
    Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 2 γ ⊓
      Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 2 (-γ) = ⊥ := by
  have hri : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hl.1.symm
  have hlneg := irgSS_neg_longPos (F := F) hri hl
  rw [irgSS_psu_rootGroup_eq_long (hσ := unitaryInvolution_involutive hF) hl,
    irgSS_psu_rootGroup_eq_long (hσ := unitaryInvolution_involutive hF) hlneg]
  exact irgSS_longRootHom_inf hl.1 hri

end CFSG.StandardType.RCKRP
