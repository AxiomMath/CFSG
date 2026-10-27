module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Quasithin.Background.SmithB45L2Field
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin.SmithD37

open BenderSuzuki.MatrixGroups CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

section CharTwo

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem nonempty_sl2_mulEquiv_pgl2 :
    Nonempty (SL(2, K) ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  have hcard : Nat.card (PSL2MatrixGroup K) = Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
    rw [Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).toEquiv,
      CFSG.GorensteinWalter.sl2_card_formula, CFSG.BenderSuzuki.External.huppertXI13_card_pgl2]
  exact ⟨CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm.trans (MulEquiv.ofBijective _
    ((Nat.bijective_iff_injective_and_card _).2
      ⟨CFSG.Glauberman.Dickson.h826_pslToPGL_injective, hcard⟩))⟩

theorem nonempty_sl2_mulEquiv_alt5 (hK : Nat.card K = 4) :
    Nonempty (SL(2, K) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K (Or.inl hK)
  exact ⟨CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 2 K).trans e)⟩

end CharTwo

theorem two_dvd_of_two_pow_sq_modEq {e : ℕ} (h : (2 ^ e) ^ 2 ≡ 1 [MOD 5]) : 2 ∣ e := by
  by_contra hodd
  obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
  have h1 : (2 ^ (2 * k + 1)) ^ 2 = 4 * 16 ^ k := by
    rw [← pow_mul, show (2 * k + 1) * 2 = 2 + 4 * k by ring, pow_add, pow_mul]
    norm_num
  have h16 : 16 ^ k ≡ 1 [MOD 5] := by simpa using (show 16 ≡ 1 [MOD 5] by decide).pow k
  have h2 := (Nat.ModEq.mul_left 4 h16).symm.trans (h1 ▸ h)
  exact absurd h2 (by decide)

theorem exists_sl2_mulEquiv {F : Type} [Field F] [Finite F]
    {e : ℕ} (hF : Nat.card F = 2 ^ e) (he : e ≠ 0) (H : Subgroup (PSL2MatrixGroup F))
    [IsSimpleGroup H] (hnc : ¬ ∀ a b : H, a * b = b * a) :
    ∃ m, m ≠ 0 ∧ m ∣ e ∧ Nonempty (SL(2, GaloisField 2 m) ≃* H) := by
  have hsolv : ¬ Group.IsSolvable H := fun h => hnc (IsSimpleGroup.comm_iff_isSolvable.mpr h)
  have hm0 : ∀ m, m ∣ e → m ≠ 0 := fun m hm h0 => he (zero_dvd_iff.mp (h0 ▸ hm))
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF H with
    ⟨-, -, -, hel⟩ | ⟨-, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ |
      ⟨h5, ⟨eA5⟩⟩ | ⟨m, -, hm1, -, -, -, E, -, hE, hEel, hEcard, -⟩ | ⟨m, hmf, ⟨eL⟩⟩ |
      ⟨m, hmf, ⟨eG⟩⟩
  · exact absurd (fun a b => hel.toIsMulCommutative.is_comm.comm a b) hnc
  · exact absurd (fun a b => hcyc.isMulCommutative.is_comm.comm a b) hnc
  · have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective)
      hsolv
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := eA4.toMonoidHom) eA4.injective)
      hsolv
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := eS4.toMonoidHom) eS4.injective)
      hsolv
  · have h2 : 2 ∣ e := two_dvd_of_two_pow_sq_modEq (h5.resolve_left (by norm_num))
    obtain ⟨e5⟩ := nonempty_sl2_mulEquiv_alt5 (K := GaloisField 2 2)
      (by rw [GaloisField.card 2 2 two_ne_zero]; norm_num)
    exact ⟨2, two_ne_zero, h2, ⟨e5.trans eA5.symm⟩⟩
  · exfalso
    have := hE
    have hEne : E ≠ ⊥ := by
      intro h0
      have h1 : Nat.card E = 1 := by rw [h0]; exact Subgroup.card_bot
      have := Nat.one_lt_two_pow (n := m) (by omega)
      omega
    have hEtop : E = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal E).resolve_left hEne
    refine hnc fun a b => ?_
    have ha : a ∈ E := hEtop ▸ Subgroup.mem_top a
    have hb : b ∈ E := hEtop ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · exact ⟨m, hm0 m hmf, hmf, ⟨CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm.trans eL.symm⟩⟩
  · have hmf' : m ∣ e := (dvd_mul_left m 2).trans hmf
    obtain ⟨eP⟩ := nonempty_sl2_mulEquiv_pgl2 (K := GaloisField 2 m)
    exact ⟨m, hm0 m hmf', hmf', ⟨eP.trans eG.symm⟩⟩

section Linear

variable {F : Type} [Field F]

theorem not_forall_mul_comm (H : Subgroup (GL (Fin 2) F))
    (hirr : ∀ S : AddSubgroup (Fin 2 → F), (∀ h ∈ H, ∀ v ∈ S,
      ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ h ∈ H, ∀ v,
      φ (((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v) :
    ¬ ∀ a b : H, a * b = b * a := by
  intro hc
  have hsc : ∀ h ∈ H, ∃ c : F, ∀ v,
      ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c • v := by
    intro h hh
    refine hend (Matrix.mulVecLin ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom
      fun h' hh' v => ?_
    have hm := congrArg (fun x : H => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (hc ⟨h, hh⟩ ⟨h', hh'⟩)
    simp only [Subgroup.coe_mul, Units.val_mul] at hm
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hm]
  let S : AddSubgroup (Fin 2 → F) := (Submodule.span F {Pi.single 0 1}).toAddSubgroup
  rcases hirr S (fun h hh v hv => by
      obtain ⟨c, hc⟩ := hsc h hh
      rw [hc]
      exact (Submodule.span F {Pi.single 0 1}).smul_mem c hv) with h0 | h1
  · have h : (Pi.single 0 1 : Fin 2 → F) ∈ S := Submodule.subset_span rfl
    rw [h0, AddSubgroup.mem_bot] at h
    simpa using congrFun h 0
  · have h : (Pi.single 1 1 : Fin 2 → F) ∈ S := h1 ▸ AddSubgroup.mem_top _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    simpa using congrFun hc 1

theorem le_statedSL {n : ℕ} (H : Subgroup (GL (Fin n) F)) [IsSimpleGroup H]
    (hnc : ¬ ∀ a b : H, a * b = b * a) : H ≤ StatedSL n F := by
  let d : H →* Fˣ := Matrix.GeneralLinearGroup.det.comp H.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.ker with h | h
  · exact absurd (fun a b => d.ker_eq_bot_iff.mp h (by rw [map_mul, map_mul, mul_comm])) hnc
  · intro x hx
    apply Subgroup.subset_closure
    have hk : (⟨x, hx⟩ : H) ∈ d.ker := h ▸ Subgroup.mem_top _
    have := congrArg Units.val (MonoidHom.mem_ker.mp hk)
    simpa [d] using this

end Linear

section Module

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Module (ZMod 2) F]

@[expose] noncomputable def binaryNatRep (H : Subgroup (GL (Fin 2) F)) :
    Representation (ZMod 2) H (Fin 2 → F) where
  toFun h := AddMonoidHom.toZModLinearMap 2
    (Matrix.mulVecLin ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom
  map_one' := by
    ext v i
    simp
  map_mul' g h := by
    ext v i
    simp

theorem eq_of_mulEquiv_sl2 [Finite F] {K : Type} [Field K] [Fintype K] [CharP K 2] {e m : ℕ}
    (hF : Nat.card F = 2 ^ e) (hK : Fintype.card K = 2 ^ m) (hm : 1 ≤ m) (hme : m ∣ e)
    (H : Subgroup (GL (Fin 2) F)) (θ : SL(2, K) ≃* H) (hH : H ≠ ⊥)
    (hirr : ∀ S : AddSubgroup (Fin 2 → F), (∀ h ∈ H, ∀ v ∈ S,
      ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ h ∈ H, ∀ v,
      φ (((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v) :
    e = m := by
  classical
  let ρ : Representation (ZMod 2) SL(2, K) (Fin 2 → F) := (binaryNatRep H).comp θ.toMonoidHom
  have hρ : ∀ g v, ρ g v = ((θ g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v :=
    fun _ _ => rfl
  have hsurj : ∀ h ∈ H, ∃ g, (θ g : GL (Fin 2) F) = h := fun h hh =>
    ⟨θ.symm ⟨h, hh⟩, by simp⟩
  have hirrρ : ρ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
    refine ⟨inferInstance, fun U hU => ?_⟩
    rcases hirr U.toAddSubgroup (fun h hh v hv => by
        obtain ⟨g, rfl⟩ := hsurj h hh
        exact hU g v hv) with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have hv' : v ∈ U.toAddSubgroup := hv
      rw [h, AddSubgroup.mem_bot] at hv'
      exact (Submodule.mem_bot _).mpr hv'
    · exact Or.inr (Submodule.toAddSubgroup_eq_top.mp h)
  have : Fact ρ.IsIrreducible := ⟨hirrρ⟩
  have hnt : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
    refine ⟨θ.symm a, fun h1 => ha ?_⟩
    have hv : ∀ v, ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := fun v => by
      have := LinearMap.congr_fun h1 v
      rwa [hρ, MulEquiv.apply_symm_apply, Module.End.one_apply] at this
    have hM : ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
      Matrix.ext_of_mulVec_single fun i => by rw [hv, Matrix.one_mulVec]
    exact Subtype.ext (Units.ext hM)
  have hcomm : ∀ ψ : EndRing ρ, ∀ g v, ψ (ρ g v) = ρ g (ψ v) := fun ψ g v =>
    ψ.map_smul (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) v
  have hscal : ∀ ψ : EndRing ρ, ∃ c : F, ∀ v, ψ v = c • v := fun ψ =>
    hend ψ.toAddMonoidHom fun h hh v => by
      obtain ⟨g, rfl⟩ := hsurj h hh
      exact hcomm ψ g v
  have hlift : ∀ c : F, ∃ ψ : EndRing ρ, ∀ v, ψ v = c • v := fun c => by
    obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ (AddMonoidHom.toZModLinearMap 2
      (DistribSMul.toAddMonoidHom (Fin 2 → F) c))).mpr fun g v => by
        simp [hρ, Matrix.mulVec_smul]
    exact ⟨ψ, fun v => congrFun hψ v⟩
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have he₀ : ∀ c c' : F, c • (Pi.single 0 1 : Fin 2 → F) = c' • Pi.single 0 1 → c = c' :=
    fun c c' h => by simpa using congrFun h 0
  have hcard : Nat.card (EndRing ρ) = Nat.card F := by
    apply le_antisymm
    · refine Nat.card_le_card_of_injective (fun ψ => (hscal ψ).choose) fun ψ ψ' h => ?_
      refine LinearMap.ext fun v => ?_
      rw [(hscal ψ).choose_spec v, (hscal ψ').choose_spec v]
      exact congrArg (· • v) h
    · refine Nat.card_le_card_of_injective (fun c => (hlift c).choose) fun c c' h => he₀ c c' ?_
      rw [← (hlift c).choose_spec, ← (hlift c').choose_spec]
      exact congrArg (fun ψ : EndRing ρ => ψ (Pi.single 0 1)) h
  have hD : Nat.card (EndRing ρ) = 2 ^ e := hcard.trans hF
  have : Module.Finite (EndRing ρ) (Fin 2 → F) := Module.Finite.of_finite
  have hdim : Module.finrank (EndRing ρ) (Fin 2 → F) = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := Fin 2 → F)
    rw [Nat.card_fun, Nat.card_fin, hcard] at h1
    exact (Nat.pow_right_injective Finite.one_lt_card h1).symm
  exact CFSG.Quasithin.B45L2.eq_of_finrank_eq_two hm hK ρ hnt hD hdim hme

end Module

theorem eq_statedSL_of_dim_two {F : Type} [Field F] [Fintype F]
    [CharP F 2] (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) (hA : A38Types ↥H)
    (hirr : ∀ S : AddSubgroup (Fin 2 → F), (∀ h ∈ H, ∀ v ∈ S,
      ((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ h ∈ H, ∀ v,
      φ (((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v) :
    H = CFSG.Assembly.LowTwoRank.StatedSL 2 F := by
  classical
  have : IsSimpleGroup H := CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA
  have hnc := not_forall_mul_comm H hirr hend
  have hle := le_statedSL H hnc
  obtain ⟨e, -, hFe⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (e : ℕ) := Nat.card_eq_fintype_card.trans hFe
  let χ : StatedSL 2 F ≃* PSL2MatrixGroup F :=
    (specialLinearGroupEquivStatedSL 2 F).symm.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm
  let H' : Subgroup (PSL2MatrixGroup F) := (H.subgroupOf (StatedSL 2 F)).map χ.toMonoidHom
  let eH : H ≃* H' :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans (Subgroup.equivMapOfInjective _ _ χ.injective)
  have : IsSimpleGroup H' := eH.symm.isSimpleGroup
  have hnc' : ¬ ∀ a b : H', a * b = b * a := fun h =>
    hnc fun a b => eH.injective (by rw [map_mul, map_mul, h])
  obtain ⟨m, hm0, hme, ⟨θ⟩⟩ := exists_sl2_mulEquiv hF e.ne_zero H' hnc'
  let : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let : Module (ZMod 2) F := (ZMod.algebra F 2).toModule
  have hK : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm0]
  have hH : H ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot H).mp inferInstance
  have hem : (e : ℕ) = m := eq_of_mulEquiv_sl2 hF hK (Nat.one_le_iff_ne_zero.mpr hm0) hme H
    (θ.trans eH.symm) hH hirr hend
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
    ← Nat.card_congr (θ.trans eH.symm).toEquiv, CFSG.GorensteinWalter.sl2_card_formula,
    CFSG.GorensteinWalter.sl2_card_formula, GaloisField.card 2 m hm0, hF, hem]

end CFSG.Quasithin.SmithD37
