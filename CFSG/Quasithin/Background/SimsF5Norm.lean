module

public import CFSG.Quasithin.Background.SimsF5Mark
public import CFSG.Quasithin.Background.SimsF5Ah
public import CFSG.Quasithin.Background.SimsF5AhFacts
public import CFSG.Quasithin.Background.SimsF5ModelO2
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.SimsF5Ai
public import CFSG.Quasithin.Background.SimsF5Main
public import CFSG.Quasithin.Background.SimsF5Phi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutHalf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Transport

variable {A B : Type} [Group A] [Group B]

theorem nm_oPPrime_map {f : A →* B} (hf : Function.Injective f) (p : ℕ) (L : Subgroup A) :
    oPPrime p (L.map f) = (oPPrime p L).map f := by
  unfold oPPrime
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    exact ⟨x, ⟨hx, k, by rwa [orderOf_injective f hf] at hk⟩, rfl⟩
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rwa [orderOf_injective f hf]⟩

theorem nm_ctr_map {f : A →* B} (hf : Function.Injective f) (L : Subgroup A) :
    ctr (L.map f) = (ctr L).map f := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.2 fun a ha => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hc (f a) ⟨a, ha, rfl⟩
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc a ha]

theorem nm_mem_ctr_oPPrime_map {f : A →* B} (hf : Function.Injective f) {p : ℕ} {L : Subgroup A}
    {y : B} (hy : y ∈ ctr (oPPrime p (L.map f))) : ∃ x ∈ ctr (oPPrime p L), f x = y := by
  rw [nm_oPPrime_map hf, nm_ctr_map hf] at hy
  exact hy

end Transport

theorem nm_GDot_normal : (GDot.subgroupOf M0Dot).Normal :=
  Subgroup.normal_of_index_eq_two index_GDot_subgroupOf_M0Dot

theorem nm_GDot_conj {c g : GL6} (hc : c ∈ M0Dot) (hg : g ∈ M0Dot) :
    c * g * c⁻¹ ∈ GDot ↔ g ∈ GDot := by
  have key : ∀ {c g : GL6}, c ∈ M0Dot → g ∈ M0Dot → g ∈ GDot → c * g * c⁻¹ ∈ GDot := by
    intro c g hc hg hgG
    have := nm_GDot_normal.conj_mem ⟨g, hg⟩ hgG ⟨c, hc⟩
    exact this
  constructor
  · intro h
    have := key (M0Dot.inv_mem hc) (M0Dot.mul_mem (M0Dot.mul_mem hc hg) (M0Dot.inv_mem hc)) h
    simpa [mul_assoc] using this
  · exact key hc hg

theorem nm_card_fix_conj (σ τ : Equiv.Perm (Fin 45)) :
    (Finset.univ.filter fun ℓ : Fin 45 => (σ * τ * σ⁻¹) ℓ = ℓ).card =
      (Finset.univ.filter fun ℓ : Fin 45 => τ ℓ = ℓ).card := by
  refine Finset.card_nbij' (fun ℓ => σ⁻¹ ℓ) (fun ℓ => σ ℓ) ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    rw [Finset.mem_coe, Finset.mem_filter] at hℓ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : σ (τ (σ⁻¹ ℓ)) = ℓ := hℓ.2
    have := congrArg (fun x => σ⁻¹ x) h1
    simpa using this
  · intro ℓ hℓ
    rw [Finset.mem_coe, Finset.mem_filter] at hℓ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    show σ (τ (σ⁻¹ (σ ℓ))) = σ ℓ
    simp [hℓ.2]
  · intro ℓ _
    simp
  · intro ℓ _
    simp

section Iso

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

@[expose] def NmCompat (Θ : E ≃* ↥M0Dot) (Gp M₁ M₂ : Subgroup E) : Prop :=
  (∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ M1Dot ↔ x ∈ M₁) ∧
    (∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ M2Dot ↔ x ∈ M₂) ∧
    (∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp)

theorem nm_compat_conj {Θ : E ≃* ↥M0Dot} (hΘ : NmCompat Θ Gp M₁ M₂) (c : ↥M0Dot)
    (hc : (c : GL6) ∈ M1Dot ⊓ M2Dot) : NmCompat (Θ.trans (MulAut.conj c)) Gp M₁ M₂ := by
  have hval : ∀ x : E, (((Θ.trans (MulAut.conj c)) x : ↥M0Dot) : GL6) =
      (c : GL6) * (Θ x : GL6) * (c : GL6)⁻¹ := fun x => rfl
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hval, ← hΘ.1 x]
    constructor
    · intro h
      have := M1Dot.mul_mem (M1Dot.mul_mem (M1Dot.inv_mem hc.1) h) hc.1
      simpa [mul_assoc] using this
    · intro h
      exact M1Dot.mul_mem (M1Dot.mul_mem hc.1 h) (M1Dot.inv_mem hc.1)
  · rw [hval, ← hΘ.2.1 x]
    constructor
    · intro h
      have := M2Dot.mul_mem (M2Dot.mul_mem (M2Dot.inv_mem hc.2) h) hc.2
      simpa [mul_assoc] using this
    · intro h
      exact M2Dot.mul_mem (M2Dot.mul_mem hc.2 h) (M2Dot.inv_mem hc.2)
  · rw [hval, ← hΘ.2.2 x]
    exact nm_GDot_conj c.2 (Θ x).2


theorem nm_full_of_Gp [Finite E] (hGp : Gp.Normal) {Mi : Subgroup E} {MiDot : Subgroup GL6}
    (hMiDot : MiDot ≤ M0Dot)
    (hnorm : M0Dot ⊓ Subgroup.normalizer ((GDot ⊓ MiDot : Subgroup GL6) : Set GL6) = MiDot)
    (hcard : 2 * Nat.card ↥(GDot ⊓ MiDot) = Nat.card ↥MiDot) {fb : E} (hfb : fb ∈ Mi)
    (hfbG : fb ∉ Gp) {Θ : E ≃* ↥M0Dot}
    (hY : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp)
    (hP : ∀ x : E, x ∈ Gp → (((Θ x : ↥M0Dot) : GL6) ∈ MiDot ↔ x ∈ Mi)) :
    ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ MiDot ↔ x ∈ Mi := by
  have hval : ∀ x y : E, ((Θ (x * y * x⁻¹) : ↥M0Dot) : GL6) =
      (Θ x : GL6) * (Θ y : GL6) * (Θ x : GL6)⁻¹ := fun x y => by simp
  have hfwd : ∀ x : E, x ∈ Mi → ∀ h : GL6, h ∈ GDot ⊓ MiDot →
      (Θ x : GL6) * h * (Θ x : GL6)⁻¹ ∈ GDot ⊓ MiDot := by
    intro x hx h hh
    have hh0 : h ∈ M0Dot := GDot_le_M0Dot hh.1
    set y := Θ.symm ⟨h, hh0⟩ with hy
    have hyv : ((Θ y : ↥M0Dot) : GL6) = h := by rw [hy, MulEquiv.apply_symm_apply]
    have hyG : y ∈ Gp := (hY y).1 (hyv ▸ hh.1)
    have hyM : y ∈ Mi := (hP y hyG).1 (hyv ▸ hh.2)
    have hcG : x * y * x⁻¹ ∈ Gp := hGp.conj_mem y hyG x
    have hcM : x * y * x⁻¹ ∈ Mi := Mi.mul_mem (Mi.mul_mem hx hyM) (Mi.inv_mem hx)
    rw [← hyv, ← hval]
    exact ⟨(hY _).2 hcG, (hP _ hcG).2 hcM⟩
  have hback : ∀ x : E, x ∈ Mi → ((Θ x : ↥M0Dot) : GL6) ∈ MiDot := by
    intro x hx
    rw [← hnorm]
    refine ⟨(Θ x).2, Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hfwd x hx h hh, fun hh => ?_⟩⟩
    have := hfwd x⁻¹ (Mi.inv_mem hx) _ hh
    have hinv : ((Θ x⁻¹ : ↥M0Dot) : GL6) = (Θ x : GL6)⁻¹ := by simp
    rw [hinv] at this
    simpa [mul_assoc] using this
  have hS : Mi.map Θ.toMonoidHom = MiDot.subgroupOf M0Dot := by
    have hle : Mi.map Θ.toMonoidHom ≤ MiDot.subgroupOf M0Dot := by
      rintro _ ⟨x, hx, rfl⟩
      exact hback x hx
    have hGM : (Gp ⊓ Mi).map Θ.toMonoidHom = (GDot ⊓ MiDot).subgroupOf M0Dot := by
      ext g
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨x, ⟨hxG, hxM⟩, rfl⟩
        exact ⟨(hY x).2 hxG, (hP x hxG).2 hxM⟩
      · intro hg
        refine ⟨Θ.symm g, ?_, by simp⟩
        have hg' : ((Θ (Θ.symm g) : ↥M0Dot) : GL6) = (g : GL6) := by simp
        have hG : Θ.symm g ∈ Gp := (hY _).1 (hg'.symm ▸ hg.1)
        exact ⟨hG, (hP _ hG).1 (hg'.symm ▸ hg.2)⟩
    have hcardGM : Nat.card ↥(Gp ⊓ Mi) = Nat.card ↥(GDot ⊓ MiDot) := by
      have h1 : Nat.card ↥((Gp ⊓ Mi).map Θ.toMonoidHom) = Nat.card ↥(Gp ⊓ Mi) :=
        Subgroup.card_map_of_injective Θ.injective
      rw [← h1, hGM]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans GDot_le_M0Dot)).toEquiv
    have hidx : 2 ≤ ((Gp ⊓ Mi).subgroupOf Mi).index := by
      have hne : ((Gp ⊓ Mi).subgroupOf Mi).index ≠ 1 := by
        rw [Ne, Subgroup.index_eq_one]
        intro h
        have : (⟨fb, hfb⟩ : ↥Mi) ∈ (Gp ⊓ Mi).subgroupOf Mi := h ▸ Subgroup.mem_top _
        exact hfbG this.1
      have hpos : ((Gp ⊓ Mi).subgroupOf Mi).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hcardMi : 2 * Nat.card ↥(GDot ⊓ MiDot) ≤ Nat.card ↥Mi := by
      have hmul := Subgroup.card_mul_index ((Gp ⊓ Mi).subgroupOf Mi)
      have hsub : Nat.card ↥((Gp ⊓ Mi).subgroupOf Mi) = Nat.card ↥(Gp ⊓ Mi) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [hsub, hcardGM] at hmul
      rw [← hmul, mul_comm]
      exact Nat.mul_le_mul_left _ hidx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective Θ.injective]
    have : Nat.card ↥(MiDot.subgroupOf M0Dot) = Nat.card ↥MiDot :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMiDot).toEquiv
    rw [this, ← hcard]
    exact hcardMi
  intro x
  constructor
  · intro hx
    have : Θ x ∈ Mi.map Θ.toMonoidHom := by rw [hS]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Θ.injective hyx
    rwa [← this]
  · exact hback x

end Iso



section Main


theorem exists_normIso {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
    {fb : ↥(M₁ ⊓ M₂)} (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    ∃ (Θ : E ≃* ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z ∧ NmCompat Θ Gp M₁ M₂ ∧
      (∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ TDot ↔ x ∈ Tb) ∧
      ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot ∧ ((Θ (zb : E) : ↥M0Dot) : GL6) = zDot := by
  haveI : Finite E := h.f431.amalgam.finite
  have hGp : Gp.Normal := h.f431.amalgam.normal
  have hfbG : (fb : E) ∉ Gp := h.f431.amalgam.native.1
  have hfb2 : (fb : E) * (fb : E) = 1 := h.f431.amalgam.native.2.1
  obtain ⟨Θ₀, hY0, hP10, hP20, hfix0⟩ := exists_markIso h.f431.amalgam
  set Θ₁ : E ≃* ↥M0Dot := Θ₀.trans lamA with hΘ₁
  have hY1 : ∀ x : E, ((Θ₁ x : ↥M0Dot) : GL6) ∈ GDot ↔ x ∈ Gp := fun x =>
    (lamA_mem_GDot _).trans (hY0 x)
  have hC1 : NmCompat Θ₁ Gp M₁ M₂ :=
    ⟨nm_full_of_Gp hGp M1Dot_le_M0Dot M0Dot_inf_normalizer_GDot_inf_M1Dot
        (by rw [card_GDot_inf_M1Dot, card_M1Dot]) fb.2.1 hfbG hY1
        (fun x hx => (lamA_mem_M1Dot _).trans (hP10 x hx)),
      nm_full_of_Gp hGp M2Dot_le_M0Dot M0Dot_inf_normalizer_GDot_inf_M2Dot
        (by rw [card_GDot_inf_M2Dot, card_M2Dot]) fb.2.2 hfbG hY1
        (fun x hx => (lamA_mem_M2Dot _).trans (hP20 x hx)),
      hY1⟩
  have hfix1 : 15 ≤ (Finset.univ.filter fun ℓ : Fin 45 =>
      act45 (Θ₁ (fb : E)) ℓ = ℓ).card := by
    rw [hΘ₁, MulEquiv.trans_apply, act45_lamA]
    exact hfix0
  have hM12 : (M₁ ⊓ M₂).map Θ₁.toMonoidHom = (M1Dot ⊓ M2Dot).subgroupOf M0Dot := by
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hC1.1 x).2 hx.1, (hC1.2.1 x).2 hx.2⟩
    · intro hg
      refine ⟨Θ₁.symm g, ⟨(hC1.1 _).1 ?_, (hC1.2.1 _).1 ?_⟩, by simp⟩
      · simpa using hg.1
      · simpa using hg.2
  have hTb := h.Tb_syl
  have hS1 : CFSG.QuasithinUnique.IsSylowTwoOf (Tb.map Θ₁.toMonoidHom)
      ((M1Dot ⊓ M2Dot).subgroupOf M0Dot) := by
    rw [← hM12]
    refine ⟨Subgroup.map_mono hTb.1, hTb.2.1.map _, ?_⟩
    show ¬ 2 ∣ (Tb.map Θ₁.toMonoidHom).relIndex ((M₁ ⊓ M₂).map Θ₁.toMonoidHom)
    rw [Subgroup.relIndex_map_map_of_injective _ _ Θ₁.injective]
    exact hTb.2.2
  have hS2 : CFSG.QuasithinUnique.IsSylowTwoOf (TDot.subgroupOf M0Dot)
      ((M1Dot ⊓ M2Dot).subgroupOf M0Dot) := by
    have hT := isSylowOf_TDot_M12
    refine ⟨fun x hx => hT.1 hx, ?_, ?_⟩
    · exact hT.2.1.comap_of_injective M0Dot.subtype M0Dot.subtype_injective
    · show ¬ 2 ∣ (TDot.subgroupOf M0Dot).relIndex ((M1Dot ⊓ M2Dot).subgroupOf M0Dot)
      rw [Subgroup.relIndex_subgroupOf (inf_le_left.trans M1Dot_le_M0Dot)]
      exact hT.2.2
  obtain ⟨c, hc, hcT⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hS1 hS2
  have hc' : (c : GL6) ∈ M1Dot ⊓ M2Dot := hc
  set Θ₂ : E ≃* ↥M0Dot := Θ₁.trans (MulAut.conj c) with hΘ₂
  have hC2 : NmCompat Θ₂ Gp M₁ M₂ := nm_compat_conj hC1 c hc'
  have hT2 : ∀ x : E, ((Θ₂ x : ↥M0Dot) : GL6) ∈ TDot ↔ x ∈ Tb := by
    intro x
    have h1 : ((Θ₂ x : ↥M0Dot) : GL6) ∈ TDot ↔ Θ₂ x ∈ TDot.subgroupOf M0Dot :=
      Subgroup.mem_subgroupOf.symm
    have h2 : c⁻¹ * Θ₂ x * c = Θ₁ x := by
      rw [hΘ₂, MulEquiv.trans_apply, MulAut.conj_apply]
      group
    rw [h1, hcT, CFSG.Quasithin.B6.mem_conjSub, h2]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Θ₁.injective hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfix2 : 15 ≤ (Finset.univ.filter fun ℓ : Fin 45 =>
      act45 (Θ₂ (fb : E)) ℓ = ℓ).card := by
    have : act45 (Θ₂ (fb : E)) = act45 c * act45 (Θ₁ (fb : E)) * (act45 c)⁻¹ := by
      rw [hΘ₂, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [this, nm_card_fix_conj]
    exact hfix1
  set a : Ah := lamA.symm (Θ₂ (fb : E)) with ha
  have haT : a ∈ That := by
    rw [← lamA_mem_TDot, ha, MulEquiv.apply_symm_apply]
    exact (hT2 _).2 h.fb_mem
  have haY : a ∉ Yh := by
    rw [← lamA_mem_GDot, ha, MulEquiv.apply_symm_apply]
    intro hG
    exact hfbG ((hC2.2.2 _).1 hG)
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul, ← map_mul, hfb2, map_one, map_one]
  have hafix : 8 ≤ (Finset.univ.filter fun ℓ : Fin 45 =>
      (a : Equiv.Perm (Fin 45)) ℓ = ℓ).card := by
    have : (a : Equiv.Perm (Fin 45)) = act45 (Θ₂ (fb : E)) := by
      rw [← act45_lamA, ha, MulEquiv.apply_symm_apply]
    rw [this]
    omega
  obtain ⟨s, hsT, hsf⟩ := good_of_fixed haT haY ha2 hafix
  set d : ↥M0Dot := lamA s with hd
  have hdT : (d : GL6) ∈ TDot := (lamA_mem_TDot s).2 hsT
  have hd12 : (d⁻¹ : ↥M0Dot) ∈ (M1Dot ⊓ M2Dot).subgroupOf M0Dot := by
    have := TDot_le_M12 hdT
    exact Subgroup.inv_mem _ this
  have hdf : d * lamA fhatA * d⁻¹ = Θ₂ (fb : E) := by
    rw [hd, ← map_mul, ← map_inv, ← map_mul, hsf, ha, MulEquiv.apply_symm_apply]
  set Θ : E ≃* ↥M0Dot := Θ₂.trans (MulAut.conj d⁻¹) with hΘ
  have hC : NmCompat Θ Gp M₁ M₂ := nm_compat_conj hC2 d⁻¹ hd12
  have hΘf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot := by
    have : Θ (fb : E) = lamA fhatA := by
      rw [hΘ, MulEquiv.trans_apply, MulAut.conj_apply, ← hdf]
      group
    rw [this]
    exact lamA_fhatA
  have hΘT : ∀ x : E, ((Θ x : ↥M0Dot) : GL6) ∈ TDot ↔ x ∈ Tb := by
    intro x
    rw [← hT2 x]
    have hval : ((Θ x : ↥M0Dot) : GL6) = (d : GL6)⁻¹ * (Θ₂ x : GL6) * (d : GL6) := by
      simp [hΘ]
    rw [hval]
    constructor
    · intro hx
      have := TDot.mul_mem (TDot.mul_mem hdT hx) (TDot.inv_mem hdT)
      simpa [mul_assoc] using this
    · intro hx
      exact TDot.mul_mem (TDot.mul_mem (TDot.inv_mem hdT) hx) hdT
  set j1 : ↥M₁ →* β.G0 := f1 (c := β) with hj1
  have hf1inj : Function.Injective j1 := fun a b hab => by
    have : β.φ1 a = β.φ1 b := congrArg Subtype.val hab
    exact h.f431.faithful.1 this
  have hz := h.f431.z_mem
  unfold GiOne at hz
  obtain ⟨w, hw, hwz⟩ := nm_mem_ctr_oPPrime_map h.f431.inj hz
  obtain ⟨zb, hzb, hzbw⟩ := nm_mem_ctr_oPPrime_map (A := ↥M₁) (f := j1) hf1inj hw
  have hzbz : ε (β.φ1 zb) = z := by
    rw [← hwz, ← hzbw]
    rfl
  refine ⟨Θ, zb, hzbz, hC, hΘT, hΘf, ?_⟩
  set ψ : ↥M₁ →* GL6 := M0Dot.subtype.comp (Θ.toMonoidHom.comp M₁.subtype) with hψ
  have hψinj : Function.Injective ψ :=
    Subtype.val_injective.comp (Θ.injective.comp Subtype.val_injective)
  have hKψ : ((Gp ⊓ M₁).subgroupOf M₁).map ψ = GDot ⊓ M1Dot := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hC.2.2 _).2 hx.1, (hC.1 _).2 x.2⟩
    · intro hg
      have hg0 : g ∈ M0Dot := GDot_le_M0Dot hg.1
      set y := Θ.symm ⟨g, hg0⟩ with hy
      have hyv : ((Θ y : ↥M0Dot) : GL6) = g := by rw [hy, MulEquiv.apply_symm_apply]
      have hyM : y ∈ M₁ := (hC.1 y).1 (hyv ▸ hg.2)
      have hyG : y ∈ Gp := (hC.2.2 y).1 (hyv ▸ hg.1)
      exact ⟨⟨y, hyM⟩, ⟨hyG, hyM⟩, hyv⟩
  have hmem : ψ zb ∈ ctr (oPPrime 2 (GDot ⊓ M1Dot)) := by
    rw [← hKψ, nm_oPPrime_map hψinj, nm_ctr_map hψinj]
    exact ⟨zb, hzb, rfl⟩
  rcases ctr_oPPrime_GDot_inf_M1Dot hmem with h1 | h1
  · exfalso
    apply h.f431.z_inv.1
    have hE : (zb : E) = 1 := by
      have h1' : ((Θ (zb : E) : ↥M0Dot) : GL6) = 1 := h1
      have : Θ (zb : E) = 1 := Subtype.ext h1'
      exact Θ.injective (this.trans (map_one Θ).symm)
    have hzb1 : zb = 1 := Subtype.ext hE
    have hφ : β.φ1 zb = 1 := by
      rw [hzb1]
      exact β.φ1.map_one
    rw [← hzbz, hφ, map_one]
  · exact h1

end Main

end CFSG.Quasithin.SimsF5
