module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGStdPosCore
import CFSG.LocalAnalysis.StandardType.GGStdPosTrans
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusNorm
import CFSG.LocalAnalysis.StandardType.GGStdPosRankCard
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.Walter.Bender1970.S2.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
import CFSG.LieType.TitsSimplicity.Unipotent
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

private theorem ggKGCent_exists_units_ne_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ s : (GaloisField 2 f)ˣ, s ≠ 1 := by
  have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : 1 < Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    omega
  have : Nontrivial (GaloisField 2 f)ˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  exact exists_ne 1

private theorem ggKGCent_le_or_le_centralizer {G : Type*} [Group G] {J M B : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple J) (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hcomm : ∀ b ∈ B, ∀ j ∈ J, b * j * b⁻¹ * j⁻¹ ∈ M) :
    J ≤ M ∨ B ≤ Subgroup.centralizer (J : Set G) := by
  have hN : (M.subgroupOf J).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hJM g.2) a).mp ha⟩
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hJ (M.subgroupOf J)
    with h | h
  · refine Or.inr fun b hb => Walter.mem_centralizer_of_commutator_mem_center hJ.1 fun j hj => ?_
    have hbj : b * j * b⁻¹ * j⁻¹ ∈ J :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hBJ hb) j).mp hj) (inv_mem hj)
    exact Subgroup.mem_map.mpr
      ⟨⟨_, hbj⟩, h (Subgroup.mem_subgroupOf.mpr (hcomm b hb j hj)), rfl⟩
  · refine Or.inl fun j hj => ?_
    have hj' : (⟨j, hj⟩ : J) ∈ M.subgroupOf J := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hj'

private theorem ggKGCent_comm_mem_of_mem_sup {G : Type*} [Group G] {M Y₁ Y₂ : Subgroup G}
    {b : G} (h₁ : Y₁ ≤ Subgroup.normalizer (M : Set G))
    (h₂ : Y₂ ≤ Subgroup.normalizer (M : Set G)) (hb₁ : ∀ y ∈ Y₁, b * y * b⁻¹ * y⁻¹ ∈ M)
    (hb₂ : ∀ y ∈ Y₂, b * y * b⁻¹ * y⁻¹ ∈ M) {y : G} (hy : y ∈ Y₁ ⊔ Y₂) :
    b * y * b⁻¹ * y⁻¹ ∈ M := by
  let A : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (M : Set G) ∧ b * g * b⁻¹ * g⁻¹ ∈ M}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {g g'} hg hg' => by
        refine ⟨mul_mem hg.1 hg'.1, ?_⟩
        have e : b * (g * g') * b⁻¹ * (g * g')⁻¹ =
            b * g * b⁻¹ * g⁻¹ * (g * (b * g' * b⁻¹ * g'⁻¹) * g⁻¹) := by group
        rw [e]
        exact mul_mem hg.2 ((Subgroup.mem_normalizer_iff.mp hg.1 _).mp hg'.2)
      inv_mem' := fun {g} hg => by
        refine ⟨inv_mem hg.1, ?_⟩
        have e : b * g⁻¹ * b⁻¹ * g⁻¹⁻¹ = g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hg.1) _).mp (inv_mem hg.2) }
  have hA : Y₁ ⊔ Y₂ ≤ A :=
    sup_le (fun y hy => ⟨h₁ hy, hb₁ y hy⟩) fun y hy => ⟨h₂ hy, hb₂ y hy⟩
  exact (hA hy).2

private theorem ggKGCent_commutator_le {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hBU : BruhatExtras Δ H) {G : Type*} [Group G]
    (ψ : K →* G) (D : Subgroup G) :
    ⁅(ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ, (ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ⁆ ≤
      (ggKGCentRootSpan Δ ψ D).map ψ := by
  have hTR : ggTorus Δ ≤ Subgroup.normalizer (ggKGCentRootSpan Δ ψ D : Set K) :=
    le_normalizer_iSup₂ fun t ht γ hγ y hy =>
      le_iSup₂_of_le (f := fun γ (_ : γ ∈ ggKGCentRoots Δ ψ D) => Δ.rootGroup γ) γ hγ le_rfl
        ((Subgroup.mem_normalizer_iff.mp
          (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp ht γ) hγ.1) y).mp hy)
  have hTc : ∀ a ∈ ggTorus Δ, ∀ b ∈ ggTorus Δ, a * b = b * a := by
    rw [ggStdPos_ggTorus_eq hct hext hBU]
    exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
      (LieType.TitsSimplicity.iSup_le_centralizer_iSup hext ha) b hb).symm
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (QuasithinUnique.Setup.X6.commutator_le_of_sup_normalizer hTR hTc)

private theorem ggKGCent_conj_rootSpan {K : Type*} [Group K] {Δ : UniversalRootDatum K}
    {nn : Fin Δ.rank → K} {H : Fin Δ.rank → Subgroup K} {F : Type*} [Field F] [Finite F]
    [CharP F 2] {xp : (Fin Δ.rank → ℤ) → F → K}
    {C : (Fin Δ.rank → ℤ) → (Fin Δ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan Δ.isFiniteType Δ.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix Δ.isFiniteType).toCoxeterSystem
      (weylAction Δ.isFiniteType) Δ.roots Δ.rootGroup nn H)
    (hext : SteinbergExtras Δ nn H) (hBU : BruhatExtras Δ H) (hE : ChevalleyExtras Δ F xp C O)
    (hdiv : Δ.divisible = ∅) {s : Fˣ} (hs : s ≠ 1) {G : Type*} [Group G] {ψ : K →* G}
    (hker : ψ.ker ≤ Subgroup.center K) {Bs D : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs)
    (hD : D ≤ Bs) :
    ψ.range ⊓ Subgroup.centralizer (D : Set G) ≤
        Subgroup.normalizer (((ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ : Subgroup G) : Set G) ∧
      ∀ b ∈ Bs, ∀ y ∈ ψ.range ⊓ Subgroup.centralizer (D : Set G),
        b * y * b⁻¹ * y⁻¹ ∈ (ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ := by
  have hK1 : (Subgroup.centralizer (D : Set G)).comap ψ =
      ((Subgroup.centralizer (D : Set G)).comap ψ ⊓ Subgroup.normalizer (ggTorus Δ : Set K)) ⊔
        ggKGCentRootSpan Δ ψ D :=
    ggStdPos_centralizer_eq hct hext hBU (ggStdPos_transitive_of_chevalleyExtras hct hE hdiv) ψ
      hker (D : Set G) fun d hd => hstd d (hD hd)
  have hY : ψ.range ⊓ Subgroup.centralizer (D : Set G) =
      ((Subgroup.centralizer (D : Set G)).comap ψ ⊓
        Subgroup.normalizer (ggTorus Δ : Set K)).map ψ ⊔ (ggKGCentRootSpan Δ ψ D).map ψ := by
    rw [← Subgroup.map_comap_eq, ← Subgroup.map_sup, ← hK1]
  have hNR : (Subgroup.centralizer (D : Set G)).comap ψ ⊓ Subgroup.normalizer (ggTorus Δ : Set K) ≤
      Subgroup.normalizer (ggKGCentRootSpan Δ ψ D : Set K) := by
    refine le_normalizer_iSup₂ fun k hk β hβ y hy => ?_
    obtain ⟨hkC, hkN⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨w, hw⟩ := ggStdPos_exists_actsAs_of_mem_normalizer hct hext hBU hE hdiv hs hkN
    refine le_iSup₂_of_le (f := fun γ (_ : γ ∈ ggKGCentRoots Δ ψ D) => Δ.rootGroup γ)
      (weylAction Δ.isFiniteType w β) ⟨weylAction_mem_roots _ w hβ.1, ?_⟩ le_rfl
      (hw.conj_mem hβ.1 hy)
    rw [← hw β hβ.1]
    rintro _ ⟨z, hz, rfl⟩
    show k * z * k⁻¹ ∈ (Subgroup.centralizer (D : Set G)).comap ψ
    exact mul_mem (mul_mem hkC (hβ.2 hz)) (inv_mem hkC)
  have hY₁ : ((Subgroup.centralizer (D : Set G)).comap ψ ⊓
      Subgroup.normalizer (ggTorus Δ : Set K)).map ψ ≤
        Subgroup.normalizer (((ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ : Subgroup G) : Set G) :=
    (Subgroup.map_mono ((le_inf inf_le_right hNR).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _))).trans (Subgroup.le_normalizer_map ψ)
  have hY₂ : (ggKGCentRootSpan Δ ψ D).map ψ ≤
      Subgroup.normalizer (((ggTorus Δ ⊔ ggKGCentRootSpan Δ ψ D).map ψ : Subgroup G) : Set G) :=
    (Subgroup.map_mono le_sup_right).trans Subgroup.le_normalizer
  refine ⟨hY ▸ sup_le hY₁ hY₂, fun b hb y hy => ?_⟩
  rw [hY] at hy
  refine ggKGCent_comm_mem_of_mem_sup hY₁ hY₂ ?_ ?_ hy
  ·
    rintro _ ⟨k, hk, rfl⟩
    have hkN := (Subgroup.mem_inf.mp hk).2
    obtain ⟨w, hw⟩ := ggStdPos_exists_actsAs_of_mem_normalizer hct hext hBU hE hdiv hs hkN
    obtain ⟨m, hm, hkm⟩ := ggStdPos_exists_conj_eq hct hext hBU hker (hstd b hb) hw
    rw [← ggStdPos_ggTorus_eq hct hext hBU] at hkm
    refine ⟨k * (k⁻¹ * m) * k⁻¹,
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hkN _).mp hkm), ?_⟩
    rw [hm, map_mul, map_mul, map_inv, map_mul, map_inv]
    group
  ·
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨r', hr', hrr⟩ := ggStdPos_conj_mem_map_iSup (A := ggKGCentRoots Δ ψ D) (hstd b hb)
      (fun β hβ => hβ.1) hr
    refine ⟨r' * r⁻¹, Subgroup.mem_sup_right (mul_mem hr' (inv_mem hr)), ?_⟩
    rw [hrr, map_mul, map_inv]

theorem ggKGCent_le_rootSpan
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpJ : p ∣ Nat.card J) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs) :
    J ≤ (ggKGCentRootSpan (ggU tg n f).D ψ D).map ψ := by
  obtain ⟨⟨hp, -, hadm, hrank⟩, ⟨hker, hrange, ht, hpdvd⟩, -, -, -⟩ := hloc
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by
      have := hadm.2.1
      omega
    rw [hf1] at hpdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvd)
  obtain ⟨s, hs⟩ := ggKGCent_exists_units_ne_one hf
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ := ggStdPos_bruhatData hrank ht
  obtain ⟨hN, hcomm⟩ := ggKGCent_conj_rootSpan hct hext hBU hE hdiv hs hker hstd
    (SecFiveL1Odd.le_bstar hcfg)
  have hDJ : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  have hJq : Assembly.IsQuasisimple J := hDJ.2.2.2.2.2.1.2.2
  have hJY : J ≤ ψ.range ⊓ Subgroup.centralizer (D : Set G) := by
    refine le_inf ?_ (hDJ.2.2.2.2.2.1.1.trans inf_le_right)
    rw [hrange]
    exact SecFiveL1Odd.J_le hL hcfg hpJ hX
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    (SecFiveL1Odd.bstar_le_centralizer hcfg).trans
      (SecFiveL1Odd.centralizer_le_normalizer_J ha₀ hcfg)
  rcases ggKGCent_le_or_le_centralizer hJq (hJY.trans hN) hBsJ
      (fun b hb j hj => hcomm b hb j (hJY hj)) with hJM | hBC
  ·
    exact (commutator_self_eq_of_isQuasisimple hJq).ge.trans
      ((Subgroup.commutator_mono hJM hJM).trans (ggKGCent_commutator_le hct hext hBU ψ D))
  ·
    exfalso
    have hBD : B ≤ D := by
      rw [hDJ.2.2.2.2.2.2]
      exact le_inf le_rfl (hcfg.1.1.2.1.1.trans hBC)
    have hle : Nat.card B ≤ Nat.card D := Subgroup.card_le_of_le hBD
    rw [hcfg.1.1.1.2.2.2.2.2.2.1.1.2.1, hDJ.2.2.1] at hle
    have h4 := (ggKGPos_prime_rank_ge_four hcfg).2.2
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    omega

end CFSG.StandardType

end
