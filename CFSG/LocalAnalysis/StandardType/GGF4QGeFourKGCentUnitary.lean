module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourUnitaryLifts
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.LiftAutPSU
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.Mathlib.GroupTheory.ConjugationLift
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOmegaMinusTorus
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourL1
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4SharedRefl
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1

public section

namespace CFSG.StandardType.F4KGPosition

open CFSG.LieType.Universal CFSG.StandardType.TableCRes

theorem exists_unitary_lifts_fixed_of_f4_member
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .PSU 6 f X) :
    ∃ ψ : (ggU .PSU 6 f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ ψ.range = X ∧
      ∃ ℓ : ↥Bs →* (ggU .PSU 6 f).K,
        (∀ (b : ↥Bs) (u : (ggU .PSU 6 f).K),
          (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
        ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
        (∀ b : ↥Bs, ℓ b ^ p = 1) ∧ p ^ 3 ≤ Nat.card ℓ.range ∧
        ∀ t ∈ Subgroup.centralizer (Bs : Set G),
          ∀ α : MulAut (ggU .PSU 6 f).K,
            (∀ u, ψ (α u) = t⁻¹ * ψ u * t) → ∀ b : ↥Bs, α (ℓ b) = ℓ b := by
  cases f with
  | zero => omega
  | succ g =>
    obtain ⟨ψ, hker, hrange, ℓ, hℓ, hkernel, hpow, hcard⟩ :=
      exists_unitary_lifts_of_f4_member_holds hcfg hX hf hpq hmark
    obtain ⟨hp, hp2, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
    have hpq' : ¬ p ∣ 2 ^ (g + 1) + 1 :=
      not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
    refine ⟨ψ, hker, hrange, ℓ, hℓ, hkernel, hpow, hcard, ?_⟩
    intro t ht α hα b
    exact ClassicalPosition.mulAut_apply_liftHom_PSU_eq (by decide) ψ hker hp hpq'
      Bs ℓ hℓ hpow ht α hα b

theorem exists_noncyclic_pSubgroup_of_unitary_f4_member
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .PSU 6 f X) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup p S ∧ p ^ 3 ≤ Nat.card S ∧ ¬ IsCyclic S := by
  obtain ⟨ψ, -, hrange, ℓ, hℓ, hkernel, hpow, hcard, -⟩ :=
    exists_unitary_lifts_fixed_of_f4_member hcfg hX hf hpq hmark
  have hker : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (ψ.range : Set G) := by
    simpa only [hrange] using hkernel
  let φ : ℓ.range →* G := ψ.comp ℓ.range.subtype
  have hinj : Function.Injective φ :=
    MonoidHom.injective_comp_range_subtype_of_ker_lift ψ Bs ℓ hℓ hker
  have hcardφ : p ^ 3 ≤ Nat.card φ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hcard
  have hpowφ : ∀ s ∈ φ.range, s ^ p = 1 := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨b, hb⟩ := u.property
    have hu : u ^ p = 1 := by
      apply Subtype.ext
      change (u : (ggU .PSU 6 f).K) ^ p = 1
      rw [← hb]
      exact hpow b
    rw [← map_pow, hu, map_one]
  obtain ⟨hp, -, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  refine ⟨φ.range, ?_, fun s => ⟨1, Subtype.ext (by simpa using hpowφ s s.property)⟩,
    hcardφ, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [← hrange]
    exact ⟨(u : (ggU .PSU 6 f).K), rfl⟩
  · exact TableB.not_isCyclic_of_card hp.one_lt hpowφ
      ((pow_le_pow_right₀ hp.one_le (by decide : 2 ≤ 3)).trans hcardφ)

open CFSG.Assembly CFSG.Open

theorem card_bstar_eq_four_of_omega_source
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hL : GGCentralImage .POmegaMinus 4 f L) : Nat.card Bs = p ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, v, -, hvs, -, hvker, -⟩ :=
    exists_omegaMinus_position_of_f4_member_holds hcfg (Or.inl rfl) hf hpq hL
  have hmap : Nat.card (v.ker.map Bs.subtype) = Nat.card v.ker :=
    Subgroup.card_map_of_injective Bs.subtype_injective
  rw [hvker] at hmap
  have hk : Nat.card v.ker = p := hmap.symm.trans hcfg.1.1.card_bstar_inf_centralizer_L
  have hrange : v.range = ⊤ := by
    apply top_unique
    intro a _
    exact hvs a
  have hr : Nat.card v.range = p ^ 3 := by
    rw [hrange, Subgroup.card_top]
    change Nat.card (Fin 3 → ZMod p) = p ^ 3
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hcard := Subgroup.card_ker_mul_card_range v
  rw [hk, hr] at hcard
  exact hcard.symm.trans (by ring)

theorem centralizer_bstar_le_normalizer_K_unitary
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hL : GGCentralImage .POmegaMinus 4 f L) (hK : GGCentralImage .PSU 6 f K) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hBsCard : Nat.card Bs = p ^ 4 := card_bstar_eq_four_of_omega_source hcfg hf hpq hL
  obtain ⟨ψ, -, -, ℓ, -, hkernel, -, hcard, -⟩ :=
    exists_unitary_lifts_fixed_of_f4_member hcfg (Or.inr rfl) hf hpq hK
  obtain ⟨hp, hp2, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hprod := Subgroup.card_ker_mul_card_range ℓ
  have hmul : Nat.card ℓ.ker * p ^ 3 ≤ p * p ^ 3 := by
    calc
      Nat.card ℓ.ker * p ^ 3 ≤ Nat.card ℓ.ker * Nat.card ℓ.range :=
        Nat.mul_le_mul_left _ hcard
      _ = Nat.card Bs := hprod
      _ = p * p ^ 3 := by rw [hBsCard]; ring
  have hbound : Nat.card ℓ.ker ≤ p := by
    by_contra hn
    exact (not_lt_of_ge hmul)
      (mul_lt_mul_of_pos_right (lt_of_not_ge hn) (pow_pos hp.pos 3))
  have hkercard : Nat.card ℓ.ker =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hkernel, Subgroup.card_map_of_injective Bs.subtype_injective]
  have hcardCK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
    rw [← hkercard]
    exact hbound
  have hEC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    (hcfg.bstar_le_normalizer (Or.inr rfl)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K)
  have hNb : GGNbr p B x D J y K := hcfg.2.2.2
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  have hcomp := isComponentOf_of_isNeighborOf hc.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hc.2.2 hNb)
  obtain ⟨hBmax, hyB, hy1, -, -, -⟩ := hNb.1
  have hS : LargeEvenSStar p B y K :=
    ⟨hBmax, hyB, hy1, hcomp.1, fun P hPle hPp =>
      ggSCNoTV_isCyclic hp2 hc.2.1.2.1 hc.2.1.2.2.2 hcfg.1.2.2.2.1
        hEC hcardCK hPle hPp⟩
  obtain ⟨P, hPK, hPp, -, hPnc⟩ :=
    exists_noncyclic_pSubgroup_of_unitary_f4_member hcfg (Or.inr rfl) hf hpq hK
  have hnc : ∃ P : Subgroup G, P ≤ K ∧ IsPGroup p P ∧ ¬ IsCyclic P :=
    ⟨P, hPK, hPp, hPnc⟩
  have hyBs : y ∈ Bs := hc.2.1.1 hyB
  intro t ht
  apply mem_normalizer_of_sstar hS hnc
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact Subgroup.mem_centralizer_iff.mp ht y hyBs

open CFSG.LieType.RootSystem

theorem exists_shared_short_root_fixed_of_tableBPos
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hposL : GGTableBPosImage p Bs .POmegaMinus 4 f L)
    {ψ : (ggU .PSU 6 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSU 6 f).K) (hrange : ψ.range = K)
    (hposK : GGTableBPos p Bs K .PSU 6 f ψ) {t : G}
    (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    ∃ (w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group)
      (k : Fin (ggU .PSU 6 f).D.rank), k.val < 2 ∧
      t ∈ Subgroup.centralizer
        (((ggRootLevi (ggU .PSU 6 f).D
          (weylAction (ggU .PSU 6 f).D.isFiniteType w (Pi.single k 1))).map ψ) : Set G) := by
  obtain ⟨hp, hp2, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hposL' := hposL
  have hposK' := hposK
  obtain ⟨ψL, hkerL, hrangeL, hTB⟩ := hposL
  obtain ⟨εL, hεL, hlevL, -⟩ := hTB
  obtain ⟨εK, hεK, hlevK, -⟩ := hposK
  obtain ⟨σO, hσO, hMO⟩ : ∃ σ : Fin 3 ≃ Fin (ggU .POmegaMinus 4 f).D.rank,
      (∀ k, (σ k).val = k.val) ∧ ∀ k l,
      (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType) (σ k) (σ l) =
        CoxeterMatrix.B 3 k l := by
    refine ⟨Equiv.refl _, fun k => rfl, fun k l => ?_⟩
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨σU, hσU, hMU⟩ := exists_coxeterMatrix_PSU_six (f := f) (by omega)
  obtain ⟨φL, hφL, hrefL, hL01, hL12, hL02, -⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres le_sup_left εL hεL σO hMO
  obtain ⟨φK, hφK, hrefK, hK01, hK12, hK02, -⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres le_sup_right εK hεK σU hMU
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  obtain ⟨u, v, c, d, huv, hd⟩ := R.exists_shared_refl_ne_two
    (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefL k)) hL01 hL12 hL02
    (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefK k)) hK01 hK12 hK02
  let wL := (u.map fun j => (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
    (σO j)).prod
  let wK := (v.map fun j => (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σU j)).prod
  have hshared : φL (wL * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
      (σO c) * wL⁻¹) =
      φK (wK * (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σU d) * wK⁻¹) := by
    dsimp [wL, wK]
    simpa only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def] using huv
  have hrr :
      ((εL (wL * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
        (σO c) * wL⁻¹) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      ((εK (wK * (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σU d) * wK⁻¹) :
        ↥(ggAutomizer K Bs)) : MulAut ↥Bs) := by
    rw [← hφL, ← hφK, hshared]
  let r : MulAut ↥Bs := εK (wK *
    (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple (σU d) * wK⁻¹)
  have hrK : r ∈ ggAutomizer K Bs := (εK _).property
  have hrL : r ∈ ggAutomizer L Bs := by
    dsimp only [r]
    rw [← hrr]
    exact (εL _).property
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hεK ⟨wK, _, rfl⟩
  have hqL := isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hp hp2 hEl hNT hf
    (Or.inl hposL') hrL hrefl
  have hqK := isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hp hp2 hEl hNT hf
    (Or.inr ⟨ψ, hker, hrange, hposK'⟩) hrK hrefl
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  have hxBs : x ∈ Bs := hcfg.1.1.2.1.1 (hDB hxD)
  have hyBs : y ∈ Bs := hcfg.1.1.2.1.1 hcfg.2.2.2.1.2.1
  have hSYL : ggRankOneIn K Bs r = ggRankOneIn L Bs r :=
    ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyBs hxBs
      hcfg.2.2.2.1.2.2.2.2.1.2.1 hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1
      (hcfg.bstar_le_normalizer (Or.inl rfl)) hrK hrL hqK hqL hrefl.1
      (GGIsReflection.ne_one hp hrefl)
  refine ⟨wK, σU d, ?_, ?_⟩
  · rw [hσU]
    have h2 : d.val ≠ 2 := fun h => hd (Fin.ext h)
    have h3 := d.isLt
    omega
  · rw [← hlevK wK (σU d)]
    change t ∈ Subgroup.centralizer (ggRankOneIn K Bs r : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hSYL] at hz
    exact Subgroup.mem_centralizer_iff.mp htL z (((ggOTwoPrime_le _).trans inf_le_left) hz)

end CFSG.StandardType.F4KGPosition

end
