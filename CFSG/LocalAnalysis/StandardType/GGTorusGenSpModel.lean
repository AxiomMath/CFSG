module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
public import CFSG.GroupTheory.PerfectCentralExtensionUnique
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open TableBSymp

private theorem card_inf_centralizer_le {M : Type} [Group M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ}
    (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) :
    Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ≤ p := by
  obtain ⟨-, hEA, -, -, h5, -⟩ := hP
  have hDE : E ⊓ Subgroup.centralizer (L' : Set M) ≤ E := inf_le_left
  have hcyc : IsCyclic (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    h5 _ (hDE.trans le_sup_left) inf_le_right
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEA hDE))
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg1 : g ^ p = 1 := Subtype.ext (by simpa using hEA.2 g (hDE g.2))
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hg1)

private theorem section_range_eq_top {K : Type} [Field K] {m : ℕ} {L : Type} [Group L]
    {ρ : L →* StatedSp m K} {σ : StatedSp m K →* L}
    (hσ : ∀ g : StatedSp m K, ρ (σ g) = g)
    (hker : ρ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    σ.range = ⊤ := by
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hperf
  have hle : (⊤ : Subgroup L) ≤ σ.range ⊔ Subgroup.center L := by
    intro x _
    have h1 : x * (σ (ρ x))⁻¹ ∈ Subgroup.center L := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    rw [show x = (x * (σ (ρ x))⁻¹) * σ (ρ x) from by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨ρ x, rfl⟩))
  exact CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (Z := Subgroup.center L) le_rfl
    (eq_top_iff.mpr hle)

private theorem exists_field_facts {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ f : ℕ, Nat.card K = 2 ^ f ∧ 1 ≤ f ∧ 2 ≤ f ∧ p ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfcard⟩ := FiniteField.card K 2
  have hKcard : Nat.card K = 2 ^ (f : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hfcard
  have hKne2 : Nat.card K ≠ 2 := fun h => hp.not_dvd_one (by rwa [h] at hpK)
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hf2 : 2 ≤ (f : ℕ) := by
    by_contra h
    have h1 : (f : ℕ) = 1 := by omega
    exact hKne2 (by rw [hKcard, h1]; norm_num)
  have hodd : Odd (Nat.card K - 1) := by
    rw [hKcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact ⟨(f : ℕ), hKcard, f.pos, hf2, by rintro rfl; exact hodd.not_two_dvd_nat hpK⟩

private theorem exists_section_of_position_Sp {K : Type} [Field K] {m : ℕ}
    [Finite K] [CharP K 2] [NeZero m] {p : ℕ} (hm : 2 ≤ m) {M : Type} [Group M] [Finite M]
    {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      θ hE)
    (f : ℕ) (hKcard : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) (hf2 : 2 ≤ f) :
    ∃ σ : StatedSp m K →* L', Function.Injective σ ∧ σ.range = ⊤ ∧
      ∀ g : StatedSp m K,
        ggQuotHom θ (σ g) = LargeEvenProjMk (LargeEvenSpGroup K m) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (StatedSp m K) :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp' (Or.inl (by
      rw [hKcard]
      exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hf2)))
  let π : StatedSp m K →* LargeEvenProj (LargeEvenSpGroup K m) :=
    LargeEvenProjMk (LargeEvenSpGroup K m)
  have hπi : Function.Injective π := AutPSp.proj_injective
  let pe : StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective π ⟨hπi, QuotientGroup.mk'_surjective _⟩
  let ρ : L' →* StatedSp m K := pe.symm.toMonoidHom.comp (ggQuotHom θ)
  have hρker : ρ.ker = Subgroup.center L' :=
    (MonoidHom.ker_comp_of_injective _ _ pe.symm.injective).trans (ker_ggQuotHom θ)
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.CoverAssembly.exists_section_of_cover_and_coprime
      (p := 2) (H := StatedSp m K) (J := LargeEvenProj (LargeEvenSpGroup K m)) (θ := π)
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']
          exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center)
      (fun P _ _ _ η hη hC h2 =>
        CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_two_cover_trivial
          hKcard hf1 hm (fun _ => hf2) P η hη hC h2)
      (fun E' _ _ π' hπ' hcen' hc' =>
        CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime
          (p := 2) E' π' hπ' hcen' hc')
      (E := L') ρ (pe.symm.surjective.comp (ggQuotHom_surjective θ)) (by rw [hρker])
  have hquot : ∀ g : StatedSp m K, ggQuotHom θ (σ g) =
      LargeEvenProjMk (LargeEvenSpGroup K m) g := by
    intro g
    have h2 : pe (ρ (σ g)) = ggQuotHom θ (σ g) := pe.apply_symm_apply _
    rw [hσ] at h2
    exact h2.symm
  have hσi : Function.Injective σ := by
    intro a b hab
    have h := congrArg (ggQuotHom θ) hab
    rw [hquot a, hquot b] at h
    exact hπi h
  exact ⟨σ, hσi, section_range_eq_top hσ (le_of_eq hρker) hpos.1, hquot⟩

private theorem exists_conj_data_of_position {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} [NeZero m] {p : ℕ} {M : Type} [Group M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      θ hE) :
    ∃ g : E →* StatedSp m K,
      ∀ e : E, MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K m) (g e)) =
        ggLAut L' θ ⟨(e : M), hE e.2⟩ := by
  classical
  have hconjR : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _) :=
    mulAut_conj_injective (TableBSymp.center_spProj_eq_bot (K := K) (m := m))
  let r : E → LargeEvenProj (LargeEvenSpGroup K m) :=
    fun e => Classical.choose (TableBSymp.sp_I_subset_inn (hpos.2.2.2.1 e))
  have hr : ∀ e : E, MulAut.conj (r e) = ggLAut L' θ ⟨(e : M), hE e.2⟩ :=
    fun e => Classical.choose_spec (TableBSymp.sp_I_subset_inn (hpos.2.2.2.1 e))
  let pe : StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨AutPSp.proj_injective, QuotientGroup.mk'_surjective _⟩
  let g0 : E → StatedSp m K := fun e => pe.symm (r e)
  have hrmul : ∀ a b : E, r (a * b) = r a * r b := by
    intro a b
    refine hconjR ?_
    rw [map_mul, hr (a * b), hr a, hr b]
    rw [show (⟨((a * b : E) : M), hE (a * b).2⟩ : Subgroup.normalizer (L' : Set M)) =
      ⟨(a : M), hE a.2⟩ * ⟨(b : M), hE b.2⟩ from Subtype.ext rfl, map_mul]
  let g : E →* StatedSp m K := MonoidHom.mk' g0 (by
    intro a b
    rw [show g0 (a * b) = pe.symm (r (a * b)) from rfl, hrmul, map_mul])
  exact ⟨g, fun e => by
    rw [show LargeEvenProjMk (LargeEvenSpGroup K m) (g e) = r e from pe.apply_symm_apply _]
    exact hr e⟩

private theorem induced_hom_central_factor {K : Type} [Field K] {m : ℕ} {M : Type} [Group M]
    {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hL : commutator L' = ⊤) (σ : StatedSp m K →* L')
    (hquot : ∀ g : StatedSp m K, ggQuotHom θ (σ g) =
      LargeEvenProjMk (LargeEvenSpGroup K m) g)
    (g : E →* StatedSp m K)
    (hg : ∀ e : E, MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K m) (g e)) =
      ggLAut L' θ ⟨(e : M), hE e.2⟩) :
    ∀ e : E, (e : M) * ((L'.subtype.comp σ) (g e))⁻¹ ∈
      Subgroup.centralizer (L' : Set M) := by
  intro e
  have hφA : ggLAut L' θ ⟨((σ (g e) : L') : M), Subgroup.le_normalizer (σ (g e)).2⟩ =
      MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K m) (g e)) := by
    rw [ggLAut_of_mem_conj (L := L') θ (σ (g e)) (Subgroup.le_normalizer (σ (g e)).2)]
    simpa [ggQuotHom_apply] using congrArg MulAut.conj (hquot (g e))
  have hgg : ggLAut L' θ ⟨(e : M), hE e.2⟩ *
      (ggLAut L' θ ⟨((σ (g e) : L') : M), Subgroup.le_normalizer (σ (g e)).2⟩)⁻¹ = 1 := by
    rw [hφA, ← hg e, mul_inv_cancel]
  have hnorm : (e : M) * ((L'.subtype.comp σ) (g e))⁻¹ ∈
      Subgroup.normalizer (L' : Set M) :=
    Subgroup.mul_mem _ (hE e.2) (Subgroup.inv_mem _ (Subgroup.le_normalizer (σ (g e)).2))
  have heq : (⟨(e : M) * ((L'.subtype.comp σ) (g e))⁻¹, hnorm⟩ :
      Subgroup.normalizer (L' : Set M)) = ⟨(e : M), hE e.2⟩ *
      ⟨((σ (g e) : L') : M), Subgroup.le_normalizer (σ (g e)).2⟩⁻¹ := Subtype.ext rfl
  have h1 : ggLAut L' θ ⟨(e : M) * ((L'.subtype.comp σ) (g e))⁻¹, hnorm⟩ = 1 := by
    rw [heq, map_mul, map_inv, hgg]
  exact mem_centralizer_of_ggLAut_eq_one (L := L') θ hL h1

private theorem rank_of_inner_action {K : Type} [Field K] [CharP K 2]
    {m : ℕ} [NeZero m] {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M]
    {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {φ₀ : StatedSp m K →* M}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      θ hE)
    (hr : p ^ (m + 1) ≤ Nat.card E) (g : E →* StatedSp m K)
    (hg : ∀ e : E, MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K m) (g e)) =
      ggLAut L' θ ⟨(e : M), hE e.2⟩)
    (hfac : ∀ e : E, (e : M) * (φ₀ (g e))⁻¹ ∈ Subgroup.centralizer (L' : Set M)) :
    IsElemAbelian p g.range ∧ p ^ m ≤ Nat.card g.range := by
  let C : Subgroup M := Subgroup.centralizer (L' : Set M)
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) := AutPSp.proj_injective
  have hconjR : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _) :=
    mulAut_conj_injective (TableBSymp.center_spProj_eq_bot (K := K) (m := m))
  have hĒab : IsElemAbelian p g.range :=
    isElemAbelian_range (fun a b => Subtype.ext (IsElemAbelian.comm hpos.2.1 a.2 b.2))
      (fun a => Subtype.ext (by simpa using hpos.2.1.2 a a.2)) g
  have hker : g.ker = (E ⊓ C).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hge
      exact ⟨e.2, by simpa [hge] using hfac e⟩
    · rintro ⟨-, hc⟩
      have h1 : ggLAut L' θ ⟨(e : M), hE e.2⟩ = 1 :=
        ggLAut_eq_one_of_mem_centralizer (L := L') θ hc
      have h3 : LargeEvenProjMk (LargeEvenSpGroup K m) (g e) = 1 :=
        hconjR (by rw [hg e, h1, map_one])
      exact hπi (by rw [h3, map_one])
  have hkercard : Nat.card g.ker = Nat.card (E ⊓ C : Subgroup M) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hD : Nat.card (E ⊓ C : Subgroup M) ≤ p := card_inf_centralizer_le hpos hp
  refine ⟨hĒab, Nat.le_of_mul_le_mul_right ?_ hp.pos⟩
  calc p ^ m * p = p ^ (m + 1) := by ring
    _ ≤ Nat.card E := hr
    _ = Nat.card g.range * Nat.card (E ⊓ C : Subgroup M) := by
      rw [← hkercard, ← TableB.card_range_mul_card_ker g]
    _ ≤ Nat.card g.range * p := Nat.mul_le_mul_left _ hD

private theorem exists_torus_conj_data {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} [NeZero m] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) {Ē : Subgroup (StatedSp m K)}
    (hĒab : IsElemAbelian p Ē) (hĒcard : p ^ m ≤ Nat.card Ē) :
    ∃ x₀ : StatedSp m K,
      (∀ f : Fin m → Multiplicative (ZMod p), x₀ * spTorusSp hζ f * x₀⁻¹ ∈ Ē) ∧
      ∀ y ∈ Ē, ∃ f : Fin m → Multiplicative (ZMod p),
        x₀ * spTorusSp hζ f * x₀⁻¹ = y := by
  let π : StatedSp m K →* LargeEvenProj (LargeEvenSpGroup K m) :=
    LargeEvenProjMk (LargeEvenSpGroup K m)
  have hπi : Function.Injective π := AutPSp.proj_injective
  let pe : StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective π ⟨hπi, QuotientGroup.mk'_surjective _⟩
  let ĒR : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) := Ē.map π
  have hĒRab : IsElemAbelian p ĒR := TableB.isElemAbelian_map hĒab π
  have hĒRcard : p ^ m ≤ Nat.card ĒR := by
    rwa [← Nat.card_congr (Ē.equivMapOfInjective π hπi).toEquiv]
  obtain ⟨x, hτE, hEτ⟩ := ReflSp.exists_conj_spTorus (K := K) (m := m)
    hp hp2 hζo hζ hĒRab hĒRcard
  let x₀ : StatedSp m K := pe.symm x
  have hxπ : π x₀ = x := pe.apply_symm_apply x
  have hπconj : ∀ f : Fin m → Multiplicative (ZMod p),
      π (x₀ * spTorusSp hζ f * x₀⁻¹) = x * spTorus hζ f * x⁻¹ :=
    fun f => by rw [map_mul, map_mul, map_inv, hxπ]; rfl
  refine ⟨x₀, ?_, ?_⟩
  · intro f
    obtain ⟨y, hy, hπy⟩ := Subgroup.mem_map.mp (hτE f)
    exact (hπi (hπy.trans (hπconj f).symm)) ▸ hy
  · intro y hy
    obtain ⟨f, hf⟩ := hEτ (π y) ⟨y, hy, rfl⟩
    exact ⟨f, hπi (by rw [hπconj f, hf])⟩

private theorem exists_tE_of_torus {K : Type} [Field K] {m p : ℕ} [NeZero p] {ζ : Kˣ}
    {x₀ : StatedSp m K} {E : Type} [Group E] {g : E →* StatedSp m K} (hζ : ζ ^ p = 1)
    (hEτ : ∀ y ∈ g.range, ∃ f : Fin m → Multiplicative (ZMod p),
      x₀ * spTorusSp hζ f * x₀⁻¹ = y) :
    ∃ tE : E → Fin m → Kˣ, (∀ e : E, tE e ^ p = 1) ∧
      ∀ e : E, x₀ * diagSp K m (tE e) * x₀⁻¹ = g e := by
  have hfE : ∀ e : E, ∃ f : Fin m → Multiplicative (ZMod p),
      x₀ * spTorusSp hζ f * x₀⁻¹ = g e :=
    fun e => hEτ (g e) (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
  choose fE hfE using hfE
  let tE : E → Fin m → Kˣ := fun e i => zmodPowHom hζ (fE e i)
  have hdiag : ∀ e : E, diagSp K m (tE e) = spTorusSp hζ (fE e) :=
    fun e => (spTorusSt_eq_diagSp (K := K) (n := m) hζ (fE e)).symm
  have htEp : ∀ e : E, tE e ^ p = 1 := by
    intro e
    funext i
    show (zmodPowHom hζ (fE e i)) ^ p = 1
    rw [zmodPowHom_apply, pow_right_comm, hζ, one_pow]
  exact ⟨tE, htEp, fun e => by rw [hdiag e, hfE e]⟩

private theorem torus_image_mem_E {K : Type} [Field K] {m p : ℕ} {M : Type} [Group M]
    {L' E : Subgroup M} {φ φ₀ : StatedSp m K →* M} {g : E →* StatedSp m K}
    {tE : E → Fin m → Kˣ}
    (hφr : φ.range = L')
    (hfac : ∀ e : E, (e : M) * (φ₀ (g e))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    (hφdt : ∀ e : E, φ (diagSp K m (tE e)) = φ₀ (g e))
    (h6 : ∀ x ∈ E ⊔ L', x ∈ Subgroup.centralizer (E : Set M) → x ^ p = 1 → x ∈ E) :
    ∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E := by
  intro t ht
  have hφtL : φ (diagSp K m t) ∈ L' := by
    rw [← hφr]
    exact MonoidHom.mem_range.mpr ⟨diagSp K m t, rfl⟩
  have hcent : φ (diagSp K m t) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    let eE : E := ⟨e, he⟩
    have hc : (e : M) * (φ (diagSp K m (tE eE)))⁻¹ ∈
        Subgroup.centralizer (L' : Set M) := by simpa [hφdt eE] using hfac eE
    have hc' : Commute ((e : M) * (φ (diagSp K m (tE eE)))⁻¹) (φ (diagSp K m t)) :=
      (Subgroup.mem_centralizer_iff.mp hc _ hφtL).symm
    have hd : Commute (φ (diagSp K m (tE eE))) (φ (diagSp K m t)) :=
      ((Commute.all (tE eE) t).map (diagSp K m)).map φ
    have heq : (e : M) = ((e : M) * (φ (diagSp K m (tE eE)))⁻¹) *
        φ (diagSp K m (tE eE)) := by group
    rw [heq]
    exact (hc'.mul_left hd).eq
  have hpoweq : (φ (diagSp K m t)) ^ p = 1 := by
    rw [← map_pow, ← map_pow, ht, map_one, map_one]
  exact h6 _ (Subgroup.mem_sup_right hφtL) hcent hpoweq

theorem exists_model_of_position_Sp {K : Type} [Field K] {m : ℕ}
    [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hm : 2 ≤ m)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      θ hE)
    (hr : p ^ (m + 1) ≤ Nat.card E) :
    ∃ φ : StatedSp m K →* M, Function.Injective φ ∧ φ.range = L' ∧
      (∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E) ∧
      ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
        e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M) := by
  classical
  have : NeZero m := ⟨by omega⟩
  obtain ⟨f, hKcard, hf1, hf2, hp2⟩ := exists_field_facts hp hpK
  obtain ⟨σ, hσi, hσtop, hquot⟩ :=
    exists_section_of_position_Sp (K := K) (m := m) (f := f) hm hpos hKcard hf1 hf2
  let φ₀ : StatedSp m K →* M := L'.subtype.comp σ
  have hφ₀i : Function.Injective φ₀ := L'.subtype_injective.comp hσi
  have hφ₀r : φ₀.range = L' := by
    rw [show φ₀ = L'.subtype.comp σ from rfl, MonoidHom.range_comp, hσtop,
      Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨g, hg⟩ := exists_conj_data_of_position (K := K) (m := m) (p := p) hpos
  have hfac : ∀ e : E, (e : M) * (φ₀ (g e))⁻¹ ∈
      Subgroup.centralizer (L' : Set M) :=
    induced_hom_central_factor (K := K) (m := m) hpos.1 σ hquot g hg
  have hĒ := rank_of_inner_action (K := K) (m := m) hp hpos hr g hg hfac
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpK
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  obtain ⟨x₀, hτE, hEτ⟩ := exists_torus_conj_data hp hp2 hζ hζo hĒ.1 hĒ.2
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨tE, htEp, htEconj⟩ := exists_tE_of_torus hζ hEτ
  let φ : StatedSp m K →* M := φ₀.comp (MulAut.conj x₀).toMonoidHom
  have hφi : Function.Injective φ := hφ₀i.comp (MulAut.conj x₀).injective
  have hφr : φ.range = L' := by
    change ((L'.subtype.comp σ).comp (MulAut.conj x₀).toMonoidHom).range = L'
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj x₀).surjective,
      Subgroup.map_top, hφ₀r]
  have hφdt : ∀ e : E, φ (diagSp K m (tE e)) = φ₀ (g e) :=
    fun e => by
      change φ₀ (x₀ * diagSp K m (tE e) * x₀⁻¹) = φ₀ (g e)
      rw [htEconj e]
  have hTmem := torus_image_mem_E hφr hfac hφdt hpos.2.2.2.2.2.1
  refine ⟨φ, hφi, hφr, hTmem, ?_⟩
  intro e he
  exact ⟨tE ⟨e, he⟩, htEp ⟨e, he⟩, by
    rw [hφdt ⟨e, he⟩]
    exact hfac ⟨e, he⟩⟩

end CFSG.StandardType
