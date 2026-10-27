module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.TwistedE6.Fixed
public import CFSG.LieType.Steinberg.TwistedE6.Weyl

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.StandardType CFSG.Open
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

@[expose] def rckHTwE6_high : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private abbrev rckHTwE6_f4Datum0 : UniversalRootDatum (Multiplicative (ZMod 2)) where
  rank := Tag.rank .F4
  cartan := Tag.cartan .F4
  isFiniteType := CFSG.LieType.Chevalley.isFiniteType_cartan .F4
  divisible := ∅
  rootGroup := fun _ => ⊥

private def rckHTwE6_longOrbit : Finset (Fin (Tag.rank .F4) → ℤ) :=
  [rckHTwE6_high, ![1, 3, 4, 2], ![1, 2, 4, 2], ![1, 2, 2, 2], ![1, 2, 2, 0], ![1, 1, 2, 2],
   ![1, 1, 2, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 1, 2, 2], ![0, 1, 2, 0], ![0, 1, 0, 0],
   ![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, -2, 0], ![-1, -1, -2, -2], ![-1, -2, -2, -2],
   ![-1, -2, -2, 0], ![-1, -2, -4, -2], ![-1, -3, -4, -2], ![-2, -3, -4, -2], ![0, -1, -2, -2],
   ![0, -1, -2, 0], ![0, -1, 0, 0]].toFinset

theorem rckHTwE6_high_sum : (∑ i : Fin (Tag.rank .F4), rckHTwE6_high i) = 11 := by
  decide +kernel

theorem rckHTwE6_height_le :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) ≤ 11 := by
  decide +kernel

theorem rckHTwE6_height_eleven_eq :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) = 11 → v = rckHTwE6_high := by
  decide +kernel

private theorem rckHTwE6_orbit_closed :
    ∀ v ∈ rckHTwE6_longOrbit, ∀ i : Fin (Tag.rank .F4),
      reflect .F4 i v ∈ rckHTwE6_longOrbit := by decide +kernel

private theorem rckHTwE6_high_mem_orbit : rckHTwE6_high ∈ rckHTwE6_longOrbit := by
  decide +kernel

theorem rckHTwE6_high_mem_rootFinset :
    rckHTwE6_high ∈ rootFinset Tag.F4 := by decide +kernel

private theorem rckHTwE6_high_mem_roots0 :
    rckHTwE6_high ∈ rckHTwE6_f4Datum0.roots :=
  (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).1
    (mem_rootFinset.1 rckHTwE6_high_mem_rootFinset)

private theorem rckHTwE6_eq_high_of_isMaxHeight0
    {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ rckHTwE6_f4Datum0.roots)
    (hmax : ∀ δ ∈ rckHTwE6_f4Datum0.roots, (∑ i, δ i) ≤ ∑ i, γ i) :
    γ = rckHTwE6_high := by
  have hθ : rckHTwE6_high ∈ rckHTwE6_f4Datum0.roots := rckHTwE6_high_mem_roots0
  have h1 : (∑ i, rckHTwE6_high i) ≤ ∑ i, γ i := hmax rckHTwE6_high hθ
  have hγ' : IsRoot .F4 γ :=
    (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hγ
  have h2 : (∑ i, γ i) ≤ 11 := rckHTwE6_height_le γ (mem_rootFinset.2 hγ')
  have hsum : (∑ i, γ i) = 11 := by
    have := rckHTwE6_high_sum
    omega
  exact rckHTwE6_height_eleven_eq γ (mem_rootFinset.2 hγ') hsum

private theorem rckHTwE6_weylAction_mem_orbit (w : GGWeyl rckHTwE6_f4Datum0) :
    weylAction rckHTwE6_f4Datum0.isFiniteType w rckHTwE6_high ∈ rckHTwE6_longOrbit := by
  obtain ⟨ω, rfl⟩ :=
    (coxeterMatrix rckHTwE6_f4Datum0.isFiniteType).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => simpa [CoxeterSystem.wordProd_nil] using rckHTwE6_high_mem_orbit
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple, reflection_apply]
    exact rckHTwE6_orbit_closed _ ih i

private theorem rckHTwE6_longRoot_mem_orbit
    {k : Type*} [Field k] (θ : k →+* k) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : GGLongRoot (twistedDatum k θ) β) : β ∈ rckHTwE6_longOrbit := by
  change GGLongRoot rckHTwE6_f4Datum0 β at hβ
  obtain ⟨w, γ₀, hγ₀, hmax, heq⟩ := hβ
  have hγ₀eq : γ₀ = rckHTwE6_high := rckHTwE6_eq_high_of_isMaxHeight0 hγ₀ hmax
  rw [hγ₀eq] at heq
  rw [heq]
  exact rckHTwE6_weylAction_mem_orbit w

private theorem rckHTwE6_exists_lift_of_mem_orbit :
    ∀ β ∈ rckHTwE6_longOrbit,
      ∃ α, α ∈ rootFinset Tag.E6 ∧ rho α = α ∧ proj α = β := by
  decide +kernel

private theorem rckHTwE6_exists_fixed_proj
    {k : Type*} [Field k] (θ : k →+* k) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : GGLongRoot (twistedDatum k θ) β) :
    ∃ α₀ : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 α₀ ∧ rho α₀ = α₀ ∧ proj α₀ = β := by
  have hmem : β ∈ rckHTwE6_longOrbit := rckHTwE6_longRoot_mem_orbit θ hβ
  obtain ⟨α, hαmem, hαrho, hαproj⟩ := rckHTwE6_exists_lift_of_mem_orbit β hmem
  exact ⟨α, mem_rootFinset.1 hαmem, hαrho, hαproj⟩

private theorem rckHTwE6_mem_centralizer
    {k : Type*} [Field k] (θ : k →+* k) {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hfix : rho α₀ = α₀) {x : fixedGroup k θ} (hx : x ∈ twistedRootGroup k θ β)
    (hx1 : x ≠ 1) {y : fixedGroup k θ}
    (hy : y ∈ Subgroup.centralizer ({x} : Set (fixedGroup k θ))) :
    y ∈ Subgroup.centralizer (twistedRootGroup k θ β : Set (fixedGroup k θ)) := by
  obtain ⟨c₀, -, hx'⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα₀ hp hfix x).1 hx
  have hc₀ : c₀ ≠ 0 := by
    intro h
    apply hx1
    apply Subtype.ext
    change (x : e6Data_valid.minGroup k) = 1
    rw [hx', h, e6Data_valid.xm_zero]
  have hyx : x * y = y * x := Subgroup.mem_centralizer_iff.mp hy x rfl
  have hyx_endo : Commute (e6Data_valid.endo k (y : e6Data_valid.minGroup k))
      (e6Data_valid.endo k (x : e6Data_valid.minGroup k)) := by
    have h := congrArg (e6Data_valid.endo k)
      (show (x : e6Data_valid.minGroup k) * (y : e6Data_valid.minGroup k) =
          (y : e6Data_valid.minGroup k) * (x : e6Data_valid.minGroup k) from
        congrArg (fun w : fixedGroup k θ => (w : e6Data_valid.minGroup k)) hyx)
    have h' : e6Data_valid.endo k (x : e6Data_valid.minGroup k) *
        e6Data_valid.endo k (y : e6Data_valid.minGroup k) =
        e6Data_valid.endo k (y : e6Data_valid.minGroup k) *
        e6Data_valid.endo k (x : e6Data_valid.minGroup k) := by
      simpa only [e6Data_valid.endo_mul] using h
    exact h'.symm
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨cz, -, hz'⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα₀ hp hfix z).1 hz
  have hxN : e6Data_valid.endo k (x : e6Data_valid.minGroup k) =
      1 + c₀ • e6Data.rootOp k α₀ := by
    rw [hx']
    exact e6Data_valid.endo_xm k α₀ c₀
  have hzN : e6Data_valid.endo k (z : e6Data_valid.minGroup k) =
      1 + cz • e6Data.rootOp k α₀ := by
    rw [hz']
    exact e6Data_valid.endo_xm k α₀ cz
  have hcomm : Commute (e6Data_valid.endo k (y : e6Data_valid.minGroup k))
      (1 + c₀ • e6Data.rootOp k α₀) := by
    rw [← hxN]
    exact hyx_endo
  have hz_comm := commute_one_add_smul_of_ne_zero hc₀ hcomm cz
  apply Subtype.ext
  change (z : e6Data_valid.minGroup k) * (y : e6Data_valid.minGroup k) =
      (y : e6Data_valid.minGroup k) * (z : e6Data_valid.minGroup k)
  apply e6Data_valid.endo_injective
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, hzN]
  exact hz_comm.eq.symm

theorem rck_lemmaHC_twistedE6
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .twistedE6 m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .twistedE6 m g).D β) :
    RCKLemmaHCent (ggU .twistedE6 m g) β := by
  change RCKLemmaHCent ⟨twistedE6Group 2 g, twistedE6Datum 2 g⟩ β
  have hβ' : GGLongRoot (twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g)) β := hβ
  obtain ⟨α₀, hα₀, hfix, hp⟩ := rckHTwE6_exists_fixed_proj (frobQ 2 g) hβ'
  intro x hx hx1 y hy
  exact rckHTwE6_mem_centralizer (frobQ 2 g) hα₀ hp hfix hx hx1 hy

end CFSG.StandardType.RCKC1