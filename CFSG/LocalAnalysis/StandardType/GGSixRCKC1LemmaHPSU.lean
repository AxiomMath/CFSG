module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.StandardType CFSG.Open
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits

private theorem rckHPSU_cent_maxHeight
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} [Fact (Nat.Prime 2)]
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {γ₀ : Fin (n / 2) → ℤ}
    (hγ₀ : γ₀ ∈ (rootDatum hF n).roots)
    (hmax : ∀ δ ∈ (rootDatum hF n).roots, ht δ ≤ ht γ₀) :
    ∀ x ∈ (rootDatum hF n).rootGroup γ₀, x ≠ 1 →
      Subgroup.centralizer ({x} : Set (SU (unitaryInvolution F 2 f) n)) ≤
        Subgroup.centralizer (((rootDatum hF n).rootGroup γ₀) :
          Set (SU (unitaryInvolution F 2 f) n)) := by
  intro x hx hx1 k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have hxmat := mat_eq_of_mem_rootGroup_maxHeight hσ hn hγ₀ hmax hx
  have hymat := mat_eq_of_mem_rootGroup_maxHeight hσ hn hγ₀ hmax hy
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := Fin.rev i₀
  have hxmat' : mat (unitaryInvolution F 2 f) n x =
      1 + Matrix.single i₀ j₀ (mat (unitaryInvolution F 2 f) n x i₀ j₀) := by
    simpa [i₀, j₀] using hxmat
  have hymat' : mat (unitaryInvolution F 2 f) n y =
      1 + Matrix.single i₀ j₀ (mat (unitaryInvolution F 2 f) n y i₀ j₀) := by
    simpa [i₀, j₀] using hymat
  have hc₀ : mat (unitaryInvolution F 2 f) n x i₀ j₀ ≠ 0 := by
    intro h0
    apply hx1
    apply mat_injective
    rw [hxmat', h0, Matrix.single_zero, add_zero, map_one]
  have hcomm_single : Commute (mat (unitaryInvolution F 2 f) n k)
      (1 + Matrix.single i₀ j₀ (mat (unitaryInvolution F 2 f) n x i₀ j₀)) := by
    have h1 : mat (unitaryInvolution F 2 f) n k * mat (unitaryInvolution F 2 f) n x =
        mat (unitaryInvolution F 2 f) n x * mat (unitaryInvolution F 2 f) n k := by
      rw [← map_mul, ← map_mul, hk]
    rwa [hxmat'] at h1
  have hcomm : Commute (mat (unitaryInvolution F 2 f) n k)
      (1 + (mat (unitaryInvolution F 2 f) n x i₀ j₀) •
        Matrix.single i₀ j₀ (1 : F)) := by
    rwa [Matrix.smul_single, smul_eq_mul, mul_one]
  have hcommy := commute_one_add_smul_of_ne_zero hc₀ hcomm
    (mat (unitaryInvolution F 2 f) n y i₀ j₀)
  rw [Matrix.smul_single, smul_eq_mul, mul_one, ← hymat'] at hcommy
  exact mat_injective (by rw [map_mul, map_mul]; exact hcommy.eq.symm)

private theorem rckHPSU_cent_of_weylAction {U : Type*} [Group U]
    {D : UniversalRootDatum U} {n : Fin D.rank → U} {H : Fin D.rank → Subgroup U}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {γ₀ β : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots)
    (w : (coxeterMatrix D.isFiniteType).Group)
    (hβ : β = weylAction D.isFiniteType w γ₀)
    (hcent : ∀ x ∈ D.rootGroup γ₀, x ≠ 1 →
      Subgroup.centralizer ({x} : Set U) ≤
        Subgroup.centralizer ((D.rootGroup γ₀ : Set U))) :
    ∀ x ∈ D.rootGroup β, x ≠ 1 →
      Subgroup.centralizer ({x} : Set U) ≤
        Subgroup.centralizer ((D.rootGroup β : Set U)) := by
  intro x hx hx1 k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let nw : U := nrep hct w
  have hact : (D.rootGroup γ₀).map (MulAut.conj nw).toMonoidHom = D.rootGroup β := by
    change (D.rootGroup γ₀).map (MulAut.conj (nrep hct w)).toMonoidHom = D.rootGroup β
    rw [hβ]
    exact actsAs_nrep hct w γ₀ hγ₀
  have hxmap : x ∈ (D.rootGroup γ₀).map (MulAut.conj nw).toMonoidHom := by
    rwa [hact]
  obtain ⟨x₀, hx₀mem, hx₀eq⟩ := Subgroup.mem_map.mp hxmap
  have hx₀1 : x₀ ≠ 1 := by
    rintro rfl
    exact hx1 (hx₀eq ▸ map_one (MulAut.conj nw).toMonoidHom)
  have hx₀eq' : nw * x₀ * nw⁻¹ = x := by
    simpa [MulAut.conj_apply] using hx₀eq
  have hk'x₀ : (nw⁻¹ * k * nw) * x₀ = x₀ * (nw⁻¹ * k * nw) := by
    have h := hk
    rw [← hx₀eq'] at h
    calc (nw⁻¹ * k * nw) * x₀
        = nw⁻¹ * (k * (nw * x₀ * nw⁻¹)) * nw := by group
      _ = nw⁻¹ * ((nw * x₀ * nw⁻¹) * k) * nw := by rw [h]
      _ = x₀ * (nw⁻¹ * k * nw) := by group
  have hcentx₀ := hcent x₀ hx₀mem hx₀1
  have hk' : nw⁻¹ * k * nw ∈ Subgroup.centralizer ({x₀} : Set U) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk'x₀
  have hk'cent := hcentx₀ hk'
  rw [Subgroup.mem_centralizer_iff] at hk'cent
  have hymap : y ∈ (D.rootGroup γ₀).map (MulAut.conj nw).toMonoidHom := by
    rwa [hact]
  obtain ⟨y₀, hy₀mem, hy₀eq⟩ := Subgroup.mem_map.mp hymap
  have hy₀eq' : nw * y₀ * nw⁻¹ = y := by
    simpa [MulAut.conj_apply] using hy₀eq
  have hy₀k := hk'cent y₀ hy₀mem
  rw [← hy₀eq']
  calc (nw * y₀ * nw⁻¹) * k
      = nw * (y₀ * (nw⁻¹ * k * nw)) * nw⁻¹ := by group
    _ = nw * ((nw⁻¹ * k * nw) * y₀) * nw⁻¹ := by rw [hy₀k]
    _ = k * (nw * y₀ * nw⁻¹) := by group

theorem rck_lemmaHC_PSU
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSU m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .PSU m g).D β) :
    RCKLemmaHCent (ggU .PSU m g) β := by
  have e : ggU .PSU m g =
      ⟨SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m,
        Unitary.rootDatum (card_galoisField_two_mul 2 g hg) m⟩ := by
    simp only [ggU, lieUniversal, hg, ↓reduceDIte]
  revert β
  rw [e]
  intro β hβ
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hβ
  have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
    card_galoisField_two_mul 2 g hg
  have hm : 2 ≤ m := by
    by_contra hlt
    exact toStd_ne_zero_of_mem_roots hγ₀ (funext fun i => absurd i.isLt (by omega))
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF m hm ζ hζ
  exact rckHPSU_cent_of_weylAction (D := Unitary.rootDatum hF m) hct hγ₀ w rfl
    (rckHPSU_cent_maxHeight hF hm hγ₀ hmax)

end CFSG.StandardType.RCKC1
