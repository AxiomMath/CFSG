module

public import CFSG.RankThree.PartOne.KE.CoreInner
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms

theorem e8_core_le_range_conj (K : Type) [Field K] [Finite K] (M : Type) [Field M] [Algebra K M]
    {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    {x : adjointGroup .E8 K}
    (hq : CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ : Subgroup (adjointGroup .E8 K)))
    (i : Fin Tag.E8.rank) (A : GL (Fin 2) M) (h : ModGL .E8 M)
    (hU : ∀ Y : SL2 K, h * simpleRootSL2 .E8 M i (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ ∈
          (adjointGroup .E8 K).map (baseChangeGL (algebraMap K M)))
    (hmem : ∀ (u : adjointGroup .E8 K) (Y : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL .E8 K) =
        h * simpleRootSL2 .E8 M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ →
        u ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
            Subgroup (adjointGroup .E8 K))) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .E8 K))} :
        Set (MulAut (adjointGroup .E8 K)))) ≤
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
  refine core_le_range_conj_of_quasisimple hp center_adjointGroup_eq_bot hB hq fun η hη => ?_
  let Z : Subgroup (MulAut (adjointGroup .E8 K)) :=
    { carrier := {η | ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
          Subgroup (adjointGroup .E8 K)), η d = d}
      mul_mem' := fun {a b} ha hb d hd => by
        rw [MulAut.mul_apply, hb d hd, ha d hd]
      one_mem' := fun d _ => rfl
      inv_mem' := fun {a} ha d hd => by
        have := ha d hd
        calc a⁻¹ d = a⁻¹ (a d) := by rw [this]
          _ = d := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
  have hη' : η ∈ Z := hη
  have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup .E8 K) (Y : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL .E8 K) =
        h * simpleRootSL2 .E8 M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ → η' u = u :=
    fun η' hη'Z u Y hu => hη'Z u (hmem u Y hu)
  exact (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E8
    (Or.inr (Or.inr rfl)) K M i A h hU Z hZ).2.2.2 rfl η hη'

theorem conjGL_one {M : Type*} [Field M] (Z : SL2 M) : conjGL (1 : GL (Fin 2) M) Z = Z :=
  Subtype.ext (by simp [conjGL])

theorem e8_core_le_range_conj_of_embedding (K : Type) [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    {x : adjointGroup .E8 K} (c : adjointGroup .E8 K) (g0 : ModGL .E8 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L)
    (hψinj : Function.Injective ψ)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .E8 L)} (hPq : CFSG.IsQuasisimple Pt) (hcomm : ⁅ψ.range, ψ.range⁆ = Pt)
    (i : Fin Tag.E8.rank) (h₀ : ModGL .E8 L)
    (hh₀ : ∀ Y : SL2 K, h₀ * simpleRootSL2 .E8 L i
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .E8 K))} :
        Set (MulAut (adjointGroup .E8 K)))) ≤
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set h'' : ModGL .E8 L := (adjEmb .E8 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ : Subgroup (adjointGroup .E8 K)),
        adjEmb .E8 K L y = h'' * simpleRootSL2 .E8 L i
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    rw [← h2] at hmem
    obtain ⟨y', hy', hy'ψ⟩ := hmem
    refine ⟨(y' : adjointGroup .E8 K), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hy', rfl⟩
    · have h3 := hψ y'
      rw [hy'ψ] at h3
      have h4 : adjEmb .E8 K L (c * (y' : adjointGroup .E8 K) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 .E8 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc adjEmb .E8 K L (y' : adjointGroup .E8 K)
          = (adjEmb .E8 K L c)⁻¹ * (adjEmb .E8 K L c * adjEmb .E8 K L (y' : adjointGroup .E8 K) *
              (adjEmb .E8 K L c)⁻¹) * adjEmb .E8 K L c := by group
        _ = _ := by rw [h4]; group
  refine e8_core_le_range_conj K L hp hB hq i 1 h'' (fun Y => ?_) (fun u Y hu => ?_)
  · obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one, ← hy]
    exact ⟨(y : ModGL .E8 K), y.2, rfl⟩
  · obtain ⟨y, hyD, hy⟩ := hKey Y
    rw [conjGL_one, ← hy] at hu
    have hu' : adjEmb .E8 K L u = adjEmb .E8 K L y := by rw [adjEmb_apply, hu]
    rw [adjEmb_injective hu']
    exact hyD

end CFSG.RankThree.PartOne.KE
