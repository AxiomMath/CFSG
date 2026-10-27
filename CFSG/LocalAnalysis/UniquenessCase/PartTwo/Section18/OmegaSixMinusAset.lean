module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusPlane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusRad
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusRadAbelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus)

theorem k_Omega6Minus_aSet_rank :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      2 ≤ n → NatOmegaMinus H ⊤ ⊥ 6 n → ∀ E ∈ E3.aSet (n + 1) H, rk ↥E ≤ 3 * n := by
  intro W _ _ H n hn hN E hE
  classical
  obtain ⟨F, hFfield, hFfinite, b, c, hF, hbc, ε, ψ, hψ⟩ :=
    exists_natCoords_of_natOmegaMinus hN
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨U, hU2, hUs, hfixU⟩ :=
    exists_fixed_singular_plane_of_mem_aSet hn hF hbc ε ψ hψ hE
  have hEab : IsElemAbelian2 E := hE.2.2.1
  let φ : ↥H →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    (StatedOmega (StatedQuadMinus 3 F b c)).subtype.comp ε.toMonoidHom
  let E₁ : Subgroup ↥H := (⊤ : Subgroup ↥E).map (Subgroup.inclusion hE.1)
  let E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := E₁.map φ
  have hφ_apply : ∀ l : ↥H, (φ l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) =
      ((ε l : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := fun _ => rfl
  have hE'Ω : E' ≤ StatedOmega (StatedQuadMinus 3 F b c) := by
    rintro _ ⟨l, -, rfl⟩
    exact (ε l).2
  have hE'2 : ∀ g ∈ E', g * g = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    rw [← map_mul, ← map_one φ]
    congr 1
    rw [← map_mul, ← map_one (Subgroup.inclusion hE.1)]
    congr 1
    apply Subtype.ext
    simpa [pow_two] using hEab.2 e e.2
  have hE'comm : ∀ g ∈ E', ∀ h ∈ E', g * h = h * g := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨e', -, rfl⟩ := Subgroup.mem_map.mp hl'
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEab.1 e e.2 e' e'.2)
  have hfixE' : ∀ g ∈ E', ∀ u ∈ U, gv g u = u := by
    rintro _ ⟨l, hl, rfl⟩ u hu
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    rw [hφ_apply]
    simpa [gv, Subgroup.inclusion] using hfixU (e : MulAut W) e.2 u hu
  obtain ⟨x, -, hxconj⟩ :=
    exists_conj_le_radGrp_of_fixes_singular_plane hbc hE'Ω hE'2 hU2 hUs hfixE'
  let E'' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    E'.map (MulAut.conj x).toMonoidHom
  have hE''rad : E'' ≤ RadGrp b c := by
    rintro _ ⟨g, hg, rfl⟩
    exact hxconj g hg
  have hE''comm : ∀ g ∈ E'', ∀ h ∈ E'', g * h = h * g := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    have hc := hE'comm g hg h hh
    calc (MulAut.conj x).toMonoidHom g * (MulAut.conj x).toMonoidHom h
        = (MulAut.conj x).toMonoidHom (g * h) := (map_mul _ g h).symm
      _ = (MulAut.conj x).toMonoidHom (h * g) := by rw [hc]
      _ = (MulAut.conj x).toMonoidHom h * (MulAut.conj x).toMonoidHom g := map_mul _ h g
  have hcardle : Nat.card ↥E'' ≤ Nat.card F ^ 3 :=
    card_le_of_le_radGrp_of_isMulCommutative_of_irreducible hbc hE''rad hE''comm
  have hφinj : Function.Injective φ := by
    intro a b h
    exact ε.injective (Subtype.ext h)
  have hcard'' : Nat.card ↥E'' = Nat.card ↥E' :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcard' : Nat.card ↥E' = Nat.card ↥E := by
    rw [Subgroup.card_map_of_injective hφinj]
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hE.1)]
    simp
  have hcard : Nat.card ↥E'' = Nat.card ↥E := hcard''.trans hcard'
  have hE2grp : IsPGroup 2 ↥E := hEab.isPGroup
  have hcardE : Nat.card ↥E = 2 ^ rk ↥E := card_eq_two_pow_of_isPGroup hE2grp
  have hF3 : Nat.card F ^ 3 = 2 ^ (3 * n) := by
    rw [hF, ← pow_mul, Nat.mul_comm]
  have hpow : 2 ^ rk ↥E ≤ 2 ^ (3 * n) := by
    rw [← hcardE, ← hcard, ← hF3]
    exact hcardle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
