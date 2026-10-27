module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoT
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Coords
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4CubeScalar
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
public import CFSG.Certificates.Kernel.U62PairGrp
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3600
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer CFSG.StandardType
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (centralizer_T46)

theorem rhoTInner_rho_of_mem
    {G : Type} [Group G] {L : Subgroup G}
    {e : (L ⧸ center L) ≃* T46} {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)}
    (hρ : RhoTSpec e ρ) {g : G} (hg : g ∈ L) :
    ρ ⟨g, le_normalizer hg⟩ = (e (QuotientGroup.mk ⟨g, hg⟩) : Equiv.Perm (Fin 693)) := by
  set y : normalizer (L : Set G) := ⟨g, le_normalizer hg⟩ with hy
  set t : Equiv.Perm (Fin 693) := (e (QuotientGroup.mk ⟨g, hg⟩) : Equiv.Perm (Fin 693)) with ht
  have hcent : t⁻¹ * ρ y ∈ centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [mem_centralizer_iff]
    intro u hu
    obtain ⟨q, hq⟩ := e.surjective ⟨u, hu⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl : (y : G) * l * (y : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hg l.2) (L.inv_mem hg)
    have hc := hρ.conj y l hl
    have hu' : (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) = u := congrArg Subtype.val hq
    have hconj : (e (QuotientGroup.mk (⟨_, hl⟩ : L)) : Equiv.Perm (Fin 693)) = t * u * t⁻¹ := by
      have h1 : (⟨_, hl⟩ : L) = ⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ := Subtype.ext rfl
      rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
        map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu']
    rw [hu', hconj] at hc
    calc u * (t⁻¹ * ρ y) = t⁻¹ * (t * u * t⁻¹) * ρ y := by group
      _ = t⁻¹ * (ρ y * u * (ρ y)⁻¹) * ρ y := by rw [hc]
      _ = t⁻¹ * ρ y * u := by group
  rw [centralizer_T46] at hcent
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 hcent)).symm

theorem rhoTInner_conj_apply {G : Type} [Group G] {L Bs : Subgroup G}
    (hBs : Bs ≤ normalizer (L : Set G)) (ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693))
    {g : G} (hg : g ∈ L) {b c : G} (hb : b ∈ Bs) (hc : c ∈ Bs) (hcb : c = g * b * g⁻¹) :
    ρ ⟨c, hBs hc⟩ = ρ ⟨g, le_normalizer hg⟩ * ρ ⟨b, hBs hb⟩ * (ρ ⟨g, le_normalizer hg⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simp [hcb])

theorem rhoTInner_exists_conj_of_mem_automizer
    {G : Type} [Group G]
    {L Bs : Subgroup G} (hBs : Bs ≤ normalizer (L : Set G)) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {φ : MulAut Bs}
    (hφ : φ ∈ ggAutomizer L Bs) :
    ∃ q ∈ T46, ∀ b : Bs, q * ρ (inclusion hBs b) * q⁻¹ = ρ (inclusion hBs (φ b)) := by
  let S : Subgroup (MulAut Bs) :=
    { carrier := {ψ | ∃ q ∈ T46, ∀ b : Bs,
        q * ρ (inclusion hBs b) * q⁻¹ = ρ (inclusion hBs (ψ b))}
      one_mem' := ⟨1, T46.one_mem, fun b => by simp⟩
      mul_mem' := by
        rintro ψ χ ⟨q₁, hq₁, h₁⟩ ⟨q₂, hq₂, h₂⟩
        refine ⟨q₁ * q₂, T46.mul_mem hq₁ hq₂, fun b => ?_⟩
        rw [MulAut.mul_apply, ← h₁ (χ b), ← h₂ b]
        group
      inv_mem' := by
        rintro ψ ⟨q, hq, hqc⟩
        refine ⟨q⁻¹, T46.inv_mem hq, fun b => ?_⟩
        have h1 := hqc (ψ⁻¹ b)
        rw [MulAut.apply_inv_self] at h1
        rw [← h1]
        group }
  have hle : ggAutomizer L Bs ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro ψ ⟨g, hgL, -, hψ⟩
    refine ⟨ρ ⟨g, le_normalizer hgL⟩, ?_, fun b => ?_⟩
    · rw [rhoTInner_rho_of_mem hρ hgL]
      exact (e (QuotientGroup.mk ⟨g, hgL⟩)).2
    · exact (rhoTInner_conj_apply hBs ρ hgL b.2 (ψ b).2 (hψ b)).symm
  exact hle hφ

theorem rhoTInner_kappa_apply {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7}
    (hW : WeylCoords Bs A x κ m) {φ : MulAut Bs} (hφ : φ ∈ A)
    (hfix : φ ⟨x, hW.x_mem⟩ = ⟨x, hW.x_mem⟩) (b : Bs) : κ m (φ b) = κ m b := by
  obtain ⟨σ, hσ⟩ := hW.perm φ hφ
  have hx := congrArg (κ m) hfix
  rw [hσ, hW.x_coord, hW.x_coord] at hx
  have hm : σ.symm m = m := by
    by_contra hne
    rw [if_neg hne, if_pos rfl] at hx
    exact one_ne_ω3 hx.symm
  rw [hσ, hm]

theorem rhoTInner_pow_three_of_piSU_pow
    {a : SU0} (h : piSU a ^ 3 = 1) : a ^ 3 = 1 := by
  have h1 : piSU (a ^ 3) = 1 := by rw [map_pow, h]
  obtain ⟨c, -, hc⟩ := CFSG.KC.U62P.Snd.ker_scalar h1
  have hdet : ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
    have h2 := congrArg Units.val (mem_SU0.mp a.2).1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  have hcoe : (((a ^ 3 : SU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 := by simp
  have hs3 : ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 = Matrix.scalar (Fin 6) c := by
    rw [← hcoe, hc, Matrix.smul_one_eq_diagonal]
    rfl
  have hc1 := eq_one_of_det_eq_one_of_pow_three_eq_scalar hdet hs3
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1, one_smul]
  rfl

end CFSG.GGQ2Prime
