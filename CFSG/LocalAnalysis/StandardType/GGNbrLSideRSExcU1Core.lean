module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

theorem ggNbrLSideRSExc_transport_of_datum
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum τ L) (hDq : D.q = 2 ^ f) {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀2 : p₀ ≠ 2) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) (hfin : Finite D.model) {R : Type} [Group R]
    (ι₀ : R →* ModGL τ L) (hι₀ : Function.Injective ι₀)
    (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) (φ ψ : MulAut R)
    {u u' : ModGL τ L} (hφ : ∀ c, ι₀ (φ c) = u * ι₀ c * u⁻¹)
    (hψ : ∀ c, ι₀ (ψ c) = u' * ι₀ c * u'⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hu'G : u' ∈ adjointGroup τ L) (hu'F : D.Φ u' = u') (hu'3 : u' ^ 3 = 1)
    (hcomm : u * u' = u' * u) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (e : R ≃* ↥S.Γ) (y : ModGL τ L),
      S.D.q = 2 ^ f ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit τ a ≠ 1 ∧ y ∈ S.D.model ∧ y ∈ Subgroup.centralizer {rootDiagUnit τ a} ∧
      y ^ 3 = 1 ∧
      (∀ r : R, ((e (φ r) : ↥S.Γ) : ModGL τ L) =
        rootDiagUnit τ a * ((e r : ↥S.Γ) : ModGL τ L) * (rootDiagUnit τ a)⁻¹) ∧
      (∀ r : R, ((e (ψ r) : ↥S.Γ) : ModGL τ L) = y * ((e r : ↥S.Γ) : ModGL τ L) * y⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₀, hy₀, hy₀u⟩ := hmem
  have hy₀u' : y₀ = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y₀ * D.g0⁻¹ = u := hy₀u
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy₀).1
  have hd : rootDiagUnit τ a = D.g0⁻¹ * u * D.g0 := ha.symm.trans hy₀u'
  have hyp : y₀ ^ 3 = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := 3)
    rw [inv_inv] at h
    rw [hy₀u', h, hu3]
    group
  have hap : ∀ j, a j ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ 1 := by
      have hpow : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 :=
        (rootDiagUnitHom τ L).map_pow a 3
      rw [hpow, ← ha, hyp, rootDiagUnit_one]
    have h2 : a ^ 3 = 1 := rootDiagUnit_injective h1
    exact fun j => congrFun h2 j
  have hne : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hy₀u'] at h
    have hu : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [hu, h]
    group
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff L 2 (2 ^ f)).2 (dvd_pow_self 2 (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀2 ((Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let S : LangSetup τ L p₀ := D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin
  have hSq : S.D.q = 2 ^ f := by
    change D.q = 2 ^ f
    exact hDq
  have hT : rootDiagUnit τ a ∈ S.D.torus := by
    change rootDiagUnit τ a ∈ D.torus
    exact ha ▸ hy₀
  let ι : R →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  have hιinj : Function.Injective ι := (MulAut.conj D.g0⁻¹).injective.comp hι₀
  have hιrange : ι.range = S.Γ := by
    show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  let F : R →* ↥S.Γ := ι.codRestrict S.Γ (fun r => by
    rw [← hιrange]
    exact ⟨r, rfl⟩)
  have hFinj : Function.Injective F := fun r s h => hιinj (congrArg Subtype.val h)
  have hFsurj : Function.Surjective F := by
    intro g
    have hg : (g : ModGL τ L) ∈ ι.range := by
      rw [hιrange]
      exact g.2
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hg
    exact ⟨r, Subtype.ext hr⟩
  let e : R ≃* ↥S.Γ := MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩
  let y : ModGL τ L := D.g0⁻¹ * u' * D.g0
  have hM : y ∈ S.D.model := by
    change y ∈ D.model
    rw [LangDatum.mem_model]
    refine ⟨?_, ?_⟩
    · change D.g0⁻¹ * u' * D.g0 ∈ adjointGroup τ L
      exact (adjointGroup τ L).mul_mem
        ((adjointGroup τ L).mul_mem ((adjointGroup τ L).inv_mem D.g0_mem) hu'G) D.g0_mem
    · change D.n * D.Φ (D.g0⁻¹ * u' * D.g0) * D.n⁻¹ = D.g0⁻¹ * u' * D.g0
      rw [map_mul, map_mul, map_inv, D.lang, hu'F]
      group
  have hC : y ∈ Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    change rootDiagUnit τ a * (D.g0⁻¹ * u' * D.g0) =
      (D.g0⁻¹ * u' * D.g0) * rootDiagUnit τ a
    rw [hd]
    calc D.g0⁻¹ * u * D.g0 * (D.g0⁻¹ * u' * D.g0)
        = D.g0⁻¹ * (u * u') * D.g0 := by group
      _ = D.g0⁻¹ * (u' * u) * D.g0 := by rw [hcomm]
      _ = D.g0⁻¹ * u' * D.g0 * (D.g0⁻¹ * u * D.g0) := by group
  have hy3 : y ^ 3 = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u') (i := 3)
    rw [inv_inv] at h
    change (D.g0⁻¹ * u' * D.g0) ^ 3 = 1
    rw [h, hu'3]
    group
  refine ⟨S, a, e, y, hSq, hT, hap, hne, hM, hC, hy3, ?_, ?_⟩
  · intro r
    change ι (φ r) = rootDiagUnit τ a * ι r * (rootDiagUnit τ a)⁻¹
    rw [hι, hι, hφ r, hd]
    group
  · intro r
    change ι (ψ r) = (D.g0⁻¹ * u' * D.g0) * ι r * (D.g0⁻¹ * u' * D.g0)⁻¹
    rw [hι, hι, hψ r]
    group

end CFSG.StandardType

end
