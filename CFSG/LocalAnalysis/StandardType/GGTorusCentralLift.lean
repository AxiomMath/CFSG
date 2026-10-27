module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestLift

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusTorData_of_centralLift_rootCoordinates
    {m N p : ℕ} {G R : Type} [Group G] [Group R] {μ : Type} [CommGroup μ]
    (ψ : G →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) (hm : 1 < m)
    (hcop : Nat.Coprime m (Nat.card ψ.ker))
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* R) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (Λ : R →* MulAut G) (hΛ : Function.Injective Λ)
    (hΛψ : ∀ x : G, Λ (ψ x) = MulAut.conj x)
    (E : Subgroup R) (hE : ∀ x, x ∈ E ↔ x ^ p = 1 ∧ x ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → R)
    (hn : ∀ k, n k ∈ Subgroup.normalizer (E : Set R))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (S : Subgroup R) (hcenter : Subgroup.center R = ⊥)
    (hcent : Subgroup.centralizer (E : Set R) ≤ S)
    (hScomm : ∀ a : Fin N → μ, ∀ t ∈ S, Commute (φ a) t)
    (htors : ∀ t ∈ S, t ^ m = 1 → t ∈ φ.range)
    (M : CoxeterMatrix (Fin N))
    (eW : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup R) E))
    (heW : ∀ k, (eW (M.simple k) : MulAut ↥E) = ggConjAut E (hn k)) :
    GGTorusTorData m N C M G (E.map Λ) := by
  classical
  have hμ : ∀ z : μ, z ^ m = 1 := by
    intro z
    apply l.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    change m • (Multiplicative.toAdd (l z) : ZMod m) = 0
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have hφpow : ∀ a : Fin N → μ, φ a ^ m = 1 := by
    intro a
    rw [← map_pow, show a ^ m = 1 by funext k; exact hμ (a k), map_one]
  have hφcomm : ∀ a b : Fin N → μ, Commute (φ a) (φ b) := by
    intro a b
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨φG, hφG⟩ := OrthRest.exists_section_of_exponent_coprime
    hψ hker hm hcop φ hφcomm hφpow
  have hφGpow : ∀ a : Fin N → μ, φG a ^ m = 1 := by
    intro a
    rw [← map_pow, show a ^ m = 1 by funext k; exact hμ (a k), map_one]
  have hφGinj : Function.Injective φG := by
    intro a b hab
    apply hφ
    rw [← hφG a, ← hφG b, hab]
  have hconjG : Function.Injective ((MulAut.conj : G →* MulAut G).comp φG) := by
    intro a b hab
    apply hΛ.comp hφ
    change Λ (φ a) = Λ (φ b)
    rw [← hφG a, ← hφG b, hΛψ, hΛψ]
    exact hab
  let E0 : Subgroup G := (E.comap φ).map φG
  have hE0 : ∀ x : G, x ∈ E0 ↔ x ^ p = 1 ∧ x ∈ φG.range := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hap : φ a ^ p = 1 := ((hE (φ a)).mp ha).1
      have ap : a ^ p = 1 := hφ (by rw [map_pow, hap, map_one])
      exact ⟨by rw [← map_pow, ap, map_one], ⟨a, rfl⟩⟩
    · rintro ⟨hp, a, rfl⟩
      have ap : a ^ p = 1 := hφGinj (by rw [map_pow, hp, map_one])
      refine ⟨a, (hE (φ a)).mpr ⟨?_, ⟨a, rfl⟩⟩, rfl⟩
      rw [← map_pow, ap, map_one]
  have hA : E0.map (MulAut.conj : G →* MulAut G) = E.map Λ := by
    ext a
    constructor
    · rintro ⟨x, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨φ b, hb, ?_⟩
      rw [← hφG b, hΛψ]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, rfl⟩ := ((hE x).mp hx).2
      refine ⟨φG b, ⟨b, hx, rfl⟩, ?_⟩
      rw [← hΛψ, hφG]
  choose nG hnG using fun k => hψ (n k)
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_map E Λ hΛ hA.symm n hn eW heW
  have hLiftN : ∀ k, Λ (n k) = MulAut.conj (nG k) := by
    intro k
    rw [← hnG k, hΛψ]
  have hΛrange : Λ.range = (MulAut.conj : G →* MulAut G).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := hψ x
      exact ⟨g, (hΛψ g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ψ g, hΛψ g⟩
  have hnGnormal : ∀ k, MulAut.conj (nG k) ∈
      Subgroup.normalizer ((scalarA E0) : Set (MulAut G)) := by
    intro k
    rw [← hLiftN]
    exact hnA k
  have hGformula : ∀ k (a : Fin N → μ),
      nG k * φG a * (nG k)⁻¹ = φG a * (φG (corTuple C.transpose k (a k)))⁻¹ := by
    intro k a
    refine OrthRest.eq_of_lift_of_coprime hker hcop ?_ ?_ ?_
    · simp only [map_mul, map_inv, hnG, hφG]
      exact hnformula k a
    · rw [show nG k * φG a * (nG k)⁻¹ = MulAut.conj (nG k) (φG a) by rfl,
        ← map_pow, hφGpow, map_one]
    · have hc : Commute (φG a) (φG (corTuple C.transpose k (a k))) := by
        change φG a * φG (corTuple C.transpose k (a k)) = _
        rw [← map_mul, ← map_mul, mul_comm]
      rw [hc.inv_right.mul_pow, hφGpow, inv_pow, hφGpow, inv_one, mul_one]
  let Tsc : Subgroup G := S.comap ψ
  have hodd : ∀ z ∈ Subgroup.center G, Odd (orderOf z) → z ∈ Tsc := by
    intro z hz _
    have hzR : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨g, rfl⟩ := hψ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
    rw [hcenter, Subgroup.mem_bot] at hzR
    change ψ z ∈ S
    rw [hzR]
    exact S.one_mem
  have hcentG : ∀ g : G, (∀ a ∈ scalarA E0,
      MulAut.conj g * a = a * MulAut.conj g) → g ∈ Tsc ⊔ Subgroup.center G := by
    intro g hg
    refine Subgroup.mem_sup_left (hcent ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply hΛ
    rw [map_mul, map_mul, hΛψ]
    have ha : Λ x ∈ scalarA E0 := by
      change Λ x ∈ E0.map (MulAut.conj : G →* MulAut G)
      rw [hA]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (hg (Λ x) ha).symm
  have hno : ∀ z ∈ ψ.ker, z ^ m = 1 → z = 1 := by
    intro z hz hzm
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzm)
      (orderOf_dvd_of_pow_eq_one (OrthRest.pow_card_ker_eq_one hz))
  have hfix : ∀ a : Fin N → μ, ∀ t ∈ Tsc, Commute (φG a) t := by
    intro a t ht
    exact (StdSubRest.commute_of_noTorsion hker hno (hφGpow a)
      (by rw [hφG]; exact (hScomm a (ψ t) ht).eq)).symm
  have htorsG : ∀ t ∈ Tsc, t ^ m = 1 → t ∈ φG.range := by
    intro t ht htm
    obtain ⟨a, ha⟩ := htors (ψ t) ht (by rw [← map_pow, htm, map_one])
    exact ⟨a, OrthRest.eq_of_lift_of_coprime hker hcop ((hφG a).trans ha)
      (hφGpow a) htm⟩
  let ρ : M.Group →* MulAut ↥(scalarA E0) := (ggAutomizer Λ.range (scalarA E0)).subtype.comp
    eA.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp eA.injective
  have hρrange : ρ.range = ggAutomizer Λ.range (scalarA E0) := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro ha
      obtain ⟨g, hg⟩ := eA.surjective ⟨a, ha⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hρsimple : ∀ k (a : ↥(scalarA E0)),
      ((ρ (M.simple k) a : ↥(scalarA E0)) : MulAut G) =
        MulAut.conj (nG k) * (a : MulAut G) * (MulAut.conj (nG k))⁻¹ := by
    intro k a
    have h := heA k
    change (((eA (M.simple k) : MulAut ↥(scalarA E0)) a : ↥(scalarA E0)) : MulAut G) = _
    rw [h, ggConjAut_apply, hLiftN]
  rw [← hA]
  obtain ⟨w, -, -, -, -, hw⟩ := exists_ggTorusTorWit_of_rootCoordinates_columns_mod l φG hconjG
    C B hCB hBC E0 hE0 ζ hζp hζ1 nG hnGnormal hGformula Tsc hodd hcentG hfix htorsG M
    ρ hρ (by simpa only [hΛrange] using hρrange) hρsimple
  exact ⟨w, hw⟩

end CFSG.StandardType
