module

public import CFSG.LieType.BorelTits.Matrix
import CFSG.GroupTheory.ConjTransport
import CFSG.CGT.PushingUpLit.SolKNA.R4.PMBasic
public import CFSG.LieType.BorelTits.Flag
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.LieType.BorelTits CFSG.Theory.Representation
open scoped commutatorElement TensorProduct

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_conj_mem_of_sylow_le [Finite K] {p : ℕ} [Fact p.Prime] {G Q : Subgroup (GL ι K)}
    (hQG : Q ≤ G) (hQ : IsPGroup p Q) (P : Sylow p G) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) :
    ∃ g : G, ∀ x (hx : x ∈ Q), g * ⟨x, hQG hx⟩ * g⁻¹ ∈ H := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (Matrix ι ι K) := inferInstance
  have : Fintype (GL ι K) :=
    Fintype.ofInjective (fun u : GL ι K => (u : Matrix ι ι K)) (fun _ _ h => Units.ext h)
  have : Finite (GL ι K) := Finite.of_fintype (GL ι K)
  have : Finite G := inferInstance
  let E : Subgroup G := Q.subgroupOf G
  have hE : IsPGroup p E := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQG).symm
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow P hE
  refine ⟨g, fun x hx => ?_⟩
  have hxE : (⟨x, hQG hx⟩ : G) ∈ E := Subgroup.mem_subgroupOf.mpr hx
  have hmap : (MulAut.conj g) ⟨x, hQG hx⟩ ∈ E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hxE
  have hP : (MulAut.conj g) ⟨x, hQG hx⟩ ∈ (P : Subgroup G) := hg hmap
  have hconj : g * ⟨x, hQG hx⟩ * g⁻¹ = (MulAut.conj g) ⟨x, hQG hx⟩ :=
    (MulAut.conj_apply g _).symm
  rw [hconj]
  exact hPH hP

theorem adjoin_eq_top_of_sylow_le [Finite K] {p : ℕ} [Fact p.Prime] {G Q : Subgroup (GL ι K)}
    (hQG : Q ≤ G) (hQ : IsPGroup p Q)
    (hspan : Algebra.adjoin K ((fun x : GL ι K => (x : Matrix ι ι K)) '' (Q : Set (GL ι K))) = ⊤)
    (P : Sylow p G) {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    Algebra.adjoin K (Set.range fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_le hQG hQ P hPH
  let S : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Set.range fun h : H => (((h : G) : GL ι K) : Matrix ι ι K))
  let u : GL ι K := ((g : G) : GL ι K)
  let U : Matrix ι ι K := (u : Matrix ι ι K)
  let U' : Matrix ι ι K := ((u⁻¹ : GL ι K) : Matrix ι ι K)
  have hUU' : U * U' = 1 := by
    simp only [U, U', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hU'U : U' * U = 1 := by
    simp only [U, U', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgen : ∀ x (hx : x ∈ Q), U * x * U' ∈ S := by
    intro x hx
    let xG : G := ⟨x, hQG hx⟩
    have hxH : g * xG * g⁻¹ ∈ H := hg x hx
    let h : H := ⟨g * xG * g⁻¹, hxH⟩
    have hunit : u * x * u⁻¹ = ((h : G) : GL ι K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hEq : U * x * U' = (((h : G) : GL ι K) : Matrix ι ι K) := by
      calc U * x * U' = ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K) := by
            simp only [U, U', Units.val_mul]
        _ = (((h : G) : GL ι K) : Matrix ι ι K) := by
            rw [hunit]
    rw [hEq]
    exact Algebra.subset_adjoin (Set.mem_range_self h)
  have hconj : ∀ M ∈ Algebra.adjoin K
      ((fun x : GL ι K => (x : Matrix ι ι K)) '' (Q : Set (GL ι K))), U * M * U' ∈ S := by
    intro M hM
    refine Algebra.adjoin_induction (p := fun M _ => U * M * U' ∈ S) ?_ ?_ ?_ ?_ hM
    · rintro x ⟨q, hq, rfl⟩
      exact hgen q hq
    · intro c
      have hc : U * algebraMap K (Matrix ι ι K) c * U' = algebraMap K (Matrix ι ι K) c := by
        rw [← Algebra.commutes c U, mul_assoc, hUU', mul_one]
      rw [hc]
      exact Subalgebra.algebraMap_mem S c
    · intro x y hx hy ihx ihy
      rw [mul_add, add_mul]
      exact add_mem ihx ihy
    · intro x y hx hy ihx ihy
      have hxy : (U * x * U') * (U * y * U') = U * (x * y) * U' := by
        calc (U * x * U') * (U * y * U')
            = U * x * (U' * U) * y * U' := by simp only [mul_assoc]
          _ = U * x * 1 * y * U' := by rw [hU'U]
          _ = U * x * y * U' := by simp only [mul_one]
          _ = U * (x * y) * U' := by simp only [mul_assoc]
      rw [← hxy]
      exact mul_mem ihx ihy
  rw [eq_top_iff]
  intro N _
  have hM : U' * N * U ∈ Algebra.adjoin K
      ((fun x : GL ι K => (x : Matrix ι ι K)) '' (Q : Set (GL ι K))) := by
    rw [hspan]
    exact Algebra.mem_top
  have hN : U * (U' * N * U) * U' ∈ S := hconj _ hM
  have hcancel : U * (U' * N * U) * U' = N := by
    calc U * (U' * N * U) * U'
        = (U * U') * N * (U * U') := by simp only [mul_assoc]
      _ = N := by rw [hUU', one_mul, mul_one]
  rwa [hcancel] at hN

theorem adjoin_range_natRep_eq_top {G : Subgroup (GL ι K)} {H : Subgroup G}
    (hspan : Algebra.adjoin K (Set.range fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) = ⊤) :
    Algebra.adjoin K (Set.range ((natRep G).comp H.subtype)) = ⊤ := by
  have hrange : Set.range ((natRep G).comp H.subtype) =
      ((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toAlgHom) ''
        Set.range (fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) := by
    rw [show ((natRep G).comp H.subtype : H → Module.End K (ι → K)) =
        (((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toAlgHom) :
          Matrix ι ι K → Module.End K (ι → K)) ∘
          (fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) from rfl]
    rw [Set.range_comp]
  rw [hrange, Algebra.adjoin_image, hspan, Algebra.map_top]
  exact (AlgHom.range_eq_top
    ((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toAlgHom)).mpr
      (AlgEquiv.surjective _)

theorem eq_bot_or_eq_top_of_isIrreducible {k Γ V : Type*} [Field k] [Monoid Γ] [AddCommGroup V]
    [Module k V] {ρ : Representation k Γ V} (hρ : ρ.IsIrreducible) (W : Submodule k V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let σ : Subrepresentation ρ := Subrepresentation.mk W hW
  rcases hρ.eq_bot_or_eq_top σ with h | h
  · left
    have h' := congrArg Subrepresentation.toSubmodule h
    change W = ⊥ at h'
    exact h'
  · right
    have h' := congrArg Subrepresentation.toSubmodule h
    change W = ⊤ at h'
    exact h'

theorem isIrreducible_of_adjoin_eq_top [Nonempty ι] {G : Subgroup (GL ι K)} {H : Subgroup G}
    (hspan : Algebra.adjoin K (Set.range fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) = ⊤) :
    Representation.IsIrreducible ((natRep G).comp H.subtype) := by
  exact irreducible_of_jacobson_density_surjective ((natRep G).comp H.subtype)
    (adjoin_range_natRep_eq_top hspan)

theorem eq_bot_of_normal_of_charP [Finite K] [Nonempty ι] {p : ℕ} [Fact p.Prime] [CharP K p]
    {G : Subgroup (GL ι K)} {H : Subgroup G}
    (hspan : Algebra.adjoin K (Set.range fun h : H => (((h : G) : GL ι K) : Matrix ι ι K)) = ⊤)
    {A : Subgroup H} [A.Normal] (hA : IsPGroup p A) : A = ⊥ := by
  classical
  let ρ : Representation K H (ι → K) := (natRep G).comp H.subtype
  let W : Submodule K (ι → K) := ⨅ a : A, LinearMap.ker (ρ (a : H) - 1)
  have hmem : ∀ w : ι → K, w ∈ W ↔ ∀ a : A, ρ (a : H) w = w := by
    intro w
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hinv : ∀ h : H, ∀ w ∈ W, ρ h w ∈ W := by
    intro h w hw
    rw [hmem] at hw ⊢
    intro a
    have hconj : h⁻¹ * (a : H) * h ∈ A :=
      Subgroup.Normal.conj_mem inferInstance (a : H) a.2 h⁻¹
    have hfix := hw ⟨h⁻¹ * (a : H) * h, hconj⟩
    calc ρ (a : H) (ρ h w) = ρ ((a : H) * h) w := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (h * (h⁻¹ * (a : H) * h)) w := by
            rw [show (a : H) * h = h * (h⁻¹ * (a : H) * h) by group]
      _ = ρ h (ρ (h⁻¹ * (a : H) * h) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ h w := by rw [hfix]
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ p A hA
  have hvW : v ∈ W := by
    rw [hmem]
    intro a
    exact hv a a.2
  rcases eq_bot_or_eq_top_of_isIrreducible (isIrreducible_of_adjoin_eq_top hspan) W hinv with
    hW | hW
  · rw [hW] at hvW
    exact absurd (by simpa using hvW) hv0
  · refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
    have hfix : ρ a = 1 := by
      refine LinearMap.ext fun w => ?_
      have hw : w ∈ W := by rw [hW]; exact Submodule.mem_top
      rw [hmem] at hw
      simpa using hw ⟨a, ha⟩
    have ha1 : (a : G) = 1 := by
      refine natRep_injective G ?_
      rw [show natRep G (a : G) = 1 from hfix, map_one]
    exact Subtype.ext (by simpa using ha1)

private theorem coe_commutator_conj {G : Type*} [Group G] {H : Subgroup G} {g x y : G}
    (hx : g * x * g⁻¹ ∈ H) (hy : g * y * g⁻¹ ∈ H) :
    ((⟨g * x * g⁻¹, hx⟩ * ⟨g * y * g⁻¹, hy⟩ * ⟨g * x * g⁻¹, hx⟩⁻¹ *
      ⟨g * y * g⁻¹, hy⟩⁻¹ : H) : G) = g * ⁅x, y⁆ * g⁻¹ := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem eq_bot_of_normal_of_commute_commutator {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] (hr : ¬ r ^ 2 ∣ Nat.card G) {H : Subgroup G} {A : Subgroup H} [A.Normal]
    (hA : IsPGroup r A) (g x₁ y₁ x₂ y₂ : G) (hx₁ : g * x₁ * g⁻¹ ∈ H) (hy₁ : g * y₁ * g⁻¹ ∈ H)
    (hx₂ : g * x₂ * g⁻¹ ∈ H) (hy₂ : g * y₂ * g⁻¹ ∈ H)
    (hkill : ∀ b : G, Commute b ⁅x₁, y₁⁆ → Commute b ⁅x₂, y₂⁆ → b ^ r = 1 → b = 1) :
    A = ⊥ := by
  classical
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  have hdvd : r ^ n ∣ Nat.card G := by
    rw [← hn]
    exact (Subgroup.card_subgroup_dvd_card A).trans (Subgroup.card_subgroup_dvd_card H)
  have hn1 : n ≤ 1 := by
    by_contra h
    exact hr ((pow_dvd_pow r (by omega : 2 ≤ n)).trans hdvd)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
  · exact Subgroup.card_eq_one.mp (by simpa using hn)
  · have hcardA : Nat.card A = r := by simpa using hn
    have hAcyc : IsCyclic A := isCyclic_of_prime_card hcardA
    let u₁ : H := ⟨g * x₁ * g⁻¹, hx₁⟩
    let v₁ : H := ⟨g * y₁ * g⁻¹, hy₁⟩
    let u₂ : H := ⟨g * x₂ * g⁻¹, hx₂⟩
    let v₂ : H := ⟨g * y₂ * g⁻¹, hy₂⟩
    have hnorm : ∀ h : H, h ∈ Subgroup.normalizer (A : Set H) := fun h => by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top h
    have hc₁ : u₁ * v₁ * u₁⁻¹ * v₁⁻¹ ∈ Subgroup.centralizer (A : Set H) :=
      CFSG.CGT.PushingUpLit.SolKNA.R4.commutator_mem_centralizer_of_isCyclic hAcyc
        (hnorm u₁) (hnorm v₁)
    have hc₂ : u₂ * v₂ * u₂⁻¹ * v₂⁻¹ ∈ Subgroup.centralizer (A : Set H) :=
      CFSG.CGT.PushingUpLit.SolKNA.R4.commutator_mem_centralizer_of_isCyclic hAcyc
        (hnorm u₂) (hnorm v₂)
    have hcoe₁ : ((u₁ * v₁ * u₁⁻¹ * v₁⁻¹ : H) : G) = g * ⁅x₁, y₁⁆ * g⁻¹ :=
      coe_commutator_conj hx₁ hy₁
    have hcoe₂ : ((u₂ * v₂ * u₂⁻¹ * v₂⁻¹ : H) : G) = g * ⁅x₂, y₂⁆ * g⁻¹ :=
      coe_commutator_conj hx₂ hy₂
    refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
    let aG : G := ((a : H) : G)
    let b : G := g⁻¹ * aG * g
    have hab : aG = g * b * g⁻¹ := by
      simp only [b, aG]
      group
    have haR : (⟨a, ha⟩ : A) ^ r = 1 := by
      rw [← hcardA]
      exact pow_card_eq_one'
    have haGr : aG ^ r = 1 := by
      have h := congrArg (fun x : A => ((x : H) : G)) haR
      simpa [aG] using h
    have hbR : b ^ r = 1 := by
      have h := conj_pow (a := g⁻¹) (b := aG) (i := r)
      rw [inv_inv] at h
      rw [show b = g⁻¹ * aG * g from rfl, h, haGr]
      group
    have hac₁ : aG * ((u₁ * v₁ * u₁⁻¹ * v₁⁻¹ : H) : G) =
        ((u₁ * v₁ * u₁⁻¹ * v₁⁻¹ : H) : G) * aG := by
      have h := Subgroup.mem_centralizer_iff.mp hc₁ a ha
      have h' := congrArg (fun x : H => (x : G)) h
      simpa [aG, Subgroup.coe_mul] using h'
    have hac₂ : aG * ((u₂ * v₂ * u₂⁻¹ * v₂⁻¹ : H) : G) =
        ((u₂ * v₂ * u₂⁻¹ * v₂⁻¹ : H) : G) * aG := by
      have h := Subgroup.mem_centralizer_iff.mp hc₂ a ha
      have h' := congrArg (fun x : H => (x : G)) h
      simpa [aG, Subgroup.coe_mul] using h'
    have hcomm₁ : Commute b ⁅x₁, y₁⁆ := by
      have hconj : Commute (g * b * g⁻¹) (g * ⁅x₁, y₁⁆ * g⁻¹) := by
        rw [← hab, ← hcoe₁]
        exact hac₁
      exact (Commute.conj_iff (a := b) (b := ⁅x₁, y₁⁆) g).mp hconj
    have hcomm₂ : Commute b ⁅x₂, y₂⁆ := by
      have hconj : Commute (g * b * g⁻¹) (g * ⁅x₂, y₂⁆ * g⁻¹) := by
        rw [← hab, ← hcoe₂]
        exact hac₂
      exact (Commute.conj_iff (a := b) (b := ⁅x₂, y₂⁆) g).mp hconj
    have hb1 : b = 1 := hkill b hcomm₁ hcomm₂ hbR
    have haG1 : aG = 1 := by
      rw [hab, hb1]
      group
    exact Subtype.ext (by simpa [aG] using haG1)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
