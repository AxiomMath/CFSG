module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphism

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

variable {G : Type} [Group G]

theorem exists_prod_equiv_sup {A D : Subgroup G} (hAD : A ≤ Subgroup.centralizer (D : Set G))
    (hinf : A ⊓ D = ⊥) :
    ∃ θ : A × D ≃* (A ⊔ D : Subgroup G), ∀ (a : A) (d : D), (θ (a, d) : G) = a * d := by
  have comm : ∀ (a : A) (d : D), Commute (A.subtype a) (D.subtype d) := fun a d =>
    (Subgroup.mem_centralizer_iff.mp (hAD a.2) d d.2).symm
  let F := MonoidHom.noncommCoprod A.subtype D.subtype comm
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, d⟩ had
    rw [MonoidHom.noncommCoprod_apply] at had
    have ha : (a : G) = (d : G)⁻¹ := eq_inv_of_mul_eq_one_left had
    have hmem : (a : G) ∈ A ⊓ D := ⟨a.2, ha ▸ D.inv_mem d.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hd : (d : G) = 1 := by rw [← inv_inv (d : G), ← ha, hmem, inv_one]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hd)
  have hrange : F.range = A ⊔ D := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun a d => rfl⟩

theorem card_sup_of_commute {A D : Subgroup G} (hAD : A ≤ Subgroup.centralizer (D : Set G))
    (hinf : A ⊓ D = ⊥) : Nat.card (A ⊔ D : Subgroup G) = Nat.card A * Nat.card D := by
  obtain ⟨θ, -⟩ := exists_prod_equiv_sup hAD hinf
  rw [← Nat.card_prod, Nat.card_congr θ.toEquiv]

@[expose] def conjToAut (Q N : Subgroup G) (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    N →* MulAut Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem conjToAut_apply_coe (Q N : Subgroup G) (hN : N ≤ Subgroup.normalizer (Q : Set G))
    (n : N) (y : Q) : ((conjToAut Q N hN n y : Q) : G) = n * y * (n : G)⁻¹ :=
  rfl

theorem card_range_conj_eq_relIndex (Q N : Subgroup G)
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    Nat.card (conjToAut Q N hN).range = (Subgroup.centralizer (Q : Set G)).relIndex N := by
  rw [← Subgroup.index_ker]
  congr 1
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn y hy
    have h := congrArg (fun α : MulAut Q => ((α ⟨y, hy⟩ : Q) : G)) hn
    simp only [conjToAut_apply_coe, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  · intro hn
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [conjToAut_apply_coe, MulAut.one_apply, ← hn y y.2, mul_inv_cancel_right]

variable {m : ℕ} {k : Type} [Field k] [Finite k]

theorem exists_semilinear_conj
    [Finite G] (hm : 1 ≤ m) (hk : Nat.card k = 2 ^ (2 * m + 1))
    {K T Q P : Subgroup G} (ψ : K ≃* suzukiGroup m k) (hTK : T ≤ K) (hQK : Q ≤ K)
    (hTU : (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k)
    (hQZ : (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k)
    (hTP : T ≤ Subgroup.centralizer (P : Set G)) (hinf : T ⊓ P = ⊥)
    (e : Multiplicative k ≃* Q)
    (he : ∀ b : k, ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G))
    {g : G} (hgS : g ∈ Subgroup.normalizer ((T ⊔ P : Subgroup G) : Set G))
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ (c : kˣ) (σ : k ≃+* k), ∀ b : k,
      g * (e (.ofAdd b) : G) * g⁻¹ = e (.ofAdd (c * σ b)) := by
  have hTmem : ∀ x : suzukiU m k, (ψ.symm x : G) ∈ T := fun x => by
    have hx : (x : suzukiGroup m k) ∈ (T.subgroupOf K).map ψ.toMonoidHom := by
      rw [hTU]
      exact x.2
    rw [Subgroup.mem_map_equiv] at hx
    exact hx
  have hTsurj : ∀ y ∈ T, ∃ x : suzukiU m k, (ψ.symm x : G) = y := fun y hy => by
    have hyU : ψ ⟨y, hTK hy⟩ ∈ suzukiU m k := by
      rw [← hTU, mem_map_subgroupOf_iff]
      exact hy
    exact ⟨⟨_, hyU⟩, by rw [MulEquiv.symm_apply_apply]⟩
  let fT : suzukiU m k →* T :=
    { toFun := fun x => ⟨(ψ.symm x : G), hTmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hfT : Function.Bijective fT := by
    refine ⟨fun x y hxy => Subtype.ext (ψ.symm.injective (Subtype.ext ?_)), fun y => ?_⟩
    · exact congrArg (fun z : T => (z : G)) hxy
    · obtain ⟨x, hx⟩ := hTsurj y y.2
      exact ⟨x, Subtype.ext hx⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_prod_equiv_sup hTP hinf
  let θ : suzukiU m k × P ≃* (T ⊔ P : Subgroup G) :=
    ((MulEquiv.ofBijective fT hfT).prodCongr (MulEquiv.refl P)).trans θ₀
  have hθ : ∀ (x : suzukiU m k) (p : P), (θ (x, p) : G) = (ψ.symm x : G) * p := fun x p =>
    hθ₀ _ _
  let cg : MulAut (T ⊔ P : Subgroup G) := (T ⊔ P).normalizerMonoidHom ⟨g, hgS⟩
  let γ : MulAut (suzukiU m k × P) := θ.trans (cg.trans θ.symm)
  have hγθ : ∀ w, (θ (γ w) : G) = g * θ w * g⁻¹ := fun w => by
    change ((θ (θ.symm (cg (θ w)))) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hroot : ∀ w : suzukiU m k × P, w ∈ rootCenter m k P ↔ (θ w : G) ∈ Q := by
    rintro ⟨x, p⟩
    rw [rootCenter, Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_bot, hθ]
    have hQ : ∀ y : suzukiGroup m k, (ψ.symm y : G) ∈ Q ↔ y ∈ suzukiZ0 m k := fun y => by
      rw [← hQZ, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hx, rfl⟩
      rw [OneMemClass.coe_one, mul_one, hQ]
      exact hx
    · intro hxp
      have hQT := (point_root_le_center_point_sylow hk ψ hTK hQK hTU hQZ).1
      have hpT : (p : G) ∈ T := by
        have h1 := T.mul_mem (T.inv_mem (hTmem x)) (hQT hxp)
        rwa [inv_mul_cancel_left] at h1
      have hp1 : (p : G) = 1 := by
        have hmem : (p : G) ∈ T ⊓ P := ⟨hpT, p.2⟩
        rwa [hinf, Subgroup.mem_bot] at hmem
      rw [hp1, mul_one, hQ] at hxp
      exact ⟨hxp, Subtype.ext hp1⟩
  have hγ : γ ∈ autStabilizer (rootCenter m k P) := by
    have hle : (rootCenter m k P).map (γ : suzukiU m k × P →* suzukiU m k × P) ≤
        rootCenter m k P := by
      rintro _ ⟨w, hw, rfl⟩
      change γ w ∈ rootCenter m k P
      rw [hroot, hγθ]
      exact (Subgroup.mem_normalizer_iff.mp hgQ _).mp ((hroot w).mp hw)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective γ.injective])
  obtain ⟨c, σ, hcσ⟩ := exists_semilinear_of_mem_autStabilizer hm hk hγ
  have hpt : ∀ b : k, (θ (rootCenterPoint m k P b : suzukiU m k × P) : G) =
      (e (.ofAdd b) : G) := fun b => by
    rw [coe_rootCenterPoint, hθ, he, OneMemClass.coe_one, mul_one]
    rfl
  refine ⟨c, σ, fun b => ?_⟩
  have h1 := congrArg (fun w => (θ w : G)) (hcσ b)
  simp only [hγθ, hpt] at h1
  exact h1

theorem odd_semilinear_order (m : ℕ) : Odd ((2 ^ (2 * m + 1) - 1) * (2 * m + 1)) := by
  refine Nat.odd_mul.2 ⟨⟨2 ^ (2 * m) - 1, ?_⟩, odd_two_mul_add_one m⟩
  have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem relIndex_centralizer_dvd_of_normalizes [Finite G] (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ (2 * m + 1))
    {K T Q P : Subgroup G} (ψ : K ≃* suzukiGroup m k) (hTK : T ≤ K) (hQK : Q ≤ K)
    (hTU : (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k)
    (hQZ : (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k)
    (hTP : T ≤ Subgroup.centralizer (P : Set G)) (hinf : T ⊓ P = ⊥)
    (e : Multiplicative k ≃* Q)
    (he : ∀ b : k, ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G))
    {N : Subgroup G} (hNS : N ≤ Subgroup.normalizer ((T ⊔ P : Subgroup G) : Set G))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) :
    (Subgroup.centralizer (Q : Set G)).relIndex N ∣ (2 ^ (2 * m + 1) - 1) * (2 * m + 1) ∧
      Odd ((Subgroup.centralizer (Q : Set G)).relIndex N) := by
  rw [← card_range_conj_eq_relIndex Q N hNQ]
  have hdvd := card_dvd_of_forall_coordSemilinear e (H := (conjToAut Q N hNQ).range) (by
    rintro _ ⟨n, rfl⟩
    obtain ⟨c, σ, h⟩ := exists_semilinear_conj hm hk ψ hTK hQK hTU hQZ hTP hinf e he
      (hNS n.2) (hNQ n.2)
    exact ⟨c, σ, fun b => Subtype.ext (by rw [conjToAut_apply_coe]; exact h b)⟩)
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := k) Nat.prime_two (by omega) hk
  rw [Nat.card_units, hk, hAut] at hdvd
  exact ⟨hdvd, (odd_semilinear_order m).of_dvd_nat hdvd⟩

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
