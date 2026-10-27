module

public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n
open scoped commutatorElement

section Quotient

variable {K D : Type} [Field K] [AddCommGroup D] [Module K D] [Module.Finite K D]

theorem exists_quotient_quadSpace (B : LinearMap.BilinForm K D) (Qf : D → K)
    (halt : ∀ e, B e e = 0) (hsmul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e)
    (hadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (hrad : ∀ e, (∀ f, B e f = 0) → Qf e = 0)
    {A : Type} [Group A] (ρ : A →* (D ≃ₗ[K] D)) (hρQ : ∀ a e, Qf (ρ a e) = Qf e) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module K E) (_ : Module.Finite K E)
      (p : D →ₗ[K] E) (B' : LinearMap.BilinForm K E) (Qf' : E → K) (ρ' : A →* (E ≃ₗ[K] E)),
      Function.Surjective p ∧ (∀ e, p e = 0 ↔ ∀ f, B e f = 0) ∧
      Module.finrank K E + Module.finrank K (LinearMap.ker B) = Module.finrank K D ∧
      (∀ e f, B' (p e) (p f) = B e f) ∧ (∀ e, Qf' (p e) = Qf e) ∧
      (∀ a e, ρ' a (p e) = p (ρ a e)) ∧ (∀ a e, Qf' (ρ' a e) = Qf' e) ∧
      (∀ e, B' e e = 0) ∧ (∀ e, (∀ f, B' e f = 0) → e = 0) ∧
      (∀ (a : K) e, Qf' (a • e) = a ^ 2 * Qf' e) ∧
      ∀ e f, Qf' (e + f) = Qf' e + Qf' f + B' e f := by
  classical
  have hskew : ∀ e f, B f e = -B e f := by
    intro e f
    have h := halt (e + f)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    linear_combination h
  set N : Submodule K D := LinearMap.ker B with hN
  have hmemN : ∀ e, e ∈ N ↔ ∀ f, B e f = 0 := by
    intro e
    rw [hN, LinearMap.mem_ker, LinearMap.ext_iff]
    simp only [LinearMap.zero_apply]
  have hNflip : N ≤ LinearMap.ker (LinearMap.flip B) := by
    intro e he
    rw [LinearMap.mem_ker, LinearMap.ext_iff]
    intro f
    rw [LinearMap.flip_apply, hskew, (hmemN e).mp he f, neg_zero, LinearMap.zero_apply]
  let Q₀ : QuadraticForm K D :=
    { toFun := Qf
      toFun_smul := fun a e => by rw [hsmul, smul_eq_mul, sq]
      exists_companion' := ⟨B, hadd⟩ }
  have hQ₀ : ∀ e, Q₀ e = Qf e := fun e => rfl
  have hNrad : N ≤ Q₀.radical := by
    intro e he
    show Q₀ e = 0 ∧ QuadraticMap.polarBilin Q₀ e = 0
    refine ⟨hrad e ((hmemN e).mp he), ?_⟩
    ext f
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, QuadraticMap.polar, hQ₀, hQ₀,
      hQ₀, hadd, (hmemN e).mp he f]
    ring
  let B' : LinearMap.BilinForm K (D ⧸ N) := LinearMap.liftQ₂ N N B le_rfl hNflip
  have hB' : ∀ e f, B' (N.mkQ e) (N.mkQ f) = B e f := fun e f => by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact LinearMap.liftQ₂_mk le_rfl hNflip e f
  let Qf' : D ⧸ N → K := Q₀.lift N hNrad
  have hQf' : ∀ e, Qf' (N.mkQ e) = Qf e := fun e => by
    rw [Submodule.mkQ_apply]
    exact QuadraticMap.lift_mk hNrad e
  have hρB : ∀ a e f, B (ρ a e) (ρ a f) = B e f := by
    intro a e f
    have h1 := hadd (ρ a e) (ρ a f)
    rw [← map_add, hρQ, hρQ, hρQ, hadd] at h1
    linear_combination -h1
  have hmap : ∀ a : A, N.map (ρ a : D →ₗ[K] D) = N := by
    intro a
    refine le_antisymm ?_ fun e he => ?_
    · rintro _ ⟨e, he, rfl⟩
      refine (hmemN _).mpr fun f => ?_
      have h := hρB a e ((ρ a).symm f)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [LinearEquiv.coe_coe, h]
      exact (hmemN e).mp he _
    · refine ⟨(ρ a).symm e, (hmemN _).mpr fun f => ?_, by simp⟩
      have h := hρB a ((ρ a).symm e) f
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← h]
      exact (hmemN e).mp he _
  have hquot : ∀ (a : A) (e : D),
      Submodule.Quotient.equiv N N (ρ a) (hmap a) (N.mkQ e) = N.mkQ (ρ a e) := fun a e => rfl
  let F : A → ((D ⧸ N) ≃ₗ[K] (D ⧸ N)) := fun a => Submodule.Quotient.equiv N N (ρ a) (hmap a)
  have hF : ∀ a e, F a (N.mkQ e) = N.mkQ (ρ a e) := hquot
  let ρ' : A →* ((D ⧸ N) ≃ₗ[K] (D ⧸ N)) := MonoidHom.mk' F fun a b => by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    rw [LinearEquiv.mul_apply, hF, hF, hF, map_mul, LinearEquiv.mul_apply]
  have hρ' : ∀ a e, ρ' a (N.mkQ e) = N.mkQ (ρ a e) := hF
  refine ⟨D ⧸ N, inferInstance, inferInstance, inferInstance, N.mkQ, B', Qf', ρ',
    N.mkQ_surjective, fun e => ?_, Submodule.finrank_quotient_add_finrank N, hB', hQf', hρ',
    fun a x => ?_, fun x => ?_, fun x hx => ?_, fun c x => ?_, fun x y => ?_⟩
  · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmemN e
  · obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    rw [hρ', hQf', hQf', hρQ]
  · obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    rw [hB', halt]
  · obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hmemN e).mpr fun f => ?_
    rw [← hB']
    exact hx _
  · obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, hQf', hQf', hsmul]
  · obtain ⟨e, rfl⟩ := N.mkQ_surjective x
    obtain ⟨f, rfl⟩ := N.mkQ_surjective y
    rw [← map_add, hQf', hQf', hQf', hB', hadd]

end Quotient

section Transport

variable {G H : Type} [Group G] [Group H] {R N Z0 Zn Y Q : Subgroup G} {K : Type} [Field K]
  {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]

theorem exists_quadModel_of_surjective (π : G → E) (c : G → K) (B : LinearMap.BilinForm K E)
    (Qf : E → K) (hπmul : ∀ x ∈ N, ∀ y ∈ N, π (x * y) = π x + π y)
    (hπsurj : ∀ e, ∃ x ∈ N, π x = e) (hπker : ∀ x ∈ N, π x = 0 ↔ x ∈ Zn)
    (hcadd : ∀ a ∈ Z0, ∀ b ∈ Z0, c (a * b) = c a + c b) (hcker : ∀ a ∈ Z0, c a = 0 ↔ a ∈ Q)
    (hcsurj : ∀ s : K, ∃ a ∈ Z0, c a = s) (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ Z0)
    (hsq : ∀ x ∈ N, x ^ 2 ∈ Z0) (hcomm_eq : ∀ x ∈ N, ∀ y ∈ N, c ⁅x, y⁆ = B (π x) (π y))
    (hsq_eq : ∀ x ∈ N, c (x ^ 2) = Qf (π x)) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hQsmul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (ρ : ↥R →* (E ≃ₗ[K] E))
    (hρπ : ∀ (r : ↥R), ∀ x ∈ N, π ((r : G) * x * (r : G)⁻¹) = ρ r (π x))
    (hρQ : ∀ (r : ↥R) e, Qf (ρ r e) = Qf e) (hρker : ∀ r : ↥R, ρ r = 1 ↔ (r : G) ∈ N)
    (hNR : N ≤ R) (hZ0N : Z0 ≤ N) (hZnN : Zn ≤ N) (hYZ0 : Y ⊓ Z0 = Q) (hYsup : Y ⊔ Z0 = Zn)
    (θ : ↥R →* H) (hθ : Function.Surjective θ) (hθker : θ.ker = Y.subgroupOf R) :
    ∃ (γ : H → K) (M₀ : Tim79.QuadModel ((N.subgroupOf R).map θ) ((Z0.subgroupOf R).map θ) K γ)
      (ψ : H →* (M₀.E ≃ₗ[K] M₀.E)),
      Tim79.GammaReg ((N.subgroupOf R).map θ) ((Z0.subgroupOf R).map θ) γ ∧
      Module.finrank K M₀.E = Module.finrank K E ∧
      (∀ g : H, ∀ x ∈ (N.subgroupOf R).map θ, M₀.π (g * x * g⁻¹) = ψ g (M₀.π x)) ∧
      (∀ g : H, ∀ v, M₀.Qf (ψ g v) = M₀.Qf v) ∧
      (∀ g : H, ψ g = 1 ↔ g ∈ (N.subgroupOf R).map θ) := by
  classical
  have hYZn : Y ≤ Zn := hYsup ▸ le_sup_left
  have hQY : Q ≤ Y := hYZ0 ▸ inf_le_left
  have hYN : Y ≤ N := hYZn.trans hZnN
  have hker : ∀ a : ↥R, θ a = 1 ↔ (a : G) ∈ Y := fun a => by
    rw [← MonoidHom.mem_ker, hθker, Subgroup.mem_subgroupOf]
  have hθeq : ∀ a b : ↥R, θ a = θ b → ((a⁻¹ * b : ↥R) : G) ∈ Y := fun a b h => by
    rw [← hker, map_mul, map_inv, h, inv_mul_cancel]
  let πH : H → E := fun h =>
    if hh : ∃ a : ↥R, (a : G) ∈ N ∧ θ a = h then π (hh.choose : G) else 0
  let γH : H → K := fun h =>
    if hh : ∃ a : ↥R, (a : G) ∈ Z0 ∧ θ a = h then c (hh.choose : G) else 0
  have hπH : ∀ a : ↥R, (a : G) ∈ N → πH (θ a) = π a := by
    intro a ha
    have hh : ∃ b : ↥R, (b : G) ∈ N ∧ θ b = θ a := ⟨a, ha, rfl⟩
    simp only [πH, dif_pos hh]
    obtain ⟨hbN, hb⟩ := hh.choose_spec
    have hY := hθeq _ _ hb
    have hdN : ((hh.choose⁻¹ * a : ↥R) : G) ∈ N := hYN hY
    have h0 : π ((hh.choose⁻¹ * a : ↥R) : G) = 0 := (hπker _ hdN).mpr (hYZn hY)
    have e : (a : G) = (hh.choose : G) * ((hh.choose⁻¹ * a : ↥R) : G) := by
      simp
    rw [e, hπmul _ hbN _ hdN, h0, add_zero]
  have hγH : ∀ a : ↥R, (a : G) ∈ Z0 → γH (θ a) = c a := by
    intro a ha
    have hh : ∃ b : ↥R, (b : G) ∈ Z0 ∧ θ b = θ a := ⟨a, ha, rfl⟩
    simp only [γH, dif_pos hh]
    obtain ⟨hbZ, hb⟩ := hh.choose_spec
    have hY := hθeq _ _ hb
    have hdZ : ((hh.choose⁻¹ * a : ↥R) : G) ∈ Z0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Z0.mul_mem (Z0.inv_mem hbZ) ha
    have hdQ : ((hh.choose⁻¹ * a : ↥R) : G) ∈ Q := by
      rw [← hYZ0]
      exact Subgroup.mem_inf.mpr ⟨hY, hdZ⟩
    have h0 : c ((hh.choose⁻¹ * a : ↥R) : G) = 0 := (hcker _ hdZ).mpr hdQ
    have e : (a : G) = (hh.choose : G) * ((hh.choose⁻¹ * a : ↥R) : G) := by
      simp
    rw [e, hcadd _ hbZ _ hdZ, h0, add_zero]
  have hmemN : ∀ x : H, x ∈ (N.subgroupOf R).map θ ↔ ∃ a : ↥R, (a : G) ∈ N ∧ θ a = x := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hmemZ : ∀ x : H, x ∈ (Z0.subgroupOf R).map θ ↔ ∃ a : ↥R, (a : G) ∈ Z0 ∧ θ a = x := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hsplit : ∀ a : ↥R, (a : G) ∈ Zn → ∃ z : ↥R, (z : G) ∈ Z0 ∧ θ a = θ z := by
    intro a ha
    haveI : (Y.subgroupOf R).Normal := by
      rw [← hθker]
      exact θ.normal_ker
    have hYR : Y ≤ R := hYN.trans hNR
    have hZR : Z0 ≤ R := hZ0N.trans hNR
    have h1 : a ∈ Y.subgroupOf R ⊔ Z0.subgroupOf R := by
      rw [← Subgroup.subgroupOf_sup hYR hZR, hYsup, Subgroup.mem_subgroupOf]
      exact ha
    have h2 : (a : ↥R) ∈ ((Y.subgroupOf R ⊔ Z0.subgroupOf R : Subgroup ↥R) : Set ↥R) := h1
    rw [Subgroup.normal_mul] at h2
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp h2
    refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
    rw [← hyz, map_mul, (hker y).mpr (Subgroup.mem_subgroupOf.mp hy), one_mul]
  let M₀ : Tim79.QuadModel ((N.subgroupOf R).map θ) ((Z0.subgroupOf R).map θ) K γH :=
    { E := E
      π := πH
      B := B
      Qf := Qf
      π_mul := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        obtain ⟨b, hb, rfl⟩ := (hmemN y).mp hy
        rw [← map_mul, hπH (a * b) (N.mul_mem ha hb), hπH a ha, hπH b hb]
        exact hπmul _ ha _ hb
      π_surj := by
        intro e
        obtain ⟨x, hx, rfl⟩ := hπsurj e
        exact ⟨θ ⟨x, hNR hx⟩, (hmemN _).mpr ⟨⟨x, hNR hx⟩, hx, rfl⟩, hπH ⟨x, hNR hx⟩ hx⟩
      π_ker := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        rw [hπH a ha, hπker _ ha, hmemZ]
        constructor
        · intro haZ
          obtain ⟨z, hz, hza⟩ := hsplit a haZ
          exact ⟨z, hz, hza.symm⟩
        · rintro ⟨z, hz, hza⟩
          have hY := hθeq _ _ hza
          have e : (a : G) = (z : G) * ((z⁻¹ * a : ↥R) : G) := by simp
          rw [e]
          exact Zn.mul_mem (hYsup ▸ Subgroup.mem_sup_right hz) (hYZn hY)
      comm_mem := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        obtain ⟨b, hb, rfl⟩ := (hmemN y).mp hy
        exact (hmemZ _).mpr ⟨⁅a, b⁆, hcomm _ ha _ hb, map_commutatorElement θ a b⟩
      sq_mem := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        exact (hmemZ _).mpr ⟨a ^ 2, hsq _ ha, map_pow θ a 2⟩
      comm_eq := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        obtain ⟨b, hb, rfl⟩ := (hmemN y).mp hy
        rw [← map_commutatorElement, hγH ⁅a, b⁆ (hcomm _ ha _ hb), hπH a ha, hπH b hb]
        exact hcomm_eq _ ha _ hb
      sq_eq := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
        rw [← map_pow, hγH (a ^ 2) (hsq _ ha), hπH a ha]
        exact hsq_eq _ ha
      alt := halt
      nondeg := hnd
      Qf_smul := hQsmul
      Qf_add := hQadd }
  have hρY : θ.ker ≤ ρ.ker := by
    intro k hk
    rw [hθker, Subgroup.mem_subgroupOf] at hk
    exact MonoidHom.mem_ker.mpr ((hρker k).mpr (hYN hk))
  let eθ := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let ψ : H →* (E ≃ₗ[K] E) := (QuotientGroup.lift θ.ker ρ hρY).comp eθ.symm.toMonoidHom
  have hψ : ∀ a : ↥R, ψ (θ a) = ρ a := by
    intro a
    have h1 : eθ.symm (θ a) = (a : ↥R ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift θ.ker ρ hρY (eθ.symm (θ a)) = ρ a
    rw [h1, QuotientGroup.lift_mk]
  refine ⟨γH, M₀, ψ, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.map_mono fun a ha => Subgroup.mem_subgroupOf.mpr
      (hZ0N (Subgroup.mem_subgroupOf.mp ha)), ?_, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := (hmemZ x).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmemZ y).mp hy
      rw [← map_mul, hγH (a * b) (Z0.mul_mem ha hb), hγH a ha, hγH b hb]
      exact hcadd _ ha _ hb
    · intro x hx h0
      obtain ⟨a, ha, rfl⟩ := (hmemZ x).mp hx
      rw [hγH a ha] at h0
      exact (hker a).mpr (hQY ((hcker _ ha).mp h0))
    · intro s
      obtain ⟨z, hz, rfl⟩ := hcsurj s
      exact ⟨θ ⟨z, hNR (hZ0N hz)⟩, (hmemZ _).mpr ⟨⟨z, hNR (hZ0N hz)⟩, hz, rfl⟩,
        hγH ⟨z, hNR (hZ0N hz)⟩ hz⟩
  · intro g x hx
    obtain ⟨r, rfl⟩ := hθ g
    obtain ⟨a, ha, rfl⟩ := (hmemN x).mp hx
    have hconj : ((r * a * r⁻¹ : ↥R) : G) ∈ N := by
      rw [← hρker, map_mul, map_mul, (hρker a).mpr ha, mul_one, map_inv, mul_inv_cancel]
    show πH (θ r * θ a * (θ r)⁻¹) = ψ (θ r) (πH (θ a))
    rw [← map_inv, ← map_mul, ← map_mul, hπH _ hconj, hπH a ha, hψ]
    exact hρπ r _ ha
  · intro g v
    obtain ⟨r, rfl⟩ := hθ g
    show Qf (ψ (θ r) v) = Qf v
    rw [hψ]
    exact hρQ r v
  · intro g
    obtain ⟨r, rfl⟩ := hθ g
    rw [hψ, hρker, hmemN]
    constructor
    · intro hr
      exact ⟨r, hr, rfl⟩
    · rintro ⟨a, ha, hra⟩
      have hY := hθeq _ _ hra
      have e : (r : G) = (a : G) * ((a⁻¹ * r : ↥R) : G) := by simp
      rw [e]
      exact N.mul_mem ha (hYN hY)

end Transport

end CFSG.RankThree.GF2n.Stroth80
