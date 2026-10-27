module

public import CFSG.Quasithin.EmptyFaithful.S143VSq
public import CFSG.Quasithin.EmptyFaithful.S143VBr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section Theta

variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

theorem uOfL22_le_normalizer_Z (h : Hyp1281Two G T M L) :
    uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  h.uOfL22_le_g1.trans (Subgroup.centralizer_le_normalizer _)

@[expose] noncomputable def liftTilde (x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) :=
  Classical.choose (mem_secImg.1 x.2)

omit [Finite G] in
theorem liftTilde_mem (x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    ((liftTilde x : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) : G) ∈
      uOfL22 T M :=
  (Classical.choose_spec (mem_secImg.1 x.2)).1

omit [Finite G] in
theorem secMk_liftTilde (x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)
      (liftTilde x) = x :=
  (Classical.choose_spec (mem_secImg.1 x.2)).2

@[expose] noncomputable def thetaFun (x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    Multiplicative D.V :=
  Multiplicative.ofAdd (D.π ((liftTilde x : ↥(Subgroup.normalizer
    (quasithinOmegaOneCenter T : Set G))) : G))

include h in
theorem thetaFun_secMk {u : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))}
    (hu : (u : G) ∈ uOfL22 T M)
    (hx : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) u ∈ tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :
    thetaFun D ⟨_, hx⟩ = Multiplicative.ofAdd (D.π (u : G)) := by
  set v := liftTilde (T := T) (M := M) ⟨_, hx⟩ with hv
  have hvU : (v : G) ∈ uOfL22 T M := liftTilde_mem _
  have hvu : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) v =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u := secMk_liftTilde _
  have hZ : (v : G)⁻¹ * u ∈ quasithinOmegaOneCenter T := secMk_eq_secMk_iff.mp hvu
  have hZU' : (v : G)⁻¹ * u ∈ centerOf (uOfL22 T M) := h.omegaOneCenter_le_centerOf_uOfL22 hZ
  unfold thetaFun
  rw [← hv]
  exact congrArg Multiplicative.ofAdd ((D.π_eq_iff _ hvU _ hu).mpr hZU')

include h in
theorem thetaFun_eq {x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))}
    {u : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))}
    (hu : (u : G) ∈ uOfL22 T M)
    (hxu : (x : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T)) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u) :
    thetaFun D x = Multiplicative.ofAdd (D.π (u : G)) := by
  have hx : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) u ∈ tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M) :=
    hxu ▸ x.2
  have : x = ⟨_, hx⟩ := Subtype.ext hxu
  rw [this]
  exact thetaFun_secMk h D hu hx

include h in
theorem thetaFun_mul (x y : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    thetaFun D (x * y) = thetaFun D x * thetaFun D y := by
  set u := liftTilde x with hu
  set v := liftTilde y with hv
  have huU : (u : G) ∈ uOfL22 T M := liftTilde_mem x
  have hvU : (v : G) ∈ uOfL22 T M := liftTilde_mem y
  have hxu := secMk_liftTilde x
  have hyv := secMk_liftTilde y
  have hxy : ((x * y : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
      SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T)) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) (u * v) := by
    rw [map_mul, hxu, hyv]
    rfl
  rw [thetaFun_eq h D ((uOfL22 T M).mul_mem huU hvU) hxy]
  have h1 : thetaFun D x = Multiplicative.ofAdd (D.π (u : G)) :=
    thetaFun_eq h D huU hxu.symm
  have h2 : thetaFun D y = Multiplicative.ofAdd (D.π (v : G)) :=
    thetaFun_eq h D hvU hyv.symm
  rw [h1, h2, ← ofAdd_add]
  exact congrArg Multiplicative.ofAdd (D.π_mul _ huU _ hvU)

omit [Finite G] in
include hZU in
theorem thetaFun_injective : Function.Injective (thetaFun (T := T) (M := M) D) := by
  intro x y hxy
  set u := liftTilde x with hu
  set v := liftTilde y with hv
  have huU : (u : G) ∈ uOfL22 T M := liftTilde_mem x
  have hvU : (v : G) ∈ uOfL22 T M := liftTilde_mem y
  have hπ : D.π (u : G) = D.π (v : G) := by
    have := hxy
    unfold thetaFun at this
    rw [← hu, ← hv] at this
    exact Multiplicative.ofAdd.injective this
  have hZ : (u : G)⁻¹ * v ∈ centerOf (uOfL22 T M) := (D.π_eq_iff _ huU _ hvU).mp hπ
  rw [hZU] at hZ
  have : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) u = secMk (Subgroup.normalizer
      (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T) v :=
    secMk_eq_secMk_iff.mpr hZ
  exact Subtype.ext ((secMk_liftTilde x).symm.trans (this.trans (secMk_liftTilde y)))

include h in
theorem thetaFun_surjective : Function.Surjective (thetaFun (T := T) (M := M) D) := by
  intro w
  obtain ⟨u, hu, hπ⟩ := D.π_surj (Multiplicative.toAdd w)
  let u' : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) :=
    ⟨u, uOfL22_le_normalizer_Z h hu⟩
  refine ⟨⟨secMk _ _ u', secMk_mem_secImg (X := uOfL22 T M) (x := u') hu⟩, ?_⟩
  rw [thetaFun_eq h D (u := u') hu rfl]
  exact congrArg Multiplicative.ofAdd hπ ▸ rfl

@[expose] noncomputable def thetaHom (h : Hyp1281Two G T M L) (D : HatModel T M) :
    ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) →* Multiplicative D.V where
  toFun := thetaFun D
  map_one' := by
    have h1 : ((1 : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
        SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T)) =
        secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) (1 : ↥(Subgroup.normalizer
            (quasithinOmegaOneCenter T : Set G))) := by
      rw [map_one]
      rfl
    rw [thetaFun_eq h D (u := 1) (uOfL22 T M).one_mem h1]
    show Multiplicative.ofAdd (D.π 1) = 1
    rw [D.π_one]
    rfl
  map_mul' := thetaFun_mul h D

@[expose] noncomputable def theta (h : Hyp1281Two G T M L)
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) (D : HatModel T M) :
    ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) ≃* Multiplicative D.V :=
  MulEquiv.ofBijective (thetaHom h D) ⟨thetaFun_injective hZU D, thetaFun_surjective h D⟩

theorem theta_apply (h : Hyp1281Two G T M L)
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) (D : HatModel T M)
    (x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    theta h hZU D x = thetaFun D x := rfl

include h in
theorem theta_eq (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
    {x : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))}
    {u : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))}
    (hu : (u : G) ∈ uOfL22 T M)
    (hxu : (x : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T)) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u) :
    theta h hZU D x = Multiplicative.ofAdd (D.π (u : G)) := by
  rw [theta_apply]
  exact thetaFun_eq h D hu hxu

@[expose] noncomputable def qtilde (h : Hyp1281Two G T M L)
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) (D : HatModel T M) :
    ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) → ZMod 2 :=
  fun x => qhat D (Multiplicative.toAdd (theta h hZU D x))

end Theta

section QTilde

variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

omit [Finite G] in
theorem zmod_two_aux : ∀ a b c : ZMod 2, a + b + c + a + b = c := by decide

omit [Finite G] in
theorem natCard_eq_two_pow_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  have : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

include h hZU in
theorem qhat_zero : qhat D 0 = 0 := by
  have := qhat_add h hZU D 0 0
  simpa using this

include h hZU in
theorem qtilde_polar (x y : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    quadPolar (qtilde h hZU D) x y =
      D.B (Multiplicative.toAdd (theta h hZU D x)) (Multiplicative.toAdd (theta h hZU D y)) := by
  unfold quadPolar qtilde
  rw [map_mul, toAdd_mul, qhat_add h hZU D]
  exact zmod_two_aux _ _ _

include h hZU in
theorem qtilde_isQuadraticFormOn : IsQuadraticFormOn (qtilde h hZU D) := by
  refine ⟨?_, fun x y z => ?_, fun x y z => ?_⟩
  · unfold qtilde
    rw [map_one, toAdd_one]
    exact qhat_zero h hZU D
  · rw [qtilde_polar h hZU D, qtilde_polar h hZU D, qtilde_polar h hZU D, map_mul, toAdd_mul,
      LinearMap.map_add₂]
  · rw [qtilde_polar h hZU D, qtilde_polar h hZU D, qtilde_polar h hZU D, map_mul, toAdd_mul,
      map_add]

include h hZU in
theorem qtilde_isNondeg : IsNondegQuadratic (qtilde h hZU D) := by
  intro x hx
  have h1 : Multiplicative.toAdd (theta h hZU D x) = 0 := by
    apply D.B_nondegenerate
    intro w
    have := hx ((theta h hZU D).symm (Multiplicative.ofAdd w))
    rw [qtilde_polar h hZU D] at this
    simpa using this
  exact (theta h hZU D).map_eq_one_iff.mp (toAdd_eq_zero.mp h1)

include h hZU in
theorem card_tilde (hd : Module.finrank (ZMod 2) D.V = 4) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) = 16 := by
  rw [Nat.card_congr (theta h hZU D).toEquiv, Nat.card_congr Multiplicative.toAdd,
    natCard_eq_two_pow_finrank, hd]
  norm_num

include h hZU in
theorem qtilde_compat
    (x : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T))
    (hx : x ∈ tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))
    (u : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) (hu : (u : G) ∈ uOfL22 T M)
    (hxu : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) u = x) :
    qtilde h hZU D ⟨x, hx⟩ = 0 ↔ (u : G) ^ 2 = 1 := by
  have h1 := theta_eq h D hZU (x := ⟨x, hx⟩) hu hxu.symm
  unfold qtilde
  rw [h1, toAdd_ofAdd]
  classical
  rw [qhat_π h hZU D hu]
  by_cases hsq : (u : G) ^ 2 = 1
  · simp [hsq]
  · simp [hsq]

include h hZU D in
theorem tilde_mul_self (w : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) : w * w = 1 := by
  apply (theta h hZU D).injective
  rw [map_mul, map_one]
  show Multiplicative.ofAdd (Multiplicative.toAdd (theta h hZU D w) +
    Multiplicative.toAdd (theta h hZU D w)) = 1
  have : ∀ a : D.V, a + a = 0 := by
    intro a
    calc a + a = (1 + 1 : ZMod 2) • a := by rw [add_smul, one_smul]
      _ = 0 := by
        have h2 : (1 + 1 : ZMod 2) = 0 := by decide
        rw [h2, zero_smul]
  rw [this]
  rfl

include h hZU D in
theorem tilde_isMulCommutative :
    IsMulCommutative ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
  ⟨⟨fun a b => (theta h hZU D).injective (by simp [mul_comm])⟩⟩

end QTilde

section Action

variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

omit [Finite G] in
theorem mcOf_le_normalizer_Z : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.centralizer_le_normalizer _

include h hZU in
theorem theta_actTilde (x : ↥(mcOf T))
    (w : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
    theta h hZU D (S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22 x w) =
      Multiplicative.ofAdd (rhoH h D x (Multiplicative.toAdd (theta h hZU D w))) := by
  have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    h.g1_le_normalizer_uOfL22 x.2
  set u := liftTilde w with hu
  have huU : (u : G) ∈ uOfL22 T M := liftTilde_mem w
  have hwu : (w : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T)) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u := (secMk_liftTilde w).symm
  have hθw : theta h hZU D w = Multiplicative.ofAdd (D.π (u : G)) := theta_eq h D hZU huU hwu
  let x' : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) :=
    ⟨x, mcOf_le_normalizer_Z x.2⟩
  have hu' : ((x' * u * x'⁻¹ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) : G) ∈
      uOfL22 T M := by
    have : ((x' * u * x'⁻¹ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) : G) =
        (x : G) * (u : G) * (x : G)⁻¹ := rfl
    rw [this]
    exact HatModel.conj_mem_uOfL22 hxN huU
  have hact : ((S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22 x w :
        ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :
      SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T)) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) (x' * u * x'⁻¹) := by
    rw [S143.actTilde_apply, map_mul, map_mul, map_inv, hwu]
  rw [theta_eq h D hZU hu' hact, hθw, toAdd_ofAdd, rhoH_apply h D x hxN, D.rho_π ⟨x, hxN⟩ huU]
  rfl

include h hZU in
theorem actTilde_mem_orthogonalGroupOf (x : ↥(mcOf T)) :
    S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22 x ∈
      orthogonalGroupOf (qtilde h hZU D) := by
  intro w
  unfold qtilde
  rw [theta_actTilde h hZU D x w, toAdd_ofAdd]
  have hmem : rhoH h D x ∈ D.img (mcOf T) := by
    rw [← range_rhoH h D]
    exact ⟨x, rfl⟩
  exact img_le_orthSub h hZU D hmem _

include h hZU in
theorem card_range_actTilde :
    Nat.card (S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22).range = Nat.card (D.img (mcOf T)) := by
  have hker : (S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22).ker = (rhoH h D).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
      h.g1_le_normalizer_uOfL22 x.2
    rw [S143.actTilde_eq_one_iff _ _ _ _ _ (uOfL22_le_normalizer_Z h) x, rhoH_apply h D x hxN,
      D.rho_eq_one_iff, hZU]
  rw [← Subgroup.index_ker, hker, ← range_rhoH h D, Subgroup.index_ker]

end Action

end S143V

end CFSG.Quasithin
