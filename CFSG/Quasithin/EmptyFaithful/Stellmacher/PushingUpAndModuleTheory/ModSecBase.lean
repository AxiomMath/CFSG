module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModelBase

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open Equiv

variable {G : Type} [Group G] {H L N : Subgroup G}

theorem IsSec.normal_subgroupOf (hs : IsSec H L N) : (L.subgroupOf N).Normal :=
  ⟨fun x hx y => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 := hs.comm (y : G) y.2 (x : G) x.2
    have e : (y : G) * x * (y : G)⁻¹ = ((y : G) * x * (y : G)⁻¹ * (x : G)⁻¹) * x := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact L.mul_mem h1 hx⟩

theorem IsSec.conj_mem_N (hs : IsSec H L N) (h : ↥H) (x : ↥N) :
    (h : G) * (x : G) * (h : G)⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp (hs.normN h.2) _).mp x.2

theorem IsSec.conj_mem_L (hs : IsSec H L N) {h : G} (hh : h ∈ H) {x : G} (hx : x ∈ L) :
    h * x * h⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp (hs.normL hh) _).mp hx

@[expose, instance_reducible] def IsSec.commGroup (hs : IsSec H L N) : CommGroup (↥N ⧸ L.subgroupOf N) :=
  have := hs.normal_subgroupOf
  { (inferInstance : Group (↥N ⧸ L.subgroupOf N)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h1 := hs.comm ((y : G)⁻¹) (N.inv_mem y.2) ((x : G)⁻¹) (N.inv_mem x.2)
      have e : (((x * y)⁻¹ * (y * x) : ↥N) : G) =
          (y : G)⁻¹ * (x : G)⁻¹ * ((y : G)⁻¹)⁻¹ * ((x : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]
      exact h1 }

@[expose] def IsSec.conjN (hs : IsSec H L N) (h : ↥H) : ↥N →* ↥N where
  toFun x := ⟨(h : G) * x * (h : G)⁻¹, hs.conj_mem_N h x⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[expose] def IsSec.W (_ : IsSec H L N) : Type := ↥N ⧸ L.subgroupOf N

instance (hs : IsSec H L N) : CommGroup hs.W := hs.commGroup

@[expose] def IsSec.proj (hs : IsSec H L N) : ↥N →* hs.W :=
  have := hs.normal_subgroupOf
  QuotientGroup.mk' (L.subgroupOf N)

theorem IsSec.proj_eq_proj_iff (hs : IsSec H L N) (x y : ↥N) :
    hs.proj x = hs.proj y ↔ (x : G)⁻¹ * (y : G) ∈ L := by
  have := hs.normal_subgroupOf
  exact (QuotientGroup.eq (s := L.subgroupOf N)).trans Subgroup.mem_subgroupOf

theorem IsSec.proj_surjective (hs : IsSec H L N) : Function.Surjective hs.proj := by
  have := hs.normal_subgroupOf
  exact QuotientGroup.mk'_surjective (L.subgroupOf N)

theorem IsSec.proj_eq_one_iff (hs : IsSec H L N) (x : ↥N) : hs.proj x = 1 ↔ (x : G) ∈ L := by
  rw [← map_one hs.proj, hs.proj_eq_proj_iff]
  simp

@[expose] def IsSec.conjQ (hs : IsSec H L N) (h : ↥H) : hs.W →* hs.W :=
  have := hs.normal_subgroupOf
  QuotientGroup.map _ _ (hs.conjN h) (fun _ hx =>
    Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr
      (hs.conj_mem_L h.2 (Subgroup.mem_subgroupOf.mp hx))))

theorem IsSec.conjQ_mk (hs : IsSec H L N) (h : ↥H) (x : ↥N) :
    hs.conjQ h (hs.proj x) = hs.proj (hs.conjN h x) := rfl

theorem IsSec.conjN_conjN (hs : IsSec H L N) (h k : ↥H) (x : ↥N) :
    hs.conjN h (hs.conjN k x) = hs.conjN (h * k) x := by
  ext
  simp [IsSec.conjN, mul_assoc]

theorem IsSec.conjN_one (hs : IsSec H L N) (x : ↥N) : hs.conjN 1 x = x := by
  ext
  simp [IsSec.conjN]

@[expose] def IsSec.conjAut (hs : IsSec H L N) (h : ↥H) : MulAut hs.W where
  toFun := hs.conjQ h
  invFun := hs.conjQ h⁻¹
  left_inv := fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [IsSec.conjQ_mk, IsSec.conjQ_mk, IsSec.conjN_conjN, inv_mul_cancel, IsSec.conjN_one]
  right_inv := fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [IsSec.conjQ_mk, IsSec.conjQ_mk, IsSec.conjN_conjN, mul_inv_cancel, IsSec.conjN_one]
  map_mul' := fun a b => map_mul _ a b

@[expose] def IsSec.conjHom (hs : IsSec H L N) : ↥H →* MulAut hs.W where
  toFun := hs.conjAut
  map_one' := MulEquiv.ext fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    show hs.conjQ 1 (hs.proj x) = hs.proj x
    rw [IsSec.conjQ_mk, IsSec.conjN_one]
  map_mul' a b := MulEquiv.ext fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    show hs.conjQ (a * b) (hs.proj x) = hs.conjQ a (hs.conjQ b (hs.proj x))
    rw [IsSec.conjQ_mk, IsSec.conjQ_mk, IsSec.conjQ_mk, IsSec.conjN_conjN]

theorem IsSec.conjHom_mk (hs : IsSec H L N) (h : ↥H) (x : ↥N) :
    hs.conjHom h (hs.proj x) = hs.proj (hs.conjN h x) := rfl

theorem IsSec.conjHom_eq_one (hs : IsSec H L N) {h : ↥H}
    (hh : ∀ x ∈ N, (h : G) * x * (h : G)⁻¹ * x⁻¹ ∈ L) : hs.conjHom h = 1 :=
  MulEquiv.ext fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    show hs.conjHom h (hs.proj x) = hs.proj x
    rw [IsSec.conjHom_mk, IsSec.proj_eq_proj_iff]
    have e : ((hs.conjN h x : ↥N) : G)⁻¹ * (x : G) =
        (h : G) * ((x : G)⁻¹) * (h : G)⁻¹ * ((x : G)⁻¹)⁻¹ := by
      simp [IsSec.conjN, mul_assoc]
    rw [e]
    exact hh _ (N.inv_mem x.2)

variable [Finite G]

@[expose] noncomputable def secModule (hs : IsSec H L N) {n : ℕ} (θ : ↥H →* Perm (Fin n))
    (hθ : Function.Surjective θ) (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H) : Model n where
  W := hs.W
  fin := by have := hs.normal_subgroupOf; exact (inferInstance : Finite (↥N ⧸ L.subgroupOf N))
  act := MonoidHom.liftOfSurjective θ hθ ⟨hs.conjHom, fun h hh =>
    hs.conjHom_eq_one fun x hx =>
      ((mem_cSecIn_iff (hs.normL)).mp (Subgroup.mem_subgroupOf.mp (hk hh))).2 x hx⟩
  sq := fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_mul, hs.proj_eq_one_iff]
    simpa [pow_two] using hs.sq x x.2

variable (hs : IsSec H L N) {n : ℕ} (θ : ↥H →* Perm (Fin n)) (hθ : Function.Surjective θ)
  (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H)

theorem secModule_act_proj (h : ↥H) (x : ↥N) :
    (secModule hs θ hθ hk).act (θ h) (hs.proj x) = hs.proj (hs.conjN h x) := by
  have := MonoidHom.liftOfRightInverse_comp_apply θ (Function.surjInv hθ)
    (Function.rightInverse_surjInv hθ)
    (⟨hs.conjHom, fun h hh => hs.conjHom_eq_one fun x hx =>
      ((mem_cSecIn_iff (hs.normL)).mp (Subgroup.mem_subgroupOf.mp (hk hh))).2 x hx⟩ :
      {g : ↥H →* MulAut hs.W // θ.ker ≤ g.ker}) h
  exact congrArg (fun φ => φ (hs.proj x)) this

theorem secModule_act_eq_one_iff (h : ↥H) :
    (secModule hs θ hθ hk).act (θ h) = 1 ↔ (h : G) ∈ cSecIn H L N := by
  rw [mem_cSecIn_iff hs.normL]
  constructor
  · intro h1
    refine ⟨h.2, fun x hx => ?_⟩
    have h2 := secModule_act_proj hs θ hθ hk h ⟨x, hx⟩
    rw [h1] at h2
    have h3 : hs.proj (hs.conjN h ⟨x, hx⟩ * ⟨x, hx⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2]
      exact mul_inv_cancel _
    have := (hs.proj_eq_one_iff _).mp h3
    simpa [IsSec.conjN] using this
  · rintro ⟨-, h1⟩
    ext w
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [secModule_act_proj]
    exact congrArg (fun φ => φ (hs.proj x)) (hs.conjHom_eq_one h1)

theorem secModule_faithful_iff :
    (secModule hs θ hθ hk).Faithful ↔ (cSecIn H L N).subgroupOf H ≤ θ.ker := by
  constructor
  · intro hf h hh
    exact hf (((secModule_act_eq_one_iff hs θ hθ hk h).mpr hh).trans (map_one _).symm)
  · intro hf
    rw [Model.Faithful, injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨h, rfl⟩ := hθ σ
    exact hf ((secModule_act_eq_one_iff hs θ hθ hk h).mp hσ)

theorem isModelSec_of_iso {M : Model n} (hker : θ.ker = (cSecIn H L N).subgroupOf H)
    (e : M.Iso (secModule hs θ hθ hker.le)) : IsModelSec M H L N := by
  have hN := hs.normal_subgroupOf
  refine ⟨hN, θ, (e.toMulEquiv.toMonoidHom : M.W →* ↥N ⧸ L.subgroupOf N), hθ, hker,
    ⟨?_, ?_, ?_⟩⟩
  · exact e.toMulEquiv.surjective
  · exact e.toMulEquiv.injective
  · intro k u x hux
    refine ⟨hs.conj_mem_N k x, ?_⟩
    show e.toMulEquiv (M.act (θ k) u) = _
    rw [e.map_act]
    have h1 : e.toMulEquiv u = hs.proj x := hux
    rw [h1, secModule_act_proj]
    rfl

theorem exists_iso_of_isModelSec {M : Model n} (hker : θ.ker = (cSecIn H L N).subgroupOf H)
    [(L.subgroupOf N).Normal] {β : M.W →* ↥N ⧸ L.subgroupOf N}
    (hβ : SecData M H L N θ β) : Nonempty (M.Iso (secModule hs θ hθ hker.le)) := by
  refine ⟨⟨MulEquiv.ofBijective (β : M.W →* (secModule hs θ hθ hker.le).W) ⟨hβ.inj, hβ.surj⟩,
    fun σ w => ?_⟩⟩
  obtain ⟨k, rfl⟩ := hθ σ
  obtain ⟨x, hx⟩ := hs.proj_surjective (β w)
  obtain ⟨hkx, h1⟩ := hβ.equiv k w x hx.symm
  show β (M.act (θ k) w) = (secModule hs θ hθ hker.le).act (θ k) (β w)
  rw [← hx, secModule_act_proj, h1]
  rfl

end CFSG.Quasithin.F53Mod
