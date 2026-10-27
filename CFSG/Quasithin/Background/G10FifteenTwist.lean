module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def conjAut {H : Subgroup (GLV V)} {x : GLV V} (hx2 : x * x = 1)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) : ↥H ≃* ↥H where
  toFun h := ⟨x * h * x⁻¹, hxH h h.2⟩
  invFun h := ⟨x * h * x⁻¹, hxH h h.2⟩
  left_inv h := by
    apply Subtype.ext
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    show x * (x * (h : GLV V) * x⁻¹) * x⁻¹ = h
    rw [hx]
    calc x * (x * (h : GLV V) * x) * x = (x * x) * (h : GLV V) * (x * x) := by group
      _ = h := by rw [hx2]; simp
  right_inv h := by
    apply Subtype.ext
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    show x * (x * (h : GLV V) * x⁻¹) * x⁻¹ = h
    rw [hx]
    calc x * (x * (h : GLV V) * x) * x = (x * x) * (h : GLV V) * (x * x) := by group
      _ = h := by rw [hx2]; simp
  map_mul' a b := by
    apply Subtype.ext
    show x * ((a : GLV V) * b) * x⁻¹ = x * (a : GLV V) * x⁻¹ * (x * (b : GLV V) * x⁻¹)
    group

@[simp] theorem coe_conjAut {H : Subgroup (GLV V)} {x : GLV V} (hx2 : x * x = 1)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (h : ↥H) :
    ((conjAut hx2 hxH h : ↥H) : GLV V) = x * (h : GLV V) * x⁻¹ := rfl

variable {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem restrictHom_injective_of_faithful (hI : Invariant H I) (hf : FaithfulOn H I) :
    Function.Injective (restrictHom H I hI) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [restrictHom_eq_one_iff] at ha
  apply Subtype.ext
  exact (faithfulOn_iff.1 hf) a a.2 ha

@[expose] noncomputable def faithfulEquiv (hI : Invariant H I) (hf : FaithfulOn H I) :
    ↥H ≃* ↥(restrictRange H I hI) :=
  MulEquiv.ofBijective (restrictHom H I hI).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.2 (restrictHom_injective_of_faithful hI hf),
      MonoidHom.rangeRestrict_surjective _⟩

@[simp] theorem coe_faithfulEquiv (hI : Invariant H I) (hf : FaithfulOn H I) (h : ↥H) :
    ((faithfulEquiv hI hf h : ↥(restrictRange H I hI)) : GLV ↥I) = restrictHom H I hI h := rfl

@[expose] noncomputable def twistAut {x : GLV V} (hx2 : x * x = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hI : Invariant H I) (hf : FaithfulOn H I) :
    ↥(restrictRange H I hI) ≃* ↥(restrictRange H I hI) :=
  (faithfulEquiv hI hf).symm.trans ((conjAut hx2 hxH).trans (faithfulEquiv hI hf))

theorem twistAut_apply {x : GLV V} (hx2 : x * x = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hI : Invariant H I) (hf : FaithfulOn H I) (h : ↥H) :
    twistAut hx2 hxH hI hf (faithfulEquiv hI hf h) = faithfulEquiv hI hf (conjAut hx2 hxH h) := by
  simp [twistAut]


theorem conjAut_conjAut {x : GLV V} (hx2 : x * x = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (h : ↥H) :
    conjAut hx2 hxH (conjAut hx2 hxH h) = h := by
  apply Subtype.ext
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  show x * (x * (h : GLV V) * x⁻¹) * x⁻¹ = h
  rw [hx]
  calc x * (x * (h : GLV V) * x) * x = (x * x) * (h : GLV V) * (x * x) := by group
    _ = h := by rw [hx2]; simp

theorem hiso_of_twist {x : GLV V} (hx2 : x * x = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hI : Invariant H I) (hf : FaithfulOn H I) (c : GLV ↥I)
    (hc : ∀ k : ↥(restrictRange H I hI),
      ((twistAut hx2 hxH hI hf k : ↥(restrictRange H I hI)) : GLV ↥I) = c * (k : GLV ↥I) * c⁻¹) :
    HIso H I (conjSub x I) := by
  refine ⟨c.trans (LinearEquiv.ofSubmodules (x : V ≃ₗ[ZMod 2] V) I (conjSub x I) rfl),
    fun k hk i j hkij => ?_⟩
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 := hc (faithfulEquiv hI hf ⟨k, hk⟩)
  rw [twistAut_apply, coe_faithfulEquiv, coe_faithfulEquiv] at h1
  have h2 : (restrictHom H I hI (conjAut hx2 hxH ⟨k, hk⟩)) (c i) =
      c ((restrictHom H I hI ⟨k, hk⟩) i) := by
    rw [h1]
    show c ((restrictHom H I hI ⟨k, hk⟩) (c⁻¹ (c i))) = _
    rw [show c⁻¹ (c i) = i from c.symm_apply_apply i]
  have h3 : (restrictHom H I hI ⟨k, hk⟩) i = j := Subtype.ext hkij
  rw [h3] at h2
  have h4 := congrArg (fun w : ↥I => ((w : ↥I) : V)) h2
  simp only [coe_restrictHom, coe_conjAut] at h4
  have hxx : ∀ w : V, x (x w) = w := fun w => by
    have := congrArg (fun e : GLV V => e w) hx2
    exact this
  show k (x ((c i : ↥I) : V)) = x ((c j : ↥I) : V)
  rw [← h4]
  show k (x ((c i : ↥I) : V)) = x (x (k (x⁻¹ ((c i : ↥I) : V))))
  rw [hx, hxx]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_sylow_H : ∃ (T : Subgroup (GLV V)) (P : Sylow 2 ↥(normalClosure Γ L)),
    X ≤ T ∧ (P : Subgroup ↥(normalClosure Γ L)).map (normalClosure Γ L).subtype =
      T ⊓ normalClosure Γ L ∧
    ∀ x ∈ X, ∀ t ∈ T ⊓ normalClosure Γ L, x * t * x⁻¹ * t⁻¹ ∈ X ⊓ normalClosure Γ L := by
  obtain ⟨T, hT, hXT, hXN⟩ := hyp.four
  have hH := normalClosure_normal Γ L
  obtain ⟨hTΓ, hcomm⟩ := hyp.toG101Hyp.g10_9 hT ⟨hXT, hXN⟩ hH
  have hHΓ : normalClosure Γ L ≤ Γ := hyp.H_le
  have hsub : ((normalClosure Γ L).subgroupOf Γ).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff hHΓ]
    intro h k hh hk
    exact hH k hk h hh
  obtain ⟨P, hP⟩ :=
    CFSG.QuasithinUnique.RankOneRecog.exists_sylow_inf_of_subnormal hTΓ hHΓ hsub
  exact ⟨T, P, hXT, hP, hcomm⟩


theorem twist_package {x : GLV V} (hx : x ∈ X) {I : Submodule (ZMod 2) V}
    (hI : Invariant (normalClosure Γ L) I) (hf : FaithfulOn (normalClosure Γ L) I) :
    ∃ (α : ↥(restrictRange (normalClosure Γ L) I hI) ≃* ↥(restrictRange (normalClosure Γ L) I hI))
      (P : Sylow 2 ↥(restrictRange (normalClosure Γ L) I hI)),
      (∀ s ∈ P, α s ∈ P) ∧ (∀ s, α (α s) = s) ∧
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) ∧
      ((∃ c : GLV ↥I, ∀ k : ↥(restrictRange (normalClosure Γ L) I hI),
          ((α k : ↥(restrictRange (normalClosure Γ L) I hI)) : GLV ↥I) =
            c * (k : GLV ↥I) * c⁻¹) → HIso (normalClosure Γ L) I (conjSub x I)) := by
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  obtain ⟨T, PH, hXT, hP, hcomm⟩ := hyp.exists_sylow_H
  have hmem : ∀ h : ↥(normalClosure Γ L), h ∈ PH ↔ (h : GLV V) ∈ T := by
    intro h
    constructor
    · intro hh
      have : (h : GLV V) ∈
          (PH : Subgroup ↥(normalClosure Γ L)).map (normalClosure Γ L).subtype := ⟨h, hh, rfl⟩
      rw [hP] at this
      exact this.1
    · intro hh
      have : (h : GLV V) ∈ T ⊓ normalClosure Γ L := ⟨hh, h.2⟩
      rw [← hP] at this
      obtain ⟨h', hh', hh'eq⟩ := this
      have : h' = h := Subtype.ext hh'eq
      rw [← this]
      exact hh'
  have hsurj : Function.Surjective (restrictHom (normalClosure Γ L) I hI).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  set PK := PH.mapSurjective hsurj with hPK
  have hmemK : ∀ s : ↥(restrictRange (normalClosure Γ L) I hI), s ∈ PK ↔
      ∃ h ∈ PH, faithfulEquiv hI hf h = s := by
    intro s
    constructor
    · intro hs
      have : s ∈ (PH : Subgroup ↥(normalClosure Γ L)).map
          (restrictHom (normalClosure Γ L) I hI).rangeRestrict := hs
      obtain ⟨h, hh, rfl⟩ := this
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h, hh, rfl⟩
  have hconjP : ∀ h ∈ PH, conjAut hx2 hxH h ∈ PH := by
    intro h hh
    rw [hmem] at hh ⊢
    rw [coe_conjAut]
    exact T.mul_mem (T.mul_mem (hXT hx) hh) (T.inv_mem (hXT hx))
  have hcX : ∀ h ∈ PH, ((h⁻¹ * conjAut hx2 hxH h : ↥(normalClosure Γ L)) : GLV V) ∈ X := by
    intro h hh
    have hhT : (h : GLV V) ∈ T := (hmem h).1 hh
    have h1 := hcomm x hx (h : GLV V)⁻¹ ⟨T.inv_mem hhT, (normalClosure Γ L).inv_mem h.2⟩
    have h2 := X.inv_mem h1.1
    have : ((h⁻¹ * conjAut hx2 hxH h : ↥(normalClosure Γ L)) : GLV V) =
        (x * (h : GLV V)⁻¹ * x⁻¹ * ((h : GLV V)⁻¹)⁻¹)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut]
      group
    rw [this]
    exact h2
  refine ⟨twistAut hx2 hxH hI hf, PK, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨h, hh, rfl⟩ := (hmemK s).1 hs
    rw [twistAut_apply]
    exact (hmemK _).2 ⟨_, hconjP h hh, rfl⟩
  · intro s
    obtain ⟨h, rfl⟩ := (faithfulEquiv hI hf).surjective s
    rw [twistAut_apply, twistAut_apply, conjAut_conjAut]
  · intro s hs t ht
    obtain ⟨h, hh, rfl⟩ := (hmemK s).1 hs
    obtain ⟨h', hh', rfl⟩ := (hmemK t).1 ht
    have e1 : (faithfulEquiv hI hf h)⁻¹ * twistAut hx2 hxH hI hf (faithfulEquiv hI hf h) =
        faithfulEquiv hI hf (h⁻¹ * conjAut hx2 hxH h) := by
      rw [twistAut_apply, map_mul, map_inv]
    have e2 : (faithfulEquiv hI hf h')⁻¹ * twistAut hx2 hxH hI hf (faithfulEquiv hI hf h') =
        faithfulEquiv hI hf (h'⁻¹ * conjAut hx2 hxH h') := by
      rw [twistAut_apply, map_mul, map_inv]
    rw [e1, e2]
    have hXc : ∀ a b : ↥(normalClosure Γ L), (a : GLV V) ∈ X → (b : GLV V) ∈ X → a * b = b * a := by
      intro a b ha hb
      apply Subtype.ext
      exact hyp.X_comm _ ha _ hb
    have hXs : ∀ a : ↥(normalClosure Γ L), (a : GLV V) ∈ X → a * a = 1 := by
      intro a ha
      apply Subtype.ext
      exact hyp.X_sq _ ha
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, hXc _ _ (hcX h hh) (hcX h' hh')]
    · rw [← map_mul, hXs _ (hcX h hh), map_one]
  · rintro ⟨c, hc⟩
    exact hiso_of_twist hx2 hxH hI hf c hc

end G108Hyp

end G11

end CFSG.Quasithin
