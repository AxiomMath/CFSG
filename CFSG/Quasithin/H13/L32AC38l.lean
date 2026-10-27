module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.H13.L32AC38g
public import CFSG.Quasithin.H13.L32AC38h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G}

@[expose] noncomputable def tildeHom (C : Ctx38 T L V H b c)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H)) :
    ↥(conjClosure V H) →* IntMod C.Wt C.hUe where
  toFun u := IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW u.2⟩
  map_one' := IntMod.val_injective (by
    show secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨1, _⟩ = 1
    exact map_one _)
  map_mul' u v := IntMod.val_injective (by
    show secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨(u : G) * v, _⟩ =
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨u, _⟩ *
        secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨v, _⟩
    rw [← map_mul]
    rfl)

variable (C : Ctx38 T L V H b c)
include C

theorem tildeHom_val (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    (u : ↥(conjClosure V H)) :
    (C.tildeHom hW u).val =
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨u, C.HN (C.UH u.2)⟩ := rfl

theorem tildeHom_eq_one_iff (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    (u : ↥(conjClosure V H)) : C.tildeHom hW u = 1 ↔ (u : G) ∈ fsuV1 T V := by
  constructor
  · intro h
    have h1 := congrArg IntMod.val h
    rw [tildeHom_val, IntMod.val_one] at h1
    have h2 := secMk_eq_one_iff.mp h1
    exact h2
  · intro h
    apply IntMod.val_injective
    rw [tildeHom_val, IntMod.val_one]
    exact secMk_eq_one_iff.mpr h

theorem tildeHom_surjective (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H)) :
    Function.Surjective (C.tildeHom hW) := by
  intro w
  have hw : w.val ∈ tildeOf (fsuV1 T V) (conjClosure V H) := hW ▸ w.val_mem
  obtain ⟨u, hu, hue⟩ := mem_secImg.mp hw
  refine ⟨⟨u, hu⟩, IntMod.val_injective ?_⟩
  rw [tildeHom_val]
  exact hue

theorem tildeHom_conj (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H)) (k : ↥H)
    (x x' : ↥(conjClosure V H)) (hx' : (x' : G) = k * x * (k : G)⁻¹) :
    C.tildeHom hW x' = C.ψ k (C.tildeHom hW x) := by
  apply IntMod.val_injective
  rw [C.ψ_apply_val, tildeHom_val, tildeHom_val, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hx'

theorem false_of_binaryNaturalSL (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h4 : Lemma14_7_4_two_three)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hK₁ : K₁ ≤ C.ψ.range) {n : ℕ}
    (hnat : BinaryNaturalSL K₁ ⊤ ⊥ n 1) : False := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have htop := G64.BinaryNaturalSL.eq_top hnat
  obtain ⟨K₂, _, _, π₀, E, hK2, hπ₀s, hE⟩ := G64.BinaryNaturalSL.exists_equiv_vec hnat
  have hπ₀i : Function.Injective π₀ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply natAct_faithful _ γ
    intro m
    obtain ⟨v, rfl⟩ := E.surjective m
    have h1 := hE γ v
    rw [hγ] at h1
    have h2 : (((1 : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) v) = v := rfl
    rw [h2] at h1
    show Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin n) K₂) :
      Matrix (Fin n) (Fin n) K₂).mulVec (Multiplicative.toAdd (E v))) * (E v)⁻¹ = 1
    rw [← h1, ofAdd_toAdd, mul_inv_cancel]
  set ε := ringEquivZModTwo hK2 with hε
  let θ := MulEquiv.ofBijective π₀ ⟨hπ₀i, hπ₀s⟩
  have hψ1 : ∀ h : ↥H, C.ψ h ∈ K₁ := fun h => by rw [htop]; trivial
  let ψ₁ : ↥H →* ↥K₁ := C.ψ.codRestrict K₁ hψ1
  let π' : ↥H →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    (statedSLEquivZModTwo hK2).toMonoidHom.comp (θ.symm.toMonoidHom.comp ψ₁)
  have hπ' : Function.Surjective π' := by
    intro s
    obtain ⟨γ, rfl⟩ := (statedSLEquivZModTwo hK2).surjective s
    obtain ⟨h, hh⟩ := hK₁ (θ γ).2
    refine ⟨h, ?_⟩
    show statedSLEquivZModTwo hK2 (θ.symm (ψ₁ h)) = statedSLEquivZModTwo hK2 γ
    congr 1
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hh
  let εv : Multiplicative (Fin n → K₂) →* Multiplicative (Fin n → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (fun i => ε (Multiplicative.toAdd v i))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        simp }
  have hεv : Function.Injective εv := by
    intro x y h
    apply Multiplicative.toAdd.injective
    funext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    exact ε.injective this
  let β : ↥(conjClosure V H) →* Multiplicative (Fin n → ZMod 2) :=
    εv.comp (E.toMonoidHom.comp (C.tildeHom hW))
  have hβker : β.ker = (fsuV1 T V).subgroupOf (conjClosure V H) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.tildeHom_eq_one_iff hW]
    constructor
    · intro hu
      have h1 : εv (E (C.tildeHom hW u)) = εv 1 := by rw [map_one]; exact hu
      have h2 := hεv h1
      rwa [MulEquiv.map_eq_one_iff] at h2
    · intro hu
      show εv (E (C.tildeHom hW u)) = 1
      rw [hu, map_one, map_one]
  have hβ : ∀ (k : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = k * x * (k : G)⁻¹ →
      β x' = Multiplicative.ofAdd (((π' k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (β x))) := by
    intro k x x' hx'
    have h1 := C.tildeHom_conj hW k x x' hx'
    set γ := θ.symm (ψ₁ k) with hγdef
    have hγ : ((π₀ γ : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) = C.ψ k := by
      have : θ γ = ψ₁ k := θ.apply_symm_apply _
      exact congrArg Subtype.val this
    have h2 := hE γ (C.tildeHom hW x)
    rw [hγ, ← h1] at h2
    have hmat : ((π' k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
        (((γ : Matrix.GeneralLinearGroup (Fin n) K₂) : Matrix (Fin n) (Fin n) K₂)).map ε := by
      show (((slCongr (ringEquivZModTwo hK2))
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K₂).symm γ) :
          Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = _
      have hc := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K₂
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K₂).symm γ)
      rw [MulEquiv.apply_symm_apply] at hc
      rw [hc]
      rfl
    apply Multiplicative.toAdd.injective
    funext i
    show ε (Multiplicative.toAdd (E (C.tildeHom hW x')) i) =
      ((π' k : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (fun j => ε (Multiplicative.toAdd (E (C.tildeHom hW x)) j))) i
    rw [h2, hmat]
    exact RingHom.map_mulVec (ε : K₂ →+* ZMod 2)
      (((γ : Matrix.GeneralLinearGroup (Fin n) K₂) : Matrix (Fin n) (Fin n) K₂))
      (Multiplicative.toAdd (E (C.tildeHom hW x))) i
  exact false_of_slSection_H h1222 h1332 h1334 h4 C.S hV2 hπ' hβker hβ

end Ctx38

end CFSG.Quasithin.H13.L32A.C
