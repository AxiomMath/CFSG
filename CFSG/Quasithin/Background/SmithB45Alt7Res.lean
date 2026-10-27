module

public import CFSG.Quasithin.Background.SmithB45Alt7IndCheck
public import CFSG.Quasithin.SteinbergCBI16Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EMod

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
  CFSG.QuasithinUnique.Setup.Offender

abbrev A7 : Type := ↥(alternatingGroup (Fin 7))

@[expose] def gen7 (b : Bool) : A7 :=
  if b then SteinbergCB.I16.gens7 1 else SteinbergCB.I16.gens7 0

@[expose] def eval7 : List Bool → A7
  | [] => 1
  | b :: w => gen7 b * eval7 w

theorem closure_gen7 : Subgroup.closure (Set.range gen7) = ⊤ := by
  rw [← SteinbergCB.I16.closure_gens7]
  congr 1
  ext g
  constructor
  · rintro ⟨b, rfl⟩
    cases b
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

@[expose] def tk (k : Fin 7) : A7 := gen7 true ^ (k.val + 1)

@[expose] def fin6Equiv : Fin 6 ≃ {i : Fin 7 // i.val < 6} where
  toFun i := ⟨Fin.castSucc i, i.isLt⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def j6 : S6 →* A7 :=
  ((extendDomainHom fin6Equiv).comp (alternatingGroup (Fin 6)).subtype).codRestrict _
    fun σ => by
      rw [mem_alternatingGroup]
      change sign ((σ : Perm (Fin 6)).extendDomain fin6Equiv) = 1
      rw [sign_extendDomain]
      exact σ.2

theorem coset_rel : ∀ (b : Bool) (k : Fin 7),
    ((gen7 b * tk k : A7) : Perm (Fin 7)) =
      ((tk ((gen7 b : Perm (Fin 7)) k) * j6 (evalG (cosW b k.val)) : A7) : Perm (Fin 7)) := by
  decide +kernel

theorem gen7_apply_val :
    ∀ (b : Bool) (k : Fin 7), ((gen7 b : Perm (Fin 7)) k).val = g7N b k.val := by
  decide +kernel

section Simple

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem exists_isLSimple (σ : S6 →* (M ≃ₗ[ZMod 2] M)) (hM : (⊤ : Submodule (ZMod 2) M) ≠ ⊥) :
    ∃ U : Submodule (ZMod 2) M, IsLSimple σ ⊤ U := by
  classical
  have hex : ∃ n, ∃ U : Submodule (ZMod 2) M,
      QuasithinUnique.Setup.Offender.IsInvariant σ ⊤ U ∧ U ≠ ⊥ ∧ Nat.card U = n :=
    ⟨_, ⊤, fun _ _ _ _ => trivial, hM, rfl⟩
  obtain ⟨U, hUinv, hU0, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hUinv, hU0, fun W hW hWU => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    have hle : Nat.find hex ≤ Nat.card W := Nat.find_min' hex ⟨W, hW, hW0, rfl⟩
    have hWU' : W.toAddSubgroup ≤ U.toAddSubgroup := hWU
    have hcard : Nat.card U.toAddSubgroup ≤ Nat.card W.toAddSubgroup := by
      change Nat.card U ≤ Nat.card W
      rw [hUn]
      exact hle
    have := AddSubgroup.eq_of_le_of_card_ge hWU' hcard
    exact Submodule.toAddSubgroup_injective this

@[expose] def resRep (σ : S6 →* (M ≃ₗ[ZMod 2] M)) (U : Submodule (ZMod 2) M)
    (hU : QuasithinUnique.Setup.Offender.IsInvariant σ ⊤ U) :
    S6 →* (↥U ≃ₗ[ZMod 2] ↥U) where
  toFun g :=
    { toFun := fun u => ⟨σ g u, hU g trivial u u.2⟩
      invFun := fun u => ⟨σ g⁻¹ u, hU g⁻¹ trivial u u.2⟩
      map_add' := fun u v => Subtype.ext (map_add (σ g) (u : M) v)
      map_smul' := fun c u => Subtype.ext (map_smul (σ g) c (u : M))
      left_inv := fun u => Subtype.ext (ρ_inv_apply σ g u)
      right_inv := fun u => Subtype.ext (ρ_apply_inv σ g u) }
  map_one' := LinearEquiv.ext fun u => Subtype.ext (by simp)
  map_mul' g h := LinearEquiv.ext fun u => Subtype.ext (ρ_mul_apply σ g h u)

omit [Finite M] in
theorem resRep_isLSimple (σ : S6 →* (M ≃ₗ[ZMod 2] M)) {U : Submodule (ZMod 2) M}
    (hU : IsLSimple σ ⊤ U) : IsLSimple (resRep σ U hU.1) ⊤ ⊤ := by
  refine ⟨fun _ _ _ _ => trivial, ?_, fun W hW _ => ?_⟩
  · intro h
    apply hU.2.1
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, hu⟩ : ↥U) ∈ (⊤ : Submodule (ZMod 2) ↥U) := trivial
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h1
  · have hinv : QuasithinUnique.Setup.Offender.IsInvariant σ ⊤ (W.map U.subtype) := by
      rintro g - _ ⟨w, hw, rfl⟩
      exact ⟨_, hW g trivial w hw, rfl⟩
    rcases hU.2.2 _ hinv (Submodule.map_subtype_le U W) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have h1 : (w : M) ∈ W.map U.subtype := ⟨w, hw, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      rw [Submodule.mem_bot]
      exact Subtype.ext h1
    · right
      rw [eq_top_iff]
      intro w _
      have h1 : (w : M) ∈ W.map U.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := h1
      rw [← Subtype.ext hww']
      exact hw'

theorem exists_block_emb (σ : S6 →* (M ≃ₗ[ZMod 2] M)) (hM : (⊤ : Submodule (ZMod 2) M) ≠ ⊥) :
    ∃ i < 12, ∃ ψ : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0) →ₗ[ZMod 2] M,
      Function.Injective ψ ∧
        ∀ b s, ψ (lin (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i b) s) = σ (gen b) (ψ s) := by
  obtain ⟨U, hU⟩ := exists_isLSimple σ hM
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_iso (resRep σ U hU.1) (resRep_isLSimple σ hU)
  refine ⟨i, hi, U.subtype.comp Ψ.toLinearMap, ?_, fun b s => ?_⟩
  · exact Subtype.val_injective.comp Ψ.injective
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [hΨ b s]
    rfl

theorem inv_of_gen7 (ρ : A7 →* (M ≃ₗ[ZMod 2] M)) {U : Submodule (ZMod 2) M}
    (h : ∀ b, ∀ u ∈ U, ρ (gen7 b) u ∈ U) : ∀ γ, ∀ u ∈ U, ρ γ u ∈ U := by
  let T : Subgroup A7 :=
    { carrier := {g | ∀ u ∈ U, ρ g u ∈ U}
      mul_mem' := fun {a b} ha hb u hu => by
        rw [map_mul, LinearEquiv.mul_apply]
        exact ha _ (hb u hu)
      one_mem' := fun u hu => by simpa using hu
      inv_mem' := fun {a} ha u hu => by
        let f : U → U := fun u => ⟨ρ a u, ha u u.2⟩
        have hf : Function.Injective f := by
          intro u u' huu
          exact Subtype.ext ((ρ a).injective (congrArg Subtype.val huu))
        obtain ⟨u', hu'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
        have h1 : ρ a u' = u := congrArg Subtype.val hu'
        have h2 : ρ a⁻¹ u = u' := by rw [← h1]; exact ρ_inv_apply ρ a u'
        rw [h2]
        exact u'.2 }
  have hT : (⊤ : Subgroup A7) ≤ T := by
    rw [← closure_gen7, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact h b
  intro γ u hu
  exact hT (Subgroup.mem_top γ) u hu

end Simple

section Rep

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)] {L : Subgroup (MulAut V)}

@[expose] def rho7 (ι : ↥L ≃* A7) : A7 →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
  (CFSG.QuasithinUnique.Setup.Layer.binPsi
    (MulEquiv.multiplicativeAdditive V).symm).toMonoidHom.comp (L.subtype.comp ι.symm.toMonoidHom)

theorem rho7_apply (ι : ↥L ≃* A7) (γ : A7) (w : Additive V) :
    rho7 ι γ w = Additive.ofMul ((ι.symm γ : MulAut V) (Additive.toMul w)) := rfl

@[expose] def sigma6 (ι : ↥L ≃* A7) : S6 →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
  (rho7 ι).comp j6

theorem sigma6_apply (ι : ↥L ≃* A7) (τ : S6) (w : Additive V) :
    sigma6 ι τ w = rho7 ι (j6 τ) w := rfl

variable [Finite V]

theorem irred_gen7 (ι : ↥L ≃* A7)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) :
    IrredPair (fun b => ((rho7 ι (gen7 b) : Additive V ≃ₗ[ZMod 2] Additive V) :
      Additive V →ₗ[ZMod 2] Additive V)) := by
  intro U hU
  have hall := inv_of_gen7 (rho7 ι) (U := U) fun b u hu => hU b u hu
  let J : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ U}
      one_mem' := U.zero_mem
      mul_mem' := fun ha hb => U.add_mem ha hb
      inv_mem' := fun ha => U.neg_mem ha }
  have hinv : ∀ l ∈ L, ∀ v ∈ J, l v ∈ J := by
    intro l hl v hv
    have h1 := hall (ι ⟨l, hl⟩) (Additive.ofMul v) hv
    rw [rho7_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  rcases hirr J hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : Additive.toMul w ∈ J := hw
    rw [h, Subgroup.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact h1
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : Additive.toMul w ∈ J := by rw [h]; trivial
    exact h1

end Rep

end CFSG.Quasithin.B45Alt7
