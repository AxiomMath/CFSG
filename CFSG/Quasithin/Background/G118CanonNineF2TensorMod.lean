module

public import CFSG.Quasithin.Background.G116IIIA5
public import CFSG.Quasithin.Background.G118Alt
public import CFSG.Quasithin.Background.G118CanonNineF2TensorPerm
public import CFSG.Quasithin.Background.G118CanonNineF2TensorPts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Intertwines (H : Subgroup (GLV V)) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (B : Submodule (ZMod 2) V) (ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5)) : Prop :=
  ∀ (γ : ↥H) (v w : ↥B), (w : V) = (γ : GLV V) (v : V) →
    (ι w : Fin 5 → ZMod 2) =
      permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ι v)

theorem exists_intertwines (hAut : G118.AutA5Input) {H : Subgroup (GLV V)}
    {B : Submodule (ZMod 2) V} (hB : IsA5Module H B) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) :
    ∃ ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5), Intertwines H φ B ι := by
  obtain ⟨φ₀, ψ₀, h₀⟩ := hB
  obtain ⟨s, hs⟩ := hAut.2 (φ.symm.trans φ₀)
  have hφ₀ : ∀ γ : ↥H, ((φ₀ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      s * ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * s⁻¹ := by
    intro γ
    have h1 : (MulAut.conjNormal s) (φ γ) = φ₀ γ := by
      rw [hs]
      simp
    rw [← h1, MulAut.conjNormal_apply]
  refine ⟨ψ₀.trans (permActLin 5 s⁻¹), ?_⟩
  intro γ v w hvw
  have h2 := h₀ γ v w hvw
  show permAct s⁻¹ (ψ₀ w : Fin 5 → ZMod 2) =
    permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
      (permAct s⁻¹ (ψ₀ v : Fin 5 → ZMod 2))
  rw [h2, hφ₀ γ, ← permAct_mul', ← permAct_mul']
  congr 1
  group

theorem exists_intertwines_conj {H : Subgroup (GLV V)} {φ : ↥H ≃* ↥(alternatingGroup (Fin 5))}
    {B : Submodule (ZMod 2) V} (hB : ∃ ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5), Intertwines H φ B ι)
    {c : GLV V} (hc : ∀ h ∈ H, h * c = c * h) :
    ∃ ι : ↥(conjSub c B) ≃ₗ[ZMod 2] ↥(permCore 5), Intertwines H φ (conjSub c B) ι := by
  obtain ⟨ι, hι⟩ := hB
  let e : ↥B ≃ₗ[ZMod 2] ↥(conjSub c B) :=
    Submodule.equivMapOfInjective (c : V →ₗ[ZMod 2] V) c.injective B
  refine ⟨e.symm.trans ι, ?_⟩
  intro γ v w hvw
  obtain ⟨v₀, rfl⟩ := e.surjective v
  obtain ⟨w₀, rfl⟩ := e.surjective w
  have hcoe : ∀ x : ↥B, ((e x : ↥(conjSub c B)) : V) = c (x : V) := fun x => rfl
  have hw : (w₀ : V) = (γ : GLV V) (v₀ : V) := by
    apply c.injective
    rw [← hcoe, hvw, hcoe]
    exact congrArg (fun g : GLV V => g (v₀ : V)) (hc γ γ.2)
  simpa using hι γ v₀ w₀ hw

theorem exists_moved {H : Subgroup (GLV V)} {φ : ↥H ≃* ↥(alternatingGroup (Fin 5))}
    {B : Submodule (ZMod 2) V} {ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5)} (hι : Intertwines H φ B ι) :
    ∃ γ : ↥H, ∃ v : ↥B, (γ : GLV V) (v : V) ≠ (v : V) := by
  have hσ₀ : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  let y₀ : ↥(permCore 5) :=
    ⟨![1, 1, 0, 0, 0], by show ∑ i, (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) i = 0; decide⟩
  refine ⟨φ.symm ⟨_, hσ₀⟩, ι.symm y₀, fun h => ?_⟩
  have h1 := hι (φ.symm ⟨_, hσ₀⟩) (ι.symm y₀) (ι.symm y₀) h.symm
  rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  have h2 : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) =
      permAct (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) ![1, 1, 0, 0, 0] := h1
  revert h2
  decide

variable [Finite V] {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem irrPlus_of_intertwines (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) (hHI : Invariant H I)
    {φ : ↥H ≃* ↥(alternatingGroup (Fin 5))} {ι : ↥I ≃ₗ[ZMod 2] ↥(permCore 5)}
    (hι : Intertwines H φ I ι) : IrrPlus H I := by
  have h4 := finrank_I D hU hdim
  have hirr : ∀ {J : Submodule (ZMod 2) V}, Invariant H J → J ≤ I → J = ⊥ ∨ J = I :=
    fun {J} hJ hJI => irr_of_finrank_four D hU hdim h4 hJ hJI
  obtain ⟨γ, v, hγv⟩ := exists_moved hι
  have hnorm : ∀ k' ∈ H, ∀ k ∈ H, k' * k * k'⁻¹ ∈ H := fun k' hk' k hk =>
    H.mul_mem (H.mul_mem hk' hk) (H.inv_mem hk')
  have hfix : fixedSpace H ⊓ I = ⊥ := by
    have hinv : Invariant H (fixedSpace H ⊓ I) := (invariant_fixedSpace hnorm).inf hHI
    rcases hirr hinv inf_le_right with h | h
    · exact h
    · exfalso
      have hv : (v : V) ∈ fixedSpace H ⊓ I := by
        rw [h]
        exact v.2
      exact hγv ((mem_fixedSpace_iff.1 hv.1) γ γ.2)
  have hcomm : commSpace H I = I := by
    have hinv : Invariant H (commSpace H I) := invariant_commSpace hnorm hHI
    rcases hirr hinv (commSpace_le_of_invariant hHI) with h | h
    · exfalso
      rw [commSpace_eq_bot_iff] at h
      exact hγv (h γ γ.2 v v.2)
    · exact h
  refine ⟨hHI, hcomm, ?_⟩
  rw [hfix]
  refine ⟨bot_lt_iff_ne_bot.2 fun h => ?_, fun J hJ _ hJI => hirr hJ hJI⟩
  rw [h, finrank_bot] at h4
  omega

theorem inf_sup_conj (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) {B : Submodule (ZMod 2) V}
    (h4 : Module.finrank (ZMod 2) B = 4) {c : GLV V} (hcH : ∀ h ∈ H, h * c = c * h)
    (hne : conjSub c B ≠ B) (hB : Invariant H B) :
    B ⊓ conjSub c B = ⊥ ∧ B ⊔ conjSub c B = ⊤ := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcB : Invariant H (conjSub c B) := by
    intro h hh u hu
    obtain ⟨b, hb, rfl⟩ := hu
    have h1 : h (c b) = c (h b) := congrArg (fun g : GLV V => g b) (hcH h hh)
    show h (c b) ∈ conjSub c B
    rw [h1]
    exact apply_mem_conjSub (hB h hh b hb)
  have hinv : Invariant H (B ⊓ conjSub c B) := hB.inf hcB
  have hbot : B ⊓ conjSub c B = ⊥ := by
    rcases irr_of_finrank_four D hU hdim h4 hinv inf_le_left with h | h
    · exact h
    · exfalso
      apply hne
      have hle : B ≤ conjSub c B := by
        have := (inf_le_right : B ⊓ conjSub c B ≤ conjSub c B)
        rwa [h] at this
      exact (Submodule.eq_of_le_of_finrank_eq hle (finrank_conjSub c B).symm).symm
  refine ⟨hbot, Submodule.eq_top_of_finrank_eq ?_⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq B (conjSub c B)
  rw [hbot, finrank_bot, finrank_conjSub, h4] at h
  rw [hdim]
  omega

theorem dcompat {H : Subgroup (GLV V)} {φ : ↥H ≃* ↥(alternatingGroup (Fin 5))}
    {B : Submodule (ZMod 2) V} {ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5)}
    (hι : Intertwines H φ B ι) (hB : Invariant H B) {d : GLV V} (hdB : ∀ b ∈ B, d b ∈ B)
    (hN : ∀ h ∈ H, d * h * d⁻¹ ∈ H) (s : Equiv.Perm (Fin 5))
    (hσ : ∀ (h g : ↥H), (g : GLV V) = d * (h : GLV V) * d⁻¹ →
      ((φ g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        s * ((φ h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * s⁻¹) (b : ↥B) :
    ((ι ⟨d (b : V), hdB b b.2⟩ : ↥(permCore 5)) : Fin 5 → ZMod 2) = permAct s (ι b) := by
  let dB : ↥B →ₗ[ZMod 2] ↥B := (d : V →ₗ[ZMod 2] V).restrict hdB
  let T : ↥(permCore 5) →ₗ[ZMod 2] ↥(permCore 5) := ι.toLinearMap ∘ₗ dB ∘ₗ ι.symm.toLinearMap
  let S : ↥(permCore 5) →ₗ[ZMod 2] ↥(permCore 5) := (permActLin 5 s⁻¹).toLinearMap ∘ₗ T
  have hT : ∀ b : ↥B, T (ι b) = ι ⟨d (b : V), hdB b b.2⟩ := by
    intro b
    show ι (dB (ι.symm (ι b))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hSapp : ∀ y, S y = permActLin 5 s⁻¹ (T y) := fun y => rfl
  have hS : ∀ σ' : ↥(alternatingGroup (Fin 5)), ∀ y y' : ↥(permCore 5),
      (y' : Fin 5 → ZMod 2) = permAct (σ' : Equiv.Perm (Fin 5)) (y : Fin 5 → ZMod 2) →
      (S y' : Fin 5 → ZMod 2) = permAct (σ' : Equiv.Perm (Fin 5)) (S y : Fin 5 → ZMod 2) := by
    intro σ' y y' hyy'
    obtain ⟨γ, rfl⟩ := φ.surjective σ'
    obtain ⟨b, rfl⟩ := ι.surjective y
    have hγb : (γ : GLV V) (b : V) ∈ B := hB γ γ.2 b b.2
    have hy' : y' = ι ⟨(γ : GLV V) (b : V), hγb⟩ := by
      apply Subtype.ext
      rw [hyy']
      exact (hι γ b ⟨_, hγb⟩ rfl).symm
    set g : ↥H := ⟨d * (γ : GLV V) * d⁻¹, hN γ γ.2⟩ with hg
    have hdγ : d ((γ : GLV V) (b : V)) = (g : GLV V) (d (b : V)) := by
      show d ((γ : GLV V) (b : V)) = (d * (γ : GLV V) * d⁻¹) (d (b : V))
      simp [LinearEquiv.mul_apply]
    have hdb : d (b : V) ∈ B := hdB b b.2
    have hgdb : (g : GLV V) (d (b : V)) ∈ B := hB g g.2 _ hdb
    have h1 : (T y' : Fin 5 → ZMod 2) =
        permAct ((φ g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (T (ι b) : Fin 5 → ZMod 2) := by
      rw [hy', hT, hT b]
      have h2 : (⟨d ((γ : GLV V) (b : V)), hdB _ hγb⟩ : ↥B) =
          ⟨(g : GLV V) (d (b : V)), hgdb⟩ := Subtype.ext hdγ
      rw [h2]
      exact hι g ⟨d (b : V), hdb⟩ ⟨(g : GLV V) (d (b : V)), hgdb⟩ rfl
    have h3 := hσ γ g rfl
    have h4 : (S y' : Fin 5 → ZMod 2) = permAct s⁻¹ (T y' : Fin 5 → ZMod 2) := by
      rw [hSapp]
      rfl
    have h5 : (S (ι b) : Fin 5 → ZMod 2) = permAct s⁻¹ (T (ι b) : Fin 5 → ZMod 2) := by
      rw [hSapp]
      rfl
    rw [h4, h5, h1, h3, ← permAct_mul', ← permAct_mul']
    congr 1
    group
  obtain ⟨a, ha⟩ := permCore_five_endo_scalar S hS
  have hS0 : ∀ y, S y = 0 → y = 0 := by
    intro y hy
    rw [hSapp] at hy
    have h1 : T y = 0 := (LinearEquiv.map_eq_zero_iff (permActLin 5 s⁻¹)).1 hy
    have h2 : dB (ι.symm y) = 0 := (LinearEquiv.map_eq_zero_iff ι).1 h1
    have h3 : d ((ι.symm y : ↥B) : V) = 0 := congrArg Subtype.val h2
    have h4 : ((ι.symm y : ↥B) : V) = 0 := (LinearEquiv.map_eq_zero_iff d).1 h3
    have h5 : ι.symm y = 0 := Subtype.ext h4
    rw [← LinearEquiv.apply_symm_apply ι y, h5, map_zero]
  have ha1 : a = 1 := by
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with h0 | h1
    · exfalso
      let y₀ : ↥(permCore 5) :=
        ⟨![1, 1, 0, 0, 0], by show ∑ i, (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) i = 0; decide⟩
      have hy₀ : y₀ = 0 := hS0 y₀ (by rw [ha, h0, zero_smul])
      have := congrArg (fun z : ↥(permCore 5) => (z : Fin 5 → ZMod 2) 0) hy₀
      revert this
      decide
    · exact h1
  have hSb : ∀ y, S y = y := fun y => by rw [ha, ha1, one_smul]
  have hTb : T (ι b) = permActCore 5 s (ι b) := by
    calc T (ι b) = permActCore 5 s (permActCore 5 s⁻¹ (T (ι b))) := by
          rw [← permActCore_mul, mul_inv_cancel, permActCore_one]
      _ = permActCore 5 s (S (ι b)) := rfl
      _ = permActCore 5 s (ι b) := by rw [hSb]
  rw [← hT b, hTb]
  rfl

end F2Tensor

end Canon

end G11

end CFSG.Quasithin
