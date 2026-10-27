module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsFrame
public import CFSG.Quasithin.H13.A6Rows1321

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace Row8

@[expose] def crdM : Matrix (Fin 6) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 1, 1, 0; 1, 1, 0, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0; 1, 1, 1, 1, 0, 0, 0, 0; 1, 1, 1, 1, 1, 1, 0, 0]

@[expose] def secM : Matrix (Fin 8) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 1, 0, 1, 1, 1, 0; 1, 1, 0, 1, 1, 0;
    1, 1, 0, 1, 0, 1; 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0]

theorem crd_sec : crdM * secM = 1 := by decide +kernel

theorem sec_even : ∀ y : Fin 6 → ZMod 2, ∑ i, (secM *ᵥ y) i = 0 := by decide +kernel

theorem crd_ker : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 → crdM *ᵥ x = 0 →
    x = 0 ∨ x = fun _ => 1 := by decide +kernel

theorem crd_one : crdM *ᵥ (fun _ : Fin 8 => (1 : ZMod 2)) = 0 := by decide +kernel

theorem sec_crd (x : Fin 8 → ZMod 2) (hx : ∑ i, x i = 0) :
    secM *ᵥ (crdM *ᵥ x) = x ∨ secM *ᵥ (crdM *ᵥ x) = x + fun _ => 1 := by
  have h1 : ∑ i, (secM *ᵥ (crdM *ᵥ x)) i = 0 := sec_even _
  have h2 : crdM *ᵥ (x + secM *ᵥ (crdM *ᵥ x)) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, crd_sec, Matrix.one_mulVec]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h3 : ∑ i, (x + secM *ᵥ (crdM *ᵥ x)) i = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, h1, add_zero]
  have key0 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have key1 : ∀ a b : ZMod 2, a + b = 1 → b = a + 1 := by decide
  rcases crd_ker _ h3 h2 with h | h
  · left
    funext i
    exact key0 _ _ (congrFun h i)
  · right
    funext i
    exact key1 _ _ (congrFun h i)

@[expose] def pm (σ : Equiv.Perm (Fin 8)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if σ⁻¹ i = j then 1 else 0

theorem pm_mulVec (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) :
    pm σ *ᵥ x = fun i => x (σ⁻¹ i) := by
  funext i
  simp [pm, Matrix.mulVec, dotProduct, ite_mul]

@[expose] def mat8 (σ : Equiv.Perm (Fin 8)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  crdM * pm σ * secM

@[expose] def crdHom : ↥(G6.coreMod 8) →* Multiplicative (Fin 6 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (crdM *ᵥ Multiplicative.toAdd x.1)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [Matrix.mulVec_add, ofAdd_add]

theorem mem_ker8 (x : ↥(G6.coreMod 8)) :
    x ∈ B5FinS8.Ker8 ↔ x.1 = 1 ∨ x.1 = G6.allOnes 8 := by
  rw [B5FinS8.Ker8, Subgroup.mem_subgroupOf, Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem crdHom_ker : B5FinS8.Ker8 ≤ crdHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases (mem_ker8 x).mp hx with h | h
  · have : Multiplicative.toAdd x.1 = 0 := by rw [h]; rfl
    simp [crdHom, this]
  · have : Multiplicative.toAdd x.1 = fun _ => 1 := by rw [h]; rfl
    simp [crdHom, this, crd_one]

@[expose] noncomputable def kappaHom : B5FinS8.Mod8 →* Multiplicative (Fin 6 → ZMod 2) :=
  QuotientGroup.lift B5FinS8.Ker8 crdHom crdHom_ker

theorem kappaHom_mk (x : ↥(G6.coreMod 8)) :
    kappaHom (QuotientGroup.mk x) = Multiplicative.ofAdd (crdM *ᵥ Multiplicative.toAdd x.1) := rfl

theorem kappaHom_bijective : Function.Bijective kappaHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [kappaHom_mk] at hq
    have h0 : crdM *ᵥ Multiplicative.toAdd x.1 = 0 := by
      have := congrArg Multiplicative.toAdd hq
      simpa using this
    have hsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
    rw [QuotientGroup.eq_one_iff, mem_ker8]
    rcases crd_ker _ hsum h0 with h | h
    · left
      exact Multiplicative.toAdd.injective (by rw [h]; rfl)
    · right
      exact Multiplicative.toAdd.injective (by rw [h]; rfl)
  · intro y
    refine ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (secM *ᵥ Multiplicative.toAdd y),
      (G6.mem_coreMod).2 (sec_even _)⟩, ?_⟩
    rw [kappaHom_mk]
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, crd_sec, Matrix.one_mulVec, ofAdd_toAdd]

@[expose] noncomputable def kappa : B5FinS8.Mod8 ≃* Multiplicative (Fin 6 → ZMod 2) :=
  MulEquiv.ofBijective kappaHom kappaHom_bijective

theorem pm_one (σ : Equiv.Perm (Fin 8)) : pm σ *ᵥ (fun _ => (1 : ZMod 2)) = fun _ => 1 := by
  rw [pm_mulVec]

theorem pm_sum (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) :
    ∑ i, (pm σ *ᵥ x) i = ∑ i, x i := by
  rw [pm_mulVec]
  exact Equiv.sum_comp σ⁻¹ x

theorem crd_perm (σ : Equiv.Perm (Fin 8)) (x : Fin 8 → ZMod 2) (hx : ∑ i, x i = 0) :
    crdM *ᵥ (pm σ *ᵥ x) = mat8 σ *ᵥ (crdM *ᵥ x) := by
  unfold mat8
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases sec_crd x hx with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, pm_one, Matrix.mulVec_add, crd_one, add_zero]

theorem kappa_aut (σ : Equiv.Perm (Fin 8)) (q : B5FinS8.Mod8) :
    Multiplicative.toAdd (kappa (D8.aut8 σ q)) = mat8 σ *ᵥ Multiplicative.toAdd (kappa q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [D8.aut8_apply, B5FinS8.act8_mk]
  change crdM *ᵥ Multiplicative.toAdd (G6.permAct 8 σ x.1) =
    mat8 σ *ᵥ (crdM *ᵥ Multiplicative.toAdd x.1)
  have h1 : Multiplicative.toAdd (G6.permAct 8 σ x.1) = pm σ *ᵥ Multiplicative.toAdd x.1 := by
    rw [pm_mulVec]
    rfl
  rw [h1]
  exact crd_perm σ _ ((G6.mem_coreMod).1 x.2)

open Equiv in
theorem alt8_data {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}
    (hrow : B42Case10 G L A) :
    ∃ (e : V ≃* B5FinS8.Mod8) (ψ : ↥(alternatingGroup (Fin 8)) →* ↥L), Function.Bijective ψ ∧
      ∀ (γ : ↥(alternatingGroup (Fin 8))) (w : V),
        e (((ψ γ : ↥L) : MulAut V) w) = D8.aut8 γ.1 (e w) := by
  obtain ⟨π, hπ⟩ := A5.alternatingNatural_eight_of_extSq hrow.1
  have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
  obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
  let e : V ≃* B5FinS8.Mod8 := e₀
  refine ⟨e, π, ⟨hinj, hπ.1⟩, fun γ w => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
  rw [← hm, D8.aut8_apply, B5FinS8.act8_mk]
  exact he₀ γ w m (G6.permAct_mem_coreMod (γ : Perm (Fin 8)) m.2) hm.symm

theorem exists_frame8 {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}
    (hrow : B42Case10 G L A) :
    ∃ fr : Frame V L ↥(alternatingGroup (Fin 8)) 6, ∀ γ, fr.mat γ = mat8 γ.1 := by
  obtain ⟨e, ψ, hψ, he⟩ := alt8_data hrow
  refine ⟨⟨e.trans kappa, ψ, hψ, fun γ => mat8 γ.1, fun γ w => ?_⟩, fun γ => rfl⟩
  show Multiplicative.toAdd (kappa (e (((ψ γ : ↥L) : MulAut V) w))) =
    mat8 γ.1 *ᵥ Multiplicative.toAdd (kappa (e w))
  rw [he, kappa_aut]

end Row8

end CFSG.Quasithin.H13.A6.GR
