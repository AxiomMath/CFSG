module

public import CFSG.Quasithin.SteinbergCBI16Central
public import CFSG.Quasithin.SteinbergCBG2TwoBits

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n k : ℕ}

@[expose] def pv (σ : Perm (Fin n)) : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) where
  toFun x i := x (σ⁻¹ i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pv_apply (σ : Perm (Fin n)) (x : Fin n → ZMod 2) (i : Fin n) :
    pv σ x i = x (σ⁻¹ i) := rfl

theorem pv_mul (σ τ : Perm (Fin n)) (x : Fin n → ZMod 2) : pv (σ * τ) x = pv σ (pv τ x) := by
  funext i
  simp only [pv_apply, mul_inv_rev, Perm.mul_apply]

theorem sum_pv (σ : Perm (Fin n)) (x : Fin n → ZMod 2) : ∑ i, pv σ x i = ∑ i, x i :=
  Equiv.sum_comp σ⁻¹ x

theorem pv_const (σ : Perm (Fin n)) (c : ZMod 2) : pv σ (fun _ => c) = fun _ => c := rfl

structure DnCoords (n k : ℕ) where
  proj : (Fin n → ZMod 2) →+ (Fin k → ZMod 2)
  incl : (Fin k → ZMod 2) →+ (Fin n → ZMod 2)
  sum_incl : ∀ y, ∑ i, incl y i = 0
  proj_incl : ∀ y, proj (incl y) = y
  ker_proj : ∀ x : Fin n → ZMod 2, ∑ i, x i = 0 → proj x = 0 → x = 0 ∨ x = fun _ => 1
  proj_one : ∑ _i : Fin n, (1 : ZMod 2) = 0 → proj (fun _ => 1) = 0

@[expose] def DnCoords.ofCodes (proj : (Fin n → ZMod 2) →+ (Fin k → ZMod 2))
    (incl : (Fin k → ZMod 2) →+ (Fin n → ZMod 2))
    (h1 : ∀ c < 2 ^ k, ∑ i, incl (G2Two.toV k c) i = 0)
    (h2 : ∀ c < 2 ^ k, proj (incl (G2Two.toV k c)) = G2Two.toV k c)
    (h3 : ∀ c < 2 ^ n, ∑ i, G2Two.toV n c i = 0 → proj (G2Two.toV n c) = 0 →
      G2Two.toV n c = 0 ∨ G2Two.toV n c = fun _ => 1)
    (h4 : ∑ _i : Fin n, (1 : ZMod 2) = 0 → proj (fun _ => 1) = 0) : DnCoords n k where
  proj := proj
  incl := incl
  sum_incl y := by
    obtain ⟨c, hc, rfl⟩ := G2Two.toV_surj y
    exact h1 c hc
  proj_incl y := by
    obtain ⟨c, hc, rfl⟩ := G2Two.toV_surj y
    exact h2 c hc
  ker_proj x := by
    obtain ⟨c, hc, rfl⟩ := G2Two.toV_surj x
    exact h3 c hc
  proj_one := h4

namespace DnCoords

variable (C : DnCoords n k)

theorem proj_pv_incl_proj (σ : Perm (Fin n)) {x : Fin n → ZMod 2} (hx : ∑ i, x i = 0) :
    C.proj (pv σ (C.incl (C.proj x))) = C.proj (pv σ x) := by
  set d := x - C.incl (C.proj x) with hd
  have hsd : ∑ i, d i = 0 := by
    rw [hd]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hx, C.sum_incl, sub_self]
  have hpd : C.proj d = 0 := by
    rw [hd, map_sub, C.proj_incl, sub_self]
  have hx' : x = C.incl (C.proj x) + d := by
    rw [hd]
    abel
  rcases C.ker_proj d hsd hpd with h0 | h1
  · rw [h0, add_zero] at hx'
    rw [← hx']
  · have h1' : ∑ _i : Fin n, (1 : ZMod 2) = 0 := by
      rw [h1] at hsd
      exact hsd
    conv_rhs => rw [hx']
    rw [map_add, map_add, h1, pv_const, C.proj_one h1', add_zero]

@[expose] def act : Perm (Fin n) →* AddMonoid.End (Fin k → ZMod 2) where
  toFun σ := (C.proj.comp (pv σ)).comp C.incl
  map_one' := AddMonoidHom.ext fun y => C.proj_incl y
  map_mul' σ τ := AddMonoidHom.ext fun y => by
    change C.proj (pv (σ * τ) (C.incl y)) = C.proj (pv σ (C.incl (C.proj (pv τ (C.incl y)))))
    rw [C.proj_pv_incl_proj σ (by rw [sum_pv]; exact C.sum_incl y), pv_mul]

theorem act_proj (σ : Perm (Fin n)) {x : Fin n → ZMod 2} (hx : ∑ i, x i = 0) :
    C.act σ (C.proj x) = C.proj (pv σ x) :=
  C.proj_pv_incl_proj σ hx

@[expose] def actA : ↥(alternatingGroup (Fin n)) →* AddMonoid.End (Fin k → ZMod 2) :=
  C.act.comp (alternatingGroup (Fin n)).subtype

theorem actA_apply (σ : ↥(alternatingGroup (Fin n))) (y : Fin k → ZMod 2) :
    C.actA σ y = C.proj (pv (σ : Perm (Fin n)) (C.incl y)) := rfl

theorem toAdd_of_mem_zpowers {x : G6.PermMod n} (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) :
    Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = fun _ => 1 := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hz : Multiplicative.toAdd (G6.allOnes n ^ z) = fun _ => ((z : ℤ) : ZMod 2) := by
    rw [toAdd_zpow]
    funext i
    change z • (1 : ZMod 2) = _
    rw [zsmul_eq_mul, mul_one]
  rw [hz]
  rcases h2 (z : ZMod 2) with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]

@[expose] def secVec (m : ↥(FFModel.altDn n).sec) : Fin n → ZMod 2 :=
  Multiplicative.toAdd (α := Fin n → ZMod 2) m.1

theorem sum_secVec (m : ↥(FFModel.altDn n).sec) : ∑ i, secVec m i = 0 :=
  G6.mem_coreMod.1 m.2

@[expose] def secHom : ↥(FFModel.altDn n).sec →* Multiplicative (Fin k → ZMod 2) where
  toFun m := Multiplicative.ofAdd (C.proj (secVec m))
  map_one' := by
    change Multiplicative.ofAdd (C.proj 0) = 1
    rw [map_zero]
    rfl
  map_mul' m m' := by
    change Multiplicative.ofAdd (C.proj (secVec m + secVec m')) = _
    rw [map_add]
    rfl

theorem secHom_eq_one {m : ↥(FFModel.altDn n).sec}
    (hm : (m.1 : G6.PermMod n) ∈ Subgroup.zpowers (G6.allOnes n)) : C.secHom m = 1 := by
  change Multiplicative.ofAdd (C.proj (secVec m)) = 1
  have hs := sum_secVec m
  have h : secVec m = 0 ∨ secVec m = fun _ => 1 := toAdd_of_mem_zpowers hm
  rcases h with h | h
  · rw [h, map_zero]
    rfl
  · rw [h] at hs ⊢
    rw [C.proj_one hs]
    rfl

theorem mem_ker_of_proj {m : ↥(FFModel.altDn n).sec} (hm : C.proj (secVec m) = 0) :
    (m.1 : G6.PermMod n) ∈ Subgroup.zpowers (G6.allOnes n) := by
  rcases C.ker_proj _ (sum_secVec m) hm with h | h
  · have : (m.1 : G6.PermMod n) = 1 := Multiplicative.toAdd.injective h
    rw [this]
    exact Subgroup.one_mem _
  · have : (m.1 : G6.PermMod n) = G6.allOnes n := Multiplicative.toAdd.injective h
    rw [this]
    exact Subgroup.mem_zpowers _

@[expose] noncomputable def secEquiv :
    (FFModel.altDn n).Sec ≃* Multiplicative (Fin k → ZMod 2) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift ((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) C.secHom
      fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx
        exact C.secHom_eq_one (Subgroup.mem_inf.1 hx).1)
    ⟨fun x y hxy => by
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨C.mem_ker_of_proj ?_, (x⁻¹ * y).2⟩
      have h : C.proj (secVec x) = C.proj (secVec y) := congrArg Multiplicative.toAdd hxy
      change C.proj (-secVec x + secVec y) = 0
      rw [map_add, map_neg, h, neg_add_cancel],
    fun z => ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (C.incl (Multiplicative.toAdd z)),
      G6.mem_coreMod.2 (C.sum_incl _)⟩, by
        rw [QuotientGroup.lift_mk]
        change Multiplicative.ofAdd (C.proj (C.incl (Multiplicative.toAdd z))) = z
        exact (congrArg Multiplicative.ofAdd (C.proj_incl _)).trans (ofAdd_toAdd z)⟩⟩

@[expose] noncomputable def coordEquiv : Additive (FFModel.altDn n).Sec ≃+ (Fin k → ZMod 2) :=
  (MulEquiv.toAdditive C.secEquiv).trans (AddEquiv.additiveMultiplicative _)

theorem coordEquiv_mk (m : ↥(FFModel.altDn n).sec) :
    C.coordEquiv (Additive.ofMul (QuotientGroup.mk m : (FFModel.altDn n).Sec)) =
      C.proj (secVec m) := rfl

theorem permAct_allOnes (σ : Perm (Fin n)) : G6.permAct n σ (G6.allOnes n) = G6.allOnes n :=
  rfl

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem intertwiner_of_witness {ρ : Representation (ZMod 2) Γ W}
    {θ : Γ ≃* ↥(alternatingGroup (Fin n))} {β : W ≃+ Additive (FFModel.altDn n).Sec}
    (h : (FFModel.altDn n).Witness ρ θ β) (γ : Γ) (w : W) :
    (β.trans C.coordEquiv) (ρ γ w) = C.actA (θ γ) ((β.trans C.coordEquiv) w) := by
  obtain ⟨-, hsec, -, hint⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (Additive.toMul (β w))
  have hw : β w = Additive.ofMul (QuotientGroup.mk m : (FFModel.altDn n).Sec) := by
    rw [hm]
    rfl
  have hm' : (FFModel.altDn n).act (θ γ) m ∈ (FFModel.altDn n).sec := hsec _ _ m.2
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hint γ w m hm' hw, hw, C.coordEquiv_mk,
    C.coordEquiv_mk]
  exact (C.act_proj (θ γ : Perm (Fin n)) (sum_secVec m)).symm

theorem witness_of_intertwiner {ρ : Representation (ZMod 2) Γ W}
    {θ : Γ ≃* ↥(alternatingGroup (Fin n))} {e : W ≃+ (Fin k → ZMod 2)}
    (he : ∀ γ w, e (ρ γ w) = C.actA (θ γ) (e w)) :
    (FFModel.altDn n).Witness ρ θ (e.trans C.coordEquiv.symm) := by
  refine ⟨inf_le_right, fun g m hm => G6.permAct_mem_coreMod _ hm, fun g m hm => ?_, ?_⟩
  · have hm' : m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := hm
    obtain ⟨hz, hc⟩ := Subgroup.mem_inf.1 hm'
    change G6.permAct n (g.1 : Perm (Fin n)) m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n
    refine Subgroup.mem_inf.2 ⟨?_, G6.permAct_mem_coreMod _ hc⟩
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have e : G6.permAct n g.1 (G6.allOnes n ^ z) = G6.allOnes n ^ z :=
      (map_zpow (G6.permAct n g.1) (G6.allOnes n) z).trans
        (congrArg (· ^ z) (permAct_allOnes g.1))
    exact (congrArg (· ∈ Subgroup.zpowers (G6.allOnes n)) e).mpr (Subgroup.zpow_mem_zpowers _ _)
  · intro γ w m hm hw
    apply C.coordEquiv.injective
    have hw' : e w = C.proj (secVec m) := by
      have := congrArg C.coordEquiv hw
      rwa [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, C.coordEquiv_mk] at this
    rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, C.coordEquiv_mk, he, hw']
    exact C.act_proj _ (sum_secVec m)

theorem exists_intertwiner {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ n .alternating) :
    ∃ (θ : Γ ≃* ↥(alternatingGroup (Fin n))) (e : W ≃+ (Fin k → ZMod 2)),
      ∀ γ w, e (ρ γ w) = C.actA (θ γ) (e w) := by
  obtain ⟨α, θ, β, hw⟩ := h
  exact ⟨θ.trans α, β.trans C.coordEquiv, C.intertwiner_of_witness hw⟩

theorem alternatingNatural_of_intertwiner {ρ : Representation (ZMod 2) Γ W}
    {θ : Γ ≃* ↥(alternatingGroup (Fin n))} {e : W ≃+ (Fin k → ZMod 2)}
    (he : ∀ γ w, e (ρ γ w) = C.actA (θ γ) (e w)) :
    Explicit.AlternatingNatural ρ n .alternating :=
  ⟨MulEquiv.refl _, θ, e.trans C.coordEquiv.symm,
    C.witness_of_intertwiner (θ := θ.trans (MulEquiv.refl _)) he⟩

@[expose] def f0 (p : Fin n) (σ : Perm (Fin n)) : Fin k → ZMod 2 :=
  C.proj (pv σ (Pi.single p 1) - Pi.single p 1)

theorem f0_mem (p : Fin n) :
    (fun g : ↥(alternatingGroup (Fin n)) => C.f0 p (g : Perm (Fin n))) ∈ Z1A C.actA := by
  intro g h
  set e : Fin n → ZMod 2 := Pi.single p 1
  change C.proj (pv ((g : Perm (Fin n)) * (h : Perm (Fin n))) e - e) =
    C.proj (pv (g : Perm (Fin n)) e - e) + C.act (g : Perm (Fin n))
      (C.proj (pv (h : Perm (Fin n)) e - e))
  have hs : ∑ i, (pv (h : Perm (Fin n)) e - e) i = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_pv, sub_self]
  rw [C.act_proj _ hs, pv_mul, map_sub (pv _), map_sub, map_sub, map_sub]
  abel

theorem finrank_H1_eq_zero {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ n .alternating) (hZ : Z1A C.actA ≤ B1A C.actA) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨θ, e, he⟩ := C.exists_intertwiner h
  exact finrank_H1_eq_zero_of_le fun f hf =>
    (transport_mem_B1A he).1 (hZ ((transport_mem_Z1A he).2 hf))

theorem finrank_H1_eq_one {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ n .alternating)
    (hZ : Nat.card (Z1A C.actA) = 2 * Nat.card (B1A C.actA)) :
    Module.finrank (ZMod 2) (H1 ρ) = 1 := by
  obtain ⟨θ, e, he⟩ := C.exists_intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.symm.toEquiv
  have : Finite W := Finite.of_equiv _ e.symm.toEquiv
  exact finrank_H1_of_card ρ ((card_H1_eq_of_card ρ he hZ).trans (pow_one 2).symm)

end DnCoords

end CFSG.Quasithin.SteinbergCB.I16
