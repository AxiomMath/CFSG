module

public import CFSG.RankThree.FFModules.ElemBestOffender
public import CFSG.RankThree.FFModules.RepMulAut
public import CFSG.Quasithin.Background.Module
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.RankThree.FFModules

variable {X : Type*} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_fixV_map_repMulAut {ρ : Representation (ZMod 2) X W} {A : Subgroup X}
    {v : Multiplicative W} :
    v ∈ CFSG.Quasithin.fixV (A.map (repMulAut ρ)) ↔
      Multiplicative.toAdd v ∈ fixSub ρ A := by
  rw [CFSG.Quasithin.mem_fixV, mem_fixSub]
  constructor
  · intro h a ha
    exact congrArg Multiplicative.toAdd (h _ (Subgroup.mem_map_of_mem _ ha))
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    exact Multiplicative.toAdd.injective (h a ha)

theorem card_fixSub_eq_card_fixV_map (ρ : Representation (ZMod 2) X W) (B : Subgroup X) :
    Nat.card (fixSub ρ B) =
      Nat.card (CFSG.Quasithin.fixV (B.map (repMulAut ρ))) :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun _ => mem_fixV_map_repMulAut.symm)

theorem card_map_repMulAut {ρ : Representation (ZMod 2) X W} (hρ : Function.Injective ρ)
    (B : Subgroup X) : Nat.card (B.map (repMulAut ρ)) = Nat.card B :=
  Subgroup.card_map_of_injective (repMulAut_injective hρ)

theorem isFFStarOffender_map_iff {ρ : Representation (ZMod 2) X W} (hρ : Function.Injective ρ)
    {A : Subgroup X} {Y : Subgroup (MulAut (Multiplicative W))}
    (hY : A.map (repMulAut ρ) ≤ Y) :
    CFSG.Quasithin.IsFFStarOffender Y (A.map (repMulAut ρ)) ↔
      A ≠ ⊥ ∧ IsElemBestOffender ρ A := by
  set f := repMulAut ρ
  have hfinj : Function.Injective f := repMulAut_injective hρ
  have hne : A.map f = ⊥ ↔ A = ⊥ :=
    ⟨fun h0 => Subgroup.map_injective hfinj (h0.trans (Subgroup.map_bot _).symm),
      fun h0 => h0 ▸ Subgroup.map_bot _⟩
  have hweight : ∀ C : Subgroup X, Nat.card (C.map f) * Nat.card (CFSG.Quasithin.fixV (C.map f)) =
      Nat.card C * Nat.card (fixSub ρ C) := fun C => by
    rw [card_map_repMulAut hρ, ← card_fixSub_eq_card_fixV_map]
  constructor
  · rintro ⟨-, hA0, ⟨hcomm, hsq⟩, hbest⟩
    refine ⟨fun h => hA0 (hne.2 h), ?_, fun C hC => ?_⟩
    · have hc : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext <| hfinj <| by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hcomm _ (Subgroup.mem_map_of_mem f x.2) _ (Subgroup.mem_map_of_mem f y.2)
      have hs : ∀ x : A, x ^ 2 = 1 := fun x => Subtype.ext <| hfinj <| by
        rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
        exact hsq _ (Subgroup.mem_map_of_mem f x.2)
      exact { is_comm := ⟨hc⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
    · have := hbest (C.map f) (Subgroup.map_mono hC)
      rwa [hweight, hweight] at this
  · rintro ⟨hA0, hA, hbest⟩
    refine ⟨hY, fun h => hA0 (hne.1 h), ⟨?_, ?_⟩, fun B hB => ?_⟩
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      have hxy : x * y = y * x := congrArg Subtype.val (hA.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, hxy]
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
    · have hBr : B ≤ f.range := hB.trans (Subgroup.map_le_range f A)
      have hCB : (B.comap f).map f = B := by
        rw [Subgroup.map_comap_eq, inf_eq_right.mpr hBr]
      have hCA : B.comap f ≤ A := by
        intro x hx
        obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp (hB (Subgroup.mem_comap.mp hx))
        exact hfinj hfa ▸ ha
      have := hbest _ hCA
      rwa [← hweight, ← hweight, hCB] at this

theorem map_repMulAut_le_range (ρ : Representation (ZMod 2) X W) (A : Subgroup X) :
    A.map (repMulAut ρ) ≤ (repMulAut ρ).range :=
  Subgroup.map_le_range _ A

theorem isFFStarOffender_map {ρ : Representation (ZMod 2) X W} (hρ : Function.Injective ρ)
    {A : Subgroup X} (hA : CFSG.IsElementaryAbelian 2 A) (hne : A ≠ ⊥)
    (h : IsBestOffender ρ A) :
    CFSG.Quasithin.IsFFStarOffender (repMulAut ρ).range
      (A.map (repMulAut ρ)) :=
  (isFFStarOffender_map_iff hρ (map_repMulAut_le_range ρ A)).2 ⟨hne, hA, h⟩

theorem isSubnormal_map {G K : Type*} [Group G] [Group K] (f : G →* K) {L M : Subgroup G}
    (h : CFSG.Open.IsSubnormal L M) : CFSG.Open.IsSubnormal (L.map f) (M.map f) :=
  CFSG.Open.IsSubnormal.map f h

theorem isQuasisimple_of_mulEquiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple K :=
  hG.of_mulEquiv e.symm

theorem isComponentOf_map {Y : Type*} [Group Y] (f : X →* Y) (hf : Function.Injective f)
    {K : Subgroup X} (h : CFSG.Open.IsComponentOf K ⊤) :
    CFSG.Open.IsComponentOf (K.map f) f.range := by
  obtain ⟨_, hsn, hqs⟩ := h
  refine ⟨?_, ?_, isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective K f hf) hqs⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hy
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  · have hs' := isSubnormal_map f hsn
    rw [← MonoidHom.range_eq_map] at hs'
    exact hs'

section AutRep

@[expose, instance_reducible] noncomputable def moduleOfSq {E : Type*} [CommGroup E]
    (h : ∀ e : E, e ^ 2 = 1) : Module (ZMod 2) (Additive E) :=
  AddCommGroup.zmodModule (fun x => toMul_eq_one.mp (h x.toMul))

variable (E : Type*) [CommGroup E] [Module (ZMod 2) (Additive E)]

@[expose] noncomputable def autRep : Representation (ZMod 2) (MulAut E) (Additive E) where
  toFun φ := (MulEquiv.toAdditive φ).toAddMonoidHom.toZModLinearMap 2
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

variable {E}

theorem autRep_apply (φ : MulAut E) (w : Additive E) :
    autRep E φ w = Additive.ofMul (φ w.toMul) :=
  rfl

theorem autRep_injective : Function.Injective (autRep E) := by
  intro φ ψ h
  ext e
  exact congrArg (fun f : Module.End (ZMod 2) (Additive E) => (f (Additive.ofMul e)).toMul) h

theorem mem_fixSub_autRep_comp {Q : Type*} [Group Q] (ι : Q →* MulAut E) (B : Subgroup Q)
    (w : Additive E) :
    w ∈ fixSub ((autRep E).comp ι) B ↔ w.toMul ∈ CFSG.Quasithin.fixV (B.map ι) := by
  rw [mem_fixSub, CFSG.Quasithin.mem_fixV]
  constructor
  · intro h x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    exact congrArg Additive.toMul (h b hb)
  · intro h b hb
    exact Additive.toMul.injective (h _ (Subgroup.mem_map_of_mem _ hb))

theorem card_fixSub_autRep_comp {Q : Type*} [Group Q] (ι : Q →* MulAut E) (B : Subgroup Q) :
    Nat.card (fixSub ((autRep E).comp ι) B) = Nat.card (CFSG.Quasithin.fixV (B.map ι)) :=
  Nat.card_congr
    { toFun := fun w => ⟨w.1.toMul, (mem_fixSub_autRep_comp ι B w.1).1 w.2⟩
      invFun := fun v => ⟨Additive.ofMul v.1, (mem_fixSub_autRep_comp ι B _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fixSub_autRep (S : Subgroup (MulAut E)) (B : Subgroup S) :
    Nat.card (fixSub ((autRep E).comp S.subtype) B) =
      Nat.card (CFSG.Quasithin.fixV (B.map S.subtype)) :=
  card_fixSub_autRep_comp S.subtype B

end AutRep

end CFSG.RankThree.FFModules

end
