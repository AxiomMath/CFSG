module

public import CFSG.Sporadic.Schreier.LyR3EPointwise
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

instance lyC_isPerfect :
    Group.IsPerfect lyC := ⟨commutator_lyC⟩

@[expose] def lyCenterEquiv :
    lyC ⧸ Subgroup.center lyC ≃* alternatingGroup (Fin 11) :=
  (QuotientGroup.quotientMulEquivOfEq center_lyC).trans lyCoverEquiv

theorem card_center_lyC :
    Nat.card (Subgroup.center lyC) = 2 := by
  rw [center_lyC, zGroup, Nat.card_zpowers, orderOf_zC]

theorem alternating_eleven_not_comm :
    ∃ a b : alternatingGroup (Fin 11), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg (fun p : alternatingGroup (Fin 11) => (p : Equiv.Perm (Fin 11)) 2) h
    revert h2
    decide

theorem isQuasisimple_lyC :
    CFSG.IsQuasisimple lyC := by
  have : IsSimpleGroup (alternatingGroup (Fin 11)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨lyC_isPerfect, lyCenterEquiv.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := alternating_eleven_not_comm
  refine ⟨lyCenterEquiv.symm a, lyCenterEquiv.symm b, fun h => hab ?_⟩
  have := congrArg lyCenterEquiv h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

@[expose] def centralizerCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃* Subgroup.centralizer ({e g} : Set H) where
  toFun x := ⟨e (x : G), by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 x.2]⟩
  invFun y := ⟨e.symm (y : H), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
      Subgroup.mem_centralizer_singleton_iff.1 y.2]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : G))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : H))
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

@[expose] def centralizerConj {G : Type*} [Group G] (x g : G) :
    Subgroup.centralizer ({x * g * x⁻¹} : Set G) ≃* Subgroup.centralizer ({g} : Set G) where
  toFun y := ⟨x⁻¹ * (y : G) * x, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc x⁻¹ * (y : G) * x * g = x⁻¹ * ((y : G) * (x * g * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * g * x⁻¹) * (y : G)) * x := by rw [h]
      _ = g * (x⁻¹ * (y : G) * x) := by group⟩
  invFun y := ⟨x * (y : G) * x⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc x * (y : G) * x⁻¹ * (x * g * x⁻¹) = x * ((y : G) * g) * x⁻¹ := by group
      _ = x * (g * (y : G)) * x⁻¹ := by rw [h]
      _ = x * g * x⁻¹ * (x * (y : G) * x⁻¹) := by group⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' y w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem card_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem centerQuotient_equiv_of_mulEquiv {A B Q : Type*} [Group A] [Group B] [Group Q]
    (e : A ≃* B) (f : B ⧸ Subgroup.center B ≃* Q) : Nonempty (A ⧸ Subgroup.center A ≃* Q) :=
  ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans f⟩

theorem centralizer_equiv_of_fusion {T G : Type*} [Group T] [Group G] (e : T ≃* G) {z : G}
    (hfus : ∀ s : G, orderOf s = 2 → ∃ x : G, x * z * x⁻¹ = s) (t : T) (ht : orderOf t = 2) :
    Nonempty (Subgroup.centralizer ({t} : Set T) ≃* Subgroup.centralizer ({z} : Set G)) := by
  have hτ : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  obtain ⟨x, hx⟩ := hfus (e t) hτ
  have hcen : Subgroup.centralizer ({e t} : Set G) =
      Subgroup.centralizer ({x * z * x⁻¹} : Set G) := by rw [hx]
  exact ⟨((centralizerCongr e t).trans (MulEquiv.subgroupCongr hcen)).trans (centralizerConj x z)⟩

theorem centralizer_equiv_lyC
    {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.Ly))
    (t : T) (ht : orderOf t = 2) : Nonempty (Subgroup.centralizer ({t} : Set T) ≃* lyC) := by
  obtain ⟨e₀⟩ := hT
  obtain ⟨E⟩ := centralizer_equiv_of_fusion (T := T) (G := J) (by exact e₀.trans lyEquivJ)
    (z := lyz) (by exact involution_centralizer_fusion_generator.2) t ht
  exact ⟨E.trans (MulEquiv.subgroupCongr lyC_eq_centralizer.symm)⟩

theorem involution_centralizers_quasisimple
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly)) (t : T) (ht : orderOf t = 2) :
    CFSG.IsQuasisimple (Subgroup.centralizer ({t} : Set T)) ∧
      Nat.card (Subgroup.center (Subgroup.centralizer ({t} : Set T))) = 2 ∧
      Nonempty (Subgroup.centralizer ({t} : Set T) ⧸
        Subgroup.center (Subgroup.centralizer ({t} : Set T)) ≃* alternatingGroup (Fin 11)) := by
  obtain ⟨E⟩ := centralizer_equiv_lyC hT t ht
  have hq : CFSG.IsQuasisimple (Subgroup.centralizer ({t} : Set T)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (A := lyC) (B := Subgroup.centralizer ({t} : Set T))
      E.symm isQuasisimple_lyC
  refine ⟨hq, ?_, ?_⟩
  · rw [← card_center_lyC]
    exact card_center_eq_of_mulEquiv (A := Subgroup.centralizer ({t} : Set T)) (B := lyC) E
  · exact centerQuotient_equiv_of_mulEquiv (A := Subgroup.centralizer ({t} : Set T)) (B := lyC)
      E lyCenterEquiv

open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six) in
theorem card_outer_lyC_dvd :
    Nat.card (Outer lyC) ∣ 2 :=
  (Subgroup.card_dvd_of_injective (centerQuotientOuterHom lyC)
    (centerQuotient_outer_injective lyC)).trans
    (outer_card_dvd_two_of_equiv_outside_six (Or.inr (by norm_num)) lyCenterEquiv)

@[expose] def autZ :
    Subgroup (MulAut J) := MulAction.stabilizer (MulAut J) lyz

theorem mem_autZ
    {α : MulAut J} : α ∈ autZ ↔ α lyz = lyz := MulAction.mem_stabilizer_iff

theorem apply_mem_lyC
    {α : MulAut J} (hα : α ∈ autZ) {x : J} (hx : x ∈ lyC) : α x ∈ lyC := by
  rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← mem_autZ.1 hα, ← map_mul, ← map_mul, hx]

@[expose] def restrictC :
    autZ →* MulAut lyC where
  toFun a :=
    { toFun := fun x => ⟨(a : MulAut J) (x : J), apply_mem_lyC a.2 x.2⟩
      invFun := fun x => ⟨((a⁻¹ : autZ) : MulAut J) (x : J), apply_mem_lyC (a⁻¹).2 x.2⟩
      left_inv := fun x => Subtype.ext (by
        change ((a⁻¹ : autZ) : MulAut J) ((a : MulAut J) (x : J)) = x
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
      right_inv := fun x => Subtype.ext (by
        change (a : MulAut J) (((a⁻¹ : autZ) : MulAut J) (x : J)) = x
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (a : MulAut J) (x : J) (y : J)) }
  map_one' := MulEquiv.ext fun x => Subtype.ext rfl
  map_mul' a b := MulEquiv.ext fun x => Subtype.ext rfl

theorem restrictC_apply
    (a : autZ) (x : lyC) : (restrictC a x : J) = (a : MulAut J) (x : J) :=
  rfl

@[expose] def autZToOuterC :
    autZ →* Outer lyC := (QuotientGroup.mk' (inner lyC)).comp restrictC

@[expose] def autZToOuterJ :
    autZ →* Outer J := (QuotientGroup.mk' (inner J)).comp autZ.subtype

theorem autZToOuterJ_surjective :
    Function.Surjective autZToOuterJ := by
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner J) q
  have h2 : orderOf (α lyz) = 2 := by rw [MulEquiv.orderOf_eq, orderOf_lyz]
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 _ h2
  have hmem : MulAut.conj x⁻¹ * α ∈ autZ := by
    rw [mem_autZ, MulAut.mul_apply, ← hx, MulAut.conj_apply]
    group
  refine ⟨⟨_, hmem⟩, ?_⟩
  · show QuotientGroup.mk' (inner J) (MulAut.conj x⁻¹ * α) = QuotientGroup.mk' (inner J) α
    have h1 : QuotientGroup.mk' (inner J) (MulAut.conj x⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := inner J) (MulAut.conj x⁻¹)).2 ⟨x⁻¹, rfl⟩
    rw [map_mul, h1, one_mul]

theorem ker_autZToOuterC_le :
    autZToOuterC.ker ≤ autZToOuterJ.ker := by
  intro a ha
  rw [MonoidHom.mem_ker] at ha ⊢
  have hin : restrictC a ∈ inner lyC := (QuotientGroup.eq_one_iff _).1 ha
  obtain ⟨c, hc⟩ := hin
  have hfix : ∀ y ∈ lyC, (MulAut.conj (c : J)⁻¹ * (a : MulAut J)) y = y := by
    intro y hy
    have h1 := congrArg (fun γ : MulAut lyC => (γ ⟨y, hy⟩ : J)) hc
    have h2 : (c : J) * y * (c : J)⁻¹ = (a : MulAut J) y := h1
    rw [MulAut.mul_apply, ← h2, MulAut.conj_apply]
    group
  show QuotientGroup.mk' (inner J) (a : MulAut J) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rcases fixes_C_cases hfix with h | h
  · refine ⟨(c : J), ?_⟩
    have h2 : (a : MulAut J) = (MulAut.conj (c : J)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h2, map_inv, inv_inv]
  · refine ⟨(c : J) * lyz, ?_⟩
    have h' : (a : MulAut J) = MulAut.conj (c : J) * MulAut.conj lyz := by
      rw [← h, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [h', map_mul]

theorem card_outer_J_dvd :
    Nat.card (Outer J) ∣ 2 := by
  have h1 : Nat.card (Outer J) = autZToOuterJ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 autZToOuterJ_surjective, Subgroup.card_top]
  have h2 : autZToOuterJ.ker.index ∣ autZToOuterC.ker.index :=
    Subgroup.index_dvd_of_le ker_autZToOuterC_le
  have h3 : autZToOuterC.ker.index = Nat.card autZToOuterC.range := Subgroup.index_ker _
  have h4 : Nat.card autZToOuterC.range ∣ Nat.card (Outer lyC) :=
    Subgroup.card_subgroup_dvd_card _
  rw [h1]
  exact h2.trans (h3 ▸ h4.trans card_outer_lyC_dvd)

theorem outer_order_divides_two
    {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.Ly)) :
    Nat.card (Outer T) ∣ 2 ∧ (Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2) := by
  obtain ⟨e⟩ := hT
  have eq := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (G := T) (H := J)
    (by exact e.trans lyEquivJ)
  have h : Nat.card (Outer T) ∣ 2 := by
    rw [Nat.card_congr eq.toEquiv]
    exact card_outer_J_dvd
  exact ⟨h, (Nat.dvd_prime Nat.prime_two).1 h⟩

end CFSG.Sporadic.LySchreier
