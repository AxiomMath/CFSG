module

public import CFSG.Quasithin.AppendixH.H11.NativeBridge
public import CFSG.Quasithin.AppendixH.H11.NativeVectors
public import CFSG.Quasithin.AppendixH.H11.ModuleRank
public import CFSG.Quasithin.Background.SzG11M12Syl

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped IsMulCommutative

namespace NativeCoords

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} (c : NativeCoords L)

private theorem mem_zpowers_of_mk_eq {m m' : G6.coreMod 12}
    (h : (QuotientGroup.mk m : Q12) = QuotientGroup.mk m') :
    ((m : G6.PermMod 12) * (m' : G6.PermMod 12)⁻¹) ∈ Subgroup.zpowers (G6.allOnes 12) := by
  have hN : m * m'⁻¹ ∈ (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12) := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk m * (QuotientGroup.mk m')⁻¹ : Q12) = 1
    rw [h, mul_inv_cancel]
  have hperm := Subgroup.mem_subgroupOf.mp hN
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hperm
  exact hperm

private theorem psi_commutator (γ : ↥CFSG.Blueprint.NativeSporadic.M12) (v : V)
    (m : G6.coreMod 12) (hm : c.ψ v = QuotientGroup.mk m) :
    c.ψ ((c.π γ : MulAut V) v * v⁻¹) =
      QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) m * m⁻¹) := by
  have heq := c.equivariant γ v m hm
  rw [map_mul, map_inv, heq, hm, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]

private theorem permMod_sq_eq_one (x : G6.PermMod 12) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  show (2 : ℕ) • Multiplicative.toAdd x i = 0
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

private theorem psi_prod {ι : Type*} (f : ι → V) (S : Finset ι) :
    c.ψ (∏ s ∈ S, f s) = ∏ s ∈ S, c.ψ (f s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]

private theorem mk_prod {ι : Type*} (f : ι → G6.coreMod 12) (S : Finset ι) :
    (QuotientGroup.mk (∏ s ∈ S, f s) : Q12) = ∏ s ∈ S, QuotientGroup.mk (f s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, ← QuotientGroup.mk_mul]

theorem injective : Function.Injective c.π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext
  apply eq_one_of_mem_zpowers_allOnes
  intro x hx
  let v : V := c.ψ.symm (QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12))
  have hm : c.ψ v = QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12) := by
    simp [v]
  have heq := c.equivariant γ v ⟨x, hx⟩ hm
  have hcoe : ((c.π γ : ↥L) : MulAut V) = 1 := by rw [hγ]; rfl
  have hmk : (QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) ⟨x, hx⟩) : Q12) =
      QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12) := by
    simpa [hcoe, hm] using heq.symm
  have hmem := mem_zpowers_of_mk_eq hmk
  simpa [G6.coreAct_coe] using hmem

@[expose] noncomputable def mulEquiv : ↥CFSG.Blueprint.NativeSporadic.M12 ≃* ↥L :=
  MulEquiv.ofBijective c.π ⟨c.injective, c.surj⟩

theorem mulEquiv_apply (γ : ↥CFSG.Blueprint.NativeSporadic.M12) : c.mulEquiv γ = c.π γ := rfl

theorem eq_one_of_fixed_of_orderOf_eq_eleven (x : ↥CFSG.Blueprint.NativeSporadic.M12)
    (hx : orderOf x = 11) (v : V) (hv : (c.π x : MulAut V) v = v) : v = 1 := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (c.ψ v)
  have hmψ : c.ψ v = QuotientGroup.mk m := hm.symm
  have heq := c.equivariant x v m hmψ
  have h2 : (QuotientGroup.mk (G6.coreAct 12 (x : Equiv.Perm (Fin 12)) m) : Q12) =
      QuotientGroup.mk m := by
    simpa [hv, hmψ] using heq.symm
  have hmem := mem_zpowers_of_mk_eq h2
  have hmem' : G6.permAct 12 (x : Equiv.Perm (Fin 12)) (m : G6.PermMod 12) *
      (m : G6.PermMod 12)⁻¹ ∈ Subgroup.zpowers (G6.allOnes 12) := by
    simpa only [G6.coreAct_coe] using hmem
  have hx11 : (x : Equiv.Perm (Fin 12)) ^ 11 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg (fun y : ↥CFSG.Blueprint.NativeSporadic.M12 =>
      (y : Equiv.Perm (Fin 12))) h
  have hx1 : (x : Equiv.Perm (Fin 12)) ≠ 1 := by
    intro h
    have h1' : x = 1 := Subtype.ext h
    rw [h1', orderOf_one] at hx
    norm_num at hx
  have hmz : (m : G6.PermMod 12) ∈ Subgroup.zpowers (G6.allOnes 12) :=
    mem_zpowers_allOnes_of_order_eleven (x : Equiv.Perm (Fin 12)) hx11 hx1 m.2 hmem'
  have hmk1 : (QuotientGroup.mk m : Q12) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hmz
  have hv1 : c.ψ v = 1 := by rw [hmψ, hmk1]
  exact c.ψ.injective (by rw [hv1, map_one])

theorem four_le_rkIdx_of_involution [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (γ : ↥CFSG.Blueprint.NativeSporadic.M12) (h1 : γ ≠ 1)
    (h2 : γ * γ = 1) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers (c.π γ : MulAut V))) := by
  obtain ⟨a, b, hab, hne, hdisj⟩ :=
    CFSG.Quasithin.G11.SzG11S.M12Syl.invol_cycles γ h1 h2
  have hγ : (γ : Equiv.Perm (Fin 12)) * (γ : Equiv.Perm (Fin 12)) = 1 := by
    have h := congrArg (fun y : ↥CFSG.Blueprint.NativeSporadic.M12 =>
      (y : Equiv.Perm (Fin 12))) h2
    simpa using h
  obtain ⟨u, hu, hind⟩ :=
    exists_independent_commutators (γ : Equiv.Perm (Fin 12)) hγ a b hab hne hdisj
  let v : Fin 4 → V := fun s => c.ψ.symm (QuotientGroup.mk (⟨u s, hu s⟩ : G6.coreMod 12))
  apply le_rkIdx_of_independent_commutators hV (c.π γ : MulAut V) v
  intro S hS hprod
  let g : Fin 4 → G6.coreMod 12 := fun s =>
    G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) ⟨u s, hu s⟩ * ⟨u s, hu s⟩⁻¹
  have hterm : ∀ s ∈ S, c.ψ ((c.π γ : MulAut V) (v s) * (v s)⁻¹) =
      QuotientGroup.mk (g s) := by
    intro s _
    exact psi_commutator (c := c) γ (v s) ⟨u s, hu s⟩ (by simp [v])
  have hψprod : c.ψ (∏ s ∈ S, ((c.π γ : MulAut V) (v s) * (v s)⁻¹)) =
      ∏ s ∈ S, QuotientGroup.mk (g s) :=
    (psi_prod (c := c) (f := fun s => (c.π γ : MulAut V) (v s) * (v s)⁻¹) S).trans
      (Finset.prod_congr rfl hterm)
  have hψ1 : c.ψ (∏ s ∈ S, ((c.π γ : MulAut V) (v s) * (v s)⁻¹)) = 1 := by
    rw [hprod, map_one]
  have hQ : (∏ s ∈ S, QuotientGroup.mk (g s) : Q12) = 1 := by
    rw [← hψprod, hψ1]
  have hQ' : (QuotientGroup.mk (∏ s ∈ S, g s) : Q12) = 1 := by
    rw [mk_prod, hQ]
  have hmemN : (∏ s ∈ S, g s) ∈
      (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12) :=
    (QuotientGroup.eq_one_iff (∏ s ∈ S, g s)).mp hQ'
  have hmem : (∏ s ∈ S, (G6.permAct 12 (γ : Equiv.Perm (Fin 12)) (u s) * (u s)⁻¹)) ∈
      Subgroup.zpowers (G6.allOnes 12) := by
    have hmem' := Subgroup.mem_subgroupOf.mp hmemN
    rw [SubmonoidClass.coe_finsetProd] at hmem'
    have hprod_eq : (∏ s ∈ S, (↑(g s) : G6.PermMod 12)) =
        ∏ s ∈ S, (G6.permAct 12 (γ : Equiv.Perm (Fin 12)) (u s) * (u s)⁻¹) := by
      apply Finset.prod_congr rfl
      intro s _
      rfl
    rwa [hprod_eq] at hmem'
  exact hind S hS hmem

theorem orderOf_m12a (hV : ∀ v : V, v ^ 2 = 1) :
    orderOf (c.π CFSG.Sporadic.Mathieu.m12a : MulAut V) = 2 := by
  have hmul : CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12a = 1 := by
    apply Subtype.ext
    change CFSG.Sporadic.Mathieu.m12gA * CFSG.Sporadic.Mathieu.m12gA = 1
    decide
  have hne : CFSG.Sporadic.Mathieu.m12a ≠ 1 := by
    intro h
    exact (by decide : CFSG.Sporadic.Mathieu.m12gA ≠ 1)
      (congrArg (fun y : ↥CFSG.Blueprint.NativeSporadic.M12 =>
        (y : Equiv.Perm (Fin 12))) h)
  have hmulL : c.π CFSG.Sporadic.Mathieu.m12a * c.π CFSG.Sporadic.Mathieu.m12a = 1 := by
    rw [← map_mul, hmul, map_one]
  have hneL : c.π CFSG.Sporadic.Mathieu.m12a ≠ 1 := by
    intro h
    exact hne (c.injective (by rw [h, map_one]))
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by simpa [pow_two] using hmulL) hneL

theorem rkIdx_m12a [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) :
    rkIdx (fixV (Subgroup.zpowers (c.π CFSG.Sporadic.Mathieu.m12a : MulAut V))) = 4 := by
  have hmul : CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12a = 1 := by
    apply Subtype.ext
    change CFSG.Sporadic.Mathieu.m12gA * CFSG.Sporadic.Mathieu.m12gA = 1
    decide
  have hne : CFSG.Sporadic.Mathieu.m12a ≠ 1 := by
    intro h
    exact (by decide : CFSG.Sporadic.Mathieu.m12gA ≠ 1)
      (congrArg (fun y : ↥CFSG.Blueprint.NativeSporadic.M12 =>
        (y : Equiv.Perm (Fin 12))) h)
  obtain ⟨c', hc'⟩ := commutators_le_closure_m12gA
  set N : Subgroup (G6.coreMod 12) :=
    (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12) with hN
  set K₀ : Subgroup (G6.PermMod 12) := Subgroup.closure (Set.range c') with hK₀
  set K₁ : Subgroup Q12 := (K₀.subgroupOf (G6.coreMod 12)).map (QuotientGroup.mk' N) with hK₁
  set K : Subgroup V := K₁.comap c.ψ.toMonoidHom with hKset
  have hcardK : Nat.card K = Nat.card K₁ := by
    rw [hKset, Subgroup.comap_equiv_eq_map_symm' c.ψ K₁,
      Subgroup.card_map_of_injective c.ψ.symm.injective]
  have hcardmap : Nat.card K₁ ≤ Nat.card (K₀.subgroupOf (G6.coreMod 12)) := by
    rw [hK₁]
    refine Nat.card_le_card_of_surjective
      (fun x : ↥(K₀.subgroupOf (G6.coreMod 12)) =>
        (⟨(QuotientGroup.mk' N) (x : G6.coreMod 12),
          Subgroup.mem_map_of_mem (QuotientGroup.mk' N) x.2⟩ :
            ↥((K₀.subgroupOf (G6.coreMod 12)).map (QuotientGroup.mk' N)))) ?_
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcard_sub : Nat.card (K₀.subgroupOf (G6.coreMod 12)) ≤ Nat.card K₀ :=
    Nat.card_le_card_of_injective
      (fun x : (K₀.subgroupOf (G6.coreMod 12)) =>
        (⟨(x : G6.coreMod 12), Subgroup.mem_subgroupOf.mp x.2⟩ : K₀))
      (by
        intro a b hab
        exact Subtype.ext (Subtype.ext (congrArg (fun z : K₀ => (z : G6.PermMod 12)) hab)))
  have hcardK0 : Nat.card K₀ ≤ 2 ^ 4 := by
    rw [hK₀]
    exact card_closure_range_le permMod_sq_eq_one c'
  have hK : Nat.card K ≤ 2 ^ 4 := by
    calc Nat.card K = Nat.card K₁ := hcardK
      _ ≤ Nat.card (K₀.subgroupOf (G6.coreMod 12)) := hcardmap
      _ ≤ Nat.card K₀ := hcard_sub
      _ ≤ 2 ^ 4 := hcardK0
  have hcomm : ∀ v : V, (c.π CFSG.Sporadic.Mathieu.m12a : MulAut V) v * v⁻¹ ∈ K := by
    intro v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (c.ψ v)
    have hmψ : c.ψ v = QuotientGroup.mk m := hm.symm
    have hψ := psi_commutator (c := c) CFSG.Sporadic.Mathieu.m12a v m hmψ
    have hmemK₁ : c.ψ ((c.π CFSG.Sporadic.Mathieu.m12a : MulAut V) v * v⁻¹) ∈ K₁ := by
      rw [hψ, hK₁]
      let a : G6.coreMod 12 :=
        G6.coreAct 12 (CFSG.Sporadic.Mathieu.m12a : Equiv.Perm (Fin 12)) m * m⁻¹
      have ha0 : a ∈ K₀.subgroupOf (G6.coreMod 12) := by
        rw [hK₀]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have hca := hc' (m : G6.PermMod 12) m.2
        show G6.permAct 12 CFSG.Sporadic.Mathieu.m12gA (m : G6.PermMod 12) *
          (m : G6.PermMod 12)⁻¹ ∈ Subgroup.closure (Set.range c')
        exact hca
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ha0
    rw [hKset]
    exact Subgroup.mem_comap.mpr hmemK₁
  apply le_antisymm
  · exact rkIdx_le_of_commutators_mem hV (c.π CFSG.Sporadic.Mathieu.m12a : MulAut V) K
      (k := 4) hK hcomm
  · exact four_le_rkIdx_of_involution (c := c) hV CFSG.Sporadic.Mathieu.m12a hne hmul

end NativeCoords

end CFSG.Quasithin.AppendixH.H11
