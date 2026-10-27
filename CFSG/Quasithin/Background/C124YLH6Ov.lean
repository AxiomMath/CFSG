module

public import CFSG.Quasithin.Background.C124YLH6Kl
public import CFSG.Quasithin.Background.C124YLA6Model

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def S0 : Subgroup P6 where
  carrier := {g | Perm.sign g = 1 ∧ g 0 = 0}
  one_mem' := ⟨by simp, rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨by simp [ha.1], by
    show a.symm 0 = 0
    exact (Equiv.symm_apply_eq a).2 ha.2.symm⟩

theorem card_S0 : Nat.card S0 = 60 := by
  have h : (Finset.univ.filter (fun g : P6 => Perm.sign g = 1 ∧ g 0 = 0)).card = 60 := by
    decide +kernel
  rw [← h, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

@[expose] def rho0 : ↥S0 →* Perm {x : Fin 6 // x ≠ 0} where
  toFun g := (g : P6).subtypePerm (fun x => ⟨fun hx hx0 => hx (by rw [hx0]; exact g.2.2),
    fun hx hx0 => hx ((g : P6).injective (by rw [hx0, g.2.2]))⟩)
  map_one' := by
    ext x
    simp
  map_mul' := fun a b => by
    ext x
    rfl

theorem rho0_injective : Function.Injective rho0 := by
  intro a b h
  apply Subtype.ext
  refine Equiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, a.2.2, b.2.2]
  · have := congrArg
      (fun f : Perm {x : Fin 6 // x ≠ 0} => ((f ⟨x, hx⟩ : {x : Fin 6 // x ≠ 0}) : Fin 6)) h
    exact this

theorem card_ne_zero_fin : Nat.card {x : Fin 6 // x ≠ 0} = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem S0_equiv_alt_five : Nonempty (↥S0 ≃* alternatingGroup (Fin 5)) := by
  classical
  have hle : rho0.range ≤ alternatingGroup {x : Fin 6 // x ≠ 0} := by
    rintro _ ⟨g, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have hperm : ∀ x : Fin 6, (g : P6) x ≠ 0 ↔ x ≠ 0 := fun x =>
      ⟨fun hx hx0 => hx (by rw [hx0]; exact g.2.2),
        fun hx hx0 => hx ((g : P6).injective (by rw [hx0, g.2.2]))⟩
    show Perm.sign ((g : P6).subtypePerm hperm) = 1
    rw [Equiv.Perm.sign_subtypePerm (g : P6) (p := fun x : Fin 6 => x ≠ 0) hperm
      (fun x hx hx0 => hx (by rw [hx0]; exact g.2.2))]
    exact g.2.1
  have hcard : Nat.card rho0.range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective rho0_injective).toEquiv]
    exact card_S0
  have hcardA : Nat.card (alternatingGroup {x : Fin 6 // x ≠ 0}) = 60 := by
    have : Nontrivial {x : Fin 6 // x ≠ 0} := ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide⟩⟩
    have h := two_mul_nat_card_alternatingGroup (α := {x : Fin 6 // x ≠ 0})
    rw [Nat.card_perm, card_ne_zero_fin] at h
    have h5 : Nat.factorial 5 = 120 := by decide
    omega
  have heq : rho0.range = alternatingGroup {x : Fin 6 // x ≠ 0} :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardA])
  let e5 : {x : Fin 6 // x ≠ 0} ≃ Fin 5 := Fintype.equivFinOfCardEq (by simp)
  exact ⟨(MonoidHom.ofInjective rho0_injective).trans
    ((MulEquiv.subgroupCongr heq).trans (Equiv.altCongrHom e5))⟩

theorem S0_le_A6 : S0 ≤ alternatingGroup (Fin 6) := fun g hg => by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact hg.1

theorem KAg_le_S0 : KAg ≤ S0 := fun g hg =>
  (by decide +kernel : ∀ g ∈ kAlist, Perm.sign g = 1 ∧ g 0 = 0) g hg

theorem isSylowTwoOf_Pg : IsSylowTwoOf Pg (alternatingGroup (Fin 6)) := by
  refine ⟨Pg_le_A6, IsPGroup.of_card (n := 3) ?_, ?_⟩
  · rw [card_Pg]
    norm_num
  · have h := Subgroup.index_mul_card (Pg.subgroupOf (alternatingGroup (Fin 6)))
    rw [card_subgroupOf_A6 Pg_le_A6, card_Pg, card_Gam] at h
    omega

theorem klein_overgroup_of_std {K0 Y0 : Subgroup P6} {n0 c : P6} {K : Subgroup P6}
    (hKY : K0 ≤ Y0) (hYA : Y0 ≤ alternatingGroup (Fin 6)) (hc60 : Nat.card Y0 = 60)
    (hA5 : Nonempty (↥Y0 ≃* alternatingGroup (Fin 5)))
    (hn0A : n0 ∈ alternatingGroup (Fin 6)) (hn0N : ∀ k ∈ K0, n0 * k * n0⁻¹ ∈ K0)
    (hn0Y : n0 ∉ Y0) (hcA : c ∈ alternatingGroup (Fin 6)) (hK : cjSub c K = K0) :
    ∃ Y : Subgroup P6, Y ≤ alternatingGroup (Fin 6) ∧ K ≤ Y ∧ Nat.card Y = 60 ∧
      Nonempty (↥Y ≃* alternatingGroup (Fin 5)) ∧
      ∃ n ∈ alternatingGroup (Fin 6), (∀ k ∈ K, n * k * n⁻¹ ∈ K) ∧ n ∉ Y := by
  have hcinv : c⁻¹ ∈ alternatingGroup (Fin 6) := inv_mem hcA
  refine ⟨cjSub c⁻¹ Y0, ?_, ?_, ?_, ?_, c⁻¹ * n0 * c, ?_, ?_, ?_⟩
  · intro x hx
    have h1 := hYA (mem_cjSub.1 hx)
    have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [h2]
    exact mul_mem (mul_mem hcinv (by simpa using h1)) hcA
  · intro k hk
    have h1 : c⁻¹⁻¹ * k * c⁻¹ ∈ K0 := by
      rw [← hK, mem_cjSub]
      have e : c⁻¹ * (c⁻¹⁻¹ * k * c⁻¹) * c = k := by group
      rw [e]
      exact hk
    exact mem_cjSub.2 (hKY h1)
  · rw [card_cjSub, hc60]
  · obtain ⟨e⟩ := hA5
    exact ⟨((Y0.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).symm.trans e : _)⟩
  · exact mul_mem (mul_mem hcinv hn0A) hcA
  · intro k hk
    have h1 : c * k * c⁻¹ ∈ K0 := by
      rw [← hK, mem_cjSub]
      have e : c⁻¹ * (c * k * c⁻¹) * c = k := by group
      rw [e]
      exact hk
    have h2 := hn0N _ h1
    rw [← hK, mem_cjSub] at h2
    have e : c⁻¹ * n0 * c * k * (c⁻¹ * n0 * c)⁻¹ = c⁻¹ * (n0 * (c * k * c⁻¹) * n0⁻¹) * c := by
      group
    rw [e]
    exact h2
  · intro hn
    apply hn0Y
    have := mem_cjSub.1 hn
    simpa [mul_assoc] using this

theorem klein_overgroup {K : Subgroup P6} (hKA : K ≤ alternatingGroup (Fin 6))
    (h4 : Nat.card K = 4) (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    ∃ Y : Subgroup P6, Y ≤ alternatingGroup (Fin 6) ∧ K ≤ Y ∧ Nat.card Y = 60 ∧
      Nonempty (↥Y ≃* alternatingGroup (Fin 5)) ∧
      ∃ n ∈ alternatingGroup (Fin 6), (∀ k ∈ K, n * k * n⁻¹ ∈ K) ∧ n ∉ Y := by
  have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  obtain ⟨c, hcA, hcle⟩ := exists_conj_le_of_isSylowTwoOf isSylowTwoOf_Pg hKA hK2
  have hH4 : Nat.card (cjSub c K) = 4 := by rw [card_cjSub, h4]
  have hHcomm : ∀ a ∈ cjSub c K, ∀ b ∈ cjSub c K, a * b = b * a := by
    intro a ha b hb
    have h := hcomm _ (mem_cjSub.1 ha) _ (mem_cjSub.1 hb)
    have h2 := congrArg (fun t => c * t * c⁻¹) h
    simpa [mul_assoc] using h2
  have hHsq : ∀ a ∈ cjSub c K, a * a = 1 := by
    intro a ha
    have h := hsq _ (mem_cjSub.1 ha)
    have h2 := congrArg (fun t => c * t * c⁻¹) h
    simpa [mul_assoc] using h2
  rcases klein_of_le_Pg hcle hH4 hHcomm hHsq with h | h
  · exact klein_overgroup_of_std Kg_le_Yg Yg_le_A6 card_Yg Yg_equiv_alt_five
      (Pg_le_A6 nu_mem_Pg) (fun k hk => Pg_norm_Kg _ nu_mem_Pg k hk) nu_not_mem_Yg hcA h
  · refine klein_overgroup_of_std KAg_le_S0 S0_le_A6 card_S0 S0_equiv_alt_five
      (n0 := swap 0 1 * swap 2 3) (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)) ?_ ?_
      hcA h
    · intro k hk
      exact memP_iff.1 ((by decide +kernel : ∀ k ∈ kAlist,
        memP (swap 0 1 * swap 2 3 * k * (swap 0 1 * swap 2 3)⁻¹) kAlist = true) k hk)
    · intro hS
      have := hS.2
      revert this
      decide +kernel

end CFSG.Quasithin.C124.YL.A6
