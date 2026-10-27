module

public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.Background.HSp4A
public import Certificates.Certificate7022
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.Quasithin.Background.HPairBridge

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open scoped Matrix

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

@[expose] def c5 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    rfl⟩

theorem c5_pow_five : c5 ^ 5 = 1 := by decide

theorem c5_ne_one : c5 ≠ 1 := by decide

omit α in
theorem card_fin_four_fun : Nat.card (Fin 4 → ZMod 2) = 16 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem isNatIrr : IsNatIrr (Γ α) := by
  classical
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  by_cases htop : U = ⊤
  · exact Or.inr htop
  exfalso
  set g : GL (Fin 4) (ZMod 2) := rep α c5 with hg
  have hgΓ : g ∈ Γ α := ⟨c5, rfl⟩
  have hg5 : g ^ 5 = 1 := by rw [hg, ← map_pow, c5_pow_five, map_one]
  have hg1 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 1 := by
    intro h
    apply c5_ne_one
    apply rep_injective α
    rw [map_one, ← hg]
    exact Units.ext h
  have hfix := fix_eq_zero_of_pow_five (g : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (by rw [← Units.val_pow_eq_pow_val, hg5, Units.val_one]) hg1
  set x : MulAut (StdMod (Fin 4) (ZMod 2)) := matAut g with hx
  have hx5 : x ^ 5 = 1 := by
    rw [hx, ← matHom_apply, ← map_pow, hg5, map_one]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := if x = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    split_ifs with h
    · rw [h, orderOf_one, pow_zero]
    · rw [pow_one]
      exact orderOf_eq_prime hx5 h
  set W : Subgroup (StdMod (Fin 4) (ZMod 2)) := AddSubgroup.toSubgroup U with hW
  let S : Subgroup (MulAut (StdMod (Fin 4) (ZMod 2))) :=
    { carrier := {y | ∀ w ∈ W, y w ∈ W ∧ y⁻¹ w ∈ W}
      one_mem' := fun w hw => ⟨hw, hw⟩
      mul_mem' := fun {y z} hy hz w hw => ⟨(hy _ (hz w hw).1).1, (hz _ (hy w hw).2).2⟩
      inv_mem' := fun {y} hy w hw => by
        rw [inv_inv]
        exact ⟨(hy w hw).2, (hy w hw).1⟩ }
  have hxS : x ∈ S := by
    intro w hw
    rw [hW, Multiplicative.mem_toSubgroup] at hw
    have h1 : x⁻¹ = matAut g⁻¹ := by
      rw [hx, ← matHom_apply, ← matHom_apply, map_inv]
    refine ⟨?_, ?_⟩
    · rw [hW, Multiplicative.mem_toSubgroup]
      exact hU g hgΓ _ hw
    · rw [hW, Multiplicative.mem_toSubgroup, h1]
      exact hU g⁻¹ ((Γ α).inv_mem hgΓ) _ hw
  have hPS : Subgroup.zpowers x ≤ S := (Subgroup.zpowers_le).mpr hxS
  have hmod := Sp4.card_modEq_card_inf_fixV hP fun y hy w hw => (hPS hy w hw).1
  have hfix1 : W ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨-, hw⟩
    rw [Subgroup.mem_bot]
    have h1 : x w = w := hw x (Subgroup.mem_zpowers x)
    have h2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd w =
        Multiplicative.toAdd w := congrArg Multiplicative.toAdd h1
    have h3 := hfix _ h2
    exact Multiplicative.toAdd.injective (h3.trans toAdd_one.symm)
  have hcardW : Nat.card W = Nat.card U := rfl
  have key : Nat.card ↥(W ⊓ fixV (Subgroup.zpowers x)) = 1 := by
    rw [hfix1, Subgroup.card_bot]
  have hmod' : Nat.card U ≡ 1 [MOD 5] := by
    rw [← hcardW]
    convert hmod using 2
    exact key.symm
  have hdvd : Nat.card U ∣ 2 ^ 4 := by
    have := AddSubgroup.card_addSubgroup_dvd_card U
    rwa [card_fin_four_fun] at this
  have hne1 : Nat.card U ≠ 1 := fun h => hbot (AddSubgroup.card_eq_one.mp h)
  have hne16 : Nat.card U ≠ 16 := fun h => htop
    (AddSubgroup.card_eq_iff_eq_top U |>.mp (h.trans card_fin_four_fun.symm))
  obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hUk] at hmod' hne1 hne16
  interval_cases k <;> simp_all [Nat.ModEq]

omit α in
theorem mulVec_inv_mulVec (A : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit α in
theorem mulVec_mulVec_inv (A : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit α in
theorem card_fix_conj_mat (A B : GL (Fin 4) (ZMod 2)) :
    Fintype.card {v : Fin 4 → ZMod 2 //
      ((A * B * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} =
      Fintype.card {v : Fin 4 → ZMod 2 //
        (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} := by
  have e : ∀ v, ((A * B * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((B : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  refine Fintype.card_congr
    { toFun := fun v => ⟨((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1,
        ?_⟩
      invFun := fun v => ⟨(A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1, ?_⟩
      left_inv := fun v => Subtype.ext (mulVec_mulVec_inv A v.1)
      right_inv := fun v => Subtype.ext (mulVec_inv_mulVec A v.1) }
  · have h := v.2
    rw [e] at h
    have h' := congrArg (fun w => ((A⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w) h
    simp only [mulVec_inv_mulVec] at h'
    exact h'
  · rw [e, mulVec_inv_mulVec, v.2]

theorem card_fix_inv8_ne_eight :
    Fintype.card {v : Fin 4 → ZMod 2 //
      ((α inv8 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} ≠ 8 := by
  classical
  intro h8
  set T := (Finset.univ.filter fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M * M = 1 ∧
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 8) with hT
  have hTc : T.card = 105 := card_transvections
  let f : alternatingGroup (Fin 8) → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    fun π => ((α (π * inv8 * π⁻¹) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hinv8 : inv8 * inv8 = 1 := by decide
  have hfT : ∀ π, f π ∈ T := by
    intro π
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have h1 : (π * inv8 * π⁻¹) * (π * inv8 * π⁻¹) = 1 := by
        calc (π * inv8 * π⁻¹) * (π * inv8 * π⁻¹) = π * (inv8 * inv8) * π⁻¹ := by group
          _ = 1 := by rw [hinv8, mul_one, mul_inv_cancel]
      change ((α (π * inv8 * π⁻¹) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((α (π * inv8 * π⁻¹) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
      rw [← Units.val_mul, ← map_mul, h1, map_one, Units.val_one]
    · rw [← Fintype.card_subtype]
      change Fintype.card {v : Fin 4 → ZMod 2 //
        ((α (π * inv8 * π⁻¹) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
          v} = 8
      rw [map_mul, map_mul, map_inv, card_fix_conj_mat, h8]
  have hfib : ∀ b ∈ Finset.univ.image f, (Finset.univ.filter fun π => f π = b).card ≤ 96 := by
    intro b hb
    obtain ⟨π₀, -, rfl⟩ := Finset.mem_image.mp hb
    rw [← card_centralizer_inv8]
    refine Finset.card_le_card_of_injOn (fun π => π₀⁻¹ * π) ?_ ?_
    · intro π hπ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      have h1 : π * inv8 * π⁻¹ = π₀ * inv8 * π₀⁻¹ := α.injective (Units.ext hπ)
      calc π₀⁻¹ * π * inv8 = π₀⁻¹ * (π * inv8 * π⁻¹) * π := by group
        _ = π₀⁻¹ * (π₀ * inv8 * π₀⁻¹) * π := by rw [h1]
        _ = inv8 * (π₀⁻¹ * π) := by group
    · intro π _ π' _ h
      exact mul_left_cancel h
  have h1 := Finset.card_le_mul_card_image Finset.univ 96 hfib
  have h2 : (Finset.univ.image f).card ≤ 105 := by
    rw [← hTc]
    refine Finset.card_le_card fun b hb => ?_
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp hb
    exact hfT π
  have h3 : (Finset.univ : Finset (alternatingGroup (Fin 8))).card = 20160 := by
    rw [Finset.card_univ, card_alternatingGroup, Fintype.card_fin]
    rfl
  omega

theorem card_fix_le_four {γ : Γ α} (h2 : γ * γ = 1) (h1 : γ ≠ 1) :
    Fintype.card {v : Fin 4 → ZMod 2 //
      ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} ≤ 4 := by
  classical
  obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
  have hσ2 : σ * σ = 1 := (ψ α).injective (by rw [map_mul, h2, map_one])
  have hσ1 : σ ≠ 1 := fun h => h1 (by rw [h, map_one])
  obtain ⟨g, hg⟩ := exists_conj_inv7 σ hσ2 hσ1
  have hσ : σ = g⁻¹ * inv7 * g := by rw [← hg]; group
  have hrep : ((ψ α σ : Γ α) : GL (Fin 4) (ZMod 2)) =
      (rep α g)⁻¹ * α inv8 * (rep α g)⁻¹⁻¹ := by
    rw [coe_ψ, hσ, inv_inv, map_mul, map_mul, map_inv]
    congr 2
    change α (altLift7 inv7) = α inv8
    rw [altLift7_inv7]
  rw [hrep, card_fix_conj_mat]
  set M := ((α inv8 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hM
  let F₀ : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
    { carrier := {v | M *ᵥ v = v}
      add_mem' := fun {v w} hv hw => by
        change M *ᵥ (v + w) = v + w
        rw [Matrix.mulVec_add, hv, hw]
      zero_mem' := Matrix.mulVec_zero M
      smul_mem' := fun c v hv => by
        change M *ᵥ (c • v) = c • v
        rw [Matrix.mulVec_smul, hv] }
  let F : AddSubgroup (Fin 4 → ZMod 2) := F₀.toAddSubgroup
  have hmemF : ∀ v, v ∈ F ↔ M *ᵥ v = v := fun v => Iff.rfl
  have hF : Fintype.card {v : Fin 4 → ZMod 2 // M *ᵥ v = v} = Nat.card F := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hdvd : Nat.card F ∣ 2 ^ 4 := by
    have := AddSubgroup.card_addSubgroup_dvd_card F
    rwa [card_fin_four_fun] at this
  have h16 : Nat.card F ≠ 16 := by
    intro h
    have htop : F = ⊤ := (AddSubgroup.card_eq_iff_eq_top F).mp (h.trans card_fin_four_fun.symm)
    have hM1 : M = 1 := Matrix.ext_iff_mulVec.mpr fun v => by
      have : v ∈ F := htop ▸ AddSubgroup.mem_top v
      rw [Matrix.one_mulVec]
      exact (hmemF v).mp this
    have : inv8 = 1 := α.injective (by rw [map_one]; exact Units.ext hM1)
    exact absurd this (by decide)
  have h8 : Nat.card F ≠ 8 := by
    rw [← hF]
    exact card_fix_inv8_ne_eight α
  rw [hF]
  obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hFk] at h16 h8 ⊢
  interval_cases k <;> simp_all

theorem card_le_four {E : Subgroup (GL (Fin 4) (ZMod 2))} (hE : E ≤ Γ α)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  classical
  set E' := E.comap (rep α) with hE'
  have hcard : Nat.card E' = Nat.card E := by
    have hmap : E'.map (rep α) = E := Subgroup.map_comap_eq_self hE
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective (rep_injective α)).symm
  have hsq' : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    apply rep_injective α
    rw [map_mul, map_one]
    exact hsq _ hx
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq' x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq' y hy)
    have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq' _ (E'.mul_mem hx hy))
    rw [← hxy, _root_.mul_inv_rev, hx', hy']
  have hel : CFSG.Open.IsElemAbelian 2 E' :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => by rw [sq]; exact hsq' x hx⟩
  have hp : IsPGroup 2 E' := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hsq' x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num) le_top hel hk).trans
      CFSG.GH74.SmallRanks.twoRank_alternatingGroup_seven_le_two
  rw [← hcard, hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

end A7

end H

end CFSG.Quasithin
