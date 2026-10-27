module

public import CFSG.Quasithin.Vol2.Ch10SecEA5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem pact_cThree'_eTwoThree :
    pact SecE.cThree' ![0, 0, 1, 1, 0] + ![0, 0, 1, 1, 0] = SecE.zThree := by
  decide +kernel

theorem isEven_eTwoThree : isEven ![0, 0, 1, 1, 0] := by decide +kernel

variable {W : Type*} [CommGroup W]

theorem exists_fix_of_isA5Module' {K : Subgroup (MulAut W)} (h : E2.IsA5Module K) :
    ∃ k ∈ oTwoUpper K, k * k ≠ 1 ∧ ∃ d ∈ oTwoUpper K, ∃ z ∈ commV (oTwoUpper K),
      k (d z * z⁻¹) = d z * z⁻¹ ∧ d (d z * z⁻¹) ≠ d z * z⁻¹ := by
  obtain ⟨θ, β, hβ⟩ := h
  set k : ↥K := θ.symm SecE.cThree
  set d : ↥K := θ.symm SecE.cThree'
  have hodd : ∀ (x : ↥K) (σ : Perm (Fin 5)), θ x = σ → σ ^ 3 = 1 → σ ≠ 1 →
      (x : MulAut W) ∈ oTwoUpper K := by
    intro x σ hx h3 h1
    refine mem_oTwoUpper_of_odd x.2 ?_
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ, hx]
    exact SecE.odd_orderOf_of_pow_three h3 h1
  have hk : (k : MulAut W) ∈ oTwoUpper K :=
    hodd k SecE.cThree (θ.apply_symm_apply _) SecE.cThree_pow_three SecE.cThree_ne_one
  have hd : (d : MulAut W) ∈ oTwoUpper K :=
    hodd d SecE.cThree' (θ.apply_symm_apply _) SecE.cThree'_pow_three SecE.cThree'_ne_one
  have hinv := commV_invariant K
  have hco : ∀ (x : ↥K) (u : ↥(commV K)), ((Multiplicative.toAdd
      (β ⟨(x : MulAut W) u, hinv _ x.2 _ u.2⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
      pact (θ x) ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) := fun x u =>
    funext fun i => hβ x u _ i
  set u : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨![0, 0, 1, 1, 0], isEven_eTwoThree⟩)
  set z : W := (d : MulAut W) (u : W) * (u : W)⁻¹
  have hzK : z ∈ commV K := (commV K).mul_mem (hinv _ d.2 _ u.2) ((commV K).inv_mem u.2)
  have hβz : ((Multiplicative.toAdd (β ⟨z, hzK⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
      SecE.zThree := by
    have e1 : (⟨z, hzK⟩ : ↥(commV K)) = ⟨(d : MulAut W) u, hinv _ d.2 _ u.2⟩ * u⁻¹ := rfl
    rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg,
      hco d u]
    have hu : ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) =
        ![0, 0, 1, 1, 0] := by
      simp [u]
    rw [hu, show θ d = SecE.cThree' from θ.apply_symm_apply _, ← pact_cThree'_eTwoThree]
    congr 1
    funext i
    exact ZMod.neg_eq_self_mod_two _
  set w : W := (d : MulAut W) z * z⁻¹
  have hwK : w ∈ commV K := (commV K).mul_mem (hinv _ d.2 _ hzK) ((commV K).inv_mem hzK)
  have hβw : ((Multiplicative.toAdd (β ⟨w, hwK⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
      SecE.vThree := by
    have e1 : (⟨w, hwK⟩ : ↥(commV K)) = ⟨(d : MulAut W) z, hinv _ d.2 _ hzK⟩ * ⟨z, hzK⟩⁻¹ :=
      rfl
    rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg,
      hco d ⟨z, hzK⟩, hβz, show θ d = SecE.cThree' from θ.apply_symm_apply _,
      ← SecE.pact_cThree'_zThree]
    congr 1
    funext i
    exact ZMod.neg_eq_self_mod_two _
  refine ⟨k, hk, ?_, d, hd, z, Subgroup.subset_closure ⟨d, hd, u, rfl⟩, ?_, ?_⟩
  · intro hkk
    apply SecE.cThree_mul_self_ne_one
    have : θ (k * k) = 1 := by
      rw [show k * k = 1 from Subtype.ext hkk, map_one]
    rwa [map_mul, show θ k = SecE.cThree from θ.apply_symm_apply _] at this
  · have e2 := hco k ⟨w, hwK⟩
    rw [hβw, show θ k = SecE.cThree from θ.apply_symm_apply _, SecE.pact_cThree_vThree,
      ← hβw] at e2
    have := β.injective (Multiplicative.toAdd.injective (Subtype.ext e2))
    exact congrArg Subtype.val this
  · intro hdw
    have e2 := hco d ⟨w, hwK⟩
    rw [hβw, show θ d = SecE.cThree' from θ.apply_symm_apply _] at e2
    apply SecE.pact_cThree'_vThree
    rw [← e2, ← hβw]
    congr 4

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
