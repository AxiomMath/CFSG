module

public import CFSG.Quasithin.Vol2.Ch10SecQ6L2a
public import CFSG.Quasithin.Vol2.Ch10SecDFacts12
public import CFSG.Quasithin.Vol2.Ch10SecQ6SL2b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

@[expose] def conjOn {G : Type*} [Group G] {Λ : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (Λ : Set G)) : Λ ≃* Λ where
  toFun l := ⟨n * l * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn l).mp l.2⟩
  invFun l := ⟨n⁻¹ * l * n, (Subgroup.mem_normalizer_iff.mp hn _).mpr (by
    rw [show n * (n⁻¹ * (l : G) * n) * n⁻¹ = l by group]
    exact l.2)⟩
  left_inv l := Subtype.ext (by
    change n⁻¹ * (n * (l : G) * n⁻¹) * n = l
    group)
  right_inv l := Subtype.ext (by
    change n * (n⁻¹ * (l : G) * n) * n⁻¹ = l
    group)
  map_mul' a b := Subtype.ext (by
    change n * ((a : G) * b) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹)
    group)

end C10P06

open C10P06 in
theorem fact12L2 : Fact12L2 := by
  intro W _ _ _ Λ n hn hcomm hnat E hEN hEab
  obtain ⟨K, _, _, hK, hreal⟩ := hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨π, Ψ, hc⟩ := exists_isL2Coord hreal
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    rw [Subgroup.mem_bot]
    have hfixv : ∀ v, (γ : Matrix (Fin 2) (Fin 2) K).mulVec v = v := fun v => by
      obtain ⟨w, rfl⟩ := hc.2.2.1 v
      rw [← hc.2.2.2.2 γ w, hγ]
      rfl
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h1 : (γ : Matrix (Fin 2) (Fin 2) K) i j = (Pi.single j (1 : K) : Fin 2 → K) i := by
      have h2 := congrFun (hfixv (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one] at h2
      exact h2
    rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Pi.single_apply]
  let πs : Matrix.SpecialLinearGroup (Fin 2) K ≃* Λ := MulEquiv.ofBijective π ⟨hπinj, hc.1⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hEab.2 a ha
  let F : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    { carrier := {α | ∃ e ∈ E, ∀ M, (πs (α M) : MulAut W) = e * πs M * e⁻¹}
      one_mem' := ⟨1, E.one_mem, fun M => by simp⟩
      mul_mem' := by
        rintro α β ⟨e, he, hα⟩ ⟨f, hf, hβ⟩
        exact ⟨e * f, E.mul_mem he hf, fun M => by
          rw [MulAut.mul_apply, hα, hβ]
          group⟩
      inv_mem' := by
        rintro α ⟨e, he, hα⟩
        refine ⟨e⁻¹, E.inv_mem he, fun M => ?_⟩
        have h1 := hα (α⁻¹ M)
        rw [MulAut.apply_inv_self] at h1
        rw [h1]
        group }
  have hFc : ∀ α ∈ F, ∀ β ∈ F, α * β = β * α := by
    rintro α ⟨e, he, hα⟩ β ⟨f, hf, hβ⟩
    refine MulEquiv.ext fun M => πs.injective (Subtype.ext ?_)
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα,
      show e * (f * (πs M : MulAut W) * f⁻¹) * e⁻¹ = (e * f) * πs M * (e * f)⁻¹ by group,
      hEc e he f hf]
    group
  have hF2 : ∀ α ∈ F, α * α = 1 := by
    rintro α ⟨e, he, hα⟩
    refine MulEquiv.ext fun M => πs.injective (Subtype.ext ?_)
    rw [MulAut.mul_apply, hα, hα, MulAut.one_apply,
      show e * (e * (πs M : MulAut W) * e⁻¹) * e⁻¹ = (e * e) * πs M * (e * e)⁻¹ by group,
      hE2 e he]
    group
  have hαe : ∀ e ∈ E, ∃ α : MulAut (Matrix.SpecialLinearGroup (Fin 2) K),
      ∀ M, (πs (α M) : MulAut W) = e * πs M * e⁻¹ := fun e he =>
    ⟨πs.trans ((conjOn (hEN he)).trans πs.symm), fun M => by
      change (πs (πs.symm (conjOn (hEN he) (πs M))) : MulAut W) = _
      rw [MulEquiv.apply_symm_apply]
      rfl⟩
  choose αf hαf using fun e : E => hαe e e.2
  let f : E → F := fun e => ⟨αf e, e, e.2, hαf e⟩
  have hf : Function.Injective f := by
    intro e e' h
    have h1 : αf e = αf e' := congrArg Subtype.val h
    have hcen : ∀ l ∈ Λ, ((e' : MulAut W)⁻¹ * e) * l = l * ((e' : MulAut W)⁻¹ * e) := by
      intro l hl
      obtain ⟨M, hM⟩ := πs.surjective ⟨l, hl⟩
      have h2 := hαf e M
      rw [h1, hαf e', hM] at h2
      change (e' : MulAut W) * l * (e' : MulAut W)⁻¹ = e * l * (e : MulAut W)⁻¹ at h2
      calc ((e' : MulAut W)⁻¹ * e) * l = (e' : MulAut W)⁻¹ * (e * l * (e : MulAut W)⁻¹) * e := by
            group
        _ = (e' : MulAut W)⁻¹ * (e' * l * (e' : MulAut W)⁻¹) * e := by rw [h2]
        _ = l * ((e' : MulAut W)⁻¹ * e) := by group
    have he2 : ((e' : MulAut W)⁻¹ * e) * ((e' : MulAut W)⁻¹ * e) = 1 :=
      hE2 _ (E.mul_mem (E.inv_mem e'.2) e.2)
    exact Subtype.ext (inv_mul_eq_one.mp (eq_one_of_centralizes hc hcomm he2 hcen)).symm
  calc Nat.card E ≤ Nat.card F := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card K := card_le_of_elem_aut hK (by omega) hFc hF2
    _ = 2 ^ n := hK

end CFSG.Quasithin.Vol2.Ch10.SecD
