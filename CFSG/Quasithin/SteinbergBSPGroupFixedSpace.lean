module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.Quasithin.SteinbergBS

open CFSG.QuasithinUnique.Setup.Offender

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

theorem natCard_subtype_ne_add_one {M : Type*} [Finite M] (a : M) :
    Nat.card {x : M // x ≠ a} + 1 = Nat.card M := by
  classical
  rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe a)]

theorem prime_dvd_natCard_of_ne_bot {p : ℕ} [Fact p.Prime] [CharP k p] (F : Submodule k E)
    [Finite F] (hF : F ≠ ⊥) : p ∣ Nat.card F := by
  obtain ⟨w, hwF, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  have hpw : p • (⟨w, hwF⟩ : F) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have h1 : addOrderOf (⟨w, hwF⟩ : F) = p :=
    addOrderOf_eq_prime hpw fun h => hw0 (congrArg Subtype.val h)
  rw [← h1]
  exact addOrderOf_dvd_natCard _

theorem exists_fixed_ne_zero {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    {B : Subgroup (E ≃ₗ[k] E)} (hB : IsPGroup p B) (F : Submodule k E) [Finite F] (hF : F ≠ ⊥)
    (hFB : ∀ b ∈ B, ∀ w ∈ F, b w ∈ F) : ∃ w ∈ F, w ≠ 0 ∧ ∀ b ∈ B, b w = w := by
  let S : SubMulAction B E :=
    { carrier := {w | w ∈ F ∧ w ≠ 0}
      smul_mem' := fun b w hw => ⟨hFB b b.2 w hw.1, fun h => hw.2 (by
        have h1 : (b : E ≃ₗ[k] E) w = (b : E ≃ₗ[k] E) 0 := by
          rw [map_zero]
          exact h
        exact (b : E ≃ₗ[k] E).injective h1)⟩ }
  have hScard : Nat.card S + 1 = Nat.card F := by
    rw [← natCard_subtype_ne_add_one (0 : F)]
    congr 1
    exact Nat.card_congr
      { toFun := fun w => ⟨⟨w, w.2.1⟩, fun h => w.2.2 (congrArg Subtype.val h)⟩
        invFun := fun w => ⟨w.1, w.1.2, fun h => w.2 (Subtype.ext h)⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  have hpF := prime_dvd_natCard_of_ne_bot F hF (p := p)
  have hpS : ¬ p ∣ Nat.card S := by
    intro h
    have h1 : p ∣ Nat.card F - Nat.card S := Nat.dvd_sub hpF h
    rw [← hScard, Nat.add_sub_cancel_left] at h1
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨⟨w, hwF, hw0⟩, hfix⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card S hpS
  exact ⟨w, hwF, hw0, fun b hb => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨b, hb⟩)⟩

theorem finite_linearEquiv [Finite E] : Finite (E ≃ₗ[k] E) :=
  Finite.of_injective (fun e : E ≃ₗ[k] E => (e : E → E)) DFunLike.coe_injective

theorem commuting_p_group_fixed_space_kernel {p : ℕ} [hp : Fact p.Prime] [Finite k] [CharP k p]
    [FiniteDimensional k E] (B : Subgroup (E ≃ₗ[k] E)) (hB : IsPGroup p B) :
    IsPGroup p ↥(Subgroup.centralizer (B : Set (E ≃ₗ[k] E)) ⊓
      centSub (MonoidHom.id (E ≃ₗ[k] E)) (fixGL B)) := by
  have : Finite E := Module.finite_of_finite k
  have : Finite (E ≃ₗ[k] E) := finite_linearEquiv
  set K := Subgroup.centralizer (B : Set (E ≃ₗ[k] E)) ⊓
    centSub (MonoidHom.id (E ≃ₗ[k] E)) (fixGL B) with hK
  refine IsPGroup.of_card
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_)
  by_contra hdp
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨a', hao⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hao' : orderOf (a' : E ≃ₗ[k] E) = d := by
    rw [Subgroup.orderOf_coe, hao]
  set a : E ≃ₗ[k] E := (a' : E ≃ₗ[k] E) with ha
  have haC : a ∈ Subgroup.centralizer (B : Set (E ≃ₗ[k] E)) := a'.2.1
  have haK : a ∈ centSub (MonoidHom.id (E ≃ₗ[k] E)) (fixGL B) := a'.2.2
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao'
    exact hd.one_lt.ne' hao'.symm
  set T : E →ₗ[k] E := (a : E →ₗ[k] E) - LinearMap.id with hT
  have hTv : ∀ v : E, T v = a v - v := fun v => rfl
  set F := LinearMap.range T with hF
  have hmemF : ∀ v : E, a v - v ∈ F := fun v => ⟨v, hTv v⟩
  have hFne : F ≠ ⊥ := by
    intro h
    apply ha1
    refine LinearEquiv.ext fun v => ?_
    have h1 := hmemF v
    rw [h, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hFB : ∀ b ∈ B, ∀ w ∈ F, b w ∈ F := by
    rintro b hb _ ⟨v, rfl⟩
    have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.1 haC b hb).symm
    have h1 : b (a v - v) = a (b v) - b v := by
      rw [map_sub, ← LinearEquiv.mul_apply, ← hab, LinearEquiv.mul_apply]
    rw [hTv, h1]
    exact hmemF _
  obtain ⟨w, ⟨v, hv⟩, hw0, hwB⟩ := exists_fixed_ne_zero hB F hFne hFB
  have hw : w = a v - v := by rw [← hv, hTv]
  have haw : a w = w := haK w hwB
  have hpow : ∀ n : ℕ, (a ^ n) v = v + n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, haw, succ_nsmul]
      rw [hw]
      abel
  have hd0 : d • w = 0 := by
    have h1 := hpow d
    rw [← hao', pow_orderOf_eq_one] at h1
    have h2 : v = v + orderOf a • w := h1
    rw [hao'] at h2
    exact (add_eq_left.1 h2.symm)
  have hdk : (d : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k p] at h
    exact hdp ((Nat.prime_dvd_prime_iff_eq hp.out hd).1 h).symm
  rw [← Nat.cast_smul_eq_nsmul k] at hd0
  exact hw0 ((smul_eq_zero.1 hd0).resolve_left hdk)

theorem p_centralizer_irreducible_module_triviality {p : ℕ} [Fact p.Prime] [Finite k]
    [CharP k p] [FiniteDimensional k E] [Nontrivial E] (S : Subgroup (E ≃ₗ[k] E))
    (hS : IsIrrAct S) (B : Subgroup (E ≃ₗ[k] E))
    (hBS : B ≤ Subgroup.centralizer (S : Set (E ≃ₗ[k] E))) (hB : IsPGroup p B) : B = ⊥ := by
  have : Finite E := Module.finite_of_finite k
  obtain ⟨w, -, hw0, hwB⟩ := exists_fixed_ne_zero hB ⊤ top_ne_bot (fun _ _ _ _ => trivial)
  have hinv : ∀ s ∈ S, ∀ u ∈ fixGL B, s u ∈ fixGL B := by
    intro s hs u hu b hb
    have hbs : b * s = s * b := (Subgroup.mem_centralizer_iff.1 (hBS hb) s hs).symm
    show b (s u) = s u
    rw [← LinearEquiv.mul_apply, hbs, LinearEquiv.mul_apply]
    rw [show b u = u from hu b hb]
  rcases hS (fixGL B) hinv with h | h
  · exact absurd ((Submodule.mem_bot k).1 (h ▸ hwB : w ∈ (⊥ : Submodule k E))) hw0
  · rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine LinearEquiv.ext fun u => ?_
    have hu : u ∈ fixGL B := h ▸ Submodule.mem_top
    exact hu b hb

end CFSG.Quasithin.SteinbergBS
