module

public import CFSG.LinearAlgebra.PGLTwoNoPSquared
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

public section

namespace CFSG.StandardType.StarFour

open CFSG.Open

private theorem toGL_mem_center_iff_scalar
    {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]
    (b : Module.Basis (Fin 2) E W) (g : W ≃ₗ[E] W) :
    b.toGL g ∈ Subgroup.center (GL (Fin 2) E) ↔ ∃ a : Eˣ, ∀ w, g w = a • w := by
  constructor
  · intro hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hg
    refine ⟨a, fun w => ?_⟩
    have hga : g = LinearEquiv.smulOfUnit a := by
      have h : b.toGL (LinearEquiv.smulOfUnit a) = b.toGL g := by
        rw [Module.Basis.toGL_smulOfUnit, ha]
      exact (b.toGL.injective h).symm
    rw [hga]
    exact LinearEquiv.smulOfUnit_apply a w
  · rintro ⟨a, ha⟩
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
    rw [← Module.Basis.toGL_smulOfUnit b a]
    exact congrArg b.toGL (LinearEquiv.ext fun w => by
      rw [LinearEquiv.smulOfUnit_apply]
      exact (ha w).symm)

private theorem pow_mem_center_of_mem_sup {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.center G) {p : ℕ} (hH : ∀ h ∈ H, h ^ p = 1) {x : G}
    (hx : x ∈ H ⊔ K) : x ^ p ∈ K := by
  haveI : K.Normal := Subgroup.normal_of_le_center hK
  obtain ⟨r, hr, z, hz, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := H) (t := K)).mp hx
  have hcomm : Commute r z := Subgroup.mem_center_iff.mp (hK hz) r
  rw [hcomm.mul_pow p, hH r hr, one_mul]
  exact K.pow_mem hz p

theorem finrank_ne_two_of_elemAbelian_action {E : Type*} [Field E] [Finite E]
    {W : Type*} [AddCommGroup W] [Module E W] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpE : (p : E) ≠ 0) {B : Type*} [CommGroup B] (hBp : ∀ b : B, b ^ p = 1)
    (ρ : B →* (W ≃ₗ[E] W)) (D : Subgroup B) (hD : Nat.card D ≤ p ^ 2)
    (hker : ∀ b : B, (∃ a : Eˣ, ∀ w, ρ b w = a • w) → b ∈ D) (hB : p ^ 4 ≤ Nat.card B) :
    Module.finrank E W ≠ 2 := by
  intro hfr
  haveI : Module.Finite E W := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  let b : Module.Basis (Fin 2) E W := Module.finBasisOfFinrankEq E W hfr
  let Z : Subgroup (GL (Fin 2) E) := Subgroup.center (GL (Fin 2) E)
  let ρ' : B →* GL (Fin 2) E := b.toGL.toMonoidHom.comp ρ
  let B' : Subgroup (GL (Fin 2) E) := ρ'.range ⊔ Z
  have hZB' : Z ≤ B' := le_sup_right
  have hscalar : ∀ c : B, (ρ' c ∈ Z ↔ ∃ a : Eˣ, ∀ w, ρ c w = a • w) :=
    fun c => toGL_mem_center_iff_scalar b (ρ c)
  have hB'le : B' ≤ Subgroup.centralizer (B' : Set (GL (Fin 2) E)) := by
    change (ρ'.range ⊔ Z : Subgroup (GL (Fin 2) E)) ≤
      Subgroup.centralizer (B' : Set (GL (Fin 2) E))
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨r, hr, z, hz, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := ρ'.range) (t := Z)).mp hh
      have hzx : z * x = x * z := (Subgroup.mem_center_iff.mp hz x).symm
      have hrx : r * x = x * r := setLike_mul_comm hr hx
      calc (r * z) * x = r * (z * x) := by rw [mul_assoc]
        _ = r * (x * z) := by rw [hzx]
        _ = (r * x) * z := by rw [mul_assoc]
        _ = (x * r) * z := by rw [hrx]
        _ = x * (r * z) := by rw [mul_assoc]
    · intro x hx
      exact Subgroup.center_le_centralizer (B' : Set (GL (Fin 2) E)) hx
  haveI hB'comm : IsMulCommutative B' :=
    IsMulCommutative.of_setLike_mul_comm fun a ha c hc =>
      (Subgroup.mem_centralizer_iff.mp (hB'le ha) c hc).symm
  let N : Subgroup B' := Z.subgroupOf B'
  let ρB : B →* B' := ρ'.codRestrict B' fun c =>
    Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨c, rfl⟩)
  let f : B →* (B' ⧸ N) := (QuotientGroup.mk' N).comp ρB
  have hQcomm : IsMulCommutative (B' ⧸ N) := by
    refine IsMulCommutative.of_comm fun a c => ?_
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (N := N) a
    obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (N := N) c
    rw [← map_mul, ← map_mul, mul_comm' a' c']
  have hHp : ∀ h ∈ ρ'.range, h ^ p = 1 := by
    intro h hh
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hh
    rw [← map_pow, hBp c, map_one]
  have hQelem : IsElemAbelian p (⊤ : Subgroup (B' ⧸ N)) := by
    haveI : IsMulCommutative (B' ⧸ N) := hQcomm
    refine ⟨inferInstance, ?_⟩
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := N) x
    rw [← map_pow]
    change ((y ^ p : B') : B' ⧸ N) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using
      pow_mem_center_of_mem_sup (le_rfl : Z ≤ Subgroup.center (GL (Fin 2) E)) hHp y.2
  have hcardQ : Nat.card (B' ⧸ N) ≤ p := by
    haveI : Fintype E := Fintype.ofFinite E
    exact CFSG.LinearAlgebra.not_pSq_pgl_two hp hpE B' hZB' hQelem
  have hker_le : f.ker ≤ D := by
    intro c hc
    apply hker c
    have hmemN : ρB c ∈ N := by
      have h2 : (ρB c : B' ⧸ N) = 1 := hc
      rwa [QuotientGroup.eq_one_iff] at h2
    have hmemZ : (ρB c : GL (Fin 2) E) ∈ Z := by
      rwa [Subgroup.mem_subgroupOf] at hmemN
    exact (hscalar c).mp hmemZ
  have hf_surj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := N) q
    obtain ⟨r, hr, z, hz, hyz⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := ρ'.range) (t := Z)).mp y.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hr
    refine ⟨c, ?_⟩
    have hy : y = (⟨r, Subgroup.mem_sup_left hr⟩ : B') *
        ⟨z, Subgroup.mem_sup_right hz⟩ :=
      Subtype.ext hyz.symm
    have hzN : (⟨z, Subgroup.mem_sup_right hz⟩ : B') ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    have hz1 : QuotientGroup.mk' N (⟨z, Subgroup.mem_sup_right hz⟩ : B') = 1 := by
      change ((⟨z, Subgroup.mem_sup_right hz⟩ : B') : B' ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hzN
    rw [hy, map_mul, hz1, mul_one]
    show QuotientGroup.mk' N (ρB c) = QuotientGroup.mk' N ⟨r, Subgroup.mem_sup_left hr⟩
    exact congrArg (QuotientGroup.mk' N) (Subtype.ext hc)
  haveI : Finite B := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0] at hB
    exact absurd hB (not_le.mpr (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) 4))
  have hcardK : Nat.card f.ker ≤ p ^ 2 := by
    calc Nat.card f.ker ≤ Nat.card D :=
          Nat.card_le_card_of_injective
            (fun x : f.ker => (⟨x.1, hker_le x.2⟩ : D)) (by
              intro x y hxy
              exact Subtype.ext (congrArg (fun z : D => (z : B)) hxy))
      _ ≤ p ^ 2 := hD
  have hcardB : Nat.card B = Nat.card (B' ⧸ N) * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf_surj).toEquiv
  have hle : p ^ 4 ≤ p ^ 3 := by
    calc p ^ 4 ≤ Nat.card B := hB
      _ = Nat.card (B' ⧸ N) * Nat.card f.ker := hcardB
      _ ≤ p * p ^ 2 := Nat.mul_le_mul hcardQ hcardK
      _ = p ^ 3 := by ring
  exact absurd hle (not_le.mpr
    (Nat.pow_lt_pow_right (Nat.Prime.one_lt (Fact.out : p.Prime)) (by norm_num : 3 < 4)))

end CFSG.StandardType.StarFour
