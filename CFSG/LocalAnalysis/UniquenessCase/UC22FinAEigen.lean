module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinAEigenBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.LinearThreeKit Matrix Subgroup
open scoped commutatorElement MatrixGroups

section

variable {K : Type} [Field K]

local notation "M₃" => Matrix (Fin 3) (Fin 3) K

local notation "PS" => stabilizer (flagSpace 3 K 1)

private theorem mem_stab_of_proj {g : SL(3, K)}
    (h : proj 3 K g ∈ projStabilizer (flagSpace 3 K 1)) : g ∈ PS := by
  rw [← comap_projStabilizer]
  exact h

private def entryHom : PS →* K where
  toFun g := ((g : SL(3, K)) : M₃) 0 0
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three]
    rw [apply_zero_eq_zero_of_mem_stabilizer_one h.2 (k := 1) (by decide),
      apply_zero_eq_zero_of_mem_stabilizer_one h.2 (k := 2) (by decide)]
    ring

private theorem entry_mul {a b : SL(3, K)} (ha : a ∈ PS) (hb : b ∈ PS) :
    ((a * b : SL(3, K)) : M₃) 0 0 = (a : M₃) 0 0 * (b : M₃) 0 0 :=
  map_mul entryHom ⟨a, ha⟩ ⟨b, hb⟩

private theorem entry_pow {a : SL(3, K)} (ha : a ∈ PS) (n : ℕ) :
    ((a ^ n : SL(3, K)) : M₃) 0 0 = (a : M₃) 0 0 ^ n :=
  map_pow entryHom ⟨a, ha⟩ n

private theorem entry_inv {a : SL(3, K)} (ha : a ∈ PS) :
    ((a⁻¹ : SL(3, K)) : M₃) 0 0 = ((a : M₃) 0 0)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← entry_mul (inv_mem ha) ha, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]

private theorem eq_one_of_mem_scalars {z : SL(3, K)} (hz : z ∈ scalars 3 K)
    (h : (z : M₃) 0 0 = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := hz
  have h' : (c : K) = 1 := by simpa [hc] using h
  exact Subtype.ext (by rw [hc, h', map_one, Matrix.SpecialLinearGroup.coe_one])

private theorem entry_pow_three_of_mem_scalars {z : SL(3, K)} (hz : z ∈ scalars 3 K) :
    (z : M₃) 0 0 ^ 3 = 1 := by
  obtain ⟨c, hc3, hc⟩ := hz
  simpa [hc] using congrArg Units.val hc3

private theorem pow_three_of_mem_scalars {z : SL(3, K)} (hz : z ∈ scalars 3 K) : z ^ 3 = 1 := by
  obtain ⟨c, hc3, hc⟩ := hz
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, ← Units.val_pow_eq_pow_val, hc3,
    Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

private theorem commute_of_proj {a b : SL(3, K)} (ha : a ∈ PS) (hb : b ∈ PS)
    (h : proj 3 K a * proj 3 K b = proj 3 K b * proj 3 K a) : Commute a b := by
  have hs : ⁅a, b⁆ ∈ scalars 3 K := by
    rw [← proj_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h1 : ((⁅a, b⁆ : SL(3, K)) : M₃) 0 0 = 1 :=
    map_commutatorElement_eq_one (entryHom (K := K)) ⟨a, ha⟩ ⟨b, hb⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_scalars hs h1)

variable {E : Subgroup (projectiveSL 3 K)} (hEP : E ≤ projStabilizer (flagSpace 3 K 1))
  (hab : IsMulCommutative E)

include hEP hab in
private theorem commute_of_mem {a b : SL(3, K)} (ha : proj 3 K a ∈ E) (hb : proj 3 K b ∈ E) :
    Commute a b := by
  refine commute_of_proj (mem_stab_of_proj (hEP ha)) (mem_stab_of_proj (hEP hb)) ?_
  exact congrArg Subtype.val (hab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)

private def lift : Subgroup SL(3, K) where
  carrier := {g | proj 3 K g ∈ E ∧ g ^ Nat.card E = 1}
  one_mem' := ⟨by rw [map_one]; exact E.one_mem, one_pow _⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact E.mul_mem ha.1 hb.1, by
    rw [(commute_of_mem hEP hab ha.1 hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv]; exact E.inv_mem ha.1, by
    rw [inv_pow, ha.2, inv_one]⟩

private theorem lift_le : lift hEP hab ≤ PS := fun _ hg => mem_stab_of_proj (hEP hg.1)

variable (h3 : ¬ 3 ∣ Nat.card E)

include h3 in
private theorem eq_one_of_mem_lift {g : SL(3, K)} (hg : g ∈ lift hEP hab) (h1 : proj 3 K g = 1) :
    g = 1 := by
  have hs : g ∈ scalars 3 K := proj_eq_one_iff.mp h1
  have hc : Nat.Coprime 3 (Nat.card E) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  refine eq_one_of_mem_scalars hs ((pow_eq_one_iff_of_coprime hc).mp ⟨?_, ?_⟩)
  · exact entry_pow_three_of_mem_scalars hs
  · rw [← entry_pow (lift_le hEP hab hg), hg.2, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]

include h3 in
private theorem exists_lift {b : projectiveSL 3 K} (hb : b ∈ E) :
    ∃ g ∈ lift hEP hab, proj 3 K g = b := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K b
  set n := Nat.card E with hn
  have hbn : proj 3 K g ^ n = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hb⟩ : E)))
  have hz : g ^ n ∈ scalars 3 K := by rw [← proj_eq_one_iff, map_pow, hbn]
  obtain ⟨k, hk⟩ : 3 ∣ 1 + 2 * n ^ 2 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;>
      simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]
  refine ⟨g ^ (1 + 2 * n ^ 2), ⟨?_, ?_⟩, ?_⟩
  · rw [map_pow]
    exact E.pow_mem hb _
  · rw [← pow_mul, pow_mul', hk, pow_mul, pow_three_of_mem_scalars hz, one_pow]
  · rw [map_pow, pow_add, pow_one, show 2 * n ^ 2 = n * (2 * n) by ring, pow_mul, hbn, one_pow,
      mul_one]

private def liftProj : lift hEP hab →* E :=
  ((proj 3 K).domRestrict (lift hEP hab)).codRestrict E fun g => g.2.1

include h3 in
private theorem liftProj_bijective : Function.Bijective (liftProj hEP hab) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun g hg => ?_, fun b => ?_⟩
  · exact Subtype.ext (eq_one_of_mem_lift hEP hab h3 g.2 (congrArg Subtype.val hg))
  · obtain ⟨g, hg, hgb⟩ := exists_lift hEP hab h3 b.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgb⟩

include h3 in
private theorem conj_eq_inv {t' : SL(3, K)} (ht : ∀ b ∈ E, proj 3 K t' * b * (proj 3 K t')⁻¹ = b⁻¹)
    {g : SL(3, K)} (hg : g ∈ lift hEP hab) : t' * g * t'⁻¹ = g⁻¹ := by
  have hmem : t' * g * t'⁻¹ * g ∈ lift hEP hab := by
    refine (lift hEP hab).mul_mem ⟨?_, ?_⟩ hg
    · rw [map_mul, map_mul, map_inv, ht _ hg.1]
      exact E.inv_mem hg.1
    · rw [conj_pow, hg.2, mul_one, mul_inv_cancel]
  have h1 : proj 3 K (t' * g * t'⁻¹ * g) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, ht _ hg.1, inv_mul_cancel]
  exact eq_inv_of_mul_eq_one_left (eq_one_of_mem_lift hEP hab h3 hmem h1)

include h3 in
private theorem mulVec_eigen {t' : SL(3, K)}
    (ht : ∀ b ∈ E, proj 3 K t' * b * (proj 3 K t')⁻¹ = b⁻¹) {g : SL(3, K)} (hg : g ∈ lift hEP hab) :
    (g : M₃) *ᵥ ((t' : M₃) *ᵥ Pi.single 0 1) = ((g : M₃) 0 0)⁻¹ • ((t' : M₃) *ᵥ Pi.single 0 1) := by
  have hgt : g * t' = t' * g⁻¹ := by
    have h := conj_eq_inv hEP hab h3 ht (inv_mem hg)
    rw [inv_inv] at h
    calc g * t' = t' * g⁻¹ * t'⁻¹ * t' := by rw [h]
      _ = t' * g⁻¹ := by group
  have hgs : g⁻¹ ∈ PS := lift_le hEP hab (inv_mem hg)
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hgt, Matrix.SpecialLinearGroup.coe_mul,
    ← mulVec_mulVec, mulVec_single_zero_of_mem_stabilizer_one hgs, mulVec_smul,
    entry_inv (lift_le hEP hab hg)]

end

theorem eigen_of_inverted {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (projectiveSL 3 K))
    (hEP : E ≤ projStabilizer (flagSpace 3 K 1))
    (hab : IsMulCommutative E) (hodd : Odd (Nat.card E)) (h3 : ¬ 3 ∣ Nat.card E)
    (t : projectiveSL 3 K) (ht : ∀ b ∈ E, t * b * t⁻¹ = b⁻¹)
    (htP : t ∉ projStabilizer (flagSpace 3 K 1)) :
    IsCyclic E ∧
      E ⊓ ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆ = ⊥ ∧
      ∃ C : Subgroup (projectiveSL 3 K),
        C ≤ ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆ ∧
        (∀ c ∈ C, ∀ b ∈ E, c * b = b * c) ∧ IsCyclic C ∧ Nat.card C = Nat.card E := by
  obtain ⟨t', rfl⟩ := proj_surjective 3 K t
  have hE₀PS := lift_le hEP hab
  have hbij := liftProj_bijective hEP hab h3
  have hcard : Nat.card (lift hEP hab) = Nat.card E := Nat.card_eq_of_bijective _ hbij
  obtain ⟨S, -, σ, hσ, ρ, hdiag⟩ := exists_point_eigenbasis (hcard ▸ hodd) hE₀PS
    (fun h => htP (mem_map_of_mem _ h)) fun g hg => mulVec_eigen hEP hab h3 ht hg
  let lam : lift hEP hab →* K := entryHom.comp (inclusion hE₀PS)
  have hlam : Function.Injective lam := by
    refine (injective_iff_map_eq_one lam).mpr fun g hg1 => ?_
    have hd := (hdiag g g.2).1
    rw [show ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 from hg1, inv_one] at hd
    have hd1 : S⁻¹ * (g : SL(3, K)) * S = 1 := Subtype.ext (by
      rw [hd, Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
      congr 1
      ext i
      fin_cases i <;> rfl)
    refine Subtype.ext ?_
    calc (g : SL(3, K)) = S * (S⁻¹ * g * S) * S⁻¹ := by group
      _ = 1 := by rw [hd1]; group
  have : IsCyclic (lift hEP hab) := isCyclic_of_injective_ringHom lam hlam
  have hEcyc : IsCyclic E := isCyclic_of_surjective (liftProj hEP hab) hbij.2
  have hc : Nat.Coprime 3 (Nat.card E) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  refine ⟨hEcyc, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro b ⟨hbE, hbC⟩
    obtain ⟨g, hg, rfl⟩ := exists_lift hEP hab h3 hbE
    rw [projStabilizer, ← map_commutator] at hbC
    obtain ⟨w, hw, hwg⟩ := mem_map.mp hbC
    obtain ⟨w, hw1, rfl⟩ := commutator_le_map_ker entryHom hw
    have hz : (w : SL(3, K))⁻¹ * g ∈ scalars 3 K := proj_eq_proj_iff.mp hwg
    have hg1 : ((g : Matrix (Fin 3) (Fin 3) K) 0 0) = 1 := by
      refine (pow_eq_one_iff_of_coprime hc).mp ⟨?_, ?_⟩
      · have h := entry_pow_three_of_mem_scalars hz
        rwa [entry_mul (inv_mem w.2) (hE₀PS hg), entry_inv w.2,
          show ((w : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 from hw1, inv_one,
          one_mul] at h
      · rw [← entry_pow (hE₀PS hg), hg.2, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    have hg' : (⟨g, hg⟩ : lift hEP hab) = 1 := hlam (by rw [map_one]; exact hg1)
    rw [mem_bot, show g = 1 from congrArg Subtype.val hg', map_one]
  · have key : ∀ b ∈ E, proj 3 K ρ * b * (proj 3 K ρ)⁻¹ = ⁅b, proj 3 K σ⁆ := by
      intro b hb
      obtain ⟨g, hg, rfl⟩ := exists_lift hEP hab h3 hb
      rw [← map_inv, ← map_mul, ← map_mul, ← map_commutatorElement, (hdiag g hg).2.1]
    refine ⟨E.map (MulAut.conj (proj 3 K ρ)).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      change proj 3 K ρ * b * (proj 3 K ρ)⁻¹ ∈ _
      rw [key b hb]
      exact commutator_mem_commutator (hEP hb) (mem_map_of_mem _ hσ)
    · rintro _ ⟨b, hb, rfl⟩ b' hb'
      change proj 3 K ρ * b * (proj 3 K ρ)⁻¹ * b' = b' * (proj 3 K ρ * b * (proj 3 K ρ)⁻¹)
      obtain ⟨g, hg, rfl⟩ := exists_lift hEP hab h3 hb
      obtain ⟨g', hg', rfl⟩ := exists_lift hEP hab h3 hb'
      simp only [← map_inv, ← map_mul]
      rw [(hdiag g hg).2.2 g' hg']
    · exact isCyclic_of_surjective _ ((MulAut.conj _).toMonoidHom.subgroupMap_surjective E)
    · exact card_map_of_injective (MulAut.conj _).injective

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
