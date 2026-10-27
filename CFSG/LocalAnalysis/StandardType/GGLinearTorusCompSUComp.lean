module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover

namespace SUTorus

variable {K : Type} [Field K] {f m : ℕ} {G : Type*} [Group G]

theorem mul_comm_of_map_mul_comm (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {I : Finset (Fin (m + 1))}
    {k : Fin (m + 1)} (hk : k ∉ I) {z u : ↥(unitarySU 2 f K (m + 1))}
    (hzu : z * u * z⁻¹ ∈ TableBUE.blockSU I) (hu : u ∈ TableBUE.blockSU I)
    (hc : ψ z * ψ u = ψ u * ψ z) : z * u = u * z := by
  set c := z * u * z⁻¹ * u⁻¹ with hcdef
  have hcker : c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hcZ := hker hcker
  have hcB : c ∈ TableBUE.blockSU I :=
    (TableBUE.blockSU I).mul_mem hzu ((TableBUE.blockSU I).inv_mem hu)
  obtain ⟨l, hl⟩ := TableBUE.mem_scalars_of_commute h hp hpq (N := (c : GL (Fin (m + 1)) K))
    fun g hg => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨g, hg⟩)).symm
  have hkk := hcB k k (Or.inl hk)
  rw [← hl, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
    one_apply_eq] at hkk
  have hl1 : l = 1 := Units.ext hkk
  have hc1 : c = 1 := Subtype.ext (by rw [← hl, hl1, map_one]; rfl)
  calc z * u = c * u * z := by rw [hcdef]; group
    _ = u * z := by rw [hc1, one_mul]

omit [Group G] in
theorem offDiag_eq_zero_of_commute_blockSU (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {z : ↥(unitarySU 2 f K (m + 1))} (hz : z ∈ diagCentU f S δ)
    (hc : ∀ i, ∀ u ∈ TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i),
      z * u = u * z)
    (a b : Fin (m + 1)) (hab : a ≠ b) :
    ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a b = 0 := by
  classical
  by_contra h0
  have hmem : b ∈ LinTorus.diagClass S δ a :=
    LinTorus.mem_diagClass.mpr fun e he => (eq_of_mem_diagCentU hz h0 he).symm
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  obtain ⟨ζ, hζo, hζq⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hp hpq
  have hζ2 : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [he]; exact mul_inv_cancel ζ
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hζo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set t : Fin (m + 1) → Kˣ := Pi.mulSingle a ζ * Pi.mulSingle b ζ⁻¹ with ht
  have hta : t a = ζ := by simp [ht, hab]
  have htb : t b = ζ⁻¹ := by simp [ht, Ne.symm hab]
  have htk : ∀ k, k ≠ a → k ≠ b → t k = 1 := fun k hka hkb => by simp [ht, hka, hkb]
  have htmem : diagHom (m + 1) t ∈ unitarySU 2 f K (m + 1) := by
    refine TableBUE.diagHom_mem_unitarySU h (fun k => ?_) ?_
    · simp only [ht, Pi.mul_apply, Pi.mulSingle_apply]
      split_ifs <;> simp [hζq, inv_pow]
    · simp only [ht, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel ζ
  have htB : (⟨diagHom (m + 1) t, htmem⟩ : ↥(unitarySU 2 f K (m + 1))) ∈
      TableBUE.blockSU (LinTorus.diagClass S δ a) := by
    intro i j hij
    show ((diagHom (m + 1) t : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j
    rw [coe_diagHom]
    by_cases hij' : i = j
    · subst hij'
      have hi : i ∉ LinTorus.diagClass S δ a := hij.elim id id
      have hia : i ≠ a := fun h' => hi (h' ▸ LinTorus.self_mem_diagClass S δ a)
      have hib : i ≠ b := fun h' => hi (h' ▸ hmem)
      rw [diagonal_apply_eq, htk i hia hib, Units.val_one, one_apply_eq]
    · rw [diagonal_apply_ne _ hij', one_apply_ne hij']
  have h1 := hc a _ htB
  have h2 : (z : GL (Fin (m + 1)) K) * diagHom (m + 1) t = diagHom (m + 1) t * z :=
    congrArg Subtype.val h1
  exact h0 (TableBUE.entry_eq_zero_of_commute h2 (by rw [hta, htb]; exact hζ2))

theorem exists_le_map_blockSU [Finite G] (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ)
    {J : Subgroup G} (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S)) :
    ∃ i, J ≤ (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ := by
  by_contra hno
  push Not at hno
  have hcomm : ∀ i,
      ⁅J, (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ⁆ = ⊥ :=
    fun i => (isComponentOf_le_or_commutator_eq_bot hJ
      (isSubnormal_map_blockSU hker hδ i)).resolve_left (hno i)
  have hproper : ∀ i, ∃ k, k ∉ LinTorus.diagClass S δ i := by
    intro i
    by_contra hall
    push Not at hall
    apply hno i
    rw [show LinTorus.diagClass S δ i = Finset.univ from Finset.eq_univ_iff_forall.mpr hall,
      blockSU_univ, ← MonoidHom.range_eq_map]
    exact hJ.1.trans inf_le_left
  have hJD := le_map_diagCentU hker hδ hJ.1 (commutator_self_eq_of_isQuasisimple hJ.2.2)
  have hdiag : ∀ x ∈ J, ∃ z : ↥(unitarySU 2 f K (m + 1)), ψ z = x ∧ ∀ a b, a ≠ b →
      ((z : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a b = 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hJD hx
    refine ⟨z, rfl, offDiag_eq_zero_of_commute_blockSU h hp hpq hz fun i u hu => ?_⟩
    obtain ⟨k, hk⟩ := hproper i
    have hzc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i) hx
    exact mul_comm_of_map_mul_comm h hp hpq hker hk (conj_mem_blockSU_of_mem_diagCentU hz hu) hu
      (Subgroup.mem_centralizer_iff.mp hzc (ψ u) ⟨u, hu, rfl⟩).symm
  apply commutator_ne_bot_of_isQuasisimple hJ.2.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨z₁, rfl, hz₁⟩ := hdiag x hx
  obtain ⟨z₂, rfl, hz₂⟩ := hdiag y hy
  rw [← map_mul, ← map_mul, mul_comm_of_offDiag_eq_zero hz₂ hz₁]

end SUTorus

end CFSG.StandardType
