module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res8Hess

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem mul_pow_three_of_central {G : Type*} [Group G] {a b z : G} (hz : ∀ g, z * g = g * z)
    (hba : b * a = z * (a * b)) (hz3 : z ^ 3 = 1) : (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
  have hl : ∀ g x : G, g * (z * x) = z * (g * x) := fun g x => by
    rw [← mul_assoc, ← hz g, mul_assoc]
  calc (a * b) ^ 3 = a * (b * a) * (b * a) * b := by rw [pow_three]; group
    _ = a * (z * (a * b)) * (z * (a * b)) * b := by rw [hba]
    _ = z * z * (a * a * (b * a) * b * b) := by simp only [mul_assoc, hl]
    _ = z * z * (a * a * (z * (a * b)) * b * b) := by rw [hba]
    _ = z ^ 3 * (a ^ 3 * b ^ 3) := by
        simp only [mul_assoc, hl]
        rw [pow_three, pow_three, pow_three]
        group
    _ = a ^ 3 * b ^ 3 := by rw [hz3, one_mul]

theorem mul_eq_one_or_of_cube {K : Type} [Field K] {s₁ s₂ : Kˣ} (h1 : s₁ ^ 3 = 1)
    (h2 : s₂ ^ 3 = 1) (h1' : s₁ ≠ 1) (h2' : s₂ ≠ 1) : s₁ * s₂ = 1 ∨ s₁ * s₂ ^ 2 = 1 := by
  have hv : ∀ s : Kˣ, s ^ 3 = 1 → s ≠ 1 → (s : K) ^ 2 + s + 1 = 0 := by
    intro s hs hs1
    have h3 : (s : K) ^ 3 = 1 := by
      have := congrArg Units.val hs
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have hne : (s : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hs1 (Units.ext h)
    have : ((s : K) - 1) * ((s : K) ^ 2 + s + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left hne
  have e1 := hv s₁ h1 h1'
  have e2 := hv s₂ h2 h2'
  have h13 : (s₁ : K) ^ 3 = 1 := by
    have := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have key : ((s₂ : K) - s₁) * ((s₂ : K) - s₁ ^ 2) = 0 := by
    linear_combination e2 - (s₂ : K) * e1 + h13
  rcases mul_eq_zero.mp key with h | h
  · right
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, sub_eq_zero.mp h]
    linear_combination h13
  · left
    apply Units.ext
    rw [Units.val_mul, Units.val_one, sub_eq_zero.mp h]
    linear_combination h13

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def HasCubeOneLift (x : projImage (slPi π 3 (p ^ f) K)) : Prop :=
  ∃ y ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk y = (x : ProjGenLinGroup (Fin 3) K) ∧ y ^ 3 = 1

theorem HasCubeOneLift.conj {x : projImage (slPi π 3 (p ^ f) K)} (hx : HasCubeOneLift x)
    (w : projImage (slPi π 3 (p ^ f) K)) : HasCubeOneLift (w * x * w⁻¹) := by
  obtain ⟨y, hy, hyx, hy3⟩ := hx
  obtain ⟨W, hW, hWw⟩ := exists_lift w
  refine ⟨W * y * W⁻¹, mul_mem (mul_mem hW hy) (inv_mem hW), ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hWw, hyx]
    rfl
  · rw [conj_pow, hy3, mul_one, mul_inv_cancel]

theorem exists_cube_scalar (hK : PiField π p f K) {x : projImage (slPi π 3 (p ^ f) K)}
    (hx : x ^ 3 = 1) {y : GL (Fin 3) K} (hy : y ∈ slPi π 3 (p ^ f) K)
    (hyx : ProjGenLinGroup.mk y = (x : ProjGenLinGroup (Fin 3) K)) :
    ∃ s : Kˣ, y ^ 3 = GeneralLinearGroup.scalar (Fin 3) s ∧ s ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨s, hs⟩ := exists_scalar_of_pow_eq_one hyx hx
  refine ⟨s, hs, ?_⟩
  have hdet : GeneralLinearGroup.det y = 1 := Units.ext (by
    rw [GeneralLinearGroup.val_det_apply, ((mem_slPi_iff hπ).mp hy).2, Units.val_one])
  have e := congrArg (fun g : GL (Fin 3) K => GeneralLinearGroup.det g) hs
  simp only [map_pow, hdet, one_pow] at e
  have hsd : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) s) = s ^ 3 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  rw [hsd] at e
  exact e.symm

theorem hasCubeOneLift_of_pair (hK : PiField π p f K) {e₁ e₂ : projImage (slPi π 3 (p ^ f) K)}
    (h12 : e₁ * e₂ = e₂ * e₁) (h1 : e₁ ^ 3 = 1) (h2 : e₂ ^ 3 = 1) :
    HasCubeOneLift e₁ ∨ HasCubeOneLift e₂ ∨ HasCubeOneLift (e₁ * e₂) ∨
      HasCubeOneLift (e₁ * e₂ ^ 2) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨y₁, hy₁, hy₁e⟩ := exists_lift e₁
  obtain ⟨y₂, hy₂, hy₂e⟩ := exists_lift e₂
  obtain ⟨s₁, hs₁, hs₁3⟩ := exists_cube_scalar hK h1 hy₁ hy₁e
  obtain ⟨s₂, hs₂, hs₂3⟩ := exists_cube_scalar hK h2 hy₂ hy₂e
  by_cases h1' : s₁ = 1
  · left
    exact ⟨y₁, hy₁, hy₁e, by rw [hs₁, h1', map_one]⟩
  by_cases h2' : s₂ = 1
  · right; left
    exact ⟨y₂, hy₂, hy₂e, by rw [hs₂, h2', map_one]⟩
  obtain ⟨ζ, hζ⟩ := exists_conj_of_comm h12 hy₁e hy₂e
  have hζ3 : ζ ^ 3 = 1 := by
    have hdet : ∀ y ∈ slPi π 3 (p ^ f) K, GeneralLinearGroup.det y = 1 := fun y hy => Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, ((mem_slPi_iff hπ).mp hy).2, Units.val_one])
    have e := congrArg (fun g : GL (Fin 3) K => GeneralLinearGroup.det g) hζ
    simp only [map_mul, map_inv, hdet y₁ hy₁, hdet y₂ hy₂, mul_one, inv_one] at e
    have hsd : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ζ) = ζ ^ 3 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    rw [hsd] at e
    exact e.symm
  have hcen : ∀ (u : Kˣ) (g : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * g = g * GeneralLinearGroup.scalar (Fin 3) u :=
    fun u g => (scalar_mul_comm u g).symm
  have hba : y₂ * y₁ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (y₁ * y₂) := by
    have e : y₁ * y₂ = GeneralLinearGroup.scalar (Fin 3) ζ * (y₂ * y₁) := by
      rw [← mul_assoc, ← hζ]
      group
    rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hba2 : y₂ ^ 2 * y₁ = GeneralLinearGroup.scalar (Fin 3) (ζ⁻¹ ^ 2) * (y₁ * y₂ ^ 2) := by
    calc y₂ ^ 2 * y₁ = y₂ * (y₂ * y₁) := by rw [pow_two]; group
      _ = y₂ * (GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (y₁ * y₂)) := by rw [hba]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * ((y₂ * y₁) * y₂) := by
          rw [← mul_assoc, ← hcen]; group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
          ((GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (y₁ * y₂)) * y₂) := by rw [hba]
      _ = GeneralLinearGroup.scalar (Fin 3) (ζ⁻¹ ^ 2) * (y₁ * y₂ ^ 2) := by
          rw [pow_two ζ⁻¹, map_mul, pow_two y₂]; group
  have hz3 : ∀ m : ℕ, (GeneralLinearGroup.scalar (Fin 3) (ζ⁻¹ ^ m)) ^ 3 = 1 := fun m => by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, inv_pow, hζ3, inv_one, one_pow, map_one]
  have c1 : (y₁ * y₂) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (s₁ * s₂) := by
    rw [mul_pow_three_of_central (hcen ζ⁻¹) hba (by simpa using hz3 1), hs₁, hs₂, map_mul]
  have c2 : (y₁ * y₂ ^ 2) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (s₁ * s₂ ^ 2) := by
    rw [mul_pow_three_of_central (hcen _) hba2 (hz3 2), hs₁, ← pow_mul,
      show 2 * 3 = 3 * 2 by rfl, pow_mul, hs₂, ← map_pow, map_mul]
  right; right
  rcases mul_eq_one_or_of_cube hs₁3 hs₂3 h1' h2' with h | h
  · left
    refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, ?_, by rw [c1, h, map_one]⟩
    rw [map_mul, hy₁e, hy₂e]
    rfl
  · right
    refine ⟨y₁ * y₂ ^ 2, mul_mem hy₁ (pow_mem hy₂ 2), ?_, by rw [c2, h, map_one]⟩
    rw [map_mul, map_pow, hy₁e, hy₂e]
    rfl

theorem hasCubeOneLift_of_transitive (hK : PiField π p f K)
    {E : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hEe : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set (projImage (slPi π 3 (p ^ f) K))), w * y₀ * w⁻¹ = y₁) :
    ∀ e ∈ E, e ≠ 1 → HasCubeOneLift e := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨⟨e₁, he₁⟩, he₁1⟩ : ∃ x : E, x ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
    exact exists_ne 1
  have he₁1' : e₁ ≠ 1 := fun h => he₁1 (Subtype.ext h)
  obtain ⟨e₂, he₂, he₂n⟩ : ∃ e₂ ∈ E, e₂ ∉ Subgroup.zpowers e₁ := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers e₁ := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hE9, Nat.card_zpowers] at h1
    have h2 : orderOf e₁ ∣ 3 := orderOf_dvd_of_pow_eq_one (hEe.2 e₁ he₁)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hcomm : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
  have he₂1 : e₂ ≠ 1 := fun h => he₂n (h ▸ one_mem _)
  have h12 : e₁ * e₂ ≠ 1 := by
    intro h
    apply he₂n
    have : e₂ = e₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (Subgroup.mem_zpowers e₁)
  have h122 : e₁ * e₂ ^ 2 ≠ 1 := by
    intro h
    apply he₂n
    have h2 : e₂ ^ 2 = e₁⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : e₂ ^ 3 = 1 := hEe.2 e₂ he₂
    have : e₂ = (e₂ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, h3, one_mul, pow_one]
    rw [this, h2]
    exact pow_mem (inv_mem (Subgroup.mem_zpowers e₁)) 2
  obtain ⟨x, hxE, hx1, hx⟩ : ∃ x ∈ E, x ≠ 1 ∧ HasCubeOneLift x := by
    rcases hasCubeOneLift_of_pair hK hcomm (hEe.2 e₁ he₁) (hEe.2 e₂ he₂) with h | h | h | h
    · exact ⟨e₁, he₁, he₁1', h⟩
    · exact ⟨e₂, he₂, he₂1, h⟩
    · exact ⟨e₁ * e₂, mul_mem he₁ he₂, h12, h⟩
    · exact ⟨e₁ * e₂ ^ 2, mul_mem he₁ (pow_mem he₂ 2), h122, h⟩
  intro e he he1
  obtain ⟨w, -, hw⟩ := htr x hxE hx1 e he he1
  rw [← hw]
  exact hx.conj w

@[expose] noncomputable def conjM' (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) :
    MulAut (projImage (slPi π 3 (p ^ f) K)) where
  toFun m := ⟨ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹,
    by
      obtain ⟨l, hl, hlm⟩ := m.2
      exact ⟨g * l * g⁻¹, conj_mem_slPi hπ hg hl, by rw [map_mul, map_mul, map_inv, hlm]⟩⟩
  invFun m := ⟨(ProjGenLinGroup.mk g)⁻¹ * (m : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk g,
    by
      obtain ⟨l, hl, hlm⟩ := m.2
      refine ⟨g⁻¹ * l * g⁻¹⁻¹, conj_mem_slPi hπ (inv_mem hg) hl, ?_⟩
      simp only [map_mul, map_inv, hlm, inv_inv]⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjM' (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    ((conjM' hπ hg m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹ :=
  rfl

theorem card_centMod_diagTau' (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Nat.card (centMod (slPi π 3 (p ^ f) K) (diagTau hτ)) = 3 * qSubPi π (p ^ f) ^ 2 := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have h1 := Subgroup.relIndex_mul_card (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ})
    (centMod (slPi π 3 (p ^ f) K) (diagTau hτ))
  rw [relindex_centralizer_diagTau hK hq hτ hτ1,
    inf_eq_left.mpr (centralizer_le_centMod _ _)] at h1
  obtain ⟨e⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] at h1
  rw [← h1, sq]

theorem card_centralizer_mk_dvd' {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K} (hy : y ∈ L)
    [Finite (GL (Fin 3) K)] :
    Nat.card (Subgroup.centralizer
      ({(⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ : projImage L)} : Set (projImage L))) ∣
      Nat.card (centMod L y) := by
  set yb : projImage L := ⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ with hyb
  let ρ : centMod L y →* projImage L :=
    { toFun := fun l => ⟨ProjGenLinGroup.mk (l : GL (Fin 3) K),
        ⟨l, (mem_centMod_iff_scalar.mp l.2).1, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hle : Subgroup.centralizer ({yb} : Set (projImage L)) ≤ ρ.range := by
    intro m hm
    obtain ⟨l, hl, hlm⟩ := m.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hm
    have hmem : l ∈ centMod L y := by
      refine mem_centMod_iff_scalar.mpr ⟨hl, l * y * l⁻¹ * y⁻¹, ?_, by group⟩
      have h1 : ProjGenLinGroup.mk (l * y * l⁻¹ * y⁻¹) = 1 := by
        have := congrArg Subtype.val hm
        simp only [Subgroup.coe_mul] at this
        have hyy : ProjGenLinGroup.mk y = (yb : ProjGenLinGroup (Fin 3) K) := rfl
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hlm, hyy, this, mul_inv_cancel_right,
          mul_inv_cancel]
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
      exact h1
    exact ⟨⟨l, hmem⟩, Subtype.ext hlm⟩
  calc Nat.card (Subgroup.centralizer ({yb} : Set (projImage L))) ∣ Nat.card ρ.range :=
        Subgroup.card_dvd_of_le hle
    _ ∣ Nat.card (centMod L y) := by
        rw [MonoidHom.range_eq_map]
        exact (Subgroup.card_map_dvd _ _).trans (by rw [Subgroup.card_top])

theorem card_centralizer_dvd_of_hasCubeOneLift (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {x : projImage (slPi π 3 (p ^ f) K)} (hx1 : x ≠ 1)
    (hx : HasCubeOneLift x) :
    Nat.card (Subgroup.centralizer ({x} : Set (projImage (slPi π 3 (p ^ f) K)))) ∣
      3 * qSubPi π (p ^ f) ^ 2 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, hy, hxy, hy3⟩ := hx
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply hx1
    apply Subtype.ext
    rw [← hxy, OneMemClass.coe_one, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar]
    exact (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hyo : orderOf y = 3 := by
    refine orderOf_eq_prime hy3 fun h1 => hyZ ?_
    rw [h1]
    exact one_mem _
  obtain ⟨g, hg, hgy⟩ := rank3II_4_10_three hK hq hτ hτ1 hy hyZ hyo
  have hyg : y = g * diagTau hτ * g⁻¹ := by rw [← hgy]; group
  have hxeq : x = ⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy.symm
  have hcard : Nat.card (centMod (slPi π 3 (p ^ f) K) y) = 3 * qSubPi π (p ^ f) ^ 2 := by
    rw [hyg, ← map_conj_centMod hπ hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      card_centMod_diagTau' hK hq hτ hτ1]
  rw [hxeq, ← hcard]
  exact card_centralizer_mk_dvd' hy

end CFSG.RankThree.PartTwo.Sec14.Res8Hess
