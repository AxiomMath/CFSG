module

public import CFSG.Quasithin.H13.NQCatLieCartanTools
public import CFSG.Quasithin.H13.NQCatLieMultL34
public import CFSG.Quasithin.H13.NQCatCartanL3

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan.L3

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.KG4413 CFSG.Quasithin.H13.NQCat
  CFSG.Quasithin.H13.NQCat.SL3

variable {K : Type} [Field K]

theorem dg3_conj_tv (s : Kˣ × Kˣ) (c : K) :
    dg3 s * tv (show (0 : Fin 3) ≠ 2 by decide) c * (dg3 s)⁻¹ =
      tv (show (0 : Fin 3) ≠ 2 by decide) ((s.1 : K) * ((s.1 * s.2 : Kˣ) : K) * c) := by
  have hv : ∀ i, (![(s.1 : K), (s.2 : K), ((s.1 * s.2)⁻¹ : Kˣ)] : Fin 3 → K) i ≠ 0 := by
    intro i
    fin_cases i <;> simp
  apply Subtype.ext
  change ((dg3 s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * transvection 0 2 c *
      (((dg3 s)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    transvection 0 2 _
  have hinv : (((dg3 s)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => ((![(s.1 : K), (s.2 : K), ((s.1 * s.2)⁻¹ : Kˣ)] : Fin 3 → K) i)⁻¹) := by
    rw [← map_inv, coe_dg3]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  rw [hinv, coe_dg3, diag_conj_transvection _ hv]
  congr 1
  simp only [Fin.isValue, cons_val_zero, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
    tail_cons, head_cons, Units.val_inv_eq_inv_val, inv_inv, Units.val_mul]
  ring

theorem eq_of_proj_tv_eq {c c' : K}
    (h : proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) c) =
      proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) c')) : c = c' := by
  rw [proj_eq_proj_iff] at h
  have hu : (tv (show (0 : Fin 3) ≠ 2 by decide) c)⁻¹ * tv (show (0 : Fin 3) ≠ 2 by decide) c' ∈
      unitriangular 3 K :=
    mul_mem (inv_mem (tv_mem_unitriangular (show (0 : Fin 3) < 2 by decide) c))
      (tv_mem_unitriangular (show (0 : Fin 3) < 2 by decide) c')
  have h1 := LieMult.eq_one_of_mem_unitriangular_of_mem_scalars hu h
  have h2 : tv (show (0 : Fin 3) ≠ 2 by decide) c = tv (show (0 : Fin 3) ≠ 2 by decide) c' :=
    inv_mul_eq_one.1 h1
  have h3 := congrFun (congrFun (congrArg Subtype.val h2) 0) 2
  simpa [coe_tv, transvection, single_apply] using h3

theorem torusConcl_l3 [Finite K] [CharP K 2] : TorusConcl (projectiveSL 3 K) False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hcomm : ∀ a ∈ dL3 K, ∀ b ∈ dL3 K, a * b = b * a := by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩ _ ⟨_, ⟨s', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm s s']
  refine torusConcl_of_torus hU₀ dL3_le_normalizer ?_ odd_card_dL3 hcomm ?_
  · rw [normalizer_projUnitriangular 2, sup_comm]
    exact projUpperTriangular_le
  intro E hEU hE hE16 hEC
  have hc : ∀ x : E, ∃ c : K, (x : projectiveSL 3 K) =
      proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) c) := by
    intro x
    obtain ⟨u, hu, hux⟩ := hEU x.2
    have hcomm : ∀ {a b : Fin 3} (hab : a < b),
        proj 3 K (tv hab.ne 1) * proj 3 K u = proj 3 K u * proj 3 K (tv hab.ne 1) := by
      intro a b hab
      rw [hux]
      exact Subgroup.mem_centralizer_iff.mp (hEC x.2) _
        ⟨tv hab.ne 1, tv_mem_unitriangular hab 1, rfl⟩
    obtain ⟨h01, h12⟩ := LieMult.entries_eq_zero_of_commute hu
      (hcomm (show (0 : Fin 3) < 1 by decide)) (hcomm (show (1 : Fin 3) < 2 by decide))
    refine ⟨(u : Matrix (Fin 3) (Fin 3) K) 0 2, ?_⟩
    have e0 : ∀ {a b : Fin 3} (hab : a ≠ b), tv hab (0 : K) = 1 := fun hab =>
      Subtype.ext (by rw [coe_tv]; simp [transvection])
    have hu' := eq_tv_mul_of_mem_unitriangular hu
    rw [h01, h12, mul_zero, sub_zero, e0, e0, one_mul, mul_one] at hu'
    rw [← hux]
    exact congrArg (proj 3 K) hu'
  choose β hβ using hc
  have hβinj : Function.Injective β := fun x y hxy => Subtype.ext (by rw [hβ x, hβ y, hxy])
  have h16 : 16 ≤ Nat.card K := by
    rw [← hE16]
    exact Nat.card_le_card_of_injective β hβinj
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE16]; norm_num)
    exact exists_ne 1
  have hc₀ : β x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply Subtype.ext
    rw [hβ x₀, h0, Subgroup.coe_one]
    have : tv (show (0 : Fin 3) ≠ 2 by decide) (0 : K) = 1 :=
      Subtype.ext (by rw [coe_tv]; simp [transvection])
    rw [this, map_one]
  have hconj : ∀ (s : Kˣ × Kˣ) (c : K), proj 3 K (dg3 s) *
      proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) c) * (proj 3 K (dg3 s))⁻¹ =
      proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) ((s.1 : K) * ((s.1 * s.2 : Kˣ) : K) * c)) := by
    intro s c
    rw [← dg3_conj_tv, map_mul, map_mul, map_inv]
  have hcomm_iff : ∀ (s : Kˣ × Kˣ), proj 3 K (dg3 s) ∈
      Subgroup.centralizer (E : Set (projectiveSL 3 K)) →
      (s.1 : K) * ((s.1 * s.2 : Kˣ) : K) = 1 := by
    intro s hs
    have h1 := Subgroup.mem_centralizer_iff.1 hs (x₀ : projectiveSL 3 K) x₀.2
    rw [hβ x₀] at h1
    have h2 : proj 3 K (dg3 s) * proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) (β x₀)) *
        (proj 3 K (dg3 s))⁻¹ = proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) (β x₀)) := by
      rw [← h1]
      group
    rw [hconj] at h2
    have h3 := eq_of_proj_tv_eq h2
    exact (mul_left_eq_self₀.1 h3).resolve_right hc₀
  let φ : Kˣ →* projectiveSL 3 K := (proj 3 K).comp (dg3.comp (MonoidHom.inr Kˣ Kˣ))
  refine ⟨lt_of_lt_of_le ?_ (card_le_relIndex_of_hom φ (fun b => ⟨_, ⟨(1, b), rfl⟩, rfl⟩)
    fun b hb => ?_), fun h0 => ?_⟩
  · rw [Nat.card_units]
    omega
  · have h1 := hcomm_iff (1, b) hb
    simp only [one_mul, Units.val_one] at h1
    exact Units.ext h1
  ·
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    have hg3 : g ^ 3 ≠ 1 := by
      intro h3
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hg, Nat.card_units] at h4
      have := Nat.le_of_dvd (by norm_num) h4
      omega
    have hmem : proj 3 K (dg3 (g, g⁻¹ * g⁻¹)) ∈ dL3 K ⊓
        Subgroup.centralizer (E : Set (projectiveSL 3 K)) := by
      refine ⟨⟨_, ⟨(g, g⁻¹ * g⁻¹), rfl⟩, rfl⟩, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [show w = proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) (β ⟨w, hw⟩)) from hβ ⟨w, hw⟩]
      have h1 := hconj (g, g⁻¹ * g⁻¹) (β ⟨w, hw⟩)
      have h2 : ((g, g⁻¹ * g⁻¹).1 : K) * (((g, g⁻¹ * g⁻¹).1 * (g, g⁻¹ * g⁻¹).2 : Kˣ) : K) = 1 := by
        simp only
        rw [← Units.val_mul, show g * (g * (g⁻¹ * g⁻¹)) = 1 by group, Units.val_one]
      rw [h2, one_mul] at h1
      calc proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) (β ⟨w, hw⟩)) *
            proj 3 K (dg3 (g, g⁻¹ * g⁻¹)) =
          (proj 3 K (dg3 (g, g⁻¹ * g⁻¹)) * proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide)
            (β ⟨w, hw⟩)) * (proj 3 K (dg3 (g, g⁻¹ * g⁻¹)))⁻¹) *
            proj 3 K (dg3 (g, g⁻¹ * g⁻¹)) := by rw [h1]
        _ = proj 3 K (dg3 (g, g⁻¹ * g⁻¹)) *
            proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) (β ⟨w, hw⟩)) := by group
    rw [h0, Subgroup.mem_bot, proj_eq_one_iff] at hmem
    have h1 : g = g⁻¹ * g⁻¹ := CartanL3.fst_eq_snd_of_dg3_mem_scalars hmem
    apply hg3
    calc g ^ 3 = g * g * g := pow_three' g
      _ = g * g * (g⁻¹ * g⁻¹) := by rw [← h1]
      _ = 1 := by group

end CFSG.Quasithin.H13.NQCat.LieCartan.L3
