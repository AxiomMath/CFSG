module

public import CFSG.Quasithin.EmptyFaithful.S152He4Layer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AOut
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.He4 (NoInvCommNine NoInvCommNine.of_injective noInvCommNine_gl)
open CFSG.Quasithin.Stellmacher.L3YC (eq_zero_or_one_of_card_two ringEquiv_eq_one_of_card_two
  conjAut_mem_range_of_card_two inner_of_three_pow_projectiveSL)
open Matrix

theorem false_of_autConf_of_noInvCommNine {M : Type} [Group M] (hZ : Subgroup.center M = ⊥)
    (hN : NoInvCommNine M) {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb)
    (hν : ν ∈ (MulAut.conj : M →* MulAut M).range)
    (hPin : Pb ≤ (MulAut.conj : M →* MulAut M).range) (hP : Nat.card Pb = 9) : False := by
  have hcj := conj_injective_of_center_eq_bot hZ
  obtain ⟨g, rfl⟩ := hν
  have hg2 : g * g = 1 := hcj (by rw [map_mul, ← pow_two, h.sq, map_one])
  have hg1 : g ≠ 1 := fun h1 => h.ne_one (by rw [h1, map_one])
  have hcard : Nat.card (Pb.comap (MulAut.conj : M →* MulAut M)) = 9 := by
    rw [← hP, ← Subgroup.card_map_of_injective hcj, Subgroup.map_comap_eq_self hPin]
  refine hg1 (hN _ hcard g hg2 fun p hp => hcj ?_)
  rw [map_mul, map_mul]
  exact h.comm _ (h.le hp)

section CardTwo

variable {F : Type} [Field F] [Finite F]

theorem eq_conj_or_eq_conj_mul_dualAut (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n F)) :
    ∃ g : projectiveSL n F, α = MulAut.conj g ∨ α = MulAut.conj g * dualAut n F := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation hn).2 α
  obtain ⟨g, hg⟩ := conjAut_mem_range_of_card_two hF A
  refine ⟨g, ?_⟩
  rw [ringEquiv_eq_one_of_card_two hF σ, map_one, mul_one, ← hg]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exact Or.inl (by rw [pow_zero, mul_one])
  · exact Or.inr (by rw [pow_one])

end CardTwo

section L52

@[expose] def l52A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩

@[expose] def l52B : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩

@[expose] def l52T34 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1], by decide +kernel⟩

@[expose] def l52T23 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩

theorem l52T_mem_unitriangular {t : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (ht : t = l52T34 ∨ t = l52T23) : t ∈ unitriangular 5 (ZMod 2) := by
  have h1 : ∀ i j : Fin 5, j < i → (l52T34 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0 := by
    intro i
    fin_cases i <;> decide +kernel
  have h2 : ∀ i : Fin 5, (l52T34 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i i = 1 := by decide +kernel
  have h3 : ∀ i j : Fin 5, j < i → (l52T23 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0 := by
    intro i
    fin_cases i <;> decide +kernel
  have h4 : ∀ i : Fin 5, (l52T23 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i i = 1 := by decide +kernel
  rcases ht with rfl | rfl
  · exact ⟨h1, h2⟩
  · exact ⟨h3, h4⟩

theorem proj_injective_l52 : Function.Injective (proj 5 (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, eq_bot_iff]
  rintro A ⟨c, -, hc⟩
  have hc1 : (c : ZMod 2) = 1 :=
    (eq_zero_or_one_of_card_two (Nat.card_zmod 2) (c : ZMod 2)).resolve_left c.ne_zero
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl

theorem center_l52 : Subgroup.center (projectiveSL 5 (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨z₀, rfl⟩ := proj_surjective 5 (ZMod 2) z
  have hz₀ : z₀ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply proj_injective_l52
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz (proj 5 (ZMod 2) x)
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz₀
  have key : ∀ s : ZMod 2, s ^ 5 = 1 → s = 1 := by decide
  have hr1 : r = 1 := key r (by simpa using hr)
  have h1 : z₀ = 1 := Subtype.ext (by rw [← hrz, hr1, map_one]; rfl)
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem exists_E9_l52 :
    ∃ E : Subgroup (projectiveSL 5 (ZMod 2)), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Finite (projectiveSL 5 (ZMod 2)) := Finite.of_surjective _ (proj_surjective 5 (ZMod 2))
  have hind : ∀ i j : Fin 3, l52A ^ (i : ℕ) * l52B ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
    decide +kernel
  refine exists_elemAbelian_nine (a := proj 5 (ZMod 2) l52A) (b := proj 5 (ZMod 2) l52B)
    ?_ ?_ ?_ fun i j h => hind i j (proj_injective_l52 ?_)
  · rw [← map_mul, ← map_mul, show l52A * l52B = l52B * l52A by decide +kernel]
  · rw [← map_pow, show l52A ^ 3 = 1 by decide +kernel, map_one]
  · rw [← map_pow, show l52B ^ 3 = 1 by decide +kernel, map_one]
  · rw [map_mul, map_pow, map_pow, h, map_one]

theorem noInvCommNine_projectiveSL_l52 : NoInvCommNine (projectiveSL 5 (ZMod 2)) := by
  let e : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ≃* projectiveSL 5 (ZMod 2) :=
    MulEquiv.ofBijective (proj 5 (ZMod 2)) ⟨proj_injective_l52, proj_surjective 5 (ZMod 2)⟩
  exact NoInvCommNine.of_injective (Matrix.SpecialLinearGroup.toGL.comp e.symm.toMonoidHom)
    (Matrix.SpecialLinearGroup.toGL_injective.comp e.symm.injective) (noInvCommNine_gl 5 le_rfl)

theorem not_fix_sylow_conj_mul_dualAut (g : projectiveSL 5 (ZMod 2))
    {S : Subgroup (projectiveSL 5 (ZMod 2))} (hS : IsSylowTwoOf S ⊤)
    (hfix : ∀ s ∈ S, (MulAut.conj g * dualAut 5 (ZMod 2)) s = s) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (projectiveSL 5 (ZMod 2)) := Finite.of_surjective _ (proj_surjective 5 (ZMod 2))
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hQ := IsPGroup.toSylow_coe hS.2.1 hidx
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (projectiveSL 5 (ZMod 2)) P (hS.2.1.toSylow hidx)
  have hmem : ∀ u ∈ unitriangular 5 (ZMod 2), h * proj 5 (ZMod 2) u * h⁻¹ ∈ S := by
    intro u hu
    have h1 : h * proj 5 (ZMod 2) u * h⁻¹ ∈
        ((h • P : Sylow 2 (projectiveSL 5 (ZMod 2))) : Set (projectiveSL 5 (ZMod 2))) := by
      rw [Sylow.coe_smul]
      refine ⟨proj 5 (ZMod 2) u, ?_, rfl⟩
      change proj 5 (ZMod 2) u ∈ (P : Subgroup (projectiveSL 5 (ZMod 2)))
      rw [hP]
      exact ⟨u, hu, rfl⟩
    rw [hh] at h1
    rw [← hQ]
    exact h1
  set δ := dualAut 5 (ZMod 2) with hδ
  set k := h⁻¹ * g * δ h with hk
  have hku : ∀ u ∈ unitriangular 5 (ZMod 2),
      k * δ (proj 5 (ZMod 2) u) = proj 5 (ZMod 2) u * k := by
    intro u hu
    have h1 := hfix _ (hmem u hu)
    rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    calc k * δ (proj 5 (ZMod 2) u)
        = h⁻¹ * (g * (δ h * δ (proj 5 (ZMod 2) u) * (δ h)⁻¹) * g⁻¹) * (g * δ h) := by
          rw [hk]; group
      _ = proj 5 (ZMod 2) u * k := by rw [h1, hk]; group
  obtain ⟨k₀, hk₀⟩ := proj_surjective 5 (ZMod 2) k
  have hmat : ∀ t : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      t ∈ unitriangular 5 (ZMod 2) → t * t = 1 →
        (k₀ : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (t : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ =
          (t : Matrix (Fin 5) (Fin 5) (ZMod 2)) * k₀ := by
    intro t ht htt
    have h1 := hku t ht
    rw [hδ, dualAut_proj, ← hk₀, ← map_mul, ← map_mul] at h1
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2))) (proj_injective_l52 h1)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    simpa only [hti, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_transpose] using h2
  have h34 := hmat l52T34 (l52T_mem_unitriangular (Or.inl rfl)) (by decide +kernel)
  have h23 := hmat l52T23 (l52T_mem_unitriangular (Or.inr rfl)) (by decide +kernel)
  have hcol : ∀ r : Fin 5, (k₀ : Matrix (Fin 5) (Fin 5) (ZMod 2)) r 4 = 0 := by
    intro r
    fin_cases r
    · have := congrFun (congrFun h34 0) 3
      simpa [Matrix.mul_apply, Fin.sum_univ_five, l52T34] using this
    · have := congrFun (congrFun h34 1) 3
      simpa [Matrix.mul_apply, Fin.sum_univ_five, l52T34] using this
    · have := congrFun (congrFun h34 2) 3
      simpa [Matrix.mul_apply, Fin.sum_univ_five, l52T34] using this
    · have := congrFun (congrFun h23 2) 4
      simpa [Matrix.mul_apply, Fin.sum_univ_five, l52T23] using this
    · have := congrFun (congrFun h34 4) 3
      simpa [Matrix.mul_apply, Fin.sum_univ_five, l52T34] using this
  have hdet := Matrix.det_eq_zero_of_column_eq_zero 4 hcol
  rw [k₀.2] at hdet
  exact one_ne_zero hdet

theorem false_of_autConf_l52 {ν : MulAut (projectiveSL 5 (ZMod 2))}
    {Lb Pb : Subgroup (MulAut (projectiveSL 5 (ZMod 2)))}
    (h : AutConf (projectiveSL 5 (ZMod 2)) ν Lb Pb) (hP : Nat.card Pb = 9) : False := by
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hPin : Pb ≤ (MulAut.conj : projectiveSL 5 (ZMod 2) →* _).range := fun p hp =>
    inner_of_three_pow_projectiveSL (by norm_num) hF p (m := 1)
      (by rw [pow_one]; exact h.elem.2 p hp)
  obtain ⟨g, hg | hg⟩ := eq_conj_or_eq_conj_mul_dualAut hF (by norm_num) ν
  · exact false_of_autConf_of_noInvCommNine center_l52 noInvCommNine_projectiveSL_l52 h
      ⟨g, hg.symm⟩ hPin hP
  · subst hg
    obtain ⟨S, hS, hSν⟩ := h.sylow
    exact not_fix_sylow_conj_mul_dualAut g hS hSν

theorem nonempty_mulEquiv_l52 {M : Type} [Group M] (hM : StatedClassicalModel M .PSL 5 2 1) :
    Nonempty (M ≃* projectiveSL 5 (ZMod 2)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
  have hF2 : Nat.card F = 2 := by simpa using hF
  exact ⟨(((e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hF2 5)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hF2 5)).trans
    (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo (Nat.card_zmod 2) 5).symm).trans
    (K1.statedProjEquivProjectiveSL 5 (ZMod 2))⟩

theorem not_psl52 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) :
    ¬ StatedClassicalModel ↥K .PSL 5 2 1 := fun hK => by
  have := hQ.finite
  obtain ⟨e⟩ := nonempty_mulEquiv_l52 hK
  obtain ⟨E, hE, hE9⟩ := exists_E9_l52
  exact false_of_autConf_l52 (h.autConf.map e) (h.card_map_rhoP_eq_nine hQ e
    (fun z hz => by rwa [center_l52, Subgroup.mem_bot] at hz) hE hE9)

end L52

end CFSG.Quasithin.H13.S126C
