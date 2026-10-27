module

public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Elt
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Aut
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.Bender.Frame

variable {k : ℕ} {E : Type} [Field E]

theorem exists_trace_norm_fixed (hU : UnitaryFieldData 2 k E) :
    ∃ a b : E, a + hU.bar a = 1 ∧ hU.bar b = b ∧ a * hU.bar a + b * b = 1 := by
  haveI := hU.charP
  haveI := hU.finite
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hinj : Function.Injective fun x : E => x * x := fun x y hxy => by
    have h : x * x = y * y := hxy
    have h0 : (x - y) * (x - y) = 0 := by linear_combination h + (y * y - x * y) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h0)
  obtain ⟨a, -, ha, -⟩ := exists_trace_norm hU
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.1 hinj (1 + a * hU.bar a)
  have hb' : b * b = 1 + a * hU.bar a := hb
  refine ⟨a, b, ha, hinj (show hU.bar b * hU.bar b = b * b from ?_), ?_⟩
  · rw [← map_mul hU.bar, hb', map_add, map_one, map_mul, hU.bar_bar, mul_comm (hU.bar a)]
  · linear_combination hb' + (a * hU.bar a) * h2

theorem exists_invPair_commute_line (hU : UnitaryFieldData 2 k E)
    {d : frameTorusSU hU (fun i => Pi.single i 1)}
    (hd : frameEigHom (UCK.isOrthonormalFrame_single hU) 0 d =
      frameEigHom (UCK.isOrthonormalFrame_single hU) 1 d) :
    ∃ c s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧ s * c * s⁻¹ = c⁻¹ ∧
      c * QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c ∧
      s * QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * s := by
  haveI := hU.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hv := UCK.isOrthonormalFrame_single (p := 2) hU
  obtain ⟨a, b, ha, hbb, hab⟩ := exists_trace_norm_fixed hU
  set M : Matrix (Fin 3) (Fin 3) E := !![a, b, 0; b, hU.bar a, 0; 0, 0, 1] with hM
  set S : Matrix (Fin 3) (Fin 3) E := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hS
  have hMs : (M.map hU.bar)ᵀ = !![hU.bar a, b, 0; b, a, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, hU.bar_bar, hbb]
  have hMM : (M.map hU.bar)ᵀ * M = 1 := by
    rw [hMs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab
        | linear_combination (b * hU.bar a) * h2
        | linear_combination (a * b) * h2
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    simp only [hM]
    simp
    linear_combination hab - (b * b) * h2
  have hM2 : M * M = !![a + 1, b, 0; b, hU.bar a + 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab + a * ha - a * hU.bar a * h2
        | linear_combination b * ha
        | linear_combination hab + hU.bar a * ha - a * hU.bar a * h2
  have hM3 : M * (M * M) = 1 := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab + a * ha + a * (1 - hU.bar a) * h2
        | linear_combination b * ha + b * h2
        | linear_combination hab + hU.bar a * ha + hU.bar a * (1 - a) * h2
  have hSs : (S.map hU.bar)ᵀ = S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS]
  have hSS : (S.map hU.bar)ᵀ * S = 1 := by
    rw [hSs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS, Matrix.mul_apply, Fin.sum_univ_three]
  have hS2 : S * S = 1 := by
    rw [hSs] at hSS
    exact hSS
  have hSdet : S.det = 1 := by
    have h1 : S.det = -1 := by
      rw [Matrix.det_fin_three]
      simp [hS]
    rw [h1]
    linear_combination -h2
  have hSM : S * M * S = (M.map hU.bar)ᵀ := by
    rw [hMs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, hS, Matrix.mul_apply, Fin.sum_univ_three]
  obtain ⟨c, hc⟩ : ∃ c : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E),
      ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = M :=
    ⟨⟨⟨M, (M.map hU.bar)ᵀ, mul_eq_one_comm.mp hMM, hMM⟩,
      mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hMM, hdet⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E),
      ((s : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = S :=
    ⟨⟨⟨S, (S.map hU.bar)ᵀ, mul_eq_one_comm.mp hSS, hSS⟩,
      mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hSS, hSdet⟩⟩, rfl⟩
  have hc3 : c ^ 3 = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, pow_three, hM3]
    rfl))
  have hss : s * s = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hs, hS2]
    rfl))
  have hscsc : s * c * s * c = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      Units.val_mul, hs, hc, hSM, hMM]
    rfl))
  have hsc : s * c * s⁻¹ = c⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hss]
    exact eq_inv_of_mul_eq_one_left hscsc
  have hne : (QuotientGroup.mk c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ≠ 1 := by
    intro h1
    obtain ⟨u, -, -, hu⟩ := (QuotientGroup.eq_one_iff c).1 h1
    have h00 : ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 0 =
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 0 := by
      rw [hu]
    have h11 : ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 =
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 := by
      rw [hu]
    rw [hc, GeneralLinearGroup.coe_scalar] at h00 h11
    simp [hM] at h00 h11
    exact one_ne_zero (by rw [← ha, h11, h00, ← two_mul, h2, zero_mul] : (1 : E) = 0)
  obtain ⟨μ, hDμ, hμ⟩ : ∃ μ : Fin 3 → E, (((d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal μ ∧ μ 0 = μ 1 := by
    refine ⟨_, ?_, (frameEigHom_eq_iff hv).1 hd⟩
    ext r s
    have h := congrFun (mulVec_frameEig hv d.2 s) r
    rw [Matrix.mulVec_single_one] at h
    by_cases hrs : r = s
    · subst hrs
      simpa using h
    · simpa [Matrix.diagonal_apply, hrs, Pi.single_apply] using h
  have hcd : c * (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c :=
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc, hDμ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hM, hμ, mul_comm]))
  have hsd : s * (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * s :=
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hDμ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hS, hμ, mul_comm]))
  refine ⟨QuotientGroup.mk c, QuotientGroup.mk s, orderOf_eq_prime ?_ hne, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
  · simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
      congrArg (fun x : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) =>
        (x : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) hsc
  · rw [← QuotientGroup.mk_mul, hcd, QuotientGroup.mk_mul]
  · rw [← QuotientGroup.mk_mul, hsd, QuotientGroup.mk_mul]

theorem exists_conj_line_mem (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hJ : ∀ x ∈ J, x ^ p = 1)
    (hJc : p ^ 2 ≤ Nat.card J) :
    ∃ (ℓ : frameTorusSU hU (fun i => Pi.single i 1))
      (g : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      frameEigHom (UCK.isOrthonormalFrame_single hU) 0 ℓ =
        frameEigHom (UCK.isOrthonormalFrame_single hU) 1 ℓ ∧
      (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
        primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ≠ 1 ∧
      g * QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * g⁻¹ ∈ J := by
  classical
  haveI := hU.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hv := UCK.isOrthonormalFrame_single (p := 2) hU
  obtain ⟨k', hk'⟩ : ∃ k', 2 ^ k = k' + 1 :=
    ⟨2 ^ k - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have e : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ k) E) ≃*
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    CFSG.ComponentClassification.Burgoyne.U.uTransport hU (by norm_num)
  have hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) * Nat.gcd 3 (k' + 2) =
      (k' + 1) ^ 3 * (k' * (k' + 2)) * ((k' + 2) * (k' ^ 2 + k' + 1)) := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
    rw [← Nat.card_congr e.toEquiv, show k' + 2 = 2 ^ k + 1 by omega, h, hk',
      show (k' + 1) ^ 2 - 1 = k' * (k' + 2) from Nat.sub_eq_of_eq_add (by ring)]
    ring
  obtain ⟨T, hTF, hTq, hTidx, -⟩ :=
    UCK.exists_frame_sylow hU hk hk' hp3 (by rwa [show k' + 2 = 2 ^ k + 1 by omega]) hcard
  obtain ⟨-, -, hcomm, -, -, -, -⟩ := frame_group_structure hU hk hv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity (2 ^ k + 1) E) p
    (by rw [card_rootsOfUnity_eq hU]; exact hpk)
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨ℓ, hℓ⟩ := UCK.exists_frameEigHom_eq hv _ (UCK.prod_line_eq_one z 2)
  have hℓp : ℓ ^ p = 1 := frameTorusSU_ext hv fun l => by
    rw [map_pow, hℓ, map_one]
    split_ifs
    · rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hzp,
        _root_.one_zpow]
    · exact hzp
  set L : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) with hL
  have hLp : L ^ p = 1 := by
    rw [hL, ← QuotientGroup.mk_pow, ← Subgroup.coe_pow, hℓp]
    rfl
  have hL1 : L ≠ 1 := fun h1 => by
    obtain ⟨s, hs3, hs⟩ := UCK.exists_eig_mul_of_mk_eq hv (d := 1) (d' := ℓ)
      (by rw [OneMemClass.coe_one, QuotientGroup.mk_one]; exact h1.symm)
    have h0 := hs 0
    rw [hℓ, map_one, one_mul, if_neg (by decide)] at h0
    have := Nat.le_of_dvd (by norm_num) (hz ▸ orderOf_dvd_of_pow_eq_one (h0 ▸ hs3 : z ^ 3 = 1))
    omega
  have hJp : IsPGroup p J := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hJ x x.2)⟩
  obtain ⟨S, hJS⟩ := hJp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))
    (hTq.toSylow hTidx) S
  have hgT : ∀ x ∈ J, ∃ t ∈ T, g * t * g⁻¹ = x := fun x hx => by
    have h1 : x ∈ ((g • hTq.toSylow hTidx : Sylow p _) : Subgroup _) := hg ▸ hJS hx
    rwa [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  have hF : ∀ x ∈ (J : Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) ∪ {g * L * g⁻¹},
      ∃ t ∈ frameTorus hU (fun i => Pi.single i 1), g * t * g⁻¹ = x := by
    rintro x (hx | rfl)
    · obtain ⟨t, ht, rfl⟩ := hgT x hx
      exact ⟨t, hTF ht, rfl⟩
    · exact ⟨L, Subgroup.mem_map_of_mem _ ℓ.2, rfl⟩
  have hK := CFSG.Open.IsElemAbelian.closure_of_commute (p := p) (fun a ha b hb => by
      obtain ⟨t, ht, rfl⟩ := hF a ha
      obtain ⟨t', ht', rfl⟩ := hF b hb
      calc g * t * g⁻¹ * (g * t' * g⁻¹) = g * (t * t') * g⁻¹ := by group
        _ = g * (t' * t) * g⁻¹ := by rw [hcomm t ht t' ht']
        _ = g * t' * g⁻¹ * (g * t * g⁻¹) := by group) (by
      rintro a (ha | rfl)
      · exact hJ a ha
      · rw [conj_pow, hLp, mul_one, mul_inv_cancel])
  have hJK := Subgroup.eq_of_le_of_card_ge (fun x hx => Subgroup.subset_closure (Or.inl hx))
    ((card_le_of_pow_eq_one hU hk hp hp5 hpk hK.2).trans hJc)
  refine ⟨ℓ, g, by rw [hℓ, hℓ, if_neg (by decide), if_neg (by decide)], hL1, ?_⟩
  rw [hJK]
  exact Subgroup.subset_closure (Set.mem_union_right _ rfl)

theorem exists_commute_invPair (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hJ : ∀ x ∈ J, x ^ p = 1)
    (hJc : p ^ 2 ≤ Nat.card J) :
    ∃ t ∈ J, t ≠ 1 ∧ ∃ c s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧
      s * c * s⁻¹ = c⁻¹ ∧ c * t = t * c ∧ s * t = t * s := by
  obtain ⟨ℓ, g, hd, hℓ1, hJℓ⟩ := exists_conj_line_mem hU hk hp hp5 hpk hJ hJc
  obtain ⟨c, s, hc, hsc, hcd, hsd⟩ := exists_invPair_commute_line hU hd
  have hconj : ∀ {a b : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)}, a * b = b * a →
      g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := fun h => by
    simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj g) h
  refine ⟨_, hJℓ, fun h => hℓ1 (by rwa [conj_eq_one_iff] at h), g * c * g⁻¹, g * s * g⁻¹,
    (MulEquiv.orderOf_eq (MulAut.conj g) c).trans hc, ?_, hconj hcd, hconj hsd⟩
  simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg (MulAut.conj g) hsc

end CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

end
