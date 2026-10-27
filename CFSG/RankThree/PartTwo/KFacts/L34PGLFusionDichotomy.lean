module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionFacts
import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionSinger

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)
open CFSG.RankThree.LocalRank
open Matrix
open scoped commutatorElement

variable {k : Type*} [Field k]

section Stabilizer

variable {u : kˣ}

private theorem pglSylow_le_stab (hk : Nat.card k = 4) :
    pglSylow (k := k) u ≤
      Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))) := by
  rw [pglSylow, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · change xDiag (k := k) u ∈
      Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : xDiag (k := k) u (aP u) = aP u := conjAut_diagGL_aP u
    have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (xDiag (k := k) u) (aP u)
    rw [hfix] at h
    calc xDiag u * MulAut.conj (aP u) =
        (xDiag u * MulAut.conj (aP u) * (xDiag u)⁻¹) * xDiag u := by group
      _ = MulAut.conj (aP u) * xDiag u := by rw [h]
  · change yInn ∈
      Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))
    rw [Subgroup.mem_centralizer_singleton_iff, yInn, ← map_mul, ← map_mul,
      commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero]

private theorem factorization_card_stab (hk : Nat.card k = 4) (hu : u ≠ 1) :
    (Nat.card ↥(Subgroup.centralizer
      ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))))).factorization 3 = 3 := by
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  haveI := LinearFieldFour.charP_two_of_card_eq_four hk
  set Stab := Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))
  have h27 : 27 ∣ Nat.card ↥Stab := by
    rw [← (pglSylow_transposition hk hu).1]
    exact Subgroup.card_dvd_of_le (pglSylow_le_stab (u := u) hk)
  have hdvd : Nat.card ↥Stab ∣ 241920 := by
    rw [← card_mulAut hk]
    exact Subgroup.card_subgroup_dvd_card Stab
  have h241 : (241920 : ℕ).factorization 3 = 3 := by
    rw [show 241920 = 3 ^ 3 * 8960 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 8960)]
    simp
  have hlower : 3 ≤ (Nat.card ↥Stab).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp (by
      simpa using h27)
  have hupper : (Nat.card ↥Stab).factorization 3 ≤ 3 := by
    have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (by norm_num : (241920 : ℕ) ≠ 0)).mpr hdvd 3
    rwa [h241] at h
  omega

private theorem exists_conj_pglSylowMax_of_stab (hk : Nat.card k = 4) (hu : u ≠ 1)
    {M : Subgroup (MulAut (projectiveSL 3 k))} (hM9 : Nat.card M = 9)
    (hMc : M ≤ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))) :
    ∃ (ψ : MulAut (projectiveSL 3 k)) (i : Fin 4),
      ψ ∈ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))) ∧
      M.map (MulAut.conj ψ).toMonoidHom = pglSylowMax u i := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  haveI := LinearFieldFour.charP_two_of_card_eq_four hk
  set Stab := Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))
  have hPcard : Nat.card ↥((pglSylow (k := k) u).subgroupOf Stab) =
      3 ^ (Nat.card ↥Stab).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pglSylow_le_stab (u := u) hk)).toEquiv,
      (pglSylow_transposition hk hu).1, factorization_card_stab (u := u) hk hu]
    norm_num
  have hBcard : Nat.card ↥(M.subgroupOf Stab) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMc).toEquiv, hM9]
  have hB : IsPGroup 3 ↥(M.subgroupOf Stab) :=
    IsPGroup.of_card (p := 3) (n := 2) (by rw [hBcard]; norm_num)
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le
    (L := ↥Stab) (p := 3) hPcard hB
  have hMle : M.map (MulAut.conj (ψ : MulAut (projectiveSL 3 k))).toMonoidHom ≤
      pglSylow u := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hx' : (⟨x, hMc hx⟩ : ↥Stab) ∈ M.subgroupOf Stab := hx
    have hmem : (MulAut.conj ψ) ⟨x, hMc hx⟩ ∈
        (M.subgroupOf Stab).map (MulAut.conj ψ).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx'
    simpa using (Subgroup.mem_subgroupOf.mp (hψ hmem))
  have hM'card : Nat.card ↥(M.map
      (MulAut.conj (ψ : MulAut (projectiveSL 3 k))).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective
      (MulAut.conj (ψ : MulAut (projectiveSL 3 k))).injective, hM9]
  obtain ⟨i, hi⟩ := (pglSylow_transposition hk hu).2.1 _ hMle hM'card
  exact ⟨ψ, i, ψ.2, hi⟩

private theorem eq_aP_of_mem_centralizer (hk : Nat.card k = 4)
    {ψ : MulAut (projectiveSL 3 k)}
    (hψ : ψ ∈ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k)))) :
    ψ (aP u) = aP u := by
  have hcomm : ψ * MulAut.conj (aP u) = MulAut.conj (aP u) * ψ :=
    Subgroup.mem_centralizer_singleton_iff.mp hψ
  have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv ψ (aP u)
  apply conj_injective hk
  rw [← h, hcomm]
  group

end Stabilizer

section Cases

variable {u : kˣ}

private theorem inner_case (hk : Nat.card k = 4) (hu : u ≠ 1)
    {ψ : MulAut (projectiveSL 3 k)}
    {M : Subgroup (MulAut (projectiveSL 3 k))}
    (hi : M.map (MulAut.conj ψ).toMonoidHom = pglSylowMax u 1)
    (hout : ∃ α ∈ M,
      α ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) : False := by
  obtain ⟨α, hαM, hαout⟩ := hout
  have hmem : MulAut.conj ψ α ∈ pglSylowMax u 1 := by
    rw [← hi]
    exact Subgroup.mem_map_of_mem _ hαM
  rw [pglSylowMax_one hk hu] at hmem
  obtain ⟨p, -, hpeq⟩ := Subgroup.mem_map.mp hmem
  apply hαout
  refine ⟨ψ⁻¹ p, ?_⟩
  rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hpeq, MulAut.conj_apply]
  group

private theorem torus_case (hk : Nat.card k = 4)
    {ψ : MulAut (projectiveSL 3 k)}
    {M : Subgroup (MulAut (projectiveSL 3 k))}
    (hψ : ψ ∈ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))))
    (hi : M.map (MulAut.conj ψ).toMonoidHom = pglSylowMax u 0)
    (htorus : xDiag u ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ t : projectiveSL 3 k, xDiag u t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹) :
    ∃ ε ∈ M, ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ t : projectiveSL 3 k, ε t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹ := by
  obtain ⟨hxout, t₀, ht₀fix, ht₀conj⟩ := htorus
  have hfixψ : ψ (aP u) = aP u := eq_aP_of_mem_centralizer hk hψ
  have hψinv : ψ⁻¹ ∈ Subgroup.centralizer ({MulAut.conj (aP u)} :
      Set (MulAut (projectiveSL 3 k))) := Subgroup.inv_mem _ hψ
  have hfixψinv : ψ⁻¹ (aP u) = aP u := eq_aP_of_mem_centralizer hk hψinv
  have hxM' : xDiag u ∈ M.map (MulAut.conj ψ).toMonoidHom := by
    rw [hi]
    exact Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨α, hαM, hαeq⟩ := Subgroup.mem_map.mp hxM'
  have hαeq'' : (MulAut.conj ψ) α = xDiag u := hαeq
  refine ⟨α, hαM, ?_, ψ⁻¹ t₀, ?_, ?_⟩
  · intro hαin
    obtain ⟨p, rfl⟩ := hαin
    apply hxout
    refine ⟨ψ p, ?_⟩
    rw [← hαeq'', MulAut.conj_apply, ← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv]
  · have hαeq' : α = ψ⁻¹ * xDiag u * ψ := by
      rw [← hαeq'', MulAut.conj_apply]
      group
    rw [hαeq']
    simp [MulAut.mul_apply, ht₀fix]
  · refine ψ.injective ?_
    simp [map_mul, map_inv, hfixψ, ht₀conj, MulEquiv.apply_symm_apply]

private theorem singer_case (hk : Nat.card k = 4)
    {ψ : MulAut (projectiveSL 3 k)}
    {M : Subgroup (MulAut (projectiveSL 3 k))}
    (hψ : ψ ∈ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))))
    {i : Fin 4} (hi23 : i = 2 ∨ i = 3)
    (hi : M.map (MulAut.conj ψ).toMonoidHom = pglSylowMax u i)
    (hsinger : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      ∃ ε ∈ pglSylowMax u i,
        ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          aP u * s * (aP u)⁻¹ ≠ s) :
    ∃ ε ∈ M, ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
        aP u * s * (aP u)⁻¹ ≠ s := by
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hk]; norm_num)
  obtain ⟨ε₀, hε₀M', hε₀out, s₀, hs₀, hs₀neq⟩ := hsinger i hi23
  have hfixψ : ψ (aP u) = aP u := eq_aP_of_mem_centralizer hk hψ
  have hε₀M'map : ε₀ ∈ M.map (MulAut.conj ψ).toMonoidHom := by
    rw [hi]
    exact hε₀M'
  obtain ⟨α, hαM, hαeq⟩ := Subgroup.mem_map.mp hε₀M'map
  have hαeq'' : (MulAut.conj ψ) α = ε₀ := hαeq
  refine ⟨α, hαM, ?_, ψ⁻¹ s₀, ?_, ?_⟩
  · intro hαin
    obtain ⟨p, rfl⟩ := hαin
    apply hε₀out
    refine ⟨ψ p, ?_⟩
    rw [← hαeq'', MulAut.conj_apply, ← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv]
  · have hfix : GL3TwoFixedModel.autFixed ε₀ =
        (GL3TwoFixedModel.autFixed α).map ψ.toMonoidHom := by
      have hαeq' : ε₀ = ψ * α * ψ⁻¹ := by
        rw [← hαeq'', MulAut.conj_apply]
      rw [hαeq', autFixed_conj]
    rw [hfix, ← CFSG.RankThree.PartTwo.map_inSubgroup_aschbacherSolvableCore ψ
      (GL3TwoFixedModel.autFixed α)] at hs₀
    obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp hs₀
    have hseq' : s = ψ⁻¹ s₀ := by
      rw [← hseq]
      simpa using (MulEquiv.symm_apply_apply ψ s).symm
    rw [← hseq']
    exact hs
  · intro h
    apply hs₀neq
    have h' : aP u * s₀ * (aP u)⁻¹ = s₀ := by
      have := congrArg ψ h
      simpa [map_mul, map_inv, hfixψ, MulEquiv.apply_symm_apply] using this
    exact h'

private theorem special_case (hk : Nat.card k = 4) (hu : u ≠ 1)
    (htorus : xDiag u ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∃ t : projectiveSL 3 k, xDiag u t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹)
    (hsinger : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      ∃ ε ∈ pglSylowMax u i,
        ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          aP u * s * (aP u)⁻¹ ≠ s)
    {M : Subgroup (MulAut (projectiveSL 3 k))} (hM9 : Nat.card M = 9)
    (hMc : M ≤ Subgroup.centralizer ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))))
    (hout : ∃ α ∈ M,
      α ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    (∃ ε ∈ M, ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          aP u * s * (aP u)⁻¹ ≠ s) ∨
      (∃ ε ∈ M, ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ t : projectiveSL 3 k, ε t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹) := by
  obtain ⟨ψ, i, hψstab, hi⟩ := exists_conj_pglSylowMax_of_stab hk hu hM9 hMc
  fin_cases i
  · exact Or.inr (torus_case hk hψstab hi htorus)
  · exact (inner_case hk hu hi hout).elim
  · exact Or.inl (singer_case hk hψstab (Or.inl rfl) hi hsinger)
  · exact Or.inl (singer_case hk hψstab (Or.inr rfl) hi hsinger)

end Cases

private theorem outer_dichotomy_of (hk : Nat.card k = 4)
    (htorus : ∀ u : kˣ, u ≠ 1 →
      xDiag u ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ t : projectiveSL 3 k, xDiag u t = t ∧ t * aP u * t⁻¹ = (aP u)⁻¹)
    (hsinger : ∀ u : kˣ, u ≠ 1 → ∀ i : Fin 4, i = 2 ∨ i = 3 →
      ∃ ε ∈ pglSylowMax u i,
        ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          aP u * s * (aP u)⁻¹ ≠ s)
    {X : Type*} [Group X] (χ : X ≃* projectiveSL 3 k) {b : X} (hb : orderOf b = 3)
    {M : Subgroup (MulAut X)} (hM9 : Nat.card M = 9)
    (hMc : M ≤ Subgroup.centralizer {MulAut.conj b})
    (hout : ∃ α ∈ M, α ∉ (MulAut.conj : X →* MulAut X).range) :
    (∃ ε ∈ M, ε ∉ (MulAut.conj : X →* MulAut X).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          b * s * b⁻¹ ≠ s) ∨
      (∃ ε ∈ M, ε ∉ (MulAut.conj : X →* MulAut X).range ∧
        ∃ t : X, ε t = t ∧ t * b * t⁻¹ = b⁻¹) := by
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hk]; norm_num)
  haveI : Finite X := Finite.of_injective (χ : X → projectiveSL 3 k) χ.injective
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hb3 : orderOf (χ b) = 3 := by
    rw [MulEquiv.orderOf_eq, hb]
  have hb1 : χ b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb3
    norm_num at hb3
  have hBcard : Nat.card ↥(Subgroup.zpowers (χ b)) = 3 := by
    rw [Nat.card_zpowers, hb3]
  have hB : IsPGroup 3 ↥(Subgroup.zpowers (χ b)) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hBcard]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le
    (L := projectiveSL 3 k) (p := 3) (card_eZero_eq hk) hB
  have hzg : MulAut.conj g (χ b) ∈ eZero k :=
    hg (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers (χ b)))
  have hzg1 : MulAut.conj g (χ b) ≠ 1 := by
    intro h
    exact hb1 ((MulAut.conj g).injective (by simp [h]))
  obtain ⟨n, -, hnconj⟩ := exists_mem_normalizer_conj_eq hk hu hzg hzg1
  let h : projectiveSL 3 k := g⁻¹ * n
  have hχb : χ b = h * aP u * h⁻¹ := by
    have hgconj : MulAut.conj g (χ b) = g * χ b * g⁻¹ := MulAut.conj_apply g (χ b)
    rw [hgconj] at hnconj
    calc χ b = g⁻¹ * (g * χ b * g⁻¹) * g := by group
      _ = g⁻¹ * (n * aP u * n⁻¹) * g := by rw [← hnconj]
      _ = h * aP u * h⁻¹ := by simp [h]; group
  let Φ : X ≃* projectiveSL 3 k := χ.trans (MulAut.conj h⁻¹)
  have hΦb : Φ b = aP u := by
    change MulAut.conj h⁻¹ (χ b) = aP u
    rw [hχb, MulAut.conj_apply]
    group
  let M' : Subgroup (MulAut (projectiveSL 3 k)) := M.map (MulAut.congr Φ).toMonoidHom
  have hM'9 : Nat.card M' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr Φ).injective, hM9]
  have hM'c : M' ≤ Subgroup.centralizer
      ({MulAut.conj (aP u)} : Set (MulAut (projectiveSL 3 k))) := by
    intro ε' hε'
    obtain ⟨ε, hεM, rfl⟩ := Subgroup.mem_map.mp hε'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hεc : ε * MulAut.conj b = MulAut.conj b * ε :=
      Subgroup.mem_centralizer_singleton_iff.mp (hMc hεM)
    have hconj : MulAut.congr Φ (MulAut.conj b) = MulAut.conj (aP u) := by
      rw [← hΦb]
      exact CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj Φ b
    have h := congrArg (MulAut.congr Φ) hεc
    rw [map_mul, map_mul] at h
    rw [hconj] at h
    exact h
  have hout' : ∃ α ∈ M', α ∉
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
    obtain ⟨α, hαM, hαout⟩ := hout
    refine ⟨MulAut.congr Φ α, Subgroup.mem_map_of_mem _ hαM, ?_⟩
    intro hαin
    apply hαout
    obtain ⟨p, hp⟩ := hαin
    refine ⟨Φ.symm p, ?_⟩
    calc MulAut.conj (Φ.symm p) = (MulAut.congr Φ).symm (MulAut.conj p) := by
          change MulAut.conj (Φ.symm p) = MulAut.congr Φ.symm (MulAut.conj p)
          exact (CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj Φ.symm p).symm
      _ = (MulAut.congr Φ).symm (MulAut.congr Φ α) := by rw [hp]
      _ = α := MulEquiv.symm_apply_apply (MulAut.congr Φ) α
  have hspecial := special_case hk hu (htorus u hu) (hsinger u hu) hM'9 hM'c hout'
  rcases hspecial with ⟨ε', hε'M', hε'out, s', hs', hs'neq⟩ |
    ⟨ε', hε'M', hε'out, t', ht'fix, ht'conj⟩
  · obtain ⟨ε, hεM, hεeq⟩ := Subgroup.mem_map.mp hε'M'
    refine Or.inl ⟨ε, hεM, ?_, Φ.symm s', ?_, ?_⟩
    · intro hεin
      apply hε'out
      obtain ⟨p, hp⟩ := hεin
      refine ⟨Φ p, ?_⟩
      rw [← hεeq, ← hp]
      exact (CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj Φ p).symm
    · have hfix : GL3TwoFixedModel.autFixed ε' =
          (GL3TwoFixedModel.autFixed ε).map Φ.toMonoidHom := by
        rw [← hεeq]
        ext y
        rw [GL3TwoFixedModel.mem_autFixed, Subgroup.mem_map]
        constructor
        · intro hy
          refine ⟨Φ.symm y, ?_, by simp⟩
          rw [GL3TwoFixedModel.mem_autFixed]
          apply Φ.injective
          rw [MulEquiv.apply_symm_apply]
          exact hy
        · rintro ⟨x, hx, rfl⟩
          rw [GL3TwoFixedModel.mem_autFixed] at hx
          change Φ (ε (Φ.symm (Φ x))) = Φ x
          rw [MulEquiv.symm_apply_apply, hx]
      rw [hfix, ← CFSG.RankThree.PartTwo.map_inSubgroup_aschbacherSolvableCore Φ
        (GL3TwoFixedModel.autFixed ε)] at hs'
      obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp hs'
      have hseq' : s = Φ.symm s' := by
        rw [← hseq]
        simpa using (MulEquiv.symm_apply_apply Φ s).symm
      rw [← hseq']
      exact hs
    · intro h
      apply hs'neq
      have h' : aP u * s' * (aP u)⁻¹ = s' := by
        have := congrArg Φ h
        simpa [map_mul, map_inv, hΦb, MulEquiv.apply_symm_apply] using this
      exact h'
  · obtain ⟨ε, hεM, hεeq⟩ := Subgroup.mem_map.mp hε'M'
    refine Or.inr ⟨ε, hεM, ?_, Φ.symm t', ?_, ?_⟩
    · intro hεin
      apply hε'out
      obtain ⟨p, hp⟩ := hεin
      refine ⟨Φ p, ?_⟩
      rw [← hεeq, ← hp]
      exact (CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj Φ p).symm
    · have hεt : ε (Φ.symm t') = Φ.symm t' := by
        apply Φ.injective
        have h := ht'fix
        rw [← hεeq] at h
        simpa [MulAut.congr_apply, MulEquiv.apply_symm_apply] using h
      exact hεt
    · refine Φ.injective ?_
      rw [map_mul, map_mul, map_inv, hΦb, MulEquiv.apply_symm_apply, ht'conj, map_inv, hΦb]

theorem outer_dichotomy (hk : Nat.card k = 4) {X : Type*} [Group X] (χ : X ≃* projectiveSL 3 k)
    {b : X} (hb : orderOf b = 3) {M : Subgroup (MulAut X)} (hM9 : Nat.card M = 9)
    (hMc : M ≤ Subgroup.centralizer {MulAut.conj b})
    (hout : ∃ α ∈ M, α ∉ (MulAut.conj : X →* MulAut X).range) :
    (∃ ε ∈ M, ε ∉ (MulAut.conj : X →* MulAut X).range ∧
        ∃ s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε),
          b * s * b⁻¹ ≠ s) ∨
      (∃ ε ∈ M, ε ∉ (MulAut.conj : X →* MulAut X).range ∧
        ∃ t : X, ε t = t ∧ t * b * t⁻¹ = b⁻¹) :=
  outer_dichotomy_of hk (fun _ hu => xDiag_torus hk hu)
    (fun _ hu i hi => pglSylowMax_singer hk hu i hi) χ hb hM9 hMc hout

end CFSG.RankThree.PartTwo.KFacts.L34
