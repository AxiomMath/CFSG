module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab
public import CFSG.Quasithin.Vol2.Ch11SecU1U3G

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Quasithin.E2P.Asc80 CFSG.GH74.GLS.IVK.Proofs2
open CFSG.Quasithin.Vol2.Ch11.SecU1.U3 CFSG.Quasithin.A312U3
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.SubgroupLists CFSG.Open
open CFSG.Blueprint (LieModel)

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_nonsquare_normOne {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hpne2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    ∃ ν : Fˣ, (ν : F) ^ (p + 1) = 1 ∧
      ∀ x : Fˣ, (x : F) ^ (p + 1) = 1 → (x : F) ^ 2 ≠ (ν : F) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := by omega
  have hdvd : p + 1 ∣ Nat.card F - 1 := by
    rw [hF]
    refine ⟨p - 1, ?_⟩
    apply Nat.cast_injective (R := ℤ)
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp1
    push_cast [Nat.cast_sub hp1, Nat.cast_sub h1]
    ring
  have hcard : Nat.card (rootsOfUnity (p + 1) F) = p + 1 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hdvd
  obtain ⟨ν₀, hν₀⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := rootsOfUnity (p + 1) F)
  rw [hcard] at hν₀
  set ν : Fˣ := ↑ν₀ with hνdef
  have hνord : orderOf ν = p + 1 := by rw [hνdef, Subgroup.orderOf_coe, hν₀]
  refine ⟨ν, ?_, ?_⟩
  · have h := ν₀.2
    rw [mem_rootsOfUnity] at h
    have h' := congrArg (fun u : Fˣ => (u : F)) h
    simpa [hνdef] using h'
  · intro x hx hx2
    have hx' : x ^ (p + 1) = 1 := Units.ext hx
    have hxord : orderOf x ∣ p + 1 := orderOf_dvd_of_pow_eq_one hx'
    have hx2' : x ^ 2 = ν := Units.ext hx2
    have hord : orderOf (x ^ 2) = p + 1 := by rw [hx2', hνord]
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hpne2
    obtain ⟨k, hk⟩ := hpodd
    have h2dvd : 2 ∣ p + 1 := by omega
    have hlt : orderOf (x ^ 2) < p + 1 := by
      rw [orderOf_pow]
      by_cases hd : orderOf x = p + 1
      · rw [hd, Nat.gcd_eq_right h2dvd]
        omega
      · have hdle : orderOf x ≤ p + 1 := Nat.le_of_dvd (by omega) hxord
        have hdlt : orderOf x < p + 1 := lt_of_le_of_ne hdle hd
        exact lt_of_le_of_lt (Nat.div_le_self _ _) hdlt
    omega

@[expose] noncomputable def gu2Diag {p : ℕ} [Fact p.Prime] {F : Type} [Field F] {ν : F}
    (hν : ν ^ (p + 1) = 1) : ↥(GU2Stated (p ^ 1) F) :=
  let hν0 : ν ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero p)] at hν
    exact zero_ne_one hν
  let M : Matrix (Fin 2) (Fin 2) F := !![ν, 0; 0, 1]
  let Mi : Matrix (Fin 2) (Fin 2) F := !![ν⁻¹, 0; 0, 1]
  have hMMi : M * Mi = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Mi, Matrix.mul_apply, Fin.sum_univ_two, hν0]
  have hMiM : Mi * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Mi, Matrix.mul_apply, Fin.sum_univ_two, hν0]
  let gl : GL (Fin 2) F := ⟨M, Mi, hMMi, hMiM⟩
  ⟨gl, by
    refine Subgroup.subset_closure ?_
    show Matrix.transpose (M.map (fun x => x ^ (p ^ 1))) * M = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, pow_one, ← pow_succ, hν,
        (Fact.out : p.Prime).ne_zero]⟩

theorem gu2Diag_val {p : ℕ} [Fact p.Prime] {F : Type} [Field F] {ν : F}
    (hν : ν ^ (p + 1) = 1) :
    ((gu2Diag hν : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![ν, 0; 0, 1] := rfl

theorem pow_succ_of_matU_eq_scalar {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ 2) {g : SU3F p F} {ζ : F}
    (hg : matU g = Matrix.scalar (Fin 3) ζ) : ζ ^ (p + 1) = 1 := by
  have hunit := (mem_unitarySU_iff (uniData hF)).mp g.2
  have h2 : Matrix.transpose ((matU g).map (uniData hF).bar) * matU g = 1 := hunit.2
  rw [hg] at h2
  have h00 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h00
  rw [(uniData hF).bar_apply, pow_one] at h00
  rw [pow_succ]
  exact h00

theorem sq_eq_of_piU_blkU_eq {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ 2) {ν μ : F} (hν : ν ^ (p + 1) = 1)
    (S : ↥(StatedSU 2 (p ^ 1) F))
    {N : ↥(GU2Stated (p ^ 1) F)}
    (hμ : ((N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) μ)
    (hker : piU p F (Lemma41aU3.blkU (uniData hF)
      (gu2Diag hν * (Subgroup.inclusion su2_le_gu2 S * N)⁻¹)) = 1) :
    ∃ ζ : F, ζ ^ (p + 1) = 1 ∧ ζ ^ 2 * μ ^ 2 = ν := by
  let A : ↥(GU2Stated (p ^ 1) F) := Subgroup.inclusion su2_le_gu2 S * N
  let X : ↥(GU2Stated (p ^ 1) F) := gu2Diag hν * A⁻¹
  have hXker : piU p F (Lemma41aU3.blkU (uniData hF) X) = 1 := hker
  obtain ⟨ζ, hζ3, hζmat⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr hXker)
  have hXscalar : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) ζ := by
    have h1 : ulBlock (matU (Lemma41aU3.blkU (uniData hF) X)) =
        ulBlock (Matrix.scalar (Fin 3) ζ) := by rw [hζmat]
    rw [matU_blkU hF, Lemma41aL3.ulBlock_blkMat] at h1
    have h2 : ulBlock (Matrix.scalar (Fin 3) ζ) = Matrix.scalar (Fin 2) ζ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ulBlock, Matrix.scalar_apply]
    rwa [h2] at h1
  have hζp : ζ ^ (p + 1) = 1 := pow_succ_of_matU_eq_scalar hF hζmat
  have hdetD : ((gu2Diag hν : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ν := by
    rw [gu2Diag_val]
    simp [Matrix.det_fin_two]
  have hdetA : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = μ ^ 2 := by
    have hA : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((S : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl
    rw [hA, Matrix.det_mul, det_of_mem_su2 hF S, hμ]
    simp [Matrix.scalar_apply, sq]
  have hXA : X * A = gu2Diag hν := by
    rw [show X = gu2Diag hν * A⁻¹ from rfl]
    group
  have hdetXA : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
      ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ν := by
    have h1 : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((gu2Diag hν : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, hXA]
    calc _ = (((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det :=
          (Matrix.det_mul _ _).symm
      _ = _ := by rw [h1, hdetD]
  refine ⟨ζ, hζp, ?_⟩
  rw [show ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ζ ^ 2 by
    rw [hXscalar]
    simp [Matrix.scalar_apply, sq], hdetA] at hdetXA
  exact hdetXA

theorem gu2Diag_not_mem_mul {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {ν : F} (hν : ν ^ (p + 1) = 1)
    (hνns : ∀ x : Fˣ, (x : F) ^ (p + 1) = 1 → (x : F) ^ 2 ≠ ν)
    (S : ↥(StatedSU 2 (p ^ 1) F)) {c : PSU3F p F}
    (hc : c ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F))) :
    piU p F (Lemma41aU3.blkU (uniData hF) (gu2Diag hν)) ≠
      piU p F (ofSU2 hF S) * c := by
  intro heq
  have hz : zcU hF ∈ leviSL hF := zcU_mem_leviSL hF
  have hcz : c * zcU hF = zcU hF * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ hz).symm
  have hcB : c ∈ leviCU hF := mem_leviCU_of_commute_z hp2 hF hcz
  obtain ⟨_, ⟨N, rfl⟩, rfl⟩ := hcB
  obtain ⟨μ, hμ⟩ := scalar_of_piU_mem_centralizer_leviSL hp2 hF (N := N) hc
  have hμp : μ ^ (p + 1) = 1 := pow_succ_eq_one_of_scalar hF hμ
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero p)] at hμp
    exact zero_ne_one hμp
  let A : ↥(GU2Stated (p ^ 1) F) := Subgroup.inclusion su2_le_gu2 S * N
  let X : ↥(GU2Stated (p ^ 1) F) := gu2Diag hν * A⁻¹
  have hD : piU p F (Lemma41aU3.blkU (uniData hF) (gu2Diag hν)) =
      piU p F (Lemma41aU3.blkU (uniData hF) A) := by
    rw [heq]
    show piU p F (ofSU2 hF S) * piU p F (Lemma41aU3.blkU (uniData hF) N) = _
    rw [show A = Subgroup.inclusion su2_le_gu2 S * N from rfl, map_mul, map_mul]
    rfl
  have hker : piU p F (Lemma41aU3.blkU (uniData hF) X) = 1 := by
    rw [show X = gu2Diag hν * A⁻¹ from rfl]
    simp only [map_mul, map_inv]
    rw [hD, mul_inv_cancel]
  obtain ⟨ζ, hζp, hνsq⟩ :=
    sq_eq_of_piU_blkU_eq hF hν S hμ hker
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero p)] at hζp
    exact zero_ne_one hζp
  have hxnorm : ((Units.mk0 (ζ * μ) (mul_ne_zero hζ0 hμ0) : Fˣ) : F) ^ (p + 1) = 1 := by
    show (ζ * μ) ^ (p + 1) = 1
    rw [mul_pow, hζp, hμp, one_mul]
  have hxsq : ((Units.mk0 (ζ * μ) (mul_ne_zero hζ0 hμ0) : Fˣ) : F) ^ 2 = ν := by
    show (ζ * μ) ^ 2 = ν
    rw [mul_pow]
    exact hνsq
  exact hνns _ hxnorm hxsq

theorem eq_zcU_of_mem_centralizer_leviSL_of_order_two {p : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {c : PSU3F p F} (hc : c ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F)))
    (hc2 : orderOf c = 2) : c = zcU hF := by
  have hz : zcU hF ∈ leviSL hF := zcU_mem_leviSL hF
  have hcz : c * zcU hF = zcU hF * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ hz).symm
  have hcB : c ∈ leviCU hF := mem_leviCU_of_commute_z hp2 hF hcz
  obtain ⟨_, ⟨N, rfl⟩, rfl⟩ := hcB
  obtain ⟨μ, hμ⟩ := scalar_of_piU_mem_centralizer_leviSL hp2 hF (N := N) hc
  have hμp : μ ^ (p + 1) = 1 := pow_succ_eq_one_of_scalar hF hμ
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero p)] at hμp
    exact zero_ne_one hμp
  have hpow : (piU p F (Lemma41aU3.blkU (uniData hF) N)) ^ 2 = 1 := by
    simpa only [hc2] using
      pow_orderOf_eq_one (piU p F (Lemma41aU3.blkU (uniData hF) N))
  have hcc : piU p F (Lemma41aU3.blkU (uniData hF) N) *
      piU p F (Lemma41aU3.blkU (uniData hF) N) = 1 := by
    rw [← pow_two]
    exact hpow
  have hNN : piU p F (Lemma41aU3.blkU (uniData hF) (N * N)) = 1 := by
    rw [map_mul, map_mul]
    exact hcc
  obtain ⟨ζ, hζmat, hζdet⟩ := blk_eq_scalar_of_piU_eq_one hF hNN
  have hN2 : (((N * N : ↥(GU2Stated (p ^ 1) F)) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (μ * μ) := by
    rw [Subgroup.coe_mul, Units.val_mul, hμ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, mul_comm]
  have hζeq : ζ = μ * μ := by
    rw [hζmat] at hN2
    have h00 := congrFun (congrFun hN2 0) 0
    simpa [Matrix.scalar_apply] using h00
  have hdetN2 : (((N * N : ↥(GU2Stated (p ^ 1) F)) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = μ ^ 4 := by
    rw [hN2, Matrix.det_fin_two]
    simp [Matrix.scalar_apply]
    ring
  have hμ4inv : (μ ^ 4)⁻¹ = μ ^ 2 := by
    rw [← hdetN2, hζdet, hζeq, sq]
  have hμ6 : μ ^ 6 = 1 := by
    have h2 : μ ^ 4 * μ ^ 2 = 1 := by
      rw [← hμ4inv]
      exact mul_inv_cancel₀ (pow_ne_zero 4 hμ0)
    calc μ ^ 6 = μ ^ 4 * μ ^ 2 := by ring
      _ = 1 := h2
  rcases piU_blkU_scalar hF hμ hμ6 with h | h
  · rw [h, orderOf_one] at hc2
    omega
  · exact h

omit [Finite Q] in
theorem exists_leviData_psu3 {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2) {L : Subgroup Q} [L.Normal]
    (ψ : PSU3F p F ≃* ↥L) {y : Q} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup Q, LeviData L p y Y := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ', hψ'⟩ := exists_equiv_zcU hp2 hF ψ hyL hy2
  set f := embU ψ' with hf
  have hfinj : Function.Injective f := embU_injective ψ'
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set Q) = (leviCU hF).map f := by
    rw [← hψ', inf_centralizer_embU, centralizer_zcU hp2 hF]
  set Y : Subgroup Q := (leviSL hF).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set Q),
      L ⊓ Subgroup.centralizer ({y} : Set Q)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviCU hp5 hF]
  have hCY : L ⊓ Subgroup.centralizer (Y : Set Q) =
      (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f :=
    inf_centralizer_map_embU ψ' (leviSL hF)
  refine ⟨Y, hYcomm, ⟨zcU hF, zcU_mem_leviSL hF, hψ'⟩, ?_, ?_, ?_, ?_⟩
  · rw [hYcomm]
    exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf (inferInstance : L.Normal) y)
      (centralizer_le_normalizer_inf (inferInstance : L.Normal) y)
  · exact ⟨((leviSL hF).equivMapOfInjective f hfinj).symm.trans (leviSLEquiv hF).symm⟩
  · intro c hc hc2
    rw [hCY] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have hc₀2 : orderOf c₀ = 2 := by
      rw [← orderOf_embU ψ' c₀]
      simpa [hf] using hc2
    have hc₀z : c₀ = zcU hF :=
      eq_zcU_of_mem_centralizer_leviSL_of_order_two hp2 hF hc₀ hc₀2
    rw [hc₀z]
    simpa [hf] using hψ'
  · obtain ⟨ν, hν, hνns⟩ := exists_nonsquare_normOne hp2 hF
    let D : ↥(GU2Stated (p ^ 1) F) := gu2Diag hν
    let g : Q := f (piU p F (Lemma41aU3.blkU (uniData hF) D))
    refine ⟨g, ⟨(ψ' (piU p F (Lemma41aU3.blkU (uniData hF) D))).2, ?_⟩, ?_⟩
    · rw [← hψ']
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      show f (piU p F (Lemma41aU3.blkU (uniData hF) D)) * f (zcU hF) =
        f (zcU hF) * f (piU p F (Lemma41aU3.blkU (uniData hF) D))
      rw [← map_mul, ← map_mul]
      rw [zcU, ← map_mul, ← map_mul, Lemma41aU3.blkU_commute]
    · intro s hs hsc
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      obtain ⟨S, rfl⟩ := exists_eq_piU_ofSU2 hF hs₀
      have h1 : f (piU p F (ofSU2 hF S)) ∈ L :=
        (ψ' (piU p F (ofSU2 hF S))).2
      have h2 : g ∈ L := (ψ' (piU p F (Lemma41aU3.blkU (uniData hF) D))).2
      have hcL : (f (piU p F (ofSU2 hF S)))⁻¹ * g ∈ L := L.mul_mem (L.inv_mem h1) h2
      have hc_inf : (f (piU p F (ofSU2 hF S)))⁻¹ * g ∈
          L ⊓ Subgroup.centralizer (Y : Set Q) := by
        change (f (piU p F (ofSU2 hF S)))⁻¹ * g ∈ L ∧
          (f (piU p F (ofSU2 hF S)))⁻¹ * g ∈ Subgroup.centralizer (Y : Set Q)
        exact ⟨hcL, hsc⟩
      rw [hCY] at hc_inf
      obtain ⟨c₀, hc₀, hc₀eq⟩ := hc_inf
      have heq : piU p F (Lemma41aU3.blkU (uniData hF) D) =
          piU p F (ofSU2 hF S) * c₀ := by
        apply hfinj
        rw [map_mul]
        show f (piU p F (Lemma41aU3.blkU (uniData hF) D)) =
          f (piU p F (ofSU2 hF S)) * f c₀
        rw [show f (piU p F (Lemma41aU3.blkU (uniData hF) D)) = g from rfl, hc₀eq]
        group
      exact gu2Diag_not_mem_mul hp2 hF hν hνns S hc₀ heq

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
