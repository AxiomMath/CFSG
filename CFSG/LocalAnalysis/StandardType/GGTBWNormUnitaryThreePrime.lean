module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryThreePrimeBlock
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitarySingular
public import CFSG.LocalAnalysis.StandardType.GGPGUQuadPhase
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMovePSU
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvectionThree
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryTwicePrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace UnitaryThreeP

variable {K : Type} [Field K] {n d p : ℕ}

theorem mem_primeFormUnitary_of_pow_prime_pow_eq_one (h : UnitaryFieldData 2 n K)
    (hpq : p ∣ 2 ^ n + 1) (hd : 0 < d) {g M : GL (Fin d) K}
    (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) {c : K}
    (hgM : (g : Matrix (Fin d) (Fin d) K) = c • (M : Matrix (Fin d) (Fin d) K)) {b : ℕ}
    (hgp : g ^ p ^ b = 1) : g ∈ primeFormUnitary h (idGram K d) := by
  obtain ⟨μ, -, hμq, hμ⟩ := hM
  set ν := c ^ (2 ^ n + 1) * μ with hν
  have hmap : (c • (M : Matrix (Fin d) (Fin d) K)).map (· ^ 2 ^ n) =
      c ^ 2 ^ n • (M : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n) := by
    ext i j
    simp [mul_pow]
  have hg : TableBUD.herm n (g : Matrix (Fin d) (Fin d) K) = ν • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [TableBUD.herm, hgM, hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ,
      smul_smul, hν, pow_succ]
  have hνq : ν ^ 2 ^ n = ν := by rw [hν, mul_pow, TableBUD.norm_pow_fixed h, hμq]
  have hgp' := TableBUD.herm_pow h hg (p ^ b)
  rw [← Units.val_pow_eq_pow_val, hgp, Units.val_one, TableBUD.herm, TableBUD.map_pow_eq_map_bar h,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.mul_one] at hgp'
  have hνp : ν ^ p ^ b = 1 := by
    have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) K => N ⟨0, hd⟩ ⟨0, hd⟩) hgp'
    simpa using h1.symm
  have key : ∀ (k : ℕ) (μ' : K), μ' ^ 2 ^ n = μ' → μ' ^ p ^ k = 1 → μ' = 1 := by
    intro k
    induction k with
    | zero => intro μ' _ h1; simpa using h1
    | succ k ih =>
      intro μ' hq h1
      have h2 : μ' ^ p = 1 := ih (μ' ^ p) (by rw [← pow_mul, mul_comm, pow_mul, hq])
        (by rw [← pow_mul, ← pow_succ']; exact h1)
      exact TableBUD.eq_one_of_fixed_of_pow h hpq hq h2
  have hν1 := key b ν hνq hνp
  change ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (1 : GL (Fin d) K) *
    (g : Matrix (Fin d) (Fin d) K) = (1 : GL (Fin d) K)
  rw [Units.val_one, Matrix.mul_one, ← TableBUD.map_pow_eq_map_bar h, ← TableBUD.herm, hg, hν1,
    one_smul]

end UnitaryThreeP


theorem ggTorusWNormSC_unitary_three_prime {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hdp : d = 3 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp35 : p = 3 ∨ 5 ≤ p := by
    rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with hq | hq | hq
    · exact Or.inl hq
    · exact absurd (hq ▸ hp) (by norm_num)
    · exact Or.inr hq
  have hd : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hd6 : (d, n) ≠ (6, 1) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hcov := LineU.unitaryCoverAt hK hd hd6
  have h := TableBU.unitaryFieldData_of_card hK hn
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ hh α
    hM hC hpair hlin hgen s hs
  classical
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card Ab = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  have hpK : p ∣ Nat.card K - 1 := TableBUD.dvd_card_sub_one' h hpq
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  set ζ : Kˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
    exact hζ₀
  have hc := QuotMove.isScalarQuot_PSU hK (by omega) hdq hp hpq
  have hAI' : ∀ a ∈ A, ∃ M' : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
      ∀ l : L', TableB.projConj (unitarySU 2 n K d) M' (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨z, hz, hza⟩ := hAI a ha
    obtain ⟨M', hM', rfl⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h) hz
    exact ⟨_, hza⟩
  set G : Subgroup (GL (Fin d) K) := (Ab.comap (TableB.projConj (unitarySU 2 n K d))).map
    (Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))).subtype with hGdef
  have hGp : TypeA.PGLTor.IsProjElem p G :=
    TypeA.PGLTor.isProjElem_comap_map_subtype hc.scalar_mem hc.map_scalar hc.ker hAb
  have hGN : ∀ (M' : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      TableB.projConj (unitarySU 2 n K d) M' ∈ Ab → (M' : GL (Fin d) K) ∈ G :=
    fun M' hM' => ⟨M', hM', rfl⟩
  have hGU : ∀ g ∈ G, ∃ (u : Kˣ) (M' : GL (Fin d) K), M' ∈ LargeEvenGUSet (Fin d) K (2 ^ n) ∧
      g = GeneralLinearGroup.scalar (Fin d) u * M' := by
    rintro _ ⟨M', hM', rfl⟩
    obtain ⟨M'', hM'', e⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h)
      (hAbI _ hM')
    obtain ⟨u, hu⟩ := hc.exists_scalar_mul_of_eq e
    exact ⟨u, M'', hM'', hu⟩
  have hunitG : ∀ g ∈ G, ∀ b : ℕ, g ^ p ^ b = 1 → g ∈ primeFormUnitary h (idGram K d) := by
    intro g hg b hgb
    obtain ⟨u, M', hM', rfl⟩ := hGU g hg
    exact UnitaryThreeP.mem_primeFormUnitary_of_pow_prime_pow_eq_one h hpq hd0 hM' (c := u)
      (by rw [Units.val_mul, GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]) hgb
  by_cases hcent : ∀ g ∈ G, g ^ p = 1 → ∀ x ∈ G, x * g = g * x
  ·
    let H₁ : Subgroup (primeFormUnitary h (idGram K d)) :=
      { carrier := {u | (u : GL (Fin d) K) ∈ G ∧ u ^ p = 1}
        mul_mem' := by
          rintro u v ⟨hu, hup⟩ ⟨hv, hvp⟩
          refine ⟨G.mul_mem hu hv, ?_⟩
          have hvp' : (v : GL (Fin d) K) ^ p = 1 := by rw [← Subgroup.coe_pow, hvp]; rfl
          have huv : Commute u v := Subtype.ext (hcent _ hv hvp' _ hu)
          rw [huv.mul_pow, hup, hvp, one_mul]
        one_mem' := ⟨G.one_mem, one_pow _⟩
        inv_mem' := by
          rintro u ⟨hu, hup⟩
          exact ⟨G.inv_mem hu, by rw [inv_pow, hup, inv_one]⟩ }
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq H₁
      (fun x hx y hy => by
        have hyp : (y : GL (Fin d) K) ^ p = 1 := by rw [← Subgroup.coe_pow, hy.2]; rfl
        exact Subtype.ext (hcent _ hy.1 hyp _ hx.1))
      (fun x hx => hx.2)
    have hdiagG : ∀ z ∈ G, z ^ p = 1 →
        (((P : GL (Fin d) K)⁻¹ * z * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
      intro z hz hzp
      have hzU := hunitG z hz 1 (by rwa [pow_one])
      have h1 := hP ⟨z, hzU⟩ ⟨hz, Subtype.ext (by rw [Subgroup.coe_pow]; exact hzp)⟩
      have e : ((P⁻¹ * ⟨z, hzU⟩ * P : primeFormUnitary h (idGram K d)) : GL (Fin d) K) =
          (P : GL (Fin d) K)⁻¹ * z * P := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [e] at h1
    by_cases hall : ∀ g ∈ G, ∃ c : Kˣ, g ^ p = GeneralLinearGroup.scalar (Fin d) (c ^ p)
    ·
      have hframe : ∀ x ∈ TypeA.inducedSub ψ A, ∃ (M' : GL (Fin d) K)
          (hM' : M' ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
          (((P : GL (Fin d) K)⁻¹ * M' * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
            x = TableB.projConj (unitarySU 2 n K d) ⟨M', TableBUE.gu_subset_normalizer h hM'⟩ := by
        intro a ha
        obtain ⟨M', hM', e⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h)
          (hAbI a ha)
        refine ⟨M', hM', ?_, e⟩
        have hM'G : M' ∈ G := hGN ⟨M', TableBUE.gu_subset_normalizer h hM'⟩ (e ▸ ha)
        obtain ⟨c', hc'⟩ := hall M' hM'G
        set y : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) c'⁻¹ * M' with hy
        have hyG : y ∈ G := G.mul_mem (hGp.scalar_mem _) hM'G
        have hyp : y ^ p = 1 := TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow hc'
        have hcs := (TypeA.PGLTor.commute_scalar c' (P : GL (Fin d) K)⁻¹).eq
        have e2 : (P : GL (Fin d) K)⁻¹ * M' * P =
            GeneralLinearGroup.scalar (Fin d) c' * ((P : GL (Fin d) K)⁻¹ * y * P) := by
          rw [hy]
          calc (P : GL (Fin d) K)⁻¹ * M' * P = (P : GL (Fin d) K)⁻¹ *
              (GeneralLinearGroup.scalar (Fin d) c' * GeneralLinearGroup.scalar (Fin d) c'⁻¹ *
                M') * P := by rw [← map_mul, mul_inv_cancel, map_one, one_mul]
            _ = ((P : GL (Fin d) K)⁻¹ * GeneralLinearGroup.scalar (Fin d) c') *
                (GeneralLinearGroup.scalar (Fin d) c'⁻¹ * M') * P := by group
            _ = GeneralLinearGroup.scalar (Fin d) c' * ((P : GL (Fin d) K)⁻¹ *
                (GeneralLinearGroup.scalar (Fin d) c'⁻¹ * M') * P) := by rw [← hcs]; group
        rw [e2, Units.val_mul, GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]
        exact (hdiagG y hyG hyp).smul _
      obtain ⟨π, hπs, hπker, hdiag⟩ :=
        LineU.exists_diagModel_of_frame h hd hcov.1
          (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf) hψ hker hperf hAI P.2 hframe
      have hπ : UnitTB.Model π := ⟨h, hπs, hπker⟩
      exact ggWNormConcl_of_unitary_diagonal hK hp hp2 hpq hd hπ hA h3 hsc hdiag
        hM hC ι φ hh α hpair hlin hgen hs
    ·
      exfalso
      push Not at hall
      obtain ⟨x, hxG, hx⟩ := hall
      obtain ⟨l, hl⟩ := hGp.pow_scalar x hxG
      have hl' : ∀ μ : Kˣ, μ ^ p ≠ l := fun μ hμ => hx μ (by rw [hl, hμ])
      have hNT : ¬ TypeA.PGLTor.IsToral G := by
        intro htor
        obtain ⟨A₀, hA₀⟩ := htor
        set D : GL (Fin d) K := A₀ * x * A₀⁻¹ with hD
        have hDd : (D : Matrix (Fin d) (Fin d) K) =
            diagonal (fun i => (D : Matrix (Fin d) (Fin d) K) i i) := by
          refine TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero fun i j hij => ?_
          rw [hD, Units.val_mul, Units.val_mul]
          exact hA₀ x hxG i j hij
        have hDp : D ^ p = GeneralLinearGroup.scalar (Fin d) l := by
          rw [hD, conj_pow, hl, ← (TypeA.PGLTor.commute_scalar l A₀).eq, mul_inv_cancel_right]
        set i₀ : Fin d := ⟨0, hd0⟩
        have h0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hDd i₀
        apply hl' (Units.mk0 _ h0)
        apply Units.ext
        have e := congrArg (fun Z : GL (Fin d) K => (Z : Matrix (Fin d) (Fin d) K) i₀ i₀) hDp
        simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, diagonal_apply_eq] at e
        rw [hDd, diagonal_pow, diagonal_apply_eq, Pi.pow_apply] at e
        rw [Units.val_pow_eq_pow_val, Units.val_mk0]
        exact e
      have h1 : Nat.card Ab * (Nat.card K - 1) ≤ Nat.card G := by
        have hsec : ∀ a : Ab, ∃ M' : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
            TableB.projConj (unitarySU 2 n K d) M' = a.1 := fun a => by
          obtain ⟨M', hM', e⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h)
            (hAbI a a.2)
          exact ⟨_, e.symm⟩
        choose sec hsec using hsec
        let F : Ab × Kˣ → G := fun q =>
          ⟨GeneralLinearGroup.scalar (Fin d) q.2 * (sec q.1 : GL (Fin d) K),
            ⟨GeneralLinearGroup.scalar (Fin d) q.2, hc.scalar_mem q.2⟩ * sec q.1,
            Subgroup.mem_comap.mpr (by rw [map_mul, hc.map_scalar, one_mul, hsec]; exact q.1.2),
            rfl⟩
        have hF : Function.Injective F := by
          rintro ⟨a, u⟩ ⟨a', u'⟩ hq
          have hq' : GeneralLinearGroup.scalar (Fin d) u * (sec a : GL (Fin d) K) =
              GeneralLinearGroup.scalar (Fin d) u' * (sec a' : GL (Fin d) K) :=
            congrArg Subtype.val hq
          have e1 : (⟨GeneralLinearGroup.scalar (Fin d) u, hc.scalar_mem u⟩ * sec a :
              Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) =
              ⟨GeneralLinearGroup.scalar (Fin d) u', hc.scalar_mem u'⟩ * sec a' :=
            Subtype.ext hq'
          have e2 := congrArg (TableB.projConj (unitarySU 2 n K d)) e1
          rw [map_mul, map_mul, hc.map_scalar, hc.map_scalar, one_mul, one_mul, hsec,
            hsec] at e2
          have haa : a = a' := Subtype.ext e2
          subst haa
          have e3 : GeneralLinearGroup.scalar (Fin d) u = GeneralLinearGroup.scalar (Fin d) u' :=
            mul_right_cancel hq'
          exact Prod.ext rfl (TypeA.PGLTor.scalar_injective e3)
        have h1 := Nat.card_le_card_of_injective F hF
        rw [Nat.card_prod, Nat.card_units] at h1
        exact h1
      have hK1 : 0 < Nat.card K - 1 := by
        have := Finite.one_lt_card (α := K)
        omega
      have hbound : Nat.card A ≤ p ^ 3 := by
        rcases TypeA.PGLTor.toral_or_card_le_of_central_sharp hp hp2 hpK hGp hcent with
          htor | hb
        · exact (hNT htor).elim
        · have e3 : Fintype.card (Fin d) / p = 3 := by
            rw [Fintype.card_fin, hdp, Nat.mul_div_cancel 3 hp.pos]
          rw [e3] at hb
          calc Nat.card A = Nat.card Ab := hcardAb.symm
            _ ≤ p ^ 3 := Nat.le_of_mul_le_mul_right (h1.trans hb) hK1
      have hxo : 0 < orderOf x := orderOf_pos x
      obtain ⟨e, m', hm'p, hxe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hxo.ne' p hp.ne_one
      have hcop : Nat.Coprime m' p :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm'p)
      obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
      set x₂ : GL (Fin d) K := x ^ (m' * k) with hx₂
      have hx₂G : x₂ ∈ G := G.pow_mem hxG _
      have hx₂b : x₂ ^ p ^ e = 1 := by
        rw [hx₂, ← pow_mul, show m' * k * p ^ e = orderOf x * k by rw [hxe]; ring, pow_mul,
          pow_orderOf_eq_one, one_pow]
      set l₂ : Kˣ := l ^ (m' * k) with hl₂
      have hx₂p : x₂ ^ p = GeneralLinearGroup.scalar (Fin d) l₂ := by
        rw [hx₂, ← pow_mul, mul_comm, pow_mul, hl, ← map_pow]
      have hl₂' : ∀ μ : Kˣ, μ ^ p ≠ l₂ := by
        intro μ hμ
        have hdm : m' * k = m' * k / p * p + 1 := by
          have h1 := Nat.div_add_mod (m' * k) p
          rw [hk, Nat.mul_comm p] at h1
          exact h1.symm
        apply hl' (μ * (l ^ (m' * k / p))⁻¹)
        rw [mul_pow, inv_pow, ← pow_mul, hμ, hl₂]
        nth_rewrite 1 [hdm]
        rw [pow_succ, mul_comm (l ^ (m' * k / p * p)) l, mul_inv_cancel_right]
      have hx₂U : x₂ ∈ primeFormUnitary h (idGram K d) := hunitG x₂ hx₂G e hx₂b
      obtain ⟨M₂, hM₂A, hM₂c⟩ := Subgroup.mem_map.mp hx₂G
      have hM₂c' : (M₂ : GL (Fin d) K) = x₂ := hM₂c
      obtain ⟨y₀, hy₀A, hy₀p, hy₀s⟩ := QuotMove.exists_nonscalar_of_lt_card hc hp hp2 hψ hker
        hperf hA hAI' (x₀ := M₂) hM₂A (by rw [hM₂c']; exact hx₂p) hl₂'
        (lt_of_lt_of_le (lt_self_pow₀ hp.one_lt (by norm_num)) h3)
      have hy₀G : (y₀ : GL (Fin d) K) ∈ G := hGN y₀ hy₀A
      set wt : Fin d → GL (Fin d) K → K := fun j z =>
        (((P : GL (Fin d) K)⁻¹ * z * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j j with hwt
      set i₀ : Fin d := ⟨0, hd0⟩ with hi₀
      have hdiagw : ∀ z ∈ G, z ^ p = 1 →
          (((P : GL (Fin d) K)⁻¹ * z * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            diagonal (fun j => wt j z) := fun z hz hzp =>
        ((Matrix.isDiag_iff_diagonal_diag _).mp (hdiagG z hz hzp)).symm
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, wt j₀ y₀ ≠ wt i₀ y₀ := by
        by_contra hcon
        push Not at hcon
        have hD := hdiagw _ hy₀G hy₀p
        have h0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hD i₀
        apply hy₀s (Units.mk0 _ h0)
        have e1 : (P : GL (Fin d) K)⁻¹ * y₀ * P =
            GeneralLinearGroup.scalar (Fin d) (Units.mk0 _ h0) := by
          apply Units.ext
          rw [hD, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
          exact congrArg diagonal (funext hcon)
        calc (y₀ : GL (Fin d) K) = (P : GL (Fin d) K) * ((P : GL (Fin d) K)⁻¹ * y₀ * P) *
              (P : GL (Fin d) K)⁻¹ := by group
          _ = GeneralLinearGroup.scalar (Fin d) (Units.mk0 _ h0) := by
            rw [e1, ← (TypeA.PGLTor.commute_scalar _ (P : GL (Fin d) K)).eq, mul_inv_cancel_right]
      set S : Finset (Fin d) := Finset.univ.filter fun j => ∀ z ∈ G, z ^ p = 1 → wt j z = wt i₀ z
        with hS
      have hmemS : ∀ j, j ∈ S ↔ ∀ z ∈ G, z ^ p = 1 → wt j z = wt i₀ z := fun j => by
        rw [hS, Finset.mem_filter]
        simp
      have hi₀S : i₀ ∈ S := (hmemS i₀).mpr fun _ _ _ => rfl
      have hj₀S : j₀ ∉ S := fun hj => hj₀ ((hmemS j₀).mp hj _ hy₀G hy₀p)
      have hsep : ∀ i k, i ∈ S → k ∉ S → ∃ z ∈ G, z ^ p = 1 ∧ wt i z ≠ wt k z := by
        intro i k hi hk
        rw [hmemS] at hk
        push Not at hk
        obtain ⟨z, hz, hzp, hne⟩ := hk
        exact ⟨z, hz, hzp, fun he => hne (he.symm.trans ((hmemS i).mp hi z hz hzp))⟩
      have hblock : ∀ g ∈ G, UnitaryThreeP.IsSBlock S
          (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        intro g hg
        have hzero : ∀ i k, (∃ z ∈ G, z ^ p = 1 ∧ wt i z ≠ wt k z) →
            (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i k = 0 := by
          rintro i k ⟨z, hz, hzp, hne⟩
          have hgz : g * z = z * g := hcent z hz hzp g hg
          have hcomm : (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              diagonal (fun j => wt j z) = diagonal (fun j => wt j z) *
                (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [← hdiagw z hz hzp, ← Units.val_mul, ← Units.val_mul]
            congr 1
            calc (P : GL (Fin d) K)⁻¹ * g * P * ((P : GL (Fin d) K)⁻¹ * z * P) =
                (P : GL (Fin d) K)⁻¹ * (g * z) * P := by group
              _ = (P : GL (Fin d) K)⁻¹ * z * P * ((P : GL (Fin d) K)⁻¹ * g * P) := by
                rw [hgz]; group
          exact TypeA.PGLTor.isBlockDiag_of_commute_diagonal hcomm i k hne
        exact ⟨fun i hi k hk => hzero i k (hsep i k hi hk),
          fun i hi k hk => hzero i k (by
            obtain ⟨z, hz, hzp, hne⟩ := hsep k i hk hi
            exact ⟨z, hz, hzp, Ne.symm hne⟩)⟩
      obtain ⟨E, hESU, hEx, hEcomm⟩ := UnitaryThreeP.exists_block_conj h hp hp2 hpq hζ P.2 hx₂U
        hx₂b hx₂p hl₂' (hblock x₂ hx₂G)
      set δ : GL (Fin d) K := (P : GL (Fin d) K) * UnitaryThreeP.blockScalar S ζ *
        (P : GL (Fin d) K)⁻¹ with hδ
      have hδx : δ = E * x₂ * E⁻¹ * x₂⁻¹ := by rw [hEx, mul_inv_cancel_right]
      have hx₂N : x₂ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
        hM₂c' ▸ M₂.2
      have hδSU : δ ∈ unitarySU 2 n K d := by
        have e : δ = E * (x₂ * E⁻¹ * x₂⁻¹) := by rw [hδx]; group
        rw [e]
        exact (unitarySU 2 n K d).mul_mem hESU
          ((Subgroup.mem_normalizer_iff.mp hx₂N (E⁻¹)).mp ((unitarySU 2 n K d).inv_mem hESU))
      have hδp : δ ^ p = 1 := by
        rw [hδ, conj_pow, UnitaryThreeP.blockScalar_pow, hζ.pow_eq_one, UnitaryThreeP.blockScalar,
          map_one, map_one, mul_one, mul_inv_cancel]
      have hδG : ∀ g ∈ G, g * δ = δ * g := by
        intro g hg
        have h1 : ((P : GL (Fin d) K)⁻¹ * g * P) * UnitaryThreeP.blockScalar S ζ =
            UnitaryThreeP.blockScalar S ζ * ((P : GL (Fin d) K)⁻¹ * g * P) := by
          apply Units.ext
          change (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              ((UnitaryThreeP.blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            ((UnitaryThreeP.blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          rw [UnitaryThreeP.coe_blockScalar]
          exact (UnitaryThreeP.blockExt_smul_one_comm (hblock g hg) _).symm
        calc g * δ = (P : GL (Fin d) K) * (((P : GL (Fin d) K)⁻¹ * g * P) *
              UnitaryThreeP.blockScalar S ζ) * (P : GL (Fin d) K)⁻¹ := by rw [hδ]; group
          _ = δ * g := by rw [h1, hδ]; group
      have hδs : ∀ u : Kˣ, δ ≠ GeneralLinearGroup.scalar (Fin d) u := by
        intro u hu
        have e1 : UnitaryThreeP.blockScalar S ζ = GeneralLinearGroup.scalar (Fin d) u := by
          calc UnitaryThreeP.blockScalar S ζ = (P : GL (Fin d) K)⁻¹ * δ * P := by rw [hδ]; group
            _ = GeneralLinearGroup.scalar (Fin d) u := by
              rw [hu, ← (TypeA.PGLTor.commute_scalar u (P : GL (Fin d) K)⁻¹).eq,
                inv_mul_cancel_right]
        have e2 : ((UnitaryThreeP.blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            ((GeneralLinearGroup.scalar (Fin d) u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
          congrArg _ e1
        rw [UnitaryThreeP.coe_blockScalar, GeneralLinearGroup.coe_scalar] at e2
        have hi : TableBUE.blockExt S ((ζ : K) • (1 : Matrix (Fin S.card) (Fin S.card) K)) i₀ i₀ =
            (u : K) := by rw [e2, Matrix.scalar_apply, diagonal_apply_eq]
        have hj : TableBUE.blockExt S ((ζ : K) • (1 : Matrix (Fin S.card) (Fin S.card) K)) j₀ j₀ =
            (u : K) := by rw [e2, Matrix.scalar_apply, diagonal_apply_eq]
        rw [UnitaryThreeP.apply_eq_blockRes (TableBUE.blockExt S ((ζ : K) •
          (1 : Matrix (Fin S.card) (Fin S.card) K))) hi₀S hi₀S, TableBUE.blockRes_blockExt,
          Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hi
        rw [TableBUE.isBlockOn_blockExt _ j₀ j₀ (Or.inl hj₀S), Matrix.one_apply_eq] at hj
        have hζ1 : (ζ : K) = 1 := hi.trans hj.symm
        have : ζ = 1 := Units.ext hζ1
        exact hp.one_lt.ne' (hζ.eq_orderOf.trans (by rw [this, orderOf_one]))
      have hδA : TableB.projConj (unitarySU 2 n K d)
          ⟨δ, Subgroup.le_normalizer hδSU⟩ ∈ Ab :=
        UnitaryThreeP.projConj_mem_inducedSub_of_commute hcov hψ hker hperf hAI' hsc
          ⟨δ, hδSU⟩ (Subtype.ext (by rw [Subgroup.coe_pow, hδp]; rfl))
          (fun M' hM' => hδG _ (hGN M' hM'))
      have hEy : ∀ y : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          TableB.projConj (unitarySU 2 n K d) y ∈ Ab → (y : GL (Fin d) K) ^ p = 1 →
            E * y = y * E := fun y hy hyp => by
        have hyG := hGN y hy
        refine hEcomm y (hblock y hyG) ⟨wt i₀ y, ?_⟩
        rw [hdiagw y hyG hyp]
        exact UnitaryThreeP.blockRes_diagonal_of_const fun j hj => (hmemS j).mp hj _ hyG hyp
      rcases hp35 with rfl | hp5
      ·
        have h3' : 3 ^ 3 ≤ Nat.card Ab := by rw [hcardAb]; exact h3
        obtain ⟨σ, hσmul, hσsc, hσ3, hσconj, hσne⟩ :=
          TypeA.PGLTor.exists_threeBlock_invariant hpK hGp hcent hNT
            (by rw [Fintype.card_fin, hdp]) ((Nat.mul_le_mul_right _ h3').trans h1)
        have hδdiag : (((P : GL (Fin d) K)⁻¹ * δ * P : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) = diagonal fun j => if j ∈ S then (ζ : K) else 1 := by
          have e : (P : GL (Fin d) K)⁻¹ * δ * P = UnitaryThreeP.blockScalar S ζ := by
            rw [hδ]; group
          rw [e, UnitaryThreeP.coe_blockScalar]
          ext i j
          by_cases hi : i ∈ S
          · by_cases hj : j ∈ S
            · simp [TableBUE.blockExt, hi, hj, Matrix.one_apply, diagonal_apply]
            · have hij : i ≠ j := fun e => hj (e ▸ hi)
              simp [TableBUE.blockExt, hi, hj, hij, diagonal_apply]
          · by_cases hij : i = j
            · subst hij
              simp [TableBUE.blockExt, hi, diagonal_apply]
            · simp [TableBUE.blockExt, hi, hij, Matrix.one_apply, diagonal_apply]
        have hζ1 : (ζ : K) ≠ 1 := by
          rw [Ne, Units.val_eq_one]
          exact hζ.ne_one (by norm_num)
        exact QuotMove.false_of_transvection_three_of_commute hc hψ hker hperf hA hAI'
          (x₀ := M₂) hM₂A (by rw [hM₂c']; exact hx₂p) hl₂' ⟨E, hESU⟩
          ⟨δ, Subgroup.le_normalizer hδSU⟩ hδA hδp (by rw [hM₂c']; exact hEx) hEy σ
          (fun z z' hz hz' hz3 => (hcent _ (hGN z hz) hz3 _ (hGN z' hz')).symm)
          (fun z z' hz hz' hz3 hz'3 => hσmul _ (hGN z hz) _ (hGN z' hz') hz3 hz'3)
          (fun u z hu _ _ => hσsc u hu _)
          (fun s hs z hz hz3 => hσconj _ _ (hGN z hz) hz3 (by
            have hm := hGN (s * z * s⁻¹) (by rw [map_mul, map_mul, map_inv]; exact hs _ hz)
            simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hm))
          (fun z hz hz3 => hσ3 _ (hGN z hz) hz3)
          (hσne _ hζ1 δ (hGN _ hδA) hδp P _ hδdiag
            (fun j => by by_cases hj : j ∈ S <;> simp [hj])
            ⟨j₀, by simp [hj₀S]⟩ ⟨i₀, by simp [hi₀S]⟩)
          hC ι φ hh α hpair hlin hgen
      · exact QuotMove.false_of_transvection_of_commute hc hp hp5 hψ hker hperf hA hAI' hbound
          (x₀ := M₂) hM₂A (by rw [hM₂c']; exact hx₂p) hl₂' ⟨E, hESU⟩
          ⟨δ, Subgroup.le_normalizer hδSU⟩ hδA hδs (by rw [hM₂c']; exact hEx) hEy
          hM hC ι φ hh α hpair hlin hgen
  ·
    exfalso
    push Not at hcent
    obtain ⟨g, hgG, hgp, g', hg'G, hne⟩ := hcent
    obtain ⟨x₀, hx₀A, rfl⟩ := Subgroup.mem_map.mp hgG
    obtain ⟨y₀, hy₀A, rfl⟩ := Subgroup.mem_map.mp hg'G
    have hgU := hunitG _ hgG 1 (by rwa [pow_one])
    set u : Kˣ := TypeA.PGLTor.commChar hGp hgG ⟨_, hg'G⟩ with hu
    have hcomm := TypeA.PGLTor.commChar_spec hGp hgG ⟨_, hg'G⟩
    rw [← hu] at hcomm
    have hu1 : u ≠ 1 := by
      intro h1
      apply hne
      rw [hcomm, h1, map_one, one_mul]
    have hup : u ^ p = 1 := TypeA.PGLTor.commChar_pow_eq_one hGp hgG ⟨_, hg'G⟩
    rcases hp35 with rfl | hp5
    ·
      obtain ⟨c', M', hM', hy₀eq⟩ := hGU _ hg'G
      have hy₀eq' : (y₀ : GL (Fin d) K) = GeneralLinearGroup.scalar (Fin d) c' * M' := hy₀eq
      have hyA : TableB.projConj (unitarySU 2 n K d)
          ⟨M', TableBUE.gu_subset_normalizer h hM'⟩ ∈ Ab := by
        have e : (⟨M', TableBUE.gu_subset_normalizer h hM'⟩ :
            Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) =
            ⟨GeneralLinearGroup.scalar (Fin d) c'⁻¹, hc.scalar_mem c'⁻¹⟩ * y₀ := by
          apply Subtype.ext
          change M' = GeneralLinearGroup.scalar (Fin d) c'⁻¹ * (y₀ : GL (Fin d) K)
          rw [hy₀eq', ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
        rw [e, map_mul, hc.map_scalar, one_mul]
        exact hy₀A
      have hxy : (x₀ : GL (Fin d) K) * M' =
          GeneralLinearGroup.scalar (Fin d) u * (M' * (x₀ : GL (Fin d) K)) := by
        have hcomm' : (x₀ : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) c' * M') =
            GeneralLinearGroup.scalar (Fin d) u *
              (GeneralLinearGroup.scalar (Fin d) c' * M' * x₀) := by
          rw [← hy₀eq']
          exact hcomm
        have hc1 := (TypeA.PGLTor.commute_scalar c' (x₀ : GL (Fin d) K)).eq
        have hc2 : GeneralLinearGroup.scalar (Fin d) u * GeneralLinearGroup.scalar (Fin d) c' =
            GeneralLinearGroup.scalar (Fin d) c' * GeneralLinearGroup.scalar (Fin d) u := by
          rw [← map_mul, ← map_mul, mul_comm]
        apply mul_left_cancel (a := GeneralLinearGroup.scalar (Fin d) c')
        calc GeneralLinearGroup.scalar (Fin d) c' * ((x₀ : GL (Fin d) K) * M')
            = (x₀ : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) c' * M') := by
              rw [← mul_assoc, hc1, mul_assoc]
          _ = GeneralLinearGroup.scalar (Fin d) u *
              (GeneralLinearGroup.scalar (Fin d) c' * M' * x₀) := hcomm'
          _ = GeneralLinearGroup.scalar (Fin d) c' *
              (GeneralLinearGroup.scalar (Fin d) u * (M' * x₀)) := by
              simp only [← mul_assoc, hc2]
      have hdiag : ∀ i, α i (hh i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
      exact UnitaryPhase.false_of_unitary_noncomm_three h hK hpq ⟨3, hdp⟩ (by omega) hdq hψ hker
        hperf hA hAI' (TableBUD.mem_guSet_of_mem_primeFormUnitary h hgU) hM' hx₀A hyA hgU hgp
        hu1 hup hxy ι φ hh α hdiag hlin hgen
    obtain ⟨D, hDSU, hDact⟩ :=
      UnitaryPhase.exists_unitary_quadPhase h hp hp5 hpq hζ hgU hgp hu1 hup hcomm
    obtain ⟨k, -, hk⟩ := QuotMove.exists_pow_eq_units hζ hup
    have hk0 : ¬ p ∣ k := by
      rintro ⟨j, rfl⟩
      apply hu1
      rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
    obtain ⟨cE, hcE⟩ := hDact _ k (by rw [hk]; exact hcomm)
    have hdiag : ∀ i, α i (hh i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    exact QuotMove.false_of_normalizing_move hc hp hpK hp2 hψ hker hperf hA hAI' (x₀ := x₀)
      (y₀ := y₀) hx₀A hy₀A hcomm hu1 ⟨D, hDSU⟩
      (QuotMove.conj_mem_inducedSub_of_phase hc hp hζ hψ hA hAI' hx₀A hgp
        (Subgroup.inclusion hc.le ⟨D, hDSU⟩) hDact)
      hk0 hcE ι φ hh α hdiag hlin hgen

theorem largeEvenLabelAll_wnorm_unitary_three_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : lab.tag = .twA)
    (hdp : lab.rank + 1 = 3 * p) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hdp hpq ⊢
  subst tag
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · have h2 : p ∣ 2 := by simpa using hpq
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact h0
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_unitary_three_prime hK hn hp (by omega) hpq hdp

theorem largeEvenLabelAll_wnorm_unitary_nine_three {p : ℕ} {lab : LargeEvenLabel}
    (hp3 : p = 3) (ht : lab.tag = .twA) (hdp : lab.rank + 1 = 9) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  subst hp3
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hdp hpq ⊢
  subst tag
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · norm_num at hpq
    · exact h0
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_unitary_three_prime hK hn Nat.prime_three (by norm_num) hpq (by omega)

end CFSG.StandardType
