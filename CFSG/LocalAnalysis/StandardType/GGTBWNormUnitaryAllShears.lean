module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryFourPrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormMpCellLabels
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryTwicePrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel


theorem ggTorusWNormSC_unitary_of_odd {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : 5 ≤ p ∨ p ∣ d) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hd6 : (d, n) ≠ (6, 1)) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
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
      set wt : Fin d → GL (Fin d) K → K := fun j z =>
        (((P : GL (Fin d) K)⁻¹ * z * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j j with hwt
      have hdiagw : ∀ z ∈ G, z ^ p = 1 →
          (((P : GL (Fin d) K)⁻¹ * z * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            diagonal (fun j => wt j z) := fun z hz hzp =>
        ((Matrix.isDiag_iff_diagonal_diag _).mp (hdiagG z hz hzp)).symm
      set cls : Fin d → Finset (Fin d) := fun b =>
        Finset.univ.filter fun j => ∀ z ∈ G, z ^ p = 1 → wt j z = wt b z with hcls
      have hmemC : ∀ b j, j ∈ cls b ↔ ∀ z ∈ G, z ^ p = 1 → wt j z = wt b z := fun b j => by
        rw [hcls, Finset.mem_filter]
        simp
      have hbC : ∀ b, b ∈ cls b := fun b => (hmemC b b).mpr fun _ _ _ => rfl
      have hclsC : ∀ b j j', j' ∈ cls j → (j ∈ cls b ↔ j' ∈ cls b) := by
        intro b j j' hj'
        rw [hmemC, hmemC]
        exact ⟨fun hj z hz hzp => ((hmemC j j').mp hj' z hz hzp).trans (hj z hz hzp),
          fun hj z hz hzp => ((hmemC j j').mp hj' z hz hzp).symm.trans (hj z hz hzp)⟩
      have hsepC : ∀ b i k, i ∈ cls b → k ∉ cls b → ∃ z ∈ G, z ^ p = 1 ∧ wt i z ≠ wt k z := by
        intro b i k hi hk
        rw [hmemC] at hk
        push Not at hk
        obtain ⟨z, hz, hzp, hne⟩ := hk
        exact ⟨z, hz, hzp, fun he => hne (he.symm.trans ((hmemC b i).mp hi z hz hzp))⟩
      have hblockC : ∀ b, ∀ g ∈ G, UnitaryThreeP.IsSBlock (cls b)
          (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        intro b g hg
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
        exact ⟨fun i hi k hk => hzero i k (hsepC b i k hi hk),
          fun i hi k hk => hzero i k (by
            obtain ⟨z, hz, hzp, hne⟩ := hsepC b k i hk hi
            exact ⟨z, hz, hzp, Ne.symm hne⟩)⟩
      set DC : GL (Fin d) K → Prop := fun y => ∃ w : Fin d → K,
        (((P : GL (Fin d) K)⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w ∧
          (∀ b j, j ∈ cls b → w j = w b) ∧ ∀ j, w j ^ p = 1 with hDC
      have hDCG : ∀ z ∈ G, z ^ p = 1 → DC z := by
        intro z hz hzp
        refine ⟨fun j => wt j z, hdiagw z hz hzp, fun b j hj => (hmemC b j).mp hj z hz hzp, ?_⟩
        intro j
        have e1 : (((P : GL (Fin d) K)⁻¹ * z * P) ^ p : GL (Fin d) K) = 1 := by
          rw [show (P : GL (Fin d) K)⁻¹ * z * P =
              (P : GL (Fin d) K)⁻¹ * z * ((P : GL (Fin d) K)⁻¹)⁻¹ by rw [inv_inv],
            conj_pow, hzp, mul_one, mul_inv_cancel]
        have e2 := congrArg (fun Z : GL (Fin d) K => (Z : Matrix (Fin d) (Fin d) K) j j) e1
        simp only [Units.val_pow_eq_pow_val, Units.val_one] at e2
        rw [hdiagw z hz hzp, diagonal_pow, diagonal_apply_eq, Pi.pow_apply,
          Matrix.one_apply_eq] at e2
        exact e2
      have hDCblock : ∀ b y, DC y → UnitaryThreeP.IsSBlock (cls b)
          (((P : GL (Fin d) K)⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rintro b y ⟨w, hw, -, -⟩
        rw [hw]
        exact UnitaryThreeP.isSBlock_diagonal w
      have hblockScalarC : ∀ b (u : Kˣ), (u : K) ^ p = 1 →
          DC ((P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls b) u * (P : GL (Fin d) K)⁻¹) := by
        intro b u hu
        refine ⟨fun j => if j ∈ cls b then (u : K) else 1, ?_, ?_, ?_⟩
        · rw [show (P : GL (Fin d) K)⁻¹ * ((P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls b) u *
              (P : GL (Fin d) K)⁻¹) * P = UnitaryThreeP.blockScalar (cls b) u by group,
            UnitaryFourP.coe_blockScalar_eq_diagonal]
        · intro b' j hj
          simp only [hclsC b b' j hj]
        · intro j
          dsimp only
          split_ifs
          · exact hu
          · exact one_pow p
      have hDCmul : ∀ y y', DC y → DC y' → DC (y * y') := by
        rintro y y' ⟨w, hw, hwc, hwp⟩ ⟨w', hw', hwc', hwp'⟩
        refine ⟨fun j => w j * w' j, ?_, fun b j hj => by dsimp only; rw [hwc b j hj, hwc' b j hj],
          fun j => by dsimp only; rw [mul_pow, hwp, hwp', one_mul]⟩
        rw [show (P : GL (Fin d) K)⁻¹ * (y * y') * P =
            ((P : GL (Fin d) K)⁻¹ * y * P) * ((P : GL (Fin d) K)⁻¹ * y' * P) by group,
          Units.val_mul, hw, hw', diagonal_mul_diagonal]
      set bad : GL (Fin d) K → Finset (Fin d) := fun y => Finset.univ.filter fun j =>
        (((P : GL (Fin d) K)⁻¹ * y * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j j ≠ 1
        with hbad
      have hshearDC : ∀ m : ℕ, ∀ y : GL (Fin d) K, DC y → (bad y).card ≤ m →
          ∃ E ∈ unitarySU 2 n K d, E * x₂ * E⁻¹ = y * x₂ ∧ ∀ z, DC z → E * z = z * E := by
        intro m
        induction m with
        | zero =>
          rintro y ⟨w, hw, -, -⟩ hcard
          have hw1 : ∀ j, w j = 1 := by
            intro j
            by_contra hj
            have hmem : j ∈ bad y := by
              rw [hbad, Finset.mem_filter, hw, diagonal_apply_eq]
              exact ⟨Finset.mem_univ _, hj⟩
            have := Finset.card_pos.mpr ⟨j, hmem⟩
            omega
          have hy1 : y = 1 := by
            have e1 : (P : GL (Fin d) K)⁻¹ * y * P = 1 := by
              apply Units.ext
              rw [hw, Units.val_one, show w = fun _ => (1 : K) from funext hw1, diagonal_one]
            calc y = (P : GL (Fin d) K) * ((P : GL (Fin d) K)⁻¹ * y * P) *
                  (P : GL (Fin d) K)⁻¹ := by group
              _ = 1 := by rw [e1, mul_one, mul_inv_cancel]
          refine ⟨1, (unitarySU 2 n K d).one_mem, ?_, fun z _ => by rw [one_mul, mul_one]⟩
          rw [hy1]
          group
        | succ m ih =>
          intro y hy hcard
          by_cases hm : (bad y).card ≤ m
          · exact ih y hy hm
          obtain ⟨w, hw, hwc, hwp⟩ := hy
          obtain ⟨j₁, hj₁⟩ : ∃ j₁, j₁ ∈ bad y := by
            by_contra hcon
            push Not at hcon
            have : bad y = ∅ := Finset.eq_empty_of_forall_notMem hcon
            rw [this, Finset.card_empty] at hm
            omega
          have hwj₁ : w j₁ ≠ 1 := by
            have := (Finset.mem_filter.mp hj₁).2
            rwa [hw, diagonal_apply_eq] at this
          have hw0 : w j₁ ≠ 0 := by
            intro h0
            have := hwp j₁
            rw [h0, zero_pow hp.ne_zero] at this
            exact zero_ne_one this
          set wU : Kˣ := Units.mk0 _ hw0 with hwU
          have hwUp : wU ^ p = 1 := Units.ext (by
            rw [Units.val_pow_eq_pow_val, hwU, Units.val_mk0, hwp, Units.val_one])
          obtain ⟨e, he, hζe⟩ := QuotMove.exists_pow_eq_units hζ hwUp
          obtain ⟨Eb, hEbSU, hEbx, hEbc⟩ := UnitaryThreeP.exists_block_conj h hp hp2 hpq hζ P.2
            hx₂U hx₂b hx₂p hl₂' (hblockC j₁ x₂ hx₂G)
          set δb : GL (Fin d) K := (P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls j₁) ζ *
            (P : GL (Fin d) K)⁻¹ with hδb
          have hEbDC : ∀ z, DC z → Eb * z = z * Eb := by
            rintro z ⟨wz, hwz, hwzc, -⟩
            refine hEbc z (by rw [hwz]; exact UnitaryThreeP.isSBlock_diagonal wz) ⟨wz j₁, ?_⟩
            rw [hwz]
            exact UnitaryThreeP.blockRes_diagonal_of_const fun j hj => hwzc j₁ j hj
          have hδbpow : ∀ k : ℕ, δb ^ k = (P : GL (Fin d) K) *
              UnitaryThreeP.blockScalar (cls j₁) (ζ ^ k) * (P : GL (Fin d) K)⁻¹ := by
            intro k
            rw [hδb, conj_pow, UnitaryThreeP.blockScalar_pow]
          have hδbDC : ∀ k : ℕ, DC (δb ^ k) := by
            intro k
            rw [hδbpow k]
            apply hblockScalarC
            rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val,
              hζ.pow_eq_one, Units.val_one, one_pow]
          have hEbpow : ∀ k : ℕ, Eb ^ k * x₂ * (Eb ^ k)⁻¹ = δb ^ k * x₂ := by
            intro k
            induction k with
            | zero => group
            | succ k ihk =>
              have hc : Eb * δb ^ k = δb ^ k * Eb := hEbDC _ (hδbDC k)
              calc Eb ^ (k + 1) * x₂ * (Eb ^ (k + 1))⁻¹
                  = Eb * (Eb ^ k * x₂ * (Eb ^ k)⁻¹) * Eb⁻¹ := by group
                _ = Eb * δb ^ k * x₂ * Eb⁻¹ := by rw [ihk]; group
                _ = δb ^ k * (Eb * x₂ * Eb⁻¹) := by rw [hc]; group
                _ = δb ^ (k + 1) * x₂ := by rw [hEbx]; group
          set y' : GL (Fin d) K := y * δb ^ (p - e) with hy'
          have hy'DC : DC y' := hDCmul y _ ⟨w, hw, hwc, hwp⟩ (hδbDC (p - e))
          have hdiag' : (((P : GL (Fin d) K)⁻¹ * y' * P : GL (Fin d) K) :
              Matrix (Fin d) (Fin d) K) =
              diagonal fun j => w j * (if j ∈ cls j₁ then ((ζ ^ (p - e) : Kˣ) : K) else 1) := by
            rw [show (P : GL (Fin d) K)⁻¹ * y' * P = ((P : GL (Fin d) K)⁻¹ * y * P) *
                ((P : GL (Fin d) K)⁻¹ * δb ^ (p - e) * P) by rw [hy']; group,
              Units.val_mul, hw, hδbpow (p - e),
              show (P : GL (Fin d) K)⁻¹ * ((P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls j₁)
                (ζ ^ (p - e)) * (P : GL (Fin d) K)⁻¹) * P =
                UnitaryThreeP.blockScalar (cls j₁) (ζ ^ (p - e)) by group,
              UnitaryFourP.coe_blockScalar_eq_diagonal, diagonal_mul_diagonal]
          have hsub : bad y' ⊆ (bad y).erase j₁ := by
            intro j hj
            have hj' := (Finset.mem_filter.mp hj).2
            rw [hdiag', diagonal_apply_eq] at hj'
            by_cases hjc : j ∈ cls j₁
            · exfalso
              apply hj'
              rw [if_pos hjc, hwc j₁ j hjc, show w j₁ = (wU : K) by rw [hwU, Units.val_mk0], ← hζe,
                ← Units.val_mul, ← pow_add, Nat.add_sub_cancel' he.le, hζ.pow_eq_one, Units.val_one]
            · rw [if_neg hjc, mul_one] at hj'
              refine Finset.mem_erase.mpr ⟨fun hjj => hjc (hjj ▸ hbC j₁), ?_⟩
              rw [hbad, Finset.mem_filter, hw, diagonal_apply_eq]
              exact ⟨Finset.mem_univ _, hj'⟩
          have hcard' : (bad y').card ≤ m := by
            have h1 := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hj₁] at h1
            omega
          obtain ⟨E', hE'SU, hE'x, hE'c⟩ := ih y' hy'DC hcard'
          refine ⟨Eb ^ e * E', (unitarySU 2 n K d).mul_mem ((unitarySU 2 n K d).pow_mem hEbSU e)
            hE'SU, ?_, ?_⟩
          · have hcy' : Eb ^ e * y' = y' * Eb ^ e := by
              have : ∀ k : ℕ, Eb ^ k * y' = y' * Eb ^ k := by
                intro k
                induction k with
                | zero => group
                | succ k ihk =>
                  rw [pow_succ, mul_assoc, hEbDC y' hy'DC, ← mul_assoc, ihk, mul_assoc]
              exact this e
            calc Eb ^ e * E' * x₂ * (Eb ^ e * E')⁻¹ = Eb ^ e * (E' * x₂ * E'⁻¹) * (Eb ^ e)⁻¹ := by
                  group
              _ = Eb ^ e * y' * x₂ * (Eb ^ e)⁻¹ := by rw [hE'x]; group
              _ = y' * (Eb ^ e * x₂ * (Eb ^ e)⁻¹) := by rw [hcy']; group
              _ = y' * (δb ^ e * x₂) := by rw [hEbpow e]
              _ = y * x₂ := by
                rw [hy', ← mul_assoc, mul_assoc y, ← pow_add, Nat.sub_add_cancel he.le,
                  show δb ^ p = 1 by
                    rw [hδbpow p, hζ.pow_eq_one, UnitaryThreeP.blockScalar, map_one, map_one,
                      mul_one, mul_inv_cancel], mul_one]
          · intro z hz
            have hcz : Eb ^ e * z = z * Eb ^ e := by
              have : ∀ k : ℕ, Eb ^ k * z = z * Eb ^ k := by
                intro k
                induction k with
                | zero => group
                | succ k ihk =>
                  rw [pow_succ, mul_assoc, hEbDC z hz, ← mul_assoc, ihk, mul_assoc]
              exact this e
            rw [mul_assoc, hE'c z hz, ← mul_assoc, hcz, mul_assoc]
      exact QuotMove.false_of_shears hc hp hp2 hψ hker hperf hA hAI' h3 (x₀ := M₂) hM₂A
        (by rw [hM₂c']; exact hx₂p) hl₂'
        (fun y hy hyp => by
          obtain ⟨E, hESU, hEx, hEc⟩ := hshearDC _ y (hDCG y (hGN y hy) hyp) le_rfl
          exact ⟨⟨E, hESU⟩, by rw [hM₂c']; exact hEx,
            fun z hz hzp => hEc z (hDCG z (hGN z hz) hzp)⟩)
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
    have hdiag : ∀ i, α i (hh i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    by_cases hp5 : ¬ 5 ≤ p
    ·
      have hp3 : p = 3 := by
        have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by norm_num)
        have := hp.two_le
        omega
      subst hp3
      have hd3 : 3 ∣ d := hpd.resolve_left hp5
      obtain ⟨u', M', hM', hy₀eq⟩ := hGU _ hg'G
      have hgGU := TableBUD.mem_guSet_of_mem_primeFormUnitary h hgU
      have hxy : (x₀ : GL (Fin d) K) * M' = GeneralLinearGroup.scalar (Fin d) u * (M' * x₀) := by
        have e : (x₀ : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) u' * M') =
            GeneralLinearGroup.scalar (Fin d) u *
              (GeneralLinearGroup.scalar (Fin d) u' * M' * x₀) := by
          rw [← hy₀eq]
          exact hcomm
        have c1 := (TypeA.PGLTor.commute_scalar u' (x₀ : GL (Fin d) K)).eq
        have c2 := (TypeA.PGLTor.commute_scalar u' (GeneralLinearGroup.scalar (Fin d) u)).eq
        apply mul_left_cancel (a := GeneralLinearGroup.scalar (Fin d) u')
        calc GeneralLinearGroup.scalar (Fin d) u' * ((x₀ : GL (Fin d) K) * M')
            = (x₀ : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) u' * M') := by
              rw [← mul_assoc, c1, mul_assoc]
          _ = GeneralLinearGroup.scalar (Fin d) u *
              (GeneralLinearGroup.scalar (Fin d) u' * M' * x₀) := e
          _ = GeneralLinearGroup.scalar (Fin d) u' *
              (GeneralLinearGroup.scalar (Fin d) u * (M' * x₀)) := by
              rw [mul_assoc (GeneralLinearGroup.scalar (Fin d) u') M', ← mul_assoc, ← c2,
                mul_assoc]
      have hyA : TableB.projConj (unitarySU 2 n K d) ⟨M', TableBUE.gu_subset_normalizer h hM'⟩ ∈
          TypeA.inducedSub ψ A := by
        have e : (⟨M', TableBUE.gu_subset_normalizer h hM'⟩ :
            Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) =
            ⟨GeneralLinearGroup.scalar (Fin d) u'⁻¹, hc.scalar_mem u'⁻¹⟩ * y₀ := by
          apply Subtype.ext
          change M' = GeneralLinearGroup.scalar (Fin d) u'⁻¹ * (y₀ : GL (Fin d) K)
          rw [show (y₀ : GL (Fin d) K) = _ from hy₀eq, ← mul_assoc, ← map_mul, inv_mul_cancel,
            map_one, one_mul]
        rw [e, map_mul, hc.map_scalar, one_mul]
        exact hy₀A
      exact UnitaryPhase.false_of_unitary_noncomm_three h hK hpq hd3 (by omega) hdq hψ hker hperf
        hA hAI' hgGU hM' hx₀A hyA hgU hgp hu1 hup hxy ι φ hh α hdiag hlin hgen
    push Not at hp5
    obtain ⟨D, hDSU, hDact⟩ :=
      UnitaryPhase.exists_unitary_quadPhase h hp hp5 hpq hζ hgU hgp hu1 hup hcomm
    obtain ⟨k, -, hk⟩ := QuotMove.exists_pow_eq_units hζ hup
    have hk0 : ¬ p ∣ k := by
      rintro ⟨j, rfl⟩
      apply hu1
      rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
    obtain ⟨cE, hcE⟩ := hDact _ k (by rw [hk]; exact hcomm)
    exact QuotMove.false_of_normalizing_move hc hp hpK hp2 hψ hker hperf hA hAI' (x₀ := x₀)
      (y₀ := y₀) hx₀A hy₀A hcomm hu1 ⟨D, hDSU⟩
      (QuotMove.conj_mem_inducedSub_of_phase hc hp hζ hψ hA hAI' hx₀A hgp
        (Subgroup.inclusion hc.le ⟨D, hDSU⟩) hDact)
      hk0 hcE ι φ hh α hdiag hlin hgen

theorem largeEvenLabelAll_wnorm_unitary_w5 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hW : GGTBWNormW5UnitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨ht, hp5, -, h5p, hpq⟩ := hW
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht h5p hpq ⊢
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
  exact ggTorusWNormSC_unitary_of_odd hK hn hp (by omega) (Or.inl hp5) hpq
    (by show 5 ≤ r + 1; omega) (fun he => by
      have := congrArg Prod.fst he
      simp only at this
      omega)

theorem largeEvenLabelAll_wnorm_unitary_w3 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hW : GGTBWNormW3UnitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨ht, rfl, h3d, h12, hpq⟩ := hW
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht h3d h12 hpq ⊢
  subst tag
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · have h2 : 3 ∣ 2 := by simpa using hpq
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact h0
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_unitary_of_odd hK hn hp (by norm_num) (Or.inr h3d) hpq
    (by show 5 ≤ r + 1; omega) (fun he => by
      have := congrArg Prod.fst he
      simp only at this
      omega)

end CFSG.StandardType
