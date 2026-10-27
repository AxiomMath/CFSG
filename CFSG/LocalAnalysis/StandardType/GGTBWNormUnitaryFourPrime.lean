module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryThreePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTwoShears

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace UnitaryFourP

variable {K : Type} [Field K] {d : ℕ}

theorem coe_blockScalar_eq_diagonal (S : Finset (Fin d)) (ζ : Kˣ) :
    ((UnitaryThreeP.blockScalar S ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun j => if j ∈ S then (ζ : K) else 1) := by
  rw [UnitaryThreeP.coe_blockScalar]
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hij : i = j
  all_goals simp_all [TableBUE.blockExt, diagonal_apply, Matrix.one_apply]

end UnitaryFourP


theorem ggTorusWNormSC_unitary_four_prime {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (hdp : d = 4 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hp2 : p ≠ 2 := by omega
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
      have hbound : Nat.card A ≤ p ^ 4 := by
        rcases TypeA.PGLTor.toral_or_card_le_of_central_sharp hp hp2 hpK hGp hcent with
          htor | hb
        · exfalso
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
        ·
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
          have h1 : Nat.card (Ab × Kˣ) ≤ Nat.card G := Nat.card_le_card_of_injective F hF
          rw [Nat.card_prod, Nat.card_units] at h1
          have e3 : Fintype.card (Fin d) / p = 4 := by
            rw [Fintype.card_fin, hdp, Nat.mul_div_cancel 4 hp.pos]
          rw [e3] at hb
          have hK1 : 0 < Nat.card K - 1 := by
            have := Finite.one_lt_card (α := K)
            omega
          calc Nat.card A = Nat.card Ab := hcardAb.symm
            _ ≤ p ^ 4 := Nat.le_of_mul_le_mul_right (h1.trans hb) hK1
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
      set cls : Fin d → Finset (Fin d) := fun b =>
        Finset.univ.filter fun j => ∀ z ∈ G, z ^ p = 1 → wt j z = wt b z with hcls
      have hmemC : ∀ b j, j ∈ cls b ↔ ∀ z ∈ G, z ^ p = 1 → wt j z = wt b z := fun b j => by
        rw [hcls, Finset.mem_filter]
        simp
      have hbC : ∀ b, b ∈ cls b := fun b => (hmemC b b).mpr fun _ _ _ => rfl
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
      have hx₂N : x₂ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
        hM₂c' ▸ M₂.2
      have hshearC : ∀ b, ∃ (E : unitarySU 2 n K d) (δ : unitarySU 2 n K d),
          (δ : GL (Fin d) K) = (P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls b) ζ *
            (P : GL (Fin d) K)⁻¹ ∧
          (E : GL (Fin d) K) * x₂ * (E : GL (Fin d) K)⁻¹ = δ * x₂ ∧
          (δ : GL (Fin d) K) ^ p = 1 ∧
          TableB.projConj (unitarySU 2 n K d) ⟨δ, Subgroup.le_normalizer δ.2⟩ ∈ Ab ∧
          ∀ y : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
            TableB.projConj (unitarySU 2 n K d) y ∈ TypeA.inducedSub ψ A →
              (y : GL (Fin d) K) ^ p = 1 → (E : GL (Fin d) K) * y = y * E := by
        intro b
        obtain ⟨E, hESU, hEx, hEcomm⟩ := UnitaryThreeP.exists_block_conj h hp hp2 hpq hζ P.2
          hx₂U hx₂b hx₂p hl₂' (hblockC b x₂ hx₂G)
        set δ : GL (Fin d) K := (P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls b) ζ *
          (P : GL (Fin d) K)⁻¹ with hδ
        have hδx : δ = E * x₂ * E⁻¹ * x₂⁻¹ := by rw [hEx, mul_inv_cancel_right]
        have hδSU : δ ∈ unitarySU 2 n K d := by
          have e : δ = E * (x₂ * E⁻¹ * x₂⁻¹) := by rw [hδx]; group
          rw [e]
          exact (unitarySU 2 n K d).mul_mem hESU
            ((Subgroup.mem_normalizer_iff.mp hx₂N (E⁻¹)).mp ((unitarySU 2 n K d).inv_mem hESU))
        have hδp : δ ^ p = 1 := by
          rw [hδ, conj_pow, UnitaryThreeP.blockScalar_pow, hζ.pow_eq_one,
            UnitaryThreeP.blockScalar, map_one, map_one, mul_one, mul_inv_cancel]
        have hδG : ∀ g ∈ G, g * δ = δ * g := by
          intro g hg
          have h1 : ((P : GL (Fin d) K)⁻¹ * g * P) * UnitaryThreeP.blockScalar (cls b) ζ =
              UnitaryThreeP.blockScalar (cls b) ζ * ((P : GL (Fin d) K)⁻¹ * g * P) := by
            apply Units.ext
            change (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
                ((UnitaryThreeP.blockScalar (cls b) ζ : GL (Fin d) K) :
                  Matrix (Fin d) (Fin d) K) =
              ((UnitaryThreeP.blockScalar (cls b) ζ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
                (((P : GL (Fin d) K)⁻¹ * g * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            rw [UnitaryThreeP.coe_blockScalar]
            exact (UnitaryThreeP.blockExt_smul_one_comm (hblockC b g hg) _).symm
          calc g * δ = (P : GL (Fin d) K) * (((P : GL (Fin d) K)⁻¹ * g * P) *
                UnitaryThreeP.blockScalar (cls b) ζ) * (P : GL (Fin d) K)⁻¹ := by
                rw [hδ]; group
            _ = δ * g := by rw [h1, hδ]; group
        have hδA : TableB.projConj (unitarySU 2 n K d)
            ⟨δ, Subgroup.le_normalizer hδSU⟩ ∈ Ab :=
          UnitaryThreeP.projConj_mem_inducedSub_of_commute hcov hψ hker hperf hAI' hsc
            ⟨δ, hδSU⟩ (Subtype.ext (by rw [Subgroup.coe_pow, hδp]; rfl))
            (fun M' hM' => hδG _ (hGN M' hM'))
        refine ⟨⟨E, hESU⟩, ⟨δ, hδSU⟩, rfl, hEx, hδp, hδA, ?_⟩
        intro y hy hyp
        have hyG := hGN y hy
        refine hEcomm y (hblockC b y hyG) ⟨wt b y, ?_⟩
        rw [hdiagw y hyG hyp]
        exact UnitaryThreeP.blockRes_diagonal_of_const fun j hj => (hmemC b j).mp hj _ hyG hyp
      obtain ⟨E₁, δ₁, hδ₁, hE₁x, hδ₁p, hδ₁A, hE₁c⟩ := hshearC i₀
      obtain ⟨E₂, δ₂, hδ₂, hE₂x, hδ₂p, hδ₂A, hE₂c⟩ := hshearC j₀
      have hi₀j : i₀ ∉ cls j₀ := fun hm => hj₀ ((hmemC j₀ i₀).mp hm _ hy₀G hy₀p).symm
      have hj₀i : j₀ ∉ cls i₀ := fun hm => hj₀ ((hmemC i₀ j₀).mp hm _ hy₀G hy₀p)
      have hδpow : ∀ (b : Fin d) (δ : unitarySU 2 n K d), (δ : GL (Fin d) K) =
          (P : GL (Fin d) K) * UnitaryThreeP.blockScalar (cls b) ζ * (P : GL (Fin d) K)⁻¹ →
          ∀ i : ℕ, (P : GL (Fin d) K)⁻¹ * (δ : GL (Fin d) K) ^ i * P =
            UnitaryThreeP.blockScalar (cls b) (ζ ^ i) := by
        intro b δ hδ i
        rw [hδ, conj_pow, UnitaryThreeP.blockScalar_pow]
        group
      by_cases h3cls : ∃ m₀, m₀ ∉ cls i₀ ∧ m₀ ∉ cls j₀
      ·
        obtain ⟨m₀, hm₁, hm₂⟩ := h3cls
        have hind : ∀ i k : ℕ, TableB.projConj (unitarySU 2 n K d)
            ⟨δ₁, Subgroup.le_normalizer δ₁.2⟩ ^ i * TableB.projConj (unitarySU 2 n K d)
              ⟨δ₂, Subgroup.le_normalizer δ₂.2⟩ ^ k = 1 → p ∣ i ∧ p ∣ k := by
          intro i k hik
          rw [← map_pow, ← map_pow, ← map_mul] at hik
          obtain ⟨u, hu⟩ := hc.ker _ hik
          have hu' : (δ₁ : GL (Fin d) K) ^ i * (δ₂ : GL (Fin d) K) ^ k =
              GeneralLinearGroup.scalar (Fin d) u := hu
          have hP : UnitaryThreeP.blockScalar (cls i₀) (ζ ^ i) *
              UnitaryThreeP.blockScalar (cls j₀) (ζ ^ k) = GeneralLinearGroup.scalar (Fin d) u := by
            rw [← hδpow i₀ δ₁ hδ₁ i, ← hδpow j₀ δ₂ hδ₂ k]
            calc (P : GL (Fin d) K)⁻¹ * (δ₁ : GL (Fin d) K) ^ i * P *
                  ((P : GL (Fin d) K)⁻¹ * (δ₂ : GL (Fin d) K) ^ k * P)
                = (P : GL (Fin d) K)⁻¹ * ((δ₁ : GL (Fin d) K) ^ i * (δ₂ : GL (Fin d) K) ^ k) *
                    P := by group
              _ = GeneralLinearGroup.scalar (Fin d) u := by
                rw [hu', ← (TypeA.PGLTor.commute_scalar u (P : GL (Fin d) K)⁻¹).eq,
                  inv_mul_cancel_right]
          have hent : ∀ m, (if m ∈ cls i₀ then ((ζ ^ i : Kˣ) : K) else 1) *
              (if m ∈ cls j₀ then ((ζ ^ k : Kˣ) : K) else 1) = (u : K) := by
            intro m
            have e := congrArg (fun Z : GL (Fin d) K => (Z : Matrix (Fin d) (Fin d) K) m m) hP
            simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
              diagonal_apply_eq, UnitaryFourP.coe_blockScalar_eq_diagonal,
              diagonal_mul_diagonal] at e
            exact e
          have h0 := hent m₀
          have h1 := hent i₀
          have h2 := hent j₀
          rw [if_neg hm₁, if_neg hm₂, one_mul] at h0
          rw [if_pos (hbC i₀), if_neg hi₀j, mul_one, ← h0] at h1
          rw [if_neg hj₀i, if_pos (hbC j₀), one_mul, ← h0] at h2
          exact ⟨(hζ.pow_eq_one_iff_dvd i).mp (Units.ext h1),
            (hζ.pow_eq_one_iff_dvd k).mp (Units.ext h2)⟩
        exact QuotMove.false_of_two_shears hc hp hp5 hψ hker hperf hA hAI' hbound (x₀ := M₂)
          hM₂A (by rw [hM₂c']; exact hx₂p) hl₂' E₁ E₂ ⟨δ₁, Subgroup.le_normalizer δ₁.2⟩
          ⟨δ₂, Subgroup.le_normalizer δ₂.2⟩ hδ₁A hδ₂A hδ₁p hδ₂p hind
          (by rw [hM₂c']; exact hE₁x) (by rw [hM₂c']; exact hE₂x) hE₁c hE₂c
          hM hC ι φ hh α hpair hlin hgen
      ·
        push Not at h3cls
        have hall : ∀ y : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
            TableB.projConj (unitarySU 2 n K d) y ∈ TypeA.inducedSub ψ A →
              (y : GL (Fin d) K) ^ p = 1 → ∃ (u : Kˣ) (e : ℕ), (y : GL (Fin d) K) =
                GeneralLinearGroup.scalar (Fin d) u *
                  ((⟨δ₁, Subgroup.le_normalizer δ₁.2⟩ : Subgroup.normalizer
                    (unitarySU 2 n K d : Set (GL (Fin d) K))) : GL (Fin d) K) ^ e := by
          intro y hy hyp
          have hyG := hGN y hy
          have hD := hdiagw _ hyG hyp
          have ha0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hD i₀
          have hb0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hD j₀
          set aU : Kˣ := Units.mk0 _ ha0 with haU
          set bU : Kˣ := Units.mk0 _ hb0 with hbU
          have hpowd : ∀ j, wt j (y : GL (Fin d) K) ^ p = 1 := by
            intro j
            have e1 : (((P : GL (Fin d) K)⁻¹ * y * P) ^ p : GL (Fin d) K) = 1 := by
              rw [show (P : GL (Fin d) K)⁻¹ * y * P =
                  (P : GL (Fin d) K)⁻¹ * y * ((P : GL (Fin d) K)⁻¹)⁻¹ by rw [inv_inv],
                conj_pow, hyp, mul_one, mul_inv_cancel]
            have e2 := congrArg (fun Z : GL (Fin d) K => (Z : Matrix (Fin d) (Fin d) K) j j) e1
            simp only [Units.val_pow_eq_pow_val, Units.val_one] at e2
            rw [hD, diagonal_pow, diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq] at e2
            exact e2
          have hab : (aU * bU⁻¹) ^ p = 1 := by
            apply Units.ext
            rw [mul_pow, inv_pow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
              Units.val_pow_eq_pow_val, haU, hbU, Units.val_mk0, Units.val_mk0, hpowd, hpowd,
              inv_one, mul_one, Units.val_one]
          obtain ⟨e, -, he⟩ := QuotMove.exists_pow_eq_units hζ hab
          refine ⟨bU, e, ?_⟩
          have hentries : ∀ j, wt j (y : GL (Fin d) K) =
              (bU : K) * (if j ∈ cls i₀ then ((ζ ^ e : Kˣ) : K) else 1) := by
            intro j
            by_cases hj : j ∈ cls i₀
            · rw [if_pos hj, (hmemC i₀ j).mp hj _ hyG hyp, he, Units.val_mul,
                Units.val_inv_eq_inv_val, haU, hbU, Units.val_mk0, Units.val_mk0,
                mul_comm (wt i₀ (y : GL (Fin d) K)), ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
            · have hj2 : j ∈ cls j₀ := h3cls j hj
              rw [if_neg hj, mul_one, (hmemC j₀ j).mp hj2 _ hyG hyp, hbU, Units.val_mk0]
          have hconj : (P : GL (Fin d) K)⁻¹ * y * P = (P : GL (Fin d) K)⁻¹ *
              (GeneralLinearGroup.scalar (Fin d) bU * (δ₁ : GL (Fin d) K) ^ e) * P := by
            have hR : (P : GL (Fin d) K)⁻¹ * (GeneralLinearGroup.scalar (Fin d) bU *
                (δ₁ : GL (Fin d) K) ^ e) * P = GeneralLinearGroup.scalar (Fin d) bU *
                  UnitaryThreeP.blockScalar (cls i₀) (ζ ^ e) := by
              rw [← hδpow i₀ δ₁ hδ₁ e]
              calc (P : GL (Fin d) K)⁻¹ * (GeneralLinearGroup.scalar (Fin d) bU *
                    (δ₁ : GL (Fin d) K) ^ e) * P
                  = ((P : GL (Fin d) K)⁻¹ * GeneralLinearGroup.scalar (Fin d) bU) *
                      (δ₁ : GL (Fin d) K) ^ e * P := by group
                _ = GeneralLinearGroup.scalar (Fin d) bU * ((P : GL (Fin d) K)⁻¹ *
                      (δ₁ : GL (Fin d) K) ^ e * P) := by
                    rw [← (TypeA.PGLTor.commute_scalar bU (P : GL (Fin d) K)⁻¹).eq]; group
            rw [hR]
            apply Units.ext
            rw [hD, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
              UnitaryFourP.coe_blockScalar_eq_diagonal, diagonal_mul_diagonal]
            exact congrArg diagonal (funext hentries)
          have h1 := mul_left_cancel (mul_right_cancel hconj)
          rw [h1]
        have hle := QuotMove.card_le_sq_of_forall_eq_scalar_mul_pow hc hp hp2 hψ hker hperf hA
          hAI' (x₀ := M₂) hM₂A (by rw [hM₂c']; exact hx₂p) hl₂' hδ₁A hall
        have h32 : p ^ 3 ≤ p ^ 2 := h3.trans hle
        have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h32
        omega
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


theorem largeEvenLabelAll_wnorm_unitary_four_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : lab.tag = .twA)
    (hdp : lab.rank + 1 = 4 * p) (hpq : p ∣ 2 ^ lab.n + 1) :
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
  exact ggTorusWNormSC_unitary_four_prime hK hn hp hp5 hpq hdp


end CFSG.StandardType
