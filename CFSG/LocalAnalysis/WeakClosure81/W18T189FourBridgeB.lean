module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridgeA
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineShape
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatLeaf
open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (CoverOf)
open scoped MatrixGroups commutatorElement

theorem pglb_exists_isIrr {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (ρ : Q →* MulAut V) (hρ : Function.Injective ρ) {L : Subgroup Q} (hperf : ⁅L, L⁆ = L)
    (hL : L ≠ ⊥) : ∃ I : Subgroup V, IsIrr ρ L I := by
  classical
  let S : Subgroup V → Prop := fun J =>
    (∀ l ∈ L, ∀ j ∈ J, ρ l j ∈ J) ∧ ∃ l ∈ L, ∃ j ∈ J, ρ l j ≠ j
  have hV : S ⊤ := by
    refine ⟨fun l _ j _ => Subgroup.mem_top _, ?_⟩
    obtain ⟨l, hl⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL
    have hρl : ρ (l : Q) ≠ 1 := by
      intro h
      exact hl (Subtype.ext (hρ (h.trans (map_one ρ).symm)))
    obtain ⟨v, hv⟩ : ∃ v, ρ (l : Q) v ≠ v := by
      by_contra h
      push Not at h
      exact hρl (MulEquiv.ext fun v => h v)
    exact ⟨(l : Q), l.2, v, Subgroup.mem_top v, hv⟩
  have hP : ∃ n, ∃ J : Subgroup V, S J ∧ Nat.card J = n := ⟨_, ⊤, hV, rfl⟩
  obtain ⟨I, hSI, hIcard⟩ := Nat.find_spec hP
  have hImin : ∀ J : Subgroup V, S J → Nat.card J < Nat.card I → False := by
    intro J hSJ hlt
    exact Nat.find_min hP (by rw [hIcard] at hlt; exact hlt) ⟨J, hSJ, rfl⟩
  obtain ⟨hIinv, hInontriv⟩ := hSI
  have hIbot : I ≠ ⊥ := by
    intro hbot
    obtain ⟨l, _hl, j, hj, hjne⟩ := hInontriv
    rw [hbot, Subgroup.mem_bot] at hj
    exact hjne (by rw [hj, map_one])
  set gen : Set V := {x : V | ∃ i ∈ I, ∃ l ∈ L, x = ρ l i * i⁻¹} with hgen_def
  set I' : Subgroup V := Subgroup.closure gen with hI'def
  have hI'le : I' ≤ I := by
    rw [hI'def, Subgroup.closure_le]
    rintro x ⟨i, hi, l, hl, rfl⟩
    exact I.mul_mem (hIinv l hl i hi) (I.inv_mem hi)
  have hI'inv : ∀ l ∈ L, ∀ j ∈ I', ρ l j ∈ I' := by
    intro l' hl' j hj
    have hsub : I' ≤ Subgroup.comap (ρ l') I' := by
      rw [hI'def, Subgroup.closure_le]
      rintro x ⟨i, hi, l, hl, rfl⟩
      change ρ l' (ρ l i * i⁻¹) ∈ I'
      have hcomp : ρ (l' * l) i = ρ l' (ρ l i) := by rw [map_mul]; rfl
      have heq : ρ l' (ρ l i * i⁻¹) =
          (ρ (l' * l) i * i⁻¹) * (ρ l' i * i⁻¹)⁻¹ := by
        rw [hcomp, map_mul, map_inv]
        group
      rw [heq]
      exact I'.mul_mem
        (Subgroup.subset_closure ⟨i, hi, l' * l, L.mul_mem hl' hl, rfl⟩)
        (I'.inv_mem (Subgroup.subset_closure ⟨i, hi, l', hl', rfl⟩))
    exact hsub hj
  have hI'nontriv : ∃ l ∈ L, ∃ j ∈ I', ρ l j ≠ j := by
    by_contra hcon
    push Not at hcon
    have hfixI : ∀ i ∈ I, ∀ l ∈ L, ρ l i = i := by
      intro i hi l hl
      let φ : ↥L →* I' :=
        { toFun := fun a => ⟨ρ (a : Q) i * i⁻¹,
            Subgroup.subset_closure ⟨i, hi, (a : Q), a.2, rfl⟩⟩
          map_one' := by
            apply Subtype.ext
            show ρ ((1 : ↥L) : Q) i * i⁻¹ = 1
            simp
          map_mul' := fun a b => by
            apply Subtype.ext
            show ρ ((a * b : ↥L) : Q) i * i⁻¹ =
              (ρ (a : Q) i * i⁻¹) * (ρ (b : Q) i * i⁻¹)
            have hb : ρ (a : Q) (ρ (b : Q) i * i⁻¹) = ρ (b : Q) i * i⁻¹ :=
              hcon (a : Q) a.2 _ (Subgroup.subset_closure ⟨i, hi, (b : Q), b.2, rfl⟩)
            have hb' : ρ (a : Q) (ρ (b : Q) i) * (ρ (a : Q) i)⁻¹ = ρ (b : Q) i * i⁻¹ := by
              simpa only [map_mul, map_inv] using hb
            have h2 : ρ (a : Q) (ρ (b : Q) i) = (ρ (b : Q) i * i⁻¹) * ρ (a : Q) i :=
              calc ρ (a : Q) (ρ (b : Q) i)
                  = (ρ (a : Q) (ρ (b : Q) i) * (ρ (a : Q) i)⁻¹) * ρ (a : Q) i := by group
                _ = (ρ (b : Q) i * i⁻¹) * ρ (a : Q) i := by rw [hb']
            rw [show ((a * b : ↥L) : Q) = (a : Q) * (b : Q) from rfl, map_mul]
            change ρ (a : Q) (ρ (b : Q) i) * i⁻¹ =
              (ρ (a : Q) i * i⁻¹) * (ρ (b : Q) i * i⁻¹)
            rw [h2]
            ac_rfl }
      have hperfL : commutator ↥L = ⊤ := by
        have h1 : (commutator ↥L).map L.subtype = L := by
          have h := Subgroup.map_commutator L.subtype (H₁ := ⊤) (H₂ := ⊤)
          rw [Subgroup.map_top, Subgroup.range_subtype, hperf] at h
          exact h
        have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
        exact Subgroup.map_injective L.subtype_injective (h1.trans h2.symm)
      have hle : commutator ↥L ≤ φ.ker := by
        change ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ φ.ker
        rw [Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
      have hker : φ.ker = ⊤ := by
        rw [hperfL] at hle
        exact top_le_iff.mp hle
      have hmem : (⟨l, hl⟩ : ↥L) ∈ φ.ker := by rw [hker]; trivial
      have h1 : φ ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.mp hmem
      have hval : ρ l i * i⁻¹ = 1 := by
        have := congrArg Subtype.val h1
        simpa [φ] using this
      exact mul_inv_eq_one.mp hval
    obtain ⟨l, hl, i, hi, hine⟩ := hInontriv
    exact hine (hfixI i hi l hl)
  have hI'eq : I' = I := by
    have hcard : Nat.card I' = Nat.card I := by
      by_contra hne
      have hlt : Nat.card I' < Nat.card I := by
        have hle := Subgroup.card_le_of_le hI'le
        omega
      exact hImin I' ⟨hI'inv, hI'nontriv⟩ hlt
    exact Subgroup.eq_of_le_of_card_ge hI'le (by omega)
  refine ⟨I, hIbot, ?_, ?_⟩
  · exact hI'eq.symm.trans hI'def
  · intro J hJI hJinv hCJ
    by_cases hJnontriv : ∃ l ∈ L, ∃ j ∈ J, ρ l j ≠ j
    · right
      have hcard : Nat.card J = Nat.card I := by
        by_contra hne
        have hlt : Nat.card J < Nat.card I := by
          have hle := Subgroup.card_le_of_le hJI
          omega
        exact hImin J ⟨hJinv, hJnontriv⟩ hlt
      exact Subgroup.eq_of_le_of_card_ge hJI (by omega)
    · left
      apply le_antisymm _ hCJ
      intro j hj
      refine ⟨hJI hj, fun l hl => ?_⟩
      by_contra hjne
      exact hJnontriv ⟨l, hl, j, hj, hjne⟩

theorem pglb_exists_subgroup_card_four {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (h2 : IsPGroup 2 ↥A) (h4 : 4 ≤ Nat.card ↥A) : ∃ B ≤ A, Nat.card ↥B = 4 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by have := not_le.1 h; omega
    interval_cases n <;> omega
  have hdvd : 2 ^ 2 ∣ Nat.card ↥A := by
    rw [hn]; exact pow_dvd_pow 2 hn2
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 (n := 2) hdvd
  have hB'4 : Nat.card ↥B' = 4 := by simpa using hB'
  refine ⟨B'.map A.subtype, Subgroup.map_subtype_le B', ?_⟩
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective B' A.subtype A.subtype_injective).toEquiv,
    hB'4]

theorem pglb_isPGL2_of_hyp66Shape (hO : LieOrderFormulasInput)
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} (hL : F6.IsL2 7 1 ↥L)
    (hs : Hyp66Shape Q L) : F6.IsPGL2 7 Q := by
  have hcardL : Nat.card ↥L = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hL
  rcases hs with ⟨p, e, hp, hp2, h9, hL'⟩ | ⟨p, e, Y, hY, hp, hp2, h3, hlie, hcov⟩ | h3
  · have hmodel : CFSG.Blueprint.LieModel ↥L .PSL 2 p e :=
      Or.inl ⟨by decide, hL'⟩
    have hord := (hO ↥L .PSL 2 p e hL'.1 hmodel).2.1
    have hlt : lieOrderNumerator .PSL 2 (p ^ e) ≤ 336 := by
      have hd : lieOrderDivisor .PSL 2 (p ^ e) ≤ 2 := by
        rw [pglb_lieOrderDivisor_psl_two]; exact Nat.gcd_le_left _ (by norm_num)
      rw [hcardL] at hord
      omega
    have hge : 990 ≤ lieOrderNumerator .PSL 2 (p ^ e) := by
      rw [pglb_lieOrderNumerator_psl_two]
      have hq10 : 10 ≤ p ^ e := by omega
      have hq2 : 100 ≤ (p ^ e) ^ 2 := by
        have := Nat.pow_le_pow_left hq10 2
        simpa using this
      have hsub : 99 ≤ (p ^ e) ^ 2 - 1 := by omega
      calc 990 = 10 * 99 := by norm_num
        _ ≤ (p ^ e) * ((p ^ e) ^ 2 - 1) := Nat.mul_le_mul hq10 hsub
    omega
  · obtain ⟨eY⟩ := hcov.2
    have hcardY : Nat.card Y ≤ 168 := by
      rw [← Nat.card_congr eY.toEquiv]
      have h := Subgroup.card_mul_index (Subgroup.center ↥L)
      rw [hcardL] at h
      change Nat.card (↥L ⧸ Subgroup.center ↥L) ≤ 168
      rw [show Nat.card (↥L ⧸ Subgroup.center ↥L) = (Subgroup.center ↥L).index from rfl]
      have hdvd : (Subgroup.center ↥L).index ∣ 168 :=
        ⟨Nat.card ↥(Subgroup.center ↥L), h.symm.trans (mul_comm _ _)⟩
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hq5 : 5 ≤ p ^ e := by
      obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := e)
      omega
    rcases hlie with ⟨-, hmodel⟩ | hmodel
    · have hord := (hO Y .PSL 3 p e hmodel.admissible hmodel).2.1
      have hbound : lieOrderNumerator .PSL 3 (p ^ e) ≤ 504 := by
        have hd : lieOrderDivisor .PSL 3 (p ^ e) ≤ 3 := by
          rw [pglb_lieOrderDivisor_psl_three]; exact Nat.gcd_le_left _ (by norm_num)
        calc lieOrderNumerator .PSL 3 (p ^ e) =
              Nat.card Y * lieOrderDivisor .PSL 3 (p ^ e) := hord.symm
          _ ≤ 168 * 3 := Nat.mul_le_mul hcardY hd
      have hge : 372000 ≤ lieOrderNumerator .PSL 3 (p ^ e) := by
        rw [pglb_lieOrderNumerator_psl_three]
        have h1 : 125 ≤ (p ^ e) ^ 3 := by
          have := Nat.pow_le_pow_left hq5 3
          simpa using this
        have h2 : 24 ≤ (p ^ e) ^ 2 - 1 := by
          have := Nat.pow_le_pow_left hq5 2
          simp only [Nat.reducePow] at this
          omega
        have h3 : 124 ≤ (p ^ e) ^ 3 - 1 := by omega
        calc 372000 = 125 * 24 * 124 := by norm_num
          _ ≤ (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      omega
    · have hord := (hO Y .PSU 3 p e hmodel.admissible hmodel).2.1
      have hbound : lieOrderNumerator .PSU 3 (p ^ e) ≤ 504 := by
        have hd : lieOrderDivisor .PSU 3 (p ^ e) ≤ 3 := by
          rw [pglb_lieOrderDivisor_psu_three]; exact Nat.gcd_le_left _ (by norm_num)
        calc lieOrderNumerator .PSU 3 (p ^ e) =
              Nat.card Y * lieOrderDivisor .PSU 3 (p ^ e) := hord.symm
          _ ≤ 168 * 3 := Nat.mul_le_mul hcardY hd
      have hge : 378000 ≤ lieOrderNumerator .PSU 3 (p ^ e) := by
        rw [pglb_lieOrderNumerator_psu_three]
        have h1 : 125 ≤ (p ^ e) ^ 3 := by
          have := Nat.pow_le_pow_left hq5 3
          simpa using this
        have h2 : 24 ≤ (p ^ e) ^ 2 - 1 := by
          have := Nat.pow_le_pow_left hq5 2
          simp only [Nat.reducePow] at this
          omega
        have h3 : 126 ≤ (p ^ e) ^ 3 + 1 := by
          have := Nat.pow_le_pow_left hq5 3
          simp only [Nat.reducePow] at this
          omega
        calc 378000 = 125 * 24 * 126 := by norm_num
          _ ≤ (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      omega
  · exact h3

theorem pglb_card_isPGL2_seven {Q : Type} [Group Q] (h : F6.IsPGL2 7 Q) : Nat.card Q = 336 := by
  obtain ⟨K, hField, hFinite, hK, ⟨e⟩⟩ := h
  have hcardGL : Nat.card (GL (Fin 2) K) = 2016 := by
    rw [pglb_card_gl_two, hK]; norm_num
  have hcardS : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) = 6 := by
    rw [pglb_card_statedScalars_two, hK]
  have hcardQ :
      Nat.card (GL (Fin 2) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) = 336 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K)
    rw [hcardGL, hcardS] at h
    omega
  rw [Nat.card_congr e.toEquiv, hcardQ]

theorem pglb_isPerfect_of_isL2_seven {Q : Type} [Group Q] {L : Subgroup Q}
    (hL : F6.IsL2 7 1 ↥L) : ⁅L, L⁆ = L := by
  have hcard : Nat.card ↥L = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hL
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hshape : Socle185Shape ↥L := Or.inr (Or.inr hL)
  haveI : IsSimpleGroup ↥L := hshape.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hshape.exists_not_commute
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator ↥L) with hbot | htop
  · exfalso
    have hmem : ⁅a, b⁆ ∈ commutator ↥L :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  · have hmap : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [show commutator ↥L = ⁅(⊤ : Subgroup ↥L), ⊤⁆ from rfl, Subgroup.map_commutator,
        Subgroup.map_top, Subgroup.range_subtype]
    calc ⁅L, L⁆ = (commutator ↥L).map L.subtype := hmap.symm
      _ = (⊤ : Subgroup ↥L).map L.subtype := by rw [htop]
      _ = L := by rw [Subgroup.map_top, Subgroup.range_subtype]

end CFSG.LocalAnalysis.WeakClosure81

end
