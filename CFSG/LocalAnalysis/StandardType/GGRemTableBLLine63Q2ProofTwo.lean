module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepTwoB
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Final
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLayer
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType CFSG.SectionRank.OddCover

variable {K : Type} [Field K]

section Center

variable [Finite K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isPGroup_two_center (hcov : Line63.UnitaryCoverOddAt 1 6 K)
    (hKd : UnitaryFieldData 2 1 K) (hpq : 3 ∣ 2 ^ 1 + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) :
    IsPGroup 2 (Subgroup.center ↥L) := by
  classical
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_redCover hcov hL θ
  intro g
  obtain ⟨s, hs⟩ := hφ2 g.1
  have hψ : ggQuotHom θ g.1 = 1 := by
    have h : g.1 ∈ (ggQuotHom θ).ker := by
      rw [ker_ggQuotHom θ]
      exact g.2
    exact h
  have hs1 : LargeEvenProjMk (unitarySU 2 1 K 6) s = 1 := (hφ3 s g.1 hs).symm.trans hψ
  obtain ⟨c, hc3, hc⟩ := exists_scalar_of_proj_eq_one hKd hpq hs1
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
    rfl
  have h3 : redMkL L (g.1 ^ 3) = 1 := by rw [map_pow, ← hs, ← map_pow, hs3, map_one]
  have hg3 : ((g.1 ^ 3 : ↥L) : G) ∈ twoCenter L := (redMkL_eq_one_iff L _).mp h3
  have hgc : ∀ l ∈ L, ((g.1 : ↥L) : G) * l = l * ((g.1 : ↥L) : G) := fun l hl =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp g.2 ⟨l, hl⟩)).symm
  set a : G := ((g.1 : ↥L) : G) with ha
  set m : ℕ := (2 ^ Nat.card G) ^ 2 with hm
  have h1 : (a ^ 3) ^ (2 ^ Nat.card G) = 1 := by simpa [ha] using hg3.2.2
  have e1 : (a ^ m) ^ 3 = a ^ (3 * 2 ^ Nat.card G * 2 ^ Nat.card G) := by
    rw [← pow_mul]
    congr 1
    rw [hm]
    ring
  have e2 : ((a ^ 3) ^ (2 ^ Nat.card G)) ^ (2 ^ Nat.card G) =
      a ^ (3 * 2 ^ Nat.card G * 2 ^ Nat.card G) := by
    rw [pow_mul, pow_mul]
  have hz' : a ^ m = 1 := hz (a ^ m) (L.pow_mem g.1.2 m) (fun l hl =>
    ((show Commute a l from hgc l hl).pow_left m).eq) (by rw [e1, ← e2, h1, one_pow])
  refine ⟨2 * Nat.card G, Subtype.ext (Subtype.ext ?_)⟩
  have hk : (2 : ℕ) ^ (2 * Nat.card G) = m := by rw [hm, ← pow_mul, mul_comm]
  simpa [hk, ha] using hz'

end Center

section Inner

variable [Finite K] {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

theorem all_inner_two (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5)
    (hKd : UnitaryFieldData 2 1 K) (hpq : 3 ∣ 2 ^ 1 + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) :
    ∀ (b : G) (hb : b ∈ Bs), ∃ (M : GL (Fin 6) K) (hMgu : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      IsInner 1 M ∧ ggLAut L θ ⟨b, hBN hb⟩ = TableB.projConj (unitarySU 2 1 K 6)
        ⟨M, TableBUE.gu_subset_normalizer (d := 6) hKd hMgu⟩ := by
  classical
  intro b hb
  obtain ⟨A, hA, hgraph⟩ := ggLAut_mem_of_induces L θ hBN hBI hb
  have hAN : A ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd hA
  have hac0 : ggLAut L θ ⟨b, hBN hb⟩ = TableB.projConj (unitarySU 2 1 K 6) ⟨A, hAN⟩ := by
    ext r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective r
    exact (hgraph s (conjN A hAN s) rfl).trans (projConj_mk_eq A hAN s).symm
  refine ⟨A, hA, ?_, hac0⟩
  by_contra hMn
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨-, hrank⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨u, hu⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu hKd hA
  have hgn : ¬ IsInner 1 (GeneralLinearGroup.scalar (Fin 6) u * A) :=
    fun h => hMn ((isInner_scalar_mul_iff u A).mp h)
  have hgN : GeneralLinearGroup.scalar (Fin 6) u * A ∈
      Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hu)
  have hac : ggLAut L θ ⟨b, hBN hb⟩ = TableB.projConj (unitarySU 2 1 K 6)
      ⟨GeneralLinearGroup.scalar (Fin 6) u * A, hgN⟩ := by
    rw [hac0]
    have hu' : GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) K := ⟨u, rfl⟩
    have : (⟨GeneralLinearGroup.scalar (Fin 6) u * A, hgN⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))) =
        ⟨GeneralLinearGroup.scalar (Fin 6) u, TableB.scalar_mem_normalizer _ hu'⟩ * ⟨A, hAN⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, TableB.projConj_of_scalar _ hu', one_mul]
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hxC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  have hxL : x ∉ L := fun hxL => hS.2.2.1 (hz x hxL hxC hx3)
  have hxa : x * b = b * x := CFSG.StandardType.TableB.IsElemAbelian.comm hBs hxBs hb
  have h5 := five_le_twoLocalRank_of_outer hKd hpq hL θ hZ2 (hBN hb) (hBs.2 b hb) hu hgn hac hx3
    hS.2.2.1 hxC hxa hxL
  omega

end Inner

section Frame

open CFSG.RankThree.Classical2 CFSG.RankThree.Classical

variable [Finite K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_of_frame_two (hKd : UnitaryFieldData 2 1 K) (hpq : 3 ∣ 2 ^ 1 + 1)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) {Bs : Subgroup G}
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBcard : Nat.card Bs ≤ 3 ^ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {P : GL (Fin 6) K} (hP : P ∈ primeFormUnitary hKd (idGram K 6))
    (hdiag : ∀ (b : G) (hb : b ∈ Bs), ∃ (M : GL (Fin 6) K)
      (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
      ggLAut L θ ⟨b, hBN hb⟩ = TableB.projConj (unitarySU 2 1 K 6) ⟨M, hM⟩ ∧
        ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ∀ g ∈ Bs, g ∈ L := by
  classical
  obtain ⟨T, hTab, hTcard, hTdiag⟩ := exists_torusFive hKd hpq
  set c := TableBUE.conjSU hKd P hP with hc
  set Φ : ↥T →* LargeEvenProj (unitarySU 2 1 K 6) :=
    (LargeEvenProjMk (unitarySU 2 1 K 6)).comp
      ((c.symm : ↥(unitarySU 2 1 K 6) ≃* ↥(unitarySU 2 1 K 6)).toMonoidHom.comp
        T.subtype) with hΦ
  have hΦe : ∀ e : T, Φ e = LargeEvenProjMk (unitarySU 2 1 K 6)
      (c.symm (e : ↥(unitarySU 2 1 K 6))) := fun e => rfl
  have hker : Nat.card Φ.ker ≤ 3 := by
    have hex : ∀ e : Φ.ker, ∃ z : rootsOfUnity 3 K,
        (((e : ↥T) : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) =
          GeneralLinearGroup.scalar (Fin 6) (z : Kˣ) := by
      intro e
      have h1 : LargeEvenProjMk (unitarySU 2 1 K 6)
          (c.symm ((e : ↥T) : ↥(unitarySU 2 1 K 6))) = 1 := by
        rw [← hΦe]
        exact e.2
      obtain ⟨z, hz3, hz⟩ := exists_scalar_of_proj_eq_one hKd hpq h1
      refine ⟨⟨z, (mem_rootsOfUnity _ _).mpr hz3⟩, ?_⟩
      have h2 : ((c.symm ((e : ↥T) : ↥(unitarySU 2 1 K 6)) : ↥(unitarySU 2 1 K 6)) :
          GL (Fin 6) K) = P * (((e : ↥T) : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) * P⁻¹ := rfl
      rw [h2] at hz
      have h3 : (((e : ↥T) : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) =
          P⁻¹ * (GeneralLinearGroup.scalar (Fin 6) z) * P := by
        rw [← hz]
        group
      show (((e : ↥T) : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) =
        GeneralLinearGroup.scalar (Fin 6) z
      rw [h3, ← (TypeA.PGLTor.commute_scalar z P⁻¹).eq]
      group
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro e e' h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hf e, hf e', h]
    exact (Nat.card_le_card_of_injective f hfinj).trans (card_rootsOfUnity K 3)
  have hcard := CFSG.StandardType.TableB.card_range_mul_card_ker Φ
  rw [hTcard] at hcard
  have hrange : 3 ^ 4 ≤ Nat.card Φ.range := by
    have h1 : Nat.card Φ.range * Nat.card Φ.ker ≤ Nat.card Φ.range * 3 :=
      Nat.mul_le_mul_left _ hker
    rw [hcard] at h1
    omega
  set ψ := ggQuotHom θ with hψ
  have hψker : IsPGroup 2 ψ.ker := by rw [ker_ggQuotHom θ]; exact hZ2
  have hΦp : IsPGroup 3 Φ.range :=
    (isPGroup_three_of_isElemAbelian hTab).of_surjective Φ.rangeRestrict
      Φ.rangeRestrict_surjective
  obtain ⟨S, -, hS3, hSmap, hSinj⟩ := exists_sylow_lift ψ hψker hΦp
    (fun y _ => ggQuotHom_surjective θ y) (B := ⊥) IsPGroup.of_bot (by simp)
  have hSΦ : ∀ t ∈ S, ∃ e : ↥T, Φ e = ψ t := by
    intro t ht
    have h : ψ t ∈ Φ.range := by rw [← hSmap]; exact ⟨t, ht, rfl⟩
    obtain ⟨e, he⟩ := h
    exact ⟨e, he⟩
  have hS3' : ∀ t ∈ S, t ^ 3 = 1 := by
    intro t ht
    refine hSinj _ (S.pow_mem ht 3) ?_
    obtain ⟨e, he⟩ := hSΦ t ht
    have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hTab.2 _ e.2)
    rw [map_pow, ← he, ← map_pow, he3, map_one]
  have hcent : ∀ t ∈ S, ∀ (b : G) (hb : b ∈ Bs),
      L.normalizerMonoidHom ⟨b, hBN hb⟩ t = t := by
    intro t ht b hb
    obtain ⟨M, hMN, hac, hMd⟩ := hdiag b hb
    obtain ⟨e, he⟩ := hSΦ t ht
    obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag hMd
    obtain ⟨t', ht'⟩ := hTdiag (e : ↥(unitarySU 2 1 K 6)) e.2
    have hcs : conjN M hMN (c.symm (e : ↥(unitarySU 2 1 K 6))) =
        c.symm (e : ↥(unitarySU 2 1 K 6)) := by
      apply Subtype.ext
      rw [coe_conjN]
      show M * (P * ((e : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) * P⁻¹) * M⁻¹ =
        P * ((e : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) * P⁻¹
      have hM' : M = P * diagHom 6 σ * P⁻¹ := by rw [← hσ]; group
      have hcomm := (diagHom_commute σ t').eq
      rw [ht', hM']
      calc P * diagHom 6 σ * P⁻¹ * (P * diagHom 6 t' * P⁻¹) * (P * diagHom 6 σ * P⁻¹)⁻¹
          = P * (diagHom 6 σ * diagHom 6 t' * (diagHom 6 σ)⁻¹) * P⁻¹ := by group
        _ = P * diagHom 6 t' * P⁻¹ := by rw [hcomm]; group
    have h1 : ψ (L.normalizerMonoidHom ⟨b, hBN hb⟩ t) = ψ t := by
      have hq : ψ (L.normalizerMonoidHom ⟨b, hBN hb⟩ t) = ggLAut L θ ⟨b, hBN hb⟩ (ψ t) := by
        rw [hψ, ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
      rw [hq, hac, ← he, hΦe, projConj_mk_eq M hMN (c.symm (e : ↥(unitarySU 2 1 K 6))), hcs]
    set tb := L.normalizerMonoidHom ⟨b, hBN hb⟩ t with htb
    have hz : t⁻¹ * tb ∈ Subgroup.center ↥L := by
      rw [← ker_ggQuotHom θ]
      show ψ _ = 1
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have htb3 : tb ^ 3 = 1 := by rw [htb, ← map_pow, hS3' t ht, map_one]
    have hcz : Commute t (t⁻¹ * tb) := Subgroup.mem_center_iff.mp hz t
    have hz3 : (t⁻¹ * tb) ^ 3 = 1 := by
      have e : tb = t * (t⁻¹ * tb) := by group
      have h := hcz.mul_pow 3
      rw [← e, htb3, hS3' t ht, one_mul] at h
      exact h.symm
    exact (inv_mul_eq_one.mp (eq_one_of_cube hZ2 hz hz3)).symm
  set S' : Subgroup G := S.map L.subtype with hS'
  have hS'le : S' ≤ Bs := by
    rintro _ ⟨t, ht, rfl⟩
    apply hSC
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hcent t ht b hb)
      rw [normalizerMonoidHom_coe L ⟨b, hBN hb⟩ t] at h
      show b * (t : G) = (t : G) * b
      calc b * (t : G) = b * t * b⁻¹ * b := by group
        _ = (t : G) * b := by rw [h]
    · simpa using congrArg Subtype.val (hS3' t ht)
  have hcardS : Nat.card S = Nat.card Φ.range := by
    rw [← hSmap]
    refine Nat.card_congr (Equiv.ofBijective
      (fun s : S => (⟨ψ s, ⟨s, s.2, rfl⟩⟩ : ↥(S.map ψ))) ⟨?_, ?_⟩)
    · intro s s' h
      apply Subtype.ext
      have h2 : ψ ((s : ↥L)⁻¹ * (s' : ↥L)) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val h
      exact inv_mul_eq_one.mp (hSinj _ (S.mul_mem (S.inv_mem s.2) s'.2) h2)
    · rintro ⟨y, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hcardS' : Nat.card S' = Nat.card S :=
    Nat.card_congr (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).toEquiv.symm
  have hSeq : S' = Bs :=
    Subgroup.eq_of_le_of_card_ge hS'le (by rw [hcardS', hcardS]; exact hBcard.trans hrange)
  intro g hg
  rw [← hSeq] at hg
  obtain ⟨t, -, rfl⟩ := hg
  exact t.2

end Frame

section Component

theorem exists_component_ggBeta_two {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) :
    ∃ a ∈ (ggBeta L θ hBsN).range, a ≠ 1 ∧ ∃ J' : Subgroup R, IsComponentOf J' (ggFix a) := by
  classical
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨hDB, hDe, hDcard, hxD, hJdef, hJcomp, hDC⟩ := hcfg.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  obtain ⟨d, hdD, hdx⟩ := CFSG.StandardType.exists_mem_not_mem_zpowers hp hDcard
    (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
    CFSG.StandardType.eq_sup_zpowers_of_card hp hDe hDcard hxD hS.2.2.1 hdD hdx
  set d₀ : Bs := ⟨d, hBBs (hDB hdD)⟩ with hd₀
  set aγ := ggGamma L hBsN d₀ with haγ
  have hfix : (ggFix aγ).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBsN d₀
  have hJE : J = (LargeEvenLayer (ggFix aγ)).map L.subtype := by
    rw [hJdef, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  have hEcomp : IsComponentOf (LargeEvenLayer (ggFix aγ)) (ggFix aγ) := by
    have h1 := isComponentOf_comap_of_injective L.subtype L.subtype_injective
      (K' := J) (C := ggFix aγ) (by rw [hfix]; exact hJcomp)
    have h2 : J.comap L.subtype = LargeEvenLayer (ggFix aγ) := by
      rw [hJE, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [← h2]
    exact h1.1
  set f := ggQuotHom θ with hf
  have hfsurj : Function.Surjective f := ggQuotHom_surjective θ
  have hker : f.ker = Subgroup.center ↥L := ker_ggQuotHom θ
  set a := ggBeta L θ hBsN d₀ with ha
  have hcompat : ∀ l, a (f l) = f (aγ l) := fun l => ggBeta_ggQuotHom L hBsN θ d₀ l
  have haγ3 : aγ ^ 3 = 1 := by
    rw [haγ, ← map_pow]
    have h3 : d₀ ^ 3 = 1 := Subtype.ext (hBs.2 d (hBBs (hDB hdD)))
    rw [h3, map_one]
  have hZ2' : IsPGroup 2 f.ker := by rw [hker]; exact hZ2
  have hFix : ggFix a = (ggFix aγ).map f :=
    map_ggFix_eq_of_lift f hfsurj (le_of_eq hker) hZ2' haγ3 hcompat
  have ha1 : a ≠ 1 := by
    intro h
    have hc := mem_centralizer_of_ggLAut_eq_one L θ hL (g := ⟨(d₀ : G), hBsN d₀.2⟩) (by
      rw [← ggBeta_eq L θ hBsN d₀]
      exact h)
    apply hdx
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hDB hdD, hc⟩
  refine ⟨a, ⟨d₀, rfl⟩, ha1, (LargeEvenLayer (ggFix aγ)).map f, ?_⟩
  rw [hFix]
  refine isComponentOf_map_of_not_le_ker f hEcomp ?_
  rw [hker]
  exact not_le_center_of_isQuasisimple hEcomp.2.2

end Component

section Main

variable [Finite K]

theorem stepTwo_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) : False := by
  classical
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hKd : UnitaryFieldData 2 1 K :=
    CFSG.StandardType.TableBU.unitaryFieldData_of_card hK (Nat.le_refl 1)
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hcov := LineU.unitaryCoverOddAt_six_two K hK4
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := isPGroup_two_center hcov hKd hpq hL θ hz
  have hinner := all_inner_two hcfg hlt hKd hpq hL θ hZ2 hBN hBI hz
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hcardBs, -⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN' : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBN
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hxC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  have hxL : x ∉ L := fun hxL => hS.2.2.1 (hz x hxL hxC hx3)
  have hN := TableBUE.gu_subset_normalizer (d := 6) hKd
  set Ab := (ggBeta L θ hBN).range with hAb
  have hAbab : CFSG.Open.IsElemAbelian 3 Ab := isElemAbelian_range_ggBeta θ hBs hBN
  have hcardAb : Nat.card Ab * 3 = Nat.card Bs :=
    (card_range_ggBeta_bstar hcfg hL θ hBN' hBN).2.2
  have hAb27 : Nat.card Ab = 27 := by
    rw [hcardBs] at hcardAb
    omega
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)) := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN hBI b
  by_cases hfr : ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 1 K 6) ⟨M, hN hM⟩
  ·
    obtain ⟨P, hP, hPd⟩ := hfr
    have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
      config_selfCent hcfg
    have hrange := le_of_frame_two hKd hpq θ hZ2 hBN (by rw [hcardBs]) hSC hP
      (fun b hb => by
        obtain ⟨M₀, hM₀gu, hM₀d, hM₀eq⟩ := hPd (ggBeta L θ hBN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
        exact ⟨M₀, hN hM₀gu, by rw [← ggBeta_eq L θ hBN ⟨b, hb⟩]; exact hM₀eq, hM₀d⟩)
    exact hxL (hrange x hxBs)
  · rcases TableBU63.fieldType_or_heis hKd hK hpq hAbab hAbI (by rw [hAb27]; norm_num) hfr with
      ⟨M, hMN, l, -, hM3, hl, hMA⟩ | hheis
    ·
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hMA
      obtain ⟨M', hM'gu, hM'in, hM'eq⟩ := hinner b hb
      have hρ : TableB.projConj (unitarySU 2 1 K 6) ⟨M, hMN⟩ =
          TableB.projConj (unitarySU 2 1 K 6) ⟨M', hN hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq L θ hBN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq hKd hK hpq hMN (hN hM'gu) hρ
      have hMin : IsInner 1 M := by
        rw [hc, ← (TypeA.PGLTor.commute_scalar c M').eq]
        exact (isInner_scalar_mul_iff c M').mpr hM'in
      exact not_isInner_of_pow_three_eq_scalar hKd hM3 hl hMin
    ·
      obtain ⟨x', y', z', hx'N, hy'N, hz'N, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3m, hz3, hζ3, hζ1,
        hxy, hxz, hyz, hzs⟩ := hheis
      have hyA' := hyA
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hyA
      obtain ⟨M', hM'gu, hM'in, hM'eq⟩ := hinner b hb
      have hρ : TableB.projConj (unitarySU 2 1 K 6) ⟨y', hy'N⟩ =
          TableB.projConj (unitarySU 2 1 K 6) ⟨M', hN hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq L θ hBN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c₀, hc₀⟩ := exists_scalar_of_projConj_eq hKd hK hpq hy'N (hN hM'gu) hρ
      have hy'in : IsInner 1 y' := by
        rw [hc₀, ← (TypeA.PGLTor.commute_scalar c₀ M').eq]
        exact (isInner_scalar_mul_iff c₀ M').mpr hM'in
      have hy'cube : ∃ w : Kˣ, y' ^ 3 = GeneralLinearGroup.scalar (Fin 6) w := by
        have hmem : y' ^ 3 ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
          Subgroup.pow_mem _ hy'N 3
        have hρ3 : TableB.projConj (unitarySU 2 1 K 6) ⟨y' ^ 3, hmem⟩ =
            TableB.projConj (unitarySU 2 1 K 6) ⟨1, Subgroup.one_mem _⟩ := by
          have h1 : (⟨y' ^ 3, hmem⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))) = ⟨y', hy'N⟩ ^ 3 := rfl
          have h2 : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))) = 1 := rfl
          rw [h1, h2, map_pow, map_one]
          exact hAbab.2 _ hyA'
        obtain ⟨w, hw⟩ := exists_scalar_of_projConj_eq hKd hK hpq hmem (Subgroup.one_mem _) hρ3
        exact ⟨w, by rw [hw, one_mul]⟩
      obtain ⟨w, hw⟩ := hy'cube
      obtain ⟨c, hc⟩ := exists_pow_three_eq_one_of_isInner hKd hpq hy'in hw
      have hsN : GeneralLinearGroup.scalar (Fin 6) c ∈
          Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
        TableB.scalar_mem_normalizer _ ⟨c, rfl⟩
      have hy''N : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) := mul_mem hsN hy'N
      have hy''u : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          primeFormUnitary hKd (idGram K 6) :=
        TableBUD.mem_primeFormUnitary_of_pow_eq_one hKd hpq (by norm_num)
          (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hyu) (c := (c : K))
          (by rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
            TableBUD.scalar_mul_eq_smul]) hc
      have hy''A : TableB.projConj (unitarySU 2 1 K 6) ⟨GeneralLinearGroup.scalar (Fin 6) c * y',
          hy''N⟩ ∈ Ab := by
        have : (⟨GeneralLinearGroup.scalar (Fin 6) c * y', hy''N⟩ :
            ↥(Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))) =
            ⟨GeneralLinearGroup.scalar (Fin 6) c, hsN⟩ * ⟨y', hy'N⟩ := rfl
        rw [this, map_mul, TableB.projConj_of_scalar _ ⟨c, rfl⟩, one_mul]
        exact hyA'
      have hxy' : x' * (GeneralLinearGroup.scalar (Fin 6) c * y') =
          GeneralLinearGroup.scalar (Fin 6) ζ *
            ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
        calc x' * (GeneralLinearGroup.scalar (Fin 6) c * y')
            = GeneralLinearGroup.scalar (Fin 6) c * (x' * y') := by
              rw [← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c x').eq.symm]
          _ = GeneralLinearGroup.scalar (Fin 6) c *
                (GeneralLinearGroup.scalar (Fin 6) ζ * (y' * x')) := by rw [hxy]
          _ = (GeneralLinearGroup.scalar (Fin 6) c * GeneralLinearGroup.scalar (Fin 6) ζ) *
                (y' * x') := by rw [mul_assoc]
          _ = (GeneralLinearGroup.scalar (Fin 6) ζ * GeneralLinearGroup.scalar (Fin 6) c) *
                (y' * x') := by
              rw [(TypeA.PGLTor.commute_scalar c (GeneralLinearGroup.scalar (Fin 6) ζ)).eq]
          _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
              rw [mul_assoc, mul_assoc]
      have hy''z : (GeneralLinearGroup.scalar (Fin 6) c * y') * z' =
          z' * (GeneralLinearGroup.scalar (Fin 6) c * y') := by
        rw [mul_assoc, hyz, ← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c z').eq]
      obtain ⟨a, haAb, ha1, J', hacomp⟩ := exists_component_ggBeta_two hcfg hL θ hBN hZ2
      exact not_isComponentOf_ggFix_of_heis_two hKd hpq hAb27
        ⟨x', GeneralLinearGroup.scalar (Fin 6) c * y', z', hx'N, hy''N, hz'N, ζ, hxu, hy''u, hzu,
          hxA, hy''A, hzA, hx3m, hc, hz3, hζ3, hζ1, hxy', hxz, hy''z, hzs⟩ a haAb ha1 J' hacomp

end Main

theorem line63StepTwoQ2_holds :
    Line63StepTwoQ2 := by
  intro G _ _ B Bs x L D J hcfg hlt K _ _ hK hL θ hBN hBI hz
  exact stepTwo_two hcfg hlt hK hL θ hBN hBI hz

end CFSG.StandardType.Line63.H5

end
