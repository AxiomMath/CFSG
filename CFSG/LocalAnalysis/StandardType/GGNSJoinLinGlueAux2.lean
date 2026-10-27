module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinLinGlueAux
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CoverData
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

theorem nsLG_recipeLinear_of_rawDatum {ℓ : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum ⟨.A, ℓ, 1⟩ Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Q (LargeEvenProj (LargeEvenSLGroup (Fin (ℓ + 1)) K))
        (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ)
        (LargeEvenMatFieldImage (LargeEvenProjMk _)) := by
  simpa only [LargeEvenRawDatum, LargeEvenRecipeLinear, pow_one] using h

theorem nsLG_charP_two_of_card_two {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, h])

theorem nsLG_subsingleton_units_of_card_two {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) : Subsingleton Kˣ := by
  have hu : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, h]
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have h1 : Fintype.card Kˣ = 1 := by rw [← Nat.card_eq_fintype_card, hu]
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h1
  exact ⟨fun x y => by rw [ha x, ha y]⟩

theorem nsLG_linear_bound
    (hLin : GGLabelRigidInput → ∀ {N : ℕ}, 6 ≤ N → ∀ {F : Type} [Field F] [Finite F] [CharP F 2],
      Nat.card F = 2 → ∀ {g : GL (Fin N) F}, g ^ 3 = 1 →
        ∀ {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))},
          CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) →
            ∀ {labJ : LargeEvenLabel}, LargeEvenInLambda2 labJ →
              GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀) → labJ.n ≤ 2)
    (hRig : GGLabelRigidInput) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hInn : GGInnerDiagAll 3 B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) {ℓ : ℕ} (hℓ : 5 ≤ ℓ)
    (hhasK : GGHasLabel ⟨.A, ℓ, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hhasJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) : labJ.n ≤ 2 := by
  have hT : GGThmIHyp 3 B x L := hcfg.1
  have hSS := hT.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hx1 : x ^ 3 = 1 := hSS.1.1.2 x hxB
  have hJK : J ≤ K := le_of_ggNbr hL hT hcfg.2.2 (hP G 3 B x L D J hT hcfg.2.2) hnb
  have hcompK := ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hInnK : GGInnerDiagOn Bs K := hInn.2 y K hnb
  have hKΛ : LargeEvenInLambda2 ⟨.A, ℓ, 1⟩ := by
    simp only [LargeEvenInLambda2]
    omega
  have hKmark := ggInnerDiagOn_relabel hRig hInnK hKΛ hhasK
  unfold CFSG.StandardType.LargeEvenMarking at hKmark
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hKmark
  have hraw' : LargeEvenRawDatum lab (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
          (lab = ⟨.A, ℓ, 1⟩ ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
              (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) := hraw
  have hhas_lab : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw'
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hiso : GGLabelIso lab ⟨.A, ℓ, 1⟩ :=
    hRig lab ⟨.A, ℓ, 1⟩ (↥K ⧸ Subgroup.center ↥K) hlab hKΛ hhas_lab hhasK
  have hraw'' := largeEvenRawDatum_of_ggLabelIso hiso hraw'
  obtain ⟨K0, hfieldK0, hfinK0, hcardK0, hQ⟩ := nsLG_recipeLinear_of_rawDatum hraw''
  letI := hfieldK0
  letI := hfinK0
  haveI : CharP K0 2 := nsLG_charP_two_of_card_two hcardK0
  obtain ⟨-, -, θ0, -, hNK, hind⟩ := hQ
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNK hxBs
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hep : e ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  have hφe : ∀ l : ↥K, φ (θ0 (QuotientGroup.mk l)) = θ0 (QuotientGroup.mk (e l)) := by
    intro l
    apply hφ l (e l)
    show ((e l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hφeq : φ = ggInducedAut θ0 e := by
    ext r
    obtain ⟨q, rfl⟩ := θ0.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφe l, ggInducedAut_apply]
  have hφpow : φ ^ 3 = 1 := by
    rw [hφeq, ← map_pow, hep, map_one]
  obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut hφI
  have hA3 : A ^ 3 = 1 := by
    have h1 : TableB.linConjAut (Fin (ℓ + 1)) K0 (A ^ 3) = 1 := by
      rw [map_pow, ← hA, hφpow]
    obtain ⟨c, hc⟩ := q1CentLin_scalar_of_linConjAut_eq_one (by omega : 2 ≤ ℓ + 1) h1
    haveI : Subsingleton K0ˣ := nsLG_subsingleton_units_of_card_two hcardK0
    have hc1 : c = 1 := Subsingleton.elim c 1
    rw [hc1, map_one] at hc
    exact hc.symm
  have hJcompK : CFSG.Assembly.IsComponentOf (J.subgroupOf K) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcompK
  have hJcompK' : CFSG.Open.IsComponentOf (J.subgroupOf K) (ggAutFixedSubgroup e) := by
    have h := CFSG.Assembly.isComponentOf_iff_open.mp hJcompK
    simpa only [ggAutFixedSubgroup, ggFixSub] using h
  let J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin (ℓ + 1)) K0)) :=
    (J.subgroupOf K).map (q2CoverMap θ0)
  obtain ⟨hJ₀comp, ι, ι_mk⟩ := q2_cover_data hKperf θ0 e (J.subgroupOf K) hJcompK'
  have hφe2 : ggInducedAut θ0 e = TableB.linConjAut (Fin (ℓ + 1)) K0 A := by
    rw [← hφeq, hA]
  have hJ₀comp' : CFSG.Open.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin (ℓ + 1)) K0 A)) := by
    rw [← hφe2]
    exact hJ₀comp
  have hhasJsub : GGHasLabel labJ
      (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)).symm hhasJ
  have hhasJ₀ : GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    ggHasLabel_of_mulEquiv ι hhasJsub
  exact hLin hRig (by omega : 6 ≤ ℓ + 1) (F := K0) hcardK0 (g := A) hA3
    (J₀ := J₀) hJ₀comp' (labJ := labJ) hΛJ hhasJ₀

end NSJoin

end CFSG.StandardType

end
