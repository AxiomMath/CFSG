module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCover
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.Line63 CFSG.StandardType.Line63.H5
  CFSG.StandardType.USixTwo CFSG.ClassicalGroups.UnitaryFlag

section Certificates


theorem unitaryCoverAt_four {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) : LineU.UnitaryCoverAt n 4 K := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    CFSG.StandardType.TableBU.unitaryFieldData_of_card hK (by omega)
  haveI : CharP K 2 := hU.charP
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : commutator (unitarySU 2 n K 4) = ⊤ := by
    haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hK (le_refl 4)
    exact Group.IsPerfect.commutator_eq_top
  refine LineU.unitaryCoverAt_of_section hperf ?_
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
    hK ⟨2, rfl⟩ (le_refl 4) hq hπ hcen

theorem unitaryCoverOddAt_four_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    Line63.UnitaryCoverOddAt 1 4 K := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by norm_num [hK]⟩
  haveI : CharP K 2 := hU.charP
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by norm_num [hK]
  refine LineU.unitaryCoverOddAt_of_section ?_ ?_
  · haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF
      (show 4 ≤ 4 by norm_num)
    exact Group.IsPerfect.commutator_eq_top
  · intro E _ _ π hπ hcen hodd
    exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
      (n := 4) hF ⟨2, rfl⟩ (by norm_num) E π hπ hcen (Nat.coprime_two_left.2 hodd)

theorem exists_diagModel_coprime_odd {Lb : Type} [Group Lb] [Finite Lb] {K : Type} [Field K]
    [Finite K] {d p : ℕ} (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ 1 + 1) (hpd : ¬ p ∣ d) (hcov : Line63.UnitaryCoverOddAt 1 d K)
    {ψ : Lb →* LargeEvenProj (unitarySU 2 1 K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center Lb) (hperf : commutator Lb = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {A : Subgroup (MulAut Lb)} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K d))
        (LargeEvenGUSet (Fin d) K (2 ^ 1)), ∀ l : Lb, x (ψ l) = ψ (a l)) :
    ∃ φ : ↥(unitarySU 2 1 K d) →* Lb, UnitTB.Model φ ∧
      ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t := by
  have hcovT : ∀ θ : LargeEvenProj (unitarySU 2 1 K d) ≃* LargeEvenProj (unitarySU 2 1 K d),
      ∃ φ : ↥(unitarySU 2 1 K d) →* Lb,
        ∀ s, θ (ψ (φ s)) = LargeEvenProjMk (unitarySU 2 1 K d) s := by
    intro θ
    have hk : (θ.toMonoidHom.comp ψ).ker = ψ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ θ.injective]
    obtain ⟨φ, hφ⟩ := hcov.2 Lb (θ.toMonoidHom.comp ψ) (θ.surjective.comp hψ) (hk ▸ hker) hperf
      (hk ▸ hodd)
    exact ⟨φ, hφ⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := LineU.exists_diagModel_coprime_of_twist hK le_rfl hd hp hpq
    hpd hψ hker hperf hcov.1 hcovT hA hAI
  exact ⟨φ, ⟨CFSG.StandardType.TableBU.unitaryFieldData_of_card hK le_rfl, hφs, hφker⟩, hdiag⟩

theorem exists_diagonal_cover_of_unitary_four
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hInn : GGInnerDiagOn Bs X)
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 3, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 3, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F 4) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 4 → F, LineU.ActsDiagU φ a t := by
  classical
  have hp : p.Prime := Fact.out
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = (2 ^ f) ^ 2 := by simpa [pow_two] using hFK
  have hF2 : Nat.card F = 2 ^ (2 * f) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hF
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm]
  have : CharP F 2 := charP_two_of_card hF2
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hAe : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hAI : ∀ a ∈ (ggGamma X hN).range, ∃ φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 f F 4))
        (LargeEvenGUSet (Fin 4) F (2 ^ f)),
      ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, ggBeta_mem X θ hN hBsI b,
      fun l => ggBeta_ggQuotHom X hN θ b l⟩
  have hf1 : 1 ≤ f := hΛ.1
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime (L' := X) (K := F) (n := f) (d := 4) (p := p)
      hF hf1 (by norm_num) hp hpq (not_dvd_four_of_dvd_two_pow_add_one hp hf1 hpq)
      (unitaryCoverAt_four hF hf) (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hXperf hAe hAI
  exact ⟨F, hField, hFinite, inferInstance, hN, φ, hF,
    ⟨CFSG.StandardType.TableBU.unitaryFieldData_of_card hF hf1, hφs, hφker⟩, hdiag⟩

theorem exists_diagonal_cover_of_unitary_four_two_red
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hXp : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (unitarySU 2 1 F 4))
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 4)) (LargeEvenGUSet (Fin 4) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ (hNbar : (redMkB hN).range ≤
        Subgroup.normalizer ((redMkL X).range : Set (RedGrp X))),
      ∃ φ : ↥(unitarySU 2 1 F 4) →* (redMkL X).range,
        UnitTB.Model φ ∧
          ∀ a ∈ (ggGamma (redMkL X).range hNbar).range,
            ∃ t : Fin 4 → F, LineU.ActsDiagU φ a t := by
  classical
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  let Xbar : Subgroup (RedGrp X) := (redMkL X).range
  let Bbar : Subgroup (RedGrp X) := (redMkB hN).range
  have hNbar : Bbar ≤ Subgroup.normalizer (Xbar : Set (RedGrp X)) := by
    intro b hb
    have : Xbar.Normal := by
      change (redMkL X).range.Normal
      infer_instance
    have htop : Subgroup.normalizer (Xbar : Set (RedGrp X)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop]
    exact Subgroup.mem_top b
  let ψ : ↥X →* LargeEvenProj (unitarySU 2 1 F 4) := ggQuotHom θ
  have hzker : zTwo X ≤ ψ.ker := by
    rw [show ψ.ker = Subgroup.center ↥X by
      simpa [ψ] using ker_ggQuotHom θ]
    exact zTwo_le_center
  let ψQ : Qt X →* LargeEvenProj (unitarySU 2 1 F 4) := qLift ψ hzker
  have hψQ : Function.Surjective ψQ :=
    qLift_surjective hzker (ggQuotHom_surjective θ)
  have hkerQ : ψQ.ker ≤ Subgroup.center (Qt X) :=
    qLift_ker_le_center hzker (by simpa [ψ] using (ker_ggQuotHom θ).le)
  have hperfQ : commutator (Qt X) = ⊤ := qmk_perfect hXp
  have hoddQ : Odd (Nat.card ψQ.ker) :=
    qLift_odd_ker hzker (by simpa [ψ] using (ker_ggQuotHom θ).le)
  let AQ : Subgroup (MulAut (Qt X)) := (ggGamma X hN).range.map (qAutHom X)
  have hγrange : IsElemAbelian 3 (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hAQ : IsElemAbelian 3 AQ := by
    simpa [AQ] using IsElemAbelian.map hγrange (qAutHom X)
  have hAIQ : ∀ a ∈ AQ, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 4)) (LargeEvenGUSet (Fin 4) F (2 ^ 1)),
      ∀ l : Qt X, x (ψQ l) = ψQ (a l) := by
    intro a ha
    change a ∈ (ggGamma X hN).range.map (qAutHom X) at ha
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, rfl⟩ := hγ
    obtain ⟨x, hxI, hxind⟩ := hBI (b⁻¹) (Subgroup.inv_mem Bs b.2)
    refine ⟨x, hxI, ?_⟩
    intro l
    obtain ⟨l0, rfl⟩ := qmk_surjective l
    rw [qAutHom_mk]
    change x (ggQuotHom θ l0) = ggQuotHom θ (ggGamma X hN b l0)
    have hrel : ((ggGamma X hN b l0 : ↥X) : G) = (b⁻¹ : ↥Bs)⁻¹ * (l0 : G) * (b⁻¹ : ↥Bs) := by
      simp only [Subgroup.coe_inv, inv_inv]
      exact ggGamma_coe X hN b l0
    have hx := hxind l0 (ggGamma X hN b l0) hrel
    simpa [ggQuotHom_apply, ψQ, qLift_mk] using hx
  have hperfSU : commutator (unitarySU 2 1 F 4) = ⊤ := by
    haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF' (le_refl 4)
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨φQ, hMQ, hdiagQ⟩ := exists_diagModel_coprime_odd (p := 3) hF' (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) (unitaryCoverOddAt_four_two F hF) hψQ hkerQ
    hperfQ hoddQ hAQ hAIQ
  obtain ⟨φ, hM, hdiag⟩ := exists_diag_redQt hN hNbar hMQ hdiagQ
  exact ⟨hNbar, φ, hM, hdiag⟩

end Certificates

end CFSG.StandardType

end
