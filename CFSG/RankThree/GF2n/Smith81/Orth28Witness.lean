module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

section Witness

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem orthComm_eq_iff_conj {p z : G} (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hz : z ∈ Z) :
    ⁅p, x⁆ = z ↔ p * x * p⁻¹ = x * z := by
  have h1 : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hxZ z hz)
  rw [h1]
  constructor
  · intro h
    rw [← h]
    simp only [commutatorElement_def]
    group
  · intro h
    rw [commutatorElement_def, h]
    group

theorem orthTheta_surj_of_root {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (gm : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    {v : G} (hvQ : v ∈ Q) (hvZ : ⁅v, x⁆ ∈ Z) (hv1 : ⁅v, x⁆ ≠ 1) {Γ : Subgroup G}
    (hΓ : IsZConjugate Z Γ) (hvΓ : v ∈ Γ) : ∀ z ∈ Z, ∃ w ∈ Q, ⁅w, x⁆ = z := by
  have H := hs.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hv1' : v ≠ 1 := by
    rintro rfl
    exact hv1 (by simp)
  have hvZ' : v ∉ Z := by
    intro hvz
    apply hv1
    have h1 : x * v = v * x := mul_inv_eq_iff_eq_mul.mp (hxZ v hvz)
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
  have hΓQ : Γ ≤ Q := by
    have := (IsZConjugate.self Z).le_QB_of_mem H hΓ hv1' hvΓ (by rw [H.QB_Z]; exact hvQ)
    rwa [H.QB_Z] at this
  have hΓZ : Γ ≠ Z := fun h => hvZ' (h ▸ hvΓ)
  have hcΓ : Ctx M Q Z Γ := ⟨H, hΓ, hΓQ, hΓZ⟩
  obtain ⟨b, hb0, -, hline, -, -⟩ := hcΓ.dictB gm
  obtain ⟨T, hTπ, -, -⟩ := gm.linear_of_centralizes hs.memM hxZ
  have hcomm_iff : ∀ {y : G}, y ∈ Q → (⁅y, x⁆ ∈ Z ↔ T (M₀.π y) = M₀.π y) := by
    intro y hy
    have hxy : x * y * x⁻¹ ∈ Q := conj_mem_Q H hs.memM hy
    rw [← Z.inv_mem_iff, commutatorElement_inv,
      Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hy hxy, hTπ y hy]
  have hTv : T (M₀.π v) = M₀.π v := (hcomm_iff hvQ).mp hvZ
  obtain ⟨s₀, hs₀⟩ := (hline _).mp (M₀.pi_mem_img hvΓ hvQ)
  have hπv0 : M₀.π v ≠ 0 := fun h => hvZ' ((M₀.π_ker v hvQ).mp h)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hπv0 (by rw [hs₀, zero_smul])
  have hTb : T b = b := by
    have h1 : s₀ • T b = s₀ • b := by rw [← map_smul, ← hs₀, hTv]
    exact smul_right_injective _ hs₀0 h1
  have hTΓ : ∀ w ∈ Γ, ⁅w, x⁆ ∈ Z := by
    intro w hw
    obtain ⟨s, hs⟩ := (hline _).mp (M₀.pi_mem_img hw (hΓQ hw))
    refine (hcomm_iff (hΓQ hw)).mpr ?_
    rw [hs, map_smul, hTb]
  let ψ : ↥Γ →* ↥Z :=
    { toFun := fun w => ⟨⁅(w : G), x⁆, hTΓ w w.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun w w' => Subtype.ext (by
        have hwQ : (w : G) ∈ Q := hΓQ w.2
        have hw' : ⁅(w' : G), x⁆ ∈ Z := hTΓ w' w'.2
        have hw : ⁅(w : G), x⁆ ∈ Z := hTΓ w w.2
        show ⁅((w * w' : ↥Γ) : G), x⁆ = ⁅(w : G), x⁆ * ⁅(w' : G), x⁆
        have h1 : (w : G) * ⁅(w' : G), x⁆ * (w : G)⁻¹ = ⁅(w' : G), x⁆ := by
          rw [← Z_central H hw' hwQ]; group
        have h2 : ⁅(w : G) * (w' : G), x⁆ =
            (w : G) * ⁅(w' : G), x⁆ * (w : G)⁻¹ * ⁅(w : G), x⁆ := by
          simp only [commutatorElement_def]; group
        rw [Subgroup.coe_mul, h2, h1, Z_central H hw' (hZQ hw)]) }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : ⁅(w : G), x⁆ = 1 := congrArg Subtype.val hw
    by_contra hne
    have hw1 : (w : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hcomm : Commute x (w : G) := (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hxN := hΓ.mem_normalizer_of_commute H hw1 w.2 hcomm
    have hxv : x * v * x⁻¹ ∈ Γ := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvΓ
    have hinv : ⁅v, x⁆⁻¹ ∈ Γ := by
      have e : ⁅v, x⁆⁻¹ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact Γ.mul_mem hxv (Γ.inv_mem hvΓ)
    have hbot : Z ⊓ Γ = ⊥ := by
      obtain ⟨g, rfl⟩ := hΓ
      exact inf_conjSubgroup_eq_bot_of_isTI H.ti (fun h => hΓZ h)
    have : ⁅v, x⁆⁻¹ ∈ Z ⊓ Γ := ⟨Z.inv_mem hvZ, hinv⟩
    rw [hbot, Subgroup.mem_bot, inv_eq_one] at this
    exact hv1 this
  have hbij : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le hinj (by rw [hΓ.card_eq])
  intro z hz
  obtain ⟨w, hw⟩ := hbij.2 ⟨z, hz⟩
  exact ⟨w, hΓQ w.2, congrArg Subtype.val hw⟩

theorem orthWitness_holds : OrthWitnessStatement := by
  intro G _ _ M Q Z B hc X x hs q' hq'Q hq'c hqZ hq1 z' hz'
  have H := hs.hyp
  obtain ⟨K, _, _, _, γ, M₀, gm⟩ := stroth_globalModelData H
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  have hz₀x : IsConj (g₀⁻¹ * x * g₀) x := isConj_iff.mpr ⟨g₀, by group⟩
  obtain ⟨Γ, hΓ, hq'Γ⟩ := exists_isZConjugate_mem hz₀ (hz₀x.trans hq'c)
  obtain ⟨p, hp, hpz⟩ := orthTheta_surj_of_root gm hs hq'Q hqZ hq1 hΓ hq'Γ z' hz'
  refine ⟨p⁻¹, Q.inv_mem hp, ?_⟩
  have := (orthComm_eq_iff_conj hxZ hz').mp hpz
  simpa using this

end Witness

end CFSG.RankThree.GF2n.Smith81
