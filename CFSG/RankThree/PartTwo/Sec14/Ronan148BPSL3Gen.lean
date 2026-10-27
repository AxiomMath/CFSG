module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSTrans
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofHessL
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofSeitzU
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofTwentySeven
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (ModThree qSubPi PiField slPi)
open scoped commutatorElement

theorem mulAut_mul_conj' {X : Type*} [Group X] (σ : MulAut X) (x : X) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  refine MulEquiv.ext fun k => ?_
  simp [MulAut.mul_apply, MulAut.inv_apply]

theorem mem_normalizer_of_conj_mem' {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ v ∈ H, g * v * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem eq_one_of_mem_of_mem {G : Type*} [Group G] {Y F : Subgroup G} (hY : ¬ 3 ∣ Nat.card Y)
    (hF : IsPGroup 3 F) {y : G} (hyY : y ∈ Y) (hyF : y ∈ F) : y = 1 := by
  obtain ⟨k, hk⟩ := hF ⟨y, hyF⟩
  have h1 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf y ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hyY
  have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY)
  have h3 : orderOf y = 1 := Nat.dvd_one.mp (by
    rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.mp h3

theorem sigGenConcl_of_gen {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {F : Subgroup X} (hF3 : IsPGroup 3 F)
    (hF : ∀ x : X, (∀ σ ∈ P, σ x = x) → x ∈ F) {K₀ : Subgroup X}
    (hgen : K₀ ≤ sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧
      ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y}) :
    SigGenConcl P (K₀.map (MulAut.conj : X →* MulAut X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := PS.conj_injective hZ
  unfold SigGenConcl
  refine (Subgroup.map_mono hgen).trans ?_
  rw [(Subgroup.gc_map_comap _).l_sSup]
  refine iSup₂_le fun Y hY => ?_
  obtain ⟨hYK, hY3, hYP⟩ := hY
  set V := Y.map (MulAut.conj : X →* MulAut X) with hV
  have hV3 : ¬ 3 ∣ Nat.card V := by
    rw [hV, Subgroup.card_map_of_injective hinj]
    exact hY3
  have hPV : P ≤ Subgroup.normalizer (V : Set (MulAut X)) := by
    intro σ hσ
    refine mem_normalizer_of_conj_mem' fun v hv => ?_
    obtain ⟨y, hy, rfl⟩ := hv
    rw [mulAut_mul_conj']
    exact ⟨σ y, hYP σ hσ y hy, rfl⟩
  have hC : V ⊓ Subgroup.centralizer (P : Set (MulAut X)) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨y, hy, rfl⟩, hvC⟩
    have hfix : ∀ σ ∈ P, σ y = y := by
      intro σ hσ
      have h1 := Subgroup.mem_centralizer_iff.mp hvC σ hσ
      apply hinj
      rw [← mulAut_mul_conj', h1, mul_inv_cancel_right]
    have := eq_one_of_mem_of_mem hY3 hF3 hy (hF y hfix)
    rw [Subgroup.mem_bot, this, map_one]
  have hcomm : V = ⁅V, P⁆ := by
    have h := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
      Nat.prime_three P V hP hPV ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3)
    rw [hC, sup_bot_eq] at h
    exact h.symm
  refine le_sSup ⟨Subgroup.map_mono hYK, ⟨le_top,
    (isPiSubgroup_piCompl_iff Nat.prime_three _).2 hV3, hPV⟩, hcomm⟩

theorem isPGroup_centralizer_hessian {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {k : ℕ}
    (hk : ∀ π : Bool, ModThree π (p ^ e) → qSubPi π (p ^ e) = 3 ^ k)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) : IsPGroup 3 (Subgroup.centralizer ({x} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hEψ : CFSG.Assembly.IsElemAbelian 3 (E.map ψ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom E hEe
  have hEψ9 : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have htrψ : ∀ y₀ ∈ E.map ψ.toMonoidHom, y₀ ≠ 1 → ∀ y₁ ∈ E.map ψ.toMonoidHom, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.map ψ.toMonoidHom : Subgroup _) : Set _),
        w * y₀ * w⁻¹ = y₁ := by
    rintro _ ⟨y₀, hy₀, rfl⟩ hy₀1 _ ⟨y₁, hy₁, rfl⟩ hy₁1
    have hy₀1' : y₀ ≠ 1 := fun h => hy₀1 (by rw [h, map_one])
    have hy₁1' : y₁ ≠ 1 := fun h => hy₁1 (by rw [h, map_one])
    obtain ⟨w, hw, hwy⟩ := htr y₀ hy₀ hy₀1' y₁ hy₁ hy₁1'
    refine ⟨ψ w, ?_, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨w, hw, rfl⟩
    · change ψ w * ψ y₀ * (ψ w)⁻¹ = ψ y₁
      rw [← map_inv, ← map_mul, ← map_mul, hwy]
  have hcube := Res8Hess.hasCubeOneLift_of_transitive hK hEψ hEψ9 htrψ
  have hψx1 : ψ x ≠ 1 := fun h => hx1 (ψ.injective (by rw [h, map_one]))
  have hdvd := Res8Hess.card_centralizer_dvd_of_hasCubeOneLift hK hq hψx1
    (hcube _ ⟨x, hx, rfl⟩ hψx1)
  rw [hk π hq] at hdvd
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (Subgroup.centralizer ({ψ x} : Set (projImage (slPi π 3 (p ^ e) K)))) := by
    rw [← CFSG.RankThree.PartTwo.map_centralizer_singleton ψ x,
      Subgroup.card_map_of_injective ψ.injective]
  rw [← hcard, ← pow_mul, ← pow_succ'] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact IsPGroup.of_card hj

theorem eq_bot_of_hessian {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {k : ℕ}
    (hk : ∀ π : Bool, ModThree π (p ^ e) → qSubPi π (p ^ e) = 3 ^ k)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {Y : Subgroup X} (hY3 : ¬ 3 ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set X)) :
    Y = ⊥ := by
  rw [eq_bot_iff]
  refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hEe
    (by rw [hE9]; norm_num) hEY ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
    fun v hv hv1 => ?_
  intro y hy
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_of_mem hY3
    (isPGroup_centralizer_hessian he hiso hk hEe hE9 htr hv hv1) hy.1 hy.2)

theorem hessGen_or_bot
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (hperf : Group.IsPerfect X)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ ∨
      ∀ Y : Subgroup X, ¬ 3 ∣ Nat.card Y → E ≤ Subgroup.normalizer (Y : Set X) → Y = ⊥ := by
  by_cases hmod : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8
  · by_cases hU38 : Sec4.IsoLThreePi X 2 3
    · right
      intro Y hY3 hEY
      refine eq_bot_of_hessian (by norm_num) hU38 (k := 2) (fun π hq => ?_) hEe hE9 htr hY3 hEY
      cases π
      · rfl
      · exact absurd hq (by norm_num [ModThree])
    · left
      exact ks142L3HessGenNine_of_model ks142L3HessGenNineModel_proof X p e he hiso hperf hmod
        hU38 E hEe hE9 htr
  · by_cases hL4 : Sec4.IsoLThreePi X 2 2
    · right
      intro Y hY3 hEY
      refine eq_bot_of_hessian (by norm_num) hL4 (k := 1) (fun π hq => ?_) hEe hE9 htr hY3 hEY
      cases π
      · exact absurd hq (by norm_num [ModThree])
      · rfl
    · left
      have h := Sec15.ks1517Gen_of (Sec15.ks1517CentGen_of ks1517SeitzU) X p e he hiso hperf hmod
        hL4 E hEe hE9
      rwa [Res6GenL3.invariantPiSubgroups_top_piCompl_eq] at h

theorem ks142L3PGLGenModel_proof :
    KS142L3PGLGenModel :=
  ks142L3PGLGenModel_of_std
    (ks142L3PGLGenStd_of ks142L3PGLGenStdU_proof L3PGL.ks142L3PGLGenStdFour)

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
