module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfX0
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Inner
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTrans
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item14J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem zpowers_mul_three_ne {A : Subgroup G} {c d : G} (hA : Late.IsE27 A)
    (hcA : c ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1) (hcd : c ∉ Subgroup.zpowers d) :
    Subgroup.zpowers c ≠ Subgroup.zpowers (c * d) ∧
      Subgroup.zpowers c ≠ Subgroup.zpowers (c * d ^ 2) ∧
      Subgroup.zpowers (c * d) ≠ Subgroup.zpowers (c * d ^ 2) := by
  have hE : CFSG.Assembly.IsElemAbelian 3
      (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) :=
    Proof152ResW.isElemAbelian_sup hA hcA hdA
  have hmem : ∀ {b b' : G}, b ∈ Subgroup.zpowers d → b' ∈ Subgroup.zpowers d →
      Subgroup.zpowers (c * b) = Subgroup.zpowers (c * b') → b = b' :=
    fun hb hb' h => zpowers_mul_injOn (A := Subgroup.zpowers c ⊔ Subgroup.zpowers d)
      (B := Subgroup.zpowers d) hE (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      rfl hcd hb hb' h
  have hd2 : d ^ 2 ≠ 1 := by
    intro h
    have h3 : d ^ 3 = 1 := hA.1.2 d hdA
    exact hd1 (by
      calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h, inv_one, mul_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    have h' : Subgroup.zpowers (c * 1) = Subgroup.zpowers (c * d) := by simpa using hh
    exact hd1 (hmem (one_mem _) (Subgroup.mem_zpowers d) h').symm
  · intro hh
    have h' : Subgroup.zpowers (c * 1) = Subgroup.zpowers (c * d ^ 2) := by simpa using hh
    exact hd2 (hmem (one_mem _) (pow_mem (Subgroup.mem_zpowers d) 2) h').symm
  · intro hh
    have h' : d = d ^ 2 := hmem (Subgroup.mem_zpowers d)
      (pow_mem (Subgroup.mem_zpowers d) 2) hh
    have h1d : (1 : G) = d := by
      calc 1 = d * d⁻¹ := (mul_inv_cancel d).symm
        _ = d ^ 2 * d⁻¹ := by rw [← h']
        _ = d := by group
    exact hd1 h1d.symm

theorem omegaA_eq_triple {A : Subgroup G} {c d : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hcd : c ∉ Subgroup.zpowers d)
    (h1Ω : Subgroup.zpowers c ∈ omegaA A)
    (hcdΩ : Subgroup.zpowers (c * d) ∈ omegaA A)
    (hcd2Ω : Subgroup.zpowers (c * d ^ 2) ∈ omegaA A) (h3 : (omegaA A).ncard = 3) :
    omegaA A = {Subgroup.zpowers c, Subgroup.zpowers (c * d),
      Subgroup.zpowers (c * d ^ 2)} := by
  obtain ⟨hne1, hne2, hne3⟩ := zpowers_mul_three_ne hA hcA hdA hd1 hcd
  have hS3 : ({Subgroup.zpowers c, Subgroup.zpowers (c * d),
      Subgroup.zpowers (c * d ^ 2)} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne1, hne2]),
      Set.ncard_insert_of_notMem (by simp [hne3]), Set.ncard_singleton]
  have hsub : ({Subgroup.zpowers c, Subgroup.zpowers (c * d),
      Subgroup.zpowers (c * d ^ 2)} : Set (Subgroup G)) ⊆ omegaA A := by
    intro F hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    rcases hF with rfl | rfl | rfl
    · exact h1Ω
    · exact hcdΩ
    · exact hcd2Ω
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h3, hS3]) (Set.toFinite _)).symm

theorem mem_centralizer_of_mul_mem_sup {X Θ : Subgroup G} {c t x : G}
    (hctx : t * x = c) (hcX : c ∈ Subgroup.centralizer (X : Set G)) (hxX : x ∈ X)
    (htθ : t ∈ Θ) (hXθ : X ≤ Subgroup.normalizer (Θ : Set G))
    (hinfs : X ⊓ Θ = ⊥) : t ∈ Subgroup.centralizer (X : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have ht_eq : t = c * x⁻¹ := by
    rw [← hctx]
    group
  have hconj : t * y * t⁻¹ = x⁻¹ * y * x := by
    rw [ht_eq]
    have hcomm := Subgroup.mem_centralizer_iff.mp hcX (x⁻¹ * y * x)
      (X.mul_mem (X.mul_mem (X.inv_mem hxX) hy) hxX)
    calc c * x⁻¹ * y * (c * x⁻¹)⁻¹ = c * (x⁻¹ * y * x) * c⁻¹ := by group
      _ = (x⁻¹ * y * x) * c * c⁻¹ := by rw [← hcomm]
      _ = x⁻¹ * y * x := by group
  have hmemX : t * y * t⁻¹ * y⁻¹ ∈ X := by
    rw [hconj]
    exact X.mul_mem (X.mul_mem (X.mul_mem (X.inv_mem hxX) hy) hxX) (X.inv_mem hy)
  have hyN : y ∈ Subgroup.normalizer (Θ : Set G) := hXθ hy
  have hmemθ : t * y * t⁻¹ * y⁻¹ ∈ Θ := by
    have h1 : y * t * y⁻¹ ∈ Θ := (Subgroup.mem_normalizer_iff.mp hyN t).mp htθ
    have h2 : y * t⁻¹ * y⁻¹ ∈ Θ := by simpa [mul_assoc] using Θ.inv_mem h1
    simpa [mul_assoc] using Θ.mul_mem htθ h2
  have hz1 : t * y * t⁻¹ * y⁻¹ = 1 := by
    have hmem : t * y * t⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinfs]
      exact ⟨hmemX, hmemθ⟩
    simpa using hmem
  have ht_conj : t * y * t⁻¹ = y := by
    have h := congrArg (fun z => z * y) hz1
    simpa [mul_assoc] using h
  have hty : t * y = y * t := by
    have h := congrArg (fun z => z * t) ht_conj
    simpa [mul_assoc] using h
  exact hty.symm

namespace Ctx

variable {A L : Subgroup G} {c d : G}

private theorem exists_thetaComponent_le_x₀
    (h48 : Sec4.Item4_8) (h : Ctx A c L d) :
    ∃ K ∈ thetaComponentsAt 3 d, x₀ L d ≤ K := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.sec13Data
  have hA : Late.IsE27 A := h.isE27
  have hdA : d ∈ A := h.mem_d
  have hd1 : d ≠ 1 := h.ne_d
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hD.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1)
  obtain ⟨hdL, S3, hdS, hSd⟩ := Proof15Res4.isThreeCentralIn_of_isZCentral h.zCentral
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs h.conf.j2 hdL hd1
    ⟨S3, hdS, hSd⟩
  exact exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hD.mem_A hdA hD.ne_one
    hD.mem_lA.1 hJq

private theorem omega_case2_first_alt {A : Subgroup G} {c d : G} (hA : Late.IsE27 A)
    (hcA : c ∈ A) (hc1 : c ≠ 1) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : d ∉ Subgroup.zpowers c)
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hab : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A))
    (h9 : Nat.card (oThreeWStar A) = 9)
    (hΩP : omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c))
    (h3 : (omegaA A).ncard = 3)
    (htriple : omegaA A = {Subgroup.zpowers c, Subgroup.zpowers (c * d),
      Subgroup.zpowers (c * d ^ 2)}) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
      (omegaA A).ncard = 3 ∧
      (∀ F ∈ omegaA A, ∃ b ∈ Subgroup.zpowers d, F = Subgroup.zpowers (c * b)) ∧
      ∃ w ∈ oThreeWPre A, (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom =
        Subgroup.zpowers (c * d) := by
  refine ⟨hWd, h3, ?_, ?_⟩
  · intro F hF
    rw [htriple] at hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    rcases hF with rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [mul_one]⟩
    · exact ⟨d, Subgroup.mem_zpowers d, rfl⟩
    · exact ⟨d ^ 2, pow_mem (Subgroup.mem_zpowers d) 2, rfl⟩
  · exact Proof15Res4.exists_conj_of_case2 hA hcA hc1 hdA hd1 hdc hWd hab h9
      (Or.inl ⟨hΩP, h3⟩) d (Subgroup.mem_zpowers d)

private theorem x₀_inf_theta_eq_bot
    (h : Ctx A c L d) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d) :
    x₀ L d ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ := by
  have hθK_le : inSubgroup (aschbacherSolvableCore 3) K ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) :=
    Res7MemFix.theta_le_of_mem hK
  rw [eq_bot_iff]
  calc x₀ L d ⊓ inSubgroup (aschbacherSolvableCore 3) K
      ≤ x₀ L d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) :=
        inf_le_inf_left _ hθK_le
    _ = ⊥ := h.inf_pPrimeCoreOf_eq_bot

private theorem omega_case2_second_alt_aux
    (h : Ctx A c L d) (hA : Late.IsE27 A)
    (hB9 : Nat.card (A ⊓ L : Subgroup G) = 9) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hKθ : K = x₀ L d ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    (hJK : x₀ L d ≤ K) {a : G} (haA : a ∈ A) (haK : a ∈ K) (ha1 : a ≠ 1)
    (haL : a ∉ L) :
    ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) K, ∃ x ∈ x₀ L d,
      t * x = c ∧ t ∈ Subgroup.centralizer (x₀ L d : Set G) ∧
        x ∈ Subgroup.zpowers d := by
  have hAeq : A = Subgroup.zpowers a ⊔ (A ⊓ L) :=
    Ronan148B.eq_zpowers_sup_inf' hA haA ha1 haL hB9
  have hAK : A ≤ K := by
    rw [hAeq]
    exact sup_le (Subgroup.zpowers_le.mpr haK) (h.inf_le_x₀.trans hJK)
  have hcK : c ∈ K := hAK h.sec13Data.mem_A
  have hX_le_N : x₀ L d ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    hJK.trans (Sec17.Proof171Steps.le_normalizer_theta K)
  have hcSup : c ∈ (x₀ L d ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) := by
    rw [← hKθ]
    exact hcK
  have hcprod : c ∈ (inSubgroup (aschbacherSolvableCore 3) K : Set G) * (x₀ L d : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      (inSubgroup (aschbacherSolvableCore 3) K) (x₀ L d) hX_le_N, sup_comm]
    exact hcSup
  obtain ⟨t, htθ, x, hxX, hctx⟩ := hcprod
  have hinfs := x₀_inf_theta_eq_bot h hK
  have hcCentX : c ∈ Subgroup.centralizer (x₀ L d : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.x₀_le_centralizer hy)
  have htCentX : t ∈ Subgroup.centralizer (x₀ L d : Set G) :=
    mem_centralizer_of_mul_mem_sup hctx hcCentX hxX htθ hX_le_N hinfs
  have hxCentX : x ∈ Subgroup.centralizer (x₀ L d : Set G) := by
    have hx_eq : x = t⁻¹ * c := by
      rw [← hctx]
      group
    rw [hx_eq]
    exact (Subgroup.centralizer (x₀ L d : Set G)).mul_mem
      ((Subgroup.centralizer (x₀ L d : Set G)).inv_mem htCentX) hcCentX
  have hxZ : x ∈ Subgroup.zpowers d := by
    rw [← h.center_x₀]
    refine ⟨⟨x, hxX⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxCentX y y.2)
  exact ⟨t, htθ, x, hxX, hctx, htCentX, hxZ⟩

private theorem omega_case2_second_alt
    (h : Ctx A c L d) (hA : Late.IsE27 A) (hcL : c ∉ L)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) (hB9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hKθ : K = x₀ L d ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    (hJK : x₀ L d ≤ K) {a : G} (haA : a ∈ A) (haK : a ∈ K) (ha1 : a ≠ 1)
    (haL : a ∉ L) : False := by
  obtain ⟨t, htθ, x, hxX, hctx, htCentX, hxZ⟩ :=
    omega_case2_second_alt_aux h hA hB9 hK hKθ hJK haA haK ha1 haL
  have hdA : d ∈ A := h.mem_d
  have hxA : x ∈ A := Subgroup.zpowers_le.mpr hdA hxZ
  have htA : t ∈ A := by
    have ht_eq : t = c * x⁻¹ := by
      rw [← hctx]
      group
    rw [ht_eq]
    exact A.mul_mem h.sec13Data.mem_A (A.inv_mem hxA)
  have htθ3 : ¬ 3 ∣ Nat.card ↥(inSubgroup (aschbacherSolvableCore 3) K) :=
    (Sec6.theta_solvable_and_not_dvd K).2
  have ht1 : t = 1 :=
    CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr htθ3)
      (orderOf_dvd_of_pow_eq_one (hA.1.2 t htA))
      (by rw [← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htθ))
  have hcx : c = x := by
    calc c = t * x := hctx.symm
      _ = 1 * x := by rw [ht1]
      _ = x := one_mul x
  exact hcL (by rw [hcx]; exact Subgroup.zpowers_le.mpr h.mem_L hxZ)

private theorem omega_case2_case3 (h : Ctx A c L d) (hdΩ : Subgroup.zpowers d ∉ omegaA A)
    (hA : Late.IsE27 A) (hcA : c ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hcL : c ∉ L) (hB9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hAsup : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h12 : (omegaA A).ncard = 12) : False := by
  have hdB : d ∈ A ⊓ L := ⟨hdA, hdL⟩
  have hcB : c ∉ A ⊓ L := fun hh => hcL hh.2
  have hlines := ON134.ncard_lines_ne hA.1 hcA hAsup hcB hB9 hdB hd1
  have hsub : omegaA A ⊆
      {F : Subgroup G | F ≤ A ∧ Nat.card F = 3 ∧ F ≠ Subgroup.zpowers d} := by
    intro F hF
    obtain ⟨hFA, hF3, -⟩ := mem_omegaA_iff.mp hF
    exact ⟨hFA, hF3, fun heq => hdΩ (heq ▸ hF)⟩
  have hΩeq : omegaA A =
      {F : Subgroup G | F ≤ A ∧ Nat.card F = 3 ∧ F ≠ Subgroup.zpowers d} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hlines, h12]) (Set.toFinite _)
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
    card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
  have hnotle : ¬ A ⊓ L ≤ Subgroup.zpowers d := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hB9, hd3] at hcard
    omega
  obtain ⟨y, hyB, hyd⟩ := Set.not_subset.mp hnotle
  have hy1 : y ≠ 1 := fun hh => hyd (hh.symm ▸ Subgroup.one_mem _)
  have hy3 : Nat.card (Subgroup.zpowers y) = 3 :=
    card_zpowers_of_pow_three (hA.1.2 y hyB.1) hy1
  have hyΩ : Subgroup.zpowers y ∈ omegaA A := by
    rw [hΩeq]
    exact ⟨Subgroup.zpowers_le.mpr hyB.1, hy3, fun heq => hyd (heq ▸ Subgroup.mem_zpowers y)⟩
  exact (h.off _ hyΩ (Subgroup.zpowers_le.mpr ⟨hyB.1, hyB.2⟩)).elim

theorem omega_case2
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
      (omegaA A).ncard = 3 ∧
      (∀ F ∈ omegaA A, ∃ b ∈ Subgroup.zpowers d, F = Subgroup.zpowers (c * b)) ∧
      ∃ w ∈ oThreeWPre A, (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom =
        Subgroup.zpowers (c * d) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hA : Late.IsE27 A := h.isE27
  have hcA : c ∈ A := hD.mem_A
  have hc1 : c ≠ 1 := hD.ne_one
  have hdA : d ∈ A := h.mem_d
  have hd1 : d ≠ 1 := h.ne_d
  have hdL : d ∈ L := h.mem_L
  obtain ⟨hcL, hB9, hAsup⟩ := j2_point_facts hD h.conf.j2
  have hcd : c ∉ Subgroup.zpowers d := fun hh => hcL (Subgroup.zpowers_le.mpr hdL hh)
  have hdc : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA hd1 hcA hcd
  obtain ⟨K, hK, hJK⟩ := exists_thetaComponent_le_x₀ h48 h
  rcases h134 G A c L hD h.conf.j2 d hdA hd1 h.zCentral K hK hJK with
    ⟨-, -, hΩ1⟩ | ⟨hKθ, -, hWd, hab, h9, -, hΩ2⟩ | ⟨-, hWd, hΩ3, h12⟩
  · exact absurd hΩ1 h.conf.omega_ne
  · rcases hΩ2 with ⟨hΩP, h3⟩ | ⟨I, hI, hdI, htcI, a, haAK, had, hΩe, h6, La, hLa, hJLa⟩
    · obtain ⟨-, hcbΩ⟩ := h.omega_facts h134 h48
      have h1Ω : Subgroup.zpowers c ∈ omegaA A := by
        simpa using hcbΩ 1 (one_mem _)
      have hcdΩ : Subgroup.zpowers (c * d) ∈ omegaA A := hcbΩ d (Subgroup.mem_zpowers d)
      have hcd2Ω : Subgroup.zpowers (c * d ^ 2) ∈ omegaA A :=
        hcbΩ (d ^ 2) (pow_mem (Subgroup.mem_zpowers d) 2)
      exact omega_case2_first_alt hA hcA hc1 hdA hd1 hdc hWd hab h9 hΩP h3
        (omegaA_eq_triple hA hcA hdA hd1 hcd h1Ω hcdΩ hcd2Ω h3)
    · have ha1 : a ≠ 1 := fun hh => had (hh.symm ▸ Subgroup.one_mem _)
      by_cases haL : a ∈ L
      · have haΩ : Subgroup.zpowers a ∈ omegaA A := by
          rw [hΩe]
          refine Set.mem_union_right _ ⟨1, one_mem _, ?_⟩
          have e : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
            ext y
            simp
          rw [e, Subgroup.map_id]
        exact (h.off _ haΩ (Subgroup.zpowers_le.mpr ⟨haAK.1, haL⟩)).elim
      · exact (omega_case2_second_alt h hA hcL hK hB9 hKθ hJK haAK.1 haAK.2 ha1 haL).elim
  · exact (omega_case2_case3 h (h.omega_facts h134 h48).1 hA hcA hdA hd1 hdL hcL hB9
      hAsup h12).elim

theorem omega_le_closure
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d) :
    ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c, d} := by
  intro F hF
  obtain ⟨-, -, hpt, -⟩ := omega_case2 h134 h48 h
  obtain ⟨b, hb, rfl⟩ := hpt F hF
  rw [Subgroup.zpowers_le]
  have hc : c ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert c {d})
  have hd : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  exact Subgroup.mul_mem _ hc (Subgroup.zpowers_le.mpr hd hb)

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
