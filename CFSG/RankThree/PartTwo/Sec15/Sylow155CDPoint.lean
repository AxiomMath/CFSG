module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Fpf
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.Ronan138SMain
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Point


private theorem isZCentral_of_isThreeCentralIn {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hd1 : d ≠ 1) (hd : IsThreeCentralIn L d) : IsZCentral L d := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S, hS1, hS2⟩ := hd
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hS1 hS2
  exact ⟨_, hSy, hZ⟩

private theorem orbitIn_subset_omegaA {A : Subgroup G} {b : G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) :
    orbitIn (oThreeWPre A) (Subgroup.zpowers b) ⊆ omegaA A := by
  rintro F ⟨π, hπ, rfl⟩
  have hπA : π ∈ Subgroup.normalizer (A : Set G) := Subgroup.map_subtype_le _ hπ
  exact (map_conj_mem_omegaA_iff hπA).mpr hbΩ

private theorem apply_eq_of_normalizer_le {A : Subgroup G} (hA : Late.IsE27 A) {e : G}
    (heA : e ∈ A)
    (hWe : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G))
    (hPi : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) {σ : MulAut ↥A}
    (hσ : σ ∈ oThreeWStar A) : σ ⟨e, heA⟩ = ⟨e, heA⟩ := by
  obtain ⟨s, hs, -, hsσ⟩ := Ronan152SL25.exists_mem_oThreeWPre hσ
  have hmem : s * e * s⁻¹ ∈ Subgroup.zpowers e :=
    (Subgroup.mem_normalizer_iff.mp (hWe hs) e).mp (Subgroup.mem_zpowers e)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : σ ⟨e, heA⟩ = ⟨e, heA⟩ ^ k := by
    apply Subtype.ext
    rw [← hsσ, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow]
    exact hk.symm
  exact Ronan138S.apply_eq_of_mem_zpowers_of_pow_three σ (hPi.2 σ hσ)
    (Subtype.ext (hA.1.2 e heA)) (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'.symm⟩)

theorem zpowers_eq_of_ncard_six (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h6 : (omegaA A).ncard = 6) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {D L' : Subgroup G} {b' d' : G}
    (hD : IsHyperplane A D) (hc' : IsLBConfig A D b' d' L') :
    Subgroup.zpowers d' = Subgroup.zpowers d := by
  have hA : Late.IsE27 A := h.isE27'
  have h134x : ∀ {B Lb : Subgroup G} {b d : G}, IsHyperplane A B → IsLBConfig A B b d Lb →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 := by
    intro B Lb b d hB hc
    rcases Ronan152SL25.omegaA_cases h134 h48 h hB hc with h1 | ⟨hWd, hPi, hPi9, -⟩ | h12
    · rw [h1, Set.ncard_singleton] at h6
      omega
    · exact ⟨hWd, hPi, hPi9⟩
    · omega
  obtain ⟨hWd, hPi, hPi9⟩ := h134x hB hc
  obtain ⟨hWd', -, -⟩ := h134x hD hc'
  obtain ⟨hbΩ, hLb, hJb, -, hbA, hb1, hdA, hd1, hdc, hdb⟩ :=
    Ronan152SL25.lbConfig_facts hA hB hc
  obtain ⟨-, -, hJ', -, -, -, hd'A, hd'1, hd'c, -⟩ := Ronan152SL25.lbConfig_facts hA hD hc'
  obtain ⟨σ, hσPi, hσ1, hσb, hσd⟩ := Ronan152SL25.exists_fix_of_ncard_lt hA hdA hbA hWd hPi hPi9
    (by omega) (orbitIn_subset_omegaA hbΩ)
  have hσd' : σ ⟨d', hd'A⟩ = ⟨d', hd'A⟩ := apply_eq_of_normalizer_le hA hd'A hWd' hPi hσPi
  have hbd : b ∉ Subgroup.zpowers d := Proof152ResW.not_mem_zpowers_symm hA hb1 hdA hdb
  have hd'B : d' ∈ Subgroup.closure ({b, d} : Set G) :=
    Ronan152SL25.mem_closure_of_apply_eq hA hσ1 hbA hdA hd1 hbd hσb hσd hσd'
  have hd'Ω : Subgroup.zpowers d' ∉ omegaA A :=
    Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
      (Item148HJ.sec14Std_of_isLBConfig h hc') hJ' hd'A hd'1 hd'c
  by_contra hne
  have hBA : Subgroup.closure ({b, d} : Set G) ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hd'3 : Nat.card (Subgroup.zpowers d') = 3 := Proof152WE.card_zpowers_eq_three hA hd'A hd'1
  obtain ⟨k, hk, hkeq⟩ := Proof152ResW.exists_eq_zpowers_mul hA hbA hdA hd1 hbd
    (Subgroup.zpowers_le.mpr (hBA hd'B)) hd'3 hne
  have hΩb : omegaA A ≠ {Subgroup.zpowers b} := by
    intro h1
    rw [h1, Set.ncard_singleton] at h6
    omega
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  have hdZ : IsZCentral Lb d := isZCentral_of_isThreeCentralIn hJb hd1 hdc
  obtain ⟨-, hpts⟩ := Proof15Res11.omega_facts h134 h48 hdata hJb hΩb hdA hd1 hdZ
  exact hd'Ω (hkeq ▸ hpts k hk)

theorem mem_of_forall_not_mem_omegaA (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hΩ : omegaA A ≠ {Subgroup.zpowers b}) {F : Subgroup G} (hF : IsHyperplane A F)
    (hfree : ∀ x ∈ F, x ≠ 1 → Subgroup.zpowers x ∉ omegaA A) : d ∈ F := by
  by_contra hdF
  have hA : Late.IsE27 A := h.isE27'
  obtain ⟨hbΩ, hLb, hJb, -, hbA, hb1, hdA, hd1, hdc, hdb⟩ :=
    Ronan152SL25.lbConfig_facts hA hB hc
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  have hdZ : IsZCentral Lb d := isZCentral_of_isThreeCentralIn hJb hd1 hdc
  obtain ⟨-, hpts⟩ := Proof15Res11.omega_facts h134 h48 hdata hJb hΩ hdA hd1 hdZ
  have hbd : b ∉ Subgroup.zpowers d := Proof152ResW.not_mem_zpowers_symm hA hb1 hdA hdb
  have hAeq : F ⊔ Subgroup.zpowers d = A :=
    Item148HJ.sup_zpowers_eq_of_isHyperplane hF hdA hdF
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hFn : F ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    intro f hf
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (hcomm d hdA f (hF.1 hf) : Commute d f) k).eq
  have hbmem : b ∈ ((F ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [hAeq]
    exact hbA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F (Subgroup.zpowers d) hFn] at hbmem
  obtain ⟨f, hf, z, hz, hfz'⟩ := hbmem
  have hz' : z ∈ Subgroup.zpowers d := hz
  have hfz : f * z = b := hfz'
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [one_mul] at hfz
    exact hbd (hfz ▸ hz')
  exact hfree f hf hf1 (by
    rw [eq_mul_inv_of_mul_eq hfz]
    exact hpts z⁻¹ (inv_mem hz'))

end Point

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
