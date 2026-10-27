module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155CDPoint
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Ronan148QInv
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section CP


private theorem isZCentral_of_isThreeCentralIn {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hd1 : d ≠ 1) (hd : IsThreeCentralIn L d) : IsZCentral L d := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S, hS1, hS2⟩ := hd
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hS1 hS2
  exact ⟨_, hSy, hZ⟩

private theorem map_mem_lbMembers_of_ne {A L : Subgroup G} {c a : G} (hS : Sec14Std G A c L)
    {K K₁ : Subgroup G} (hK : K ∈ Ronan148D.lbMembers A a) (hK₁ : K₁ ∈ Ronan148D.lbMembers A a)
    (hne₁ : K₁ ≠ K) {g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G)) :
    K.map (MulAut.conj g).toMonoidHom ∈ Ronan148D.lbMembers A a := by
  by_contra hK'X
  set K' := K.map (MulAut.conj g).toMonoidHom
  have hne : K' ≠ K := fun heq => hK'X (heq ▸ hK)
  have hne₁' : K' ≠ K₁ := fun heq => hK'X (heq ▸ hK₁)
  obtain ⟨hKa, D, b, d, Lb, hD, haD, hc, hDK⟩ := hK
  obtain ⟨hK₁a, D₁, b₁, d₁, L₁, hD₁, haD₁, hc₁, hD₁K⟩ := hK₁
  have hK' : K' ∈ thetaComponentsAt 3 a := Sec6.map_conj_mem_thetaComponentsAt hg hKa
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hKa
  have hAS := Ronan148D.le_sup_of_ne hS hKa hK₁a (Ne.symm hne₁) hD haD hc hDK hD₁ haD₁ hc₁ hD₁K
  exact Ronan148D.false_of_le_commute hS hD hc hKa hDK hg hAS
    (sup_le hKC (le_centralizer_of_mem_thetaComponentsAt hK₁a))
    fun s hs k hk => Ronan148D.commutator_mem_theta_of_ne_sup hK' hKa hK₁a hne hne₁' hk hs

theorem exists_cp_of_ncard_six (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c d : G}
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdZ : IsZCentral L d) (hdA : d ∈ A) (hd1 : d ≠ 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    {a : G} (haK : a ∈ K) (haA : a ∈ A) (had : a ∉ Subgroup.zpowers d)
    (haΩ : Subgroup.zpowers a ∈ omegaA A) (h6 : (omegaA A).ncard = 6) {La : Subgroup G}
    (hLa : lA A a = {La})
    (hJa : Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ X : Subgroup G, X ≤ Subgroup.centralizer ({d} : Set G) ∧ Ronan148Q.Inv143Q A d d X ∧
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  have hS : Sec14Std G A c L := h.toSec14Std
  have hA : Late.IsE27 A := hS.isE27'
  have ha3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdL : d ∈ L := Proof15Res4.mem_of_isZCentral hdZ
  have hB : IsHyperplane A (Subgroup.closure {c, d}) :=
    Proof15Res11.isHyperplane_of h hJ hdA hd1 hdL
  have hcd : IsLBConfig A (Subgroup.closure {c, d}) c d L := Proof15Res11.isLBConfig_of h hJ hdZ
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hLaA : La ∈ lA A a := by
    rw [hLa]
    exact Set.mem_singleton La
  have hRa : Sec15R G A a La := Proof1511.sec15R_point h haΩ hLaA
  obtain ⟨d', hd'A, hd'1, hd'L, S, hd'S, hSd'⟩ :=
    exists_three_central_of_j2 hRa.toSec14Std.toSec13Data hJa
  have hd'Z : IsZCentral La d' := isZCentral_of_isThreeCentralIn hJa hd'1 ⟨hd'L, S, hd'S, hSd'⟩
  have hca' : IsLBConfig A (Subgroup.closure {a, d'}) a d' La :=
    Proof15Res11.isLBConfig_of hRa hJa hd'Z
  have hBa' : IsHyperplane A (Subgroup.closure {a, d'}) :=
    Proof15Res11.isHyperplane_of hRa hJa hd'A hd'1 hd'L
  have hdd' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_ncard_six h134 h48 hS h6 hB hcd hBa' hca'
  have hdZa : IsZCentral La d := by
    obtain ⟨S₀, hS₀, hZ⟩ := hd'Z
    exact ⟨S₀, hS₀, hZ.trans hdd'⟩
  have hdLa : d ∈ La := Proof15Res4.mem_of_isZCentral hdZa
  have hB' : IsHyperplane A (Subgroup.closure {a, d}) :=
    Proof15Res11.isHyperplane_of hRa hJa hdA hd1 hdLa
  have hca : IsLBConfig A (Subgroup.closure {a, d}) a d La :=
    Proof15Res11.isLBConfig_of hRa hJa hdZa
  have hdB' : d ∈ Subgroup.closure ({a, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have haB' : a ∈ Subgroup.closure ({a, d} : Set G) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hda : d ∉ Subgroup.zpowers a := Proof152ResW.not_mem_zpowers_symm hA hd1 haA had
  obtain ⟨K₂, hK₂, hK₂res⟩ := Desc143X.exists_mem_le_residual h48 hS hB' hca hdB' hd1 hda
  have hres₁ := Item148HJ.lB_eq_residual hS hB hcd
  have hres₂ := Item148HJ.lB_eq_residual hS hB' hca
  have hDK₁ : lB A (Subgroup.closure {c, d}) ≤ K := by
    rw [hres₁]
    exact hLK
  have hDK₂ : lB A (Subgroup.closure {a, d}) ≤ K₂ := by
    rw [hres₂]
    exact hK₂res
  have hKmem : K ∈ Ronan148D.lbMembers A d := ⟨hK, _, c, d, L, hB, hdB, hcd, hDK₁⟩
  have hK₂mem : K₂ ∈ Ronan148D.lbMembers A d := ⟨hK₂, _, a, d, La, hB', hdB', hca, hDK₂⟩
  have hdK : d ∈ K :=
    hLK (Item148HJ.inf_le_residual hS hB hcd (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩))
  have hdK₂ : d ∈ K₂ :=
    hK₂res (Item148HJ.inf_le_residual hS hB' hca (Subgroup.mem_inf.mpr ⟨hdA, hdLa⟩))
  have hty : ∀ {D Lb : Subgroup G} {b : G} {K' : Subgroup G}, IsHyperplane A D →
      IsLBConfig A D b d Lb → K' ∈ thetaComponentsAt 3 d → lB A D ≤ K' →
      K' = lB A D ⊔ inSubgroup (aschbacherSolvableCore 3) K' ∧
        Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)) := by
    intro D Lb b K' hD hc hK' hDK'
    rcases Ronan148D.member_cases h134 hS hD hc rfl hK' hDK' with ⟨hKeq, htc, -⟩ | ⟨-, h12⟩
    · exact ⟨hKeq, htc⟩
    · omega
  obtain ⟨hKeq₁, htc₁⟩ := hty hB hcd hK hDK₁
  obtain ⟨hKeq₂, htc₂⟩ := hty hB' hca hK₂ hDK₂
  have hne : K ≠ K₂ := by
    intro hKK
    have hsup₁ : lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) K = K :=
      hKeq₁.symm
    have hsup₂ : lB A (Subgroup.closure {a, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) K = K := by
      rw [hKK]
      exact hKeq₂.symm
    have hdC : d ∈ Subgroup.centralizer (lB A (Subgroup.closure {c, d}) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (lB_le_centralizer A _ hx) d hdB).symm
    have haC : a ∈ Subgroup.centralizer (lB A (Subgroup.closure {a, d}) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (lB_le_centralizer A _ hx) a haB').symm
    have hdθ : d ∈ Sec4.thetaQuotCentralizer K :=
      Sec12.mem_thetaQuotCentralizer_of_sup_eq hDK₁ hsup₁ (Subgroup.le_normalizer hdK) hdC
    have haθ : a ∈ Sec4.thetaQuotCentralizer K :=
      Sec12.mem_thetaQuotCentralizer_of_sup_eq (by rw [hKK]; exact hDK₂) hsup₂
        (Subgroup.le_normalizer haK) haC
    have hBθ : Subgroup.closure ({a, d} : Set G) ≤ Sec4.thetaQuotCentralizer K := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact haθ
      · exact hdθ
    have hBK : Subgroup.closure ({a, d} : Set G) ≤ K := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact haK
      · exact hdK
    have hB9 : Nat.card (Subgroup.closure ({a, d} : Set G)) = 9 := by
      have h1 := hB'.2
      rw [hA.2] at h1
      omega
    have hB3 : IsPGroup 3 (Subgroup.closure ({a, d} : Set G)) :=
      IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
    have hcard := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 hBθ
    rw [inf_eq_left.mpr hBK, hB9, htc₁.1] at hcard
    omega
  have hmem2 : ∀ K₃ ∈ Ronan148D.lbMembers A d, K₃ = K ∨ K₃ = K₂ := fun K₃ hK₃ =>
    Ronan148D.eq_or_eq_of_mem_lbMembers hS hKmem hK₂mem hK₃ hne
  have hsSup : sSup (Ronan148D.lbMembers A d) = K ⊔ K₂ := by
    have h𝒳 : Ronan148D.lbMembers A d = {K, K₂} := by
      ext K₃
      constructor
      · intro hK₃
        rcases hmem2 K₃ hK₃ with h3 | h3
        · rw [h3]
          exact Set.mem_insert _ _
        · rw [h3]
          exact Set.mem_insert_of_mem _ rfl
      · rintro (h3 | h3)
        · rw [h3]
          exact hKmem
        · rw [h3]
          exact hK₂mem
    rw [h𝒳, sSup_pair]
  have hall : ∀ K₃ ∈ Ronan148D.lbMembers A d, ∀ g ∈ Subgroup.centralizer ({d} : Set G),
      K₃.map (MulAut.conj g).toMonoidHom ∈ Ronan148D.lbMembers A d := by
    intro K₃ hK₃ g hg
    rcases hmem2 K₃ hK₃ with h3 | h3
    · rw [h3]
      exact map_mem_lbMembers_of_ne hS hKmem hK₂mem (Ne.symm hne) hg
    · rw [h3]
      exact map_mem_lbMembers_of_ne hS hK₂mem hKmem hne hg
  refine ⟨K ⊔ K₂, sup_le (le_centralizer_of_mem_thetaComponentsAt hK)
    (le_centralizer_of_mem_thetaComponentsAt hK₂), Or.inl ?_, ?_⟩
  · have hN := Ronan148Q.le_normalizer_sup_sSup_of hall
    rwa [hsSup] at hN
  · exact Ronan148D.isCentralProductA6Covers_sup ha3 hd1 hK hK₂ hne hdK hdK₂ htc₁ htc₂

end CP

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
