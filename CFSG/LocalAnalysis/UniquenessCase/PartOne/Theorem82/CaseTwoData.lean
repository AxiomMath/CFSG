module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CenterNine
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPerfect
import CFSG.RankThree.OddKernel.CentralCoverComponentModels
import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4End
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped Pointwise
open CFSG.Yardstones.Mf4cdcdf2e013 (Asc83CComponent Hyp81 QuasisimpleModOTwo)

variable {G : Type} [Group G] [Finite G]

namespace Ctx812

theorem exists_sylowThreeData (c : Ctx812 G) (h812 : ¬ QuasisimpleModOTwo c.L)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) :
    ∃ d : SylowThreeData G, d.M = c.S.M ∧ d.L = c.L ∧ d.S = P ⊓ c.L ∧
      Function.Injective d.Lf ∧ (∀ i, Asc83CComponent c.S.M (d.Lf i)) ∧
      ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases c.hyp81.2.2.2.2 with hq | ⟨L₁, L₂, L₃, hLjoin, hL₁L, hL₂L, hL₃L,
    hcomp₁, hr₁, hcomp₂, hr₂, hcomp₃, hr₃, -⟩
  · exact absurd hq h812
  let Lf : Fin 3 → Subgroup G := ![L₁, L₂, L₃]
  have hcompLf : ∀ i, Asc83CComponent c.S.M (Lf i) := by
    intro i
    fin_cases i
    · simpa [Lf] using hcomp₁
    · simpa [Lf] using hcomp₂
    · simpa [Lf] using hcomp₃
  have hrankLf : ∀ i, CFSG.Open.pRank 3 (Lf i) = 1 := by
    intro i
    fin_cases i
    · simpa [Lf] using hr₁
    · simpa [Lf] using hr₂
    · simpa [Lf] using hr₃
  have hconj_mem : ∀ (m : G) (hm : m ∈ c.S.M) (Y : Subgroup G),
      Asc83CComponent c.S.M Y → CFSG.Open.pRank 3 Y = 1 →
      Y.map (MulAut.conj m).toMonoidHom = L₁ ∨
        Y.map (MulAut.conj m).toMonoidHom = L₂ ∨
          Y.map (MulAut.conj m).toMonoidHom = L₃ :=
    fun m hm Y hY hYrank =>
      c.map_conj_mem_of_asc83CComponent hm hLjoin hcomp₁ hcomp₂ hcomp₃ hY hYrank
  have hLnorm : ∀ i j, Lf j ≤ Subgroup.normalizer (Lf i : Set G) := by
    intro i j
    let T : Type := Set.range Lf
    have hTcomp : ∀ L : T, Asc83CComponent c.S.M L.1 := by
      rintro ⟨L, k, rfl⟩
      exact hcompLf k
    have hTrank : ∀ L : T, CFSG.Open.pRank 3 L.1 = 1 := by
      rintro ⟨L, k, rfl⟩
      exact hrankLf k
    letI : MulAction ↥c.S.M T :=
      { smul m L :=
          ⟨L.1.map (MulAut.conj (m : G)).toMonoidHom, by
            rcases hconj_mem (m : G) m.2 L.1 (hTcomp L) (hTrank L) with h | h | h
            · exact ⟨0, by simpa [Lf] using h.symm⟩
            · exact ⟨1, by simpa [Lf] using h.symm⟩
            · exact ⟨2, by simpa [Lf] using h.symm⟩⟩
        one_smul L := by
          apply Subtype.ext
          have h1 : (MulAut.conj (((1 : ↥c.S.M) : G))).toMonoidHom = MonoidHom.id G := by
            ext g
            simp
          show L.1.map (MulAut.conj (((1 : ↥c.S.M) : G))).toMonoidHom = L.1
          rw [h1, Subgroup.map_id]
        mul_smul a b L := by
          apply Subtype.ext
          show L.1.map (MulAut.conj (((a * b : ↥c.S.M) : G))).toMonoidHom =
            (L.1.map (MulAut.conj (b : G)).toMonoidHom).map
              (MulAut.conj (a : G)).toMonoidHom
          rw [Subgroup.map_map]
          congr 1
          ext g
          simp [mul_assoc] }
    let ρ : ↥c.S.M →* Equiv.Perm T := MulAction.toPermHom ↥c.S.M T
    haveI hperfLj : Group.IsPerfect ↥(Lf j) :=
      Subgroup.isPerfect_iff.mpr (hcompLf j).2.2.1
    let ej : ↥((Lf j).subgroupOf c.S.M) ≃* ↥(Lf j) :=
      Subgroup.subgroupOfEquivOfLe (hcompLf j).1
    haveI hperfj : Group.IsPerfect ↥((Lf j).subgroupOf c.S.M) :=
      Group.IsPerfect.ofSurjective (f := ej.symm.toMonoidHom) ej.symm.surjective
    let eT : Fin 3 → T := fun i => ⟨Lf i, ⟨i, rfl⟩⟩
    have hsurjT : Function.Surjective eT := by
      rintro ⟨L, i, rfl⟩
      exact ⟨i, rfl⟩
    haveI : Finite T := Finite.of_surjective eT hsurjT
    have hTcard : Nat.card T ≤ 4 := by
      have h : Nat.card T ≤ 3 := by
        simpa using Nat.card_le_card_of_surjective eT hsurjT
      omega
    haveI : Finite ↥(Set.univ : Set T) := Finite.of_equiv T (Equiv.Set.univ T).symm
    have hcardT : Nat.card (Set.univ : Set T) ≤ 4 := by
      rw [Nat.card_congr (Equiv.Set.univ T)]
      exact hTcard
    have hfix : ∀ h ∈ (Lf j).subgroupOf c.S.M, ∀ y ∈ (Set.univ : Set T), ρ h y = y :=
      CFSG.RankThree.PartTwo.Sec8.Item8KFacts3.fixes_of_isPerfect ρ hperfj hcardT
        (by intro h _ y _; exact Set.mem_univ y)
    have hfixpt : ∀ (L : Subgroup G), L ∈ Set.range Lf → ∀ x ∈ Lf j,
        L.map (MulAut.conj x).toMonoidHom = L := by
      intro L hL x hx
      let y : T := ⟨L, hL⟩
      have hxM : x ∈ c.S.M := (hcompLf j).1 hx
      have hmem : (⟨x, hxM⟩ : ↥c.S.M) ∈ (Lf j).subgroupOf c.S.M :=
        Subgroup.mem_subgroupOf.mpr hx
      have hy := hfix ⟨x, hxM⟩ hmem y (Set.mem_univ y)
      have hval : (ρ ⟨x, hxM⟩ y).1 = L.map (MulAut.conj x).toMonoidHom := rfl
      have h' := congrArg Subtype.val hy
      rwa [hval] at h'
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hfixpt (Lf i) ⟨i, rfl⟩ x hx
  have hpair : ∀ a b : Fin 3, (Lf a ⊔ Lf b) = c.L → False := by
    intro a b hHL
    let A : Subgroup G := Lf a
    let B : Subgroup G := Lf b
    let H : Subgroup G := A ⊔ B
    have hAB : B ≤ Subgroup.normalizer (A : Set G) := hLnorm a b
    haveI : (A.subgroupOf H).Normal := by
      have h := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := B) (N := A) hAB
      rw [sup_comm] at h
      simpa [H] using h
    have hArank : CFSG.pRank 3 ↥(A.subgroupOf H) = 1 := by
      rw [CFSG.pRank_congr_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ H)) 3,
        CFSG.SectionRank.pRank_coe_eq_openPRank, hrankLf a]
    have hBrank : CFSG.pRank 3 ↥B = 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank, hrankLf b]
    let ψ : ↥B →* ↥H ⧸ A.subgroupOf H :=
      (QuotientGroup.mk' (A.subgroupOf H)).comp (Subgroup.inclusion le_sup_right)
    have hψ : Function.Surjective ψ := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf H) z
      have hxmem : (x : G) ∈ (A : Set G) * (B : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hAB]
        exact x.2
      obtain ⟨a, ha, b, hb, hxab⟩ := hxmem
      refine ⟨⟨b, hb⟩, ?_⟩
      change QuotientGroup.mk' (A.subgroupOf H)
          (Subgroup.inclusion le_sup_right (⟨b, hb⟩ : B)) =
        QuotientGroup.mk' (A.subgroupOf H) x
      have hx : x = Subgroup.inclusion le_sup_left (⟨a, ha⟩ : A) *
          Subgroup.inclusion le_sup_right (⟨b, hb⟩ : B) := by
        apply Subtype.ext
        simpa using hxab.symm
      rw [hx, map_mul]
      have hker : QuotientGroup.mk' (A.subgroupOf H)
          (Subgroup.inclusion le_sup_left (⟨a, ha⟩ : A)) = 1 :=
        (QuotientGroup.eq_one_iff
          (Subgroup.inclusion le_sup_left (⟨a, ha⟩ : A))).mpr
          (Subgroup.mem_subgroupOf.mpr ha)
      rw [hker, one_mul]
    have hQrank : CFSG.pRank 3 (↥H ⧸ A.subgroupOf H) ≤ 1 :=
      CFSG.Quasithin.H13.Ch4.L436.pRank_le_one_of_surjective'
        Nat.prime_three (by norm_num) ψ hψ hBrank.le
    have hleadd := CFSG.RankThree.OddKernel.pRank_le_add_of_normal
      (p := 3) Nat.prime_three (A.subgroupOf H)
    have hHrank : CFSG.pRank 3 ↥H = 3 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
        show H = c.L from hHL, c.pRank_three_L]
    omega
  have hLjoinLf : c.L = Lf 0 ⊔ Lf 1 ⊔ Lf 2 := by simpa [Lf] using hLjoin
  have hne01 : Lf 0 ≠ Lf 1 := by
    intro hEq
    exact hpair 0 2 (by rw [hLjoinLf, ← hEq, sup_idem])
  have hne02 : Lf 0 ≠ Lf 2 := by
    intro hEq
    refine hpair 0 1 ?_
    rw [hLjoinLf, ← hEq]
    exact (sup_eq_left.mpr le_sup_left).symm
  have hne12 : Lf 1 ≠ Lf 2 := by
    intro hEq
    refine hpair 1 0 ?_
    rw [hLjoinLf, ← hEq, sup_assoc, sup_idem]
    exact sup_comm _ _
  have hLf_inj : Function.Injective Lf := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hne01 hab).elim
    · exact (hne02 hab).elim
    · exact (hne01 hab.symm).elim
    · rfl
    · exact (hne12 hab).elim
    · exact (hne02 hab.symm).elim
    · exact (hne12 hab.symm).elim
    · rfl
  let d : SylowThreeData G :=
    { M := c.S.M
      Lf := Lf
      L := c.L
      S := P ⊓ c.L
      hLM := fun i => (hcompLf i).1
      hLnorm := hLnorm
      hcomm := fun i j hij =>
        commutator_le_pCoreOf_of_asc83CComponent (hcompLf i) (hcompLf j)
          (fun h => hij (hLf_inj h))
      hperf := fun i => (hcompLf i).2.2.1
      hrank := hrankLf
      hL := by simpa [Lf] using hLjoin
      hS := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hP c.hyp81.1 c.le_normalizer_L }
  refine ⟨d, rfl, rfl, rfl, hLf_inj, hcompLf, ?_⟩
  intro m hm i
  rcases hconj_mem m hm (Lf i) (hcompLf i) (hrankLf i) with h | h | h
  · exact ⟨0, by simpa [d, Lf] using h⟩
  · exact ⟨1, by simpa [d, Lf] using h⟩
  · exact ⟨2, by simpa [d, Lf] using h⟩

end Ctx812

namespace Ctx812E

theorem pRank_Lf_le_one (c : Ctx812E G) {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i)) (k : Fin 3) :
    CFSG.Open.pRank p (d.Lf k) ≤ 1 := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  have hp1 : 1 < p := hpp.one_lt
  have hPle : P ≤ c.S.M := hP.le
  have hPnormL : P ≤ Subgroup.normalizer (c.L : Set G) := hPle.trans (le_normalizer_L c)
  have hmain : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      CFSG.Open.pRank p (d.Lf k) ≤ 1 := by
    intro i j k hij hik hjk
    by_contra hle
    have h2 : 2 ≤ CFSG.Open.pRank p (d.Lf k) := by omega
    obtain ⟨R, hRL, hRab, hRcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := p) hp1 (d.Lf k)
    have hRrank : 2 ≤ CFSG.Open.pRank p R := by
      have h := CFSG.SectionRank.le_pRank hp1 (le_refl R) hRab hRcard
      omega
    have hR : IsPGroup p R := hRab.isPGroup
    have hRM : R ≤ c.S.M := hRL.trans ((d.hLM k).trans (le_of_eq hdM))
    let E : Subgroup G := d.A i ⊔ d.A j
    have hAiL : d.A i ≤ d.Lf i := (d.A_le_H i).trans (d.H_le_Lf i)
    have hAjL : d.A j ≤ d.Lf j := (d.A_le_H j).trans (d.H_le_Lf j)
    have hinf : d.A i ⊓ d.A j = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ d.S := (d.A_le_S i) hx.1
      have hxi : x ∈ d.Lf i := hAiL hx.1
      have hxj : x ∈ d.Lf j ⊔ d.Lf k := Subgroup.mem_sup_left (hAjL hx.2)
      exact d.eq_one_of_mem_Lf_of_mem_sup hij hik hjk hxS hxi hxj
    have hES : E ≤ d.S := sup_le (d.A_le_S i) (d.A_le_S j)
    have hEP : E ≤ P := by
      have h := hES
      rw [hdS] at h
      exact h.trans inf_le_left
    have hAiAb : CFSG.Open.IsElemAbelian 3 (d.A i) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ((d.mem_A_iff i).mp hx).2⟩
      exact Subtype.ext (d.S_commute x y (d.A_le_S i x.2) (d.A_le_S i y.2))
    have hAjAb : CFSG.Open.IsElemAbelian 3 (d.A j) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ((d.mem_A_iff j).mp hx).2⟩
      exact Subtype.ext (d.S_commute x y (d.A_le_S j x.2) (d.A_le_S j y.2))
    have hEab : CFSG.Open.IsElemAbelian 3 E :=
      CFSG.Open.IsElemAbelian.sup_of_commute hAiAb hAjAb
        (fun x hx y hy => d.S_commute x y (d.A_le_S i hx) (d.A_le_S j hy))
    have hEcent : E ≤ Subgroup.centralizer (P : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxZp : IsPGroup 3 (Subgroup.zpowers x) :=
          hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hx)
        have hxS : x ∈ Subgroup.normalizer (d.S : Set G) := by
          rw [hdS]
          exact CFSG.RankThree.PartOne.mem_normalizer_inf hx (hPnormL hx)
        exact d.threeElement_centralizes_A i hxZp hxS (hPn i hx) a ha
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxZp : IsPGroup 3 (Subgroup.zpowers x) :=
          hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hx)
        have hxS : x ∈ Subgroup.normalizer (d.S : Set G) := by
          rw [hdS]
          exact CFSG.RankThree.PartOne.mem_normalizer_inf hx (hPnormL hx)
        exact d.threeElement_centralizes_A j hxZp hxS (hPn j hx) a ha
    have hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G) := le_inf hEP hEcent
    have hEcard : Nat.card E = 3 ^ 2 := by
      have hcomm : ∀ x ∈ d.A i, ∀ y ∈ d.A j, x * y = y * x :=
        fun x hx y hy => d.S_commute x y (d.A_le_S i hx) (d.A_le_S j hy)
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (d.A i) (d.A j) hcomm).1
      rw [hinf, d.card_A i, d.card_A j] at h
      simp at h
      omega
    have hAiNormO : d.A i ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
      (hAiL.trans (d.hLM i)).trans
        ((le_of_eq hdM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M))
    have hAjNormO : d.A j ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
      (hAjL.trans (d.hLM j)).trans
        ((le_of_eq hdM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M))
    have hcommik : ⁅d.A i, R⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
      have h := d.hcomm i k hik
      rw [hdM] at h
      exact (Subgroup.commutator_mono hAiL hRL).trans h
    have hcommjk : ⁅d.A j, R⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
      have h := d.hcomm j k hjk
      rw [hdM] at h
      exact (Subgroup.commutator_mono hAjL hRL).trans h
    have hcommij : ⁅d.A i ⊔ d.A j, R⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
        (d.A i) (d.A j) R (CFSG.Open.pCoreOf 2 c.S.M) hcommik hcommjk hAiNormO hAjNormO
    have hcommE : ⁅R, E⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
      rw [Subgroup.commutator_comm]
      exact hcommij
    exact c.false_of_commutator_le_pCoreOf hp h76 hP hE hEab hEcard hRM hR hRrank hcommE
  fin_cases k
  · exact hmain 1 2 0 (by decide) (by decide) (by decide)
  · exact hmain 0 2 1 (by decide) (by decide) (by decide)
  · exact hmain 0 1 2 (by decide) (by decide) (by decide)

end Ctx812E

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
