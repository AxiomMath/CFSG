module

public import CFSG.Timmesfeld.ARS.Sec8Orbit
public import CFSG.Timmesfeld.ARS.Singular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

open CentralOrbit

theorem exists_conjSub_ne_of_isSigmaMaximal (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R)
    (hmax : IsSigmaMaximal R (centralGroup R A)) {S : Set (Subgroup G)} (hS : S ⊆ R)
    (hcol : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P) (hAT : A ∈ pts R (gen S))
    {B₁ : Subgroup G} (hB₁ : B₁ ∈ pts R (gen S)) (hB₁A : B₁ ≠ A) :
    ∃ C ∈ centralSet R A, ∃ c ∈ C, conjSub (gen S) c ≠ gen S := by
  have := h.finite
  have hR := h.root
  by_contra! hall
  have hCN : centralGroup R A ≤ Subgroup.normalizer ((gen S : Subgroup G) : Set G) :=
    gen_le fun C hC c hc => conjSub_eq_self_iff.1 (hall C hC c hc)
  obtain ⟨g, hg, hgB⟩ := Singular.exists_conjSub_eq h hS hcol hAT hB₁
  have hNN : (⨆ X ∈ normSet R (gen S), X) ≤ Subgroup.normalizer ((gen S : Subgroup G) : Set G) :=
    iSup₂_le fun X hX x hx => conjSub_eq_self_iff.1 (hX.2 x hx)
  have hgN := hNN hg
  have hCB : centralGroup R B₁ ≤ Subgroup.normalizer ((gen S : Subgroup G) : Set G) := by
    rw [← hgB, ← conjSub_centralGroup hR A g, ← conjSub_of_mem hgN]
    exact Subgroup.map_mono hCN
  have hKS : IsSigmaSubgroup R (gen (centralSet R A ∪ centralSet R B₁)) :=
    isSigmaSubgroup_gen (Set.union_subset (fun _ hX => hX.1) fun _ hX => hX.1)
  rcases hmax.2.2 _ hKS (gen_mono Set.subset_union_left) with hKA | hKtop
  ·
    have hsub : centralSet R B₁ ⊆ centralSet R A := fun X hX =>
      ⟨hX.1, (commuting_centralGroup A).mono le_rfl (hKA ▸ le_gen (Set.mem_union_right _ hX))⟩
    have hAB : A ∈ rootClosure R B₁ := mem_rootClosure_of_centralSet_subset hR hB₁.1 hA hsub
    rw [rootClosure_eq_singleton h hB₁.1] at hAB
    exact hB₁A hAB.symm
  ·
    have hKN : gen (centralSet R A ∪ centralSet R B₁) ≤
        Subgroup.normalizer ((gen S : Subgroup G) : Set G) :=
      gen_le fun X hX => hX.elim (fun hX => (le_centralGroup hX).trans hCN)
        fun hX => (le_centralGroup hX).trans hCB
    have hTn : (gen S).Normal :=
      ⟨fun n hn x => (Subgroup.mem_normalizer_iff.1 (hKN (hKtop ▸ Subgroup.mem_top x)) n).1 hn⟩
    have hT2 : IsPGroup 2 (gen S) :=
      (Q_eq_M h hA).2.2.2.2.to_le (Singular.gen_le_M h hS hcol hAT)
    have hTbot := h.twoCore (gen S) hTn hT2
    exact hR.ne_bot A hA (le_bot_iff.1 (hTbot ▸ hAT.2))

theorem exists_line_of_conjSub_ne (h : Hyp G R) {A B : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) {S : Set (Subgroup G)} (hS : S ⊆ R)
    (hcol : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P) (hAT : A ∈ pts R (gen S))
    (hmaxT : ∀ S' ⊆ R, (∀ P ∈ S', ∀ Q ∈ S', P ≠ Q → Q ∈ lambdaSet R P) → A ∈ S' →
      gen S ≤ gen S' → gen S' ≤ gen S)
    (hpts : ∀ P ∈ pts R (gen S), P ≠ A → P ∈ orbit R A B) {C : Subgroup G}
    (hC : C ∈ centralSet R A) {c : G} (hc : c ∈ C) (hTc : conjSub (gen S) c ≠ gen S) :
    C ∈ sigmaSet R A ∧ C ∉ lambdaSet R A ∧ ∃ D ∈ orbit R A B, ∃ L ∈ orbit R A B,
      L ∈ lambdaSet R D ∧ C ∈ lambdaSet R D ∧ C ∈ lambdaSet R L := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  have hCR : C ∈ R := hC.1
  have hCA : Commuting A C := hC.2
  have hcc : c * c = 1 := hR.mul_self C hCR c hc
  have hinv : ∀ X : Subgroup G, conjSub (conjSub X c) c = X := fun X => by
    rw [← conjSub_mul, hcc, conjSub_one]
  have hc1 : c ≠ 1 := fun e => hTc (by rw [e, conjSub_one])
  have hCA' : C ≠ A := fun e => hTc (conjSub_of_mem (hAT.2 (e ▸ hc)))
  have hCl : C ∉ lambdaSet R A := fun hCl =>
    hTc ((Singular.mem_normSet_of_le_M h hS hcol hAT hCR (QD.le_M hCl)).2 c hc)
  have hCσ : C ∈ sigmaSet R A := ⟨hCR, hCA', hCA⟩
  refine ⟨hCσ, hCl, ?_⟩
  have hcov : CoveredBy R (gen S) := Singular.coveredBy_gen h hS hcol
  have hcovc : CoveredBy R (conjSub (gen S) c) := hcov.conj hR c
  have hAc : conjSub A c = A := conjSub_of_forall_commute fun a ha => (hCA a ha c hc).symm
  have hATc : A ≤ conjSub (gen S) c := by
    rw [← hAc]
    exact Subgroup.map_mono hAT.2
  have hT2 : ∀ P Q : Subgroup G, P ∈ R → P ≤ gen S → Q ∈ R → Q ≤ gen S → P ≠ Q →
      Q ∈ lambdaSet R P := fun P Q hP hPle hQ hQle hPQ =>
    Singular.mem_lambdaSet h hS hcol ⟨hP, hPle⟩ ⟨hQ, hQle⟩ hPQ
  have hcolc : ∀ P Q : Subgroup G, P ∈ R → P ≤ conjSub (gen S) c → Q ∈ R →
      Q ≤ conjSub (gen S) c → P ≠ Q → Q ∈ lambdaSet R P := by
    intro P Q hP hPle hQ hQle hPQ
    have hPc : conjSub P c ≤ gen S := by
      rw [← hinv (gen S)]
      exact Subgroup.map_mono hPle
    have hQc : conjSub Q c ≤ gen S := by
      rw [← hinv (gen S)]
      exact Subgroup.map_mono hQle
    have hne : conjSub P c ≠ conjSub Q c := fun e => hPQ (RankOne.map_conj_inj.1 e)
    have := conjSub_mem_lambdaSet hR
      (hT2 _ _ (hR.conjSub_mem hP c) hPc (hR.conjSub_mem hQ c) hQc hne) c
    rwa [hinv, hinv] at this
  have hoff : ∀ P ∈ pts R (gen S), ¬ P ≤ conjSub (gen S) c → P ∈ orbit R A B ∧
      P ∈ lambdaSet R A ∧ ¬ Commuting C P ∧ conjSub P c ∈ lambdaSet R P ∧
      conjSub P c ∈ lambdaSet R A := by
    intro P hP hPTc
    have hPA : P ≠ A := fun e => hPTc (by rw [e]; exact hATc)
    have hPl : P ∈ lambdaSet R A := Singular.mem_lambdaSet h hS hcol hAT hP hPA.symm
    have hPc : conjSub P c ≠ P := fun e => hPTc (by rw [← e]; exact Subgroup.map_mono hP.2)
    have hCP : ¬ Commuting C P := fun hc' =>
      hPc (conjSub_of_forall_commute fun p hp => hc' c hc p hp)
    obtain ⟨hs, -, -, -⟩ := commutator_mem_lambdaSet h hA hCσ hCl hPl hCP
    exact ⟨hpts P hP hPA, hPl, hCP, QD.conjSub_mem_lambdaSet_of_special hR hiso hCR hP.1 hs hc hc1,
      conjSub_mem_lambdaSet_of_mem_centralGroup hR (le_centralGroup hC hc) hPl⟩
  have hTnle : ¬ gen S ≤ conjSub (gen S) c := by
    intro hle
    refine hTc (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [conjSub, Subgroup.card_map_of_injective fun _ _ e => (MulAut.conj c).injective e]
  obtain ⟨x, hxT, hxTc⟩ := Set.not_subset.1 hTnle
  have hx1 : x ≠ 1 := fun e => hxTc (by rw [e]; exact Subgroup.one_mem _)
  obtain ⟨E, hER, hET, hxE⟩ := hcov x hxT hx1
  have hEpt : E ∈ pts R (gen S) := ⟨hER, hET⟩
  have hETc : ¬ E ≤ conjSub (gen S) c := fun hle => hxTc (hle hxE)
  obtain ⟨hEO, hEl, hCE, hEcE, hEcl⟩ := hoff E hEpt hETc
  have hEcT : conjSub E c ≤ conjSub (gen S) c := Subgroup.map_mono hET
  have hUcov : ∀ y ∈ gen S ⊓ conjSub (gen S) c, y ≠ 1 →
      ∃ P ∈ R, P ≤ gen S ⊓ conjSub (gen S) c ∧ y ∈ P := by
    intro y hy hy1
    obtain ⟨P, hPR, hPT, hyP⟩ := hcov y hy.1 hy1
    obtain ⟨P', hP'R, hP'T, hyP'⟩ := hcovc y hy.2 hy1
    have hPP' : P = P' := Sec3.eq_of_mem_of_mem hR hiso hPR hP'R hyP hyP' hy1
    exact ⟨P, hPR, le_inf hPT (hPP' ▸ hP'T), hyP⟩
  by_cases hhyp : gen S ≤ (gen S ⊓ conjSub (gen S) c) ⊔ E
  ·
    exfalso
    set S' : Set (Subgroup G) :=
      insert E (insert (conjSub E c) (pts R (gen S ⊓ conjSub (gen S) c))) with hS'
    have hmemS' : ∀ P ∈ S', P ∈ R ∧ (P = E ∨ P ≤ conjSub (gen S) c) ∧
        (P = conjSub E c ∨ P ≤ gen S) := by
      rintro P (rfl | rfl | hP)
      · exact ⟨hER, Or.inl rfl, Or.inr hET⟩
      · exact ⟨hR.conjSub_mem hER c, Or.inr hEcT, Or.inl rfl⟩
      · exact ⟨hP.1, Or.inr (hP.2.trans inf_le_right), Or.inr (hP.2.trans inf_le_left)⟩
    have hcol' : ∀ P ∈ S', ∀ Q ∈ S', P ≠ Q → Q ∈ lambdaSet R P := by
      intro P hP Q hQ hPQ
      obtain ⟨hPR, hP1, hP2⟩ := hmemS' P hP
      obtain ⟨hQR, hQ1, hQ2⟩ := hmemS' Q hQ
      rcases hP2 with rfl | hPT
      · rcases hQ1 with rfl | hQTc
        · exact mem_lambdaSet_comm hER hEcE
        · exact hcolc _ _ hPR hEcT hQR hQTc hPQ
      · rcases hQ2 with rfl | hQT
        · rcases hP1 with rfl | hPTc
          · exact hEcE
          · exact hcolc _ _ hPR hPTc hQR hEcT hPQ
        · exact hT2 _ _ hPR hPT hQR hQT hPQ
    have hS'R : S' ⊆ R := fun P hP => (hmemS' P hP).1
    have hAS' : A ∈ S' := Or.inr (Or.inr ⟨hA, le_inf hAT.2 hATc⟩)
    have hle : gen S ≤ gen S' := by
      refine hhyp.trans (sup_le ?_ (le_gen (Or.inl rfl)))
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      obtain ⟨P, hPR, hPU, hyP⟩ := hUcov y hy hy1
      exact le_gen (Or.inr (Or.inr ⟨hPR, hPU⟩)) hyP
    have hEcTS : conjSub E c ≤ gen S :=
      (le_gen (Or.inr (Or.inl rfl))).trans (hmaxT S' hS'R hcol' hAS' hle)
    apply hETc
    rw [← hinv E]
    exact Subgroup.map_mono hEcTS
  obtain ⟨y, hyT, hyU⟩ := Set.not_subset.1 hhyp
  have hy1 : y ≠ 1 := fun e => hyU (by rw [e]; exact Subgroup.one_mem _)
  obtain ⟨F, hFR, hFT, hyF⟩ := hcov y hyT hy1
  have hFpt : F ∈ pts R (gen S) := ⟨hFR, hFT⟩
  have hFle : ¬ F ≤ (gen S ⊓ conjSub (gen S) c) ⊔ E := fun hle => hyU (hle hyF)
  have hFTc : ¬ F ≤ conjSub (gen S) c := fun hle => hFle (le_sup_of_le_left (le_inf hFT hle))
  have hEF : E ≠ F := fun e => hFle (by rw [← e]; exact le_sup_right)
  obtain ⟨hFO, hFl, hCF, hFcF, -⟩ := hoff F hFpt hFTc
  have hFcT : conjSub F c ≤ conjSub (gen S) c := Subgroup.map_mono hFT
  have hFE : F ∈ lambdaSet R E := hT2 _ _ hER hET hFR hFT hEF
  have hbot : (E ⊔ F) ⊓ conjSub (gen S) c = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    by_contra hz1
    obtain ⟨P, hPR, hPle, hzP⟩ := hFE.2 z hz.1 hz1
    obtain ⟨P', hP'R, hP'le, hzP'⟩ := hcovc z hz.2 hz1
    have hPP' : P = P' := Sec3.eq_of_mem_of_mem hR hiso hPR hP'R hzP hzP' hz1
    have hPTc : P ≤ conjSub (gen S) c := hPP' ▸ hP'le
    have hEP : E ≠ P := fun e => hETc (by rw [e]; exact hPTc)
    have hsup := (mem_lambdaSet_of_le_sup hR hiso hER hFE hER le_sup_left hPR hPle hEP).2
    apply hFle
    calc F ≤ E ⊔ F := le_sup_right
      _ = E ⊔ P := hsup.symm
      _ ≤ (gen S ⊓ conjSub (gen S) c) ⊔ E :=
        sup_le le_sup_right (le_sup_of_le_left (le_inf (hPle.trans (sup_le hET hFT)) hPTc))
  obtain ⟨hsE, hDA, hCD, hED⟩ := commutator_mem_lambdaSet h hA hCσ hCl hEl hCE
  obtain ⟨hsF, hLA, hCL, hFL⟩ := commutator_mem_lambdaSet h hA hCσ hCl hFl hCF
  have hDR : ⁅C, E⁆ ∈ R := hsE.1
  have hLR : ⁅C, F⁆ ∈ R := hsF.1
  have hDO : ⁅C, E⁆ ∈ orbit R A B := mem_of_mem_lambdaSet h hA hB hEO hDA
    (mem_lambdaSet_comm hDR hED)
  have hLO : ⁅C, F⁆ ∈ orbit R A B := mem_of_mem_lambdaSet h hA hB hFO hLA
    (mem_lambdaSet_comm hLR hFL)
  have hDle : ⁅C, E⁆ ≤ E ⊔ conjSub E c := by
    rw [Sec3.sup_conjSub_eq_of_special hR hiso hCR hER hsE hc hc1, Subgroup.commutator_comm]
    exact le_sup_left
  have hLle : ⁅C, F⁆ ≤ F ⊔ conjSub F c := by
    rw [Sec3.sup_conjSub_eq_of_special hR hiso hCR hFR hsF hc hc1, Subgroup.commutator_comm]
    exact le_sup_left
  have hDL : ⁅C, E⁆ ≠ ⁅C, F⁆ := by
    intro e
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
    obtain ⟨e₁, he₁, e₂, he₂, hde⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hEcE.1.2.2 a ha b hb) (hDle hd)
    obtain ⟨f₁, hf₁, f₂, hf₂, hdf⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hFcF.1.2.2 a ha b hb) (hLle (e ▸ hd))
    have hmem : f₁⁻¹ * e₁ ∈ (E ⊔ F) ⊓ conjSub (gen S) c := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_right (F.inv_mem hf₁))
        (Subgroup.mem_sup_left he₁), ?_⟩
      have e' : f₁⁻¹ * e₁ = f₂ * e₂⁻¹ := by
        calc f₁⁻¹ * e₁ = f₁⁻¹ * (e₁ * e₂) * e₂⁻¹ := by group
          _ = f₁⁻¹ * (f₁ * f₂) * e₂⁻¹ := by rw [hde, hdf]
          _ = f₂ * e₂⁻¹ := by group
      rw [e']
      exact Subgroup.mul_mem _ (hFcT hf₂) (Subgroup.inv_mem _ (hEcT he₂))
    rw [hbot, Subgroup.mem_bot] at hmem
    have hfe : f₁ = e₁ := inv_mul_eq_one.1 hmem
    have he₁1 : e₁ = 1 := by
      have hmem' : e₁ ∈ E ⊓ F := ⟨he₁, hfe ▸ hf₁⟩
      rwa [inf_eq_bot hR hiso hER hFR hEF, Subgroup.mem_bot] at hmem'
    have hdE : d ∈ conjSub E c := by
      rw [← hde, he₁1, one_mul]
      exact he₂
    have hdF : d ∈ conjSub F c := by
      rw [← hdf, hfe, he₁1, one_mul]
      exact hf₂
    have hne : conjSub E c ≠ conjSub F c := fun e' => hEF (RankOne.map_conj_inj.1 e')
    have hmem' : d ∈ conjSub E c ⊓ conjSub F c := ⟨hdE, hdF⟩
    rw [inf_eq_bot hR hiso (hR.conjSub_mem hER c) (hR.conjSub_mem hFR c) hne,
      Subgroup.mem_bot] at hmem'
    exact hd1 hmem'
  have hFEc : Commuting F (conjSub E c) := by
    rw [commuting_iff_commutator_eq_bot, ← le_bot_iff]
    have h1 : ⁅F, conjSub E c⁆ ≤ A :=
      (Subgroup.commutator_mono (QD.le_M hFl) (QD.le_M hEcl)).trans hcommA.le
    have h2 : ⁅F, conjSub E c⁆ ≤ E :=
      (Subgroup.commutator_mono (QD.le_M hFE) (QD.le_M hEcE)).trans (Q_eq_M h hER).2.2.1.le
    exact (le_inf h1 h2).trans (inf_eq_bot hR hiso hA hER hEl.1.2.1.symm).le
  have hDF : Commuting ⁅C, E⁆ F :=
    (Commuting.sup_left ((Singular.commuting_gen h hS hcol).mono hET hFT) hFEc.symm).mono
      hDle le_rfl
  have hLM : ⁅C, F⁆ ≤ M R ⁅C, E⁆ :=
    commutator_le_of_le_normalizer (QD.le_M hCD) (QD.le_normalizer_M hR hDR ⟨hFR, hDF⟩)
  have hmemL : ⁅C, F⁆ ∈ {X | X ∈ R ∧ X ≤ M R ⁅C, E⁆} := ⟨hLR, hLM⟩
  rw [(Q_eq_M h hDR).2.1] at hmemL
  exact ⟨_, hDO, _, hLO, hmemL.resolve_left (Ne.symm hDL), hCD, hCL⟩

theorem exists_not_commuting_of_isSigmaMaximal (h : Hyp G R) {A B : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    {S : Set (Subgroup G)} (hS : S ⊆ R) (hcol : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P)
    (hAT : A ∈ pts R (gen S)) {B₁ : Subgroup G} (hB₁ : B₁ ∈ pts R (gen S)) (hB₁A : B₁ ≠ A)
    (hpts : ∀ P ∈ pts R (gen S), P ≠ A → P ∈ orbit R A B) {Y : Subgroup G}
    (hY : Y ∈ sigmaSet R A) (hYl : Y ∉ lambdaSet R A) : ∃ X ∈ orbit R A B, ¬ Commuting Y X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra! hall
  have hYR : Y ∈ R := hY.1
  have hYΔ₀ : Y ∈ centralSet R A := ⟨hYR, hY.2.2⟩
  have hΩa : ∀ Z, Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z →
      Z ∈ centralSet R A ∧ Z ≠ A ∧ ∀ X ∈ orbit R A B, Commuting Z X := by
    intro Z hZ
    induction hZ with
    | refl => exact ⟨hYΔ₀, hY.2.1, hall⟩
    | @tail Z₁ Z₂ _ hedge ih =>
      obtain ⟨hZ₁Δ, -, hZ₁O⟩ := ih
      obtain ⟨-, hZ₂Δ, hop⟩ := hedge
      have hZ₁R : Z₁ ∈ R := hZ₁Δ.1
      have hZ₂R : Z₂ ∈ R := hZ₂Δ.1
      have hZ₂A : Z₂ ≠ A := by
        rintro rfl
        exact hop.not_commuting (hR.ne_bot Z₁ hZ₁R) hZ₁Δ.2.symm
      have hZ₂l : Z₂ ∉ lambdaSet R A := fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet hR hZ₁R hop (mem_lambdaSet_comm hA hl)
          hZ₁Δ.2.symm
      refine ⟨hZ₂Δ, hZ₂A, fun X hX => ?_⟩
      by_contra hc
      have hXl := subset_lambdaSet hR hB hX
      obtain ⟨-, hJA, hZ₂J, hXJ⟩ :=
        commutator_mem_lambdaSet h hA ⟨hZ₂R, hZ₂A, hZ₂Δ.2⟩ hZ₂l hXl hc
      have hJO := mem_of_mem_lambdaSet h hA hB hX hJA (mem_lambdaSet_comm hJA.1.1 hXJ)
      exact not_commuting_of_opposite_of_mem_lambdaSet hR hZ₁R hop
        (mem_lambdaSet_comm hJA.1.1 hZ₂J) (hZ₁O _ hJO)
  have hΩT : ∀ Z, Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z →
      Commuting Z (gen S) := by
    intro Z hZ
    obtain ⟨hZΔ, -, hZO⟩ := hΩa Z hZ
    refine commuting_iff_le_centralizer.2 (gen_le fun P hP => commuting_iff_le_centralizer.1 ?_)
    by_cases hPA : P = A
    · rw [hPA]
      exact hZΔ.2.symm
    · exact hZO P (hpts P ⟨hS hP, le_gen hP⟩ hPA)
  have hΩN : ∀ Z, Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z →
      Z ∈ normSet R (gen S) := fun Z hZ =>
    ⟨(hΩa Z hZ).1.1, fun z hz => conjSub_of_forall_commute fun t ht => hΩT Z hZ z hz t ht⟩
  have hd0 := component_decomposition hR hiso (centralSet R A) (fun _ hX => hX.1)
    (fun g hg X hX => by
      have hgA : conjSub A g = A := conjSub_of_forall_commute fun a ha =>
        ((commuting_centralGroup (R := R) A) a ha g hg).symm
      refine ⟨hR.conjSub_mem hX.1 g, ?_⟩
      have := hX.2.conjSub g
      rwa [hgA] at this)
    (fun X hX Z hZ hs => ⟨hs.1, (Commuting.sup_right hX.2 hZ.2).mono le_rfl
      (QD.commutator_le_of_le le_sup_left le_sup_right)⟩)
  have hNN : (⨆ X ∈ normSet R (gen S), X) ≤ Subgroup.normalizer ((gen S : Subgroup G) : Set G) :=
    iSup₂_le fun X hX x hx => conjSub_eq_self_iff.1 (hX.2 x hx)
  have hd1 := component_decomposition hR hiso (normSet R (gen S)) (fun _ hX => hX.1)
    (fun g hg X hX => by
      refine ⟨hR.conjSub_mem hX.1 g, fun y hy => conjSub_eq_self_iff.2 ?_⟩
      have hgN := hNN hg
      have hy' : g⁻¹ * y * g ∈ Subgroup.normalizer ((gen S : Subgroup G) : Set G) :=
        conjSub_eq_self_iff.1 (hX.2 _ (mem_conjSub.1 hy))
      have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hy') (Subgroup.inv_mem _ hgN))
    (fun X hX Z hZ hs => ⟨hs.1, fun z hz => conjSub_eq_self_iff.2
      (QD.commutator_le_of_le (fun x hx => conjSub_eq_self_iff.1 (hX.2 x hx))
        (fun x hx => conjSub_eq_self_iff.1 (hZ.2 x hx)) hz)⟩)
  have hclosed : ∀ W ∈ normSet R (gen S), Commuting W (gen S) → ∀ W' ∈ normSet R (gen S),
      Opposite W W' → Commuting W' (gen S) := by
    intro W hW hWT W' hW' hop
    by_contra hW'T
    obtain ⟨P, hP, hW'P⟩ := Singular.exists_mem_lambdaSet h hS hcol hW' hW'T
    exact not_commuting_of_opposite_of_mem_lambdaSet hR hW.1 hop (mem_lambdaSet_comm hP.1 hW'P)
      (hWT.mono le_rfl hP.2)
  have hpath1 : ∀ Z, Relation.ReflTransGen (oppGraph (normSet R (gen S))) Y Z →
      Commuting Z (gen S) ∧ Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z := by
    intro Z hZ
    induction hZ with
    | refl => exact ⟨hΩT Y Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | @tail Z₁ Z₂ _ hedge ih =>
      obtain ⟨hZ₁T, hZ₁Ω⟩ := ih
      obtain ⟨hZ₁N, hZ₂N, hop⟩ := hedge
      have hZ₂T := hclosed Z₁ hZ₁N hZ₁T Z₂ hZ₂N hop
      have hcA : ∀ {W : Subgroup G}, W ∈ normSet R (gen S) → Commuting W (gen S) →
          W ∈ centralSet R A := fun hW hWT => ⟨hW.1, (hWT.mono le_rfl hAT.2).symm⟩
      exact ⟨hZ₂T, hZ₁Ω.tail ⟨hcA hZ₁N hZ₁T, hcA hZ₂N hZ₂T, hop⟩⟩
  have hpath01 : ∀ Z, Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z →
      Relation.ReflTransGen (oppGraph (normSet R (gen S))) Y Z := by
    intro Z hZ
    induction hZ with
    | refl => exact Relation.ReflTransGen.refl
    | @tail Z₁ Z₂ hpre hedge ih =>
      exact ih.tail ⟨hΩN Z₁ hpre, hΩN Z₂ (hpre.tail hedge), hedge.2.2⟩
  have hYI : Y ∉ isolatedSet R A := by
    intro hI
    have hmem : Y ∈ {X | X ∈ R ∧ X ≤ M R A} := ⟨hYR, (Q_eq_M h hA).1 ▸ QD.le_Q hI⟩
    rw [(Q_eq_M h hA).2.1] at hmem
    rcases hmem with e | hl
    · exact hY.2.1 e
    · exact hYl hl
  obtain ⟨C₀, hC₀, hYC₀⟩ := QD.exists_opposite_of_notMem_isolatedSet hYΔ₀ hYI
  have hC₀Ω : Relation.ReflTransGen (oppGraph (centralSet R A)) Y C₀ :=
    Relation.ReflTransGen.single ⟨hYΔ₀, hC₀, hYC₀⟩
  set Ω : Set (Subgroup G) := {Z | Relation.ReflTransGen (oppGraph (centralSet R A)) Y Z}
    with hΩdef
  have hstab0 : centralGroup R A ≤ stabSet Ω := fun g hg =>
    QD.mem_stabSet_of_forall (fun Z hZ => (hd0.2.1 Y hYΔ₀ ⟨C₀, hC₀, hYC₀⟩ Z hZ).2 g hg)
      (fun Z hZ => (hd0.2.1 Y hYΔ₀ ⟨C₀, hC₀, hYC₀⟩ Z hZ).2 g⁻¹ (Subgroup.inv_mem _ hg))
  have hYN := hΩN Y Relation.ReflTransGen.refl
  have hstab1 : ∀ X ∈ normSet R (gen S), X ≤ stabSet Ω := by
    intro X hX x hx
    have hxN : x ∈ ⨆ X ∈ normSet R (gen S), X :=
      Subgroup.mem_iSup_of_mem X (Subgroup.mem_iSup_of_mem hX hx)
    refine QD.mem_stabSet_of_forall (fun Z hZ => ?_) (fun Z hZ => ?_)
    · exact (hpath1 _ ((hd1.2.1 Y hYN ⟨C₀, hΩN C₀ hC₀Ω, hYC₀⟩ Z (hpath01 Z hZ)).2 x hxN)).2
    · exact (hpath1 _ ((hd1.2.1 Y hYN ⟨C₀, hΩN C₀ hC₀Ω, hYC₀⟩ Z (hpath01 Z hZ)).2 x⁻¹
        (Subgroup.inv_mem _ hxN))).2
  have hKS : IsSigmaSubgroup R (gen (centralSet R A ∪ normSet R (gen S))) :=
    isSigmaSubgroup_gen (Set.union_subset (fun _ hX => hX.1) fun _ hX => hX.1)
  rcases hmax.2.2 _ hKS (gen_mono Set.subset_union_left) with hKA | hKtop
  · obtain ⟨X, hX, hAX⟩ := Singular.exists_not_commuting h hS hcol hAT hB₁ hB₁A.symm
    exact hAX ((commuting_centralGroup A).mono le_rfl (hKA ▸ le_gen (Set.mem_union_right _ hX)))
  · have hKstab : gen (centralSet R A ∪ normSet R (gen S)) ≤ stabSet Ω :=
      gen_le fun X hX => hX.elim (fun hX => (le_centralGroup hX).trans hstab0)
        fun hX => hstab1 X hX
    obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hYR hA
    have hgS : g ∈ stabSet Ω := hKstab (hKtop ▸ Subgroup.mem_top g)
    have hAΩ : A ∈ Ω := hg ▸ conjSub_mem_of_mem_stabSet hgS Relation.ReflTransGen.refl
    exact (hΩa A hAΩ).2.1 rfl

theorem exists_not_commuting_of_notMem (h : Hyp G R) {A B Z : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hAne : sigmaSet R A ≠ lambdaSet R A) (hZ : Z ∈ lambdaSet R A)
    (hZO : Z ∉ orbit R A B) : ∃ Y ∈ sigmaSet R A, Y ∉ lambdaSet R A ∧
      ∃ I ∈ lambdaSet R A, I ∉ orbit R A B ∧ ¬ Commuting Y I := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  have hZR : Z ∈ R := hZ.1.1
  obtain ⟨E, hER, hEle, hEcol⟩ := exists_plane_of_sigmaSet_ne h hA hZ hAne
  obtain ⟨-, -, -, -, hcoll, -⟩ := plane hR hiso hER hA hZ hEcol
  obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hER hA hZ hEcol
  have hEN : E ≤ E ⊔ A ⊔ Z := le_sup_left.trans le_sup_left
  have hAN : A ≤ E ⊔ A ⊔ Z := le_sup_right.trans le_sup_left
  have hZN : Z ≤ E ⊔ A ⊔ Z := le_sup_right
  have hZA : Z ≠ A := hZ.1.2.1
  have hEA : E ≠ A := fun e => hEle (by rw [e]; exact le_sup_left)
  have hEl : E ∈ lambdaSet R A := hcoll A hA hAN E hER hEN hEA.symm
  have hZE : Z ∈ lambdaSet R E := hEcol Z hZR le_sup_right
  have hEO : E ∉ orbit R A B := fun hEO => hZO (mem_of_mem_lambdaSet h hA hB hEO hZ hZE)
  obtain ⟨T, hTR, hT⟩ := htrans Z hZR A hA hZN hAN hZA
  have hEL : ¬ E ≤ Z ⊔ A := fun hle => hEle (hle.trans (sup_comm Z A).le)
  obtain ⟨P', hP'R, hP'le, hP'E, hP'Z⟩ := exists_mem_le_sup_ne_ne hR hiso hER hZE E Z
  obtain ⟨t, ht, hEt⟩ := hT.2.2.2 E hER hEN hEL P' hP'R hP'le hP'Z
  have hTE : ¬ Commuting T E := fun hc =>
    hP'E (hEt.symm.trans (conjSub_of_forall_commute fun e he => hc t ht e he))
  have hTA : Commuting A T := hT.2.2.1.mono le_sup_right le_rfl
  have hNM : E ⊔ A ⊔ Z ≤ M R A := sup_le (sup_le (QD.le_M hEl) QD.le_M_self) (QD.le_M hZ)
  have hTnl : T ∉ lambdaSet R A := by
    intro hTl
    refine hTE fun x hx e he => ?_
    have h1 : ⁅e, x⁆ ∈ A ⊓ Z :=
      ⟨hcommA ▸ Subgroup.commutator_mem_commutator (hNM (hEN he)) (QD.le_M hTl hx),
        hT.2.1 x hx e (hEN he)⟩
    rw [inf_eq_bot hR hiso hA hZR hZA.symm, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hTA' : T ≠ A := fun e => hTE (by rw [e]; exact hEl.1.2.2)
  exact ⟨T, ⟨hTR, hTA', hTA⟩, hTnl, E, hEl, hEO, hTE⟩

theorem exists_mem_centralGroup_conjSub_eq_of_isSigmaMaximal (h : Hyp G R) {A B C : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hB : B ∈ lambdaSet R A)
    (hC : C ∈ lambdaSet R A) : ∃ g ∈ centralGroup R A, conjSub B g = C := by
  have := h.finite
  have hR := h.root
  by_contra hBC
  set 𝒯 : Set (Subgroup G) := {T | ∃ S ⊆ R, (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P) ∧
    A ∈ S ∧ T = gen S} with h𝒯
  have hne : 𝒯.Nonempty := ⟨gen {A}, {A}, Set.singleton_subset_iff.2 hA,
    fun P hP Q hQ hPQ => absurd (hP.trans hQ.symm) hPQ, rfl, rfl⟩
  obtain ⟨_, ⟨S, hS, hcol, hAS, rfl⟩, hTmax⟩ :=
    Set.exists_max_image 𝒯 (fun T => Nat.card T) (Set.toFinite 𝒯) hne
  have hmaxT : ∀ S' ⊆ R, (∀ P ∈ S', ∀ Q ∈ S', P ≠ Q → Q ∈ lambdaSet R P) → A ∈ S' →
      gen S ≤ gen S' → gen S' ≤ gen S := fun S' hS' hcol' hAS' hle =>
    (Subgroup.eq_of_le_of_card_ge hle (hTmax _ ⟨S', hS', hcol', hAS', rfl⟩)).symm.le
  have hAT : A ∈ pts R (gen S) := ⟨hA, le_gen hAS⟩
  obtain ⟨B₁, hB₁, hB₁A⟩ : ∃ B₁ ∈ pts R (gen S), B₁ ≠ A := by
    by_contra! hall
    have hTA : gen S ≤ A := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact A.one_mem
      obtain ⟨P, hPR, hPT, hxP⟩ := Singular.coveredBy_gen h hS hcol x hx hx1
      rw [← hall P ⟨hPR, hPT⟩]
      exact hxP
    have hcolAB : ∀ P ∈ ({A, B} : Set (Subgroup G)), ∀ Q ∈ ({A, B} : Set (Subgroup G)),
        P ≠ Q → Q ∈ lambdaSet R P := by
      rintro P (rfl | rfl) Q (rfl | rfl) hPQ
      · exact absurd rfl hPQ
      · exact hB
      · exact mem_lambdaSet_comm hA hB
      · exact absurd rfl hPQ
    have hle := hmaxT {A, B} (by rintro _ (rfl | rfl); exacts [hA, hB.1.1]) hcolAB (Or.inl rfl)
      (hTA.trans (le_gen (Or.inl rfl)))
    exact hB.1.2.1 (hall B ⟨hB.1.1, (le_gen (Or.inr rfl)).trans hle⟩)
  have hB₁l : B₁ ∈ lambdaSet R A := Singular.mem_lambdaSet h hS hcol hAT hB₁ hB₁A.symm
  have hpts : ∀ P ∈ pts R (gen S), P ≠ A → P ∈ orbit R A B₁ := by
    intro P hP hPA
    by_cases hPB : P = B₁
    · rw [hPB]
      exact mem_self R A B₁
    · exact mem_of_mem_lambdaSet h hA hB₁l (mem_self R A B₁)
        (Singular.mem_lambdaSet h hS hcol hAT hP hPA.symm)
        (Singular.mem_lambdaSet h hS hcol hB₁ hP (Ne.symm hPB))
  obtain ⟨Z, hZ, hZO⟩ : ∃ Z ∈ lambdaSet R A, Z ∉ orbit R A B₁ := by
    by_contra! hall
    exact hBC (exists_conjSub_eq (hall B hB) (hall C hC))
  obtain ⟨C', hC', c, hc, hTc⟩ :=
    exists_conjSub_ne_of_isSigmaMaximal h hA hmax hS hcol hAT hB₁ hB₁A
  obtain ⟨hC'σ, hC'l, D, hD, L, hL, hLD, hCD, hCL⟩ :=
    exists_line_of_conjSub_ne h hA hB₁l hS hcol hAT hmaxT hpts hC' hc hTc
  have h2 : ∀ X ∈ orbit R A B₁, ∀ I ∈ lambdaSet R A, I ∉ orbit R A B₁ → Commuting X I :=
    fun X hX I hI hIO => commuting_of_forall_commuting h hA hB₁l hC'σ hC'l
      (fun J hJ hJO => commuting_of_mem_lambdaSet h hA hB₁l hC'σ hC'l hD hL hLD hCD hCL hJ hJO)
      hX hI hIO
  obtain ⟨Y, hY, hYl, I, hI, hIO, hYI⟩ := exists_not_commuting_of_notMem h hA hB₁l hAne hZ hZO
  rcases forall_commuting_or_forall_commuting h hA hB₁l h2 hY hYl with h3 | h3
  · obtain ⟨X, hX, hYX⟩ :=
      exists_not_commuting_of_isSigmaMaximal h hA hB₁l hmax hS hcol hAT hB₁ hB₁A hpts hY hYl
    exact hYX (h3 X hX)
  · exact hYI (h3 I hI hIO)

theorem exists_mem_levi_conjSub_eq_of_isSigmaMaximal (h : Hyp G R) {A A₀ B C : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) :
    ∃ v ∈ levi R A A₀, conjSub B v = C := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  obtain ⟨g, hg, hBg⟩ := exists_mem_centralGroup_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hB.1 hC.1
  have hgMV : g ∈ M R A ⊔ levi R A A₀ := gen_centralSet_eq h hA hAne hA₀ ▸ hg
  have hVN : levi R A A₀ ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) :=
    iSup₂_le fun E hE => QD.le_normalizer_M hR hA ⟨hE.1.1, hE.1.2.2⟩
  have hgMV' : g ∈ ((M R A ⊔ levi R A A₀ : Subgroup G) : Set G) := hgMV
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVN] at hgMV'
  obtain ⟨m, hm, v, hv, rfl⟩ := hgMV'
  refine ⟨v, hv, ?_⟩
  have hvA : conjSub A v = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hv) a ha).symm
  have hvA₀ : conjSub A₀ v = A₀ := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hv) a ha).symm
  have hBv : conjSub B v ∈ lambdaStar R A A₀ := by
    refine ⟨?_, hR.conjSub_mem hB.1.1.1 v, ?_⟩
    · have := conjSub_mem_lambdaSet hR hB.1 v
      rwa [hvA] at this
    · have := Sec3.special_conjSub hR hB.2.2 v
      rwa [hvA₀] at this
  have hCle : C ≤ A ⊔ conjSub B v := by
    rw [← hBg, conjSub_mul]
    exact (conjSub_le_commutator_sup hm).trans (sup_le_sup_right
      ((Subgroup.commutator_mono (QD.le_M hBv.1) le_rfl).trans hcommA.le) _)
  obtain ⟨D', -, hu⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hBv.1
  exact ((hu C ⟨hC.1.1.1, hCle, hC.2⟩).trans
    (hu (conjSub B v) ⟨hBv.1.1.1, le_sup_right, hBv.2⟩).symm).symm

end CFSG.Timmesfeld.ARS
