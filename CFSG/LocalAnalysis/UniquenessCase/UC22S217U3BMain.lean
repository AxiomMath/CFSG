module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UCKP1
import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

private theorem uc22s217u3b_conjClosure_le {M L : Subgroup G} (hLM : L ≤ M) :
    conjClosure M L ≤ M := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨g, hg, rfl⟩ := hK
  rintro _ ⟨l, hl, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact M.mul_mem (M.mul_mem hg (hLM hl)) (M.inv_mem hg)

theorem uc22s217u3b_rank_gt_three (hCen : UCK.U3Center) (hFF : UCK.U3FixField) {M : Subgroup G}
    {n s r q : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) (hrn : ¬ r ∣ n)
    (hq : q.Prime) (hq3 : 3 < q)
    (hfix : ∀ (X : Type) [Group X] [Finite X], IsSU3 X n → ∀ α : MulAut X, α ^ r = 1 →
      α ∈ (MulAut.conj : X →* MulAut X).range → ∃ z : X, orderOf z = q ∧ α z = z) :
    ∀ K₀ K₁ : Subgroup G, K₀ ∈ calC M → K₁ ∈ calC M → K₀ ≠ K₁ →
      IsSU3 (Bar2 K₀) n → IsSU3 (Bar2 K₁) n → ∀ y ∈ M, orderOf y = r →
      y ∈ normalizer (K₀ : Set G) → y ∈ normalizer (K₁ : Set G) →
      ∃ W : Subgroup G, W ≤ M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧
        Nat.card W = q ^ 2 := by
  intro K₀ K₁ hK₀ hK₁ hne hX₀ hX₁ y hyM hyr hy₀ hy₁
  have hr2 : r ≠ 2 := by
    have := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
    omega
  have hq2 : q ≠ 2 := by omega
  obtain ⟨hα₀r, hα₀⟩ := uc22s217u3b_inner hFF hX₀ hs hsn hr hrs hrn hy₀ hyr
  obtain ⟨hα₁r, hα₁⟩ := uc22s217u3b_inner hFF hX₁ hs hsn hr hrs hrn hy₁ hyr
  obtain ⟨z₀, hz₀o, hz₀⟩ := hfix (Bar2 K₀) hX₀ _ hα₀r hα₀
  obtain ⟨z₁, hz₁o, hz₁⟩ := hfix (Bar2 K₁) hX₁ _ hα₁r hα₁
  obtain ⟨A₀, hA₀K, hA₀c, hA₀q⟩ := uc22s217u3b_lift_elem hr hr2 hq hq2 hy₀ hyr hz₀o hz₀
  obtain ⟨A₁, hA₁K, hA₁c, hA₁q⟩ := uc22s217u3b_lift_elem hr hr2 hq hq2 hy₁ hyr hz₁o hz₁
  have hZ : ¬ q ∣ Nat.card (center (Bar2 K₀)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hX₀))
    omega
  exact uc22s217u3b_two_cent hK₀ hK₁ hne hr hr2 hq hq2 hZ hyM hyr hA₀K hA₁K hA₀c hA₁c hA₀q hA₁q

private theorem uc22s217u3b_normalizer_le (D : Data G) (hCen : UCK.U3Center)
    (hFF : UCK.U3FixField) {K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ calC D.M) (hK₁ : K₁ ∈ calC D.M)
    (hne : K₀ ≠ K₁) {n : ℕ} (hX₀ : IsSU3 (Bar2 K₀) n) (hX₁ : IsSU3 (Bar2 K₁) n) {s r : ℕ}
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) (hrn : ¬ r ∣ n) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (h76 : Conclusion76 D.M q)
    (hfix : ∀ (X : Type) [Group X] [Finite X], IsSU3 X n → ∀ α : MulAut X, α ^ r = 1 →
      α ∈ (MulAut.conj : X →* MulAut X).range → ∃ z : X, orderOf z = q ∧ α z = z)
    (hW : ∀ y ∈ D.M, orderOf y = r → ∃ W : Subgroup G,
      W ≤ D.M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧ Nat.card W = q ^ 2)
    (hnorm : ∀ y ∈ D.M, orderOf y = r →
      y ∈ normalizer (K₀ : Set G) ∧ y ∈ normalizer (K₁ : Set G))
    {X₀ : Subgroup G} (hX₀K : X₀ ≤ K₀) (hX₀c : Nat.card X₀ = r) {x : G} (hxM : x ∈ D.M)
    (hxr : orderOf x = r) (hxK : x ∉ K₀) :
    normalizer (zpowers x : Set G) ≤ D.M := by
  classical
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  have hxc : Nat.card (zpowers x) = r := by rw [Nat.card_zpowers, hxr]
  have hxN := hnorm x hxM hxr
  obtain ⟨hα₀r, hα₀⟩ := uc22s217u3b_inner hFF hX₀ hs hsn hr hrs hrn hxN.1 hxr
  have hZ3 : ∀ z ∈ center (Bar2 K₀), z ^ 3 = 1 := fun z hz =>
    UCK.pow_three_eq_one_of_mem_center (hCen (Bar2 K₀) n hX₀) hz
  obtain ⟨A, hAK, hAc, hAr⟩ :=
    uc22s217u3b_exists_partner hr (by omega) hZ3 hX₀K hX₀c hxN.1 hxr hα₀r hα₀
  obtain ⟨hEel, hEc⟩ := uc22s217u3b_sup_elemAbelian hr hxr hxK hAK hAc hAr
  have hEM : zpowers x ⊔ A ≤ D.M := sup_le (Subgroup.zpowers_le.2 hxM) (hAK.trans hK₀.1.le)
  obtain ⟨hα₁r, hα₁⟩ := uc22s217u3b_inner hFF hX₁ hs hsn hr hrs hrn hxN.2 hxr
  obtain ⟨z, hzo, hz⟩ := hfix (Bar2 K₁) hX₁ _ hα₁r hα₁
  obtain ⟨Q, hQK, hQc, hQq⟩ :=
    uc22s217u3b_exists_cent_sup hK₀ hK₁ hne hr hr2 hq hq2 hxN.2 hzo hz hAK hEel.isPGroup
  have h6 : 0 < CFSG.Open.pRank q (D.M ⊓ centralizer ((zpowers x ⊔ A : Subgroup G) : Set G)) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_pRank' (k := 1) hq (le_inf (hQK.trans hK₁.1.le) hQc)
      (UC6S898.isElemAbelian_of_card_prime hq hQq) (by rw [hQq, pow_one]))
  have h7 : ∀ X : Subgroup G, X ≤ zpowers x ⊔ A → Nat.card X = r →
      1 < CFSG.Open.pRank q (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE hXc
    obtain ⟨y, hyX, hyr, hgen⟩ := UC6S898.exists_generator hr hXc
    have hXy : X = zpowers y := le_antisymm (fun w hw => by
        obtain ⟨k, rfl⟩ := hgen w hw
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k)
      (Subgroup.zpowers_le.2 hyX)
    subst hXy
    obtain ⟨W, hWle, hWel, hWc⟩ := hW y (hEM (hXE (Subgroup.mem_zpowers y))) hyr
    have h2 := le_pRank' hq (hWle.trans (inf_le_inf_left _ (centralizer_le_normalizer _))) hWel hWc
    omega
  have hΓ := h76 r hr _ hEM hEel hEc h6 h7
  exact (UC6S898.normalizer_le_gamma le_sup_left hr (UC6S898.isElemAbelian_of_card_prime hr hxc)
    hxc).trans hΓ

theorem uc22s217u3b_false_of
    (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hSg : SigmaStd D) (hCen : UCK.U3Center)
    (hFF : UCK.U3FixField) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {s r : ℕ} (hs : Odd s)
    (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) (hrn : ¬ r ∣ n) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hsp : IsStronglyPEmbedded q D.M) (h76 : Conclusion76 D.M q)
    (hfix : ∀ (X : Type) [Group X] [Finite X], IsSU3 X n → ∀ α : MulAut X, α ^ r = 1 →
      α ∈ (MulAut.conj : X →* MulAut X).range → ∃ z : X, orderOf z = q ∧ α z = z)
    (hrank : ∀ K₀ K₁ : Subgroup G, K₀ ∈ calC D.M → K₁ ∈ calC D.M → K₀ ≠ K₁ →
      IsSU3 (Bar2 K₀) n → IsSU3 (Bar2 K₁) n → ∀ y ∈ D.M, orderOf y = r →
      y ∈ normalizer (K₀ : Set G) → y ∈ normalizer (K₁ : Set G) →
      ∃ W : Subgroup G, W ≤ D.M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧
        Nat.card W = q ^ 2) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  have hZr : ∀ {K : Subgroup G}, IsSU3 (Bar2 K) n → ¬ r ∣ Nat.card (center (Bar2 K)) :=
    fun hK h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hK))
      omega
  have hLM : L ≤ D.M := hL.1.le
  have hT₁ : IsPGroup 2 (D.T ⊓ normalizer (L : Set G) : Subgroup G) :=
    D.sylowM.isPGroup.to_le inf_le_left
  have hTL : IsSylowOf 2 ((D.T ⊓ normalizer (L : Set G) : Subgroup G) ⊓ L) L := by
    rw [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  have hone := uc22ine229_exists_mem_normalizer_of_isSU3 hT₁ inf_le_right hTL hX hs hsn hr hrs
  obtain ⟨x, hxcl, hxr, hxT⟩ :=
    exists_mem_conjClosure_orderOf_mem_normalizer D.sylowM hL hr hr2 (hZr hX) hone
  obtain ⟨x₀, hx₀L, hx₀r, -⟩ := hone
  have hxM : x ∈ D.M := uc22s217u3b_conjClosure_le hLM hxcl
  have hxc : Nat.card (zpowers x) = r := by rw [Nat.card_zpowers, hxr]
  have hxp : IsPGroup r (zpowers x) := IsPGroup.of_card (n := 1) (by rw [hxc, pow_one])
  have hxne : zpowers x ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hxc
    exact hr.ne_one hxc.symm
  have hnsp : ¬ IsStronglyPEmbedded r D.M := fun hsr =>
    uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hxr
      (uc22p22r_mem_uniqueSet_of_sp D hr hsr (Subgroup.zpowers_le.2 hxM) hxp hxne)
      (Subgroup.zpowers_le.2 hxT)
  have hrank3 : CFSG.Open.pRank r D.M ≤ 3 := s21_15_pRank_le_three hSg hr hr2 hL hnsp
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  let f : MulAut G := MulAut.conj m
  have hMf : D.M.map f.toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map f.toMonoidHom ∈ calC D.M := calC_map D.M f hMf hL
  have hne : L ≠ L.map f.toMonoidHom := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he.symm)
  have hX' : IsSU3 (Bar2 (L.map f.toMonoidHom)) n :=
    uc22p20p_isSU3_of_mulEquiv
      (bar2Equiv (Subgroup.equivMapOfInjective L f.toMonoidHom f.injective)) hX
  have hX₀c : Nat.card (zpowers x₀) = r := by rw [Nat.card_zpowers, hx₀r]
  have hX₀L : zpowers x₀ ≤ L := Subgroup.zpowers_le.2 hx₀L
  have hX₀L' : (zpowers x₀).map f.toMonoidHom ≤ L.map f.toMonoidHom := Subgroup.map_mono hX₀L
  have hX₀c' : Nat.card ((zpowers x₀).map f.toMonoidHom) = r := by
    rw [Subgroup.card_map_of_injective f.injective, hX₀c]
  have hnorm : ∀ y ∈ D.M, orderOf y = r →
      y ∈ normalizer (L : Set G) ∧ y ∈ normalizer (L.map f.toMonoidHom : Set G) :=
    fun y hy hyr =>
      ⟨UC6S898.normalizes_of_rank_lt_four hL hy hr hr5 hyr hX₀L hX₀c (hZr hX) hrank3,
        UC6S898.normalizes_of_rank_lt_four hL' hy hr hr5 hyr hX₀L' hX₀c' (hZr hX') hrank3⟩
  have hW : ∀ y ∈ D.M, orderOf y = r → ∃ W : Subgroup G,
      W ≤ D.M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧ Nat.card W = q ^ 2 :=
    fun y hy hyr => hrank _ _ hL hL' hne hX hX' y hy hyr (hnorm y hy hyr).1 (hnorm y hy hyr).2
  have hxLL : x ∉ L ∨ x ∉ L.map f.toMonoidHom := by
    by_contra h
    push Not at h
    obtain ⟨hsn₀, hp₀, hqs₀, hcen₀⟩ := calC_subgroupOf hL
    obtain ⟨hsn₁, hp₁, hqs₁, -⟩ := calC_subgroupOf hL'
    have hL'M : L.map f.toMonoidHom ≤ D.M := hL'.1.le
    have hne' : L.subgroupOf D.M ≠ (L.map f.toMonoidHom).subgroupOf D.M := by
      intro he
      apply hne
      have := congrArg (Subgroup.map D.M.subtype) he
      rwa [Subgroup.map_subgroupOf_eq_of_le hLM, Subgroup.map_subgroupOf_eq_of_le hL'M] at this
    have hbot := UC6S898.eq_bot_of_le_inf (A := L.subgroupOf D.M)
      (A' := (L.map f.toMonoidHom).subgroupOf D.M) (E := (zpowers x).subgroupOf D.M) hr hr2
      hsn₀ hp₀ hqs₀ hsn₁ hp₁ hqs₁ hne' (by rw [hcen₀]; exact hZr hX)
      (fun w hw => (Subgroup.zpowers_le.2 h.1) hw) (fun w hw => (Subgroup.zpowers_le.2 h.2) hw)
      ((UC6S898.isElemAbelian_of_card_prime hr hxc).subgroupOf D.M)
    apply hxne
    have := congrArg (Subgroup.map D.M.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 hxM), Subgroup.map_bot] at this
  have hNx : normalizer (zpowers x : Set G) ≤ D.M := by
    rcases hxLL with hxK | hxK
    · exact uc22s217u3b_normalizer_le D hCen hFF hL hL' hne hX hX' hs hsn hr hrs hrn hq hq2 h76
        hfix hW hnorm hX₀L hX₀c hxM hxr hxK
    · exact uc22s217u3b_normalizer_le D hCen hFF hL' hL hne.symm hX' hX hs hsn hr hrs hrn hq hq2
        h76 hfix hW (fun y hy hyr => (hnorm y hy hyr).symm) hX₀L' hX₀c' hxM hxr hxK
  have hxU : zpowers x ∈ uniqueSet D.M := by
    refine ⟨Subgroup.zpowers_le.2 hxM, fun g hxg => ?_⟩
    by_cases hg : g ∈ D.M
    · exact UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hg)
    · exfalso
      have hyM : g⁻¹ * x * g ∈ D.M := (UC6S898.mem_map_conj_iff g x).1 (hxg (Subgroup.mem_zpowers x))
      have hconj : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hyr : orderOf (g⁻¹ * x * g) = r := by
        rw [← hconj, orderOf_injective _ (MulAut.conj g⁻¹).injective x, hxr]
      have hyN : g⁻¹ * x * g ∈ normalizer (L : Set G) := (hnorm _ hyM hyr).1
      obtain ⟨hαr, hα⟩ := uc22s217u3b_inner hFF hX hs hsn hr hrs hrn hyN hyr
      obtain ⟨z, hzo, hz⟩ := hfix (Bar2 L) hX _ hαr hα
      obtain ⟨A, hAL, hAc, hAq⟩ := uc22s217u3b_lift_elem hr hr2 hq hq2 hyN hyr hzo hz
      have hN := UC6S898.normalizer_map_conj_le g⁻¹ hNx
      rw [MonoidHom.map_zpowers, hconj] at hN
      have hAM : A ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom :=
        (hAc.trans (centralizer_le_normalizer _)).trans hN
      have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
      apply hsp.2.2 g⁻¹ hg'
      have hAq' : q ∣ Nat.card A := by rw [hAq]
      exact hAq'.trans (Subgroup.card_dvd_of_le (le_inf (hAL.trans hLM) hAM))
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hxr hxU (Subgroup.zpowers_le.2 hxT)

theorem uc22s217u3b_not_isSU3
    (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hSg : SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hCen : UCK.U3Center)
    (hSyl : UCK.U3Syl) (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hn : ¬ IsPowTwo n)
    (hn3 : n ≠ 3) : ¬ IsSU3 (Bar2 L) n := by
  intro hX
  have hn2 : 2 ≤ n := UCK.u3Range (Bar2 L) n hX
  obtain ⟨s, r, hs, hsn, hr, hrs, hrn⟩ := uc22s217u3b_exists_sr (by omega) hn
  obtain ⟨q, hq, hq3, hqn⟩ := UC6S898.exists_prime_gt_three_dvd hn2 hn3
  have hq2 : q ≠ 2 := by omega
  have hZq : ¬ q ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hX))
    omega
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  obtain ⟨E, hEL, hEel, hEc⟩ := exists_elemAbelian_sq_of_isSU3 hSyl hX hq hq3 hqn
  have h4 := calCRankTwice D.M L hL hnN' q hq hq2 hZq E hEL hEel 2 hEc
  have hqσ : q ∈ D.sig := hSg.four_mem q hq hq2 (by omega)
  have hsp := sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hqσ
  have hfix : ∀ (X : Type) [Group X] [Finite X], IsSU3 X n → ∀ α : MulAut X, α ^ r = 1 →
      α ∈ (MulAut.conj : X →* MulAut X).range → ∃ z : X, orderOf z = q ∧ α z = z :=
    fun X _ _ hK α hαr hα => hFI X n hK s hs hsn r hr hrs α hαr hα q hq hq3 hqn
  exact uc22s217u3b_false_of D Ch h211 hH c hSg hCen hFF hL hnN hX hs hsn hr hrs hrn hq hq2 hsp
    (h76 q hqσ hsp) hfix (uc22s217u3b_rank_gt_three hCen hFF hs hsn hr hrs hrn hq hq3 hfix)

end CFSG.LocalAnalysis.UniquenessCase.UC22
