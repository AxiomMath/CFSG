module

public import CFSG.Quasithin.H13.AS91Sec7FourA
public import CFSG.Quasithin.H13.AS91Sec7FourB
public import CFSG.Quasithin.H13.AS91Sec7Three
public import CFSG.Quasithin.H13.AS91Sec7Smul

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace M24G

theorem trio_eq_of_two {a b : Finset (Finset (Fin 24))} (ha : IsTrio a) (hb : IsTrio b)
    {o₁ o₂ : Finset (Fin 24)} (h₁a : o₁ ∈ a) (h₂a : o₂ ∈ a) (h₁b : o₁ ∈ b) (h₂b : o₂ ∈ b)
    (h12 : o₁ ≠ o₂) : a = b := by
  have key : ∀ T : Finset (Finset (Fin 24)), IsTrio T → o₁ ∈ T → o₂ ∈ T →
      T = {o₁, o₂, Finset.univ \ (o₁ ∪ o₂)} := by
    intro T hT hT1 hT2
    have hcard : ((T.erase o₁).erase o₂).card = 1 := by
      have h1 := Finset.card_erase_of_mem hT1
      have h2 := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h12.symm, hT2⟩ :
        o₂ ∈ T.erase o₁)
      have h3 := hT.1
      omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hcard
    have heT : e ∈ T ∧ e ≠ o₁ ∧ e ≠ o₂ := by
      have hm : e ∈ (T.erase o₁).erase o₂ := by
        rw [he]
        exact Finset.mem_singleton_self e
      obtain ⟨h2e, hm'⟩ := Finset.mem_erase.1 hm
      obtain ⟨h1e, heT⟩ := Finset.mem_erase.1 hm'
      exact ⟨heT, h1e, h2e⟩
    have hsub : ({o₁, o₂, e} : Finset (Finset (Fin 24))) ⊆ T := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact hT1
      · exact hT2
      · exact heT.1
    have hc3 : ({o₁, o₂, e} : Finset (Finset (Fin 24))).card = 3 :=
      Finset.card_eq_three.2 ⟨o₁, o₂, e, h12, Ne.symm heT.2.1, Ne.symm heT.2.2, rfl⟩
    have hTeq : T = {o₁, o₂, e} :=
      (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hc3, hT.1]))).symm
    have hF : e = Finset.univ \ (o₁ ∪ o₂) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
      constructor
      · intro hxe
        exact ⟨fun hx1 => Finset.disjoint_left.1 (hT.2.2.1 e heT.1 o₁ hT1 heT.2.1) hxe hx1,
          fun hx2 => Finset.disjoint_left.1 (hT.2.2.1 e heT.1 o₂ hT2 heT.2.2) hxe hx2⟩
      · rintro ⟨hx1, hx2⟩
        have hxU : x ∈ T.biUnion id := by
          rw [hT.2.2.2]
          exact Finset.mem_univ x
        obtain ⟨d, hdT, hxd⟩ := Finset.mem_biUnion.1 hxU
        rw [hTeq] at hdT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdT
        rcases hdT with rfl | rfl | rfl
        · exact absurd hxd hx1
        · exact absurd hxd hx2
        · exact hxd
    rw [hF] at hTeq
    exact hTeq
  exact (key a ha h₁a h₂a).trans (key b hb h₁b h₂b).symm

section Pencil


theorem mem_of_not_disjoint_pencil {U t a b : Finset (Finset (Fin 24))} (hU : IsSextet U)
    (ht : t ∈ triosOf U) (ha : a ∈ triosOf U) (hb : b ∈ triosOf U) {o : Finset (Fin 24)}
    (hoa : o ∈ a) (hob : o ∈ b) (hab : a ≠ b) (hta : ¬ Disjoint t a) (htb : ¬ Disjoint t b) :
    o ∈ t := by
  by_cases hta' : t = a
  · rw [hta']
    exact hoa
  by_cases htb' : t = b
  · rw [htb']
    exact hob
  have hab' : ¬ Disjoint a b := Finset.not_disjoint_iff.2 ⟨o, hoa, hob⟩
  obtain ⟨p, -, hpt, hpa, hpb⟩ := exists_common_octad hU ht ha hb hta' htb' hab hta htb hab'
  by_cases hpo : p = o
  · rw [← hpo]
    exact hpt
  exact absurd (trio_eq_of_two (mem_triosOf.1 ha).1 (mem_triosOf.1 hb).1 hpa hoa hpb hob hpo) hab

end Pencil

end M24G

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem comp_refl_of {x u y : G ⧸ c.G1} (hxu : c.Delta.Adj x u) (hyu : c.Delta.Adj y u) :
    comp c.Delta x u y u :=
  ⟨⟨hxu, hyu⟩, ⟨hxu, hyu⟩, SimpleGraph.Reachable.refl _⟩

theorem comp_of_adj_pt {x u y w : G ⧸ c.G1} (hxu : c.Delta.Adj x u) (hyu : c.Delta.Adj y u)
    (hxw : c.Delta.Adj x w) (hyw : c.Delta.Adj y w) (huw : c.Delta.Adj u w) :
    comp c.Delta x u y w :=
  ⟨⟨hxu, hyu⟩, ⟨hxw, hyw⟩, SimpleGraph.Adj.reachable huw⟩

theorem exists_fix_conj_E (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y y' : G ⧸ c.G1}
    {L M : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M)
    (hM3 : M ∈ c.deltaAt 3 u L) (hy'M : c.OnL y' M) (hxu : x ≠ u) (hyu : y ≠ u)
    (hy'u : y' ≠ u) :
    ∃ e : G, e • u = u ∧ e • x = x ∧ e • y' = y ∧ ∀ n, c.OnL u n → e • n = n := by
  obtain ⟨g, hgu, hgL⟩ := c.exists_frame hLu
  have hX : c.OnL (g⁻¹ • x) c.l0 := by
    have h := (cInc_smul c.G1 c.G2 g⁻¹ x L).2 hLx
    rwa [← hgL, inv_smul_smul] at h
  have hXne : g⁻¹ • x ≠ c.x0 := fun h => hxu (by rw [← hgu, ← h, smul_inv_smul])
  have hp0 : g⁻¹ • y' ≠ c.x0 := fun h => hy'u (by rw [← hgu, ← h, smul_inv_smul])
  have hq0 : g⁻¹ • y ≠ c.x0 := fun h => hyu (by rw [← hgu, ← h, smul_inv_smul])
  have hk : g⁻¹ • M ∈ c.delta 3 := (c.mem_deltaAt_iff_frame hgu hgL).1 hM3
  have hpM : c.OnL (g⁻¹ • y') (g⁻¹ • M) := (cInc_smul c.G1 c.G2 g⁻¹ y' M).2 hy'M
  have hqM : c.OnL (g⁻¹ • y) (g⁻¹ • M) := (cInc_smul c.G1 c.G2 g⁻¹ y M).2 hMy
  obtain ⟨-, -, -, -, -, -, -, h6⟩ := hI.s54 G z hJ c (g⁻¹ • x) hX hXne
  obtain ⟨e, he, hep⟩ := h6 3 (by decide) (g⁻¹ • M) hk (g⁻¹ • y') hpM (g⁻¹ • y) hqM hp0 hq0
  obtain ⟨heE, hest⟩ := Subgroup.mem_inf.1 he
  have hfix : e • (g⁻¹ • x) = g⁻¹ • x := MulAction.mem_stabilizer_iff.1 hest
  have he1 : e • c.x0 = c.x0 := c.smul_x0_of_mem (c.E_le_G1 heE)
  have hu1 : g⁻¹ • u = c.x0 := by rw [← hgu, inv_smul_smul]
  refine ⟨g * e * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hu1, he1, hgu]
  · rw [mul_smul, mul_smul, hfix, smul_inv_smul]
  · rw [mul_smul, mul_smul, hep, smul_inv_smul]
  · intro n hn
    have hn0 : c.OnL c.x0 (g⁻¹ • n) := c.onL_x0_inv_smul hgu hn
    rw [mul_smul, mul_smul, c.E_smul_line hn0 heE, smul_inv_smul]

theorem exists_claim_star (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v : G ⧸ c.G1}
    {L M l' : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L) (hMu : c.OnL u M)
    (hMy : c.OnL y M) (hM3 : M ∈ c.deltaAt 3 u L) (hxu : c.Delta.Adj x u)
    (huy : c.Delta.Adj u y) (hl'u : c.OnL u l') (hvl' : c.OnL v l') (hvu : v ≠ u)
    (hxv : c.Delta.Adj x v) (hMl' : M ∈ c.deltaAt 1 u l') :
    ∃ u', c.OnL u' l' ∧ u' ≠ u ∧ c.Delta.Adj x u' ∧ c.Delta.Adj y u' := by
  have hcard := c.stmt7_1_one hI.s54 hJ hl'u hvl' hvu hMl'
  have h1 : 1 < ({a | c.OnL a M ∧ c.Delta.Adj v a} : Set (G ⧸ c.G1)).ncard := by
    rw [hcard]
    norm_num
  obtain ⟨y', ⟨hy'M, hvy'⟩, hy'u⟩ := Set.exists_ne_of_one_lt_ncard h1 u
  obtain ⟨e, he1, he2, he3, he4⟩ :=
    c.exists_fix_conj_E hI hJ hLu hLx hMu hMy hM3 hy'M hxu.ne huy.ne.symm hy'u
  have hl'' : e • l' = l' := he4 l' hl'u
  have hu'l' : c.OnL (e • v) l' := by
    have h := (cInc_smul c.G1 c.G2 e v l').2 hvl'
    rwa [hl''] at h
  refine ⟨e • v, hu'l', fun h => hvu ((MulAction.injective e) (h.trans he1.symm)), ?_, ?_⟩
  · have h := (c.adj_smul_iff e).2 hxv
    rwa [he2] at h
  · have h := (c.adj_smul_iff e).2 hvy'.symm
    rwa [he3] at h

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section Basic


theorem not_onL_of_disjoint (hI : Sec7Inputs) (hJ : HypJ4 G z) {x v : G ⧸ c.G1}
    {L' m : G ⧸ c.G2} (hvx : v ≠ x) (hLv : c.OnL v L') (hLx : c.OnL x L') (hm : c.OnL x m)
    {g : G} (hg : g • c.x0 = x) (hdis : Disjoint (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • L'))) :
    ¬ c.OnL v m := by
  intro hvm
  have hmL : m = L' := c.eq_of_onL hI.lineU hJ hvx hvm hm hLv hLx
  rw [hmL] at hdis
  have hc : (ρ.trio (g⁻¹ • L')).card = 3 := (ρ.isTrio_trio_at hg hLx).1
  rw [disjoint_self.1 hdis] at hc
  simp at hc

end Basic

section Spread


include ρ in
theorem witness_of_spread (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v : G ⧸ c.G1}
    (h2v : c.Rh 2 x v y) (h1v : ¬ c.Rh 1 x v y) (hcomp : comp c.Delta x u y v)
    {π : G ⧸ c.G3} (hvπ : c.OnP v π) {L' M' : G ⧸ c.G2} (hLv : c.OnL v L')
    (hLx' : c.OnL x L') (hLπ' : c.LnP L' π) (hMv : c.OnL v M') (hMy : c.OnL y M')
    (h3 : M' ∈ c.deltaAt 3 v L') (hMπ : c.MeetsP v M' π) {m : G ⧸ c.G2} (hxm : c.OnL x m)
    (hmπ : c.LnP m π) (hvm : ¬ c.OnL v m) (hadj : ∀ a, c.OnL a m → c.Delta.Adj v a) :
    ∃ w, c.OnL w m ∧ dSet c.Delta c.Rh 1 x u y w := by
  obtain ⟨hxv, hvy, -, -⟩ := c.rh21_path h2v h1v
  have hnxy : ¬ c.Delta.Adj x y := c.rh21_not_adj h1v hxv hvy
  obtain ⟨g, hg, hgL⟩ := c.exists_frame hLv
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hvπ
  have hκ := (ρ.meetsP_iff_kappa_one hg hMv hvπ).1 hMπ
  obtain ⟨o, hoM, hoU⟩ := M24G.exists_octad_of_kappa_one hκ
  obtain ⟨D, hD, hDiff⟩ := ρ.stmt7_3_two hI hJ hg hvπ hmπ hvm hadj
  obtain ⟨t, ht⟩ := Finset.card_eq_one.1 (M24G.stmt2_1_2_triosOf hU D hD o hoU)
  have htmem : t ∈ D.filter (o ∈ ·) := by
    rw [ht]
    exact Finset.mem_singleton_self t
  obtain ⟨htD, hot⟩ := Finset.mem_filter.1 htmem
  obtain ⟨hIT, hTU, -⟩ := (M24G.mem_spreadsOf.1 hD).2 t htD
  obtain ⟨k, hvk, hkπ, hkt⟩ :=
    ρ.exists_line_of_mem_triosOf hg hvπ (M24G.mem_triosOf.2 ⟨hIT, hTU⟩)
  have hk1 : k ∈ c.deltaAt 1 v M' :=
    (ρ.octad_iff hg hLv hMv h3 hvπ hLπ' hvk hkπ hκ hoM hoU).2.2 (by rw [hkt]; exact hot)
  obtain ⟨w', hw'm, hw'k⟩ := (hDiff k hvk).2 (by rw [hkt]; exact htD)
  have hw'x : w' ≠ x := by
    intro e
    rw [e] at hw'k
    have hkL : k = L' := c.eq_of_onL hI.lineU hJ hxv.ne.symm hvk hw'k hLv hLx'
    rw [hkL] at hk1
    obtain ⟨i, -, hi⟩ := ρ.deltaAt_existsUnique hMv hLv
    exact absurd ((hi 1 hk1).trans (hi 3 (ρ.deltaAt_symm 3 hLv hMv h3)).symm) (by decide)
  have hxw' : c.Delta.Adj x w' := c.adj_of_onL (Ne.symm hw'x) hxm hw'm
  have hvw' : c.Delta.Adj v w' := hadj w' hw'm
  have hyw' : y ≠ w' := fun e => hnxy (by rw [e]; exact hxw')
  have hCoL : c.CoL M' k := Loc49.CoL.symm c
    ((ρ.coL_iff_delta_one_of_meetsP hLv hMv h3 hvπ hLπ' hMπ hvk hkπ).2 hk1)
  have hR : c.Rh 1 y v w' :=
    c.rh_one_iff.2 (Or.inr ⟨hvy.symm, hvw', hyw', M', k, hMv, hMy, hvk, hw'k, hCoL⟩)
  exact ⟨w', hw'm, Or.inr ⟨hxw', v, hcomp, hR⟩⟩

end Spread

section Main


include ρ in
theorem stmt7_4_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L)
    (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π) (hLπ : c.LnP L π)
    (hMπ : c.MeetsP u M π) {m : G ⧸ c.G2} (hm : c.OnL x m) (hmπ : c.LnP m π) :
    ∃ w, c.OnL w m ∧ dSet c.Delta c.Rh 1 x u y w := by
  obtain ⟨hxu, huy, -, -⟩ := c.rh21_path h2 h1
  have hnxy : ¬ c.Delta.Adj x y := c.rh21_not_adj h1 hxu huy
  have hxπ : c.OnP x π := c.inc_pt_plane hLx hLπ
  have hM3 : M ∈ c.deltaAt 3 u L := c.rh21_mem_delta3 hI hJ h2 h1 hLu hLx hMu hMy
  have hcompU : comp c.Delta x u y u := c.comp_refl_of hxu huy.symm
  obtain ⟨l', hl'u, hl'π, hl'M, hl'L, -⟩ :=
    ρ.exists_delta_one_of_meetsP hLu hMu hM3 hπu hLπ hMπ
  have hMl' : M ∈ c.deltaAt 1 u l' := ρ.deltaAt_symm 1 hMu hl'u hl'M
  have hl'L' : l' ≠ L := by
    intro e
    rw [e] at hl'L
    obtain ⟨i, -, hi⟩ := ρ.deltaAt_existsUnique hLu hLu
    have h0 : L ∈ c.deltaAt 0 u L := (ρ.mem_deltaAt_zero_iff hLu hLu).2 rfl
    exact absurd ((hi 0 h0).trans (hi 1 hl'L).symm) (by decide)
  have hxl' : ¬ c.OnL x l' := fun h =>
    hl'L' (c.eq_of_onL hI.lineU hJ hxu.ne.symm hl'u h hLu hLx)
  have h3 : {a | c.OnL a l' ∧ c.Delta.Adj x a}.ncard = 3 :=
    c.stmt7_1_one hI.s54 hJ hLu hLx hxu.ne hl'L
  obtain ⟨gx, hgx, -⟩ := c.exists_frame hLx
  obtain ⟨o, hoU, hiff⟩ := ρ.stmt7_3_one hI hJ hgx hxπ hl'π hxl' h3
  have h31 : 1 < ({a | c.OnL a l' ∧ c.Delta.Adj x a} : Set (G ⧸ c.G1)).ncard := by
    rw [h3]
    norm_num
  obtain ⟨v, ⟨hvl', hxv⟩, hvu⟩ := Set.exists_ne_of_one_lt_ncard h31 u
  obtain ⟨u', hu'l', hu'u, hxu', hyu'⟩ :=
    c.exists_claim_star hI hJ hLu hLx hMu hMy hM3 hxu huy hl'u hvl' hvu hxv hMl'
  have huu' : c.Delta.Adj u u' := c.adj_of_onL (Ne.symm hu'u) hl'u hu'l'
  obtain ⟨h2', h1'⟩ := ρ.claimA hI hJ h2 h1 hxu' huu' hyu' hLu hLx hMu hMy hl'u hu'l'
    (Or.inl hl'L) hl'M
  obtain ⟨L', hxL', hu'L'⟩ := c.exists_onL_of_adj hxu'
  obtain ⟨M', hyM', hu'M'⟩ := c.exists_onL_of_adj hyu'
  have hu'π : c.OnP u' π := c.inc_pt_plane hu'l' hl'π
  have hL'π : c.LnP L' π := c.lnP_of_adj hI.gamma2 hJ hxπ hu'π hxu' hxL' hu'L'
  have hM'l' : M' ∈ c.deltaAt 1 u' l' :=
    (hI.s56 G z hJ c u u' y huu' hyu'.symm huy).2.2 l' M M' 1 hl'u hu'l' hMu hMy hu'M' hyM'
      hMl'
  have hl'M' : l' ∈ c.deltaAt 1 u' M' := ρ.deltaAt_symm 1 hu'l' hu'M' hM'l'
  have h3' : M' ∈ c.deltaAt 3 u' L' := c.rh21_mem_delta3 hI hJ h2' h1' hu'L' hxL' hu'M' hyM'
  have hMπ' : c.MeetsP u' M' π := by
    unfold Loc49.MeetsP
    exact ⟨fun hM'π => c.rh21_not_onP hI hJ h2 h1 hxπ (c.inc_pt_plane hyM' hM'π),
      l', hu'l', hl'π, hl'M'⟩
  have hcomp' : comp c.Delta x u y u' := c.comp_of_adj_pt hxu huy.symm hxu' hyu' huu'
  by_cases hot : o ∈ ρ.trio (gx⁻¹ • m)
  ·
    obtain ⟨w, hwl', hxw, hwm⟩ := (hiff m hm).2 ⟨hmπ, hot⟩
    refine ⟨w, hwm, ?_⟩
    by_cases hwu : w = u
    · rw [hwu]
      exact Or.inl hcompU
    · have huw : c.Delta.Adj u w := c.adj_of_onL (Ne.symm hwu) hl'u hwl'
      have hyw : y ≠ w := fun e => hnxy (by rw [e]; exact hxw)
      have hCoL : c.CoL M l' := Loc49.CoL.symm c
        ((ρ.coL_iff_delta_one_of_meetsP hLu hMu hM3 hπu hLπ hMπ hl'u hl'π).2 hl'M)
      exact Or.inr ⟨hxw, u, hcompU,
        c.rh_one_iff.2 (Or.inr ⟨huy.symm, huw, hyw, M, l', hMu, hMy, hl'u, hwl', hCoL⟩)⟩
  · have hU' : IsSextet (ρ.sext (gx⁻¹ • π)) := ρ.isSextet_sext_at hgx hxπ
    have hLL' : L ≠ L' := by
      intro e
      apply hl'L'
      exact c.eq_of_onL hI.lineU hJ (Ne.symm hu'u) hl'u hu'l' hLu (by rw [e]; exact hu'L')
    have hab : ρ.trio (gx⁻¹ • L) ≠ ρ.trio (gx⁻¹ • L') := fun e =>
      hLL' (ρ.eq_of_trio_at hgx hLx hxL' e)
    have hoa : o ∈ ρ.trio (gx⁻¹ • L) := ((hiff L hLx).1 ⟨u, hl'u, hxu, hLu⟩).2
    have hob : o ∈ ρ.trio (gx⁻¹ • L') := ((hiff L' hxL').1 ⟨u', hu'l', hxu', hu'L'⟩).2
    have hpen : Disjoint (ρ.trio (gx⁻¹ • m)) (ρ.trio (gx⁻¹ • L)) ∨
        Disjoint (ρ.trio (gx⁻¹ • m)) (ρ.trio (gx⁻¹ • L')) := by
      by_contra hcon
      rw [not_or] at hcon
      exact hot (M24G.mem_of_not_disjoint_pencil hU'
        (ρ.trio_mem_triosOf hgx hxπ hm hmπ) (ρ.trio_mem_triosOf hgx hxπ hLx hLπ)
        (ρ.trio_mem_triosOf hgx hxπ hxL' hL'π) hoa hob hab hcon.1 hcon.2)
    rcases hpen with hdis | hdis
    ·
      have hδ2 : m ∈ c.deltaAt 2 x L :=
        (ρ.mem_deltaAt_two_iff_at hgx hLx hm).2 ⟨hdis, ⟨π, hLπ, hmπ⟩⟩
      exact ρ.witness_of_spread hI hJ h2 h1 hcompU hπu hLu hLx hLπ hMu hMy hM3 hMπ hm hmπ
        (ρ.not_onL_of_disjoint hI hJ hxu.ne.symm hLu hLx hm hgx hdis)
        (fun a ha => c.stmt7_1_two hI.s54 hJ hLx hLu hxu.ne.symm hδ2 ha)
    ·
      have hδ2 : m ∈ c.deltaAt 2 x L' :=
        (ρ.mem_deltaAt_two_iff_at hgx hxL' hm).2 ⟨hdis, ⟨π, hL'π, hmπ⟩⟩
      exact ρ.witness_of_spread hI hJ h2' h1' hcomp' hu'π hu'L' hxL' hL'π hu'M' hyM' h3' hMπ' hm
        hmπ (ρ.not_onL_of_disjoint hI hJ hxu'.ne.symm hu'L' hxL' hm hgx hdis)
        (fun a ha => c.stmt7_1_two hI.s54 hJ hxL' hu'L' hxu'.ne.symm hδ2 ha)

end Main

end ResM24

end CFSG.Quasithin.H13.AS91
