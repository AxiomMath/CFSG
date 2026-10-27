module

public import CFSG.Quasithin.H13.AS91Sec5KerFacts
public import CFSG.Quasithin.H13.AS91Sec7Smul

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio M24g)

theorem exists_third_of_ncard_three {α : Type*} {S : Set α} (h3 : S.ncard = 3) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ w ∈ S, w ≠ x ∧ w ≠ y ∧ ∀ a ∈ S, a = x ∨ a = y ∨ a = w := by
  have hpair : ({x, y} : Set α) ⊆ S :=
    Set.insert_subset_iff.2 ⟨hx, Set.singleton_subset_iff.2 hy⟩
  have hd : (S \ {x, y}).ncard = 1 := by
    rw [Set.ncard_sdiff hpair, h3, Set.ncard_pair hxy]
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.1 hd
  have hwmem : w ∈ S \ {x, y} := by
    rw [hw]
    exact Set.mem_singleton w
  refine ⟨w, hwmem.1, fun e => hwmem.2 (by simp [e]), fun e => hwmem.2 (by simp [e]), ?_⟩
  intro a ha
  by_cases hax : a = x
  · exact Or.inl hax
  by_cases hay : a = y
  · exact Or.inr (Or.inl hay)
  have ha' : a ∈ S \ {x, y} := ⟨ha, by simp [hax, hay]⟩
  rw [hw] at ha'
  exact Or.inr (Or.inr (Set.mem_singleton_iff.1 ha'))

theorem exists_swap_trio_delta
    {t t' : Finset (Finset (Fin 24))} (ht : IsTrio t) (ht' : IsTrio t') {i : Fin 5}
    (h : M24G.Delta t t' i) :
    ∃ τ ∈ M24g, τ • t = t' ∧ τ • t' = t := by
  obtain ⟨a, ha, hat⟩ := M24G.trio_transitive ht
  obtain ⟨b, hb, hbt⟩ := M24G.trio_transitive ht'
  have hg : b⁻¹ * a ∈ M24g := mul_mem (inv_mem hb) ha
  have hgt : (b⁻¹ * a) • t = t' := by
    rw [mul_smul, hat, ← hbt, inv_smul_smul]
  have hs : M24G.Delta t' ((b⁻¹ * a) • t') i := by
    have h1 := (M24G.delta_smul_iff hg i).2 h
    rwa [hgt] at h1
  have hst : IsTrio ((b⁻¹ * a) • t') := (M24G.isTrio_smul_iff hg).2 ht'
  obtain ⟨g, hgM, hgt', hgs⟩ :=
    M24G.delta_orbit ht' hst ht hs (M24G.delta_symm ht ht' h)
  refine ⟨g * (b⁻¹ * a), mul_mem hgM hg, ?_, ?_⟩
  · rw [mul_smul, hgt, hgt']
  · rw [mul_smul, hgs]

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem smul_ne_x0 {g : G} (hg : g • c.x0 = c.x0) {b : G ⧸ c.G1} (hb : b ≠ c.x0) :
    g • b ≠ c.x0 := by
  intro e
  apply hb
  calc b = g⁻¹ • g • b := (inv_smul_smul g b).symm
    _ = g⁻¹ • c.x0 := by rw [e]
    _ = c.x0 := inv_smul_eq_iff.2 hg.symm

theorem exists_swap_on_line {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) {b d : G ⧸ c.G1}
    (hbm : c.OnL b m) (hdm : c.OnL d m) (hbx : b ≠ c.x0) (hdx : d ≠ c.x0) :
    ∃ g : G, g • c.x0 = c.x0 ∧ g • b = d ∧ g • d = b := by
  classical
  obtain ⟨h, hh⟩ := c.exists_G1_smul_l0 hm
  have hkx : (h : G)⁻¹ • c.x0 = c.x0 := c.smul_x0_of_mem (inv_mem h.2)
  have hkm : (h : G)⁻¹ • m = c.l0 := by rw [← hh, inv_smul_smul]
  have hb₁ : (h : G)⁻¹ • b ∈ c.ptsL := by
    have h1 := (cInc_smul c.G1 c.G2 (h : G)⁻¹ b m).2 hbm
    rwa [hkm] at h1
  have hd₁ : (h : G)⁻¹ • d ∈ c.ptsL := by
    have h1 := (cInc_smul c.G1 c.G2 (h : G)⁻¹ d m).2 hdm
    rwa [hkm] at h1
  let P₁ : ↥c.ptsL := ⟨(h : G)⁻¹ • b, hb₁⟩
  let P₂ : ↥c.ptsL := ⟨(h : G)⁻¹ • d, hd₁⟩
  let X₀ : ↥c.ptsL := ⟨c.x0, c.x0_mem_ptsL⟩
  have hX₁ : X₀ ≠ P₁ := fun e => c.smul_ne_x0 hkx hbx (congrArg Subtype.val e).symm
  have hX₂ : X₀ ≠ P₂ := fun e => c.smul_ne_x0 hkx hdx (congrArg Subtype.val e).symm
  obtain ⟨s, -, hs⟩ := c.exists_CZ_perm (Equiv.swap P₁ P₂)
  have hsx : s • c.x0 = c.x0 := by
    have h1 := hs X₀
    rw [Equiv.swap_apply_of_ne_of_ne hX₁ hX₂] at h1
    exact h1
  have hsb : s • ((h : G)⁻¹ • b) = (h : G)⁻¹ • d := by
    have h1 := hs P₁
    rw [Equiv.swap_apply_left] at h1
    exact h1
  have hsd : s • ((h : G)⁻¹ • d) = (h : G)⁻¹ • b := by
    have h1 := hs P₂
    rw [Equiv.swap_apply_right] at h1
    exact h1
  refine ⟨(h : G) * s * (h : G)⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hkx, hsx, c.smul_x0_of_mem h.2]
  · rw [mul_smul, mul_smul, hsb, smul_inv_smul]
  · rw [mul_smul, mul_smul, hsd, smul_inv_smul]

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem exists_swap_lines
    {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    {i : Fin 5} (h : M24G.Delta (ρ.trio m) (ρ.trio n) i) :
    ∃ g : G, g • c.x0 = c.x0 ∧ g • m = n ∧ g • n = m := by
  obtain ⟨τ, hτ, h1, h2⟩ := exists_swap_trio_delta (ρ.isTrio_trio hm) (ρ.isTrio_trio hn) h
  obtain ⟨h0, hφ⟩ := ρ.exists_φ_eq hτ
  rw [← hφ] at h1 h2
  have hm' : c.OnL c.x0 ((h0 : G) • m) := (c.cInc_x0_smul h0.2).2 hm
  have hn' : c.OnL c.x0 ((h0 : G) • n) := (c.cInc_x0_smul h0.2).2 hn
  refine ⟨(h0 : G), c.smul_x0_of_mem h0.2, ?_, ?_⟩
  · apply ρ.trio_injOn hm' hn
    rw [ρ.trio_smul_line h0 hm]
    exact h1
  · apply ρ.trio_injOn hn' hm
    rw [ρ.trio_smul_line h0 hn]
    exact h2

include ρ in
theorem exists_swap_of_deltaAt
    {i : Fin 5} {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (h : n ∈ c.deltaAt i c.x0 m) : ∃ g : G, g • c.x0 = c.x0 ∧ g • m = n ∧ g • n = m := by
  have key := (ρ.mem_deltaAt_iff i (one_smul G c.x0) hm hn).1 h
  simp only [inv_one, one_smul] at key
  exact ρ.exists_swap_lines hm hn key

end ResM24

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_g1 (ρ : ResM24 c)
    {i : Fin 5} {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (hi : n ∈ c.deltaAt i c.x0 m) {b d : G ⧸ c.G1} (hbm : c.OnL b m) (hdn : c.OnL d n)
    (hbx : b ≠ c.x0) (hdx : d ≠ c.x0) :
    ∃ g : G, g • c.x0 = c.x0 ∧ g • b = d ∧ c.OnL (g • d) m := by
  obtain ⟨g₀, hg₀x, hg₀m, hg₀n⟩ := ρ.exists_swap_of_deltaAt hm hn hi
  have hb₀ : c.OnL (g₀ • b) n := by
    rw [← hg₀m]
    exact (cInc_smul c.G1 c.G2 g₀ b m).2 hbm
  have hd₀ : c.OnL (g₀ • d) m := by
    rw [← hg₀n]
    exact (cInc_smul c.G1 c.G2 g₀ d n).2 hdn
  obtain ⟨e₁, he₁, he₁b⟩ := c.E_transitive_line hn hb₀ (c.smul_ne_x0 hg₀x hbx) hdn hdx
  refine ⟨e₁ * g₀, ?_, ?_, ?_⟩
  · rw [mul_smul, hg₀x, c.smul_x0_of_mem (c.E_le_G1 he₁)]
  · rw [mul_smul, he₁b]
  · rw [mul_smul]
    have h1 := (cInc_smul c.G1 c.G2 e₁ (g₀ • d) m).2 hd₀
    rwa [ρ.E_smul_line he₁ hm] at h1

theorem core_x0
    (hJ : HypJ4 G z) (hG2 : Stmt5_Gamma2) (h55 : Stmt5_5)
    (h54 : Stmt5_4) (ρ : ResM24 c) (hK : c.KerFacts) {b d : G ⧸ c.G1}
    (hb : c.Delta.Adj c.x0 b) (hd : c.Delta.Adj c.x0 d) (hbd : c.Delta.Adj b d) :
    ∃ g : G, g • c.x0 = c.x0 ∧ g • b = d ∧ g • d = b := by
  obtain ⟨-, m, hx0m, hbm⟩ := colGraph_adj.mp hb
  obtain ⟨-, n, hx0n, hdn⟩ := colGraph_adj.mp hd
  have hbx : b ≠ c.x0 := hb.ne.symm
  have hdx : d ≠ c.x0 := hd.ne.symm
  by_cases hmn : m = n
  · rw [← hmn] at hdn
    exact c.exists_swap_on_line hx0m hbm hdn hbx hdx
  obtain ⟨p, hx0p, hbp, hdp⟩ := h55 G z hJ c c.x0 b d hb hbd hd
  have hmp : c.LnP m p := c.lnP_of_adj hG2 hJ hx0p hbp hb hx0m hbm
  have hnp : c.LnP n p := c.lnP_of_adj hG2 hJ hx0p hdp hd hx0n hdn
  rcases (ρ.coL_iff_deltaAt hx0m hx0n).1 ⟨p, hmp, hnp⟩ with h0 | h1 | h2
  · exact absurd ((ρ.mem_deltaAt_zero_iff hx0m hx0n).1 h0).symm hmn
  ·
    obtain ⟨g₁, hg₁x, hg₁b, hg₁d⟩ := c.exists_g1 ρ hx0m hx0n h1 hbm hdn hbx hdx
    have hδ : m ∈ c.deltaAt 1 c.x0 n := ρ.deltaAt_symm 1 hx0m hx0n h1
    have hcard := c.stmt7_1_one h54 hJ hx0n hdn hdx hδ
    have hx0S : c.x0 ∈ {a | c.OnL a m ∧ c.Delta.Adj d a} := ⟨hx0m, hd.symm⟩
    have hbS : b ∈ {a | c.OnL a m ∧ c.Delta.Adj d a} := ⟨hbm, hbd.symm⟩
    obtain ⟨b', -, -, -, hS⟩ := exists_third_of_ncard_three hcard hx0S hbS hb.ne
    have hg₁S : g₁ • d ∈ {a | c.OnL a m ∧ c.Delta.Adj d a} := by
      refine ⟨hg₁d, ?_⟩
      have h1' := (c.adj_smul_iff g₁).2 hbd
      rwa [hg₁b] at h1'
    rcases hS (g₁ • d) hg₁S with h | h | h
    · exact absurd h (c.smul_ne_x0 hg₁x hdx)
    · exact ⟨g₁, hg₁x, hg₁b, h⟩
    ·
      have hnle := hK.not_le hx0m hx0n hmn
      obtain ⟨e, he_n, he_m⟩ : ∃ e ∈ c.Eker n, e ∉ c.Eker m := by
        by_contra hcon
        push Not at hcon
        exact hnle (fun e he => hcon e he)
      have he_E : e ∈ c.E := ((c.mem_Eker).1 he_n).1
      have hed : e • d = d := ((c.mem_Eker).1 he_n).2 d hdn
      have hex : e • c.x0 = c.x0 := c.smul_x0_of_mem (c.E_le_G1 he_E)
      have heb : e • b ≠ b := by
        intro h'
        apply he_m
        rw [← c.E_inf_stab_eq_Eker hx0m hbm hbx]
        exact Subgroup.mem_inf.2 ⟨he_E, MulAction.mem_stabilizer_iff.2 h'⟩
      have hebS : e • b ∈ {a | c.OnL a m ∧ c.Delta.Adj d a} := by
        refine ⟨?_, ?_⟩
        · have h1' := (cInc_smul c.G1 c.G2 e b m).2 hbm
          rwa [ρ.E_smul_line he_E hx0m] at h1'
        · have h1' := (c.adj_smul_iff e).2 hbd.symm
          rwa [hed] at h1'
      have hebb' : e • b = b' := by
        rcases hS (e • b) hebS with h' | h' | h'
        · exact absurd (MulAction.injective e (h'.trans hex.symm)) hb.ne.symm
        · exact absurd h' heb
        · exact h'
      have hee : e * e = 1 := by
        rw [← pow_two]
        exact c.E_elem.2 e he_E
      refine ⟨e * g₁, ?_, ?_, ?_⟩
      · rw [mul_smul, hg₁x, hex]
      · rw [mul_smul, hg₁b, hed]
      · rw [mul_smul, h, ← hebb', ← mul_smul, hee, one_smul]
  ·
    obtain ⟨g₁, hg₁x, hg₁b, hg₁d⟩ := c.exists_g1 ρ hx0m hx0n h2 hbm hdn hbx hdx
    have hδ : m ∈ c.deltaAt 2 c.x0 n := ρ.deltaAt_symm 2 hx0m hx0n h2
    obtain ⟨e₂, he₂, he₂d⟩ :=
      hK.smul_two hx0n hx0m (Or.inl hδ) hg₁d (c.smul_ne_x0 hg₁x hdx) hbm hbx
    have he₂E : e₂ ∈ c.E := ((c.mem_Eker).1 he₂).1
    have he₂d' : e₂ • d = d := ((c.mem_Eker).1 he₂).2 d hdn
    refine ⟨e₂ * g₁, ?_, ?_, ?_⟩
    · rw [mul_smul, hg₁x, c.smul_x0_of_mem (c.E_le_G1 he₂E)]
    · rw [mul_smul, hg₁b, he₂d']
    · rw [mul_smul, he₂d]

theorem core_gen
    (hJ : HypJ4 G z) (hG2 : Stmt5_Gamma2) (h55 : Stmt5_5)
    (h54 : Stmt5_4) (ρ : ResM24 c) (hK : c.KerFacts) {a b d : G ⧸ c.G1}
    (hab : c.Delta.Adj a b) (hbd : c.Delta.Adj b d) (had : c.Delta.Adj a d) :
    ∃ g : G, g • a = a ∧ g • b = d ∧ g • d = b := by
  obtain ⟨-, m, ham, -⟩ := colGraph_adj.mp hab
  obtain ⟨f, hfa, -⟩ := c.exists_frame ham
  have hfa' : f⁻¹ • a = c.x0 := by rw [← hfa, inv_smul_smul]
  have hb' : c.Delta.Adj c.x0 (f⁻¹ • b) := by
    have h1 := (c.adj_smul_iff f⁻¹).2 hab
    rwa [hfa'] at h1
  have hd' : c.Delta.Adj c.x0 (f⁻¹ • d) := by
    have h1 := (c.adj_smul_iff f⁻¹).2 had
    rwa [hfa'] at h1
  have hbd' : c.Delta.Adj (f⁻¹ • b) (f⁻¹ • d) := (c.adj_smul_iff f⁻¹).2 hbd
  obtain ⟨g₀, hg₀x, hg₀b, hg₀d⟩ := c.core_x0 hJ hG2 h55 h54 ρ hK hb' hd' hbd'
  refine ⟨f * g₀ * f⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hfa', hg₀x, hfa]
  · rw [mul_smul, mul_smul, hg₀b, smul_inv_smul]
  · rw [mul_smul, mul_smul, hg₀d, smul_inv_smul]

end Loc49

theorem stmt5_6_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c))
    (hker : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      c.KerFacts)
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (h55 : Stmt5_5) (h54 : Stmt5_4) : Stmt5_6 := by
  intro G _ _ z hJ c a b d hab hbd had
  obtain ⟨ρ⟩ := hres G z hJ c
  have hK := hker G z hJ c
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m n hAm hBm hAn hDn
    obtain ⟨p, hap, hbp, hdp⟩ := h55 G z hJ c a b d hab hbd had
    have hmp : c.LnP m p := c.lnP_of_adj hG2 hJ hap hbp hab hAm hBm
    have hnp : c.LnP n p := c.lnP_of_adj hG2 hJ hap hdp had hAn hDn
    rcases (ρ.coL_iff_deltaAt hAm hAn).1 ⟨p, hmp, hnp⟩ with h | h | h
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
  · obtain ⟨g, h1, h2, h3⟩ := c.core_gen hJ hG2 h55 h54 ρ hK had.symm hab hbd.symm
    exact ⟨g, h2, h3, h1⟩
  · obtain ⟨g, h1, h2, h3⟩ := c.core_gen hJ hG2 h55 h54 ρ hK hab.symm had hbd
    exact ⟨g, h2, h3, h1⟩
  · obtain ⟨g, h1, h2, h3⟩ := c.core_gen hJ hG2 h55 h54 ρ hK hab hbd had
    exact ⟨g, h2, h3, h1⟩
  · intro m n n' i hAm hBm hAn hDn hBn' hDn' hn
    obtain ⟨g, hgd, hga, hgb⟩ := c.core_gen hJ hG2 h55 h54 ρ hK had.symm hab hbd.symm
    have han : c.OnL a (g • m) := by
      have h1 := (cInc_smul c.G1 c.G2 g b m).2 hBm
      rwa [hgb] at h1
    have hbn : c.OnL b (g • m) := by
      have h1 := (cInc_smul c.G1 c.G2 g a m).2 hAm
      rwa [hga] at h1
    have hgm : m = g • m := c.eq_of_onL hLU hJ hab.ne hAm hBm han hbn
    have hbgn : c.OnL b (g • n) := by
      have h1 := (cInc_smul c.G1 c.G2 g a n).2 hAn
      rwa [hga] at h1
    have hdgn : c.OnL d (g • n) := by
      have h1 := (cInc_smul c.G1 c.G2 g d n).2 hDn
      rwa [hgd] at h1
    have hnn : n' = g • n := c.eq_of_onL hLU hJ hbd.ne hBn' hDn' hbgn hdgn
    have hgn : g • n ∈ c.deltaAt i b m := by
      have h1 := (c.mem_deltaAt_smul_iff g i).2 hn
      rwa [hga, ← hgm] at h1
    rw [hnn]
    exact hgn

end CFSG.Quasithin.H13.AS91
