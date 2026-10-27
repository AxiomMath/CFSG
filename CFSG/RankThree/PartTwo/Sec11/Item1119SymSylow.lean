module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymNoWreath
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolSylowAux
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolSylowGlobal
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolFalseSylow
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymTypes

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_zpowers_conj (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {n : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.zpowers (n * d * n⁻¹) = Subgroup.zpowers d := by
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [MonoidHom.map_zpowers] at h1
  exact h1

theorem sym1119_conj_not_mem_zpowers_d
    (h : Sec11Data G A c L a R Y d x s r g) {n : G}
    (hn : n⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hcd' : c ∉ Subgroup.zpowers d) : n * c * n⁻¹ ∉ Subgroup.zpowers d := by
  intro hmem
  apply hcd'
  have := (Subgroup.mem_normalizer_iff.mp hn (n * c * n⁻¹)).mp hmem
  simpa [mul_assoc] using this

theorem sym1119_map_conj_line (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {n z : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    (Subgroup.closure ({z, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({n * z * n⁻¹, d} : Set G) :=
  Item1119Sym.map_conj_closure_pair n z d (sym1119_zpowers_conj h113 h117 h hn)
theorem sym1119_not_dvd_index (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hg3 : g ^ 3 = 1)
    {h₀ : G} (hh₀ : h₀ ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (hNA : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (he₀c : h₀ * c * h₀⁻¹ ∉ Subgroup.closure ({c, d} : Set G))
    (hB : ∀ n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * c * n⁻¹ ∈ Subgroup.closure ({c, d} : Set G) ∨
        n * c * n⁻¹ ∈ Subgroup.closure ({h₀ * c * h₀⁻¹, d} : Set G)) :
    ¬ 3 ∣ (sec11P R g).index := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) with hNdef
  set e₀ : G := h₀ * c * h₀⁻¹ with he₀def
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hc3 : c ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.mem_A
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have hcd' : c ∉ Subgroup.zpowers d := (sym1119_indep h).2.1
  have hmemA : ∀ n ∈ N, n * c * n⁻¹ ∈ A := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (hNA hn) c).mp h.mem_A
  have hnotd : ∀ n ∈ N, n * c * n⁻¹ ∉ Subgroup.zpowers d := fun n hn =>
    sym1119_conj_not_mem_zpowers_d h (hNd (N.inv_mem hn)) hcd'
  have he₀A : e₀ ∈ A := hmemA h₀ hh₀
  have he₀d : e₀ ∉ Subgroup.zpowers d := hnotd h₀ hh₀
  have he₀3 : e₀ ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h he₀A
  have he₀dc : e₀ * d = d * e₀ := Item1117Proof.commute_of_mem_A h he₀A hdA
  have hl₁l₂ : Subgroup.closure ({c, d} : Set G) ≠ Subgroup.closure ({e₀, d} : Set G) := by
    intro heq
    apply he₀c
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  have hline : ∀ n ∈ N, ∀ u : G, u * d = d * u → u ^ 3 = 1 → u ∉ Subgroup.zpowers d →
      ∀ w : G, w ∈ Subgroup.closure ({u, d} : Set G) → w ∉ Subgroup.zpowers d →
      Subgroup.closure ({w, d} : Set G) = Subgroup.closure ({u, d} : Set G) := fun n hn u hud hu3 hu w hw hwd =>
    Item1119Sym.closure_pair_eq_of_mem u w d hud hu3 hd3 hd1 hu hw hwd
  have hmap_c : ∀ n ∈ N, (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({c, d} : Set G) ∨
      (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({e₀, d} : Set G) := by
    intro n hn
    rw [sym1119_map_conj_line h113 h117 h (hNd hn)]
    rcases hB n hn with h1 | h1
    · left
      exact hline n hn c hcd hc3 hcd' _ h1 (hnotd n hn)
    · right
      exact hline n hn e₀ he₀dc he₀3 he₀d _ h1 (hnotd n hn)
  have hmap_e : ∀ n ∈ N, (Subgroup.closure ({e₀, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({c, d} : Set G) ∨
      (Subgroup.closure ({e₀, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({e₀, d} : Set G) := by
    intro n hn
    rw [sym1119_map_conj_line h113 h117 h (hNd hn)]
    have hnh : n * h₀ ∈ N := N.mul_mem hn hh₀
    have e1 : n * e₀ * n⁻¹ = (n * h₀) * c * (n * h₀)⁻¹ := by rw [he₀def]; group
    rw [e1]
    rcases hB (n * h₀) hnh with h1 | h1
    · left
      exact hline _ hnh c hcd hc3 hcd' _ h1 (hnotd _ hnh)
    · right
      exact hline _ hnh e₀ he₀dc he₀3 he₀d _ h1 (hnotd _ hnh)
  apply Item1119Sym.not_dvd_index_of_normalizer_maximal (sec11P R g) (sym1119_isPGroup_P h)
  intro S hS3 hPS hSN
  have hgR : g ∉ R := fun hgR => h.g_not_mem (h.isSylowOf.le hgR)
  have hRlt : R < sec11P R g :=
    lt_of_le_of_ne (Item1119Proof.R_le_P R g) fun heq => hgR (heq ▸ Item1119Proof.g_mem_P R g)
  have hPR : Nat.card (sec11P R g) = 3 * Nat.card R := by
    have h1 := Item1119Sym.three_mul_card_le_of_lt R (sec11P R g) (sym1119_isPGroup_P h) hRlt
    have h2 := Item1119Sym.relindex_le_three R g h.g_mem_normalizer hg3
    have h3 := Subgroup.relIndex_mul_card (H := R) (K := sec11P R g)
    rw [inf_eq_left.mpr (Item1119Proof.R_le_P R g)] at h3
    change R.relIndex (R ⊔ Subgroup.zpowers g) * Nat.card R = Nat.card (sec11P R g) at h3
    have h4 : R.relIndex (R ⊔ Subgroup.zpowers g) * Nat.card R ≤ 3 * Nat.card R :=
      Nat.mul_le_mul_right _ h2
    omega
  refine Item1119Sym.eq_of_le_isPGroup (sec11P R g) S R
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)) c ({c, c * d, c * d ^ 2} : Finset G) hPS hS3
    (fun K' hK'H hK'3 hRK' => h.isSylowOf.eq_of_le hRK' hK'H hK'3)
    (Item1119Proof.R_le_P R g) hPR (Item1119Proof.R_le_centralizer_c h) ?_ ?_ ?_
  · intro z hz
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← conj_zpow]
    have : z * c * z⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]; exact Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [this]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  · exact Finset.card_le_three
  · intro s hs
    have hsN : s ∈ N := hSN hs
    have hs3 : ∃ k : ℕ, s ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hS3 ⟨s, hs⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hfix := Item1119Sym.three_group_fixes_line _ _ hl₁l₂ s hs3 (hmap_c s hsN) (hmap_e s hsN)
    have hsc : s * c * s⁻¹ ∈ Subgroup.closure ({c, d} : Set G) := by
      have : s * c * s⁻¹ ∈ (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj s).toMonoidHom :=
        ⟨c, Subgroup.subset_closure (by simp), rfl⟩
      rwa [hfix] at this
    have hsd : s * d * s⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp (hNd hsN) d).mp (Subgroup.mem_zpowers d)
    obtain ⟨j, hj⟩ := Item1119Sym.conj_eq_of_three_power_order s c d hs3 hc3 hcd hcd' hsd hsc
    rw [hj]
    have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
    have hjm : d ^ j = d ^ (j % 3) := zpow_eq_zpow_emod j hd3'
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
    · rw [hjm, h0]; simp
    · rw [hjm, h1]; simp
    · rw [hjm, h2]; simp
theorem sym1119_false_of_sylow_fixed' (P W₀ : Subgroup G) (r : G) (hP3 : IsPGroup 3 P)
    (hidx : ¬ 3 ∣ P.index) (hG : oResidual 3 G = ⊤)
    (hW : ∀ (K : Subgroup P) [K.Normal], IsEmpty (P ⧸ K ≃* W33)) (hW0P : W₀ ≤ P)
    (hPP : ⁅P, P⁆ ≤ W₀)
    (hNW : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (W₀ : Set G))
    (hr : r ∈ P) (hrW : r ∉ W₀)
    (hfix : ∀ n ∈ Subgroup.normalizer (P : Set G), n * r * n⁻¹ * r⁻¹ ∈ W₀) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Item1119Sym.false_of_sylow_fixed (hP3.toSylow hidx) W₀ r hG hW hW0P hPP hNW hr hrW hfix

theorem sym1119_false_of_B (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1120 : Item1120) (hctx : Sym1119Ctx G A c L a R Y d x s r g)
    (hord : orderOf x = 27) {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G))
    (hfc : f ∉ Subgroup.zpowers c) (hr3 : r ^ 3 = f)
    {h₀ : G} (hh₀ : h₀ ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (he₀c : h₀ * c * h₀⁻¹ ∉ Subgroup.closure ({c, d} : Set G))
    (hB : ∀ n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * c * n⁻¹ ∈ Subgroup.closure ({c, d} : Set G) ∨
        n * c * n⁻¹ ∈ Subgroup.closure ({h₀ * c * h₀⁻¹, d} : Set G)) : False := by
  have h := hctx.big.toSec11Data
  have hra : r * a = a * r := hctx.r_comm
  have hg3 : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hctx.big.orderOf_g] at this
  have hs : Subgroup.zpowers s = Subgroup.zpowers c := hctx.s_eq_c
  have hNA := hctx.N_le_A
  have hNd := hctx.N_le_d
  have hPA : sec11P R g ≤ Subgroup.normalizer (A : Set G) := fun p hp =>
    hNA (Subgroup.le_normalizer hp)
  have hV : sec11P R g ≤
      Subgroup.normalizer ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G) :=
    h1120 G A c L a R Y d x s r g hctx.big
  have hPP := sym1119_PP_le_W0 h45 h113 h117 h hra hg3 hs hord hf hfc hr3 hPA hV
  obtain ⟨-, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  have hnoW := fun (K : Subgroup (sec11P R g)) [K.Normal] =>
    sym1119_noWreath h45 h113 h117 h hra hg3 hs hord hf hfc hr3 hctx.A_le_Z2 hPA hV hPP K
  have hidx := sym1119_not_dvd_index h113 h117 h hg3 hh₀ hNA hNd he₀c hB
  have hNfix : ∀ n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * x ^ 3 * n⁻¹ ∈ sym1119W0 A x ∧ n * r * n⁻¹ * r⁻¹ ∈ sym1119W0 A x := fun n hn =>
    sym1119_N_fix h45 h113 h117 h hra hg3 hs hord hf hfc hr3 hn (hNA hn) (hNd hn)
  have hNW : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((sym1119W0 A x : Subgroup G) : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    refine Item1119Sym.conj_mem_closure_of_gens ((A : Set G) ∪ {x ^ 3}) (sym1119W0 A x) n ?_ hw
    rintro u (hu | hu)
    · exact sym1119_A_le_W0 A x ((Subgroup.mem_normalizer_iff.mp (hNA hn) u).mp hu)
    · rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact (hNfix n hn).1
  exact sym1119_false_of_sylow_fixed' (sec11P R g) (sym1119W0 A x) r (sym1119_isPGroup_P h) hidx
    (by haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact hctx.big.toTheoremFourHyp.oResidual_eq_top 3) hnoW (sym1119_W0_le_P h45 h) hPP hNW
    (Item1119Proof.R_le_P R g (sym1119_r_mem_R h)) (sym1119_r_not_mem_W0 h45 h hyr1)
    (fun n hn => (hNfix n hn).2)


end Facts

end CFSG.RankThree.PartTwo.Sec11

end
