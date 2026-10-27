module

public import CFSG.LocalAnalysis.StandardType.GGE6DepSetDict
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelChart
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem exists_actsAs_evalWord_gensAll {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    {t w : ZMod 3} (hgen : ∀ i : Fin 7, ∃ φ ∈ ggAutomizer ⊤ Bs, ActsAs ι φ (gensAll 0 t 0 w i))
    (word : List (Fin 7)) :
    ∃ φ ∈ ggAutomizer ⊤ Bs, ActsAs ι φ (evalWord (gensAll 0 t 0 w) word) := by
  induction word with
  | nil => exact ⟨1, (ggAutomizer ⊤ Bs).one_mem, ActsAs.one ι⟩
  | cons i l ih =>
      obtain ⟨φ, hφ, hφa⟩ := hgen i
      obtain ⟨ψ, hψ, hψa⟩ := ih
      exact ⟨φ * ψ, (ggAutomizer ⊤ Bs).mul_mem hφ hψ, hφa.mul hψa⟩

private noncomputable def pt {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ Vec6) (v : Vec6) : ↥Bs :=
  Additive.toMul (ι.symm v)

private theorem iota_pt {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} (v : Vec6) :
    ι (Additive.ofMul (pt ι v)) = v := by
  simp [pt]

private theorem xx_eq_single : xx = Pi.single 5 (1 : ZMod 3) := by
  funext i
  fin_cases i <;> simp [xx]

private theorem automizer_top_conj {Bs : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer ⊤ Bs) :
    ∃ g : G, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφ
  exact ⟨g, hgN, hg⟩

private theorem actsAs_apply_pt {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs}
    {gm : Mat6} (h : ActsAs ι φ gm) {a a' : Vec6} (haa : gm.mulVec a = a') :
    φ (pt ι a) = pt ι a' := by
  apply Additive.ofMul.injective
  apply ι.injective
  rw [h (pt ι a), iota_pt a, haa, iota_pt a']

private theorem pt_eq_of {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {b : ↥Bs} {v : Vec6}
    (h : ι (Additive.ofMul b) = v) : pt ι v = b := by
  apply Additive.ofMul.injective
  apply ι.injective
  rw [iota_pt v, h]

private theorem pt_mem_L {Bs L : Subgroup G} {x : G} {hxBs : x ∈ Bs}
    {ι : Additive ↥Bs ≃+ Vec6} (hι : GGE6DepCoord Bs L x hxBs ι) {v : Vec6} (hv : v 5 = 0) :
    ((pt ι v : ↥Bs) : G) ∈ L := by
  refine (hι.2.1 (pt ι v)).mpr ?_
  rwa [iota_pt v]

private theorem setU_bil6_add (u v w : Vec6) : bil6 (u + v) w = bil6 u w + bil6 v w := by
  simp only [bil6, add_dotProduct]

private theorem setU_bil6_neg (u w : Vec6) : bil6 (-u) w = -bil6 u w := by
  simp only [bil6, neg_dotProduct]

private def setU {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ Vec6) (wv : Vec6) : Subgroup ↥Bs where
  carrier := {u | bil6 (ι (Additive.ofMul u)) xx = 0 ∧ bil6 (ι (Additive.ofMul u)) xs = 0 ∧
    bil6 (ι (Additive.ofMul u)) wv = 0}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [bil6, ofMul_one, zero_dotProduct]
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · rw [ofMul_mul, map_add, setU_bil6_add, ha1, hb1, add_zero]
    · rw [ofMul_mul, map_add, setU_bil6_add, ha2, hb2, add_zero]
    · rw [ofMul_mul, map_add, setU_bil6_add, ha3, hb3, add_zero]
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · rw [ofMul_inv, map_neg, setU_bil6_neg, ha1, neg_zero]
    · rw [ofMul_inv, map_neg, setU_bil6_neg, ha2, neg_zero]
    · rw [ofMul_inv, map_neg, setU_bil6_neg, ha3, neg_zero]

private theorem mem_setU {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ Vec6) (wv : Vec6) (u : ↥Bs) :
    u ∈ setU ι wv ↔ bil6 (ι (Additive.ofMul u)) xx = 0 ∧ bil6 (ι (Additive.ofMul u)) xs = 0 ∧
      bil6 (ι (Additive.ofMul u)) wv = 0 :=
  Iff.rfl

private theorem card_setU {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ Vec6) (wv : Vec6)
    (hcard : (Finset.univ.filter fun v : Vec6 =>
      bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0).card = 27) :
    3 ^ 3 ≤ Nat.card (setU ι wv) := by
  classical
  let e : ↥(setU ι wv) ≃ {v : Vec6 // bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0} :=
    Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) (fun u => mem_setU ι wv u)
  have h1 : Nat.card (setU ι wv)
      = Nat.card {v : Vec6 // bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0} :=
    Nat.card_congr e
  have h2 : Nat.card {v : Vec6 // bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0}
      = (Finset.univ.filter fun v : Vec6 =>
          bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0).card :=
    Nat.subtype_card _ (by intro v; simp)
  rw [h1, h2, hcard]
  norm_num

private theorem u1_exists {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs}
    {gm : Mat6} (h : ActsAs ι φ gm) (hiso : gm.transpose * gram6 * gm = gram6) (u : ↥Bs) :
    ∃ u₁ : ↥Bs, φ u₁ = u ∧ ∀ z : Vec6,
      bil6 (ι (Additive.ofMul u₁)) z = bil6 (ι (Additive.ofMul u)) (gm.mulVec z) := by
  refine ⟨φ⁻¹ u, MulAut.apply_inv_self ↥Bs φ u, ?_⟩
  intro z
  have hu : ι (Additive.ofMul u) = gm.mulVec (ι (Additive.ofMul (φ⁻¹ u))) := by
    have h' := h (φ⁻¹ u)
    rwa [MulAut.apply_inv_self] at h'
  rw [hu]
  exact (bil6_isometry hiso _ _).symm

theorem ggE6Dep_setting_of_frame {Bs L : Subgroup G} {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    {ι : Additive ↥Bs ≃+ Vec6} (hι : GGE6DepCoord Bs L x hxBs ι)
    (hy : ι (Additive.ofMul ⟨y, hyBs⟩) = xs) {t w : ZMod 3} (htw : t * w = 2)
    (hgen : ∀ i : Fin 7, ∃ φ ∈ ggAutomizer ⊤ Bs, ActsAs ι φ (gensAll 0 t 0 w i)) :
    GGE6DepConjSetting 3 Bs x y L := by
  classical
  obtain ⟨gm, wv, x1, y1, ⟨word, hword⟩, hgx1, hgy1, hgxx, hwv5, hx15, hy15, hnwv, hnx1, hny1,
    hbx1y1, hbxswv, hne1, hne2, hne3, hne4, ⟨wx1, hwx1⟩, ⟨wy1, hwy1⟩, ⟨wxs, hwxs⟩, ⟨wwv, hwwv⟩,
    hcomm1, hcomm2, hcard⟩ := chart t w 1 htw one_ne_zero
  rw [one_smul] at hgy1
  obtain ⟨φg, hφgA, hφg⟩ := exists_actsAs_evalWord_gensAll hgen word
  rw [hword] at hφg
  obtain ⟨gG, hgGN, hgG⟩ := automizer_top_conj hφgA
  have hiso : gm.transpose * gram6 * gm = gram6 := by
    rw [← hword]
    exact evalWord_gensAll_isometry htw word
  have hnxs : norm6 xs = 1 := by decide +kernel
  have hxpt : pt ι xx = ⟨x, hxBs⟩ := pt_eq_of (hι.1.trans xx_eq_single.symm)
  have hypt : pt ι xs = ⟨y, hyBs⟩ := pt_eq_of hy
  have hφx1 : φg (pt ι x1) = ⟨x, hxBs⟩ := by
    rw [actsAs_apply_pt hφg hgx1, hxpt]
  have hφy1 : φg (pt ι y1) = ⟨y, hyBs⟩ := by
    rw [actsAs_apply_pt hφg hgy1, hypt]
  have hφx : φg ⟨x, hxBs⟩ = pt ι wv := by
    rw [← hxpt]
    exact actsAs_apply_pt hφg hgxx
  have hxeq : x = gG * ((pt ι x1 : ↥Bs) : G) * gG⁻¹ := by
    have h := hgG (pt ι x1)
    rw [hφx1] at h
    exact h
  have hyeq : y = gG * ((pt ι y1 : ↥Bs) : G) * gG⁻¹ := by
    have h := hgG (pt ι y1)
    rw [hφy1] at h
    exact h
  have hweq : ((pt ι wv : ↥Bs) : G) = gG * x * gG⁻¹ := by
    have h := hgG ⟨x, hxBs⟩
    rw [hφx] at h
    exact h
  have hyL : y ∈ L := by
    have h := pt_mem_L hι (v := xs) (by decide +kernel)
    rw [hypt] at h
    exact h
  have horth1 : GGCorootOrth 3 (ggAutomizer L Bs) (pt ι x1) (pt ι y1) :=
    corootOrth_of_words hι hnx1 hny1 hne1 hne2 ⟨wx1, hwx1⟩ ⟨wy1, hwy1⟩ hcomm1
  have horth2 : GGCorootOrth 3 (ggAutomizer L Bs) (⟨y, hyBs⟩ : ↥Bs) (pt ι wv) := by
    have h := corootOrth_of_words hι hnxs hnwv hne3 hne4 ⟨wxs, hwxs⟩ ⟨wwv, hwwv⟩ hcomm2
    rw [← hypt]
    exact h
  refine ⟨hZ, hBsL, gG, ((pt ι x1 : ↥Bs) : G), ((pt ι y1 : ↥Bs) : G), ((pt ι wv : ↥Bs) : G),
    (pt ι x1).2, (pt ι y1).2, hyBs, (pt ι wv).2, hgGN, hxeq, hyeq, hweq,
    pt_mem_L hι hx15, pt_mem_L hι hy15, hyL, pt_mem_L hι hwv5, horth1, horth2,
    setU ι wv, card_setU ι wv hcard, ?_, ?_⟩
  ·
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := (mem_setU ι wv u).mp hu
    apply mem_fixedByCentres_of_perp hι
    intro c hc
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨by rw [hy]; exact hnxs, by rw [hy]; exact hu2⟩
    · have h := iota_pt (ι := ι) wv
      exact ⟨by rw [h]; exact hnwv, by rw [h]; exact hu3⟩
  ·
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := (mem_setU ι wv u).mp hu
    refine ⟨?_, ?_⟩
    · refine (hι.2.1 u).mpr ?_
      rw [← bil6_xx (ι (Additive.ofMul u))]
      exact hu1
    · obtain ⟨u₁, hu₁, hbil⟩ := u1_exists hφg hiso u
      refine ⟨u₁, ?_, ?_, ?_⟩
      · apply mem_fixedByCentres_of_perp hι
        intro c hc
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        · have h := iota_pt (ι := ι) x1
          exact ⟨by rw [h]; exact hnx1, by rw [h, hbil x1, hgx1]; exact hu1⟩
        · have h := iota_pt (ι := ι) y1
          exact ⟨by rw [h]; exact hny1, by rw [h, hbil y1, hgy1]; exact hu2⟩
      · refine (hι.2.1 u₁).mpr ?_
        rw [← bil6_xx (ι (Additive.ofMul u₁)), hbil xx, hgxx]
        exact hu3
      · have h := hgG u₁
        rw [hu₁] at h
        rw [h]
        group

end E6Dep

end CFSG.StandardType

end
