module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3R2
public import CFSG.RankThree.PartTwo.Sec11.DataExistsR
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoGroup
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoSylow

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11.R2No

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem false_of_R2 (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : ResidueConfig G A c L a R Y d) (hctx : A ∉ partTwoT G ∨ A ∈ partTwoS G)
    (hR2 : ResidueR2 G A c d) : False := by
  have hs := h.toSec11StdOfCtx hctx
  obtain ⟨hΩ, hcyc⟩ := h113 G A c L a R Y hs
  obtain ⟨ζ, hζ⟩ := exists_rotation_R2 h45 h hctx hΩ hR2
  obtain ⟨x, hx⟩ := hs.exists_zpowers_eq_inf_L
  obtain ⟨s, hs'⟩ := RChoice.exists_zpowers_eq_of_isCyclic hcyc
  have hA : A = Subgroup.closure ({c, a, d} : Set G) := by
    rw [← h.closure_eq]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨r, hRgen, -⟩ := hs.exists_eq_closure h45 h.inf_eq_zpowers hA hx hs'
  have hsx : x * s = s * x := (hs.commute_s_x hx hs').symm
  have hRN : R ≤ Subgroup.normalizer (L : Set G) :=
    h.isSylowOf.le.trans (hs.normalizer_le_normalizer_L h45)
  have hxR : x ∈ R ⊓ L := hx ▸ Subgroup.mem_zpowers x
  have hsR : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := hs' ▸ Subgroup.mem_zpowers s
  have hrR : r ∈ R := hRgen ▸ Subgroup.subset_closure (by simp)
  have hrx : ∃ e : ℤ, r * x * r⁻¹ = x ^ e := by
    have hm : r * x * r⁻¹ ∈ R ⊓ L :=
      ⟨R.mul_mem (R.mul_mem hrR hxR.1) (R.inv_mem hrR),
        (Subgroup.mem_normalizer_iff.mp (hRN hrR) x).mp hxR.2⟩
    rw [hx] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hrs : ∃ e : ℤ, r * s * r⁻¹ = s ^ e := by
    have hm : r * s * r⁻¹ ∈ R ⊓ Sec4.thetaQuotCentralizer L :=
      ⟨R.mul_mem (R.mul_mem hrR hsR.1) (R.inv_mem hrR),
        Sec6.conj_mem_thetaQuotCentralizer hsR.2 (hRN hrR)⟩
    rw [hs'] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [h.inf_eq_zpowers]; exact Subgroup.mem_zpowers d).1
  obtain ⟨f, -, -, -, hv⟩ :=
    Item116Fusion.exists_coords_cda hs h.inf_eq_zpowers h.not_mem_zpowers
  have hAgen : ∀ t ∈ A, ∃ i j k : ℕ, t = c ^ i * d ^ j * a ^ k := by
    intro t ht
    obtain ⟨v, hvt⟩ : ∃ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) = t :=
      ⟨Multiplicative.toAdd (f.symm ⟨t, ht⟩), by simp⟩
    exact ⟨(v 0).val, (v 1).val, (v 2).val, by rw [← hvt, hv v]⟩
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hR3 : IsPGroup 3 R := h.isSylowOf_top.isPGroup
  have hRW : R ≤ Subgroup.normalizer (A : Set G) := by
    rw [hΩ]
    exact le_normalizer_closure_pow_three
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hRcB : ∀ y ∈ R, ∀ b ∈ Subgroup.closure ({c, d} : Set G), y * b * y⁻¹ = b := by
    intro y hy b hb
    obtain ⟨k, hk⟩ := hR3 ⟨y, hy⟩
    exact h.threeElement_centralizes y (hRW hy) ⟨k, by simpa using congrArg Subtype.val hk⟩ b hb
  have hRAB : ∀ y ∈ R, a⁻¹ * (y * a * y⁻¹) ∈ Subgroup.closure ({c, d} : Set G) := by
    intro y hy
    have := h.conj_mem_of_mem_normalizer y⁻¹ (Subgroup.inv_mem _ (hRW hy))
      (Subgroup.inv_mem _ (hRH hy)) a h.a_mem
    simpa using this
  have hact : ∃ y ∈ R, y * a * y⁻¹ ≠ a := by
    obtain ⟨w, hwW, hwB, hwa⟩ := h.exists_transvection c hcB
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hA3 c h.mem_A) h.ne_one
    obtain ⟨j, ⟨k, hk⟩, hmove⟩ := exists_three_element_moving hc3 (hwB c hcB) hwa
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (A : Set G)) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact h.isSylowOf_top.of_le hRW le_top
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hgW, hgR⟩ := exists_conj_mem_of_isSylowOf hSyl
      (Subgroup.pow_mem _ hwW j) ⟨k, hk⟩
    by_contra hcon
    push Not at hcon
    have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    have hfixA : ∀ t ∈ A, (g * w ^ j * g⁻¹) * t * (g * w ^ j * g⁻¹)⁻¹ = t := by
      intro t ht
      have hc' : (g * w ^ j * g⁻¹) * c = c * (g * w ^ j * g⁻¹) :=
        mul_inv_eq_iff_eq_mul.mp (hRcB _ hgR c hcB)
      have hd' : (g * w ^ j * g⁻¹) * d = d * (g * w ^ j * g⁻¹) :=
        mul_inv_eq_iff_eq_mul.mp (hRcB _ hgR d hdB)
      have ha' : (g * w ^ j * g⁻¹) * a = a * (g * w ^ j * g⁻¹) :=
        mul_inv_eq_iff_eq_mul.mp (hcon _ hgR)
      have hA' : A ≤ Subgroup.centralizer ({g * w ^ j * g⁻¹} : Set G) := by
        rw [← h.closure_eq, Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases hz with hz | hz | hz
        · rw [hz]; exact hc'.symm
        · rw [hz]; exact hd'.symm
        · rw [hz]; exact ha'.symm
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hA' ht)).symm
    have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgW a).mp h.a_mem
    have h1 := hfixA _ hga
    apply hmove
    have h2 : g * (w ^ j * a * (w ^ j)⁻¹) * g⁻¹ = g * a * g⁻¹ := by
      rw [← h1]
      group
    exact mul_left_cancel (mul_right_cancel h2)
  have hBA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact h.mem_A
    · rw [hz]; exact hdA
  have hWB : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ b ∈ Subgroup.closure ({c, d} : Set G),
      w * b * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) := fun w hw b hb =>
    (Subgroup.mem_normalizer_iff.mp (h.normalizer_le hw) b).mp hb
  have hRK0 : R ≤ K0 A (Subgroup.closure ({c, d} : Set G)) := fun y hy =>
    ⟨hRW hy, hRcB y hy, fun t ht => h.conj_mem_of_mem_normalizer y (hRW hy) (hRH hy) t ht⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 3 R (K0 A (Subgroup.closure ({c, d} : Set G))) :=
    h.isSylowOf_top.of_le hRK0 le_top
  obtain ⟨k, hkK, hkn⟩ := exists_mem_normalizer_of_isSylowOf hSylK
    (normalizer_le_normalizer_K0 hWB hζ.mem)
  have hkB : ∀ b ∈ Subgroup.closure ({c, d} : Set G), k⁻¹ * b * k = b := fun b hb =>
    conj_inv_eq_of_conj_eq (hkK.2.1 b hb)
  have hnb : ∀ b ∈ Subgroup.closure ({c, d} : Set G),
      (k⁻¹ * ζ) * b * (k⁻¹ * ζ)⁻¹ = ζ * b * ζ⁻¹ := by
    intro b hb
    have hb' := hWB ζ hζ.mem b hb
    calc (k⁻¹ * ζ) * b * (k⁻¹ * ζ)⁻¹ = k⁻¹ * (ζ * b * ζ⁻¹) * k := by group
      _ = ζ * b * ζ⁻¹ := hkB _ hb'
  have hna : ∃ b0 ∈ Subgroup.closure ({c, d} : Set G),
      (k⁻¹ * ζ) * a * (k⁻¹ * ζ)⁻¹ = a⁻¹ * b0 := by
    have hb1 : a⁻¹ * (k⁻¹ * a * k) ∈ Subgroup.closure ({c, d} : Set G) := hkK.2.2 a h.a_mem
    refine ⟨(a⁻¹ * (k⁻¹ * a * k))⁻¹, Subgroup.inv_mem _ hb1, ?_⟩
    have hcomm : a⁻¹ * (a⁻¹ * (k⁻¹ * a * k))⁻¹ = (a⁻¹ * (k⁻¹ * a * k))⁻¹ * a⁻¹ :=
      hAc _ (A.inv_mem h.a_mem) _ (A.inv_mem (hBA hb1))
    have e : (k⁻¹ * ζ) * a * (k⁻¹ * ζ)⁻¹ = k⁻¹ * (ζ * a * ζ⁻¹) * k := by group
    rw [e, hζ.inv_a, hcomm]
    group
  have hnR : ∀ y ∈ R, (k⁻¹ * ζ) * y * (k⁻¹ * ζ)⁻¹ ∈ R := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hkn y).mp hy
  have hnB : ∀ b ∈ Subgroup.closure ({c, d} : Set G),
      (k⁻¹ * ζ) * b * (k⁻¹ * ζ)⁻¹ ∈ Subgroup.closure ({c, d} : Set G) := by
    intro b hb
    rw [hnb b hb]
    exact hWB ζ hζ.mem b hb
  have hn2c : (k⁻¹ * ζ) ^ 2 * c * ((k⁻¹ * ζ) ^ 2)⁻¹ ∈ Subgroup.zpowers d := by
    have e1 : (k⁻¹ * ζ) ^ 2 * c * ((k⁻¹ * ζ) ^ 2)⁻¹ =
        (k⁻¹ * ζ) * ((k⁻¹ * ζ) * c * (k⁻¹ * ζ)⁻¹) * (k⁻¹ * ζ)⁻¹ := by
      rw [pow_two]
      group
    rw [e1, hnb c hcB, hnb _ (hWB ζ hζ.mem c hcB)]
    have e2 : ζ * (ζ * c * ζ⁻¹) * ζ⁻¹ = ζ ^ 2 * c * (ζ ^ 2)⁻¹ := by
      rw [pow_two]
      group
    rw [e2]
    exact hζ.sq_c
  have hn2d : (k⁻¹ * ζ) ^ 2 * d * ((k⁻¹ * ζ) ^ 2)⁻¹ ∈ Subgroup.zpowers c := by
    have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    have e1 : (k⁻¹ * ζ) ^ 2 * d * ((k⁻¹ * ζ) ^ 2)⁻¹ =
        (k⁻¹ * ζ) * ((k⁻¹ * ζ) * d * (k⁻¹ * ζ)⁻¹) * (k⁻¹ * ζ)⁻¹ := by
      rw [pow_two]
      group
    rw [e1, hnb d hdB, hnb _ (hWB ζ hζ.mem d hdB)]
    have e2 : ζ * (ζ * d * ζ⁻¹) * ζ⁻¹ = ζ ^ 2 * d * (ζ ^ 2)⁻¹ := by
      rw [pow_two]
      group
    rw [e2]
    exact hζ.sq_d
  exact core_group (A := A) (B := Subgroup.closure ({c, d} : Set G)) (R := R) (a := a) (c := c)
    (d := d) (x := x) (s := s) (r := r) (n := k⁻¹ * ζ) hAc hA3 rfl h.a_mem h.mem_A hdA h.ne_one
    h.not_mem_zpowers hAgen
    (fun z hz hz3 => by rw [hΩ]; exact Subgroup.subset_closure ⟨hz, hz3⟩) hR3 hRcB hRAB hRgen
    hsx hrx hrs hact hnR hnB hna hn2c hn2d

end Certified

end CFSG.RankThree.PartTwo.Sec11
