module

public import CFSG.RankThree.SubgroupLists.MitchellIsoDickson
import CFSG.RankThree.SubgroupLists.MitchellIcosa
import CFSG.RankThree.SubgroupLists.MitchellIcosaSecond
import CFSG.RankThree.SubgroupLists.MitchellNondegenerate
import CFSG.RankThree.SubgroupLists.SymplecticInvolutionPairs
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K : Type} [Field K]

theorem neg_one_mem_isoCent : (-1 : GL V₄ K) ∈ isoCent K :=
  Subgroup.mem_inf.mpr ⟨neg_one_mem_statedSp_two, by rw [mem_matCent]; simp⟩

theorem leviBlock_neg_one : leviBlock ((-1 : GL V₄ K) : Matrix V₄ V₄ K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviBlock]

theorem isoLeviImage_mono {G₁ G₂ : Subgroup (GL V₄ K)} (h : G₁ ≤ G₂) :
    isoLeviImage K G₁ ≤ isoLeviImage K G₂ := by
  unfold isoLeviImage
  exact Subgroup.map_mono (Subgroup.map_mono fun _ hx => h hx)

theorem eq_or_eq_neg_of_isoLeviBar_eq {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) {a b : GL V₄ K}
    (haG : a ∈ G) (haC : a ∈ isoCent K) (hbG : b ∈ G) (hbC : b ∈ isoCent K)
    (h : isoLeviBar haG haC = isoLeviBar hbG hbC) : a = b ∨ a = -b := by
  obtain ⟨ε, hε, hab⟩ := exists_smul_of_isoLeviBar_eq haG haC hbG hbC h
  have hε' : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
  rcases mul_eq_zero.mp hε' with h1 | h1
  · left
    refine eq_of_leviBlock_eq hU0 haG hbG haC hbC ?_
    rw [hab, show ε = 1 by linear_combination h1, one_smul]
  · right
    rw [← neg_one_mul]
    refine eq_of_leviBlock_eq hU0 haG (G.mul_mem hneg hbG) haC
      (mul_mem neg_one_mem_isoCent hbC) ?_
    rw [leviBlock_val_mul _ hbC, leviBlock_neg_one, hab, show ε = -1 by linear_combination h1,
      neg_smul, one_smul, neg_one_mul]

private theorem cliffB_eq_zero_of_commute (h2 : (2 : K) ≠ 0) {d f m : Matrix V₄ V₄ K}
    (hdM : d ∈ (cliffSpace : Submodule K _)) (hfM : f ∈ (cliffSpace : Submodule K _))
    (hm : m ∈ (cliffSpace : Submodule K _)) (hdd : d * d = 1) (hmd : cliffB m d = 0)
    (hcm : d * f * m = m * (d * f)) : cliffB f m = 0 := by
  have hdm : d * m = -(m * d) :=
    (mul_eq_neg_mul_iff h2 hdM hm).mpr (by rw [cliffB_comm]; exact hmd)
  have key : d * (f * m + m * f) = 0 := by
    calc d * (f * m + m * f) = d * f * m + d * m * f := by noncomm_ring
      _ = m * (d * f) + -(m * d) * f := by rw [hcm, hdm]
      _ = 0 := by noncomm_ring
  rw [mul_add_mul_of_mem h2 hfM hm, Matrix.mul_smul, Matrix.mul_one] at key
  have key2 : (2 * cliffB f m) • (1 : Matrix V₄ V₄ K) = 0 := by
    rw [← hdd, ← Matrix.mul_smul, key, Matrix.mul_zero]
  have h00 := congrFun (congrFun key2 (Sum.inl 0)) (Sum.inl 0)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.zero_apply] at h00
  exact (mul_eq_zero.mp h00).resolve_left h2

section Isotropic

variable {p : ℕ} [Fact p.Prime]

private theorem false_of_icosa_core_isotropic (hp7 : 7 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ (ZMod p)) ∈ G)
    {d e f f₂ : GL V₄ (ZMod p)} (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G) (hf₂G : f₂ ∈ G)
    (hd : IsNCInv d) (he : IsNCInv e) (hf : IsNCInv f) (hf₂ : IsNCInv f₂)
    (hθ : 16 * cliffB ⟪d⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪d⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪d⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : ZMod p, ⟪f⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪d⟫ ⟪f⟫ ≠ 0) (hf₂S : ∀ a b c : ZMod p, ⟪f₂⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫ + c • ⟪f⟫)
    {v : Matrix V₄ V₄ (ZMod p)} (hvM : v ∈ (cliffSpace : Submodule (ZMod p) _))
    (hvd : cliffB v ⟪d⟫ = 0) (hve : cliffB v ⟪e⟫ = 0) (hvf : cliffB v ⟪f⟫ = 0)
    (hvf₂ : cliffB v ⟪f₂⟫ = 0) (hvv : cliffB v v = 0) (hv0 : v ≠ 0) : False := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨hx5, hxj, hyj, hxy, hxy'⟩ :=
    icosa_triple_core (p := p) (by omega) hU0 hneg hdG heG hfG hd he hf hθ hβ1 hfP hγ
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hfM := (mem_cliffSpace_of_involution h2 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).1
  have hf₂M := (mem_cliffSpace_of_involution h2 hf₂.1 hf₂.2.1 hf₂.2.2.1 hf₂.2.2.2).1
  have hdd : ⟪d⟫ * ⟪d⟫ = 1 := by rw [← Units.val_mul, hd.2.1, Units.val_one]
  have hee : ⟪e⟫ * ⟪e⟫ = 1 := by rw [← Units.val_mul, he.2.1, Units.val_one]
  have hβ : cliffB ⟪d⟫ ⟪e⟫ * cliffB ⟪d⟫ ⟪e⟫ ≠ 1 := by rwa [← sq]
  obtain ⟨u, w, huM, hwM, hud, hue, huf, hwd, hwe, hwf, huw, hQu, hQw⟩ :=
    exists_orth_pair_of_three hp2 hGS hU0 hneg hdG heG hfG hd he hf hβ hfP
  have hind := lin_indep_of_not_mem_span h2 (cliffB_eq_one_of_mul_self h2 hdd)
    (cliffB_eq_one_of_mul_self h2 hee) hβ hfP
  have hcomm : ∀ m : Matrix V₄ V₄ (ZMod p), m ∈ (cliffSpace : Submodule (ZMod p) _) →
      ∀ a b : GL V₄ (ZMod p), ⟪a⟫ ∈ (cliffSpace : Submodule (ZMod p) _) →
      ⟪b⟫ ∈ (cliffSpace : Submodule (ZMod p) _) → cliffB m ⟪a⟫ = 0 → cliffB m ⟪b⟫ = 0 →
      ⟪a * b⟫ * m = m * ⟪a * b⟫ := by
    intro m hm a b ha hb hma hmb
    rw [Units.val_mul]
    exact (mul_comm_of_anticomm ((mul_eq_neg_mul_iff h2 hm ha).mpr hma)
      ((mul_eq_neg_mul_iff h2 hm hb).mpr hmb)).symm
  obtain ⟨k, -, hk⟩ := exists_isoFrame h2 hvM hvv hv0
  have hZG : G ⊓ matCent u ⊓ matCent w ≤ G := fun _ h => h.1.1
  have hU0' := frameGroup_U0 (RingHom.id _) k hU0
  have hneg' := frameGroup_neg (RingHom.id _) k hneg
  have hZ'G' : frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w) ≤
      frameGroup (RingHom.id _) k G := Subgroup.map_mono hZG
  have hU0Z : ∀ x ∈ frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w), IsSqZero x →
      x = 1 := fun x hx => hU0' x (hZ'G' hx)
  have hnegZ : (-1 : GL V₄ (ZMod p)) ∈ frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w) :=
    frameGroup_neg _ k ⟨⟨hneg, mem_matCent.mpr (by simp)⟩, mem_matCent.mpr (by simp)⟩
  have hxZ := mem_frameGroup (RingHom.id _) k (G := G ⊓ matCent u ⊓ matCent w) (g := d * e)
    ⟨⟨G.mul_mem hdG heG, hcomm u huM d e hdM heM hud hue⟩, hcomm w hwM d e hdM heM hwd hwe⟩
  have hyZ := mem_frameGroup (RingHom.id _) k (G := G ⊓ matCent u ⊓ matCent w) (g := d * f)
    ⟨⟨G.mul_mem hdG hfG, hcomm u huM d f hdM hfM hud huf⟩, hcomm w hwM d f hdM hfM hwd hwf⟩
  have hxC := hk _ (hGS (G.mul_mem hdG heG)) (hcomm v hvM d e hdM heM hvd hve)
  have hyC := hk _ (hGS (G.mul_mem hdG hfG)) (hcomm v hvM d f hdM hfM hvd hvf)
  have hy₂G := mem_frameGroup (RingHom.id _) k (G.mul_mem hdG hf₂G)
  have hy₂C := hk _ (hGS (G.mul_mem hdG hf₂G)) (hcomm v hvM d f₂ hdM hf₂M hvd hvf₂)
  have hx10 : (d * e) ^ 10 = 1 := by
    rw [show (d * e) ^ 10 = ((d * e) ^ 5) ^ 2 by rw [← pow_mul]]
    rcases hx5 with h | h <;> rw [h] <;> simp
  have hp10 : ¬ p ∣ 10 := fun h => by
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp (show p ∣ 2 * 5 from h) with h' | h' <;>
      have := Nat.le_of_dvd (by norm_num) h' <;> omega
  have hD := not_dvd_card_isoLeviImage hp7 hU0' hneg' (hZ'G' hxZ) hxC
    (by rw [← map_pow, hx10, map_one]) hp10
    (frameHom_pow_ne (RingHom.id _) k (hxj 4 (by norm_num) (by norm_num))).1
  have hXY := isoLeviImage_mono (K := ZMod p) hZ'G'
  have hX : ¬ p ∣ Nat.card (isoLeviImage (ZMod p)
      (frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w))) :=
    fun h => hD (h.trans (Subgroup.card_dvd_of_le hXY))
  have hbar1 : ∀ {a : GL V₄ (ZMod p)}
      (haZ : a ∈ frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w))
      (haC : a ∈ isoCent (ZMod p)), isoLeviBar haZ haC = 1 → a = 1 ∨ a = -1 := fun haZ haC h =>
    eq_or_eq_neg_of_isoLeviBar_eq hU0Z hnegZ haZ haC (one_mem _) (one_mem _)
      (h.trans ((isoLeviBar_eq_one_iff _ _).mpr
        (Or.inl (by rw [Units.val_one, leviBlock_one]))).symm)
  have hxbar : orderOf (isoLeviBar hxZ hxC) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [isoLeviBar_pow, isoLeviBar_eq_one_iff, ← map_pow]
      rcases hx5 with h | h
      · exact Or.inl (by rw [h, map_one, Units.val_one, leviBlock_one])
      · exact Or.inr (by rw [h, frameHom_neg_one, leviBlock_neg_one])
    · have h1 := frameHom_pow_ne (RingHom.id _) k (hxj 1 le_rfl (by norm_num))
      rw [pow_one] at h1
      rcases hbar1 hxZ hxC h with h' | h'
      exacts [h1.1 h', h1.2 h']
  have hybar : 2 < orderOf (isoLeviBar hyZ hyC) := by
    have hne : ∀ j, 1 ≤ j → j < 3 → isoLeviBar hyZ hyC ^ j ≠ 1 := fun j hj1 hj3 h => by
      rw [isoLeviBar_pow] at h
      have h1 := frameHom_pow_ne (RingHom.id _) k (hyj j hj1 hj3)
      rcases hbar1 _ _ h with h' | h'
      exacts [h1.1 h', h1.2 h']
    by_contra hle
    exact hne _ (orderOf_pos _) (by omega) (pow_orderOf_eq_one _)
  have hnc : isoLeviBar hxZ hxC * isoLeviBar hyZ hyC ≠
      isoLeviBar hyZ hyC * isoLeviBar hxZ hxC := by
    intro h
    rw [isoLeviBar_mul, isoLeviBar_mul] at h
    rcases eq_or_eq_neg_of_isoLeviBar_eq hU0Z hnegZ (Subgroup.mul_mem _ hxZ hyZ)
        (mul_mem hxC hyC) (Subgroup.mul_mem _ hyZ hxZ) (mul_mem hyC hxC) h with h' | h'
    · refine hxy (frameHom_injective (RingHom.id _) k ?_)
      rw [map_mul (frameHom _ k) (d * e) (d * f), map_mul (frameHom _ k) (d * f) (d * e)]
      exact h'
    · refine hxy' (frameHom_injective (RingHom.id _) k ?_)
      rw [frameHom_neg, map_mul (frameHom _ k) (d * e) (d * f),
        map_mul (frameHom _ k) (d * f) (d * e)]
      exact h'
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨eX⟩ := nonempty_mulEquiv_alternating_five hF _ hX hxbar hybar hnc
  have hXeq := eq_of_le_of_mulEquiv_alternating_five hF hXY hD eX
  have hz : (isoLeviBar hy₂G hy₂C).1 ∈ isoLeviImage (ZMod p)
      (frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w)) := by
    rw [hXeq]
    exact (isoLeviBar hy₂G hy₂C).2
  obtain ⟨c, hcZ, hcC, hc⟩ := exists_isoLeviBar_eq (⟨_, hz⟩ : isoLeviImage (ZMod p)
    (frameGroup (RingHom.id _) k (G ⊓ matCent u ⊓ matCent w)))
  have hc' : isoLeviBar (hZ'G' hcZ) hcC = isoLeviBar hy₂G hy₂C := by
    have hval := congrArg Subtype.val hc
    exact Subtype.ext hval
  obtain ⟨c₀, hc₀Z, hc₀⟩ := Subgroup.mem_map.mp hcZ
  have hy₂uw : ⟪d * f₂⟫ * u = u * ⟪d * f₂⟫ ∧ ⟪d * f₂⟫ * w = w * ⟪d * f₂⟫ := by
    rcases eq_or_eq_neg_of_isoLeviBar_eq hU0' hneg' (hZ'G' hcZ) hcC hy₂G hy₂C hc' with h' | h'
    · rw [← frameHom_injective (RingHom.id _) k (hc₀.trans h')]
      exact ⟨hc₀Z.1.2, hc₀Z.2⟩
    · have e₀ : c₀ = -(d * f₂) :=
        frameHom_injective (RingHom.id _) k (by rw [hc₀, h', frameHom_neg])
      have h1 : c₀ ∈ matCent u := hc₀Z.1.2
      have h1' : c₀ ∈ matCent w := hc₀Z.2
      rw [e₀, mem_matCent, Units.val_neg, neg_mul, mul_neg, neg_inj] at h1 h1'
      exact ⟨h1, h1'⟩
  have hf₂u := cliffB_eq_zero_of_commute h2 hdM hf₂M huM hdd hud
    (by rw [← Units.val_mul]; exact hy₂uw.1)
  have hf₂w := cliffB_eq_zero_of_commute h2 hdM hf₂M hwM hdd hwd
    (by rw [← Units.val_mul]; exact hy₂uw.2)
  obtain ⟨a, b, c', habc⟩ := mem_span_three_of_orth_pair h2 hdM heM hfM huM hwM hf₂M hind
    ⟨hud, hue, huf⟩ ⟨hwd, hwe, hwf⟩ huw hQu hQw ⟨hf₂u, hf₂w⟩
  exact hf₂S a b c' habc

theorem false_of_icosa_pair_isotropic (hp7 : 7 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ (ZMod p)) ∈ G)
    {t e f f₂ : GL V₄ (ZMod p)} (htG : t ∈ G) (heG : e ∈ G) (hfG : f ∈ G) (hf₂G : f₂ ∈ G)
    (ht : IsNCInv t) (he : IsNCInv e) (hf : IsNCInv f) (hf₂ : IsNCInv f₂)
    (hθ : 16 * cliffB ⟪t⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪t⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪t⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : ZMod p, ⟪f⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪t⟫ ⟪f⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪f⟫ ≠ 0)
    (hf₂S : ∀ a b c : ZMod p, ⟪f₂⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫)
    {v : Matrix V₄ V₄ (ZMod p)} (hvM : v ∈ (cliffSpace : Submodule (ZMod p) _))
    (hvt : cliffB v ⟪t⟫ = 0) (hve : cliffB v ⟪e⟫ = 0) (hvf : cliffB v ⟪f⟫ = 0)
    (hvf₂ : cliffB v ⟪f₂⟫ = 0) (hvv : cliffB v v = 0) (hv0 : v ≠ 0) : False := by
  rcases hγ with hγ | hγ
  · exact false_of_icosa_core_isotropic hp7 hGS hU0 hneg htG heG hfG hf₂G ht he hf hf₂ hθ hβ1
      hfP hγ hf₂S hvM hvt hve hvf hvf₂ hvv hv0
  · rw [cliffB_comm] at hθ hβ1
    exact false_of_icosa_core_isotropic hp7 hGS hU0 hneg heG htG hfG hf₂G he ht hf hf₂ hθ hβ1
      (fun a b h => hfP b a (h.trans (add_comm _ _))) hγ
      (fun a b c h => hf₂S b a c (h.trans (congrArg (· + c • ⟪f⟫) (add_comm _ _))))
      hvM hve hvt hvf hvf₂ hvv hv0

end Isotropic

end CFSG.RankThree.SubgroupLists
