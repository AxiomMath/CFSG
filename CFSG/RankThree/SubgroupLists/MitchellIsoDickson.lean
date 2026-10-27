module

public import CFSG.RankThree.SubgroupLists.MitchellIsoTorus
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.Dihedral.GorensteinWalter.FieldTransport

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem exists_smul_of_isoLeviBar_eq {K : Type} [Field K] {G : Subgroup (GL V₄ K)}
    {a b : GL V₄ K} (haG : a ∈ G) (haC : a ∈ isoCent K) (hbG : b ∈ G) (hbC : b ∈ isoCent K)
    (h : isoLeviBar haG haC = isoLeviBar hbG hbC) :
    ∃ ε : K, ε * ε = 1 ∧ leviBlock (a : Matrix V₄ V₄ K) = ε • leviBlock (b : Matrix V₄ V₄ K) := by
  have h1 : isoLeviBar (G.mul_mem haG (G.inv_mem hbG)) (mul_mem haC (inv_mem hbC)) = 1 := by
    rw [← isoLeviBar_mul haG haC (G.inv_mem hbG) (inv_mem hbC), ← isoLeviBar_inv hbG hbC, h,
      mul_inv_cancel]
  have hab : leviBlock (a : Matrix V₄ V₄ K) =
      leviBlock ((a * b⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * leviBlock (b : Matrix V₄ V₄ K) := by
    rw [← leviBlock_val_mul _ hbC, inv_mul_cancel_right]
  rcases (isoLeviBar_eq_one_iff _ _).mp h1 with h' | h'
  · exact ⟨1, one_mul 1, by rw [hab, h', one_mul, one_smul]⟩
  · exact ⟨-1, by norm_num, by rw [hab, h', neg_mul, one_mul, neg_smul, one_smul]⟩

private theorem false_of_commute_isoLeviBar_conj {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {x : GL V₄ (ZMod p)}
    (hxG : x ∈ G) (hxC : x ∈ isoCent (ZMod p)) {k : ℕ} (hk : x ^ k = 1) (hpk : ¬ p ∣ k)
    (hx4 : x ^ 4 ≠ 1) {y : isoLeviImage (ZMod p) G} (hy : orderOf y = p)
    (hc : Commute (isoLeviBar hxG hxC * y * (isoLeviBar hxG hxC)⁻¹) y) : False := by
  obtain ⟨g₀, hg₀G, hg₀C, rfl⟩ := exists_isoLeviBar_eq y
  have hgG : g₀ ^ 2 ∈ G := G.pow_mem hg₀G 2
  have hgC : g₀ ^ 2 ∈ isoCent (ZMod p) := pow_mem hg₀C 2
  have hgp : (g₀ ^ 2) ^ p = 1 := by
    have h1 : isoLeviBar (G.pow_mem hg₀G p) (pow_mem hg₀C p) = 1 := by
      have h := pow_orderOf_eq_one (isoLeviBar hg₀G hg₀C)
      rwa [hy, isoLeviBar_pow] at h
    refine hU0 _ (G.pow_mem hgG p) (isSqZero_of_leviBlock_eq_one (pow_mem hgC p) ?_)
    rw [pow_right_comm, leviBlock_val_pow (pow_mem hg₀C p)]
    rcases (isoLeviBar_eq_one_iff _ _).mp h1 with h' | h' <;> rw [h'] <;> simp
  have hg1 : g₀ ^ 2 ≠ 1 := by
    intro h1
    have h2 : isoLeviBar hg₀G hg₀C ^ 2 = 1 := by
      rw [isoLeviBar_pow, isoLeviBar_eq_one_iff, h1, Units.val_one, leviBlock_one]
      exact Or.inl rfl
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hy] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hcG : x * g₀ ^ 2 * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hxG hgG) (G.inv_mem hxG)
  have hcC : x * g₀ ^ 2 * x⁻¹ ∈ isoCent (ZMod p) := mul_mem (mul_mem hxC hgC) (inv_mem hxC)
  have hc2 : isoLeviBar hcG hcC * isoLeviBar hgG hgC =
      isoLeviBar hgG hgC * isoLeviBar hcG hcC := by
    have h := (hc.pow_pow 2 2).eq
    rwa [conj_pow, isoLeviBar_pow, isoLeviBar_inv, isoLeviBar_mul, isoLeviBar_mul] at h
  have heq : isoLeviBar (G.mul_mem hcG hgG) (mul_mem hcC hgC) =
      isoLeviBar (G.mul_mem hgG hcG) (mul_mem hgC hcC) := by
    rw [← isoLeviBar_mul hcG hcC hgG hgC, ← isoLeviBar_mul hgG hgC hcG hcC]
    exact hc2
  obtain ⟨ε, hε, hlev⟩ := exists_smul_of_isoLeviBar_eq (G.mul_mem hcG hgG) (mul_mem hcC hgC)
    (G.mul_mem hgG hcG) (mul_mem hgC hcC) heq
  rw [leviBlock_val_mul _ hgC, leviBlock_val_mul _ hcC] at hlev
  exact false_of_isoCent_normalizes (by omega) hU0 hgG hxG hgC hxC hgp hg1 hk hpk hx4
    ⟨ε, hε, hlev⟩

theorem not_dvd_card_isoLeviImage {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) {x : GL V₄ (ZMod p)} (hxG : x ∈ G)
    (hxC : x ∈ isoCent (ZMod p)) {k : ℕ} (hk : x ^ k = 1) (hpk : ¬ p ∣ k) (hx4 : x ^ 4 ≠ 1) :
    ¬ p ∣ Nat.card (isoLeviImage (ZMod p) G) := by
  intro hpH
  have hfalse : ∀ y : isoLeviImage (ZMod p) G, orderOf y = p →
      Commute (isoLeviBar hxG hxC * y * (isoLeviBar hxG hxC)⁻¹) y → False :=
    fun y hy hc => false_of_commute_isoLeviBar_conj hp7 hU0 hxG hxC hk hpk hx4 hy hc
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpH
  have hall : ¬ ∀ a b : isoLeviImage (ZMod p) G, a * b = b * a := fun h => hfalse y hy (h _ _)
  have hconj : orderOf (isoLeviBar hxG hxC * y * (isoLeviBar hxG hxC)⁻¹) = p :=
    (SemiconjBy.orderOf_eq _ (show SemiconjBy (isoLeviBar hxG hxC) y _ from
      (inv_mul_cancel_right _ _).symm)).symm.trans hy
  have hsmall : ∀ {d : ℕ}, 0 < d → d < 7 → ¬ orderOf y ∣ d := fun hd0 hd7 h => by
    rw [hy] at h
    have := Nat.le_of_dvd hd0 h
    omega
  have hFcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFcard
      (isoLeviImage (ZMod p) G) with
    hE | ⟨_, -, -, hcyc⟩ | ⟨_, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, _, -, -, N, C, hN, hNE, hNm, hC, -, -, hNC⟩ | ⟨m, -, hm1, ⟨e⟩⟩ | ⟨m, -, hm2, -⟩
  ·
    exact hall (@mul_comm' _ _ hE.toIsMulCommutative)
  ·
    haveI := hcyc
    exact hall mul_comm'
  ·
    exact hfalse y hy (commute_of_equiv_dihedral e (by rw [hconj]; omega) (by rw [hy]; omega))
  ·
    rcases orderOf_dvd_of_equiv_alternating_four e y with h | h <;>
      exact hsmall (by norm_num) (by norm_num) h
  ·
    rcases orderOf_dvd_of_equiv_perm_four e y with h | h <;>
      exact hsmall (by norm_num) (by norm_num) h
  ·
    rcases orderOf_dvd_of_equiv_alternating_five e y with h | h | h <;>
      exact hsmall (by norm_num) (by norm_num) h
  ·
    rcases Nat.eq_zero_or_pos m with rfl | hm
    ·
      have hN1 : N = ⊥ := Subgroup.eq_bot_of_card_eq N (by rw [hNm, pow_zero])
      rw [hN1, bot_sup_eq] at hNC
      have hCtop : ∀ a, a ∈ C := fun a => by rw [hNC]; exact Subgroup.mem_top a
      haveI := hC
      exact hall fun a b => congrArg Subtype.val (mul_comm' (⟨a, hCtop a⟩ : C) ⟨b, hCtop b⟩)
    ·
      obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p
        (by rw [hNm]; exact dvd_pow_self p hm.ne')
      have hn' : orderOf (n : isoLeviImage (ZMod p) G) = p := by rw [Subgroup.orderOf_coe, hn]
      have hmem := hN.conj_mem (n : isoLeviImage (ZMod p) G) n.2 (isoLeviBar hxG hxC)
      exact hfalse _ hn'
        (congrArg Subtype.val (@mul_comm' _ _ hNE.toIsMulCommutative ⟨_, hmem⟩ n))
  ·
    obtain rfl := Nat.dvd_one.mp hm1
    have hcard : Nat.card (isoLeviImage (ZMod p) G) =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      (Nat.card_congr e.toEquiv).trans (Nat.card_congr
        (CFSG.GorensteinWalter.FieldTransport.pslZModEquivGaloisFieldOne p).toEquiv).symm
    exact false_of_isoLeviImage_eq_top hp7 hU0 hneg (Subgroup.eq_top_of_card_eq _ hcard)
  ·
    have := Nat.dvd_one.mp hm2
    omega

end CFSG.RankThree.SubgroupLists
