module

public import CFSG.RankThree.SubgroupLists.SymplecticSkewElliptic
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem mem_map_conj {G : Subgroup (GL V₄ K)} {k y : GL V₄ K} :
    y ∈ G.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * y * k ∈ G := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hg
  · intro h
    refine ⟨k⁻¹ * y * k, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_map_conj {G : Subgroup (GL V₄ K)} {k g : GL V₄ K} (hg : g ∈ G) :
    k * g * k⁻¹ ∈ G.map (MulAut.conj k).toMonoidHom :=
  ⟨g, hg, rfl⟩

theorem map_conj_le_statedSp {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) {k : GL V₄ K}
    (hk : k ∈ StatedSp 2 K) : G.map (MulAut.conj k).toMonoidHom ≤ StatedSp 2 K := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_mem (mul_mem hk (hGS hg)) (inv_mem hk)

theorem commutant_map_conj {G : Subgroup (GL V₄ K)} (hcomm : commutant G = ⊥) (k : GL V₄ K) :
    commutant (G.map (MulAut.conj k).toMonoidHom) = ⊥ := by
  rw [eq_bot_iff]
  intro M hM
  rw [mem_commutant] at hM
  have hM' : ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * M * (k : Matrix V₄ V₄ K) ∈ commutant G := by
    rw [mem_commutant]
    intro g hg
    have h := hM _ (conj_mem_map_conj (k := k) hg)
    simp only [Units.val_mul] at h
    have hkk : ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (k : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g : Matrix V₄ V₄ K) * (((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * M * (k : Matrix V₄ V₄ K))
        = ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((k : Matrix V₄ V₄ K) * g *
            ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * M) * (k : Matrix V₄ V₄ K) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) (k : Matrix V₄ V₄ K), hkk,
            Matrix.one_mul]
      _ = ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (M * ((k : Matrix V₄ V₄ K) * g *
            ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K))) * (k : Matrix V₄ V₄ K) := by rw [h]
      _ = ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * M * (k : Matrix V₄ V₄ K) * g := by
          simp only [Matrix.mul_assoc]
          rw [hkk, Matrix.mul_one]
  rw [hcomm, Algebra.mem_bot] at hM'
  obtain ⟨c, hc⟩ := hM'
  rw [Algebra.mem_bot]
  refine ⟨c, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one] at hc ⊢
  have hkk' : (k : Matrix V₄ V₄ K) * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc c • (1 : Matrix V₄ V₄ K)
      = (k : Matrix V₄ V₄ K) * (c • 1) * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hkk']
    _ = M := by
        rw [hc]
        simp only [Matrix.mul_assoc]
        rw [hkk', Matrix.mul_one, ← Matrix.mul_assoc, hkk', Matrix.one_mul]

theorem notr_map_conj {G : Subgroup (GL V₄ K)} {k : GL V₄ K} (hk : k ∈ StatedSp 2 K)
    (hnotr : ∀ (a : V₄ → K) (c : K), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G) :
    ∀ (a : V₄ → K) (c : K), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G.map (MulAut.conj k).toMonoidHom := by
  intro a c ha hc hT
  have hconj := conj_spTrans (inv_mem hk) a c
  rw [inv_inv] at hconj
  rw [mem_map_conj, hconj] at hT
  refine hnotr _ c ?_ hc hT
  intro h0
  apply ha
  rw [← gl_mulVec_inv_mulVec k a, h0, Matrix.mulVec_zero]

theorem det_ne_zero_of_unipAxis_tGL {S : Matrix (Fin 2) (Fin 2) K}
    (h : unipAxis (tGL S) = lagInl) : S.det ≠ 0 := by
  intro h0
  obtain ⟨b, hb0, hb⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hmem : mkV 0 b ∈ unipAxis (tGL S) := by
    rw [mem_unipAxis, tGL_mulVec, hb, zero_add]
  rw [h] at hmem
  apply hb0
  ext i
  exact hmem i

theorem det_ne_zero_of_unipAxis_uGL {S : Matrix (Fin 2) (Fin 2) K}
    (h : unipAxis (uGL S) = graphLag 0) : S.det ≠ 0 := by
  intro h0
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hmem : mkV a 0 ∈ unipAxis (uGL S) := by
    rw [mem_unipAxis, uGL_mulVec, ha, zero_add]
  rw [h] at hmem
  apply ha0
  ext i
  have := hmem i
  simpa using this

theorem false_of_skew_elation {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) [Group.IsPerfect G]
    (hcomm : commutant G = ⊥) (hirr : IsIrreducibleOn G)
    (hnotr : ∀ (a : V₄ → ZMod p) (c : ZMod p), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G)
    {x : GL V₄ (ZMod p)} (hxG : x ∈ G) (hx : IsSqZero x)
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) : False := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain ⟨g, hg, hdisj⟩ := exists_conj_unipAxis_disjoint hp5 hGS hirr hnotr hxG hx hx2
  set y := g * x * g⁻¹ with hy
  have hyG : y ∈ G := G.mul_mem (G.mul_mem hg hxG) (G.inv_mem hg)
  have hysq : IsSqZero y := isSqZero_conj hx g
  have hy2 : finrank (ZMod p) (unipAxis y) = 2 := by rw [hy, finrank_unipAxis_conj]; exact hx2
  obtain ⟨h, hhS, hA, hB⟩ := exists_mem_statedSp_translate_eq hx2 hy2
    (fun u hu v hv => spForm_eq_zero_of_mem_unipAxis (hGS hxG) hx hx2 hu hv)
    (fun u hu v hv => spForm_eq_zero_of_mem_unipAxis (hGS hyG) hysq hy2 hu hv) hdisj
  set G' := G.map (MulAut.conj h⁻¹).toMonoidHom with hG'
  have hG'S : G' ≤ StatedSp 2 (ZMod p) := map_conj_le_statedSp hGS (inv_mem hhS)
  have : Group.IsPerfect G' := Group.IsPerfect.map _
  have hcomm' : commutant G' = ⊥ := commutant_map_conj hcomm _
  have hnotr' := notr_map_conj (inv_mem hhS) hnotr
  have hx'G : h⁻¹ * x * h⁻¹⁻¹ ∈ G' := conj_mem_map_conj hxG
  have hy'G : h⁻¹ * y * h⁻¹⁻¹ ∈ G' := conj_mem_map_conj hyG
  have hx'ax : unipAxis (h⁻¹ * x * h⁻¹⁻¹) = lagInl := by
    rw [unipAxis_conj, ← hA, ← translate_mul, inv_mul_cancel, translate_one]
  have hy'ax : unipAxis (h⁻¹ * y * h⁻¹⁻¹) = graphLag 0 := by
    rw [unipAxis_conj, ← hB, ← translate_mul, inv_mul_cancel, translate_one]
  obtain ⟨S, hS, hxS⟩ := exists_eq_tGL_of_unipAxis_eq_lagInl (hG'S hx'G) (isSqZero_conj hx _)
    hx'ax
  obtain ⟨S', -, hyS⟩ := exists_eq_uGL_of_unipAxis_eq_graphLag_zero (hG'S hy'G)
    (isSqZero_conj hysq _) hy'ax
  have hSdet : S.det ≠ 0 := det_ne_zero_of_unipAxis_tGL (hxS ▸ hx'ax)
  have hS'det : S'.det ≠ 0 := det_ne_zero_of_unipAxis_uGL (hyS ▸ hy'ax)
  have hdich' : ∀ y ∈ G', ∀ z ∈ G', IsSqZero y → IsSqZero z →
      finrank (ZMod p) (unipAxis y) = 2 → finrank (ZMod p) (unipAxis z) = 2 →
      unipAxis y = unipAxis z ∨ unipAxis y ⊓ unipAxis z = ⊥ :=
    fun y hy z hz hy' hz' hy2 hz2 => unipAxis_eq_or_disjoint hp5 hG'S hnotr' hy hz hy' hz' hy2 hz2
  have hΔ : ∀ y ∈ G', ∀ z ∈ G', IsSqZero y → IsSqZero z →
      finrank (ZMod p) (unipAxis y) = 2 → finrank (ZMod p) (unipAxis z) = 2 →
      unipAxis y ⊓ unipAxis z = ⊥ → ∃ τ : ZMod p, ∀ a ∈ unipAxis y,
        ((y : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((z : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ a) =
          τ • a := by
    intro y hy z hz hy' hz' hy2 hz2 hdisj'
    by_cases hev : ∃ a ∈ unipAxis y, a ≠ 0 ∧ ∃ μ : ZMod p,
        ((y : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((z : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ a) = μ • a
    · obtain ⟨a, ha, ha0, μ, hμ⟩ := hev
      by_cases hsc : ∀ b ∈ unipAxis y,
          ((y : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((z : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ b) = μ • b
      · exact ⟨μ, hsc⟩
      · push Not at hsc
        obtain ⟨b, hb, hbμ⟩ := hsc
        obtain ⟨c, d, hc, hd, hT⟩ :=
          exists_spTrans_of_disjoint_axes hp5 hG'S hy hz hy' hz' hy2 hdisj' ha ha0 hμ hb hbμ
        exact absurd hT (hnotr' c d hc hd)
    · push Not at hev
      exact (false_of_elliptic_pair hp5 hG'S hcomm' hnotr' hy hz hy' hz' hy2 hz2 hdisj'
        fun b hb hb0 μ => hev b hb hb0 μ).elim
  exact false_of_regulus_core h2 hG'S hcomm' hdich' hΔ hS hSdet hS'det (hxS ▸ hx'G) (hyS ▸ hy'G)

end CFSG.RankThree.SubgroupLists
