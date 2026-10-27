module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchDef
import CFSG.LocalAnalysis.StandardType.PhanELocalFlag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Exch

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem plxn_finrank_sup_of_disjoint {A B : Submodule K (Fin 3 → K)}
    (h : Disjoint A B) : finrank K ↥(A ⊔ B) = finrank K A + finrank K B := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [h.eq_bot, finrank_bot, add_zero] at hsum
  exact hsum

private theorem plxn_point_of_subspace (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {t₀ : Submodule K (Fin 3 → K)} (ht₀ : finrank K t₀ = 1)
    (ht₀V : t₀ ⊓ Vsub 3 1 = ⊥) : ∃ t : V K f, t.1 = t₀ := by
  classical
  have hdisj : Disjoint t₀ (Vsub 3 1) := disjoint_iff.mpr ht₀V
  have hsup2 : finrank K ↥(t₀ ⊔ Vsub 3 1) = 2 := by
    rw [plxn_finrank_sup_of_disjoint hdisj, ht₀,
      finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)]
  have htop' : t₀ ⊔ Vsub 3 1 ≠ ⊤ := by
    intro h
    have h3 : finrank K ↥(t₀ ⊔ Vsub 3 1) = 3 := by
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ (t₀ ⊔ Vsub 3 1 : Submodule K (Fin 3 → K)) := by
    by_contra h
    exact htop' (Submodule.eq_top_iff'.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  let l : Submodule K (Fin 3 → K) := t₀ ⊔ K ∙ w
  have hwl : w ∉ t₀ := fun hmem => hw (Submodule.mem_sup_left hmem)
  have hlfin : finrank K l = 2 := by
    change finrank K ↥(t₀ ⊔ K ∙ w) = 2
    rw [Submodule.finrank_sup_span_singleton hwl, ht₀]
  have hlV : l ⊓ Vsub 3 1 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxl, hxV⟩ := hx
    change x ∈ t₀ ⊔ K ∙ w at hxl
    rw [Submodule.mem_sup] at hxl
    obtain ⟨a, ha, b, hb, hab⟩ := hxl
    rw [Submodule.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero] at hab
      have hbot : x ∈ t₀ ⊓ Vsub 3 1 := ⟨hab ▸ ha, hxV⟩
      rw [ht₀V, Submodule.mem_bot] at hbot
      exact hbot
    · exfalso
      have htrace : c⁻¹ • x - c⁻¹ • a = w := by
        rw [← hab, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
        abel
      have hwmem : w ∈ t₀ ⊔ Vsub 3 1 := by
        rw [← htrace]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right hxV))
          (Submodule.smul_mem _ _ (Submodule.mem_sup_left ha))
      exact hw hwmem
  obtain ⟨z, hzdim, hzavoid⟩ := exists_z_avoid (K := K) (f := f) hK hq
    ({t₀ ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))
    (by rw [Finset.card_singleton]; norm_num)
  have hzd : t₀ ⊔ Vsub 3 1 ≠ dirZ K f z := (hzavoid (t₀ ⊔ Vsub 3 1) (by simp)).symm
  obtain ⟨c, hc, h1, _, _⟩ :=
    exists_mem_setA2A1 (K := K) (f := f) ht₀ hlfin le_sup_left ht₀V hlV hzdim hzd
  exact ⟨⟨t₀, ⟨⟨c, hc⟩, h1⟩⟩, rfl⟩

private theorem plxn_exists_pt (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (D : Finset (Submodule K (Fin 3 → K))) (hDne : D.Nonempty) (hDc : D.card ≤ 4)
    (hDdim : ∀ d ∈ D, finrank K d = 2) (hDV : ∀ d ∈ D, Vsub 3 1 ≤ d) :
    ∃ t : V K f, t.1 ⊔ Vsub 3 1 ∉ D := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hDtop : ∀ d ∈ D, d ≠ ⊤ := by
    intro d hd htop
    have hd2 := hDdim d hd
    rw [htop, finrank_top, Module.finrank_fin_fun] at hd2
    omega
  have h16 : 16 ≤ Nat.card K := by
    rw [hK]
    nlinarith [hq]
  have hcard : D.card < ENat.card K := by
    rw [ENat.card_eq_coe_fintype_card]
    have hlt : D.card < Fintype.card K := by
      rw [← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt hDc (lt_of_lt_of_le (by norm_num) h16)
    exact_mod_cast hlt
  let p : Submodule K (Fin 3 → K) → Submodule K (Fin 3 → K) :=
    fun d => if d ∈ D then d else ⊥
  have hp : ∀ d, p d ≠ ⊤ := by
    intro d
    by_cases hd : d ∈ D
    · simp only [p, if_pos hd]; exact hDtop d hd
    · simp only [p, if_neg hd]; exact bot_ne_top
  have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt D p hp hcard
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hsub
  have hvD : ∀ d ∈ D, v ∉ d := by
    intro d hd hmem
    exact hv (Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, by
      simp only [p, if_pos hd]; exact hmem⟩⟩)
  have hvV : v ∉ Vsub 3 1 := by
    obtain ⟨d₀, hd₀⟩ := hDne
    exact fun hmem => hvD d₀ hd₀ (hDV d₀ hd₀ hmem)
  have hv0 : v ≠ 0 := by
    obtain ⟨d₀, hd₀⟩ := hDne
    intro h0
    exact hvD d₀ hd₀ (by rw [h0]; exact zero_mem d₀)
  have ht₀ : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have ht₀V : (K ∙ v) ⊓ Vsub 3 1 = ⊥ :=
    (disjoint_comm.mpr ((Submodule.disjoint_span_singleton' (s := Vsub 3 1) (x := v) hv0).mpr
      hvV)).eq_bot
  obtain ⟨t, ht⟩ := plxn_point_of_subspace (K := K) (f := f) hK hq ht₀ ht₀V
  refine ⟨t, fun hmem => hvD (t.1 ⊔ Vsub 3 1) hmem ?_⟩
  rw [ht]
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)

private theorem plxn_chamber {p l : Submodule K (Fin 3 → K)} (hp : finrank K p = 1)
    (hl : finrank K l = 2) (hpl : p ≤ l) (hpV : p ⊓ Vsub 3 1 = ⊥) (hlV : l ⊓ Vsub 3 1 = ⊥)
    {z : Submodule K (Fin 2 → K)} (hz : finrank K z = 1) (hd : p ⊔ Vsub 3 1 ≠ dirZ K f z) :
    ∃ c : ↥(setA2A1 K f), c.1.1.E 1 = p ∧ c.1.1.E 2 = l ∧ c.1.2.E 1 = z := by
  obtain ⟨c, hc, h1, h2, h3⟩ := exists_mem_setA2A1 (K := K) (f := f) hp hl hpl hpV hlV hz hd
  exact ⟨⟨c, hc⟩, h1, h2, h3⟩

private theorem plxn_line {p q : V K f} (h : p.1 ⊔ Vsub 3 1 ≠ q.1 ⊔ Vsub 3 1) :
    finrank K ↥(p.1 ⊔ q.1) = 2 ∧ ((p.1 ⊔ q.1) ⊓ Vsub 3 1 : Submodule K (Fin 3 → K)) = ⊥ := by
  have hpq : p.1 ≠ q.1 := fun heq => h (by rw [heq])
  have hdisj : Disjoint p.1 q.1 := by
    rw [disjoint_iff]
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvp, hvq⟩ := hv
    by_contra hv0
    have hp1 : K ∙ v = p.1 := by
      refine Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem v p.1).mpr hvp) ?_
      rw [finrank_span_singleton hv0, finrank_pt p]
    have hq1 : K ∙ v = q.1 := by
      refine Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem v q.1).mpr hvq) ?_
      rw [finrank_span_singleton hv0, finrank_pt q]
    exact hpq (hp1.symm.trans hq1)
  have hpV : finrank K ↥(p.1 ⊔ Vsub 3 1) = 2 := by
    rw [plxn_finrank_sup_of_disjoint (disjoint_iff.mpr (pt_inf_Vsub p)), finrank_pt p,
      finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)]
  refine ⟨?_, ?_⟩
  · rw [plxn_finrank_sup_of_disjoint hdisj, finrank_pt p, finrank_pt q]
  · by_contra hne
    have hVle : Vsub 3 1 ≤ p.1 ⊔ q.1 := by
      have hle : (p.1 ⊔ q.1) ⊓ Vsub 3 1 ≤ Vsub 3 1 := inf_le_right
      have hfin1 : finrank K ↥((p.1 ⊔ q.1) ⊓ Vsub 3 1) = 1 := by
        have hpos : 0 < finrank K ↥((p.1 ⊔ q.1) ⊓ Vsub 3 1) := by
          rw [Nat.pos_iff_ne_zero]
          intro h0
          exact hne (Submodule.finrank_eq_zero.mp h0)
        have hle1 : finrank K ↥((p.1 ⊔ q.1) ⊓ Vsub 3 1) ≤ 1 := by
          have h : finrank K ↥((p.1 ⊔ q.1) ⊓ Vsub 3 1) ≤ finrank K ↥(Vsub 3 1) :=
            Submodule.finrank_mono inf_le_right
          rwa [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)] at h
        omega
      have heq : (p.1 ⊔ q.1) ⊓ Vsub 3 1 = Vsub 3 1 :=
        Submodule.eq_of_le_of_finrank_eq hle
          (by rw [hfin1, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)])
      rw [← heq]
      exact inf_le_left
    have hpsup : p.1 ⊔ Vsub 3 1 ≤ p.1 ⊔ q.1 :=
      sup_le le_sup_left hVle
    have hpqfin : finrank K ↥(p.1 ⊔ q.1) = 2 := by
      rw [plxn_finrank_sup_of_disjoint hdisj, finrank_pt p, finrank_pt q]
    have heq : p.1 ⊔ Vsub 3 1 = p.1 ⊔ q.1 :=
      Submodule.eq_of_le_of_finrank_eq hpsup (by rw [hpV, hpqfin])
    have hqle : q.1 ≤ p.1 ⊔ Vsub 3 1 := heq.symm ▸ le_sup_right
    have hfinq : finrank K ↥(q.1 ⊔ Vsub 3 1) = 2 := by
      rw [plxn_finrank_sup_of_disjoint (disjoint_iff.mpr (pt_inf_Vsub q)), finrank_pt q,
        finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)]
    have hqsup : q.1 ⊔ Vsub 3 1 ≤ p.1 ⊔ Vsub 3 1 := sup_le hqle le_sup_right
    exact h (Submodule.eq_of_le_of_finrank_eq hqsup (by rw [hfinq, hpV])).symm

private theorem plxn_planar (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {x y w : V K f} (hxy : x.1 ⊔ Vsub 3 1 ≠ y.1 ⊔ Vsub 3 1)
    (hyw : y.1 ⊔ Vsub 3 1 ≠ w.1 ⊔ Vsub 3 1)
    (hwx : w.1 ⊔ Vsub 3 1 ≠ x.1 ⊔ Vsub 3 1) :
    PlanarTriple (X K f) (Sum.inl 0) (Sum.inl 1) (P K f) x y w := by
  classical
  obtain ⟨z₀, hz₀dim, hz₀avoid⟩ := exists_z_avoid (K := K) (f := f) hK hq
    ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, w.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))
    (Finset.card_le_three.trans (by norm_num))
  obtain ⟨hxyfin, hxyV⟩ := plxn_line (p := x) (q := y) hxy
  obtain ⟨hywfin, hywV⟩ := plxn_line (p := y) (q := w) hyw
  obtain ⟨hwxfin, hwxV⟩ := plxn_line (p := w) (q := x) hwx
  have hdx : dirZ K f z₀ ≠ x.1 ⊔ Vsub 3 1 := hz₀avoid (x.1 ⊔ Vsub 3 1) (by simp)
  have hdy : dirZ K f z₀ ≠ y.1 ⊔ Vsub 3 1 := hz₀avoid (y.1 ⊔ Vsub 3 1) (by simp)
  have hdw : dirZ K f z₀ ≠ w.1 ⊔ Vsub 3 1 := hz₀avoid (w.1 ⊔ Vsub 3 1) (by simp)
  obtain ⟨e₁, he₁p, he₁l, he₁z⟩ := plxn_chamber
    (finrank_pt x) hxyfin le_sup_left (pt_inf_Vsub x) hxyV hz₀dim hdx.symm
  obtain ⟨f₁, hf₁p, hf₁l, hf₁z⟩ := plxn_chamber
    (finrank_pt y) hxyfin le_sup_right (pt_inf_Vsub y) hxyV hz₀dim hdy.symm
  obtain ⟨e₂, he₂p, he₂l, he₂z⟩ := plxn_chamber
    (finrank_pt y) hywfin le_sup_left (pt_inf_Vsub y) hywV hz₀dim hdy.symm
  obtain ⟨f₂, hf₂p, hf₂l, hf₂z⟩ := plxn_chamber
    (finrank_pt w) hywfin le_sup_right (pt_inf_Vsub w) hywV hz₀dim hdw.symm
  obtain ⟨e₃, he₃p, he₃l, he₃z⟩ := plxn_chamber
    (finrank_pt w) hwxfin le_sup_left (pt_inf_Vsub w) hwxV hz₀dim hdw.symm
  obtain ⟨f₃, hf₃p, hf₃l, hf₃z⟩ := plxn_chamber
    (finrank_pt x) hwxfin le_sup_right (pt_inf_Vsub x) hwxV hz₀dim hdx.symm
  refine ⟨e₁, f₁, e₂, f₂, e₃, f₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (adj_a e₁ f₁).mpr ⟨he₁l.trans hf₁l.symm, he₁z.trans hf₁z.symm⟩
  · exact (adj_b f₁ e₂).mpr ⟨hf₁p.trans he₂p.symm, hf₁z.trans he₂z.symm⟩
  · exact (adj_a e₂ f₂).mpr ⟨he₂l.trans hf₂l.symm, he₂z.trans hf₂z.symm⟩
  · exact (adj_b f₂ e₃).mpr ⟨hf₂p.trans he₃p.symm, hf₂z.trans he₃z.symm⟩
  · exact (adj_a e₃ f₃).mpr ⟨he₃l.trans hf₃l.symm, he₃z.trans hf₃z.symm⟩
  · exact (adj_b f₃ e₁).mpr ⟨hf₃p.trans he₁p.symm, hf₃z.trans he₁z.symm⟩
  · exact Subtype.ext he₁p
  · exact Subtype.ext hf₁p
  · exact Subtype.ext hf₂p
  · exact Subtype.ext hf₃p

theorem cn_exch (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (s : Finset (V K f))
    (hs : s.Nonempty) (hc : s.card ≤ 4) :
    ∃ t : V K f, ∀ p ∈ s, (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj p t := by
  classical
  have hdir : ∀ p : V K f, finrank K ↥(p.1 ⊔ Vsub 3 1) = 2 := by
    intro p
    rw [plxn_finrank_sup_of_disjoint (disjoint_iff.mpr (pt_inf_Vsub p)), finrank_pt p,
      finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)]
  obtain ⟨t, ht⟩ := plxn_exists_pt (K := K) (f := f) hK hq (s.image fun p => p.1 ⊔ Vsub 3 1)
    (hs.image _) (Finset.card_image_le.trans hc)
    (by
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨p, -, rfl⟩ := hd
      exact hdir p)
    (by
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨p, -, rfl⟩ := hd
      exact le_sup_right)
  refine ⟨t, fun p hp => ?_⟩
  have hdp : p.1 ⊔ Vsub 3 1 ∈ s.image fun p => p.1 ⊔ Vsub 3 1 :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hne : p.1 ⊔ Vsub 3 1 ≠ t.1 ⊔ Vsub 3 1 := fun heq => ht (heq ▸ hdp)
  rw [pointGraph_adj_iff hK hq p t]
  exact ⟨fun hpt => hne (by rw [hpt]), hne⟩

theorem cone_exch (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {x y z : V K f}
    (hxy : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj x y)
    (hyz : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj y z)
    (hzx : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj z x) :
    ∃ t : V K f, (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj x t ∧
      (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj y t ∧
      (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj z t ∧
      PlanarTriple (X K f) (Sum.inl 0) (Sum.inl 1) (P K f) x y t ∧
      PlanarTriple (X K f) (Sum.inl 0) (Sum.inl 1) (P K f) y z t ∧
      PlanarTriple (X K f) (Sum.inl 0) (Sum.inl 1) (P K f) z x t := by
  classical
  rw [pointGraph_adj_iff hK hq x y] at hxy
  rw [pointGraph_adj_iff hK hq y z] at hyz
  rw [pointGraph_adj_iff hK hq z x] at hzx
  have hdir : ∀ p : V K f, finrank K ↥(p.1 ⊔ Vsub 3 1) = 2 := by
    intro p
    rw [plxn_finrank_sup_of_disjoint (disjoint_iff.mpr (pt_inf_Vsub p)), finrank_pt p,
      finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num : 1 ≤ 3)]
  have hDc : ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} :
      Finset (Submodule K (Fin 3 → K))).card ≤ 4 :=
    Finset.card_le_three.trans (by norm_num)
  have hDdim : ∀ d ∈ ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} :
      Finset (Submodule K (Fin 3 → K))), finrank K d = 2 := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hdir x
    · exact hdir y
    · exact hdir z
  have hDV : ∀ d ∈ ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} :
      Finset (Submodule K (Fin 3 → K))), Vsub 3 1 ≤ d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> exact le_sup_right
  obtain ⟨t, ht⟩ := plxn_exists_pt (K := K) (f := f) hK hq
    ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))
    ⟨x.1 ⊔ Vsub 3 1, by simp⟩ hDc hDdim hDV
  have hxt_dir : x.1 ⊔ Vsub 3 1 ≠ t.1 ⊔ Vsub 3 1 :=
    fun heq => ht (heq ▸ (by simp : x.1 ⊔ Vsub 3 1 ∈
      ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))))
  have hyt_dir : y.1 ⊔ Vsub 3 1 ≠ t.1 ⊔ Vsub 3 1 :=
    fun heq => ht (heq ▸ (by simp : y.1 ⊔ Vsub 3 1 ∈
      ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))))
  have hzt_dir : z.1 ⊔ Vsub 3 1 ≠ t.1 ⊔ Vsub 3 1 :=
    fun heq => ht (heq ▸ (by simp : z.1 ⊔ Vsub 3 1 ∈
      ({x.1 ⊔ Vsub 3 1, y.1 ⊔ Vsub 3 1, z.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))))
  have hxt : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj x t := by
    rw [pointGraph_adj_iff hK hq x t]
    exact ⟨fun hpt => hxt_dir (by rw [hpt]), hxt_dir⟩
  have hyt : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj y t := by
    rw [pointGraph_adj_iff hK hq y t]
    exact ⟨fun hpt => hyt_dir (by rw [hpt]), hyt_dir⟩
  have hzt : (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj z t := by
    rw [pointGraph_adj_iff hK hq z t]
    exact ⟨fun hpt => hzt_dir (by rw [hpt]), hzt_dir⟩
  exact ⟨t, hxt, hyt, hzt,
    plxn_planar hK hq hxy.2 hyt_dir hxt_dir.symm,
    plxn_planar hK hq hyz.2 hzt_dir hyt_dir.symm,
    plxn_planar hK hq hzx.2 hxt_dir hzt_dir.symm⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Exch

end
