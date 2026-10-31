module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3Crit
public import CFSG.LocalAnalysis.StandardType.PhanELocalCodes
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchDir
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

namespace Exch

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem plxd_finrank_sup_of_ne {p t : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (ht : finrank K t = 1) (hne : p ≠ t) :
    finrank K ↥(p ⊔ t) = 2 := by
  have hinf : p ⊓ t = ⊥ := by
    by_contra h
    have hpos : 0 < finrank K ↥(p ⊓ t) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact h ((Submodule.finrank_eq_zero).mp h0)
    have hle : finrank K ↥(p ⊓ t) ≤ finrank K p := Submodule.finrank_mono inf_le_left
    have h1 : finrank K ↥(p ⊓ t) = 1 := by omega
    have hpt : p ⊓ t = p := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hp])
    have hle' : p ≤ t := by rw [← hpt]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle' (by rw [hp, ht]))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq p t
  rw [hinf, finrank_bot, add_zero, hp, ht] at hsum
  omega

private theorem plxd_sup_Vsub_one_eq_top {x : FlagK K 3} (h2 : x.E 2 ⊓ Vsub 3 1 = ⊥) :
    x.E 2 ⊔ Vsub 3 1 = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 2) (Vsub (K := K) 3 1)
  rw [h2, finrank_bot, add_zero, x.dim 2 (by norm_num),
    finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
  rw [Module.finrank_fin_fun]
  omega

private theorem plxd_farSet_013 {x : FlagK K 3} :
    x ∈ farSet 3 [0, 1, 3] ↔ x.E 1 ⊓ Vsub 3 1 = ⊥ ∧ x.E 2 ⊓ Vsub 3 1 = ⊥ := by
  have hle : ∀ i, i < [0, 1, 3].length → [0, 1, 3].getD i 0 ≤ 3 := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> decide
  rw [mem_farSet_iff hle]
  constructor
  · intro h
    exact ⟨(h 1 (by decide) 1 (by decide)).1 (by decide),
      (h 1 (by decide) 2 (by decide)).1 (by decide)⟩
  · rintro ⟨h1, h2⟩ i hi j hj
    have htop3 : x.E 3 = ⊤ := x.top 3 (by norm_num)
    have hbot0 : x.E 0 = ⊥ := FlagK.E_zero x
    have hsup2 : x.E 2 ⊔ Vsub 3 1 = ⊤ := plxd_sup_Vsub_one_eq_top h2
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> interval_cases j <;>
      simp [Vsub_zero, Vsub_self, htop3, hbot0, h1, h2, hsup2]

theorem mem_setA2A1_iff (c : FlagK K 3 × FlagK K 2) :
    c ∈ setA2A1 K f ↔ c.1.E 1 ⊓ Vsub 3 1 = ⊥ ∧ c.1.E 2 ⊓ Vsub 3 1 = ⊥ ∧
      c.1.E 1 ⊔ Vsub 3 1 ≠ dirZ K f (c.2.E 1) := by
  have hblockU : blockU K 3 [0, 1, 3] c.1.E 1 1 = c.1.E 1 ⊔ Vsub 3 1 := by
    simp only [blockU, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_self, Nat.zero_add,
      Vsub_self, inf_top_eq]
  change (c.1 ∈ farSet 3 [0, 1, 3] ∧
      blockU K 3 [0, 1, 3] c.1.E 1 1 ≠ dirZ K f (c.2.E 1)) ↔ _
  rw [plxd_farSet_013, hblockU]
  tauto

theorem exists_mem_setA2A1 {p l : Submodule K (Fin 3 → K)} (hp : finrank K p = 1)
    (hl : finrank K l = 2) (hpl : p ≤ l) (hpV : p ⊓ Vsub 3 1 = ⊥) (hlV : l ⊓ Vsub 3 1 = ⊥)
    {z : Submodule K (Fin 2 → K)} (hz : finrank K z = 1) (hd : p ⊔ Vsub 3 1 ≠ dirZ K f z) :
    ∃ c ∈ setA2A1 K f, c.1.E 1 = p ∧ c.1.E 2 = l ∧ c.2.E 1 = z := by
  refine ⟨(Plane.ofChain p l hp hl hpl, ofPoint z hz), ?_, ?_, ?_, ?_⟩
  · rw [mem_setA2A1_iff]
    exact ⟨hpV, hlV, hd⟩
  · exact Plane.ofChain_E_one p l hp hl hpl
  · exact Plane.ofChain_E_two p l hp hl hpl
  · exact ofPoint_E_one z hz

variable (K f)

noncomputable abbrev X : ChamberSystem (Fin 2 ⊕ Fin 1) ↥(setA2A1 K f) :=
  ((flagSys K 2).prod (flagSys K 1)).restrict (setA2A1 K f)

@[expose] def V : Type := {p : Submodule K (Fin 3 → K) // ∃ c : ↥(setA2A1 K f), c.1.1.E 1 = p}

@[expose] def P (c : ↥(setA2A1 K f)) : V K f := ⟨c.1.1.E 1, c, rfl⟩

variable {K f}

theorem adj_a (c c' : ↥(setA2A1 K f)) :
    (X K f).adj (Sum.inl 0) c c' ↔ c.1.1.E 2 = c'.1.1.E 2 ∧ c.1.2.E 1 = c'.1.2.E 1 := by
  change (flagSys K 2).adj 0 c.1.1 c'.1.1 ∧ c.1.2 = c'.1.2 ↔
    c.1.1.E 2 = c'.1.1.E 2 ∧ c.1.2.E 1 = c'.1.2.E 1
  rw [Plane.adj_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, flag_ext h2⟩

theorem adj_b (c c' : ↥(setA2A1 K f)) :
    (X K f).adj (Sum.inl 1) c c' ↔ c.1.1.E 1 = c'.1.1.E 1 ∧ c.1.2.E 1 = c'.1.2.E 1 := by
  change (flagSys K 2).adj 1 c.1.1 c'.1.1 ∧ c.1.2 = c'.1.2 ↔
    c.1.1.E 1 = c'.1.1.E 1 ∧ c.1.2.E 1 = c'.1.2.E 1
  rw [Plane.adj_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, flag_ext h2⟩

theorem adj_c (c c' : ↥(setA2A1 K f)) :
    (X K f).adj (Sum.inr 0) c c' ↔ c.1.1.E 1 = c'.1.1.E 1 ∧ c.1.1.E 2 = c'.1.1.E 2 := by
  change c.1.1 = c'.1.1 ∧ (flagSys K 1).adj 0 c.1.2 c'.1.2 ↔
    c.1.1.E 1 = c'.1.1.E 1 ∧ c.1.1.E 2 = c'.1.1.E 2
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨by rw [h1], by rw [h1]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Plane.ext h1 h2, flagSys_one_adj K c.1.2 c'.1.2 0⟩

theorem finrank_pt (p : V K f) : finrank K p.1 = 1 := by
  obtain ⟨c, hc⟩ := p.2
  rw [← hc]
  exact Plane.finrank_E_one c.1.1

theorem pt_inf_Vsub (p : V K f) : p.1 ⊓ Vsub 3 1 = ⊥ := by
  obtain ⟨c, hc⟩ := p.2
  rw [← hc]
  exact ((mem_setA2A1_iff c.1).mp c.2).1

theorem pointGraph_adj_iff (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (p t : V K f) :
    (pointGraph (X K f) (Sum.inl 0) (P K f)).Adj p t ↔
      p ≠ t ∧ p.1 ⊔ Vsub 3 1 ≠ t.1 ⊔ Vsub 3 1 := by
  constructor
  · rintro ⟨hne, e, g, hadj, hPe, hPf⟩
    refine ⟨hne, ?_⟩
    intro hdir
    have hadj' := (adj_a e g).mp hadj
    have hpe : e.1.1.E 1 = p.1 := congrArg Subtype.val hPe
    have hpf : g.1.1.E 1 = t.1 := congrArg Subtype.val hPf
    have hline : e.1.1.E 2 ⊓ Vsub 3 1 = ⊥ := ((mem_setA2A1_iff e.1).mp e.2).2.1
    have hpt : p.1 ⊔ t.1 = p.1 ⊔ Vsub 3 1 := by
      have hle : p.1 ⊔ t.1 ≤ p.1 ⊔ Vsub 3 1 := by
        apply sup_le le_sup_left
        rw [hdir]
        exact le_sup_left
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [plxd_finrank_sup_of_ne (finrank_pt p) (finrank_pt t)
        (fun h => hne (Subtype.ext h))]
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq p.1 (Vsub (K := K) 3 1)
      rw [pt_inf_Vsub p, finrank_bot, add_zero, finrank_pt p,
        finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
      omega
    have hle : p.1 ⊔ Vsub 3 1 ≤ e.1.1.E 2 := by
      rw [← hpt]
      exact sup_le (by rw [← hpe]; exact e.1.1.mono (by norm_num))
        (by rw [← hpf, hadj'.1]; exact g.1.1.mono (by norm_num))
    have hVle : Vsub 3 1 ≤ e.1.1.E 2 := le_sup_right.trans hle
    have hbot : Vsub (K := K) 3 1 = ⊥ := by
      rw [← inf_eq_left.mpr hVle, inf_comm, hline]
    have : finrank K (Vsub (K := K) 3 1) = 0 := by rw [hbot, finrank_bot]
    rw [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at this
    omega
  · rintro ⟨hne, hdir⟩
    have hpt_ne : p.1 ≠ t.1 := fun h => hne (Subtype.ext h)
    have hℓfin : finrank K ↥(p.1 ⊔ t.1) = 2 :=
      plxd_finrank_sup_of_ne (finrank_pt p) (finrank_pt t) hpt_ne
    have hℓV : (p.1 ⊔ t.1) ⊓ Vsub 3 1 = ⊥ := by
      by_contra h
      have hVle : Vsub 3 1 ≤ p.1 ⊔ t.1 := by
        have hpos : 0 < finrank K ↥((p.1 ⊔ t.1) ⊓ Vsub 3 1) := by
          rw [Nat.pos_iff_ne_zero]
          intro h0
          exact h ((Submodule.finrank_eq_zero).mp h0)
        have hle : finrank K ↥((p.1 ⊔ t.1) ⊓ Vsub 3 1) ≤ finrank K (Vsub 3 1) :=
          Submodule.finrank_mono inf_le_right
        have h1 : finrank K ↥((p.1 ⊔ t.1) ⊓ Vsub 3 1) = 1 := by
          rw [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hle
          omega
        have heq : (p.1 ⊔ t.1) ⊓ Vsub 3 1 = Vsub 3 1 :=
          Submodule.eq_of_le_of_finrank_eq inf_le_right
            (by rw [h1, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)])
        rw [← heq]
        exact inf_le_left
      have hfinpV : finrank K ↥(p.1 ⊔ Vsub 3 1) = 2 := by
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq p.1 (Vsub (K := K) 3 1)
        rw [pt_inf_Vsub p, finrank_bot, add_zero, finrank_pt p,
          finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
        omega
      have hfintV : finrank K ↥(t.1 ⊔ Vsub 3 1) = 2 := by
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq t.1 (Vsub (K := K) 3 1)
        rw [pt_inf_Vsub t, finrank_bot, add_zero, finrank_pt t,
          finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
        omega
      have hpV : p.1 ⊔ Vsub 3 1 = p.1 ⊔ t.1 :=
        Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hVle) (by rw [hfinpV, hℓfin])
      have htV : t.1 ⊔ Vsub 3 1 = p.1 ⊔ t.1 :=
        Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_right hVle) (by rw [hfintV, hℓfin])
      exact hdir (hpV.trans htV.symm)
    obtain ⟨z, hz, hzdir⟩ := exists_z_avoid hK hq
      ({p.1 ⊔ Vsub 3 1, t.1 ⊔ Vsub 3 1} : Finset (Submodule K (Fin 3 → K)))
      ((Finset.card_le_two (a := p.1 ⊔ Vsub 3 1) (b := t.1 ⊔ Vsub 3 1)).trans (by norm_num))
    have hpz : p.1 ⊔ Vsub 3 1 ≠ dirZ K f z :=
      fun h => hzdir (p.1 ⊔ Vsub 3 1) (by simp) h.symm
    have htz : t.1 ⊔ Vsub 3 1 ≠ dirZ K f z :=
      fun h => hzdir (t.1 ⊔ Vsub 3 1) (by simp) h.symm
    obtain ⟨e₀, he₀, he1, he2, hez⟩ :=
      exists_mem_setA2A1 (finrank_pt p) hℓfin le_sup_left (pt_inf_Vsub p) hℓV hz hpz
    obtain ⟨g₀, hg₀, hg1, hg2, hgz⟩ :=
      exists_mem_setA2A1 (finrank_pt t) hℓfin le_sup_right (pt_inf_Vsub t) hℓV hz htz
    refine ⟨hne, ⟨e₀, he₀⟩, ⟨g₀, hg₀⟩, (adj_a ⟨e₀, he₀⟩ ⟨g₀, hg₀⟩).mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [he2, hg2]
    · rw [hez, hgz]
    · apply Subtype.ext
      exact he1
    · apply Subtype.ext
      exact hg1

end Exch

end CFSG.ClassicalInvolution.Phan.PhanE

end
