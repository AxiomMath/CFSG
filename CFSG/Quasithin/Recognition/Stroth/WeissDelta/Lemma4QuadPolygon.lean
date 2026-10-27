module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4QuadL
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypesPolygon

public section

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y] [Finite Y]

theorem quadSetup_of_polygon4
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 4) (hW : WeissFree c.G0 c.graph 4)
    (hg : ((2 * 4 + 2 : ℕ) : ℕ∞) < c.graph.egirth)
    {k m : ℕ} (F : Type) [Field F] [Finite F] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    QuadSetup c.G0 c.graph k m F (fun v => ∃ g : c.G0, g • c.xv = v) := by
  classical
  have hq1 : 3 ≤ (P1 ⊓ P2).relIndex P1 := by
    obtain ⟨e, he, hrel⟩ := hV1
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hq2 : 3 ≤ (P1 ⊓ P2).relIndex P2 := by
    obtain ⟨e, he, hrel⟩ := hV2
    rw [hrel]
    have h : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    omega
  have hdeg : ∀ v : c.Γ, ∃ w w' : c.Γ,
      c.graph.Adj v w ∧ c.graph.Adj v w' ∧ w ≠ w' := by
    intro v
    have hpos : 0 < Nat.card (c.graph.neighborSet v) := by
      rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
      · rw [hv]; omega
      · rw [hv]; omega
    obtain ⟨⟨w, hw⟩, -⟩ := Nat.card_pos_iff.mp hpos
    obtain ⟨w', hw', hne⟩ := exists_adj_ne c hc hq1 hq2 v w (by simpa using hw)
    exact ⟨w, w', by simpa using hw, hw', hne.symm⟩
  refine
    { egirth := hg
      moufang := hM
      weissFree := hW
      ne := exists_adj_ne c hc hq1 hq2
      three := ?_
      val := card_adj_ne_eq_two_pow c hc hV1 hV2
      loc := ?_
      kernel_le := ?_
      adj := ?_
      conj := ?_
      u3 := ?_
      l2 := ?_ }
  ·
    intro v w w' hvw hvw'
    by_cases hww' : w = w'
    · subst hww'
      obtain ⟨u, hu1, hu2⟩ := exists_adj_ne c hc hq1 hq2 v w hvw
      exact ⟨u, hu1, hu2, hu2⟩
    · have hval : 3 ≤ (c.graph.neighborSet v).ncard := by
        rw [← Nat.card_coe_set_eq]
        rcases card_neighborSet_eq c hc v with ⟨-, hv⟩ | ⟨-, hv⟩
        · rw [hv]; exact hq1
        · rw [hv]; exact hq2
      have hmem : w ∈ c.graph.neighborSet v := by simpa using hvw
      have hSn : (c.graph.neighborSet v \ {w}).ncard =
          (c.graph.neighborSet v).ncard - 1 :=
        Set.ncard_sdiff_singleton_of_mem (s := c.graph.neighborSet v) hmem
      have h1 : 1 < (c.graph.neighborSet v \ {w}).ncard := by rw [hSn]; omega
      obtain ⟨u, hu, hune⟩ := Set.exists_ne_of_one_lt_ncard h1 w'
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, SimpleGraph.mem_neighborSet] at hu
      exact ⟨u, hu.1, hu.2, hune⟩
  ·
    intro w u v hwu hwv
    have h2tr : ∀ {a b a' b' : {x : c.Γ // c.graph.Adj w x}}, a ≠ b → a' ≠ b' →
        ∃ p : ↥(localGroup c.G0 c.graph w), p • a = a' ∧ p • b = b' := by
      obtain (⟨g, rfl⟩ | ⟨g, rfl⟩) := exists_smul_eq_xv_or_lv (c := c) w
      · exact MulAction.is_two_pretransitive_iff.mp
          (isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g).1.2.1
      · exact MulAction.is_two_pretransitive_iff.mp
          (isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g).2.2.1
    obtain ⟨b, hwb, hbu⟩ := exists_adj_ne c hc hq1 hq2 w u hwu
    obtain ⟨d, hwd, hdv⟩ := exists_adj_ne c hc hq1 hq2 w v hwv
    obtain ⟨p, hp1, hp2⟩ := h2tr (a := ⟨u, hwu⟩) (b := ⟨b, hwb⟩) (a' := ⟨v, hwv⟩)
      (b' := ⟨d, hwd⟩) (fun h => hbu (congrArg Subtype.val h).symm)
      (fun h => hdv (congrArg Subtype.val h).symm)
    obtain ⟨σ, hσ⟩ := p.2
    refine ⟨σ, MulAction.mem_stabilizer_iff.mp σ.2, ?_⟩
    have hp1' : (p.1 : Equiv.Perm {x : c.Γ // c.graph.Adj w x}) ⟨u, hwu⟩ = ⟨v, hwv⟩ := by
      simpa [Subgroup.smul_def] using hp1
    have h := congrArg (fun e : Equiv.Perm {x : c.Γ // c.graph.Adj w x} =>
      (e ⟨u, hwu⟩).1) hσ
    rw [localPermHom_apply] at h
    rw [hp1'] at h
    simpa using h
  ·
    have hg4 : (4 : ℕ∞) < c.graph.egirth :=
      lt_trans (by norm_num) hg
    exact fun z => fixingSubgroup_le_stabilizer_of_twinFree (H := c.G0) (Γ := c.graph)
      (twinFree_of_egirth (Γ := c.graph) hg4 hdeg) z
  ·
    intro v w hvw
    have hnot : ¬ ((∃ g : c.G0, g • c.xv = v) ∧ ∃ g : c.G0, g • c.xv = w) := by
      rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      exact CosetGeom.vtype_ne_of_adj hvw
        (by rw [CosetGeom.vtype_smul, CosetGeom.vtype_smul])
    have hsome : (∃ g : c.G0, g • c.xv = v) ∨ ∃ g : c.G0, g • c.xv = w := by
      obtain (⟨a, ha⟩ | ⟨a, ha⟩) := exists_smul_eq_xv_or_lv (c := c) v
      · exact Or.inl ⟨a, ha⟩
      · obtain (⟨b, hb⟩ | ⟨b, hb⟩) := exists_smul_eq_xv_or_lv (c := c) w
        · exact Or.inr ⟨b, hb⟩
        · exfalso
          exact CosetGeom.vtype_ne_of_adj hvw
            (by rw [← ha, ← hb, CosetGeom.vtype_smul, CosetGeom.vtype_smul])
    constructor
    · rintro hv hw
      exact hnot ⟨hv, hw⟩
    · intro hw
      rcases hsome with hv | hw'
      · exact hv
      · exact absurd hw' hw
  ·
    intro v w hvw
    by_cases hv : (fun v => ∃ g : c.G0, g • c.xv = v) v
    · obtain ⟨b, hb⟩ := hvw.mp hv
      obtain ⟨a, ha⟩ := hv
      refine ⟨b * a⁻¹, ?_⟩
      rw [mul_smul, ← ha, inv_smul_smul, hb]
    · have hw : ¬ (fun v => ∃ g : c.G0, g • c.xv = v) w := fun h => hv (hvw.mpr h)
      obtain (⟨a, ha⟩ | ⟨a, ha⟩) := exists_smul_eq_xv_or_lv (c := c) v
      · exact absurd ⟨a, ha⟩ hv
      · obtain (⟨b, hb⟩ | ⟨b, hb⟩) := exists_smul_eq_xv_or_lv (c := c) w
        · exact absurd ⟨b, hb⟩ hw
        · refine ⟨b * a⁻¹, ?_⟩
          rw [mul_smul, ← ha, inv_smul_smul, hb]
  ·
    intro v hv
    obtain ⟨g, hg⟩ := hv
    rw [← hg]
    exact (isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g).1
  ·
    intro v hv
    obtain (⟨g, hg⟩ | ⟨g, hg⟩) := exists_smul_eq_xv_or_lv (c := c) v
    · exact absurd ⟨g, hg⟩ hv
    · rw [← hg]
      exact (isLocal_of_polygon4 c hc hM hW F hk hm hF hU3 hL2 hV1 hV2 g).2

theorem weissLemma4'_of_polygon4
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (hc : c.IsFaithful)
    (hM : MoufangCondition c.G0 c.graph 4) (hW : WeissFree c.G0 c.graph 4)
    (hg : ((2 * 4 + 2 : ℕ) : ℕ∞) < c.graph.egirth)
    {k m : ℕ} (F : Type) [Field F] [Finite F] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hV1 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1)
    (hV2 : ∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) :
    WeissLemma4' c.G0 c.graph 4 :=
  QuadSetup.weissLemma4' hk hm hF
    (quadSetup_of_polygon4 c hc hM hW hg F hk hm hF hU3 hL2 hV1 hV2)

end CFSG.Quasithin.Stroth.WeissDelta

end
