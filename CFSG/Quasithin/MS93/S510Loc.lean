module

public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem mem_stabCenter_iff {δ : Vtx X} {z : X.Universal} :
    z ∈ stabCenter X δ ↔ z ∈ stab X δ ∧ ∀ y ∈ stab X δ, y * z = z * y := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hc y y.2), rfl⟩

theorem stabCenter_smul (g : X.Universal) (δ : Vtx X) :
    stabCenter X (g • δ) = (stabCenter X δ).map (MulAut.conj g).toMonoidHom := by
  ext z
  rw [mem_map_conj, mem_stabCenter_iff, mem_stabCenter_iff, mem_stab_smul]
  refine and_congr_right fun _ => ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H (g * y * g⁻¹) (by rw [mem_stab_smul]; simpa [mul_assoc] using hy)
    calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * z * g * y := by group
  · have := H (g⁻¹ * y * g) ((mem_stab_smul X).1 hy)
    calc y * z = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = z * y := by group

theorem commute_of_mem_stabCenter {δ : Vtx X} {z y : X.Universal} (hz : z ∈ stabCenter X δ)
    (hy : y ∈ stab X δ) : y * z = z * y :=
  (mem_stabCenter_iff.1 hz).2 y hy

end General

section Case

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def LineCase (h : PUHyp M T L) (q : ℕ) (a : ↥M →* ↥(StatedSp 2 F)) : Prop :=
  ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
    Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
    S5.jOff h.le L q (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)

omit [Fintype F] in
theorem exists_case56_iff (h : PUHyp M T L) (q : ℕ) (a : ↥M →* ↥(StatedSp 2 F))
    (δ : Vtx (puAmalgam h.le)) :
    (∃ l, S5.Case56 h q a δ l) ↔
      S5.jOff h.le L q δ (baseB _) = S5.jOff h.le L q (baseA _) (baseB _) ∧ LineCase h q a := by
  constructor
  · rintro ⟨l, hJ, hl, hT, hJl⟩
    exact ⟨hJ, l, hl, hT, hJl⟩
  · rintro ⟨hJ, l, hl, hT, hJl⟩
    exact ⟨l, hJ, hl, hT, hJl⟩

omit [Fintype F] in
theorem lam55_facts (h : PUHyp M T L) {q : ℕ} {α' δ μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hcase : ∀ l, ¬ S5.Case56 h q a δ l) (hμ : μ ∈ S5.lam h q a α' δ) :
    ∃ ν, (puAmalgam h.le).treeGraph.Adj (baseA _) ν ∧ (puAmalgam h.le).treeGraph.Adj ν μ ∧
      (∃ t ∈ stab _ (baseA (puAmalgam h.le)), t • baseB _ = ν ∧ t • δ = μ) ∧
      Qv _ ν ⊔ ZM _ α' = stab _ (baseA (puAmalgam h.le)) ∧
      ZH _ (baseB _) ⊓ Subgroup.centralizer
          (S5.jOff h.le L q (baseA _) ν : Set (puAmalgam h.le).Universal) ≤
        stabCenter _ (baseA (puAmalgam h.le)) ∧
      (puTrans h.le L (baseA _) ≤ S5.jOff h.le L q μ ν ⊔ S5.zHat _ (baseA _) α' ∨
        (Qv _ (baseA (puAmalgam h.le)) ≤ S5.jOff h.le L q δ (baseB _) ∧
          (Qv _ (baseA (puAmalgam h.le))).relIndex
              (S5.jOff h.le L q δ (baseB _) ⊓ S5.jOff h.le L q (baseA _) (baseB _)) ≤ q ^ 2 ∧
          XM _ (baseA (puAmalgam h.le)) ≠
            S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓
              Subgroup.centralizer
                (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal))) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hZ'st, -, -, -, -, -⟩ := S5B.crit_facts h hc
  obtain ⟨g, x, hg, hx, hconc, hμeq⟩ := hμ
  have hconc55 : S5.Concl55 h q α' δ g x := by
    rcases hconc with ⟨-, hc55⟩ | ⟨l, hl, -⟩
    · exact hc55
    · exact absurd hl (hcase l)
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hc⟩ := hconc55
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  have hxα : x⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hxst)
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hgα] at this
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (g⁻¹ • baseB (puAmalgam h.le)) (g⁻¹ • δ) :=
    (adj_smul _ g⁻¹ _ _).2 hβδ
  have hle1 : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ hadj1.symm
  have hZhZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ ZM _ α' := inf_le_left
  have hJx : ∀ ρ, S5.jOff h.le L q (x⁻¹ • ρ) (x⁻¹ • (g⁻¹ • baseB (puAmalgam h.le))) =
      S5.rconj x (S5.jOff h.le L q ρ (g⁻¹ • baseB (puAmalgam h.le))) := by
    intro ρ
    rw [S5B.jOff_smul h.le hLn, S5.rconj]
  rcases hμeq with rfl | rfl
  · refine ⟨g⁻¹ • baseB _, hadj1, hadj2, ⟨g⁻¹, inv_mem hg, rfl, rfl⟩, ?_, hb1, ?_⟩
    · refine le_antisymm (sup_le hle1 hZ'st) ?_
      rw [← ha1]
      exact sup_le_sup_left hZhZ _
    · rcases hc with hc | hc
      · exact Or.inl (hc.trans inf_le_left)
      · exact Or.inr hc
  · have hadj1' : (puAmalgam h.le).treeGraph.Adj (baseA _)
        (x⁻¹ • (g⁻¹ • baseB (puAmalgam h.le))) := by
      have := (adj_smul _ x⁻¹ _ _).2 hadj1
      rwa [hxα] at this
    have hqv : Qv _ (x⁻¹ • (g⁻¹ • baseB (puAmalgam h.le))) =
        S5.rconj x (Qv _ (g⁻¹ • baseB (puAmalgam h.le))) := by
      rw [qv_smul, S5.rconj]
    refine ⟨x⁻¹ • (g⁻¹ • baseB _), hadj1', (adj_smul _ x⁻¹ _ _).2 hadj2,
      ⟨x⁻¹ * g⁻¹, mul_mem (inv_mem hxst) (inv_mem hg), by rw [mul_smul], by rw [mul_smul]⟩,
      ?_, ?_, ?_⟩
    · rw [hqv]
      exact ha2
    · have := hJx (baseA _)
      rw [hxα] at this
      rw [this]
      exact hb2
    · rcases hc with hc | hc
      · left
        rw [hJx]
        exact hc.trans inf_le_right
      · exact Or.inr hc

omit [Fintype F] in
theorem loc55 (h : PUHyp M T L) {q : ℕ} {γ γ' ε δ μ : Vtx (puAmalgam h.le)}
    {c : (puAmalgam h.le).Universal} (hc : IsCritical _ γ γ') (hγ : γ = c • baseA _)
    (hε : ε = c • baseB _) (hεδ : (puAmalgam h.le).treeGraph.Adj ε δ)
    (hcase : S5.jOff h.le L q δ ε ≠ S5.jOff h.le L q γ ε ∨ ¬ LineCase h q a)
    (hμ : c⁻¹ • μ ∈ S5.lam h q a (c⁻¹ • γ') (c⁻¹ • δ)) :
    ∃ ν, (puAmalgam h.le).treeGraph.Adj γ ν ∧ (puAmalgam h.le).treeGraph.Adj ν μ ∧
      (∃ t ∈ stab _ γ, t • ε = ν ∧ t • δ = μ) ∧
      Qv _ ν ⊔ ZM _ γ' = stab _ γ ∧
      ZH _ ε ⊓ Subgroup.centralizer
          (S5.jOff h.le L q γ ν : Set (puAmalgam h.le).Universal) ≤ stabCenter _ γ ∧
      (puTrans h.le L γ ≤ S5.jOff h.le L q μ ν ⊔ S5.zHat _ γ γ' ∨
        (Qv _ γ ≤ S5.jOff h.le L q δ ε ∧
          (Qv _ γ).relIndex (S5.jOff h.le L q δ ε ⊓ S5.jOff h.le L q γ ε) ≤ q ^ 2 ∧
          XM _ γ ≠ S5.uSub h.le L γ ⊔ XM _ γ ⊓
            Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal))) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  subst hγ hε
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (c⁻¹ • γ') := by
    have := (isCritical_smul _ c⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (c⁻¹ • δ) := by
    have := (adj_smul _ c⁻¹ _ _).2 hεδ
    rwa [inv_smul_smul] at this
  have hcase' : ∀ l, ¬ S5.Case56 h q a (c⁻¹ • δ) l := by
    intro l hl
    obtain ⟨hJ, hLC⟩ := (exists_case56_iff h q a _).1 ⟨l, hl⟩
    rcases hcase with hne | hnl
    · apply hne
      have e1 : δ = c • (c⁻¹ • δ) := (smul_inv_smul c δ).symm
      rw [e1, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn, hJ]
    · exact hnl hLC
  obtain ⟨ν₀, hαν, hνμ, ⟨t₀, ht₀, htβ, htδ⟩, hgen, hcen, hL⟩ :=
    lam55_facts h hc' hβδ hcase' hμ
  have eμ : μ = c • (c⁻¹ • μ) := (smul_inv_smul c μ).symm
  have eγ' : γ' = c • (c⁻¹ • γ') := (smul_inv_smul c γ').symm
  have eδ : δ = c • (c⁻¹ • δ) := (smul_inv_smul c δ).symm
  refine ⟨c • ν₀, (adj_smul _ c _ _).2 hαν, by rw [eμ]; exact (adj_smul _ c _ _).2 hνμ,
    ⟨c * t₀ * c⁻¹, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [mem_stab_smul]
    simpa [mul_assoc] using ht₀
  · rw [mul_smul, mul_smul, inv_smul_smul, htβ]
  · rw [mul_smul, mul_smul, htδ, ← eμ]
  · rw [eγ', qv_smul, zm_smul, stab_smul, ← Subgroup.map_sup, hgen]
  · rw [zh_smul, S5B.jOff_smul h.le hLn, PU.centralizer_map_mulEquiv,
      ← Subgroup.map_inf _ _ _ (MulAut.conj c).injective, stabCenter_smul,
      map_conj_le_map_conj_iff]
    exact hcen
  · rcases hL with hL | ⟨h1, h2, h3⟩
    · left
      rw [eμ, eγ', puTrans_smul h.le hLn, S5B.jOff_smul h.le hLn, S5B.zHat_smul,
        ← Subgroup.map_sup, map_conj_le_map_conj_iff]
      exact hL
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [eδ, qv_smul, S5B.jOff_smul h.le hLn, map_conj_le_map_conj_iff]
        exact h1
      · rw [eδ, qv_smul, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn,
          ← Subgroup.map_inf _ _ _ (MulAut.conj c).injective,
          Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]
        exact h2
      · intro he
        apply h3
        rw [xm_smul, S5B.uSub_smul h.le hLn, puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv,
          ← Subgroup.map_inf _ _ _ (MulAut.conj c).injective, ← Subgroup.map_sup] at he
        exact Subgroup.map_injective (MulAut.conj c).injective he

end Case

end S510

end CFSG.Quasithin.MS93
