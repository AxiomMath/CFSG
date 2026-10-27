module

public import CFSG.Quasithin.MS93.S5A55Lift
public import CFSG.Quasithin.MS93.S5BAux

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5

section Sp

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem finrank_fixSp_eq_one_of_not_isCandSp {R D : Subgroup (MSP.Sp4 F)} (hR : IsPGroup 2 R)
    (hDR : D ≤ R) (hDc : Nat.card F ^ 2 ≤ Nat.card D) (hD : ¬ IsCandSp R D) :
    Module.finrank F (MSP.fixSp D) = 1 := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hD2 : IsPGroup 2 D := hR.to_le hDR
  have hDne : D ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hDc
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have h1 : 1 ≤ Module.finrank F (MSP.fixSp D) := by
    obtain ⟨w, -, hw0, hw⟩ := MSP.exists_fixed_ne_zero hD2 (W := ⊤) top_ne_bot
      (fun _ _ _ _ => Submodule.mem_top)
    have hmem : w ∈ MSP.fixSp D := fun r hr => hw r hr
    have hne : MSP.fixSp D ≠ ⊥ := fun h0 => hw0 (by rw [h0] at hmem; exact hmem)
    exact Nat.one_le_iff_ne_zero.2 fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  have h4 : Module.finrank F (MSP.fixSp D) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp D)
    simpa using this
  by_contra hne1
  rcases (show Module.finrank F (MSP.fixSp D) = 2 ∨ Module.finrank F (MSP.fixSp D) = 3 ∨
      Module.finrank F (MSP.fixSp D) = 4 by omega) with h2 | h3 | h4'
  ·
    obtain ⟨-, -⟩ := MSP.isLine_fixSp_of_finrank_two hD2 h2
    apply hD
    have hV : Nat.card (MSP.V4 F) = Nat.card F ^ 4 := MSP.card_V4
    have hfix : Nat.card (MSP.fixSp D) = Nat.card F ^ 2 := by rw [MSP.card_fixSp, h2]
    refine ⟨hDR, ?_, ?_⟩
    · rw [hV, hfix]
      calc Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
        _ ≤ Nat.card F ^ 2 * Nat.card D := Nat.mul_le_mul_left _ hDc
    · rw [hV, hfix]
      ring_nf
      exact le_rfl
  ·
    obtain ⟨p, hp, -, hDp⟩ := MSP.exists_point_of_finrank_fixSp_three h3
    have hc := Subgroup.card_le_of_le hDp
    rw [MSP.card_xPoint hp] at hc
    have : Nat.card F < Nat.card F ^ 2 := by
      calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
        _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq1 (by norm_num)
    omega
  ·
    have htop : MSP.fixSp D = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4']; simp)
    exact hDne (MSP.fixSp_eq_top_iff.1 htop)

end Sp

section CaseA

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem exists_jOff_eq_map (q : ℕ) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    ∃ y ∈ stab (puAmalgam h.le) (baseB _), jOff h.le L q δ (baseB _) =
      (jOff h.le L q (baseA (puAmalgam h.le)) (baseB _)).map (MulAut.conj y).toMonoidHom := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨y, hy, hyα⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
  refine ⟨y, hy, ?_⟩
  rw [← jOff_smul h.le hLn, hyα, (mem_stab _).1 hy]

theorem finite_of_le_stab_baseA {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ stab (puAmalgam h.le) (baseA _)) : Finite ↥K := by
  have := finite_stab_baseA h
  exact Finite.of_injective _ (Subgroup.inclusion_injective hK)

theorem jOff_le_stab_baseA (q : ℕ) (δ : Vtx (puAmalgam h.le)) :
    jOff h.le L q δ (baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
  (iSup₂_le fun _ hE => hE.1.1).trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)

theorem relIndex_jOff_le {q : ℕ} (hq : 1 ≤ q) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex (jOff h.le L q (baseA _) (baseB _)) ≤
      (Qv _ (baseA (puAmalgam h.le))).relIndex (jOff h.le L q δ (baseB _)) ∧
    ((Qv _ (baseA (puAmalgam h.le))).relIndex (jOff h.le L q δ (baseB _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (jOff h.le L q (baseA _) (baseB _)) →
      Qv _ (baseA (puAmalgam h.le)) ≤ jOff h.le L q δ (baseB _)) := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hQJ := S5B.qv_le_jOff (L := L) h hq hα (adj_baseA_baseB (puAmalgam h.le))
  obtain ⟨y, -, hJδ⟩ := exists_jOff_eq_map h q hβδ
  set Q := Qv (puAmalgam h.le) (baseA (puAmalgam h.le))
  set Jα := jOff h.le L q (baseA (puAmalgam h.le)) (baseB _)
  set Jδ := jOff h.le L q δ (baseB (puAmalgam h.le))
  have : Finite ↥Q := finite_of_le_stab_baseA h (qv_le_stab _ _)
  have : Finite ↥Jα := finite_of_le_stab_baseA h (jOff_le_stab_baseA h q _)
  have hcard : Nat.card Jδ = Nat.card Jα := by rw [hJδ, card_map_conj]
  have e1 := Subgroup.relIndex_mul_card Q Jα
  have e2 := Subgroup.relIndex_mul_card Q Jδ
  rw [inf_of_le_left hQJ] at e1
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hle : Nat.card ↥(Q ⊓ Jδ) ≤ Nat.card Q := Subgroup.card_le_of_le inf_le_left
  have key : Q.relIndex Jα * Nat.card Q = Q.relIndex Jδ * Nat.card ↥(Q ⊓ Jδ) := by
    rw [e1, e2, hcard]
  refine ⟨?_, fun heq => ?_⟩
  · by_contra hlt
    push Not at hlt
    have : Q.relIndex Jδ * Nat.card ↥(Q ⊓ Jδ) < Q.relIndex Jα * Nat.card Q :=
      Nat.mul_lt_mul_of_lt_of_le hlt hle hQpos
    omega
  · rw [heq] at key
    have hpos : 0 < Q.relIndex Jα := Nat.pos_of_ne_zero (by
      intro h0
      rw [h0, zero_mul] at e1
      exact (Nat.card_pos (α := Jα)).ne' e1.symm)
    have hc : Nat.card ↥(Q ⊓ Jδ) = Nat.card Q := (Nat.eq_of_mul_eq_mul_left hpos key).symm
    have : Q ⊓ Jδ = Q := Subgroup.eq_of_le_of_card_ge inf_le_left hc.ge
    exact inf_eq_left.1 this

omit [Fintype F] in
theorem vIm_jOff_baseA {A₀ : Subgroup ↥(StatedSp 2 F)}
    (hA₀T : A₀ ≤ imSp a T) (hJ : jOffM M T L (2 ^ k) = liftT T a A₀) :
    vIm h.le a (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) = A₀ := by
  rw [jOff_baseA h, vIm_imM h, hJ, imSp_liftT hA₀T]

omit [Fintype F] in
theorem le_normalizer_vIm_jOff (q : ℕ) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    imSp a T ≤ Subgroup.normalizer (vIm h.le a (jOff h.le L q δ (baseB _)) : Set _) := by
  rw [← vIm_imM h, ← puAmalgam.qv_baseB]
  rintro _ ⟨m, hm, rfl⟩
  have hn := qv_le_normalizer_jOff h q hβδ
    (show (puAmalgam h.le).ofA m ∈ Qv (puAmalgam h.le) (baseB _) from hm)
  have he : (jOff h.le L q δ (baseB (puAmalgam h.le))).map
      (MulAut.conj ((puAmalgam h.le).ofA m)).toMonoidHom = jOff h.le L q δ (baseB _) :=
    map_conj_eq_of_mem_normalizer hn
  have he' := congrArg (vIm h.le a) he
  rw [vIm_map_conj] at he'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← he']
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← he'] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : a m * y * (a m)⁻¹ = a m * x * (a m)⁻¹ := hyx
      simpa using h1
    rwa [← this]

omit [Fintype F] in
theorem jOff_le_of_vIm_le {A₀ : Subgroup ↥(StatedSp 2 F)}
    (hJ : jOffM M T L (2 ^ k) = liftT T a A₀) {K : Subgroup (puAmalgam h.le).Universal}
    (hKT : K ≤ Qv _ (baseB (puAmalgam h.le))) (hKA : vIm h.le a K ≤ A₀) :
    K ≤ jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
  rw [jOff_baseA h, hJ]
  intro x hx
  have hxT := hKT hx
  rw [puAmalgam.qv_baseB] at hxT
  obtain ⟨m, hm, rfl⟩ := hxT
  have hmT : (m : G) ∈ T := Subgroup.mem_subgroupOf.1 hm
  have hma : a m ∈ A₀ := hKA ⟨m, hx, rfl⟩
  exact ⟨m, Subgroup.mem_subgroupOf.2 (mem_liftT.2 ⟨hmT, m.2, hma⟩), rfl⟩

omit [Fintype F] in
theorem vIm_jOff_inf_jOff {A₀ : Subgroup ↥(StatedSp 2 F)}
    (hA₀T : A₀ ≤ imSp a T) (hJ : jOffM M T L (2 ^ k) = liftT T a A₀)
    {δ : Vtx (puAmalgam h.le)} :
    vIm h.le a (jOff h.le L (2 ^ k) δ (baseB _) ⊓ jOff h.le L (2 ^ k) (baseA _) (baseB _)) =
      vIm h.le a (jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le))) ⊓ A₀ := by
  apply le_antisymm
  · rw [← vIm_jOff_baseA h hA₀T hJ]
    exact le_inf (vIm_mono' h inf_le_left) (vIm_mono' h inf_le_right)
  · rintro _ ⟨⟨m, hm, rfl⟩, hmA⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    have hKT : jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) ⊓
        (Subgroup.zpowers ((puAmalgam h.le).ofA m)) ≤ Qv _ (baseB _) :=
      inf_le_left.trans (iSup₂_le fun _ hE => hE.1.1)
    have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) :=
      (iSup₂_le fun _ hE => hE.1.1 : jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) ≤
        Qv _ (baseB _)) hm
    rw [puAmalgam.qv_baseB] at hmT
    obtain ⟨m', hm', he⟩ := hmT
    have hmm : m' = m := (puAmalgam h.le).ofA_injective he
    subst hmm
    rw [jOff_baseA h, hJ]
    exact ⟨m', Subgroup.mem_subgroupOf.2
      (mem_liftT.2 ⟨Subgroup.mem_subgroupOf.1 hm', m'.2, hmA⟩), rfl⟩

theorem not_isCandSp_vIm_jOff (hd : IsSp4Data M T L k F a) {A₀ : Subgroup ↥(StatedSp 2 F)}
    (hA : candMax (imSp a T) = {A₀}) (hJ : jOffM M T L (2 ^ k) = liftT T a A₀)
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hne : jOff h.le L (2 ^ k) δ (baseB _) ≠
      jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) :
    ¬ IsCandSp (imSp a T) (vIm h.le a (jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)))) := by
  intro hc
  have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ Set.mem_singleton A₀
  have hA₀T : A₀ ≤ imSp a T := hA₀.1.1
  have hvJ := vIm_jOff_baseA h hA₀T hJ
  obtain ⟨y, -, hJδ⟩ := exists_jOff_eq_map h (2 ^ k) hβδ
  set Jα := jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)
  set Jδ := jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le))
  have hJαst := jOff_le_stab_baseA h (2 ^ k) (baseA (puAmalgam h.le))
  have hJδst := jOff_le_stab_baseA h (2 ^ k) δ
  have hnot : ¬ IsMVtx _ (baseB (puAmalgam h.le)) :=
    (isMVtx_iff_of_adj _ (adj_baseA_baseB _)).1 (isMVtx_baseA _)
  have hJα2 : IsPGroup 2 Jα := (isPGroup_qv _ h.hyp20 hnot).to_le (iSup₂_le fun _ hE => hE.1.1)
  have hJδ2 : IsPGroup 2 Jδ := (isPGroup_qv _ h.hyp20 hnot).to_le (iSup₂_le fun _ hE => hE.1.1)
  have hle := (relIndex_jOff_le h (q := 2 ^ k) Nat.one_le_two_pow hβδ).1
  rw [← card_vIm h hd hJαst hJα2, ← card_vIm h hd hJδst hJδ2, hvJ] at hle
  have hge := hA₀.2 _ hc
  have hmax : vIm h.le a Jδ ∈ candMax (imSp a T) :=
    ⟨hc, fun B hB => (hA₀.2 B hB).trans hle⟩
  rw [hA] at hmax
  have hsub : Jδ ≤ Jα := jOff_le_of_vIm_le h hJ (iSup₂_le fun _ hE => hE.1.1) hmax.le
  have : Finite ↥Jα := finite_of_le_stab_baseA h hJαst
  have hcard : Nat.card Jα ≤ Nat.card Jδ := by rw [hJδ, card_map_conj]
  exact hne (Subgroup.eq_of_le_of_card_ge hsub hcard)

end CaseA

end S5

end CFSG.Quasithin.MS93
