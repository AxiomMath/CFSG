module

public import CFSG.Quasithin.MS93.S5DBase
public import CFSG.Quasithin.MS93.S5CMain

public section

namespace CFSG.Quasithin.MS93.S5D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Transv

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commute_of_vec_fixed (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (nv : S5.NatVec M T L a) {y m : G} (hyU : y ∈ Uq M T L) (hm : m ∈ M)
    (hfix : MSP.mat (a ⟨m, hm⟩) *ᵥ nv.vec ⟨y, hyU⟩ = nv.vec ⟨y, hyU⟩) : m * y = y * m := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hmy : m * y * m⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hm) y).1 hyU
  have hvec := nv.vec_conj ⟨m, hm⟩ ⟨y, hyU⟩ hmy
  have h0 : m * y * m⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have : nv.vec (⟨m * y * m⁻¹, hmy⟩ * (⟨y, hyU⟩ : ↥(Uq M T L))⁻¹) = 0 := by
      rw [nv.vec_mul, nv.vec_inv, hvec, hfix, add_neg_cancel]
    exact (nv.vec_eq_zero_iff _).1 this
  have := hlift m hm y hyU h0
  calc m * y = m * y * m⁻¹ * m := by group
    _ = y * m := by rw [this]

theorem exists_xPoint_sup_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E Q : Subgroup G} (hET : E ≤ T) (hEQ : E ≤ Q) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2)
    (hEc : 2 ≤ Nat.card (S5.imSp a E))
    (hRT : ¬ ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (T : Set G)) :
    ∃ s s' : Submodule F (MSP.V4 F), MSP.IsPoint s ∧ MSP.IsPoint s' ∧ s ≠ s' ∧
      MSP.xPoint s ⊔ MSP.xPoint s' ≤ S5.imSp a Q := by
  have := hd.charP
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hEM : E ≤ M := hET.trans h.le
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨s, hs, hcomm, -, hEs⟩ :=
    S510.exists_point_of_relIndex h hd hEM (by rw [pow_one]; exact hrel)
  obtain ⟨t, htT, hts⟩ : ∃ t : ↥M, (t : G) ∈ T ∧
      s.map (Matrix.mulVecLin (MSP.mat (a t))) ≠ s := by
    by_contra hno
    push Not at hno
    apply hRT
    have hT2 : IsPGroup 2 ↥(S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
    have hinv : ∀ r ∈ S5.imSp a T, ∀ w ∈ s, MSP.mat r *ᵥ w ∈ s := by
      rintro _ ⟨t, ht, rfl⟩ w hw
      rw [← hno t (Subgroup.mem_subgroupOf.1 ht)]
      exact Submodule.mem_map_of_mem hw
    have hs0 : s ≠ ⊥ := by
      rintro rfl
      have := hs
      unfold MSP.IsPoint at this
      rw [finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨w, hws, hw0, hwfix⟩ := MSP.exists_fixed_ne_zero hT2 hs0 hinv
    have hall : ∀ v ∈ s, ∀ r ∈ S5.imSp a T, MSP.mat r *ᵥ v = v := by
      obtain ⟨x, -, rfl⟩ := MSP.exists_eq_span_of_isPoint hs
      intro v hv r hr
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      obtain ⟨d, hd'⟩ := Submodule.mem_span_singleton.1 hws
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hd'
        exact hw0 hd'.symm
      have h1 := hwfix r hr
      rw [← hd', Matrix.mulVec_smul] at h1
      have h2 : MSP.mat r *ᵥ x = x := smul_right_injective _ hd0 h1
      rw [Matrix.mulVec_smul, h2]
    intro y hy
    have hyU : y ∈ Uq M T L := commutator_le_left_of_le_normalizer (hEM.trans hUn) hy
    have hvy := (S511S.commSp_le_iff_vec h nv hEM).1 le_rfl ⟨y, hyU⟩ hy
    rw [show MSP.commSp (S5.imSp a E) = s from hcomm] at hvy
    rw [Subgroup.mem_centralizer_iff]
    intro t' ht'
    exact commute_of_vec_fixed h hd nv hyU (h.le ht')
      (hall _ hvy _ ⟨⟨t', h.le ht'⟩, Subgroup.mem_subgroupOf.2 ht', rfl⟩)
  set s' := s.map (Matrix.mulVecLin (MSP.mat (a t))) with hs'
  obtain ⟨xs, hxs, rfl⟩ := MSP.exists_eq_span_of_isPoint hs
  have hs'eq : s' = F ∙ (MSP.mat (a t) *ᵥ xs) := map_span_mat (a t) xs
  have hs'p : MSP.IsPoint s' := hs'eq ▸ MSP.isPoint_span (mat_mulVec_ne_zero (a t) hxs)
  have hEa : S5.imSp a E = MSP.xPoint (F ∙ xs) :=
    Subgroup.eq_of_le_of_card_ge hEs (by rw [MSP.card_xPoint hs, hNF]; exact hEc)
  refine ⟨F ∙ xs, s', hs, hs'p, fun he => hts he.symm, sup_le ?_ ?_⟩
  · rw [← hEa]
    exact S5.imSp_mono a hEQ
  · rw [hs', ← MSP.xPoint_map_conj, ← hEa]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨t * e * t⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have heQ : (e : G) ∈ Q := hEQ (Subgroup.mem_subgroupOf.1 he)
      exact (Subgroup.mem_normalizer_iff.1 (hTQ htT) e).1 heQ
    · simp [map_mul, map_inv, MulAut.conj_apply]

theorem exists_xPoint_sup_le_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (g : (puAmalgam h.le).Universal) {E Q : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (g • baseB (puAmalgam h.le))) (hQ : Q ≤ Qv _ (g • baseB (puAmalgam h.le)))
    (hEQ : E ≤ Q)
    (hTQ : Qv _ (g • baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (Q : Set (puAmalgam h.le).Universal))
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (g • baseA (puAmalgam h.le))) = 2)
    (hEc : 2 ≤ (Qv _ (g • baseA (puAmalgam h.le))).relIndex E)
    (hRT : ¬ ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), E⁆ ≤
      Subgroup.centralizer (Qv _ (g • baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) :
    ∃ s s' : Submodule F (MSP.V4 F), MSP.IsPoint s ∧ MSP.IsPoint s' ∧ s ≠ s' ∧
      MSP.xPoint s ⊔ MSP.xPoint s' ≤ S5.vIm h.le a (Q.map (MulAut.conj g⁻¹).toMonoidHom) := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  have hQQ : Q = (Q.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv Q g).symm
  rw [hEE, hQQ] at hEQ
  rw [hEE] at hE hrel hEc hRT
  rw [hQQ] at hQ hTQ
  rw [PU.qv_smul, map_conj_le_map_conj_iff, puAmalgam.qv_baseB] at hE hQ
  obtain ⟨E₀, hE₀T, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hE
  obtain ⟨Q₀, hQ₀T, hQ₀M, hQ₀⟩ := S5B.exists_eq_imM h.le hQ
  rw [hE₀] at hrel hEc hRT hEQ
  rw [hQ₀] at hTQ hEQ ⊢
  rw [map_conj_le_map_conj_iff, imM_le_imM_iff h.le hE₀M] at hEQ
  have hTT : ((imM h.le T).map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
      imM h.le T := by
    have := map_conj_map_conj_inv (imM h.le T) g⁻¹
    rwa [inv_inv] at this
  rw [puAmalgam.qv_smul_baseB, le_normalizer_map_conj_iff, hTT] at hTQ
  have hTQ₀ := S5C.le_normalizer_of_imM h.le h.le hQ₀M hTQ
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hUM hE₀M] at hrel
  rw [PU.qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hE₀M, ← hd.card_imSp h hE₀T] at hEc
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator,
    puAmalgam.qv_smul_baseB, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
    ← imM_commutator h.le hUM hE₀M] at hRT
  have hRT₀ : ¬ ⁅Uq M T L, E₀⁆ ≤ Subgroup.centralizer (T : Set G) := by
    intro hle
    apply hRT
    have h1 : imM h.le ⁅Uq M T L, E₀⁆ ≤
        imM h.le (⁅Uq M T L, E₀⁆ ⊓ Subgroup.centralizer (T : Set G)) :=
      imM_mono h.le (le_inf le_rfl hle)
    rw [imM_inf_centralizer h.le _ h.le] at h1
    exact h1.trans inf_le_right
  rw [S5.vIm_imM h]
  exact exists_xPoint_sup_le h hd hE₀T hEQ hTQ₀ hrel hEc hRT₀

end Transv

namespace IsChain

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
  {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem false_of_two (h32 : S32) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M ≠ Uq M T L ⊔ Zq M L) (hch : S510.IsChain h (2 ^ 1) a s t N)
    (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
      S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)))
    (hlc : S510.LineCase h (2 ^ 1) a) {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 2 ≤ N)
    (hQJ : Qv _ (geo _ s t (2 * i)) ≤
      S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)))
    (hidx : (Qv _ (geo _ s t (2 * i))).relIndex
      (S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)) ⊓
        S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1))) ≤ (2 ^ 1) ^ 2)
    (hQJ' : Qv _ (geo _ s t (2 * i + 2)) ≤
      S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1))) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hdd := hch.dist_eq
  have hLn := h.L_subgroupOf_normal
  have hcase' : ∀ j ≤ N,
      S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ 1) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ S510.LineCase h (2 ^ 1) a := fun j hj => Or.inl (hcase j hj)
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  obtain ⟨l, hl, hTl, hJl⟩ := hlc
  have hγ2M : IsMVtx _ (P (2 * i + 2)) := by
    have := hch.isMVtx_P (j := i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hεγ2 : (puAmalgam h.le).treeGraph.Adj (P (2 * i + 1)) (P (2 * i + 2)) :=
    hch.adj_P (i := 2 * i + 1) (by omega)
  have hcr := hch.crit i (by omega)
  have hγ'M : IsMVtx _ (P (2 * i + b)) := hcr.isMVtx_right _ hyp
  obtain ⟨g, hg0, hg1, -⟩ := hch.lam i hi1 (by omega)
  rw [← hP] at hg0 hg1
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le)) (g⁻¹ • P (2 * i + 2)) := by
    have := (adj_smul _ g⁻¹ _ _).mpr hεγ2
    rwa [hg1, inv_smul_smul] at this
  obtain ⟨x, hx, hxδ⟩ := exists_mem_stab_smul _ (adj_baseA_baseB _).symm hβδ
  have eγ2 : P (2 * i + 2) = g • (x • baseA (puAmalgam h.le)) := by rw [hxδ, smul_inv_smul]
  have hJγ : S5.jOff h.le L (2 ^ 1) (P (2 * i)) (P (2 * i + 1)) =
      (S5.jOff h.le L (2 ^ 1) (baseA _) (baseB _)).map (MulAut.conj g).toMonoidHom := by
    rw [hg0, hg1, S5B.jOff_smul h.le hLn]
  have hJγ2 : S5.jOff h.le L (2 ^ 1) (P (2 * i + 2)) (P (2 * i + 1)) =
      (S5.jOff h.le L (2 ^ 1) (x • baseA _) (baseB _)).map (MulAut.conj g).toMonoidHom := by
    rw [eγ2, hg1, S5B.jOff_smul h.le hLn]
  have hQγ : Qv _ (P (2 * i)) = (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom :=
    by rw [hg0, PU.qv_smul]
  have hQγ2 : Qv _ (P (2 * i + 2)) =
      (Qv _ (x • baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom := by
    rw [eγ2, PU.qv_smul]
  have hQα : Qv _ (baseA (puAmalgam h.le)) ≤ S5.jOff h.le L 2 (x • baseA _) (baseB _) := by
    have := hQJ
    rw [hQγ, hJγ2, map_conj_le_map_conj_iff] at this
    exact this
  have hQδ : Qv _ (x • baseA (puAmalgam h.le)) ≤ S5.jOff h.le L 2 (baseA _) (baseB _) := by
    have := hQJ'
    rw [hQγ2, hJγ, map_conj_le_map_conj_iff] at this
    exact this
  have hidx' : (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L 2 (x • baseA _) (baseB _) ⊓ S5.jOff h.le L 2 (baseA _) (baseB _)) ≤ 4 := by
    have := hidx
    rw [hQγ, hJγ2, hJγ, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at this
    exact this
  have hcase0 : S5.jOff h.le L 2 (x • baseA _) (baseB _) ≠
      S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
    intro heq
    apply hcase i (by omega)
    rw [hJγ2, hJγ]
    exact congrArg (fun K => K.map (MulAut.conj g).toMonoidHom) heq
  have hE : ZM _ (P (2 * i + b)) ≤ Qv _ (g • baseB (puAmalgam h.le)) := by
    rw [← hg1]
    refine zm_le_qv_of_dist_lt _ hγ'M ?_
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hQ : Qv _ (P (2 * i + 2)) ≤ Qv _ (g • baseB (puAmalgam h.le)) := by
    rw [← hg1]
    exact qv_le_qv _ hyp hγ2M hεγ2.symm
  have hEQ : ZM _ (P (2 * i + b)) ≤ Qv _ (P (2 * i + 2)) := by
    refine zm_le_qv_of_dist_lt _ hγ'M ?_
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hTQ : Qv _ (g • baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (Qv _ (P (2 * i + 2)) : Set (puAmalgam h.le).Universal) := by
    rw [← hg1]
    exact (qv_le_stab_of_adj _ hεγ2).trans (stab_le_normalizer_qv _ _)
  have hrel : (Subgroup.centralizer (ZM _ (P (2 * i + b)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (g • baseA (puAmalgam h.le))) =
      2 := by
    rw [← hg0]
    have := hch.partA hd hb hcase' (j := i) (by omega)
    rwa [pow_one] at this
  have hEc : 2 ≤ (Qv _ (g • baseA (puAmalgam h.le))).relIndex (ZM _ (P (2 * i + b))) := by
    rw [← hg0]
    have := S511S.le_relIndex_zm_gp h hd (ms22_iii _ hyp hb0 h.centHyp hcr)
    rwa [pow_one] at this
  have hRT : ¬ ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), ZM _ (P (2 * i + b))⁆ ≤
      Subgroup.centralizer (Qv _ (g • baseB (puAmalgam h.le)) :
        Set (puAmalgam h.le).Universal) := by
    rw [← hg0, ← hg1]
    intro hle
    have hp2 := hch.p2 hb hcase' (j := i) (by omega)
    exact S511.critR_not_le_stabCenter h hd hcr
      ((S510S2.critR_le_commutator_uSub_gp h (by omega) hcr).trans ((le_inf le_rfl hle).trans hp2))
  obtain ⟨σ, σ', hσ, hσ', hσσ, hX⟩ := exists_xPoint_sup_le_gp h hd g hE hQ hEQ hTQ hrel hEc hRT
  have hQmap : (Qv _ (P (2 * i + 2))).map (MulAut.conj g⁻¹).toMonoidHom =
      Qv _ (x • baseA (puAmalgam h.le)) := by
    rw [hQγ2]
    have := map_conj_map_conj_inv (Qv _ (x • baseA (puAmalgam h.le))) g⁻¹
    rwa [inv_inv] at this
  rw [hQmap] at hX
  exact false_of_base h (by omega) hd (h32 G M T L h).2.1 hXU hl hTl hJl hx hQα hQδ hidx' hcase0
    hσ hσ' hσσ hX

end IsChain

theorem cruxNXZ2_holds (h32 : S32) : S5C.CruxNXZ2 := by
  intro G _ _ M T L h _ hb k F _ _ a hk hd hXU hlc _ α' _ _ N s _ hch hcase h2 h3 i hi1 hiN
  subst hk
  exact (IsChain.false_of_two h32 hd hXU hch hb hcase hlc hi1 (by omega)
    (h2 i hi1 (by omega)).2.1 (h2 i hi1 (by omega)).2.2 (h3 i hi1 (by omega)).1).elim

theorem s510NXZ'_holds (h32 : S32) : S5B.S510NXZ' :=
  S5C.s510NXZ'_of_cruxNXZ2 h32 (cruxNXZ2_holds h32)

end CFSG.Quasithin.MS93.S5D
