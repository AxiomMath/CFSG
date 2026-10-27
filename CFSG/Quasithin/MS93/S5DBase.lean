module

public import CFSG.Quasithin.MS93.S5DThom
public import CFSG.Quasithin.Recognition.M12AmalAutIso
public import CFSG.Quasithin.MS93.S5DCore

public section

namespace CFSG.Quasithin.MS93.S5D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Transport

variable {G E : Type} [Group G] [Group E]

theorem baum_map_of_injective (f : G →* E) (hf : Function.Injective f) (H : Subgroup G) :
    baum (H.map f) = (baum H).map f := by
  unfold baum
  rw [AmalTransport.thompsonJ_map_of_injective f hf, PU.omegaOneCenterOf_map hf]
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, fun z hz => ?_⟩, rfl⟩
    have := hc (f z) ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact hf this
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hc z hz]

end Transport

section Base

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem thompsonJ_imM (h : PUHyp M T L) :
    thompsonJ (imM h.le T) = imM h.le (thompsonJ T) := by
  have hJ : thompsonJ T = (thompsonJ (T.subgroupOf M)).map M.subtype := by
    have := AmalTransport.thompsonJ_map_of_injective M.subtype M.subtype_injective (T.subgroupOf M)
    rwa [Subgroup.map_subgroupOf_eq_of_le h.le] at this
  rw [imM, imM, AmalTransport.thompsonJ_map_of_injective _ (puAmalgam h.le).ofA_injective, hJ,
    PU.map_subtype_subgroupOf]

theorem baum_imM (h : PUHyp M T L) : baum (imM h.le T) = imM h.le (baum T) := by
  have hB : baum T = (baum (T.subgroupOf M)).map M.subtype := by
    have := baum_map_of_injective M.subtype M.subtype_injective (T.subgroupOf M)
    rwa [Subgroup.map_subgroupOf_eq_of_le h.le] at this
  rw [imM, imM, baum_map_of_injective _ (puAmalgam h.le).ofA_injective, hB,
    PU.map_subtype_subgroupOf]

theorem liftT_imSp_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) {K : Subgroup G}
    (hKT : K ≤ T) (hQK : pCoreOf 2 M ≤ K) : S5.liftT T a (S5.imSp a K) = K := by
  apply le_antisymm
  · intro t ht
    obtain ⟨htT, htM, hta⟩ := S5.mem_liftT.1 ht
    obtain ⟨k, hk, hkM, hka⟩ := S5.mem_imSp.1 hta
    have hkT : k ∈ T := hKT hk
    have hker : k⁻¹ * t ∈ T ⊓ S5.kerG a := by
      refine ⟨T.mul_mem (T.inv_mem hkT) htT, (S5.mem_kerG a).2 ⟨M.mul_mem (M.inv_mem hkM) htM, ?_⟩⟩
      have : a ⟨k⁻¹ * t, M.mul_mem (M.inv_mem hkM) htM⟩ = (a ⟨k, hkM⟩)⁻¹ * a ⟨t, htM⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [this, hka, inv_mul_cancel]
    rw [hd.inf_kerG h] at hker
    have := K.mul_mem hk (hQK hker)
    rwa [mul_inv_cancel_left] at this
  · intro t ht
    exact S5.mem_liftT.2 ⟨hKT ht, h.le (hKT ht), S5.mem_imSp.2 ⟨t, ht, h.le (hKT ht), rfl⟩⟩

omit [Fintype F] in
theorem imSp_le_of_le_vPre (h : PUHyp M T L) {K : Subgroup G} {Y : Subgroup ↥(StatedSp 2 F)}
    (hK : imM h.le K ≤ S5.vPre h.le a Y) : S5.imSp a K ≤ Y := by
  rw [imM, S5.vPre, Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hK
  exact Subgroup.map_le_iff_le_comap.2 hK

omit [Finite G] in
theorem card_mul_card_le_card_sup' {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    [Finite ↥(A ⊔ B)] (hAB : A ⊓ B = ⊥) : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : Γ) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨x, y⟩ ⟨x', y'⟩ heq
  have heq' : (x : Γ) * y = x' * y' := congrArg Subtype.val heq
  have h1 : (x' : Γ)⁻¹ * x = y' * (y : Γ)⁻¹ := by
    calc (x' : Γ)⁻¹ * x = (x' : Γ)⁻¹ * (x * y) * (y : Γ)⁻¹ := by group
      _ = (x' : Γ)⁻¹ * (x' * y') * (y : Γ)⁻¹ := by rw [heq']
      _ = y' * (y : Γ)⁻¹ := by group
  have hmem : (x' : Γ)⁻¹ * x ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem x'.2) x.2, h1 ▸ B.mul_mem y'.2 (B.inv_mem y.2)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have hx : x = x' := Subtype.ext (by
    calc (x : Γ) = x' * ((x' : Γ)⁻¹ * x) := by group
      _ = x' := by rw [hmem, mul_one])
  have hy : y = y' := Subtype.ext (by
    have h2 : y' * (y : Γ)⁻¹ = 1 := h1 ▸ hmem
    calc (y : Γ) = (y' * (y : Γ)⁻¹)⁻¹ * y' := by group
      _ = y' := by rw [h2, inv_one, one_mul])
  rw [hx, hy]

theorem false_of_base (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L 1 F a) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hne : Xq M ≠ Uq M T L ⊔ Zq M L) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l))
    (hJl : S5.jOff h.le L 2 (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {x : (puAmalgam h.le).Universal} (hx : x ∈ stab _ (baseB (puAmalgam h.le)))
    (hQα : Qv _ (baseA (puAmalgam h.le)) ≤ S5.jOff h.le L 2 (x • baseA _) (baseB _))
    (hQδ : Qv _ (x • baseA (puAmalgam h.le)) ≤ S5.jOff h.le L 2 (baseA _) (baseB _))
    (hidx : (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L 2 (x • baseA _) (baseB _) ⊓ S5.jOff h.le L 2 (baseA _) (baseB _)) ≤ 4)
    (hcase : S5.jOff h.le L 2 (x • baseA _) (baseB _) ≠ S5.jOff h.le L 2 (baseA _) (baseB _))
    {s s' : Submodule F (MSP.V4 F)} (hs : MSP.IsPoint s) (hs' : MSP.IsPoint s') (hss : s ≠ s')
    (hX : MSP.xPoint s ⊔ MSP.xPoint s' ≤ S5.vIm h.le a (Qv _ (x • baseA (puAmalgam h.le)))) :
    False := by
  classical
  have : CharP F 2 := hd.charP
  have hNF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  have hLn := h.L_subgroupOf_normal
  have hxB : x • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hx
  set Jα := S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) with hJα
  set Jδ := S5.jOff h.le L 2 (x • baseA (puAmalgam h.le)) (baseB _) with hJδ
  have hJδmap : Jδ = Jα.map (MulAut.conj x).toMonoidHom := by
    rw [hJδ, hJα, ← S5B.jOff_smul h.le hLn 2 x (baseA _) (baseB _), hxB]
  set J₀ := S5.jOffM M T L 2 with hJ₀
  have hJα₀ : Jα = imM h.le J₀ := S5.jOff_baseA h 2
  have hJ₀T : J₀ ≤ T := iSup₂_le fun E hE => (S5.offSetM_le 2 hE)
  have hQB : Qv _ (baseB (puAmalgam h.le)) = imM h.le T := puAmalgam.qv_baseB h.le
  have hJαB : Jα ≤ Qv _ (baseB (puAmalgam h.le)) := by rw [hJα₀, hQB]; exact imM_mono h.le hJ₀T
  obtain ⟨K₀, hK₀T, hK₀M, hK₀⟩ := S5B.exists_eq_imM h.le (hQB ▸ (inf_le_right.trans hJαB) :
    Jδ ⊓ Jα ≤ imM h.le T)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδβ : (puAmalgam h.le).treeGraph.Adj (x • baseA (puAmalgam h.le)) (baseB _) := by
    rw [← hxB]
    exact (adj_smul _ x _ _).mpr hαβ
  have hδM : IsMVtx _ (x • baseA (puAmalgam h.le)) :=
    (isMVtx_smul _ x _).mpr (isMVtx_baseA _)
  have hQαJα : Qv _ (baseA (puAmalgam h.le)) ≤ Jα := S5B.qv_le_jOff h (by norm_num)
    (isMVtx_baseA _) hαβ
  have hQδJδ : Qv _ (x • baseA (puAmalgam h.le)) ≤ Jδ := S5B.qv_le_jOff h (by norm_num) hδM hδβ
  have hQA : Qv _ (baseA (puAmalgam h.le)) = imM h.le (pCoreOf 2 M) := S5B.qv_baseA_eq h
  have hQK₀ : pCoreOf 2 M ≤ K₀ := by
    rw [← imM_le_imM_iff h.le (pCoreOf_le' M), ← hQA, ← hK₀]
    exact le_inf hQα hQαJα
  have hK₀J₀ : K₀ ≤ J₀ := by
    rw [← imM_le_imM_iff h.le hK₀M, ← hK₀, ← hJα₀]
    exact inf_le_right
  have hQJ₀ : pCoreOf 2 M ≤ J₀ := hQK₀.trans hK₀J₀
  have hXK₀ : MSP.xPoint s ⊔ MSP.xPoint s' ≤ S5.imSp a K₀ := by
    refine hX.trans ?_
    rw [← S5.vIm_imM h, ← hK₀]
    exact Subgroup.map_mono (Subgroup.comap_mono (le_inf hQδJδ hQδ))
  have hcK₀ : Nat.card (S5.imSp a K₀) ≤ 4 := by
    rw [hd.card_imSp h hK₀T, ← S5B.relIndex_imM h.le hK₀M, ← hQA, ← hK₀]
    exact hidx
  have hcX : 4 ≤ Nat.card ↥(MSP.xPoint s ⊔ MSP.xPoint s') := by
    have h1 := card_mul_card_le_card_sup' (S5.xPoint_inf_xPoint hs hs' hss)
    rw [MSP.card_xPoint hs, MSP.card_xPoint hs', hNF] at h1
    exact h1
  have hK₀a : S5.imSp a K₀ = MSP.xPoint s ⊔ MSP.xPoint s' :=
    (Subgroup.eq_of_le_of_card_ge hXK₀ (hcK₀.trans hcX)).symm
  have hK₀eq : K₀ = S5.liftT T a (MSP.xPoint s ⊔ MSP.xPoint s') := by
    rw [← hK₀a, liftT_imSp_eq h hd hK₀T hQK₀]
  have hTl₀ : S5.imSp a T ≤ MSP.stab l := imSp_le_of_le_vPre h (hQB ▸ hTl)
  have hJl₀ : S5.imSp a J₀ ≤ MSP.qLine l := imSp_le_of_le_vPre h (hJα₀ ▸ hJl)
  have hq8 : Nat.card (MSP.qLine l) = 8 := by rw [MSP.card_qLine hl, hNF]; norm_num
  have hKJ : S5.imSp a K₀ ≤ S5.imSp a J₀ := S5.imSp_mono a hK₀J₀
  have hJ₀a : S5.imSp a J₀ = MSP.qLine l := by
    have hdvd : Nat.card (S5.imSp a J₀) ∣ 8 := hq8 ▸ Subgroup.card_dvd_of_le hJl₀
    have h4 : 4 ≤ Nat.card (S5.imSp a J₀) := by
      have := Subgroup.card_le_of_le hKJ
      rw [hK₀a] at this
      exact hcX.trans this
    have h8 : Nat.card (S5.imSp a J₀) = 4 ∨ Nat.card (S5.imSp a J₀) = 8 := by
      have hle : Nat.card (S5.imSp a J₀) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hc : Nat.card (S5.imSp a J₀) <;> simp_all
    rcases h8 with h4' | h8'
    · exfalso
      have heq : S5.imSp a K₀ = S5.imSp a J₀ :=
        Subgroup.eq_of_le_of_card_ge hKJ (by rw [h4', hK₀a]; exact hcX)
      have hJK : J₀ = K₀ := by
        rw [← liftT_imSp_eq h hd hJ₀T hQJ₀, ← heq, liftT_imSp_eq h hd hK₀T hQK₀]
      have hle : Jα ≤ Jδ := by
        rw [hJα₀, hJK, ← hK₀]
        exact inf_le_left
      have : Finite ↥(Qv _ (baseB (puAmalgam h.le))) :=
        finite_qv _ h.hyp20 (not_isMVtx_baseB _)
      have hJδB : Jδ ≤ Qv _ (baseB (puAmalgam h.le)) := S5B.jOff_le_qv h.le L _ _ _
      have : Finite ↥Jδ := Finite.of_injective _ (Subgroup.inclusion_injective hJδB)
      have hcd : Nat.card Jδ = Nat.card Jα := by
        rw [hJδmap, Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hcase (Subgroup.eq_of_le_of_card_ge hle hcd.le).symm
    · exact Subgroup.eq_of_le_of_card_ge hJl₀ (by rw [hq8, h8'])
  have hlT : MSP.qLine l ≤ S5.imSp a T := hJ₀a ▸ S5.imSp_mono a hJ₀T
  have hJ₀eq : J₀ = S5.liftT T a (MSP.qLine l) := by
    rw [← hJ₀a, liftT_imSp_eq h hd hJ₀T hQJ₀]
  have hthom₀ : thompsonJ T ≤ J₀ :=
    hJ₀eq ▸ thompsonJ_le_liftT_qLine h hd hXL hne hl hTl₀ hlT
  have hbaum₀ : baum T ≤ J₀ := hJ₀eq ▸ baum_le_liftT_qLine h hd hXL hne hl hTl₀ hlT
  have hxN : x ∈ Subgroup.normalizer (imM h.le T : Set (puAmalgam h.le).Universal) :=
    hQB ▸ stab_le_normalizer_qv _ _ hx
  have hJT : thompsonJ T ≤ M := (C1GN.thompsonJ_le T).trans h.le
  have hBT : baum T ≤ M := inf_le_left.trans h.le
  have hthomK : thompsonJ T ≤ K₀ := by
    rw [← imM_le_imM_iff h.le hJT, ← hK₀, ← thompsonJ_imM h]
    have hN : x ∈ Subgroup.normalizer (thompsonJ (imM h.le T) : Set _) :=
      S51.normalizer_le_of_char (C1GN.thompsonJ_le (imM h.le T))
        (QuasithinUnique.Setup.characteristic_thompsonJ (imM h.le T)) hxN
    have h1 : thompsonJ (imM h.le T) ≤ Jα := by
      rw [thompsonJ_imM h, hJα₀]
      exact imM_mono h.le hthom₀
    refine le_inf ?_ h1
    rw [← map_conj_eq_of_mem_normalizer hN, hJδmap]
    exact Subgroup.map_mono h1
  have hbaumK : baum T ≤ K₀ := by
    rw [← imM_le_imM_iff h.le hBT, ← hK₀, ← baum_imM h]
    have hN : x ∈ Subgroup.normalizer (baum (imM h.le T) : Set _) :=
      S51.normalizer_le_of_char (inf_le_left : baum (imM h.le T) ≤ imM h.le T)
        (C1GN.characteristic_baum (imM h.le T)) hxN
    have h1 : baum (imM h.le T) ≤ Jα := by
      rw [baum_imM h, hJα₀]
      exact imM_mono h.le hbaum₀
    refine le_inf ?_ h1
    rw [← map_conj_eq_of_mem_normalizer hN, hJδmap]
    exact Subgroup.map_mono h1
  exact false_of_xPoint hd h hb hs hs' hK₀T hK₀eq hK₀a hthomK hbaumK

end Base

end CFSG.Quasithin.MS93.S5D
