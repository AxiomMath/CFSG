module

public import CFSG.Quasithin.MS93.S5CCoc
public import CFSG.Quasithin.MS93.S38Base
public import CFSG.Quasithin.MS93.S511SVec

public section

namespace CFSG.Quasithin.MS93.S5C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
private theorem card_mul_card_le_card_sup {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    [Finite ↥(A ⊔ B)] (hAB : A ⊓ B = ⊥) : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : Γ) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ heq
  have heq' : (a : Γ) * b = a' * b' := congrArg Subtype.val heq
  have h1 : (a' : Γ)⁻¹ * a = b' * (b : Γ)⁻¹ := by
    calc (a' : Γ)⁻¹ * a = (a' : Γ)⁻¹ * (a * b) * (b : Γ)⁻¹ := by group
      _ = (a' : Γ)⁻¹ * (a' * b') * (b : Γ)⁻¹ := by rw [heq']
      _ = b' * (b : Γ)⁻¹ := by group
  have hmem : (a' : Γ)⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have ha : a = a' := Subtype.ext (by
    calc (a : Γ) = a' * ((a' : Γ)⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one])
  have hb : b = b' := Subtype.ext (by
    have h2 : b' * (b : Γ)⁻¹ = 1 := h1 ▸ hmem
    calc (b : Γ) = (b' * (b : Γ)⁻¹)⁻¹ * b' := by group
      _ = b' := by rw [h2, inv_one, one_mul])
  rw [ha, hb]

omit [Finite G] [Fintype F] in
private theorem isPoint_map {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) (g : MSP.Sp4 F) :
    MSP.IsPoint (p.map (Matrix.mulVecLin (MSP.mat g))) := by
  have := (Submodule.equivMapOfInjective (Matrix.mulVecLin (MSP.mat g))
    (MSP.mulVec_mat_injective g) p).finrank_eq
  exact this.symm.trans hp

private theorem commute_of_vec_fixed (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
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

theorem le_card_imSp_of_transv (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E Q : Subgroup G} (hET : E ≤ T) (hEQ : E ≤ Q) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hEc : 2 ^ k ≤ Nat.card (S5.imSp a E))
    (hRT : ¬ ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (T : Set G)) :
    (2 ^ k) ^ 2 ≤ Nat.card (S5.imSp a Q) := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hEM : E ≤ M := hET.trans h.le
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨s, hs, hcomm, -, hEs⟩ := S510.exists_point_of_relIndex h hd hEM hrel
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
  have hs'p : MSP.IsPoint s' := isPoint_map hs (a t)
  set A := S5.imSp a E with hA
  set B := A.map (MulAut.conj (a t)).toMonoidHom with hB
  have hBs : B ≤ MSP.xPoint s' := by
    rw [hs', ← MSP.xPoint_map_conj]
    exact Subgroup.map_mono hEs
  have hAB : A ⊓ B = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hEs hBs).trans
      (S5.xPoint_inf_xPoint hs hs'p fun he => hts he.symm).le)
  have hBQ : B ≤ S5.imSp a Q := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨t * e * t⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have heQ : (e : G) ∈ Q := hEQ (Subgroup.mem_subgroupOf.1 he)
      exact (Subgroup.mem_normalizer_iff.1 (hTQ htT) e).1 heQ
    · simp [map_mul, map_inv, MulAut.conj_apply]
  have hAQ : A ≤ S5.imSp a Q := S5.imSp_mono a hEQ
  have hcB : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj (a t)).injective
  have h1 := card_mul_card_le_card_sup hAB
  have h2 : Nat.card ↥(A ⊔ B) ≤ Nat.card (S5.imSp a Q) := Subgroup.card_le_of_le (sup_le hAQ hBQ)
  rw [hcB] at h1
  calc (2 ^ k) ^ 2 = 2 ^ k * 2 ^ k := by ring
    _ ≤ Nat.card A * Nat.card A := Nat.mul_le_mul hEc hEc
    _ ≤ _ := h1.trans h2

theorem commutator_le_centralizer_of_not_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) (hTl : S5.imSp a T ≤ MSP.stab l)
    {E : Subgroup G} (hEM : E ≤ M) (hEl : S5.imSp a E ≤ MSP.qLine l)
    {t : ↥M} (htT : (t : G) ∈ T) (htl : a t ∉ MSP.qLine l)
    (hRt : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer ({(t : G)} : Set G)) :
    ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (T : Set G) := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hT2 : IsPGroup 2 ↥(S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hinv : ∀ r ∈ S5.imSp a T, ∀ w ∈ l, MSP.mat r *ᵥ w ∈ l :=
    fun r hr w hw => MSP.mulVec_mem_of_mem_stab (hTl hr) hw
  have hl0 : l ≠ ⊥ := by
    rintro rfl
    have := hl.1
    rw [finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨w, hwl, hw0, hwfix⟩ := MSP.exists_fixed_ne_zero hT2 hl0 hinv
  have htw : MSP.mat (a t) *ᵥ w = w := hwfix _ ⟨t, Subgroup.mem_subgroupOf.2 htT, rfl⟩
  intro y hy
  have hyU : y ∈ Uq M T L := commutator_le_left_of_le_normalizer (hEM.trans hUn) hy
  have hvl : nv.vec ⟨y, hyU⟩ ∈ l :=
    (S511S.commSp_le_iff_vec h nv hEM).1 ((MSP.commSp_mono hEl).trans (MSP.commSp_qLine_le hl))
      ⟨y, hyU⟩ hy
  have hty : (t : G) * y = y * t := Subgroup.mem_centralizer_iff.1 (hRt hy) t rfl
  have htv : MSP.mat (a t) *ᵥ nv.vec ⟨y, hyU⟩ = nv.vec ⟨y, hyU⟩ :=
    nv.mat_mulVec_vec_of_commute t ⟨y, hyU⟩ hty
  have hvw : nv.vec ⟨y, hyU⟩ ∈ F ∙ w := by
    by_contra hvw
    apply htl
    have hlt : (F ∙ w) < (F ∙ w) ⊔ (F ∙ nv.vec ⟨y, hyU⟩) := by
      refine lt_of_le_of_ne le_sup_left fun heq => hvw ?_
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have h1 : Module.finrank F (F ∙ w) = 1 := finrank_span_singleton hw0
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    have hle : (F ∙ w) ⊔ (F ∙ nv.vec ⟨y, hyU⟩) ≤ l :=
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hwl)
        ((Submodule.span_singleton_le_iff_mem _ _).2 hvl)
    have h3 := Submodule.finrank_mono hle
    have heq : (F ∙ w) ⊔ (F ∙ nv.vec ⟨y, hyU⟩) = l :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hl.1] at h3 ⊢; omega)
    rw [MSP.mem_fixer]
    intro u hu
    rw [← heq] at hu
    obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, htw, htv]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hvw
  rw [Subgroup.mem_centralizer_iff]
  intro t' ht'
  refine commute_of_vec_fixed h hd nv hyU (h.le ht') ?_
  rw [← hc, Matrix.mulVec_smul, hwfix _ ⟨⟨t', h.le ht'⟩, Subgroup.mem_subgroupOf.2 ht', rfl⟩]

theorem relIndex_centralizer_le_of_le_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {E : Subgroup G} (hEM : E ≤ M)
    (hEl : S5.imSp a E ≤ MSP.qLine l) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ (2 ^ k) ^ 2 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have h1 := S5B.relIndex_centralizer_mul_card h hlift c hEM
  have hFq := hd.nat_card_eq
  rw [MSP.card_V4, hFq] at h1
  have hlfix : l ≤ MSP.fixSp (S5.imSp a E) :=
    (MSP.fixSp_qLine hl).symm.le.trans (MSP.fixSp_antitone hEl)
  have hlc : Nat.card l = (2 ^ k) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hl.1, hFq]
  have h2 : (2 ^ k) ^ 2 ≤ Nat.card (MSP.fixSp (S5.imSp a E)) := by
    rw [← hlc]
    exact Nat.card_mono (Set.toFinite _) fun x hx => hlfix hx
  have hq : 0 < (2 ^ k) ^ 2 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hq
  calc (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) * (2 ^ k) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
          Nat.card (MSP.fixSp (S5.imSp a E)) := Nat.mul_le_mul_left _ h2
    _ = (2 ^ k) ^ 4 := h1
    _ = (2 ^ k) ^ 2 * (2 ^ k) ^ 2 := by ring

theorem le_relIndex_of_transv_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (g : (puAmalgam h.le).Universal) {E Q : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (g • baseB (puAmalgam h.le))) (hQ : Q ≤ Qv _ (g • baseB (puAmalgam h.le)))
    (hEQ : E ≤ Q)
    (hTQ : Qv _ (g • baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (Q : Set (puAmalgam h.le).Universal))
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (g • baseA (puAmalgam h.le))) = 2 ^ k)
    (hEc : 2 ^ k ≤ (Qv _ (g • baseA (puAmalgam h.le))).relIndex E)
    (hRT : ¬ ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), E⁆ ≤
      Subgroup.centralizer (Qv _ (g • baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) :
    (2 ^ k) ^ 2 ≤ (Qv _ (g • baseA (puAmalgam h.le))).relIndex Q := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  have hQQ : Q = (Q.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv Q g).symm
  rw [hEE, hQQ] at hEQ
  rw [hEE] at hE hrel hEc hRT
  rw [hQQ] at hQ hTQ ⊢
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
  have hTQ₀ := le_normalizer_of_imM h.le h.le hQ₀M hTQ
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
  rw [PU.qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hQ₀M, ← hd.card_imSp h hQ₀T]
  exact le_card_imSp_of_transv h hd hE₀T hEQ hTQ₀ hrel hEc hRT₀

theorem commutator_le_centralizer_of_not_mem_gp (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) (g : (puAmalgam h.le).Universal)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l))
    {E : Subgroup (puAmalgam h.le).Universal}
    (hEl : E ≤ (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom)
    {t : (puAmalgam h.le).Universal} (htT : t ∈ Qv _ (g • baseB (puAmalgam h.le)))
    (htl : t ∉ (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom)
    (hRt : ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), E⁆ ≤
      Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), E⁆ ≤
      Subgroup.centralizer (Qv _ (g • baseB (puAmalgam h.le)) :
        Set (puAmalgam h.le).Universal) := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hEl hRt ⊢
  rw [map_conj_le_map_conj_iff, S5B.vPre_eq_imM] at hEl
  obtain ⟨E₀, -, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hEl
  rw [← S5B.vPre_eq_imM, hE₀] at hEl
  rw [hE₀] at hRt ⊢
  have hEl₀ : S5.imSp a E₀ ≤ MSP.qLine l := by
    rw [imM, S5.vPre,
      Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hEl
    exact Subgroup.map_le_iff_le_comap.2 hEl
  have hTl₀ : S5.imSp a T ≤ MSP.stab l := by
    rw [puAmalgam.qv_baseB, imM, S5.vPre,
      Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hTl
    exact Subgroup.map_le_iff_le_comap.2 hTl
  rw [puAmalgam.qv_smul_baseB] at htT
  obtain ⟨_, ⟨t₀, ht₀T, rfl⟩, rfl⟩ := htT
  have ht₀l : a t₀ ∉ MSP.qLine l := by
    intro hmem
    apply htl
    exact Subgroup.mem_map_of_mem _ ⟨t₀, hmem, rfl⟩
  have hRt₀ : ⁅Uq M T L, E₀⁆ ≤ Subgroup.centralizer ({(t₀ : G)} : Set G) := by
    intro x hx
    have hxM : x ∈ M := commutator_le_of_le hUM hE₀M hx
    have hmem : (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨x, hxM⟩) ∈
        (⁅imM h.le (Uq M T L), imM h.le E₀⁆).map (MulAut.conj g).toMonoidHom := by
      rw [← imM_commutator h.le hUM hE₀M]
      exact Subgroup.mem_map_of_mem _ ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator] at hRt
    have hc := Subgroup.mem_centralizer_iff.1 (hRt hmem) _ rfl
    have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA) :=
      (MulAut.conj g).injective.comp (puAmalgam h.le).ofA_injective
    have hc2 : ((MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA) (t₀ * ⟨x, hxM⟩) =
        ((MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA) (⟨x, hxM⟩ * t₀) := by
      simp only [map_mul, MonoidHom.comp_apply]
      exact hc
    have hc3 := congrArg Subtype.val (hinj hc2)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hc3
  have key := commutator_le_centralizer_of_not_mem h hd hl hTl₀ hE₀M hEl₀
    (Subgroup.mem_subgroupOf.1 ht₀T) ht₀l hRt₀
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator,
    puAmalgam.qv_smul_baseB, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
    ← imM_commutator h.le hUM hE₀M]
  have h1 : imM h.le ⁅Uq M T L, E₀⁆ ≤
      imM h.le (⁅Uq M T L, E₀⁆ ⊓ Subgroup.centralizer (T : Set G)) :=
    imM_mono h.le (le_inf le_rfl key)
  rw [imM_inf_centralizer h.le _ h.le] at h1
  exact h1.trans inf_le_right

theorem relIndex_centralizer_le_of_le_qLine_gp (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) (g : (puAmalgam h.le).Universal)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {E : Subgroup (puAmalgam h.le).Universal}
    (hEl : E ≤ (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom) :
    (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (g • baseA (puAmalgam h.le))) ≤ (2 ^ k) ^ 2 := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hEl ⊢
  rw [map_conj_le_map_conj_iff, S5B.vPre_eq_imM] at hEl
  obtain ⟨E₀, -, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hEl
  rw [← S5B.vPre_eq_imM, hE₀] at hEl
  have hEl₀ : S5.imSp a E₀ ≤ MSP.qLine l := by
    rw [imM, S5.vPre,
      Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hEl
    exact Subgroup.map_le_iff_le_comap.2 hEl
  rw [hE₀, S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hUM hE₀M]
  exact relIndex_centralizer_le_of_le_qLine h hd hl hE₀M hEl₀

theorem xm_inf_centralizer_le_centralizer_vPre_gp (h : PUHyp M T L) (h32 : S32)
    (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k) (g : (puAmalgam h.le).Universal)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (g • baseB (puAmalgam h.le)))
    (hTE : Qv _ (g • baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hEl : E ≤ (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom)
    (hcard : (2 ^ k) ^ 2 ≤ (Qv _ (g • baseA (puAmalgam h.le))).relIndex E) :
    XM _ (g • baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (((S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hTE hEl hcard ⊢
  rw [PU.qv_smul, map_conj_le_map_conj_iff] at hE
  rw [map_conj_le_map_conj_iff] at hEl
  rw [PU.qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hcard
  have hBB : ((Qv _ (baseB (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = Qv _ (baseB (puAmalgam h.le)) := by
    have := map_conj_map_conj_inv (Qv _ (baseB (puAmalgam h.le))) g⁻¹
    rwa [inv_inv] at this
  rw [PU.qv_smul, le_normalizer_map_conj_iff, hBB] at hTE
  have key := xm_inf_centralizer_le_centralizer_vPre h h32 hd hk hE hTE hl hEl hcard
  rw [PU.xm_smul, PU.centralizer_map_mulEquiv (MulAut.conj g) (E.map (MulAut.conj g⁻¹).toMonoidHom),
    PU.centralizer_map_mulEquiv (MulAut.conj g) (S5.vPre h.le a (MSP.qLine l)),
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff]
  exact key

theorem not_imSp_le_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2) :
    ¬ S5.imSp a E ≤ commutator (MSP.Sp4 F) := by
  have hrel' : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ 1 := by
    rw [pow_one]
    exact hrel
  obtain ⟨p, hp, -, hfix, hxP⟩ := S510.exists_point_of_relIndex h hd hEM hrel'
  obtain ⟨g, hgE, hg1⟩ : ∃ g ∈ S5.imSp a E, g ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : S5.imSp a E = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    have htop : MSP.fixSp (S5.imSp a E) = ⊤ := by
      rw [hbot]
      ext v
      simp [MSP.mem_fixSp, MSP.mat_one]
    rw [show MSP.fixSp (S5.imSp a E) = MSP.perp p from hfix] at htop
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    have h3 := MSP.finrank_perp p
    rw [htop, finrank_top, h4] at h3
    have hp1 : Module.finrank F p = 1 := hp
    omega
  obtain ⟨x, hx0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  obtain ⟨c, rfl⟩ := (MSP.mem_xPoint_span hx0).1 (hxP hgE)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hg1 (MSP.transv_zero x)
  exact fun hle => MSP.transv_not_mem_commutator_of_card_two (by rw [hd.nat_card_eq, pow_one])
    hx0 c hc0 (hle hgE)

theorem not_vIm_le_commutator_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (g : (puAmalgam h.le).Universal) {E : Subgroup (puAmalgam h.le).Universal}
    (hEst : E ≤ stab _ (g • baseA (puAmalgam h.le)))
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (g • baseA (puAmalgam h.le))) = 2) :
    ¬ S5.vIm h.le a (E.map (MulAut.conj g⁻¹).toMonoidHom) ≤ commutator (MSP.Sp4 F) := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hEst hrel
  rw [PU.stab_smul, map_conj_le_map_conj_iff, puAmalgam.stab_baseA] at hEst
  obtain ⟨E₀, -, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hEst
  rw [hE₀] at hrel ⊢
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hUM hE₀M] at hrel
  rw [S5B.vIm_imM]
  exact not_imSp_le_commutator h hd hE₀M hrel

theorem uSub_sup_inf_centralizer_le_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (g : (puAmalgam h.le).Universal) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (g • baseB (puAmalgam h.le)))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hEl : E ≤ (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom)
    (hcard : 2 ^ k < (Qv _ (g • baseA (puAmalgam h.le))).relIndex E)
    (hodd : 2 ≤ k ∨
      ¬ S5.vIm h.le a (E.map (MulAut.conj g⁻¹).toMonoidHom) ≤ commutator (MSP.Sp4 F)) :
    (S5.uSub h.le L (g • baseA (puAmalgam h.le)) ⊔ (XM _ (g • baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (g • baseA (puAmalgam h.le)) :
          Set (puAmalgam h.le).Universal))) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (((S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  have hLn := h.L_subgroupOf_normal
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hZM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hEl hcard ⊢
  rw [PU.qv_smul, map_conj_le_map_conj_iff, puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hE
  rw [map_conj_le_map_conj_iff, hE₀] at hEl
  have hEl₀ : S5.imSp a E₀ ≤ MSP.qLine l := by
    rw [imM, S5.vPre,
      Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hEl
    exact Subgroup.map_le_iff_le_comap.2 hEl
  rw [hE₀, PU.qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hE₀M, ← hd.card_imSp h hE₀T] at hcard
  rw [hE₀, S5B.vIm_imM] at hodd
  rw [hE₀, S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.xm_smul, S5B.xm_baseA_eq h,
    puTrans_smul_baseA hLn, PU.centralizer_map_mulEquiv (MulAut.conj g) (imM h.le L),
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← imM_inf_centralizer h.le _ h.L_le,
    ← Subgroup.map_sup, ← S5B.imM_sup_of_le h.le hUM hZM,
    PU.centralizer_map_mulEquiv (MulAut.conj g) (imM h.le E₀),
    PU.centralizer_map_mulEquiv (MulAut.conj g) (S5.vPre h.le a (MSP.qLine l)),
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff,
    ← imM_inf_centralizer h.le _ hE₀M]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hx' := Subgroup.mem_subgroupOf.1 hx
  exact commute_of_mem_uq_sup_inf_centralizer h hd hE₀M hl hEl₀
    (by rw [hd.nat_card_eq]; exact hcard) hodd hx'.1 hx'.2 y.2 hy

theorem eq_jOff_of_isOffCand (h : PUHyp M T L) {q : ℕ} {γ ε : Vtx (puAmalgam h.le)}
    (hε : ¬ IsMVtx _ ε) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : S5.IsOffCand h.le L q γ ε E)
    (hcard : Nat.card E = Nat.card (S5.jOff h.le L q γ ε))
    (hJ : ¬ S5.jOff h.le L q γ ε ≤ Qv _ γ) : E = S5.jOff h.le L q γ ε := by
  have hyp := h.hyp20
  have : Finite ↥(Qv _ ε) := finite_qv _ hyp hε
  have hJε : S5.jOff h.le L q γ ε ≤ Qv _ ε := S5B.jOff_le_qv h.le L q γ ε
  have : Finite ↥(S5.jOff h.le L q γ ε) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hJε)
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ ∈ S5.offSet h.le L q γ ε := by
    by_contra hno
    push Not at hno
    apply hJ
    refine iSup₂_le fun E₁ hE₁ => absurd hE₁ (hno E₁)
  have hE₁J : E₁ ≤ S5.jOff h.le L q γ ε := le_iSup₂_of_le E₁ hE₁ le_rfl
  have hEoff : E ∈ S5.offSet h.le L q γ ε := by
    refine ⟨hE, fun E' hE' => ?_⟩
    calc Nat.card E' ≤ Nat.card E₁ := hE₁.2 E' hE'
      _ ≤ Nat.card (S5.jOff h.le L q γ ε) := Subgroup.card_le_of_le hE₁J
      _ = Nat.card E := hcard.symm
  exact Subgroup.eq_of_le_of_card_ge (le_iSup₂_of_le E hEoff le_rfl) hcard.symm.le

end CFSG.Quasithin.MS93.S5C
