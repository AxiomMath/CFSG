module

public import CFSG.Quasithin.MS93.Q2GSp
public import CFSG.Quasithin.MS93.S5A55X
public import CFSG.Quasithin.MS93.S38EndStmt
public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

section Group

variable {Γ : Type*} [Group Γ]

theorem card_sup_mul_card_inf {A B : Subgroup Γ} (hB : B ≤ Subgroup.normalizer (A : Set Γ)) :
    Nat.card (A ⊔ B : Subgroup Γ) * Nat.card (A ⊓ B : Subgroup Γ) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set Γ)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup Γ, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

theorem card_eq_relIndex_mul {H K : Subgroup Γ} (hHK : H ≤ K) :
    Nat.card K = H.relIndex K * Nat.card H := by
  rw [← Subgroup.relIndex_mul_card H K, inf_of_le_left hHK]

theorem two_mul_card_le [Finite Γ] {H K : Subgroup Γ} (hHK : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  have h1 := card_eq_relIndex_mul hHK
  have hr : H.relIndex K ≠ 1 := fun h1' => hne (le_antisymm hHK (Subgroup.relIndex_eq_one.1 h1'))
  have hr0 : H.relIndex K ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  rw [h1]
  have : 2 ≤ H.relIndex K := by omega
  exact Nat.mul_le_mul_right _ this

end Group

theorem eq_bot_of_finrank_fixSp_four {K : Type} [Field K] {E : Subgroup (MSP.Sp4 K)}
    (h4 : Module.finrank K (MSP.fixSp E) = 4) : E = ⊥ :=
  MSP.fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq (by rw [h4]; simp))

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_sixteen (hK : Nat.card K = 2) {P : Subgroup (MSP.Sp4 K)} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨S, hS⟩ := MSP.exists_sylow_sylS (F := K)
  have h1 : Nat.card (Q : Subgroup (MSP.Sp4 K)) = Nat.card (S : Subgroup (MSP.Sp4 K)) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 : Nat.card (S : Subgroup (MSP.Sp4 K)) = 16 := by
    rw [hS, MSP.card_sylS, hK]
    norm_num
  calc Nat.card P ≤ Nat.card (Q : Subgroup (MSP.Sp4 K)) := Subgroup.card_le_of_le hPQ
    _ = 16 := by rw [h1, h2]

end Sylow

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} {l : Submodule F (MSP.V4 F)}

structure EvenData (M T L : Subgroup G) (a : ↥M →* ↥(StatedSp 2 F))
    (l : Submodule F (MSP.V4 F)) : Prop where
  sp4 : S5.IsSp4Data M T L 1 F a
  xu : Xq M = Uq M T L ⊔ Zq M L
  notCent : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)
  line : MSP.IsLine l
  tStab : S5.imSp a T ≤ MSP.stab l
  jEq : S5.imSp a (S5.jOffM M T L 2) = MSP.qLine l ⊓ commutator (MSP.Sp4 F)
  offNe : (S5.offSetM M T L 2).Nonempty

namespace EvenData

variable (h : PUHyp M T L) (D : EvenData M T L a l)

omit [Finite G] in
include D in
theorem card_F : Nat.card F = 2 := by rw [D.sp4.nat_card_eq, pow_one]

omit [Finite G] in
include D in
theorem charP : CharP F 2 := D.sp4.charP

omit [Finite G] in
theorem jOffM_le : S5.jOffM M T L 2 ≤ T := iSup₂_le fun _ hE => S5.offSetM_le 2 hE

include h in
theorem pCore_le_jOffM : pCoreOf 2 M ≤ S5.jOffM M T L 2 := by
  have h1 := S5B.qv_le_jOff (L := L) h (q := 2) (by norm_num) (isMVtx_baseA (puAmalgam h.le))
    (adj_baseA_baseB _)
  rw [S5.qv_baseA_eq h, S5.jOff_baseA h] at h1
  exact (imM_le_imM_iff h.le (pCoreOf_le' M)).1 h1

omit [Finite G] in
include D in
theorem card_imSp_jOffM : Nat.card (S5.imSp a (S5.jOffM M T L 2)) = 4 := by
  rw [D.jEq]
  exact MSP.card_qLine_inf_commutator D.card_F D.line

include h D in
theorem relIndex_jOffM : (pCoreOf 2 M).relIndex (S5.jOffM M T L 2) = 4 := by
  rw [← D.sp4.card_imSp h jOffM_le]
  exact D.card_imSp_jOffM

include h D in
theorem card_jOffM : Nat.card (S5.jOffM M T L 2) = 4 * Nat.card (pCoreOf 2 M) := by
  rw [card_eq_relIndex_mul (pCore_le_jOffM h), relIndex_jOffM h D]

include D in
theorem card_le_of_cand {E : Subgroup G} (hE : S5.IsOffCandM M T L 2 E) :
    Nat.card E ≤ Nat.card (S5.jOffM M T L 2) := by
  obtain ⟨E₀, hE₀⟩ := D.offNe
  exact (hE₀.2 E hE).trans (Subgroup.card_le_of_le (le_iSup₂_of_le E₀ hE₀ le_rfl))

include D in
theorem le_of_cand {E : Subgroup G} (hE : S5.IsOffCandM M T L 2 E)
    (hc : Nat.card (S5.jOffM M T L 2) ≤ Nat.card E) : E ≤ S5.jOffM M T L 2 := by
  have hmem : E ∈ S5.offSetM M T L 2 := ⟨hE, fun E' hE' => (D.card_le_of_cand hE').trans hc⟩
  exact le_iSup₂_of_le E hmem le_rfl

include h D in
theorem relIndex_U_mul {E : Subgroup G} (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
      Nat.card (MSP.fixSp (S5.imSp a E)) = 16 := by
  obtain ⟨nv⟩ := D.sp4.nonempty_natVec
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  rw [inf_comm, S5.card_uq_inf_centralizer h D.sp4 hEM, nv.card_Uq, MSP.card_V4, D.card_F]
    at h1
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
      Nat.card (MSP.fixSp (S5.imSp a E)) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      = 16 * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [mul_assoc, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

include h D in
theorem relIndex_X_mul {E : Subgroup G} (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Xq M) *
      (Nat.card (MSP.fixSp (S5.imSp a E)) * Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (E : Set G)))
      = 16 * Nat.card ↥(Zq M L) := by
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Xq M)
  rw [inf_comm, S5.card_xq_inf_centralizer h D.sp4 D.xu hEM] at h1
  have h2 := S5.card_xq_inf_centralizer h D.sp4 D.xu (J := ⊥) bot_le
  have hb1 : S5.imSp a (⊥ : Subgroup G) = ⊥ := by
    rw [S5.imSp, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hb2 : MSP.fixSp (⊥ : Subgroup (MSP.Sp4 F)) = ⊤ := MSP.fixSp_eq_top_iff.2 rfl
  have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    refine eq_top_iff.2 fun x _ => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  rw [hb1, hb2, hc, inf_top_eq, inf_top_eq] at h2
  have : Finite F := inferInstance
  rw [h1, h2]
  have h16 : Nat.card ↥(⊤ : Submodule F (MSP.V4 F)) = 16 := by
    rw [Nat.card_congr Submodule.topEquiv.toEquiv, MSP.card_V4, D.card_F]
    norm_num
  rw [h16]

omit [Finite G] [Fintype F] in
theorem imSp_inf_pre (E : Subgroup G) (Y : Subgroup (MSP.Sp4 F)) :
    S5.imSp a (E ⊓ (Y.comap a).map M.subtype) = S5.imSp a E ⊓ Y := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
    obtain ⟨hmE, ⟨m', hm', hm'm⟩⟩ := hm
    have : m' = m := Subtype.ext hm'm
    subst this
    exact ⟨⟨m', Subgroup.mem_subgroupOf.2 hmE, rfl⟩, hm'⟩
  · rintro ⟨⟨m, hm, rfl⟩, hmY⟩
    refine ⟨m, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hm, m, hmY, rfl⟩, rfl⟩

include h D in
theorem le_of_imSp_le {E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ T) (hE₂ : E₂ ≤ T)
    (hQ : pCoreOf 2 M ≤ E₂) (hle : S5.imSp a E₁ ≤ S5.imSp a E₂) : E₁ ≤ E₂ := by
  intro e he
  have heM : e ∈ M := h.le (hE₁ he)
  obtain ⟨m, hm, hme⟩ := hle ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  have hmE : (m : G) ∈ E₂ := Subgroup.mem_subgroupOf.1 hm
  have hk : (m : G)⁻¹ * e ∈ T ⊓ S5.kerG a := by
    refine ⟨T.mul_mem (T.inv_mem (hE₂ hmE)) (hE₁ he), (S5.mem_kerG a).2 ⟨M.mul_mem
      (M.inv_mem m.2) heM, ?_⟩⟩
    have e1 : (⟨(m : G)⁻¹ * e, M.mul_mem (M.inv_mem m.2) heM⟩ : ↥M) = m⁻¹ * ⟨e, heM⟩ := rfl
    rw [e1, map_mul, map_inv, hme, inv_mul_cancel]
  rw [D.sp4.inf_kerG h] at hk
  have := E₂.mul_mem hmE (hQ hk)
  rwa [mul_inv_cancel_left] at this

include h D in
theorem le_pCore_of_imSp_eq_bot {E : Subgroup G} (hE : E ≤ T) (hb : S5.imSp a E = ⊥) :
    E ≤ pCoreOf 2 M := by
  have hQT : pCoreOf 2 M ≤ T := h.pCore_le
  exact le_of_imSp_le h D hE hQT le_rfl (by
    rw [hb]
    exact bot_le)

include h D in
theorem imSp_T_inf_qLine :
    S5.imSp a T ⊓ MSP.qLine l = MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
  have hK := D.card_F
  have : CharP F 2 := D.charP
  set El := MSP.qLine l ⊓ commutator (MSP.Sp4 F) with hEl
  have hEl4 : Nat.card El = 4 := MSP.card_qLine_inf_commutator hK D.line
  have hQ8 : Nat.card (MSP.qLine l) = 8 := by rw [MSP.card_qLine D.line, hK]; norm_num
  have hJT : S5.imSp a (S5.jOffM M T L 2) ≤ S5.imSp a T := S5.imSp_mono a jOffM_le
  rw [D.jEq] at hJT
  have hle : El ≤ S5.imSp a T ⊓ MSP.qLine l := le_inf hJT inf_le_left
  by_contra hne
  have hlt := two_mul_card_le hle (Ne.symm hne)
  have hA : S5.imSp a T ⊓ MSP.qLine l = MSP.qLine l := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    have h8 : 8 ≤ Nat.card ↥(S5.imSp a T ⊓ MSP.qLine l) := by
      rw [hEl4] at hlt
      omega
    rw [hQ8]
    exact h8
  set E := T ⊓ ((MSP.qLine l).comap a).map M.subtype with hEdef
  have hET : E ≤ T := inf_le_left
  have hEM : E ≤ M := hET.trans h.le
  have hQE : pCoreOf 2 M ≤ E := by
    refine le_inf h.pCore_le fun x hx => ?_
    obtain ⟨hxM, hx1⟩ := (S5.mem_kerG a).1 (D.sp4.pCoreOf_le_kerG h hx)
    exact ⟨⟨x, hxM⟩, by rw [SetLike.mem_coe, Subgroup.mem_comap, hx1]; exact Subgroup.one_mem _,
      rfl⟩
  have hEim : S5.imSp a E = MSP.qLine l := by
    rw [hEdef, imSp_inf_pre, hA]
  have hrel : (pCoreOf 2 M).relIndex E = 8 := by
    rw [← D.sp4.card_imSp h hET, hEim, hQ8]
  have hU := relIndex_U_mul h D hEM
  rw [hEim, MSP.fixSp_qLine D.line, Module.natCard_eq_pow_finrank (K := F), D.line.1, hK] at hU
  have hcand : S5.IsOffCandM M T L 2 E := ⟨hET, by omega, by omega⟩
  have h1 := D.card_le_of_cand hcand
  rw [card_jOffM h D, card_eq_relIndex_mul hQE, hrel] at h1
  have hpos : 0 < Nat.card ↥(pCoreOf 2 M) := Nat.card_pos
  omega

include h D in
theorem card_imSp_T_le : Nat.card (S5.imSp a T) ≤ 8 := by
  have hK := D.card_F
  have : CharP F 2 := D.charP
  have hT2 : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hN : S5.imSp a T ≤ Subgroup.normalizer (MSP.qLine l : Set (MSP.Sp4 F)) := by
    rw [MSP.normalizer_qLine D.line]
    exact D.tStab
  have hi : Nat.card ↥(MSP.qLine l ⊓ S5.imSp a T) = 4 := by
    rw [inf_comm, imSp_T_inf_qLine h D, MSP.card_qLine_inf_commutator hK D.line]
  have hq : Nat.card ↥(MSP.qLine l) = 8 := by rw [MSP.card_qLine D.line, hK]; norm_num
  have hc : Nat.card ↥(MSP.qLine l ⊔ S5.imSp a T) * 4 = 8 * Nat.card ↥(S5.imSp a T) := by
    have := card_sup_mul_card_inf hN
    rw [hi, hq] at this
    exact this
  have hP : IsPGroup 2 ↥(MSP.qLine l ⊔ S5.imSp a T) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    refine IsPGroup.of_card (n := n + 1) ?_
    rw [hn] at hc
    have : Nat.card ↥(MSP.qLine l ⊔ S5.imSp a T) * 4 = 2 ^ (n + 1) * 4 := by
      rw [hc, pow_succ]
      ring
    omega
  have h16 : Nat.card ↥(MSP.qLine l ⊔ S5.imSp a T) ≤ 16 := card_le_sixteen hK hP
  omega

include h D in
theorem imSp_T_inf_commutator :
    S5.imSp a T ⊓ commutator (MSP.Sp4 F) = MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
  have hK := D.card_F
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hK
  have hEl4 := MSP.card_qLine_inf_commutator hK D.line
  have hJT : S5.imSp a (S5.jOffM M T L 2) ≤ S5.imSp a T := S5.imSp_mono a jOffM_le
  rw [D.jEq] at hJT
  have hle : MSP.qLine l ⊓ commutator (MSP.Sp4 F) ≤ S5.imSp a T ⊓ commutator (MSP.Sp4 F) :=
    le_inf hJT inf_le_right
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hEl4]
  have hidx := MSP.index_commutator c
  have hrel : (commutator (MSP.Sp4 F)).relIndex (S5.imSp a T) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (commutator (MSP.Sp4 F)) (S5.imSp a T)
    rw [hidx] at hdvd
    have hne : (commutator (MSP.Sp4 F)).relIndex (S5.imSp a T) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      obtain ⟨t, htT, hto⟩ := S5Q2.exists_mem_T_not_mem_commutator h D.sp4
      exact fun hle' => hto (hle' ⟨t, Subgroup.mem_subgroupOf.2 htT, rfl⟩)
    have := (Nat.dvd_prime Nat.prime_two).1 hdvd
    omega
  have h1 : 2 * Nat.card ↥(S5.imSp a T ⊓ commutator (MSP.Sp4 F)) = Nat.card ↥(S5.imSp a T) := by
    have := Subgroup.relIndex_mul_card (commutator (MSP.Sp4 F)) (S5.imSp a T)
    rw [hrel, inf_comm] at this
    exact this
  have h8 : Nat.card ↥(S5.imSp a T) ≤ 8 := card_imSp_T_le h D
  have h4 : Nat.card ↥(S5.imSp a T ⊓ commutator (MSP.Sp4 F)) ≤ 4 := by omega
  exact h4

omit [Finite G] [Fintype F] in
private theorem imSp_sup' {E₁ E₂ : Subgroup G} (h₁ : E₁ ≤ M) (h₂ : E₂ ≤ M) :
    S5.imSp a (E₁ ⊔ E₂) = S5.imSp a E₁ ⊔ S5.imSp a E₂ := by
  rw [S5.imSp, S5.imSp, S5.imSp, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

include h D in
theorem imSp_sup_pCore {E : Subgroup G} (hEM : E ≤ M) :
    S5.imSp a (E ⊔ pCoreOf 2 M) = S5.imSp a E := by
  rw [imSp_sup' hEM (pCoreOf_le' M)]
  have hb : S5.imSp a (pCoreOf 2 M) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨hmM, hm1⟩ :=
      (S5.mem_kerG a).1 (D.sp4.pCoreOf_le_kerG h (Subgroup.mem_subgroupOf.1 hm))
    exact (Subgroup.mem_bot).2 hm1
  rw [hb, sup_bot_eq]

omit [Finite G] in
include D in
theorem card_fixSp_eq (E : Subgroup (MSP.Sp4 F)) :
    Nat.card (MSP.fixSp E) = 2 ^ Module.finrank F (MSP.fixSp E) := by
  rw [MSP.card_fixSp, D.card_F]

include h D in
theorem imSp_eq_of_isXOff {E : Subgroup G} (hE : IsXOff M T E) :
    S5.imSp a E = MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
  obtain ⟨hET, -, hEQ, hineq⟩ := hE
  have hK := D.card_F
  have : CharP F 2 := D.charP
  have hEM : E ≤ M := hET.trans h.le
  have hT2 : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hET' : S5.imSp a E ≤ S5.imSp a T := S5.imSp_mono a hET
  have hfrel : (pCoreOf 2 M).relIndex E = Nat.card (S5.imSp a E) :=
    (D.sp4.card_imSp h hET).symm
  have hEb : S5.imSp a E ≠ ⊥ := fun hb => hEQ (le_pCore_of_imSp_eq_bot h D hET hb)
  have hf8 : Nat.card (S5.imSp a E) ≤ 8 :=
    (Subgroup.card_le_of_le hET').trans (card_imSp_T_le h D)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Nat.card (S5.imSp a E) = 2 ∨ Nat.card (S5.imSp a E) = 4 ∨
      Nat.card (S5.imSp a E) = 8 := by
    obtain ⟨j, hj⟩ := (hT2.to_le hET').exists_card_eq
    have hj0 : j ≠ 0 := fun h0 => hEb (by
      rw [h0, pow_zero] at hj
      exact Subgroup.card_eq_one.1 hj)
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j <;> first | exact absurd rfl hj0 | simp [hj]
  have hd4 : Module.finrank F (MSP.fixSp (S5.imSp a E)) ≤ 4 := Q2G.finrank_fixSp_le _
  have hd4' : Module.finrank F (MSP.fixSp (S5.imSp a E)) ≠ 4 := fun h4 =>
    hEb (eq_bot_of_finrank_fixSp_four h4)
  have hfix := card_fixSp_eq D (S5.imSp a E)
  have hc : Nat.card (MSP.fixSp (S5.imSp a E)) = 1 ∨ Nat.card (MSP.fixSp (S5.imSp a E)) = 2 ∨
      Nat.card (MSP.fixSp (S5.imSp a E)) = 4 ∨ Nat.card (MSP.fixSp (S5.imSp a E)) = 8 := by
    rw [hfix]
    interval_cases (Module.finrank F (MSP.fixSp (S5.imSp a E))) <;> simp_all
  have hX := relIndex_X_mul h D hEM
  rw [hfrel] at hineq
  have hZpos : 0 < Nat.card ↥(Zq M L) := Nat.card_pos
  by_cases he : S5.imSp a E ≤ commutator (MSP.Sp4 F)
  ·
    have hZ : Zq M L ≤ Subgroup.centralizer (E : Set G) :=
      S5Q2.le_centralizer_of_mem_commutator h D.sp4 hEM fun x hx =>
        he ⟨⟨x, hEM hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [inf_of_le_left hZ] at hX
    have hle : S5.imSp a E ≤ MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
      rw [← imSp_T_inf_commutator h D]
      exact le_inf hET' he
    have h4 : Nat.card (S5.imSp a E) ≤ 4 := by
      have := Subgroup.card_le_of_le hle
      rwa [MSP.card_qLine_inf_commutator hK D.line] at this
    have hrX : (Subgroup.centralizer (E : Set G)).relIndex (Xq M) *
        Nat.card (MSP.fixSp (S5.imSp a E)) = 16 := by
      have : (Subgroup.centralizer (E : Set G)).relIndex (Xq M) *
          Nat.card (MSP.fixSp (S5.imSp a E)) * Nat.card ↥(Zq M L) = 16 * Nat.card ↥(Zq M L) := by
        rw [mul_assoc]
        exact hX
      exact Nat.eq_of_mul_eq_mul_right hZpos this
    rcases hf with h2 | h4' | h8
    ·
      exfalso
      have h8' : Nat.card (MSP.fixSp (S5.imSp a E)) = 8 := by
        rcases hc with h1 | h1 | h1 | h1 <;> rw [h1] at hrX ⊢ <;> omega
      have hd3 : Module.finrank F (MSP.fixSp (S5.imSp a E)) = 3 := by
        rw [hfix] at h8'
        have : (2 : ℕ) ^ Module.finrank F (MSP.fixSp (S5.imSp a E)) = 2 ^ 3 := by rw [h8']; norm_num
        exact Nat.pow_right_injective (le_refl 2) this
      obtain ⟨p, hp, hpE⟩ := MSP.eq_xPoint_of_finrank_fixSp_three hd3 (by rw [hK, h2])
      exact MSP.xPoint_not_le_commutator hK hp (hpE ▸ he)
    · refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [MSP.card_qLine_inf_commutator hK D.line, h4']
    · omega
  ·
    exfalso
    obtain ⟨_, ⟨x, hx, rfl⟩, hxo⟩ := Set.not_subset.1 he
    have hZ := S5Q2.inf_centralizer_eq_of_not_mem h D.sp4 hEM (Subgroup.mem_subgroupOf.1 hx)
      hxo
    rw [hZ] at hX
    have hZ2 : 2 * Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (M : Set G)) ≤ Nat.card ↥(Zq M L) :=
      two_mul_card_le inf_le_left fun heq => D.notCent (heq ▸ inf_le_right)
    have hpos : 0 < Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (M : Set G)) := Nat.card_pos
    have h32 : 32 ≤ (Subgroup.centralizer (E : Set G)).relIndex (Xq M) *
        Nat.card (MSP.fixSp (S5.imSp a E)) := by
      by_contra hcon
      push Not at hcon
      have : (Subgroup.centralizer (E : Set G)).relIndex (Xq M) *
          Nat.card (MSP.fixSp (S5.imSp a E)) *
          Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (M : Set G)) <
          32 * Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (M : Set G)) :=
        Nat.mul_lt_mul_of_pos_right hcon hpos
      rw [mul_assoc, hX] at this
      omega
    have hE'T : E ⊔ pCoreOf 2 M ≤ T := sup_le hET h.pCore_le
    have hE'M : E ⊔ pCoreOf 2 M ≤ M := hE'T.trans h.le
    have hE'im : S5.imSp a (E ⊔ pCoreOf 2 M) = S5.imSp a E := imSp_sup_pCore h D hEM
    have hrel' : (pCoreOf 2 M).relIndex (E ⊔ pCoreOf 2 M) = Nat.card (S5.imSp a E) := by
      rw [← D.sp4.card_imSp h hE'T, hE'im]
    have hU := relIndex_U_mul h D hE'M
    rw [hE'im] at hU
    have hQE' : pCoreOf 2 M ≤ E ⊔ pCoreOf 2 M := le_sup_right
    have hcE' : Nat.card ↥(E ⊔ pCoreOf 2 M) = Nat.card (S5.imSp a E) * Nat.card ↥(pCoreOf 2 M) := by
      rw [card_eq_relIndex_mul hQE', hrel']
    have hJ := card_jOffM h D
    have hQpos : 0 < Nat.card ↥(pCoreOf 2 M) := Nat.card_pos
    have hJE : S5.imSp a (S5.jOffM M T L 2) ≤ commutator (MSP.Sp4 F) := by
      rw [D.jEq]
      exact inf_le_right
    have hcand : (Subgroup.centralizer ((E ⊔ pCoreOf 2 M : Subgroup G) : Set G)).relIndex
          (Uq M T L) ≤ Nat.card (S5.imSp a E) →
        (Subgroup.centralizer ((E ⊔ pCoreOf 2 M : Subgroup G) : Set G)).relIndex
          (Uq M T L) ≤ 4 → S5.IsOffCandM M T L 2 (E ⊔ pCoreOf 2 M) := fun h1 h2 =>
      ⟨hE'T, by rw [hrel']; exact h1, by norm_num; exact h2⟩
    rcases hf with hf | hf | hf <;> rcases hc with h1 | h1 | h1 | h1 <;>
      rw [h1] at h32 hU <;> rw [hf] at hineq hcand hcE' <;> try omega
    ·
      have hle := D.le_of_cand (hcand (by omega) (by omega)) (by rw [hJ, hcE'])
      have hle' : S5.imSp a E ≤ S5.imSp a (S5.jOffM M T L 2) := by
        rw [← hE'im]
        exact S5.imSp_mono a hle
      exact he (hle'.trans hJE)
    ·
      have := D.card_le_of_cand (hcand (by omega) (by omega))
      rw [hJ, hcE'] at this
      omega
    ·
      have := D.card_le_of_cand (hcand (by omega) (by omega))
      rw [hJ, hcE'] at this
      omega

include h D in
theorem mem_of_imSp_mem {E : Subgroup G} {y : G} (hyT : y ∈ T) (hET : E ≤ T)
    (hQ : pCoreOf 2 M ≤ E) (hy : a ⟨y, h.le hyT⟩ ∈ S5.imSp a E) : y ∈ E := by
  obtain ⟨m, hm, hme⟩ := hy
  have hmE : (m : G) ∈ E := Subgroup.mem_subgroupOf.1 hm
  have hk : (m : G)⁻¹ * y ∈ T ⊓ S5.kerG a := by
    refine ⟨T.mul_mem (T.inv_mem (hET hmE)) hyT, (S5.mem_kerG a).2 ⟨M.mul_mem
      (M.inv_mem m.2) (h.le hyT), ?_⟩⟩
    have e1 : (⟨(m : G)⁻¹ * y, M.mul_mem (M.inv_mem m.2) (h.le hyT)⟩ : ↥M) =
        m⁻¹ * ⟨y, h.le hyT⟩ := rfl
    rw [e1, map_mul, map_inv, hme, inv_mul_cancel]
  rw [D.sp4.inf_kerG h] at hk
  have := E.mul_mem hmE (hQ hk)
  rwa [mul_inv_cancel_left] at this

include h D in
theorem relIndex_eq_four {E : Subgroup G} (hE : IsXOff M T E) :
    (pCoreOf 2 M).relIndex E = 4 := by
  rw [← D.sp4.card_imSp h hE.1, imSp_eq_of_isXOff h D hE]
  exact MSP.card_qLine_inf_commutator D.card_F D.line

include h D in
theorem relIndex_X_eq_four {E : Subgroup G} (hE : IsXOff M T E) :
    (Subgroup.centralizer (E : Set G)).relIndex (Xq M) = 4 := by
  have hK := D.card_F
  have hEM : E ≤ M := hE.1.trans h.le
  have hX := relIndex_X_mul h D hEM
  have hEim := imSp_eq_of_isXOff h D hE
  have hZ : Zq M L ≤ Subgroup.centralizer (E : Set G) :=
    S5Q2.le_centralizer_of_mem_commutator h D.sp4 hEM fun x hx => by
      have hx' : a ⟨x, hEM hx⟩ ∈ S5.imSp a E := ⟨⟨x, hEM hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [hEim] at hx'
      exact hx'.2
  rw [inf_of_le_left hZ, hEim, fixSp_qLine_inf_commutator hK D.line,
    Module.natCard_eq_pow_finrank (K := F), D.line.1, hK] at hX
  have hZpos : 0 < Nat.card ↥(Zq M L) := Nat.card_pos
  have h1 : (Subgroup.centralizer (E : Set G)).relIndex (Xq M) * 4 * Nat.card ↥(Zq M L) =
      16 * Nat.card ↥(Zq M L) := by
    rw [mul_assoc]
    exact hX
  have h2 := Nat.eq_of_mul_eq_mul_right hZpos h1
  omega

include h D in
theorem xOffCent : XOffCent M T := by
  rintro E hE y ⟨hyT, hyC⟩
  have hK := D.card_F
  have : CharP F 2 := D.charP
  have hEM : E ≤ M := hE.1.trans h.le
  have hEim := imSp_eq_of_isXOff h D hE
  have hyM : y ∈ M := h.le hyT
  have hT2 : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hinv : ∀ r ∈ S5.imSp a T, ∀ w ∈ l, MSP.mat r *ᵥ w ∈ l :=
    fun r hr w hw => MSP.mulVec_mem_of_mem_stab (D.tStab hr) hw
  have hl0 : l ≠ ⊥ := by
    rintro rfl
    have := D.line.1
    rw [finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨w, hwl, hw0, hwfix⟩ := MSP.exists_fixed_ne_zero hT2 hl0 hinv
  have hyim : a ⟨y, hyM⟩ ∈ S5.imSp a T := ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.2 hyT, rfl⟩
  have hq : a ⟨y, hyM⟩ ∈ MSP.qLine l := by
    refine mem_qLine_of_centralizer hK D.line (D.tStab hyim) hwl hw0 (hwfix _ hyim) ?_
    intro e he
    rw [← hEim] at he
    obtain ⟨m, hm, rfl⟩ := he
    have hmE : (m : G) ∈ E := Subgroup.mem_subgroupOf.1 hm
    have hc : (m : G) * y = y * m := Subgroup.mem_centralizer_iff.1 hyC m hmE
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc.symm
  have hmem : a ⟨y, hyM⟩ ∈ S5.imSp a (E ⊔ pCoreOf 2 M) := by
    rw [imSp_sup_pCore h D hEM, hEim, ← imSp_T_inf_qLine h D]
    exact ⟨hyim, hq⟩
  exact mem_of_imSp_mem h D hyT (sup_le hE.1 h.pCore_le) le_sup_right hmem

include h D in
theorem xOffData : XOffData M T := by
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => xOffCent h D F hF ⟨hy, hyC⟩)
  · have e : S5.imSp a (F₁ ⊔ pCoreOf 2 M) = S5.imSp a (F₂ ⊔ pCoreOf 2 M) := by
      rw [imSp_sup_pCore h D (h₁.1.trans h.le), imSp_sup_pCore h D (h₂.1.trans h.le),
        imSp_eq_of_isXOff h D h₁, imSp_eq_of_isXOff h D h₂]
    exact le_antisymm
      (le_of_imSp_le h D (sup_le h₁.1 h.pCore_le) (sup_le h₂.1 h.pCore_le) le_sup_right e.le)
      (le_of_imSp_le h D (sup_le h₂.1 h.pCore_le) (sup_le h₁.1 h.pCore_le) le_sup_right e.ge)
  · rw [relIndex_eq_four h D hF]
    exact relIndex_X_eq_four h D hF

include h D in
theorem four_le_relIndex {t : G} (htT : t ∈ T) (htO : t ∉ pCoreOf 2 M) :
    4 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Uq M T L) := by
  have hK := D.card_F
  have : CharP F 2 := D.charP
  have hET : Subgroup.zpowers t ≤ T := (Subgroup.zpowers_le).2 htT
  have hEM : Subgroup.zpowers t ≤ M := hET.trans h.le
  have hRb : S5.imSp a (Subgroup.zpowers t) ≠ ⊥ := fun hb =>
    htO (le_pCore_of_imSp_eq_bot h D hET hb (Subgroup.mem_zpowers t))
  have hRT : S5.imSp a (Subgroup.zpowers t) ≤ S5.imSp a T := S5.imSp_mono a hET
  have hU := relIndex_U_mul h D hEM
  have hfix := card_fixSp_eq D (S5.imSp a (Subgroup.zpowers t))
  have hd4 : Module.finrank F (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) ≤ 4 :=
    finrank_fixSp_le _
  have hd4' : Module.finrank F (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) ≠ 4 := fun h4 =>
    hRb (eq_bot_of_finrank_fixSp_four h4)
  have hd3 : Module.finrank F (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) ≠ 3 := by
    intro h3
    have h2 : Nat.card F ≤ Nat.card (S5.imSp a (Subgroup.zpowers t)) := by
      rw [hK]
      have := (Subgroup.one_lt_card_iff_ne_bot _).2 hRb
      omega
    obtain ⟨p, hp, hpE⟩ := MSP.eq_xPoint_of_finrank_fixSp_three h3 h2
    have hst : MSP.xPoint p ≤ MSP.stab l := hpE ▸ hRT.trans D.tStab
    have hpl := (MSP.xPoint_le_stab_iff hp D.line).1 hst
    have hQ : S5.imSp a (Subgroup.zpowers t) ≤ MSP.qLine l :=
      hpE ▸ MSP.xPoint_le_qLine D.line hpl
    have hRE : S5.imSp a (Subgroup.zpowers t) ≤ MSP.qLine l ⊓ commutator (MSP.Sp4 F) := by
      rw [← imSp_T_inf_qLine h D]
      exact le_inf hRT hQ
    exact MSP.xPoint_not_le_commutator hK hp (hpE ▸ hRE.trans inf_le_right)
  have hc : Nat.card (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) = 1 ∨
      Nat.card (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) = 2 ∨
      Nat.card (MSP.fixSp (S5.imSp a (Subgroup.zpowers t))) = 4 := by
    rw [hfix]
    interval_cases (Module.finrank F (MSP.fixSp (S5.imSp a (Subgroup.zpowers t)))) <;> simp_all
  rcases hc with hc | hc | hc <;> rw [hc] at hU <;> omega

include h D in
theorem exists_l {E : Subgroup G} (hE : IsXOff M T E) {m : G} (hm : m ∈ E) :
    ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
  have hmM : m ∈ M := hE.1.trans h.le hm
  have hLa := S5Q2.map_L_eq_commutator h D.sp4
  have hmc : a ⟨m, hmM⟩ ∈ commutator (MSP.Sp4 F) := by
    have hm' : a ⟨m, hmM⟩ ∈ S5.imSp a E := ⟨⟨m, hmM⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    rw [imSp_eq_of_isXOff h D hE] at hm'
    exact hm'.2
  rw [← hLa] at hmc
  obtain ⟨y, hy, hya⟩ := hmc
  let l₀ : ↥L := ⟨y, Subgroup.mem_subgroupOf.1 hy⟩
  let φ : ↥L →* ↥(StatedSp 2 F) := a.comp (Subgroup.inclusion h.L_le)
  have hφl₀ : φ l₀ = a ⟨m, hmM⟩ := hya
  have hm2 : φ l₀ ^ 2 ^ 1 = 1 := by
    rw [hφl₀, pow_one, pow_two, ← map_mul]
    have : (⟨m, hmM⟩ * ⟨m, hmM⟩ : ↥M) = 1 :=
      Subtype.ext (by simpa [pow_two] using hE.2.1.2 m hm)
    rw [this, map_one]
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt φ l₀ hm2
  refine ⟨l₀ ^ k, ⟨f, hf⟩, S5.kerG a, S5.kerG_le a, S5.le_normalizer_kerG a, fun hle => ?_, ?_⟩
  · obtain ⟨e, he, he1⟩ := Q2G.exists_ne_one D.card_F D.line
    have he2 := he.2
    rw [← hLa] at he2
    obtain ⟨y', hy', rfl⟩ := he2
    obtain ⟨hy'M, hy'1⟩ := (S5.mem_kerG a).1 (hle (Subgroup.mem_subgroupOf.1 hy'))
    exact he1 hy'1
  · refine (S5.mem_kerG a).2 ⟨M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM, ?_⟩
    have e : (⟨((l₀ ^ k : ↥L) : G)⁻¹ * m, M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM⟩ : ↥M) =
        (⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ : ↥M)⁻¹ * ⟨m, hmM⟩ := rfl
    rw [e, map_mul, map_inv]
    have : a ⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ = φ (l₀ ^ k) := rfl
    rw [this, hk, hφl₀, inv_mul_cancel]

end EvenData

end CFSG.Quasithin.MS93.Q2G
