module

public import CFSG.Quasithin.MS93.S5Q2Even
public import CFSG.Quasithin.MS93.S5A54
public import CFSG.Quasithin.MS93.S5BAux
public import CFSG.Quasithin.MS93.S5Q2V

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5

section GroupTheory

variable {Γ : Type*} [Group Γ]

private theorem card_sup_mul_card_inf' {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) :
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

end GroupTheory

section Count

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

include h in
theorem omegaOneCenterOf_eq_xq_inf_centralizer {J : Subgroup G} (hJM : J ≤ M)
    (hQJ : pCoreOf 2 M ≤ J) :
    omegaOneCenterOf J = Xq M ⊓ Subgroup.centralizer (J : Set G) := by
  apply le_antisymm
  · rw [omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
    rintro x ⟨⟨hxJ, hxC⟩, hx2⟩
    have hxQ : x ∈ pCoreOf 2 M := h.charTwo ⟨hJM hxJ, Subgroup.centralizer_le hQJ hxC⟩
    exact ⟨Subgroup.subset_closure ⟨⟨hxQ, Subgroup.centralizer_le hQJ hxC⟩, hx2⟩, hxC⟩
  · rintro x ⟨hxX, hxC⟩
    exact Subgroup.subset_closure ⟨⟨hQJ (Xq_le_pCoreOf M hxX), hxC⟩,
      S5Q2.sq_eq_one_of_mem_Xq hxX⟩

include h in
theorem card_uq_inf_centralizer (hd : IsSp4Data M T L k F a) {E : Subgroup G} (hEM : E ≤ M) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (E : Set G)) =
      Nat.card (MSP.fixSp (imSp a E)) *
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨-, hUL, hlift⟩ := sp4Lift G M T L h k F _ _ a hd
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  set CE : Subgroup ↥(Uq M T L) := (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L)
  have h1 := Subgroup.relIndex_mul_card (H := nv.toVec.ker) (K := CE)
  rw [Subgroup.relIndex_ker] at h1
  have hCE : Nat.card CE = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (E : Set G)) := by
    rw [card_subgroupOf, inf_comm]
  have hmap : Nat.card (CE.map nv.toVec) = Nat.card (MSP.fixSp (imSp a E)) := by
    let f : ↥(CE.map nv.toVec) → ↥(MSP.fixSp (imSp a E)) := fun x =>
      ⟨Multiplicative.toAdd (x : Multiplicative (MSP.V4 F)), by
        obtain ⟨_, ⟨u, hu, rfl⟩⟩ := x
        exact nv.vec_mem_fixSp u (Subgroup.mem_subgroupOf.1 hu)⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨fun x y hxy => ?_, fun v => ?_⟩)
    · apply Subtype.ext
      have hxy' := congrArg (fun z : ↥(MSP.fixSp (imSp a E)) => (z : MSP.V4 F)) hxy
      exact Multiplicative.toAdd.injective hxy'
    · obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd (v : MSP.V4 F))
      have hvu : nv.vec u = v := by rw [NatVec.vec, hu]; rfl
      have huE : (u : G) ∈ Subgroup.centralizer (E : Set G) :=
        (nv.mem_centralizer_iff_vec_mem_fixSp hUn hlift hEM u).2 (hvu ▸ v.2)
      refine ⟨⟨nv.toVec u, ⟨u, Subgroup.mem_subgroupOf.2 huE, rfl⟩⟩, Subtype.ext ?_⟩
      exact hvu
  have hker : nv.toVec.ker ⊓ CE = nv.toVec.ker := by
    refine inf_eq_left.2 fun u hu => Subgroup.mem_subgroupOf.2 ?_
    have hu' : (u : G) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := (nv.ker_iff u).1 hu
    rw [hUL] at hu'
    exact Subgroup.centralizer_le hEM hu'.2
  have hkc : Nat.card nv.toVec.ker = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    have hk : nv.toVec.ker = (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
      ext u
      rw [MonoidHom.mem_ker, nv.ker_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h' => h'.2, fun h' => ⟨u.2, h'⟩⟩
    rw [hk, card_subgroupOf, inf_comm]
  rw [← hCE, ← h1, hmap, hker, hkc]

include h in
theorem card_xq_inf_centralizer (hd : IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {J : Subgroup G} (hJM : J ≤ M) :
    Nat.card ↥(Xq M ⊓ Subgroup.centralizer (J : Set G)) =
      Nat.card (MSP.fixSp (imSp a J)) * Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (J : Set G)) := by
  obtain ⟨-, hUL, -⟩ := sp4Lift G M T L h k F _ _ a hd
  set A := Uq M T L ⊓ Subgroup.centralizer (J : Set G)
  set B := Zq M L ⊓ Subgroup.centralizer (J : Set G)
  have hsplit := S5Q2.xq_inf_centralizer_eq h hd hXU hJM
  have hcomm : ∀ {b y : G}, b ∈ Xq M → y ∈ Xq M → b * y * b⁻¹ = y := fun hb hy => by
    rw [S5Q2.mul_comm_of_mem_Xq hb hy, mul_inv_cancel_right]
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm hb.1.1 (h.Uq_le_Xq hx.1)]
      exact hx
    · intro hx
      have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = b * x * b⁻¹ :=
        hcomm (inv_mem hb.1.1) (h.Uq_le_Xq hx.1)
      have e' : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
      rw [← e', e]
      exact hx
  have hinf : A ⊓ B = Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    apply le_antisymm
    · rintro x ⟨⟨hxU, -⟩, ⟨⟨-, hxL⟩, -⟩⟩
      exact ⟨hxU, hxL⟩
    · intro x hx
      have hxM : x ∈ Uq M T L ⊓ Subgroup.centralizer (M : Set G) := hUL ▸ hx
      have hxJ : x ∈ Subgroup.centralizer (J : Set G) := Subgroup.centralizer_le hJM hxM.2
      exact ⟨⟨hx.1, hxJ⟩, ⟨⟨h.Uq_le_Xq hx.1, hx.2⟩, hxJ⟩⟩
  have h1 := card_sup_mul_card_inf' hBA
  rw [hinf, card_uq_inf_centralizer h hd hJM] at h1
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  rw [hsplit]
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  ring

include h in
theorem card_omegaOneCenterOf_imM {K : Subgroup G} (hKM : K ≤ M) :
    Nat.card ↥(omegaOneCenterOf (imM h.le K)) = Nat.card ↥(omegaOneCenterOf K) := by
  have hle : omegaOneCenterOf K ≤ M :=
    (PU.omegaOneCenterOf_le_centerOf K).trans (inf_le_left.trans hKM)
  have e : omegaOneCenterOf (imM h.le K) = imM h.le (omegaOneCenterOf K) := by
    rw [imM, imM, PU.omegaOneCenterOf_map (puAmalgam h.le).ofA_injective,
      PU.omegaOneCenterOf_subgroupOf hKM]
  rw [e, card_imM h.le hle]

theorem xm_ne_of_finrank_fixSp (hq55 : S5Q2.Q2Cent55) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hne : jOff h.le L (2 ^ k) δ (baseB _) ≠
      jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _))
    (hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ jOff h.le L (2 ^ k) δ (baseB _))
    (hline : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ vPre h.le a (MSP.stab l) ∧
      jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ vPre h.le a (MSP.qLine l))
    (hfα : Module.finrank F (MSP.fixSp
      (vIm h.le a (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)))) = 2)
    (hfδ : Module.finrank F (MSP.fixSp (vIm h.le a (jOff h.le L (2 ^ k) δ (baseB _)))) = 1) :
    XM _ (baseA (puAmalgam h.le)) ≠ uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
  intro hX
  have := hd.charP
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hZM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  have hXU : Xq M = Uq M T L ⊔ Zq M L := by
    have hZ : imM h.le (Zq M L) = XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
      rw [xm_baseA_eq h, puTrans_L_baseA h, ← imM_inf_centralizer h.le _ h.L_le]
    have e : imM h.le (Xq M) = imM h.le (Uq M T L ⊔ Zq M L) := by
      rw [imM_sup_of_le h (Uq_le h.L_le) hZM, ← uSub_baseA h, hZ, ← xm_baseA_eq h]
      exact hX
    exact le_antisymm ((imM_le_imM_iff h.le (Xq_le M)).1 e.le)
      ((imM_le_imM_iff h.le (sup_le (Uq_le h.L_le) hZM)).1 e.ge)
  have hTβ : Qv _ (baseB (puAmalgam h.le)) ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact qv_le_stab_of_adj _ (adj_baseA_baseB _).symm
  have hJst : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le M :=
    (iSup₂_le fun _ hE => hE.1.1).trans hTβ
  have hDst : jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) ≤ imM h.le M :=
    (iSup₂_le fun _ hE => hE.1.1).trans hTβ
  obtain ⟨J₀, -, hJ₀M, hJ₀⟩ := exists_eq_imM h.le hJst
  obtain ⟨D₀, -, hD₀M, hD₀⟩ := exists_eq_imM h.le hDst
  have hQJ₀ : pCoreOf 2 M ≤ J₀ := by
    have h1 := S5B.qv_le_jOff (L := L) h (q := 2 ^ k) Nat.one_le_two_pow hα (adj_baseA_baseB _)
    rw [qv_baseA_eq h, hJ₀] at h1
    exact (imM_le_imM_iff h.le (pCoreOf_le' M)).1 h1
  have hQD₀ : pCoreOf 2 M ≤ D₀ := by
    have h1 := hQJ
    rw [qv_baseA_eq h, hD₀] at h1
    exact (imM_le_imM_iff h.le (pCoreOf_le' M)).1 h1
  obtain ⟨y, hy, hyα⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
  have hyβ : y • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hy
  have hJδ : jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) =
      (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map (MulAut.conj y).toMonoidHom := by
    rw [← jOff_smul h.le hLn, hyα, hyβ]
  have hcard : Nat.card ↥(omegaOneCenterOf D₀) = Nat.card ↥(omegaOneCenterOf J₀) := by
    rw [← card_omegaOneCenterOf_imM h hD₀M, ← card_omegaOneCenterOf_imM h hJ₀M, ← hD₀, ← hJ₀,
      hJδ, PU.omegaOneCenterOf_map (MulAut.conj y).injective, card_map_conj]
  rw [omegaOneCenterOf_eq_xq_inf_centralizer h hD₀M hQD₀,
    omegaOneCenterOf_eq_xq_inf_centralizer h hJ₀M hQJ₀, card_xq_inf_centralizer h hd hXU hD₀M,
    card_xq_inf_centralizer h hd hXU hJ₀M, MSP.card_fixSp, MSP.card_fixSp, ← vIm_imM h,
    ← vIm_imM h, ← hD₀, ← hJ₀, hfδ, hfα] at hcard
  have hZpos : 0 < Nat.card ↥(Zq M L) := Nat.card_pos
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hZD : Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (D₀ : Set G)) ≤ Nat.card ↥(Zq M L) :=
    Subgroup.card_le_of_le inf_le_left
  have hfull : ∀ {K : Subgroup G}, Zq M L ≤ Subgroup.centralizer (K : Set G) →
      Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (K : Set G)) = Nat.card ↥(Zq M L) := fun hK => by
    rw [inf_of_le_left hK]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
    rw [hq] at hcard
    by_cases hJe : vIm h.le a (jOff h.le L (2 ^ 1) (baseA (puAmalgam h.le)) (baseB _)) ≤
        commutator (MSP.Sp4 F)
    ·
      have hC : Zq M L ≤ Subgroup.centralizer (J₀ : Set G) :=
        S5Q2.le_centralizer_of_mem_commutator h hd hJ₀M fun j hj => by
          rw [hJ₀, vIm_imM h] at hJe
          exact hJe ⟨⟨j, hJ₀M hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      rw [hfull hC] at hcard
      nlinarith
    · obtain ⟨_, ⟨j, hj, rfl⟩, hjo⟩ := Set.not_subset.1 (by rwa [hJ₀, vIm_imM h] at hJe)
      have hj' : (j : G) ∈ J₀ := Subgroup.mem_subgroupOf.1 hj
      have hJC := S5Q2.inf_centralizer_eq_of_not_mem h hd hJ₀M hj' hjo
      by_cases hDe : vIm h.le a (jOff h.le L (2 ^ 1) δ (baseB _)) ≤ commutator (MSP.Sp4 F)
      ·
        have hZc := hq55 G M T L h hmin hb F _ _ a hd δ hβδ (by simpa using hne)
          (by simpa using hQJ) (by simpa using hline) (by simpa using hJe) (by simpa using hDe)
        rw [hfull (hZc.trans (Subgroup.centralizer_le hJ₀M)),
          hfull (hZc.trans (Subgroup.centralizer_le hD₀M))] at hcard
        nlinarith
      · obtain ⟨_, ⟨d, hdD, rfl⟩, hdo⟩ := Set.not_subset.1 (by rwa [hD₀, vIm_imM h] at hDe)
        have hDC := S5Q2.inf_centralizer_eq_of_not_mem h hd hD₀M
          (Subgroup.mem_subgroupOf.1 hdD) hdo
        rw [hJC, hDC] at hcard
        have : 0 < Nat.card ↥(Zq M L ⊓ Subgroup.centralizer (M : Set G)) := Nat.card_pos
        nlinarith
  · have hZc := S5Q2.zq_le_centralizer_of_two_le h hd hk
    rw [hfull (hZc.trans (Subgroup.centralizer_le hJ₀M)),
      hfull (hZc.trans (Subgroup.centralizer_le hD₀M))] at hcard
    have h2 : Nat.card F ^ 1 * Nat.card ↥(Zq M L) < Nat.card F ^ 2 * Nat.card ↥(Zq M L) :=
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hq1 (by norm_num)) hZpos
    omega

end Count

end S5

end CFSG.Quasithin.MS93
