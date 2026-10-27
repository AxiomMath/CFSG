module

public import CFSG.Quasithin.MS93.S5Q2OddB
public import CFSG.Quasithin.MS93.S5Q2Even
public import CFSG.Quasithin.MS93.S5Q2Odd

public section

namespace CFSG.Quasithin.MS93.S5Q2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace UC

section Group

omit [Finite G] in
private theorem relIndex_le_two_of_forall' {H H' : Subgroup G}
    (hH : ∀ g ∈ H', ∀ g' ∈ H', g ∉ H → g' ∉ H → g⁻¹ * g' ∈ H) : H.relIndex H' ≤ 2 := by
  by_cases htop : H.subgroupOf H' = ⊤
  · rw [Subgroup.relIndex, htop, Subgroup.index_top]
    omega
  · have hex : ∃ x : H', x ∉ H.subgroupOf H' := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun x _ => hcon x)
    obtain ⟨x, hx⟩ := hex
    have h2 : (H.subgroupOf H').index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨x, fun y => ?_⟩
      by_cases hy : y ∈ H.subgroupOf H'
      · refine Or.inr ⟨hy, fun hyx => hx ?_⟩
        have := (H.subgroupOf H').mul_mem ((H.subgroupOf H').inv_mem hy) hyx
        simpa using this
      · refine Or.inl ⟨?_, hy⟩
        rw [Subgroup.mem_subgroupOf] at hy hx ⊢
        have hyinv : (y : G)⁻¹ ∉ H := fun hh => hy (by simpa using H.inv_mem hh)
        have := hH (y : G)⁻¹ (H'.inv_mem y.2) (x : G) x.2 hyinv hx
        simpa using this
    rw [Subgroup.relIndex, h2]

theorem exists_mul_of_mem_xq (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L) {x : G}
    (hx : x ∈ Xq M) : ∃ u ∈ Uq M T L, ∃ z ∈ Zq M L, u * z = x := by
  have hn : Uq M T L ≤ Subgroup.normalizer (Zq M L : Set G) :=
    (Uq_le h.L_le).trans (le_normalizer_Zq h.le_normalizer)
  rw [hXU, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx
  obtain ⟨u, hu, z, hz, rfl⟩ := hx
  exact ⟨u, hu, z, hz, rfl⟩

theorem comm_mem_zq (h : PUHyp M T L) {m z : G} (hm : m ∈ M) (hz : z ∈ Zq M L) :
    ⁅m, z⁆ ∈ Zq M L := by
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.1 (le_normalizer_Zq h.le_normalizer hm) z).1 hz)
    (inv_mem hz)

theorem comm_eq_one_of_mem_zq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a) {m u : G}
    (hm : m ∈ M) (hu : u ∈ Uq M T L) (hmu : ⁅m, u⁆ ∈ Zq M L) : ⁅m, u⁆ = 1 := by
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  have e := hlift m hm u hu (by rw [← commutatorElement_def]; exact hmu.2)
  rw [commutatorElement_def, e, mul_inv_cancel]

theorem exists_comm_iff_of_comm_not_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {c d : G} (hc : c ∈ Xq M) (hdZ : d ∉ Zq M L)
    (hP : ∀ t ∈ T, ⁅t, c⁆ = 1 ∨ ⁅t, c⁆ = d) :
    ∃ u ∈ Uq M T L, ∀ t ∈ T, (⁅t, c⁆ = 1 ↔ ⁅t, u⁆ = 1) := by
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_xq h hXU hc
  refine ⟨u, hu, fun t htT => ?_⟩
  have htz : ⁅t, z⁆ ∈ Zq M L := comm_mem_zq h (h.le htT) hz
  have e : ⁅t, u * z⁆ = ⁅t, u⁆ * ⁅t, z⁆ := X52.comm_mul_eq (h.Uq_le_Xq hu) htz.1
  constructor
  · intro h1
    refine comm_eq_one_of_mem_zq h hd (h.le htT) hu ?_
    rw [e] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem htz
  · intro h1
    rcases hP t htT with h2 | h2
    · exact h2
    · exfalso
      apply hdZ
      rw [← h2, e, h1, one_mul]
      exact htz

theorem relIndex_centralizer_zq_eq_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    (Subgroup.centralizer (Zq M L : Set G)).relIndex T = 2 := by
  have hodd : ∀ t (ht : t ∈ M), t ∉ Subgroup.centralizer (Zq M L : Set G) →
      a ⟨t, ht⟩ ∉ commutator (MSP.Sp4 F) := fun t ht htC hmc =>
    htC (Subgroup.mem_centralizer_iff.2 fun x hx =>
      (S5Q2.commute_of_mem_commutator h hd hmc hx).symm)
  have hle : (Subgroup.centralizer (Zq M L : Set G)).relIndex T ≤ 2 := by
    refine relIndex_le_two_of_forall' fun t ht t' ht' h1 h2 => ?_
    have e1 := hodd t (h.le ht) h1
    have e2 := hodd t' (h.le ht') h2
    have hm : a (⟨t, h.le ht⟩⁻¹ * ⟨t', h.le ht'⟩) ∈ commutator (MSP.Sp4 F) := by
      rw [map_mul, map_inv]
      exact S5Q2.mul_mem_commutator_of_not_mem hd (fun h' => e1 (by simpa using h')) e2
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      (S5Q2.commute_of_mem_commutator h hd hm hx).symm
  have hne1 : (Subgroup.centralizer (Zq M L : Set G)).relIndex T ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    obtain ⟨t, htT, hto⟩ := S5Q2.exists_mem_T_not_mem_commutator h hd
    exact hC fun c hc => S5Q2.mem_centralizer_of_commute h hd hto hc
      (Subgroup.mem_centralizer_iff.1 (h1 htT) c hc).symm
  have hne0 : (Subgroup.centralizer (Zq M L : Set G)).relIndex T ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  omega

theorem relIndex_centralizer_le_four (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {u : G} (hu : u ∈ Uq M T L) (huT : u ∉ Subgroup.centralizer (T : Set G))
    {K : Subgroup G} (hKT : K ≤ T) (hKu : K ≤ Subgroup.centralizer ({u} : Set G)) :
    (Subgroup.centralizer (K : Set G)).relIndex (Uq M T L) ≤ 4 := by
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  obtain ⟨cc⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hFq : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hKM : K ≤ M := hKT.trans h.le
  have hrel := S5B.relIndex_centralizer_mul_card h hlift cc hKM
  have hAB : (K.subgroupOf M).map a ≤ (T.subgroupOf M).map a :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (hKT (Subgroup.mem_subgroupOf.1 hx))
  have hB2 : IsPGroup 2 ((T.subgroupOf M).map a) :=
    (h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm).map a
  have hvA : cc.vec ⟨u, hu⟩ ∈ MSP.fixSp ((K.subgroupOf M).map a) := by
    rw [← S5B.mem_centralizer_iff_vec h hlift cc hKM]
    exact Subgroup.mem_centralizer_iff.2 fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.1 (hKu hk)
  have hvB : cc.vec ⟨u, hu⟩ ∉ MSP.fixSp ((T.subgroupOf M).map a) := by
    rw [← S5B.mem_centralizer_iff_vec h hlift cc h.le]
    exact huT
  have hlt : MSP.fixSp ((T.subgroupOf M).map a) <
      MSP.fixSp ((T.subgroupOf M).map a) ⊔ Submodule.span F {cc.vec ⟨u, hu⟩} := by
    refine lt_of_le_of_ne le_sup_left fun e => hvB ?_
    rw [e]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hle : MSP.fixSp ((T.subgroupOf M).map a) ⊔ Submodule.span F {cc.vec ⟨u, hu⟩} ≤
      MSP.fixSp ((K.subgroupOf M).map a) :=
    sup_le (MSP.fixSp_antitone hAB) ((Submodule.span_singleton_le_iff_mem _ _).2 hvA)
  have h1 := S5.finrank_pos_of_ne_bot (S5.fixSp_ne_bot hB2)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 := Submodule.finrank_mono hle
  have hcard : 2 ^ 2 ≤ Nat.card (MSP.fixSp ((K.subgroupOf M).map a)) := by
    rw [MSP.card_fixSp, hFq]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [MSP.card_V4, hFq] at hrel
  nlinarith

theorem comm_eq_one_of_comm_mem_z0q (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {c d : G} (hcZ : c ∈ Z0q M T) (hc : c ∈ Xq M)
    (hdZ : d ∈ Zq M L) (hP : ∀ t ∈ T, ⁅t, c⁆ = 1 ∨ ⁅t, c⁆ = d) {t : G} (ht : t ∈ T) :
    ⁅t, c⁆ = 1 := by
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_xq h hXU hc
  have hzZ : z ∈ Z0q M T := by
    have e : z = u⁻¹ * (u * z) := by group
    rw [e]
    exact mul_mem (inv_mem (Uq_le_Z0q h.L_le hu)) hcZ
  have htz : ⁅t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (Subgroup.mem_centralizer_iff.1 (z0q_inf_zq_le h hd ⟨hzZ, hz⟩) t (h.le ht))
  have e : ⁅t, u * z⁆ = ⁅t, u⁆ := by
    rw [X52.comm_mul_eq (h.Uq_le_Xq hu) (by rw [htz]; exact one_mem _), htz, mul_one]
  rw [e]
  refine comm_eq_one_of_mem_zq h hd (h.le ht) hu ?_
  rw [← e]
  rcases hP t ht with h1 | h1 <;> rw [h1]
  · exact one_mem _
  · exact hdZ

end Group

omit [Finite G] in
private theorem eq_of_relIndex_eq_two' {Γ : Type*} [Group Γ] {H K N : Subgroup Γ} (hHK : H ≤ K)
    (hKN : K ≤ N) (hNK : ¬ N ≤ K) (h2 : H.relIndex N = 2) : H = K := by
  have e := Subgroup.relIndex_mul_relIndex H K N hHK hKN
  rw [h2] at e
  have h1 : K.relIndex N ≠ 1 := fun h1 => hNK (Subgroup.relIndex_eq_one.1 h1)
  have h3 : H.relIndex K = 1 := by
    rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | h0
    · rw [h0, zero_mul] at e; omega
    · rcases Nat.eq_zero_or_pos (K.relIndex N) with h0' | h0'
      · rw [h0', mul_zero] at e; omega
      · have : H.relIndex K * K.relIndex N = 2 := e
        have hle : H.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ this)
        interval_cases (H.relIndex K)
        · rfl
        · omega
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.1 h3)

section Vertex

variable (h : PUHyp M T L)

theorem exists_pullback (hd : S5.IsSp4Data M T L 1 F a) {γ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) {c t₁ : (puAmalgam h.le).Universal}
    (hcC : c ∈ XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal))
    (hcX : c ∈ XM _ (baseA (puAmalgam h.le))) (ht₁ : t₁ ∈ Qv _ (baseB (puAmalgam h.le)))
    (hd1 : ⁅t₁, c⁆ ≠ 1) :
    ∃ c₀ t₁₀ : ↥M, (puAmalgam h.le).ofA c₀ = c ∧ (puAmalgam h.le).ofA t₁₀ = t₁ ∧
      (c₀ : G) ∈ Xq M ∧ (t₁₀ : G) ∈ T ∧ ⁅(t₁₀ : G), (c₀ : G)⁆ ≠ 1 ∧
      (⁅t₁, c⁆ ∈ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
          (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ↔
        ⁅(t₁₀ : G), (c₀ : G)⁆ ∈ Zq M L) ∧
      (∀ t ∈ T, ⁅t, (c₀ : G)⁆ = 1 ∨ ⁅t, (c₀ : G)⁆ = ⁅(t₁₀ : G), (c₀ : G)⁆) ∧
      ∀ t (ht : t ∈ T), ((puAmalgam h.le).ofA ⟨t, h.le ht⟩ ∈ Qv _ (baseB (puAmalgam h.le)) ⊓
          Subgroup.centralizer ((XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ :
            Set (puAmalgam h.le).Universal) : Subgroup _) : Set (puAmalgam h.le).Universal) ↔
        ⁅t, (c₀ : G)⁆ = 1) := by
  have hγM : IsMVtx _ γ := (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hTstγ : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hct₁ : t₁ * c ≠ c * t₁ := fun e => hd1 (commutatorElement_eq_one_iff_mul_comm.2 e)
  have hKiff : ∀ t ∈ Qv _ (baseB (puAmalgam h.le)), (t ∈ Qv _ (baseB (puAmalgam h.le)) ⊓
      Subgroup.centralizer ((XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ :
        Set (puAmalgam h.le).Universal) : Subgroup _) : Set (puAmalgam h.le).Universal) ↔
      ⁅t, c⁆ = 1) := by
    intro t ht
    constructor
    · intro htK
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 htK.2 c hcC).symm
    · intro h1
      by_contra htK
      have htC : t ∉ Subgroup.centralizer ((XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ :
          Set (puAmalgam h.le).Universal) : Subgroup _) : Set (puAmalgam h.le).Universal) :=
        fun htC => htK ⟨ht, htC⟩
      have hEst : Subgroup.zpowers t ≤ stab _ γ := (Subgroup.zpowers_le).2 (hTstγ ht)
      have hEC : ¬ XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ :
          Set (puAmalgam h.le).Universal) ≤ Subgroup.centralizer
            ((Subgroup.zpowers t : Subgroup _) : Set (puAmalgam h.le).Universal) := by
        intro hle'
        apply htC
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.1 (hle' hx) t (Subgroup.mem_zpowers t)).symm
      have hcz : c ∈ Subgroup.centralizer
          ((Subgroup.zpowers t : Subgroup _) : Set (puAmalgam h.le).Universal) := by
        have htc : t ∈ Subgroup.centralizer ({c} : Set (puAmalgam h.le).Universal) :=
          Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h1)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.zpowers_le).2 htc hy)
      have hcZ := cX_inf_centralizer_le_stabCenter h hd hγM hEst hEC ⟨hcC, hcz⟩
      obtain ⟨w, hw, hwc⟩ := hcZ
      apply hct₁
      rw [← hwc]
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨t₁, hTstγ ht₁⟩))
  have hP : ∀ t ∈ Qv _ (baseB (puAmalgam h.le)), ⁅t, c⁆ = 1 ∨ ⁅t, c⁆ = ⁅t₁, c⁆ := by
    intro t ht
    rcases comm_eq_or_vtx h hd hγM hcC (hTstγ ht) (hTstγ ht₁) with h1 | h1 | h1
    · left
      rw [← commutatorElement_inv c t, h1, inv_one]
    · exact (hd1 (by rw [← commutatorElement_inv c t₁, h1, inv_one])).elim
    · right
      rw [← commutatorElement_inv c t, h1, commutatorElement_inv]
  have hcX' : c ∈ imM h.le (Xq M) := by
    rw [← S5B.xm_baseA_eq h]
    exact hcX
  obtain ⟨c₀, hc₀, rfl⟩ := hcX'
  have ht₁' : t₁ ∈ imM h.le T := by
    rw [← puAmalgam.qv_baseB]
    exact ht₁
  obtain ⟨t₁₀, ht₁₀, rfl⟩ := ht₁'
  have hmemT : ∀ t (ht : t ∈ T), (puAmalgam h.le).ofA ⟨t, h.le ht⟩ ∈
      Qv _ (baseB (puAmalgam h.le)) := fun t ht => by
    rw [puAmalgam.qv_baseB]
    exact ⟨⟨t, h.le ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have hconv : ∀ x y : ↥M, ⁅(puAmalgam h.le).ofA x, (puAmalgam h.le).ofA y⁆ =
      (puAmalgam h.le).ofA ⁅x, y⁆ := fun x y => (map_commutatorElement _ x y).symm
  have hcoe : ∀ x y : ↥M, ((⁅x, y⁆ : ↥M) : G) = ⁅(x : G), (y : G)⁆ := fun x y =>
    map_commutatorElement M.subtype x y
  have hinj := (puAmalgam h.le).ofA_injective
  refine ⟨c₀, t₁₀, rfl, rfl, Subgroup.mem_subgroupOf.1 hc₀, Subgroup.mem_subgroupOf.1 ht₁₀,
    fun e => hd1 ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hconv, map_eq_one_iff _ hinj, ← Subtype.coe_inj, hcoe, Subgroup.coe_one]
    exact e
  · rw [hconv, cX_baseA h, imM, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_subgroupOf, hcoe]
  · have := hP _ (hmemT t ht)
    rw [hconv, hconv, map_eq_one_iff _ hinj, hinj.eq_iff, ← Subtype.coe_inj,
      ← Subtype.coe_inj, hcoe, hcoe, Subgroup.coe_one] at this
    exact this
  · rw [hKiff _ (hmemT t ht), hconv, map_eq_one_iff _ hinj, ← Subtype.coe_inj, hcoe,
      Subgroup.coe_one]

theorem false_of_comm_not_mem (H55 : Q2Cent55) (h54 : S54) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    (hA : S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) ≠ Qv _ (baseB (puAmalgam h.le)))
    (hB : ¬ (S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
        commutator (MSP.Sp4 F) ∧
      (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)).relIndex
        (Qv _ (baseB (puAmalgam h.le))) = 2))
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    {c t₁ : (puAmalgam h.le).Universal}
    (hcC : c ∈ XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal))
    (hcX : c ∈ XM _ (baseA (puAmalgam h.le))) (ht₁ : t₁ ∈ Qv _ (baseB (puAmalgam h.le)))
    (hd1 : ⁅t₁, c⁆ ≠ 1)
    (hdC : ⁅t₁, c⁆ ∉ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal)) :
    False := by
  have h20 := h.hyp20
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβadj.symm hβγ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  obtain ⟨hcard1, ⟨l₁, hl₁, hT₁, hJl₁⟩, hJq⟩ := (h54 G M T L h hmin hb 1 F _ _ a hd).resolve_right
    fun ⟨_, _, p, hp, hTq⟩ => X52.vIm_qv_baseB_ne_qPoint h hd hC hp hTq
  simp only [pow_one] at hcard1 hJl₁ hJq
  norm_num at hJq
  obtain ⟨c₀, t₁₀, rfl, rfl, hc₀X, ht₁T, hd₀, hdiff, hP₀, hKiff₀⟩ :=
    exists_pullback h hd hβγ hcC hcX ht₁ hd1
  have hdZ : ⁅(t₁₀ : G), (c₀ : G)⁆ ∉ Zq M L := fun h' => hdC (hdiff.2 h')
  set Tβ := Qv _ (baseB (puAmalgam h.le)) with hTβ
  set Jα := S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) with hJα
  set Cα := XM _ (baseA (puAmalgam h.le)) ⊓
    Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) with hCα
  set Cγ := XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal)
    with hCγ
  set Kα := Tβ ⊓ Subgroup.centralizer (Cα : Set (puAmalgam h.le).Universal) with hKα
  set Kγ := Tβ ⊓ Subgroup.centralizer (Cγ : Set (puAmalgam h.le).Universal) with hKγ
  have hinj := (puAmalgam h.le).ofA_injective
  have hTst : Tβ ≤ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hαβadj.symm
  have hTfin : Finite ↥Tβ := finite_qv _ h20 (not_isMVtx_baseB _)
  have hJT : Jα ≤ Tβ := S5B.jOff_le_qv h.le L _ _ _
  have hJfin : Finite ↥Jα :=
    Finite.of_injective (Subgroup.inclusion hJT) (Subgroup.inclusion_injective hJT)
  have hQT : Qv _ (baseA (puAmalgam h.le)) ≤ Tβ := qv_le_qv _ h20 hα hαβadj
  have hKT : Kγ ≤ Tβ := inf_le_left
  have hKαT : Kα ≤ Tβ := inf_le_left
  have hCg : Cγ = Cα.map (MulAut.conj g).toMonoidHom := by
    rw [hCγ, hCα, ← hgα, cX_smul h]
  have hTg : Tβ.map (MulAut.conj g).toMonoidHom = Tβ := by
    rw [hTβ, ← qv_smul, hgβ]
  have hKg : Kγ = Kα.map (MulAut.conj g).toMonoidHom := by
    rw [hKγ, hKα, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hTg,
      ← PU.centralizer_map_mulEquiv, ← hCg]
  have hK2 : Kα.relIndex Tβ = 2 := by
    rw [hKα, Subgroup.inf_relIndex_left, hCα, cX_baseA h, hTβ, puAmalgam.qv_baseB,
      S5B.relIndex_centralizer_imM h.le h.le Zq_le]
    exact relIndex_centralizer_zq_eq_two h hd hC
  have hKγ2 : Kγ.relIndex Tβ = 2 := by
    rw [hKg, ← hTg, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hK2
  have hTKα : ¬ Tβ ≤ Kα := fun h' => by
    have := Subgroup.relIndex_eq_one.2 h'
    omega
  have hKe : S5.vIm h.le a Kα ≤ commutator (MSP.Sp4 F) := by
    rintro _ ⟨m, hm, rfl⟩
    by_contra hodd
    refine hC fun z hz => S5Q2.mem_centralizer_of_commute h hd hodd hz ?_
    have h1 : (puAmalgam h.le).ofA ⟨z, Zq_le hz⟩ ∈ Cα := by
      rw [hCα, cX_baseA h]
      exact ⟨⟨z, Zq_le hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hm).2 _ h1
    have h3 : (⟨z, Zq_le hz⟩ : ↥M) * m = m * ⟨z, Zq_le hz⟩ :=
      hinj (by rw [map_mul, map_mul]; exact h2)
    exact (congrArg Subtype.val h3).symm
  obtain ⟨u₀, hu₀, hiff⟩ := exists_comm_iff_of_comm_not_mem h hd hXU hc₀X hdZ hP₀
  have hK₀M : T ⊓ Subgroup.centralizer ({u₀} : Set G) ≤ M := inf_le_left.trans h.le
  have hKγ₀ : Kγ = imM h.le (T ⊓ Subgroup.centralizer ({u₀} : Set G)) := by
    apply le_antisymm
    · intro x hx
      have hxT : x ∈ imM h.le T := by
        rw [← puAmalgam.qv_baseB]
        exact hx.1
      obtain ⟨x₀, hx₀, rfl⟩ := hxT
      have hx₀T := Subgroup.mem_subgroupOf.1 hx₀
      refine ⟨x₀, Subgroup.mem_subgroupOf.2 ⟨hx₀T, ?_⟩, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1
        ((hiff _ hx₀T).1 ((hKiff₀ _ hx₀T).1 hx)))
    · rintro _ ⟨x₀, hx₀, rfl⟩
      have hx₀' := Subgroup.mem_subgroupOf.1 hx₀
      exact (hKiff₀ _ hx₀'.1).2 ((hiff _ hx₀'.1).2 (commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_singleton_iff.1 hx₀'.2)))
  have huT : u₀ ∉ Subgroup.centralizer (T : Set G) := fun hu => hd₀ ((hiff _ ht₁T).2
    (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hu _ ht₁T)))
  have hU4 : (Subgroup.centralizer (Kγ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) ≤ 4 := by
    rw [hKγ₀, S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hK₀M]
    exact relIndex_centralizer_le_four h hd hu₀ huT inf_le_left inf_le_right
  have hQK : Qv _ (baseA (puAmalgam h.le)) ≤ Kγ := by
    intro y hy
    have hyT : y ∈ imM h.le T := by
      rw [← puAmalgam.qv_baseB]
      exact hQT hy
    obtain ⟨y₀, hy₀, rfl⟩ := hyT
    rw [hKγ₀]
    refine ⟨y₀, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hy₀, ?_⟩, rfl⟩
    have hux : (puAmalgam h.le).ofA ⟨u₀, Uq_le h.L_le hu₀⟩ ∈ XM _ (baseA (puAmalgam h.le)) := by
      rw [S5B.xm_baseA_eq h]
      exact ⟨⟨u₀, Uq_le h.L_le hu₀⟩, Subgroup.mem_subgroupOf.2 (h.Uq_le_Xq hu₀), rfl⟩
    have e := Subgroup.mem_centralizer_iff.1 (qv_le_centralizer_xm _ _ hy) _ hux
    have e' : (⟨u₀, Uq_le h.L_le hu₀⟩ : ↥M) * y₀ = y₀ * ⟨u₀, Uq_le h.L_le hu₀⟩ :=
      hinj (by rw [map_mul, map_mul]; exact e)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val e').symm
  have hJ2 : 2 ≤ Jα.relIndex Tβ := by
    have h0 : Jα.relIndex Tβ ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have h1 : Jα.relIndex Tβ ≠ 1 := fun h1 =>
      hA (le_antisymm hJT (Subgroup.relIndex_eq_one.1 h1))
    omega
  have hQK4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex Kγ := by
    have e1 := Subgroup.relIndex_mul_relIndex _ _ _ hQK hKT
    have e2 := Subgroup.relIndex_mul_relIndex _ _ _
      (S5B.qv_le_jOff h (by norm_num) hα hαβadj) hJT
    rw [hKγ2] at e1
    nlinarith
  have hcJK : Nat.card Jα ≤ Nat.card Kγ := by
    have e3 := Subgroup.relIndex_mul_card (H := Jα) (K := Tβ)
    have e4 := Subgroup.relIndex_mul_card (H := Kγ) (K := Tβ)
    rw [inf_of_le_left hJT] at e3
    rw [inf_of_le_left hKT, hKγ2] at e4
    nlinarith
  obtain ⟨⟨⟨E₀, hE₀⟩⟩, -⟩ := Nat.card_pos_iff.1 (by rw [hcard1]; norm_num :
    0 < Nat.card (S5.offSet h.le L 2 (baseA (puAmalgam h.le)) (baseB _)))
  have hE₀J : E₀ ≤ Jα :=
    le_iSup₂ (f := fun E (_ : E ∈ S5.offSet h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) => E)
      E₀ hE₀
  have hKoff : Kγ ∈ S5.offSet h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
    refine ⟨⟨hKT, hU4.trans hQK4, hU4.trans (by norm_num)⟩, fun E' hE' => ?_⟩
    exact (hE₀.2 E' hE').trans ((Subgroup.card_le_of_le hE₀J).trans hcJK)
  have hKJ : Kγ = Jα := Subgroup.eq_of_le_of_card_ge
    (le_iSup₂ (f := fun E (_ : E ∈ S5.offSet h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) => E)
      Kγ hKoff) hcJK
  have hgβ' : g⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem hg)
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g⁻¹ • baseA (puAmalgam h.le)) := by
    have := (adj_smul _ g⁻¹ (baseB (puAmalgam h.le)) (baseA _)).mpr hαβadj.symm
    rwa [hgβ'] at this
  have hJδ : S5.jOff h.le L 2 (g⁻¹ • baseA (puAmalgam h.le)) (baseB _) = Kα := by
    have e := S5B.jOff_smul h.le hLn 2 g⁻¹ (baseA (puAmalgam h.le)) (baseB _)
    rw [hgβ'] at e
    rw [e, ← hJα, ← hKJ, hKg, map_conj_inv_map_conj]
  have hJne : S5.jOff h.le L 2 (g⁻¹ • baseA (puAmalgam h.le)) (baseB _) ≠ Jα := by
    rw [hJδ]
    intro e
    apply hB
    rw [← e]
    exact ⟨hKe, hK2⟩
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤
      S5.jOff h.le L 2 (g⁻¹ • baseA (puAmalgam h.le)) (baseB _) := by
    rw [hJδ]
    exact le_inf hQT ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le inf_le_left))
  have hJodd : ¬ S5.vIm h.le a Jα ≤ commutator (MSP.Sp4 F) := by
    intro hJe
    have hJK : Jα ≤ Kα := le_inf hJT (Subgroup.le_centralizer_iff.1
      (cX_le_centralizer_of_vIm_le h hd (hJT.trans hTst) hJe))
    have hJKe : Jα = Kα := by
      rw [← hKJ] at hJK ⊢
      exact eq_of_relIndex_eq_two' hJK hKαT hTKα hKγ2
    exact hB ⟨hJe, by rw [hJKe]; exact hK2⟩
  exact hC (H55 G M T L h hmin hb F _ _ a hd _ hβδ hJne hQJ ⟨l₁, hl₁, hT₁, hJl₁⟩ hJodd
    (by rw [hJδ]; exact hKe))

end Vertex

end UC

namespace UC

variable (h : PUHyp M T L)

private theorem map_stabCenter_le'' (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    (stabCenter _ δ).map (MulAut.conj g).toMonoidHom ≤ stabCenter _ (g • δ) := by
  rintro _ ⟨z, hz, rfl⟩
  have hzs := (S5B.stabCenter_le_inf δ hz).1
  have hzc := (S5B.stabCenter_le_inf δ hz).2
  have hgz : (MulAut.conj g).toMonoidHom z ∈ stab _ (g • δ) := by
    rw [stab_smul]
    exact ⟨z, hzs, rfl⟩
  refine ⟨⟨_, hgz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  have hy : g⁻¹ * (y : (puAmalgam h.le).Universal) * g ∈ stab _ δ := (mem_stab_smul _).1 y.2
  have hyz := Subgroup.mem_centralizer_iff.1 hzc _ hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul]
  calc (y : (puAmalgam h.le).Universal) * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by
        group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hyz]
    _ = g * z * g⁻¹ * y := by group

theorem zm_inf_cX_le_stabCenter_of_jOff_ne (H55 : Q2Cent55) (h54 : S54) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hJ : S5.jOff h.le L 2 (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ≠
      S5.jOff h.le L 2 (baseA _) (baseB _)) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ (XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ⊓
        Subgroup.centralizer (puTrans h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) :
          Set (puAmalgam h.le).Universal)) ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hCH := h.centHyp
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := by
    have := two_le_critDist _ h20 hb0
    exact dist_geo _ (by rw [hc.2.1]; omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1)
      (by have := two_le_critDist _ h20 hb0; rw [hc.2.1]; omega)
    rwa [hαβ] at this
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβadj.symm hβγ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  set Tβ := Qv _ (baseB (puAmalgam h.le)) with hTβ
  set Cα := XM _ (baseA (puAmalgam h.le)) ⊓
    Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) with hCα
  set Cγ := XM _ γ ⊓ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal)
    with hCγ
  have hTstγ : Tβ ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hQst : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ γ :=
    qv_le_stab_of_dist_le_two _ h20 hα hd2.le
  have hXQ : XM _ γ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    ms22_i _ h20 hCH hγM hα (by rw [SimpleGraph.dist_comm, hd2]; omega)
  have hZX : ZM _ (baseA (puAmalgam h.le)) ≤ XM _ (baseA _) := zm_le_xm _ h20 hb0 hα
  rintro z ⟨hzZ, hzC⟩
  by_cases hA : S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) = Tβ
  · exact absurd (jOff_eq_of_eq_qv h hβγ hA) hJ
  by_cases hB : S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
      commutator (MSP.Sp4 F) ∧
    (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)).relIndex Tβ = 2
  · have hnot := not_cX_le_xm_of_even h hmin hb hd h54 hC hB.1 hB.2 hc hαβ hJ
    have hEC : ¬ Cγ ≤ Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) := by
      intro hle
      refine hnot fun c hc' => mem_omegaOneCenterOf (hXQ hc'.1)
        (fun y hy => Subgroup.mem_centralizer_iff.1 (hle hc') y hy)
        ((isElemAbelian_xm _ _).2 c hc'.1)
    exact cX_inf_centralizer_le_stabCenter h hd hγM hQst hEC
      ⟨hzC, (hZX.trans (xm_le_centralizer _ _)) hzZ⟩
  by_contra hzG
  have hCg : Cγ = Cα.map (MulAut.conj g).toMonoidHom := by
    rw [hCγ, hCα, ← hgα, cX_smul h]
  have hTg : Tβ.map (MulAut.conj g).toMonoidHom = Tβ := by
    rw [hTβ, ← qv_smul, hgβ]
  have hTC : ¬ Cγ ≤ Subgroup.centralizer (Tβ : Set (puAmalgam h.le).Universal) := by
    intro hle'
    apply not_cX_le_centralizer_qv_baseB h hd hC
    rw [hCg, ← hTg, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hle'
    exact hle'
  have hzT : z ∉ Subgroup.centralizer (Tβ : Set (puAmalgam h.le).Universal) := fun hzT =>
    hzG (cX_inf_centralizer_le_stabCenter h hd hγM hTstγ hTC ⟨hzC, hzT⟩)
  rw [Subgroup.mem_centralizer_iff] at hzT
  push Not at hzT
  obtain ⟨t₁, ht₁, hct₁⟩ := hzT
  have hd1 : ⁅t₁, z⁆ ≠ 1 := fun h1 => hct₁ (commutatorElement_eq_one_iff_mul_comm.1 h1)
  by_cases hdC : ⁅t₁, z⁆ ∈ Cα
  · obtain ⟨c₀, t₁₀, rfl, rfl, hc₀X, ht₁T, hd₀, hdiff, hP₀, -⟩ :=
      exists_pullback h hd hβγ hzC (hZX hzZ) ht₁ hd1
    have hc₀Z : (c₀ : G) ∈ Z0q M T := by
      rw [puAmalgam.zm_baseA] at hzZ
      obtain ⟨z₀, hz₀, he⟩ := hzZ
      rw [← (puAmalgam h.le).ofA_injective he]
      exact Subgroup.mem_subgroupOf.1 hz₀
    exact hd₀ (comm_eq_one_of_comm_mem_z0q h hd hXU hc₀Z hc₀X (hdiff.1 hdC) hP₀ ht₁T)
  · exact false_of_comm_not_mem h H55 h54 hmin hb hd hXU hC hA hB hβγ hzC (hZX hzZ) ht₁ hd1 hdC

theorem zm_inf_cX_le_stabCenter_of_isCritical (H55 : Q2Cent55) (h54 : S54)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {x x' : Vtx (puAmalgam h.le)} (hc : IsCritical _ x x')
    (hJ : S5.jOff h.le L 2 (geo _ x x' 2) (geo _ x x' 1) ≠ S5.jOff h.le L 2 x (geo _ x x' 1)) :
    ZM _ x ⊓ (XM _ (geo _ x x' 2) ⊓
        Subgroup.centralizer (puTrans h.le L (geo _ x x' 2) : Set (puAmalgam h.le).Universal)) ≤
      stabCenter _ (geo _ x x' 2) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hb0 := h.critDist_pos
  obtain ⟨g, hgx, hgβ⟩ := exists_smul_base_edge _ hc.1 (adj_geo_one_of_isCritical _ hb0 hc)
  have hx' : x' = g • (g⁻¹ • x') := (smul_inv_smul g x').symm
  have hgeo : ∀ i, geo _ x x' i = g • geo _ (baseA (puAmalgam h.le)) (g⁻¹ • x') i := by
    intro i
    conv_lhs => rw [hgx, hx']
    exact geo_smul _ g _ _ i
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • x') := by
    rw [← isCritical_smul _ g, smul_inv_smul, ← hgx]
    exact hc
  have h1 : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • x') 1 = baseB _ := by
    have e := hgeo 1
    rw [hgβ] at e
    exact ((smul_left_cancel_iff g).1 e).symm
  have key := zm_inf_cX_le_stabCenter_of_jOff_ne h H55 h54 hmin hb hd hXU hC hc' h1
    (fun heq => hJ (by
      rw [hgeo 2, hgeo 1, h1, hgx, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn, heq]))
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) key
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul, ← cX_smul h, ← hgx] at h2
  rw [hgeo 2]
  exact h2.trans (map_stabCenter_le'' h g _)

theorem cX_inf_zm_le_stabCenter_of_not_case56 (H55 : Q2Cent55) (h54 : S54)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {γ μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ μ) (h1 : geo _ γ μ 1 = baseB _)
    (h2 : geo _ γ μ 2 = baseA _) (hcase : ∀ l, ¬ S5.Case56 h 2 a γ l) :
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ⊓
        ZM _ γ ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have key := zm_inf_cX_le_stabCenter_of_isCritical h H55 h54 hmin hb hd hXU hC hc (by
    rw [h1, h2]
    exact (jOff_ne_of_not_case56 h hmin hb hd h54 hC hcase).symm)
  rw [h2] at key
  exact fun r hr => key ⟨hr.2, hr.1⟩

end UC

end CFSG.Quasithin.MS93.S5Q2
