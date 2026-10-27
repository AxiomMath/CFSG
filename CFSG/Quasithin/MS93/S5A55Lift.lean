module

public import CFSG.Quasithin.MS93.S5A56
public import CFSG.Quasithin.MS93.S38EPU

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

section GroupTheory

variable {Γ : Type*} [Group Γ]

theorem eq_bot_of_isPerfect_of_isPGroup {L : Subgroup Γ} [Finite ↥L] (hperf : Group.IsPerfect ↥L)
    (h2 : IsPGroup 2 L) : L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Subsingleton ↥L := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent ↥L h2.isNilpotent
  refine eq_bot_iff.mpr fun x hx => ?_
  have := Subsingleton.elim (⟨x, hx⟩ : ↥L) 1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem le_of_le_sup_of_isPGroup {L W P : Subgroup Γ} [Finite ↥L] (hL : ⁅L, L⁆ = L)
    (hP : IsPGroup 2 P) (hPW : P ≤ Subgroup.normalizer (W : Set Γ)) (hLW : L ≤ W ⊔ P) :
    L ≤ W := by
  set N := Subgroup.normalizer (W : Set Γ) with hN
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hLN : L ≤ N := hLW.trans (sup_le hWN hPW)
  have : (W.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  set φ := QuotientGroup.mk' (W.subgroupOf N)
  have hsub : L.subgroupOf N ≤ W.subgroupOf N ⊔ P.subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hWN hPW]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hLW (Subgroup.mem_subgroupOf.1 hx))
  have hLP : (L.subgroupOf N).map φ ≤ (P.subgroupOf N).map φ := by
    refine (Subgroup.map_mono hsub).trans ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ le_rfl
    rintro _ ⟨w, hw, rfl⟩
    rw [show φ w = 1 from (QuotientGroup.eq_one_iff w).2 hw]
    exact Subgroup.one_mem _
  have hP' : IsPGroup 2 (P.subgroupOf N) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
  have h2 : IsPGroup 2 ((L.subgroupOf N).map φ) := (hP'.map φ).to_le hLP
  have hperf : Group.IsPerfect ↥((L.subgroupOf N).map φ) := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
    have : Group.IsPerfect ↥(L.subgroupOf N) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLN).symm.surjective
    have e : (L.subgroupOf N).map φ = (φ.comp (L.subgroupOf N).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e]
    exact Group.IsPerfect.range _
  have : Finite ↥(L.subgroupOf N) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hLN).symm.toEquiv
  have : Finite ↥((L.subgroupOf N).map φ) :=
    Finite.of_surjective _ (φ.subgroupMap_surjective (L.subgroupOf N))
  have hbot := eq_bot_of_isPerfect_of_isPGroup hperf h2
  intro x hx
  have hmem : φ ⟨x, hLN hx⟩ ∈ (L.subgroupOf N).map φ :=
    ⟨⟨x, hLN hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmem)

theorem le_sup_of_le_sup_sup {L J Z Q : Subgroup Γ} [Finite ↥L] (hL : ⁅L, L⁆ = L)
    (hZQ : IsPGroup 2 ↥(Z ⊔ Q)) (hQJ : Q ≤ Subgroup.normalizer (J : Set Γ))
    (hQn : J ⊔ Z ≤ Subgroup.normalizer (Q : Set Γ)) (hle : L ≤ J ⊔ Z ⊔ Q) : L ≤ J ⊔ Z := by
  set H := J ⊔ Z with hH
  set K := H ⊔ Q with hK
  set W := ⨆ k : ↥K, J.map (MulAut.conj (k : Γ)).toMonoidHom with hW
  have hJW : J ≤ W := by
    refine le_trans ?_ (le_iSup _ (1 : ↥K))
    intro j hj
    exact ⟨j, hj, by simp⟩
  have hWH : W ≤ H := by
    refine iSup_le fun k => ?_
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ H, ∃ y ∈ Q, x * y = (k : Γ) := by
      have hk : (k : Γ) ∈ ((H ⊔ Q : Subgroup Γ) : Set Γ) := k.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right H Q hQn] at hk
      obtain ⟨x, hx, y, hy, hxy⟩ := hk
      exact ⟨x, hx, y, hy, hxy⟩
    rw [← hxy]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : y * j * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hQJ hy) j).1 hj
    have e : (MulAut.conj (x * y)).toMonoidHom j = x * (y * j * y⁻¹) * x⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact H.mul_mem (H.mul_mem hx (le_sup_left (b := Z) hj')) (H.inv_mem hx)
  have hKW : K ≤ Subgroup.normalizer (W : Set Γ) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [hW, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_map]
    refine le_trans ?_ (le_iSup _ (⟨g, hg⟩ * k : ↥K))
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨j, hj, by simp [mul_assoc]⟩
  have hPW : Z ⊔ Q ≤ Subgroup.normalizer (W : Set Γ) :=
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right).trans hKW
  have hLW : L ≤ W ⊔ (Z ⊔ Q) := by
    refine hle.trans (sup_le (sup_le (hJW.trans le_sup_left) ?_) ?_)
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  exact (le_of_le_sup_of_isPGroup hL hZQ hPW hLW).trans hWH

private theorem mem_normalizer_of_map_conj_eq {K : Subgroup Γ} {t : Γ}
    (h : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : t * y * t⁻¹ = t * x * t⁻¹ := hyx
      simpa using h1
    rwa [← this]

end GroupTheory

section Lift

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem finite_stab_baseA : Finite ↥(stab (puAmalgam h.le) (baseA _)) := by
  rw [puAmalgam.stab_baseA]
  exact Finite.of_surjective _
    (Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective).surjective

theorem finite_puTrans_baseA : Finite ↥(puTrans h.le L (baseA (puAmalgam h.le))) := by
  have := finite_stab_baseA h
  exact Finite.of_injective _ (Subgroup.inclusion_injective (puTrans_le_stab h.le L _))

theorem qv_le_normalizer_jOff (q : ℕ) {α₁ β₁ : Vtx (puAmalgam h.le)}
    (hab : (puAmalgam h.le).treeGraph.Adj β₁ α₁) :
    Qv (puAmalgam h.le) β₁ ≤
      Subgroup.normalizer (jOff h.le L q α₁ β₁ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  intro t ht
  refine mem_normalizer_of_map_conj_eq ?_
  rw [← jOff_smul h.le hLn, (mem_stab _).1 (qv_le_stab _ _ ht),
    (mem_stab _).1 (qv_le_stab_of_adj _ hab ht)]

theorem adj_smul_inv_baseB {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) (baseA _)) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) ∧
      (puAmalgam h.le).treeGraph.Adj (g⁻¹ • baseB (puAmalgam h.le)) (g⁻¹ • δ) := by
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  refine ⟨?_, (adj_smul _ g⁻¹ _ _).2 hβδ⟩
  have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
  rwa [hgα] at this

theorem isPGroup_zHat_sup_qv {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _) :
    IsPGroup 2 ↥(zHat _ (baseA (puAmalgam h.le)) α' ⊔ Qv _ (baseA (puAmalgam h.le))) := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hnot : ¬ IsMVtx _ (baseB (puAmalgam h.le)) :=
    (isMVtx_iff_of_adj _ (adj_baseA_baseB _)).1 hα
  refine (isPGroup_qv _ hyp hnot).to_le (sup_le ?_ (qv_le_qv _ hyp hα (adj_baseA_baseB _)))
  exact inf_le_left.trans (zm_le_qv_baseB h hc hβ)

theorem zHat_le_stab {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _) :
    zHat _ (baseA (puAmalgam h.le)) α' ≤ stab _ (baseA (puAmalgam h.le)) :=
  inf_le_left.trans ((zm_le_qv_baseB h hc hβ).trans
    (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm))

theorem puTrans_le_jOff_sup_zHat (hd : IsSp4Data M T L k F a) (q : ℕ)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hβ : geo _ (baseA _) α' 1 = baseB _) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) (baseA _))
    (hsp : imSp a L ≤ vIm h.le a (jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔
      zHat _ (baseA (puAmalgam h.le)) α')) :
    puTrans h.le L (baseA _) ≤
      jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔
        zHat _ (baseA (puAmalgam h.le)) α' := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  obtain ⟨hαβ₁, hβ₁α₁⟩ := adj_smul_inv_baseB h hg hβδ
  have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ hαβ₁.symm
  have hQT₁ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) :=
    qv_le_qv _ hyp hα hαβ₁
  have hJst : jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ≤
      stab _ (baseA (puAmalgam h.le)) :=
    (iSup₂_le fun _ hE => hE.1.1).trans hT₁
  have hZst := zHat_le_stab h hc hβ
  have hK : jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔
      zHat _ (baseA (puAmalgam h.le)) α' ⊔ Qv _ (baseA (puAmalgam h.le)) ≤
      stab _ (baseA (puAmalgam h.le)) :=
    sup_le (sup_le hJst hZst) (qv_le_stab _ _)
  have hL' := (lift56 h hd hK le_sup_right).1 (hsp.trans (vIm_mono' h le_sup_left))
  have := finite_puTrans_baseA h
  refine le_sup_of_le_sup_sup (S38E.puTrans_baseA_perfect h) (isPGroup_zHat_sup_qv h hc hβ)
    (hQT₁.trans (qv_le_normalizer_jOff h q hβ₁α₁)) ?_ hL'
  exact (sup_le hJst hZst).trans (stab_le_normalizer_qv _ _)

theorem qv_sup_zHat_eq_stab (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab (puAmalgam h.le) (baseA _))
    (htop : vIm h.le a (Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔
      zHat _ (baseA (puAmalgam h.le)) α') = ⊤) :
    Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ zHat _ (baseA (puAmalgam h.le)) α' =
      stab _ (baseA (puAmalgam h.le)) := by
  have hαβ₁ := (adj_smul_inv_baseB h hg (adj_baseA_baseB (puAmalgam h.le)).symm).1
  exact (lift56 h hd (sup_le (qv_le_stab_of_adj _ hαβ₁.symm) (zHat_le_stab h hc hβ))
    ((qv_le_qv _ h.hyp20 (isMVtx_baseA _) hαβ₁).trans le_sup_left)).2 htop

include h in
theorem mem_centralizer_of_fixSp_inf_eq_bot (hd : IsSp4Data M T L k F a) {J : Subgroup G}
    (hJM : J ≤ M) (hfix : MSP.fixSp (imSp a T) ⊓ MSP.fixSp (imSp a J) = ⊥) {z : G}
    (hz : z ∈ Uq M T L ⊔ Dq M L) (hzT : z ∈ Subgroup.centralizer (T : Set G))
    (hzJ : z ∈ Subgroup.centralizer (J : Set G)) : z ∈ Subgroup.centralizer (M : Set G) := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  obtain ⟨-, hUL, hlift⟩ := sp4Lift G M T L h k F _ _ a hd
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hDn : M ≤ Subgroup.normalizer (Dq M L : Set G) := le_normalizer_Dq h.le_normalizer
  obtain ⟨u, hu, d, hdD, rfl⟩ : ∃ u ∈ Uq M T L, ∃ d ∈ Dq M L, u * d = z := by
    have hz' : z ∈ ((Uq M T L ⊔ Dq M L : Subgroup G) : Set G) := hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((Uq_le h.L_le).trans hDn)] at hz'
    obtain ⟨u, hu, d, hd', e⟩ := hz'
    exact ⟨u, hu, d, hd', e⟩
  have key : ∀ y ∈ M, y * (u * d) = u * d * y → y * u * y⁻¹ = u := by
    intro y hy hc
    have hu' : y * u * y⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hy) u).1 hu
    have hd' : y * d * y⁻¹ ∈ Dq M L := (Subgroup.mem_normalizer_iff.1 (hDn hy) d).1 hdD
    have e1 : y * u * y⁻¹ * (y * d * y⁻¹) = u * d := by
      calc y * u * y⁻¹ * (y * d * y⁻¹) = y * (u * d) * y⁻¹ := by group
        _ = u * d := by rw [hc]; group
    have hw : u⁻¹ * (y * u * y⁻¹) ∈ Dq M L := by
      have e2 : u⁻¹ * (y * u * y⁻¹) = d * (y * d * y⁻¹)⁻¹ := by
        calc u⁻¹ * (y * u * y⁻¹) =
            u⁻¹ * (y * u * y⁻¹ * (y * d * y⁻¹)) * (y * d * y⁻¹)⁻¹ := by group
          _ = d * (y * d * y⁻¹)⁻¹ := by rw [e1]; group
      rw [e2]
      exact mul_mem hdD (inv_mem hd')
    have hcomm := IsSp4Data.commute_of_mem_Uq h (inv_mem hu) hu'
    have hwL : y * u * y⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hcomm]
      exact hw.2
    exact hlift y hy u hu hwL
  have hcT : u ∈ Subgroup.centralizer (T : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have := key y (h.le hy) (Subgroup.mem_centralizer_iff.1 hzT y hy)
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [this]
  have hcJ : u ∈ Subgroup.centralizer (J : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have := key y (hJM hy) (Subgroup.mem_centralizer_iff.1 hzJ y hy)
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [this]
  have hv : nv.vec ⟨u, hu⟩ = 0 := by
    have h1 := nv.vec_mem_fixSp (E := T) ⟨u, hu⟩ hcT
    have h2 := nv.vec_mem_fixSp (E := J) ⟨u, hu⟩ hcJ
    have h3 : nv.vec ⟨u, hu⟩ ∈ MSP.fixSp (imSp a T) ⊓ MSP.fixSp (imSp a J) := ⟨h1, h2⟩
    rwa [hfix, Submodule.mem_bot] at h3
  have huM : u ∈ Subgroup.centralizer (M : Set G) := by
    have : u ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := ⟨hu, (nv.vec_eq_zero_iff _).1 hv⟩
    rw [hUL] at this
    exact this.2
  have hcL : u * d ∈ Subgroup.centralizer (L : Set G) :=
    mul_mem (Subgroup.centralizer_le h.L_le huM) hdD.2
  have hle : M ≤ Subgroup.centralizer ({u * d} : Set G) := by
    rw [h.eq_sup]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hcL y hy)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzT y hy)
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hy)


theorem zh_inf_centralizer_jOff_le (h53 : S53) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : IsSp4Data M T L k F a)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab (puAmalgam h.le) (baseA _))
    (hfix : MSP.fixSp (vIm h.le a (Qv _ (baseB (puAmalgam h.le)))) ⊓
      MSP.fixSp (vIm h.le a (jOff h.le L (2 ^ k) (baseA _) (g⁻¹ • baseB (puAmalgam h.le)))) =
        ⊥) :
    ZH _ (baseB (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (jOff h.le L (2 ^ k) (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) :
          Set (puAmalgam h.le).Universal) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  set J := jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJ
  set J₁ := jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (g⁻¹ • baseB (puAmalgam h.le)) with hJ₁
  have hJ₁J : J₁ = J.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hJ₁, hJ, ← jOff_smul h.le hLn, hgα]
  have hαβ₁ := (adj_smul_inv_baseB h hg (adj_baseA_baseB (puAmalgam h.le)).symm).1
  have hJ₁st : J₁ ≤ stab _ (baseA (puAmalgam h.le)) :=
    (iSup₂_le fun _ hE => hE.1.1).trans (qv_le_stab_of_adj _ hαβ₁.symm)
  have hUs : stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (uSub h.le L (baseA (puAmalgam h.le)) : Set _) :=
    S38E.le_normalizer_commutator' (stab_le_normalizer_zm _ _)
      (stab_le_normalizer_puTrans h.le hLn _)
  have hDs : stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (dSub h.le L (baseA (puAmalgam h.le)) : Set _) :=
    le_normalizer_inf (stab_le_normalizer_qv _ _)
      (le_normalizer_centralizer (stab_le_normalizer_puTrans h.le hLn _))
  have hUDs := le_normalizer_sup hUs hDs
  rintro z ⟨hzZ, hzC⟩
  have hzX : z ∈ XM _ (baseA (puAmalgam h.le)) :=
    zm_le_xm _ hyp hb0 hα (zh_le_zm _ (adj_baseA_baseB _) hzZ)
  have hzUD : z ∈ uSub h.le L (baseA (puAmalgam h.le)) ⊔ dSub h.le L (baseA _) := by
    have hgz : g * z * g⁻¹ ∈ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (J : Set _) := by
      refine ⟨(Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_xm _ _ hg) z).1 hzX, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun j hj => ?_
      have hj' : g⁻¹ * j * g⁻¹⁻¹ ∈ J₁ := by rw [hJ₁J]; exact ⟨j, hj, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hzC _ hj'
      calc j * (g * z * g⁻¹) = g * ((g⁻¹ * j * g⁻¹⁻¹) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * j * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * j := by group
    have h1 := h53 G M T L h hmin hb k F _ _ a hd hgz
    have h2 := (Subgroup.mem_normalizer_iff.1 (hUDs (inv_mem hg)) _).1 h1
    simpa [mul_assoc] using h2
  have hst : stab (puAmalgam h.le) (baseA _) = imM h.le M := puAmalgam.stab_baseA h.le
  obtain ⟨J₁₀, -, hJ₁₀M, hJ₁₀⟩ := exists_eq_imM h.le (hst ▸ hJ₁st)
  rw [uSub_baseA h, dSub_baseA h, ← imM_sup_of_le h (Uq_le h.L_le) Dq_le] at hzUD
  obtain ⟨z₀, hz₀, rfl⟩ := hzUD
  have hz₀' : (z₀ : G) ∈ Uq M T L ⊔ Dq M L := Subgroup.mem_subgroupOf.1 hz₀
  have hzT : (z₀ : G) ∈ Subgroup.centralizer (T : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    have hmem : (puAmalgam h.le).ofA ⟨t, h.le ht⟩ ∈ Qv _ (baseB (puAmalgam h.le)) := by
      rw [puAmalgam.qv_baseB]
      exact ⟨⟨t, h.le ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (zh_le_centralizer _ _ hzZ) _ hmem
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
  have hzJ : (z₀ : G) ∈ Subgroup.centralizer (J₁₀ : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun j hj => ?_
    have hmem : (puAmalgam h.le).ofA ⟨j, hJ₁₀M hj⟩ ∈ J₁ := by
      rw [hJ₁₀]
      exact ⟨⟨j, hJ₁₀M hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hzC _ hmem
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
  have hfix' : MSP.fixSp (imSp a T) ⊓ MSP.fixSp (imSp a J₁₀) = ⊥ := by
    rw [← vIm_imM h, ← vIm_imM h, ← puAmalgam.qv_baseB, ← hJ₁₀]
    exact hfix
  have hc := mem_centralizer_of_fixSp_inf_eq_bot h hd hJ₁₀M hfix' hz₀' hzT hzJ
  rw [stabCenter_baseA]
  exact ⟨z₀, Subgroup.mem_subgroupOf.2 ⟨z₀.2, hc⟩, rfl⟩

end Lift

end S5

end CFSG.Quasithin.MS93
