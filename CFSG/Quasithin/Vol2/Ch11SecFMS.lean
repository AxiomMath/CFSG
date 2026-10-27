module

public import CFSG.Quasithin.Vol2.Ch11SecA15MS3
public import CFSG.Quasithin.Vol2.Ch11SecD556B
public import CFSG.Quasithin.Vol2.Ch11SecFBasic
public import CFSG.Quasithin.Vol2.Ch11SecFFacts3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₃ : Subgroup G}

open SecA in
theorem inf_L_le_lOf_sup_pCoreOf (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) : T ⊓ L ≤ LOf L V₁ ⊔ pCoreOf 2 L := by
  have hLV := L_le_normalizer_fsuV h
  have hUV := IsVi.le_fsuV hU
  have hflag := isFlagW_of_isVi h hU
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  have hP : autOn (T ⊓ L) (fsuV T I) ≤
      perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I))) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
      ⟨-, -, -, -, -, hG2⟩
    · exact hF.sylowSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · exact hF.sylowSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
      exact hF.sylowG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
  intro t ht
  have htV : t ∈ Subgroup.normalizer (fsuV T I : Set G) := hLV ht.2
  have hg := hP (conjV_mem_autOn ht htV)
  rw [← autOn_inf_normalizer hUV, ← autOn_perfectCore (inf_le_left.trans hLV)] at hg
  obtain ⟨l, hl, hlV, hlt⟩ := mem_autOn_iff.mp hg
  have hc : l⁻¹ * t ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (lOf_le_L hl)) ht.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) hlt
    simp only [conjV_apply_coe] at h1
    calc v * (l⁻¹ * t) = l⁻¹ * (l * v * l⁻¹) * t := by group
      _ = l⁻¹ * (t * v * t⁻¹) * t := by rw [h1]
      _ = l⁻¹ * t * v := by group
  rw [centralizer_eq_pCoreOf h1102 h] at hc
  have := Subgroup.mul_mem_sup hl hc
  simpa using this

theorem pCoreOf_lOf_le (hRL : FactSp4RL) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hOQ : pCoreOf 2 L ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    (hVQ : ⁅V₃, pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))⁆ ≠ ⊥) :
    pCoreOf 2 (LOf L V₁) ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hG₁Q₁ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
    (Subgroup.normalizer (V₁ : Set G))
  have hL₁Q₁ := (SecD.lOf_le_normalizer L V₁).trans hG₁Q₁
  have h1 := hRL G T L I n V₁ V₃ X (SecD.natSetting11_of h1102 h1141 h hV₁) hk hV₁ hV₃ hX _
    (pCoreOf_normalizer_V₁_le_ROf h hV₁) hL₁Q₁ ((SecA.IsVi.le_normalizer hV₁).trans hG₁Q₁)
    ((SecD.cartan_le_normalizer_V₁ hN h1102 h hV₁ hX).trans hG₁Q₁) hVQ
  have h2 : pCoreOf 2 (LOf L V₁) ≤ pCoreOf 2 (L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    pCoreOf_le_pCoreOf_of_le_normalizer (perfectCore_le _) fun x hx =>
      SecD.mem_normalizer_lOf (Subgroup.le_normalizer hx.1) hx.2
  exact h2.trans (h1.trans (sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hL₁Q₁) hOQ))

theorem coe_sup_pCoreOf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    ((L ⊔ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Subgroup G) : Set G) =
      (L : Set G) * (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((pCoreOf_normalizer_V₁_le_T h hV₁).trans h.normal)

theorem mem_cComp_sup_pCoreOf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    L ∈ cComp (L ⊔ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) := by
  have hQ₁L := (pCoreOf_normalizer_V₁_le_T h hV₁).trans h.normal
  have hLM := SecA.mem_cComp_of_le h le_rfl (sup_le Subgroup.le_normalizer h.normal)
  have hn : (L.subgroupOf (L ⊔ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQ₁L)
  exact SecA.mem_cComp_of_quasisimple (ne_bot_of_mem_cComp hLM) (perfect_of_mem_cComp hLM)
    h.fsu.quasisimple (IsSubnormal.step le_sup_left hn (IsSubnormal.refl _))

theorem isMSPair_Q₁ (h331 : Stmt3_3_1) (hF15 : SecA.Facts15) (hN : SecA.NatFacts)
    (hRL : FactSp4RL) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h1154 : Stmt11_5_4)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃)
    (hk : KindSp4 L (fsuV T I) n)
    (hOQ : pCoreOf 2 L ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    (hVQ : ⁅V₃, pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))⁆ ≠ ⊥) :
    IsMSPair (L ⊔ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
      (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₁ := pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) with hQ₁def
  have hQ₁T : Q₁ ≤ T := pCoreOf_normalizer_V₁_le_T h hV₁
  have hQ₁L : Q₁ ≤ Subgroup.normalizer (L : Set G) := hQ₁T.trans h.normal
  have hG₁Q₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (Q₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hTQ₁ : T ≤ Subgroup.normalizer (Q₁ : Set G) := (SecA.IsVi.le_normalizer hV₁).trans hG₁Q₁
  have hQ₁2 : IsPGroup 2 Q₁ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hcoe : ((L ⊔ Q₁ : Subgroup G) : Set G) = (L : Set G) * (Q₁ : Set G) :=
    coe_sup_pCoreOf h hV₁
  have hle : L ⊔ Q₁ ≤ L ⊔ T := sup_le_sup_left hQ₁T L
  have hnorm : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ Q₁ : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer)
      ((le_inf h.normal hTQ₁).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _))
  have hchar : QuasithinUnique.CharTwo (L ⊔ Q₁) := by
    have hn : ((L ⊔ Q₁).subgroupOf (L ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
    exact QuasithinUnique.CharTwo.of_isSubnormal (SecA.charTwo_LT h) hle hn.isSubnormal
  have hcomp : L ∈ cComp (L ⊔ Q₁) := mem_cComp_sup_pCoreOf h hV₁
  have hL₁Q₁ : LOf L V₁ ≤ Subgroup.normalizer (Q₁ : Set G) :=
    (SecD.lOf_le_normalizer L V₁).trans hG₁Q₁
  have hO₂L₁ := pCoreOf_lOf_le hRL hN h1102 h1141 h hV₁ hV₃ hk hOQ hVQ
  have hlt : LOf L V₁ ⊔ Q₁ < L ⊔ Q₁ := by
    refine lt_of_le_of_ne (sup_le_sup_right SecA.lOf_le_L _) fun heq => ?_
    have hlt' := SecA.lOf_sup_ROf_lt hN h1102 h hV₁
    have hLle : L ≤ LOf L V₁ ⊔ ROf T L V₁ := (le_sup_left.trans heq.symm.le).trans
      (sup_le_sup_left (pCoreOf_normalizer_V₁_le_ROf h hV₁) _)
    exact lt_irrefl _ (lt_of_le_of_lt (sup_le hLle le_sup_right) hlt')
  have hQO : Q₁ ≤ pCoreOf 2 (LOf L V₁ ⊔ Q₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le hL₁Q₁ Subgroup.le_normalizer) hQ₁2
  have hOQ' : pCoreOf 2 (LOf L V₁ ⊔ Q₁) ≤ Q₁ := by
    intro x hx
    have hTL₁ : Q₁ ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
      hQ₁T.trans (SecA.T_le_normalizer_lOf h.normal (SecA.IsVi.le_normalizer hV₁))
    have hx' : x ∈ ((LOf L V₁ ⊔ Q₁ : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTL₁] at hx'
    obtain ⟨l, hl, q, hq, rfl⟩ := hx'
    have hlO : l ∈ pCoreOf 2 (LOf L V₁ ⊔ Q₁) := by
      have := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hQO hq))
      simpa using this
    have hlO₂ : l ∈ pCoreOf 2 (LOf L V₁) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_right : pCoreOf 2 (LOf L V₁ ⊔ Q₁) ⊓ LOf L V₁ ≤ _) ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left) ⟨hlO, hl⟩
      exact fun k hk => SecD.mem_normalizer_inf
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk))
        (Subgroup.le_normalizer hk)
    exact Subgroup.mul_mem _ (hO₂L₁ hlO₂) hq
  have hodd : ¬ 2 ∣ (LOf L V₁ ⊔ Q₁).relIndex (L ⊔ Q₁) := by
    have hS := B6.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right) hle hnorm
    have hTLQ : T ⊓ (L ⊔ Q₁) ≤ LOf L V₁ ⊔ Q₁ := by
      intro x ⟨hxT, hxG⟩
      have hx : x ∈ ((L ⊔ Q₁ : Subgroup G) : Set G) := hxG
      rw [hcoe] at hx
      obtain ⟨l, hl, q, hq, rfl⟩ := hx
      have hlT : l ∈ T := by
        have := T.mul_mem hxT (T.inv_mem (hQ₁T hq))
        simpa using this
      have hl' := inf_L_le_lOf_sup_pCoreOf hF15 h1102 h hV₁ ⟨hlT, hl⟩
      exact Subgroup.mul_mem _ ((sup_le_sup_left hOQ _) hl') (Subgroup.mem_sup_right hq)
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hTLQ hlt.le
    intro h2
    apply hS.2.2
    change 2 ∣ (T ⊓ (L ⊔ Q₁)).relIndex (L ⊔ Q₁)
    rw [← hmul]
    exact dvd_mul_of_dvd_right h2 _
  have hms3 : ∀ C : Subgroup G, C ≤ Q₁ → C ≠ ⊥ → (C.subgroupOf Q₁).Characteristic →
      ¬ L ⊔ Q₁ ≤ Subgroup.normalizer (C : Set G) := by
    intro C hCR hC hchar' hG
    have hRC : Subgroup.normalizer (Q₁ : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (C.subgroupOf Q₁)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at this
    have hCM := SecA.normalizer_le_of_isPGroup h331 h (hQ₁2.to_le hCR) hC
      (sup_le (le_sup_left.trans hG) (hTQ₁.trans hRC))
    exact normalizer_V₁_not_le h1154 h hV₁ (hG₁Q₁.trans (hRC.trans hCM))
  exact ⟨⟨SecA.sqtkGroup_of_le_normalizer h331 h (sup_le Subgroup.le_normalizer hQ₁L), hchar, L,
    hcomp, hcoe, SecA.rankTwo_L hF15 h1102 h⟩,
    Or.inl ⟨LOf L V₁ ⊔ Q₁, hlt, hodd, le_antisymm hQO hOQ'⟩, hms3⟩

end CFSG.Quasithin.Vol2.Ch11.SecF
