module

public import CFSG.Quasithin.Vol2.Ch11SecD551C
public import CFSG.Quasithin.Vol2.Ch11SecD551B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem kOf_cComp_centralizer (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    quasithinIsCComponent (KOf L V₁ V₁) (Subgroup.centralizer (V₁ : Set G)) := by
  have hK := kOf_cComp h1110 h1112 h hV₁
  have hKC := kOf_le_centralizer hTI h1102 h1141 h1143 h hV₁
  have hCN : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCsn : IsSubnormal (Subgroup.centralizer (V₁ : Set G))
      (Subgroup.normalizer (V₁ : Set G)) :=
    IsSubnormal.step hCN inferInstance (IsSubnormal.refl _)
  exact ⟨hK.1, hK.2.1, A3.subnormal_of_le_of_le hK.2.2.1 hKC hCN,
    fun K' hlt h1 hp hsn => hK.2.2.2 K' hlt h1 hp (A3.subnormal_trans hsn hCsn)⟩

theorem pCoreOf_kOf_le_ROf (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (KOf L V₁ V₁) ≤ ROf T L V₁ ∧ pCoreOf 2 (KOf L V₁ V₁) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (SecA.IsVi.le_normalizer hV₁).trans (normalizer_le_normalizer_kOf L V₁ V₁)
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hsylT : QuasithinUnique.IsSylowTwoOf T (K ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hQT : pCoreOf 2 K ≤ T :=
    (le_ROf' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hTQ)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hsylT)
  exact ⟨le_ROf hQT (hT2.to_le hQT)
    ((le_conjClosure _ _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)) hTQ, hQT⟩

theorem isSolvable_sup_of_isPGroup {R N : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable ↥N) :
    Group.IsSolvable ↥(R ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNH : N ≤ R ⊔ N := le_sup_right
  have : (N.subgroupOf (R ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (sup_le hRN Subgroup.le_normalizer)
  have hq : IsPGroup 2 (↥(R ⊔ N) ⧸ N.subgroupOf (R ⊔ N)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_sup hR hRN (by rw [sup_comm]; exact x.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have : Group.IsNilpotent (↥(R ⊔ N) ⧸ N.subgroupOf (R ⊔ N)) := hq.isNilpotent
  have : Group.IsSolvable ↥(N.subgroupOf (R ⊔ N)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).symm.surjective
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf (R ⊔ N)).subtype
    (QuotientGroup.mk' (N.subgroupOf (R ⊔ N)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem false_of_case_one (hFact : FactSolvPointG2) (hMult : SL2pMultFact) (hTI : PointsTIFact)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    [IsMulCommutative ↥(fsuV T I)] (hG2 : KindG2 L (fsuV T I) n)
    (hreal : G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hK1 : Case11_1_2One (KOf L V₁ V₁)) : False := by
  have hPM := not_oTwoTwoPrime_le_M hFact hMult hTI h1102 h1110 h1112 h1141 h1143 h hreal hV₁ hK1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set P := oTwoTwoPrime K with hPdef
  set R₁ := ROf T L V₁ with hR₁def
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hR₁T : R₁ ≤ T := ROf_le_T h V₁
  have hR₁2 : IsPGroup 2 R₁ := hT2.to_le hR₁T
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hR₁P : R₁ ≤ Subgroup.normalizer (P : Set G) := hR₁T.trans (hTN.trans
    ((normalizer_le_normalizer_kOf L V₁ V₁).trans (normalizer_le_normalizer_oTwoTwoPrime K)))
  have hQR := (pCoreOf_kOf_le_ROf h hV₁).1
  have hodd : ¬ 2 ∣ (R₁ ⊓ P).relIndex P := fun h2 => odd_relIndex_oTwoTwoPrime K
    (h2.trans (Subgroup.relIndex_dvd_of_le_left P (le_inf hQR (pCoreOf_le_oTwoTwoPrime K))))
  have hS := isSylowIn_sup_of_normal hR₁2 hR₁P hodd
  have hsolv := isSolvable_sup_of_isPGroup hR₁2 hR₁P (isSolvable_oTwoTwoPrime K)
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  have hV₁R : V₁ ≤ R₁ := le_ROf hV₁T (hT2.to_le hV₁T) (lOf_le_normalizer L V₁) hTN
  have heven : Even (Nat.card ↥(R₁ ⊔ P)) := by
    rw [even_iff_two_dvd]
    exact dvd_trans (two_dvd_card_of_ne_bot (hT2.to_le hV₁T) (SecA.IsVi.ne_bot h hV₁ le_rfl))
      (Subgroup.card_dvd_of_le (hV₁R.trans le_sup_left))
  have hle := le_M_of_sylow_R₁ h1102 h1110 h1122 h hG2 hV₁ hS
    (nParam_eq_one_of_le_one (E1.solvable_nParam_le_one hsolv) heven)
  exact hPM (le_sup_right.trans hle)

theorem false_of_case_two (hSig : L2pSignalizerFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2) (h : Hyp11 G T L I n)
    (hG2 : KindG2 L (fsuV T I) n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hlt : LOf L V₁ < KOf L V₁ V₁) (hK2 : Case11_1_2Two L (KOf L V₁ V₁)) : False := by
  obtain ⟨⟨p, hp, hp11, hpsl⟩, -⟩ := hK2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQT⟩ := pCoreOf_kOf_le_ROf h hV₁
  set K := KOf L V₁ V₁ with hKdef
  set L₁ := LOf L V₁ with hL₁def
  set R₁ := ROf T L V₁ with hR₁def
  set Q := pCoreOf 2 K with hQdef
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hR₁T : R₁ ≤ T := ROf_le_T h V₁
  have hR₁2 : IsPGroup 2 R₁ := hT2.to_le hR₁T
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTN.trans (normalizer_le_normalizer_kOf L V₁ V₁)
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (hTN ht)
  have hL₁K : L₁ ≤ K := le_conjClosure _ _
  have hXR : L₁ ⊔ T ≤ Subgroup.normalizer (R₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T)
  have hRL : ⁅R₁, L₁⁆ ≤ pCoreOf 2 L₁ := by
    have hle : ⁅R₁, L₁⁆ ≤ R₁ ⊓ L₁ := Subgroup.commutator_le.mpr fun r hr l hl => by
      rw [commutatorElement_def]
      refine ⟨?_, L₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL₁ (hR₁T hr)) l).mp hl)
        (L₁.inv_mem hl)⟩
      have hl' : l * r⁻¹ * l⁻¹ ∈ R₁ :=
        (Subgroup.mem_normalizer_iff.mp (hXR (Subgroup.mem_sup_left hl)) _).mp (R₁.inv_mem hr)
      have e : r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) := by group
      rw [e]
      exact R₁.mul_mem hr hl'
    refine hle.trans (CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_
      (hR₁2.to_le inf_le_left))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun l hl =>
      mem_normalizer_inf (hXR (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  have hRK : ⁅R₁, K⁆ ≤ Q := hSig G K L₁ R₁ p n hp hp11 h.one_lt hpsl hL₁K
    (perfectCore_perfect _) ((h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁) hR₁2
    (hR₁T.trans hTK) (hR₁T.trans hTL₁) hRL
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hsc : R₁ ⊔ Q ≤ sectionCentralizer K Q := sup_le
    (fun r hr => ⟨hTK (hR₁T hr), hTQ (hR₁T hr), fun k hk => by
      have := Subgroup.commutator_le.mp hRK r hr k hk
      rwa [commutatorElement_def] at this⟩)
    (fun q hq => ⟨((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer) hq,
      Subgroup.le_normalizer hq, fun k hk => by
        have hk' : k * q⁻¹ * k⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hKQ hk) _).mp (Q.inv_mem hq)
        have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
        rw [e]
        exact Q.mul_mem hq hk'⟩)
  have hKN : K ≤ Subgroup.normalizer ((R₁ ⊔ Q : Subgroup G) : Set G) := fun k hk =>
    A4.mem_normalizer_of_conj_mem fun x hx => by
      have hxk := (hsc hx).2.2 k hk
      have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
      rw [e]
      exact (R₁ ⊔ Q).mul_mem (Subgroup.mem_sup_right (Q.inv_mem hxk)) hx
  have hRQT : R₁ ⊔ Q ≤ T := sup_le hR₁T hQT
  have hRO : R₁ ≤ pCoreOf 2 (K ⊔ T) := le_sup_left.trans
    (le_ROf' (hT2.to_le hRQT) (hRQT.trans le_sup_right)
      (sup_le hKN (le_normalizer_sup (le_sup_right.trans hXR) hTQ)))
  have hOR : pCoreOf 2 (K ⊔ T) ≤ R₁ :=
    le_ROf (pCoreOf_two_le_of_isSylowTwoOf
        (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (hL₁K.trans (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
      (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hKR : K ≤ Subgroup.normalizer (R₁ : Set G) := by
    have hReq : R₁ = pCoreOf 2 (K ⊔ T) := le_antisymm hRO hOR
    rw [hReq]
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  have h22 := h1122 G T L I n (2 * n) V₁ V₂ h hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)
  obtain ⟨hW0, hNW0, -⟩ := h22.2.2.2.2.2.1 hG2
  have hWR : E3.wClos (fsuV T I) 0 T ≤ R₁ := hW0.trans (inf_centralizer_le_ROf h1102 h hV₁)
  have hKM : K ≤ Subgroup.normalizer (L : Set G) := fun k hk => hNW0 (by
    rw [← wClos_zero_eq_of_le hR₁T hWR]
    exact E3.normalizer_le_normalizer_wClos R₁ (hKR hk))
  exact hlt.ne (kOf_eq_lOf_of_le (kOf_cComp h1110 h1112 h hV₁) (lOf_ne_bot h1110 h hV₁) hKM).symm

end CFSG.Quasithin.Vol2.Ch11.SecD
