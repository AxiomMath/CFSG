module

public import CFSG.Quasithin.EmptyFaithful.T1515Inputs
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S1519

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem Ce15Four.card_eq {T Mc M : Subgroup G} (h : Ce15Four T Mc M) :
    Nat.card (V154 T Mc M) = 16 := h.1

theorem Ce15Six.card_eq {T Mc M : Subgroup G} {p : ℕ} (h : Ce15Six T Mc M p) :
    Nat.card (V154 T Mc M) = 256 := h.1

theorem Ce15Seven.card_eq {T Mc M : Subgroup G} (h : Ce15Seven T Mc M) :
    Nat.card (V154 T Mc M) = 64 := h.1

theorem Ce15.card_ge {T Mc M : Subgroup G} (h : Ce15 T Mc M) : 16 ≤ Nat.card (V154 T Mc M) := by
  rcases h with h | ⟨p, -, h⟩ | h
  · rw [h.card_eq]
  · rw [h.card_eq]
    norm_num
  · rw [h.card_eq]
    norm_num

theorem Ce15Four.not_seven {T Mc M : Subgroup G} (h : Ce15Four T Mc M) : ¬ Ce15Seven T Mc M := by
  intro h7
  have := h.card_eq
  rw [h7.card_eq] at this
  omega

theorem Ce15Six.not_seven {T Mc M : Subgroup G} {p : ℕ} (h : Ce15Six T Mc M p) :
    ¬ Ce15Seven T Mc M := by
  intro h7
  have := h.card_eq
  rw [h7.card_eq] at this
  omega

theorem not_seven_of_four_or_six {T Mc M : Subgroup G}
    (h : Ce15Four T Mc M ∨ Ce15Six T Mc M 3) : ¬ Ce15Seven T Mc M := by
  rcases h with h | h
  · exact h.not_seven
  · exact h.not_seven

theorem ce15Small_of_four_or_six {T Mc M : Subgroup G}
    (h : Ce15Four T Mc M ∨ Ce15Six T Mc M 3) : Ce15Small T Mc M :=
  h.elim Or.inl fun h => Or.inr (Or.inl h)

namespace Setting1516

variable {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}

theorem z1_le_V (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : Z₁ ≤ V154 T Mc M :=
  h.z1_le.trans inf_le_left

theorem z2_le_V (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : Z₂ ≤ V154 T Mc M :=
  h.z2_le.trans inf_le_left

theorem V_le_T (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : V154 T Mc M ≤ T := by
  rw [h.hV]
  exact (isTwoReducedIn_VZ hq hM.1.1).2

theorem V_isElemAbelian (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : IsElemAbelian 2 (V154 T Mc M) := by
  rw [h.hV]
  exact isElemAbelian_VZ hq hM.1.1

theorem z1_isElemAbelian (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : IsElemAbelian 2 Z₁ :=
  isElemAbelian_mono151 h.z1_le_V (h.V_isElemAbelian hq hM)

theorem z1_le_T (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : Z₁ ≤ T := h.z1_le_V.trans (h.V_le_T hq hM)

theorem thompsonJi_le_self1516 (R : Subgroup G) (i : ℕ) : thompsonJi R i ≤ R :=
  iSup₂_le fun _ hA => hA.1

theorem z_le_vE_of_hV (hV : V154 T Mc M = VZ T M) :
    quasithinOmegaOneCenter T ≤ vE1516 T Mc M := by
  refine le_inf ?_ ?_
  · rw [hV]
    exact le_conjClosure _ _
  · intro z hz
    have hzc := (quasithinOmegaOneCenter_le_center T hz).2
    exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.mp hzc j (thompsonJi_le_self1516 T 1 hj)

theorem z_le_vE (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) :
    quasithinOmegaOneCenter T ≤ vE1516 T Mc M :=
  z_le_vE_of_hV h.hV

theorem z_le (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : quasithinOmegaOneCenter T ≤ Z₁ ⊔ V₂ := by
  by_cases h7 : Ce15Seven T Mc M
  · exact (h.z_le_vE.trans inf_le_left).trans (h.decomp_seven h7).1.ge
  · exact h.vE_sup.2.trans (sup_le_sup_left (h.z2_le_v2 h7) _)

theorem rank_pos (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) : 1 < CFSG.Open.pRank 2 T :=
  one_lt_pRank_of_card (h.V_isElemAbelian hq hM) (h.V_le_T hq hM)
    (by have := h.ce15.card_ge; omega)

theorem z1_le_g1 (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : Z₁ ≤ g1_1516 Z₁ := by
  intro a ha
  rw [g1_1516, Subgroup.mem_centralizer_iff]
  intro b hb
  have := h.z1_isElemAbelian hq hM
  have hc := this.1
  have := mul_comm' (⟨a, ha⟩ : Z₁) ⟨b, hb⟩
  exact (congrArg (fun z : Z₁ => (z : G)) this).symm

end Setting1516

theorem lemma_15_1_17 {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (h19 : Lemma1519Concl T Mc M) :
    Lemma15117Concl T M Z₁ := by
  have hZ1V : Z₁ ≤ V154 T Mc M := hS.z1_le_V
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hJS : thompsonJ T ≤ s1516 T Z₁ :=
    hJC.trans (inf_le_inf_left T (Subgroup.centralizer_le hZ1V))
  have hrank : 0 < CFSG.Open.pRank 2 T := by
    have := hS.rank_pos hq hM
    omega
  have hJ : thompsonJ (s1516 T Z₁) = thompsonJ T := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact (thompsonJi_eq_of_le hrank (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJS)
      (s1516_le T Z₁)).symm
  have hB : baum (s1516 T Z₁) = baum T :=
    (baum_eq_baum_centralizer (hS.z1_isElemAbelian hq hM) (hS.z1_le_T hq hM)
      (hJC.trans (inf_le_inf_left T (Subgroup.centralizer_le hZ1V)))).symm
  exact ⟨hS.sylow, hJ, hB, by rw [hB]; exact h19.one_cgs⟩

theorem lemma_15_1_18_one {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (h14 : Lemma15114Concl T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) :
    Z₁ ≤ vE1516 T Mc M ∧
      oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ mZ1516 Mc Z₁ := by
  refine ⟨hS.z1_le, fun x hx => ⟨?_, hq.centralizer_le_mc (oTwoUpper_le _ hx)⟩⟩
  exact Subgroup.centralizer_le hS.z1_le (h14.one (Ce15.not_case3b hS.ce15) hx)

theorem lemma_15_1_18_two_ne {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) :
    ¬ (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ≤ mZ1516 Mc Z₁ :=
  fun hle => hS.caseI (hle.trans (mZ1516_le_mc _ _))

omit [Finite G] in
theorem conjAct_mem_oTwoUpper_autOn {K V : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G))
    {y : G} (hyK : y ∈ K) (hyodd : Odd (orderOf y)) :
    conjAct V ⟨y, hKN hyK⟩ ∈ oTwoUpper (autOn K V) := by
  apply mem_oTwoUpper_of_odd
  · exact mem_autOn_iff_exists.mpr ⟨y, hKN hyK, hyK, rfl⟩
  · have h1 : orderOf (conjAct V ⟨y, hKN hyK⟩) ∣
        orderOf (⟨y, hKN hyK⟩ : Subgroup.normalizer (V : Set G)) := orderOf_map_dvd _ _
    have h2 : orderOf (⟨y, hKN hyK⟩ : Subgroup.normalizer (V : Set G)) = orderOf y :=
      (Subgroup.orderOf_coe _).symm
    exact Odd.of_dvd_nat hyodd (h2 ▸ h1)

theorem lemma_15_1_18_two_eq {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (hX : Setting1516Extra T Mc M Z₁)
    (h15 : Lemma1515Concl T Mc M) :
    oTwoUpper (M ⊓ Mc ⊓ g1_1516 Z₁) =
      oTwoUpper (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  set V := V154 T Mc M with hVdef
  have hZ1V : Z₁ ≤ V := hS.z1_le_V
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V154 T Mc M
  have hAK0 : M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := fun x hx =>
    ⟨⟨hx.1, h15.centralizer_le hx.2⟩, Subgroup.centralizer_le hZ1V hx.2⟩
  refine le_antisymm ?_ (oTwoUpper_mono hAK0)
  have hne := lemma_15_1_18_two_ne hS
  set K : Subgroup G := M ⊓ g1_1516 Z₁ with hK
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hMN
  have hKsyl : K = oTwoUpper K ⊔ s1516 T Z₁ := by
    have h := hS.sylow
    rw [inf_comm] at h
    exact eq_oTwoUpper_sup_of_isSylowTwoOf h
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxK0, hxodd⟩
  by_contra hxA
  have hxV : x ∉ Subgroup.centralizer (V : Set G) := fun hxc =>
    hxA (mem_oTwoUpper_of_odd ⟨hxK0.1.1, hxc⟩ hxodd)
  have hxK : x ∈ K := ⟨hxK0.1.1, hxK0.2⟩
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hKN hxK
  set O := oTwoUpper (autOn K V) with hO
  have hxbarO : conjAct V ⟨x, hxN⟩ ∈ O := conjAct_mem_oTwoUpper_autOn hKN hxK hxodd
  have hxbar_ne : conjAct V ⟨x, hxN⟩ ≠ 1 := fun h => hxV (A4.conjAct_eq_one_iff.mp h)
  have hcardO : (Nat.card O).Prime := hX.prime_o2
  have hzO : Subgroup.zpowers (conjAct V ⟨x, hxN⟩) = O := by
    have hle : Subgroup.zpowers (conjAct V ⟨x, hxN⟩) ≤ O := Subgroup.zpowers_le.mpr hxbarO
    have hdvd := Subgroup.card_dvd_of_le hle
    have hne1 : Nat.card (Subgroup.zpowers (conjAct V ⟨x, hxN⟩)) ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at h1
      exact hxbar_ne h1
    have : Nat.card (Subgroup.zpowers (conjAct V ⟨x, hxN⟩)) = Nat.card O := by
      rcases (Nat.dvd_prime hcardO).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle this.ge
  have hodd_mem : ∀ y ∈ K, Odd (orderOf y) → y ∈ M ⊓ Mc ⊓ g1_1516 Z₁ := by
    intro y hyK hyodd
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hKN hyK
    have hybarO : conjAct V ⟨y, hyN⟩ ∈ O := conjAct_mem_oTwoUpper_autOn hKN hyK hyodd
    rw [← hzO] at hybarO
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hybarO
    have hxjK0 : x ^ j ∈ M ⊓ Mc ⊓ g1_1516 Z₁ := Subgroup.zpow_mem _ hxK0 j
    have hxjN : x ^ j ∈ Subgroup.normalizer (V : Set G) := hMN hxjK0.1.1
    have hw : y * (x ^ j)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : conjAct V (⟨y, hyN⟩ * (⟨x, hxN⟩ ^ j)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hj, mul_inv_cancel]
      have h2 := A4.conjAct_eq_one_iff.mp h1
      simpa using h2
    have hwM : y * (x ^ j)⁻¹ ∈ M := M.mul_mem hyK.1 (M.inv_mem hxjK0.1.1)
    have hwK0 : y * (x ^ j)⁻¹ ∈ M ⊓ Mc ⊓ g1_1516 Z₁ := hAK0 ⟨hwM, hw⟩
    have := (M ⊓ Mc ⊓ g1_1516 Z₁).mul_mem hwK0 hxjK0
    simpa using this
  have hO2K : oTwoUpper K ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyK, hyodd⟩
    exact hodd_mem y hyK hyodd
  have hSK0 : s1516 T Z₁ ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := fun y hy =>
    ⟨⟨hM.1.1.2 (hy.1), hq.t_le_mc hy.1⟩, hy.2⟩
  have hKK0 : K ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := by
    rw [hKsyl]
    exact sup_le hO2K hSK0
  exact hne fun y hy => ⟨hKK0 hy |>.2, (hKK0 hy).1.2⟩

theorem eq_of_isSylowTwoOf_of_le1516 {S Q H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hQ : IsPGroup 2 Q) (hSQ : S ≤ Q) (hQH : Q ≤ H) : Q = S := by
  have hmul := Subgroup.relIndex_mul_relIndex S Q H hSQ hQH
  have hodd : ¬ 2 ∣ S.relIndex H := hS.2.2
  have hodd1 : ¬ 2 ∣ S.relIndex Q := fun h => hodd (h.trans ⟨_, hmul.symm⟩)
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : S.relIndex Q ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card S Q
  obtain ⟨m, -, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm : m = 0 := by
    by_contra hm0
    exact hodd1 (hmeq ▸ dvd_pow_self 2 hm0)
  have h1 : S.relIndex Q = 1 := by rw [hmeq, hm, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSQ

theorem isSylowTwoOf_of_normalizer_le1516 {S H K : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSH : S ≤ H) (hK : IsSylowTwoOf S K) (hNK : H ⊓ Subgroup.normalizer (S : Set G) ≤ K) :
    IsSylowTwoOf S H := by
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS2.comap_of_injective _ Subtype.val_injective
  obtain ⟨P, hSP⟩ := hS'.exists_le_sylow
  refine ⟨hSH, hS2, ?_⟩
  have hPeq : S.subgroupOf H = (P : Subgroup H) := by
    by_contra hne
    have hlt : S.subgroupOf H < (P : Subgroup H) := lt_of_le_of_ne hSP hne
    have : Group.IsNilpotent (P : Subgroup H) := P.isPGroup'.isNilpotent
    have hlt' : (S.subgroupOf H).subgroupOf (P : Subgroup H) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact absurd htop (not_le_of_gt hlt)
    obtain ⟨x, hxn, hxS⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
    set g : G := ((x : H) : G) with hg
    have hgH : g ∈ H := (x : H).2
    have key : ∀ y : (P : Subgroup H),
        y ∈ Subgroup.normalizer (((S.subgroupOf H).subgroupOf (P : Subgroup H) :
          Subgroup (P : Subgroup H)) : Set (P : Subgroup H)) →
        ∀ s ∈ S, ((y : H) : G) * s * ((y : H) : G)⁻¹ ∈ S := by
      intro y hy s hs
      have hs' : (⟨s, hSH hs⟩ : H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hs
      have hsP : (⟨⟨s, hSH hs⟩, hSP hs'⟩ : (P : Subgroup H)) ∈
          (S.subgroupOf H).subgroupOf (P : Subgroup H) := Subgroup.mem_subgroupOf.mpr hs'
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp hsP
    have hgN : g ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · exact key x hxn s
      · intro hgs
        have h2 := key x⁻¹ (Subgroup.inv_mem _ hxn) _ hgs
        simpa [hg, mul_assoc] using h2
    have hgK : g ∈ K := hNK ⟨hgH, hgN⟩
    set Q : Subgroup G := S ⊔ Subgroup.zpowers g with hQ
    have hQP : Q ≤ (P : Subgroup H).map H.subtype := by
      refine sup_le ?_ ?_
      · intro s hs
        have hs' : (⟨s, hSH hs⟩ : H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hs
        exact ⟨⟨s, hSH hs⟩, hSP hs', rfl⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨(x : H), x.2, rfl⟩
    have hQ2 : IsPGroup 2 Q := (P.isPGroup'.map H.subtype).to_le hQP
    have hQK : Q ≤ K := sup_le hK.1 (Subgroup.zpowers_le.mpr hgK)
    have hQS : Q = S := eq_of_isSylowTwoOf_of_le1516 hK hQ2 le_sup_left hQK
    have hgS : g ∈ S := hQS ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
    exact hxS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hgS))
  rw [hPeq]
  exact P.not_dvd_index

omit [Finite G] in
theorem normalizer_le_normalizer_of_char1516 {Q C : Subgroup G} (hCQ : C ≤ Q)
    (hchar : (C.subgroupOf Q).Characteristic) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := Q)
    (C.subgroupOf Q)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at this

theorem lemma_15_1_18_four {T Mc M Z₁ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (h17 : Lemma15117Concl T M Z₁) :
    IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := by
  have hS2 : IsPGroup 2 (s1516 T Z₁) := hq.sylow.1.to_le (s1516_le T Z₁)
  have hbaum : baum (s1516 T Z₁) ≠ ⊥ := by
    rw [h17.baumS]
    exact baum_ne_bot hq
  have hNM : Subgroup.normalizer (s1516 T Z₁ : Set G) ≤ M :=
    (normalizer_le_normalizer_baum _).trans ((normalizer_le_cgs hbaum).trans h17.cgs)
  exact isSylowTwoOf_of_normalizer_le1516 hS2 (s1516_le_g1 T Z₁) h17.sylow
    (fun x hx => ⟨hx.1, hNM hx.2⟩)

theorem lemma_15_1_18_seven_isUniqueM {T Mc Z₁ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (h1 : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      mZ1516 Mc Z₁) : IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc := by
  refine ⟨⟨hq.mc_max, sup_le (mZ1516_le_mc _ _) hq.t_le_mc⟩, fun M' hM' => ?_⟩
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := (quasithinOmegaOneCenter_le_center T hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzc t ht).symm
  have hsyl : IsSylowTwoOf T (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    isSylowTwoOf_of_le151 hq.sylow hTC
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M' :=
    (eq_oTwoUpper_sup_of_isSylowTwoOf hsyl).le.trans
      (sup_le (h1.trans (le_sup_left.trans hM'.2)) (le_sup_right.trans hM'.2))
  exact hq.mc_unique M' hM'.1 hCZ

theorem normalizer_le_mc_of_char1516 {T Mc Z₁ C : Subgroup G}
    (hU : IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc) (h3 : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G))
    (hCQ : C ≤ q1_1516 Mc Z₁) (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf (q1_1516 Mc Z₁)).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ Mc := by
  have hMZN : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hN : mZ1516 Mc Z₁ ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    (sup_le hMZN h3).trans (normalizer_le_normalizer_of_char1516 hCQ hchar)
  have hC2 : IsPGroup 2 C := (pCoreOf_isPGroup 2 _).to_le hCQ
  obtain ⟨M', hM', hle⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G)) ⟨C, hC1, hC2, rfl⟩
  have : M' = Mc := hU.2 M' ⟨hM', hN.trans hle⟩
  rw [← this]
  exact hle

theorem lemma_15_1_18_seven_cgs {T Mc Z₁ : Subgroup G}
    (hU : IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc) (h3 : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)) :
    CGS (q1_1516 Mc Z₁) ≤ Mc := by
  unfold CGS
  exact iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hchar =>
    normalizer_le_mc_of_char1516 hU h3 hCQ hC1 hchar

theorem lemma_15_1_18_seven {T Mc M Z₁ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (h14 : Lemma15114Concl T Mc M) {Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (h3 : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)) :
    IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc ∧ CGS (q1_1516 Mc Z₁) ≤ Mc := by
  have hU := lemma_15_1_18_seven_isUniqueM hq (lemma_15_1_18_one hq h14 hS).2
  exact ⟨hU, lemma_15_1_18_seven_cgs hU h3⟩

theorem lemma_15_1_18_five {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂)
    (hU : IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc) (h3 : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)) :
    cgsIn (g1_1516 Z₁) (q1_1516 Mc Z₁) = mZ1516 Mc Z₁ ∧
      mZ1516 Mc Z₁ = g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) ∧
      HypC23 (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) := by
  have hZ1p : IsPGroup 2 Z₁ := isPGroup_of_isElemAbelian (hS.z1_isElemAbelian hq hM)
  have hZ1G : Z₁ ≤ g1_1516 Z₁ := hS.z1_le_g1 hq hM
  have hZ1MZ : Z₁ ≤ mZ1516 Mc Z₁ := le_inf hZ1G (hS.z1_le_T hq hM |>.trans hq.t_le_mc)
  have hMZN1 : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (Z₁ : Set G) :=
    (mZ1516_le_g1 Mc Z₁).trans (Subgroup.centralizer_le_normalizer _)
  have hZ1Q : Z₁ ≤ q1_1516 Mc Z₁ := le_pCoreOf_of_le_normalizer 2 hZ1MZ hMZN1 hZ1p
  have hQne : q1_1516 Mc Z₁ ≠ ⊥ := fun h =>
    hS.z1_ne (le_bot_iff.mp (h ▸ hZ1Q))
  have hcgs_le : cgsIn (g1_1516 Z₁) (q1_1516 Mc Z₁) ≤ mZ1516 Mc Z₁ := by
    unfold cgsIn
    exact iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hchar =>
      le_inf inf_le_left ((inf_le_right).trans
        (normalizer_le_mc_of_char1516 hU h3 hCQ hC1 hchar))
  have hMZ_N : mZ1516 Mc Z₁ ≤ g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) :=
    le_inf (mZ1516_le_g1 Mc Z₁) (le_normalizer_pCoreOf 2 _)
  have hN_cgs : g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) ≤
      cgsIn (g1_1516 Z₁) (q1_1516 Mc Z₁) := inf_normalizer_le_cgsIn hQne
  have hcgs_eq : cgsIn (g1_1516 Z₁) (q1_1516 Mc Z₁) = mZ1516 Mc Z₁ :=
    le_antisymm hcgs_le (hMZ_N.trans hN_cgs)
  have hmz_eq : mZ1516 Mc Z₁ = g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) :=
    le_antisymm hMZ_N (hN_cgs.trans hcgs_le)
  refine ⟨hcgs_eq, hmz_eq, ?_⟩
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := fun h =>
    hS.z1_ne (le_bot_iff.mp (h ▸ le_pCoreOf_of_le_normalizer 2 hZ1G
      (Subgroup.centralizer_le_normalizer _) hZ1p))
  have hsqtk : IsSQTKIn (g1_1516 Z₁) :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc,
      kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc⟩
  have hQp : IsPGroup 2 (q1_1516 Mc Z₁) := pCoreOf_isPGroup 2 _
  refine ⟨hsqtk, ⟨(q1_1516_le Mc Z₁).trans (mZ1516_le_g1 Mc Z₁), hQne, ?_⟩, mZ1516_le_g1 Mc Z₁,
    hcgs_le, ?_⟩
  · rw [← hmz_eq]
    rfl
  · have hcc : conjClosure (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) = q1_1516 Mc Z₁ := by
      refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (le_conjClosure _ _)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) z).mp hz
    rw [hcc]
    refine ⟨le_rfl, hQp, ?_⟩
    simp

theorem lemma_15_1_18_six (h116 : AS116Statement) {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂)
    (h4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁)) :
    ∀ z : G, z ∈ quasithinOmegaOneCenter T → z ≠ 1 →
      Lemma115Hyp (g1_1516 Z₁) (s1516 T Z₁) Mc z := by
  intro z hz hz1
  have hzm := mem_quasithinOmegaOneCenter_iff.mp hz
  refine h116 G hq.qtke.2.1 Z₁ (g1_1516 Z₁) (s1516 T Z₁) T Mc z
    (isPGroup_of_isElemAbelian (hS.z1_isElemAbelian hq hM)) hS.z1_ne
    (sup_le (hS.z1_le_g1 hq hM) le_rfl) (Subgroup.centralizer_le_normalizer _) h4
    (isSylowTwoOf_of_le151 hq.sylow le_top) (s1516_le T Z₁) hzm.1 hzm.2.1 hz1 hzm.2.2
    hq.mc_max (centralizer_singleton_le_mc_of_mem_omegaOneCenter hq hz hz1)

theorem exists_eq_mul_of_isSylowTwoOf1516 {H T : Subgroup G} (hT : IsSylowTwoOf T H) {x : G}
    (hx : x ∈ H) : ∃ t ∈ T, ∃ o ∈ oTwoUpper H, x = t * o := by
  classical
  have hNH : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNH
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H y.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  set f : ↥H →* (↥H ⧸ (oTwoUpper H).subgroupOf H) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := T.subgroupOf H) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((T.subgroupOf H).map f)
  have hodd : ¬ 2 ∣ (T.subgroupOf H).index := hT.2.2
  have h1 : ((T.subgroupOf H).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      refine hodd ?_
      rw [hn] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  rw [Subgroup.index_eq_one] at h1
  have hmem : f ⟨x, hx⟩ ∈ (T.subgroupOf H).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t : ↥H)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper H).subgroupOf H := by
    rw [← QuotientGroup.eq]
    exact hteq
  refine ⟨t, Subgroup.mem_subgroupOf.mp ht, (t : G)⁻¹ * x, Subgroup.mem_subgroupOf.mp h2, ?_⟩
  group

theorem lemma_15_1_18_three {T Mc M Z₁ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hX : Setting1516Extra T Mc M Z₁) (h19 : Lemma1519Concl T Mc M)
    (h1 : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ mZ1516 Mc Z₁)
    (h2 : oTwoUpper (M ⊓ Mc ⊓ g1_1516 Z₁) =
      oTwoUpper (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
    (h4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁)) :
    T ≤ Subgroup.normalizer (mZ1516 Mc Z₁ : Set G) ∧
      T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := by
  set MZ := mZ1516 Mc Z₁ with hMZ
  set B : Subgroup G := Mc ⊓ Subgroup.centralizer (VZ T Mc : Set G) with hB
  have hTM : T ≤ M := hM.1.1.2
  have hTMc : T ≤ Mc := hq.t_le_mc
  have hTMcS : IsSylowTwoOf T Mc := isSylowTwoOf_of_le151 hq.sylow hTMc
  have hBN : Mc ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer
      ((le_normalizer_VZ T Mc).trans (normalizer_le_normalizer_centralizer _))
  have hBC : B ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    Subgroup.centralizer_le (le_conjClosure (quasithinOmegaOneCenter T) Mc) hx.2
  have hPMZ : oTwoUpper B ≤ MZ := (oTwoUpper_mono hBC).trans h1
  have hPN : Mc ≤ Subgroup.normalizer (oTwoUpper B : Set G) :=
    hBN.trans (normalizer_le_normalizer_oTwoUpper B)
  have hBsyl : IsSylowTwoOf (T ⊓ B) B := A4.isSylowTwoOf_inf_normal hTMcS inf_le_left hBN
  have hord : OrdLE T Mc M := h19.two.2 Mc hq.inM_mc
  set K₀ : Subgroup G := M ⊓ Mc ⊓ g1_1516 Z₁ with hK₀
  have hK₀MZ : K₀ ≤ MZ := fun x hx => ⟨hx.2, hx.1.2⟩
  have hdec : ∀ x ∈ MZ, ∃ n ∈ K₀, ∃ o ∈ oTwoUpper B, x = n * o := by
    intro x hx
    obtain ⟨a, ha, c, hc, hxac⟩ := hord x hx.2
    obtain ⟨r, hr, o, ho, hco⟩ := exists_eq_mul_of_isSylowTwoOf1516 hBsyl (show c ∈ B from hc)
    have hxn : x = (a * r) * o := by rw [hxac, hco, mul_assoc]
    have hoMZ : o ∈ MZ := hPMZ ho
    have hn : a * r ∈ K₀ := by
      have hnMZ : a * r ∈ MZ := by
        have : a * r = x * o⁻¹ := by rw [hxn]; group
        rw [this]
        exact MZ.mul_mem hx (MZ.inv_mem hoMZ)
      refine ⟨⟨M.mul_mem ha.2 (hTM hr.1), Mc.mul_mem ha.1 (hTMc hr.1)⟩, hnMZ.1⟩
    exact ⟨a * r, hn, o, ho, hxn⟩
  set U : Subgroup G := oTwoUpper K₀ ⊔ oTwoUpper B with hU
  have hU1 : oTwoUpper MZ ≤ U := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨n, hn, o, ho, rfl⟩ := hdec x hx
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K₀ hn
    have hnN : n ∈ Subgroup.normalizer (oTwoUpper B : Set G) := hPN hn.1.2
    have hxo : n * o * n⁻¹ ∈ oTwoUpper B := (Subgroup.mem_normalizer_iff.mp hnN o).mp ho
    obtain ⟨y, hy, hyeq⟩ := A4.exists_pow_mul_eq hxo hnN (2 ^ k)
    refine ⟨k, ?_⟩
    have : n * o = (n * o * n⁻¹) * n := by group
    rw [this, hyeq]
    exact U.mul_mem ((le_sup_right : oTwoUpper B ≤ U) hy) ((le_sup_left : oTwoUpper K₀ ≤ U) hk)
  have hU2 : U ≤ oTwoUpper MZ := by
    refine sup_le (oTwoUpper_mono hK₀MZ) ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxB, hxodd⟩
    exact mem_oTwoUpper_of_odd (h1 (mem_oTwoUpper_of_odd (hBC hxB) hxodd)) hxodd
  have hOMZ : oTwoUpper MZ = oTwoUpper (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔
      oTwoUpper B := by
    rw [← h2]
    exact le_antisymm hU1 hU2
  set A : Subgroup G := M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) with hA
  have hMA : M ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer
      ((le_normalizer_V154 T Mc M).trans (normalizer_le_normalizer_centralizer _))
  have hTA : T ≤ Subgroup.normalizer (oTwoUpper A : Set G) :=
    (hTM.trans hMA).trans (normalizer_le_normalizer_oTwoUpper A)
  have hTO : T ≤ Subgroup.normalizer (oTwoUpper MZ : Set G) := by
    rw [hOMZ]
    exact fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hTA ht, hTMc.trans hPN ht⟩
  have hSle : s1516 T Z₁ ≤ MZ := le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans hTMc)
  have hSmz : IsSylowTwoOf (s1516 T Z₁) MZ := A4.isSylowTwoOf_mono h4 hSle (mZ1516_le_g1 Mc Z₁)
  have hmzeq : MZ = oTwoUpper MZ ⊔ s1516 T Z₁ := eq_oTwoUpper_sup_of_isSylowTwoOf hSmz
  have hTMZ : T ≤ Subgroup.normalizer (MZ : Set G) := by
    have : T ≤ Subgroup.normalizer ((oTwoUpper MZ ⊔ s1516 T Z₁ : Subgroup G) : Set G) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hTO ht, hX.s_normal ht⟩
    rwa [← hmzeq] at this
  exact ⟨hTMZ, hTMZ.trans (normalizer_le_normalizer_pCoreOf 2 MZ)⟩

theorem lemma_15_1_18_of_q3 (h116 : AS116Statement) {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h14 : Lemma15114Concl T Mc M)
    (h17 : Lemma15117Concl T M Z₁) (hq3 : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)) :
    Lemma15118Concl T Mc M Z₁ := by
  have h1 := lemma_15_1_18_one hC.qtfe h14 hC.setting
  have h4 := lemma_15_1_18_four hC.qtfe h17
  have h7 := lemma_15_1_18_seven hC.qtfe h14 hC.setting hq3
  exact ⟨h1, lemma_15_1_18_two_ne hC.setting, hq3, h4,
    lemma_15_1_18_five hC.qtfe hC.mf hC.setting h7.1 hq3,
    lemma_15_1_18_six h116 hC.qtfe hC.mf hC.setting h4, h7⟩

theorem lemma_15_1_18_extra_q3 {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (hX : Setting1516Extra T Mc M Z₁)
    (h15 : Lemma1515Concl T Mc M) (h14 : Lemma15114Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h17 : Lemma15117Concl T M Z₁) :
    Lemma15118Extra T Mc M Z₁ ∧ T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := by
  have h1 := lemma_15_1_18_one hC.qtfe h14 hC.setting
  have h2 := lemma_15_1_18_two_eq hC.qtfe hC.mf hC.setting hX h15
  have h4 := lemma_15_1_18_four hC.qtfe h17
  obtain ⟨hmz, hq3⟩ := lemma_15_1_18_three hC.qtfe hC.mf hX h19 h1.2 h2 h4
  exact ⟨⟨h2, hX.s_normal, hmz⟩, hq3⟩

theorem lemma_15_1_18_extra {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (hX : Setting1516Extra T Mc M Z₁)
    (h15 : Lemma1515Concl T Mc M) (h14 : Lemma15114Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h17 : Lemma15117Concl T M Z₁) : Lemma15118Extra T Mc M Z₁ :=
  (lemma_15_1_18_extra_q3 hC hX h15 h14 h19 h17).1

theorem lemma_15_1_18 (h116 : AS116Statement) {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (hX : Setting1516Extra T Mc M Z₁)
    (h15 : Lemma1515Concl T Mc M) (h14 : Lemma15114Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h17 : Lemma15117Concl T M Z₁) : Lemma15118Concl T Mc M Z₁ :=
  lemma_15_1_18_of_q3 h116 hC h14 h17 (lemma_15_1_18_extra_q3 hC hX h15 h14 h19 h17).2

end CFSG.Quasithin
