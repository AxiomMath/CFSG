module

public import CFSG.Quasithin.Background.E6TwentyThreeH
public import CFSG.Quasithin.Background.E6TwentyThree

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623A3Layer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L U₀ X : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 3 → ¬ L ≤ M →
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) = ⊥ →
    U₀ < U → E3.mQuot V U₀ ≤ 2 →
    IsComponentIn X (Subgroup.centralizer (U₀ : Set G)) → ⁅L, X⁆ = ⊥

section Layer

variable {G : Type} [Group G] [Finite G]

@[expose] def compJoin (H : Subgroup G) : Subgroup G := sSup {X | IsComponentIn X H}

omit [Finite G] in
theorem le_normalizer_compJoin (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((compJoin H : Subgroup G) : Set G) := by
  have hle : ∀ g ∈ H, (compJoin H).map (MulAut.conj g).toMonoidHom ≤ compJoin H := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ?_
    have h := BenderBranch.isComponentIn_map (MulAut.conj g) hX
    have hHg : H.map (MulAut.conj g).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    rwa [hHg] at h
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hle k hk) ?_
  intro y hy
  have h := hle k⁻¹ (inv_mem hk) ⟨y, hy, rfl⟩
  refine ⟨(MulAut.conj k⁻¹).toMonoidHom y, h, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem le_normalizer_centralizer_compJoin (H : Subgroup G) :
    H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer ((compJoin H : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hHE := le_normalizer_compJoin H
  have key : ∀ g ∈ H, ∀ n ∈ H ⊓ Subgroup.centralizer ((compJoin H : Subgroup G) : Set G),
      g * n * g⁻¹ ∈ H ⊓ Subgroup.centralizer ((compJoin H : Subgroup G) : Set G) := by
    intro g hg n hn
    obtain ⟨hnH, hnC⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hnH) (inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : g⁻¹ * b * g ∈ compJoin H := by
      have := (Subgroup.mem_normalizer_iff.mp (hHE (inv_mem hg)) b).mp hb
      simpa using this
    have h := (Subgroup.mem_centralizer_iff.mp hnC) _ hb'
    calc b * (g * n * g⁻¹) = g * ((g⁻¹ * b * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
      _ = g * n * g⁻¹ * b := by group
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨key k hk n, fun h => ?_⟩
  have := key k⁻¹ (inv_mem hk) _ h
  simpa [mul_assoc] using this

theorem charTwo_centralizer_compJoin_sup {H Q : Subgroup G} (hO : oddCoreIn H = ⊥)
    (hQ2 : IsPGroup 2 Q) (hQH : Q ≤ H) :
    CharTwo ((H ⊓ Subgroup.centralizer ((compJoin H : Subgroup G) : Set G)) ⊔ Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := H ⊓ Subgroup.centralizer ((compJoin H : Subgroup G) : Set G) with hC
  have hHC := le_normalizer_centralizer_compJoin H
  have hCH : C ≤ H := inf_le_left
  have hKH : C ⊔ Q ≤ H := sup_le hCH hQH
  have hQC : Q ≤ Subgroup.normalizer (C : Set G) := hQH.trans hHC
  have hCn : IsSubnormal C H := IsSubnormal.step hCH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC) (IsSubnormal.refl H)
  refine DoubleA3.charTwo_of_no_component ?_ ?_
  ·
    intro Y hY
    rw [DoubleA3.isComponentIn_iff_open] at hY
    obtain ⟨hYK, hYsub, hYq⟩ := hY
    have hperf : Group.IsPerfect ↥Y := ⟨hYq.1⟩
    have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    have hYC : Y ≤ C := B1Red.perfect_le_of_nilpotent_quotient (N := C ⊔ Q) le_sup_right
      le_sup_left (fun n hn m hm => (Subgroup.mem_normalizer_iff.mp (hHC (hKH hn)) m).mp hm)
      hYK (by rw [sup_comm]; exact hYK) hperf
    have hYH : IsComponentIn Y H := DoubleA3.isComponentIn_iff_open.mpr
      ⟨hYC.trans hCH,
        A3Push.isSubnormal_trans (A4.subnormal_of_le_of_le hYsub hYC le_sup_left) hCn, hYq⟩
    have hYJ : Y ≤ compJoin H := le_sSup hYH
    have hcen : Subgroup.center ↥Y = ⊤ := by
      refine eq_top_iff.mpr fun y _ => Subgroup.mem_center_iff.mpr fun z => ?_
      apply Subtype.ext
      have hz := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hYC z.2)).2) y (hYJ y.2)
      simpa using hz.symm
    obtain ⟨p, q, hpq⟩ := (hYq.2).toNontrivial.exists_pair_ne
    apply hpq
    induction p using QuotientGroup.induction_on with
    | H y₁ =>
      induction q using QuotientGroup.induction_on with
      | H y₂ =>
        rw [QuotientGroup.eq, hcen]
        exact Subgroup.mem_top _
  ·
    have hOK := E3.oddCoreIn_le (C ⊔ Q)
    have hOodd := E3.odd_card_oddCoreIn' (C ⊔ Q)
    have hOC : oddCoreIn (C ⊔ Q) ≤ C := by
      intro y hy
      obtain ⟨n, hn⟩ := Vol2Native.L239.exists_pow_mem_of_mem_sup hQ2 hQC (hOK hy)
      have hodd : Odd (orderOf y) := by
        have h1 : orderOf (⟨y, hy⟩ : ↥(oddCoreIn (C ⊔ Q))) ∣ Nat.card ↥(oddCoreIn (C ⊔ Q)) :=
          orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hOodd h1
      have hy' : y ∈ Subgroup.zpowers (y ^ 2 ^ n) := by
        rw [mem_zpowers_pow_iff]
        exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
      exact (Subgroup.zpowers_le.mpr hn) hy'
    have h1 : oddCoreIn (C ⊔ Q) ≤ oddCoreIn C :=
      le_oddCoreIn_of_odd hOC ((le_sup_left : C ≤ C ⊔ Q).trans (le_normalizer_oddCoreIn _))
        hOodd
    have h2 : oddCoreIn C ≤ oddCoreIn H :=
      oddCoreIn_le_of_subnormal'' hCH
        (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC))
    exact le_bot_iff.mp (hO ▸ h1.trans h2)

end Layer

section CaseB

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem centralizer_inf_inf_centralizer (h : HypE61 T M V) (hUV : U ≤ V) {U' : Subgroup G}
    (hU'1 : E3.mQuot V U' = 1) {a : G} (haU : a ∈ U) (haU' : a ∉ U') :
    Subgroup.centralizer ((U ⊓ U' : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer (U : Set G) := by
  have hU'i : U'.relIndex V = 2 := by
    rw [E3.relIndex_eq_two_pow h.isPGroup_V, hU'1, pow_one]
  apply le_antisymm
  · intro g hg
    obtain ⟨hg₀, hga⟩ := Subgroup.mem_inf.mp hg
    have hle : U ≤ Subgroup.centralizer ({g} : Set G) := by
      refine (le_inf_sup_zpowers hUV hU'i haU haU').trans (sup_le ?_ ?_)
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hg₀) u hu
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hga).symm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
  · exact le_inf (Subgroup.centralizer_le inf_le_left) (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr haU))

theorem centralizer_data (h : HypE61 T M V) {U₀ : Subgroup G} (hΓ : U₀ ∈ gammaE64 V M) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.centralizer (U₀ : Set G)) ∧
      cgsIn (Subgroup.centralizer (U₀ : Set G)) (T ⊓ Subgroup.centralizer (V : Set G)) ≤ M ∧
      IsSQTKIn (Subgroup.centralizer (U₀ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨e6_5_one h hΓ, (e6_5_two h hΓ).1.trans inf_le_right, ?_⟩
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hU₀V : U₀ ≤ V := hΓ.1
  have hU₀C : U₀ ≤ Subgroup.centralizer (U₀ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v (hU₀V hv) u (hU₀V hu)
  have hO2 : pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) ≠ ⊥ := by
    intro h0
    apply hΓ.2.1
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hU₀C
      (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hU₀V)
    rw [h0] at this
    exact le_bot_iff.mp this
  exact ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
    kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩

end CaseB

theorem e623A3Dichotomy_of_layer (h311 : Theorem311Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (h621 : E621Stmt)
    (hLay : E623A3Layer) : E623A3Dichotomy := by
  intro G _ _ T M V U L hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM
  classical
  by_cases hZ : U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) = ⊥
  swap
  · exact e623A3Dichotomy_of_inf_ne_bot (hC129 G) hV h hm hUV hU1 hH hLb hL3 hLM hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.normal
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h (Or.inr hm) hr1).2
  have hconjV : ∀ s ∈ T, CFSG.conjugate U s ≤ V ∧ E3.mQuot V (CFSG.conjugate U s) = 1 :=
    fun s hs => ⟨conjugate_le_of_mem_normalizer hUV (hTN hs),
      (mQuot_conjugate (hTN hs)).trans hU1⟩
  have hconjB : ∀ {X Y : Subgroup G} (s : G), IsBlock2 X Y →
      IsBlock2 (CFSG.conjugate X s) (CFSG.conjugate Y s) := fun s hY =>
    Setup.Campbell.isBlock2_map_conj hY s⁻¹
  have hcardU : ∀ s : G, Nat.card (CFSG.conjugate U s) = Nat.card U :=
    BenderBranch.card_conjugate U
  intro t ht
  by_cases hUU : U ≤ CFSG.conjugate U t
  ·
    have hUeq : CFSG.conjugate U t = U :=
      (Subgroup.eq_of_le_of_card_ge hUU (hcardU t).le).symm
    have hLt : IsBlock2 (Subgroup.centralizer (U : Set G)) (CFSG.conjugate L t) := by
      have := hconjB t hLb.1
      rwa [BenderBranch.conjugate_centralizer, hUeq] at this
    by_cases hLL : L = CFSG.conjugate L t
    · exact Or.inl hLL.symm
    · exact Or.inr (distinctBlocksCommuteStatement _ L _ hH hLb.1 hLt hLL)
  have hUU' : ¬ U ≤ CFSG.conjugate U t⁻¹ := by
    intro hle
    apply hUU
    have h1 := BenderBranch.conjugate_mono hle t
    rw [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one] at h1
    have h2 := Subgroup.eq_of_le_of_card_ge h1 (hcardU t).ge
    rw [h2]
  have hcorank : ∀ s ∈ T, ¬ U ≤ CFSG.conjugate U s →
      U ⊓ CFSG.conjugate U s < U ∧ E3.mQuot V (U ⊓ CFSG.conjugate U s) ≤ 2 ∧
        U ⊓ CFSG.conjugate U s ≠ ⊥ := by
    intro s hs hUs
    have hq : E3.mQuot V (U ⊓ CFSG.conjugate U s) ≤ 2 := by
      have := mQuot_inf_le (U := U) (U' := CFSG.conjugate U s) hV2
      rw [hU1, (hconjV s hs).2] at this
      exact this
    refine ⟨lt_of_le_of_ne (inf_le_left : U ⊓ CFSG.conjugate U s ≤ U) fun heq => hUs ?_, hq,
      fun h0 => ?_⟩
    · calc U = U ⊓ CFSG.conjugate U s := heq.symm
        _ ≤ CFSG.conjugate U s := inf_le_right
    · rw [h0] at hq; omega
  obtain ⟨hU₀lt, hU₀q, hU₀1⟩ := hcorank t ht hUU
  obtain ⟨hU₁lt, hU₁q, -⟩ := hcorank t⁻¹ (inv_mem ht) hUU'
  set U₀ : Subgroup G := U ⊓ CFSG.conjugate U t with hU₀
  set H₀ : Subgroup G := Subgroup.centralizer (U₀ : Set G) with hH₀
  have hU₀V : U₀ ≤ V := inf_le_left.trans hUV
  have hLH₀ : L ≤ H₀ := hLb.1.2.1.trans (Subgroup.centralizer_le inf_le_left)
  have hΓ : U₀ ∈ gammaE64 V M :=
    mem_gammaE64_of_mQuot_lt hV h hU₀V hU₀1 (fun hle => hLM (hLH₀.trans hle)) (by omega)
  obtain ⟨hQsyl, hcgs, hsq⟩ := centralizer_data h hΓ
  have hO : oddCoreIn H₀ = ⊥ := h621 G T M V U₀ hV h (Or.inr hm) hU₀V hU₀1
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hQH₀ : Q ≤ H₀ := hQsyl.1
  have hQM : Q ≤ M := inf_le_left.trans h.inM.2
  set C : Subgroup G := H₀ ⊓ Subgroup.centralizer ((compJoin H₀ : Subgroup G) : Set G) with hC
  set K : Subgroup G := C ⊔ Q with hK
  have hKH₀ : K ≤ H₀ := sup_le inf_le_left hQH₀
  have hKc : CharTwo K := charTwo_centralizer_compJoin_sup hO hQsyl.isPGroup hQH₀
  have hKs : IsSQTKIn K := IsSQTKIn.mono hsq hKH₀
  have hKQ : IsSylowTwoOf Q K := Lin2.isSylowTwoOf_of_le_of_le hQsyl le_sup_right hKH₀
  have hKcgs : cgsIn K Q ≤ M := (cgsIn_mono hKH₀).trans hcgs
  have hLC : L ≤ C := by
    refine le_inf hLH₀ ?_
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun X hX => ?_
    have h1 := hLay G T M V U L U₀ X hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀lt hU₀q hX
    rw [Subgroup.commutator_comm] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hLtH : CFSG.conjugate L t ≤ Subgroup.centralizer
      ((CFSG.conjugate U t : Subgroup G) : Set G) := by
    rw [← BenderBranch.conjugate_centralizer]
    exact BenderBranch.conjugate_mono hLb.1.2.1 t
  have hLtC : CFSG.conjugate L t ≤ C := by
    refine le_inf (hLtH.trans (Subgroup.centralizer_le inf_le_right)) ?_
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun X hX => ?_
    have hX' := isComponentIn_conjugate' hX t⁻¹
    rw [hU₀, BenderBranch.conjugate_inf, BenderBranch.conjugate_conjugate, mul_inv_cancel,
      BenderBranch.conjugate_one, inf_comm] at hX'
    have h1 := hLay G T M V U L _ _ hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₁lt hU₁q hX'
    have h2 : ⁅CFSG.conjugate L t, X⁆ = ⊥ := by
      have hXX : CFSG.conjugate (CFSG.conjugate X t⁻¹) t = X := by
        rw [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one]
      rw [← hXX]
      unfold CFSG.conjugate
      rw [← Subgroup.map_commutator]
      change (⁅L, CFSG.conjugate X t⁻¹⁆).map _ = ⊥
      rw [h1, Subgroup.map_bot]
    rw [Subgroup.commutator_comm] at h2
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  obtain ⟨a, haU, haUt⟩ := Set.not_subset.mp hUU
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hZQ : ∀ v ∈ V, v ∈ Q ∧ ∀ q ∈ Q, v * q = q * v := fun v hv =>
    ⟨Subgroup.mem_inf.mpr ⟨h.le hv,
      Subgroup.mem_centralizer_iff.mpr fun w hw => hVab w hw v hv⟩,
      fun q hq => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).2) v hv⟩
  have hKa : K ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (U : Set G) := by
    rw [← centralizer_inf_inf_centralizer h hUV (hconjV t ht).2 haU haUt]
    exact inf_le_inf_right _ hKH₀
  have hLK : L ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := le_inf (hLC.trans le_sup_left)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haU) |> hLb.1.2.1.trans)
  have hb1 : IsBlock2 K L := by
    refine A3Push.isBlock2_of_isBlock2_centralizer (hC129 G) hKc hKs hKQ hQM hKcgs
      (hZQ a (hUV haU)).1 (hZQ a (hUV haU)).2 ?_ hL3 hLM
    exact ⟨hLb.1.1, hLK, (isSubnormal_iff_subgroupOf hLK).mp
      (A4.subnormal_of_le_of_le (IsBlock2.isSubnormal hLb.1) hLK hKa)⟩
  have hUtU : ¬ CFSG.conjugate U t ≤ U := by
    intro hle
    apply hUU
    rw [Subgroup.eq_of_le_of_card_ge hle (hcardU t).ge]
  obtain ⟨b, hbUt, hbU⟩ := Set.not_subset.mp hUtU
  have hKb : K ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer ((CFSG.conjugate U t : Subgroup G) : Set G) := by
    rw [← centralizer_inf_inf_centralizer h (hconjV t ht).1 hU1 hbUt hbU,
      inf_comm (CFSG.conjugate U t) U]
    exact inf_le_inf_right _ hKH₀
  have hLtK : CFSG.conjugate L t ≤ K ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf (hLtC.trans le_sup_left)
      (hLtH.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbUt)))
  have hLtb : IsBlock2 (Subgroup.centralizer ((CFSG.conjugate U t : Subgroup G) : Set G))
      (CFSG.conjugate L t) := by
    have := hconjB t hLb.1
    rwa [BenderBranch.conjugate_centralizer] at this
  have hLt3 : IsAltType (CFSG.conjugate L t) 3 := L238.IsAltType.map_equiv hL3 (MulAut.conj t⁻¹)
  have hLtM : ¬ CFSG.conjugate L t ≤ M := by
    intro hle
    apply hLM
    have h1 := BenderBranch.conjugate_mono hle t⁻¹
    rw [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one,
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
        (Subgroup.le_normalizer (h.inM.2 (inv_mem ht)))] at h1
    exact h1
  have hb2 : IsBlock2 K (CFSG.conjugate L t) := by
    refine A3Push.isBlock2_of_isBlock2_centralizer (hC129 G) hKc hKs hKQ hQM hKcgs
      (hZQ b ((hconjV t ht).1 hbUt)).1 (hZQ b ((hconjV t ht).1 hbUt)).2 ?_ hLt3 hLtM
    exact ⟨hLtb.1, hLtK, (isSubnormal_iff_subgroupOf hLtK).mp
      (A4.subnormal_of_le_of_le (IsBlock2.isSubnormal hLtb) hLtK hKb)⟩
  by_cases hLL : L = CFSG.conjugate L t
  · exact Or.inl hLL.symm
  · exact Or.inr (distinctBlocksCommuteStatement K L _ hKc hb1 hb2 hLL)

end CFSG.Quasithin.E6
