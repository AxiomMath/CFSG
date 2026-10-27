module

public import CFSG.Quasithin.Background.E6TwentyThreeG
public import CFSG.Quasithin.Background.E6TwentyTwo

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

omit [Finite G] in
theorem le_inf_sup_zpowers {U' : Subgroup G} (hUV : U ≤ V) (hU' : U'.relIndex V = 2) {a : G}
    (haU : a ∈ U) (haU' : a ∉ U') :
    U ≤ (U ⊓ U') ⊔ Subgroup.zpowers a := by
  intro u hu
  by_cases huU' : u ∈ U'
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hu, huU'⟩)
  have hidx : (U'.subgroupOf V).index = 2 := hU'
  have hmul : u * a ∈ U' := by
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u, hUV hu⟩)
      (b := ⟨a, hUV haU⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf]
        exact ⟨fun h => absurd h huU', fun h => absurd h haU'⟩)
    simpa [Subgroup.mem_subgroupOf] using h
  have hua : u * a ∈ U ⊓ U' := Subgroup.mem_inf.mpr ⟨mul_mem hu haU, hmul⟩
  have : u = (u * a) * a⁻¹ := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hua)
    (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers a)))

theorem isBlock2_centralizer_inf (hC129 : ASC129Statement G)
    (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (hm : 2 < E3.mParam (autI hV M))
    (hUV : U ≤ V) (hU1 : E3.mQuot V U = 1)
    (hLb : IsBlock2 (Subgroup.centralizer (U : Set G)) L) (hL3 : IsAltType L 3) (hLM : ¬ L ≤ M)
    {U' : Subgroup G} (hU'1 : E3.mQuot V U' = 1) (hUU' : ¬ U ≤ U')
    (hZ : (U ⊓ U') ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    IsBlock2 (Subgroup.centralizer ((U ⊓ U' : Subgroup G) : Set G)) L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  set U₀ : Subgroup G := U ⊓ U' with hU₀
  have hU₀V : U₀ ≤ V := inf_le_left.trans hUV
  have hU₀1 : U₀ ≠ ⊥ := fun h0 => hZ (by rw [h0, bot_inf_eq])
  have hLH₀ : L ≤ Subgroup.centralizer (U₀ : Set G) :=
    hLb.2.1.trans (Subgroup.centralizer_le inf_le_left)
  have hU₀M : ¬ Subgroup.centralizer (U₀ : Set G) ≤ M := fun hle => hLM (hLH₀.trans hle)
  have hU₀q : E3.mQuot V U₀ ≤ 2 := by
    have := mQuot_inf_le (U := U) (U' := U') hV2
    rw [hU1, hU'1] at this
    exact this
  have hΓ : U₀ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₀V hU₀1 hU₀M (by omega)
  have hH₀ : CharTwo (Subgroup.centralizer (U₀ : Set G)) :=
    as_E_6_6_four_proved G T M V U₀ h ⟨hΓ.2.1, hΓ.1, hΓ.2.2.1, hΓ.2.2.2⟩ hZ
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hQsyl : IsSylowTwoOf Q (Subgroup.centralizer (U₀ : Set G)) := e6_5_one h hΓ
  have hcgs : cgsIn (Subgroup.centralizer (U₀ : Set G)) Q ≤ M :=
    (e6_5_two h hΓ).1.trans inf_le_right
  have hQM : Q ≤ M := inf_le_left.trans h.inM.2
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hU₀C : U₀ ≤ Subgroup.centralizer (U₀ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v (hU₀V hv) u (hU₀V hu)
  have hO2 : pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) ≠ ⊥ := by
    intro h0
    apply hU₀1
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hU₀C
      (Subgroup.centralizer_le_normalizer _) (hV2.to_le hU₀V)
    rw [h0] at this
    exact le_bot_iff.mp this
  have hsq : IsSQTKIn (Subgroup.centralizer (U₀ : Set G)) :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨a, haU, haU'⟩ := Set.not_subset.mp hUU'
  have hU'i : U'.relIndex V = 2 := by
    rw [E3.relIndex_eq_two_pow hV2, hU'1, pow_one]
  have hUeq : Subgroup.centralizer (U₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer (U : Set G) := by
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
  have haQ : a ∈ Q := Subgroup.mem_inf.mpr ⟨h.le (hUV haU),
    Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v hv a (hUV haU)⟩
  have haZ : ∀ q ∈ Q, a * q = q * a := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).2) a (hUV haU)
  refine A3Push.isBlock2_of_isBlock2_centralizer hC129 hH₀ hsq hQsyl hQM hcgs haQ haZ ?_ hL3 hLM
  rw [hUeq]
  exact hLb

theorem charTwo_centralizer_inf (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (hm : 2 < E3.mParam (autI hV M)) (hUV : U ≤ V) (hU1 : E3.mQuot V U = 1) {U' : Subgroup G}
    (hU'1 : E3.mQuot V U' = 1) (hM : ¬ Subgroup.centralizer ((U ⊓ U' : Subgroup G) : Set G) ≤ M)
    (hZ : (U ⊓ U') ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    CharTwo (Subgroup.centralizer ((U ⊓ U' : Subgroup G) : Set G)) := by
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hU₀1 : U ⊓ U' ≠ ⊥ := fun h0 => hZ (by rw [h0, bot_inf_eq])
  have hU₀q : E3.mQuot V (U ⊓ U') ≤ 2 := by
    have := mQuot_inf_le (U := U) (U' := U') hV2
    rw [hU1, hU'1] at this
    exact this
  have hΓ : U ⊓ U' ∈ gammaE64 V M :=
    mem_gammaE64_of_mQuot_lt hV h (inf_le_left.trans hUV) hU₀1 hM (by omega)
  exact as_E_6_6_four_proved G T M V (U ⊓ U') h ⟨hΓ.2.1, hΓ.1, hΓ.2.2.1, hΓ.2.2.2⟩ hZ

omit [Finite G] in
theorem inf_center_le_conjugate {t : G} (ht : t ∈ T) :
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≤ CFSG.conjugate U t := by
  intro z hz
  obtain ⟨hzU, -, hzC⟩ := hz
  rw [BenderBranch.mem_conjugate_iff]
  have hzt : t * z = z * t := (Subgroup.mem_centralizer_iff.mp hzC) t ht
  rw [hzt]
  simpa using hzU

theorem e623A3Dichotomy_of_inf_ne_bot (hC129 : ASC129Statement G)
    (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (hm : 2 < E3.mParam (autI hV M))
    (hUV : U ≤ V) (hU1 : E3.mQuot V U = 1) (hH : CharTwo (Subgroup.centralizer (U : Set G)))
    (hLb : IsChi0Block (Subgroup.centralizer (U : Set G)) L) (hL3 : IsAltType L 3)
    (hLM : ¬ L ≤ M) (hZ : U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    ∀ t ∈ T, CFSG.conjugate L t = L ∨ ⁅L, CFSG.conjugate L t⁆ = ⊥ := by
  classical
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.normal
  have hconjV : ∀ s ∈ T, CFSG.conjugate U s ≤ V ∧ E3.mQuot V (CFSG.conjugate U s) = 1 :=
    fun s hs => ⟨conjugate_le_of_mem_normalizer hUV (hTN hs),
      (mQuot_conjugate (hTN hs)).trans hU1⟩
  have hconjB : ∀ {X Y : Subgroup G} (s : G), IsBlock2 X Y →
      IsBlock2 (CFSG.conjugate X s) (CFSG.conjugate Y s) := fun s hY =>
    Setup.Campbell.isBlock2_map_conj hY s⁻¹
  have hcardU : ∀ s : G, Nat.card (CFSG.conjugate U s) = Nat.card U :=
    BenderBranch.card_conjugate U
  have hZt : ∀ s ∈ T, U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≤
      U ⊓ CFSG.conjugate U s := fun s hs =>
    le_inf inf_le_left (inf_center_le_conjugate hs)
  have hZne : ∀ s ∈ T, (U ⊓ CFSG.conjugate U s) ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ :=
    fun s hs h0 => hZ (eq_bot_iff.mpr (by
      rw [← h0]
      exact le_inf (hZt s hs) inf_le_right))
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
  ·
    have hUU' : ¬ U ≤ CFSG.conjugate U t⁻¹ := by
      intro hle
      apply hUU
      have h1 := BenderBranch.conjugate_mono hle t
      rw [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one] at h1
      have h2 := Subgroup.eq_of_le_of_card_ge h1 (hcardU t).ge
      rw [h2]
    have hb1 := isBlock2_centralizer_inf hC129 hV h hm hUV hU1 hLb.1 hL3 hLM
      (hconjV t ht).2 hUU (hZne t ht)
    have hb2 := isBlock2_centralizer_inf hC129 hV h hm hUV hU1 hLb.1 hL3 hLM
      (hconjV t⁻¹ (inv_mem ht)).2 hUU' (hZne t⁻¹ (inv_mem ht))
    have hb2' : IsBlock2 (Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G))
        (CFSG.conjugate L t) := by
      have := hconjB t hb2
      rwa [BenderBranch.conjugate_centralizer, BenderBranch.conjugate_inf,
        BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one,
        inf_comm] at this
    have hM₀ : ¬ Subgroup.centralizer ((U ⊓ CFSG.conjugate U t : Subgroup G) : Set G) ≤ M :=
      fun hle => hLM (hb1.2.1.trans hle)
    have hH₀ := charTwo_centralizer_inf hV h hm hUV hU1 (hconjV t ht).2 hM₀ (hZne t ht)
    by_cases hLL : L = CFSG.conjugate L t
    · exact Or.inl hLL.symm
    · exact Or.inr (distinctBlocksCommuteStatement _ L _ hH₀ hb1 hb2' hLL)

end CFSG.Quasithin.E6
