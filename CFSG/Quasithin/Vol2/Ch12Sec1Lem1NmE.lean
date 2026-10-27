module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmD
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1A5
public import CFSG.Quasithin.Vol2.Ch4Sec3C57Use
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Ns

theorem charTwo_of_le_of_pCoreOf_le {G : Type} [Group G] [Finite G] {X Y : Subgroup G}
    (hXY : X ≤ Y) (hO : pCoreOf 2 Y ≤ X) (hY : CharTwo Y) : CharTwo X :=
  CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hY hXY hO

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

omit [Finite G] in
theorem pCoreOf_ne_bot_of_short {B : Subgroup G} (hB : IsShort2 B) : pCoreOf 2 B ≠ ⊥ := by
  intro h
  have hU : blockU B = ⊥ := by
    rw [blockU, blockQ, h, Subgroup.commutator_bot_left]
  have hlt := hB.2.2.2.2.1
  rw [hU] at hlt
  exact absurd hlt (not_lt_bot)

variable (S) in
include S in
theorem not_normal_inf_centralizer (F : Frame S m) (hm : 3 ≤ m)
    (hn : ∀ l ∈ L, ∀ x ∈ L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G),
      l * x * l⁻¹ ∈ L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)) : False := by
  have hsn : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) S.three_le'
  set X := (L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)).subgroupOf L with hX
  have hXn : X.Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hn l l.2 x hx⟩
  have hP := Subgroup.Normal.map hXn S.C₁.ρ S.C₁.ρ_surj
  rw [S.map_inf] at hP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀))
    with h | h
  ·
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
      Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hm
    obtain ⟨a, b, hab⟩ := Sec121Thm.exists_not_commute_SL hm
    have ha1 : a ≠ 1 := by rintro rfl; simp at hab
    obtain ⟨l, hl⟩ := psi_lv_surjective F a
    have hρ : S.C₁.ρ ⟨l, Sec1216Lv.lv_le_L L _ l.2⟩ ∈
        PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) :=
      (S.mem_centralizer_iff _).mp (Sec1216Lv.lv_le_centralizer L _ l.2)
    rw [h, Subgroup.mem_bot] at hρ
    apply ha1
    apply frameMat_injective F
    rw [← hl, frameMat_psi_lv, hρ]
    simp [frameMat]
  ·
    obtain ⟨w, hw, hw1⟩ := exists_ne_one_W₁ F (by omega)
    have hwa : w ≠ a₀ := by
      rintro rfl
      have h1 := hw.2
      rw [S.hns] at h1
      exact one_ne_zero h1
    obtain ⟨l, hl⟩ := S.C₁.exists_conj_eq (by have := S.three_le'; omega) S.ha₀ hw.1
      S.a₀_ne hw1
    have hρ : S.C₁.ρ l ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) := by
      rw [h]; exact Subgroup.mem_top _
    have hlC := (S.mem_centralizer_iff l).mpr hρ
    have hfix : (l : G) * a₀ * (l : G)⁻¹ = a₀ := by
      have hlv := Subgroup.mem_centralizer_singleton_iff.mp hlC
      have e : (l : G) * a₀ * (l : G)⁻¹ * ((l : G) * c₀ * (l : G)⁻¹) = a₀ * c₀ := by
        calc (l : G) * a₀ * (l : G)⁻¹ * ((l : G) * c₀ * (l : G)⁻¹) =
            (l : G) * (a₀ * c₀) * (l : G)⁻¹ := by group
          _ = a₀ * c₀ := by rw [hlv, mul_inv_cancel_right]
      exact (S.decomp_unique (S.C₁.conj_mem l S.ha₀) S.ha₀ (S.C₂.conj_mem l S.hc₀) S.hc₀ e).1
    exact hwa (hl.symm.trans hfix)

theorem false_of_alt3 (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m)
    (hmaxLT : IsMaxSubgroupIn (L ⊔ T) ((L ⊔ T) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)))
    {B : Subgroup G}
    (hQY : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))))
    (hcY : CharTwo (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))))
    (hB : IsChi0Block (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) B)
    (h3 : IsAltType B 3) (hJ : ⁅B, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆ = B)
    (hBn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hBM : ¬ B ≤ Subgroup.normalizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  set Y := centralizerSection H (Sec1216Lv.lv L (a₀ * c₀))
    (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) with hY
  have hYH : Y ≤ H := centralizerSection_le_left _ _ _
  have hBY : B ≤ Y := hB.1.2.1
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) := (hQY.1.trans hYH).trans hBn
  have huniq := S.isUniqueM_sup h331
  have hQLT : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := by
    have hQe := setup121Q_holds G T L V V₁ V₂ n S.hyp S.hTL
    rw [hQ, ← hQe]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hO₂B : pCoreOf 2 B ≤ Q :=
    (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hBY hB.1.2.2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf hQY)
  obtain ⟨α, hα, hαk, -⟩ := id h3
  have hA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hcardB : Nat.card B = Nat.card (pCoreOf 2 B) * 3 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hα
    rw [hαk, hA3] at h1
    rw [← h1, pCoreOf, Subgroup.card_map_of_injective B.subtype_injective]
  have hBQ : B ⊓ Q = pCoreOf 2 B := by
    refine le_antisymm (fun x hx => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 B) hO₂B)
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hx.2⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : α ⟨x, hx.1⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hx.1⟩ : ↥B) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    have h3' : α ⟨x, hx.1⟩ = 1 := by
      have h4 : α ⟨x, hx.1⟩ ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥(alternatingGroup (Fin 3))) (x := α ⟨x, hx.1⟩)
        rwa [hA3] at this
      have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨h1, h4⟩
      rwa [hcop, pow_one] at this
    have hmem : (⟨x, hx.1⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := by
      rw [← hαk, MonoidHom.mem_ker]
      exact h3'
    exact ⟨⟨x, hx.1⟩, by exact hmem, rfl⟩
  have hidx : Q.relIndex (B ⊔ Q) = 3 := by
    have h1 := Lin2.card_sup_mul_card_inf hQB
    rw [sup_comm, inf_comm, hBQ, hcardB] at h1
    have h2 := Subgroup.relIndex_mul_card Q (B ⊔ Q)
    rw [inf_of_le_left (le_sup_right : Q ≤ B ⊔ Q)] at h2
    have hpos : 0 < Nat.card (pCoreOf 2 B) := Nat.card_pos
    have hposQ : 0 < Nat.card Q := Nat.card_pos
    have h3 : Nat.card (B ⊔ Q : Subgroup G) = Nat.card Q * 3 := by
      have := h1
      nlinarith
    rw [h3] at h2
    exact Nat.eq_of_mul_eq_mul_right hposQ (h2.trans (mul_comm _ _))
  have hint : ∀ K : Subgroup G, Q ≤ K → K ≤ B ⊔ Q → K = Q ∨ K = B ⊔ Q := by
    intro K hQK hKBQ
    have h1 := Subgroup.relIndex_mul_relIndex Q K (B ⊔ Q) hQK hKBQ
    rw [hidx] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ h1) with h2 | h2
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hQK
    · right
      rw [h2] at h1
      have h3 : K.relIndex (B ⊔ Q) = 1 := by omega
      exact le_antisymm hKBQ (Subgroup.relIndex_eq_one.mp h3)
  have hQlt : Q < B ⊔ Q := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    rw [← h, Subgroup.relIndex_self] at hidx
    omega
  have hum : ∃ N : Subgroup G, IsUniqueMaxOver (B ⊔ Q) Q N := by
    refine ⟨Q, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hQlt, fun K hQK hK => ?_⟩, le_rfl⟩,
      fun N hN => ?_⟩⟩
    · rcases hint K hQK.le hK with h | h
      · exact absurd h (ne_of_gt hQK)
      · exact h
    · rcases hint N hN.2 hN.1.1.le with h | h
      · exact h
      · exact absurd h (ne_of_lt hN.1.1)
  have hC : C5.NoCommonNormal Q (B ⊔ Q) (L ⊔ T) := by
    intro X hXQ hX1 hHX hMX
    have hX2 : IsPGroup 2 X := hQ2.to_le hXQ
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (⟨X, hX1, hX2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (X : Set G)))
    have hM'M : M' = M := huniq.2 M' ⟨hM', hMX.trans hNM'⟩
    exact hBM ((le_sup_left.trans hHX).trans (hM'M ▸ hNM'))
  have hNB : (L ⊔ T) ⊓ Subgroup.normalizer (B : Set G) ≠ L ⊔ T := by
    intro h
    have hLTB : L ⊔ T ≤ Subgroup.normalizer (B : Set G) := by
      rw [← h]; exact inf_le_right
    have hO := pCoreOf_ne_bot_of_short hB.1.1
    have hO2 : IsPGroup 2 (pCoreOf 2 B) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (⟨_, hO, hO2, rfl⟩ : IsTwoLocal (Subgroup.normalizer ((pCoreOf 2 B : Subgroup G) : Set G)))
    have hBO : Subgroup.normalizer (B : Set G) ≤
        Subgroup.normalizer ((pCoreOf 2 B : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B
    have hM'M : M' = M := huniq.2 M' ⟨hM', (hLTB.trans hBO).trans hNM'⟩
    exact hBM ((Subgroup.le_normalizer.trans hBO).trans (hM'M ▸ hNM'))
  have hLTv : (L ⊔ T) ⊓ H ≤ (L ⊔ T) ⊓ Subgroup.normalizer (B : Set G) :=
    inf_le_inf_left _ hBn
  have hNBeq : (L ⊔ T) ⊓ Subgroup.normalizer (B : Set G) = (L ⊔ T) ⊓ H := by
    by_contra hne
    exact hNB (hmaxLT.2 _ (lt_of_le_of_ne hLTv (Ne.symm hne)) inf_le_left)
  have hmax : IsMaxSubgroupIn (L ⊔ T) ((L ⊔ T) ⊓ Subgroup.normalizer (B : Set G)) := by
    rw [hNBeq]; exact hmaxLT
  have hblock : IsBlock2 (B ⊔ Q) B := by
    refine ⟨hB.1.1, le_sup_left, Subgroup.Normal.isSubnormal ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQB)
  have hsylBQ : IsSylowTwoOf Q (B ⊔ Q) := by
    rw [A4.isSylowTwoOf_iff_maximal] at hQY ⊢
    exact ⟨le_sup_right, hQY.2.1, fun P hP hP2 hQP =>
      hQY.2.2 P (hP.trans (sup_le hBY hQY.1)) hP2 hQP⟩
  have hcBQ : CharTwo (B ⊔ Q) :=
    charTwo_of_le_of_pCoreOf_le (sup_le hBY hQY.1)
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hQY).trans le_sup_right) hcY
  have h2 := Ch4.C57.relIndex_eq_two_of_block rfl hQB hblock (Or.inr (Or.inl h3))
    hsylBQ hcBQ hum (inf_le_left.trans le_sup_right) hQLT hC hJ hmax
  rw [hNBeq] at h2
  have hnormal : ((L ⊔ T) ⊓ H).subgroupOf (L ⊔ T) |>.Normal :=
    Subgroup.normal_of_index_eq_two h2
  refine S.not_normal_inf_centralizer F hm fun l hl x hx => ?_
  have hxLT : x ∈ (L ⊔ T) ⊓ H := ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have h3 := hnormal.conj_mem ⟨x, Subgroup.mem_sup_left hx.1⟩ hxLT ⟨l, Subgroup.mem_sup_left hl⟩
  rw [Subgroup.mem_subgroupOf] at h3
  exact ⟨L.mul_mem (L.mul_mem hl hx.1) (L.inv_mem hl), h3.2⟩

theorem false_of_alt5 (hA318 : Lem1211NormalA318) (F : Frame S m) (hm : 3 ≤ m) {B : Subgroup G}
    (h5 : IsAltType B 5)
    (hBor : IsBorelOfBlock B (B ⊓ (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) ⊓
        Subgroup.normalizer (L : Set G)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B₀ := B ⊓ (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
    (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) ⊓
    Subgroup.normalizer (L : Set G)) with hB₀
  obtain ⟨α, hα, hαk, -⟩ := id h5
  have hcard : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 := by
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      A5Syl.card_alt5]
  unfold IsBorelOfBlock at hBor
  split_ifs at hBor with h60
  · rw [hcard] at h60
    norm_num at h60
  obtain ⟨S', hS', hS'eq⟩ := hBor
  set P := (S'.subgroupOf B).map α with hPdef
  have hS'2 : IsPGroup 2 (S'.subgroupOf B) :=
    hS'.2.1.comap_of_injective _ Subtype.val_injective
  have hP2 : IsPGroup 2 P := hS'2.map α
  have hPidx : ¬ 2 ∣ P.index := fun h =>
    hS'.2.2 (h.trans (Subgroup.index_map_dvd (S'.subgroupOf B) hα))
  have hP4 : Nat.card P = 4 := by
    obtain ⟨j, hj⟩ := hP2.exists_card_eq
    have h1 := Subgroup.card_mul_index P
    rw [hj, A5Syl.card_alt5] at h1
    have hj6 : j < 6 := by
      by_contra h
      have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 0 < P.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at h1; omega)
      nlinarith
    rw [hj]
    interval_cases j <;> omega
  obtain ⟨g, hgN, hg3⟩ := A5Syl.exists_orderOf_three P hP4
  obtain ⟨z, hz⟩ := hα g
  have hO₂S : pCoreOf 2 B ≤ S' := B6.pCoreOf_two_le_of_isSylowTwoOf hS'
  have hzS : (z : G) ∈ Subgroup.normalizer (S' : Set G) := by
    refine Sec121Swap.mem_normalizer_of_conj_mem fun s hs => ?_
    have hsB : s ∈ B := hS'.1 hs
    have h1 : α (z * ⟨s, hsB⟩ * z⁻¹) ∈ P := by
      rw [map_mul, map_mul, map_inv, hz]
      exact (Subgroup.mem_normalizer_iff.mp hgN _).mp ⟨⟨s, hsB⟩, hs, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := h1
    have hk : s'⁻¹ * (z * ⟨s, hsB⟩ * z⁻¹) ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs'e, inv_mul_cancel]
    rw [hαk] at hk
    have hk' : ((s'⁻¹ * (z * ⟨s, hsB⟩ * z⁻¹) : ↥B) : G) ∈ S' :=
      hO₂S ⟨_, by exact hk, rfl⟩
    have e : (z : G) * s * (z : G)⁻¹ =
        (s' : G) * ((s'⁻¹ * (z * ⟨s, hsB⟩ * z⁻¹) : ↥B) : G) := by simp
    rw [e]
    exact S'.mul_mem hs' hk'
  have hzB₀ : (z : G) ∈ B₀ ⊔ pCoreOf 2 B := by
    rw [hS'eq]
    exact ⟨z.2, hzS⟩
  have hB₀N : B₀ ≤ Subgroup.normalizer ((pCoreOf 2 B : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B₀ _ hB₀N] at hzB₀
  obtain ⟨b₀, hb₀, u, hu, hbu⟩ := hzB₀
  have hb₀B : b₀ ∈ B := hb₀.1
  have huB : u ∈ B := CFSG.LieType.BorelTits.pCoreOf_le 2 B hu
  have hαu : α ⟨u, huB⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hαk]
    obtain ⟨u', hu', hu'e⟩ := hu
    have : u' = ⟨u, huB⟩ := Subtype.ext hu'e
    rw [← this]
    exact hu'
  have hαb₀ : α ⟨b₀, hb₀B⟩ = g := by
    have e : z = ⟨b₀, hb₀B⟩ * ⟨u, huB⟩ := Subtype.ext hbu.symm
    rw [← hz, e, map_mul, hαu, mul_one]
  have h3 : 3 ∣ orderOf (⟨b₀, hb₀B⟩ : ↥B) := by
    rw [← hg3, ← hαb₀]
    exact orderOf_map_dvd α _
  have hne : orderOf b₀ ≠ 0 := (isOfFinOrder_of_finite b₀).orderOf_pos.ne'
  have h3' : 3 ∣ orderOf b₀ := by rwa [← Subgroup.orderOf_coe] at h3
  have hd3 : orderOf (b₀ ^ (orderOf b₀ / 3)) = 3 := orderOf_pow_orderOf_div hne h3'
  have hdB₀ : b₀ ^ (orderOf b₀ / 3) ∈ B₀ := B₀.pow_mem hb₀ _
  have hdC := mem_centralizer_V_of_mem_Y F hm hdB₀.2.2 hdB₀.2.1
  have hdL := hA318 G T L V V₁ V₂ n S.hyp S.hTL _ hdB₀.2.2 ⟨1, by rw [hd3, pow_one]⟩
  obtain ⟨hc₁, hnat₁⟩ := S.hyp.nat₁
  have hdO := Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 S.hyp S.le₁ S.hyp.norm₁ hnat₁
    ⟨hdL, Subgroup.centralizer_le (by exact_mod_cast S.le₁) hdC⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hdO⟩
  have hk' : (b₀ ^ (orderOf b₀ / 3)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h4 := orderOf_dvd_of_pow_eq_one hk'
  rw [hd3] at h4
  have : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4)
  omega

end Setting

end Sec1211Ns

open Sec1211Ns in
theorem lem1211Normal_of (h331 : Stmt3_3_1)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hBlk : Lem1211NormalBlk)
    (hLin : Lem1211NormalLin) (hA318 : Lem1211NormalA318) (hMax : Lem1211NormalMax) :
    Lem1211Normal := by
  intro G _ _ T L V V₁ V₂ n β hyp hTL hβ v hv hns hchar hnorm
  by_contra hHM
  obtain ⟨S₀⟩ := KGH91.Setting.nonempty hyp
  have hns' := hns
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, hac⟩ := hns
  have hP := KGH91.eq_pairing S₀.hn S₀.C₁ S₀.C₂ S₀.dual hβ.1 hβ.2.1 hβ.2.2.2.2
    ⟨a₀, ha₀, c₀, hc₀, by rw [hac]; exact one_ne_zero⟩ a₀ ha₀ c₀ hc₀
  have S : Sec1211Ns.Setting T L V V₁ V₂ n a₀ c₀ :=
    { toSetting := S₀, hTL := hTL, ha₀ := ha₀, hc₀ := hc₀, hns := hP ▸ hac }
  obtain ⟨F⟩ := S.nonempty_frame
  have hm : 3 ≤ n - 1 := S.three_le
  have hlv := S.lv_eq_oTwoUpper
  have hnorm' : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤
      Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) := by
    rw [hlv]; exact hnorm
  obtain ⟨R, B, -, -, -, hQY, hB, hBor, hJ, hBM⟩ :=
    S.exists_block_not_le h331 h129 F hm hchar hnorm' hHM
  have hBn := hBlk G T L V V₁ V₂ n β hyp hTL hβ (a₀ * c₀) hv hns' hchar hnorm B
    (by rw [← hlv]; exact hB)
  have hYH := centralizerSection_le_left (Subgroup.centralizer ({a₀ * c₀} : Set G))
    (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))
  have hcY := A4.charTwo_of_normal hYH (fun h hh =>
    Setting.mem_normalizer_centralizerSection hh (hnorm' hh)) hchar
  rcases hB.2 with ⟨k, hk, hlin⟩ | h3 | h5
  · exact Setting.false_of_lin h331 hLin F hm hQY hB hk hlin hBor hBn hBM
  · exact Setting.false_of_alt3 h331 F hm (hMax G T L V V₁ V₂ n β hyp hTL hβ _ hv hns') hQY hcY hB
      h3 hJ hBn hBM
  · exact Setting.false_of_alt5 hA318 F hm h5 hBor

end CFSG.Quasithin.H13
