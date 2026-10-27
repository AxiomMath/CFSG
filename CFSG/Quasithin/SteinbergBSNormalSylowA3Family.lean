module

public import CFSG.Quasithin.SteinbergBSNormalSylowA3Parabolic
public import CFSG.Quasithin.H13.A7SharedSolvableOvergroup

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath
open scoped commutatorElement

structure CommutingA3Family {H : Type*} [Group H] (T R : Subgroup H) {r : ℕ}
    (L : Fin r → Subgroup H) : Prop where
  one_le : 1 ≤ r
  injective : Function.Injective L
  le_odd : ∀ i, L i ≤ oddOrderSubgroup (⊤ : Subgroup H)
  odd_eq : oddOrderSubgroup (⊤ : Subgroup H) = ⨆ i, L i
  indep : iSupIndep L
  commute : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥
  alt4 : ∀ i, Nonempty (↥(L i) ≃* alternatingGroup (Fin 4))
  short : ∀ i, IsShort2 (L i)
  card_quot : ∀ i, Nat.card (↥(L i) ⧸ CFSG.pCore 2 ↥(L i)) = 3
  perfect_J : ∀ i, ⁅L i, thompsonJ R⁆ = L i
  permuted : ∀ t ∈ T, ∀ i, ∃ j, (L i).map (MulAut.conj t).toMonoidHom = L j
  transitive : ∀ i j, ∃ t ∈ T, (L i).map (MulAut.conj t).toMonoidHom = L j
  normal_QK : ∀ i, ((L i).subgroupOf (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R) ⊔
    oddOrderSubgroup (⊤ : Subgroup H))).Normal
  subnormal : ∀ i, (L i).IsSubnormal
  U_eq : ⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R), oddOrderSubgroup (⊤ : Subgroup H)⁆ =
    ⨆ i, blockQ (L i)
  U_indep : iSupIndep fun i => blockQ (L i)
  U_ne_bot :
    ⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R), oddOrderSubgroup (⊤ : Subgroup H)⁆ ≠ ⊥
  U_elem : IsElemAbelian 2
    ⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R), oddOrderSubgroup (⊤ : Subgroup H)⁆
  U_normal :
    (⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R), oddOrderSubgroup (⊤ : Subgroup H)⁆).Normal
  U_le : ⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R), oddOrderSubgroup (⊤ : Subgroup H)⁆ ≤
    BlueprintB2.centerTorsion 2 (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R))
  center_le : BlueprintB2.centerTorsion 2 (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R)) ≤ R

namespace NormalSylowA3

variable {H : Type} [Group H] [Finite H]

theorem exists_three_pow_mem (hsolv : Group.IsSolvable H) {T M R : Subgroup H}
    (hT : IsSylowTwoOf T ⊤) (hTn : ¬ T.Normal) (hMlt : M < ⊤) (hTM : T ≤ M)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M) {c : H}
    (hcK : c ∈ oddOrderSubgroup (⊤ : Subgroup H)) (hc3 : orderOf c = 3) :
    ∀ x ∈ oddOrderSubgroup (⊤ : Subgroup H),
      ∃ k : ℕ, x ^ 3 ^ k ∈ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oddOrderSubgroup (⊤ : Subgroup H) with hK
  set Q := blockQ (K ⊔ R) with hQ
  have hKn : K.Normal := WreathHyp.oddOrderSubgroup_top_normal (H := H)
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 H := hT.2.1.toSylow hT2
  have hX : IsCoatom M := by
    refine ⟨hMlt.ne, fun Y hMY => ?_⟩
    by_contra hY
    exact absurd (hmax Y (hTM.trans hMY.le) (lt_top_iff_ne_top.mpr hY)) (not_le_of_gt hMY)
  have huniq : ∀ Y : Subgroup H, IsCoatom Y → (S : Subgroup H) ≤ Y → Y = M := by
    intro Y hY hTY
    rcases (hmax Y hTY (lt_top_iff_ne_top.mpr hY.1)).lt_or_eq with h | h
    · exact absurd (hY.2 M h) hMlt.ne
    · exact h
  obtain ⟨p, hp, -, Po, -, hPon, hPop, hPoT, -⟩ :=
    CFSG.Quasithin.H13.A7.A7_solvable_unique_Sylow_overgroup_structure hsolv S hTn hX hTM huniq
  set π := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hKPo : K ≤ Po.comap π := oddOrderSubgroup_le_of_pow_mem fun h _ => by
    have hmem : π h ∈ Po ⊔ (S : Subgroup H).map π := by
      rw [hPoT]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_pGroup (hT.2.1.map π)
      (by rw [normalizer_eq_top_iff.mpr hPon]; exact le_top) hmem
    exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
  have hcore : CFSG.pCore 2 H ⊓ K ≤ Q := by
    have hn : (CFSG.pCore 2 H ⊓ K).Normal := by
      have : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
      exact Subgroup.normal_inf_normal _ _
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (inf_le_right.trans le_sup_left) ?_
      (CFSG.pCore_isPGroup.to_le inf_le_left)
    rw [normalizer_eq_top_iff.mpr hn]
    exact le_top
  have hpow : ∀ x ∈ K, ∃ k : ℕ, x ^ p ^ k ∈ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := hPop ⟨π x, hKPo hx⟩
    have h1 : x ^ p ^ k ∈ CFSG.pCore 2 H := by
      rw [← QuotientGroup.eq_one_iff]
      have := congrArg Subtype.val hk
      simpa [hπ, map_pow] using this
    exact ⟨k, hcore ⟨h1, K.pow_mem hx _⟩⟩
  have hp3 : p = 3 := by
    by_contra hp3
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hpow c hcK
    have hnd : ¬ p ∣ orderOf c := by
      rw [hc3]
      exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    have hcQ : c ∈ Q := mem_of_not_dvd_orderOf_of_pow_mem hnd hk
    obtain ⟨n, hn⟩ := C1.blockQ_isPGroup (K ⊔ R) ⟨c, hcQ⟩
    have hdvd : orderOf c ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    rw [hc3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  subst hp3
  exact hpow

end NormalSylowA3

open NormalSylowA3

variable {H : Type} [Group H] [Finite H]

theorem solvable_normal_Sylow_part_commuting_A3_family (hsolv : Group.IsSolvable H)
    (hchar : CharTwo (⊤ : Subgroup H)) {T M R : Subgroup H} (hT : IsSylowTwoOf T ⊤)
    (hTn : ¬ T.Normal) (hMlt : M < ⊤) (hTM : T ≤ M)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M) (hR1 : R ≠ ⊥) (hRT : R ≤ T)
    (hRTn : T ≤ normalizer (R : Set H))
    (hRsyl : IsSylowTwoOf R (oddOrderSubgroup (⊤ : Subgroup H) ⊔ R))
    (hnoChar : NoCharNormal R ⊤) :
    ∃ (r : ℕ) (L : Fin r → Subgroup H), CommutingA3Family T R L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oddOrderSubgroup (⊤ : Subgroup H) with hK
  set Q := blockQ (K ⊔ R) with hQ
  have hKn : K.Normal := WreathHyp.oddOrderSubgroup_top_normal (H := H)
  have hKT : K ⊔ T = ⊤ := odd_sup_sylow hT
  have hNRn : ⊤ ≤ normalizer ((K ⊔ R : Subgroup H) : Set H) := top_le_normalizer_odd_sup hT hRTn
  have hcharKR : CharTwo (K ⊔ R) := charTwo_odd_sup hchar hT hRTn
  have hQR : Q ≤ R := hRsyl.pCoreOf_le
  have hQ2 : IsPGroup 2 Q := C1.blockQ_isPGroup _
  have hQn : ⊤ ≤ normalizer (Q : Set H) := fun g _ =>
    C1.mem_normalizer_blockQ (hNRn (Subgroup.mem_top g))
  have hQnormal : Q.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hQn)
  obtain ⟨P, s, Y, hRP, hPNR, hPT, hs, hY, hgen, hYK, hYA4, hY3, hYJ, hYtrans⟩ :=
    exists_block_family hsolv hchar hT hMlt hTM hmax hR1 hRT hRTn hRsyl hnoChar
  obtain ⟨hKeq, hU1, hUel, hUn, hUZ, -⟩ :=
    normal_Sylow_part_block_centrality hT le_top (by rw [odd_normalizer_eq_top]) hKT
      (hasNoTwoQuotient_oddOrderSubgroup _) hRT hRTn hRsyl hcharKR hRP hPNR hPT hs Y hY hgen
  set i₀ : Fin s := ⟨0, hs⟩ with hi₀
  obtain ⟨r, L, E⟩ := exists_conjEnum T (Y i₀)
  have hconj_comp : ∀ a b : H, (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := fun a b => by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hKL : K = ⨆ j, L j := by
    rw [← E.iSup_eq]
    refine hKeq.trans (le_antisymm (iSup_le fun i => ?_) (le_iSup (fun i => conjJoin T (Y i)) i₀))
    obtain ⟨t₀, ht₀, he⟩ := hYtrans i₀ i
    rw [← he]
    refine iSup_le fun t => ?_
    rw [Subgroup.map_map, hconj_comp]
    exact le_iSup (fun u : ↥T => (Y i₀).map (MulAut.conj (u : H)).toMonoidHom)
      ⟨_, T.mul_mem t.2 (hRT ht₀)⟩
  have hr : 1 ≤ r := (E.all 1 T.one_mem).choose.pos
  have hfacts : ∀ j, IsShort2 (L j) ∧ L j ≤ K ∧ Nonempty (↥(L j) ≃* alternatingGroup (Fin 4)) ∧
      Nat.card (↥(L j) ⧸ CFSG.pCore 2 ↥(L j)) = 3 ∧ ⁅L j, thompsonJ R⁆ = L j ∧
      ⁅Q, L j⁆ = blockQ (L j) ∧ blockQ (L j) ≤ BlueprintB2.centerTorsion 2 Q := by
    intro j
    obtain ⟨t, ht, hj⟩ := E.mem j
    rw [hj]
    have hφ : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
    have hshort : IsShort2 ((Y i₀).map (MulAut.conj t).toMonoidHom) :=
      Lin2.IsShort2.map_equiv (hY i₀).1 (MulAut.conj t)
    have h3 : Nat.card (↥((Y i₀).map (MulAut.conj t).toMonoidHom) ⧸
        CFSG.pCore 2 ↥((Y i₀).map (MulAut.conj t).toMonoidHom)) = 3 :=
      (card_quot_pCore_map_injective (MulAut.conj t).toMonoidHom hφ (Y i₀)).trans (hY3 i₀)
    have hRPt : R ≤ P.map (MulAut.conj t).toMonoidHom := by
      intro x hx
      refine ⟨t⁻¹ * x * t, hRP ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hRTn (T.inv_mem ht)) x).mp hx
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hPtKR : P.map (MulAut.conj t).toMonoidHom ≤ K ⊔ R := by
      rintro _ ⟨x, hx, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (hNRn (Subgroup.mem_top t)) x).mp (hPNR hx)
      simpa using this
    obtain ⟨hUZj, hQLj, -⟩ :=
      full_Sylow_short_core_propagation hcharKR hRsyl hRPt hPtKR (isBlock2_map_conj (hY i₀) t)
    obtain ⟨hQU, -⟩ := short_order_three_is_alternating_four hshort h3
    refine ⟨hshort, ?_, ?_, h3, ?_, hQLj.trans hQU.symm, by rw [hQU]; exact hUZj⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hKn.conj_mem y (hYK i₀ hy) t
    · obtain ⟨e⟩ := hYA4 i₀
      exact ⟨((Y i₀).equivMapOfInjective (MulAut.conj t).toMonoidHom hφ).symm.trans e⟩
    · have hJ : (thompsonJ R).map (MulAut.conj t).toMonoidHom = thompsonJ R :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (GammaExtra.normalizer_le_normalizer_thompsonJ R (hRTn ht))
      rw [← hJ, ← Subgroup.map_commutator, hYJ i₀]
  obtain ⟨c, hcY, hc3⟩ : ∃ c ∈ Y i₀, orderOf c = 3 := by
    obtain ⟨e⟩ := hYA4 i₀
    have h12 : Nat.card ↥(Y i₀) = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Y i₀)) 3 (by rw [h12]; norm_num)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hK3 := exists_three_pow_mem hsolv (R := R) hT hTn hMlt hTM hmax (hYK i₀ hcY) hc3
  have hthree : ∀ x ∈ Q ⊔ K, ∃ k : ℕ, x ^ 3 ^ k ∈ Q := by
    intro x hx
    have hmap : (Q ⊔ K).map (QuotientGroup.mk' Q) = K.map (QuotientGroup.mk' Q) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    obtain ⟨k, hk, hkx⟩ : QuotientGroup.mk' Q x ∈ K.map (QuotientGroup.mk' Q) :=
      hmap ▸ Subgroup.mem_map_of_mem _ hx
    obtain ⟨m, hm⟩ := hK3 k hk
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff (N := Q), QuotientGroup.mk_pow]
    change (QuotientGroup.mk' Q x) ^ 3 ^ m = 1
    rw [← hkx, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hm
  have hh : A3LiftHyp (Q ⊔ K) Q L :=
    { Q_le := le_sup_left
      Q_norm := fun g _ => hQn (Subgroup.mem_top g)
      Q_two := hQ2
      cent_le := fun x hx => hcharKR ⟨(sup_le (hQR.trans le_sup_right) le_sup_left) hx.1, hx.2⟩
      inj := E.inj
      short := fun j => (hfacts j).1
      L_le := fun j => (hfacts j).2.1.trans le_sup_right
      ord3 := fun j => (hfacts j).2.2.2.1
      Q_norm_L := fun j => Subgroup.le_normalizer_iff_commutator_le_right.mpr (by
        rw [(hfacts j).2.2.2.2.2.1]
        exact C1.blockQ_le _)
      comm_eq := fun j => (hfacts j).2.2.2.2.2.1
      U_le_Z := fun j => (hfacts j).2.2.2.2.2.2
      gen := congrArg (Q ⊔ ·) hKL
      three := hthree }
  have hnormal : ∀ j, ((L j).subgroupOf (Q ⊔ K)).Normal := fun j =>
    (normal_subgroupOf_iff_le_normalizer ((hfacts j).2.1.trans le_sup_right)).2
      (hh.H_le_normalizer_L j)
  refine ⟨r, L,
    { one_le := hr
      injective := E.inj
      le_odd := fun j => (hfacts j).2.1
      odd_eq := hKL
      indep := hh.L_indep
      commute := fun i j hij => hh.L_commute i j hij
      alt4 := fun j => (hfacts j).2.2.1
      short := fun j => (hfacts j).1
      card_quot := fun j => (hfacts j).2.2.2.1
      perfect_J := fun j => (hfacts j).2.2.2.2.1
      permuted := ?_
      transitive := ?_
      normal_QK := hnormal
      subnormal := fun j => IsSubnormal.step _ _ ((hfacts j).2.1.trans le_sup_right)
        (Subgroup.Normal.isSubnormal inferInstance) (hnormal j)
      U_eq := ?_
      U_indep := hh.U_indep
      U_ne_bot := hU1
      U_elem := hUel
      U_normal := normalizer_eq_top_iff.mp (top_le_iff.mp hUn)
      U_le := hUZ
      center_le := (BlueprintB2.centerTorsion_le 2 Q).trans hQR }⟩
  · intro t ht i
    obtain ⟨t₁, ht₁, hi⟩ := E.mem i
    obtain ⟨j, hj⟩ := E.all (t * t₁) (T.mul_mem ht ht₁)
    refine ⟨j, ?_⟩
    rw [hi, Subgroup.map_map, hconj_comp, hj]
  · intro i j
    obtain ⟨t₁, ht₁, hi⟩ := E.mem i
    obtain ⟨t₂, ht₂, hj⟩ := E.mem j
    refine ⟨t₂ * t₁⁻¹, T.mul_mem ht₂ (T.inv_mem ht₁), ?_⟩
    rw [hi, hj, Subgroup.map_map, hconj_comp, inv_mul_cancel_right]
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro q hq k hk
      have hk' : k ∈ ⨆ j, L j := by
        rw [← hKL]
        exact hk
      have hkT : k ∈ actTriv (Q ⊔ K) Q (⨆ j, blockQ (L j)) :=
        (iSup_le fun j => hh.L_le_actTriv j) hk'
      have hmem := hkT.2.2.2 q⁻¹ (Q.inv_mem hq)
      have e : ⁅q, k⁆ = q⁻¹⁻¹ * (k * q⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hmem
    · refine iSup_le fun j => ?_
      rw [← (hfacts j).2.2.2.2.2.1]
      exact Subgroup.commutator_mono le_rfl (hfacts j).2.1

end CFSG.Quasithin.SteinbergBS
