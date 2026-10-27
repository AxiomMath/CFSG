module

public import CFSG.Walter.Bender1970.S38.Basic
public import CFSG.Walter.Bender1970.S38.ActionMain
public import CFSG.Walter.Bender1970.S3.FStar
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}

theorem mem_normalizer_sylow_of_mem (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {k : G} (hk : k ∈ K)
    (hkQ : ∀ x ∈ (T : Subgroup G) ⊓ K, k * x * k⁻¹ ∈ (T : Subgroup G) ⊓ K) :
    k ∈ Subgroup.normalizer ((T : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem' fun s hs => ?_
  obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hs
  have hkw : k * w * k⁻¹ = w := by
    rw [(Subgroup.mem_centralizer_iff.mp hw.2) k hk, mul_inv_cancel_right]
  have : k * (w * v) * k⁻¹ = (k * w * k⁻¹) * (k * v * k⁻¹) := by group
  rw [this, hkw]
  exact (T : Subgroup G).mul_mem hw.1 (hkQ v hv).1

theorem eq_of_sq_eq_one_of_isCyclic {C : Subgroup G} (hC : IsCyclic C) {a b : G} (ha : a ∈ C)
    (hb : b ∈ C) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) : a = b := by
  classical
  have := Fintype.ofFinite C
  by_contra hab
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa using ha2)
    · exact Subtype.ext (by simpa using hb2)
  have h1 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  omega

theorem rank_inf_eq_of_isCyclic (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G))
    (hKQ : Bender38Component K ((T : Subgroup G) ⊓ K))
    (hWne : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥)
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) :
    rank ((T : Subgroup G) ⊓ K) = rank (T : Subgroup G) - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tg := (T : Subgroup G) with hTg
  set W := Tg ⊓ Subgroup.centralizer (K : Set G) with hW
  set Q := Tg ⊓ K with hQ
  have hcommT : ∀ x ∈ Tg, ∀ y ∈ Tg, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy => hcommT x hx.1 y hy.1
  have hTp : IsPGroup 2 Tg := T.isPGroup'
  have hQp : IsPGroup 2 Q := hTp.to_le inf_le_left
  have hWQ := inf_inf_eq_bot T.isPGroup' hKQ
  have hΩQ : Nat.card (omegaOneOfComm 2 Q hcommQ) = Nat.card Q := by
    congr 2
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, hKQ.sq_eq_one x h⟩⟩
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hw₀1' : w₀ ≠ 1 := fun h => hw₀1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp) ⟨w₀, hw₀.1⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hw₀1' hk
  set w₁ := w₀ ^ 2 ^ (k - 1) with hw₁
  have hw₁W : w₁ ∈ W := W.pow_mem hw₀ _
  have hw₁o : orderOf w₁ = 2 := by
    rw [hw₁, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 1)),
      hk, Nat.pow_div (Nat.sub_le k 1) two_pos, Nat.sub_sub_self (by omega), pow_one]
  have hw₁1 : w₁ ≠ 1 := fun h => by rw [h, orderOf_one] at hw₁o; omega
  have hw₁2 : w₁ ^ 2 = 1 := by rw [← hw₁o, pow_orderOf_eq_one]
  have hΩW : ∀ x ∈ W, x ^ 2 = 1 → x = 1 ∨ x = w₁ := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (eq_of_sq_eq_one_of_isCyclic hWcyc hx hw₁W hx1 hw₁1 hx2 hw₁2)
  have hΩT : Nat.card (omegaOneOfComm 2 Tg hcommT) = 2 * Nat.card Q := by
    have hmemΩT : ∀ x, x ∈ omegaOneOfComm 2 Tg hcommT ↔ x ∈ Tg ∧ x ^ 2 = 1 := fun x => Iff.rfl
    let f : Bool × Q → omegaOneOfComm 2 Tg hcommT := fun x =>
      ⟨(if x.1 then w₁ else 1) * x.2, by
        refine ⟨Tg.mul_mem ?_ x.2.2.1, ?_⟩
        · cases x.1
          · exact Tg.one_mem
          · exact hw₁W.1
        · have hc : Commute (if x.1 then w₁ else 1) (x.2 : G) := by
            cases x.1
            · exact Commute.one_left _
            · exact hcommT _ hw₁W.1 _ x.2.2.1
          rw [hc.mul_pow, hKQ.sq_eq_one _ x.2.2, mul_one]
          cases x.1
          · exact one_pow 2
          · exact hw₁2⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨b₁, v₁⟩ ⟨b₂, v₂⟩ h
        have h1 : (if b₁ then w₁ else 1) * (v₁ : G) = (if b₂ then w₁ else 1) * v₂ :=
          congrArg Subtype.val h
        have hdec : ∀ (a a' : G) (v v' : G), a ∈ W → a' ∈ W → v ∈ Q → v' ∈ Q →
            a * v = a' * v' → a = a' ∧ v = v' := by
          intro a a' v v' ha ha' hv hv' heq
          have h2 : a'⁻¹ * a = v' * v⁻¹ := by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq, mul_inv_cancel_right]
          have h3 : a'⁻¹ * a ∈ W ⊓ Q := ⟨W.mul_mem (W.inv_mem ha') ha,
            h2 ▸ Q.mul_mem hv' (Q.inv_mem hv)⟩
          rw [hWQ, Subgroup.mem_bot, inv_mul_eq_one] at h3
          subst h3
          exact ⟨rfl, mul_left_cancel heq⟩
        have hbW : ∀ b : Bool, (if b then w₁ else 1) ∈ W := fun b => by
          cases b
          · exact W.one_mem
          · exact hw₁W
        obtain ⟨h3, h4⟩ := hdec _ _ _ _ (hbW b₁) (hbW b₂) v₁.2 v₂.2 h1
        have hb : b₁ = b₂ := by
          cases b₁ <;> cases b₂
          · rfl
          · exact absurd h3.symm (by simpa using hw₁1)
          · exact absurd h3 (by simpa using hw₁1)
          · rfl
        rw [hb, Subtype.ext h4]
      · rintro ⟨x, hxT, hx2⟩
        obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hxT
        have hw2 : w ^ 2 = 1 := by
          have hc : Commute w v := hcommT w hw.1 v hv.1
          rw [hc.mul_pow, hKQ.sq_eq_one v hv, mul_one] at hx2
          exact hx2
        rcases hΩW w hw hw2 with rfl | rfl
        · exact ⟨(false, ⟨v, hv⟩), Subtype.ext (by simp [f])⟩
        · exact ⟨(true, ⟨v, hv⟩), Subtype.ext (by simp [f])⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_bool]
  have h1 := card_omegaOneOfComm Nat.prime_two Tg hcommT hTp
  have h2 := card_omegaOneOfComm Nat.prime_two Q hcommQ hQp
  rw [hΩT, ← hΩQ, h2] at h1
  rw [rank_eq_pRank_of_isPGroup Nat.prime_two hTp, rank_eq_pRank_of_isPGroup Nat.prime_two hQp]
  have h3 : 2 ^ (CFSG.Open.pRank 2 Q + 1) = 2 ^ CFSG.Open.pRank 2 Tg := by
    rw [pow_succ, mul_comm, h1]
  have := Nat.pow_right_injective le_rfl h3
  omega

theorem eq_of_isComponentOf_of_isCyclic
    (hHA : IsAStar H) (hK : IsComponentOf K H)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G))
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G))
    {L : Subgroup G} (hL : IsComponentOf L H) : L = K := by
  by_contra hne
  have hLK : ⁅L, K⁆ = ⊥ := (isComponentOf_eq_or_commutator_eq_bot hL hK).resolve_left hne
  have hLQ := bender38Component hHA hL T hTH hTab
  have hTLW : ∀ x ∈ (T : Subgroup G) ⊓ L,
      x ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := fun x hx =>
    ⟨hx.1, (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK) hx.2⟩
  obtain ⟨a, ha, ha1, -⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ L)
    (by have := hLQ.four_le_card; omega) 1
  obtain ⟨b, hb, hb1, hba⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ L)
    (by have := hLQ.four_le_card; omega) a
  exact hba (eq_of_sq_eq_one_of_isCyclic hWcyc (hTLW b hb) (hTLW a ha) hb1 ha1
    (hLQ.sq_eq_one b hb) (hLQ.sq_eq_one a ha))

theorem componentLayerOf_le_of_isCyclic
    (hHA : IsAStar H) (hK : IsComponentOf K H)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G))
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) :
    componentLayerOf H ≤ K :=
  sSup_le fun _ hL => (eq_of_isComponentOf_of_isCyclic hHA hK T hTH hTab hWcyc hL).le

theorem qCoreOf_two_le (hK : IsComponentOf K H) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) :
    qCoreOf H 2 ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · have h1 := CFSG.Glauberman.pCore_le_sylow (T.subtype hTH) hx
    exact h1
  · have h1 : (x : G) ∈ CFSG.fittingSubgroupOf H := ⟨x, CFSG.pCore_le_fitting H 2 hx, rfl⟩
    have h2 := fittingSubgroupOf_le_centralizer_layer H h1
    show (x : G) ∈ Subgroup.centralizer (K : Set G)
    have hKE : K ≤ componentLayerOf H := le_sSup hK
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro y hy
    exact h2 y (hKE hy)

theorem mem_center_of_isCyclic
    (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G))
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G))
    {s : G} (hsW : s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G))
    (hs2 : orderOf s = 2) (hsF : s ∈ generalizedFittingSubgroupOf H) :
    ∀ h ∈ H, h * s * h⁻¹ = s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    omega
  have hEK := componentLayerOf_le_of_isCyclic hHA hK T hTH hTab hWcyc
  have hsE : s ∈ Subgroup.centralizer (componentLayerOf H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hsW.2 x (hEK hx)
  have hsFit : s ∈ CFSG.fittingSubgroupOf H :=
    generalizedFittingSubgroupOf_inf_centralizer_le H ⟨hsF, hsE⟩
  have hO2W := qCoreOf_two_le hK T hTH
  obtain ⟨s', hs'F, rfl⟩ := hsFit
  have hs2' : orderOf (s' : G) = 2 := hs2
  have hs'2 : s' ^ 2 ^ 1 = 1 := Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, ← hs2', pow_orderOf_eq_one]
    rfl)
  have hs'O : s' ∈ CFSG.pCore 2 H := mem_pCore_of_mem_normal_nilpotent Nat.prime_two
    CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent hs'F hs'2
  intro h hh
  have hconj : (⟨h, hh⟩ : H) * s' * (⟨h, hh⟩ : H)⁻¹ ∈ CFSG.pCore 2 H :=
    CFSG.pCore_normal.conj_mem s' hs'O ⟨h, hh⟩
  have h1 := hO2W ⟨_, hconj, rfl⟩
  have hconj2 : (h * s' * h⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← hs2', pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hconj1 : h * s' * h⁻¹ ≠ 1 := by
    intro h2
    apply hne1 _ hs2
    calc (s' : G) = h⁻¹ * (h * s' * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group
  exact eq_of_sq_eq_one_of_isCyclic hWcyc h1 hsW hconj1 (hne1 _ hs2) hconj2
    (by show (s' : G) ^ 2 = 1; rw [← hs2', pow_orderOf_eq_one])

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem exists_conj_of_isCyclic
    {t : G} (ht : orderOf t = 2) (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) (hK : IsComponentOf K H)
    (hWcyc : IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G))
    {u v : G} (hu : u ∈ (T : Subgroup G)) (hu2 : orderOf u = 2) (hv : v ∈ (T : Subgroup G))
    (hv2 : orderOf v = 2) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), n * u * n⁻¹ = v := by
  have := hG.isSimpleGroup
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hTab := hG.hasAbelianSylowTwo T
  have hKQ := hG.bender38Component' hH T htT hK
  have hWne := hG.centralizer_inf_ne_bot ht hH T htT hK
  have hrank := rank_inf_eq_of_isCyclic hHA hK T hTH hTab hKQ hWne hWcyc
  obtain ⟨n₁, hn₁, hn₁u⟩ := bender1970_1_3 hG.nonabelian T hTab inf_le_left hrank hu hu2
  obtain ⟨n₂, hn₂, hn₂v⟩ := bender1970_1_3 hG.nonabelian T hTab inf_le_left hrank hv hv2
  have hconjord : ∀ (n x : G), orderOf (n * x * n⁻¹) = orderOf x := fun n x => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    omega
  obtain ⟨k, hk, hkQ, hkuv⟩ := hKQ.trans _ hn₁u (hne1 _ ((hconjord _ _).trans hu2)) _ hn₂v
    (hne1 _ ((hconjord _ _).trans hv2))
  have hkN := mem_normalizer_sylow_of_mem hHA hK T hTH hk hkQ
  refine ⟨n₂⁻¹ * k * n₁, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₂) hkN) hn₁,
    ?_⟩
  calc n₂⁻¹ * k * n₁ * u * (n₂⁻¹ * k * n₁)⁻¹ = n₂⁻¹ * (k * (n₁ * u * n₁⁻¹) * k⁻¹) * n₂ := by
        group
    _ = n₂⁻¹ * (n₂ * v * n₂⁻¹) * n₂ := by rw [hkuv]
    _ = v := by group

theorem centralizer_eq_of_central (hHco : IsCoatom H) {s : G} (hs1 : s ≠ 1)
    (hs : ∀ h ∈ H, h * s * h⁻¹ = s) :
    Subgroup.centralizer ({s} : Set G) = H ∧ benderM s = {H} := by
  have hHC : H ≤ Subgroup.centralizer ({s} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * s = h * s * h⁻¹ * h := by group
      _ = s * h := by rw [hs h hh]
  have hCH : Subgroup.centralizer ({s} : Set G) = H :=
    (hHco.le_iff.mp hHC).resolve_left (hG.centralizer_ne_top hs1)
  refine ⟨hCH, ?_⟩
  have hmem : ∀ M ∈ benderM s, M = H := fun M hM =>
    (hHco.le_iff.mp (hCH ▸ centralizer_le_of_mem_benderM hM)).resolve_left
      (isCoatom_of_mem_benderM hM).1
  obtain ⟨M, hM⟩ := hG.benderM_nonempty hs1
  ext M'
  constructor
  · intro hM'
    exact hmem M' hM'
  · intro hM'
    rw [Set.mem_singleton_iff] at hM'
    rw [hM', ← hmem M hM]
    exact hM

end BenderCounterexample

end CFSG.Walter
