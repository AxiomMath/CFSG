module

public import CFSG.Quasithin.H13.A5S136k
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.Quasithin.H13.A5X1367n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup normalizer_le_normalizer_pCoreOf)
open scoped commutatorElement

theorem exists_omegaOneCenter_of_normal {G : Type} [Group G] [Finite G] {T U : Subgroup G}
    (hT : IsPGroup 2 T) (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  set C := U.subgroupOf T ⊓ Subgroup.center ↥T with hC
  have hCne : C ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hC2 : IsPGroup 2 C := (hT.to_subgroup (U.subgroupOf T)).to_inf_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥C := by
    rcases hC2.card_eq_or_dvd with h1 | h2
    · exfalso
      apply hCne
      exact Subgroup.eq_bot_of_card_eq C h1
    · exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 hdvd
  have hx1 : x.1.1 ≠ 1 := by
    intro h1
    have : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx2 : x.1.1 ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one x
    rw [hx] at h2
    have h2' : (x ^ 2).1.1 = (1 : ↥C).1.1 := by rw [h2]
    simpa using h2'
  intro h
  apply hx1
  have hmem : x.1.1 ∈ U ⊓ quasithinOmegaOneCenter T := by
    refine ⟨Subgroup.mem_subgroupOf.mp x.2.1, Subgroup.subset_closure ⟨⟨x.1.2, ?_⟩, hx2⟩⟩
    show x.1.1 ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp x.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  rw [h, Subgroup.mem_bot] at hmem
  exact hmem

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem pCoreOf_sup_T_eq_bot (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) : pCoreOf 2 (K₀ ⊔ T) = ⊥ := by
  by_contra hO
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hTsyl : IsSylowTwoOf T (K₀ ⊔ T) := isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hsylTv := S.isSylowTwoOf_Tv h1222 h517
  have hidx : S.Tv.relIndex T ≤ 2 := le_of_eq S.index_Tv
  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hvO : S.v12 ∈ pCoreOf 2 (K₀ ⊔ S.Tv) := by
    have hle : Subgroup.zpowers S.v12 ≤ K₀ ⊔ S.Tv :=
      (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : K₀ ⊔ S.Tv ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    exact le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
  have hL : quasithinIsLocal S.Tv K₀ :=
    ⟨S.isPGroup_T.to_le inf_le_left, hK₀,
      (B6.isSylowTwoOf_mono hsylTv le_sup_right (sup_le hK₀G S.Tv_le_Gv)).2.2,
      fun h => S.v12_ne_one (by rw [h, Subgroup.mem_bot] at hvO; exact hvO)⟩
  obtain ⟨K₂, hK₂, hK₀K₂⟩ :=
    Vol2Native.lemma_1_2_5_exists hloc h37 h39 hO hTsyl inf_le_left hidx hL le_sup_left
  have hK₂le : K₂ ≤ K₀ ⊔ T := le_of_mem_cComp hK₂
  have hK₂H : K₂ ⊔ T = K₀ ⊔ T :=
    le_antisymm (sup_le hK₂le le_sup_right) (sup_le_sup_right hK₀K₂ T)
  have hK₂loc : quasithinIsLocal T K₂ :=
    ⟨S.isPGroup_T, cComp_mem_of_le hK₂ le_sup_left (le_of_eq hK₂H),
      by rw [hK₂H]; exact hTsyl.2.2, by rw [hK₂H]; exact hO⟩
  have hZK : ⁅quasithinOmegaOneCenter T, K₂⁆ ≠ ⊥ := by
    intro h
    apply hz
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.commutator_mem_commutator S.z_mem_omegaOneCenter (hK₀K₂ hk)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hK₂f := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hK₂loc hZK
  have hQ₂ : QTH13 G T K₂ :=
    { S.h13 with faithful := hK₂f, a5 := fun _ K hK => S.h13.a5 S.a5 K hK }
  have hA5₂ := S.h13.a5 S.a5 K₂ hK₂f
  obtain ⟨V₂, ⟨S₂⟩⟩ := exists_setting h132two h132fsu h132A5 hQ₂ hA5₂
  have hTK₂ : T ≤ Subgroup.normalizer (K₂ : Set G) := S₂.T_le_NL
  have hZ₂ := S₂.omegaOneCenter_inf_centralizer_L h331 h1327
  set O := pCoreOf 2 K₂ with hOdef
  have hOK : O ≤ K₂ := pCoreOf_le 2 K₂
  have hKO : K₂ ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K₂)
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 K₂
  have hOT : O ≤ T := by
    have hsub : IsSubnormal K₂ (K₂ ⊔ T) :=
      IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hTK₂)) (IsSubnormal.refl _)
    exact (pCoreOf_two_le_of_subnormal hsub).trans
      (pCoreOf_two_le_of_isSylowTwoOf (hK₂H ▸ hTsyl))
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  obtain ⟨φ, hφs, hφk⟩ := hA5₂
  set R₀ := K₀.subgroupOf K₂ with hR₀
  have hR₀p : ⁅R₀, R₀⁆ = R₀ := by
    apply Subgroup.map_injective K₂.subtype_injective
    rw [Subgroup.map_commutator, hR₀, Subgroup.map_subgroupOf_eq_of_le hK₀K₂, hK₀p]
  have hRtop : R₀.map φ = ⊤ := by
    refine eq_top_of_perfect_alt5 (by rw [← Subgroup.map_commutator, hR₀p]) fun hbot => ?_
    have hK₀O : K₀ ≤ O := by
      intro k hk
      have hk' : (⟨k, hK₀K₂ hk⟩ : ↥K₂) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have : φ ⟨k, hK₀K₂ hk⟩ ∈ R₀.map φ := ⟨⟨k, hK₀K₂ hk⟩, hk, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      rw [hφk] at hk'
      exact ⟨_, hk', rfl⟩
    have hs : Group.IsSolvable ↥K₀ := by
      have : Group.IsNilpotent ↥K₀ := (hO2.to_le hK₀O).isNilpotent
      infer_instance
    have h1 := (isSolvable_iff_perfectCore_eq_bot K₀).mp hs
    rw [perfectCore_eq_self_of_perfect hK₀p] at h1
    exact ne_bot_of_mem_cComp hK₀ h1
  have hdecomp : ∀ k ∈ K₂, ∃ k₀ ∈ K₀, k₀⁻¹ * k ∈ O := by
    intro k hk
    obtain ⟨⟨k₀, hk₀K₂⟩, hk₀, he⟩ : φ ⟨k, hk⟩ ∈ R₀.map φ := hRtop ▸ Subgroup.mem_top _
    refine ⟨k₀, hk₀, ?_⟩
    have : (⟨k₀, hk₀K₂⟩ : ↥K₂)⁻¹ * ⟨k, hk⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hφk] at this
    exact ⟨_, this, rfl⟩
  set Nk := K₂ ⊓ Subgroup.normalizer (K₀ : Set G) with hNk
  have hNkO : Nk ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hKO
  have hNkK : Nk ⊔ O = K₂ := by
    refine le_antisymm (sup_le inf_le_left hOK) fun k hk => ?_
    obtain ⟨k₀, hk₀, hko⟩ := hdecomp k hk
    have hk₀N : k₀ ∈ Nk := ⟨hK₀K₂ hk₀, Subgroup.le_normalizer hk₀⟩
    have : k = k₀ * (k₀⁻¹ * k) := by group
    rw [this]
    exact (Nk ⊔ O).mul_mem (Subgroup.mem_sup_left hk₀N) (Subgroup.mem_sup_right hko)
  have hfin : ∀ A B : Subgroup G, A.relIndex B ≠ 0 := fun A B => Subgroup.index_ne_zero_of_finite
  have hidxN : Nk.relIndex K₂ ≤ 2 := by
    have h1 := B6.relIndex_inf_eq_relIndex_sup hNkO
    rw [hNkK] at h1
    rw [← h1]
    have hTvO : S.Tv ⊓ O ≤ Nk ⊓ O := by
      intro x hx
      exact ⟨⟨hOK hx.2, hTK hx.1⟩, hx.2⟩
    calc (Nk ⊓ O).relIndex O ≤ (S.Tv ⊓ O).relIndex O :=
          Subgroup.relIndex_le_of_le_left hTvO (hfin _ _)
      _ = S.Tv.relIndex O := Subgroup.inf_relIndex_right _ _
      _ ≤ S.Tv.relIndex T := Subgroup.relIndex_le_of_le_right hOT (hfin _ _)
      _ ≤ 2 := hidx
  have hO2res := hK₂f.2.1
  have hNkeq : Nk = K₂ := by
    have hNkK₂ : Nk ≤ K₂ := inf_le_left
    rcases Nat.lt_or_ge (Nk.relIndex K₂) 2 with h1 | h2
    · have hone : Nk.relIndex K₂ = 1 := by
        have := hfin Nk K₂
        omega
      exact le_antisymm hNkK₂ (Subgroup.relIndex_eq_one.mp hone)
    · have htwo : (Nk.subgroupOf K₂).index = 2 := le_antisymm hidxN h2
      have hnorm : (Nk.subgroupOf K₂).Normal := Subgroup.normal_of_index_eq_two htwo
      refine hO2res Nk hNkK₂ hnorm fun x hx => ⟨1, ?_⟩
      have := Subgroup.mul_self_mem_of_index_two htwo ⟨x, hx⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa [pow_one, pow_two] using this
  have hK₀n : (K₀.subgroupOf K₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀K₂).2 (hNkeq ▸ inf_le_right)
  have hKeq : K₀ = K₂ := by
    refine hO2res K₀ hK₀K₂ hK₀n fun x hx => ?_
    obtain ⟨k₀, hk₀, hko⟩ := hdecomp x hx
    obtain ⟨j, hj⟩ := hO2 ⟨_, hko⟩
    have hj' : (k₀⁻¹ * x) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hxN : k₀⁻¹ * x ∈ Subgroup.normalizer (K₀ : Set G) := by
      have hm : k₀⁻¹ * x ∈ K₂ := K₂.mul_mem (K₂.inv_mem (hK₀K₂ hk₀)) hx
      rw [← hNkeq] at hm
      exact hm.2
    have key : ∀ m : ℕ, x ^ m * ((k₀⁻¹ * x) ^ m)⁻¹ ∈ K₀ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hpow : (k₀⁻¹ * x) ^ m ∈ Subgroup.normalizer (K₀ : Set G) :=
          Subgroup.pow_mem _ hxN m
        have hk₀' : x * (k₀⁻¹ * x)⁻¹ ∈ K₀ := by
          rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
          exact hk₀
        have h1 : (k₀⁻¹ * x) ^ m * (x * (k₀⁻¹ * x)⁻¹) * ((k₀⁻¹ * x) ^ m)⁻¹ ∈ K₀ :=
          (Subgroup.mem_normalizer_iff.mp hpow _).mp hk₀'
        have e : x ^ (m + 1) * ((k₀⁻¹ * x) ^ (m + 1))⁻¹ =
            (x ^ m * ((k₀⁻¹ * x) ^ m)⁻¹) *
              ((k₀⁻¹ * x) ^ m * (x * (k₀⁻¹ * x)⁻¹) * ((k₀⁻¹ * x) ^ m)⁻¹) := by
          rw [pow_succ, pow_succ]
          group
        rw [e]
        exact K₀.mul_mem ih h1
    refine ⟨j, ?_⟩
    have := key (2 ^ j)
    rwa [hj', inv_one, mul_one] at this
  have hCT : T ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥ := by
    intro h
    have hv : S.v12 ∈ T ⊓ Subgroup.centralizer (K₂ : Set G) := by
      refine ⟨S.V_le_T S.v12_mem_V, ?_⟩
      show S.v12 ∈ Subgroup.centralizer (K₂ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [← hKeq] at hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hk)
    rw [h, Subgroup.mem_bot] at hv
    exact S.v12_ne_one hv
  have hCTn : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (K₂ : Set G) : Subgroup G) : Set G) := by
    intro t ht
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · refine ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizer K₂ (hTK₂ ht)) x).mp hx.2
    · refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizer K₂ (Subgroup.inv_mem _ (hTK₂ ht))) x).mp hx.2
      rwa [inv_inv] at this
  apply exists_omegaOneCenter_of_normal S.isPGroup_T inf_le_left hCTn hCT
  rw [eq_bot_iff, ← hZ₂]
  rintro x ⟨⟨-, hx⟩, hxZ⟩
  exact ⟨hxZ, hx⟩

theorem not_le_normalizer_of_characteristic (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) {C : Subgroup G} (hCT : C ≤ S.Tv)
    (hC : C ≠ ⊥) (hchar : (C.subgroupOf S.Tv).Characteristic) :
    ¬ K₀ ≤ Subgroup.normalizer (C : Set G) := by
  intro hKC
  apply hC
  have hO := S.pCoreOf_sup_T_eq_bot h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀
    hTK hz
  have hTvn : T ≤ Subgroup.normalizer (S.Tv : Set G) := by
    have h2 : (S.Tv.subgroupOf T).index = 2 := S.index_Tv
    have hn := Subgroup.normal_of_index_eq_two h2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    hTvn.trans (normalizer_le_normalizer_of_characteristic hCT hchar)
  have hC2 : IsPGroup 2 C := S.isPGroup_T.to_le (hCT.trans inf_le_left)
  have hCH : C ≤ K₀ ⊔ T := (hCT.trans inf_le_left).trans le_sup_right
  have hle : C ≤ pCoreOf 2 (K₀ ⊔ T) :=
    le_pCoreOf_of_normalizes hCH (sup_le hKC hTC) hC2
  rw [hO] at hle
  exact le_bot_iff.mp hle

end Setting

end CFSG.Quasithin.H13.A5
