module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111Rk2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Burnside

variable {Q : Type*} [Group Q] [Finite Q]

theorem not_isCyclic_sylow_two_of_perfect (hperf : commutator Q = ⊤) (heven : 2 ∣ Nat.card Q)
    (P : Sylow 2 Q) : ¬ IsCyclic (P : Subgroup Q) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card Q).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  have hcomp := IsCyclic.isComplement' hmin hP
  have hker : (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker = ⊤ := by
    refine eq_top_iff.mpr (hperf ▸ (commutator_def Q) ▸ Subgroup.commutator_le.mpr ?_)
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have := IsCyclic.isMulCommutative (α := (P : Subgroup Q))
    exact mul_comm' _ _
  rw [hker, Subgroup.isComplement'_top_left] at hcomp
  exact P.ne_bot_of_dvd_card heven hcomp

end Burnside

section General

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_sq {t s : G} (ht : t ^ 2 = 1)
    (hs : s ∈ Subgroup.zpowers t) : s = 1 ∨ s = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have ht' : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← sq]
    exact ht
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, ht', one_zpow]
  · right
    rw [zpow_add, zpow_mul, ht', one_zpow, one_mul, zpow_one]

theorem TwoComp.inv_mul_conj_mem {T H K₁ K₂ : Subgroup G} (tc : TwoComp T H K₁ K₂)
    (hK₁ : K₁ ∈ cComp H) {k y : G} (hk : k ∈ K₁) (hy : y ∈ K₂) :
    y⁻¹ * (k * y * k⁻¹) ∈ pCoreOf 2 H := by
  have hkH : k ∈ H := le_of_mem_cComp hK₁ hk
  have hyH : y ∈ H := le_of_mem_cComp tc.cK₂ hy
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hco := tc.comm (π ⟨k, hkH⟩) ⟨⟨k, hkH⟩, hk, rfl⟩ (π ⟨y, hyH⟩) ⟨⟨y, hyH⟩, hy, rfl⟩
  have hmem : y⁻¹ * (k * y * k⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hyH) (H.mul_mem (H.mul_mem hkH hyH) (H.inv_mem hkH))
  have h1 : π ⟨y⁻¹ * (k * y * k⁻¹), hmem⟩ = 1 := by
    have e : (⟨y⁻¹ * (k * y * k⁻¹), hmem⟩ : ↥H) =
        (⟨y, hyH⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ * ⟨y, hyH⟩ * (⟨k, hkH⟩ : ↥H)⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hco]
    group
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
  exact ⟨_, h1, rfl⟩

variable [Finite G]

theorem false_of_isSylowTwoOf_of_le_two {K T : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hRS : IsRankOneSylow (O2Q K)) (hTK : IsSylowTwoOf (T ⊓ K) K)
    (h2 : ∀ x ∈ T ⊓ K, ∀ y ∈ T ⊓ K, x ∉ pCoreOf 2 K → y ∉ pCoreOf 2 K →
      x * y⁻¹ ∈ pCoreOf 2 K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set U := modO2Image K (T ⊓ K) with hU
  have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK
  have hidx : ¬ 2 ∣ U.index := by
    have := hTt.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  obtain ⟨hne, -, -⟩ := hRS _ hTt.2.1 hidx
  have hUne : U ≠ ⊥ := by
    intro hb
    apply hne
    rw [← hU, hb]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hone : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', hkk⟩
      rwa [show k = k' from Subtype.ext hkk.symm]
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  obtain ⟨x, hx, rfl⟩ := hu
  have hx1 : π x ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hxO : (x : G) ∉ pCoreOf 2 K := fun h => hx1 ((hone x).mpr h)
  have hcyc : IsCyclic ↥U := by
    have hxU : π x ∈ U := ⟨x, hx, rfl⟩
    refine ⟨⟨⟨π x, hxU⟩, fun v => ?_⟩⟩
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
    by_cases hy1 : π y = 1
    · refine ⟨0, Subtype.ext ?_⟩
      simp only [zpow_zero, OneMemClass.coe_one]
      exact hy1.symm
    · refine ⟨1, Subtype.ext ?_⟩
      have hyO : (y : G) ∉ pCoreOf 2 K := fun h => hy1 ((hone y).mpr h)
      have hxy := h2 x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy) hxO hyO
      have h3 : π (x * y⁻¹) = 1 := (hone (x * y⁻¹)).mpr hxy
      rw [map_mul, map_inv, mul_inv_eq_one] at h3
      simp only [zpow_one]
      exact h3
  have hperf : commutator (O2Q K) = ⊤ := by
    rw [commutator_def, ← Vol2.Ch11.SecS.modO2Image_self K]
    exact Vol2.Ch11.SecS.modO2Image_perfect le_rfl hK
  have heven : 2 ∣ Nat.card (O2Q K) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hTt.2.1
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq U (by simpa using hk)) hUne
    · exact (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ Subgroup.card_subgroup_dvd_card U)
  exact not_isCyclic_sylow_two_of_perfect hperf heven (IsPGroup.toSylow hTt.2.1 hidx) hcyc

end General

namespace Hyp5_2_4

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem eq_oTwoUpper_of_bender (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0})
    (hU3 : FactU3Cover) (h510 : Stmt5_1_10) (h524 : Stmt5_2_4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hK₁ : quasithinIsCComponent L₂ H)
    (hKeq : oTwoUpper H = conjClosure L₂ T) (hbend : IsBenderAny (O2Q L₂))
    (hS2 : sec52S M H ≤ L₂ ∨ ∃ t : G, t ^ 2 = 1 ∧
      t ∈ Subgroup.normalizer (pCoreOf 2 L₂ : Set G) ∧
      pCoreOf 2 (L₂ ⊔ sec52S M H) ≤ pCoreOf 2 L₂ ⊔ Subgroup.zpowers t) :
    L₂ = oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hL₂K : L₂ ≤ oTwoUpper H := hKeq ▸ le_conjClosure L₂ T
  by_contra hne
  have hlt : L₂ < oTwoUpper H := lt_of_le_of_ne hL₂K hne
  have hK₁c : L₂ ∈ cComp H := hK₁
  obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁c hKeq hlt
  set S := sec52S M H with hSdef
  have hK₂ := tc.cK₂
  have hK₂H : K₂ ≤ H := le_of_mem_cComp hK₂
  have hK₂K : K₂ ≤ oTwoUpper H := le_sup_right.trans tc.sup.symm.le
  have hL₂H : L₂ ≤ H := le_of_mem_cComp hK₁c
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hRS₁ := hRL _ (isRankOneListed_of_isBenderAny hU3 hbend)
  have hRS₂ : IsRankOneSylow (O2Q K₂) := by
    obtain ⟨t, -, hK₂eq⟩ := tc.conj
    rw [hK₂eq]
    exact hRS₁.of_mulEquiv
      (A312.modO2Equiv (L₂.equivMapOfInjective _ (MulAut.conj t).injective))
  have hTK₂ : IsSylowTwoOf (T ⊓ K₂) K₂ := A312.isSylowTwoOf_inf_of_subnormal hK₂.2.2.1 hTH
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  have hSK : S ⊓ oTwoUpper H = T ⊓ oTwoUpper H := hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hTK₂S : T ⊓ K₂ ≤ S := fun x hx => (hSK.ge ⟨hx.1, hK₂K hx.2⟩).1
  have hOHK₂ : pCoreOf 2 H ⊓ K₂ ≤ pCoreOf 2 K₂ := by
    have hn : K₂ ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ K₂ : Subgroup G) : Set G) :=
      fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 H (hK₂H hy), Subgroup.le_normalizer hy⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right hn ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hL₂K₂ : ∀ x ∈ L₂, x ∈ K₂ → x ∈ pCoreOf 2 K₂ := by
    intro x hx₁ hx₂
    refine hOHK₂ ⟨?_, hx₂⟩
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    have h1 : π ⟨x, hL₂H hx₁⟩ ∈ modO2Image H L₂ ⊓ modO2Image H K₂ :=
      ⟨⟨⟨x, hL₂H hx₁⟩, hx₁, rfl⟩, ⟨⟨x, hL₂H hx₁⟩, hx₂, rfl⟩⟩
    rw [tc.inf, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    exact ⟨_, h1, rfl⟩
  refine false_of_isSylowTwoOf_of_le_two hK₂.2.1 hRS₂ hTK₂ ?_
  rcases hS2 with hSL₂ | ⟨t, ht2, htN, hO⟩
  · intro x hx _ _ hxO _
    exact absurd (hL₂K₂ x (hSL₂ (hTK₂S hx)) hx.2) hxO
  have hSN : S ≤ Subgroup.normalizer (L₂ : Set G) :=
    (le_sup_right.trans le_sup_left).trans (h524 G T M L V H B D L₂ n hyp).2.2.2
  have hSK₂ : S ≤ Subgroup.normalizer (K₂ : Set G) := by
    intro s hs
    have hsH := hSH hs
    have hK₂c : K₂ ∈ cComp (oTwoUpper H) := cComp_mem_of_le hK₂ hK₂K hKH
    have hKs : K₂.map (MulAut.conj s).toMonoidHom ∈ cComp (oTwoUpper H) := by
      have h1 := cComp_map_mulEquiv (MulAut.conj s) hK₂c
      rwa [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hKN hsH)] at h1
    rcases tc.cK _ hKs with h1 | h1
    · exfalso
      apply tc.ne
      have h2 := map_mulAut_inv_map (MulAut.conj s) K₂
      rw [h1, ← map_inv,
        CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hSN (S.inv_mem hs))] at h2
      exact h2.symm
    · exact A38.map_conj_eq_iff.mp h1
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTH
  have hOS : pCoreOf 2 H ≤ S :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (hOT.trans h.T_le) (pCoreOf_le 2 H))
      (inf_le_right.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  set Y := (T ⊓ K₂) ⊔ pCoreOf 2 H with hYdef
  have hYS : Y ≤ S := sup_le hTK₂S hOS
  have hL₂Y : L₂ ≤ Subgroup.normalizer (Y : Set G) := by
    intro k hk
    have hkH := hL₂H hk
    have hmap : Y.map (MulAut.conj k).toMonoidHom ≤ Y := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have hc := tc.inv_mul_conj_mem hK₁c hk hy.2
        have e : (MulAut.conj k).toMonoidHom y = y * (y⁻¹ * (k * y * k⁻¹)) := by
          simp [MulAut.conj_apply]
        rw [e]
        exact Y.mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hc)
      · rintro _ ⟨y, hy, rfl⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hkH) y).mp hy
        exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using h1)
    exact mem_normalizer_of_conj_mem' fun y hy => by
      simpa [MulAut.conj_apply] using hmap ⟨y, hy, rfl⟩
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := by
    refine F1.le_normalizer_sup (fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (h.pCoreOf_inf_le hyp.hStar.1.1 hs), hSK₂ hs⟩)
      (hSH.trans (le_normalizer_pCoreOf 2 H))
  have hY : Y ≤ pCoreOf 2 (L₂ ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 (hYS.trans le_sup_right) (sup_le hL₂Y hSY)
      ((pCoreOf_isPGroup 2 _).to_le hYS)
  have hTK₂O : T ⊓ K₂ ≤ pCoreOf 2 L₂ ⊔ Subgroup.zpowers t := (le_sup_left.trans hY).trans hO
  have hzt : Subgroup.zpowers t ≤ Subgroup.normalizer (pCoreOf 2 L₂ : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hcoset : ∀ x ∈ T ⊓ K₂, x ∉ pCoreOf 2 L₂ → x * t⁻¹ ∈ pCoreOf 2 L₂ := by
    intro x hx hxO
    obtain ⟨a, ha, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hzt).mp (hTK₂O hx)
    rcases eq_one_or_eq_of_mem_zpowers_of_sq ht2 hs with rfl | rfl
    · exact absurd (by simpa using ha) hxO
    · simpa [mul_assoc] using ha
  intro x hx y hy hxO hyO
  have hxL : x ∉ pCoreOf 2 L₂ := fun h' => hxO (hL₂K₂ x ((pCoreOf_le 2 L₂) h') hx.2)
  have hyL : y ∉ pCoreOf 2 L₂ := fun h' => hyO (hL₂K₂ y ((pCoreOf_le 2 L₂) h') hy.2)
  have h3 : x * y⁻¹ ∈ pCoreOf 2 L₂ := by
    have := (pCoreOf 2 L₂).mul_mem (hcoset x hx hxL) ((pCoreOf 2 L₂).inv_mem (hcoset y hy hyL))
    simpa [mul_assoc] using this
  exact hL₂K₂ _ ((pCoreOf_le 2 L₂) h3) (K₂.mul_mem hx.2 (K₂.inv_mem hy.2))

end Hyp5_2_4

end CFSG.Quasithin.H13
