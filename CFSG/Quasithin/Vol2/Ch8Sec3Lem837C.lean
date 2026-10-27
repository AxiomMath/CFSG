module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837A
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837KG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_le {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

omit [Finite G] in
theorem zpowers_le_pCoreOf {H : Subgroup G} {z : G} (hz2 : orderOf z = 2) (hzH : z ∈ H)
    (hH : H ≤ Subgroup.centralizer ({z} : Set G)) : Subgroup.zpowers z ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2grp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((Subgroup.zpowers_le).mpr hzH) (fun c hc => ?_) hz2grp
  have hcz : Commute c z := (Subgroup.mem_centralizer_iff.mp (hH hc) z rfl).symm
  refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [(hcz.zpow_right k).eq, mul_inv_cancel_right]
    exact hy
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [((hcz.inv_left).zpow_right k).eq, mul_assoc, inv_mul_cancel, mul_one]
    exact hy

theorem pCoreOf_sup_eq_inf_centralizerSection {H X T : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hXH : X ≤ H)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    pCoreOf 2 (X ⊔ T) = T ⊓ centralizerSection H X (pCoreOf 2 X) ∧
      IsSylowTwoOf (pCoreOf 2 (X ⊔ T)) (centralizerSection H X (pCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizerSection H X (pCoreOf 2 X) with hYdef
  have hTsyl : IsSylowTwoOf T (H ⊓ Subgroup.normalizer (X : Set G)) :=
    isSylowTwoOf_of_le hT (le_inf hTH hTX)
  have hS : IsSylowTwoOf (T ⊓ Y) Y := isSylowTwoOf_inf_centralizerSection hTsyl
  have hsig := isSignalizer_of_isSylowTwoOf_centralizerSection hXH hS
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    le_normalizer_centralizerSection H X ⟨hTH ht, hTX ht⟩
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTX
  have h1 : T ⊓ Y ≤ pCoreOf 2 (X ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (sup_le hsig.2.2 fun t ht => ?_) hS.2.1
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTY ht⟩
  have hTXT : IsSylowIn 2 T (X ⊔ T) :=
    isSylowTwoOf_of_le hT le_sup_right
  have hOT : pCoreOf 2 (X ⊔ T) ≤ T := pCoreOf_le_of_isSylowIn hTXT
  have hOXT : pCoreOf 2 (X ⊔ T) ≤ X ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hOY : pCoreOf 2 (X ⊔ T) ≤ Y := by
    rw [le_centralizerSection_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 X)]
    refine ⟨hOXT.trans (sup_le hXH hTH), (Subgroup.commutator_le).mpr fun x hx o ho => ?_⟩
    have hoX : o ∈ Subgroup.normalizer (X : Set G) := hXTN (hOXT ho)
    have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx)
    have hc1 : x * o * x⁻¹ * o⁻¹ ∈ X := by
      have h2 : o * x⁻¹ * o⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hoX _).mp (X.inv_mem hx)
      have e : x * o * x⁻¹ * o⁻¹ = x * (o * x⁻¹ * o⁻¹) := by group
      rw [e]
      exact X.mul_mem hx h2
    have hc2 : x * o * x⁻¹ * o⁻¹ ∈ pCoreOf 2 (X ⊔ T) := by
      have h2 : x * o * x⁻¹ ∈ pCoreOf 2 (X ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp hxO o).mp ho
      exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ ho)
    have hXO : X ⊓ pCoreOf 2 (X ⊔ T) ≤ pCoreOf 2 X := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun y hy => ?_)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy)⟩
    rw [commutatorElement_def]
    exact hXO ⟨hc1, hc2⟩
  have heq : pCoreOf 2 (X ⊔ T) = T ⊓ Y := le_antisymm (le_inf hOT hOY) h1
  exact ⟨heq, heq ▸ hS⟩

theorem isPGroup_inf_centralizer
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) :
    IsPGroup 2 ↥((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnn := not_le_normalizer_of_row hrow
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hL0Tq := B6.isTwoQuotient_of_sup_eq hT2
    (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure L T)) (sup_comm T (fsuL0 T L))
  rintro ⟨y, hy, hyC⟩
  obtain ⟨k, hk⟩ := hL0Tq y hy
  have hO : y ^ 2 ^ k ∈ pCoreOf 2 (fsuL0 T L) := hCL0 ⟨hk, Subgroup.pow_mem _ hyC _⟩
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hO⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have hm' : (y ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  change y ^ 2 ^ (k + m) = 1
  rw [pow_add, pow_mul, hm']

theorem normalizer_ch83S_le
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) (z : G) :
    Subgroup.normalizer (ch83S T L z : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := thompsonJ_le_centralizer_fsuV (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
    (a39ForSQTK_of_cat h39) hyp hV hN
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hc : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hc.1, hc.2, hVVM⟩
    · exact Or.inr ⟨hc, rfl⟩
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    isSylowTwoOf_of_le hyp.fsu.sylow hTK
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hXL : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hQ : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L ⊔ T) := by
    have hCV2 := isPGroup_inf_centralizer h37 h38 h326 hyp hrow
    have hle : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
        (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      inf_le_inf_right _ le_sup_right
    refine le_trans hle (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => ?_) hCV2)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      Vol2.Ch10.SecA.le_normalizer_centralizer hN hg⟩
  have hQS : pCoreOf 2 (fsuL0 T L ⊔ T) ≤ ch83S T L z := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)).trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hJS : thompsonJ T ≤ ch83S T L z :=
    (le_inf (thompsonJ_le_self T) hJ).trans (hQ.trans hQS)
  exact (h3108 G T L I (fsuV T I) hyp.fsu hVp hJ (ch83S T L z)
    (hT2.to_le hST) hJS).2

theorem ch83Yz_le_fsuM (h836 : Stmt8_3_6) (hYns : Claim837YNonsolv) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    ch83Yz T L z ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hsolv : Group.IsSolvable ↥(ch83Yz T L z)
  swap
  · exact hYns G T L I hyp h731 hc hrow z hz2 hzV hsolv
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hTX : T ≤ Subgroup.normalizer (ch83X T L z : Set G) := fun t ht => by
    have h1 : t ∈ Subgroup.normalizer
        ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (hTM ht) (Subgroup.le_normalizer (hTz ht))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [ch83X, E1.map_twoResidual, h1]
  obtain ⟨-, hS⟩ := pCoreOf_sup_eq_inf_centralizerSection hyp.fsu.sylow hTz hXGz hTX
  have hn1 : E1.nParam (ch83Yz T L z) ≤ 1 := E1.solvable_nParam_le_one hsolv
  have hn0 : E1.nParam (ch83Yz T L z) ≠ 0 := by
    intro h
    have hodd := E1.odd_of_nParam_le_zero (le_of_eq h)
    have hzS : z ∈ ch83S T L z :=
      zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) (sup_le hXGz hTz)
        (Subgroup.mem_zpowers z)
    have hzY : z ∈ ch83Yz T L z := hS.1 hzS
    have h2 : 2 ∣ Nat.card ↥(ch83Yz T L z) := by
      have := Subgroup.orderOf_dvd_natCard (ch83Yz T L z) hzY
      rwa [hz2] at this
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
  have hn : E1.nParam (ch83Yz T L z) = 1 := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hn1)
    rw [← hk] at hn1 hn0 ⊢
    have hk1 : k ≤ 1 := by exact_mod_cast hn1
    have hk0 : k ≠ 0 := by exact_mod_cast hn0
    have : k = 1 := by omega
    rw [this]
    rfl
  exact h836 G T L I hyp h731 hc hrow z hz2 hzV _ hS hn

theorem inf_normalizer_ch83X_le
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (h836 : Stmt8_3_6) (hYns : Claim837YNonsolv) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.normalizer (ch83X T L z : Set G) ≤
      fsuM T L := by
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hTX : T ≤ Subgroup.normalizer (ch83X T L z : Set G) := fun t ht => by
    have h1 : t ∈ Subgroup.normalizer
        ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (hTM ht) (Subgroup.le_normalizer (hTz ht))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [ch83X, E1.map_twoResidual, h1]
  obtain ⟨-, hS⟩ := pCoreOf_sup_eq_inf_centralizerSection hyp.fsu.sylow hTz hXGz hTX
  have hYM := ch83Yz_le_fsuM h836 hYns hyp h731 hrow hV hN hz2 hzV
  have hSM := normalizer_ch83S_le h37 h38 h39 h326 h3108 hyp hV hrow hN z
  have hYH : ch83Yz T L z ≤
      Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.normalizer (ch83X T L z : Set G) :=
    le_inf (centralizerSection_le_left _ _ _) (centralizerSection_le_normalizer_left _ _ _)
  have hF := B6.frattini_two hYH
    (le_normalizer_centralizerSection (Subgroup.centralizer ({z} : Set G)) (ch83X T L z)) hS
  exact hF.trans (sup_le hYM (inf_le_right.trans hSM))

end Ch837

end CFSG.Quasithin.H13
