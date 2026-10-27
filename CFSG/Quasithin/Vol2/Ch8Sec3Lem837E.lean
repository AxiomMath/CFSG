module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837D
public import CFSG.Quasithin.Vol2.Ch10SecB4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjByElt_eq_conjugate (t : G) (K : Subgroup G) :
    conjByElt t K = CFSG.conjugate K t⁻¹ := by
  rw [CFSG.conjugate, inv_inv]
  rfl

theorem le_normalizer_ch83X {T L : Subgroup G} {z : G}
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) :
    T ≤ Subgroup.normalizer (ch83X T L z : Set G) := fun t ht => by
  have h1 : t ∈ Subgroup.normalizer
      ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    E1.mem_normalizer_inf (le_normalizer_conjClosure L T ht) (Subgroup.le_normalizer (hTz ht))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
  rw [ch83X, E1.map_twoResidual, h1]

theorem xi_data
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    ∃ _ : OTwoQuot (ch83X T L z ⊔ T) ≃* S152N.W3,
      oTwoUpper (ch83X T L z ⊔ T) = ch83X T L z ∧ IsXi T (ch83X T L z) ∧
      (pCoreOf 2 (ch83X T L z)).relIndex (ch83X T L z) = 9 ∧
      ∃ P : Subgroup G, IsSylowIn 3 P (ch83X T L z) ∧ Nat.card P = 9 ∧
        ¬ EmptyFaithfulMultiple.AutCyclic T P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨φ⟩ := nonempty_oTwoQuot_equiv h37 h38 h326 hyp hV hrow hN hz1 hzV
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hTX := le_normalizer_ch83X (L := L) hTz
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  set X := ch83X T L z with hXdef
  have hO2 : oTwoUpper (X ⊔ T) = X := by
    rw [← F6.twoResidual_eq_oTwoUpper]
    apply le_antisymm
    · exact twoResidual_le_of_isTwoQuotient le_sup_left (sup_le Subgroup.le_normalizer hTX)
        (B6.isTwoQuotient_of_sup_eq hT2 (sup_le Subgroup.le_normalizer hTX) (sup_comm T _))
    · calc X = twoResidual X :=
            (twoResidual_twoResidual (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))).symm
        _ ≤ twoResidual (X ⊔ T) := F6.twoResidual_mono le_sup_left
  have hsyl : IsSylowTwoOf T (X ⊔ T) := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
  have hTop : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    intro h
    have hzO := zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) (sup_le hXGz hTz)
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hXi := Der6D.xi_of_iso hsyl hTop φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  rw [hO2] at hXi hrel
  have h3 : 3 ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three X
  have hPc : Nat.card P = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP, hrel]
  have hXi' : IsXi T (oTwoUpper (X ⊔ T)) := by rw [hO2]; exact hXi
  have hP' : IsSylowIn 3 P (oTwoUpper (X ⊔ T)) := by rw [hO2]; exact hP
  exact ⟨φ, hO2, hXi, hrel, P, hP, hPc, Der6D.not_autCyclic hyp.fsu.sylow hsyl φ hXi' hP' hPc⟩

omit [Finite G] in
theorem commutator_sup_eq {K K' : Subgroup G} (hK : ⁅K, K⁆ = K) (hK' : ⁅K', K'⁆ = K') :
    ⁅K ⊔ K', K ⊔ K'⁆ = K ⊔ K' := by
  refine le_antisymm ((Subgroup.commutator_le).mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (K ⊔ K').mul_mem ((K ⊔ K').mul_mem ((K ⊔ K').mul_mem ha hb) ((K ⊔ K').inv_mem ha))
      ((K ⊔ K').inv_mem hb)
  · calc K = ⁅K, K⁆ := hK.symm
      _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc K' = ⁅K', K'⁆ := hK'.symm
      _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem isSolvable_of_oTwoQuot_equiv {H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3) :
    Group.IsSolvable ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable S152N.W3 := CFSG.Quasithin.H.L3Wr.isSolvable_W3
  have h2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H) := by
    exact CFSG.pCore_isPGroup
  have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥H) := h2.isNilpotent
  refine Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥H).subtype
    (φ.toMonoidHom.comp (QuotientGroup.mk' _)) fun x hx => ?_
  have hx1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) x) = 1 :=
    φ.injective ((hx : φ.toMonoidHom (QuotientGroup.mk' _ x) = 1).trans (map_one φ).symm)
  exact ⟨⟨x, (QuotientGroup.eq_one_iff x).mp hx1⟩, rfl⟩

theorem false_of_l2_four_of_not_hstar
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (h836 : Stmt8_3_6) (hKG : KGRankOneOvergroups)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    (φ : OTwoQuot (ch83X T L z ⊔ T) ≃* S152N.W3)
    (hrel : (pCoreOf 2 (ch83X T L z)).relIndex (ch83X T L z) = 9)
    {K : Subgroup G} {t : G} (hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)))
    (hKz : ch83Kz T L z = K ⊔ conjByElt t K) (hTK : conjClosure K T = K ⊔ conjByElt t K)
    {n : ℕ} (hn4 : 4 ≤ n) (hmod : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K))
    (hns : ¬ IsHStar T (fsuM T L) (ch83Kz T L z ⊔ T)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  set Gz := Subgroup.centralizer ({z} : Set G) with hGzdef
  set X := ch83X T L z with hXdef
  set Kz := ch83Kz T L z with hKzdef
  set M := fsuM T L with hMdef
  set H₀ := Kz ⊔ T with hH₀def
  have hTM : T ≤ M := le_normalizer_conjClosure L T
  have hXGz : X ≤ Gz := (twoResidual_le _).trans inf_le_right
  have hXKz : X ≤ Kz := le_conjClosure _ _
  have hKzGz : Kz ≤ Gz := conjClosure_le fun h hh x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hH₀Gz : H₀ ≤ Gz := sup_le hKzGz hTz
  have hTX := le_normalizer_ch83X (L := L) hTz
  have hTK₀ : T ≤ Subgroup.normalizer (Kz : Set G) :=
    hTz.trans (le_normalizer_conjClosure _ _)
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 H₀ :=
    zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) hH₀Gz
  have hPH₀ : pCoreOf 2 H₀ ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hSQ : IsSQTKIn H₀ :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPH₀
  have hTH₀ : IsSylowTwoOf T H₀ := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
  have hKH₀ : K ≤ H₀ := by
    rw [hH₀def, hKz]
    exact le_sup_left.trans le_sup_left
  have hKcH₀ : K ∈ cComp H₀ := cComp_mem_of_le hKc hKH₀ hH₀Gz
  have hcl : conjClosure K T ⊔ T = H₀ := by rw [hTK, hH₀def, hKz]
  obtain ⟨hBsolv, hover⟩ := hKG G H₀ T K hSQ hPH₀ hTH₀ hKcH₀ hcl ⟨n, Or.inl ⟨by omega, hmod⟩⟩
  rw [hTK, ← hKz] at hBsolv hover
  set B := H₀ ⊓ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) with hBdef
  have hXTB : X ⊔ T ≤ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) := by
    rcases hover (X ⊔ T) le_sup_right (sup_le (hXKz.trans le_sup_left) le_sup_right) with h | h
    · exfalso
      have : Group.IsSolvable ↥(X ⊔ T) := isSolvable_of_oTwoQuot_equiv φ
      have hKXT : K ≤ X ⊔ T := h ▸ hKH₀
      have : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKXT)
      exact ne_bot_of_mem_cComp hKc (eq_bot_of_perfect_of_isSolvable (perfect_of_mem_cComp hKc))
    · exact h
  have hTKS : T ⊓ Kz ≤ ch83S T L z :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hXTB
      (hyp.fsu.sylow.1.to_le inf_le_left)
  set B₀ := Kz ⊓ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) with hB₀def
  set S := ch83S T L z with hSdef
  have hST : S ≤ T := pCoreOf_le_of_isSylowIn (isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right)
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hTK₀ hs⟩
  have hTB₀ : T ≤ Subgroup.normalizer (B₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK₀ hs, Subgroup.le_normalizer (hTN hs)⟩
  have hSB₀ : S ≤ Subgroup.normalizer (B₀ : Set G) := hST.trans hTB₀
  set H₁ := B₀ ⊔ S with hH₁def
  have hH₁B : H₁ ≤ B := sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    (le_inf (hST.trans le_sup_right) (hST.trans hTN))
  have : Group.IsSolvable ↥B := hBsolv
  have : Group.IsSolvable ↥H₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hH₁B)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun s hs =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right hs)
  have hTH₁ : T ≤ Subgroup.normalizer (H₁ : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTB₀ hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTS hs)]
  have hS₁ : IsSylowTwoOf S H₁ := by
    have hT' : IsSylowTwoOf T (H₁ ⊔ T) := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
    have hinf := B6.isSylowTwoOf_inf_normal hT' le_sup_left (sup_le Subgroup.le_normalizer hTH₁)
    have heq : T ⊓ H₁ = S := by
      refine le_antisymm (fun x hx => ?_) (le_inf hST le_sup_right)
      have hx2 : x ∈ ((B₀ ⊔ S : Subgroup G) : Set G) := hx.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left B₀ S hSB₀] at hx2
      obtain ⟨b, hb, c, hc', rfl⟩ := Set.mem_mul.mp hx2
      have hbT : b ∈ T := by
        have := T.mul_mem hx.1 (T.inv_mem (hST hc'))
        rwa [mul_inv_cancel_right] at this
      exact S.mul_mem (hTKS ⟨hbT, hb.1⟩) hc'
    rw [← heq]
    exact hinf
  have hzS : z ∈ S := zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) (sup_le hXGz hTz)
    (Subgroup.mem_zpowers z)
  have hn₁ : E1.nParam H₁ = 1 := by
    have hn1 : E1.nParam H₁ ≤ 1 := E1.solvable_nParam_le_one inferInstance
    have hn0 : E1.nParam H₁ ≠ 0 := by
      intro h
      have hodd := E1.odd_of_nParam_le_zero (le_of_eq h)
      have h2 : 2 ∣ Nat.card ↥H₁ := by
        have := Subgroup.orderOf_dvd_natCard H₁ (Subgroup.mem_sup_right hzS)
        rwa [hz2] at this
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hn1)
    rw [← hk] at hn1 hn0 ⊢
    have hk1 : k ≤ 1 := by exact_mod_cast hn1
    have hk0 : k ≠ 0 := by exact_mod_cast hn0
    have : k = 1 := by omega
    rw [this]
    rfl
  have hH₁M : H₁ ≤ M := h836 G T L I hyp h731 hc hrow z hz2 hzV H₁ hS₁ hn₁
  have hBM : B ≤ M := by
    intro x hx
    have hx1 : x ∈ ((Kz ⊔ T : Subgroup G) : Set G) := hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kz T hTK₀] at hx1
    obtain ⟨k, hk, u, hu, rfl⟩ := Set.mem_mul.mp hx1
    have hkN : k ∈ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hx.2 (Subgroup.inv_mem _ (hTN hu))
      rwa [mul_inv_cancel_right] at this
    exact M.mul_mem (hH₁M (Subgroup.mem_sup_left ⟨hk, hkN⟩)) (hTM hu)
  have hH₀M : H₀ ≤ M := by
    by_contra hne
    exact hns ⟨⟨le_sup_right, hPH₀⟩, hne, fun Y hY hYH₀ hYM =>
      (hover Y hY.1 hYH₀).resolve_right fun hYN => hYM ((le_inf hYH₀ hYN).trans hBM)⟩
  have hperf : ⁅Kz, Kz⁆ = Kz := by
    have hK' : ⁅conjByElt t K, conjByElt t K⁆ = conjByElt t K := by
      unfold conjByElt
      rw [← Subgroup.map_commutator, perfect_of_mem_cComp hKc]
    rw [hKz]
    exact commutator_sup_eq (perfect_of_mem_cComp hKc) hK'
  have hKzC := le_centralizer_of_perfect h326 hyp hV hrow hz1 hzV (le_sup_left.trans hH₀M) hKzGz
    hperf
  exact not_ch83X_le_centralizer h37 h38 h326 hyp hrow hrel (hXKz.trans hKzC)


theorem false_of_l2_four
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (h734 : Stmt7_3_4) (h836 : Stmt8_3_6) (hKG : KGRankOneOvergroups) (hL2N : Claim837L2N)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    (φ : OTwoQuot (ch83X T L z ⊔ T) ≃* S152N.W3)
    (hrel : (pCoreOf 2 (ch83X T L z)).relIndex (ch83X T L z) = 9)
    {K : Subgroup G} {t : G} (htT : t ∈ T) (htN : t ∉ Subgroup.normalizer (K : Set G))
    (hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)))
    (hKz : ch83Kz T L z = K ⊔ conjByElt t K) (hTK : conjClosure K T = K ⊔ conjByElt t K)
    {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (hmod : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  refine false_of_l2_four_of_not_hstar h37 h38 h326 h836 hKG hyp h731 hrow hV hN hz2 hzV φ hrel
    hKc hKz hTK hn4 hmod fun hstar => ?_
  obtain ⟨h734a, -, -, hn721⟩ := h734 G T L I hyp h731 hV
  have hn2 : nPrime (autI hV ⊤) = 2 := (hn721 hc).2.2.2.2.2.2.2.2 hrow
  have hle : E1.nParam (ch83Kz T L z ⊔ T) ≤ 2 := by
    have h := (h734a _ hstar).2
    rw [hn2] at h
    exact_mod_cast h
  have hKz' : ch83Kz T L z = K ⊔ CFSG.conjugate K t⁻¹ :=
    hKz.trans (by rw [conjByElt_eq_conjugate])
  have htN' : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
    htN (by simpa using Subgroup.inv_mem _ h)
  have h3 := hL2N G T L I hyp h731 hc hrow z hz2 hzV K t⁻¹ n (T.inv_mem htT) htN' hKc hKz'
    hn hn4 hmod
  exact absurd (h3.trans hle) (by norm_num)

end Ch837

end CFSG.Quasithin.H13
