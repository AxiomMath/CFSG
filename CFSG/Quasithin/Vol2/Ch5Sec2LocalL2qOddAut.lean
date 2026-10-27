module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2Z
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Burnside

variable {X : Type} [Group X] [Finite X]

theorem sylow_eq_bot_of_perfect (hX : Group.IsPerfect X) (P : Sylow 2 X)
    (hP : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X)) :
    (P : Subgroup X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := MonoidHom.ker_transferSylow_isComplement' P hP
  have hcomm : ∀ a b : ↥(P : Subgroup X), a * b = b * a := fun a b =>
    Subtype.ext (hP (Subgroup.le_normalizer b.2) a a.2)
  have hker : (MonoidHom.transferSylow P hP).ker = ⊤ := by
    rw [eq_top_iff, ← hX.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  rw [hker] at hc
  have h1 := hc.card_mul_card
  rw [Subgroup.card_top] at h1
  have h2 : Nat.card ↥(P : Subgroup X) = 1 := by
    have hpos : 0 < Nat.card X := Nat.card_pos
    nlinarith [Nat.card_pos (α := ↥(P : Subgroup X))]
  exact Subgroup.eq_bot_of_card_eq _ h2

theorem normalizer_le_centralizer_of_card_two {P : Subgroup X} (hP : Nat.card P = 2) :
    Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
  classical
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  · have hy : n * x * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
    have hy1 : n * x * n⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [this, h]
      group
    have hxy : n * x * n⁻¹ = x := by
      by_contra hne
      have h3 : ({(1 : X), x, n * x * n⁻¹} : Finset X).card ≤ Nat.card P := by
        rw [← Nat.card_eq_finsetCard]
        refine Nat.card_mono (Set.toFinite _) ?_
        intro z hz
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact P.one_mem
        · exact hx
        · exact hy
      rw [hP, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne)] at h3
      · omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hx1, Ne.symm hy1⟩
    calc x * n = n * x * n⁻¹ * n := by rw [hxy]
      _ = n * x := by group

theorem card_eq_four_of_isSylowTwoOf_top {m : ℕ} (hm : Odd m) (hX : Nat.card X = 4 * m)
    {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) : Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP.2.1
  have hidx : ¬ 2 ∣ P.index := by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
  have h1 := Subgroup.card_mul_index P
  rw [hk, hX] at h1
  obtain ⟨m', rfl⟩ := hm
  rw [hk]
  rcases k with _ | _ | _ | k
  · simp at h1
    omega
  · simp at h1
    omega
  · rfl
  · exfalso
    have e : 2 ^ (k + 3) * P.index = 8 * (2 ^ k * P.index) := by ring
    rw [e] at h1
    omega

end Burnside

section PSL2

open CFSG.GorensteinWalter

theorem psl2_mulAut_odd_inner {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : 3 < p)
    (φ : MulAut (PSL2 (ZMod p))) (hφ : Odd (orderOf φ)) :
    ∃ s : PSL2 (ZMod p), φ = MulAut.conj s := by
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hK : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p, 1, Fact.out, hpo, le_rfl, by simp⟩
  have hcard : 3 < Nat.card (ZMod p) := by simpa using hp3
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) (p := p) (f := 1) (by simp) hK
    hcard φ
  have hσ : x.right = 1 := by
    apply RingEquiv.ext
    intro a
    have h := DFunLike.congr_fun (Subsingleton.elim (x.right : ZMod p →+* ZMod p)
      (RingHom.id _)) a
    simpa using h
  have hx' : x = SemidirectProduct.inl x.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [hσ, map_one, mul_one]
  rw [hx', pGammaL2ToMulAutPSL2_inl] at hx
  have hinj := pgl2InnerAutPSL2_injective (ZMod p) hK hcard
  have hodd : Odd (orderOf x.left) := by
    rw [← orderOf_injective _ hinj x.left, hx]
    exact hφ
  have h2 := pgl2_psl2Range_index_eq_two (ZMod p) hK
  have hmem : x.left ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range := by
    obtain ⟨k, hk⟩ := hodd
    have hsq : x.left * x.left ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range :=
      (Subgroup.mul_mem_iff_of_index_two h2).mpr Iff.rfl
    have e : x.left = (x.left * x.left) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf x.left + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hsq _
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, by rw [← hx, ← hs, pgl2InnerAutPSL2_toPGL]⟩

theorem mulAut_odd_inner_of_isPSL {Q : Type} [Group Q] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : 3 < p) (hQ : IsPSL 2 p 1 Q) (α : MulAut Q) (hα : Odd (orderOf α)) :
    ∃ g : Q, α = MulAut.conj g := by
  obtain ⟨e⟩ := Vol2Native.A312L.equiv_psl2_zmod_of_model hQ
  have hφ : Odd (orderOf (MulAut.congr e α)) := by
    rw [MulEquiv.orderOf_eq]
    exact hα
  obtain ⟨s, hs⟩ := psl2_mulAut_odd_inner hp2 hp3 _ hφ
  refine ⟨e.symm s, MulEquiv.ext fun q => ?_⟩
  have h1 := DFunLike.congr_fun hs (e q)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem factL2qOddAutNormalizes_holds :
    FactL2qOddAutNormalizes := by
  intro Q _ _ hQ P R hP hRperf hR1 hRt hPR α hαP hαodd
  obtain ⟨q, hq, hq5, hq8, hQq⟩ := hQ
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq11 : 11 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> revert hq5 hq8 <;> decide
  have hq2 : q ≠ 2 := by omega
  obtain ⟨g, hg⟩ := mulAut_odd_inner_of_isPSL hq2 (by omega) hQq α hαodd
  have hgN : g ∈ Subgroup.normalizer (P : Set Q) :=
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr (hg ▸ hαP)
  obtain ⟨e⟩ := Vol2Native.A312L.equiv_psl2_zmod_of_model hQq
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hK : IsOddPrimePower (Nat.card (ZMod q)) := ⟨q, 1, hq, hqo, le_rfl, by simp⟩
  obtain ⟨m, hm, hQm⟩ : ∃ m : ℕ, Odd m ∧ Nat.card Q = 4 * m := by
    have hc : Nat.card Q = q * (q ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, psl2_card_formula (ZMod q) hK, Nat.card_zmod]
    obtain ⟨c, hc8, hco⟩ : ∃ c : ℕ, q ^ 2 - 1 = 8 * c ∧ Odd c := by
      rcases hq8 with h8 | h8
      · obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 3 := ⟨q / 8, by omega⟩
        refine ⟨8 * a ^ 2 + 6 * a + 1, ?_, ⟨4 * a ^ 2 + 3 * a, by ring⟩⟩
        rw [show (8 * a + 3) ^ 2 = 8 * (8 * a ^ 2 + 6 * a + 1) + 1 by ring, Nat.add_sub_cancel]
      · obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 5 := ⟨q / 8, by omega⟩
        refine ⟨8 * a ^ 2 + 10 * a + 3, ?_, ⟨4 * a ^ 2 + 5 * a + 1, by ring⟩⟩
        rw [show (8 * a + 5) ^ 2 = 8 * (8 * a ^ 2 + 10 * a + 3) + 1 by ring, Nat.add_sub_cancel]
    refine ⟨q * c, hqo.mul hco, ?_⟩
    rw [hc, hc8, show q * (8 * c) = 2 * (4 * (q * c)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  have hP4 : Nat.card P = 4 := card_eq_four_of_isSylowTwoOf_top hm hQm hP
  have hPe : IsSylowTwoOf (P.map e.toMonoidHom) ⊤ :=
    isSylowTwoOf_top_map_of_surjective hP e.toMonoidHom e.surjective
  have hPeidx : ¬ 2 ∣ (P.map e.toMonoidHom).index := by
    have := hPe.2.2
    rwa [show ((P.map e.toMonoidHom).subgroupOf ⊤).index = (P.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _] at this
  have ePS : ↥P ≃* ↥(P.map e.toMonoidHom) := P.equivMapOfInjective e.toMonoidHom e.injective
  have hPK : IsKleinFour ↥P := by
    obtain ⟨m', -, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod q) hK
      (hPe.2.1.toSylow hPeidx)
    have hd : Nat.card (DihedralGroup (2 ^ m')) = 4 := by
      rw [← Nat.card_congr eS.toEquiv]
      show Nat.card ↥(P.map e.toMonoidHom) = 4
      rw [← Nat.card_congr ePS.toEquiv, hP4]
    rw [DihedralGroup.nat_card] at hd
    have hm1 : m' = 1 := by
      have h2 : 2 ^ m' = 2 ^ 1 := by omega
      exact Nat.pow_right_injective le_rfl h2
    subst hm1
    have hD : Monoid.exponent (DihedralGroup (2 ^ 1)) = 2 :=
      (inferInstance : IsKleinFour (DihedralGroup 2)).exponent_two
    exact ⟨hP4, (Monoid.exponent_eq_of_mulEquiv (ePS.trans eS)).trans hD⟩
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, y * x = x * y := by
    intro x hx y hy
    have h1 : (⟨y, hy⟩ * ⟨x, hx⟩ : ↥P) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
      calc (⟨y, hy⟩ * ⟨x, hx⟩ : ↥P) = (⟨y, hy⟩ * ⟨x, hx⟩)⁻¹ := (IsKleinFour.inv_eq_self _).symm
        _ = (⟨x, hx⟩ : ↥P)⁻¹ * (⟨y, hy⟩ : ↥P)⁻¹ := mul_inv_rev _ _
        _ = ⟨x, hx⟩ * ⟨y, hy⟩ := by rw [IsKleinFour.inv_eq_self, IsKleinFour.inv_eq_self]
    exact congrArg Subtype.val h1
  have hCP : Subgroup.centralizer (P : Set Q) = P := by
    have hPeK : IsKleinFour ↥(P.map e.toMonoidHom) := isKleinFour_map_mulEquiv_cross P hPK e
    have h1 := psl2_kleinFour_centralizer_eq_self (ZMod q) hK _ hPeK
    apply le_antisymm
    · intro c hc
      have hec : e c ∈ Subgroup.centralizer
          ((P.map e.toMonoidHom : Subgroup (PSL2 (ZMod q))) : Set (PSL2 (ZMod q))) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨y, hy, rfl⟩
        show e y * e c = e c * e y
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc y hy]
      rw [h1] at hec
      obtain ⟨y, hy, hye⟩ := hec
      have hyc : y = c := e.injective hye
      rwa [← hyc]
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hPcomm x hx y hy
  set N := Subgroup.normalizer (P : Set Q) with hNdef
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hsyl : ∀ M : Subgroup Q, P ≤ M → IsSylowTwoOf P M := fun M hM =>
    ⟨hM, hP.2.1, fun h => hP.2.2 (h.trans (by
      rw [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P]
      exact Subgroup.relIndex_dvd_index_of_le hM))⟩
  have hN12 : Nat.card N ∣ 12 := by
    have hPn : (P.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr le_rfl
    let φ : ↥N →* MulAut ↥(P.subgroupOf N) := MulAut.conjNormal
    have ePN : ↥(P.subgroupOf N) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPN
    have hker : Nat.card φ.ker = 4 := by
      have h1 : φ.ker = P.subgroupOf N := by
        ext n
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro hn
          have hnC : (n : Q) ∈ Subgroup.centralizer (P : Set Q) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            have h2 := DFunLike.congr_fun hn ⟨⟨y, hPN hy⟩, hy⟩
            have h3 : (n : Q) * y * (n : Q)⁻¹ = y := by
              have h4 := congrArg (fun z : ↥(P.subgroupOf N) => ((z : ↥N) : Q)) h2
              simpa [φ, MulAut.conjNormal_apply] using h4
            calc y * n = ((n : Q) * y * (n : Q)⁻¹) * n := by rw [h3]
              _ = n * y := by group
          rw [hCP] at hnC
          exact hnC
        · intro hn
          refine MulEquiv.ext fun z => Subtype.ext (Subtype.ext ?_)
          have hz : ((z : ↥N) : Q) ∈ P := z.2
          simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
            Subgroup.coe_inv]
          rw [← hPcomm _ hn _ hz]
          group
      rw [h1, Nat.card_congr ePN.toEquiv, hP4]
    have hrange : Nat.card φ.range ∣ 6 := by
      have hPNK : IsKleinFour ↥(P.subgroupOf N) :=
        ⟨by rw [Nat.card_congr ePN.toEquiv, hP4],
          (Monoid.exponent_eq_of_mulEquiv ePN).trans hPK.exponent_two⟩
      obtain ⟨eS3⟩ := GorensteinWalter.gw_prop9_aut_kleinFour_is_S3 hPNK
      have h6 : Nat.card (MulAut ↥(P.subgroupOf N)) = 6 := by
        rw [Nat.card_congr eS3.toEquiv, Nat.card_perm, Nat.card_fin]
        rfl
      rw [← h6]
      exact Subgroup.card_subgroup_dvd_card _
    have hNcard : Nat.card N = 4 * Nat.card φ.range := by
      have h1 := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker, hker] at h1
      exact h1.symm
    have hodd : ¬ 2 ∣ Nat.card φ.range := by
      have h1 := Subgroup.card_mul_index (P.subgroupOf N)
      rw [Nat.card_congr ePN.toEquiv, hP4, hNcard] at h1
      have h2 : (P.subgroupOf N).index = Nat.card φ.range := by omega
      rw [← h2]
      exact (hsyl N hPN).2.2
    have hle := Nat.le_of_dvd (by norm_num) hrange
    rw [hNcard]
    interval_cases h : Nat.card φ.range <;> omega
  have hRN : R ⊔ P ≤ Subgroup.normalizer (R : Set Q) := sup_le Subgroup.le_normalizer hPR
  have hSsyl : IsSylowTwoOf (P ⊓ R) R :=
    A4.isSylowTwoOf_inf_normal (hsyl (R ⊔ P) le_sup_right) le_sup_left hRN
  have hRperf' : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hRperf
  have hsylR : ∀ S : Subgroup Q, IsSylowTwoOf S R → ∃ S' : Sylow 2 ↥R,
      ((S' : Subgroup ↥R) : Set ↥R) = {x : ↥R | (x : Q) ∈ S} := by
    intro S hS
    have h2 : IsPGroup 2 (S.subgroupOf R) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact ⟨h2.toSylow hS.2.2, by ext x; rfl⟩
  have hPR' : P ≤ R := by
    by_contra hnot
    have hlt : P ⊓ R < P := lt_of_le_of_ne inf_le_left fun h => hnot (h ▸ inf_le_right)
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ R ≤ P)
    have h2 := Subgroup.card_lt_of_lt hlt
    rw [hP4] at h1 h2
    have h3 : 0 < Nat.card ↥(P ⊓ R) := Nat.card_pos
    have hidx := Subgroup.card_mul_index ((P ⊓ R).subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at hidx
    interval_cases hc : Nat.card ↥(P ⊓ R)
    ·
      have hRodd : Odd (Nat.card R) := by
        rw [← hidx, one_mul]
        exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSsyl.2.2)
      have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
      have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
      exact Group.IsPerfect.not_isSolvable ↥R hsolv
    ·
      obtain ⟨S', hS'⟩ := hsylR _ hSsyl
      have hS'2 : Nat.card ↥(S' : Subgroup ↥R) = 2 := by
        have e1 : (S' : Subgroup ↥R) = (P ⊓ R).subgroupOf R := SetLike.coe_injective hS'
        rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hc]
      have h4 := sylow_eq_bot_of_perfect hRperf' S'
        (normalizer_le_centralizer_of_card_two hS'2)
      rw [h4, Subgroup.card_bot] at hS'2
      exact absurd hS'2 (by norm_num)
    · omega
  have hNR : P < R ⊓ N := by
    refine lt_of_le_of_ne (le_inf hPR' hPN) fun heq => ?_
    obtain ⟨S', hS'⟩ := hsylR P (hsyl R hPR')
    have hnorm : Subgroup.normalizer ((S' : Subgroup ↥R) : Set ↥R) ≤
        Subgroup.centralizer ((S' : Subgroup ↥R) : Set ↥R) := by
      intro x hx
      have hxN : (x : Q) ∈ N := by
        refine mem_normalizer_of_conj_mem' fun y hy => ?_
        have h1 : (⟨y, hPR' hy⟩ : ↥R) ∈ ((S' : Subgroup ↥R) : Set ↥R) := by
          rw [hS']
          exact hy
        have h2 := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hPR' hy⟩).mp h1
        have h3 : ((x * ⟨y, hPR' hy⟩ * x⁻¹ : ↥R) : Q) ∈ P := by
          have : (x * ⟨y, hPR' hy⟩ * x⁻¹ : ↥R) ∈ ((S' : Subgroup ↥R) : Set ↥R) := h2
          rw [hS'] at this
          exact this
        simpa using h3
      have hxP : (x : Q) ∈ P := by
        rw [heq]
        exact ⟨x.2, hxN⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : (y : Q) ∈ P := by
        have : y ∈ ((S' : Subgroup ↥R) : Set ↥R) := hy
        rw [hS'] at this
        exact this
      exact Subtype.ext (hPcomm _ hxP _ hyP)
    have h4 := sylow_eq_bot_of_perfect hRperf' S' hnorm
    have h5 : Nat.card ↥(S' : Subgroup ↥R) = 4 := by
      have e1 : (S' : Subgroup ↥R) = P.subgroupOf R := SetLike.coe_injective hS'
      rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR').toEquiv, hP4]
    rw [h4, Subgroup.card_bot] at h5
    exact absurd h5 (by norm_num)
  have h12 : Nat.card ↥(R ⊓ N) = 12 := by
    have h1 := (Subgroup.card_dvd_of_le (inf_le_right : R ⊓ N ≤ N)).trans hN12
    have h2 := Subgroup.card_dvd_of_le (le_inf hPR' hPN : P ≤ R ⊓ N)
    have h3 := Subgroup.card_lt_of_lt hNR
    rw [hP4] at h2 h3
    have hle := Nat.le_of_dvd (by norm_num) h1
    interval_cases hc : Nat.card ↥(R ⊓ N) <;> omega
  have hNeq : R ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by
    rw [h12]
    exact Nat.le_of_dvd (by norm_num) hN12)
  have hgR : g ∈ R := by
    rw [← hNeq] at hgN
    exact hgN.1
  rw [hg]
  exact CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hgR)

end PSL2

end CFSG.Quasithin.H13
