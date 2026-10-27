module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch10SecB3Odd
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch11SecB21Odd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def TrivOnV (T L I H : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) →
    ∀ A : Subgroup G, A ≤ cenL0 T L I → A ≤ H → IsPGroup p A → ⁅fsuVM T L I, A⁆ = ⊥

theorem fsuV_facts (h3228 : TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) :
    fsuV T I ≤ quasithinOmegaOneCenter (pCoreOf 2 (fsuL0 T L ⊔ T)) ∧
      fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      fsuV T I = ⁅fsuV T I, fsuL0 T L⁆ ∧ fsuV T I ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVX, ⟨hn, -, -⟩, hO⟩ := h3228 G T L I hyp.fsu
  have hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVX).mp hn
  have hel := SecA.isElemAbelian_fsuVM hyp
  have hV2 : ∀ v ∈ fsuV T I, v ^ 2 = 1 := fun v hv => hel.2 v (SecA.fsuV_le_fsuVM T L I hv)
  have hVp : IsPGroup 2 (fsuV T I) := fun v => ⟨1, Subtype.ext (by simpa using hV2 v v.2)⟩
  have hVO : fsuV T I ≤ pCoreOf 2 (fsuL0 T L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVX hN hVp
  obtain ⟨-, hI1, -, hIc, -⟩ := hyp.fsu.irrPlus
  refine ⟨fun v hv => Subgroup.subset_closure
    ⟨⟨hVO hv, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩, hV2 v hv⟩, hN, ?_, ?_⟩
  · rw [hO] at hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
  · refine le_antisymm (conjClosure_le fun t ht z hz => ?_)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hN))
    have hz' : z ∈ ⁅I, fsuL0 T L⁆ := by rw [hIc]; exact hz
    have h1 : I.map (MulAut.conj t).toMonoidHom ≤ fsuV T I := by
      rintro _ ⟨i, hi, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure ht hi
    have h2 : (fsuL0 T L).map (MulAut.conj t).toMonoidHom ≤ fsuL0 T L := by
      rintro _ ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L ht) l).mp hl
    have hm := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hz'
    rw [Subgroup.map_commutator] at hm
    simpa [MulAut.conj_apply] using Subgroup.commutator_mono h1 h2 hm
  · intro h
    apply hI1
    rw [eq_bot_iff]
    exact (le_conjClosure I T).trans h.le

theorem commutator_fsuL0_le_of_le_cenL0
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {A : Subgroup G}
    (hA : A ≤ cenL0 T L I) : ⁅fsuL0 T L, A⁆ ≤ pCoreOf 2 (fsuL0 T L) := by
  rw [Subgroup.commutator_le]
  intro l hl a ha
  obtain ⟨haM, hac⟩ := mem_cenL0.mp (hA ha)
  refine SecA.fsuL0_inf_centralizer_le h37 h38 hyp ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h1 : a * l⁻¹ * a⁻¹ ∈ fsuL0 T L :=
      (Subgroup.mem_normalizer_iff.mp haM l⁻¹).mp (Subgroup.inv_mem _ hl)
    have := Subgroup.mul_mem _ hl h1
    simpa [mul_assoc] using this
  · have e : ⁅l, a⁆ = (a * l * a⁻¹ * l⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ (hac l hl)

theorem hall_faithful_of
    (hDHB : Ch11.SecB.DerivedHallBorel) (h4413 : TmpL6_4_4_13)
    (h443 : Stmt4_4_3') (h3228 : TmpL6_3_2_2_eight) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3)
    (hyp : Hyp10 G T L I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn : 1 < E1.nParam H)
    (htriv : TrivOnV T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {b : G} (hbB : b ∈ B)
    (hb : ∀ l ∈ fsuL0 T L, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := fsuM T L with hMdef
  by_contra hb1
  have hbC : b ∈ cenL0 T L I := mem_cenL0.mpr ⟨(hB.1 hbB).2, hb⟩
  have hbo : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hbo
  have hbodd : Odd (orderOf b) := hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hbB)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr hpd)
  have : Fact p.Prime := ⟨hp⟩
  set y := b ^ (orderOf b / p) with hydef
  have hyo : orderOf y = p := orderOf_pow_orderOf_div (orderOf_pos b).ne' hpd
  have hyC : y ∈ cenL0 T L I := Subgroup.pow_mem _ hbC _
  have hyX : y ∈ H ⊓ M := Subgroup.pow_mem _ (hB.1 hbB) _
  have hy1 : y ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hyo, h, orderOf_one])
  have hpL := not_dvd_of_mem_cenL0 h37 h38 h1013 hyp hp hp2 hyC hyo
  have hTM : T ≤ M := SecA.le_fsuM T L
  obtain ⟨B', hB', hB'ab, hTB'⟩ := hDHB G T M H hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow ⟨fsuM_isMaxTwoLocal h331 hyp, hTM⟩ (normalizer_T_le h331 hyp) hH hn
  have hyP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨x, hx, hle⟩ :=
    Ch11.SecB.exists_conj_le_hall hp2 hB' (Subgroup.zpowers_le.mpr hyX) hyP
  obtain ⟨z, hzB', hzy⟩ := hle (Subgroup.mem_zpowers y)
  have hxz : x * z * x⁻¹ = y := by simpa [MulAut.conj_apply] using hzy
  have hzC : z ∈ cenL0 T L I :=
    (Subgroup.mem_normalizer_iff.mp (fsuM_le_normalizer_cenL0 T L I hx.2) z).mpr
      (by rw [hxz]; exact hyC)
  have hzp : z ^ p = 1 := by
    have h1 : (x * z * x⁻¹) ^ p = 1 := by rw [hxz, ← hyo, pow_orderOf_eq_one]
    rw [conj_pow] at h1
    have h2 : z ^ p = x⁻¹ * (x * z ^ p * x⁻¹) * x := by group
    rw [h2, h1, mul_one, inv_mul_cancel]
  have hz1 : z ≠ 1 := fun h => hy1 (by rw [← hxz, h, mul_one, mul_inv_cancel])
  set C := B' ⊓ cenL0 T L I with hCdef
  have hCab : ∀ a ∈ C, ∀ c ∈ C, a * c = c * a := fun a ha c hc => hB'ab a ha.1 c hc.1
  set A := Ch11.SecB.torsionSub C hCab p with hAdef
  have hzA : z ∈ A := Ch11.SecB.mem_torsionSub.mpr ⟨⟨hzB', hzC⟩, hzp⟩
  have hA1 : A ≠ ⊥ := fun h => hz1 (by rw [h] at hzA; exact hzA)
  have hAC : A ≤ C := fun w hw => (Ch11.SecB.mem_torsionSub.mp hw).1
  have hAB' : A ≤ B' := hAC.trans inf_le_left
  have hAcen : A ≤ cenL0 T L I := hAC.trans inf_le_right
  have hAel : IsElemAbelian p A := Ch11.SecB.isElemAbelian_torsionSub C hCab p
  have hAX : A ≤ H ⊓ M := hAB'.trans hB'.1
  have hAp : IsPGroup p A := fun w =>
    ⟨1, Subtype.ext (by simpa using (Ch11.SecB.mem_torsionSub.mp w.2).2)⟩
  have hTX : T ≤ H ⊓ M := le_inf hH.1.1 hTM
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTX
  have hNA : T ⊓ Subgroup.normalizer (B' : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht w hw
    obtain ⟨⟨hwB, hwC⟩, hwp⟩ := Ch11.SecB.mem_torsionSub.mp hw
    refine Ch11.SecB.mem_torsionSub.mpr ⟨⟨(Subgroup.mem_normalizer_iff.mp ht.2 w).mp hwB, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (fsuM_le_normalizer_cenL0 T L I (hTM ht.1)) w).mp hwC
    · rw [conj_pow, hwp, mul_one, mul_inv_cancel]
  have hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) :=
    Ch11.SecB.mul_comm_sylow_of_normalizes
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))
      (B6.pCoreOf_two_le_of_isSylowTwoOf hTS) hTX hAX hTB' hNA
  have h1 := (((h4413 G H T (H ⊓ M) hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hH.1.2 hn
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1)
    (isUniqueMaxOver_of_isHStar h331 hyp hH)).2 B' hB').1 p A hp hAB' hAel hAT).2
  obtain ⟨hV1, hV2, hV3, hV4⟩ := fsuV_facts h3228 hyp
  have hVA : ⁅fsuV T I, A⁆ = ⊥ := by
    have h := htriv p hp hp2 hpL A hAcen (hAX.trans inf_le_left) hAp
    rw [eq_bot_iff] at h ⊢
    exact (Subgroup.commutator_mono (SecA.fsuV_le_fsuVM T L I) le_rfl).trans h
  have hAodd : Odd (Nat.card A) := hB'.2.1.of_dvd_nat (Subgroup.card_dvd_of_le hAB')
  rcases h443 G T M L A T (fsuV T I) hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow (fsuM_isMaxTwoLocal h331 hyp) hTM hyp.fsu.maximal hyp.fsu.faithful
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)) hyp.fsu.quasisimple
      (hAX.trans inf_le_right) hA1 hAel.1 hAodd
      (commutator_fsuL0_le_of_le_cenL0 h37 h38 hyp hAcen) le_rfl hAT rfl hV1 hV2 hV3 hV4
      hVA with hN | hN
  · exact h1 fun w hw => ⟨hw.1, hN hw.2⟩
  · exact hyp.not_normal (hTM.trans hN.1)

end CFSG.Quasithin.Vol2.Ch10.SecB
