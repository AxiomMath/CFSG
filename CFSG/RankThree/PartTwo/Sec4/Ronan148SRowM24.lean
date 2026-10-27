module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SGood
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowRuJ4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429

section E9

variable {S : Type} [Group S] [Finite S]

theorem isElemAbelian_zpowers_of_pow {s : S} (hs : s ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers s) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact ((Commute.refl s).zpow_zpow i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs, one_zpow]

theorem e9_of_commute {s f : S} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hf3 : f ^ 3 = 1)
    (hsf : s * f = f * s) (hfs : f ∉ Subgroup.zpowers s) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers s ⊔ Subgroup.zpowers f) ∧
      Nat.card ↥(Subgroup.zpowers s ⊔ Subgroup.zpowers f) = 9 := by
  have hf1 : f ≠ 1 := fun h => hfs (h ▸ Subgroup.one_mem _)
  have hcomm : ∀ x ∈ Subgroup.zpowers s, ∀ y ∈ Subgroup.zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute s f from hsf) i j).eq
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hof : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  have hinf : Subgroup.zpowers s ⊓ Subgroup.zpowers f = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxs, hxf⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hfs
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers f := Subgroup.zpowers_le.mpr hxf
    have hcard : Nat.card (Subgroup.zpowers f) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hof]
      have hdvd : orderOf x ∣ 3 := hof ▸ orderOf_dvd_of_mem_zpowers hxf
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · omega
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have hfx : f ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers f
    exact (Subgroup.zpowers_le.mpr hxs) hfx
  refine ⟨Sec13.isElemAbelian_sup (isElemAbelian_zpowers_of_pow hs3)
    (isElemAbelian_zpowers_of_pow hf3) hcomm, ?_⟩
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hos, hof] at h
  exact h

theorem mem_normalizer_of_map_le {F : Subgroup S} {n : S}
    (h : F.map (MulAut.conj n).toMonoidHom ≤ F) : n ∈ Subgroup.normalizer (F : Set S) := by
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  have heq : F.map (MulAut.conj n).toMonoidHom = F :=
    Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective hinj])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj n).toMonoidHom x ∈ F.map (MulAut.conj n).toMonoidHom := ⟨x, hx, rfl⟩
    rw [heq] at this
    simpa using this
  · intro hx
    have hx' : (MulAut.conj n).toMonoidHom x ∈ F.map (MulAut.conj n).toMonoidHom := by
      rw [heq]
      simpa using hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [hinj hyx] at hy

theorem move_of_conj {s f n : S} (hfs : f ∉ Subgroup.zpowers s) (h1 : n * s * n⁻¹ = f)
    (h2 : n * f * n⁻¹ = s * f) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers s ⊔ Subgroup.zpowers f : Subgroup S) : Set S) ∧
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  refine ⟨mem_normalizer_of_map_le ?_, fun hn => hfs ?_⟩
  · rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show n * s * n⁻¹ ∈ _
      rw [h1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
    · rw [Subgroup.zpowers_le]
      show n * f * n⁻¹ ∈ _
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))
  · rw [← h1]
    exact (Subgroup.mem_normalizer_iff.mp hn s).mp (Subgroup.mem_zpowers s)

end E9

section SurvEAt

variable {S S' T : Type} [Group S] [Group S'] [Group T]

@[expose] def SurvEAt (s : S) (T : Type) [Group T] : Prop :=
  ∀ K : Subgroup S, CC425 s K →
    IsExtOf K T (Multiplicative (ZMod 3)) ∧
      ∃ F : Subgroup S, F ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
        ∃ n ∈ Subgroup.normalizer (F : Set S),
          n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

theorem survE_of_at (h : ∀ s : S, SurvEAt s T) : SurvE S T := fun s K hK => h s K hK

theorem SurvEAt.of_mulEquiv [Finite S] (e : S ≃* S') {s : S} (h : SurvEAt (e s) T) :
    SurvEAt s T := by
  intro K hK
  obtain ⟨hext, F, hFK, hF, hF9, n, hn, hns⟩ := h (K.map (e : S →* S')) (hK.map e)
  refine ⟨isExtOf_congr (K.equivMapOfInjective _ e.injective).symm hext,
    F.map e.symm.toMonoidHom, ?_, isElemAbelian_map _ hF,
    by rw [Subgroup.card_map_of_injective e.symm.injective, hF9], e.symm n, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hzy⟩ := hFK hy
    rw [← hzy]
    simpa using hz
  · rw [← Subgroup.map_equiv_normalizer_eq F e.symm]
    exact ⟨n, hn, rfl⟩
  · intro hn'
    apply hns
    have hZ : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers (e s) :=
      MonoidHom.map_zpowers _ s
    rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨e.symm n, hn', by simp⟩

theorem SurvE.of_mulEquiv [Finite S] (e : S ≃* S') (h : SurvE S' T) : SurvE S T :=
  survE_of_at fun s => SurvEAt.of_mulEquiv e (fun K hK => h (e s) K hK)

end SurvEAt

theorem not_mem_zpowers_of_ne {S : Type} [Group S] {s f : S} (hs3 : s ^ 3 = 1) (h1 : f ≠ 1)
    (h2 : f ≠ s) (h3 : f ≠ s⁻¹) : f ∉ Subgroup.zpowers s := by
  intro hf
  by_cases hs1 : s = 1
  · subst hs1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hf
    exact h1 hf
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
  have hk : s ^ k = s ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hos]
    norm_num
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> rw [hk, h] at h1 h2 h3
  · exact h1 (zpow_zero s)
  · exact h2 (zpow_one s)
  · apply h3
    rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub, zpow_one,
      show s ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact hs3, one_mul]

@[expose] def m24N0W : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2,
   -1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, -2, 1, -2, 1, -2,
   1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2]

@[expose] def m24N0 : Blueprint.NativeSporadic.M24 := RonanK432.m24ClassWord m24N0W

set_option maxRecDepth 200000 in
theorem m24N0_facts :
    (m24N0 * RonanK432.m24RA * m24N0⁻¹) * RonanK432.m24RA =
        RonanK432.m24RA * (m24N0 * RonanK432.m24RA * m24N0⁻¹) ∧
      m24N0 * RonanK432.m24RA * m24N0⁻¹ ≠ 1 ∧
      m24N0 * RonanK432.m24RA * m24N0⁻¹ ≠ RonanK432.m24RA ∧
      m24N0 * RonanK432.m24RA * m24N0⁻¹ ≠ RonanK432.m24RA⁻¹ ∧
      m24N0 * (m24N0 * RonanK432.m24RA * m24N0⁻¹) * m24N0⁻¹ =
        RonanK432.m24RA * (m24N0 * RonanK432.m24RA * m24N0⁻¹) := by
  decide +kernel

section M24

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.Census219
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore (map_subtype_centralizer)
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (tp_eq_of_rep)
open CFSG.Sporadic.SmallOddCore (tp)


theorem m24y_eq : m24y = RonanK432.m24RA := Subtype.ext (tp_eq_of_rep (rep_wT xW))

theorem survEAt_m24y : SurvEAt m24y (alternatingGroup (Fin 6)) := by
  intro K hK
  obtain ⟨-, ⟨e'⟩, hQ⟩ := m24_layer
  have hC : Nat.card ↥(Subgroup.centralizer ({m24y} : Set Blueprint.NativeSporadic.M24)) = 1080 := by
    rw [Nat.card_congr e'.toEquiv, card_m24TcQ]
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 1080 :=
    (card_theta_quot_dvd K).trans (hC ▸ Subgroup.card_dvd_of_le hK.le_centralizer)
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hK.isQuasisimple) (M := 1080)
    (B := 11) (by norm_num) (by norm_num) hK.isType hdvd
  have hlist : typeOrders425 1080 11 = [1080] := by decide +kernel
  rw [hlist, List.mem_singleton] at hmem
  have hle : Nat.card ↥(Subgroup.centralizer ({m24y} : Set Blueprint.NativeSporadic.M24)) ≤
      Nat.card K := by
    rw [hC, ← hmem]
    exact Nat.le_of_dvd Nat.card_pos (card_theta_quot_dvd K)
  have hKeq : K = Subgroup.centralizer ({m24y} : Set Blueprint.NativeSporadic.M24) :=
    Subgroup.eq_of_le_of_card_ge hK.le_centralizer hle
  refine ⟨isExtOf_congr ((MulEquiv.subgroupCongr hKeq).trans e').symm hQ.isExtOf, ?_⟩
  obtain ⟨hc, hf1, hf2, hf3, hnf⟩ := m24N0_facts
  rw [← m24y_eq] at hc hf1 hf2 hf3 hnf
  set f := m24N0 * m24y * m24N0⁻¹ with hf
  have hy3 : m24y ^ 3 = 1 := by rw [m24y_eq]; exact RonanK432.m24RA_pow_three
  have hy1 : m24y ≠ 1 := by
    intro h
    have := hK.orderOf_eq
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hfy3 : f ^ 3 = 1 := by rw [hf, conj_pow, hy3]; group
  have hfs := not_mem_zpowers_of_ne hy3 hf1 hf2 hf3
  obtain ⟨hE, hE9⟩ := e9_of_commute hy3 hy1 hfy3 hc.symm hfs
  obtain ⟨hn, hns⟩ := move_of_conj hfs rfl hnf
  refine ⟨Subgroup.zpowers m24y ⊔ Subgroup.zpowers f, ?_, hE, hE9, m24N0, hn, hns⟩
  rw [hKeq]
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc))

theorem card_centralizer_m24B {t : Blueprint.NativeSporadic.M24}
    (ht : (t : Equiv.Perm (Fin 24)) = tp 24 m24Row3B.rep) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set Blueprint.NativeSporadic.M24)) = 504 := by
  rw [← Subgroup.card_map_of_injective Blueprint.NativeSporadic.M24.subtype_injective,
    map_subtype_centralizer, ht]
  exact m24_threeSpec_rowB

theorem survE_m24 : SurvE ↥Blueprint.NativeSporadic.M24 (alternatingGroup (Fin 6)) := by
  refine survE_of_at fun s K hK => ?_
  have hord : orderOf (s : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hK.orderOf_eq
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover s.2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  set gP : Blueprint.NativeSporadic.M24 := ⟨g, hg⟩ with hgP
  set φ : Blueprint.NativeSporadic.M24 ≃* Blueprint.NativeSporadic.M24 := MulAut.conj gP⁻¹ with hφ
  have hφs : ((φ s : Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) = tp 24 r.rep := by
    have : ((φ s : Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) =
        g⁻¹ * (s : Equiv.Perm (Fin 24)) * g := by
      simp [hφ, hgP, MulAut.conj_apply]
    rw [this, hgr]
    group
  rcases hr with rfl | rfl
  · have hφy : φ s = m24y := Subtype.ext hφs
    refine SurvEAt.of_mulEquiv φ ?_ K hK
    rw [hφy]
    exact survEAt_m24y
  · exfalso
    exact goodCC425_of_card_dvd (M := 504) (B := 8) (card_centralizer_m24B hφs).dvd
      (by norm_num) (by norm_num) (by decide +kernel) _ (hK.map φ)

end M24

section Row

theorem checkSL_m24' : ∀ q < 626, 2 ≤ q → q ^ 3 ∣ 244823040 →
    244823040 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_m24' : ∀ q < 626, 2 ≤ q → q ^ 3 ∣ 244823040 →
    244823040 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel


theorem rankTwo_spor_m24 : RankTwoData (Spor .M24) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .M24 ≃* Spor .M24 := b
  haveI : Finite (Blueprint.NativeSporadic.Carrier .M24) :=
    (inferInstance : Finite ↥Blueprint.NativeSporadic.M24)
  haveI : Finite (Spor .M24) := Finite.of_equiv _ b'.toEquiv
  have hrank : CFSG.pRank 3 (Spor .M24) = 2 :=
    (CFSG.RankThree.Asc83Table.M24.table (L := Spor .M24) ⟨b'.symm⟩).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer
    (CFSG.Quasithin.A318P.not_dvd_outer_M24 b'.symm Nat.prime_three (by norm_num)),
    fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .M24)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .M24)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .M24)).symm.trans hrank)

end Row

section RowM24


theorem rowOf425_m24
    : RowOf425 (Spor .M24) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M24 ≃* Spor .M24 := b
  refine row425_of_survE ?_ (RankTwoData.of_mulEquiv e rankTwo_spor_m24)
    (Or.inl ⟨⟨e.trans b'.symm⟩, SurvE.of_mulEquiv (e.trans b'.symm) survE_m24⟩)
  intro L _ _ hS hL hZ3 ⟨e'⟩
  have hc : Nat.card (L ⧸ Subgroup.center L) = 244823040 := by
    rw [Nat.card_congr ((e'.trans e).trans b'.symm).toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  exact center_eq_bot_of_card hS hL hZ3 (N := 244823040) hc
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m24')
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m24')
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RowM24

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
