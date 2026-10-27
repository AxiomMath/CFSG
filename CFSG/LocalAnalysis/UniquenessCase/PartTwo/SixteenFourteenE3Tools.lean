module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
import CFSG.Quasithin.Background.HSL3One
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s1614e3_comm_of_isElemAbelianOfRank {p n : ℕ} {X : Type} [Group X]
    {E : Subgroup X} (hE : IsElemAbelianOfRank p n ↥E) :
    ∀ a b : ↥E, a * b = b * a := by
  obtain ⟨e⟩ := hE
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s1614e3_pow_of_isElemAbelianOfRank {p n : ℕ} (hp : p.Prime) {X : Type}
    [Group X] {E : Subgroup X} (hE : IsElemAbelianOfRank p n ↥E) :
    ∀ a : ↥E, a ^ p = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e⟩ := hE
  intro a
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

private theorem s1614e3_card_of_isElemAbelianOfRank {p n : ℕ} (hp : p.Prime) {X : Type}
    [Group X] {E : Subgroup X} (hE : IsElemAbelianOfRank p n ↥E) :
    Nat.card ↥E = p ^ n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e⟩ := hE
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem s1614e3_three_le_pRank_of_case4At (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p.Prime)
    (h4At : Case168_4At D V₀ V hV L p 3) :
    3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := by
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hc.setting.hyp151.le
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt
    (s1614e3_comm_of_isElemAbelianOfRank h4At.1)
    (s1614e3_pow_of_isElemAbelianOfRank hp h4At.1)
    (s1614e3_card_of_isElemAbelianOfRank hp h4At.1)
    (lBar V₀ V hV L).subtype (lBar V₀ V hV L).subtype_injective ?_
  rw [Subgroup.range_subtype]
  exact hLM

theorem s1614e3_two_mul_rkIdx_le {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {t : MulAut T} (ht : t * t = 1) : 2 * rkIdx (fixV (Subgroup.zpowers t)) ≤ rk T := by
  have h1 := CFSG.Quasithin.H.SL3One.card_le_card_fixV_sq hT ht
  rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hT),
    card_eq_two_pow hT (fixV (Subgroup.zpowers t))] at h1
  rw [← pow_mul] at h1
  have h2 : rk T ≤ rk ↥(fixV (Subgroup.zpowers t)) * 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
  omega

theorem s1614e3_mQuot_eq_rkIdx_imgTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {U : Subgroup G}
    (hU : U ≤ V) : E3.mQuot V U = rkIdx (imgTil ⊥ V hV U) := by
  have htop : imgTil ⊥ V hV V = ⊤ := by
    rw [← imgTil_preTil ⊥ V hV ⊤, preTil_top]
  have hmq := s16c167_mQuot_imgTil hV (I := V) (C := U) le_rfl hU
  rw [← hmq, htop]
  unfold E3.mQuot rkIdx
  rw [Subgroup.relIndex_top_right]

private theorem s1614e3_mem_centralizer_of_actTil_eq_one {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {g : ↥(stabTil ⊥ V)}
    (h : actTil ⊥ V hV g = 1) : (g : G) ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1 :=
    Subgroup.mem_bot.mp ((actTil_eq_one_iff ⊥ V hV g).1 h v hv)
  have h2 : (g : G) * v * (g : G)⁻¹ = v := mul_inv_eq_one.1 h1
  have h3 : (g : G) * v = v * (g : G) := by
    calc (g : G) * v = ((g : G) * v * (g : G)⁻¹) * (g : G) := by group
      _ = v * (g : G) := by rw [h2]
  exact h3.symm

private theorem s1614e3_actTil_eq_one_of_mem_centralizer {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {g : ↥(stabTil ⊥ V)}
    (h : (g : G) ∈ centralizer (V : Set G)) : actTil ⊥ V hV g = 1 := by
  rw [actTil_eq_one_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have h1 : v * (g : G) = (g : G) * v := Subgroup.mem_centralizer_iff.1 h v hv
  show (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1
  rw [← h1]
  group

theorem s1614e3_lift_involution (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) {s : MulAut (Vtil ⊥ V hV)}
    (hs : s ∈ Mbar D.M ⊥ V hV) (hs2 : orderOf s = 2) :
    ∃ t ∈ D.M, t ^ 2 ∈ centralizer (V : Set G) ∧ t ∉ centralizer (V : Set G) ∧
      barSub ⊥ V hV (Subgroup.zpowers t) = Subgroup.zpowers s ∧
      imgTil ⊥ V hV (V ⊓ centralizer ({t} : Set G)) = fixV (Subgroup.zpowers s) ∧
      E3.mQuot V (V ⊓ centralizer ({t} : Set G)) = rkIdx (fixV (Subgroup.zpowers s)) ∧
      (∀ U : Subgroup G, U ≤ V → (imgTil ⊥ V hV U ≤ fixV (Subgroup.zpowers s) ↔
        U ≤ V ⊓ centralizer ({t} : Set G))) ∧
      (∀ U : Subgroup G, U ≤ V → imgTil ⊥ V hV U = fixV (Subgroup.zpowers s) →
        U = V ⊓ centralizer ({t} : Set G)) := by
  classical
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  obtain ⟨g, hgM, hgs⟩ := (mem_barSub ⊥ V hV D.M s).1 hs
  have hact : actTil ⊥ V hV (⟨(g : G), g.2⟩ : ↥(stabTil ⊥ V)) = s := by
    simpa using hgs
  have hs2' : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs2] at h
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    omega
  have hA2 : actTil ⊥ V hV (g ^ 2) = 1 := by
    rw [map_pow, hgs, hs2']
  have hA : (g : G) ^ 2 ∈ centralizer (V : Set G) :=
    s1614e3_mem_centralizer_of_actTil_eq_one hV hA2
  have hB : (g : G) ∉ centralizer (V : Set G) := by
    intro h
    have h1 : actTil ⊥ V hV g = 1 :=
      s1614e3_actTil_eq_one_of_mem_centralizer hV h
    rw [hgs] at h1
    exact hs1 h1
  have hsub : (Subgroup.zpowers (g : G)).subgroupOf (stabTil ⊥ V) =
      Subgroup.zpowers g := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  have hC : barSub ⊥ V hV (Subgroup.zpowers (g : G)) = Subgroup.zpowers s := by
    unfold barSub
    rw [hsub, MonoidHom.map_zpowers, hgs]
  have hD : imgTil ⊥ V hV (V ⊓ centralizer ({(g : G)} : Set G)) =
      fixV (Subgroup.zpowers s) := by
    have hfix := s16c167_fixV_actTil hV (m := (g : G)) g.2
    rw [hact] at hfix
    exact hfix.symm
  have hE : E3.mQuot V (V ⊓ centralizer ({(g : G)} : Set G)) =
      rkIdx (fixV (Subgroup.zpowers s)) := by
    have hmq := s16c167_rkIdx_fixV_actTil hV (m := (g : G)) g.2
    rw [hact] at hmq
    exact hmq.symm
  have hF : ∀ U : Subgroup G, U ≤ V → (imgTil ⊥ V hV U ≤ fixV (Subgroup.zpowers s) ↔
      U ≤ V ⊓ centralizer ({(g : G)} : Set G)) := by
    intro U hUV
    rw [← hD]
    constructor
    · intro h u hu
      have hxV : u ∈ V := hUV hu
      have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨u, hxV⟩) ∈
          imgTil ⊥ V hV (V ⊓ centralizer ({(g : G)} : Set G)) :=
        h ((mem_imgTil ⊥ V hV U _).2 ⟨IntMod.mk hV ⟨u, hxV⟩, hu, rfl⟩)
      obtain ⟨y, hy, hyeq⟩ := (mem_imgTil ⊥ V hV _ _).1 hmem
      have hyu : y.val = u := by
        have h1 : y.val * (IntMod.mk hV ⟨u, hxV⟩).val⁻¹ = 1 :=
          Subgroup.mem_bot.mp ((mkTil_eq_iff ⊥ V hV y _).1 hyeq)
        exact mul_inv_eq_one.1 h1
      rw [hyu] at hy
      exact hy
    · intro h q hq
      obtain ⟨y, hyU, rfl⟩ := (mem_imgTil ⊥ V hV U q).1 hq
      exact (mem_imgTil ⊥ V hV (V ⊓ centralizer ({(g : G)} : Set G)) _).2
        ⟨y, h hyU, rfl⟩
  have hG : ∀ U : Subgroup G, U ≤ V → imgTil ⊥ V hV U = fixV (Subgroup.zpowers s) →
      U = V ⊓ centralizer ({(g : G)} : Set G) := by
    intro U hUV hU
    refine le_antisymm ?_ ?_
    · exact (hF U hUV).1 hU.le
    · intro x hx
      have hxV : x ∈ V := (Subgroup.mem_inf.1 hx).1
      have hxmem : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ imgTil ⊥ V hV U := by
        rw [hU, ← hD]
        exact (mem_imgTil ⊥ V hV (V ⊓ centralizer ({(g : G)} : Set G)) _).2
          ⟨IntMod.mk hV ⟨x, hxV⟩, hx, rfl⟩
      obtain ⟨y, hyU, hyeq⟩ := (mem_imgTil ⊥ V hV U _).1 hxmem
      have hyx : y.val = x := by
        have h1 : y.val * (IntMod.mk hV ⟨x, hxV⟩).val⁻¹ = 1 :=
          Subgroup.mem_bot.mp ((mkTil_eq_iff ⊥ V hV y _).1 hyeq)
        exact mul_inv_eq_one.1 h1
      rw [← hyx]
      exact hyU
  exact ⟨(g : G), hgM, hA, hB, hC, hD, hE, hF, hG⟩

theorem s1614e3_centralizer_eq (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) {t : G} (ht : t ∈ D.M) {U : Subgroup G} (hUV : U ≤ V)
    (htU : U ≤ centralizer ({t} : Set G))
    (hcent : ∀ m ∈ Mbar D.M ⊥ V hV, (∀ x ∈ imgTil ⊥ V hV U, m x = x) →
      m = 1 ∨ m ∈ barSub ⊥ V hV (Subgroup.zpowers t)) :
    D.M ⊓ centralizer (U : Set G) =
      (D.M ⊓ centralizer (V : Set G)) ⊔ Subgroup.zpowers t := by
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxM : x ∈ D.M := hx.1
    have hxU : x ∈ centralizer (U : Set G) := hx.2
    have hfix : ∀ q ∈ imgTil ⊥ V hV U, actTil ⊥ V hV ⟨x, hMst hxM⟩ q = q := by
      intro q hq
      obtain ⟨z, hzU, rfl⟩ := (mem_imgTil ⊥ V hV U q).1 hq
      rw [actTil_mk]
      congr 1
      refine IntMod.val_injective ?_
      rw [actStab_apply_val]
      have h1 : z.val * x = x * z.val := Subgroup.mem_centralizer_iff.1 hxU z.val hzU
      show x * z.val * x⁻¹ = z.val
      rw [← h1]
      group
    rcases hcent (actTil ⊥ V hV ⟨x, hMst hxM⟩)
      (actTil_mem_barSub ⊥ V hV hxM (hMst hxM)) hfix with h1 | hbar
    · have hxC : x ∈ centralizer (V : Set G) :=
        s1614e3_mem_centralizer_of_actTil_eq_one hV h1
      exact Subgroup.mem_sup_left ⟨hxM, hxC⟩
    · obtain ⟨g', hg't, hg'eq⟩ := (mem_barSub ⊥ V hV (Subgroup.zpowers t) _).1 hbar
      have hg'M : (g' : G) ∈ D.M := Subgroup.zpowers_le.mpr ht hg't
      have h1 : actTil ⊥ V hV (⟨x, hMst hxM⟩ * g'⁻¹) = 1 := by
        rw [map_mul, map_inv, hg'eq]
        group
      have hxC : x * (g' : G)⁻¹ ∈ centralizer (V : Set G) :=
        s1614e3_mem_centralizer_of_actTil_eq_one hV h1
      have hxeq : x = (x * (g' : G)⁻¹) * (g' : G) := by group
      rw [hxeq]
      exact Subgroup.mul_mem_sup ⟨Subgroup.mul_mem _ hxM (Subgroup.inv_mem _ hg'M), hxC⟩ hg't
  · refine sup_le ?_ ?_
    · exact le_inf inf_le_left
        (inf_le_right.trans (Subgroup.centralizer_le hUV))
    · refine le_inf (Subgroup.zpowers_le.mpr ht) (Subgroup.zpowers_le.mpr ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        Subgroup.mem_centralizer_singleton_iff.mp (htU hu)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
