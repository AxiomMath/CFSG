module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainComp
import CFSG.Timmesfeld.Bridge.OddTranspMain
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

private theorem qComp_commute (c : SzCfg G D d E e n)
    {a : ↥(Subgroup.closure E)} (ha : a ∈ szE E)
    {x y : ↥(Subgroup.closure E)}
    (hx : x ∈ ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆)
    (hy : y ∈ ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆) : Commute x y :=
  OddTransp.commute_of_mem_commutator_self c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.closure E))) ha hx hy

private theorem qComp_mul_self (c : SzCfg G D d E e n)
    {a : ↥(Subgroup.closure E)} (ha : a ∈ szE E)
    {x : ↥(Subgroup.closure E)}
    (hx : x ∈ ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆) : x * x = 1 := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  have hD : Asc72.IsOddTransp (szE E) := c.setup.oddT
  have hN : IsNormalSet (szE E) := c.setup.normal
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  let S : Set K := {g | ∃ q ∈ Q, ∃ t ∈ Subgroup.zpowers a, ⁅q, t⁆ = g}
  have hS_pair : ∀ y ∈ S, ∀ z ∈ S, Commute y z := by
    intro y hy z hz
    exact OddTransp.commute_of_mem_commutator_self hD hN hQ ha
      (by rw [Subgroup.commutator_def]; exact Subgroup.subset_closure hy)
      (by rw [Subgroup.commutator_def]; exact Subgroup.subset_closure hz)
  have hS_sq : ∀ y ∈ S, y * y = 1 := by
    rintro y ⟨q, hq, t, ht, rfl⟩
    rcases (mem_zpowers_of_mul_self (hD.mul_self_eq_one ha)).mp ht with h1 | h1
    · rw [h1, commutatorElement_one_right]
      simp
    · rw [h1]
      have hqD : q * a * q⁻¹ ∈ szE E := hN q a ha
      have hcomm : Commute (q * a * q⁻¹) a := by
        simpa using OddTransp.commute_conj_of_mem hD hN hQ ha hq (Subgroup.one_mem Q)
      by_cases hua : q * a * q⁻¹ = a
      · rw [commutatorElement_def, hua]
        simp
      · have hz := hD.orderOf_mul_eq_two hqD ha hua hcomm
        have hpow : (q * a * q⁻¹ * a) ^ 2 = 1 := by
          rw [← hz, pow_orderOf_eq_one]
        rw [commutatorElement_def, hD.inv_eq ha]
        simpa [pow_two] using hpow
  have hxclosure : x ∈ Subgroup.closure S := by
    have hxc := hx
    rw [Subgroup.commutator_def] at hxc
    simpa only [S, Q, H, K] using hxc
  exact OddLocal.mul_self_eq_one_of_mem_closure hS_pair hS_sq hxclosure

private theorem qComp_le_pCore {a : ↥(Subgroup.closure E)} :
    ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆ ≤
      CFSG.pCore 2 ↥(Subgroup.closure E) :=
  Subgroup.commutator_le_left _ _

theorem commutator_szQ_le (E : Set G) {a : G} (ha : a ∈ Subgroup.closure E) :
    ⁅szQ E, Subgroup.zpowers a⁆ ≤ szQ E := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  have hmap : (⁅Q, Subgroup.zpowers (⟨a, ha⟩ : K)⁆).map H.subtype =
      ⁅szQ E, Subgroup.zpowers a⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rfl
  rw [← hmap]
  rintro x ⟨y, hy, rfl⟩
  exact Subgroup.mem_map_of_mem H.subtype (Subgroup.commutator_le_left Q _ hy)

theorem SzCfg.commute_of_mem_commutator (c : SzCfg G D d E e n) {a t y : G} (ha : a ∈ E)
    (ht : t ∈ szComp E a) (hy : y ∈ ⁅szQ E, Subgroup.zpowers a⁆) : Commute t y := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  have haH : a ∈ Subgroup.closure E := Subgroup.subset_closure ha
  have htE : t ∈ E := ht.1
  have htH : t ∈ Subgroup.closure E := Subgroup.subset_closure htE
  have hyQ : y ∈ szQ E := commutator_szQ_le E haH hy
  have hyH : y ∈ Subgroup.closure E := szQ_le_closure E hyQ
  let aK : K := ⟨a, haH⟩
  let tK : K := ⟨t, htH⟩
  let yK : K := ⟨y, hyH⟩
  have haK : aK ∈ szE E := ha
  have htK : tK ∈ szE E := htE
  have htcommG : Commute (tK : G) (aK : G) := ht.2
  have htcomm : Commute tK aK :=
    (commute_coe_iff (H := H) (u := tK) (v := aK)).mp htcommG
  have hyKmem : yK ∈ ⁅Q, Subgroup.zpowers aK⁆ := by
    have hmap : (⁅Q, Subgroup.zpowers aK⁆).map H.subtype =
        ⁅szQ E, Subgroup.zpowers a⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      rfl
    have hy' : y ∈ (⁅Q, Subgroup.zpowers aK⁆).map H.subtype := by
      rw [hmap]; exact hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    have hzy' : z = yK := Subtype.ext hzy
    rwa [hzy'] at hz
  have hcommK : Commute tK yK :=
    OddTransp.commute_of_mem_commutator c.setup.oddT c.setup.normal
      (CFSG.pCore_isPGroup (p := 2) (G := K)) haK htK htcomm hyKmem
  exact (commute_coe_iff (H := H) (u := tK) (v := yK)).mpr hcommK

private def szCompK (E : Set G) (a : ↥(Subgroup.closure E)) : Set ↥(Subgroup.closure E) :=
  {u | u ∈ szE E ∧ Commute u a}

private theorem compK_commute (c : SzCfg G D d E e n)
    {a b x : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E) (hx : x ∈ szE E)
    (hba : Commute b a) (hxa : Commute x a) : Commute b x := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  obtain ⟨P, haP⟩ := c.exists_szS ha
  have hbaG : Commute (b : G) (a : G) := (commute_coe_iff (H := H) (u := b) (v := a)).mpr hba
  have hxaG : Commute (x : G) (a : G) := (commute_coe_iff (H := H) (u := x) (v := a)).mpr hxa
  have haG : (a : G) ∈ E := ha
  have hbP : (b : G) ∈ szS E P :=
    (c.mem_szS_iff_commute P haG hb haP).mpr hbaG
  have hxP : (x : G) ∈ szS E P :=
    (c.mem_szS_iff_commute P haG hx haP).mpr hxaG
  have hbD : (b : G) ∈ D := (c.subset_commSet hb).1
  have hxD : (x : G) ∈ D := (c.subset_commSet hx).1
  have hcommG : Commute (b : G) (x : G) :=
    c.hyp.setup.oddT.commute_of_isPGroup (isPGroup_szS E P) hbD hxD hbP hxP
  exact (commute_coe_iff (H := H) (u := b) (v := x)).mp hcommG

private theorem qComp_le_centralizer_comp (c : SzCfg G D d E e n)
    {a b x : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E) (hx : x ∈ szE E)
    (hba : Commute b a) (hxa : Commute x a) :
    ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers x⁆ ≤
      Subgroup.centralizer ({b} : Set ↥(Subgroup.closure E)) := by
  intro y hy
  have hbx : Commute b x := compK_commute c ha hb hx hba hxa
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (OddTransp.commute_of_mem_commutator c.setup.oddT c.setup.normal
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.closure E))) hx hb hbx hy).symm

private theorem sup_center_le_centralizer_comp (c : SzCfg G D d E e n)
    {a b : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E) (hba : Commute b a) :
    Subgroup.closure (⋃ x ∈ szCompK E a,
        ((⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers x⁆ :
          Subgroup ↥(Subgroup.closure E)) : Set ↥(Subgroup.closure E))) ⊔
      Subgroup.center ↥(Subgroup.closure E) ≤
      Subgroup.centralizer ({b} : Set ↥(Subgroup.closure E)) := by
  refine sup_le ?_ (Subgroup.center_le_centralizer {b})
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hyx⟩ := hy
  exact qComp_le_centralizer_comp c ha hb hx.1 hba hx.2 hyx

private theorem pCore_le_sup_qComp (c : SzCfg G D d E e n)
    {a f : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) :
    CFSG.pCore 2 ↥(Subgroup.closure E) ≤
      Subgroup.closure (⋃ x ∈ szCompK E a,
        ((⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers x⁆ :
          Subgroup ↥(Subgroup.closure E)) : Set ↥(Subgroup.closure E))) ⊔
        ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers f⁆ := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let C : Set K := szCompK E a
  let Q1 : Subgroup K := Subgroup.closure (⋃ x ∈ C,
    ((⁅Q, Subgroup.zpowers x⁆ : Subgroup K) : Set K))
  let Qf : Subgroup K := ⁅Q, Subgroup.zpowers f⁆
  let Q0 : Subgroup K := Q1 ⊔ Qf
  have hQ0Q : Q0 ≤ Q := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      exact qComp_le_pCore hzx
    · exact qComp_le_pCore
  have hgen : Subgroup.closure (insert f C) = ⊤ := by
    simpa [C, szCompK] using c.closure_insert_comp_top (a := a) (b := f) ha hf haf
  have hT2 : ∀ t ∈ insert f C, t * t = 1 := by
    intro t ht
    rcases ht with rfl | ht
    · exact c.setup.oddT.mul_self_eq_one hf
    · exact c.setup.oddT.mul_self_eq_one ht.1
  have hgencomm : ∀ t ∈ insert f C, ∀ q ∈ Q, ⁅q, t⁆ ∈ Q0 := by
    intro t ht q hq
    rcases ht with htf | htC
    · rw [htf]
      exact Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers f))
    · have hmem : ⁅q, t⁆ ∈ (⁅Q, Subgroup.zpowers t⁆ : Subgroup K) :=
        Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers t)
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by
        simp only [Set.mem_iUnion]
        exact ⟨t, htC, hmem⟩))
  have hcommle : ⁅Q, ⊤⁆ ≤ Q0 :=
    OddTransp.commutator_le_of_closure hQ0Q hgen hT2 hgencomm
  have hnpc : Q ≤ ⁅Q, ⊤⁆ :=
    OddTransp.pCore_le_commutator_of_isBenderGroup c.setup c.perfect c.isBenderGroup_zStar
  exact hnpc.trans hcommle


private theorem centralizer_eq_sup_center (c : SzCfg G D d E e n)
    {a f : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) :
    Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
        CFSG.pCore 2 ↥(Subgroup.closure E) =
      Subgroup.closure (⋃ x ∈ szCompK E a,
        ((⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers x⁆ :
          Subgroup ↥(Subgroup.closure E)) : Set ↥(Subgroup.closure E))) ⊔
        (Subgroup.center ↥(Subgroup.closure E) ⊓ CFSG.pCore 2 ↥(Subgroup.closure E)) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let C : Subgroup K := Subgroup.centralizer ({a} : Set K) ⊓ Q
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Q1 : Subgroup K := Subgroup.closure (⋃ x ∈ szCompK E a,
    ((⁅Q, Subgroup.zpowers x⁆ : Subgroup K) : Set K))
  let Qf : Subgroup K := ⁅Q, Subgroup.zpowers f⁆
  have hQ1Q : Q1 ≤ Q := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    exact qComp_le_pCore hzx
  have hQfQ : Qf ≤ Q := qComp_le_pCore
  have hQ0Q : Q1 ⊔ Qf ≤ Q := sup_le hQ1Q hQfQ
  have hQeq : Q = Q1 ⊔ Qf :=
    le_antisymm (pCore_le_sup_qComp c ha hf haf) hQ0Q
  have hQ1C : Q1 ≤ C := by
    refine le_inf ?_ hQ1Q
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (OddTransp.commute_of_mem_commutator (D := szE E) (Q := Q) (a := x) (f := a)
        c.setup.oddT c.setup.normal (CFSG.pCore_isPGroup (p := 2) (G := K))
        hx.1 ha hx.2.symm hyx).symm
  have hZle : Z ≤ C :=
    le_inf (le_trans inf_le_left (Subgroup.center_le_centralizer ({a} : Set K))) inf_le_right
  have hinfQfZ : C ⊓ Qf ≤ Z := by
    intro y hy
    obtain ⟨⟨hya, hyQ⟩, hyQf⟩ := hy
    have hya' : Commute y a := Subgroup.mem_centralizer_singleton_iff.mp hya
    have hyQa : y ∈ ⁅Q, Subgroup.zpowers a⁆ :=
      OddTransp.mem_commutator_of_commute c.setup.oddT c.setup.normal
        (CFSG.pCore_isPGroup (p := 2) (G := K)) ha hf haf hyQf hya'
    have hcenter : y ∈ Subgroup.center K := by
      have hgen : Subgroup.closure (insert f {u | u ∈ szE E ∧ Commute u a}) = ⊤ :=
        c.closure_insert_comp_top (a := a) (b := f) ha hf haf
      have hres := OddTransp.localQ_three c.setup.oddT c.setup.normal
        (CFSG.pCore_isPGroup (p := 2) (G := K)) c.setup ha hf haf hgen
      exact hres.1 ⟨hyQa, hyQf⟩
    exact ⟨hcenter, hyQ⟩
  refine le_antisymm ?_ (sup_le hQ1C hZle)
  intro y hy
  obtain ⟨hya, hyQ⟩ := hy
  have hnorm : Q1 ≤ Subgroup.normalizer (Qf : Set K) :=
    le_trans hQ1Q (Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := Subgroup.zpowers f))
  have hmul : (↑(Q1 ⊔ Qf) : Set K) = ↑Qf * ↑Q1 := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Qf Q1 hnorm
  have hyQ' : y ∈ (↑Qf * ↑Q1 : Set K) := hmul ▸ (hQeq ▸ hyQ)
  obtain ⟨y₂, hy₂, y₁, hy₁, hy_eq⟩ := Set.mem_mul.mp hyQ'
  have hy₁C : y₁ ∈ C := hQ1C hy₁
  have hy₂C : y₂ ∈ C := by
    have hval : y₂ = y * y₁⁻¹ := by rw [← hy_eq]; group
    rw [hval]
    exact C.mul_mem ⟨hya, hyQ⟩ (C.inv_mem hy₁C)
  have hy₂Z : y₂ ∈ Z := hinfQfZ ⟨hy₂C, hy₂⟩
  rw [← hy_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy₂Z) (Subgroup.mem_sup_left hy₁)

private theorem mem_center_of_commute (c : SzCfg G D d E e n)
    {a f y : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) (hyQ : y ∈ CFSG.pCore 2 ↥(Subgroup.closure E))
    (hya : Commute y a) (hyf : Commute y f) : y ∈ Subgroup.center ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Q1 : Subgroup K := Subgroup.closure (⋃ x ∈ szCompK E a,
    ((⁅Q, Subgroup.zpowers x⁆ : Subgroup K) : Set K))
  have hC := centralizer_eq_sup_center c ha hf haf
  have hyC : y ∈ Subgroup.centralizer ({a} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hya, hyQ⟩
  rw [hC] at hyC
  change y ∈ Q1 ⊔ (Subgroup.center K ⊓ Q) at hyC
  have hle : Subgroup.closure (insert f (szCompK E a)) ≤
      Subgroup.centralizer ({y} : Set K) := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with hzf | hzC
    · rw [hzf]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyf.symm
    · have hzc := sup_center_le_centralizer_comp c ha hzC.1 hzC.2
      have hle : Q1 ⊔ (Subgroup.center K ⊓ Q) ≤ Q1 ⊔ Subgroup.center K :=
        sup_le le_sup_left (le_trans inf_le_left le_sup_right)
      have hyC' : y ∈ Q1 ⊔ Subgroup.center K := hle hyC
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hzc hyC')).symm
  have hgen : Subgroup.closure (insert f (szCompK E a)) = ⊤ := by
    simpa [szCompK] using c.closure_insert_comp_top (a := a) (b := f) ha hf haf
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen ▸ Subgroup.mem_top g))

private theorem centralizer_eq_qComp_sup_center (c : SzCfg G D d E e n)
    {a f : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) :
    Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
        CFSG.pCore 2 ↥(Subgroup.closure E) =
      ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆ ⊔
        (Subgroup.center ↥(Subgroup.closure E) ⊓ CFSG.pCore 2 ↥(Subgroup.closure E)) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨hya, hyQ⟩ := hy
    have hya' : Commute y a := Subgroup.mem_centralizer_singleton_iff.mp hya
    obtain ⟨x, hx, w, hwQ, hwa, hwf, hy_eq⟩ :=
      OddTransp.exists_commutator_mul_of_commute c.setup.oddT c.setup.normal
        (CFSG.pCore_isPGroup (p := 2) (G := K)) ha hf haf hyQ hya'
    have hwZ : w ∈ Z :=
      ⟨mem_center_of_commute c ha hf haf hwQ hwa hwf, hwQ⟩
    rw [hy_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hwZ)
  · refine sup_le ?_ ?_
    · intro y hy
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, qComp_le_pCore hy⟩
      exact (OddTransp.commute_of_mem_commutator c.setup.oddT c.setup.normal
        (CFSG.pCore_isPGroup (p := 2) (G := K)) ha ha (Commute.refl a) hy).symm
    · intro y hy
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hy.1 a).symm, hy.2⟩

private theorem centralizer_commute (c : SzCfg G D d E e n)
    {a f : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) {u v : ↥(Subgroup.closure E)}
    (hu : u ∈ Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
      CFSG.pCore 2 ↥(Subgroup.closure E))
    (hv : v ∈ Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
      CFSG.pCore 2 ↥(Subgroup.closure E)) : Commute u v := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  have hC := centralizer_eq_qComp_sup_center c ha hf haf
  have hZnorm : Qa ≤ Subgroup.normalizer (Z : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Z.Normal)]
    exact le_top
  have hprod : (↑(Z ⊔ Qa) : Set K) = ↑Z * ↑Qa :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z Qa hZnorm
  have hC' : Subgroup.centralizer ({a} : Set K) ⊓ Q = Z ⊔ Qa := by
    rw [hC, sup_comm]
  have hu' : u ∈ (↑Z * ↑Qa : Set K) := by
    rw [← hprod, ← hC']
    exact hu
  have hv' : v ∈ (↑Z * ↑Qa : Set K) := by
    rw [← hprod, ← hC']
    exact hv
  obtain ⟨z₁, hz₁, q₁, hq₁, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨z₂, hz₂, q₂, hq₂, rfl⟩ := Set.mem_mul.mp hv'
  have h11 : z₁ * z₂ = z₂ * z₁ := (Subgroup.mem_center_iff.mp hz₁.1 z₂).symm
  have h12 : z₁ * q₂ = q₂ * z₁ := (Subgroup.mem_center_iff.mp hz₁.1 q₂).symm
  have h21 : q₁ * z₂ = z₂ * q₁ := Subgroup.mem_center_iff.mp hz₂.1 q₁
  have h22 : q₁ * q₂ = q₂ * q₁ := (qComp_commute c ha hq₁ hq₂).eq
  show (z₁ * q₁) * (z₂ * q₂) = (z₂ * q₂) * (z₁ * q₁)
  calc (z₁ * q₁) * (z₂ * q₂) = z₁ * (q₁ * z₂) * q₂ := by group
    _ = z₁ * (z₂ * q₁) * q₂ := by rw [h21]
    _ = (z₁ * z₂) * (q₁ * q₂) := by group
    _ = (z₂ * z₁) * (q₁ * q₂) := by rw [h11]
    _ = (z₂ * z₁) * (q₂ * q₁) := by rw [h22]
    _ = z₂ * (z₁ * q₂) * q₁ := by group
    _ = z₂ * (q₂ * z₁) * q₁ := by rw [h12]
    _ = (z₂ * q₂) * (z₁ * q₁) := by group

private theorem commutator_qComp_le_center (c : SzCfg G D d E e n)
    {a b : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E)
    (hab : ¬ Commute a b) :
    ⁅⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers a⁆,
        ⁅CFSG.pCore 2 ↥(Subgroup.closure E), Subgroup.zpowers b⁆⁆ ≤
      Subgroup.center ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  let Qb : Subgroup K := ⁅Q, Subgroup.zpowers b⁆
  have hgen : Subgroup.closure (insert b {u | u ∈ szE E ∧ Commute u a}) = ⊤ :=
    c.closure_insert_comp_top (a := a) (b := b) ha hb hab
  have hres := OddTransp.localQ_three c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := K)) c.setup ha hb hab hgen
  have hinf : Qa ⊓ Qb ≤ Subgroup.center K := hres.1
  have hQbNa : Qb ≤ Subgroup.normalizer (Qa : Set K) :=
    le_trans (qComp_le_pCore)
      (Subgroup.normalizer_commutator_ge_left Q (Subgroup.zpowers a))
  have h1 : ⁅Qa, Qb⁆ ≤ Qa :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hQbNa
  have hQaNb : Qa ≤ Subgroup.normalizer (Qb : Set K) :=
    le_trans (qComp_le_pCore)
      (Subgroup.normalizer_commutator_ge_left Q (Subgroup.zpowers b))
  have h2 : ⁅Qa, Qb⁆ ≤ Qb :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hQaNb
  exact (le_inf h1 h2).trans hinf


private theorem commutator_qComp_centralizer_le_center (c : SzCfg G D d E e n)
    {a b u v : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E)
    (hab : ¬ Commute a b) (hu : u ∈ ⁅CFSG.pCore 2 ↥(Subgroup.closure E),
      Subgroup.zpowers b⁆)
    (hv : v ∈ Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
      CFSG.pCore 2 ↥(Subgroup.closure E)) : ⁅u, v⁆ ∈ Subgroup.center ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  have hC := centralizer_eq_qComp_sup_center c ha hb hab
  have hC' : Subgroup.centralizer ({a} : Set K) ⊓ Q = Z ⊔ Qa := by
    rw [hC, sup_comm]
  have hZnorm : Qa ≤ Subgroup.normalizer (Z : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Z.Normal)]
    exact le_top
  have hprod : (↑(Z ⊔ Qa) : Set K) = ↑Z * ↑Qa :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z Qa hZnorm
  have hv' : v ∈ (↑Z * ↑Qa : Set K) := by
    rw [← hprod, ← hC']
    exact hv
  obtain ⟨z, hz, q, hq, rfl⟩ := Set.mem_mul.mp hv'
  have hcenter : ⁅u, q⁆ ∈ Subgroup.center K :=
    (commutator_qComp_le_center c hb ha (fun h => hab h.symm))
      (Subgroup.commutator_mem_commutator hu hq)
  rw [commutatorElement_mul_right_eq_mul_conj]
  have huz : ⁅u, z⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hz.1 u)
  rw [huz, one_mul]
  have hzc := Subgroup.mem_center_iff.mp hcenter z
  rw [hzc, mul_assoc, mul_inv_cancel, mul_one]
  exact hcenter

private theorem commutator_mem_center (c : SzCfg G D d E e n)
    {a b x y : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E)
    (hab : ¬ Commute a b) (hx : x ∈ CFSG.pCore 2 ↥(Subgroup.closure E))
    (hy : y ∈ CFSG.pCore 2 ↥(Subgroup.closure E)) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  have hgen : Subgroup.closure (insert b {u | u ∈ szE E ∧ Commute u a}) = ⊤ :=
    c.closure_insert_comp_top (a := a) (b := b) ha hb hab
  have hres := OddTransp.localQ_three c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := K)) c.setup ha hb hab hgen
  have hmul := hres.2.1
  obtain ⟨xa, hxaQ, hxaa, xb, hxbQb, rfl⟩ := hmul x hx
  obtain ⟨ya, hyaQ, hyaa, yb, hybQb, rfl⟩ := hmul y hy
  have hxaC : xa ∈ Subgroup.centralizer ({a} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxaa, hxaQ⟩
  have hyaC : ya ∈ Subgroup.centralizer ({a} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyaa, hyaQ⟩
  have hxaya : Commute xa ya := centralizer_commute c ha hb hab hxaC hyaC
  have hxbyb : Commute xb yb := qComp_commute c hb hxbQb hybQb
  have hcross1 : ⁅xb, ya⁆ ∈ Subgroup.center K :=
    commutator_qComp_centralizer_le_center c ha hb hab hxbQb hyaC
  have hybxa : ⁅yb, xa⁆ ∈ Subgroup.center K :=
    commutator_qComp_centralizer_le_center c ha hb hab hybQb hxaC
  have hcross2 : ⁅xa, yb⁆ ∈ Subgroup.center K := by
    have := Subgroup.inv_mem _ hybxa
    rwa [commutatorElement_inv] at this
  have h1 : ⁅xb, ya * yb⁆ = ⁅xb, ya⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hzero : ⁅xb, yb⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hxbyb
    rw [hzero, mul_one]
    group
  have h2 : ⁅xa, ya * yb⁆ = ⁅xa, yb⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hzero : ⁅xa, ya⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hxaya
    rw [hzero, one_mul]
    have hc := Subgroup.mem_center_iff.mp hcross2 ya
    rw [hc]
    group
  change ⁅xa * xb, ya * yb⁆ ∈ Subgroup.center K
  rw [commutatorElement_mul_left_eq_conj_mul, h1, h2]
  have hc := Subgroup.mem_center_iff.mp hcross1 xa
  rw [hc]
  have hmul : ⁅xb, ya⁆ * xa * xa⁻¹ * ⁅xa, yb⁆ = ⁅xb, ya⁆ * ⁅xa, yb⁆ := by group
  rw [hmul]
  exact Subgroup.mul_mem _ hcross1 hcross2

private theorem sq_mem_center_of_mem_centralizer (c : SzCfg G D d E e n)
    {a f : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hf : f ∈ szE E)
    (haf : ¬ Commute a f) {u : ↥(Subgroup.closure E)}
    (hu : u ∈ Subgroup.centralizer ({a} : Set ↥(Subgroup.closure E)) ⊓
      CFSG.pCore 2 ↥(Subgroup.closure E)) :
    u * u ∈ Subgroup.center ↥(Subgroup.closure E) ⊓
      CFSG.pCore 2 ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  have hC := centralizer_eq_qComp_sup_center c ha hf haf
  have hC' : Subgroup.centralizer ({a} : Set K) ⊓ Q = Z ⊔ Qa := by
    rw [hC, sup_comm]
  have hZnorm : Qa ≤ Subgroup.normalizer (Z : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Z.Normal)]
    exact le_top
  have hprod : (↑(Z ⊔ Qa) : Set K) = ↑Z * ↑Qa :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z Qa hZnorm
  have hu' : u ∈ (↑Z * ↑Qa : Set K) := by
    rw [← hprod, ← hC']
    exact hu
  obtain ⟨z, hz, q, hq, rfl⟩ := Set.mem_mul.mp hu'
  have hq2 : q * q = 1 := qComp_mul_self c ha hq
  have hz2 : z * z ∈ Z := Z.mul_mem hz hz
  have hzc := Subgroup.mem_center_iff.mp hz.1 q
  have hsq : (z * q) * (z * q) = (z * z) * (q * q) := by
    calc (z * q) * (z * q) = z * (q * z) * q := by group
      _ = z * (z * q) * q := by rw [hzc]
      _ = (z * z) * (q * q) := by group
  rw [hsq, hq2, mul_one]
  exact hz2

private theorem square_mem_center (c : SzCfg G D d E e n)
    {a b x : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E)
    (hab : ¬ Commute a b) (hx : x ∈ CFSG.pCore 2 ↥(Subgroup.closure E)) :
    x * x ∈ Subgroup.center ↥(Subgroup.closure E) := by
  let K := ↥(Subgroup.closure E)
  let Q : Subgroup K := CFSG.pCore 2 K
  have hgen : Subgroup.closure (insert b {u | u ∈ szE E ∧ Commute u a}) = ⊤ :=
    c.closure_insert_comp_top (a := a) (b := b) ha hb hab
  have hres := OddTransp.localQ_three c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := K)) c.setup ha hb hab hgen
  obtain ⟨xa, hxaQ, hxaa, xb, hxbQb, rfl⟩ := hres.2.1 x hx
  have hxaC : xa ∈ Subgroup.centralizer ({a} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxaa, hxaQ⟩
  have hxa2 : xa * xa ∈ Subgroup.center K ⊓ Q :=
    sq_mem_center_of_mem_centralizer c ha hb hab hxaC
  have hxb2 : xb * xb = 1 := qComp_mul_self c hb hxbQb
  have hcross : ⁅xb, xa⁆ ∈ Subgroup.center K := by
    have := commutator_qComp_centralizer_le_center c ha hb hab hxbQb hxaC
    exact this
  have hxaxb : xb * xa = ⁅xb, xa⁆ * (xa * xb) := by
    rw [commutatorElement_def]
    group
  have hsq : (xa * xb) * (xa * xb) = ⁅xb, xa⁆ * (xa * xa) * (xb * xb) := by
    have hcx := Subgroup.mem_center_iff.mp hcross xa
    calc (xa * xb) * (xa * xb) = xa * (xb * xa) * xb := by group
      _ = xa * (⁅xb, xa⁆ * (xa * xb)) * xb := by rw [hxaxb]
      _ = (xa * ⁅xb, xa⁆) * xa * (xb * xb) := by group
      _ = (⁅xb, xa⁆ * xa) * xa * (xb * xb) := by rw [hcx]
      _ = ⁅xb, xa⁆ * (xa * xa) * (xb * xb) := by group
  rw [hsq, hxb2, mul_one]
  exact Subgroup.mul_mem _ hcross hxa2.1


private theorem mem_szZ_of_mem_center
    {y : ↥(Subgroup.closure E)} (hyQ : y ∈ CFSG.pCore 2 ↥(Subgroup.closure E))
    (hyZ : y ∈ Subgroup.center ↥(Subgroup.closure E)) : (y : G) ∈ szZ E := by
  let H : Subgroup G := Subgroup.closure E
  refine ⟨mem_szQ_iff.mpr ⟨y.2, hyQ⟩, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro a ha
  let aK : ↥(Subgroup.closure E) := ⟨a, Subgroup.subset_closure ha⟩
  have hcommK : Commute y aK := (Subgroup.mem_center_iff.mp hyZ aK).symm
  exact ((commute_coe_iff (H := H) (u := y) (v := aK)).mpr hcommK).symm

private theorem commute_of_mem_centralizer_of_mem_comp (c : SzCfg G D d E e n)
    {a b y : ↥(Subgroup.closure E)} (ha : a ∈ szE E) (hb : b ∈ szE E)
    (hba : Commute b a) (hyQ : y ∈ CFSG.pCore 2 ↥(Subgroup.closure E))
    (hya : Commute y a) : Commute y b := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers a⁆
  let Q1 : Subgroup K := Subgroup.closure (⋃ x ∈ szCompK E a,
    ((⁅Q, Subgroup.zpowers x⁆ : Subgroup K) : Set K))
  obtain ⟨f, hfE, hfna⟩ := c.exists_not_commute (show (a : G) ∈ E from ha)
  let fK : K := ⟨f, Subgroup.subset_closure hfE⟩
  have hfK : fK ∈ szE E := hfE
  have hafG : ¬ Commute (a : G) f := fun h => hfna h.symm
  have hafK : ¬ Commute a fK := fun h =>
    hafG ((commute_coe_iff (H := H) (u := a) (v := fK)).mpr h)
  have hyC : y ∈ Subgroup.centralizer ({a} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hya, hyQ⟩
  have hC := centralizer_eq_qComp_sup_center c ha hfK hafK
  rw [hC] at hyC
  change y ∈ Qa ⊔ Z at hyC
  have hQaQ1 : Qa ≤ Q1 := by
    intro z hz
    exact Subgroup.subset_closure (by
      simp only [Set.mem_iUnion]
      exact ⟨a, ⟨ha, Commute.refl a⟩, hz⟩)
  have hle : Qa ⊔ Z ≤ Q1 ⊔ Subgroup.center K :=
    sup_le (le_trans hQaQ1 le_sup_left) (le_trans inf_le_left le_sup_right)
  have hzc := sup_center_le_centralizer_comp c ha hb hba
  have hyc : y ∈ Subgroup.centralizer ({b} : Set K) := hzc (hle hyC)
  exact Subgroup.mem_centralizer_singleton_iff.mp hyc

theorem SzCfg.exists_mul_eq (c : SzCfg G D d E e n) {a b y : G} (ha : a ∈ E) (hb : b ∈ E)
    (hab : ¬ Commute a b) (hy : y ∈ szQ E) :
    ∃ y₁ ∈ szQ E, Commute y₁ a ∧ ∃ y₂ ∈ ⁅szQ E, Subgroup.zpowers b⁆, y = y₁ * y₂ := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let aK : K := ⟨a, Subgroup.subset_closure ha⟩
  let bK : K := ⟨b, Subgroup.subset_closure hb⟩
  let yK : K := ⟨y, szQ_le_closure E hy⟩
  have haK : aK ∈ szE E := ha
  have hbK : bK ∈ szE E := hb
  have hyKQ : yK ∈ Q := (mem_szQ_iff.mp hy).2
  have habK : ¬ Commute aK bK := fun h =>
    hab ((commute_coe_iff (H := H) (u := aK) (v := bK)).mpr h)
  have hgen : Subgroup.closure (insert bK {f | f ∈ szE E ∧ Commute f aK}) = ⊤ :=
    c.closure_insert_comp_top ha hb habK
  obtain ⟨-, hmul, -⟩ := OddTransp.localQ_three c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := K)) c.setup haK hbK habK hgen
  obtain ⟨y₁, hy₁Q, hy₁a, y₂, hy₂Q, hy_eq⟩ := hmul yK hyKQ
  refine ⟨(y₁ : G), mem_szQ_iff.mpr ⟨y₁.2, hy₁Q⟩, ?_, (y₂ : G), ?_, ?_⟩
  · exact (commute_coe_iff (H := H) (u := y₁) (v := aK)).mpr hy₁a
  · have hmap : (⁅Q, Subgroup.zpowers bK⁆).map H.subtype =
        ⁅szQ E, Subgroup.zpowers b⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem H.subtype hy₂Q
  · exact congrArg Subtype.val hy_eq

theorem SzCfg.commute_iff_of_mem_comp (c : SzCfg G D d E e n) {a b y : G} (ha : a ∈ E)
    (hb : b ∈ szComp E a) (hy : y ∈ szQ E) : Commute y a ↔ Commute y b := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let aK : K := ⟨a, Subgroup.subset_closure ha⟩
  let bK : K := ⟨b, Subgroup.subset_closure hb.1⟩
  let yK : K := ⟨y, szQ_le_closure E hy⟩
  have haK : aK ∈ szE E := ha
  have hbK : bK ∈ szE E := hb.1
  have hyKQ : yK ∈ Q := (mem_szQ_iff.mp hy).2
  have hbaK : Commute bK aK :=
    (commute_coe_iff (H := H) (u := bK) (v := aK)).mp hb.2
  constructor
  · intro hya
    have hyaK : Commute yK aK :=
      (commute_coe_iff (H := H) (u := yK) (v := aK)).mp hya
    have hcommK : Commute yK bK :=
      commute_of_mem_centralizer_of_mem_comp c haK hbK hbaK hyKQ hyaK
    exact (commute_coe_iff (H := H) (u := yK) (v := bK)).mpr hcommK
  · intro hyb
    have hybK : Commute yK bK :=
      (commute_coe_iff (H := H) (u := yK) (v := bK)).mp hyb
    have habK : Commute aK bK := hbaK.symm
    have hcommK : Commute yK aK :=
      commute_of_mem_centralizer_of_mem_comp c hbK haK habK hyKQ hybK
    exact (commute_coe_iff (H := H) (u := yK) (v := aK)).mpr hcommK


theorem SzCfg.mem_szZ_of_commute (c : SzCfg G D d E e n) {a b y : G} (ha : a ∈ E)
    (hb : b ∈ E) (hab : ¬ Commute a b) (hy : y ∈ szQ E) (hya : Commute y a)
    (hyb : Commute y b) : y ∈ szZ E := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let aK : K := ⟨a, Subgroup.subset_closure ha⟩
  let bK : K := ⟨b, Subgroup.subset_closure hb⟩
  let yK : K := ⟨y, szQ_le_closure E hy⟩
  have haK : aK ∈ szE E := ha
  have hbK : bK ∈ szE E := hb
  have hyKQ : yK ∈ Q := (mem_szQ_iff.mp hy).2
  have habK : ¬ Commute aK bK := fun h =>
    hab ((commute_coe_iff (H := H) (u := aK) (v := bK)).mpr h)
  have hyaK : Commute yK aK :=
    (commute_coe_iff (H := H) (u := yK) (v := aK)).mp hya
  have hybK : Commute yK bK :=
    (commute_coe_iff (H := H) (u := yK) (v := bK)).mp hyb
  have hcenter := mem_center_of_commute c haK hbK habK hyKQ hyaK hybK
  exact mem_szZ_of_mem_center hyKQ hcenter

theorem SzCfg.mem_closure_sup_szZ (c : SzCfg G D d E e n) {a y : G} (ha : a ∈ E)
    (hy : y ∈ szQ E) (hya : Commute y a) :
    y ∈ Subgroup.closure {w | ∃ t ∈ szComp E a, ∃ x ∈ szQ E, w = x * t * x⁻¹ * t⁻¹} ⊔
      szZ E := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let Z : Subgroup K := Subgroup.center K ⊓ Q
  let aK : K := ⟨a, Subgroup.subset_closure ha⟩
  let yK : K := ⟨y, szQ_le_closure E hy⟩
  have haK : aK ∈ szE E := ha
  have hyKQ : yK ∈ Q := (mem_szQ_iff.mp hy).2
  obtain ⟨b, hbE, hbna⟩ := c.exists_not_commute ha
  let bK : K := ⟨b, Subgroup.subset_closure hbE⟩
  have hbK : bK ∈ szE E := hbE
  have habG : ¬ Commute a b := fun h => hbna h.symm
  have habK : ¬ Commute aK bK := fun h =>
    habG ((commute_coe_iff (H := H) (u := aK) (v := bK)).mpr h)
  let Qa : Subgroup K := ⁅Q, Subgroup.zpowers aK⁆
  have hyaK : Commute yK aK :=
    (commute_coe_iff (H := H) (u := yK) (v := aK)).mp hya
  have hyC : yK ∈ Subgroup.centralizer ({aK} : Set K) ⊓ Q :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyaK, hyKQ⟩
  have hC := centralizer_eq_qComp_sup_center c haK hbK habK
  have hC' : Subgroup.centralizer ({aK} : Set K) ⊓ Q = Z ⊔ Qa := by
    rw [hC, sup_comm]
  have hZnorm : Qa ≤ Subgroup.normalizer (Z : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Z.Normal)]
    exact le_top
  have hprod : (↑(Z ⊔ Qa) : Set K) = ↑Z * ↑Qa :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z Qa hZnorm
  have hy' : yK ∈ (↑Z * ↑Qa : Set K) := by
    rw [← hprod, ← hC']
    exact hyC
  obtain ⟨z, hz, q, hq, hy_eq⟩ := Set.mem_mul.mp hy'
  have hzZ : (z : G) ∈ szZ E := mem_szZ_of_mem_center hz.2 hz.1
  have hqMap : (q : G) ∈ ⁅szQ E, Subgroup.zpowers a⁆ := by
    have hmap : (⁅Q, Subgroup.zpowers aK⁆).map H.subtype =
        ⁅szQ E, Subgroup.zpowers a⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem H.subtype hq
  have hW : ⁅szQ E, Subgroup.zpowers a⁆ ≤
      Subgroup.closure {w | ∃ t ∈ szComp E a, ∃ x ∈ szQ E, w = x * t * x⁻¹ * t⁻¹} := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    rcases (mem_zpowers_of_mul_self
      (c.hyp.setup.oddT.mul_self_eq_one (c.subset_commSet ha).1)).mp ht with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [h1, commutatorElement_def]
      exact Subgroup.subset_closure ⟨a, ⟨ha, Commute.refl a⟩, x, hx, rfl⟩
  have hqW : (q : G) ∈
      Subgroup.closure {w | ∃ t ∈ szComp E a, ∃ x ∈ szQ E, w = x * t * x⁻¹ * t⁻¹} :=
    hW hqMap
  have hyG : y = (z : G) * (q : G) := (congrArg Subtype.val hy_eq).symm
  rw [hyG]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzZ) (Subgroup.mem_sup_left hqW)

theorem SzCfg.commutator_mem_szZ (c : SzCfg G D d E e n) {x y : G} (hx : x ∈ szQ E)
    (hy : y ∈ szQ E) : x * y * x⁻¹ * y⁻¹ ∈ szZ E := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let xK : K := ⟨x, szQ_le_closure E hx⟩
  let yK : K := ⟨y, szQ_le_closure E hy⟩
  have hxKQ : xK ∈ Q := (mem_szQ_iff.mp hx).2
  have hyKQ : yK ∈ Q := (mem_szQ_iff.mp hy).2
  obtain ⟨b, hbE, hbna⟩ := c.exists_not_commute c.e_mem
  let aK : K := ⟨e, Subgroup.subset_closure c.e_mem⟩
  let bK : K := ⟨b, Subgroup.subset_closure hbE⟩
  have haK : aK ∈ szE E := c.e_mem
  have hbK : bK ∈ szE E := hbE
  have habK : ¬ Commute aK bK := fun h =>
    (fun h' => hbna h'.symm) ((commute_coe_iff (H := H) (u := aK) (v := bK)).mpr h)
  have hcenter := commutator_mem_center c haK hbK habK hxKQ hyKQ
  have hcommQ : xK * yK * xK⁻¹ * yK⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hxKQ hyKQ) (Q.inv_mem hxKQ)) (Q.inv_mem hyKQ)
  have hz := mem_szZ_of_mem_center hcommQ hcenter
  change ((xK * yK * xK⁻¹ * yK⁻¹ : K) : G) ∈ szZ E
  exact hz

theorem SzCfg.mul_self_mem_szZ (c : SzCfg G D d E e n) {x : G} (hx : x ∈ szQ E) :
    x * x ∈ szZ E := by
  let H : Subgroup G := Subgroup.closure E
  let K := ↥H
  let Q : Subgroup K := CFSG.pCore 2 K
  let xK : K := ⟨x, szQ_le_closure E hx⟩
  have hxKQ : xK ∈ Q := (mem_szQ_iff.mp hx).2
  obtain ⟨b, hbE, hbna⟩ := c.exists_not_commute c.e_mem
  let aK : K := ⟨e, Subgroup.subset_closure c.e_mem⟩
  let bK : K := ⟨b, Subgroup.subset_closure hbE⟩
  have haK : aK ∈ szE E := c.e_mem
  have hbK : bK ∈ szE E := hbE
  have habK : ¬ Commute aK bK := fun h =>
    (fun h' => hbna h'.symm) ((commute_coe_iff (H := H) (u := aK) (v := bK)).mpr h)
  have hcenter := square_mem_center c haK hbK habK hxKQ
  have hsqQ : xK * xK ∈ Q := Q.mul_mem hxKQ hxKQ
  have hz := mem_szZ_of_mem_center hsqQ hcenter
  change ((xK * xK : K) : G) ∈ szZ E
  exact hz


end CFSG.Timmesfeld.Bridge.OddRoot
