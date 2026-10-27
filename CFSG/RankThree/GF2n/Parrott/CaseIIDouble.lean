module

import all CFSG.RankThree.GF2n.Parrott.Setup
public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.GroupTheory.ConjOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott.CaseIIDouble

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G] {z : G}

abbrev D2 (G : Type) [Group G] : Type := G × Multiplicative (ZMod 2)

def zz (z : G) : D2 G := (z, 1)

theorem H_zz (z : G) : H (zz z) = (H z).prod ⊤ := by
  ext x
  rw [Subgroup.mem_prod]
  constructor
  · intro hx
    refine ⟨?_, Subgroup.mem_top x.2⟩
    rw [H, Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Prod.fst hx
  · rintro ⟨hx1, -⟩
    rw [H, Subgroup.mem_centralizer_singleton_iff] at hx1
    rw [H, Subgroup.mem_centralizer_singleton_iff]
    refine Prod.ext ?_ ?_
    · simpa [zz] using hx1
    · simp [zz]

theorem mem_H_of_zz {x : G} {c : Multiplicative (ZMod 2)} (hx : (x, c) ∈ H (zz z)) :
    x ∈ H z := by
  rw [H_zz, Subgroup.mem_prod] at hx
  exact hx.1

theorem mk_mem_H_zz {x : G} {c : Multiplicative (ZMod 2)} (hx : x ∈ H z) :
    (x, c) ∈ H (zz z) := by
  rw [H_zz, Subgroup.mem_prod]
  exact ⟨hx, Subgroup.mem_top c⟩

theorem J_zz (z : G) : J (zz z) = (J z).prod ⊤ := by
  let C2 := Multiplicative (ZMod 2)
  let A : Type := ↥(H z)
  let B : Type := ↥(⊤ : Subgroup C2)
  let K : Subgroup (D2 G) := (H z).prod ⊤
  let e : ↥K ≃* A × B := Subgroup.prodEquiv (H z) ⊤
  have hK : H (zz z) = K := H_zz z
  apply le_antisymm
  · intro y hy
    rw [J, hK, inSubgroup, Subgroup.mem_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Subgroup.mem_prod]
    constructor
    · rw [J, inSubgroup, Subgroup.mem_map]
      let fstA : ↥K →* A := (MonoidHom.fst A B).comp e.toMonoidHom
      have hsurj : Function.Surjective fstA := by
        intro a
        exact ⟨e.symm (a, 1), by simp [fstA]⟩
      have hmap : (pCore 2 ↥K).map fstA ≤ pCore 2 A := by
        apply le_sSup
        refine ⟨(pCore_normal (p := 2) (G := ↥K)).map fstA hsurj, ?_⟩
        exact IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥K)) fstA
      have hmem : fstA k ∈ pCore 2 A := hmap (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      exact ⟨fstA k, hmem, rfl⟩
    · exact (Subgroup.mem_prod.mp k.2).2
  · rintro y ⟨hyJ, hyB⟩
    rw [J, hK, inSubgroup, Subgroup.mem_map]
    have hyJ' : y.1 ∈ Subgroup.map (H z).subtype (pCore 2 (H z)) := by
      simpa [J, inSubgroup] using hyJ
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hyJ'
    have hyK : y ∈ K := by
      rw [Subgroup.mem_prod]
      exact ⟨hay ▸ a.2, hyB⟩
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    let Q : Subgroup ↥K := ((pCore 2 A).prod (⊤ : Subgroup B)).comap e.toMonoidHom
    have hQnorm : Q.Normal :=
      (Subgroup.prod_normal (pCore 2 A) (⊤ : Subgroup B)).comap e.toMonoidHom
    have hC2card : Nat.card C2 = 2 := by
      simp [C2, Nat.card_zmod]
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    have hpProd : IsPGroup 2 ↥((pCore 2 A).prod (⊤ : Subgroup B)) := by
      apply IsPGroup.of_card (n := n + 1)
      rw [Nat.card_congr (Subgroup.prodEquiv (pCore 2 A) (⊤ : Subgroup B)).toEquiv,
        Nat.card_prod, hn]
      have htop : Nat.card ↥(⊤ : Subgroup B) = 2 := by
        rw [Subgroup.card_top]
        simpa [B] using hC2card
      rw [htop, pow_succ]
    have hQmap : Q.map e.toMonoidHom = (pCore 2 A).prod (⊤ : Subgroup B) := by
      rw [Subgroup.map_comap_eq]
      rw [show e.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.mpr e.surjective,
        top_inf_eq]
    have hQp : IsPGroup 2 ↥Q :=
      hpProd.of_equiv ((Subgroup.equivMapOfInjective Q e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hQmap)).symm
    have hQle : Q ≤ pCore 2 ↥K := le_sSup ⟨hQnorm, hQp⟩
    apply hQle
    rw [Subgroup.mem_comap, Subgroup.mem_prod]
    constructor
    · have hk1 : (e ⟨y, hyK⟩).1 = a := by
        apply Subtype.ext
        exact hay.symm
      simpa [hk1] using ha
    · exact Subgroup.mem_top _

theorem mem_J_of_zz {x : G} {c : Multiplicative (ZMod 2)} (hx : (x, c) ∈ J (zz z)) :
    x ∈ J z := by
  rw [J_zz, Subgroup.mem_prod] at hx
  exact hx.1

theorem mk_mem_J_zz {x : G} {c : Multiplicative (ZMod 2)} (hx : x ∈ J z) :
    (x, c) ∈ J (zz z) := by
  rw [J_zz, Subgroup.mem_prod]
  exact ⟨hx, Subgroup.mem_top c⟩

theorem centerIn_J_zz (z : G) : centerIn (J (zz z)) = (centerIn (J z)).prod ⊤ := by
  rw [J_zz]
  ext x
  simp only [centerIn, Subgroup.mem_inf, Subgroup.mem_prod]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hxcent⟩
    refine ⟨⟨hx1, ?_⟩, hx2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp hxcent (a, 1)
      (Subgroup.mem_prod.mpr ⟨ha, Subgroup.mem_top 1⟩)
    exact congrArg Prod.fst h
  · rintro ⟨⟨hx1, hxcent1⟩, hx2⟩
    refine ⟨⟨hx1, hx2⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y.1 ∈ J z := (Subgroup.mem_prod.mp hy).1
    have h := Subgroup.mem_centralizer_iff.mp hxcent1 y.1 hy1
    exact Prod.ext h (mul_comm _ _)

theorem pPrimeCore_D2 : pPrimeCore 2 (D2 G) = (pPrimeCore 2 G).prod ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C2 := Multiplicative (ZMod 2)
  have hC2card : Nat.card C2 = 2 := by
    simp [C2, Nat.card_zmod]
  have hC2 : pPrimeCore 2 C2 = ⊥ := by
    rw [pPrimeCore_eq_bot_iff]
    intro K hK hcop
    have hdvd : Nat.card ↥K ∣ Nat.card C2 := Subgroup.card_subgroup_dvd_card K
    rw [hC2card] at hdvd
    have hcard : Nat.card ↥K = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hcop
        norm_num at hcop
    exact Subgroup.eq_bot_of_card_eq K hcard
  have hcard : Nat.card ↥((pPrimeCore 2 G).prod (⊥ : Subgroup C2)) =
      Nat.card ↥(pPrimeCore 2 G) := by
    rw [Nat.card_congr (Subgroup.prodEquiv (pPrimeCore 2 G) (⊥ : Subgroup C2)).toEquiv,
      Nat.card_prod]
    simp
  apply le_antisymm
  · rw [Subgroup.le_prod_iff]
    constructor
    · change Subgroup.map (MonoidHom.fst G C2) (pPrimeCore 2 (D2 G)) ≤
        sSup {K : Subgroup G | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}
      apply le_sSup
      exact ⟨(pPrimeCore_normal (p := 2) (G := D2 G)).map
          (MonoidHom.fst G C2) (by intro a; exact ⟨(a, 1), rfl⟩),
          Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _)
            (pPrimeCore_coprime_card (p := 2) (G := D2 G))⟩
    · rw [← hC2]
      change Subgroup.map (MonoidHom.snd G C2) (pPrimeCore 2 (D2 G)) ≤
        sSup {K : Subgroup C2 | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}
      apply le_sSup
      exact ⟨(pPrimeCore_normal (p := 2) (G := D2 G)).map
          (MonoidHom.snd G C2) (by intro b; exact ⟨(1, b), rfl⟩),
          Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _)
            (pPrimeCore_coprime_card (p := 2) (G := D2 G))⟩
  · change (pPrimeCore 2 G).prod (⊥ : Subgroup C2) ≤
      sSup {K : Subgroup (D2 G) | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}
    apply le_sSup
    refine ⟨Subgroup.prod_normal (pPrimeCore 2 G) (⊥ : Subgroup C2), ?_⟩
    rw [hcard]
    exact pPrimeCore_coprime_card (p := 2) (G := G)

theorem H_zz_sup_pPrimeCore_eq_top_iff (z : G) :
    H (zz z) ⊔ pPrimeCore 2 (D2 G) = ⊤ ↔ H z ⊔ pPrimeCore 2 G = ⊤ := by
  let C2 := Multiplicative (ZMod 2)
  have hPnorm : ((pPrimeCore 2 G).prod (⊥ : Subgroup C2)).Normal :=
    Subgroup.prod_normal (pPrimeCore 2 G) (⊥ : Subgroup C2)
  have hsup : (H z).prod ⊤ ⊔ (pPrimeCore 2 G).prod (⊥ : Subgroup C2) =
      (H z ⊔ pPrimeCore 2 G).prod ⊤ := by
    apply le_antisymm
    · exact sup_le (Subgroup.prod_mono le_sup_left le_rfl)
        (Subgroup.prod_mono le_sup_right bot_le)
    · intro x hx
      rw [Subgroup.mem_prod] at hx
      rw [Subgroup.mem_sup_of_normal_right]
      obtain ⟨h, hh, p, hp, hx1⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := H z) (t := pPrimeCore 2 G)).mp hx.1
      refine ⟨(h, x.2), ?_, (p, 1), ?_, ?_⟩
      · rw [Subgroup.mem_prod]; exact ⟨hh, Subgroup.mem_top _⟩
      · rw [Subgroup.mem_prod]; exact ⟨hp, by simp⟩
      · ext <;> simp [hx1]
  rw [H_zz, pPrimeCore_D2, hsup]
  constructor
  · intro h
    apply eq_top_iff.mpr
    intro g _
    have htop : ((g, (1 : Multiplicative (ZMod 2))) : D2 G) ∈ (⊤ : Subgroup (D2 G)) :=
      Subgroup.mem_top _
    have hmem : ((g, (1 : Multiplicative (ZMod 2))) : D2 G) ∈
        (H z ⊔ pPrimeCore 2 G).prod ⊤ := h ▸ htop
    exact (Subgroup.mem_prod.mp hmem).1
  · intro h
    rw [h, Subgroup.top_prod_top]

def fstH (z : G) : ↥(H (zz z)) →* ↥(H z) where
  toFun x := ⟨(x : D2 G).1, mem_H_of_zz x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intro a b; ext; rfl

noncomputable def quotientMapZZ (z : G) :
    ↥(H (zz z)) →* (↥(H z) ⧸ (J z).subgroupOf (H z)) :=
  (QuotientGroup.mk' ((J z).subgroupOf (H z))).comp (fstH z)

theorem quotientMapZZ_surjective (z : G) : Function.Surjective (quotientMapZZ z) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((J z).subgroupOf (H z)) y
  refine ⟨⟨((x : G), 1), mk_mem_H_zz x.2⟩, ?_⟩
  rfl

theorem quotientMapZZ_ker (z : G) :
    (quotientMapZZ z).ker = (J (zz z)).subgroupOf (H (zz z)) := by
  ext x
  rw [MonoidHom.mem_ker, quotientMapZZ, MonoidHom.comp_apply]
  change QuotientGroup.mk ((fstH z) x) = 1 ↔ x ∈ (J (zz z)).subgroupOf (H (zz z))
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    rw [J_zz, Subgroup.mem_prod]
    exact ⟨by simpa [fstH] using hx, Subgroup.mem_top _⟩
  · intro hx
    rw [J_zz, Subgroup.mem_prod] at hx
    simpa [fstH] using hx.1

noncomputable def quotientEquivZZ (z : G) :
    (↥(H (zz z)) ⧸ (J (zz z)).subgroupOf (H (zz z))) ≃*
      (↥(H z) ⧸ (J z).subgroupOf (H z)) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientMapZZ_ker z).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientMapZZ z)
      (quotientMapZZ_surjective z))

theorem quotientEquivZZ_mk (z : G) (x : G) (c : Multiplicative (ZMod 2))
    (hx : (x, c) ∈ H (zz z)) :
    quotientEquivZZ z (QuotientGroup.mk ⟨(x, c), hx⟩) =
      QuotientGroup.mk ⟨x, mem_H_of_zz hx⟩ := by
  rw [quotientEquivZZ, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

noncomputable def quotientDataZZ
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) :
    QuotientData (z := zz z) (J_subgroupOf_normal (zz z)) :=
  ⟨D.X, D.instX, D.lie, (quotientEquivZZ z).trans D.iso⟩

theorem qH_zz
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) (x : G)
    (c : Multiplicative (ZMod 2)) (hx : (x, c) ∈ H (zz z)) :
    qH (quotientDataZZ D) ⟨(x, c), hx⟩ = qH D ⟨x, mem_H_of_zz hx⟩ := by
  have hcomp : QuotientData.toQA45 (quotientDataZZ D) =
      (quotientEquivZZ z).trans (QuotientData.toQA45 D) := by
    unfold QuotientData.toQA45
    rfl
  unfold qH
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hcomp, MulEquiv.trans_apply]
  change D.toQA45 (quotientEquivZZ z (QuotientGroup.mk ⟨(x, c), hx⟩)) =
    D.toQA45 (QuotientGroup.mk ⟨x, mem_H_of_zz hx⟩)
  rw [quotientEquivZZ_mk]

theorem parrottHyp_zz (h : Tim79a.ParrottHypA z) : Tim79a.ParrottHyp (zz z) := by
  let C2 := Multiplicative (ZMod 2)
  let T : Subgroup (D2 G) := (⊥ : Subgroup G).prod (⊤ : Subgroup C2)
  let F : Subgroup (D2 G) := (J z).prod (⊥ : Subgroup C2)
  have hC2card : Nat.card C2 = 2 := by
    simp [C2, Nat.card_zmod]
  have hcommF : ⁅F, F⁆ = (Subgroup.zpowers z).prod (⊥ : Subgroup C2) := by
    change ⁅(J z).prod (⊥ : Subgroup C2), (J z).prod (⊥ : Subgroup C2)⁆ = _
    rw [Subgroup.commutator_prod_prod, h.commutator]
    congr 1
    simp
  have hcenterF : (Subgroup.center ↥F).map F.subtype = (centerIn (J z)).prod (⊥ : Subgroup C2) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_prod]
      constructor
      · rw [centerIn]
        refine ⟨(Subgroup.mem_prod.mp c.2).1, ?_⟩
        change (F.subtype c).1 ∈ Subgroup.centralizer (J z : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hmem : ((a, 1) : D2 G) ∈ F :=
          Subgroup.mem_prod.mpr ⟨ha, Subgroup.mem_bot.mpr rfl⟩
        have h := Subgroup.mem_center_iff.mp hc ⟨((a, 1) : D2 G), hmem⟩
        exact congrArg (fun x : ↥F => (x : D2 G).1) h
      · exact (Subgroup.mem_prod.mp c.2).2
    · rintro ⟨hy1, hy2⟩
      rw [centerIn] at hy1
      obtain ⟨hy1J, hy1c⟩ := hy1
      refine ⟨⟨y, Subgroup.mem_prod.mpr ⟨hy1J, hy2⟩⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hq := Subgroup.mem_prod.mp q.2
      have hq2 : (q : D2 G).2 = 1 := Subgroup.mem_bot.mp hq.2
      have hcomm := Subgroup.mem_centralizer_iff.mp hy1c (q : D2 G).1 hq.1
      exact Prod.ext hcomm (by simp [Subgroup.coe_mul, hq2])
  have hFext : IsExtraspecial2 F := by
    have hp : IsPGroup 2 F := by
      apply IsPGroup.of_card (n := 9)
      rw [show F = (J z).prod (⊥ : Subgroup C2) from rfl,
        Nat.card_congr (Subgroup.prodEquiv (J z) (⊥ : Subgroup C2)).toEquiv,
        Nat.card_prod, h.card_J]
      simp
    refine ⟨hp, ?_, ?_⟩
    · rw [hcommF, hcenterF, centerIn_J_eq_zpowers_A h]
    · rw [hcommF, Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers z) (⊥ : Subgroup C2)).toEquiv,
        Nat.card_prod, Nat.card_zpowers, orderOf_z_A h]
      simp
  have hTcard : Nat.card T = 2 := by
    rw [show T = (⊥ : Subgroup G).prod (⊤ : Subgroup C2) from rfl,
      Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup G) (⊤ : Subgroup C2)).toEquiv,
      Nat.card_prod, Subgroup.card_top, hC2card]
    simp
  have hTF : T ⊓ F = ⊥ := by
    rw [show T = (⊥ : Subgroup G).prod (⊤ : Subgroup C2) from rfl,
      show F = (J z).prod (⊥ : Subgroup C2) from rfl]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_bot, Subgroup.mem_top,
      and_true, true_and, Prod.mk.eta]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact Prod.ext h1 h2
    · intro hy
      subst hy
      simp
  have hTcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f := by
    intro t ht f hf
    have ht1 : t.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp ht).1
    have hf2 : f.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hf).2
    ext <;> simp [ht1, hf2]
  have hTFsup : T ⊔ F = J (zz z) := by
    rw [show T = (⊥ : Subgroup G).prod (⊤ : Subgroup C2) from rfl,
      show F = (J z).prod (⊥ : Subgroup C2) from rfl, J_zz]
    apply le_antisymm
    · exact sup_le (Subgroup.prod_mono bot_le le_rfl) (Subgroup.prod_mono le_rfl bot_le)
    · intro x hx
      rw [Subgroup.mem_prod] at hx
      have hx_eq : ((1 : G), x.2) * ((x.1, (1 : C2)) : D2 G) = x := by
        ext <;> simp
      rw [← hx_eq]
      exact Subgroup.mul_mem_sup
        (Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, hx.2⟩)
        (Subgroup.mem_prod.mpr ⟨hx.1, Subgroup.mem_bot.mpr rfl⟩)
  have hcommJ : ⁅J (zz z), J (zz z)⁆ = Subgroup.zpowers (zz z) := by
    rw [J_zz, Subgroup.commutator_prod_prod, h.commutator]
    have htop : ⁅(⊤ : Subgroup C2), (⊤ : Subgroup C2)⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr (by infer_instance)
    rw [htop]
    ext y
    rw [Subgroup.mem_prod]
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy1
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [Subgroup.mem_bot] at hy2
      ext <;> simp [zz, hk, hy2]
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine ⟨Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩, ?_⟩
      · simpa [zz] using congrArg Prod.fst hk
      · have h2 := congrArg Prod.snd hk
        simpa [zz] using h2.symm
  have hcent : H (zz z) ⊓ Subgroup.centralizer (J (zz z) : Set (D2 G)) ≤ J (zz z) := by
    intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxH1 : x.1 ∈ H z := mem_H_of_zz hxH
    have hxC1 : x.1 ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := Subgroup.mem_centralizer_iff.mp hxC (a, 1) (mk_mem_J_zz ha)
      exact congrArg Prod.fst h
    rw [J_zz, Subgroup.mem_prod]
    exact ⟨h.centralizer_le ⟨hxH1, hxC1⟩, Subgroup.mem_top x.2⟩
  let D : QuotientData (z := z) (J_subgroupOf_normal z) := Classical.choice h.quotient
  refine ⟨?_, ⟨T, F, hTcard, hFext, ?_, hTF, hTcomm, hTFsup⟩, hcommJ, hcent, ?_⟩
  · rw [zz, Prod.orderOf, orderOf_z_A h]
    simp
  · rw [show F = (J z).prod (⊥ : Subgroup C2) from rfl,
      Nat.card_congr (Subgroup.prodEquiv (J z) (⊥ : Subgroup C2)).toEquiv,
      Nat.card_prod, h.card_J]
    simp
  · exact ⟨J_subgroupOf_normal (zz z), D.X, D.instX, D.lie, ⟨(quotientEquivZZ z).trans D.iso⟩⟩

theorem qVZMod_zz_eq_zero_iff (h2 : Tim79a.ParrottHyp (zz z)) (j : G)
    (c : Multiplicative (ZMod 2)) (hj : (j, c) ∈ J (zz z)) :
    qVZMod h2 (QuotientV.pi (zz z) ⟨(j, c), hj⟩) = 0 ↔ j * j = 1 := by
  have hc2 : ∀ d : Multiplicative (ZMod 2), d * d = 1 := by
    intro d
    revert d
    decide
  have hzero : qVZMod h2 (QuotientV.pi (zz z) ⟨(j, c), hj⟩) = 0 ↔
      qV h2 (QuotientV.pi (zz z) ⟨(j, c), hj⟩) = 1 := by
    constructor
    · intro h
      apply (zpowersEquivZModTwo h2).injective
      apply Multiplicative.toAdd.injective
      rw [qVZMod] at h
      simpa using h
    · intro h
      rw [qVZMod, h, map_one]
      rfl
  rw [hzero, qV_pi]
  constructor
  · intro hq
    have h1 : ((qJ h2 ⟨(j, c), hj⟩ : Subgroup.zpowers (zz z)) : D2 G) = 1 := by
      rw [hq]
      rfl
    rw [qJ_coe] at h1
    have h2' := congrArg Prod.fst h1
    simpa [pow_two] using h2'
  · intro hjj
    apply Subtype.ext
    rw [qJ_coe, pow_two]
    exact Prod.ext hjj (hc2 c)

theorem map_centralizerJ_zz (x : G) (c : Multiplicative (ZMod 2))
    (hx : (x, c) ∈ H (zz z)) :
    (centralizerJ ⟨(x, c), hx⟩).map (J (zz z)).subtype =
      ((centralizerJ ⟨x, mem_H_of_zz hx⟩).map (J z).subtype).prod ⊤ := by
  ext y
  constructor
  · rintro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Subgroup.mem_prod]
    constructor
    · rw [Subgroup.mem_map]
      refine ⟨⟨(j : D2 G).1, mem_J_of_zz j.2⟩, ?_, rfl⟩
      rw [mem_centralizerJ_iff]
      exact congrArg Prod.fst (mem_centralizerJ_iff.mp hj)
    · exact Subgroup.mem_top _
  · rintro ⟨hy1, hy2⟩
    change y.1 ∈ Subgroup.map (J z).subtype (centralizerJ ⟨x, mem_H_of_zz hx⟩) at hy1
    obtain ⟨j, hj, hj_eq⟩ := Subgroup.mem_map.mp hy1
    have hj_eq' : (j : G) = y.1 := by
      simpa only [Subgroup.subtype_apply] using hj_eq
    rw [Subgroup.mem_map]
    refine ⟨⟨y, ?_⟩, ?_, rfl⟩
    · rw [J_zz, Subgroup.mem_prod]
      exact ⟨by rw [← hj_eq']; exact j.2, hy2⟩
    · rw [mem_centralizerJ_iff]
      refine Prod.ext ?_ ?_
      · change y.1 * x = x * y.1
        rw [← hj_eq']
        exact mem_centralizerJ_iff.mp hj
      · change y.2 * c = c * y.2
        exact mul_comm _ _

theorem orderOf_fst_of_orderOf_prod_eq_three {b : G} {c : Multiplicative (ZMod 2)}
    (h : orderOf ((b, c) : D2 G) = 3) : orderOf b = 3 := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hc2 : orderOf c ∣ 2 := by
    simpa [hcard] using orderOf_dvd_natCard c
  have hpd : (orderOf b).lcm (orderOf c) = 3 := by
    rw [← h, Prod.orderOf]
  have hb3 : orderOf b ∣ 3 := by
    rw [← hpd]
    exact Nat.dvd_lcm_left _ _
  have hc3 : orderOf c ∣ 3 := by
    rw [← hpd]
    exact Nat.dvd_lcm_right _ _
  have hc1 : orderOf c = 1 := by
    have hdvd : orderOf c ∣ 1 := by
      have := Nat.dvd_gcd hc2 hc3
      simpa using this
    exact Nat.dvd_one.mp hdvd
  have hb_ne1 : orderOf b ≠ 1 := by
    intro hb1
    have hb_eq1 : b = 1 := orderOf_eq_one_iff.mp hb1
    have hc_eq1 : c = 1 := orderOf_eq_one_iff.mp hc1
    rw [hb_eq1, hc_eq1] at h
    rw [show ((1 : G), (1 : Multiplicative (ZMod 2))) = (1 : D2 G) from rfl,
      orderOf_one] at h
    norm_num at h
  rcases (Nat.dvd_prime Nat.prime_three).mp hb3 with hb | hb
  · exact absurd hb hb_ne1
  · exact hb

theorem prod_top_injective {A B : Subgroup G}
    (h : A.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) =
      B.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) : A = B := by
  ext a
  constructor
  · intro ha
    have hmem : (a, (1 : Multiplicative (ZMod 2))) ∈
        A.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :=
      Subgroup.mem_prod.mpr ⟨ha, Subgroup.mem_top 1⟩
    rw [h] at hmem
    exact (Subgroup.mem_prod.mp hmem).1
  · intro ha
    have hmem : (a, (1 : Multiplicative (ZMod 2))) ∈
        B.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :=
      Subgroup.mem_prod.mpr ⟨ha, Subgroup.mem_top 1⟩
    rw [← h] at hmem
    exact (Subgroup.mem_prod.mp hmem).1

theorem exists_conj_of_qH_eq_order_three
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) {a b : ↥(H z)}
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hq : qH D a = qH D b) :
    ∃ j : ↥(H z), (j : G) ∈ J z ∧ j * b * j⁻¹ = a := by
  have hcos : a * b⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨j, hj, hjconj⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mul_inv_mem
    (isPGroup_J_subgroupOf (z := z)) ha hb hcos
  exact ⟨j, Subgroup.mem_subgroupOf.mp hj, hjconj⟩

theorem parrottEqualityBranch_zz_iff
    (h2 : Tim79a.ParrottHyp (zz z))
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) :
    ParrottEqualityBranch (z := zz z) (D := quotientDataZZ D) h2 ↔
      ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
        qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
        centralizerJ (sigma1Nine D) = centralizerJ σ₂ := by
  let aZ : ↥(H (zz z)) := sigma1Nine (z := zz z) (D := quotientDataZZ D)
  let a' : ↥(H z) := sigma1Nine (z := z) D
  let a1 : G := (aZ : D2 G).1
  let a2 : Multiplicative (ZMod 2) := (aZ : D2 G).2
  have ha : (a1, a2) ∈ H (zz z) := aZ.2
  have ha_order : orderOf aZ = 3 := sigma1Nine_order (z := zz z) (D := quotientDataZZ D)
  have ha_prod_order : orderOf ((a1, a2) : D2 G) = 3 := by
    rw [Subgroup.orderOf_coe aZ]
    exact ha_order
  have ha1_order : orderOf a1 = 3 := orderOf_fst_of_orderOf_prod_eq_three ha_prod_order
  let a1' : ↥(H z) := ⟨a1, mem_H_of_zz ha⟩
  have ha1'_order : orderOf a1' = 3 := by
    rw [← Subgroup.orderOf_coe a1']
    exact ha1_order
  have hq_a1' : qH D a1' = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) := by
    rw [← qH_zz (z := z) D a1 a2 ha]
    exact qH_sigma1Nine (z := zz z) (D := quotientDataZZ D)
  have hq_eq : qH D a1' = qH D a' := by
    rw [hq_a1', qH_sigma1Nine (z := z) (D := D)]
  obtain ⟨j, hjJ, hjconj⟩ := exists_conj_of_qH_eq_order_three (z := z) D ha1'_order
    (sigma1Nine_order (z := z) D) hq_eq
  have hqj : qH D j = 1 := (J_mem_iff D j).mp (Subgroup.mem_subgroupOf.mpr hjJ)
  have hqjinv : qH D j⁻¹ = 1 := by rw [map_inv, hqj, inv_one]
  have hCJ_conj : centralizerJ a1' = (centralizerJ a').map (conjJ' z j).toMonoidHom := by
    have h := map_centralizerJ_conj (z := z) (g := j) (x := a')
    rw [hjconj] at h
    exact h.symm
  constructor
  · intro hEq
    obtain ⟨σ₂, hσ₂ord, hσ₂q, hσ₂CJ⟩ := hEq
    let b : G := (σ₂ : D2 G).1
    let c2 : Multiplicative (ZMod 2) := (σ₂ : D2 G).2
    have hσ : (b, c2) ∈ H (zz z) := σ₂.2
    have hσ_prod_order : orderOf ((b, c2) : D2 G) = 3 := by
      rw [Subgroup.orderOf_coe σ₂]
      exact hσ₂ord
    have hb_order : orderOf b = 3 := orderOf_fst_of_orderOf_prod_eq_three hσ_prod_order
    let b' : ↥(H z) := ⟨b, mem_H_of_zz hσ⟩
    have hb'_order : orderOf b' = 3 := by
      rw [← Subgroup.orderOf_coe b']
      exact hb_order
    have hq_b' : qH D b' = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
      rw [← qH_zz (z := z) D b c2 hσ]
      exact hσ₂q
    have hprod : ((centralizerJ a1').map (J z).subtype).prod
        (⊤ : Subgroup (Multiplicative (ZMod 2))) =
        ((centralizerJ b').map (J z).subtype).prod ⊤ := by
      change ((centralizerJ ⟨a1, mem_H_of_zz ha⟩).map (J z).subtype).prod ⊤ =
        ((centralizerJ ⟨b, mem_H_of_zz hσ⟩).map (J z).subtype).prod ⊤
      rw [← map_centralizerJ_zz (z := z) a1 a2 ha,
        ← map_centralizerJ_zz (z := z) b c2 hσ, hσ₂CJ]
    have hCJ : centralizerJ a1' = centralizerJ b' :=
      Subgroup.map_injective (J z).subtype_injective (prod_top_injective hprod)
    let b'' : ↥(H z) := j⁻¹ * b' * j
    have hb''_CJ : centralizerJ b'' = centralizerJ a' := by
      have h1 : (centralizerJ a1').map (conjJ' z j⁻¹).toMonoidHom = centralizerJ a' := by
        have h := map_centralizerJ_conj (z := z) (g := j⁻¹) (x := a1')
        have hconj' : j⁻¹ * a1' * j⁻¹⁻¹ = a' := by
          calc j⁻¹ * a1' * j⁻¹⁻¹ = j⁻¹ * (j * a' * j⁻¹) * j := by
                rw [hjconj, inv_inv]
            _ = a' := by group
        rw [hconj'] at h
        exact h
      have h2 : (centralizerJ a1').map (conjJ' z j⁻¹).toMonoidHom = centralizerJ b'' := by
        rw [hCJ]
        have h := map_centralizerJ_conj (z := z) (g := j⁻¹) (x := b')
        rw [show j⁻¹ * b' * j⁻¹⁻¹ = b'' from by rw [inv_inv]] at h
        exact h
      rw [h1] at h2
      exact h2.symm
    refine ⟨b'', ?_, ?_, ?_⟩
    · rw [show b'' = (MulAut.conj j⁻¹) b' from by rw [MulAut.conj_apply, inv_inv]]
      rw [MulEquiv.orderOf_eq]
      exact hb'_order
    · calc qH D b'' = qH D (j⁻¹ * b' * j) := rfl
        _ = qH D j⁻¹ * qH D b' * qH D j := by rw [map_mul, map_mul]
        _ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
            rw [hqjinv, hq_b', hqj]
            group
    · exact hb''_CJ.symm
  · rintro ⟨b, hb_order, hqb, hCJ⟩
    let b' : ↥(H z) := j * b * j⁻¹
    have hb'_order : orderOf b' = 3 := by
      rw [show b' = (MulAut.conj j) b from by rw [MulAut.conj_apply]]
      rw [MulEquiv.orderOf_eq]
      exact hb_order
    have hq_b' : qH D b' = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
      calc qH D b' = qH D j * qH D b * qH D j⁻¹ := by rw [map_mul, map_mul]
        _ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
            rw [hqj, hqb, hqjinv]
            group
    have hCJ_b' : centralizerJ b' = (centralizerJ a').map (conjJ' z j).toMonoidHom := by
      have h := map_centralizerJ_conj (z := z) (g := j) (x := b)
      rw [← hCJ] at h
      exact h.symm
    have hb'a1 : centralizerJ b' = centralizerJ a1' := by
      rw [hCJ_b', hCJ_conj]
    let σ₂ : ↥(H (zz z)) := ⟨((b' : G), (1 : Multiplicative (ZMod 2))), mk_mem_H_zz b'.2⟩
    refine ⟨σ₂, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe σ₂]
      change orderOf (((b' : G), (1 : Multiplicative (ZMod 2))) : D2 G) = 3
      rw [Prod.orderOf]
      simpa using hb'_order
    · rw [show qH (quotientDataZZ D) σ₂ = qH D b' from
        qH_zz (z := z) D (b' : G) (1 : Multiplicative (ZMod 2)) (mk_mem_H_zz b'.2)]
      exact hq_b'
    · apply Subgroup.map_injective (J (zz z)).subtype_injective
      rw [map_centralizerJ_zz (z := z) (b' : G) 1 (mk_mem_H_zz b'.2),
        map_centralizerJ_zz (z := z) a1 a2 ha, hb'a1]

end CFSG.RankThree.GF2n.Parrott.CaseIIDouble
