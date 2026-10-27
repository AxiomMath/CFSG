module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Lift

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_lift_normalizer148 (hA3 : IsPGroup 3 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {n : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hn : n ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ∃ (w : G) (hw : w ∈ Y ⊔ A), w ∈ Subgroup.normalizer (A : Set G) ∧
      QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩ = n := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) n
  obtain ⟨k, hk⟩ := hA3.exists_card_eq
  set N := pPrimeCoreOf 3 Y
  have hNY : N ≤ Y ⊔ A := (pPrimeCoreOf_le 3 Y).trans le_sup_left
  have hNcop : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Y
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  set P : Subgroup G := N ⊔ A
  have hNP : N ≤ P := le_sup_left
  have hAP : A ≤ P := le_sup_right
  have hPmul : ∀ x ∈ P, ∃ y ∈ N, ∃ z ∈ A, y * z = x := by
    intro x hx
    have hx' : x ∈ (N : Set G) * (A : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N A hAN]
      exact hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hx'
    exact ⟨y, hy, z, hz, hyz⟩
  have hdisj : Disjoint (N.subgroupOf P) (A.subgroupOf P) := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxA
    obtain ⟨j, hj⟩ := hA3 ⟨(x : G), Subgroup.mem_subgroupOf.mp hxA⟩
    have hj' : (x : G) ^ 3 ^ j = 1 := congrArg Subtype.val hj
    exact Subtype.ext
      (eq_one_of_pow_three_pow_eq_one148 hNcop (Subgroup.mem_subgroupOf.mp hxN) hj')
  have hcover : ((N.subgroupOf P : Subgroup P) : Set P) *
      ((A.subgroupOf P : Subgroup P) : Set P) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, z, hz, hyz⟩ := hPmul (x : G) x.2
    exact Set.mem_mul.mpr ⟨⟨y, hNP hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨z, hAP hz⟩,
      Subgroup.mem_subgroupOf.mpr hz, Subtype.ext hyz⟩
  have hcompA : (N.subgroupOf P).IsComplement' (A.subgroupOf P) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hcover
  have hidxA : (A.subgroupOf P).index = Nat.card N := by
    rw [hcompA.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv]
  have h3A : ¬ 3 ∣ (A.subgroupOf P).index := by
    rw [hidxA]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hNcop
  have hBP : ∀ x ∈ A, (m : G) * x * (m : G)⁻¹ ∈ P := by
    intro x hx
    have hmxM : (m : G) * x * (m : G)⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem m.2 (Subgroup.mem_sup_right hx)) ((Y ⊔ A).inv_mem m.2)
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (alpha148 A Y x hx)).mp
      (alpha148_mem_img148 hx)
    have h3 : QuotientGroup.mk' (ker148 A Y) m * alpha148 A Y x hx *
        (QuotientGroup.mk' (ker148 A Y) m)⁻¹ =
        QuotientGroup.mk' (ker148 A Y) ⟨(m : G) * x * (m : G)⁻¹, hmxM⟩ := by
      rw [alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h3, mem_img148_iff] at h1
    obtain ⟨g, hgY, hgA, hg⟩ := h1
    have hk' : g⁻¹ * ((m : G) * x * (m : G)⁻¹) ∈ N := mk'_ker148_eq_iff.mp hg
    have e : (m : G) * x * (m : G)⁻¹ = g * (g⁻¹ * ((m : G) * x * (m : G)⁻¹)) :=
      (mul_inv_cancel_left _ _).symm
    rw [e]
    exact P.mul_mem (Subgroup.mem_sup_right hgA) (Subgroup.mem_sup_left hk')
  set B : Subgroup G := A.map (MulAut.conj (m : G)).toMonoidHom with hBdef
  have hBle : B ≤ P := by
    rw [hBdef]
    rintro _ ⟨x, hx, rfl⟩
    exact hBP x hx
  have hBcard : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := k) (by rw [hBcard]; exact hk)
  have hcardB : Nat.card (B.subgroupOf P) = Nat.card (A.subgroupOf P) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hBcard]
  have hidxB : (B.subgroupOf P).index = (A.subgroupOf P).index := by
    have h1 := (B.subgroupOf P).card_mul_index
    have h2 := (A.subgroupOf P).card_mul_index
    rw [hcardB] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have h3B : ¬ 3 ∣ (B.subgroupOf P).index := by
    rw [hidxB]
    exact h3A
  have hSA3 : IsPGroup 3 (A.subgroupOf P) := hA3.comap_subtype
  have hSB3 : IsPGroup 3 (B.subgroupOf P) := hB3.comap_subtype
  haveI : Finite (Subgroup P) :=
    Finite.of_injective (fun H : Subgroup P => (H : Set P)) SetLike.coe_injective
  haveI : Finite (Sylow 3 P) :=
    Finite.of_injective (fun Q : Sylow 3 P => (Q : Subgroup P)) fun Q R h => Sylow.ext h
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (↥P) (IsPGroup.toSylow hSA3 h3A)
    (IsPGroup.toSylow hSB3 h3B)
  have hsub : MulAut.conj s • (A.subgroupOf P) = B.subgroupOf P := by
    have h1 := congrArg Sylow.toSubgroup hs
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hfwd : ∀ x ∈ A, (s : G) * x * (s : G)⁻¹ ∈ B := by
    intro x hx
    have h1 : MulAut.conj s ⟨x, hAP hx⟩ ∈ B.subgroupOf P := by
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul (⟨x, hAP hx⟩ : ↥P) (MulAut.conj s)
        (A.subgroupOf P) (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨o, hoN, z, hzA, hoz⟩ := hPmul (s : G) s.2
  have hoY : o ∈ Y ⊔ A := hNY hoN
  have hCoB : A.map (MulAut.conj o).toMonoidHom ≤ B := by
    rw [hBdef]
    rintro _ ⟨x', hx', rfl⟩
    have hx : z⁻¹ * x' * z ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hzA) hx') hzA
    have h1 := hfwd _ hx
    have h2 : (s : G) * (z⁻¹ * x' * z) * (s : G)⁻¹ = o * x' * o⁻¹ := by
      rw [← hoz]
      group
    change o * x' * o⁻¹ ∈ B
    rw [← h2]
    exact h1
  have hCoEq : A.map (MulAut.conj o).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hCoB (le_of_eq (by
      rw [hBcard, Subgroup.card_map_of_injective (MulAut.conj o).injective]))
  have hwY : o⁻¹ * (m : G) ∈ Y ⊔ A := (Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem hoY) m.2
  refine ⟨o⁻¹ * (m : G), hwY, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hmh : (m : G) * h * (m : G)⁻¹ ∈ B := by
        rw [hBdef]
        exact ⟨h, hh, rfl⟩
      rw [← hCoEq] at hmh
      obtain ⟨x', hx', hx'eq⟩ := hmh
      have e1 : o⁻¹ * (m : G) * h * (o⁻¹ * (m : G))⁻¹ =
          o⁻¹ * ((m : G) * h * (m : G)⁻¹) * o := by
        group
      rw [e1, ← hx'eq]
      have e2 : o⁻¹ * ((MulAut.conj o).toMonoidHom x') * o = x' := by
        change o⁻¹ * (o * x' * o⁻¹) * o = x'
        group
      rw [e2]
      exact hx'
    · intro hh
      have hmh : (m : G) * h * (m : G)⁻¹ ∈ B := by
        rw [← hCoEq]
        refine ⟨o⁻¹ * (m : G) * h * (o⁻¹ * (m : G))⁻¹, hh, ?_⟩
        change o * (o⁻¹ * (m : G) * h * (o⁻¹ * (m : G))⁻¹) * o⁻¹ =
          (m : G) * h * (m : G)⁻¹
        group
      rw [hBdef] at hmh
      obtain ⟨a, ha, haeq⟩ := hmh
      have haeq' : (MulAut.conj (m : G)) a = (MulAut.conj (m : G)) h := haeq
      rw [← (MulAut.conj (m : G)).injective haeq']
      exact ha
  · have ho1 : QuotientGroup.mk' (ker148 A Y) (⟨o, hoY⟩ : ↥(Y ⊔ A)) = 1 :=
      mk'_ker148_eq_one_iff.mpr hoN
    have e : (⟨o⁻¹ * (m : G), hwY⟩ : ↥(Y ⊔ A)) = (⟨o, hoY⟩ : ↥(Y ⊔ A))⁻¹ * m :=
      Subtype.ext rfl
    rw [e, map_mul, map_inv, ho1, inv_one, one_mul]

theorem exists_mem_inf_of_innerOn148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJM : J ≤ Y ⊔ A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center ↥(img148 A Y J) = ⊥) {a : G} (ha : a ∈ A)
    (hin : InnerOn148 (img148 A Y J) (alpha148 A Y a ha)) :
    ∃ (u : G) (hu : u ∈ A), u ∈ J ∧ ∀ y ∈ img148 A Y J,
      alpha148 A Y a ha * y * (alpha148 A Y a ha)⁻¹ =
        alpha148 A Y u hu * y * (alpha148 A Y u hu)⁻¹ := by
  have hA3 : ∀ b ∈ A, b ^ 3 = 1 := hAF.1.2
  have hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hJn : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  obtain ⟨x, hxJ, hxc⟩ := hin
  have hcen : ∀ z ∈ img148 A Y J, (∀ y ∈ img148 A Y J, z * y * z⁻¹ = y) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := hzc w w.2
      change (w : _) * z = z * w
      calc (w : _) * z = z * w * z⁻¹ * z := by rw [this]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hxA : ∀ (b : G) (hb : b ∈ A), alpha148 A Y b hb * x = x * alpha148 A Y b hb := by
    intro b hb
    set β := alpha148 A Y b hb
    have hβ : β ∈ img148 A Y A := alpha148_mem_img148 hb
    have hβa : β * alpha148 A Y a ha = alpha148 A Y a ha * β := by
      rw [← alpha148_mul hb ha, ← alpha148_mul ha hb]
      congr 1
      exact hAc b hb a ha
    have hz : β * x * β⁻¹ ∈ img148 A Y J :=
      (Subgroup.mem_normalizer_iff.mp (hJn hβ) x).mp hxJ
    have hzx : x⁻¹ * (β * x * β⁻¹) = 1 := by
      refine hcen _ ((img148 A Y J).mul_mem ((img148 A Y J).inv_mem hxJ) hz) fun y hy => ?_
      have hy' : β⁻¹ * y * β ∈ img148 A Y J := by
        have := (Subgroup.mem_normalizer_iff.mp (hJn ((img148 A Y A).inv_mem hβ)) y).mp hy
        rwa [inv_inv] at this
      have h1 := hxc _ hy'
      have h2 := hxc y hy
      calc x⁻¹ * (β * x * β⁻¹) * y * (x⁻¹ * (β * x * β⁻¹))⁻¹
          = x⁻¹ * (β * (x * (β⁻¹ * y * β) * x⁻¹) * β⁻¹) * x := by group
        _ = x⁻¹ * (β * (alpha148 A Y a ha * (β⁻¹ * y * β) * (alpha148 A Y a ha)⁻¹) * β⁻¹)
              * x := by rw [h1]
        _ = x⁻¹ * ((β * alpha148 A Y a ha) * β⁻¹ * y * β * (β * alpha148 A Y a ha)⁻¹)
              * x := by group
        _ = x⁻¹ * ((alpha148 A Y a ha * β) * β⁻¹ * y * β * (alpha148 A Y a ha * β)⁻¹)
              * x := by rw [hβa]
        _ = x⁻¹ * (alpha148 A Y a ha * y * (alpha148 A Y a ha)⁻¹) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
        _ = y := by group
    have hβx : β * x * β⁻¹ = x := by
      calc β * x * β⁻¹ = x * (x⁻¹ * (β * x * β⁻¹)) := by group
        _ = x := by rw [hzx, mul_one]
    calc β * x = β * x * β⁻¹ * β := by group
      _ = x * β := by rw [hβx]
  have hx3 : x ^ 3 = 1 := by
    refine hcen _ ((img148 A Y J).pow_mem hxJ 3) fun y hy => ?_
    have ha3 : alpha148 A Y a ha ^ 3 = 1 := by
      rw [← alpha148_pow ha]
      simp only [hA3 a ha]
      rfl
    have hy1 : x * y * x⁻¹ ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem hxJ hy) ((img148 A Y J).inv_mem hxJ)
    have hy2 : x * (x * y * x⁻¹) * x⁻¹ ∈ img148 A Y J :=
      (img148 A Y J).mul_mem ((img148 A Y J).mul_mem hxJ hy1) ((img148 A Y J).inv_mem hxJ)
    set α' := alpha148 A Y a ha
    calc x ^ 3 * y * (x ^ 3)⁻¹ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by
          rw [pow_three]; group
      _ = α' * (α' * (α' * y * α'⁻¹) * α'⁻¹) * α'⁻¹ := by
          rw [hxc y hy, hxc _ hy1, hxc _ hy2]
      _ = α' ^ 3 * y * (α' ^ 3)⁻¹ := by rw [pow_three]; group
      _ = y := by rw [ha3]; group
  obtain ⟨u, huA, huJ, hu⟩ := exists_alpha148_eq_of_mem_img148 hAF hAY hJM hAJ hxJ hxA hx3
  refine ⟨u, huA, huJ, fun y hy => ?_⟩
  rw [hu]
  exact hxc y hy

theorem img148_inf_centralizer_of_le (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {D J : Subgroup G} (hDA : D ≤ A) (hJM : J ≤ Y ⊔ A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    img148 A Y J ⊓ Subgroup.centralizer (img148 A Y D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      img148 A Y (J ⊓ Subgroup.centralizer (D : Set G)) := by
  set N := pPrimeCoreOf 3 Y
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hB3 : IsPGroup 3 D := isPGroup_three_of_pow148 fun b hb => hA3 b (hDA hb)
  have hN3 : Nat.Coprime 3 (Nat.card ↥(N ⊓ J)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 Y)
  have hBN : D ≤ Subgroup.normalizer ((N ⊓ J : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAN (hDA hb), hAJ (hDA hb)⟩
  apply le_antisymm
  · rintro x ⟨hxJ, hxc⟩
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hxJ
    have hk : ∀ b ∈ D, j⁻¹ * (b * j * b⁻¹) ∈ N ⊓ J := by
      intro b hb
      have hbA : b ∈ A := hDA hb
      have hbjJ : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hAJ hbA) j).mp hjJ
      refine ⟨?_, J.mul_mem (J.inv_mem hjJ) hbjJ⟩
      have hbjM : b * j * b⁻¹ ∈ Y ⊔ A := hJM hbjJ
      have hbY : (b : G) ∈ Y ⊔ A := Subgroup.mem_sup_right hbA
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _
        (mem_img148_iff.mpr ⟨b, hbY, hb, rfl⟩)
      have hmk : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
          QuotientGroup.mk' (ker148 A Y) ⟨b * j * b⁻¹, hbjM⟩ := by
        have e1 : QuotientGroup.mk' (ker148 A Y) ⟨b * j * b⁻¹, hbjM⟩ =
            QuotientGroup.mk' (ker148 A Y) ⟨b, hbY⟩ * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
              (QuotientGroup.mk' (ker148 A Y) ⟨b, hbY⟩)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e1, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact mk'_ker148_eq_iff.mp hmk
    obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
    have hyJ : y ∈ J := by
      have := J.mul_mem hjJ hy.2
      rwa [mul_inv_cancel_left] at this
    have hyM : y ∈ Y ⊔ A := hJM hyJ
    refine mem_img148_iff.mpr ⟨y, hyM, ⟨hyJ, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr hyc
    · exact (mk'_ker148_eq_iff (g := ⟨j, hjM⟩) (h := ⟨y, hyM⟩)).mpr hy.1 |>.symm
  · intro x hx
    obtain ⟨d, hdM, hdJC, rfl⟩ := mem_img148_iff.mp hx
    have hdJ : d ∈ J := (Subgroup.mem_inf.mp hdJC).1
    have hdC : d ∈ Subgroup.centralizer (D : Set G) := (Subgroup.mem_inf.mp hdJC).2
    refine Subgroup.mem_inf.mpr ⟨mem_img148_iff.mpr ⟨d, hdM, hdJ, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e, heM, heD, rfl⟩ := mem_img148_iff.mp hh
    have hed : e * d = d * e := (Subgroup.mem_centralizer_iff.mp hdC) e heD
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hed

theorem conj_mem_zpowers_of_alpha148 (hA3 : ∀ a ∈ A, a ^ 3 = 1) {w c : G}
    (hw : w ∈ Y ⊔ A) (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hc : c ∈ A)
    (hn : QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩ ∈
      Subgroup.normalizer (Subgroup.zpowers (alpha148 A Y c hc) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    w * c * w⁻¹ ∈ Subgroup.zpowers c := by
  have hwc : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwA c).mp hc
  have h1 := (Subgroup.mem_normalizer_iff.mp hn (alpha148 A Y c hc)).mp
    (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hpow : alpha148 A Y (c ^ k) (A.zpow_mem hc k) = alpha148 A Y c hc ^ k := by
    rw [alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
    rfl
  have hconj : alpha148 A Y (w * c * w⁻¹) hwc = QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩ *
      alpha148 A Y c hc * (QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩)⁻¹ := by
    rw [alpha148_eq_mk', alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hk' : alpha148 A Y (c ^ k) (A.zpow_mem hc k) = alpha148 A Y (w * c * w⁻¹) hwc := by
    rw [hpow, hconj, hk]
  have hcw := alpha148_injective hA3 (A.zpow_mem hc k) hwc hk'
  rw [← hcw]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k

theorem mem_normalizer_zpowers_of_alpha148 (hA3 : ∀ a ∈ A, a ^ 3 = 1) {w c : G}
    (hw : w ∈ Y ⊔ A) (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hc : c ∈ A)
    (hn : QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩ ∈
      Subgroup.normalizer (Subgroup.zpowers (alpha148 A Y c hc) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hw' : w⁻¹ ∈ Y ⊔ A := (Y ⊔ A).inv_mem hw
  have hwA' : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hwA
  have hn' : QuotientGroup.mk' (ker148 A Y) ⟨w⁻¹, hw'⟩ ∈
      Subgroup.normalizer (Subgroup.zpowers (alpha148 A Y c hc) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have e : QuotientGroup.mk' (ker148 A Y) ⟨w⁻¹, hw'⟩ =
        (QuotientGroup.mk' (ker148 A Y) ⟨w, hw⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact Subgroup.inv_mem _ hn
  have hf := conj_mem_zpowers_of_alpha148 hA3 hw hwA hc hn
  have hb := conj_mem_zpowers_of_alpha148 hA3 hw' hwA' hc hn'
  have key : ∀ g : G, g * c * g⁻¹ ∈ Subgroup.zpowers c → ∀ h ∈ Subgroup.zpowers c,
      g * h * g⁻¹ ∈ Subgroup.zpowers c := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hg k
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key w hf h hh
  · intro hh
    have := key w⁻¹ hb (w * h * w⁻¹) hh
    rwa [show w⁻¹ * (w * h * w⁻¹) * w⁻¹⁻¹ = h by group] at this

end Lift

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
