module

public import Mathlib.GroupTheory.SchurZassenhaus
public import CFSG.LocalAnalysis.ZStar.TransferReduction

public section

namespace CFSG

namespace ZStar.TransferReduction

universe u

variable {G : Type u} [Group G] [Fintype G]

private theorem isolated_quotient {t : G} (ht : Isolated t) (ht2 : t * t = 1)
    (M : Subgroup G) [M.Normal] :
    Isolated (QuotientGroup.mk' M t) := by
  intro qg hcomm
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M qg
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let a : G := g * t * g⁻¹
  let r : G := a * t
  have ha2 : a * a = 1 := by
    dsimp [a]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; simp
  have hcomm' : q a * q t = q t * q a := by
    simpa [q, a, map_mul, map_inv] using hcomm
  have hqr2 : q r * q r = 1 := by
    change (q a * q t) * (q a * q t) = 1
    calc
      (q a * q t) * (q a * q t) = q a * (q t * q a) * q t := by group
      _ = q a * (q a * q t) * q t := by rw [← hcomm']
      _ = (q a * q a) * (q t * q t) := by group
      _ = 1 := by rw [← map_mul, ← map_mul, ha2, ht2]; simp
  have horderDvdTwo : orderOf (q r) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    simpa [pow_two] using hqr2
  have horderOdd : Odd (orderOf (q r)) := by
    exact (odd_orderOf_conjugate_mul ht ht2 g).of_dvd_nat
      (orderOf_map_dvd q r)
  have horderOne : orderOf (q r) = 1 := by
    have hpos : 0 < orderOf (q r) := (isOfFinOrder_of_finite (q r)).orderOf_pos
    have hle : orderOf (q r) ≤ 2 := Nat.le_of_dvd (by decide) horderDvdTwo
    obtain ⟨k, hk⟩ := horderOdd
    omega
  have hqr : q r = 1 := orderOf_eq_one_iff.mp horderOne
  change q a = q t
  have hqt2 : q t * q t = 1 := by rw [← map_mul, ht2, map_one]
  calc
    q a = q a * (q t * q t) := by rw [hqt2, mul_one]
    _ = (q a * q t) * q t := by group
    _ = q t := by simpa [r] using congrArg (fun z => z * q t) hqr

private theorem normal_two_le_center_of_terminal {t : G}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (M : Subgroup G) [M.Normal] (hM : IsPGroup 2 M) :
    M ≤ Subgroup.center G := by
  have hT : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_two_of_sq_eq_one t ht2
  have hTM : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ M) :=
    IsPGroup.to_sup_of_normal_right (H := Subgroup.zpowers t) (K := M) hT hM
  obtain ⟨P, hP⟩ := hTM.exists_le_sylow
  have htP : t ∈ P := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hMP : M ≤ P := fun m hm => hP (Subgroup.mem_sup_right hm)
  have htC : t ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hz := Subgroup.mem_center_iff.mp (mem_center_sylow_two ht P htP)
    exact congrArg Subtype.val (hz ⟨m, hMP hm⟩)
  have hCtop : Subgroup.centralizer (M : Set G) = ⊤ :=
    hmin _ inferInstance htC
  exact (Subgroup.centralizer_eq_top_iff_subset.mp hCtop)

private theorem zStar_lift_of_central_normal_two {t : G}
    (ht : Isolated t) (ht2 : t * t = 1)
    (M : Subgroup G) [M.Normal] (hM : IsPGroup 2 M)
    (hMcenter : M ≤ Subgroup.center G)
    (hquot :
      ∃ Obar : Subgroup (G ⧸ M), Obar.Normal ∧ Odd (Nat.card Obar) ∧
        ∀ qg : G ⧸ M,
          qg * QuotientGroup.mk' M t * qg⁻¹ * (QuotientGroup.mk' M t)⁻¹ ∈ Obar) :
    ∃ O : Subgroup G, O.Normal ∧ Odd (Nat.card O) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ O := by
  classical
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  obtain ⟨Obar, hObarNormal, hObarOdd, hObarComm⟩ := hquot
  let _ : Obar.Normal := hObarNormal
  let K : Subgroup G := Subgroup.comap q Obar
  let _ : K.Normal := Subgroup.normal_comap q
  have hMK : M ≤ K := by
    intro m hm
    change q m ∈ Obar
    rw [show q m = 1 by exact (QuotientGroup.eq_one_iff m).mpr hm]
    exact Obar.one_mem
  let MK : Subgroup K := M.subgroupOf K
  have hMKnormal : MK.Normal := by infer_instance
  let _ : MK.Normal := hMKnormal
  let qK : K →* Obar :=
    (q.comp K.subtype).codRestrict Obar (fun x => x.property)
  have hqKsurj : Function.Surjective qK := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective M (y : G ⧸ M)
    have hxK : x ∈ K := by
      change q x ∈ Obar
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxK⟩, ?_⟩
    apply Subtype.ext
    exact hx
  have hqKker : qK.ker = MK := by
    ext x
    change qK x = 1 ↔ (x : G) ∈ M
    constructor
    · intro hx
      have hx' := congrArg Subtype.val hx
      change q (x : G) = 1 at hx'
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx'
    · intro hx
      apply Subtype.ext
      change q (x : G) = 1
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
  have hMKindex : MK.index = Nat.card Obar := by
    rw [← hqKker, Subgroup.index_ker]
    have hrange : qK.range = ⊤ := MonoidHom.range_eq_top.mpr hqKsurj
    rw [hrange]
    simp
  have hMKcard : Nat.card MK = Nat.card M := by
    exact Nat.card_congr (M.subgroupOfEquivOfLe hMK)
  have hcoprime : (Nat.card MK).Coprime MK.index := by
    obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow.mp hM)
    have hnMK : Nat.card MK ∣ 2 ^ n := by
      rw [hMKcard]
      exact hn
    apply Nat.Coprime.of_dvd_left hnMK
    rw [hMKindex]
    exact hObarOdd.coprime_two_left.pow_left n
  obtain ⟨L, hLcomp⟩ :=
    Subgroup.exists_left_complement'_of_coprime (N := MK) hcoprime
  have hLodd : Odd (Nat.card L) := by
    rw [← hLcomp.index_eq_card, hMKindex]
    exact hObarOdd
  have hMKcenterK : MK ≤ Subgroup.center K := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hMcenter hm) (k : G)
  have hMKnormL : MK ≤ Subgroup.normalizer (L : Set K) :=
    hMKcenterK.trans (Subgroup.center_le_normalizer (L : Set K))
  have hsup : MK ⊔ L = ⊤ := by
    rw [sup_comm]
    exact hLcomp.sup_eq_top
  have hLnormal : L.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hsup]
    exact sup_le hMKnormL Subgroup.le_normalizer
  let _ : L.Normal := hLnormal
  have hquotTwo : IsPGroup 2 (K ⧸ L) := by
    obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow.mp hM)
    apply IsPGroup.of_card_dvd_pow (n := n)
    have hcard : Nat.card (K ⧸ L) = Nat.card MK := by
      rw [← Subgroup.index_eq_card]
      exact (Subgroup.isComplement'_comm.mpr hLcomp).index_eq_card
    rw [hcard, hMKcard]
    exact hn
  let LX : Subgroup G := Subgroup.map K.subtype L
  have hLXK : LX ≤ K := Subgroup.map_subtype_le L
  have hrestrict : LX.subgroupOf K = L := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hLXK]
  have hLXnormal : (LX.subgroupOf K).Normal := by
    rw [hrestrict]
    exact hLnormal
  have hLXodd : Odd (Nat.card LX) := by
    rw [show Nat.card LX = Nat.card L by exact Subgroup.card_subtype K L]
    exact hLodd
  let O : Subgroup G := Subgroup.normalClosure (LX : Set G)
  let _ : O.Normal := Subgroup.normalClosure_normal
  have hOodd : Odd (Nat.card O) :=
    odd_card_normalClosure_of_normal_subgroupOf K LX hLXK hLXnormal hLXodd
  refine ⟨O, inferInstance, hOodd, ?_⟩
  intro g
  let c : G := g * t * g⁻¹ * t⁻¹
  have hcK : c ∈ K := by
    change q c ∈ Obar
    have hc := hObarComm (q g)
    change q g * q t * (q g)⁻¹ * (q t)⁻¹ ∈ Obar at hc
    simpa [c, map_mul, map_inv] using hc
  let ck : K := ⟨c, hcK⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hckOdd : Odd (orderOf ck) := by
    rw [← orderOf_injective K.subtype K.subtype_injective ck]
    simpa [ck, c, htinv, mul_assoc] using
      odd_orderOf_conjugate_mul ht ht2 g
  have hckL : ck ∈ L := by
    rw [← QuotientGroup.eq_one_iff (N := L) ck]
    by_contra hne
    have htwo : 2 ∣ orderOf (QuotientGroup.mk' L ck) :=
      hquotTwo.dvd_orderOf hne
    have hdvd : orderOf (QuotientGroup.mk' L ck) ∣ orderOf ck :=
      orderOf_map_dvd (QuotientGroup.mk' L) ck
    have hnotEven : ¬Even (orderOf ck) := Nat.not_even_iff_odd.mpr hckOdd
    exact hnotEven (even_iff_two_dvd.mpr (htwo.trans hdvd))
  apply Subgroup.le_normalClosure
  change c ∈ LX
  exact ⟨ck, hckL, rfl⟩

theorem zStar_lift_of_odd_normal {t : G}
    (M : Subgroup G) [M.Normal] (hModd : Odd (Nat.card M))
    (hquot :
      ∃ Obar : Subgroup (G ⧸ M), Obar.Normal ∧ Odd (Nat.card Obar) ∧
        ∀ qg : G ⧸ M,
          qg * QuotientGroup.mk' M t * qg⁻¹ * (QuotientGroup.mk' M t)⁻¹ ∈ Obar) :
    ∃ O : Subgroup G, O.Normal ∧ Odd (Nat.card O) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ O := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  obtain ⟨Obar, hObarNormal, hObarOdd, hObarComm⟩ := hquot
  let _ : Obar.Normal := hObarNormal
  let O : Subgroup G := Subgroup.comap q Obar
  have hOodd : Odd (Nat.card O) := by
    have hcard : Nat.card O = Nat.card M * Nat.card Obar := by
      calc
        Nat.card O = (O : Set G).ncard := Nat.card_coe_set_eq (O : Set G)
        _ = Nat.card M * Nat.card Obar := by
          simpa [O, q] using
            (QuotientGroup.card_preimage_mk M (Obar : Set (G ⧸ M)))
    rw [hcard]
    exact hModd.mul hObarOdd
  refine ⟨O, inferInstance, hOodd, ?_⟩
  intro g
  change q (g * t * g⁻¹ * t⁻¹) ∈ Obar
  have hg := hObarComm (q g)
  change q g * q t * (q g)⁻¹ * (q t)⁻¹ ∈ Obar at hg
  simpa [map_mul, map_inv] using hg

theorem card_quotient_lt_of_ne_bot (M : Subgroup G) [M.Normal]
    (hMne : M ≠ ⊥) : Nat.card (G ⧸ M) < Nat.card G := by
  have hMone : 1 < Nat.card M := by
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hneOne : Nat.card M ≠ 1 := by
      intro h
      exact hMne (Subgroup.card_eq_one.mp h)
    omega
  have hqpos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M]
  exact lt_mul_of_one_lt_right hqpos hMone

theorem zStar_of_terminal_normal_two_quotient {t : G}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (M : Subgroup G) [M.Normal] (hM : IsPGroup 2 M)
    (hquot :
      QuotientGroup.mk' M t ≠ 1 →
      Isolated (QuotientGroup.mk' M t) →
      QuotientGroup.mk' M t * QuotientGroup.mk' M t = 1 →
      ∃ Obar : Subgroup (G ⧸ M), Obar.Normal ∧ Odd (Nat.card Obar) ∧
        ∀ qg : G ⧸ M,
          qg * QuotientGroup.mk' M t * qg⁻¹ * (QuotientGroup.mk' M t)⁻¹ ∈ Obar) :
    ∃ O : Subgroup G, O.Normal ∧ Odd (Nat.card O) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ O := by
  have hMcenter := normal_two_le_center_of_terminal ht ht2 hmin M hM
  by_cases htM : t ∈ M
  · have htcenter : t ∈ Subgroup.center G := hMcenter htM
    refine ⟨⊥, inferInstance, by simp, ?_⟩
    intro g
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_center_iff.mp htcenter g]
    group
  · have hqtne : QuotientGroup.mk' M t ≠ 1 := by
      simpa [QuotientGroup.eq_one_iff] using htM
    have hqt2 : QuotientGroup.mk' M t * QuotientGroup.mk' M t = 1 := by
      rw [← map_mul, ht2, map_one]
    exact zStar_lift_of_central_normal_two ht ht2 M hM hMcenter
      (hquot hqtne (isolated_quotient ht ht2 M) hqt2)

end ZStar.TransferReduction

end CFSG
