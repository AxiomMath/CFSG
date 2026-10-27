module

public import CFSG.Quasithin.Recognition.M12AscClasses
public import CFSG.Quasithin.Recognition.M12AscI2
public import CFSG.Quasithin.Recognition.M12AscCount
public import CFSG.GH74.ThompsonOrderFormula

public section

namespace CFSG.Quasithin

open Subgroup CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

theorem mem_zpowers_subtype_iff {I : Subgroup G} (x w : I) :
    w ∈ Subgroup.zpowers x ↔ (w : G) ∈ Subgroup.zpowers (x : G) := by
  simp only [Subgroup.mem_zpowers_iff, Subtype.ext_iff, Subgroup.coe_zpow]

theorem KleinCore.subgroupOf [Finite G] {K V : Subgroup G} {z y : G} (h : KleinCore K V z y)
    (X : Subgroup G) (hKX : K ≤ X) (hzX : z ∈ X) (hyX : y ∈ X) :
    KleinCore (K.subgroupOf X) (V.subgroupOf X) ⟨z, hzX⟩ ⟨y, hyX⟩ where
  z_sq := Subtype.ext h.z_sq
  z_ne := fun e => h.z_ne (congrArg Subtype.val e)
  z_mem := Subgroup.mem_subgroupOf.2 h.z_mem
  V_le := fun v hv => Subgroup.mem_subgroupOf.2 (h.V_le (Subgroup.mem_subgroupOf.1 hv))
  V_card := by
    rw [← h.V_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.V_le.trans hKX)).toEquiv
  V_sq := fun v hv => Subtype.ext (h.V_sq v.1 (Subgroup.mem_subgroupOf.1 hv))
  cent := fun k hk hkz => Subgroup.mem_subgroupOf.2
    (h.cent k.1 (Subgroup.mem_subgroupOf.1 hk) (congrArg Subtype.val hkz))
  y_mem := Subgroup.mem_subgroupOf.2 h.y_mem
  y_cube := Subtype.ext h.y_cube
  y_norm := fun v hv => Subgroup.mem_subgroupOf.2
    (h.y_norm v.1 (Subgroup.mem_subgroupOf.1 hv))
  y_ne := fun e => h.y_ne (congrArg Subtype.val e)
  syl := fun W hWK hW => by
    have hmap : W.map X.subtype ≤ K := by
      rintro _ ⟨w, hw, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hWK hw)
    have hp : IsPGroup 2 (W.map X.subtype) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hW
      refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
      rw [card_map_subtype, hn]
    have := h.syl _ hmap hp
    rwa [card_map_subtype] at this

namespace AscModel

variable (m : AscModel z)

include m

theorem card_thompsonPairs_t [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {t y : G}
    {K V : Subgroup G} (hD : IData m t y K V) :
    ∃ n : ℕ, 4 * n = Nat.card K ∧ 3 ≤ n ∧ thompsonPairCount t z t = n * (n - 2) := by
  classical
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hnc : ¬ IsConj z t := m.not_isConj_of_notMem_fSub hyp hD.t_Q hD.t_F
  have ht1 : t ≠ 1 := fun e => hD.t_F (e ▸ one_mem _)
  set I : Subgroup G := Subgroup.centralizer ({t} : Set G) with hI
  have hmemI : ∀ a, a ∈ I ↔ a * t = t * a := fun a => Subgroup.mem_centralizer_singleton_iff
  have htI : t ∈ I := (hmemI t).2 rfl
  have hKI : K ≤ I := hD.K_le
  have hzK : z ∈ K := hD.klein.V_le hD.klein.z_mem
  have hzI : z ∈ I := hKI hzK
  have hyI : y ∈ I := hKI hD.klein.y_mem
  have hcardI : Nat.card I = 4 * Nat.card K := hD.card_I
  have : Fintype I := Fintype.ofFinite I
  let t' : I := ⟨t, htI⟩
  let z' : I := ⟨z, hzI⟩
  set K' : Subgroup I := K.subgroupOf I with hK'
  have hK'n : K'.Normal := ⟨fun k hk g => hD.K_norm g.1 g.2 k.1 hk⟩
  have hklein : KleinCore K' (V.subgroupOf I) z' ⟨y, hyI⟩ := hD.klein.subgroupOf I hKI hzI hyI
  have hz'K : z' ∈ K' := Subgroup.mem_subgroupOf.2 hzK
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  have hz1' : z' ≠ 1 := fun e => asc_z_ne_one hyp (congrArg Subtype.val e)
  set Zf : Finset I := Finset.univ.filter (fun x : I => x ∈ K' ∧ x * x = 1 ∧ x ≠ 1) with hZfdef
  have hZf : ∀ x, x ∈ Zf ↔ x ∈ K' ∧ x * x = 1 ∧ x ≠ 1 := fun x => by simp [hZfdef]
  have htc : ∀ x : I, x * t' = t' * x := fun x => Subtype.ext ((hmemI x.1).1 x.2)
  have ht2' : t' * t' = 1 := Subtype.ext hD.t_sq
  have hsq' : ∀ a : I, a * a ∈ K' := fun a => hD.sq_mem a.1 a.2
  have htK' : t' ∉ K' := fun h => hD.t_K h
  have hA : ∀ x ∈ Zf, (Zf.filter (fun w => w * x = x * w)).card = 3 := fun x hx =>
    hklein.card_commuting Zf hZf hx
  have hB : ∀ x ∈ Zf, ∀ w ∈ Zf, x * w ≠ w * x → Odd (orderOf (x * w)) := fun x hx w hw hne =>
    hklein.odd_order ((hZf x).1 hx).1 ((hZf x).1 hx).2.1 ((hZf w).1 hw).1 ((hZf w).1 hw).2.1 hne
  set Pf : Finset (I × I) := Finset.univ.filter (fun p : I × I =>
    p.1 * p.1 = 1 ∧ p.1 ∉ K' ∧ p.2 ∈ Zf ∧ t' ∈ Subgroup.zpowers (p.1 * p.2)) with hPfdef
  have hPf : ∀ p, p ∈ Pf ↔
      p.1 * p.1 = 1 ∧ p.1 ∉ K' ∧ p.2 ∈ Zf ∧ t' ∈ Subgroup.zpowers (p.1 * p.2) := fun p => by
    simp [hPfdef]
  have hcount := asc_pair_count ht2' htc K' hsq' htK' Zf hZf hA hB Pf hPf
  have hmemP : ∀ p ∈ thompsonPairs t z t, p.1 ∈ I ∧ p.2 ∈ I := fun p hp =>
    mem_centralizer_of_mem_thompsonPairs hD.t_sq hz2 hD.t_sq hp
  let f : thompsonPairs t z t → I × I := fun p =>
    (⟨p.1.1, (hmemP p.1 p.2).1⟩, ⟨p.1.2, (hmemP p.1 p.2).2⟩)
  have hfP : ∀ p, f p ∈ Pf := by
    intro p
    obtain ⟨hta, hzb, hmem⟩ := mem_thompsonPairs.1 p.2
    obtain ⟨c, hc⟩ := isConj_iff.1 hta
    have ha2 : p.1.1 * p.1.1 = 1 := by
      rw [← hc]
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [hD.t_sq]; group
    have ha1 : p.1.1 ≠ 1 := by
      intro e
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc, e]; group
    have haK : p.1.1 ∉ K := by
      intro haK
      obtain ⟨k, -, hk⟩ := hD.klein.exists_conj_z haK ha2 ha1
      exact hnc ((isConj_iff.2 ⟨k, hk⟩).trans hta.symm)
    have hbK : p.1.2 ∈ K := hD.conj_mem p.1.2 (hmemP p.1 p.2).2 hzb
    obtain ⟨d, hd⟩ := isConj_iff.1 hzb
    have hb2 : p.1.2 * p.1.2 = 1 := by rw [← hd]; exact asc_conj_sq hyp d
    have hb1 : p.1.2 ≠ 1 := by rw [← hd]; exact asc_conj_ne_one hyp d
    rw [hPf]
    refine ⟨Subtype.ext ha2, fun h => haK h,
      (hZf _).2 ⟨hbK, Subtype.ext hb2, fun h => hb1 (congrArg Subtype.val h)⟩, ?_⟩
    exact (mem_zpowers_subtype_iff _ _).2 hmem
  let g : thompsonPairs t z t → {q // q ∈ Pf} := fun p => ⟨f p, hfP p⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro p p' h
      have h1 : p.1.1 = p'.1.1 := congrArg (fun q : {q // q ∈ Pf} => ((q.1.1 : I) : G)) h
      have h2 : p.1.2 = p'.1.2 := congrArg (fun q : {q // q ∈ Pf} => ((q.1.2 : I) : G)) h
      exact Subtype.ext (Prod.ext h1 h2)
    · rintro ⟨⟨a', b'⟩, hq⟩
      rw [hPf] at hq
      obtain ⟨ha2, haK, hb, hmem⟩ := hq
      obtain ⟨hbK, hb2, hb1⟩ := (hZf _).1 hb
      have ha2' : a'.1 * a'.1 = 1 := congrArg Subtype.val ha2
      have haK' : a'.1 ∉ K := fun h => haK h
      have ha1 : a'.1 ≠ 1 := fun h => haK' (h ▸ one_mem _)
      have hta : IsConj t a'.1 := by
        rcases m.involution_classes hyp hD.t_Q hD.t_F hD.t_sq ha2' ha1 with h | h
        · exact absurd (hD.conj_mem a'.1 a'.2 h) haK'
        · exact h
      have hb2' : b'.1 * b'.1 = 1 := congrArg Subtype.val hb2
      have hb1' : b'.1 ≠ 1 := fun h => hb1 (Subtype.ext h)
      obtain ⟨k, -, hk⟩ := hD.klein.exists_conj_z hbK hb2' hb1'
      have hzb : IsConj z b'.1 := isConj_iff.2 ⟨k, hk⟩
      have hmem' : t ∈ Subgroup.zpowers (a'.1 * b'.1) := (mem_zpowers_subtype_iff _ _).1 hmem
      exact ⟨⟨(a'.1, b'.1), mem_thompsonPairs.2 ⟨hta, hzb, hmem'⟩⟩,
        Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))⟩
  have hPairs : thompsonPairCount t z t = Pf.card := by
    show Nat.card (thompsonPairs t z t) = Pf.card
    rw [Nat.card_congr (Equiv.ofBijective g hbij), Nat.card_eq_fintype_card, Fintype.card_coe]
  have hconj : (conjugatesOf z' : Set I) = (Zf : Set I) := by
    ext x
    show IsConj z' x ↔ x ∈ Zf
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine (hZf x).2 ⟨?_, ?_, ?_⟩
      · rw [← hc]
        exact hK'n.conj_mem z' hz'K c
      · rw [← hc]
        calc c * z' * c⁻¹ * (c * z' * c⁻¹) = c * (z' * z') * c⁻¹ := by group
          _ = 1 := by rw [hz2']; group
      · intro e
        apply hz1'
        calc z' = c⁻¹ * (c * z' * c⁻¹) * c := by group
          _ = 1 := by rw [hc, e]; group
    · intro hx
      obtain ⟨hxK, hx2, hx1⟩ := (hZf x).1 hx
      obtain ⟨k, -, hk⟩ := hklein.exists_conj_z hxK hx2 hx1
      exact isConj_iff.2 ⟨k, hk⟩
  have hcongj : Nat.card (conjugatesOf z') = Zf.card := by
    rw [hconj, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid :=
    m.tb_facts hyp hD.t_Q hD.t_F hD.t_sq
  have hcent : Nat.card (Subgroup.centralizer ({z'} : Set I)) = 16 := by
    rw [← m.card_cSub hf]
    have hH : ∀ x : Subgroup.centralizer ({z'} : Set I), (x : I).1 * z = z * (x : I).1 := fun x =>
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨(x : I).1, (m.mem_cSub_iff hD.t_Q hf).2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (hH x), (hmemI _).1 (x : I).2⟩⟩) ⟨?_, ?_⟩)
    · intro x x' h
      have h1 : (x : I).1 = (x' : I).1 := congrArg (fun w : ↥(m.cSub hf) => (w : G)) h
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨y', hy'⟩
      obtain ⟨hyH, hyt⟩ := (m.mem_cSub_iff hD.t_Q hf).1 hy'
      refine ⟨⟨⟨y', (hmemI _).2 hyt⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyH)
  have hmain := card_centralizer_mul_card_conjugatesOf z'
  rw [hcent, hcongj] at hmain
  have hz'Zf : z' ∈ Zf := (hZf z').2 ⟨hz'K, hz2', hz1'⟩
  refine ⟨Zf.card, ?_, ?_, ?_⟩
  · omega
  · have h3 := hA z' hz'Zf
    have := Finset.card_le_card (Finset.filter_subset (fun w => w * z' = z' * w) Zf)
    omega
  · rw [hPairs, hcount]

theorem card_G_formula [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {t y : G}
    {K V : Subgroup G} (hD : IData m t y K V) :
    Nat.card G = 12 * Nat.card K * (Nat.card K + 72) := by
  obtain ⟨n, hn4, hn3, hrt⟩ := m.card_thompsonPairs_t hyp hD
  have hrz := m.card_thompsonPairs_z hyp hD.t_Q hD.t_F hD.t_sq
  have ht1 : t ≠ 1 := fun e => hD.t_F (e ▸ one_mem _)
  have ht : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hD.t_sq) ht1
  have hnc : ¬ IsConj z t := m.not_isConj_of_notMem_fSub hyp hD.t_Q hD.t_F
  have hcl : ∀ x : G, orderOf x = 2 → IsConj t x ∨ IsConj z x := by
    intro x hx
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    have hx1 : x ≠ 1 := by
      intro e
      rw [e, orderOf_one] at hx
      omega
    exact (m.involution_classes hyp hD.t_Q hD.t_F hD.t_sq hx2 hx1).symm
  obtain ⟨hcard, -⟩ := CFSG.GH74.thompson_two_involution_class_order_formula (t := t) (u := z)
    ht hyp.orderTwo (fun h => hnc h.symm) hcl
  rw [hrt, hrz] at hcard
  have hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) = 192 := card_ascH hyp
  have hct : Nat.card (Subgroup.centralizer ({t} : Set G)) = 4 * Nat.card K := hD.card_I
  rw [hcz, hct] at hcard
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have e : j + 2 - 2 = j := by omega
  rw [e] at hcard
  rw [hcard, ← hn4]
  ring

end AscModel

end CFSG.Quasithin
