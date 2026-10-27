module

public import CFSG.Monster.GMS.S4FusionBasic
public import CFSG.Monster.GMS.Leech.Pairs
public import CFSG.Monster.GMS.Facts.Section4

public section

namespace CFSG.Monster.GMS.S4Fusion

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

section Linear

theorem exists_pair_bil₀ {x : Fin 24 → ZMod 2} (hx : x ≠ 0) :
    ∃ v₁ v₂ : Fin 24 → ZMod 2, bil₀ v₁ x = 0 ∧ bil₀ v₂ x = 0 ∧ bil₀ v₁ v₂ = 1 := by
  obtain ⟨y, hy0, hy1, hy2⟩ : ∃ y, bil₀ y x = 0 ∧ y ≠ 0 ∧ y ≠ x := by
    by_contra hno
    push Not at hno
    let f : (Fin 24 → ZMod 2) →+ ZMod 2 :=
      AddMonoidHom.mk' (fun v => bil₀ v x) (fun u v => Leech.bil₀_add_left u v x)
    have hsurj : Function.Surjective f := by
      obtain ⟨v, hv⟩ := Leech.exists_bil₀_eq_one hx
      intro c
      rcases zmod2_cases c with rfl | rfl
      · exact ⟨0, map_zero f⟩
      · exact ⟨v, by show bil₀ v x = 1; rw [bil₀_comm]; exact hv⟩
    have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsurj
    have hker : (f.ker : Set (Fin 24 → ZMod 2)) ⊆ {0, x} := by
      intro y hy
      by_cases h0 : y = 0
      · exact Or.inl h0
      · exact Or.inr (hno y hy h0)
    have hle : Nat.card f.ker ≤ 2 := by
      calc Nat.card f.ker = (f.ker : Set (Fin 24 → ZMod 2)).ncard :=
            (Nat.card_coe_set_eq _).symm
        _ ≤ ({0, x} : Set (Fin 24 → ZMod 2)).ncard := Set.ncard_le_ncard hker (Set.toFinite _)
        _ = 2 := Set.ncard_pair hx.symm
    have htot : Nat.card (Fin 24 → ZMod 2) = 2 ^ 24 := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have h2 : Nat.card (ZMod 2) = 2 := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    rw [htot, h2] at hcard
    omega
  have hind : LinearIndependent (ZMod 2) ![x, y] :=
    Leech.linearIndependent_fin_two hx hy1 hy2.symm
  obtain ⟨w, hw⟩ := Leech.exists_bil₀_eq hind ![0, 1]
  refine ⟨y, w, hy0, ?_, ?_⟩
  · simpa using hw 0
  · rw [bil₀_comm]
    simpa using hw 1

end Linear

section Core

variable {G : Type} [Group G]

theorem isPGroup_leechQ (z : G) : IsPGroup 2 (leechQ z) := by
  unfold leechQ
  exact (CFSG.pCore_isPGroup (p := 2)).map _

theorem hasNormalTwoCommutator_of_isConj_mul
    (h13 : Co1ModuleUniqueness)
    [Finite G]
    {a z₀ b z u t s : G} (h : TwoClasses a z₀ b z u) (ht : IsConj a t) (hs : IsConj z₀ s)
    (hts : t * s = s * t) (hmul : IsConj a (t * s)) : HasNormalTwoCommutator t s := by
  have ht2 : orderOf t = 2 := (orderOf_eq_of_isConj ht).symm.trans h.orderOf_a
  have htQ : t ∈ leechQ s := h.mem_leechQ_of_isConj_mul ht hs hts hmul
  obtain ⟨L⟩ := exists_leechSystem h13 (h.gms s hs)
  have hts' : t ≠ s := by
    rintro rfl
    exact h.not_isConj (ht.trans hs.symm)
  have hv : L.vec t ≠ 0 := (L.vec_ne_zero_iff htQ).2 ⟨ne_one_of_orderOf ht2, hts'⟩
  obtain ⟨v₁, v₂, h1, h2, h12⟩ := exists_pair_bil₀ hv
  obtain ⟨p, hpQ, hpv⟩ := L.vec_surj v₁
  obtain ⟨q, hqQ, hqv⟩ := L.vec_surj v₂
  have hpt : ⁅p, t⁆ = 1 := (L.comm_eq_one_iff hpQ htQ).2 (by rw [hpv]; exact h1)
  have hqt : ⁅q, t⁆ = 1 := (L.comm_eq_one_iff hqQ htQ).2 (by rw [hqv]; exact h2)
  have hpq : ⁅p, q⁆ = s := (L.comm_eq_z_iff hpQ hqQ).2 (by rw [hpv, hqv]; exact h12)
  have hpC : p ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hpt)
  have hqC : q ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hqt)
  refine ⟨leechQ s ⊓ Subgroup.centralizer ({t} : Set G), ?_, ?_, ?_, p, ⟨hpQ, hpC⟩, q,
    ⟨hqQ, hqC⟩, hpq⟩
  · intro g hg
    exact Subgroup.mem_inf.mpr ⟨hg.2, leechQ_le_centralizer s hg.1⟩
  · exact (isPGroup_leechQ s).to_le inf_le_left
  · intro g hg n hn
    exact ⟨conj_mem_leechQ hg.2 hn.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.1 hn.2) (Subgroup.inv_mem _ hg.1)⟩

theorem not_hasNormalTwoCommutator
    (h13 : Co1ModuleUniqueness) (hNF : Co2StabFacts) [Finite G]
    {a z₀ b z u t s : G} (h : TwoClasses a z₀ b z u) (ht : IsConj a t) (hs : IsConj a s)
    (hts : t * s = s * t) (hw : IsConj z₀ (t * s)) : ¬ HasNormalTwoCommutator t s := by
  rintro ⟨N, hNle, hNp, hNn, p, hp, q, hq, hpq⟩
  have ht2 : orderOf t = 2 := (orderOf_eq_of_isConj ht).symm.trans h.orderOf_a
  have hs2 : orderOf s = 2 := (orderOf_eq_of_isConj hs).symm.trans h.orderOf_a
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf ht2
  obtain ⟨w, hwdef⟩ : ∃ w, w = t * s := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have htw : t * w = s := by rw [hwdef, ← mul_assoc, htt, one_mul]
  have hwt : t * w = w * t := by
    rw [htw, hwdef, mul_assoc, ← hts, ← mul_assoc, htt, one_mul]
  have hinf : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [hwdef]
    exact centralizer_inf_mul_eq t s
  have htQ : t ∈ leechQ w := h.mem_leechQ_of_isConj_mul ht hw hwt (by rw [htw]; exact hs)
  obtain ⟨L⟩ := exists_leechSystem h13 (h.gms w hw)
  have hvt : L.vec t ∈ co1Orbit 0 :=
    (L.mem_typeSet.mp (L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem hw htQ ht))).2
  have hvt0 : L.vec t ≠ 0 := Leech.ne_zero_of_mem_co1Orbit hvt
  have hfin : Finite Co1 := Finite.of_surjective L.φ L.φ_surj
  let K' : Subgroup ↥(Subgroup.centralizer ({w} : Set G)) :=
    (Subgroup.centralizer ({t} : Set G)).subgroupOf (Subgroup.centralizer ({w} : Set G))
  have hK' : ∀ c : ↥(Subgroup.centralizer ({w} : Set G)), c ∈ K' ↔
      (c : G) ∈ Subgroup.centralizer ({t} : Set G) := fun c => Iff.rfl
  let Hb : Subgroup Co1 := K'.map L.φ
  have hHb_le : Hb ≤ co1Stab (L.vec t) := by
    rintro _ ⟨c, hc, rfl⟩
    have hct : (c : G) * t * (c : G)⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp ((hK' c).mp hc), mul_inv_cancel_right]
    show co1Act (L.φ c) (L.vec t) = L.vec t
    rw [← L.vec_conj c t htQ, hct]
  have hstab_le : co1Stab (L.vec t) ≤ Hb := by
    intro cb hcb
    have hcb' : co1Act cb (L.vec t) = L.vec t := hcb
    obtain ⟨c, rfl⟩ := L.φ_surj cb
    have hcQ : (c : G) * t * (c : G)⁻¹ ∈ leechQ w := L.conj_mem c htQ
    have hvec : L.vec ((c : G) * t * (c : G)⁻¹) = L.vec t := by
      rw [L.vec_conj c t htQ]
      exact hcb'
    rcases L.eq_or_eq_mul_z hcQ htQ hvec with e | e
    · exact ⟨c, (hK' c).mpr (mem_centralizer_singleton_iff_conj.mpr e), rfl⟩
    ·
      obtain ⟨y, hy⟩ := Leech.exists_bil₀_eq (Leech.linearIndependent_fin_one hvt0) ![1]
      obtain ⟨r, hrQ, hrv⟩ := L.vec_surj y
      have hr : ⁅r, t⁆ = w := (L.comm_eq_z_iff hrQ htQ).2 (by rw [hrv]; simpa using hy 0)
      have hrC : r ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hrQ
      have h1 : r * t * r⁻¹ * t⁻¹ = w := hr
      have h2 : r * t * r⁻¹ = t * w := by
        rw [hwt, ← h1]
        group
      have hc' : ((⟨r, hrC⟩⁻¹ * c : ↥(Subgroup.centralizer ({w} : Set G))) : G) * t *
          ((⟨r, hrC⟩⁻¹ * c : ↥(Subgroup.centralizer ({w} : Set G))) : G)⁻¹ = t := by
        calc ((⟨r, hrC⟩⁻¹ * c : ↥(Subgroup.centralizer ({w} : Set G))) : G) * t *
              ((⟨r, hrC⟩⁻¹ * c : ↥(Subgroup.centralizer ({w} : Set G))) : G)⁻¹
            = r⁻¹ * ((c : G) * t * (c : G)⁻¹) * r := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              group
          _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [e, h2]
          _ = t := by group
      refine ⟨⟨r, hrC⟩⁻¹ * c, (hK' _).mpr (mem_centralizer_singleton_iff_conj.mpr hc'), ?_⟩
      have hφr : L.φ ⟨r, hrC⟩ = 1 := (L.φ_ker ⟨r, hrC⟩).2 hrQ
      rw [map_mul, map_inv, hφr, inv_one, one_mul]
  have hcard : Nat.card (co1Stab (L.vec t)) ≤ 2 * Nat.card Hb := by
    have := Subgroup.card_le_of_le hstab_le
    omega
  let N₀ : Subgroup ↥(Subgroup.centralizer ({w} : Set G)) :=
    N.subgroupOf (Subgroup.centralizer ({w} : Set G))
  let Nb : Subgroup Co1 := N₀.map L.φ
  have hNb_le : Nb ≤ Hb := Subgroup.map_mono fun c hc => (hK' c).mpr (hNle hc).1
  have hNb_norm : ∀ x ∈ Hb, ∀ n ∈ Nb, x * n * x⁻¹ ∈ Nb := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨k * m * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hkC : (k : G) ∈ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({s} : Set G) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨(hK' k).mp hk, k.2⟩
    exact hNn k hkC m hm
  have hNb_p : IsPGroup 2 Nb :=
    (hNp.comap_subtype (K := Subgroup.centralizer ({w} : Set G))).map L.φ
  have hNb : Nb = ⊥ := hNF (L.vec t) hvt Hb hHb_le hcard Nb hNb_le hNb_norm hNb_p
  have hQN : ∀ n ∈ N, n ∈ leechQ w := by
    intro n hn
    have hnCw : n ∈ Subgroup.centralizer ({w} : Set G) := by
      have := hNle hn
      rw [← hinf] at this
      exact this.2
    have hmem : L.φ ⟨n, hnCw⟩ ∈ Nb := ⟨⟨n, hnCw⟩, hn, rfl⟩
    rw [hNb, Subgroup.mem_bot] at hmem
    exact (L.φ_ker ⟨n, hnCw⟩).1 hmem
  have hc := L.extraspecial.comm p (hQN p hp) q (hQN q hq)
  rw [hpq] at hc
  rcases hc with h1 | h1
  · exact ne_one_of_orderOf hs2 h1
  · rw [h1] at hs
    exact h.not_isConj (hs.trans hw.symm)

end Core

end CFSG.Monster.GMS.S4Fusion
