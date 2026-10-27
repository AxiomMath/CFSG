module

public import CFSG.Monster.GMS.Leech.Count
public import CFSG.Monster.GMS.Facts.LeechCosets
public import CFSG.Monster.GMS.Facts.LeechInvolutions

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Matrix

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

omit L in
theorem mul_self_eq_one_of_orderOf_eq_two {t : G} (h : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← h]
  exact pow_orderOf_eq_one t

include L

theorem orderOf_φ {t : G} (ht : t ∈ Subgroup.centralizer ({z} : Set G)) (h2 : orderOf t = 2)
    (hQ : t ∉ leechQ z) : orderOf (L.φ ⟨t, ht⟩) = 2 := by
  have hsq : (⟨t, ht⟩ : Subgroup.centralizer ({z} : Set G)) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using mul_self_eq_one_of_orderOf_eq_two h2)
  have h1 : L.φ ⟨t, ht⟩ ≠ 1 := fun h => hQ ((L.φ_ker _).1 h)
  exact orderOf_eq_prime (by rw [← map_pow, hsq, map_one]) h1

theorem φ_mul_self {t : G} (ht : t ∈ Subgroup.centralizer ({z} : Set G)) (h2 : t * t = 1) :
    L.φ ⟨t, ht⟩ * L.φ ⟨t, ht⟩ = 1 := by
  rw [← map_mul]
  have : (⟨t, ht⟩ : Subgroup.centralizer ({z} : Set G)) * ⟨t, ht⟩ = 1 := Subtype.ext h2
  rw [this, map_one]

theorem involution_bounds
    [Finite G] {t : G} (ht : t ∈ Subgroup.centralizer ({z} : Set G)) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) ≤
        2 * ((co1Fix (L.φ ⟨t, ht⟩)).ncard *
          Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1))) ∧
      (Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
          2 * ((co1Fix (L.φ ⟨t, ht⟩)).ncard *
            Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1))) →
        (∀ q ∈ leechQ z, L.vec q ∈ co1Fix (L.φ ⟨t, ht⟩) → t * q = q * t) ∧
          Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G)) =
            2 * (co1Fix (L.φ ⟨t, ht⟩)).ncard) := by
  have : Finite Co1 := CFSG.Sporadic.Co1.fam_co1_simplicity.1
  set s := L.φ ⟨t, ht⟩ with hs
  set D : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)
    with hD
  have hDC : D ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hcardD := L.card_eq_card_image_mul D hDC
  have himg : L.image D ≤ Subgroup.centralizer ({s} : Set Co1) := by
    intro x hx
    obtain ⟨c, hcD, rfl⟩ := L.mem_image.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hct : (c : G) * t = t * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcD).2
    rw [hs, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hct
  have hA : Nat.card ↥(L.image D) ≤ Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) :=
    Subgroup.card_le_of_le himg
  have hsub : (↑(leechQ z ⊓ D) : Set G) ⊆ {g | g ∈ leechQ z ∧ L.vec g ∈ co1Fix s} := by
    intro g hg
    obtain ⟨hgQ, hgD⟩ := Subgroup.mem_inf.1 hg
    refine ⟨hgQ, ?_⟩
    have hgt : g * t = t * g :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hgD).2
    show co1Act s (L.vec g) = L.vec g
    rw [hs, ← L.vec_conj ⟨t, ht⟩ g hgQ]
    congr 1
    show t * g * t⁻¹ = g
    rw [← hgt]
    group
  have hQD : leechQ z ⊓ D = leechQ z ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, hD]
    constructor
    · rintro ⟨hg, -, h⟩
      exact ⟨hg, h⟩
    · rintro ⟨hg, h⟩
      exact ⟨hg, L.mem_centralizer hg, h⟩
  have hB : Nat.card ↥(leechQ z ⊓ D) ≤ 2 * (co1Fix s).ncard := by
    calc Nat.card ↥(leechQ z ⊓ D) = ((leechQ z ⊓ D : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ {g | g ∈ leechQ z ∧ L.vec g ∈ co1Fix s}.ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 * (co1Fix s).ncard := L.ncard_preimage _
  have hpos1 : 0 < Nat.card ↥(leechQ z ⊓ D) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) := Nat.card_pos
  refine ⟨?_, fun heq => ?_⟩
  · calc Nat.card D = Nat.card ↥(L.image D) * Nat.card ↥(leechQ z ⊓ D) := hcardD
      _ ≤ Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) * (2 * (co1Fix s).ncard) :=
          Nat.mul_le_mul hA hB
      _ = 2 * ((co1Fix s).ncard * Nat.card ↥(Subgroup.centralizer ({s} : Set Co1))) := by ring
  · have h3 : Nat.card ↥(L.image D) * Nat.card ↥(leechQ z ⊓ D) =
        Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) * (2 * (co1Fix s).ncard) := by
      rw [← hcardD, heq]
      ring
    have h4 : Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) * Nat.card ↥(leechQ z ⊓ D) =
        Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) * (2 * (co1Fix s).ncard) := by
      refine le_antisymm (Nat.mul_le_mul_left _ hB) ?_
      have h5 := Nat.mul_le_mul_right (Nat.card ↥(leechQ z ⊓ D)) hA
      rw [h3] at h5
      exact h5
    have hb : Nat.card ↥(leechQ z ⊓ D) = 2 * (co1Fix s).ncard := Nat.eq_of_mul_eq_mul_left hpos2 h4
    have heqset : (↑(leechQ z ⊓ D) : Set G) = {g | g ∈ leechQ z ∧ L.vec g ∈ co1Fix s} := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [L.ncard_preimage, ← hb, ← Nat.card_coe_set_eq]
      rfl
    refine ⟨fun q hq hqW => ?_, by rw [← hQD, hb]⟩
    have hmem : q ∈ (↑(leechQ z ⊓ D) : Set G) := by
      rw [heqset]
      exact ⟨hq, hqW⟩
    have hmemD := (Subgroup.mem_inf.1 hmem).2
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hmemD).2).symm

omit L in
theorem orderOf_conj_eq_two {t : G} (g : G) (h2 : orderOf t = 2) : orderOf (g * t * g⁻¹) = 2 := by
  have h1 : t ≠ 1 := by
    rintro rfl
    simp at h2
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact mul_self_eq_one_of_orderOf_eq_two h2
  refine orderOf_eq_prime (by rw [conj_pow, ht2]; group) fun h => h1 ?_
  have := congrArg (fun y => g⁻¹ * y * g) h
  simpa [mul_assoc] using this

omit L in
theorem card_inf_centralizer_conj {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (a : G) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun d => ⟨g⁻¹ * d * g, ?_⟩
      invFun := fun d => ⟨g * d * g⁻¹, ?_⟩
      left_inv := fun d => Subtype.ext (by group)
      right_inv := fun d => Subtype.ext (by group) }
  · obtain ⟨hdC, hd⟩ := Subgroup.mem_inf.1 d.2
    have hd' : (d : G) * (g * a * g⁻¹) = g * a * g⁻¹ * d :=
      Subgroup.mem_centralizer_singleton_iff.1 hd
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hdC) hg,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g⁻¹ * (d : G) * g * a = g⁻¹ * ((d : G) * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * (d : G)) * g := by rw [hd']
      _ = a * (g⁻¹ * (d : G) * g) := by group
  · obtain ⟨hdC, hd⟩ := Subgroup.mem_inf.1 d.2
    have hd' : (d : G) * a = a * d := Subgroup.mem_centralizer_singleton_iff.1 hd
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg hdC) (inv_mem hg),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g * (d : G) * g⁻¹ * (g * a * g⁻¹) = g * ((d : G) * a) * g⁻¹ := by group
      _ = g * (a * (d : G)) * g⁻¹ := by rw [hd']
      _ = g * a * g⁻¹ * (g * (d : G) * g⁻¹) := by group

theorem central_lift_facts
    [Finite G] (hI : Co1InvolutionFacts) {t : G}
    (ht : t ∈ Subgroup.centralizer ({z} : Set G)) (h2 : orderOf t = 2) (hQ : t ∉ leechQ z)
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7) :
    (co1Fix (L.φ ⟨t, ht⟩)).ncard *
        Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1)) =
          2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 ∧
      (∀ q ∈ leechQ z, L.vec q ∈ co1Fix (L.φ ⟨t, ht⟩) → t * q = q * t) ∧
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 17 := by
  obtain ⟨hle, heq⟩ := L.involution_bounds ht
  obtain ⟨h1a, h1b⟩ := hI.1 _ (L.orderOf_φ ht h2 hQ)
  rw [hcard] at hle heq
  have hattain : (co1Fix (L.φ ⟨t, ht⟩)).ncard *
      Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1)) =
        2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 := by
    generalize (co1Fix (L.φ ⟨t, ht⟩)).ncard *
      Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1)) = N at hle h1a ⊢
    omega
  have hw := h1b hattain
  obtain ⟨hlam, hQc⟩ := heq (by rw [hattain]; norm_num)
  refine ⟨hattain, hlam, ?_⟩
  rw [hQc, hw]
  norm_num

theorem exists_conj_of_inv_mem
    {t x : G} (ht : t ∈ Subgroup.centralizer ({z} : Set G))
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) (ht2 : t * t = 1) (hx2 : x * x = 1)
    (hq' : t⁻¹ * x ∈ leechQ z)
    (hft : ∀ q ∈ leechQ z, L.vec q ∈ co1Fix (L.φ ⟨t, ht⟩) → t * q = q * t)
    (hfx : ∀ q ∈ leechQ z, L.vec q ∈ co1Fix (L.φ ⟨x, hx⟩) → x * q = q * x) :
    ∃ p ∈ leechQ z, p * t * p⁻¹ = x ∨ p * (t * z) * p⁻¹ = x := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨q', hq'def⟩ : ∃ q', q' = t⁻¹ * x := ⟨_, rfl⟩
  rw [← hq'def] at hq'
  have hx_eq : x = t * q' := by rw [hq'def, mul_inv_cancel_left]
  have hq'C : q' ∈ Subgroup.centralizer ({z} : Set G) := L.mem_centralizer hq'
  have hφ : L.φ ⟨x, hx⟩ = L.φ ⟨t, ht⟩ := by
    have : (⟨x, hx⟩ : Subgroup.centralizer ({z} : Set G)) = ⟨t, ht⟩ * ⟨q', hq'C⟩ :=
      Subtype.ext hx_eq
    rw [this, map_mul, (L.φ_ker ⟨q', hq'C⟩).2 hq', mul_one]
  have hq'inv : t * q' * t⁻¹ = q'⁻¹ := by
    have h : t * q' * t * q' = 1 := by
      calc t * q' * t * q' = t * q' * (t * q') := by group
        _ = x * x := by rw [← hx_eq]
        _ = 1 := hx2
    calc t * q' * t⁻¹ = t * q' * t := by rw [hti]
      _ = (t * q' * t * q') * q'⁻¹ := by group
      _ = q'⁻¹ := by rw [h, one_mul]
  have hfix : L.vec q' ∈ co1Fix (L.φ ⟨t, ht⟩) := by
    show co1Act (L.φ ⟨t, ht⟩) (L.vec q') = L.vec q'
    rw [← L.vec_conj' ht hq', hq'inv, L.vec_inv hq']
  have horth : ∀ p ∈ leechQ z, L.vec p ∈ co1Fix (L.φ ⟨t, ht⟩) → q' * p = p * q' := by
    intro p hp hpf
    have h1 := hft p hp hpf
    have h2 := hfx p hp (by rw [hφ]; exact hpf)
    have h3 : t * (q' * p) = t * (p * q') := by
      calc t * (q' * p) = (t * q') * p := by rw [mul_assoc]
        _ = x * p := by rw [← hx_eq]
        _ = p * x := h2
        _ = p * (t * q') := by rw [← hx_eq]
        _ = (p * t) * q' := by rw [mul_assoc]
        _ = (t * p) * q' := by rw [h1]
        _ = t * (p * q') := by rw [mul_assoc]
    exact mul_left_cancel h3
  obtain ⟨w, hw⟩ := Leech.exists_add_eq_of_forall_bil₀_eq_zero (g := L.φ ⟨t, ht⟩)
    (L.φ_mul_self ht ht2) (u := L.vec q') (fun v hv => by
      obtain ⟨p, hp, rfl⟩ := L.vec_surj v
      exact (L.comm_eq_one_iff hq' hp).1
        (commutatorElement_eq_one_iff_mul_comm.2 (horth p hp hv)))
  obtain ⟨r, hr, rfl⟩ := L.vec_surj w
  have htrt : t * r * t⁻¹ ∈ leechQ z := L.conj_mem' ht hr
  set e := r * (t * r * t⁻¹)⁻¹ with he
  have heQ : e ∈ leechQ z := mul_mem hr (inv_mem htrt)
  have hve : L.vec e = L.vec q' := by
    rw [he, L.vec_mul r hr _ (inv_mem htrt), L.vec_inv htrt, L.vec_conj' ht hr, add_comm]
    exact hw
  have hrt : r * t * r⁻¹ = e * t := by
    rw [he]
    group
  have hxe : x = q'⁻¹ * t := by
    calc x = t * q' := hx_eq
      _ = (t * q' * t⁻¹) * t := by group
      _ = q'⁻¹ * t := by rw [hq'inv]
  rcases L.eq_or_eq_mul_z heQ (inv_mem hq') (by rw [hve, L.vec_inv hq']) with h | h
  · exact ⟨r, hr, Or.inl (by rw [hrt, h, hxe])⟩
  · refine ⟨r, hr, Or.inr ?_⟩
    have hzr : r * z * r⁻¹ = z := by
      rw [L.extraspecial.central r hr]
      group
    have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.1 ht
    calc r * (t * z) * r⁻¹ = (r * t * r⁻¹) * (r * z * r⁻¹) := by group
      _ = (q'⁻¹ * z * t) * z := by rw [hrt, h, hzr]
      _ = q'⁻¹ * (z * t) * z := by group
      _ = q'⁻¹ * (t * z) * z := by rw [hzt]
      _ = q'⁻¹ * t * (z * z) := by group
      _ = x := by rw [L.z_mul_self, mul_one, hxe]

theorem conj_not_mem {t g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (hQ : t ∉ leechQ z) :
    g * t * g⁻¹ ∉ leechQ z := by
  intro h
  apply hQ
  have := L.conj_mem' (inv_mem hg) h
  simpa [mul_assoc] using this

theorem leechCosetData
    [Finite G] (hI : Co1InvolutionFacts) : LeechCosetData z := by
  intro t ht h2 hQ hcard g hg hmem
  have hx : g * t * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hg ht) (inv_mem hg)
  have hx2 : orderOf (g * t * g⁻¹) = 2 := orderOf_conj_eq_two g h2
  have hxcard := (card_inf_centralizer_conj hg t).trans hcard
  obtain ⟨-, hft, -⟩ := L.central_lift_facts hI ht h2 hQ hcard
  obtain ⟨-, hfx, -⟩ := L.central_lift_facts hI hx hx2 (L.conj_not_mem hg hQ) hxcard
  exact L.exists_conj_of_inv_mem ht hx (mul_self_eq_one_of_orderOf_eq_two h2)
    (mul_self_eq_one_of_orderOf_eq_two hx2) hmem hft hfx

theorem leechInvolutionData
    [Finite G] (hI : Co1InvolutionFacts) : LeechInvolutionData z := by
  refine ⟨?_, ?_⟩
  · intro r₀ hr₀ h2 hQ hcard x hx hx2 hxQ
    obtain ⟨hatt, -, -⟩ := L.central_lift_facts hI hr₀ h2 hQ hcard
    obtain ⟨γ, hγ⟩ := hI.2.1 _ _ (L.orderOf_φ hr₀ h2 hQ) (L.orderOf_φ hx hx2 hxQ) hatt
    obtain ⟨c, rfl⟩ := L.φ_surj γ
    refine ⟨c, c.2, fun k hk => ?_⟩
    have hy : orderOf (c * (⟨r₀, hr₀⟩ : Subgroup.centralizer ({z} : Set G)) * c⁻¹ * ⟨x, hx⟩) =
        2 ^ k := (Subgroup.orderOf_coe _).symm.trans hk
    have hdvd := orderOf_map_dvd L.φ
      (c * (⟨r₀, hr₀⟩ : Subgroup.centralizer ({z} : Set G)) * c⁻¹ * ⟨x, hx⟩)
    rw [hy] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    refine hγ j ?_
    have hmap : L.φ (c * (⟨r₀, hr₀⟩ : Subgroup.centralizer ({z} : Set G)) * c⁻¹ * ⟨x, hx⟩) =
        L.φ c * L.φ ⟨r₀, hr₀⟩ * (L.φ c)⁻¹ * L.φ ⟨x, hx⟩ := by
      simp only [map_mul, map_inv]
    rw [← hmap, hj]
  · intro r hr r' hr' h2 h2' hQ hQ' hcard hcard'
    obtain ⟨hatt, -, -⟩ := L.central_lift_facts hI hr h2 hQ hcard
    obtain ⟨hatt', hfr', -⟩ := L.central_lift_facts hI hr' h2' hQ' hcard'
    obtain ⟨γ, hγ⟩ := isConj_iff.1 (hI.2.2 _ _ (L.orderOf_φ hr h2 hQ)
      (L.orderOf_φ hr' h2' hQ') hatt hatt')
    obtain ⟨c, rfl⟩ := L.φ_surj γ
    have hx : (c : G) * r * (c : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem c.2 hr) (inv_mem c.2)
    have hx2 : orderOf ((c : G) * r * (c : G)⁻¹) = 2 := orderOf_conj_eq_two (c : G) h2
    have hxcard := (card_inf_centralizer_conj c.2 r).trans hcard
    obtain ⟨-, hfx, -⟩ := L.central_lift_facts hI hx hx2 (L.conj_not_mem c.2 hQ) hxcard
    have hφx : L.φ ⟨(c : G) * r * (c : G)⁻¹, hx⟩ = L.φ ⟨r', hr'⟩ := by
      rw [← hγ]
      have : (⟨(c : G) * r * (c : G)⁻¹, hx⟩ : Subgroup.centralizer ({z} : Set G)) =
          c * ⟨r, hr⟩ * c⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have hmem : r'⁻¹ * ((c : G) * r * (c : G)⁻¹) ∈ leechQ z := by
      refine (L.φ_ker ⟨r'⁻¹ * ((c : G) * r * (c : G)⁻¹), mul_mem (inv_mem hr') hx⟩).1 ?_
      have : (⟨r'⁻¹ * ((c : G) * r * (c : G)⁻¹), mul_mem (inv_mem hr') hx⟩ :
          Subgroup.centralizer ({z} : Set G)) = ⟨r', hr'⟩⁻¹ * ⟨(c : G) * r * (c : G)⁻¹, hx⟩ := rfl
      rw [this, map_mul, map_inv, hφx, inv_mul_cancel]
    obtain ⟨p, hp, hpx⟩ := L.exists_conj_of_inv_mem hr' hx (mul_self_eq_one_of_orderOf_eq_two h2')
      (mul_self_eq_one_of_orderOf_eq_two hx2) hmem hfr' hfx
    have hzc : (c : G) * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
    rcases hpx with hpx | hpx
    · refine ⟨(c : G)⁻¹ * p, mul_mem (inv_mem c.2) (L.mem_centralizer hp), Or.inl ?_⟩
      calc (c : G)⁻¹ * p * r' * ((c : G)⁻¹ * p)⁻¹ = (c : G)⁻¹ * (p * r' * p⁻¹) * (c : G) := by
            group
        _ = (c : G)⁻¹ * ((c : G) * r * (c : G)⁻¹) * (c : G) := by rw [hpx]
        _ = r := by group
    · have h4 : p * z * p⁻¹ = z := by
        rw [L.extraspecial.central p hp]
        group
      have h5 : p * r' * p⁻¹ * z = (c : G) * r * (c : G)⁻¹ := by
        calc p * r' * p⁻¹ * z = p * r' * p⁻¹ * (p * z * p⁻¹) := by rw [h4]
          _ = p * (r' * z) * p⁻¹ := by group
          _ = _ := hpx
      have h6 : p * r' * p⁻¹ = (c : G) * r * (c : G)⁻¹ * z := by
        calc p * r' * p⁻¹ = (p * r' * p⁻¹ * z) * z := by
              rw [mul_assoc _ z z, L.z_mul_self, mul_one]
          _ = (c : G) * r * (c : G)⁻¹ * z := by rw [h5]
      have hcz : (c : G)⁻¹ * z * c = z := by
        calc (c : G)⁻¹ * z * c = (c : G)⁻¹ * (z * c) := by group
          _ = (c : G)⁻¹ * (c * z) := by rw [hzc]
          _ = z := by group
      refine ⟨(c : G)⁻¹ * p, mul_mem (inv_mem c.2) (L.mem_centralizer hp), Or.inr ?_⟩
      calc (c : G)⁻¹ * p * r' * ((c : G)⁻¹ * p)⁻¹ = (c : G)⁻¹ * (p * r' * p⁻¹) * (c : G) := by
            group
        _ = (c : G)⁻¹ * ((c : G) * r * (c : G)⁻¹ * z) * (c : G) := by rw [h6]
        _ = r * ((c : G)⁻¹ * z * c) := by group
        _ = r * z := by rw [hcz]

theorem leechData_involution_one
    [Finite G] (hI : Co1InvolutionFacts) :
    ∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) ≤
        2 ^ 46 * 3 ^ 5 * 5 ^ 2 * 7 := by
  intro t ht h2 hQ
  obtain ⟨hle, -⟩ := L.involution_bounds ht
  obtain ⟨h1a, -⟩ := hI.1 _ (L.orderOf_φ ht h2 hQ)
  calc Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      ≤ 2 * ((co1Fix (L.φ ⟨t, ht⟩)).ncard *
          Nat.card ↥(Subgroup.centralizer ({L.φ ⟨t, ht⟩} : Set Co1))) := hle
    _ ≤ 2 * (2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7) := Nat.mul_le_mul_left 2 h1a
    _ ≤ 2 ^ 46 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num

theorem leechData_involution_two
    [Finite G] (hI : Co1InvolutionFacts) :
    ∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
        2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 17 :=
  fun _ ht h2 hQ hcard => (L.central_lift_facts hI ht h2 hQ hcard).2.2

end LeechSystem

end CFSG.Monster.GMS
