module

public import CFSG.Quasithin.Background.Asc81cPfTrans2

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W]
  {G : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))} {X₀ Y₀ : Subgroup (MulAut W)}

omit [Finite W] in
theorem no_swap (hodd : Odd (Nat.card G)) {g : MulAut W}
    (hg : g ∈ G) {Z Z' : Subgroup (MulAut W)} (hne : Z ≠ Z')
    (h1 : Z.map (MulAut.conj g).toMonoidHom = Z')
    (h2 : Z'.map (MulAut.conj g).toMonoidHom = Z) : False := by
  have hgg : g * g ∈ Subgroup.normalizer (Z : Set (MulAut W)) := by
    have h3 : Z.map (MulAut.conj (g * g)).toMonoidHom = Z := by
      rw [← map_conj_map_conj, h1, h2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h3
  have hgodd : Odd (orderOf g) := odd_orderOf_of_mem hodd hg
  obtain ⟨m, hm⟩ := hgodd
  have hg' : g = (g * g) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul]
    calc g = g ^ (orderOf g + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      _ = g ^ (2 * (m + 1)) := by rw [hm]; ring_nf
  have hgN : g ∈ Subgroup.normalizer (Z : Set (MulAut W)) := by
    rw [hg']
    exact Subgroup.pow_mem _ hgg _
  have h3 : Z.map (MulAut.conj g).toMonoidHom = Z := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgN
  rw [h3] at h1
  exact hne h1

@[expose] def oddU (G Z : Subgroup (MulAut W)) : Subgroup W := fixV Z ⊓ commSub ⊤ G

theorem TransSetting.oddU_inf_eq_bot (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    {Z Z' : Subgroup (MulAut W)} (hZ : Z ∈ Ω) (hZ' : Z' ∈ Ω) (hne : Z ≠ Z') :
    oddU G Z ⊓ oddU G Z' = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨hv1, hv2⟩, hv3, -⟩
  have h1 : v ∈ fixV G ⊓ commSub ⊤ G := by
    rw [← hT.fixV_inf_eq hW hX₀ hY₀ hnc hZ hZ' hne]
    exact ⟨⟨hv1, hv3⟩, hv2⟩
  rwa [fixV_inf_commSub_eq_bot' hW hodd] at h1

omit [Finite W] in
theorem oddU_map_conj {G Z : Subgroup (MulAut W)} {y : MulAut W} (hy : y ∈ G) {u : W}
    (hu : u ∈ oddU G Z) : y u ∈ oddU G (Z.map (MulAut.conj y).toMonoidHom) := by
  refine ⟨?_, commSub_stable' hy hu.2⟩
  rw [fixV_map_conj]
  exact ⟨u, hu.1, rfl⟩

theorem card_fixV_eq_mul_oddU (hW : ∀ w : W, w ^ 2 = 1) {G Z : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card G)) (hZG : Z ≤ G) :
    Nat.card (fixV Z) = Nat.card (fixV G) * Nat.card (oddU G Z) := by
  have hbot : fixV G ⊓ oddU G Z = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, -, hv2⟩
    have h1 : v ∈ fixV G ⊓ commSub ⊤ G := ⟨hv1, hv2⟩
    rwa [fixV_inf_commSub_eq_bot' hW hodd] at h1
  have heq : fixV G ⊔ oddU G Z = fixV Z := by
    refine le_antisymm (sup_le (fun v hv z hz => hv z (hZG hz)) inf_le_left) ?_
    intro v hv
    have hv' : v ∈ fixV G ⊔ commSub ⊤ G := by
      rw [fixV_sup_commSub_eq_top' hW hodd]
      exact Subgroup.mem_top v
    obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv'
    have hwZ : w ∈ fixV Z := by
      have h1 := (fixV Z).mul_mem ((fixV Z).inv_mem (fun z hz => hc z (hZG hz))) hv
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem_sup hc ⟨hwZ, hw⟩
  rw [← heq, card_sup_of_inf_eq_bot hbot]

theorem card_commSub_G_eq (hW : ∀ w : W, w ^ 2 = 1) {G Z : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card G)) (hZG : Z ≤ G) (hZodd : Odd (Nat.card Z)) :
    Nat.card (commSub (⊤ : Subgroup W) G) =
      Nat.card (oddU G Z) * Nat.card (commSub (⊤ : Subgroup W) Z) := by
  have h1 := card_fixV_mul_card_commSub hW hodd
  have h2 := card_fixV_mul_card_commSub hW hZodd
  rw [card_fixV_eq_mul_oddU hW hodd hZG, ← h1, mul_assoc] at h2
  have hpos : 0 < Nat.card (fixV G) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm

@[expose] def normSet (Ω : Set (Subgroup (MulAut W))) (A : Subgroup (MulAut W)) :
    Set (Subgroup (MulAut W)) :=
  {B | B ∈ Ω ∧ B ≠ A ∧ ∃ x ∈ A, x ≠ 1 ∧ B.map (MulAut.conj x).toMonoidHom = B}

theorem TransSetting.oddU_ne_bot (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    {B : Subgroup (MulAut W)} (hB : B ∈ Ω) : oddU G B ≠ ⊥ := by
  intro h0
  have hBh := (hT.hyp B hB).1
  have h1 := card_fixV_eq_mul_oddU hW hodd hBh.1
  rw [h0, Subgroup.card_bot, mul_one] at h1
  have hfix : ∀ B' ∈ Ω, fixV B' = fixV B := by
    intro B' hB'
    have hle : fixV G ≤ fixV B' := fun v hv z hz => hv z ((hT.hyp B' hB').1.1 hz)
    have hcard : Nat.card (fixV B') = Nat.card (fixV B) := by
      obtain ⟨g, -, rfl⟩ := hT.trans B hB B' hB'
      rw [fixV_map_conj, Subgroup.card_map_of_injective g.injective]
    have heq : fixV G = fixV B' := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h1])
    rw [← heq, Subgroup.eq_of_le_of_card_ge
      (show fixV G ≤ fixV B from fun v hv z hz => hv z (hBh.1 hz)) h1.le]
  have hXY := eq_of_fixV_eq hW (hT.hyp X₀ hX₀).1 (hT.hyp Y₀ hY₀).1
    ((hfix X₀ hX₀).trans (hfix Y₀ hY₀).symm)
  exact hnc (hXY ▸ commutes_self_of_isCyclic (hT.hyp X₀ hX₀).1.2.2.1)

theorem TransSetting.normSet_subset (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    {A B : Subgroup (MulAut W)} (hA : A ∈ Ω) (hBA : B ∈ normSet Ω A) :
    oddU G B ≤ commSub (⊤ : Subgroup W) A ∧
      ∀ B' ∈ normSet Ω A, ∃ y ∈ A, B' = B.map (MulAut.conj y).toMonoidHom := by
  classical
  have hsub : ∀ B ∈ normSet Ω A, oddU G B ≤ commSub (⊤ : Subgroup W) A := by
    rintro B ⟨hB, hBA, x, hx, hx1, hxB⟩
    have hAh := (hT.hyp A hA).1
    have hzp : Subgroup.zpowers x ≤ A := (Subgroup.zpowers_le).2 hx
    have hzp1 : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 ((Subgroup.zpowers_eq_bot).1 h)
    have hzpodd : Odd (Nat.card (Subgroup.zpowers x)) :=
      Odd.of_dvd_nat hAh.2.2.2.1 (Subgroup.card_dvd_of_le hzp)
    have hxN : x ∈ Subgroup.normalizer (B : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hxB
    have hinv : ∀ b ∈ Subgroup.zpowers x, ∀ m ∈ oddU G B, b m ∈ oddU G B := by
      intro b hb m hm
      exact ⟨fixV_stable_of_normalizer ((Subgroup.zpowers_le.2 hxN) hb) hm.1,
        commSub_stable' (hAh.1 (hzp hb)) hm.2⟩
    obtain ⟨hdec, -⟩ := B1.coprime_decomp hW hzpodd (M := oddU G B) hinv
    have h1 : oddU G B ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
      rw [fixV_eq_of_le hW hAh hzp hzp1, eq_bot_iff]
      rintro v ⟨⟨hv1, hv2⟩, hv3⟩
      have h2 : v ∈ fixV G ⊓ commSub ⊤ G := by
        rw [← hT.fixV_inf_eq hW hX₀ hY₀ hnc hB hA hBA]
        exact ⟨⟨hv1, hv3⟩, hv2⟩
      rwa [fixV_inf_commSub_eq_bot' hW hodd] at h2
    rw [h1, bot_sup_eq] at hdec
    rw [← hdec, ← commSub_eq_of_le hW hAh hzp hzp1]
    exact commSub_mono le_top le_rfl
  refine ⟨hsub B hBA, ?_⟩
  obtain ⟨hB, hBA', x, hx, hx1, hxB⟩ := hBA
  have hAh := (hT.hyp A hA).1
  let N : Subgroup (MulAut W) := A ⊓ Subgroup.normalizer (B : Set (MulAut W))
  have hmemN : ∀ y, y ∈ N ↔ y ∈ A ∧ B.map (MulAut.conj y).toMonoidHom = B := fun y =>
    ⟨fun h => ⟨h.1, Subgroup.mem_normalizer_iff_map_conj_eq.1 h.2⟩,
      fun h => ⟨h.1, Subgroup.mem_normalizer_iff_map_conj_eq.2 h.2⟩⟩
  have hUB := hsub B ⟨hB, hBA', x, hx, hx1, hxB⟩
  have hU1 := hT.oddU_ne_bot hW hX₀ hY₀ hnc hodd hB
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ oddU G B, u ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hU1 ((Subgroup.eq_bot_iff_forall _).2 hall)
  have hstab : ∀ y ∈ A, ∀ u ∈ oddU G B, u ≠ 1 → y u ∈ oddU G B → y ∈ N := by
    intro y hy u hu hu1 hyu
    refine (hmemN y).2 ⟨hy, ?_⟩
    by_contra hne
    have h1 : y u ∈ oddU G B ⊓ oddU G (B.map (MulAut.conj y).toMonoidHom) :=
      ⟨hyu, oddU_map_conj (hAh.1 hy) hu⟩
    rw [hT.oddU_inf_eq_bot hW hX₀ hY₀ hnc hodd hB (hT.inv y (hAh.1 hy) B hB) (Ne.symm hne)] at h1
    exact hu1 (y.injective (h1.trans (map_one y).symm))
  have hNle : Nat.card N + 1 ≤ Nat.card (oddU G B) := by
    have hmem : ∀ y : N, (y : MulAut W) u₀ ∈ ((oddU G B : Set W) \ {1}) := by
      intro y
      refine ⟨⟨fixV_stable_of_normalizer y.2.2 hu₀.1, commSub_stable' (hAh.1 y.2.1) hu₀.2⟩,
        fun h0 => hu₀1 ?_⟩
      have h1 : (y : MulAut W) u₀ = (y : MulAut W) 1 := by rw [map_one]; exact h0
      exact (y : MulAut W).injective h1
    let f : N → ↥((oddU G B : Set W) \ {1}) := fun y => ⟨_, hmem y⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : MulAut W) u₀ = (b : MulAut W) u₀ := congrArg Subtype.val hab
      have h2 : ((b : MulAut W)⁻¹ * a) u₀ = u₀ := by
        rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
      have hba : (b : MulAut W)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem b.2.1) a.2.1
      by_contra hne
      have hne' : (b : MulAut W)⁻¹ * a ≠ 1 := fun h => hne (Subtype.ext (by
        rw [inv_mul_eq_one] at h
        exact h.symm))
      have hzp : Subgroup.zpowers ((b : MulAut W)⁻¹ * a) ≤ A := (Subgroup.zpowers_le).2 hba
      have hzp1 : Subgroup.zpowers ((b : MulAut W)⁻¹ * a) ≠ ⊥ := fun h =>
        hne' ((Subgroup.zpowers_eq_bot).1 h)
      have h3 : u₀ ∈ fixV A := by
        rw [← fixV_eq_of_le hW hAh hzp hzp1]
        exact mem_fixV_zpowers h2
      have h4 : u₀ ∈ fixV G ⊓ commSub ⊤ G := by
        rw [← hT.fixV_inf_eq hW hX₀ hY₀ hnc hB hA hBA']
        exact ⟨⟨hu₀.1, h3⟩, hu₀.2⟩
      rw [fixV_inf_commSub_eq_bot' hW hodd] at h4
      exact hu₀1 h4
    have h1 := Nat.card_le_card_of_injective f hf
    rw [card_diff_one] at h1
    have h2 : 0 < Nat.card (oddU G B) := Nat.card_pos
    omega
  have : Fintype W := Fintype.ofFinite W
  have := finite_mulAut (W := W)
  have : Fintype (MulAut W) := Fintype.ofFinite _
  let sA : Finset (MulAut W) := (A : Set (MulAut W)).toFinset
  let sU : Finset W := ((oddU G B : Set W) \ {1}).toFinset
  let tV : Finset W := ((commSub (⊤ : Subgroup W) A : Set W) \ {1}).toFinset
  let f : MulAut W × W → W := fun p => p.1 p.2
  have hmemS : ∀ p : MulAut W × W, p ∈ sA ×ˢ sU ↔ p.1 ∈ A ∧ p.2 ∈ oddU G B ∧ p.2 ≠ 1 := by
    intro p
    simp only [sA, sU, Finset.mem_product, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff]
  have hmemT : ∀ w, w ∈ tV ↔ w ∈ commSub (⊤ : Subgroup W) A ∧ w ≠ 1 := by
    intro w
    simp only [tV, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  have hfA : ∀ p ∈ sA ×ˢ sU, f p ∈ commSub (⊤ : Subgroup W) A ∧ f p ≠ 1 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (hmemS p).1 hp
    refine ⟨commSub_stable' h1 (hUB h2), fun h0 => h3 ?_⟩
    have h4 : p.1 p.2 = p.1 1 := by rw [map_one]; exact h0
    exact p.1.injective h4
  have hfib : ∀ b : W, ((sA ×ˢ sU).filter fun p => f p = b).card ≤ Nat.card N := by
    intro b
    by_cases hempty : ((sA ×ˢ sU).filter fun p => f p = b) = ∅
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.2 hempty
    obtain ⟨hp₀s, hp₀b⟩ := Finset.mem_filter.1 hp₀
    obtain ⟨hp₀1, -, -⟩ := (hmemS p₀).1 hp₀s
    calc ((sA ×ˢ sU).filter fun p => f p = b).card ≤ (N : Set (MulAut W)).toFinset.card := by
          refine Finset.card_le_card_of_injOn (fun p => p₀.1⁻¹ * p.1) ?_ ?_
          · intro p hp
            obtain ⟨hps, hpb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
            obtain ⟨hp1, hp2, hp3⟩ := (hmemS p).1 hps
            rw [Finset.mem_coe, Set.mem_toFinset, SetLike.mem_coe]
            refine hstab _ (A.mul_mem (A.inv_mem hp₀1) hp1) p.2 hp2 hp3 ?_
            have h1 : (p₀.1⁻¹ * p.1) p.2 = p₀.2 := by
              rw [MulAut.mul_apply, show p.1 p.2 = b from hpb, ← hp₀b, MulAut.inv_apply_self]
            rw [h1]
            exact ((hmemS p₀).1 hp₀s).2.1
          · intro p hp q hq hpq
            obtain ⟨hps, hpb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
            obtain ⟨hqs, hqb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
            have h1 : p.1 = q.1 := mul_left_cancel hpq
            have h2 : p.1 p.2 = q.1 q.2 := (show p.1 p.2 = b from hpb).trans hqb.symm
            rw [h1] at h2
            exact Prod.ext h1 (q.1.injective h2)
      _ = Nat.card N := by rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  have hsA : sA.card = Nat.card A := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have hsU : sU.card = Nat.card (oddU G B) - 1 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one]
  have htV : tV.card = Nat.card A := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one, card_commSub hAh]
    rfl
  have hsurj : ∀ w ∈ commSub (⊤ : Subgroup W) A, w ≠ 1 →
      ∃ y ∈ A, ∃ u ∈ oddU G B, u ≠ 1 ∧ y u = w := by
    intro w hw hw1
    by_contra hnot
    push Not at hnot
    have hmaps : ∀ p ∈ sA ×ˢ sU, f p ∈ tV.erase w := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := (hmemS p).1 hp
      refine Finset.mem_erase.2 ⟨hnot p.1 h1 p.2 h2 h3, (hmemT _).2 (hfA p hp)⟩
    have h1 := Finset.card_le_mul_card_image_of_maps_to hmaps _ fun b _ => hfib b
    rw [Finset.card_erase_of_mem ((hmemT w).2 ⟨hw, hw1⟩), Finset.card_product, hsA, hsU,
      htV] at h1
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : Nat.card N * (Nat.card A - 1) ≤ (Nat.card (oddU G B) - 1) * (Nat.card A - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (Nat.card (oddU G B) - 1) * (Nat.card A - 1) <
        (Nat.card (oddU G B) - 1) * Nat.card A := by
      have h4 : 0 < Nat.card (oddU G B) - 1 := by
        have : 1 ≤ Nat.card N := Nat.card_pos
        omega
      exact Nat.mul_lt_mul_of_pos_left (by omega) h4
    rw [mul_comm] at h1
    omega
  intro B' hB'
  have hU1' := hT.oddU_ne_bot hW hX₀ hY₀ hnc hodd hB'.1
  obtain ⟨u', hu', hu'1⟩ : ∃ u ∈ oddU G B', u ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hU1' ((Subgroup.eq_bot_iff_forall _).2 hall)
  obtain ⟨y, hy, u, hu, hu1, hyu⟩ := hsurj u' (hsub B' hB' hu') hu'1
  refine ⟨y, hy, ?_⟩
  by_contra hne
  have h1 : u' ∈ oddU G B' ⊓ oddU G (B.map (MulAut.conj y).toMonoidHom) :=
    ⟨hu', hyu ▸ oddU_map_conj (hAh.1 hy) hu⟩
  rw [hT.oddU_inf_eq_bot hW hX₀ hY₀ hnc hodd hB'.1 (hT.inv y (hAh.1 hy) B hB) hne] at h1
  exact hu'1 h1

omit [Finite W] in
theorem TransSetting.mem_normSet_map_conj (hT : TransSetting G Ω) {g : MulAut W} (hg : g ∈ G)
    {A B : Subgroup (MulAut W)} (hB : B ∈ normSet Ω A) :
    B.map (MulAut.conj g).toMonoidHom ∈ normSet Ω (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBΩ, hBA, x, hx, hx1, hxB⟩ := hB
  refine ⟨hT.inv g hg B hBΩ, fun h => hBA (map_conj_injective g h), g * x * g⁻¹,
    ⟨x, hx, rfl⟩, fun h => hx1 ?_, ?_⟩
  · have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · rw [map_conj_map_conj, show g * x * g⁻¹ * g = g * x by group, ← map_conj_map_conj, hxB]

omit [Finite W] in
theorem TransSetting.normSet_map_conj (hT : TransSetting G Ω) {g : MulAut W} (hg : g ∈ G)
    (A : Subgroup (MulAut W)) :
    normSet Ω (A.map (MulAut.conj g).toMonoidHom) =
      (fun B => B.map (MulAut.conj g).toMonoidHom) '' normSet Ω A := by
  ext B
  constructor
  · intro hB
    refine ⟨B.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_⟩
    · have h1 := hT.mem_normSet_map_conj (G.inv_mem hg) hB
      rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    · show (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B
      rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  · rintro ⟨B', hB', rfl⟩
    exact hT.mem_normSet_map_conj hg hB'

@[expose] def normSet' (Ω : Set (Subgroup (MulAut W))) (A : Subgroup (MulAut W)) :
    Set (Subgroup (MulAut W)) :=
  {B | B ∈ Ω ∧ A ∈ normSet Ω B}

omit [Finite W] in
theorem TransSetting.normSet'_map_conj (hT : TransSetting G Ω) {g : MulAut W} (hg : g ∈ G)
    (A : Subgroup (MulAut W)) :
    normSet' Ω (A.map (MulAut.conj g).toMonoidHom) =
      (fun B => B.map (MulAut.conj g).toMonoidHom) '' normSet' Ω A := by
  ext B
  constructor
  · rintro ⟨hBΩ, hAB⟩
    refine ⟨B.map (MulAut.conj g⁻¹).toMonoidHom, ⟨hT.inv _ (G.inv_mem hg) B hBΩ, ?_⟩, ?_⟩
    · have h1 := hT.mem_normSet_map_conj (G.inv_mem hg) hAB
      rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    · show (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B
      rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  · rintro ⟨B', ⟨hB'Ω, hAB'⟩, rfl⟩
    exact ⟨hT.inv g hg B' hB'Ω, hT.mem_normSet_map_conj hg hAB'⟩

theorem TransSetting.ncard_normSet_eq (hT : TransSetting G Ω) {A : Subgroup (MulAut W)}
    (hA : A ∈ Ω) : (normSet Ω A).ncard = (normSet' Ω A).ncard := by
  classical
  have hfin := finite_subgroups (W := W)
  have hΩfin : Ω.Finite := Set.toFinite Ω
  have hconst : ∀ B ∈ Ω, (normSet Ω B).ncard = (normSet Ω A).ncard ∧
      (normSet' Ω B).ncard = (normSet' Ω A).ncard := by
    intro B hB
    obtain ⟨g, hg, rfl⟩ := hT.trans A hA B hB
    rw [hT.normSet_map_conj hg, hT.normSet'_map_conj hg,
      Set.ncard_image_of_injective _ (map_conj_injective g),
      Set.ncard_image_of_injective _ (map_conj_injective g)]
    exact ⟨rfl, rfl⟩
  let Ωf := hΩfin.toFinset
  have hcardN : ∀ B ∈ Ωf, (normSet Ω B).ncard = (Ωf.filter fun C => C ∈ normSet Ω B).card := by
    intro B _
    rw [Set.ncard_eq_toFinset_card _ ((Set.toFinite Ω).subset (fun _ h => h.1))]
    congr 1
    ext C
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Ωf]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  have hcardN' : ∀ B ∈ Ωf,
      (normSet' Ω B).ncard = (Ωf.filter fun C => B ∈ normSet Ω C).card := by
    intro B _
    rw [Set.ncard_eq_toFinset_card _ ((Set.toFinite Ω).subset (fun _ h => h.1))]
    congr 1
    ext C
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Ωf, normSet']
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hsum : ∑ B ∈ Ωf, (normSet Ω B).ncard = ∑ B ∈ Ωf, (normSet' Ω B).ncard := by
    rw [Finset.sum_congr rfl hcardN, Finset.sum_congr rfl hcardN']
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hc1 : ∑ B ∈ Ωf, (normSet Ω B).ncard = Ωf.card * (normSet Ω A).ncard := by
    rw [Finset.sum_congr rfl fun B hB => (hconst B (hΩfin.mem_toFinset.1 hB)).1,
      Finset.sum_const, smul_eq_mul]
  have hc2 : ∑ B ∈ Ωf, (normSet' Ω B).ncard = Ωf.card * (normSet' Ω A).ncard := by
    rw [Finset.sum_congr rfl fun B hB => (hconst B (hΩfin.mem_toFinset.1 hB)).2,
      Finset.sum_const, smul_eq_mul]
  have hpos : 0 < Ωf.card := Finset.card_pos.2 ⟨A, hΩfin.mem_toFinset.2 hA⟩
  rw [hc1, hc2] at hsum
  exact Nat.eq_of_mul_eq_mul_left hpos hsum

theorem TransSetting.ncard_normSet_lt (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    {A B : Subgroup (MulAut W)} (hA : A ∈ Ω) (hBA : B ∈ normSet Ω A) :
    (normSet Ω A).ncard + 1 ≤ Nat.card A := by
  have := finite_mulAut (W := W)
  obtain ⟨-, hc⟩ := hT.normSet_subset hW hX₀ hY₀ hnc hodd hA hBA
  obtain ⟨-, -, x, hx, hx1, hxB⟩ := hBA
  have hsub : normSet Ω A ⊆
      (fun y => B.map (MulAut.conj y).toMonoidHom) '' ((A : Set (MulAut W)) \ {1}) := by
    intro B' hB'
    obtain ⟨y, hy, rfl⟩ := hc B' hB'
    by_cases hy1 : y = 1
    · refine ⟨x, ⟨hx, hx1⟩, ?_⟩
      show B.map (MulAut.conj x).toMonoidHom = B.map (MulAut.conj y).toMonoidHom
      rw [hxB, hy1, map_conj_one]
    · exact ⟨y, ⟨hy, hy1⟩, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_image_le (f := fun y => B.map (MulAut.conj y).toMonoidHom)
    (s := (A : Set (MulAut W)) \ {1}) (Set.toFinite _)
  have h2' : ((A : Set (MulAut W)) \ {1}).ncard = (A : Set (MulAut W)).ncard - 1 :=
    Set.ncard_sdiff_singleton_of_mem A.one_mem
  have h3 : (A : Set (MulAut W)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
  have h4 : 0 < Nat.card A := Nat.card_pos
  omega

theorem TransSetting.semiregular (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) (hodd : Odd (Nat.card G))
    {A K : Subgroup (MulAut W)} (hA : A ∈ Ω) (hK : K ∈ Ω) (hKA : K ≠ A) {x : MulAut W}
    (hx : x ∈ A) (hxK : K.map (MulAut.conj x).toMonoidHom = K) : x = 1 := by
  by_contra hx1
  have hAh := (hT.hyp A hA).1
  have hKO : K ∈ normSet Ω A := ⟨hK, hKA, x, hx, hx1, hxK⟩
  obtain ⟨g, hg, hgK⟩ := hT.trans K hK A hA
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'def
  have hA'Ω : A' ∈ Ω := hT.inv g hg A hA
  have hA'A : A' ≠ A := by
    intro h
    apply hKA
    apply map_conj_injective g
    show K.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj g).toMonoidHom
    rw [← hgK]
    exact h.symm
  have hA'O' : A' ∈ normSet' Ω A := by
    refine ⟨hA'Ω, hA, Ne.symm hA'A, g * x * g⁻¹, ⟨x, hx, rfl⟩, fun h => hx1 ?_, ?_⟩
    · have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    · rw [hgK, map_conj_map_conj, show g * x * g⁻¹ * g = g * x by group, ← map_conj_map_conj,
        hxK]
  have hA'O : A' ∉ normSet Ω A := by
    intro hA'
    obtain ⟨-, hc⟩ := hT.normSet_subset hW hX₀ hY₀ hnc hodd hA hKO
    obtain ⟨y, hy, hyA'⟩ := hc A' hA'
    have hyA : A.map (MulAut.conj y⁻¹).toMonoidHom = A :=
      map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic hAh.2.2.1 (A.inv_mem hy) hz
    refine no_swap hodd (G.mul_mem (G.inv_mem (hAh.1 hy)) hg) hKA ?_ ?_
    · rw [← map_conj_map_conj, ← hgK, hyA]
    · rw [← map_conj_map_conj, ← hA'def, hyA', map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hfree : ∀ h ∈ A, A'.map (MulAut.conj h).toMonoidHom = A' → h = 1 := by
    intro h hh hhA'
    by_contra hh1
    exact hA'O ⟨hA'Ω, hA'A, h, hh, hh1, hhA'⟩
  have hinv : ∀ h ∈ A, A'.map (MulAut.conj h).toMonoidHom ∈ normSet' Ω A := by
    intro h hh
    have hAh' : A.map (MulAut.conj h).toMonoidHom = A :=
      map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic hAh.2.2.1 hh hz
    refine ⟨hT.inv h (hAh.1 hh) A' hA'Ω, ?_⟩
    have h1 := hT.mem_normSet_map_conj (hAh.1 hh) hA'O'.2
    rwa [hAh'] at h1
  have hcard : Nat.card A ≤ (normSet' Ω A).ncard := by
    have h1 := Set.ncard_le_ncard_of_injOn (fun h => A'.map (MulAut.conj h).toMonoidHom)
      (s := (A : Set (MulAut W))) (t := normSet' Ω A) (fun h hh => hinv h hh) ?_ (Set.toFinite _)
    · rwa [← Nat.card_coe_set_eq] at h1
    · intro h hh h' hh' hhh
      have h2 : A'.map (MulAut.conj (h'⁻¹ * h)).toMonoidHom = A' := by
        rw [← map_conj_map_conj]
        show (A'.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h'⁻¹).toMonoidHom = A'
        rw [show A'.map (MulAut.conj h).toMonoidHom = A'.map (MulAut.conj h').toMonoidHom
          from hhh, map_conj_map_conj, inv_mul_cancel, map_conj_one]
      have h3 := hfree _ (A.mul_mem (A.inv_mem hh') hh) h2
      rw [inv_mul_eq_one] at h3
      exact h3.symm
  have h1 := hT.ncard_normSet_eq hA
  have h2 := hT.ncard_normSet_lt hW hX₀ hY₀ hnc hodd hA hKO
  omega

end Pf

end Asc81c

end CFSG.Quasithin
