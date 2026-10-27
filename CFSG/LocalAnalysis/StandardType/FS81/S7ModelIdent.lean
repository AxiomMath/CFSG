module

public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelWeyl
public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelOrbit
public import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIso

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

private theorem ncard_le_mul_ncard_of_fibers {α β : Type*} [Finite α]
    {s : Set α} {t : Set β} (ht : t.Finite) (f : α → β)
    (hmaps : ∀ a ∈ s, f a ∈ t) (c : ℕ)
    (hfib : ∀ b ∈ t, {a | a ∈ s ∧ f a = b}.ncard ≤ c) :
    s.ncard ≤ t.ncard * c := by
  classical
  have hs : s.Finite := Set.toFinite s
  have hsFintype := hs.fintype
  have htFintype := ht.fintype
  have hcart : (hs.toFinset : Set α).MapsTo f ht.toFinset := by
    intro a ha
    exact ht.mem_toFinset.mpr (hmaps a (hs.mem_toFinset.mp ha))
  have h := Finset.card_eq_sum_card_fiberwise (s := hs.toFinset) (t := ht.toFinset) (f := f) hcart
  rw [Set.ncard_eq_toFinset_card s hs, h]
  calc ∑ b ∈ ht.toFinset, (hs.toFinset.filter (fun a => f a = b)).card
      ≤ ∑ b ∈ ht.toFinset, c := by
        apply Finset.sum_le_sum
        intro b hb
        have hb' := hfib b (ht.mem_toFinset.mp hb)
        rwa [← Set.ncard_coe_finset (hs.toFinset.filter (fun a => f a = b)),
          show ((hs.toFinset.filter (fun a => f a = b) : Finset α) : Set α) =
            {a | a ∈ s ∧ f a = b} from by
              ext a; simp]
    _ = ht.toFinset.card * c := by rw [Finset.sum_const, smul_eq_mul]
    _ = t.ncard * c := by rw [← Set.ncard_eq_toFinset_card t ht]

section M6


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ncard_orbit_frameCoord_le (hK : Nat.card K = 2)
    (a : Fin (7 + 1) → ZMod 3) (ha : a ≠ 0) :
    (Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
      ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
        (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)}) ≤
      2 * (normalizerLines ⊤ (frameTorusE8 K)
        (TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a))).ncard := by
  classical
  have : Finite (adjointGroup .E8 K) := CFSG.LieType.Chevalley.generated_group_finite .E8 K
  let b : adjointGroup .E8 K :=
    TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a)
  let φ : (Fin (7 + 1) → ZMod 3) → adjointGroup .E8 K :=
    fun a' => TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a')
  let B : Set (Subgroup (adjointGroup .E8 K)) := normalizerLines ⊤ (frameTorusE8 K) b
  let A : Set (Fin (7 + 1) → ZMod 3) := {a' | Subgroup.zpowers (φ a') ∈ B}
  have hφinj : Function.Injective φ := by
    intro x y h
    exact Multiplicative.ofAdd.injective (TableBExcTwoTB.tE_injective TableBExcTwo.frameE8 h)
  have hbT : b ∈ frameTorusE8 K := ⟨Multiplicative.ofAdd a, rfl⟩
  have hb3 : b ^ 3 = 1 := (isElemAbelian_frameTorusE8 (K := K)).2 b hbT
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : Multiplicative.ofAdd a = 1 :=
      TableBExcTwoTB.tE_injective TableBExcTwo.frameE8 (by
        rw [show TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a) = b from rfl,
          h, map_one])
    exact ha (Multiplicative.ofAdd.injective (by simpa using h1))
  have hφrange : Set.range φ = (frameTorusE8 K : Set (adjointGroup .E8 K)) := by
    ext x; constructor
    · rintro ⟨a', rfl⟩
      exact ⟨Multiplicative.ofAdd a', rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨Multiplicative.toAdd u, by simp [φ]⟩
  have hBfin : B.Finite := by
    change (normalizerLines ⊤ (frameTorusE8 K) b).Finite
    rw [normalizerLines]
    refine (Set.Finite.image (fun g : adjointGroup .E8 K => Subgroup.zpowers (g * b * g⁻¹))
      (Set.toFinite ((⊤ ⊓ Subgroup.normalizer (frameTorusE8 K : Set (adjointGroup .E8 K))) :
        Set (adjointGroup .E8 K)))).subset ?_
    rintro Z ⟨g, hg, hgZ⟩
    exact ⟨g, hg, hgZ.symm⟩
  have hA_bound : A.ncard ≤ 2 * B.ncard := by
    have hfib : ∀ L ∈ B, {a' | a' ∈ A ∧ Subgroup.zpowers (φ a') = L}.ncard ≤ 2 := by
      intro L hL
      change L ∈ normalizerLines ⊤ (frameTorusE8 K) b at hL
      rw [normalizerLines] at hL
      obtain ⟨g, hg, hgL⟩ := hL
      have hyT : g * b * g⁻¹ ∈ frameTorusE8 K :=
        (Subgroup.mem_normalizer_iff.mp hg.2 b).mp hbT
      have hb_ord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
      have hy_ord : orderOf (g * b * g⁻¹) = 3 := by
        rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g b (g * b * g⁻¹) by
          show g * b = g * b * g⁻¹ * g
          group), hb_ord]
      have hy3 : (g * b * g⁻¹) ^ 3 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hy_ord]
      have hy1 : g * b * g⁻¹ ≠ 1 := by
        intro h
        apply hb1
        calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by group
      have hLsub : (L : Set (adjointGroup .E8 K)) ⊆ Set.range φ := by
        rw [hφrange, hgL]
        exact Subgroup.zpowers_le.mpr hyT
      have hLcard : (L : Set (adjointGroup .E8 K)).ncard ≤ 3 := by
        rw [hgL]
        change Nat.card (Subgroup.zpowers (g * b * g⁻¹)) ≤ 3
        rw [Nat.card_zpowers, hy_ord]
      have htarget : ((L : Set (adjointGroup .E8 K)) \ {1}).ncard ≤ 2 := by
        rw [Set.ncard_sdiff_singleton_of_mem (L.one_mem)]
        omega
      calc {a' | a' ∈ A ∧ Subgroup.zpowers (φ a') = L}.ncard
          ≤ (φ ⁻¹' ((L : Set (adjointGroup .E8 K)) \ {1})).ncard := by
            apply Set.ncard_le_ncard
            · intro a' ha'
              rw [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff]
              refine ⟨?_, ?_⟩
              · rw [← ha'.2]; exact Subgroup.mem_zpowers _
              · intro h1
                have hLbot : L = ⊥ := by
                  rw [← ha'.2]
                  exact Subgroup.zpowers_eq_bot.mpr h1
                have hyL : g * b * g⁻¹ ∈ L := by
                  rw [hgL]; exact Subgroup.mem_zpowers _
                rw [hLbot] at hyL
                exact hy1 (by simpa using hyL)
            · exact Set.toFinite _
        _ = ((L : Set (adjointGroup .E8 K)) \ {1}).ncard :=
            Set.ncard_preimage_of_injective_subset_range hφinj (Set.sdiff_subset.trans hLsub)
        _ ≤ 2 := htarget
    have hmaps : ∀ a' ∈ A, Subgroup.zpowers (φ a') ∈ B := fun a' ha' => ha'
    have hres := ncard_le_mul_ncard_of_fibers (s := A) (t := B) hBfin
      (fun a' => Subgroup.zpowers (φ a')) hmaps 2 hfib
    rwa [mul_comm] at hres
  have hOrb_sub : {u : Fin Tag.E8.rank → ZMod 3 |
        ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
          (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)} ⊆
      ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 '' A := by
    rintro u ⟨w, rfl⟩
    obtain ⟨n, hn, hkey⟩ := exists_mem_normalizer_frameTorusE8_torusAct hK w
    obtain ⟨a', ha', ha'Λ⟩ := hkey a
    refine ⟨a', ?_, ?_⟩
    · change Subgroup.zpowers (φ a') ∈ normalizerLines ⊤ (frameTorusE8 K) b
      rw [normalizerLines]
      refine ⟨n, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hn⟩, ?_⟩
      rw [ha']
    · rw [← ha'Λ]
  have hOrb_bound : (Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
        ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
          (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)}) ≤ 2 * B.ncard := by
    calc Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
            ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
              (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)}
        ≤ (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 '' A).ncard :=
          Set.ncard_le_ncard hOrb_sub (Set.Finite.image _ (Set.toFinite A))
      _ ≤ A.ncard := Set.ncard_image_le
      _ ≤ 2 * B.ncard := hA_bound
  simpa only [B, b] using hOrb_bound

theorem exists_conj_rootThree_of_ncard_normalizerLines_eq (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E8 K)} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E)
    {b : adjointGroup .E8 K} (hbE : b ∈ E) (hb1 : b ≠ 1)
    (h120 : (normalizerLines ⊤ E b).ncard = 120) :
    ∃ g : adjointGroup .E8 K, g * b * g⁻¹ = rootThree .E8 K (highRoot .E8) := by
  classical
  obtain ⟨c, hc⟩ := CFSG.StandardType.TableBExcTwoTB.exists_conj_frame_of_card_E8 hK hE hcard
  have hc' : E = (frameTorusE8 K).map (MulAut.conj c).toMonoidHom := hc
  let b₀ : adjointGroup .E8 K := c⁻¹ * b * c
  have hb_eq : b = c * b₀ * c⁻¹ := by dsimp only [b₀]; group
  have hrange : ((MulAut.conj c).toMonoidHom).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact (MulAut.conj c).surjective
  have hconj_b₀ : ((MulAut.conj c).toMonoidHom) b₀ = b := by
    show c * b₀ * c⁻¹ = b
    dsimp only [b₀]; group
  have h120₀ : (normalizerLines ⊤ (frameTorusE8 K) b₀).ncard = 120 := by
    have hinj : Function.Injective ((MulAut.conj c).toMonoidHom) := (MulAut.conj c).injective
    have h := ncard_normalizerLines_map ((MulAut.conj c).toMonoidHom) hinj (frameTorusE8 K) b₀
    rw [hrange, ← hc', hconj_b₀] at h
    rw [h120] at h
    exact h.symm
  have hb₀T : b₀ ∈ frameTorusE8 K := by
    have hbm : b ∈ (frameTorusE8 K).map (MulAut.conj c).toMonoidHom := by
      rw [← hc']; exact hbE
    obtain ⟨t, ht, hbt⟩ := hbm
    have : b₀ = t := by
      dsimp only [b₀]
      rw [← hbt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [this]
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    exact hb1 (by rw [hb_eq, h]; group)
  obtain ⟨u, hu⟩ := hb₀T
  let a : Fin (7 + 1) → ZMod 3 := Multiplicative.toAdd u
  have hba : TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a) = b₀ := by
    rw [show Multiplicative.ofAdd a = u from rfl]
    exact hu
  have ha : a ≠ 0 := by
    intro h0
    have hu1 : u = 1 := by
      rw [← ofAdd_toAdd u, show Multiplicative.toAdd u = 0 from h0]
      rfl
    exact hb₀1 (by rw [← hu, hu1, map_one])
  have hv : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a ≠ 0 := by
    intro h0
    exact ha (frameCoordHom_frameE8_injective (by rw [h0, map_zero]))
  have hbound : Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
        ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
          (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)} ≤ 240 := by
    have h := ncard_orbit_frameCoord_le hK a ha
    calc _ ≤ 2 * (normalizerLines ⊤ (frameTorusE8 K)
          (TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd a))).ncard := h
      _ = 2 * (normalizerLines ⊤ (frameTorusE8 K) b₀).ncard := by rw [hba]
      _ = 240 := by rw [h120₀]
  obtain ⟨w, hw⟩ :=
    eq_torusAct_frameCoord_of_ncard_le (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a) hv hbound
  obtain ⟨n, hn, hkey⟩ := exists_mem_normalizer_frameTorusE8_torusAct hK w
  obtain ⟨x, hx, hxΛ⟩ := hkey (Pi.single 0 1)
  obtain ⟨g₀, hg₀⟩ := exists_conj_tE_single_eq_rootThree (K := K)
  rcases hw with hw | hw
  · have hax : a = x := frameCoordHom_frameE8_injective (by rw [hxΛ, ← hw])
    have hb₀eq : b₀ = n * TableBExcTwoTB.tE K TableBExcTwo.frameE8
        (Multiplicative.ofAdd (Pi.single 0 1)) * n⁻¹ := by
      rw [← hba, hax, ← hx]
    refine ⟨g₀ * (c * n)⁻¹, ?_⟩
    calc g₀ * (c * n)⁻¹ * b * (g₀ * (c * n)⁻¹)⁻¹
        = g₀ * TableBExcTwoTB.tE K TableBExcTwo.frameE8
            (Multiplicative.ofAdd (Pi.single 0 1)) * g₀⁻¹ := by
          rw [hb_eq, hb₀eq]; group
      _ = rootThree .E8 K (highRoot .E8) := hg₀
  · have hax : a = -x := frameCoordHom_frameE8_injective (by rw [hw, map_neg, hxΛ])
    have hb₀eq : b₀ = (n * TableBExcTwoTB.tE K TableBExcTwo.frameE8
        (Multiplicative.ofAdd (Pi.single 0 1)) * n⁻¹)⁻¹ := by
      rw [← hba, hax, ofAdd_neg, map_inv, hx]
    have hg₀inv : ∃ g, g * (TableBExcTwoTB.tE K TableBExcTwo.frameE8
        (Multiplicative.ofAdd (Pi.single 0 1)))⁻¹ * g⁻¹ =
        rootThree .E8 K (highRoot .E8) := by
      refine ⟨EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) * g₀, ?_⟩
      have h1 : g₀ * (TableBExcTwoTB.tE K TableBExcTwo.frameE8
          (Multiplicative.ofAdd (Pi.single 0 1)))⁻¹ * g₀⁻¹ =
          (rootThree .E8 K (highRoot .E8))⁻¹ := by
        rw [← hg₀]; group
      have h2 := pinnedElt_mul_rootThree_mul_inv (K := K) (α := highRoot .E8)
        (isRoot_highRoot .E8)
      calc EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) * g₀ *
              (TableBExcTwoTB.tE K TableBExcTwo.frameE8
                (Multiplicative.ofAdd (Pi.single 0 1)))⁻¹ *
              (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) * g₀)⁻¹
          = EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) *
              (g₀ * (TableBExcTwoTB.tE K TableBExcTwo.frameE8
                (Multiplicative.ofAdd (Pi.single 0 1)))⁻¹ * g₀⁻¹) *
              (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))⁻¹ := by group
        _ = EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) *
              (rootThree .E8 K (highRoot .E8))⁻¹ *
              (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))⁻¹ := by rw [h1]
        _ = rootThree .E8 K (highRoot .E8) := by
              calc EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) *
                    (rootThree .E8 K (highRoot .E8))⁻¹ *
                    (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))⁻¹
                  = (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) *
                      rootThree .E8 K (highRoot .E8) *
                      (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))⁻¹)⁻¹ := by group
                _ = (rootThree .E8 K (highRoot .E8))⁻¹⁻¹ := by rw [h2]
                _ = rootThree .E8 K (highRoot .E8) := inv_inv _
    obtain ⟨g₁, hg₁⟩ := hg₀inv
    refine ⟨g₁ * (c * n)⁻¹, ?_⟩
    calc g₁ * (c * n)⁻¹ * b * (g₁ * (c * n)⁻¹)⁻¹
        = g₁ * (TableBExcTwoTB.tE K TableBExcTwo.frameE8
            (Multiplicative.ofAdd (Pi.single 0 1)))⁻¹ * g₁⁻¹ := by
          rw [hb_eq, hb₀eq]; group
      _ = rootThree .E8 K (highRoot .E8) := hg₁

theorem exists_mem_conj_eq_map_rootThree_of_ncard_normalizerLines_eq {G : Type} [Group G]
    (hK : Nat.card K = 2) (ι : adjointGroup .E8 K →* G) (hι : Function.Injective ι)
    {E : Subgroup G} (hEY : E ≤ ι.range) (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E)
    {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1) (h120 : (normalizerLines ι.range E b).ncard = 120) :
    ∃ y ∈ ι.range, y * b * y⁻¹ = ι (rootThree .E8 K (highRoot .E8)) := by
  have hE0 : (E.comap ι).map ι = E := Subgroup.map_comap_eq_self hEY
  obtain ⟨b₀, rfl⟩ := hEY hbE
  have hb₀E : b₀ ∈ E.comap ι := hbE
  have hb₀1 : b₀ ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hcard0 : 3 ^ 8 ≤ Nat.card (E.comap ι) := by
    rw [← Subgroup.card_map_of_injective hι, hE0]
    exact hcard
  have hlines : (normalizerLines ⊤ (E.comap ι) b₀).ncard = 120 := by
    rw [← ncard_normalizerLines_map ι hι (E.comap ι) b₀, hE0]
    exact h120
  obtain ⟨g, hg⟩ := exists_conj_rootThree_of_ncard_normalizerLines_eq hK
    (isElemAbelian_comap ι hι hE) hcard0 hb₀E hb₀1 hlines
  refine ⟨ι g, ⟨g, rfl⟩, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, hg]

theorem exists_hom_range_eq_apply_rootThree_eq {G : Type} [Group G]
    (hK : Nat.card K = 2) (ι : adjointGroup .E8 K →* G) (hι : Function.Injective ι)
    {E : Subgroup G} (hEY : E ≤ ι.range) (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E)
    {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1) (h120 : (normalizerLines ι.range E b).ncard = 120) :
    ∃ ι' : adjointGroup .E8 K →* G, Function.Injective ι' ∧ ι'.range = ι.range ∧
      ι' (rootThree .E8 K (highRoot .E8)) = b := by
  obtain ⟨y, ⟨y', rfl⟩, hy⟩ :=
    exists_mem_conj_eq_map_rootThree_of_ncard_normalizerLines_eq hK ι hι hEY hE hcard hbE hb1 h120
  refine ⟨(MulAut.conj (ι y')⁻¹).toMonoidHom.comp ι,
    (MulAut.conj (ι y')⁻¹).injective.comp hι, ?_, ?_⟩
  · ext g
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨y'⁻¹ * m * y', by simp only [map_mul, map_inv]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨y' * m * y'⁻¹, by simp only [map_mul, map_inv]; group⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hy]
    group


end M6

end CFSG.StandardType.FrameRoute.FS81

end
