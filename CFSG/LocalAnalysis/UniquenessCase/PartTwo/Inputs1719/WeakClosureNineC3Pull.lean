module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Coord3

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

structure CoordModel914 {P : Type} [Group P] [Finite P] (G L₀ T₀ Es : Subgroup P) : Prop where
  L_le : L₀ ≤ G
  T_le : T₀ ≤ G
  three_dvd : 3 ∣ Nat.card L₀
  sq : ∃ d ∈ T₀ ⊓ L₀, d ^ 2 ≠ 1
  mov : ∀ E : Subgroup P, E ≤ T₀ → IsElemAbelian 2 E →
    ∃ (H Xh : Subgroup P) (p : ℕ), MovWit914 L₀ T₀ E H Xh p
  fix : ∀ E : Subgroup P, E ≤ T₀ → IsElemAbelian 2 E → E ≠ ⊥ →
    (∃ (K Xh : Subgroup P) (p : ℕ), K ≤ G ∧ FixWit914 T₀ E K Xh p) ∨ E = Es
  normal : ∀ F : Subgroup P, F ≤ T₀ → T₀ ≤ normalizer (F : Set P) → IsElemAbelian 2 F →
    F = ⊥ ∨ F = Es ∨ (Nat.card F = 2 ∧ ∀ x ∈ F, x ≠ 1 → PairProp914 L₀ x)
  star : Es ≠ ⊥ → Es ≤ T₀ ∧ T₀ ≤ normalizer (Es : Set P) ∧ IsElemAbelian 2 Es ∧
    (∀ E : Subgroup P, E ≤ T₀ ⊓ centralizer (Es : Set P) → IsElemAbelian 2 E →
      MovStar914 L₀ T₀ Es E) ∧
    ∃ K : Subgroup P, K ≤ G ∧ (∃ Y : Subgroup P, TwoPTwoIrred K (K ⊓ T₀) Y 3) ∧
      Es ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (Es : Set P) ≤ K ∧ K ⊔ T₀ = G

section Pullback

variable {B P : Type} [Group B] [Group P] {ι : B →* P}

theorem pairProp_of_map (hι : Function.Injective ι) {L : Subgroup B} {L₀ : Subgroup P}
    (hL : L.map ι = L₀) {x : B} (h : PairProp914 L₀ (ι x)) : PairProp914 L x := by
  obtain ⟨l, hl, h2, hne⟩ := h
  rw [← hL] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  refine ⟨l', hl', ?_, fun h => hne ?_⟩
  · have h1 : (Subgroup.closure ({x, l' * x * l'⁻¹} : Set B)).map ι =
        Subgroup.closure {ι x, ι l' * ι x * (ι l')⁻¹} := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, map_mul, map_mul,
        map_inv]
    rw [← h1] at h2
    exact h2.of_equiv ((Subgroup.closure _).equivMapOfInjective ι hι).symm
  · have := congrArg ι h
    simpa [map_mul, map_inv] using this

theorem three_of_map (hι : Function.Injective ι) {G : Subgroup P} (hr : ι.range = G)
    {D : Subgroup B} {T₀ Xh : Subgroup P} (hD : D.map ι = T₀) (hXG : Xh ≤ G)
    (h : ∃ y ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3) :
    ∃ y ∈ closure {z | ∃ d ∈ D, ∃ x ∈ Xh.comap ι, z = d * x * d⁻¹}, orderOf y = 3 := by
  obtain ⟨z, hz, hzo⟩ := h
  have hS : ({w | ∃ d ∈ T₀, ∃ x ∈ Xh, w = d * x * d⁻¹} : Set P) =
      ι '' {w | ∃ d ∈ D, ∃ x ∈ Xh.comap ι, w = d * x * d⁻¹} := by
    ext w
    constructor
    · rintro ⟨d, hd, x, hx, rfl⟩
      rw [← hD] at hd
      obtain ⟨d', hd', rfl⟩ := hd
      have hx' : x ∈ ι.range := hr ▸ hXG hx
      obtain ⟨x', rfl⟩ := hx'
      exact ⟨d' * x' * d'⁻¹, ⟨d', hd', x', hx, rfl⟩, by simp [map_mul, map_inv]⟩
    · rintro ⟨_, ⟨d, hd, x, hx, rfl⟩, rfl⟩
      exact ⟨ι d, hD ▸ mem_map_of_mem ι hd, ι x, hx, by simp [map_mul, map_inv]⟩
  rw [hS, ← MonoidHom.map_closure] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  exact ⟨z', hz', by rwa [orderOf_injective ι hι] at hzo⟩

variable [Finite P]

theorem CoordModel914.coordFacts {G L₀ T₀ Es : Subgroup P} (hM : CoordModel914 G L₀ T₀ Es)
    (hι : Function.Injective ι) (hr : ι.range = G) {L D : Subgroup B} (hL : L.map ι = L₀)
    (hD : D.map ι = T₀) : CoordFacts914 L D (Es.comap ι) := by
  have hpre : ∀ {y : P}, y ∈ G → ∃ x, ι x = y := fun hy => by rw [← hr] at hy; exact hy
  have hmc : ∀ {K : Subgroup P}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    map_comap_eq_self (hr ▸ hK)
  have hmemL : ∀ x, ι x ∈ L₀ ↔ x ∈ L := fun x => by rw [← hL]; exact mem_map_iff_mem hι
  have hmemD : ∀ x, ι x ∈ T₀ ↔ x ∈ D := fun x => by rw [← hD]; exact mem_map_iff_mem hι
  have hmapD : ∀ {E : Subgroup B}, E ≤ D → E.map ι ≤ T₀ := fun hE => hD ▸ map_mono hE
  have hcent : ∀ {x : B}, x ∈ centralizer ((Es.comap ι : Subgroup B) : Set B) → Es ≤ G →
      ι x ∈ centralizer (Es : Set P) := by
    intro x hx hEsG
    rw [mem_centralizer_iff] at hx ⊢
    intro s hs
    obtain ⟨s', rfl⟩ := hpre (hEsG hs)
    rw [← map_mul, ← map_mul, hx s' hs]
  have hmov : ∀ {E : Subgroup B} {H Xh : Subgroup P} {p : ℕ},
      MovWit914 L₀ T₀ (E.map ι) H Xh p → MovWit914 L D E (H.comap ι) (Xh.comap ι) p := by
    intro E H Xh p hw
    have hHG : H ≤ G := hw.le.trans hM.L_le
    have hXG : Xh ≤ G := hw.irr.sylowP.le.trans hHG
    refine ⟨fun x hx => (hmemL x).mp (hw.le hx), ?_, fun e he => ?_, ?_,
      TC914.isElemAbelian_comap hι hw.elem, ?_, ?_⟩
    · rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      have h1 : ι x ∈ H ⊓ centralizer (L₀ : Set P) := by
        refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        rw [← hL] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx.2) z hz]
      rw [hw.inf_centralizer, mem_bot, ← map_one ι] at h1
      exact hι h1
    · refine NFA6.mem_normalizer_of_map hι ?_
      rw [hmc hHG]
      exact hw.normalizes (mem_map_of_mem ι he)
    · refine (TC914.twoPTwoIrred_map_iff hι).mp ?_
      rw [map_inf_eq _ _ _ hι, hmc hHG, hD, hmc hXG]
      exact hw.irr
    · obtain ⟨y, ⟨⟨hyH, hyT⟩, hyN⟩, x, hx, hne⟩ := hw.nontriv
      obtain ⟨y', rfl⟩ := hpre (hHG hyH)
      obtain ⟨x', rfl⟩ := hpre (hXG hx)
      refine ⟨y', ⟨⟨hyH, (hmemD y').mp hyT⟩, NFA6.mem_normalizer_of_map hι ?_⟩, x', hx,
        fun h => hne ?_⟩
      · rw [hmc hXG]
        exact hyN
      · rw [← map_inv, ← map_mul, ← map_mul, h]
    · rcases hw.three with h | h
      · exact Or.inl h
      · exact Or.inr (three_of_map hι hr hD hXG h)
  have hfix : ∀ {E : Subgroup B} {K Xh : Subgroup P} {p : ℕ}, K ≤ G →
      FixWit914 T₀ (E.map ι) K Xh p → FixWit914 D E (K.comap ι) (Xh.comap ι) p := by
    intro E K Xh p hKG hw
    have hXG : Xh ≤ G := hw.irr.sylowP.le.trans hKG
    refine ⟨fun x hx => hw.le (mem_map_of_mem ι hx), fun hle => hw.not_le ?_, ?_, ?_⟩
    · rw [← hmc hKG, ← NFA6.pCoreOf_map hι]
      exact map_mono hle
    · refine (TC914.twoPTwoIrred_map_iff hι).mp ?_
      rw [map_inf_eq _ _ _ hι, hmc hKG, hD, hmc hXG]
      exact hw.irr
    · rcases hw.three with h | h
      · exact Or.inl h
      · exact Or.inr (three_of_map hι hr hD hXG h)
  refine ⟨?_, ?_, fun E hED hEe => ?_, fun E hED hEe hne => ?_, fun F hFD hFN hFe => ?_,
    fun hne => ?_⟩
  · rw [← card_map_of_injective hι, hL]
    exact hM.three_dvd
  · obtain ⟨d, ⟨hdT, hdL⟩, hd2⟩ := hM.sq
    obtain ⟨d', rfl⟩ := hpre (hM.T_le hdT)
    refine ⟨d', ⟨(hmemD d').mp hdT, (hmemL d').mp hdL⟩, fun h => hd2 ?_⟩
    rw [← map_pow, h, map_one]
  · obtain ⟨H, Xh, p, hw⟩ := hM.mov (E.map ι) (hmapD hED) (hEe.map ι)
    exact ⟨H.comap ι, Xh.comap ι, p, hmov hw⟩
  · have hne' : E.map ι ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective E hι).mp h)
    rcases hM.fix (E.map ι) (hmapD hED) (hEe.map ι) hne' with ⟨K, Xh, p, hKG, hw⟩ | h
    · exact Or.inl ⟨K.comap ι, Xh.comap ι, p, hfix hKG hw⟩
    · right
      rw [← h, comap_map_eq_self_of_injective hι]
  · have hFN' : T₀ ≤ normalizer ((F.map ι : Subgroup P) : Set P) := by
      rw [← hD]
      rintro _ ⟨d, hd, rfl⟩
      exact NFA6.mem_normalizer_map (hFN hd)
    rcases hM.normal (F.map ι) (hmapD hFD) hFN' (hFe.map ι) with h | h | ⟨hc, hp⟩
    · exact Or.inl ((map_eq_bot_iff_of_injective F hι).mp h)
    · right
      left
      rw [← h, comap_map_eq_self_of_injective hι]
    · refine Or.inr (Or.inr ⟨by rwa [card_map_of_injective hι] at hc, fun x hx hx1 => ?_⟩)
      refine pairProp_of_map hι hL (hp (ι x) (mem_map_of_mem ι hx) fun h => hx1 (hι ?_))
      rw [h, map_one]
  · have hEs : Es ≠ ⊥ := by
      rintro rfl
      refine hne (eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hι ?_))
      rw [map_one]
      exact (mem_bot).mp hx
    obtain ⟨hEsT, hTN, hEse, hstar, K, hKG, ⟨Y, hY⟩, hEK, hCK, hKT⟩ := hM.star hEs
    have hEsG : Es ≤ G := hEsT.trans hM.T_le
    refine ⟨fun x hx => (hmemD x).mp (hEsT hx), fun d hd => ?_, TC914.isElemAbelian_comap hι hEse,
      fun E hE hEe => ?_, {K.comap ι}, fun K' hK' => ?_, ?_⟩
    · refine NFA6.mem_normalizer_of_map hι ?_
      rw [hmc hEsG]
      exact hTN ((hmemD d).mpr hd)
    · have hE' : E.map ι ≤ T₀ ⊓ centralizer (Es : Set P) := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨(hmemD x).mpr (hE hx).1, hcent (hE hx).2 hEsG⟩
      obtain ⟨H, Xh, hw, hEsH, hcomm⟩ := hstar (E.map ι) hE' (hEe.map ι)
      have hHG : H ≤ G := hw.le.trans hM.L_le
      refine ⟨H.comap ι, Xh.comap ι, hmov hw, fun e he => ?_, fun e he x hx => ?_⟩
      · refine NFA6.mem_normalizer_of_map hι ?_
        rw [hmc hHG]
        exact hEsH he
      · have h1 := hcomm (ι e) he (ι x) hx
        rw [← hmc hHG, ← NFA6.pCoreOf_map hι, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
          ← map_mul] at h1
        exact (mem_map_iff_mem hι).mp h1
    · rw [Finset.mem_singleton] at hK'
      subst hK'
      have hYG : Y ≤ G := hY.sylowP.le.trans hKG
      refine ⟨Y.comap ι, (TC914.twoPTwoIrred_map_iff hι).mp ?_, fun x hx => ?_, fun d hd => ?_⟩
      · rw [map_inf_eq _ _ _ hι, hmc hKG, hD, hmc hYG]
        exact hY
      · have h1 := hEK hx
        rw [← hmc hKG, ← NFA6.pCoreOf_map hι] at h1
        exact (mem_map_iff_mem hι).mp h1
      · exact hCK ⟨(hmemD d).mpr hd.1, hcent hd.2 hEsG⟩
    · rw [Finset.iSup_singleton]
      apply map_injective hι
      rw [Subgroup.map_sup, hmc hKG, hD, hKT, ← MonoidHom.range_eq_map, hr]

end Pullback

end CFSG.LocalAnalysis.WeakClosure81.Coord3
