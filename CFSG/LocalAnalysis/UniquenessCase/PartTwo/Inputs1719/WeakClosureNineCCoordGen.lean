module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordEmbed

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Coord

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81.NFA6

variable {Y : Type} [Group Y]

structure MovModel (L₀ T₀ E H Xh : Subgroup Y) (p : ℕ) : Prop where
  le : H ≤ L₀
  normalizes : E ≤ normalizer (H : Set Y)
  two : TwoPTwo H (H ⊓ T₀) Xh p
  card : Nat.card Xh = p
  nontriv : ∃ y ∈ H ⊓ T₀ ⊓ normalizer (Xh : Set Y), ∃ x ∈ Xh, y * x * y⁻¹ ≠ x
  three : p = 3 ∨ ∃ y ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3

structure FixModel (G T₀ E K Xh : Subgroup Y) (p : ℕ) : Prop where
  le_G : K ≤ G
  le : E ≤ K
  not_le : ¬ E ≤ pCoreOf 2 K
  two : TwoPTwo K (K ⊓ T₀) Xh p
  card : Nat.card Xh = p
  three : p = 3 ∨ ∃ y ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3

structure CoordModel (G L₀ T₀ Es₀ : Subgroup Y) : Prop where
  base : ModelBase G L₀ T₀
  sq : ∃ d ∈ T₀ ⊓ L₀, d ^ 2 ≠ 1
  mov : ∀ E : Subgroup Y, E ≤ T₀ → IsElemAbelian 2 E →
    ∃ (H Xh : Subgroup Y) (p : ℕ), MovModel L₀ T₀ E H Xh p
  fix : ∀ E : Subgroup Y, E ≤ T₀ → IsElemAbelian 2 E → E ≠ ⊥ →
    (∃ (K Xh : Subgroup Y) (p : ℕ), FixModel G T₀ E K Xh p) ∨ E = Es₀
  normal : ∀ F : Subgroup Y, F ≤ T₀ → T₀ ≤ normalizer (F : Set Y) → IsElemAbelian 2 F →
    F = ⊥ ∨ F = Es₀ ∨ (Nat.card F = 2 ∧ ∀ x ∈ F, x ≠ 1 → PairProp914 L₀ x)
  star : Es₀ ≠ ⊥ → Es₀ ≤ T₀ ∧ T₀ ≤ normalizer (Es₀ : Set Y) ∧ IsElemAbelian 2 Es₀ ∧
    4 ≤ Nat.card Es₀ ∧
    (∀ E : Subgroup Y, E ≤ T₀ ⊓ centralizer (Es₀ : Set Y) → IsElemAbelian 2 E →
      ∃ H Xh : Subgroup Y, MovModel L₀ T₀ E H Xh 3 ∧ Es₀ ≤ normalizer (H : Set Y) ∧
        ∀ e ∈ Es₀, ∀ x ∈ Xh, e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H) ∧
    ∃ K Z : Subgroup Y, K ≤ G ∧ TwoPTwo K (K ⊓ T₀) Z 3 ∧ Nat.card Z = 3 ∧
      Es₀ ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (Es₀ : Set Y) ≤ K ∧ K ⊔ T₀ = G

variable {X : Type} [Group X] {ι : X →* Y}

private theorem isElemAbelian_of_prime_card {G : Type*} [Group G] {E : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card E = p) : IsElemAbelian p E := by
  have hcyc : IsCyclic E := @isCyclic_of_prime_card E _ p ⟨hp⟩ hcard
  refine ⟨⟨⟨fun a b => @CommGroup.mul_comm E (@IsCyclic.commGroup E _ hcyc) a b⟩⟩,
    fun x hx => ?_⟩
  have h := pow_card_eq_one' (G := E) (x := (⟨x, hx⟩ : E))
  rw [hcard] at h
  simpa using congrArg Subtype.val h

private theorem centralizer_comap_eq_bot {G L₀ : Subgroup Y} {L : Subgroup X}
    (hι : Function.Injective ι) (hrange : ι.range = G) (hL : L.map ι = L₀)
    (hcent : ∀ g ∈ G, (∀ x ∈ L₀, g * x = x * g) → g = 1) :
    centralizer (L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  apply hι
  rw [map_one]
  refine hcent (ι z) ?_ fun y hy => ?_
  · rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
  · rw [← hL] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hz l hl]

private theorem twoPTwoIrred_comap {G T₀ : Subgroup Y} {D : Subgroup X}
    {K Z : Subgroup Y} {p : ℕ} (hι : Function.Injective ι) (hrange : ι.range = G)
    (hD : D.map ι = T₀) (hKG : K ≤ G) (h : TwoPTwo K (K ⊓ T₀) Z p)
    (hZ : Nat.card Z = p) :
    TwoPTwoIrred (K.comap ι) (K.comap ι ⊓ D) (Z.comap ι) p := by
  have hZG : Z ≤ G := h.sylowP.le.trans hKG
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  refine ⟨twoPTwo_of_map hι ?_, irred_of_prime_card ?_⟩
  · rw [hmc hKG, Subgroup.map_inf_eq _ _ _ hι, hmc hKG, hD, hmc hZG]
    exact h
  · rw [← Subgroup.card_map_of_injective (K := Z.comap ι) hι, hmc hZG, hZ]
    exact h.prime

private theorem order_three_comap {D : Subgroup X} {T₀ : Subgroup Y} {Xh : Subgroup X}
    {X' : Subgroup Y} {p : ℕ} (hι : Function.Injective ι) (hD : D.map ι = T₀)
    (hX : Xh.map ι = X')
    (h : p = 3 ∨ ∃ y' ∈ closure {z | ∃ d ∈ T₀, ∃ x ∈ X', z = d * x * d⁻¹},
      orderOf y' = 3) :
    p = 3 ∨ ∃ y ∈ closure {z | ∃ d ∈ D, ∃ x ∈ Xh, z = d * x * d⁻¹}, orderOf y = 3 := by
  rcases h with h3 | ⟨y', hy', hy3⟩
  · exact Or.inl h3
  · right
    have hset : ι '' {z | ∃ d ∈ D, ∃ x ∈ Xh, z = d * x * d⁻¹} =
        {z | ∃ d ∈ T₀, ∃ x ∈ X', z = d * x * d⁻¹} := by
      ext z
      constructor
      · rintro ⟨w, ⟨d, hd, x, hx, rfl⟩, rfl⟩
        exact ⟨ι d, hD ▸ Subgroup.mem_map_of_mem ι hd, ι x,
          hX ▸ Subgroup.mem_map_of_mem ι hx, by simp⟩
      · rintro ⟨d, hd, x, hx, rfl⟩
        rw [← hD] at hd
        obtain ⟨d₁, hd₁, rfl⟩ := hd
        rw [← hX] at hx
        obtain ⟨x₁, hx₁, rfl⟩ := hx
        exact ⟨d₁ * x₁ * d₁⁻¹, ⟨d₁, hd₁, x₁, hx₁, rfl⟩, by simp⟩
    have hy'' : y' ∈ Subgroup.map ι
        (Subgroup.closure {z | ∃ d ∈ D, ∃ x ∈ Xh, z = d * x * d⁻¹}) := by
      rw [MonoidHom.map_closure, hset]
      exact hy'
    obtain ⟨y, hy, hyy⟩ := hy''
    refine ⟨y, hy, ?_⟩
    have hord := orderOf_injective ι hι y
    rw [hyy] at hord
    rw [← hord]
    exact hy3

private theorem movWit914_comap {G L₀ T₀ : Subgroup Y} {L D : Subgroup X}
    {E : Subgroup X} {H' X' : Subgroup Y} {p : ℕ} (hι : Function.Injective ι)
    (hrange : ι.range = G) (hL : L.map ι = L₀) (hD : D.map ι = T₀)
    (hL₀G : L₀ ≤ G) (hc : centralizer (L : Set X) = ⊥)
    (hm : MovModel L₀ T₀ (E.map ι) H' X' p) :
    MovWit914 L D E (H'.comap ι) (X'.comap ι) p := by
  have hK'G : H' ≤ G := hm.le.trans hL₀G
  have hX'G : X' ≤ G := hm.two.sylowP.le.trans hK'G
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  have hcard : Nat.card (X'.comap ι) = p := by
    rw [← Subgroup.card_map_of_injective (K := X'.comap ι) hι, hmc hX'G, hm.card]
  have helem : IsElemAbelian p (X'.comap ι) :=
    isElemAbelian_of_prime_card hm.two.prime hcard
  refine ⟨?_, ?_, ?_, ?_, helem, ?_, ?_⟩
  · rw [← Subgroup.map_le_map_iff_of_injective hι, hmc hK'G, hL]
    exact hm.le
  · rw [hc, inf_bot_eq]
  · intro e he
    refine mem_normalizer_of_map hι ?_
    rw [hmc hK'G]
    exact hm.normalizes (Subgroup.mem_map_of_mem ι he)
  · exact twoPTwoIrred_comap hι hrange hD hK'G hm.two hm.card
  · obtain ⟨y', ⟨⟨hy'H, hy'T⟩, hy'n⟩, x', hx'X, hne⟩ := hm.nontriv
    rw [← hmc hK'G] at hy'H
    obtain ⟨y, hyH, rfl⟩ := hy'H
    have hyD : y ∈ D := by
      rw [← hD] at hy'T
      exact (Subgroup.mem_map_iff_mem hι).mp hy'T
    have hyn : y ∈ normalizer (X'.comap ι) := by
      refine mem_normalizer_of_map hι ?_
      rw [hmc hX'G]
      exact hy'n
    rw [← hmc hX'G] at hx'X
    obtain ⟨x, hxX, rfl⟩ := hx'X
    refine ⟨y, ⟨⟨hyH, hyD⟩, hyn⟩, x, hxX, ?_⟩
    intro heq
    exact hne (by simpa [map_mul, map_inv] using congrArg ι heq)
  · exact order_three_comap hι hD (hmc hX'G) hm.three

private theorem fixWit914_comap {G T₀ : Subgroup Y} {D : Subgroup X} {E : Subgroup X}
    {K' X' : Subgroup Y} {p : ℕ} (hι : Function.Injective ι) (hrange : ι.range = G)
    (hD : D.map ι = T₀) (hm : FixModel G T₀ (E.map ι) K' X' p) :
    FixWit914 D E (K'.comap ι) (X'.comap ι) p := by
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  have hX'G : X' ≤ G := hm.two.sylowP.le.trans hm.le_G
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_le_iff_le_comap.mp hm.le
  · intro hle
    apply hm.not_le
    have h := Subgroup.map_mono (f := ι) hle
    rwa [pCoreOf_map hι, hmc hm.le_G] at h
  · exact twoPTwoIrred_comap hι hrange hD hm.le_G hm.two hm.card
  · exact order_three_comap hι hD (hmc hX'G) hm.three

private theorem pairProp914_comap {L₀ : Subgroup Y} {L : Subgroup X} (hι : Function.Injective ι)
    (hL : L.map ι = L₀) {x : X} (h : PairProp914 L₀ (ι x)) : PairProp914 L x := by
  obtain ⟨l', hl'L, h2, hne⟩ := h
  rw [← hL] at hl'L
  obtain ⟨l, hl, rfl⟩ := hl'L
  refine ⟨l, hl, IsPGroup.to_le (h2.comap_of_injective ι hι) ((Subgroup.closure_le _).mpr ?_), ?_⟩
  · intro z hz
    rcases hz with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · intro heq
    exact hne (by simpa [map_mul, map_inv] using congrArg ι heq)

private theorem movStar914_comap {G L₀ T₀ Es₀ : Subgroup Y} {L D Es : Subgroup X}
    {E : Subgroup X} {H' Xh' : Subgroup Y} (hι : Function.Injective ι)
    (hrange : ι.range = G) (hL : L.map ι = L₀) (hD : D.map ι = T₀) (hL₀G : L₀ ≤ G)
    (hc : centralizer (L : Set X) = ⊥) (hEsmap : Es.map ι = Es₀)
    (hm : MovModel L₀ T₀ (E.map ι) H' Xh' 3) (hnorm : Es₀ ≤ normalizer (H' : Set Y))
    (hcomm : ∀ e ∈ Es₀, ∀ x ∈ Xh', e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H') :
    MovStar914 L D Es E := by
  have hK'G : H' ≤ G := hm.le.trans hL₀G
  have hX'G : Xh' ≤ G := hm.two.sylowP.le.trans hK'G
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  refine ⟨H'.comap ι, Xh'.comap ι, movWit914_comap hι hrange hL hD hL₀G hc hm, ?_, ?_⟩
  · intro e he
    refine mem_normalizer_of_map hι ?_
    rw [hmc hK'G]
    exact hnorm (hEsmap ▸ Subgroup.mem_map_of_mem ι he)
  · intro e he x hx
    have h1 : ι (e * x * e⁻¹ * x⁻¹) ∈ pCoreOf 2 H' := by
      have := hcomm (ι e) (hEsmap ▸ Subgroup.mem_map_of_mem ι he) (ι x)
        (hmc hX'G ▸ Subgroup.mem_map_of_mem ι hx)
      simpa using this
    have h2 : ι (e * x * e⁻¹ * x⁻¹) ∈ (pCoreOf 2 (H'.comap ι)).map ι := by
      rw [pCoreOf_map hι, hmc hK'G]
      exact h1
    exact (Subgroup.mem_map_iff_mem hι).mp h2

private theorem closeFamily914_comap {G T₀ Es₀ : Subgroup Y} {D Es : Subgroup X}
    (hι : Function.Injective ι) (hrange : ι.range = G) (hD : D.map ι = T₀)
    (hEsmap : Es.map ι = Es₀) {K' Z' : Subgroup Y} (hK'G : K' ≤ G)
    (h2 : TwoPTwo K' (K' ⊓ T₀) Z' 3) (hZ : Nat.card Z' = 3)
    (hEp : Es₀ ≤ pCoreOf 2 K') (hcen : T₀ ⊓ centralizer (Es₀ : Set Y) ≤ K')
    (hsup : K' ⊔ T₀ = G) :
    ∃ Ks : Finset (Subgroup X), CloseFamily914 D Es Ks := by
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  have htop : (⊤ : Subgroup X).map ι = G := by
    rw [← MonoidHom.range_eq_map, hrange]
  refine ⟨{K'.comap ι}, fun K hK => ?_, ?_⟩
  · rw [Finset.mem_singleton] at hK
    subst hK
    refine ⟨Z'.comap ι, twoPTwoIrred_comap hι hrange hD hK'G h2 hZ, ?_, ?_⟩
    · rw [← Subgroup.map_le_map_iff_of_injective hι, pCoreOf_map hι, hmc hK'G, hEsmap]
      exact hEp
    · intro x hx
      refine hcen ⟨?_, ?_⟩
      · rw [← hD]
        exact Subgroup.mem_map_of_mem ι hx.1
      · refine Subgroup.mem_centralizer_iff.mpr fun a' ha' => ?_
        rw [← hEsmap] at ha'
        obtain ⟨a, ha, rfl⟩ := ha'
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx.2 a ha]
  · rw [Finset.iSup_singleton]
    apply Subgroup.map_injective hι
    rw [Subgroup.map_sup, hmc hK'G, hD, hsup, htop]

private theorem star914_comap {G L₀ T₀ Es₀ : Subgroup Y} {L D : Subgroup X}
    (hM : CoordModel G L₀ T₀ Es₀) (hι : Function.Injective ι) (hrange : ι.range = G)
    (hL : L.map ι = L₀) (hD : D.map ι = T₀) (hc : centralizer (L : Set X) = ⊥) :
    (Es₀.comap ι) ≠ ⊥ →
      Es₀.comap ι ≤ D ∧ D ≤ normalizer (Es₀.comap ι : Set X) ∧
        IsElemAbelian 2 (Es₀.comap ι) ∧
        (∀ E : Subgroup X, E ≤ D ⊓ centralizer (Es₀.comap ι : Set X) →
          IsElemAbelian 2 E → MovStar914 L D (Es₀.comap ι) E) ∧
        ∃ Ks : Finset (Subgroup X), CloseFamily914 D (Es₀.comap ι) Ks := by
  intro hEsne
  have hmc : ∀ {K : Subgroup Y}, K ≤ G → (K.comap ι).map ι = K := fun hK =>
    Subgroup.map_comap_eq_self (hrange ▸ hK)
  have hmemT : ∀ x, ι x ∈ T₀ ↔ x ∈ D := fun x => by
    rw [← hD]
    exact Subgroup.mem_map_iff_mem hι
  have hEs₀ne : Es₀ ≠ ⊥ := by
    rintro rfl
    exact hEsne (by rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff ι).mpr hι])
  obtain ⟨hEs₀T, hEs₀norm, hEs₀e, -, hmovstar, K', Z', hK'G, h2, hZ, hEp, hcen, hsup⟩ :=
    hM.star hEs₀ne
  have hEsmap : (Es₀.comap ι).map ι = Es₀ := hmc (hEs₀T.trans hM.base.T₀_le)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmemT x).mp (hEs₀T hx)
  · intro d hd
    refine mem_normalizer_of_map hι ?_
    rw [hEsmap]
    exact hEs₀norm (hD ▸ Subgroup.mem_map_of_mem ι hd)
  · exact hEs₀e.comap hι
  · intro E hE hEe
    have hE'T : E.map ι ≤ T₀ := hD ▸ Subgroup.map_mono fun x hx => (hE hx).1
    have hE'c : E.map ι ≤ centralizer (Es₀ : Set Y) := by
      intro e' he'
      obtain ⟨e, he, rfl⟩ := he'
      refine Subgroup.mem_centralizer_iff.mpr fun a' ha' => ?_
      rw [← hEsmap] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hE he).2 a ha]
    obtain ⟨H', X', hm, hnorm, hcomm⟩ :=
      hmovstar (E.map ι) (fun x hx => ⟨hE'T hx, hE'c hx⟩) (hEe.map ι)
    exact movStar914_comap hι hrange hL hD hM.base.L₀_le hc hEsmap hm hnorm hcomm
  · exact closeFamily914_comap hι hrange hD hEsmap hK'G h2 hZ hEp hcen hsup

theorem coordFacts_of_model {G L₀ T₀ Es₀ : Subgroup Y} (hM : CoordModel G L₀ T₀ Es₀) [Finite X]
    (ι : X →* Y) (hι : Function.Injective ι) (hrange : ι.range = G) {L D : Subgroup X}
    (hL : L.map ι = L₀) (hD : D.map ι = T₀) : CoordFacts914 L D (Es₀.comap ι) := by
  have hmemL : ∀ x, ι x ∈ L₀ ↔ x ∈ L := fun x => by
    rw [← hL]
    exact Subgroup.mem_map_iff_mem hι
  have hTpre : ∀ {y : Y}, y ∈ T₀ → ∃ x ∈ D, ι x = y := fun hy => by
    rw [← hD] at hy
    exact hy
  have hc : centralizer (L : Set X) = ⊥ :=
    centralizer_comap_eq_bot hι hrange hL hM.base.cent
  refine { three_dvd := ?_, sq := ?_, mov := ?_, fix := ?_, normal := ?_, star := ?_ }
  · rw [← Subgroup.card_map_of_injective hι, hL]
    exact hM.base.three_dvd
  · obtain ⟨d₀, ⟨hd₀T, hd₀L⟩, hd₀2⟩ := hM.sq
    rw [← hD] at hd₀T
    obtain ⟨d, hdD, rfl⟩ := hd₀T
    refine ⟨d, ⟨hdD, (hmemL d).mp hd₀L⟩, fun h => hd₀2 ?_⟩
    rw [← map_pow, h, map_one]
  · intro E hED hEe
    obtain ⟨H', X', p, hm⟩ := hM.mov (E.map ι) (hD ▸ Subgroup.map_mono hED) (hEe.map ι)
    exact ⟨H'.comap ι, X'.comap ι, p,
      movWit914_comap hι hrange hL hD hM.base.L₀_le hc hm⟩
  · intro E hED hEe hE1
    have hE'T : E.map ι ≤ T₀ := hD ▸ Subgroup.map_mono hED
    have hE'1 : E.map ι ≠ ⊥ := fun h =>
      hE1 ((Subgroup.map_eq_bot_iff_of_injective E hι).mp h)
    rcases hM.fix (E.map ι) hE'T (hEe.map ι) hE'1 with ⟨K', X', p, hm⟩ | hEs
    · exact Or.inl ⟨K'.comap ι, X'.comap ι, p, fixWit914_comap hι hrange hD hm⟩
    · exact Or.inr (by rw [← hEs, Subgroup.comap_map_eq_self_of_injective hι E])
  · intro F hFD hFn hFe
    have hF'T : F.map ι ≤ T₀ := hD ▸ Subgroup.map_mono hFD
    have hF'norm : T₀ ≤ normalizer ((F.map ι : Subgroup Y) : Set Y) := by
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := hTpre ht'
      exact mem_normalizer_map (hFn ht)
    rcases hM.normal (F.map ι) hF'T hF'norm (hFe.map ι) with hbot | hEs | ⟨hcard, hpair⟩
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective F hι).mp hbot)
    · exact Or.inr (Or.inl (by rw [← hEs, Subgroup.comap_map_eq_self_of_injective hι F]))
    · refine Or.inr (Or.inr ⟨?_, fun x hx hx1 => ?_⟩)
      · rw [← Subgroup.card_map_of_injective hι, hcard]
      · exact pairProp914_comap hι hL (hpair (ι x) (Subgroup.mem_map_of_mem ι hx)
          fun h => hx1 (hι (by simpa using h)))
  · exact star914_comap hM hι hrange hL hD hc

theorem coordFacts_of_equiv [Finite Y] {G L₀ T₀ Es₀ : Subgroup Y} (hM : CoordModel G L₀ T₀ Es₀)
    [Finite X] (e : X ≃* G) {L D : Subgroup X} (hLn : L.Normal) (hL1 : L ≠ ⊥) (hLp : ⁅L, L⁆ = L)
    (hD : IsSylowIn 2 D ⊤) : ∃ Es : Subgroup X, CoordFacts914 L D Es := by
  obtain ⟨ι, hι, hr, hL, hD'⟩ := exists_embedding hM.base e hLn hL1 hLp hD
  exact ⟨_, coordFacts_of_model hM ι hι hr hL hD'⟩

end CFSG.LocalAnalysis.WeakClosure81.Coord
