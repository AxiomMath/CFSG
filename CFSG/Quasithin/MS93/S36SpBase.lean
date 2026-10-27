module

public import CFSG.Quasithin.MS93.S36Frat

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement

variable {G : Type} [Group G]

section TImage

variable {T : Subgroup G}

theorem mem_tImage {ψ : MulAut ↥T} {K : Subgroup G} {x : G} :
    x ∈ tImage ψ K ↔ ∃ t : ↥T, (t : G) ∈ K ∧ (ψ t : G) = x := by
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ψ t, ⟨t, ht, rfl⟩, rfl⟩

theorem apply_mem_tImage (ψ : MulAut ↥T) {K : Subgroup G} {t : ↥T} (ht : (t : G) ∈ K) :
    (ψ t : G) ∈ tImage ψ K :=
  mem_tImage.2 ⟨t, ht, rfl⟩

theorem tImage_mono (ψ : MulAut ↥T) {K K' : Subgroup G} (h : K ≤ K') : tImage ψ K ≤ tImage ψ K' :=
  Subgroup.map_mono (Subgroup.map_mono (fun _ hx => h hx))

theorem apply_mem_tImage_iff (ψ : MulAut ↥T) {K : Subgroup G} (t : ↥T) :
    (ψ t : G) ∈ tImage ψ K ↔ (t : G) ∈ K := by
  refine ⟨fun h => ?_, apply_mem_tImage ψ⟩
  obtain ⟨s, hs, hst⟩ := mem_tImage.1 h
  have : s = t := ψ.injective (Subtype.ext hst)
  rwa [this] at hs

theorem tImage_inf (ψ : MulAut ↥T) (K K' : Subgroup G) :
    tImage ψ (K ⊓ K') = tImage ψ K ⊓ tImage ψ K' := by
  ext x
  simp only [Subgroup.mem_inf, mem_tImage]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨t, h1, rfl⟩, ⟨t, h2, rfl⟩⟩
  · rintro ⟨⟨t, h1, rfl⟩, ⟨s, h2, hs⟩⟩
    have : s = t := ψ.injective (Subtype.ext hs)
    subst this
    exact ⟨s, ⟨h1, h2⟩, rfl⟩

theorem tImage_eq_map (ψ : MulAut ↥T) (K : Subgroup G) :
    tImage ψ K = ((K.subgroupOf T).map ψ.toMonoidHom).map T.subtype := rfl

theorem tImage_sup (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    tImage ψ (K ⊔ K') = tImage ψ K ⊔ tImage ψ K' := by
  rw [tImage_eq_map, tImage_eq_map, tImage_eq_map, ← Subgroup.map_sup, ← Subgroup.map_sup]
  congr 2
  exact Subgroup.subgroupOf_sup hK hK'

theorem tImage_commutator (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    tImage ψ ⁅K, K'⁆ = ⁅tImage ψ K, tImage ψ K'⁆ := by
  rw [tImage_eq_map, tImage_eq_map, tImage_eq_map, ← Subgroup.map_commutator,
    ← Subgroup.map_commutator]
  congr 2
  exact commutator_subgroupOf hK hK'

theorem tImage_tImage (φ ψ : MulAut ↥T) (K : Subgroup G) :
    tImage φ (tImage ψ K) = tImage (φ * ψ) K := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := mem_tImage.1 hx
    obtain ⟨t, ht, hts⟩ := mem_tImage.1 hs
    have : ψ t = s := Subtype.ext hts
    subst this
    exact mem_tImage.2 ⟨t, ht, rfl⟩
  · intro hx
    obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hx
    exact mem_tImage.2 ⟨ψ t, apply_mem_tImage ψ ht, rfl⟩

theorem tImage_one (K : Subgroup G) : tImage (1 : MulAut ↥T) K = K ⊓ T := by
  ext x
  simp only [mem_tImage, Subgroup.mem_inf, MulAut.one_apply]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, t.2⟩
  · rintro ⟨hx, hxT⟩
    exact ⟨⟨x, hxT⟩, hx, rfl⟩

theorem tImage_of_le_one {K : Subgroup G} (hK : K ≤ T) : tImage (1 : MulAut ↥T) K = K := by
  rw [tImage_one, inf_eq_left.2 hK]

theorem tImage_inv_tImage (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage ψ⁻¹ (tImage ψ K) = K := by
  rw [tImage_tImage, inv_mul_cancel, tImage_of_le_one hK]

theorem tImage_tImage_inv (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage ψ (tImage ψ⁻¹ K) = K := by
  rw [tImage_tImage, mul_inv_cancel, tImage_of_le_one hK]

theorem tImage_le_tImage_iff (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) :
    tImage ψ K ≤ tImage ψ K' ↔ K ≤ K' := by
  refine ⟨fun h x hx => ?_, tImage_mono ψ⟩
  have := h (apply_mem_tImage ψ (t := ⟨x, hK hx⟩) hx)
  exact (apply_mem_tImage_iff ψ ⟨x, hK hx⟩).1 this

theorem tImage_le_iff (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    tImage ψ K ≤ K' ↔ K ≤ tImage ψ⁻¹ K' := by
  conv_lhs => rw [← tImage_tImage_inv ψ hK']
  exact tImage_le_tImage_iff ψ hK

theorem tImage_self (ψ : MulAut ↥T) : tImage ψ (T : Subgroup G) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, -, rfl⟩ := mem_tImage.1 hx
    exact (ψ t).2
  · intro hx
    refine mem_tImage.2 ⟨ψ⁻¹ ⟨x, hx⟩, (ψ⁻¹ ⟨x, hx⟩).2, ?_⟩
    simp

theorem card_tImage (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    Nat.card (tImage ψ K) = Nat.card K := by
  rw [tImage_eq_map, Subgroup.card_map_of_injective T.subtype_injective,
    Subgroup.card_map_of_injective ψ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem relIndex_tImage (ψ : MulAut ↥T) {K K' : Subgroup G} (hK' : K' ≤ T) :
    (tImage ψ K).relIndex (tImage ψ K') = K.relIndex K' := by
  rw [tImage_eq_map, tImage_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ T.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ ψ.injective, Subgroup.relIndex_subgroupOf hK']

theorem tImage_centralizer (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    T ⊓ Subgroup.centralizer (tImage ψ K : Set G) =
      tImage ψ (T ⊓ Subgroup.centralizer (K : Set G)) := by
  ext x
  constructor
  · rintro ⟨hxT, hxC⟩
    refine mem_tImage.2 ⟨ψ⁻¹ ⟨x, hxT⟩, ⟨(ψ⁻¹ ⟨x, hxT⟩).2, ?_⟩, by simp⟩
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    have hkt : (ψ ⟨k, hK hk⟩ : G) ∈ tImage ψ K := apply_mem_tImage ψ hk
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ hkt
    have hc' : ψ ⟨k, hK hk⟩ * ⟨x, hxT⟩ = ⟨x, hxT⟩ * ψ ⟨k, hK hk⟩ := Subtype.ext hc
    have := congrArg (fun z => (ψ⁻¹ : MulAut ↥T) z) hc'
    simp only [map_mul, MulAut.inv_apply_self] at this
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨t, ⟨-, htC⟩, rfl⟩ := mem_tImage.1 hx
    refine ⟨(ψ t).2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨s, hs, rfl⟩ := mem_tImage.1 hy
    have hc := Subgroup.mem_centralizer_iff.1 htC _ hs
    have hc' : s * t = t * s := Subtype.ext hc
    have := congrArg ψ hc'
    rw [map_mul, map_mul] at this
    exact congrArg Subtype.val this

theorem tImage_eq_bot_iff (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage ψ K = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    have := h ▸ apply_mem_tImage ψ (t := ⟨x, hK hx⟩) hx
    rw [Subgroup.mem_bot] at this ⊢
    have h1 : ψ ⟨x, hK hx⟩ = 1 := Subtype.ext this
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  · rintro rfl
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hx
    rw [Subgroup.mem_bot] at ht ⊢
    have : t = 1 := Subtype.ext ht
    rw [this, map_one]
    rfl

theorem le_normalizer_tImage (ψ : MulAut ↥T) {K : Subgroup G}
    (hKn : T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer (tImage ψ K : Set G) := by
  have key : ∀ x ∈ T, ∀ y ∈ tImage ψ K, x * y * x⁻¹ ∈ tImage ψ K := by
    intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hy
    set s : ↥T := ψ⁻¹ ⟨x, hx⟩
    have hst : (s : G) * t * (s : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKn s.2) t).1 ht
    have hst' : ((s * t * s⁻¹ : ↥T) : G) ∈ K := by simpa using hst
    have := apply_mem_tImage ψ hst'
    rw [map_mul, map_mul, map_inv] at this
    simpa [s] using this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (T.inv_mem hx) _ hy
  simpa [mul_assoc] using this

end TImage

section Criteria

variable [Finite G] {M T L : Subgroup G}

theorem comm_le_of_comm_le (h : PUHyp M T L) {Y : Subgroup G} (hYT : Y ≤ T)
    (hYQ : ¬ Y ≤ pCoreOf 2 M) {N N₁ : Subgroup G} (hNn : M ≤ Subgroup.normalizer (N : Set G))
    (hN₁n : M ≤ Subgroup.normalizer (N₁ : Set G)) (hNY : ⁅N, Y⁆ ≤ N₁) : ⁅N, L⁆ ≤ N₁ := by
  have hc1 : ∀ g ∈ M, ∀ x ∈ N₁, g * x * g⁻¹ ∈ N₁ :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.1 (hN₁n hg) x).1 hx
  have hc : ∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.1 (hNn hg) x).1 hx
  let K : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∀ n ∈ N, ⁅n, m⁆ ∈ N₁}
      one_mem' := ⟨M.one_mem, fun n _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, fun n hn => ?_⟩
        have e : ⁅n, x * y⁆ = ⁅n, x⁆ * (x * ⁅n, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N₁.mul_mem (hx n hn) (hc1 _ hxM _ (hy n hn))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨M.inv_mem hxM, fun n hn => ?_⟩
        have e : ⁅n, x⁻¹⁆ = x⁻¹ * ⁅n, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hc1 _ (M.inv_mem hxM) _ (N₁.inv_mem (hx _ hn)) }
  have hKM : K ≤ M := fun x hx => hx.1
  have hKn : (K.subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxM, hx⟩ := hx
    refine ⟨M.mul_mem (M.mul_mem m.2 hxM) (M.inv_mem m.2), fun n hn => ?_⟩
    have hn' : (m : G)⁻¹ * n * m ∈ N := by simpa using hc _ (M.inv_mem m.2) n hn
    have e : ⁅n, (m : G) * (x : G) * (m : G)⁻¹⁆ =
        (m : G) * ⁅(m : G)⁻¹ * n * m, (x : G)⁆ * (m : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact hc1 _ m.2 _ (hx _ hn')
  have hYK : Y ⊓ M ≤ K := by
    rintro y ⟨hy, hyM⟩
    exact ⟨hyM, fun n hn => hNY (Subgroup.commutator_mem_commutator hn hy)⟩
  have hLK : L ≤ K :=
    (S36.le_normalClosureIn_of_not_le h hYT hYQ).trans
      (normalClosureIn_le_of hKM hKn hYK)
  rw [Subgroup.commutator_le]
  intro n hn l hl
  exact (hLK hl).2 n hn

theorem vq_eq_uq_of_le (h : PUHyp M T L) {Y : Subgroup G} (hYT : Y ≤ T)
    (hYQ : ¬ Y ≤ pCoreOf 2 M) {N₀ : Subgroup G} (hN₀M : N₀ ≤ M)
    (hN₀n : T ≤ Subgroup.normalizer (N₀ : Set G)) (hQY : ⁅pCoreOf 2 M, Y⁆ ≤ N₀)
    (hN₀L : ⁅N₀, L⁆ ≤ Z0q M T) : Vq M L = Uq M T L := by
  set Z := Z0q M T with hZ
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_Z0q M T
  have hZM : Z ≤ M := Z0q_le M T
  have hLn := h.le_normalizer
  set N := N₀ ⊔ Z with hN
  have hNM : N ≤ M := sup_le hN₀M hZM
  have hNn : M ≤ Subgroup.normalizer (N : Set G) := by
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_sup hN₀n (h.le.trans hZn)
    have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
      have key : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N := by
        intro l hl x hx
        have hle : N ≤ N.comap (MulAut.conj l).toMonoidHom := by
          refine sup_le (fun n hn => ?_) (fun z hz => ?_)
          · show l * n * l⁻¹ ∈ N
            have hc : ⁅l, n⁆ ∈ Z := by
              have := hN₀L (Subgroup.commutator_mem_commutator hn hl)
              have e : ⁅l, n⁆ = ⁅n, l⁆⁻¹ := (commutatorElement_inv n l).symm
              rw [e]
              exact Z.inv_mem this
            have e : l * n * l⁻¹ = ⁅l, n⁆ * n := by
              simp only [commutatorElement_def]
              group
            rw [e, hN, sup_comm]
            exact Subgroup.mul_mem_sup hc hn
          · show l * z * l⁻¹ ∈ N
            exact Subgroup.mem_sup_right
              ((Subgroup.mem_normalizer_iff.1 (hZn (h.L_le hl)) z).1 hz)
        exact hle hx
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key l hl x, fun hx => ?_⟩
      have := key l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using this
    rw [h.eq_sup]
    exact sup_le hLN hTN
  have hN₀Z : N₀ ≤ Subgroup.normalizer (Z : Set G) := hN₀M.trans hZn
  have hNL : ⁅N, L⁆ ≤ Z := by
    rw [hN, Subgroup.commutator_le]
    intro x hx l hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₀Z,
      Set.mem_mul] at hx
    obtain ⟨n, hn, z, hz, rfl⟩ := hx
    have e : ⁅n * z, l⁆ = n * ⁅z, l⁆ * n⁻¹ * ⁅n, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Z.mul_mem ?_ (hN₀L (Subgroup.commutator_mem_commutator hn hl))
    have hzl : ⁅z, l⁆ ∈ Z := by
      have e' : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e']
      exact Z.mul_mem hz ((Subgroup.mem_normalizer_iff.1 (hZn (h.L_le hl)) _).1 (Z.inv_mem hz))
    have hnM : n ∈ M := hN₀M hn
    exact (Subgroup.mem_normalizer_iff.1 (hZn hnM) _).1 hzl
  have hQN : ⁅pCoreOf 2 M, L⁆ ≤ N :=
    comm_le_of_comm_le h hYT hYQ (le_normalizer_pCoreOf M) hNn (hQY.trans le_sup_left)
  have hV : Vq M L = ⁅⁅pCoreOf 2 M, L⁆, L⁆ :=
    commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M) hLn
      h.perfect
  have hVZ : Vq M L ≤ Z := by
    rw [hV]
    exact (Subgroup.commutator_mono hQN le_rfl).trans hNL
  apply le_antisymm
  · have hV' : Vq M L = ⁅Vq M L, L⁆ := hV
    rw [hV']
    exact Subgroup.commutator_mono hVZ le_rfl
  · exact Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl

end Criteria

end CFSG.Quasithin.MS93.S36SP
