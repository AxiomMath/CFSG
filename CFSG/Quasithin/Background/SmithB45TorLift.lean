module

public import CFSG.Quasithin.Background.SmithB45TorOrbit
public import CFSG.Quasithin.Background.SmithB45Disp

public section

namespace CFSG.Quasithin.B45Tor

open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp

section Map

variable {G G' : Type*} [Group G] [Group G']

theorem orbit_data_map (ψ : G →* G') (hψ : Function.Injective ψ) {p : ℕ} {R H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (R : Set G)) {k : ℕ}
    (horb : ∀ K : Subgroup G, K ≤ R → Nat.card K = p →
      ∃ S : Finset (Subgroup G), k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g K) :
    (∀ g ∈ (H.map ψ : Set G'), ∀ r ∈ R.map ψ, g * r * g⁻¹ ∈ R.map ψ) ∧
      ∀ K : Subgroup G', K ≤ R.map ψ → Nat.card K = p →
        ∃ S : Finset (Subgroup G'), k ≤ S.card ∧
          ∀ K' ∈ S, ∃ g ∈ (H.map ψ : Set G'), K' = K.map (MulAut.conj g).toMonoidHom := by
  classical
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨r, hr, rfl⟩
    refine ⟨g * r * g⁻¹, conj_mem_of_mem_normalizer (hHN hg) hr, ?_⟩
    simp only [map_mul, map_inv]
  · intro K hK hKp
    set K₀ := K.comap ψ with hK₀
    have hKmap : K₀.map ψ = K :=
      Subgroup.map_comap_eq_self (hK.trans (Subgroup.map_le_range ψ R))
    have hK₀R : K₀ ≤ R := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hK hx
      rwa [← hψ hyx]
    have hK₀p : Nat.card K₀ = p := by
      rw [← hKp, ← hKmap, Subgroup.card_map_of_injective hψ]
    obtain ⟨S₀, hS₀, hS₀'⟩ := horb K₀ hK₀R hK₀p
    refine ⟨S₀.image (Subgroup.map ψ), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (Subgroup.map_injective hψ)]
      exact hS₀
    · intro K' hK'
      obtain ⟨K₀', hK₀', rfl⟩ := Finset.mem_image.1 hK'
      obtain ⟨g, hg, rfl⟩ := hS₀' K₀' hK₀'
      refine ⟨ψ g, ⟨g, hg, rfl⟩, ?_⟩
      rw [← hKmap, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, map_mul, map_inv]

theorem closure_le_normalizer {R : Subgroup G} {i j h : G} (hq : IsQ8Data R i j h) :
    Subgroup.closure ({i, j, h} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [hq.mem_i, hq.mem_j, hq.mem_h]

end Map

section Lift

variable {V : Type*} [CommGroup V]

theorem modelProj_injective (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥) {M : Type*}
    [Group M] (e : L ⧸ Subgroup.center L ≃* M) : Function.Injective (modelProj L e) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have := mem_center_of_modelProj_eq_one L e hl
  rwa [hZL, Subgroup.mem_bot] at this

theorem exists_modelLift (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥) {M : Type*}
    [Group M] (e : L ⧸ Subgroup.center L ≃* M) :
    ∃ ψ : M →* MulAut V, Function.Injective ψ ∧ ∀ l : L, ψ (modelProj L e l) = l := by
  have hinj := modelProj_injective L hZL e
  set π' := MulEquiv.ofBijective (modelProj L e) ⟨hinj, modelProj_surjective L e⟩ with hπ'
  refine ⟨L.subtype.comp π'.symm.toMonoidHom, L.subtype_injective.comp π'.symm.injective,
    fun l => ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    Subgroup.coe_subtype]
  congr 1
  exact π'.symm_apply_apply l

theorem index_eq_of_modelProj_conj (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {x x₀ : L} {g : M}
    (h : modelProj L e x = g * modelProj L e x₀ * g⁻¹) :
    (fixV (Subgroup.zpowers (x : MulAut V))).index =
      (fixV (Subgroup.zpowers (x₀ : MulAut V))).index := by
  obtain ⟨ψ, -, hψ⟩ := exists_modelLift L hZL e
  obtain ⟨l, rfl⟩ := modelProj_surjective L e g
  have hx : (x : MulAut V) = l * x₀ * (l : MulAut V)⁻¹ := by
    rw [← hψ x, h, ← map_inv, ← map_mul, ← map_mul, hψ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hx, CFSG.QuasithinUnique.Setup.X5.index_fixV_conj]

variable [Finite V] (hV : ∀ v : V, v * v = 1)
include hV

theorem two_pow_le_index_of_orbits (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {R H : Subgroup M} (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (hHN : H ≤ Subgroup.normalizer (R : Set M)) {k : ℕ}
    (horb : ∀ K : Subgroup M, K ≤ R → Nat.card K = p →
      ∃ S : Finset (Subgroup M), k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g K)
    {c : M} (hc : c * c = 1) (hcR : InvOn R c) {m : ℕ}
    (hm : ∀ n : ℕ, 0 < n → orderOf (2 : ZMod p) ∣ 2 * n → m ≤ n) {x : L}
    (hx : modelProj L e x = c) :
    2 ^ (k * m) ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨ψ, hψ, hψπ⟩ := exists_modelLift L hZL e
  obtain ⟨hN, horb'⟩ := orbit_data_map ψ hψ hHN horb
  have hxc : (x : MulAut V) = ψ c := by rw [← hx, hψπ]
  refine two_pow_le_index_fixV_of_inverts hV hp2 (R.map ψ) ?_ ?_ ?_ _ hN horb' ?_ ?_ hm
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, hRc a ha b hb, map_mul]
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hRp r hr, map_one]
  · rw [Subgroup.card_map_of_injective hψ, hRcard]
  · rw [hxc, ← map_mul, hc, map_one]
  · rintro _ ⟨r, hr, rfl⟩
    rw [hxc, ← map_inv, ← map_mul, ← map_mul, hcR r hr, map_inv]

theorem two_pow_le_index_of_orbits_mem (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {R H : Subgroup M} (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (hHN : H ≤ Subgroup.normalizer (R : Set M)) {k : ℕ}
    (horb : ∀ K : Subgroup M, K ≤ R → Nat.card K = p →
      ∃ S : Finset (Subgroup M), k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g K)
    {x : L} (hx : modelProj L e x ∈ R) (hx1 : x ≠ 1) :
    2 ^ ((k - 1) * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨ψ, hψ, hψπ⟩ := exists_modelLift L hZL e
  obtain ⟨hN, horb'⟩ := orbit_data_map ψ hψ hHN horb
  refine two_pow_le_index_fixV_of_mem hV hp2 (R.map ψ) ?_ ?_ ?_ _ hN horb' ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, hRc a ha b hb, map_mul]
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hRp r hr, map_one]
  · rw [Subgroup.card_map_of_injective hψ, hRcard]
  · exact ⟨_, hx, hψπ x⟩
  · intro h1
    exact hx1 (Subtype.ext h1)

end Lift

end CFSG.Quasithin.B45Tor
