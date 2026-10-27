module

public import CFSG.Quasithin.Background.RonanE611Sp4X
public import CFSG.Quasithin.Background.RonanE611Gen
public import CFSG.Quasithin.Background.ONanE68Sp4

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6.E68Proof CFSG.RankThree.PartOne.KCRootAxis

namespace Sp4G

section Basic

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def Adapted (φ : ↥L ≃* antiSp K) (S : Subgroup G) : Prop :=
  (S.subgroupOf L).map φ.toMonoidHom = antiUnipotent K

@[expose] def emb (φ : ↥L ≃* antiSp K) : antiSp K →* G := L.subtype.comp φ.symm.toMonoidHom

variable (φ : ↥L ≃* antiSp K)

theorem emb_phi (g : ↥L) : emb φ (φ g) = (g : G) := by simp [emb]

theorem emb_injective : Function.Injective (emb φ) := fun x y h =>
  φ.symm.injective (Subtype.ext h)

theorem emb_mem (x : antiSp K) : emb φ x ∈ L := (φ.symm x).2

theorem exists_emb {g : G} (hg : g ∈ L) : ∃ x, emb φ x = g := ⟨φ ⟨g, hg⟩, emb_phi φ ⟨g, hg⟩⟩

variable {S : Subgroup G}

theorem mem_antiUnipotent_iff (hφ : Adapted φ S) (y : antiSp K) :
    y ∈ antiUnipotent K ↔ emb φ y ∈ S := by
  rw [← hφ]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, emb_phi]
    exact hg
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    exact hy

theorem emb_mem_normalizer (hφ : Adapted φ S) (hSL : S ≤ L) {b : antiSp K}
    (hb : b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) :
    emb φ b ∈ L ⊓ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_inf.2 ⟨emb_mem φ b, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hconj : ∀ y : antiSp K, emb φ b * emb φ y * (emb φ b)⁻¹ = emb φ (b * y * b⁻¹) := fun y => by
    simp [map_mul, map_inv]
  constructor
  · intro hg
    obtain ⟨y, rfl⟩ := exists_emb φ (hSL hg)
    rw [hconj, ← mem_antiUnipotent_iff φ hφ]
    exact (Subgroup.mem_normalizer_iff.1 hb y).1 ((mem_antiUnipotent_iff φ hφ y).2 hg)
  · intro hg
    have hgL : g ∈ L := by
      have h1 := hSL hg
      have h2 : (emb φ b)⁻¹ * (emb φ b * g * (emb φ b)⁻¹) * emb φ b ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (emb_mem φ b)) h1) (emb_mem φ b)
      simpa [mul_assoc] using h2
    obtain ⟨y, rfl⟩ := exists_emb φ hgL
    rw [hconj, ← mem_antiUnipotent_iff φ hφ] at hg
    exact (mem_antiUnipotent_iff φ hφ y).1 ((Subgroup.mem_normalizer_iff.1 hb y).2 hg)

theorem card_comap_emb {T : Subgroup G} (hTL : T ≤ L) : Nat.card (T.comap (emb φ)) = Nat.card T := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : ↥(T.comap (emb φ)) => (⟨emb φ x, x.2⟩ : ↥T))
    ⟨fun a b h => ?_, fun w => ?_⟩)
  · have h1 := congrArg Subtype.val h
    have h' : emb φ (a : antiSp K) = emb φ (b : antiSp K) := h1
    exact Subtype.ext (emb_injective φ h')
  · obtain ⟨x, hx⟩ := exists_emb φ (hTL w.2)
    exact ⟨⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact w.2)⟩, Subtype.ext hx⟩

theorem map_comap_emb {T : Subgroup G} (hTL : T ≤ L) : (T.comap (emb φ)).map (emb φ) = T := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    obtain ⟨x, hx⟩ := exists_emb φ (hTL hg)
    exact ⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact hg), hx⟩

end Basic

section Adapted

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

theorem exists_adapted {n : ℕ} (hn : 2 ≤ n) (hL : StatedClassicalModel ↥L .PSp 2 2 n)
    (hS : IsSylowTwoOf S L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : ↥L ≃* antiSp K),
      Nat.card K = 2 ^ n ∧ Adapted φ S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU2, hUidx⟩ := isPGroup_and_not_dvd_index
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  have hS0 := isSylowTwoOf_subgroupOf_top_of hS
  obtain ⟨hP2, hPidx⟩ := isPGroup_and_not_dvd_index hS0
  obtain ⟨e', he'⟩ := exists_equiv_map_eq_sylow ((antiProjEquiv K).trans e.symm)
    (hU2.toSylow hUidx) (hP2.toSylow hPidx)
  have hmap : (antiUnipotent K).map e'.toMonoidHom = S.subgroupOf L := he'
  refine ⟨K, inferInstance, inferInstance, hchar, e'.symm, hK, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv, ← hmap, Subgroup.mem_map_equiv]
  simp

end Adapted

section Roots

variable {G : Type} [Group G] {L S : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_roots_of_central {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {φ : ↥L ≃* antiSp K}
    (hφ : Adapted φ S) (hSL : S ≤ L) {W : Subgroup G} (hWS : W ≤ S)
    (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w)
    (hWn : ∀ b ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ w ∈ W, b * w * b⁻¹ ∈ W)
    (hWcard : Nat.card W = 2 ^ n) :
    W = (rootShort K).map (emb φ) ∨ W = (rootLong K).map (emb φ) := by
  have hmap := map_comap_emb φ (hWS.trans hSL)
  have hW'' := Sp4X.eq_rootShort_or_rootLong hK hn (W := W.comap (emb φ))
    (fun x hx => (mem_antiUnipotent_iff φ hφ x).2 (hWS (Subgroup.mem_comap.1 hx)))
    (fun w hw s hs => by
      apply emb_injective φ
      rw [map_mul, map_mul]
      exact hWc _ (Subgroup.mem_comap.1 hw) _ ((mem_antiUnipotent_iff φ hφ s).1 hs))
    (fun b hb w hw => by
      refine Subgroup.mem_comap.2 ?_
      rw [map_mul, map_mul, map_inv]
      exact hWn _ (emb_mem_normalizer φ hφ hSL hb) _ (Subgroup.mem_comap.1 hw))
    (by rw [card_comap_emb φ (hWS.trans hSL)]; exact hWcard)
  rcases hW'' with h | h
  · left
    rw [← hmap, h]
  · right
    rw [← hmap, h]

end Roots

section Parabolic

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem rootU_one : rootU K Axis.one = rootShort K := Subgroup.ext fun _ => Iff.rfl

theorem rootU_two : rootU K Axis.two = rootLong K := Subgroup.ext fun _ => Iff.rfl

theorem parabolic {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {φ : ↥L ≃* antiSp K}
    (hφ : Adapted φ S) (hS : IsSylowTwoOf S L) {P W : Subgroup G} (hPL : P ≤ L)
    (hPS : L ⊓ Subgroup.normalizer (S : Set G) ≤ P) (hPlt : P ≠ L)
    (hPmax : ∀ K' : Subgroup G, P ≤ K' → K' ≤ L → K' = P ∨ K' = L)
    (hWS : W ≤ S) (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w)
    (hWn : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W) (hW2 : ∀ w ∈ W, w * w = 1)
    (hWcard : Nat.card W = 2 ^ n) :
    ∃ i : Axis, W = (rootU K i).map (emb φ) ∧ P = (rootN K i).map (emb φ) ∧
      rootGroupOfParabolicR P = W ∧
      (∀ g ∈ L, (∀ w ∈ W, g * w = w * g) → g ∈ P) ∧
      ⁅L ⊓ Subgroup.centralizer (W : Set G), L ⊓ Subgroup.centralizer (W : Set G)⁆ =
        L ⊓ Subgroup.centralizer (W : Set G) ∧
      ∃ X₀ : Subgroup G, X₀ ≤ P ∧ IsCyclic ↥X₀ ∧ Nat.card ↥X₀ = 2 ^ n - 1 ∧
        ∀ p ∈ P, ∃ c ∈ L ⊓ Subgroup.centralizer (W : Set G), ∃ x ∈ X₀, p = c * x := by
  classical
  have hSL : S ≤ L := hS.1
  have hSP : S ≤ P := fun s hs => hPS (Subgroup.mem_inf.2 ⟨hSL hs, Subgroup.le_normalizer hs⟩)
  have hB : ∀ b ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ w ∈ W, b * w * b⁻¹ ∈ W :=
    fun b hb w hw => hWn b (hPS hb) w hw
  have hex : ∃ i : Axis, W = (rootU K i).map (emb φ) := by
    rcases eq_roots_of_central hn hK hφ hSL hWS hWc hB hWcard with h | h
    · exact ⟨Axis.one, by rw [rootU_one]; exact h⟩
    · exact ⟨Axis.two, by rw [rootU_two]; exact h⟩
  obtain ⟨i, hWi⟩ := hex
  have hW'' : W.comap (emb φ) = rootU K i := by
    rw [hWi, Subgroup.comap_map_eq_self_of_injective (emb_injective φ)]
  have hWmem : ∀ x : antiSp K, x ∈ rootU K i ↔ emb φ x ∈ W := fun x => by
    rw [← hW'', Subgroup.mem_comap]
  have hPmem : ∀ x : antiSp K, x ∈ P.comap (emb φ) ↔ emb φ x ∈ P := fun x => Subgroup.mem_comap
  have hPmax'' : ∀ K'' : Subgroup (antiSp K), P.comap (emb φ) ≤ K'' →
      K'' = P.comap (emb φ) ∨ K'' = ⊤ := by
    intro K'' hK''
    have hK'L : K''.map (emb φ) ≤ L := by
      rintro _ ⟨x, -, rfl⟩
      exact emb_mem φ x
    have hPK' : P ≤ K''.map (emb φ) := by
      intro p hp
      obtain ⟨x, hx⟩ := exists_emb φ (hPL hp)
      exact ⟨x, hK'' (Subgroup.mem_comap.2 (by rw [hx]; exact hp)), hx⟩
    rcases hPmax _ hPK' hK'L with h | h
    · left
      apply le_antisymm
      · intro x hx
        have : emb φ x ∈ K''.map (emb φ) := ⟨x, hx, rfl⟩
        rw [h] at this
        exact Subgroup.mem_comap.2 this
      · exact hK''
    · right
      rw [eq_top_iff]
      intro x _
      have : emb φ x ∈ K''.map (emb φ) := by rw [h]; exact emb_mem φ x
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← emb_injective φ hyx]
  have hPle : P.comap (emb φ) ≤ rootN K i := by
    intro p hp
    rw [rootN, Subgroup.mem_normalizer_iff]
    intro u
    have hfwd : ∀ (q : antiSp K), q ∈ P.comap (emb φ) → ∀ u ∈ rootU K i, q * u * q⁻¹ ∈ rootU K i := by
      intro q hq u hu
      rw [hWmem] at hu ⊢
      rw [map_mul, map_mul, map_inv]
      exact hWn _ ((hPmem q).1 hq) _ hu
    constructor
    · exact hfwd p hp u
    · intro hu
      have := hfwd p⁻¹ (Subgroup.inv_mem _ hp) _ hu
      simpa [mul_assoc] using this
  have hP'' : P.comap (emb φ) = rootN K i := by
    rcases hPmax'' (rootN K i) hPle with h | h
    · exact h.symm
    · exact absurd h (ne_of_lt (Sp4X.rootN_lt_top hK hn i))
  have hPi : P = (rootN K i).map (emb φ) := by
    rw [← hP'', map_comap_emb φ hPL]
  have hSP' : IsSylowTwoOf S P := isSylowTwoOf_of_le hS hSP hPL
  refine ⟨i, hWi, hPi, ?_, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro z hz
      have hz1 := (Subgroup.mem_inf.1 hz).1
      have hz2 := (Subgroup.mem_inf.1 hz).2
      have hzP : z ∈ P := by
        have : Subgroup.closure {x : G | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} ≤ P :=
          (Subgroup.closure_le P).2 fun x hx => hx.1
        exact this hz1
      obtain ⟨z'', hz''⟩ := exists_emb φ (hPL hzP)
      have hz''N : z'' ∈ rootN K i := by
        rw [← hP'']
        exact (hPmem z'').2 (by rw [hz'']; exact hzP)
      have hcomm : ∀ y ∈ rootN K i, (∃ k : ℕ, y ^ 2 ^ k = 1) → z'' * y = y * z'' := by
        intro y hy ⟨k, hk⟩
        have hyP : emb φ y ∈ P := (hPmem y).1 (by rw [hP'']; exact hy)
        have h2 : emb φ y ∈ Subgroup.closure {x : G | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} :=
          Subgroup.subset_closure ⟨hyP, k, by rw [← map_pow, hk, map_one]⟩
        have h3 := Subgroup.mem_centralizer_iff.1 hz2 _ h2
        apply emb_injective φ
        rw [map_mul, map_mul, hz'']
        exact h3.symm
      have hu := Sp4X.mem_rootU_of_commute_two_elements hK hn i hz''N hcomm
      have := (hWmem z'').1 hu
      rwa [hz''] at this
    · exact le_rootGroupOfParabolicR hSP' hWS hWc hWn
        (fun w hw => ⟨1, by rw [pow_one, pow_two]; exact hW2 w hw⟩)
  ·
    intro g hgL hgc
    obtain ⟨x, rfl⟩ := exists_emb φ hgL
    have hx : x ∈ rootC K i := by
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      apply emb_injective φ
      rw [map_mul, map_mul]
      exact (hgc _ ((hWmem u).1 hu)).symm
    have : x ∈ P.comap (emb φ) := by
      rw [hP'']
      exact Sp4X.rootC_le_rootN i hx
    exact (hPmem x).1 this
  ·
    have hC : L ⊓ Subgroup.centralizer (W : Set G) = (rootC K i).map (emb φ) := by
      ext g
      constructor
      · intro hg
        have hgL := (Subgroup.mem_inf.1 hg).1
        have hgc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2
        obtain ⟨x, rfl⟩ := exists_emb φ hgL
        refine ⟨x, ?_, rfl⟩
        refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
        apply emb_injective φ
        rw [map_mul, map_mul]
        exact hgc _ ((hWmem u).1 hu)
      · rintro ⟨x, hx, rfl⟩
        refine Subgroup.mem_inf.2 ⟨emb_mem φ x, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
        obtain ⟨u, hu⟩ := exists_emb φ ((hWS.trans hSL) hw)
        have huW : u ∈ rootU K i := (hWmem u).2 (by rw [hu]; exact hw)
        have := Subgroup.mem_centralizer_iff.1 hx u huW
        rw [← hu, ← map_mul, ← map_mul, this]
    rw [hC, ← Subgroup.map_commutator, Sp4X.rootC_perfect hK hn i]
  ·
    obtain ⟨X₀, hX₀N, hX₀c, hX₀card, hX₀dec⟩ := Sp4X.exists_complement hK hn i
    refine ⟨X₀.map (emb φ), ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (hPmem x).1 (by rw [hP'']; exact hX₀N hx)
    · have : IsCyclic ↥X₀ := hX₀c
      exact isCyclic_of_surjective (Subgroup.equivMapOfInjective X₀ (emb φ)
        (emb_injective φ)).toMonoidHom (Subgroup.equivMapOfInjective X₀ (emb φ)
        (emb_injective φ)).surjective
    · rw [Subgroup.card_map_of_injective (emb_injective φ)]
      exact hX₀card
    · intro p hp
      obtain ⟨x, rfl⟩ := exists_emb φ (hPL hp)
      have hxN : x ∈ rootN K i := by
        rw [← hP'']
        exact (hPmem x).2 hp
      obtain ⟨c, hc, x₀, hx₀, rfl⟩ := hX₀dec x hxN
      refine ⟨emb φ c, Subgroup.mem_inf.2 ⟨emb_mem φ c, Subgroup.mem_centralizer_iff.2
        fun w hw => ?_⟩, emb φ x₀, ⟨x₀, hx₀, rfl⟩, map_mul _ _ _⟩
      obtain ⟨u, hu⟩ := exists_emb φ ((hWS.trans hSL) hw)
      have huW : u ∈ rootU K i := (hWmem u).2 (by rw [hu]; exact hw)
      have := Subgroup.mem_centralizer_iff.1 hc u huW
      rw [← hu, ← map_mul, ← map_mul, this]

end Parabolic

end Sp4G

end CFSG.Quasithin.RonanE611
