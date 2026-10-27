module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Kbar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups Pointwise

namespace SzPS8

open L28

section Centre

variable {K : Type} [Field K] [CharP K 2]

theorem center_sl2_eq_bot : Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h2 := sub_pow_char (p := 2) r 1
  rw [hr, one_pow, sub_self] at h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

noncomputable def slEquivPsl2 : SL(2, K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientBot (G := SL(2, K))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot (K := K)).symm)

theorem fusionIsBenderGroup_of_sl2_gf {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* SL(2, GaloisField 2 f)) : fusionIsBenderGroup X :=
  Or.inl ⟨f, hf, ⟨e.trans slEquivPsl2⟩⟩

end Centre

section Nonabelian

variable {n : ℕ}

theorem card_sl2_gf (hn : n ≠ 0) :
    Nat.card SL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [card_sl2_finiteField, GaloisField.card 2 n hn]

theorem not_isMulCommutative_sl2_gf (hn : n ≠ 0) :
    ¬ IsMulCommutative SL(2, GaloisField 2 n) := by
  intro hc
  have hcard : 1 < Nat.card SL(2, GaloisField 2 n) := by
    rw [card_sl2_gf hn]
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow hn 2
    have h3 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h4 : 3 ≤ (2 ^ n) ^ 2 - 1 := by omega
    nlinarith
  have hnt : Nontrivial SL(2, GaloisField 2 n) := Finite.one_lt_card_iff_nontrivial.mp hcard
  have hc' : Subgroup.center SL(2, GaloisField 2 n) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_center_iff.mpr fun h => hc.is_comm.comm h g
  rw [center_sl2_eq_bot] at hc'
  exact bot_ne_top hc'

theorem not_isMulCommutative_of_sl2_gf {S : Type} [Group S] (hn : n ≠ 0)
    (e : S ≃* SL(2, GaloisField 2 n)) : ¬ IsMulCommutative S := fun h =>
  not_isMulCommutative_sl2_gf hn ⟨⟨fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.is_comm.comm _ _⟩⟩

end Nonabelian

section SylowU

variable {n : ℕ} (hn : n ≠ 0)

include hn in
theorem card_U_gf : Nat.card (U (GaloisField 2 n)) = 2 ^ n := by
  have hinj : Function.Injective (upHom (K := GaloisField 2 n)) := fun x y h =>
    Multiplicative.toAdd.injective (up_injective h)
  rw [U, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (GaloisField 2 n) ≃ GaloisField 2 n),
    GaloisField.card 2 n hn]

omit hn in
theorem isPGroup_U_gf : IsPGroup 2 (U (GaloisField 2 n)) := by
  intro g
  obtain ⟨x, hx⟩ := g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : (g : SL(2, GaloisField 2 n)) ^ 2 = 1 := by
    rw [← hx, pow_two]
    show up (Multiplicative.toAdd x) * up (Multiplicative.toAdd x) = 1
    rw [up_mul, CharTwo.add_self_eq_zero, up_zero]
  simpa using h2

include hn in
theorem index_U_gf : ¬ 2 ∣ (U (GaloisField 2 n)).index := by
  have h := (U (GaloisField 2 n)).card_mul_index
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  rw [card_U_gf hn, card_sl2_finiteField, hq] at h
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have h1 : (U (GaloisField 2 n)).index = (2 ^ n) ^ 2 - 1 := by
    have : 2 ^ n * (U (GaloisField 2 n)).index = 2 ^ n * ((2 ^ n) ^ 2 - 1) := h
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [h1]
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h3 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow h2 (by norm_num)
  have h4 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hpos
  omega

end SylowU

section Conj

variable {n : ℕ} (hn : n ≠ 0)

include hn in
theorem exists_conj_eq_U {P : Subgroup SL(2, GaloisField 2 n)} (hP2 : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) :
    ∃ g : SL(2, GaloisField 2 n), ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ U (GaloisField 2 n) := by
  classical
  let SP : Sylow 2 SL(2, GaloisField 2 n) := hP2.toSylow hPidx
  let SU : Sylow 2 SL(2, GaloisField 2 n) := isPGroup_U_gf.toSylow (index_U_gf hn)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, GaloisField 2 n) SU SP
  refine ⟨g, fun x => ?_⟩
  have h1 : (SP : Subgroup SL(2, GaloisField 2 n)) =
      MulAut.conj g • (SU : Subgroup SL(2, GaloisField 2 n)) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hSP : x ∈ (SP : Subgroup SL(2, GaloisField 2 n)) ↔ x ∈ P := by simp [SP]
  rw [← hSP, h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : s ∈ U (GaloisField 2 n) := by simpa [SU] using hs
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  · intro h
    refine ⟨g⁻¹ * x * g, by simpa [SU] using h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

end Conj

section Normalizer

variable (K : Type) [Field K]

noncomputable def diagHom :
    ↥(Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) →* Kˣ where
  toFun b := Units.mk0 ((b : SL(2, K)) 0 0) (fun h0 => by
    have := sl2_diag_mul (entry10_of_mem_normalizer b.2)
    rw [h0, zero_mul] at this
    exact zero_ne_one this)
  map_one' := by
    ext
    simp
  map_mul' b b' := by
    ext
    simp [sl2_mul_00, entry10_of_mem_normalizer b'.2]

variable {K}

theorem ker_diagHom :
    (diagHom K).ker =
      (U K).subgroupOf (Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_U_iff]
  have hb10 := entry10_of_mem_normalizer b.2
  have hd := sl2_diag_mul hb10
  constructor
  · intro h
    have h0 : (b : SL(2, K)) 0 0 = 1 := congrArg Units.val h
    refine ⟨h0, hb10, ?_⟩
    rw [h0, one_mul] at hd
    exact hd
  · rintro ⟨h0, -, -⟩
    exact Units.ext h0

theorem diagHom_surjective : Function.Surjective (diagHom K) := fun u =>
  ⟨⟨dg (u : K) u.ne_zero, mem_normalizer_of_entry10 rfl⟩, Units.ext rfl⟩

theorem relIndex_normalizer_U :
    (U K).relIndex (Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) =
      Nat.card K - 1 := by
  rw [Subgroup.relIndex, ← ker_diagHom, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (diagHom K)
      diagHom_surjective).toEquiv, Nat.card_units]

end Normalizer

section SylowNormalizer

variable {n : ℕ} (hn : n ≠ 0)

include hn in
theorem relIndex_normalizer_sylow {P : Subgroup SL(2, GaloisField 2 n)} (hP2 : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) :
    P.relIndex (Subgroup.normalizer (P : Set SL(2, GaloisField 2 n))) = 2 ^ n - 1 := by
  obtain ⟨g, hg⟩ := exists_conj_eq_U hn hP2 hPidx
  set c : SL(2, GaloisField 2 n) →* SL(2, GaloisField 2 n) := (MulAut.conj g).toMonoidHom with hc
  have hP : P = (U (GaloisField 2 n)).map c := by
    ext x
    rw [hg x]
    constructor
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [hc, MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [hc, MulAut.conj_apply, mul_assoc] using hu
  have hN : Subgroup.normalizer (P : Set SL(2, GaloisField 2 n)) =
      (Subgroup.normalizer ((U (GaloisField 2 n) : Subgroup _) : Set _)).map c := by
    ext x
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [hc, MulAut.conj_apply, mul_assoc]⟩
      show g⁻¹ * x * g ∈ Subgroup.normalizer ((U (GaloisField 2 n) : Subgroup _) : Set _)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := hx (g * y * g⁻¹)
      rw [hg (g * y * g⁻¹), hg (x * (g * y * g⁻¹) * x⁻¹)] at this
      simpa [mul_assoc] using this
    · rintro ⟨z, hz, rfl⟩ y
      rw [hg y, hg (c z * y * (c z)⁻¹)]
      have := (Subgroup.mem_normalizer_iff.mp hz) (g⁻¹ * y * g)
      simpa [hc, MulAut.conj_apply, mul_assoc] using this
  rw [hN, hP, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    relIndex_normalizer_U, GaloisField.card 2 n hn]

end SylowNormalizer

section Borel

variable {G : Type} [Group G]

theorem relIndex_eq_relIndex_map {H S : Type*} [Group H] [Group S] (ρ : H →* S)
    {T₀ K : Subgroup H} (hTK : T₀ ≤ K) (hker : ∀ k ∈ K, ρ k = 1 → k ∈ T₀) :
    T₀.relIndex K = (T₀.map ρ).relIndex (K.map ρ) := by
  have h1 : ((T₀.map ρ).comap ρ).relIndex K = (T₀.map ρ).relIndex (K.map ρ) :=
    Subgroup.relIndex_comap (T₀.map ρ) ρ K
  rw [← h1]
  have h2 : ((T₀.map ρ).comap ρ) ⊓ K = T₀ := by
    apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨t, htT, htx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx1)
      have : t⁻¹ * x ∈ T₀ := hker _ (K.mul_mem (K.inv_mem (hTK htT)) hx2) (by
        rw [map_mul, map_inv, htx, inv_mul_cancel])
      simpa using T₀.mul_mem htT this
    · intro x hx
      exact ⟨Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ρ hx), hTK hx⟩
  conv_rhs => rw [← Subgroup.inf_relIndex_right, h2]

variable {n : ℕ} (hn : n ≠ 0)

include hn in
theorem relIndex_borel_of_surjective {L S : Subgroup G} (hSL : S ≤ L)
    (hS : IsSylowTwoOf S L) (ε : ↥L →* SL(2, GaloisField 2 n)) (hε : Function.Surjective ε)
    (hker : ∀ x : ↥L, ε x = 1 → (x : G) ∈ S) :
    S.relIndex (L ⊓ Subgroup.normalizer (S : Set G)) = 2 ^ n - 1 := by
  classical
  set S₀ : Subgroup ↥L := S.subgroupOf L with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  set P : Subgroup SL(2, GaloisField 2 n) := S₀.map ε with hP
  have hP2 : IsPGroup 2 ↥P := hS₀2.map ε
  have hPidx : ¬ 2 ∣ P.index := fun hd =>
    hS.2.2 (hd.trans (Subgroup.index_map_dvd S₀ hε))
  set B₀ : Subgroup ↥L := (L ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L with hB₀
  have hS₀B₀ : S₀ ≤ B₀ := fun x hx => ⟨x.2, Subgroup.le_normalizer hx⟩
  have hfwd : ∀ b : ↥L, (∀ g : G, g ∈ S ↔ (b : G) * g * (b : G)⁻¹ ∈ S) →
      ∀ y ∈ P, ε b * y * (ε b)⁻¹ ∈ P := by
    intro b hb y hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨b * s * b⁻¹, ?_, by simp⟩
    show ((b * s * b⁻¹ : ↥L) : G) ∈ S
    simpa using (hb (s : G)).mp hs
  have hkey : ∀ c : ↥L, ε c ∈ Subgroup.normalizer (P : Set SL(2, GaloisField 2 n)) →
      ∀ s : ↥L, (s : G) ∈ S → ((c * s * c⁻¹ : ↥L) : G) ∈ S := by
    intro c hc s hs
    have h1 : ε c * ε s * (ε c)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hc (ε s)).mp ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := h1
    have h3 : ε (s'⁻¹ * (c * s * c⁻¹)) = 1 := by
      rw [map_mul, map_inv, hs'e, map_mul, map_mul, map_inv]
      group
    have h4 : ((s'⁻¹ * (c * s * c⁻¹) : ↥L) : G) ∈ S := hker _ h3
    have h5 : ((c * s * c⁻¹ : ↥L) : G) = (s' : G) * ((s'⁻¹ * (c * s * c⁻¹) : ↥L) : G) := by
      simp
    rw [h5]
    exact S.mul_mem hs' h4
  have hmap : B₀.map ε = Subgroup.normalizer (P : Set SL(2, GaloisField 2 n)) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbn : ∀ g : G, g ∈ S ↔ (b : G) * g * (b : G)⁻¹ ∈ S :=
        Subgroup.mem_normalizer_iff.mp hb.2
      have hconj : ∀ g : G, (b : G) * ((b : G)⁻¹ * g * (b : G)) * (b : G)⁻¹ = g := by
        intro g
        group
      have hbn' : ∀ g : G, g ∈ S ↔ ((b⁻¹ : ↥L) : G) * g * ((b⁻¹ : ↥L) : G)⁻¹ ∈ S := by
        intro g
        have h := hbn ((b : G)⁻¹ * g * (b : G))
        rw [hconj g] at h
        simpa using h.symm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨hfwd b hbn y, fun hy => by
        have := hfwd b⁻¹ hbn' _ hy
        simpa [mul_assoc] using this⟩
    · intro hx
      obtain ⟨b, rfl⟩ := hε x
      refine ⟨b, ⟨b.2, ?_⟩, rfl⟩
      show (b : G) ∈ Subgroup.normalizer (S : Set G)
      rw [Subgroup.mem_normalizer_iff]
      have hcinv : ε b⁻¹ ∈ Subgroup.normalizer (P : Set SL(2, GaloisField 2 n)) := by
        rw [map_inv]
        exact (Subgroup.normalizer _).inv_mem hx
      intro g
      constructor
      · intro hg
        have := hkey b hx ⟨g, hSL hg⟩ hg
        simpa using this
      · intro hg
        have hgL : (b : G) * g * (b : G)⁻¹ ∈ L := hSL hg
        have := hkey b⁻¹ hcinv ⟨_, hgL⟩ hg
        simpa [mul_assoc] using this
  have hkerS₀ : ∀ x ∈ B₀, ε x = 1 → x ∈ S₀ := fun x _ hx => hker x hx
  have h1 : S₀.relIndex B₀ = P.relIndex (Subgroup.normalizer (P : Set SL(2, GaloisField 2 n))) := by
    rw [relIndex_eq_relIndex_map ε hS₀B₀ hkerS₀, hmap]
  have h2 : (S₀.map L.subtype).relIndex (B₀.map L.subtype) = S₀.relIndex B₀ :=
    Subgroup.relIndex_map_map_of_injective S₀ B₀ L.subtype_injective
  rw [hS₀, hB₀, Subgroup.map_subgroupOf_eq_of_le hSL,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
  rw [h2, hS₀, hB₀] at *
  rw [h1, relIndex_normalizer_sylow hn hP2 hPidx]

end Borel

end SzPS8

end CFSG.Quasithin
