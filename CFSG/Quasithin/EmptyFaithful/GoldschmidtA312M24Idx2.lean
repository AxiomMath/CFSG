module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Mem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

section Index

variable {G : Type} [Group G] [Finite G]

theorem isExt_e2_of_index_two {T B Z : Subgroup G} (hT : IsPGroup 2 T) (hB : B ∈ lFamily T)
    (hZ : B ⊔ T = Z) {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : ∃ a b : Q, a * b ≠ b * a)
    (ρ : ↥Z →* Q) (hρ : Function.Surjective ρ) {V : Subgroup G} (hVZ : V ≤ Z)
    (hVker : V.subgroupOf Z ≤ ρ.ker) (hVn : Z ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1) {k : ℕ}
    (hVcard : Nat.card V = 2 ^ k) (hkerc : Nat.card ρ.ker = 2 * 2 ^ k) {u : G} (hu : u ∈ Z)
    {m : ℕ} (hm : m % 2 = 1) (hum : u ^ m = 1) (hcomm : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v)
    (hne : perfectCore Z ≠ Z) {PY : ∀ (V : Type) [Group V], Prop}
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W) (hQY : PY Q) :
    IsExt ↥B (fun V _ => IsE2 k V) PY := by
  have : Finite Q := Finite.of_surjective ρ hρ
  have hAZ : perfectCore Z ≤ Z := perfectCore_le Z
  have hVA : V ≤ perfectCore Z := by
    have := le_perfectCore_of_commutators hT hB (hZ ▸ hVZ) (hZ ▸ hu) hm hum hcomm
    rwa [hZ] at this
  have hA'eq : (perfectCore Z).subgroupOf Z = perfectCore (⊤ : Subgroup ↥Z) :=
    subgroupOf_perfectCore Z
  have hQperf : perfectCore (⊤ : Subgroup Q) = ⊤ :=
    perfectCore_eq_self_of_perfect (Seven.commutator_eq_top_of_simple hQ)
  have hmap : ((perfectCore Z).subgroupOf Z).map ρ = ⊤ := by
    rw [hA'eq, map_perfectCore ρ ⊤, Subgroup.map_top, MonoidHom.range_eq_top.mpr hρ, hQperf]
  have hKA : ¬ ρ.ker ≤ (perfectCore Z).subgroupOf Z := by
    intro hK
    apply hne
    have htop : (perfectCore Z).subgroupOf Z = ⊤ := by
      rw [eq_top_iff]
      intro z _
      have hz : ρ z ∈ ((perfectCore Z).subgroupOf Z).map ρ := by rw [hmap]; exact Subgroup.mem_top _
      obtain ⟨a, ha, haz⟩ := hz
      have hk : a⁻¹ * z ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, haz, inv_mul_cancel]
      have := Subgroup.mul_mem _ ha (hK hk)
      simpa using this
    exact le_antisymm hAZ (Subgroup.subgroupOf_eq_top.mp htop)
  have hV2 : Nat.card (V.subgroupOf Z) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVZ).toEquiv, hVcard]
  set N : Subgroup ↥Z := (perfectCore Z).subgroupOf Z ⊓ ρ.ker with hNdef
  have hNle : N ≤ ρ.ker := inf_le_right
  have hVN : V.subgroupOf Z ≤ N := le_inf (fun x hx => hVA hx) hVker
  have hN : Nat.card N = 2 ^ k := by
    have h1 : 2 ^ k ∣ Nat.card N := hV2 ▸ Subgroup.card_dvd_of_le hVN
    have h2 : Nat.card N ∣ Nat.card ρ.ker := Subgroup.card_dvd_of_le hNle
    have h3 : Nat.card N ≠ Nat.card ρ.ker := by
      intro h
      apply hKA
      have := Subgroup.eq_of_le_of_card_ge hNle (le_of_eq h.symm)
      intro x hx
      exact (this ▸ hx : x ∈ N).1
    rw [hkerc] at h2 h3
    obtain ⟨c, hc⟩ := h1
    have hpos : 0 < 2 ^ k := by positivity
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exfalso
        have : 0 < Nat.card N := Nat.card_pos
        rw [hc, h] at this
        simp at this
      · exact h
    rw [hc] at h2 h3 ⊢
    have h4 : 2 ^ k * c ∣ 2 ^ k * 2 := by rwa [mul_comm 2 (2 ^ k)] at h2
    have h5 : c ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hpos h4
    have h6 : c ≤ 2 := Nat.le_of_dvd (by norm_num) h5
    have h7 : c ≠ 2 := fun h => h3 (by rw [h, mul_comm])
    have h8 : c = 1 := by omega
    rw [h8, mul_one]
  have hAeq : Nat.card ((perfectCore Z).subgroupOf Z) = Nat.card (perfectCore Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hcardA : Nat.card ((perfectCore Z).subgroupOf Z) = Nat.card Q * 2 ^ k := by
    let φ : ↥((perfectCore Z).subgroupOf Z) →* Q := ρ.comp ((perfectCore Z).subgroupOf Z).subtype
    have hφr : φ.range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    have hφk : φ.ker = ρ.ker.subgroupOf ((perfectCore Z).subgroupOf Z) := rfl
    have hker : ρ.ker.subgroupOf ((perfectCore Z).subgroupOf Z) =
        N.subgroupOf ((perfectCore Z).subgroupOf Z) := by
      ext x
      simp [hNdef, Subgroup.mem_subgroupOf]
    have h := card_eq_range_mul_ker φ
    rw [hφr, Subgroup.card_top, hφk, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ _)).toEquiv, hN] at h
    exact h
  have hcardZ : Nat.card Z = 2 * Nat.card (perfectCore Z) := by
    have h1 := card_eq_range_mul_ker ρ
    rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, hkerc] at h1
    rw [h1, ← hAeq, hcardA]
    ring
  have hcommZ : ⁅Z, Z⁆ ≤ perfectCore Z := PermLat.commutator_le_of_card_eq_two_mul hAZ hcardZ
  let f : ↥(perfectCore Z) →* Q := ρ.comp (Subgroup.inclusion hAZ)
  have hfs : Function.Surjective f := by
    intro q
    have hq : q ∈ ((perfectCore Z).subgroupOf Z).map ρ := by rw [hmap]; exact Subgroup.mem_top q
    obtain ⟨z, hz, hzq⟩ := hq
    exact ⟨⟨z.1, hz⟩, hzq⟩
  have hcardA' : Nat.card (perfectCore Z) = Nat.card Q * 2 ^ k := hAeq ▸ hcardA
  have hfk : Nat.card f.ker = 2 ^ k := by
    have h := card_eq_range_mul_ker f
    rw [MonoidHom.range_eq_top.mpr hfs, Subgroup.card_top, hcardA'] at h
    have hpos : 0 < Nat.card Q := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos h).symm
  have hVf : V.subgroupOf (perfectCore Z) ≤ f.ker := by
    intro x hx
    exact hVker (show (⟨x.1, hAZ x.2⟩ : ↥Z) ∈ V.subgroupOf Z from hx)
  have hVf2 : Nat.card (V.subgroupOf (perfectCore Z)) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard]
  have hfker : f.ker = V.subgroupOf (perfectCore Z) :=
    (Subgroup.eq_of_le_of_card_ge hVf (by rw [hfk, hVf2])).symm
  have : (V.subgroupOf (perfectCore Z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mpr (hAZ.trans hVn)
  have hE2 : IsE2 k ↥(V.subgroupOf (perfectCore Z)) :=
    PermLat.isElemAbelianOfRank_of_card
      (fun x y => Subtype.ext (Subtype.ext (hVc x.1.1 x.2 y.1.1 y.2)))
      (fun x => Subtype.ext (Subtype.ext (hVsq x.1.1 x.2))) hVf2
  have hsolv : Group.IsSolvable f.ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (IsPGroup.of_card hfk).isNilpotent
    infer_instance
  refine A312ExtShapes.isExt_of_perfect_simple_quotient hB hZ hAZ hcommZ (perfectCore_perfect Z)
    hQ f hfs hsolv (fun V W _ _ e h => IsE2.of_mulEquiv e h) hPY (V.subgroupOf (perfectCore Z))
    hE2 ?_
  exact hPY _ _ ((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hfker)) hQY

end Index

end CFSG.Quasithin.A312M24
