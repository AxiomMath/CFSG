module

public import CFSG.Permutation.FiveTransitive.Reduction
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedFive

open MulAction SubMulAction Subgroup

private theorem normal_fixing_card_le_of_maps
    (G X : Type*) [Group G] [Finite G] [MulAction G X]
    (N : Subgroup G) [N.Normal] {k : ℕ} (a b : Fin k ↪ X)
    (q : G) (hq : ∀ i, q • a i = b i) :
    Nat.card (fixingSubgroup N (Set.range a)) ≤
      Nat.card (fixingSubgroup N (Set.range b)) := by
  let f : fixingSubgroup N (Set.range a) → fixingSubgroup N (Set.range b) :=
    fun z => ⟨MulAut.conjNormal q (z : N), by
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨i, rfl⟩
      change (q * ((z : N) : G) * q⁻¹) • b i = b i
      rw [mul_smul, mul_smul, ← hq i, inv_smul_smul]
      have hz := (mem_fixingSubgroup_iff N).mp z.property (a i) ⟨i, rfl⟩
      change q • ((z : N) • a i) = q • a i
      rw [hz]⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  exact (MulAut.conjNormal q : MulAut N).injective (congrArg Subtype.val h)

private theorem normal_fixing_card_eq
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (N : Subgroup G) [N.Normal] (k : ℕ)
    (hk : MulAction.IsMultiplyPretransitive G X k)
    (s t : Set X) (hs : s.ncard = k) (ht : t.ncard = k) :
    Nat.card (fixingSubgroup N s) = Nat.card (fixingSubgroup N t) := by
  obtain ⟨m, a, ha⟩ := s.toFinite.fin_embedding
  have hm : m = k := by
    rw [← hs, ← ha, Set.ncard_range_of_injective a.injective, Nat.card_fin]
  subst m
  obtain ⟨m, b, hb⟩ := t.toFinite.fin_embedding
  have hm : m = k := by
    rw [← ht, ← hb, Set.ncard_range_of_injective b.injective, Nat.card_fin]
  subst m
  obtain ⟨q, hq⟩ := hk.exists_smul_eq a b
  have hq' (i : Fin k) : q • a i = b i := DFunLike.congr_fun hq i
  rw [← ha, ← hb]
  apply Nat.le_antisymm (normal_fixing_card_le_of_maps G X N a b q hq')
  apply normal_fixing_card_le_of_maps G X N b a q⁻¹
  intro i
  rw [← hq' i, inv_smul_smul]

@[expose] abbrev normalSylowImage
    (G X : Type*) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ}
    (S : Sylow p (fixingSubgroup N s)) : Subgroup G :=
  (S : Subgroup (fixingSubgroup N s)).map
    (N.subtype.comp (fixingSubgroup N s).subtype)

private abbrev normalFixerImage
    (G X : Type*) [Group G] [MulAction G X] (N : Subgroup G) (s : Set X) : Subgroup G :=
  (fixingSubgroup N s).map N.subtype

private theorem mem_normalFixerImage_iff
    (G X : Type*) [Group G] [MulAction G X] (N : Subgroup G) (s : Set X) (g : G) :
    g ∈ normalFixerImage G X N s ↔ g ∈ N ∧ ∀ x ∈ s, g • x = x := by
  constructor
  · intro hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨n.property, (mem_fixingSubgroup_iff N).mp hn⟩
  · rintro ⟨hgN, hgfix⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hgN⟩, (mem_fixingSubgroup_iff N).mpr hgfix, rfl⟩

theorem exists_mem_normalizer_maps_fixed_five
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (s : Set X) (hs : s.ncard = 4)
    {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup N s))
    (a b : Fin 5 → X) (ha : Function.Injective a) (hb : Function.Injective b)
    (haR : ∀ r ∈ normalSylowImage G X N s S, ∀ i, r • a i = a i)
    (hbR : ∀ r ∈ normalSylowImage G X N s S, ∀ i, r • b i = b i) :
    ∃ g : G, g ∈ Subgroup.normalizer (normalSylowImage G X N s S) ∧
      ∀ i, g • a i = b i := by
  classical
  let H : Subgroup N := fixingSubgroup N s
  let SP : Subgroup G := normalSylowImage G X N s S
  let bX : Fin 5 ↪ X := ⟨b, hb⟩
  let b4 : Fin 4 ↪ X := ⟨fun i => b i.castSucc, hb.comp (Fin.castSucc_injective 4)⟩
  let t : Set X := Set.range bX
  let t4 : Set X := Set.range b4
  let Ht : Subgroup G := normalFixerImage G X N t
  let H4 : Subgroup G := normalFixerImage G X N t4
  have ht4 : t4.ncard = 4 := by
    rw [Set.ncard_range_of_injective b4.injective, Nat.card_fin]
  have ht4t : t4 ⊆ t := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, rfl⟩
  have hHt4 : Ht ≤ H4 := by
    intro g hg
    have h := (mem_normalFixerImage_iff G X N t g).mp hg
    exact (mem_normalFixerImage_iff G X N t4 g).mpr ⟨h.1, fun x hx => h.2 x (ht4t hx)⟩
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5
  have hcard : 5 ≤ Fintype.card X := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective a ha
  have h4 : MulAction.IsMultiplyPretransitive G X 4 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 4) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hH4card : Nat.card H4 = Nat.card H := by
    calc
      Nat.card H4 = Nat.card (fixingSubgroup N t4) :=
        (Nat.card_congr ((fixingSubgroup N t4).equivMapOfInjective
          N.subtype N.subtype_injective).toEquiv).symm
      _ = Nat.card H := (normal_fixing_card_eq G X N 4 h4 s t4 hs ht4).symm
  obtain ⟨q, hqEmb⟩ := h5.exists_smul_eq (⟨a, ha⟩ : Fin 5 ↪ X) bX
  have hq (i : Fin 5) : q • a i = b i := DFunLike.congr_fun hqEmb i
  have hSPleN : SP ≤ N := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact (w : N).property
  have hSPleHt : SP ≤ Ht := by
    intro z hz
    apply (mem_normalFixerImage_iff G X N t z).mpr
    refine ⟨hSPleN hz, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hbR z hz i
  let QSP : Subgroup G := SP.map (MulAut.conj q).toMonoidHom
  have hQSPleHt : QSP ≤ Ht := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    apply (mem_normalFixerImage_iff G X N t _).mpr
    refine ⟨(inferInstance : N.Normal).conj_mem w (hSPleN hw) q, ?_⟩
    rintro _ ⟨i, rfl⟩
    change (q * w * q⁻¹) • b i = b i
    rw [mul_smul, mul_smul, ← hq i, inv_smul_smul, haR w hw i]
  have hQSPcard : Nat.card QSP = Nat.card SP :=
    Nat.card_congr (SP.equivMapOfInjective (MulAut.conj q).toMonoidHom
      (MulAut.conj q).injective).toEquiv.symm
  have hSPcard : Nat.card SP = Nat.card S :=
    Nat.card_congr ((S : Subgroup H).equivMapOfInjective
      (N.subtype.comp H.subtype) (N.subtype_injective.comp H.subtype_injective)).toEquiv.symm
  let SU : Subgroup Ht := SP.subgroupOf Ht
  let TU : Subgroup Ht := QSP.subgroupOf Ht
  have hSUcard : Nat.card SU = Nat.card S :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSPleHt).toEquiv).trans hSPcard
  have hTUcard : Nat.card TU = Nat.card S :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQSPleHt).toEquiv).trans
      (hQSPcard.trans hSPcard)
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hSUisP : IsPGroup p SU := IsPGroup.of_card (hSUcard.trans hn)
  have hTUisP : IsPGroup p TU := IsPGroup.of_card (hTUcard.trans hn)
  obtain ⟨U, hSUleU⟩ := hSUisP.exists_le_sylow
  obtain ⟨T, hTUleT⟩ := hTUisP.exists_le_sylow
  have hUcard : Nat.card U = Nat.card S := by
    have hUdvd : Nat.card U ∣ Nat.card H := by
      rw [← hH4card]
      exact U.toSubgroup.card_subgroup_dvd_card.trans (Subgroup.card_dvd_of_le hHt4)
    obtain ⟨m, hm⟩ := U.isPGroup'.exists_card_eq
    have hdvd : Nat.card U ∣ Nat.card S := by
      rw [hm] at hUdvd ⊢
      exact S.pow_dvd_card_of_pow_dvd_card hUdvd
    apply Nat.le_antisymm (Nat.le_of_dvd (Nat.card_pos (α := S)) hdvd)
    rw [← hSUcard]
    exact Nat.le_of_dvd (Nat.card_pos (α := U)) (Subgroup.card_dvd_of_le hSUleU)
  have hTcard : Nat.card T = Nat.card S :=
    (Nat.card_congr (Sylow.equiv T U).toEquiv).trans hUcard
  have hSUEq : SU = (U : Subgroup Ht) := by
    apply Subgroup.eq_of_le_of_card_ge hSUleU
    rw [hSUcard, hUcard]
  have hTUEq : TU = (T : Subgroup Ht) := by
    apply Subgroup.eq_of_le_of_card_ge hTUleT
    rw [hTUcard, hTcard]
  obtain ⟨k, hk⟩ := exists_smul_eq Ht T U
  have hkSub : TU.map (MulAut.conj k).toMonoidHom = SU := by
    rw [hTUEq, hSUEq]
    exact congrArg Sylow.toSubgroup hk
  let kG : G := k
  have hkQSP :
      QSP.map (MulAut.conj kG).toMonoidHom = SP := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ :=
        Subgroup.mem_map.mp hy
      let zHt : Ht := ⟨z, hQSPleHt hz⟩
      have hzTU : zHt ∈ TU := hz
      have hkzSU :
          MulAut.conj k zHt ∈ SU := by
        rw [← hkSub]
        exact
          Subgroup.mem_map_of_mem
            (MulAut.conj k).toMonoidHom hzTU
      change
        (MulAut.conj kG z : G) ∈ SP
      exact hkzSU
    · calc
        Nat.card SP = Nat.card QSP :=
          hQSPcard.symm
        _ = Nat.card
            (QSP.map
              (MulAut.conj kG).toMonoidHom) :=
          Nat.card_congr
            (QSP.equivMapOfInjective
              (MulAut.conj kG).toMonoidHom
              (MulAut.conj kG).injective).toEquiv
        _ ≤ Nat.card
            (QSP.map
              (MulAut.conj kG).toMonoidHom) :=
          le_rfl
  let cG : G := kG * q
  have hcMap :
      SP.map (MulAut.conj cG).toMonoidHom = SP := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ :=
        Subgroup.mem_map.mp hy
      have hqz :
          MulAut.conj q z ∈ QSP :=
        Subgroup.mem_map_of_mem
          (MulAut.conj q).toMonoidHom hz
      have hkqz :
          MulAut.conj kG (MulAut.conj q z) ∈ SP := by
        rw [← hkQSP]
        exact
          Subgroup.mem_map_of_mem
            (MulAut.conj kG).toMonoidHom hqz
      have heq :
          MulAut.conj cG z =
            MulAut.conj kG (MulAut.conj q z) := by
        dsimp only [cG]
        simp only [MulAut.conj_apply]
        group
      change MulAut.conj cG z ∈ SP
      rw [heq]
      exact hkqz
    · calc
        Nat.card SP = Nat.card
            (SP.map
              (MulAut.conj cG).toMonoidHom) :=
          Nat.card_congr
            (SP.equivMapOfInjective
              (MulAut.conj cG).toMonoidHom
              (MulAut.conj cG).injective).toEquiv
        _ ≤ Nat.card
            (SP.map
              (MulAut.conj cG).toMonoidHom) :=
          le_rfl
  have hcNormalizer :
      cG ∈ Subgroup.normalizer SP :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      hcMap
  refine ⟨cG, hcNormalizer, ?_⟩
  intro i
  calc
    cG • a i = kG • (q • a i) := by simp only [cG, mul_smul]
    _ = kG • b i := by rw [hq i]
    _ = b i := (mem_normalFixerImage_iff G X N t kG).mp k.property |>.2 (b i) ⟨i, rfl⟩

@[expose] abbrev normalSylowNormalizer
    (G X : Type*) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) : Subgroup G :=
  Subgroup.normalizer (normalSylowImage G X N s S)

@[expose] abbrev normalSylowInNormalizer
    (G X : Type*) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) :
    Subgroup (normalSylowNormalizer G X N s S) :=
  (normalSylowImage G X N s S).subgroupOf (normalSylowNormalizer G X N s S)

@[expose] abbrev normalSylowFixedPoints
    (G X : Type*) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) :=
  MulAction.fixedPoints (normalSylowInNormalizer G X N s S) X

end FiveTransitive.NormalSylowFixedFive

end CFSG
