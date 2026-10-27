module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsLift
import CFSG.GroupTheory.CoprimeQuotientNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open CFSG.GroupTheory

namespace IsSumZeroCoords

variable {Y : Type} [Group Y] {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y}

theorem card_ker (h : IsSumZeroCoords A c) : Nat.card c.ker = 3 := by
  let e : c.ker ≃ ZMod 3 :=
    { toFun := fun v => Multiplicative.toAdd v.1 0
      invFun := fun t => ⟨Multiplicative.ofAdd (fun _ => t), by
        rw [MonoidHom.mem_ker]
        exact (h.2.1 _).mpr ⟨t, rfl⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext i
        obtain ⟨t, ht⟩ := (h.2.1 v.1).mp (MonoidHom.mem_ker.mp v.2)
        show Multiplicative.toAdd v.1 0 = Multiplicative.toAdd v.1 i
        rw [ht]
      right_inv := fun t => rfl }
  rw [Nat.card_congr e, Nat.card_zmod]

theorem card_eq (h : IsSumZeroCoords A c) : Nat.card A = 27 := by
  have hk := Subgroup.card_ker_mul_card_range c
  have h81 : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [h.card_ker, h81] at hk
  have h27 : Nat.card c.range = 27 := by omega
  rwa [h.1] at h27

theorem isElemAbelian (h : IsSumZeroCoords A c) : IsElemAbelian 3 A := by
  obtain ⟨rfl, -, -, -⟩ := h
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu⟩ := a.2
    obtain ⟨w, hw⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hw, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨u, rfl⟩ := hx
    have hu : u ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp [toAdd_pow]
      decide +revert
    rw [← map_pow, hu, map_one]

theorem map_mulEquiv {Y' : Type} [Group Y'] (h : IsSumZeroCoords A c) (e : Y ≃* Y') :
    IsSumZeroCoords (A.map e.toMonoidHom) (e.toMonoidHom.comp c) := by
  obtain ⟨hrange, hker, h3, h4⟩ := h
  refine ⟨by rw [MonoidHom.range_comp, hrange], fun v => ?_, ?_, ?_⟩
  · have hv : e (c v) = 1 ↔ c v = 1 := by simp
    exact hv.trans (hker v)
  · intro n' hn'
    rw [← Subgroup.map_equiv_normalizer_eq A e] at hn'
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hn'
    obtain ⟨σ, hσ⟩ := h3 n hn
    exact ⟨σ, fun v => by simpa using congrArg e (hσ v)⟩
  · intro σ
    obtain ⟨n, hn⟩ := h4 σ
    exact ⟨e n, fun v => by simpa using congrArg e (hn v)⟩

theorem conj (h : IsSumZeroCoords A c) (g : Y) :
    IsSumZeroCoords (A.map (MulAut.conj g).toMonoidHom) ((MulAut.conj g).toMonoidHom.comp c) :=
  h.map_mulEquiv (MulAut.conj g)

theorem map_quotient [Finite Y] (h : IsSumZeroCoords A c) (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) :
    IsSumZeroCoords (A.map (QuotientGroup.mk' N)) ((QuotientGroup.mk' N).comp c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 A := h.isElemAbelian.isPGroup
  obtain ⟨hrange, hker, h3, h4⟩ := h
  have hcmem : ∀ v, c v ∈ A := fun v => hrange.le ⟨v, rfl⟩
  refine ⟨by rw [MonoidHom.range_comp, hrange], fun v => ?_, ?_, ?_⟩
  · rw [← hker v]
    constructor
    · intro hv
      exact Coords.eq_of_mk'_eq_of_isPGroup N hN hA (hcmem v) A.one_mem
        (by rw [map_one]; exact hv)
    · intro hv
      show QuotientGroup.mk' N (c v) = 1
      rw [hv, map_one]
  · intro nb hnb
    rw [← normal_coprime_quotient_normalizer 3 N hN A hA] at hnb
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hnb
    obtain ⟨σ, hσ⟩ := h3 n hn
    exact ⟨σ, fun v => by simpa using congrArg (QuotientGroup.mk' N) (hσ v)⟩
  · intro σ
    obtain ⟨n, hn⟩ := h4 σ
    exact ⟨QuotientGroup.mk' N n, fun v => by simpa using congrArg (QuotientGroup.mk' N) (hn v)⟩

theorem of_quotient [Finite Y] (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z)
    (hA : IsPGroup 3 A) {cb : Multiplicative (Fin 4 → ZMod 3) →* Y ⧸ Z}
    (h : IsSumZeroCoords (A.map (QuotientGroup.mk' Z)) cb) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y,
      IsSumZeroCoords A c ∧ (QuotientGroup.mk' Z).comp c = cb := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hrange, hker, h3, h4⟩ := h
  obtain ⟨c, hcA, hcb⟩ := Coords.exists_hom_lift Z hZ hA cb hrange.le
  have hcv : ∀ v, QuotientGroup.mk' Z (c v) = cb v := fun v => DFunLike.congr_fun hcb v
  have hcmem : ∀ v, c v ∈ A := fun v => hcA ⟨v, rfl⟩
  have key : ∀ {a b : Y}, a ∈ A → b ∈ A →
      QuotientGroup.mk' Z a = QuotientGroup.mk' Z b → a = b :=
    fun ha hb hab => Coords.eq_of_mk'_eq_of_isPGroup Z hZ hA ha hb hab
  refine ⟨c, ⟨?_, fun v => ?_, ?_, ?_⟩, hcb⟩
  · refine le_antisymm hcA fun a ha => ?_
    have hmem : QuotientGroup.mk' Z a ∈ cb.range := by
      rw [hrange]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, key (hcmem v) ha (by rw [hcv v]; exact hv)⟩
  · rw [← hker v, ← hcv v]
    constructor
    · intro hv
      rw [hv, map_one]
    · intro hv
      exact key (hcmem v) A.one_mem (by rw [hv, map_one])
  · intro n hn
    have hn' : QuotientGroup.mk' Z n ∈
        Subgroup.normalizer ((A.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z)) :=
      Subgroup.le_normalizer_map _ (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
    obtain ⟨σ, hσ⟩ := h3 _ hn'
    refine ⟨σ, fun v => key ?_ (hcmem _) ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hcmem v)
    · rw [map_mul, map_mul, map_inv, hcv, hcv, hσ v]
  · intro σ
    obtain ⟨nb, hnb⟩ := h4 σ
    have hnb_norm : nb ∈
        Subgroup.normalizer ((A.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z)) := by
      apply Coords.mem_normalizer_of_conj_mem
      intro a ha
      rw [← hrange] at ha ⊢
      obtain ⟨v, rfl⟩ := ha
      rw [hnb v]
      exact ⟨_, rfl⟩
    rw [← normal_coprime_quotient_normalizer 3 Z hZ A hA] at hnb_norm
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hnb_norm
    refine ⟨n, fun v => key ?_ (hcmem _) ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hcmem v)
    · rw [map_mul, map_mul, map_inv, hcv, hcv]
      exact hnb v

end IsSumZeroCoords

theorem exists_isSumZeroCoords_of_conj {Y : Type} [Group Y] {A B : Subgroup Y}
    (hB : ∃ g : Y, B = A.map (MulAut.conj g).toMonoidHom) (hA : ∃ c, IsSumZeroCoords A c) :
    ∃ c, IsSumZeroCoords B c := by
  obtain ⟨g, rfl⟩ := hB
  obtain ⟨c, hc⟩ := hA
  exact ⟨_, hc.conj g⟩

namespace IsSumZeroCoords

theorem exists_of_uniqueElemSylow {P : Type} [Group P] [Finite P] (hP : UniqueElemSylow 3 3 P)
    {A₀ : Subgroup P} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* P} (h₀ : IsSumZeroCoords A₀ c₀)
    {A : Subgroup P} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* P, IsSumZeroCoords A c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq hP h₀.isElemAbelian
    (by rw [h₀.card_eq]; norm_num) hA (by rw [h27]; norm_num)
  exact exists_isSumZeroCoords_of_conj ⟨g, hg⟩ ⟨c₀, h₀⟩

theorem exists_of_forall_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ B : Subgroup Y', IsElemAbelian 3 B → Nat.card B = 27 →
      ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y', IsSumZeroCoords B c)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c := by
  obtain ⟨c', hc'⟩ := h (A.map e.toMonoidHom) (hA.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, h27])
  have h' := hc'.map_mulEquiv e.symm
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Y := by
    ext y
    simp
  rw [Subgroup.map_map, hid, Subgroup.map_id] at h'
  exact ⟨_, h'⟩

theorem exists_of_forall_quotient {Y : Type} [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal]
    (hZ : ¬ 3 ∣ Nat.card Z)
    (h : ∀ B : Subgroup (Y ⧸ Z), IsElemAbelian 3 B → Nat.card B = 27 →
      ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y ⧸ Z, IsSumZeroCoords B c)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨cb, hcb⟩ := h (A.map (QuotientGroup.mk' Z)) (hA.map _)
    (by rw [Coords.card_map_mk' Z hZ hA.isPGroup, h27])
  obtain ⟨c, hc, -⟩ := of_quotient Z hZ hA.isPGroup hcb
  exact ⟨c, hc⟩

theorem exists_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* H} (h₀ : IsSumZeroCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c :=
  exists_of_forall_quotient Z hZ
    (fun _ hB hB27 => exists_of_forall_mulEquiv e
      (fun _ hB' hB27' => exists_of_uniqueElemSylow hU (h₀.map_quotient N hN) hB' hB27')
      hB hB27) hA h27

end IsSumZeroCoords

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
