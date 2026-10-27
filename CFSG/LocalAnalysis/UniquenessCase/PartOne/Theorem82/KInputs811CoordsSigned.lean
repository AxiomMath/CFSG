module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsLift
import CFSG.GroupTheory.CoprimeQuotientNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open CFSG.GroupTheory

namespace IsSignedCoords

variable {Y : Type} [Group Y] {A : Subgroup Y} {c : Multiplicative (Fin 3 → ZMod 3) →* Y}

theorem card_eq (h : IsSignedCoords A c) : Nat.card A = 27 := by
  rw [← h.2.1, ← Nat.card_congr (MonoidHom.ofInjective h.1).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem isElemAbelian (h : IsSignedCoords A c) : IsElemAbelian 3 A := by
  obtain ⟨-, rfl, -, -⟩ := h
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

theorem map_mulEquiv {Y' : Type} [Group Y'] (h : IsSignedCoords A c) (e : Y ≃* Y') :
    IsSignedCoords (A.map e.toMonoidHom) (e.toMonoidHom.comp c) := by
  obtain ⟨hinj, hrange, h3, h4⟩ := h
  refine ⟨e.injective.comp hinj, by rw [MonoidHom.range_comp, hrange], ?_, ?_⟩
  · intro n' hn'
    rw [← Subgroup.map_equiv_normalizer_eq A e] at hn'
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hn'
    obtain ⟨σ, ε, hε, hσ⟩ := h3 n hn
    exact ⟨σ, ε, hε, fun v => by simpa using congrArg e (hσ v)⟩
  · intro σ ε hε
    obtain ⟨n, hn⟩ := h4 σ ε hε
    exact ⟨e n, fun v => by simpa using congrArg e (hn v)⟩

theorem conj (h : IsSignedCoords A c) (g : Y) :
    IsSignedCoords (A.map (MulAut.conj g).toMonoidHom) ((MulAut.conj g).toMonoidHom.comp c) :=
  h.map_mulEquiv (MulAut.conj g)

theorem map_quotient [Finite Y] (h : IsSignedCoords A c) (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) :
    IsSignedCoords (A.map (QuotientGroup.mk' N)) ((QuotientGroup.mk' N).comp c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 A := h.isElemAbelian.isPGroup
  obtain ⟨hinj, hrange, h3, h4⟩ := h
  refine ⟨?_, by rw [MonoidHom.range_comp, hrange], ?_, ?_⟩
  · intro v w hvw
    exact hinj (Coords.eq_of_mk'_eq_of_isPGroup N hN hA (hrange ▸ ⟨v, rfl⟩)
      (hrange ▸ ⟨w, rfl⟩) hvw)
  · intro nb hnb
    rw [← normal_coprime_quotient_normalizer 3 N hN A hA] at hnb
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hnb
    obtain ⟨σ, ε, hε, hσ⟩ := h3 n hn
    exact ⟨σ, ε, hε, fun v => by simpa using congrArg (QuotientGroup.mk' N) (hσ v)⟩
  · intro σ ε hε
    obtain ⟨n, hn⟩ := h4 σ ε hε
    exact ⟨QuotientGroup.mk' N n, fun v => by simpa using congrArg (QuotientGroup.mk' N) (hn v)⟩

theorem of_quotient [Finite Y] (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z)
    (hA : IsPGroup 3 A) {cb : Multiplicative (Fin 3 → ZMod 3) →* Y ⧸ Z}
    (h : IsSignedCoords (A.map (QuotientGroup.mk' Z)) cb) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y,
      IsSignedCoords A c ∧ (QuotientGroup.mk' Z).comp c = cb := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hinj, hrange, h3, h4⟩ := h
  obtain ⟨c, hcA, hcb⟩ := Coords.exists_hom_lift Z hZ hA cb hrange.le
  have hcv : ∀ v, QuotientGroup.mk' Z (c v) = cb v := fun v => DFunLike.congr_fun hcb v
  have hcmem : ∀ v, c v ∈ A := fun v => hcA ⟨v, rfl⟩
  have key : ∀ {a b : Y}, a ∈ A → b ∈ A →
      QuotientGroup.mk' Z a = QuotientGroup.mk' Z b → a = b :=
    fun ha hb hab => Coords.eq_of_mk'_eq_of_isPGroup Z hZ hA ha hb hab
  refine ⟨c, ⟨?_, ?_, ?_, ?_⟩, hcb⟩
  · intro v w hvw
    apply hinj
    rw [← hcv v, ← hcv w, hvw]
  · refine le_antisymm hcA fun a ha => ?_
    have hmem : QuotientGroup.mk' Z a ∈ cb.range := by
      rw [hrange]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, key (hcmem v) ha (by rw [hcv v]; exact hv)⟩
  · intro n hn
    have hn' : QuotientGroup.mk' Z n ∈
        Subgroup.normalizer ((A.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z)) :=
      Subgroup.le_normalizer_map _ (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
    obtain ⟨σ, ε, hε, hσ⟩ := h3 _ hn'
    refine ⟨σ, ε, hε, fun v => key ?_ (hcmem _) ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hcmem v)
    · rw [map_mul, map_mul, map_inv, hcv, hcv, hσ v]
  · intro σ ε hε
    obtain ⟨nb, hnb⟩ := h4 σ ε hε
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

end IsSignedCoords

theorem exists_isSignedCoords_of_conj {Y : Type} [Group Y] {A B : Subgroup Y}
    (hB : ∃ g : Y, B = A.map (MulAut.conj g).toMonoidHom) (hA : ∃ c, IsSignedCoords A c) :
    ∃ c, IsSignedCoords B c := by
  obtain ⟨g, rfl⟩ := hB
  obtain ⟨c, hc⟩ := hA
  exact ⟨_, hc.conj g⟩

namespace IsSignedCoords

theorem exists_of_uniqueElemSylow {P : Type} [Group P] [Finite P] (hP : UniqueElemSylow 3 3 P)
    {A₀ : Subgroup P} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* P} (h₀ : IsSignedCoords A₀ c₀)
    {A : Subgroup P} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* P, IsSignedCoords A c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq hP h₀.isElemAbelian
    (by rw [h₀.card_eq]; norm_num) hA (by rw [h27]; norm_num)
  exact exists_isSignedCoords_of_conj ⟨g, hg⟩ ⟨c₀, h₀⟩

theorem exists_of_forall_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ B : Subgroup Y', IsElemAbelian 3 B → Nat.card B = 27 →
      ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y', IsSignedCoords B c)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c := by
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
      ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y ⧸ Z, IsSignedCoords B c)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨cb, hcb⟩ := h (A.map (QuotientGroup.mk' Z)) (hA.map _)
    (by rw [Coords.card_map_mk' Z hZ hA.isPGroup, h27])
  obtain ⟨c, hc, -⟩ := IsSignedCoords.of_quotient Z hZ hA.isPGroup hcb
  exact ⟨c, hc⟩

theorem exists_of_model {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c :=
  exists_of_forall_quotient Z hZ
    (fun _ hB hB27 => exists_of_forall_mulEquiv e
      (fun _ hB' hB27' => exists_of_uniqueElemSylow hU (h₀.map_quotient N hN) hB' hB27')
      hB hB27) hA h27

end IsSignedCoords

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
