module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParS
public import CFSG.Quasithin.H13.A7BlkAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H13.A7Blk

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_parab_of_alt (h : ThreeNat A L T) {n : ℕ} (hn : 7 ≤ n) (halt : UC22.IsAlt ↥L n)
    {a : ℕ} (hM : ∀ X : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 ↥X →
      T3ParabIn (alternatingGroup (Fin n)) X a) :
    T3ParabIn L T a := by
  obtain ⟨e⟩ := halt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  have hT : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := le_trans h.sylow.le h.normal
  let σ : ↥T →* Equiv.Perm (Fin n) :=
    (permAutEquiv (n := n) hn5 hn6).symm.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp
        (L.normalizerMonoidHom.comp (Subgroup.inclusion hT)))
  let X : Subgroup (Equiv.Perm (Fin n)) := σ.range
  have hX : IsPGroup 2 ↥X :=
    h.sylow.isPGroup.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  obtain ⟨P₀, hP₀N, hP₀norm, hP₀inf, hP₀card, hP₀exp⟩ := hM X hX
  let Pₗ : Subgroup ↥L :=
    (P₀.subgroupOf (alternatingGroup (Fin n))).map e.symm.toMonoidHom
  let P : Subgroup (MulAut W) := Pₗ.map L.subtype
  have hσ_def : ∀ t : ↥T,
      permAutEquiv (n := n) hn5 hn6 (σ t) =
        (MulAut.congr e) (L.normalizerMonoidHom (Subgroup.inclusion hT t)) :=
    fun t => MulEquiv.apply_symm_apply _ _
  have hσ_spec : ∀ (t : ↥T) (l : ↥L),
      (σ t : Equiv.Perm (Fin n)) * (e l : Equiv.Perm (Fin n)) * (σ t)⁻¹ =
        (e ⟨(t : MulAut W) * (l : MulAut W) * (t : MulAut W)⁻¹,
          ((Subgroup.mem_normalizer_iff.1 (hT t.2))
            (l : MulAut W)).1 l.2⟩ : Equiv.Perm (Fin n)) := by
    intro t l
    rw [← coe_permAutEquiv_apply hn5 hn6 (σ t) (e l)]
    congr 1
    rw [hσ_def t, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
  have hmemP : ∀ p₀ : ↥(alternatingGroup (Fin n)),
      (p₀ : Equiv.Perm (Fin n)) ∈ P₀ → ((e.symm p₀ : ↥L) : MulAut W) ∈ P := by
    intro p₀ hp
    exact Subgroup.mem_map_of_mem L.subtype
      (Subgroup.mem_map_of_mem e.symm.toMonoidHom (Subgroup.mem_subgroupOf.mpr hp))
  have huniq : ∀ t : ↥(T ⊓ L),
      (σ ⟨(t : MulAut W), t.2.1⟩ : Equiv.Perm (Fin n)) =
        (e ⟨(t : MulAut W), t.2.2⟩ : Equiv.Perm (Fin n)) := by
    intro t
    apply (permAutEquiv (n := n) hn5 hn6).injective
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hσ_def ⟨(t : MulAut W), t.2.1⟩, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [coe_permAutEquiv_apply hn5 hn6]
    have hc : L.normalizerMonoidHom
        (Subgroup.inclusion hT ⟨(t : MulAut W), t.2.1⟩) (e.symm a) =
        ⟨((t : MulAut W) * ((e.symm a : ↥L) : MulAut W) * (t : MulAut W)⁻¹),
          ((Subgroup.mem_normalizer_iff.1 (hT t.2.1))
            ((e.symm a : ↥L) : MulAut W)).1 (e.symm a).2⟩ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    have hx' : (⟨(t : MulAut W) * ((e.symm a : ↥L) : MulAut W) * (t : MulAut W)⁻¹,
        ((Subgroup.mem_normalizer_iff.1 (hT t.2.1))
          ((e.symm a : ↥L) : MulAut W)).1 (e.symm a).2⟩ : ↥L) =
        ⟨(t : MulAut W), t.2.2⟩ * (e.symm a) * ⟨(t : MulAut W), t.2.2⟩⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hc, hx', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨l, -, rfl⟩
    exact l.2
  · intro t ht x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p₀, hp₀, hlp⟩ := Subgroup.mem_map.mp hl
    have hp₀' : (p₀ : Equiv.Perm (Fin n)) ∈ P₀ := Subgroup.mem_subgroupOf.mp hp₀
    let tT : ↥T := ⟨t, ht⟩
    have hnorm : (σ tT : Equiv.Perm (Fin n)) * (p₀ : Equiv.Perm (Fin n)) *
        (σ tT)⁻¹ ∈ P₀ :=
      hP₀norm (σ tT) ⟨tT, rfl⟩ p₀ hp₀'
    have hspec := hσ_spec tT l
    have hel : (e l : Equiv.Perm (Fin n)) = (p₀ : Equiv.Perm (Fin n)) := by
      rw [← hlp]
      exact congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Equiv.Perm (Fin n)))
        (e.apply_symm_apply p₀)
    rw [hel] at hspec
    have hg : (e ⟨t * (l : MulAut W) * t⁻¹,
        ((Subgroup.mem_normalizer_iff.1 (hT ht)) (l : MulAut W)).1 l.2⟩ :
        ↥(alternatingGroup (Fin n))) ∈ P₀.subgroupOf (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_subgroupOf]
      rw [← hspec]
      exact hnorm
    have hg' : (e ⟨t * (l : MulAut W) * t⁻¹,
        ((Subgroup.mem_normalizer_iff.1 (hT ht)) (l : MulAut W)).1 l.2⟩ :
        Equiv.Perm (Fin n)) ∈ P₀ := Subgroup.mem_subgroupOf.mp hg
    have hxeq : ((e.symm (e ⟨t * (l : MulAut W) * t⁻¹,
        ((Subgroup.mem_normalizer_iff.1 (hT ht)) (l : MulAut W)).1 l.2⟩) : ↥L) :
        MulAut W) = t * (l : MulAut W) * t⁻¹ := by
      simp
    change t * (l : MulAut W) * t⁻¹ ∈ P
    rw [← hxeq]
    exact hmemP _ hg'
  · rintro x ⟨hxT, hxL⟩
    let xT : ↥T := ⟨x, hxT⟩
    let xL : ↥L := ⟨x, hxL⟩
    have h1 : (σ xT : Equiv.Perm (Fin n)) = (e xL : Equiv.Perm (Fin n)) := by
      simpa [xT, xL] using huniq ⟨x, hxT, hxL⟩
    have hxX : (σ xT : Equiv.Perm (Fin n)) ∈ X := ⟨xT, rfl⟩
    have hxP0 : (e xL : Equiv.Perm (Fin n)) ∈ P₀ :=
      hP₀inf ⟨by rw [← h1]; exact hxX, (e xL).2⟩
    have := hmemP (e xL) hxP0
    simpa [xL] using this
  · have h1 : Nat.card ↥P = Nat.card ↥Pₗ := Subgroup.card_map_of_injective L.subtype_injective
    have h2 : Nat.card ↥Pₗ = Nat.card ↥(P₀.subgroupOf (alternatingGroup (Fin n))) :=
      Subgroup.card_map_of_injective e.symm.injective
    have h3 : Nat.card ↥(P₀.subgroupOf (alternatingGroup (Fin n))) = Nat.card ↥P₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀N).toEquiv
    have h4 : Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    rw [h1, h2, h3, hP₀card, ← h4]
  · intro p hp m hm
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨p₀, hp₀, hlp⟩ := Subgroup.mem_map.mp hl
    have hp₀' : (p₀ : Equiv.Perm (Fin n)) ∈ P₀ := Subgroup.mem_subgroupOf.mp hp₀
    have hlm : l ^ 3 ^ m = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hm
    have hel' : e l = p₀ := by
      rw [← hlp]
      exact e.apply_symm_apply p₀
    have hp₀m : p₀ ^ 3 ^ m = 1 := by
      rw [← hel', ← map_pow, hlm, map_one]
    have hp₀m' : (p₀ : Equiv.Perm (Fin n)) ^ 3 ^ m = 1 := by
      simpa [Subgroup.coe_pow] using
        congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Equiv.Perm (Fin n))) hp₀m
    have hp₀3 : (p₀ : Equiv.Perm (Fin n)) ^ 3 = 1 :=
      hP₀exp (p₀ : Equiv.Perm (Fin n)) hp₀' m hp₀m'
    have hl3 : l ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, map_one, hel']
      exact Subtype.ext (by simpa using hp₀3)
    simpa [Subgroup.coe_pow] using congrArg (L.subtype) hl3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
