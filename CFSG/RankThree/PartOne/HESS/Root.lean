module

public import CFSG.RankThree.PartOne.KFOUT3.Std

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG.RankThree.PartOne.KFOUT3 (SL3 rt permSL)
open scoped commutatorElement

section Mat

variable {K : Type} [Field K]

@[expose] def rtHom {i j : Fin 3} (h : i ≠ j) : Multiplicative K →* SL3 K where
  toFun c := rt h (Multiplicative.toAdd c)
  map_one' := KFOUT3.rt_zero h
  map_mul' _ _ := KFOUT3.rt_add h _ _

@[expose] def rootGrp {i j : Fin 3} (h : i ≠ j) : Subgroup (SL3 K) := (rtHom h).range

theorem mem_rootGrp_iff {i j : Fin 3} (h : i ≠ j) {x : SL3 K} :
    x ∈ rootGrp (K := K) h ↔ ∃ s : K, x = rt h s := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨Multiplicative.ofAdd s, rfl⟩

theorem rt_mem_rootGrp {i j : Fin 3} (h : i ≠ j) (s : K) : rt h s ∈ rootGrp (K := K) h :=
  (mem_rootGrp_iff h).2 ⟨s, rfl⟩

theorem rt_injective {i j : Fin 3} (h : i ≠ j) : Function.Injective (fun s : K => rt h s) := by
  intro a b hab
  have := congrArg (fun z : SL3 K => KFOUT3.ent z i j) hab
  simpa [KFOUT3.rt_apply_self] using this

theorem card_rootGrp {i j : Fin 3} (h : i ≠ j) : Nat.card (rootGrp (K := K) h) = Nat.card K := by
  have hinj : Function.Injective (rtHom (K := K) h) := fun a b hab => by
    have := rt_injective (K := K) h (by simpa [rtHom] using hab)
    exact Multiplicative.toAdd.injective this
  rw [rootGrp, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem commutator_rootGrp_chain {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅rootGrp (K := K) hij, rootGrp (K := K) hjk⁆ = rootGrp (K := K) hik := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff hij).1 ha
    obtain ⟨s', rfl⟩ := (mem_rootGrp_iff hjk).1 hb
    rw [show ⁅rt hij s, rt hjk s'⁆ = rt hik (s * s') from
      Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik s s']
    exact rt_mem_rootGrp hik _
  · intro x hx
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff hik).1 hx
    have h1 : ⁅rt hij s, rt hjk (1 : K)⁆ = rt hik (s * 1) :=
      Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik s 1
    rw [mul_one] at h1
    rw [← h1]
    exact Subgroup.commutator_mem_commutator (rt_mem_rootGrp hij s) (rt_mem_rootGrp hjk 1)

theorem rootGrp_commute {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) :
    ∀ a ∈ rootGrp (K := K) hij, ∀ b ∈ rootGrp (K := K) hkl, a * b = b * a := by
  intro a ha b hb
  obtain ⟨s, rfl⟩ := (mem_rootGrp_iff hij).1 ha
  obtain ⟨s', rfl⟩ := (mem_rootGrp_iff hkl).1 hb
  exact (KFOUT3.commute_rt hij hkl hjk hli s s').eq

theorem map_conj_permSL_rootGrp [CharP K 2] (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (h : i ≠ j) :
    (rootGrp (K := K) h).map (MulAut.conj (permSL σ)).toMonoidHom =
      rootGrp (K := K) (σ.injective.ne h) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff h).1 hy
    have := KFOUT3.permSL_conj_rt σ h s
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this]
    exact rt_mem_rootGrp _ _
  · intro hx
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff _).1 hx
    exact ⟨rt h s, rt_mem_rootGrp h s, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact KFOUT3.permSL_conj_rt σ h s⟩

theorem rootGrp_injective {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (h : rootGrp (K := K) hij = rootGrp (K := K) hkl) : i = k ∧ j = l := by
  have h1 : rt hij (1 : K) ∈ rootGrp (K := K) hkl := h ▸ rt_mem_rootGrp hij 1
  obtain ⟨s, hs⟩ := (mem_rootGrp_iff hkl).1 h1
  have h2 := congrArg (fun z : SL3 K => KFOUT3.ent z i j) hs
  simp only [KFOUT3.rt_apply_self, KFOUT3.rt_apply] at h2
  by_contra hne
  have h3 : ¬ (k = i ∧ l = j) := fun ⟨e1, e2⟩ => hne ⟨e1.symm, e2.symm⟩
  simp [hij, h3] at h2

end Mat

end CFSG.RankThree.PartOne.HESS
