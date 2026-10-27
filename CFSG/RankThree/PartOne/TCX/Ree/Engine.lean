module

public import CFSG.RankThree.PartOne.KLR.Embedding
public import CFSG.RankThree.PartOne.KLCE.EngineG
public import CFSG.RankThree.PartOne.TCX.LayerEngine

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.TCX.F4
open CFSG.RankThree.PartOne.TCX
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Abstract

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

@[expose] def Rg (ι : C →* ModGL τ L) (g₀ : ModGL τ L) : Subgroup (ModGL τ L) :=
  ι.range.comap (MulAut.conj g₀).toMonoidHom

theorem mem_Rg {ι : C →* ModGL τ L} {g₀ u : ModGL τ L} :
    u ∈ Rg ι g₀ ↔ g₀ * u * g₀⁻¹ ∈ ι.range := by
  simp [Rg, MulAut.conj_apply]

theorem psiG_mem_Rg (ι : C →* ModGL τ L) (g₀ : ModGL τ L) (c y : C) :
    psiG ι g₀ c y ∈ Rg ι g₀ := by
  rw [mem_Rg, psiG_apply]
  refine ⟨c * y * c⁻¹, ?_⟩
  group

@[expose] def layerQ (ι : C →* ModGL τ L) (g₀ : ModGL τ L) (c : C)
    (S : Set (Fin τ.rank → ℤ)) : Subgroup C :=
  (rootSpan τ L S ⊓ Rg ι g₀).comap (psiG ι g₀ c)

theorem mem_layerQ {ι : C →* ModGL τ L} {g₀ : ModGL τ L} {c : C} {S : Set (Fin τ.rank → ℤ)}
    {y : C} :
    y ∈ layerQ ι g₀ c S ↔ psiG ι g₀ c y ∈ rootSpan τ L S ∧ psiG ι g₀ c y ∈ Rg ι g₀ := by
  simp [layerQ, Subgroup.mem_inf]

end Abstract

section Commutator

variable {τ : Tag} {L : Type} [Field L]

theorem comm_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    {g₁ g₂ : ModGL τ L} (h₁ : g₁ ∈ torusGroup τ L ⊔ rootSpan τ L S)
    (h₂ : g₂ ∈ torusGroup τ L ⊔ rootSpan τ L S) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ rootSpan τ L S := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L) (rootSpan τ L S)
    (KE.torusGroup_le_normalizer_rootSpan hS)
  have h₁' : g₁ ∈ ((torusGroup τ L ⊔ rootSpan τ L S : Subgroup (ModGL τ L)) : Set (ModGL τ L)) :=
    h₁
  have h₂' : g₂ ∈ ((torusGroup τ L ⊔ rootSpan τ L S : Subgroup (ModGL τ L)) : Set (ModGL τ L)) :=
    h₂
  rw [e] at h₁' h₂'
  obtain ⟨t₁, ht₁, q₁, hq₁, rfl⟩ := Set.mem_mul.1 h₁'
  obtain ⟨t₂, ht₂, q₂, hq₂, rfl⟩ := Set.mem_mul.1 h₂'
  have hn : ∀ t ∈ torusGroup τ L, ∀ q ∈ rootSpan τ L S, t * q * t⁻¹ ∈ rootSpan τ L S :=
    fun t ht q hq =>
      (Subgroup.mem_normalizer_iff.1 (KE.torusGroup_le_normalizer_rootSpan hS ht) q).1 hq
  have hn' : ∀ t ∈ torusGroup τ L, ∀ q ∈ rootSpan τ L S, t⁻¹ * q * t ∈ rootSpan τ L S :=
    fun t ht q hq => by
      have := hn t⁻¹ (inv_mem ht) q hq
      simpa using this
  have hc : t₁ * t₂ = t₂ * t₁ := KE.torusGroup_comm ht₁ ht₂
  set a₁ := t₂⁻¹ * q₁ * t₂ with ha₁
  set a₂ := t₁⁻¹ * q₂ * t₁ with ha₂
  have h1 : t₁ * q₁ * (t₂ * q₂) = (t₁ * t₂) * (a₁ * q₂) := by rw [ha₁]; group
  have h2 : t₂ * q₂ * (t₁ * q₁) = (t₁ * t₂) * (a₂ * q₁) := by rw [hc, ha₂]; group
  have e1 : t₁ * q₁ * (t₂ * q₂) * (t₁ * q₁)⁻¹ * (t₂ * q₂)⁻¹ =
      (t₁ * t₂) * (a₁ * q₂) * (a₂ * q₁)⁻¹ * (t₁ * t₂)⁻¹ := by
    have : t₁ * q₁ * (t₂ * q₂) * (t₁ * q₁)⁻¹ * (t₂ * q₂)⁻¹ =
        (t₁ * q₁ * (t₂ * q₂)) * (t₂ * q₂ * (t₁ * q₁))⁻¹ := by group
    rw [this, h1, h2]
    group
  rw [e1]
  have hT : t₁ * t₂ ∈ torusGroup τ L := mul_mem ht₁ ht₂
  have ha₁Q : a₁ ∈ rootSpan τ L S := hn' t₂ ht₂ q₁ hq₁
  have ha₂Q : a₂ ∈ rootSpan τ L S := hn' t₁ ht₁ q₂ hq₂
  have hin : a₁ * q₂ * (a₂ * q₁)⁻¹ ∈ rootSpan τ L S :=
    mul_mem (mul_mem ha₁Q hq₂) (inv_mem (mul_mem ha₂Q hq₁))
  have := hn _ hT _ hin
  simpa [mul_assoc] using this

end Commutator

section Structure

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem layerStructure_abs (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1) {p : ℕ} (hp : p.Prime)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (hPq : CFSG.IsQuasisimple ↥(rootSpan τ L S ⊓ Rg ι g₀))
    (hPcent : ∀ q ∈ rootSpan τ L S, (∀ u ∈ rootSpan τ L S ⊓ Rg ι g₀, q * u = u * q) → q = 1)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : g₀⁻¹ * ι (c * x * c⁻¹) * g₀ ∈ torusGroup τ L ⊓
      Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L)))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    rootSpan τ L S ⊓ Rg ι g₀ ≤ (psiG ι g₀ c).range ∧
      IsComponentOf (Subgroup.centralizer ({x} : Set C)) (layerQ ι g₀ c S) ∧
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set C) ⊓
        Subgroup.centralizer ((layerQ ι g₀ c S : Subgroup C) : Set C)) ∧
      ((layerQ ι g₀ c S).subgroupOf (Subgroup.centralizer ({x} : Set C))).Normal ∧
      Odd ((layerQ ι g₀ c S).subgroupOf (Subgroup.centralizer ({x} : Set C))).index := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup (ModGL τ L) := rootSpan τ L S ⊓ Rg ι g₀ with hPdef
  set X : Subgroup C := Subgroup.centralizer ({x} : Set C) with hXdef
  set d : ModGL τ L := g₀⁻¹ * ι (c * x * c⁻¹) * g₀ with hd
  have hψinj : Function.Injective (psiG ι g₀ c) := psiG_injective hι g₀ c
  have hdH : d ∈ torusGroup τ L := (Subgroup.mem_inf.1 hc).1
  have hdQ : d ∈ Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L)) :=
    (Subgroup.mem_inf.1 hc).2
  have hψd : psiG ι g₀ c x = d := psiG_apply ι g₀ c x
  have hψmem : ∀ y : C, psiG ι g₀ c y ∈ adjointGroup τ L := fun y => by
    rw [psiG_apply]
    exact mul_mem (mul_mem (inv_mem hg₀C) (hιC _)) hg₀C
  have hordd : orderOf d = p := by
    rw [← hψd, orderOf_injective (psiG ι g₀ c) hψinj x, hx]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdH
  have hord' : orderOf (rootDiagUnit τ a) = p := by rw [← ha]; exact hordd
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hker : rootCharKernel a ⊆ S := hkerZ a (ha.symm.trans hd)
  have hcomm : ∀ y : C, y ∈ X →
      psiG ι g₀ c y * rootDiagUnit τ a = rootDiagUnit τ a * psiG ι g₀ c y := fun y hy => by
    rw [← ha, ← hψd, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 hy
  have hHQ' : ∀ y : C, y ∈ X → ∃ t ∈ torusGroup τ L, ∃ q ∈ rootSpan τ L S,
      psiG ι g₀ c y = t * q := fun y hy => by
    have := mem_torus_mul_rootSpan_of_commute_of_stab (hstab a hap ha1) hS hSn hker (hψmem y)
      (hcomm y hy)
    obtain ⟨t, ht, q, hq, h⟩ := Set.mem_mul.1 this
    exact ⟨t, ht, q, hq, h.symm⟩
  have hHQ : ∀ y : C, y ∈ X → psiG ι g₀ c y ∈ torusGroup τ L ⊔ rootSpan τ L S := fun y hy => by
    obtain ⟨t, ht, q, hq, h⟩ := hHQ' y hy
    rw [h]
    exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hq)
  have hPψ : P ≤ (psiG ι g₀ c).range := by
    intro u hu
    obtain ⟨huQ, huR⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨y', hy'⟩ := mem_Rg.1 huR
    have hιx' : ι (c * x * c⁻¹) = g₀ * d * g₀⁻¹ := by
      rw [hd]
      group
    have hud : u * d = d * u := Subgroup.mem_centralizer_iff.1 hdQ u huQ
    have hcomm' : y' * (c * x * c⁻¹) = (c * x * c⁻¹) * y' := by
      apply hι
      rw [map_mul ι y' (c * x * c⁻¹), map_mul ι (c * x * c⁻¹) y', hy', hιx']
      calc g₀ * u * g₀⁻¹ * (g₀ * d * g₀⁻¹) = g₀ * (u * d) * g₀⁻¹ := by group
        _ = g₀ * (d * u) * g₀⁻¹ := by rw [hud]
        _ = g₀ * d * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
    have hyX : c⁻¹ * y' * c ∈ X := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc c⁻¹ * y' * c * x = c⁻¹ * (y' * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y') * c := by rw [hcomm']
        _ = x * (c⁻¹ * y' * c) := by group
    refine ⟨c⁻¹ * y' * c, ?_⟩
    rw [psiG_apply, show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group
  have hmap : (layerQ ι g₀ c S).map (psiG ι g₀ c) = P := by
    unfold layerQ
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hPψ]
  have hQX : layerQ ι g₀ c S ≤ X := fun y hy => by
    obtain ⟨hyQ, -⟩ := mem_layerQ.1 hy
    have h2 := Subgroup.mem_centralizer_iff.1 hdQ _ hyQ
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply hψinj
    rw [map_mul, map_mul, hψd]
    exact h2
  have hnormP : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ Rg ι g₀ → ∀ v ∈ P, y * v * y⁻¹ ∈ P := by
    intro y hy hyR v hv
    obtain ⟨hvQ, hvR⟩ := Subgroup.mem_inf.1 hv
    have hnorm : y ∈ Subgroup.normalizer (rootSpan τ L S : Set (ModGL τ L)) :=
      (sup_le (KE.torusGroup_le_normalizer_rootSpan hS) Subgroup.le_normalizer) hy
    have h1 : y * v * y⁻¹ ∈ rootSpan τ L S := (Subgroup.mem_normalizer_iff.1 hnorm v).1 hvQ
    have h2 : y * v * y⁻¹ ∈ Rg ι g₀ := mul_mem (mul_mem hyR hvR) (inv_mem hyR)
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hnormal : ((layerQ ι g₀ c S).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hP : psiG ι g₀ c (n : C) ∈ P := Subgroup.mem_inf.2 (mem_layerQ.1 hn)
    have h := hnormP _ (hHQ (g : C) g.2) (psiG_mem_Rg ι g₀ c _) _ hP
    change (g : C) * (n : C) * (g : C)⁻¹ ∈ layerQ ι g₀ c S
    rw [mem_layerQ, map_mul, map_mul, map_inv]
    exact Subgroup.mem_inf.1 h
  have hodd' : Odd ((layerQ ι g₀ c S).subgroupOf X).index := by
    refine odd_index_of_sq_mem _ (fun g hg => ?_)
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hg2 : psiG ι g₀ c ((g : C) ^ 2) ∈ rootSpan τ L S :=
      (mem_layerQ.1 (by simpa using hg)).1
    rw [map_pow] at hg2
    obtain ⟨t, ht, q, hq, hu⟩ := hHQ' (g : C) g.2
    rw [hu, pow_two] at hg2
    have h1 : t * q * t ∈ rootSpan τ L S := by
      have := mul_mem hg2 (inv_mem hq)
      simpa [mul_assoc] using this
    have hnorm : t ∈ Subgroup.normalizer (rootSpan τ L S : Set (ModGL τ L)) :=
      KE.torusGroup_le_normalizer_rootSpan hS ht
    have h2 : t * q * t⁻¹ ∈ rootSpan τ L S := (Subgroup.mem_normalizer_iff.1 hnorm q).1 hq
    have ht2 : t ^ 2 ∈ rootSpan τ L S := by
      have : t ^ 2 = (t * q * t⁻¹)⁻¹ * (t * q * t) := by rw [pow_two]; group
      rw [this]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨m, hm, htm⟩ := hodd t ht
    obtain ⟨k, hk⟩ := hm
    have e1 : t ^ (2 * k + 1) = 1 := by rw [← hk]; exact htm
    have htQ : t ∈ rootSpan τ L S := by
      have : t = (t ^ 2) ^ (k + 1) := by
        calc t = t ^ (2 * k + 1) * t := by rw [e1, one_mul]
          _ = t ^ (2 * k + 1 + 1) := (pow_succ _ _).symm
          _ = (t ^ 2) ^ (k + 1) := by rw [← pow_mul]; ring_nf
      rw [this]
      exact pow_mem ht2 _
    have huQ : psiG ι g₀ c (g : C) ∈ rootSpan τ L S := by
      rw [hu]
      exact mul_mem htQ hq
    exact mem_layerQ.2 ⟨huQ, psiG_mem_Rg ι g₀ c _⟩
  have hequiv : ↥(layerQ ι g₀ c S) ≃* ↥P :=
    (Subgroup.equivMapOfInjective _ (psiG ι g₀ c) hψinj).trans (MulEquiv.subgroupCongr hmap)
  have hquasi : CFSG.IsQuasisimple ↥(layerQ ι g₀ c S) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv hequiv.symm hPq
  have hsolv : Group.IsSolvable ↥(X ⊓
      Subgroup.centralizer ((layerQ ι g₀ c S : Subgroup C) : Set C)) := by
    have hcP : ∀ y ∈ X ⊓ Subgroup.centralizer ((layerQ ι g₀ c S : Subgroup C) : Set C),
        ∀ u ∈ P, psiG ι g₀ c y * u = u * psiG ι g₀ c y := by
      intro y hy u hu
      obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨w, hw⟩ := hPψ hu
      have hwQ : w ∈ layerQ ι g₀ c S := by
        rw [mem_layerQ, hw]
        exact Subgroup.mem_inf.1 hu
      have h := Subgroup.mem_centralizer_iff.1 hyC w hwQ
      have h2 : psiG ι g₀ c (w * y) = psiG ι g₀ c (y * w) := by rw [h]
      rw [map_mul, map_mul, hw] at h2
      exact h2.symm
    refine Group.isSolvable_of_comm (fun a b => ?_)
    apply Subtype.ext
    apply hψinj
    have hca := hcP a a.2
    have hcb := hcP b b.2
    have hcom := comm_mem_rootSpan hS (hHQ (a : C) (Subgroup.mem_inf.1 a.2).1)
      (hHQ (b : C) (Subgroup.mem_inf.1 b.2).1)
    have h1 := hPcent _ hcom (fun u hu => by
      have e1 : Commute (psiG ι g₀ c (a : C)) u := hca u hu
      have e2 : Commute (psiG ι g₀ c (b : C)) u := hcb u hu
      exact (((e1.mul_left e2).mul_left e1.inv_left).mul_left e2.inv_left).eq)
    change psiG ι g₀ c ((a : C) * b) = psiG ι g₀ c ((b : C) * a)
    rw [map_mul, map_mul]
    have h2 : psiG ι g₀ c (a : C) * psiG ι g₀ c (b : C) *
        (psiG ι g₀ c (b : C) * psiG ι g₀ c (a : C))⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa [mul_assoc] using h1
    exact mul_inv_eq_one.1 h2
  exact ⟨hPψ, ⟨hQX, hquasi, hnormal.isSubnormal⟩, hsolv, hnormal, hodd'⟩

end Structure

section Intertwine

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

theorem psiG_intertwine_R {ι : C →* ModGL τ L} (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (F₀ : MulAut (adjointGroup τ L)) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = Fext F₀ (ι y)) {g₀ n₀ : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Fext F₀ g₀ = g₀ * n₀) {c : C} (hc : α₀ c = c) (y : C) :
    n₀ * Fext F₀ (psiG ι g₀ c y) * n₀⁻¹ = psiG ι g₀ c (α₀ y) := by
  have h1 : α₀ (c * y * c⁻¹) = c * α₀ y * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, hc]
  have e1 : Fext F₀ (g₀⁻¹ * ι (c * y * c⁻¹) * g₀) =
      (Fext F₀ g₀)⁻¹ * Fext F₀ (ι (c * y * c⁻¹)) * Fext F₀ g₀ := by
    rw [Fext_mul F₀ (mul_mem (inv_mem hg₀C) (hιC _)) hg₀C, Fext_mul F₀ (inv_mem hg₀C) (hιC _),
      Fext_inv F₀ hg₀C]
  rw [psiG_apply, psiG_apply, e1, hg₀, ← hα₀, h1, map_mul, map_mul, map_inv]
  group

end Intertwine

section Final

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem singleLayerData_of_engineR (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (F₀ : MulAut (adjointGroup τ L)) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = Fext F₀ (ι y)) {g₀ n₀ : ModGL τ L} (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Fext F₀ g₀ = g₀ * n₀)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1) {p : ℕ} (hp : p.Prime)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (hPq : CFSG.IsQuasisimple ↥(rootSpan τ L S ⊓ Rg ι g₀))
    (hPcent : ∀ q ∈ rootSpan τ L S, (∀ u ∈ rootSpan τ L S ⊓ Rg ι g₀, q * u = u * q) → q = 1)
    {x : C} (hx : orderOf x = p) (c : C) (hcα : α₀ c = c)
    (hc : g₀⁻¹ * ι (c * x * c⁻¹) * g₀ ∈ torusGroup τ L ⊓
      Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L)))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S)
    (hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = rootSpan τ L S ⊓ Rg ι g₀ ∧
      (∀ d, n₀ * Fext F₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hoddi⟩ := layerStructure_abs ι hι hιC g₀ hg₀C hodd hp
    hstab hS hSn hPq hPcent hx c hc hkerZ
  obtain ⟨D, hD, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ := hmodel
  have hPrange' : ρ'.range ≤ (psiG ι g₀ c).range := by
    rw [hρ'range]
    exact hPrange
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push (psiG ι g₀ c)
    (psiG_injective hι g₀ c) ρ' hρ'inj hPrange'
  have hQ : φ.range = layerQ ι g₀ c S := by
    rw [hφrange, hρ'range]
    rfl
  have hασ : ∀ d', α₀ (φ d') = φ (τ' d') := fun d' => by
    apply psiG_injective hι g₀ c
    rw [← psiG_intertwine_R hιC F₀ α₀ hα₀ hg₀C hg₀ hcα, hψφ, hρ'compat, ← hψφ]
  have hstabQ : ∀ g ∈ layerQ ι g₀ c S, α₀ g ∈ layerQ ι g₀ c S := by
    intro g hg
    rw [← hQ] at hg ⊢
    obtain ⟨d, rfl⟩ := hg
    exact ⟨τ' d, (hασ d).symm⟩
  refine ⟨layerQ ι g₀ c S, hcomp, hstabQ, fun D' hD' => ?_, fun g hg hgσ hk => ?_,
    hclaims α₀ φ hφinj hασ _ hQ⟩
  · obtain ⟨i, hi⟩ := isComponentOf_eq_of_decomposition (fun _ : Unit => layerQ ι g₀ c S)
      (fun _ => hcomp) (by rw [iSup_const]; exact hsolv) hD'
    rw [hi]
  · exact mem_of_two_power_of_odd_index hnormal hoddi hg hk

end Final

end CFSG.RankThree.PartOne.TCX.Ree
