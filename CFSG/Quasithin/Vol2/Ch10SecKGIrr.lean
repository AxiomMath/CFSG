module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KG

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem isIrrSec_of_realizesVia {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (hker : D.ker = ⊥)
    (hnt : ∃ m ∈ D.sec, m ≠ 1)
    (hirr : ∀ S : Subgroup D.Amb, S ≤ D.sec → (∀ γ, ∀ m ∈ S, D.act γ m ∈ S) →
      S = ⊥ ∨ S = D.sec) :
    XMod.IsIrrSec ↥H Z U := by
  obtain ⟨-, hZU, -, hU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hmk : ∀ m : ↥D.sec,
      (QuotientGroup.mk m : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ m = 1 := by
    intro m
    rw [QuotientGroup.eq_one_iff, hker, Subgroup.bot_subgroupOf, Subgroup.mem_bot]
  refine ⟨lt_of_le_of_ne hZU fun hZU' => ?_, fun J hJ hZJ hJU => ?_⟩
  · obtain ⟨m, hm, hm1⟩ := hnt
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have huZ : (u : V) ∈ Z := hZU' ▸ u.2
    have h1 := (hβk u).mpr huZ
    rw [hu, hmk] at h1
    exact hm1 (congrArg Subtype.val h1)
  · let S : Subgroup D.Amb :=
      { carrier := {m | ∃ hm : m ∈ D.sec, ∃ j : ↥U, (j : V) ∈ J ∧
          β j = QuotientGroup.mk ⟨m, hm⟩}
        one_mem' := ⟨D.sec.one_mem, 1, J.one_mem, by rw [map_one]; rfl⟩
        mul_mem' := by
          rintro a b ⟨ha, ja, hja, hβa⟩ ⟨hb, jb, hjb, hβb⟩
          exact ⟨D.sec.mul_mem ha hb, ja * jb, J.mul_mem hja hjb, by
            rw [map_mul, hβa, hβb]; rfl⟩
        inv_mem' := by
          rintro a ⟨ha, ja, hja, hβa⟩
          exact ⟨D.sec.inv_mem ha, ja⁻¹, J.inv_mem hja, by rw [map_inv, hβa]; rfl⟩ }
    have hSinv : ∀ γ, ∀ m ∈ S, D.act γ m ∈ S := by
      rintro γ m ⟨hm, j, hjJ, hβj⟩
      have hu : ((π γ : ↥H) : MulAut V) (j : V) ∈ U := hU (π γ) j j.2
      have hJ' : ((π γ : ↥H) : MulAut V) (j : V) ∈ J := hJ (π γ) j hjJ
      exact ⟨hsec γ m hm, ⟨_, hu⟩, hJ', hβe γ j ⟨m, hm⟩ hu (hsec γ m hm) hβj⟩
    rcases hirr S (fun m hm => hm.1) hSinv with hS | hS
    · left
      refine le_antisymm (fun j hj => ?_) hZJ
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨j, hJU hj⟩)
      have hmS : (m : D.Amb) ∈ S := ⟨m.2, ⟨j, hJU hj⟩, hj, hm.symm⟩
      rw [hS, Subgroup.mem_bot] at hmS
      have h1 : β ⟨j, hJU hj⟩ = 1 := by
        rw [← hm, (hmk m).mpr (Subtype.ext hmS)]
      exact (hβk _).mp h1
    · right
      refine le_antisymm hJU fun u hu => ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
      have hmS : (m : D.Amb) ∈ S := by rw [hS]; exact m.2
      obtain ⟨hm', j, hjJ, hβj⟩ := hmS
      have h1 : β (⟨u, hu⟩ * j⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hm, hβj, mul_inv_cancel]
      have h2 : u * (j : V)⁻¹ ∈ Z := (hβk _).mp h1
      have h3 : u = u * (j : V)⁻¹ * j := by group
      rw [h3]
      exact J.mul_mem (hZJ h2) hjJ

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KG
