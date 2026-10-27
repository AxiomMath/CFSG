module

public import CFSG.RankThree.PartOne.U5K.Pkg.Rel
public import CFSG.RankThree.PartOne.S12.Sec153Defs
import CFSG.RankThree.PartOne.S12.TerminalWeylPerm
public import CFSG.RankThree.PartOne.U5K.Pkg.Rows

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem card_reflectionGroup_five (hout : Outcome152Five p E A (lieGenerated p E)) :
    Nat.card (reflectionGroup p E) = 120 := by
  obtain ⟨f₀, -, -, -, ⟨ψ⟩, -⟩ := hout
  rw [Nat.card_congr ψ.toEquiv, card_perm_five]

theorem exists_psi_k (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∃ (ψ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)) (k : Fin 5),
      (∀ x ∈ torusImage E L, ∃ h : x ∈ reflectionGroup p E, ψ ⟨x, h⟩ k = k) ∧
      (∀ σ : Equiv.Perm (Fin 5), σ k = k →
        ((ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) ∈ torusImage E L) := by
  obtain ⟨h24, -, -⟩ := rows h15 hF hout
  obtain ⟨f₀, -, -, -, ⟨ψ⟩, -⟩ := hout
  have hLX := torusImage_le_reflectionGroup hF
  set H : Subgroup (Equiv.Perm (Fin 5)) :=
    ((torusImage E L).subgroupOf (reflectionGroup p E)).map ψ.toMonoidHom with hH
  have hS : Nat.card H = 24 := by
    rw [hH, Subgroup.card_map_of_injective ψ.injective, ← h24]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
  obtain ⟨k, hk⟩ := TerminalPerm.exists_fixed_point_of_card_24 H hS
  have hle : H ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) k := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact hk σ hσ
  have heq : H = MulAction.stabilizer (Equiv.Perm (Fin 5)) k :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [WeylIso.card_stabilizer_fin (n := 4), hS]; decide)
  refine ⟨ψ, k, fun x hx => ⟨hLX hx, hk _ ?_⟩, fun σ hσ => ?_⟩
  · exact Subgroup.mem_map_of_mem ψ.toMonoidHom (Subgroup.mem_subgroupOf.2 hx)
  · have hσH : σ ∈ H := by
      rw [heq, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hσ
    obtain ⟨x, hx, hxσ⟩ := Subgroup.mem_map.1 hσH
    have : ψ.symm σ = x := by
      rw [← hxσ]
      exact ψ.symm_apply_apply x
    rw [this]
    exact Subgroup.mem_subgroupOf.1 hx

theorem key_of_five (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∀ e : E, (∀ x ∈ reflectionGroup p E, x e = e) → e = 1 := by
  obtain ⟨h24, -, -⟩ := rows h15 hF hout
  have h120 := card_reflectionGroup_five hout
  have hXne : reflectionGroup p E ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at h120
    omega
  have hLne : torusImage E L ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at h24
    omega
  have hbot := fixedIn_reflectionGroup_eq_bot h15.h12 hF hXne hLne
  intro e he
  have hmem : (e : G) ∈ fixedIn E (reflectionGroup p E : Set (MulAut E)) :=
    ⟨e.2, fun x hx => by simpa using he x hx⟩
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem span_of_five (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∀ N : Subgroup E, (∀ x ∈ reflectionGroup p E, ∀ m ∈ N, x m ∈ N) →
      (⟨c, h15.h12.A_le_E h15.h12.c_mem⟩ : E) ∈ N →
      N = ⊤ ∨ N ≤ Subgroup.zpowers (⟨c, h15.h12.A_le_E h15.h12.c_mem⟩ : E) := by
  obtain ⟨-, -, hsup, hinf⟩ := rows h15 hF hout
  intro N hN hcN
  set N' : Subgroup G := N.map E.subtype with hN'
  have hN'E : N' ≤ E := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hinv : torusInvariant E L N' := by
    intro w hw b hb
    obtain ⟨m, hm, rfl⟩ := hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hmem : conjAut E w hwN ∈ reflectionGroup p E :=
      torusImage_le_reflectionGroup hF (conjAut_mem_torusImage hwN hw.1)
    exact ⟨conjAut E w hwN m, hN _ hmem m hm, coe_conjAut_apply hwN m⟩
  have hc' : c ∈ N' := ⟨_, hcN, rfl⟩
  by_cases hNE : N' = E
  · left
    refine eq_top_iff.2 fun m _ => ?_
    have h1 : (m : G) ∈ N' := by rw [hNE]; exact m.2
    obtain ⟨m', hm', hmm'⟩ := h1
    have : m' = m := Subtype.ext hmm'
    rwa [← this]
  · right
    have hne : N' ≠ ⊥ := fun h0 => h15.h12.c_ne_one (by
      have h2 : c ∈ N' := hc'
      rw [h0] at h2
      exact Subgroup.mem_bot.1 h2)
    rcases hF.four.1 N' hN'E hinv hne hNE with hz | hB0
    · intro m hm
      have h1 : (m : G) ∈ N' := ⟨m, hm, rfl⟩
      rw [hz] at h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · exfalso
      have h2 : c ∈ Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ :=
        ⟨Subgroup.mem_zpowers c, hB0 ▸ hc'⟩
      rw [hinf] at h2
      exact h15.h12.c_ne_one (Subgroup.mem_bot.1 h2)

theorem reflectionSet_nonempty (hF : Sec12Facts G p A c L E) (hL : torusImage E L ≠ ⊥) :
    (reflectionSet p E).Nonempty := by
  by_contra hcon
  have hempty : reflectionSet p E = ∅ := Set.not_nonempty_iff_eq_empty.1 hcon
  have hclosure := hF.three.1
  rw [hempty, Set.empty_inter, Subgroup.closure_empty] at hclosure
  exact hL hclosure

noncomputable def mkModel (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E))
    (ψ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)) (k : Fin 5)
    (hk : ∀ x ∈ torusImage E L, ∃ h : x ∈ reflectionGroup p E, ψ ⟨x, h⟩ k = k)
    (hstab : ∀ σ : Equiv.Perm (Fin 5), σ k = k →
      ((ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) ∈ torusImage E L) :
    Model p E (⟨c, h15.h12.A_le_E h15.h12.c_mem⟩ : E) where
  prime := h15.h12.prime
  five_le := Sec12Three.five_le h15.h12
  elem := h15.h12.E_elem
  card := by
    obtain ⟨-, -, -, -, -, hcard, -⟩ := hout
    exact hcard
  hc1 := fun h => h15.h12.c_ne_one (congrArg Subtype.val h)
  ψ := ψ
  k := k
  Λ := torusImage E L
  Λ_k := hk
  Λ_stab := hstab
  Λ_c := fun _ hx => torusImage_fixes_c h15.h12 hx
  key := key_of_five h15 hF hout
  D_ne := reflectionSet_nonempty hF (by
    intro h0
    obtain ⟨h24, -, -⟩ := rows h15 hF hout
    rw [h0, Subgroup.card_bot] at h24
    omega)
  span := span_of_five h15 hF hout

theorem _root_.CFSG.RankThree.PartOne.U5K.kfU5Mod_holds : KFU5Mod := by
  intro G _ _ p A c L E h15 hF hout
  obtain ⟨ψ, k, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k hk hstab
  exact ⟨M.ψ, M.v, M.equivariant, M.exists_prod, M.prod_eq_one_iff, fun t ht => M.swap_of_mem ht⟩

theorem nonempty_weylIso (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) : Nonempty (WeylIso p 4 E L) := by
  obtain ⟨ψ, k, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k hk hstab
  exact ⟨⟨ψ, fun t ht => M.swap_of_mem ht, fun σ hσ => M.surj_swap hσ, k, hk⟩⟩

end CFSG.RankThree.PartOne.U5K.Pkg
