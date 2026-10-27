module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Ball
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem pClosed_of_inf_eq_ballStab (h33 : Fan33 F) {α β : V}
    (hαβ : Γ.Adj α β) (h : nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α) : PClosed Γ G α := by
  obtain ⟨x, hxα, hxo⟩ := F.exists_orderOf_eq_valence α
  obtain ⟨h1, h2, -⟩ := h33 α β hαβ x hxα hxo
  exact h2.1 (h1.1 h)

theorem exists_fix_move {b a c : V} (ha : Γ.Adj b a) (hc : Γ.Adj b c) (hac : a ≠ c) :
    ∃ g ∈ MulAction.stabilizer G b, g • a = a ∧ g • c ≠ c := by
  obtain ⟨g, hg, hga, c', hc', hgc'⟩ := F.frobenius_nonreg b a ha
  refine ⟨g, hg, hga, fun hgc => hgc' ?_⟩
  exact mem_nbrStab.1 (F.fix_two_nbrs ha hc hac hga hgc) c' hc'

theorem mem_normalizer_inf {v a : V} {g : G} (hv : g ∈ MulAction.stabilizer G v)
    (ha : g ∈ MulAction.stabilizer G a) :
    g ∈ Subgroup.normalizer ((nbrStab Γ G v ⊓ nbrStab Γ G a : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ MulAction.stabilizer G v → g' ∈ MulAction.stabilizer G a →
      ∀ h : G, h ∈ nbrStab Γ G v ⊓ nbrStab Γ G a → g' * h * g'⁻¹ ∈ nbrStab Γ G v ⊓ nbrStab Γ G a :=
    fun g' hv' ha' h hh =>
      ⟨F.conj_mem_nbrStab_of_stab hv' hh.1, F.conj_mem_nbrStab_of_stab ha' hh.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hv ha h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hv) (inv_mem ha) _ hh
  simpa [mul_assoc] using this

theorem inf_eq_ballStab_two_of_le {b a c : V} (ha : Γ.Adj b a) (hc : Γ.Adj b c) (hac : a ≠ c)
    (h : nbrStab Γ G b ⊓ nbrStab Γ G c ≤ nbrStab Γ G a) :
    nbrStab Γ G b ⊓ nbrStab Γ G a = ballStab Γ G 2 b := by
  set N : Subgroup G := nbrStab Γ G b ⊓ nbrStab Γ G a with hN
  have hfin : Finite ↥N := by
    have : Finite ↥(MulAction.stabilizer G b) := F.loc_finite b
    exact Finite.of_injective (Subgroup.inclusion (show N ≤ MulAction.stabilizer G b from
      fun g hg => F.nbrStab_le_stabilizer b hg.1)) (Subgroup.inclusion_injective _)
  obtain ⟨k, hk, hkc⟩ := F.loc_trans b c a hc ha
  have hk' : k ∈ MulAction.stabilizer G b := hk
  have hconj : ∀ n ∈ N, k⁻¹ * n * k ∈ nbrStab Γ G b ⊓ nbrStab Γ G c := by
    intro n hn
    refine ⟨?_, ?_⟩
    · have := F.conj_mem_nbrStab_of_stab (inv_mem hk') hn.1
      simpa using this
    · have h2 := (F.mem_nbrStab_smul_iff k c (h := n)).1 (by rw [hkc]; exact hn.2)
      exact h2
  have hNeq : nbrStab Γ G b ⊓ nbrStab Γ G c = N := by
    refine le_antisymm (fun g hg => ⟨hg.1, h hg⟩) fun n hn => ?_
    let f : ↥N → ↥N := fun m => ⟨k⁻¹ * m * k, (hconj m m.2).1, h (hconj m m.2)⟩
    have hinj : Function.Injective f := by
      intro m m' hmm'
      have := congrArg Subtype.val hmm'
      simp only [f] at this
      exact Subtype.ext (by simpa using this)
    obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨n, hn⟩
    have : (n : G) = k⁻¹ * m * k := by
      have := congrArg Subtype.val hm
      simpa [f] using this.symm
    rw [this]
    exact hconj m m.2
  obtain ⟨g₁, hg₁, hg₁a, hg₁c⟩ := F.exists_fix_move ha hc hac
  obtain ⟨g₂, hg₂, hg₂c, hg₂a⟩ := F.exists_fix_move hc ha hac.symm
  have hn₁ : g₁ ∈ Subgroup.normalizer (N : Set G) :=
    F.mem_normalizer_inf hg₁ (MulAction.mem_stabilizer_iff.2 hg₁a)
  have hn₂ : g₂ ∈ Subgroup.normalizer (N : Set G) := by
    have := F.mem_normalizer_inf hg₂ (MulAction.mem_stabilizer_iff.2 hg₂c)
    rwa [hNeq] at this
  have hcl : Subgroup.closure ({g₁, g₂} : Set G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hn₁
    · exact hn₂
  have hall : ∀ γ, Γ.Adj b γ → N ≤ nbrStab Γ G γ := by
    intro γ hγ n hn
    obtain ⟨m, hm, -, hma⟩ := F.transitive_of_two_fixers ha hc hac hg₁ hg₂ hg₁a hg₁c hg₂c hg₂a
      ha hγ
    have hmn : m⁻¹ * n * m ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hcl hm)) n).1 hn
      simpa using this
    have := (F.mem_nbrStab_smul_iff m a (h := n)).2 hmn.2
    rwa [hma] at this
  refine le_antisymm (fun n hn => ?_) (F.ballStab_two_le_inf ha)
  rw [F.mem_ballStab_two_iff]
  exact ⟨hn.1, fun γ hγ => hall γ hγ hn⟩

end FanTree

theorem not_hasRightSingular_one (F : FanTree Γ G) : ¬ HasRightSingular Γ G 1 := by
  rintro ⟨P, w, hw, hwne, hfix⟩
  have h10 : Γ.Adj (P.vert 1) (P.vert 0) := (P.adj 0 (by norm_num)).symm
  obtain ⟨g, hg, hg0, c, hc, hgc⟩ := F.frobenius_nonreg (P.vert 1) (P.vert 0) h10
  have hgst : g ∈ stabRange G P.vert 0 1 := by
    rw [mem_stabRange]
    intro m hm0 hm1
    rcases Nat.lt_or_ge m 1 with h | h
    · obtain rfl : m = 0 := by omega
      exact hg0
    · obtain rfl : m = 1 := by omega
      exact MulAction.mem_stabilizer_iff.1 hg
  have hgw := hfix g hgst
  have hne : P.vert 0 ≠ w := fun h => hwne (by simpa using h.symm)
  exact hgc (mem_nbrStab.1 (F.fix_two_nbrs h10 hw hne hg0 hgw) c hc)

theorem fan_3_4 {F : FanTree Γ G} (h33 : Fan33 F) : Fan34 F := by
  intro P hP
  have hstab : ∀ g, g ∈ stabRange G P.vert 0 2 ↔ g ∈ nbrStab Γ G (P.vert 1) := by
    intro g
    rw [F.mem_stabRange_iff_nbrStab (le_refl _) (fun m _ hm => P.adj m hm)
      (fun m _ hm => P.nb m hm)]
    constructor
    · intro h
      exact h 1 (by norm_num) (by norm_num)
    · intro h m hm1 hm2
      obtain rfl : m = 1 := by omega
      exact h
  have key : ∀ β, Γ.Adj (P.vert 1) β → nbrStab Γ G (P.vert 1) ≤ nbrStab Γ G β →
      nbrStab Γ G (P.vert 1) = ballStab Γ G 2 (P.vert 1) ∧ PClosed Γ G (P.vert 1) := by
    intro β hβ hle
    have hball := F.nbrStab_eq_ballStab_two_of_le hβ hle
    refine ⟨hball, F.pClosed_of_inf_eq_ballStab h33 hβ ?_⟩
    rw [inf_eq_left.2 hle, hball]
  have h01 : Γ.Adj (P.vert 1) (P.vert 0) := (P.adj 0 (by norm_num)).symm
  have h12 : Γ.Adj (P.vert 1) (P.vert 2) := P.adj 1 (by norm_num)
  rcases hP with ⟨w, hw, hwne, hfix⟩ | ⟨w, hw, hwne, hfix⟩
  ·
    refine key (P.vert 0) h01 fun g hg => ?_
    have hgw : g • w = w := hfix g ((hstab g).2 hg)
    have hg1 : g • P.vert 1 = P.vert 1 :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg)
    exact F.fix_two_nbrs hw h01.symm (by simpa using hwne) hgw hg1
  ·
    refine key (P.vert 2) h12 fun g hg => ?_
    have hgw : g • w = w := hfix g ((hstab g).2 hg)
    have hg1 : g • P.vert 1 = P.vert 1 :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg)
    exact F.fix_two_nbrs hw h12.symm (by simpa using hwne) hgw hg1

theorem fan_3_5 {F : FanTree Γ G} (h33 : Fan33 F) : Fan35 F := by
  intro h3 h2
  obtain ⟨k, hk1, hk3, P, hP⟩ := h3
  have hk : k = 3 := by
    by_contra hne
    exact h2 ⟨k, hk1, by omega, P, hP⟩
  subst hk
  obtain ⟨w, hw, hwne, hfix⟩ := hP
  have h12 : Γ.Adj (P.vert 2) (P.vert 1) := (P.adj 1 (by norm_num)).symm
  have h23 : Γ.Adj (P.vert 2) (P.vert 3) := P.adj 2 (by norm_num)
  have h13 : P.vert 1 ≠ P.vert 3 := P.nb 1 (by norm_num)
  have hle : nbrStab Γ G (P.vert 2) ⊓ nbrStab Γ G (P.vert 1) ≤ nbrStab Γ G (P.vert 3) := by
    intro g hg
    have hgst : g ∈ stabRange G P.vert 0 3 := by
      rw [F.mem_stabRange_iff_nbrStab (by norm_num) (fun m _ hm => P.adj m hm)
        (fun m _ hm => P.nb m hm)]
      intro m hm1 hm2
      rcases Nat.lt_or_ge m 2 with h | h
      · obtain rfl : m = 1 := by omega
        exact hg.2
      · obtain rfl : m = 2 := by omega
        exact hg.1
    have hgw := hfix g hgst
    have hg2 : g • P.vert 2 = P.vert 2 :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg.1)
    exact F.fix_two_nbrs hw h23.symm (by simpa using hwne) hgw hg2
  refine ⟨P.vert 2, F.pClosed_of_inf_eq_ballStab h33 h23 ?_⟩
  exact F.inf_eq_ballStab_two_of_le h23 h12 (fun h => h13 h.symm) hle

theorem fan_4_0 {F : FanTree Γ G} (h34 : Fan34 F) (h35 : Fan35 F) : Fan40 F := by
  have hnp : ∀ v, ¬ PClosed Γ G v := F.not_pclosed
  have s1 := not_hasRightSingular_one F
  have s2 : ¬ HasRightSingular Γ G 2 := by
    rintro ⟨P, hP⟩
    exact hnp _ (h34 P (Or.inr hP)).2
  have hs2 : ¬ SingLe Γ G 2 := by
    rintro ⟨k, hk1, hk2, hk⟩
    interval_cases k
    · exact s1 hk
    · exact s2 hk
  intro k hk1 hk4 hk
  interval_cases k
  · exact s1 hk
  · exact s2 hk
  · obtain ⟨α, hα⟩ := h35 ⟨3, by norm_num, le_rfl, hk⟩ hs2
    exact hnp α hα

end CFSG.Quasithin.Fan86
