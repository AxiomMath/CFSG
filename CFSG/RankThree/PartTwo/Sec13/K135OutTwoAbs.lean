module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoBase

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outTwoGen_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : OutTwoGen Y) :
    OutTwoGen X := by
  intro V hV
  obtain ⟨a', ha', b', hb', hsub⟩ :=
    h (V.map (MulAut.congr e).toMonoidHom) (hV.map (MulAut.congr e).toMonoidHom)
  have hpull : ∀ c ∈ V.map (MulAut.congr e).toMonoidHom, (MulAut.congr e).symm c ∈ V := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
    have hback : (MulAut.congr e).symm ((MulAut.congr e).toMonoidHom x) = x :=
      (MulAut.congr e).symm_apply_apply x
    rw [hback]
    exact hx
  refine ⟨(MulAut.congr e).symm a', hpull a' ha', (MulAut.congr e).symm b', hpull b' hb', ?_⟩
  have hcomp : Subgroup.closure ({a', b'} : Set (MulAut Y)) ⊔
      (MulAut.conj : Y →* MulAut Y).range ≤
      (Subgroup.closure ({(MulAut.congr e).symm a', (MulAut.congr e).symm b'} :
          Set (MulAut X)) ⊔ (MulAut.conj : X →* MulAut X).range).comap
        (MulAut.congr e).symm.toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hx with hx | hx
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · intro x hx
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hx
      have key : (MulAut.congr e).symm (MulAut.conj z) = MulAut.conj (e.symm z) := by
        rw [MulEquiv.symm_apply_eq,
          CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
      refine Subgroup.mem_comap.mpr ?_
      show (MulAut.congr e).symm (MulAut.conj z) ∈ _
      rw [key]
      exact Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨e.symm z, rfl⟩)
  intro v hv
  have hv' : (MulAut.congr e).toMonoidHom v ∈ V.map (MulAut.congr e).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
  have h1 := hcomp (hsub hv')
  rw [Subgroup.mem_comap] at h1
  have hback : (MulAut.congr e).symm.toMonoidHom ((MulAut.congr e).toMonoidHom v) = v :=
    (MulAut.congr e).symm_apply_apply v
  rw [hback] at h1
  exact h1

theorem outTwoGen_of_card_dvd {X : Type} [Group X] [Finite X] {m : ℕ} (hm : Odd m)
    (h : Nat.card (Outer X) ∣ 4 * m) : OutTwoGen X := by
  intro V hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥(V.map (QuotientGroup.mk' (inner X))) :=
    hV.map (QuotientGroup.mk' (inner X))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hW2
  have hdvd : Nat.card ↥(V.map (QuotientGroup.mk' (inner X))) ∣ 4 * m :=
    (Subgroup.card_subgroup_dvd_card _).trans h
  rw [hn] at hdvd
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  have h4 : 2 ^ n ∣ 4 := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
  have hle4 : Nat.card ↥(V.map (QuotientGroup.mk' (inner X))) ≤ 4 := by
    rw [hn]
    exact Nat.le_of_dvd (by norm_num) h4
  obtain ⟨α, hα, β, hβ, hle⟩ :=
    ot_two_gen_of_card_le_four (V.map (QuotientGroup.mk' (inner X))) hle4
  exact ot_lift_two_gen V α β hα hβ hle

theorem ot_pow_two_eq_one_of_isPGroup {Y : Type*} [Group Y] (V : Subgroup Y)
    (hV : IsPGroup 2 V) {α : Y} (hα : α ∈ V) : ∃ k : ℕ, α ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨α, hα⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem outTwoGen_of_outPNice_two {X : Type} [Group X] [Finite X]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPNice 2 X) : OutTwoGen X := by
  obtain ⟨D, E, -, hD2, hE, -, hcmp⟩ := h
  intro V hV
  have hVD : ∀ α ∈ V, ∃ k : ℕ, α ^ (2 ^ k) ∈ D := by
    intro α hα
    obtain ⟨k, hk⟩ := ot_pow_two_eq_one_of_isPGroup V hV hα
    exact ⟨k, by rw [hk]; exact D.one_mem⟩
  have hVE : ∀ α ∈ V, α ∈ E := fun α hα => hE α (hVD α hα)
  have hcomp : ∀ a ∈ V.map (QuotientGroup.mk' (inner X)),
      ∀ b ∈ V.map (QuotientGroup.mk' (inner X)),
      a ∈ Subgroup.zpowers b ∨ b ∈ Subgroup.zpowers a := by
    intro a ha b hb
    obtain ⟨α, hαV, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨β, hβV, rfl⟩ := Subgroup.mem_map.mp hb
    rcases hcmp α (hVE α hαV) β (hVE β hβV) (hVD α hαV) (hVD β hβV) with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      have hδV : α * β ^ m ∈ V := V.mul_mem hαV (V.zpow_mem hβV m)
      obtain ⟨k, hk⟩ := ot_pow_two_eq_one_of_isPGroup V hV hδV
      have hδI : α * β ^ m ∈ inner X :=
        hD2 (α * β ^ m) hm k (by rw [hk]; exact Subgroup.one_mem _)
      have h1 : QuotientGroup.mk' (inner X) (α * β ^ m) = 1 :=
        (QuotientGroup.eq_one_iff (α * β ^ m)).mpr hδI
      rw [map_mul, map_zpow] at h1
      have h2 : QuotientGroup.mk' (inner X) α = (QuotientGroup.mk' (inner X) β) ^ (-m) := by
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.zpow_mem_zpowers _ _
    · right
      have hδV : β * α ^ m ∈ V := V.mul_mem hβV (V.zpow_mem hαV m)
      obtain ⟨k, hk⟩ := ot_pow_two_eq_one_of_isPGroup V hV hδV
      have hδI : β * α ^ m ∈ inner X :=
        hD2 (β * α ^ m) hm k (by rw [hk]; exact Subgroup.one_mem _)
      have h1 : QuotientGroup.mk' (inner X) (β * α ^ m) = 1 :=
        (QuotientGroup.eq_one_iff (β * α ^ m)).mpr hδI
      rw [map_mul, map_zpow] at h1
      have h2 : QuotientGroup.mk' (inner X) β = (QuotientGroup.mk' (inner X) α) ^ (-m) := by
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨g, hgW, hWg⟩ := ot_cyclic_of_comparable (V.map (QuotientGroup.mk' (inner X))) hcomp
  exact ot_lift_two_gen V g g hgW hgW
    (hWg.trans (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert g {g}))))

end CFSG.RankThree.PartTwo.Sec13.F135Last
