module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporArith
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Sporadic.J2
public import Certificates.Certificate3139
public import Certificates.Certificate4142
public import Certificates.Certificate7125
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem overgroups_card_of_lattice {Γ : Type} [Group Γ] [Finite Γ] (S : Subgroup Γ)
    (hS : IsSylowTwoOf S ⊤) (J : ℕ) (Y : ℕ → Subgroup Γ) (Q : ℕ → Prop)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j)
    (hmem : ∀ j < J, Q (Nat.card (Y j))) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* Γ)) {T Z : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTZ : T ≤ Z) :
    Z = ⊤ ∨ Q (Nat.card Z) := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  let ψ : X ≃* Γ := e.trans (MulAut.conj g)
  have hψ : T.map ψ.toMonoidHom = S := by
    rw [hST, Subgroup.map_map]
    rfl
  have hSZ : S ≤ Z.map ψ.toMonoidHom := by
    rw [← hψ]; exact Subgroup.map_mono hTZ
  obtain ⟨j, hj, hZ⟩ := hall _ hSZ
  have hcard : Nat.card Z = Nat.card (Z.map ψ.toMonoidHom) :=
    Nat.card_congr (Z.equivMapOfInjective _ ψ.injective).toEquiv
  by_cases hjJ : j < J
  · right
    have hm : memberOrTop J Y j = Y j := by simp [memberOrTop, hjJ]
    rw [hm] at hZ
    rw [hcard, hZ]
    exact hmem j hjJ
  · left
    have hm : memberOrTop J Y j = ⊤ := by simp [memberOrTop, hjJ]
    rw [hm] at hZ
    have := congrArg (Subgroup.comap ψ.toMonoidHom) hZ
    rw [Subgroup.comap_map_eq_self_of_injective ψ.injective, Subgroup.comap_top] at this
    exact this

open CFSG.Quasithin.E2P.SporB in
theorem j2_overgroups_card
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .J2)) {T Y : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ Nat.card Y = 2 ^ 7 ∨ 3 ∣ Nat.card Y := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* ↥CFSG.Sporadic.J2.J) := ⟨e.trans CFSG.Sporadic.J2.nativeEquiv⟩
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  have hS : IsSylowTwoOf j2Ctx.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index j2Ctx.S
    rw [j2Ctx.S_card, j2Ctx.hΓ, hN] at h1
    have h2 : j2Ctx.S.index = 4725 := by
      have : j2Ctx.k = 7 := rfl
      rw [this] at h1
      omega
    rw [h2]
    norm_num
  have hOm : j2Ctx.D.Om.size = 5 := by simpa using congrArg Array.size hL
  have hJ : j2Ctx.J = 5 := by
    have h1 : j2Ctx.D.Om.size = j2Ctx.D.mw.size := j2Ctx.membersOK.2.2.2.1
    show j2Ctx.D.mw.size = 5
    omega
  have hsz : ∀ j < j2Ctx.J, j2Ctx.D.Om[j]!.lbl.size = #[1, 3, 9, 15, 3][j]! := by
    intro j hj
    have hjO : j < j2Ctx.D.Om.size := by omega
    rw [← hL, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO)]
    simp
  refine (overgroups_card_of_lattice j2Ctx.S hS j2Ctx.J j2Ctx.Y (fun n => n = 2 ^ 7 ∨ 3 ∣ n)
    j2Ctx.complete ?_ hX' hT hTY).imp_right id
  intro j hj
  rw [j2Ctx.Y_card hj, hsz j hj]
  have hj5 : j < 5 := hJ ▸ hj
  have : j2Ctx.k = 7 := rfl
  rw [this]
  interval_cases j
  · exact Or.inl (by norm_num)
  all_goals exact Or.inr (by norm_num)

theorem noPowerOvergroup_j2 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  refine noPowerOvergroup_of_overgroups (fun X _ _ ⟨e⟩ => ?_)
    (fun X _ _ ⟨e⟩ T Y hT hTY => ?_)
  · rw [Nat.card_congr e.toEquiv]
    show 3 ∣ Nat.card NativeSporadic.J2
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num
  · rcases j2_overgroups_card ⟨e⟩ hT hTY with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨7, h⟩)
    · exact Or.inr (Or.inr h)

end CFSG.Quasithin.H13.NQCore
