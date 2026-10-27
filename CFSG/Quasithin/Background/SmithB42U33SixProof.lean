module

public import CFSG.Quasithin.Background.SmithB42U33Six
public import CFSG.Quasithin.Background.SmithB42U33Iso
public import CFSG.Quasithin.H13.U3SixUnique
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.LinearAlgebra.SL2MinimalFaithful

public section

namespace CFSG.Quasithin.B42U33

open CFSG.Open CFSG.Quasithin H13 H13.Orbit JonesParshall

section Fixed

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_one_of_fixed (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 6)
    {L : Subgroup (MulAut V)} (hsimp : IsSimpleGroup ↥L) (hL : Nat.card L = 6048) {v : V}
    (hv : ∀ l ∈ L, l v = v) : v = 1 := by
  by_contra hv1
  set C := fixV L with hCdef
  have hvC : v ∈ C := hv
  have hW : ∀ l : ↥L, C.map ((L.subtype l : MulAut V) : V →* V) = C := by
    intro l
    ext w
    constructor
    · rintro ⟨w', hw', rfl⟩
      change (l : MulAut V) w' ∈ C
      rw [hw' l l.2]
      exact hw'
    · intro hw
      exact ⟨w, hw, hw l l.2⟩
  let ρ := CFSG.SL2MinimalFaithful.quotientAction L.subtype C hW
  have hρ : ∀ (l : ↥L) (w : V), ρ l (w : V ⧸ C) = (((l : MulAut V) w : V) : V ⧸ C) :=
    fun l w => CFSG.SL2MinimalFaithful.quotientAction_mk L.subtype C hW l w
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
  ·
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hk
    have hVC : ∀ w : V ⧸ C, w ^ 2 = 1 := fun w => by
      induction w using QuotientGroup.induction_on with
      | H u => rw [← QuotientGroup.mk_pow, hV u, QuotientGroup.mk_one]
    obtain ⟨k, hk'⟩ : ∃ k, Nat.card (V ⧸ C) = 2 ^ k :=
      (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hVC)
    have h6 := six_le_of_card_dvd hVC hk' ρ.range
      (by rw [← hL]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm)
    have hC2 : 2 ≤ Nat.card C := by
      have : Nontrivial ↥C := ⟨⟨⟨v, hvC⟩, 1, fun h => hv1 (congrArg Subtype.val h)⟩⟩
      exact Finite.one_lt_card
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [hcard, hk'] at hprod
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h6
    nlinarith
  ·
    have h2 : ∀ l ∈ L, l ^ 2 = 1 := by
      intro l hl
      have hl' : ρ ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top _)
      refine MulEquiv.ext fun w => ?_
      have h1 := congrArg (fun f : MulAut (V ⧸ C) => f (w : V ⧸ C)) hl'
      simp only [hρ, MulAut.one_apply] at h1
      have hcC : (l w)⁻¹ * w ∈ C := QuotientGroup.eq.1 h1
      have hfix := hcC l hl
      have hinv : ∀ x : V, x⁻¹ = x := fun x =>
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV x)
      rw [map_mul, map_inv, hinv, hinv] at hfix
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      have e : l (l w) * l w = w * l w := by rw [hfix, mul_comm]
      exact mul_right_cancel e
    have hp : IsPGroup 2 ↥L := fun g => ⟨1, Subtype.ext (by simpa using h2 g g.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    rw [hL] at hn
    have h7 : 7 ∣ 2 ^ n := hn ▸ (by norm_num : 7 ∣ 6048)
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)

end Fixed

theorem cent_fixQ : ∀ c ∈ o0Codes, fixQW [1] c = true → fixQW [2] c = true →
    c = 0 ∨ c = 129 := by
  decide +kernel

theorem modQ_mul_self (q : ModQ) : q * q = 1 := by
  obtain ⟨c, rfl⟩ := codeQ_surjective q
  rw [← codeQ_xor, o0Xor_self, codeQ_zero]

@[expose] noncomputable def u33EquivDerived :
    U33G ≃* ↥(g2Derived (ZMod 2)) :=
  (u33EquivSubG2.trans (MulEquiv.subgroupCongr subG2_eq_commutator)).trans
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)).symm

theorem eq_one_of_fixed_Q {q : ModQ}
    (hq : ∀ δ ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) δ q = q) : q = 1 := by
  obtain ⟨c, rfl⟩ := codeQ_surjective q
  have h1 := fixQW_of (w := [1]) (by simp) c (hq _ (wordGG_mem_derived [1]))
  have h2 := fixQW_of (w := [2]) (by simp) c (hq _ (wordGG_mem_derived [2]))
  exact (codeQ_eq_one_iff c).2 (cent_fixQ c.1 c.2 h1 h2)

theorem modAct_derived (γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) (q : ModQ) :
    (FFModel.zornQ_isActionModel ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
      (Subgroup.commutator_le_self _)).modAct γ q =
      g2QAct (ZMod 2) ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ q := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem u33SixNatural :
    U33SixNatural := by
  intro V _ _ hV hcard L hP
  obtain ⟨θ⟩ := nonempty_equiv_g2Derived hP
  set ι : U33G ≃* ↥(g2Derived (ZMod 2)) := u33EquivDerived with hι
  set η : U33G ≃* ↥L := ι.trans θ.symm with hη
  have hL := card_of_b42TypeU33 hP
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hsimp : IsSimpleGroup ↥L := η.symm.isSimpleGroup
  let ψ : U33G →* MulAut V := L.subtype.comp η.toMonoidHom
  have hfixV : ∀ v : V, (∀ g, ψ g v = v) → v = 1 := by
    intro v hv
    refine eq_one_of_fixed hV hcard hsimp hL fun l hl => ?_
    obtain ⟨g, hg⟩ := η.surjective ⟨l, hl⟩
    have := hv g
    change ((η g : ↥L) : MulAut V) v = v at this
    rwa [hg] at this
  obtain ⟨F, hF⟩ := H13.U3.exists_equiv_u33_module (V := V)
    (fun v => by rw [← pow_two]; exact hV v) (by rw [hcard]; norm_num) ψ hfixV
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  let ψQ : U33G →* MulAut ModQ :=
    (g2QAct (ZMod 2)).comp ((g2Derived (ZMod 2)).subtype.comp ι.toMonoidHom)
  have hfixQ : ∀ q : ModQ, (∀ g, ψQ g q = q) → q = 1 := by
    intro q hq
    refine eq_one_of_fixed_Q fun δ hδ => ?_
    obtain ⟨g, hg⟩ := ι.surjective ⟨δ, hδ⟩
    have := hq g
    change g2QAct (ZMod 2) ((ι g : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2))) q = q at this
    rwa [hg] at this
  obtain ⟨F', hF'⟩ := H13.U3.exists_equiv_u33_module (V := ModQ) modQ_mul_self card_ModQ ψQ hfixQ
  let E : V ≃* ModQ := F.symm.trans F'
  have hE : ∀ (g : U33G) (v : V), E (ψ g v) = ψQ g (E v) := by
    intro g v
    change F' (F.symm (ψ g v)) = ψQ g (F' (F.symm v))
    obtain ⟨w, rfl⟩ := F.surjective v
    rw [← hF, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hF']
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
  set hD := FFModel.zornQ_isActionModel ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
    (Subgroup.commutator_le_self _) with hDdef
  have hinj : Function.Injective hD.modAct := by
    intro γ γ' h
    have h1 : g2QAct (ZMod 2) ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ =
        g2QAct (ZMod 2) ⟨γ'.1, Subgroup.commutator_le_self _ γ'.2⟩ :=
      MulEquiv.ext fun q => (modAct_derived γ q).symm.trans
        ((congrArg (fun f : MulAut ModQ => f q) h).trans (modAct_derived γ' q))
    have h2 := g2QAct_injective h1
    exact Subtype.ext (congrArg (fun x : ↥(quasithinG2 (ZMod 2)) => x.1) h2)
  let jD : ↥(g2Derived (ZMod 2)) ≃* ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
    Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)
  let r : ↥L ≃* ↥hD.modAct.range :=
    η.symm.trans (ι.trans (jD.trans (MonoidHom.ofInjective hinj)))
  refine H.FFModel.realizes_of_equiv (fun _ _ _ _ => trivial)
    ((Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).trans E) r (fun h u => ?_) hD.realizesMod_range
  obtain ⟨g, rfl⟩ := η.surjective h
  change hD.modAct (jD (ι (η.symm (η g)))) (E u) = E (((η g : ↥L) : MulAut V) u)
  rw [MulEquiv.symm_apply_apply, modAct_derived]
  exact (hE g u).symm

end CFSG.Quasithin.B42U33
