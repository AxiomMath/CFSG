module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelD

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

noncomputable def hdRo7CLCoordAux_subgroupOfEquiv (Bs X : Subgroup G) :
    ↥((Bs ⊓ X).subgroupOf X) ≃* ↥(Bs ⊓ X) where
  toFun x := ⟨((x : ↥X) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨(x : G), x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

lemma hdRo7CLCoordAux_card_subgroupOf (Bs X : Subgroup G) :
    Nat.card ↥((Bs ⊓ X).subgroupOf X) = Nat.card ↥(Bs ⊓ X) :=
  Nat.card_congr (hdRo7CLCoordAux_subgroupOfEquiv Bs X).toEquiv

@[expose] def hdRo7CLCoordAux_SignedData (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X)),
    Function.Injective τ ∧ Function.Surjective τ ∧
    (∀ i : Fin k, ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.sgnAut i f) : G)) ∧
    (∀ σ : Equiv.Perm (Fin k), ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.permAut σ f) : G)) ∧
    ∀ g : X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τ f : G) * (g : G)⁻¹ = (τ f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i)

lemma hdRo7CLCoordAux_signedData_of_signedEltSC {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hEab : IsElemAbelian p (Bs ⊓ X)) (h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X))
    (h : GGTorusSignedEltSC p ↥X) : hdRo7CLCoordAux_SignedData p Bs X := by
  have hEab' : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) := hEab.subgroupOf X
  have h3' : p ^ 3 ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [hdRo7CLCoordAux_card_subgroupOf]; exact h3
  have hsc : ∀ g : ↥X, (∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e = e * g) → g ^ p = 1 →
      g ∈ (Bs ⊓ X).subgroupOf X := by
    intro g hgc hgp
    rw [Subgroup.mem_subgroupOf] at ⊢
    refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 (g : G) ?_ ?_, g.2⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b hb
      have hge : (g : G) * (e : G) = (e : G) * (g : G) := by
        have h1 := hgc ⟨(e : G), he.2⟩ (Subgroup.mem_subgroupOf.mpr he)
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val h1
      have hgc' : (g : G) * (c : G) = (c : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hc.2 (g : G) g.2
      have key : (g : G) * ((e : G) * (c : G)) = ((e : G) * (c : G)) * (g : G) := by
        calc (g : G) * ((e : G) * (c : G)) = ((g : G) * e) * c := by group
          _ = ((e : G) * g) * c := by rw [hge]
          _ = (e : G) * ((g : G) * c) := by group
          _ = (e : G) * ((c : G) * (g : G)) := by rw [hgc']
          _ = ((e : G) * (c : G)) * (g : G) := by group
      exact key.symm
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨k, τ, hτinj, hτrange, hsgn, hperm, hnorm⟩ :=
    h ((Bs ⊓ X).subgroupOf X) hEab' h3' hsc
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans
      ((MulEquiv.subgroupCongr hτrange).trans (hdRo7CLCoordAux_subgroupOfEquiv Bs X))
  have hcoe : ∀ f, (eτ.toMonoidHom f : G) = (τ f : G) := fun f => rfl
  refine ⟨k, eτ.toMonoidHom, eτ.injective, eτ.surjective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.sgnAut i f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.permAut σ f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro g hg
    have hg' : ∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e * g⁻¹ ∈ (Bs ⊓ X).subgroupOf X := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      obtain ⟨e', he'⟩ := hg ⟨(e : G), he⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'
      rw [h1]
      exact e'.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe f, hcoe f'] at hff'
    exact hff'

theorem hdRo7CLCoordAux_card_inf_ge (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (hZL : Subgroup.center ↥L = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsplit := card_ggBstar_split hH.1.2.1 hZL hBsN hinner
  have hCeq : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hdRo7CLCoordAux_bstar_centralizer_eq hH
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers,
      orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  have h4 : p ^ 4 ≤ Nat.card ↥Bs := hdRo7CLCoordAux_card_bstar_ge hH
  have hle : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ L) * p := by
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := h4
      _ = Nat.card ↥(Bs ⊓ L) *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hsplit
      _ = Nat.card ↥(Bs ⊓ L) * p := by rw [hCcard]
  exact Nat.le_of_mul_le_mul_right hle hp.pos

theorem hdRo7CLCoordAux_signedData_L (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (R : Type) [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hZL : Subgroup.center ↥L = ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹)
    (hTSC : GGTorusSignedEltSC p R) :
    hdRo7CLCoordAux_SignedData p Bs L := by
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hEab : IsElemAbelian p (Bs ⊓ L) := hdRo7CLCoordAux_inf_ab hH
  have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) :=
    hdRo7CLCoordAux_card_inf_ge p B Bs x L D J y K hH hZL hBsN hinner
  let e₁ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
  have hTSC_L : GGTorusSignedEltSC p ↥L :=
    ggTorusSignedEltSC_of_mulEquiv (e₁.symm.trans θ) hTSC
  exact hdRo7CLCoordAux_signedData_of_signedEltSC hBs hZL hBsN hinner hEab h3 hTSC_L

theorem hdRo7CLCoordAux_signedData_L_coprime
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (R : Type) [Group R]
    (I : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hTSC : GGTorusSignedEltSC p R) (hCP : GGCenterPrime p R)
    (hZR : Subgroup.center R = ⊥)
    (hOutdiag : GGOutdiagPrime p R I)
    (hperf : commutator ↥L = ⊤)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L))) :
    hdRo7CLCoordAux_SignedData p Bs L := by
  classical
  have hinner : ∀ b ∈ Bs, ∃ l ∈ L, ∀ z ∈ L, b * z * b⁻¹ = l * z * l⁻¹ :=
    hdRo7CLCoordAux_hinner_of_coprime hH R I θ hBsN hOutdiag hperf hBs3
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  let γ : ↥(Bs ⊓ L) →* ↥A :=
    { toFun := fun e => ⟨ggGamma L hBsN ⟨(e : G), e.2.1⟩,
          ⟨⟨(e : G), e.2.1⟩, rfl⟩⟩
      map_one' := Subtype.ext (map_one (ggGamma L hBsN))
      map_mul' := fun e f => Subtype.ext
        (map_mul (ggGamma L hBsN) ⟨(e : G), e.2.1⟩ ⟨(f : G), f.2.1⟩) }
  let γE : ↥(Bs ⊓ L) ≃* ↥A :=
    MulEquiv.ofBijective γ
      (hdRo7CLCoordAux_gamma_subgroupOf_bijective hH hcop hBsN hinner)
  obtain ⟨k, Θ, hk3, hW, hS, hP, hN⟩ :=
    hdRo7CLCoordAux_signedModelSC_data_of_outdiagPrime p B Bs x L D J y K hH hp3
      R I θ hBsN hTSC hCP hZR hOutdiag hperf hBs3
  let τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L) :=
    γE.symm.toMonoidHom.comp Θ.toMonoidHom
  have hΘτ : ∀ f, Θ f = γE (τT f) := fun f => (γE.apply_symm_apply (Θ f)).symm
  have hγE_conj : ∀ e : ↥(Bs ⊓ L),
      ((γE e : ↥A) : MulAut ↥L) = MulAut.conj (⟨(e : G), e.2.2⟩ : ↥L) := by
    intro e
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (((ggGamma L hBsN ⟨(e : G), e.2.1⟩) z : ↥L) : G) =
      ((MulAut.conj (⟨(e : G), e.2.2⟩ : ↥L) z : ↥L) : G)
    rw [ggGamma_coe, MulAut.conj_apply]
    rfl
  have hγconj : ∀ (u : ↥L) (e e' : ↥(Bs ⊓ L)),
      (u : G) * (e : G) * (u : G)⁻¹ = (e' : G) →
      (MulAut.conj u) * ((γE e : ↥A) : MulAut ↥L) * (MulAut.conj u)⁻¹ =
        ((γE e' : ↥A) : MulAut ↥L) := by
    intro u e e' he
    rw [hγE_conj e, hγE_conj e']
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact he
  have htransfer : ∀ (α : MulAut (Fin k → Multiplicative (ZMod p))) (n : ↥L)
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut ↥L))),
      ggConjAut A hn = MulAut.congr Θ α →
      ∀ f, (n : G) * (τT f : G) * (n : G)⁻¹ = (τT (α f) : G) := by
    intro α n hn hnΘ f
    let e : ↥(Bs ⊓ L) := τT f
    let e' : ↥(Bs ⊓ L) := τT (α f)
    have hΘe : ((Θ f : ↥A) : MulAut ↥L) =
        MulAut.conj (⟨(e : G), e.2.2⟩ : ↥L) := by
      rw [hΘτ f]
      exact hγE_conj e
    have hΘe' : ((Θ (α f) : ↥A) : MulAut ↥L) =
        MulAut.conj (⟨(e' : G), e'.2.2⟩ : ↥L) := by
      rw [hΘτ (α f)]
      exact hγE_conj e'
    have hmem : (n : G) * (e : G) * (n : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem n.2 e.2.2) (L.inv_mem n.2)
    have hleft : ((ggConjAut A hn (Θ f) : ↥A) : MulAut ↥L) =
        MulAut.conj (⟨(n : G) * (e : G) * (n : G)⁻¹, hmem⟩ : ↥L) := by
      rw [ggConjAut_apply, hΘe]
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have hright : ((ggConjAut A hn (Θ f) : ↥A) : MulAut ↥L) =
        MulAut.conj (⟨(e' : G), e'.2.2⟩ : ↥L) := by
      have h1 : (ggConjAut A hn (Θ f) : ↥A) = Θ (α f) := by
        simp only [hnΘ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [h1]
      exact hΘe'
    have hconjeq : MulAut.conj (⟨(e' : G), e'.2.2⟩ : ↥L) =
        MulAut.conj (⟨(n : G) * (e : G) * (n : G)⁻¹, hmem⟩ : ↥L) :=
      hright.symm.trans hleft
    have he'p : (⟨(e' : G), e'.2.2⟩ : ↥L) ^ p = 1 := by
      apply Subtype.ext
      exact hH.1.2.1.2.1.2 (e' : G) e'.2.1
    have hep : (⟨(n : G) * (e : G) * (n : G)⁻¹, hmem⟩ : ↥L) ^ p = 1 := by
      apply Subtype.ext
      have hepE : (e : G) ^ p = 1 := hH.1.2.1.2.1.2 (e : G) e.2.1
      calc ((n : G) * (e : G) * (n : G)⁻¹) ^ p
          = (n : G) * (e : G) ^ p * (n : G)⁻¹ := by
            exact (map_pow (MulAut.conj (n : G)) (e : G) p).symm
        _ = 1 := by rw [hepE, mul_one, mul_inv_cancel]
    have heqL := hdRo7CLCoordAux_conj_injective_on_p hcop he'p hep hconjeq
    exact (congrArg (fun l : ↥L => (l : G)) heqL).symm
  refine ⟨k, τT, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    apply Θ.injective
    have h := congrArg γE hfg
    simpa only [τT, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using h
  · intro e
    obtain ⟨f, hf⟩ := Θ.surjective (γE e)
    refine ⟨f, ?_⟩
    apply γE.injective
    rw [show γE (τT f) = Θ f from γE.apply_symm_apply (Θ f), hf]
  · intro i
    obtain ⟨n, hn, hnΘ⟩ := hS i
    exact ⟨n, htransfer (SpCoord.sgnAut i) n hn hnΘ⟩
  · intro σ
    obtain ⟨n, hn, hnΘ⟩ := hP σ
    exact ⟨n, htransfer (SpCoord.permAut σ) n hn hnΘ⟩
  · intro g hg
    have hmap : ∀ a ∈ A, (MulAut.conj g) * a * (MulAut.conj g)⁻¹ ∈ A := by
      intro a ha
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      obtain ⟨e', he'⟩ := hg (τT f)
      rw [← show ((Θ f : ↥A) : MulAut ↥L) = a from congrArg Subtype.val hf,
        hΘτ f, hγconj g (τT f) e' he']
      exact (γE e').2
    have hgnormA : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut ↥L)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hmap a ha
      · rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)).injective]
    obtain ⟨π, ε, hε, hrel⟩ := hN g hgnormA
    refine ⟨π, ε, hε, ?_⟩
    intro f f' hff' i
    have hff'γ : (MulAut.conj g) * ((Θ f : ↥A) : MulAut ↥L) *
        (MulAut.conj g)⁻¹ = ((Θ f' : ↥A) : MulAut ↥L) := by
      rw [hΘτ f, hΘτ f']
      exact hγconj g (τT f) (τT f') hff'
    have harg : ((MulAut.congr Θ).symm (ggConjAut A hgnormA)) f = f' := by
      apply Θ.injective
      change Θ (Θ.symm (ggConjAut A hgnormA (Θ f))) = Θ f'
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hff'γ
    have h := hrel f i
    rw [harg] at h
    exact h

end CFSG.StandardType.HdRo7C

end
