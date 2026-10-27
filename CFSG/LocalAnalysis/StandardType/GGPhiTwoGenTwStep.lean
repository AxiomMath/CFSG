module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwHyper
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwRow
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenStepOne

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def mulSubmodule {p r : ℕ} [Fact p.Prime] (V : Submodule (ZMod p) (Fin r → ZMod p)) :
    Subgroup (Multiplicative (Fin r → ZMod p)) where
  carrier := {x | x.toAdd ∈ V}
  one_mem' := V.zero_mem
  mul_mem' := fun {_ _} ha hb => V.add_mem ha hb
  inv_mem' := fun {_} ha => V.neg_mem ha

theorem mem_mulSubmodule {p r : ℕ} [Fact p.Prime] {V : Submodule (ZMod p) (Fin r → ZMod p)}
    {x : Multiplicative (Fin r → ZMod p)} : x ∈ mulSubmodule V ↔ x.toAdd ∈ V :=
  Iff.rfl

theorem card_mulSubmodule {p r : ℕ} [Fact p.Prime] (V : Submodule (ZMod p) (Fin r → ZMod p)) :
    Nat.card ↥(mulSubmodule V) = p ^ Module.finrank (ZMod p) V := by
  have h1 : Nat.card ↥(mulSubmodule V) = Nat.card ↥V :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun x => Iff.rfl))
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem pow_eq_one_of_multiplicative_zmod {p r : ℕ} (x : Multiplicative (Fin r → ZMod p)) :
    x ^ p = 1 := by
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul]
  have h0 : p • x.toAdd = 0 := by
    funext j
    show p • (x.toAdd j) = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [h0, ofAdd_zero]

theorem range_le_iSup_phiTwoCompIn_of_row
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {R : Subgroup (ModGL τ K)} (hR : R ≤ adjointGroup τ K)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* ↥R} (hTinj : Function.Injective T)
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) ((T (ofAdd t) : ↥R) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {X : Type} [Group X] [Finite X] {Ψ : X →* ↥R} (hΨ : Function.Injective Ψ)
    (hX : commutator X = ⊤) (hZ : ∀ z ∈ Subgroup.center X, z ^ p = 1 → z = 1)
    {Rw : Type} [Group Rw] {r' : ℕ} {I : Set (MulAut Rw)}
    (hrow : GGTorusRootGenAvoidKG p r' Rw I) (θ : X →* Rw) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center X) (hI : ∀ x : X, MulAut.conj (θ x) ∈ I)
    {VG W : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hVW : IsCompl VG W)
    (hVG : ∀ t ∈ VG, T (ofAdd t) ∈ Ψ.range)
    (hW : ∀ t ∈ W, ∀ x ∈ Ψ.range, x * T (ofAdd t) = T (ofAdd t) * x)
    (hr' : r' ≤ Module.finrank (ZMod p) VG) (h3 : 3 ≤ Module.finrank (ZMod p) VG) :
    Ψ.range ≤ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R g0 γ.1 := by
  classical
  have hp : p.Prime := Fact.out
  set VGm := mulSubmodule VG with hVGm
  let E : Subgroup X := (VGm.map T).comap Ψ
  have hTsub : VGm.map T ≤ Ψ.range := by
    rintro _ ⟨x, hx, rfl⟩
    have := hVG x.toAdd hx
    rwa [ofAdd_toAdd] at this
  have hEeq : E.map Ψ = VGm.map T := Subgroup.map_comap_eq_self hTsub
  have hcardE : Nat.card E = p ^ Module.finrank (ZMod p) VG := by
    have h1 : Nat.card (E.map Ψ) = Nat.card E := Subgroup.card_map_of_injective hΨ
    have h2 : Nat.card (VGm.map T) = Nat.card VGm := Subgroup.card_map_of_injective hTinj
    rw [← h1, hEeq, h2, card_mulSubmodule]
  have hmemE : ∀ x : X, x ∈ E ↔ ∃ t ∈ VG, Ψ x = T (ofAdd t) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
      exact ⟨y.toAdd, mem_mulSubmodule.mp hy, by rw [ofAdd_toAdd]; exact hyx.symm⟩
    · rintro ⟨t, ht, hxt⟩
      refine Subgroup.mem_comap.mpr ?_
      rw [hxt]
      exact ⟨ofAdd t, mem_mulSubmodule.mpr ht, rfl⟩
  have hEelem : CFSG.Open.IsElemAbelian p E := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨s, hs, has⟩ := (hmemE a.1).mp a.2
      obtain ⟨t, ht, hbt⟩ := (hmemE b.1).mp b.2
      refine Subtype.ext (hΨ ?_)
      show Ψ ((a : X) * (b : X)) = Ψ ((b : X) * (a : X))
      rw [map_mul, map_mul, has, hbt, ← map_mul T, ← map_mul T, mul_comm (ofAdd s) (ofAdd t)]
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := (hmemE x).mp hx
      have h1 : Ψ (x ^ p) = 1 := by
        rw [map_pow, hxt, ← map_pow, pow_eq_one_of_multiplicative_zmod, map_one]
      exact hΨ (by rw [h1, map_one])
  have hsc : ∀ g : X, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hgc hgp
    have hcommT : ∀ t : Fin τ.rank → ZMod p, Ψ g * T (ofAdd t) = T (ofAdd t) * Ψ g := by
      intro t
      have ht : t ∈ VG ⊔ W := by rw [hVW.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp ht
      obtain ⟨e, he⟩ := hVG v hv
      have heE : e ∈ E := (hmemE e).mpr ⟨v, hv, he⟩
      have h1 : Ψ g * T (ofAdd v) = T (ofAdd v) * Ψ g := by
        rw [← he, ← map_mul, ← map_mul, hgc e heE]
      have h2 : Ψ g * T (ofAdd w) = T (ofAdd w) * Ψ g := hW w hw (Ψ g) ⟨g, rfl⟩
      rw [ofAdd_add, map_mul]
      calc Ψ g * (T (ofAdd v) * T (ofAdd w)) = (Ψ g * T (ofAdd v)) * T (ofAdd w) := by
            rw [mul_assoc]
        _ = (T (ofAdd v) * Ψ g) * T (ofAdd w) := by rw [h1]
        _ = T (ofAdd v) * (Ψ g * T (ofAdd w)) := by rw [mul_assoc]
        _ = T (ofAdd v) * (T (ofAdd w) * Ψ g) := by rw [h2]
        _ = (T (ofAdd v) * T (ofAdd w)) * Ψ g := by rw [mul_assoc]
    set w : ModGL τ (AlgebraicClosure K) :=
      baseChangeGL (algebraMap K (AlgebraicClosure K)) ((Ψ g : ↥R) : ModGL τ K) with hwdef
    set y : ModGL τ (AlgebraicClosure K) := g0⁻¹ * w * g0 with hydef
    have hy_adj : y ∈ adjointGroup τ (AlgebraicClosure K) :=
      mul_mem (mul_mem (inv_mem hg0C)
        (CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup
          (algebraMap K (AlgebraicClosure K)) (hR (Ψ g).2))) hg0C
    have hy_comm : ∀ t : Fin τ.rank → ZMod p,
        y * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) =
          rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * y := by
      intro t
      set d : ModGL τ (AlgebraicClosure K) :=
        rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) with hd
      have hcommw : w * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : ↥R) : ModGL τ K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : ↥R) : ModGL τ K) * w := by
        have h2 := congrArg (fun z : ↥R =>
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K)) (hcommT t)
        simpa only [hwdef, map_mul, Subgroup.coe_mul] using h2
      have hXt : w * (g0 * d * g0⁻¹) = (g0 * d * g0⁻¹) * w := by
        rw [hd, ← hT t]
        exact hcommw
      calc y * d = g0⁻¹ * (w * (g0 * d * g0⁻¹)) * g0 := by
            rw [hydef]
            exact ggPhiTwoStep_conj_mul_assoc g0 w d
        _ = g0⁻¹ * ((g0 * d * g0⁻¹) * w) * g0 := by rw [hXt]
        _ = d * y := by
            rw [hydef]
            exact ggPhiTwoStep_conj_mul_conj g0 d w
    have hy_torus : y ∈ torusGroup τ (AlgebraicClosure K) :=
      mem_torusGroup_of_forall_commute_zetaVec hp2 hζo hζ hy_adj hy_comm
    have hg_pow : (Ψ g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hw_pow : w ^ p = 1 := by
      rw [hwdef, ← map_pow, ← Subgroup.coe_pow, hg_pow, Subgroup.coe_one, map_one]
    have hy_pow : y ^ p = 1 := by
      have hyw : y = (MulAut.conj g0⁻¹) w := by
        rw [hydef, MulAut.conj_apply, inv_inv]
      rw [hyw, ← map_pow, hw_pow, map_one]
    obtain ⟨t, ht⟩ := ggPhiTwoStep_exists_rootDiagUnit_zetaVec_eq_of_pow_eq_one hζo hζ hy_torus
      hy_pow
    have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) ((Ψ g : ↥R) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) ((T (ofAdd t) : ↥R) : ModGL τ K) := by
      rw [← hwdef, hT t, ← ht, hydef]
      group
    have hxT : Ψ g = T (ofAdd t) :=
      Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hbc)
    have htVW : t ∈ VG ⊔ W := by rw [hVW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨v, hv, w', hw', hvw⟩ := Submodule.mem_sup.mp htVW
    obtain ⟨e, he⟩ := hVG v hv
    have heE : e ∈ E := (hmemE e).mpr ⟨v, hv, he⟩
    have hsplit : T (ofAdd t) = T (ofAdd v) * T (ofAdd w') := by
      rw [← hvw, ofAdd_add, map_mul]
    have hTw : T (ofAdd w') = Ψ (e⁻¹ * g) := by
      rw [map_mul, map_inv, he, hxT, hsplit, inv_mul_cancel_left]
    have hcent : e⁻¹ * g = 1 := by
      refine hZ _ (Subgroup.mem_center_iff.mpr fun z => hΨ ?_) ?_
      · have hcz := hW w' hw' (Ψ z) ⟨z, rfl⟩
        rw [hTw, ← map_mul, ← map_mul] at hcz
        exact hcz
      · refine hΨ ?_
        rw [map_pow, ← hTw, ← map_pow, pow_eq_one_of_multiplicative_zmod, map_one, map_one]
    have hge : g = e := by
      have := congrArg (fun u => e * u) hcent
      simpa using this
    rw [hge]
    exact heE
  have hrE : p ^ r' ≤ Nat.card E := by
    rw [hcardE]
    exact Nat.pow_le_pow_right hp.pos hr'
  have h3E : p ^ 3 ≤ Nat.card E := by
    rw [hcardE]
    exact Nat.pow_le_pow_right hp.pos h3
  obtain ⟨ι, J, C, hCE, hCcard, hJperf, hJcent, hJgen⟩ :=
    exists_hyperplane_family_of_rootGenAvoidKG_central hp hrow θ hθ hker hX hZ hEelem hsc
      hI hrE h3E
  have hfinr : Module.finrank (ZMod p) VG + Module.finrank (ZMod p) W = τ.rank := by
    have := Submodule.finrank_add_eq_of_isCompl hVW
    simpa [Module.finrank_fin_fun] using this
  have hWcard : (W : Set (Fin τ.rank → ZMod p)).ncard = p ^ Module.finrank (ZMod p) W := by
    rw [← Nat.card_coe_set_eq, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    rfl
  have hhyp : ∀ i, ∃ V : Set (Fin τ.rank → ZMod p), V.ncard = p ^ (τ.rank - 1) ∧
      ∀ x ∈ (J i).map Ψ, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x := by
    intro i
    let Ci : Set (Fin τ.rank → ZMod p) := {t | t ∈ VG ∧ ∃ e ∈ C i, Ψ e = T (ofAdd t)}
    let V : Set (Fin τ.rank → ZMod p) := (fun q => q.1 + q.2) '' (Ci ×ˢ (W : Set _))
    refine ⟨V, ?_, ?_⟩
    · have hinj : Set.InjOn (fun q : (Fin τ.rank → ZMod p) × (Fin τ.rank → ZMod p) => q.1 + q.2)
          (Ci ×ˢ (W : Set _)) := by
        rintro ⟨c, w⟩ ⟨⟨hc, -⟩, hw⟩ ⟨c', w'⟩ ⟨⟨hc', -⟩, hw'⟩ hcw
        simp only at hcw
        have hmem1 : c - c' ∈ VG := VG.sub_mem hc hc'
        have hdiff : c - c' = w' - w := by linear_combination hcw
        have hmem2 : c - c' ∈ W := by
          rw [hdiff]
          exact W.sub_mem hw' hw
        have h0 : c - c' = 0 := (Submodule.disjoint_def.mp hVW.disjoint) _ hmem1 hmem2
        have hcc : c = c' := sub_eq_zero.mp h0
        have hww : w = w' := by
          rw [hcc] at hcw
          exact add_left_cancel hcw
        exact Prod.ext hcc hww
      have hCicard : Ci.ncard = p ^ (Module.finrank (ZMod p) VG - 1) := by
        have hg : Function.Injective (fun t : Fin τ.rank → ZMod p => T (ofAdd t)) :=
          fun a b hab => Multiplicative.ofAdd.injective (hTinj hab)
        have himg : (fun t : Fin τ.rank → ZMod p => T (ofAdd t)) '' Ci =
            (((C i).map Ψ : Subgroup ↥R) : Set ↥R) := by
          ext z
          constructor
          · rintro ⟨t, ⟨-, e, heC, hec⟩, rfl⟩
            exact ⟨e, heC, hec⟩
          · rintro ⟨e, heC, rfl⟩
            obtain ⟨t, ht, hΨe⟩ := (hmemE e).mp (hCE i heC)
            exact ⟨t, ⟨ht, e, heC, hΨe⟩, hΨe.symm⟩
        have h1 : Ci.ncard = (((C i).map Ψ : Subgroup ↥R) : Set ↥R).ncard := by
          rw [← himg, Set.ncard_image_of_injective _ hg]
        have h2 : (((C i).map Ψ : Subgroup ↥R) : Set ↥R).ncard = Nat.card (C i) := by
          rw [← Nat.card_coe_set_eq]
          exact Subgroup.card_map_of_injective hΨ
        have h3' : Nat.card (C i) = p ^ (Module.finrank (ZMod p) VG - 1) := by
          have h := hCcard i
          rw [hcardE] at h
          have hpow : p ^ Module.finrank (ZMod p) VG =
              p ^ (Module.finrank (ZMod p) VG - 1) * p := by
            obtain ⟨r0, hr0⟩ := Nat.exists_eq_succ_of_ne_zero
              (by omega : Module.finrank (ZMod p) VG ≠ 0)
            rw [hr0, Nat.succ_sub_one, pow_succ]
          rw [hpow] at h
          exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm
        rw [h1, h2, h3']
      show ((fun q : (Fin τ.rank → ZMod p) × (Fin τ.rank → ZMod p) => q.1 + q.2) ''
        (Ci ×ˢ (W : Set (Fin τ.rank → ZMod p)))).ncard = p ^ (τ.rank - 1)
      rw [(Set.ncard_image_iff (Set.toFinite _)).mpr hinj, Set.ncard_prod, hCicard, hWcard,
        ← pow_add]
      congr 1
      omega
    · rintro _ ⟨y, hy, rfl⟩ t ⟨⟨c, w⟩, ⟨⟨hcVG, e, heC, hec⟩, hwW⟩, rfl⟩
      simp only
      rw [ofAdd_add, map_mul, ← hec]
      have h1 : Ψ y * Ψ e = Ψ e * Ψ y := by rw [← map_mul, ← map_mul, hJcent i y hy e heC]
      have h2 : Ψ y * T (ofAdd w) = T (ofAdd w) * Ψ y := hW w hwW (Ψ y) ⟨y, rfl⟩
      calc Ψ y * (Ψ e * T (ofAdd w)) = (Ψ y * Ψ e) * T (ofAdd w) := by rw [mul_assoc]
        _ = (Ψ e * Ψ y) * T (ofAdd w) := by rw [h1]
        _ = Ψ e * (Ψ y * T (ofAdd w)) := by rw [mul_assoc]
        _ = Ψ e * (T (ofAdd w) * Ψ y) := by rw [h2]
        _ = (Ψ e * T (ofAdd w)) * Ψ y := by rw [mul_assoc]
  have hperf' : ∀ i, ⁅(J i).map Ψ, (J i).map Ψ⁆ = (J i).map Ψ := fun i => by
    rw [← Subgroup.map_commutator, hJperf i]
  have hfam := iSup_le_iSup_phiTwoCompIn_of_hyperplane_family hτ hp2 hg0C hζo hζ hR hT
    (fun i => (J i).map Ψ) hperf' hhyp
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ ⨆ i, J i := by
    rw [hJgen]
    exact Subgroup.mem_top x
  have hxm : Ψ x ∈ (⨆ i, J i).map Ψ := Subgroup.mem_map_of_mem Ψ hx
  rw [Subgroup.map_iSup] at hxm
  exact hfam hxm

end CFSG.StandardType.PhiTwoRootGen

end
