module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitAltNatural
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open Orbit

namespace Core6

@[expose] def FixesOut (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∃ m : Fin 6 → ZMod 2, (∑ i, m i) = 0 ∧ m ≠ 0 ∧ m ≠ (fun _ => 1) ∧ ∀ i, m (σ⁻¹ i) = m i

instance : DecidablePred FixesOut := fun σ => by unfold FixesOut; infer_instance

@[expose] def SmallComm (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∀ u : Fin 6 → ZMod 2, (Finset.univ.filter (fun i => u (σ⁻¹ i) + u i ≠ 0)).card ≤ 2

instance : DecidablePred SmallComm := fun σ => by unfold SmallComm; infer_instance

@[expose] def InComm (σ : Equiv.Perm (Fin 6)) (m : Fin 6 → ZMod 2) : Prop :=
  ∃ u : Fin 6 → ZMod 2, (∑ i, u i) = 0 ∧ ∀ i, u (σ⁻¹ i) + u i = m i

instance (σ : Equiv.Perm (Fin 6)) : DecidablePred (InComm σ) := fun m => by
  unfold InComm; infer_instance

theorem smallComm_of_fixesOut : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 → σ ≠ 1 → FixesOut σ →
    SmallComm σ := by
  decide +kernel

theorem exists_cycle : ∀ m : Fin 6 → ZMod 2,
    (Finset.univ.filter (fun i => m i ≠ 0)).card = 2 →
    ∃ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ σ ^ 3 = 1 ∧ σ ≠ 1 ∧ FixesOut σ ∧
      InComm σ m := by
  decide +kernel

theorem exists_moved : ∀ σ : Equiv.Perm (Fin 6), σ ≠ 1 →
    ∃ m : Fin 6 → ZMod 2, (∑ i, m i) = 0 ∧ ∃ i, m (σ⁻¹ i) ≠ m i := by
  decide +kernel

section Coord

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
  {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
  {β : ↥(⊤ : Subgroup V) →* ↥(altCoreModel 6).sec ⧸
    (altCoreModel 6).ker.subgroupOf (altCoreModel 6).sec}

theorem mk_inj {a b : ↥(altCoreModel 6).sec}
    (h : (QuotientGroup.mk a : ↥(altCoreModel 6).sec ⧸
      (altCoreModel 6).ker.subgroupOf (altCoreModel 6).sec) = QuotientGroup.mk b) :
    a = b := by
  have h1 := QuotientGroup.eq.1 h
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (a⁻¹ * b).1 = 1 := h1
  exact inv_mul_eq_one.mp (Subtype.ext h2)

abbrev toP (a : ↥(altCoreModel 6).sec) : G6.PermMod 6 := a.1

theorem coord_act (hR : RealizesBy (altCoreModel 6) H ⊤ ⊥ π β)
    (γ : ↥(alternatingGroup (Fin 6))) (v : V) (m : ↥(altCoreModel 6).sec)
    (hv : coordOf β v = QuotientGroup.mk m) :
    coordOf β (((π γ : ↥H) : MulAut V) v) =
      QuotientGroup.mk ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) (toP m),
        G6.permAct_mem_coreMod _ m.2⟩ :=
  coordOf_act hR γ v m hv

theorem coord_fixed (hR : RealizesBy (altCoreModel 6) H ⊤ ⊥ π β) {w : V} (hwH : w ∈ fixV H)
    (hw1 : w ≠ 1) {m : ↥(altCoreModel 6).sec} (hm : coordOf β w = QuotientGroup.mk m) :
    m.1 = G6.allOnes 6 := by
  have hc := altCore_choose_fixed (n := 6) (by norm_num) hR hwH hm
  have hm1 : m.1 ≠ 1 := by
    intro h0
    apply hw1
    apply coordOf_injective hR
    rw [hm, coordOf_one]
    have : m = 1 := Subtype.ext h0
    rw [this]
    rfl
  obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod (n := 6) m.2 hm1
  apply wtP_eq_self_iff.1
  have : wtP (n := 6) m.1 = 2 ∨ wtP (n := 6) m.1 = 4 ∨ wtP (n := 6) m.1 = 6 := by omega
  rcases this with h | h | h
  · rw [h] at hc
    exact absurd hc (by decide)
  · rw [h] at hc
    exact absurd hc (by decide)
  · exact h

theorem eq_one_of_pi_eq_one (hR : RealizesBy (altCoreModel 6) H ⊤ ⊥ π β)
    {γ : ↥(alternatingGroup (Fin 6))} (hγ : π γ = 1) : γ = 1 := by
  by_contra hne
  obtain ⟨m, hm0, i, hi⟩ := Core6.exists_moved γ.1 fun h0 => hne (Subtype.ext h0)
  have hmS : Multiplicative.ofAdd m ∈ (altCoreModel 6).sec := hm0
  obtain ⟨w, hw⟩ := coordOf_surjective hR (QuotientGroup.mk ⟨Multiplicative.ofAdd m, hmS⟩)
  have h1 := coord_act hR γ w ⟨Multiplicative.ofAdd m, hmS⟩ hw
  rw [hγ] at h1
  have h2 : coordOf β w = _ := h1
  rw [hw] at h2
  have h3 := congrArg (fun a : ↥(altCoreModel 6).sec => Multiplicative.toAdd a.1 i) (mk_inj h2)
  exact hi h3.symm

theorem coordOf_inv' (v : V) : coordOf β v⁻¹ = (coordOf β v)⁻¹ := by
  rw [coordOf, coordOf, ← map_inv]
  rfl

theorem toAdd_permAct_mul_inv (σ : Equiv.Perm (Fin 6)) (u : G6.PermMod 6) (i : Fin 6) :
    Multiplicative.toAdd (G6.permAct 6 σ u * u⁻¹) i =
      Multiplicative.toAdd u (σ⁻¹ i) + Multiplicative.toAdd u i := by
  change Multiplicative.toAdd u (σ⁻¹ i) + (-Multiplicative.toAdd u) i = _
  have key : ∀ a b : ZMod 2, a + -b = a + b := by decide
  exact key _ _

theorem apply_z (hR : RealizesBy (altCoreModel 6) H ⊤ ⊥ π β) {z : V} (hz1 : z ≠ 1)
    (hzH : z ∈ fixV H) {x : MulAut V} (hx : x ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    x z = z := by
  have hconj : ∀ h ∈ H, x⁻¹ * h * x ∈ H := by
    intro h hh
    refine (Subgroup.mem_normalizer_iff.mp hx _).mpr ?_
    have e : x * (x⁻¹ * h * x) * x⁻¹ = h := by group
    rw [e]
    exact hh
  have h1 : x z ∈ fixV H := by
    intro h hh
    have h2 := hzH _ (hconj h hh)
    have h3 : x⁻¹ (h (x z)) = z := h2
    calc h (x z) = x (x⁻¹ (h (x z))) := by simp
      _ = x z := by rw [h3]
  have h3 : x z ≠ 1 := fun h0 => hz1 (x.injective (h0.trans (map_one x).symm))
  obtain ⟨mz, hmz⟩ := QuotientGroup.mk_surjective (coordOf β z)
  obtain ⟨mxz, hmxz⟩ := QuotientGroup.mk_surjective (coordOf β (x z))
  have e1 := coord_fixed hR hzH hz1 hmz.symm
  have e2 := coord_fixed hR h1 h3 hmxz.symm
  apply coordOf_injective hR
  rw [← hmz, ← hmxz]
  congr 1
  exact Subtype.ext (e2.trans e1.symm)

theorem wt_two_of_normalizer (hR : RealizesBy (altCoreModel 6) H ⊤ ⊥ π β) {z : V} (hz1 : z ≠ 1)
    (hzH : z ∈ fixV H) {x : MulAut V} (hx : x ∈ Subgroup.normalizer (H : Set (MulAut V)))
    {v : V} {m m' : ↥(altCoreModel 6).sec} (hm : coordOf β v = QuotientGroup.mk m)
    (hm2 : wtP (n := 6) m.1 = 2) (hm' : coordOf β (x v) = QuotientGroup.mk m') :
    wtP (n := 6) m'.1 = 2 := by
  have hxz : x z = z := apply_z hR hz1 hzH hx
  have hcz : ∀ w : V, ∀ mw : ↥(altCoreModel 6).sec, coordOf β w = QuotientGroup.mk mw →
      mw.1 = G6.allOnes 6 → w = z := by
    intro w mw hw hmw
    obtain ⟨mz, hmz⟩ := QuotientGroup.mk_surjective (coordOf β z)
    have e1 := coord_fixed hR hzH hz1 hmz.symm
    apply coordOf_injective hR
    rw [hw, ← hmz]
    congr 1
    exact Subtype.ext (hmw.trans e1.symm)
  have hc1 : ∀ w : V, ∀ mw : ↥(altCoreModel 6).sec, coordOf β w = QuotientGroup.mk mw →
      mw.1 = 1 → w = 1 := by
    intro w mw hw hmw
    apply coordOf_injective hR
    rw [hw, coordOf_one]
    have : mw = 1 := Subtype.ext hmw
    rw [this]
    rfl
  obtain ⟨σ, hsign, hσ3, hσ1, ⟨m₁, hm₁s, hm₁0, hm₁1, hm₁fix⟩, ⟨u, hus, hu⟩⟩ :=
    Core6.exists_cycle (Multiplicative.toAdd m.1) hm2
  let γ : ↥(alternatingGroup (Fin 6)) := ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  have hγ3 : γ ^ 3 = 1 := Subtype.ext hσ3
  set h : MulAut V := ((π γ : ↥H) : MulAut V) with hhdef
  have hh3 : h ^ 3 = 1 := by
    rw [hhdef, ← Subgroup.coe_pow, ← map_pow, hγ3, map_one]
    rfl
  have hm₁S : Multiplicative.ofAdd m₁ ∈ (altCoreModel 6).sec := hm₁s
  obtain ⟨v₁, hv₁⟩ := coordOf_surjective hR (QuotientGroup.mk ⟨_, hm₁S⟩)
  have hhv₁ : h v₁ = v₁ := by
    apply coordOf_injective hR
    rw [hhdef, coord_act hR γ v₁ _ hv₁, hv₁]
    congr 1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact hm₁fix i
  have hv₁1 : v₁ ≠ 1 := by
    intro h0
    apply hm₁0
    have h1 : coordOf β v₁ = QuotientGroup.mk 1 := by rw [h0, coordOf_one]; rfl
    rw [hv₁] at h1
    have h2 := congrArg (fun a : ↥(altCoreModel 6).sec => Multiplicative.toAdd a.1) (mk_inj h1)
    exact h2
  have hv₁z : v₁ ≠ z := by
    intro h0
    apply hm₁1
    obtain ⟨mz, hmz⟩ := QuotientGroup.mk_surjective (coordOf β z)
    have e1 := coord_fixed hR hzH hz1 hmz.symm
    rw [← h0, hv₁] at hmz
    have h2 : mz.1 = Multiplicative.ofAdd m₁ := by rw [mk_inj hmz]
    have h3 : (Multiplicative.ofAdd m₁ : G6.PermMod 6) = G6.allOnes 6 := h2.symm.trans e1
    exact congrArg Multiplicative.toAdd h3
  have huS : Multiplicative.ofAdd u ∈ (altCoreModel 6).sec := hus
  obtain ⟨w₀, hw₀⟩ := coordOf_surjective hR (QuotientGroup.mk ⟨_, huS⟩)
  have hv : v = h w₀ * w₀⁻¹ := by
    apply coordOf_injective hR
    rw [coordOf_mul, coordOf_inv', hhdef, coord_act hR γ w₀ _ hw₀, hw₀, hm,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    show _ = Multiplicative.toAdd (G6.permAct 6 σ (Multiplicative.ofAdd u) *
      (Multiplicative.ofAdd u)⁻¹) i
    rw [toAdd_permAct_mul_inv]
    exact (hu i).symm
  have hv1 : v ≠ 1 := by
    intro h0
    have h1 : coordOf β v = QuotientGroup.mk 1 := by rw [h0, coordOf_one]; rfl
    rw [hm] at h1
    have h2 := mk_inj h1
    rw [h2] at hm2
    exact absurd hm2 (by decide)
  have hg : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hx h).mp (π γ).2
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(alternatingGroup (Fin 6)), π γ' = ⟨x * h * x⁻¹, hg⟩ :=
    hR.1 ⟨x * h * x⁻¹, hg⟩
  have hγ'g : ((π γ' : ↥H) : MulAut V) = x * h * x⁻¹ := congrArg Subtype.val hγ'
  have hγ'3 : γ' ^ 3 = 1 := by
    apply eq_one_of_pi_eq_one hR
    rw [map_pow, hγ']
    apply Subtype.ext
    show (x * h * x⁻¹) ^ 3 = 1
    rw [conj_pow, hh3, mul_one, mul_inv_cancel]
  have hγ'1 : γ' ≠ 1 := by
    intro h0
    apply hσ1
    have h1 : π γ = 1 := by
      apply Subtype.ext
      show h = 1
      have h2 : x * h * x⁻¹ = 1 := by rw [← hγ'g, h0, map_one]; rfl
      calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
        _ = 1 := by rw [h2]; group
    exact congrArg Subtype.val (eq_one_of_pi_eq_one hR h1)
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (coordOf β (x v₁))
  have hgx : (x * h * x⁻¹) (x v₁) = x v₁ := by
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, hhv₁]
  have hfix₂ : Core6.FixesOut (γ' : Equiv.Perm (Fin 6)) := by
    refine ⟨Multiplicative.toAdd m₂.1, m₂.2, ?_, ?_, ?_⟩
    · intro h0
      apply hv₁1
      have h1 := hc1 (x v₁) m₂ hm₂.symm (by
        apply Multiplicative.toAdd.injective
        exact h0)
      exact x.injective (h1.trans (map_one x).symm)
    · intro h0
      apply hv₁z
      have h1 := hcz (x v₁) m₂ hm₂.symm (by
        apply Multiplicative.toAdd.injective
        exact h0)
      exact x.injective (h1.trans hxz.symm)
    · intro i
      have h1 := coord_act hR γ' (x v₁) m₂ hm₂.symm
      rw [hγ'g, hgx, ← hm₂] at h1
      have h2 := mk_inj h1
      exact (congrArg (fun a : ↥(altCoreModel 6).sec => Multiplicative.toAdd a.1 i) h2).symm
  have hsmall := Core6.smallComm_of_fixesOut _ (congrArg Subtype.val hγ'3)
    (fun h0 => hγ'1 (Subtype.ext h0)) hfix₂
  obtain ⟨m₃, hm₃⟩ := QuotientGroup.mk_surjective (coordOf β (x w₀))
  have hxv : x v = (x * h * x⁻¹) (x w₀) * (x w₀)⁻¹ := by
    rw [hv, map_mul, map_inv]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  have hm'eq : m' = ⟨G6.permAct 6 (γ' : Equiv.Perm (Fin 6)) (toP m₃) * (toP m₃)⁻¹,
      (altCoreModel 6).sec.mul_mem (hR.2.2.2.2.2.1 γ' m₃.1 m₃.2) ((altCoreModel 6).sec.inv_mem
        m₃.2)⟩ := by
    apply mk_inj
    rw [← hm', hxv, coordOf_mul, coordOf_inv', ← hγ'g, coord_act hR γ' (x w₀) m₃ hm₃.symm,
      ← hm₃, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hle : wtP (n := 6) m'.1 ≤ 2 := by
    rw [hm'eq]
    have h1 := hsmall (Multiplicative.toAdd (toP m₃))
    have h2 : wtP (n := 6) (G6.permAct 6 (γ' : Equiv.Perm (Fin 6)) (toP m₃) * (toP m₃)⁻¹) =
        (Finset.univ.filter (fun i => Multiplicative.toAdd (toP m₃)
          ((γ' : Equiv.Perm (Fin 6))⁻¹ i) + Multiplicative.toAdd (toP m₃) i ≠ 0)).card := by
      unfold wtP hammingNorm
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [toAdd_permAct_mul_inv]
    rw [h2]
    exact h1
  have hm'1 : m'.1 ≠ 1 := by
    intro h0
    apply hv1
    have h1 := hc1 (x v) m' hm' h0
    exact x.injective (h1.trans (map_one x).symm)
  obtain ⟨⟨r, hr⟩, h0, -⟩ := wtP_mem_of_coreMod (n := 6) m'.2 hm'1
  omega

end Coord

end Core6

open Core6 in
theorem coreSixTwoCentral : CoreSixTwoCentral := by
  intro V _ _ H X S z hz1 hzH hH hHX hXN hS v hv1 hvz
  obtain ⟨π, β, hR⟩ := (realizes_iff (altCoreModel 6) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altCore_classFn (n := 6) (by norm_num)
  have horb := orbitAltCoreSix V H z hz1 hzH hH
  have hwt : ∀ w : V, w ≠ 1 → w ≠ z → ∀ mw : ↥(altCoreModel 6).sec,
      coordOf β w = QuotientGroup.mk mw → wtP (n := 6) mw.1 = 2 ∨ wtP (n := 6) mw.1 = 4 := by
    intro w hw1 hwz mw hmw
    have hmw1 : mw.1 ≠ 1 := by
      intro h0
      apply hw1
      apply coordOf_injective hR
      rw [hmw, coordOf_one]
      have : mw = 1 := Subtype.ext h0
      rw [this]
      rfl
    have hmwz : wtP (n := 6) mw.1 ≠ 6 := by
      intro h6
      apply hwz
      obtain ⟨mz, hmz⟩ := QuotientGroup.mk_surjective (coordOf β z)
      have e1 := coord_fixed hR hzH hz1 hmz.symm
      apply coordOf_injective hR
      rw [hmw, ← hmz]
      congr 1
      exact Subtype.ext ((wtP_eq_self_iff.1 h6).trans e1.symm)
    obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod (n := 6) mw.2 hmw1
    omega
  have hXorb : ∀ x ∈ X, ∀ w : V, w ≠ 1 → w ≠ z → ∃ h ∈ H, (h : MulAut V) w = x w := by
    intro x hx w hw1 hwz
    obtain ⟨mw, hmw⟩ := QuotientGroup.mk_surjective (coordOf β w)
    obtain ⟨mx, hmx⟩ := QuotientGroup.mk_surjective (coordOf β (x w))
    rw [exists_eq_iff_of_classFn (D := altCoreModel 6) (fun y : G6.PermMod 6 => wtP (n := 6) y)
      hR hker hact htrans hmw.symm hmx.symm]
    have hxw1 : x w ≠ 1 := fun h0 => hw1 (x.injective (h0.trans (map_one x).symm))
    have hxwz : x w ≠ z := fun h0 =>
      hwz (x.injective (h0.trans (apply_z hR hz1 hzH (hXN hx)).symm))
    rcases hwt w hw1 hwz mw hmw.symm with h2 | h4
    · show wtP (n := 6) mw.1 = wtP (n := 6) mx.1
      rw [h2, wt_two_of_normalizer hR hz1 hzH (hXN hx) hmw.symm h2 hmx.symm]
    · rcases hwt (x w) hxw1 hxwz mx hmx.symm with h2' | h4'
      · exfalso
        have h3 := wt_two_of_normalizer hR hz1 hzH (Subgroup.inv_mem _ (hXN hx)) hmx.symm h2'
          (by rw [MulAut.inv_apply_self]; exact hmw.symm)
        omega
      · show wtP (n := 6) mw.1 = wtP (n := 6) mx.1
        rw [h4, h4']
  have hvorb : Nat.card (orbitIn H v) = 15 := by
    have := horb.1 v hv1 hvz
    simpa using this
  have hOinv : ∀ s ∈ S, ∀ w ∈ orbitIn H v, (s : MulAut V) w ∈ orbitIn H v := by
    rintro s hs _ ⟨h, hh, rfl⟩
    have hw1 : (h : MulAut V) v ≠ 1 := fun h0 => hv1 (h.injective (h0.trans (map_one h).symm))
    have hwz : (h : MulAut V) v ≠ z := by
      intro h0
      apply hvz
      have h2 : (h⁻¹ : MulAut V) z = z := hzH _ (H.inv_mem hh)
      rw [← h0, MulAut.inv_apply_self] at h2
      exact h2.trans h0
    obtain ⟨h', hh', he⟩ := hXorb s (hS.1 hs) (h v) hw1 hwz
    exact ⟨h' * h, H.mul_mem hh' hh, by rw [MulAut.mul_apply, he]⟩
  let O : SubMulAction ↥S V :=
    { carrier := orbitIn H v
      smul_mem' := fun s w hw => hOinv s s.2 w hw }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hS.2.1.card_modEq_card_fixedPoints (α := O)
  have hcardO : Nat.card O = 15 := hvorb
  rw [hcardO] at h1
  have hne : Nat.card (MulAction.fixedPoints ↥S O) ≠ 0 := by
    intro h0
    rw [h0] at h1
    norm_num [Nat.ModEq] at h1
  obtain ⟨⟨⟨w, hwO⟩, hwfix⟩⟩ := (Nat.card_ne_zero.mp hne).1
  obtain ⟨h, hh, rfl⟩ := hwO
  refine ⟨h, hHX hh, fun s hs => ?_⟩
  have h2 := hwfix ⟨s, hs⟩
  exact congrArg Subtype.val h2


end CFSG.Quasithin.H13
