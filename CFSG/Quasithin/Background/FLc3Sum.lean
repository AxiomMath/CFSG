module

public import CFSG.Quasithin.Background.FLc3Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open CFSG.Open CFSG.Quasithin Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {V : Type} [CommGroup V]

theorem QI_one_ne_QI_last {n : ℕ} (hn : 3 ≤ n) : QI n {1} ≠ QI n {n - 1} := by
  intro h
  have h1 : QI n {1} ≤ QI n {n - 1} := h.le
  have := (QI_le_QI_iff (fun j hj => by
    rw [Set.mem_singleton_iff] at hj
    subst hj
    exact ⟨by omega, by omega⟩)).1 h1
  have h2 : n - 1 = 1 := Set.mem_singleton_iff.1 (this rfl)
  omega

namespace StSetting

variable {n : ℕ} {ρ : SLt n →* MulAut V} {Sst : Subgroup (MulAut V)} (h : StSetting n ρ Sst)

include h

theorem outer_of_not_mem (hn : 3 ≤ n) {s : MulAut V} (hs : s ∈ Sst) (hsU : s ∉ (Ut n).map ρ) :
    ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map (h.phi hs).toMonoidHom =
      stabilizer (flagSpace n (ZMod 2) (n - d)) := by
  rcases aut_dichotomy hn (h.phi hs) (h.phi_Ut (by omega) hs) with ⟨b, hb, hbφ⟩ | hout
  · exact absurd ⟨b, hb, (h.eq_rho_of_inner hs hb hbφ).symm⟩ hsU
  · exact hout

theorem phi_comp {s t : MulAut V} (hs : s ∈ Sst) (ht : t ∈ Sst) (y : SLt n) :
    h.phi (Sst.mul_mem hs ht) y = h.phi hs (h.phi ht y) := by
  apply h.inj
  rw [h.rho_phi, h.rho_phi, h.rho_phi]
  group

theorem inner_of_outer_mul (hn : 3 ≤ n) {s t : MulAut V} (hs : s ∈ Sst) (ht : t ∈ Sst)
    (hsU : s ∉ (Ut n).map ρ) (htU : t ∉ (Ut n).map ρ) : s⁻¹ * t ∈ (Ut n).map ρ := by
  by_contra hcU
  have hs' : s⁻¹ ∈ Sst := Sst.inv_mem hs
  have hs'U : s⁻¹ ∉ (Ut n).map ρ := fun hh => hsU (by simpa using (Subgroup.inv_mem _ hh))
  have hc : s⁻¹ * t ∈ Sst := Sst.mul_mem hs' ht
  have hout_c := h.outer_of_not_mem hn hc hcU 1 le_rfl (by omega)
  have hout_t := h.outer_of_not_mem hn ht htU 1 le_rfl (by omega)
  have hout_s := h.outer_of_not_mem hn hs' hs'U (n - 1) (by omega) (by omega)
  have hcomp : (h.phi hc).toMonoidHom = (h.phi hs').toMonoidHom.comp (h.phi ht).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    exact h.phi_comp hs' ht y
  have h1 : (stabilizer (flagSpace n (ZMod 2) 1)).map (h.phi hc).toMonoidHom =
      stabilizer (flagSpace n (ZMod 2) 1) := by
    rw [hcomp, ← Subgroup.map_map, hout_t, hout_s]
    have : n - (n - 1) = 1 := by omega
    rw [this]
  have h2 : stabilizer (flagSpace n (ZMod 2) 1) = stabilizer (flagSpace n (ZMod 2) (n - 1)) :=
    h1.symm.trans hout_c
  apply QI_one_ne_QI_last hn
  ext g
  simp only [mem_flagStabilizer, Set.mem_singleton_iff, forall_eq]
  rw [h2]

end StSetting

@[expose] def fstBasis (n : ℕ) (hn : 1 ≤ n) : Multiplicative (Vt n) :=
  Multiplicative.ofAdd (Pi.single (⟨0, hn⟩ : Fin n) 1)

theorem eq_e0_of_fixed {n : ℕ} (hn : 1 ≤ n) {x : Multiplicative (Vt n)} (hx : x ≠ 1)
    (hf : ∀ g ∈ Ut n, actM g x = x) : x = fstBasis n hn := by
  have hv : ∀ g ∈ Ut n, mat g *ᵥ Multiplicative.toAdd x = Multiplicative.toAdd x := fun g hg => by
    have := congrArg Multiplicative.toAdd (hf g hg)
    rwa [toAdd_actM] at this
  have hz := fixed_coord_zero hv
  apply Multiplicative.toAdd.injective
  funext b
  by_cases hb : (b : ℕ) = 0
  · have hb0 : b = ⟨0, hn⟩ := Fin.ext hb
    rw [hb0]
    have hne : Multiplicative.toAdd x ⟨0, hn⟩ ≠ 0 := by
      intro h0
      apply hx
      apply Multiplicative.toAdd.injective
      funext c
      by_cases hc : (c : ℕ) = 0
      · rw [show c = ⟨0, hn⟩ from Fin.ext hc]
        exact h0
      · exact hz c (by omega)
    show Multiplicative.toAdd x ⟨0, hn⟩ = (Pi.single (⟨0, hn⟩ : Fin n) (1 : ZMod 2) : Vt n) ⟨0, hn⟩
    rw [Pi.single_eq_same]
    revert hne
    generalize Multiplicative.toAdd x ⟨0, hn⟩ = c
    revert c
    decide
  · have hb' : b ≠ ⟨0, hn⟩ := fun h' => hb (by rw [h'])
    show Multiplicative.toAdd x b = (Pi.single (⟨0, hn⟩ : Fin n) (1 : ZMod 2) : Vt n) b
    rw [Pi.single_eq_of_ne hb', hz b (by omega)]

theorem exists_moved_e0 {n : ℕ} (hn : 2 ≤ n) : ∃ g : SLt n, actM g (fstBasis n (by omega)) ≠ fstBasis n (by omega) := by
  have h10 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := fun h' => by
    have := congrArg Fin.val h'
    simp at this
  refine ⟨Matrix.SpecialLinearGroup.transvection h10 (1 : ZMod 2), fun h' => ?_⟩
  have h2 := congrFun (congrArg Multiplicative.toAdd h') ⟨1, by omega⟩
  rw [toAdd_actM] at h2
  have hco : mat (Matrix.SpecialLinearGroup.transvection h10 (1 : ZMod 2) : SLt n) =
      1 + Matrix.single (⟨1, by omega⟩ : Fin n) ⟨0, by omega⟩ (1 : ZMod 2) :=
    Matrix.SpecialLinearGroup.transvection_coe h10 1
  rw [hco, mat_transv_mulVec_apply h10] at h2
  simp [fstBasis] at h2

namespace StSetting

variable {n : ℕ} {ρ : SLt n →* MulAut V} {Sst : Subgroup (MulAut V)} (h : StSetting n ρ Sst)

include h

theorem outer_moves (hn : 3 ≤ n) (hV2 : ∀ w : V, w ^ 2 = 1) {U₁ : Subgroup V}
    (D : VModel n ρ U₁ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a)) {u : V} (hu : u ∈ U₁)
    (hx : D.β ⟨u, hu⟩ ≠ 1) (hf : ∀ g ∈ Ut n, actM g (D.β ⟨u, hu⟩) = D.β ⟨u, hu⟩)
    {a : MulAut V} (ha : a ∈ Sst) (haU : a ∉ (Ut n).map ρ) : a u ≠ u := by
  intro hau
  have hinjβ : Function.Injective D.β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    have := D.ker w hw
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have huf : ∀ s ∈ Ut n, ρ s u = u := by
    intro s hs
    have h1 := D.equiv s ⟨u, hu⟩ (D.inv s u hu)
    have h1' : D.β ⟨ρ s u, D.inv s u hu⟩ = D.β ⟨u, hu⟩ := by
      rw [h1]
      exact hf s hs
    exact congrArg Subtype.val (hinjβ h1')
  set H : Subgroup (SLt n) := (MulAction.stabilizer (MulAut V) u).comap ρ with hH
  have hUH : Ut n ≤ H := fun s hs => huf s hs
  have hQ1 : QI n {1} ≤ H := fun x hx' =>
    fixQ_of_model D hV2 (by omega) (c := 1) (fun a ha i hi hic => fix_nat a ha i hi hic) hu huf x hx'
  have hout := h.outer_of_not_mem hn ha haU
  have hmapQ : (QI n {1}).map (h.phi ha).toMonoidHom = QI n {n - 1} := by
    ext g
    have h1 := hout 1 le_rfl (by omega)
    have e1 : ∀ d : ℕ, (QI n {d} : Subgroup (SLt n)) = stabilizer (flagSpace n (ZMod 2) d) := by
      intro d
      ext g'
      simp only [mem_flagStabilizer, Set.mem_singleton_iff, forall_eq]
    rw [e1, e1, ← h1]
  have hau' : a⁻¹ u = u := by
    have : a⁻¹ (a u) = a⁻¹ u := by rw [hau]
    rw [MulAut.inv_apply] at this ⊢
    simpa using this.symm
  have hmap : (QI n {1}).map (h.phi ha).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx', rfl⟩
    show (ρ (h.phi ha x)) u = u
    rw [h.rho_phi]
    have h2 : (ρ x) u = u := hQ1 hx'
    show a (ρ x (a⁻¹ u)) = u
    rw [hau', h2, hau]
  have hQ1' : QI n {n - 1} ≤ H := by
    rw [← hmapQ]
    exact hmap
  have hHtop : H = ⊤ := by
    have hcutsH := eq_QI_cuts hUH
    have hc1 : cuts H ⊆ {1} := by
      have := (le_iff_cuts (Ut_le_QI n {1}) hUH).1 hQ1
      rwa [cuts_QI (fun i hi => by
        rw [Set.mem_singleton_iff] at hi
        subst hi
        exact ⟨le_rfl, by omega⟩)] at this
    have hc2 : cuts H ⊆ {n - 1} := by
      have := (le_iff_cuts (Ut_le_QI n {n - 1}) hUH).1 hQ1'
      rwa [cuts_QI (fun i hi => by
        rw [Set.mem_singleton_iff] at hi
        subst hi
        exact ⟨by omega, by omega⟩)] at this
    have hempty : cuts H = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      have h1 := Set.mem_singleton_iff.1 (hc1 hi)
      have h2 := Set.mem_singleton_iff.1 (hc2 hi)
      omega
    rw [hcutsH, hempty]
    ext g
    simp
  obtain ⟨g, hg⟩ := exists_moved_e0 (by omega : 2 ≤ n)
  have hxe : D.β ⟨u, hu⟩ = fstBasis n (by omega) := eq_e0_of_fixed (by omega) hx hf
  have h1 := D.equiv g ⟨u, hu⟩ (D.inv g u hu)
  have hρg : ρ g u = u := by
    have : g ∈ H := hHtop ▸ Subgroup.mem_top g
    exact this
  have e : (⟨ρ g u, D.inv g u hu⟩ : ↥U₁) = ⟨u, hu⟩ := Subtype.ext hρg
  rw [e, hxe] at h1
  exact hg h1.symm

end StSetting

namespace VModel

variable {n : ℕ} {ρ : SLt n →* MulAut V} {U' : Subgroup V} {X : Type} [CommGroup X]
  {act : SLt n → X → X} (D : VModel n ρ U' ⊥ X act)

include D

theorem β_injective : Function.Injective D.β := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  have := D.ker w hw
  rw [Subgroup.mem_bot] at this
  exact Subtype.ext this

end VModel

theorem actM_e0_fixed {n : ℕ} (hn : 1 ≤ n) : ∀ g ∈ Ut n, actM g (fstBasis n hn) = fstBasis n hn := by
  intro g hg
  apply Multiplicative.toAdd.injective
  rw [toAdd_actM]
  funext b
  show (mat g *ᵥ (Pi.single (⟨0, hn⟩ : Fin n) (1 : ZMod 2) : Vt n)) b = _
  rw [Matrix.mulVec_single_one]
  by_cases hb : b = ⟨0, hn⟩
  · rw [hb]
    simp [fstBasis, hg.2 ⟨0, hn⟩]
  · have : (⟨0, hn⟩ : Fin n) < b := by
      rw [Fin.lt_def]
      have : (b : ℕ) ≠ 0 := fun h' => hb (Fin.ext h')
      show 0 < (b : ℕ)
      omega
    simp [fstBasis, hg.1 b ⟨0, hn⟩ this, Pi.single_eq_of_ne hb]

theorem e0_ne_one {n : ℕ} (hn : 1 ≤ n) : fstBasis n hn ≠ 1 := by
  intro h'
  have := congrFun (congrArg Multiplicative.toAdd h') ⟨0, hn⟩
  simp [fstBasis] at this

namespace StSetting

variable {n : ℕ} {ρ : SLt n →* MulAut V} {Sst : Subgroup (MulAut V)} (h : StSetting n ρ Sst)

include h

theorem outer_inf_eq_bot (hn : 3 ≤ n) (hV2 : ∀ w : V, w ^ 2 = 1) [Finite V] {U₁ : Subgroup V}
    (D : VModel n ρ U₁ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a)) {u : V} (hu : u ∈ U₁)
    (hx : D.β ⟨u, hu⟩ ≠ 1) (hf : ∀ g ∈ Ut n, actM g (D.β ⟨u, hu⟩) = D.β ⟨u, hu⟩)
    {a : MulAut V} (ha : a ∈ Sst) (haU : a ∉ (Ut n).map ρ) : U₁ ⊓ U₁.map a.toMonoidHom = ⊥ := by
  by_contra hne
  have hinjβ := D.β_injective
  have hmoves := h.outer_moves hn hV2 D hu hx hf ha haU
  have huf : ∀ s ∈ Ut n, ρ s u = u := by
    intro s hs
    have h1 := D.equiv s ⟨u, hu⟩ (D.inv s u hu)
    have h1' : D.β ⟨ρ s u, D.inv s u hu⟩ = D.β ⟨u, hu⟩ := by
      rw [h1]
      exact hf s hs
    exact congrArg Subtype.val (hinjβ h1')
  set W : Subgroup V := U₁ ⊓ U₁.map a.toMonoidHom with hW
  have hs' : a⁻¹ ∈ Sst := Sst.inv_mem ha
  have hWinv : ∀ g : SLt n, ∀ w ∈ W, (ρ g) w ∈ W := by
    intro g w ⟨hw1, hw2⟩
    refine ⟨D.inv g w hw1, ?_⟩
    obtain ⟨u', hu', rfl⟩ := hw2
    refine ⟨ρ (h.phi hs' g) u', D.inv _ u' hu', ?_⟩
    rw [h.rho_phi hs']
    show a ((a⁻¹ * ρ g * a⁻¹⁻¹) u') = ρ g (a u')
    simp [MulAut.mul_apply]
  obtain ⟨w₀, hw₀U, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨w.1, w.2, fun h' => hw (Subtype.ext h')⟩
  set X : Subgroup (Multiplicative (Vt n)) := (W.subgroupOf U₁).map D.β with hX
  have hXinv : SInvG (Ut n) X := by
    intro q hq x hx'
    obtain ⟨w, hw, rfl⟩ := hx'
    have h1 := D.equiv q w (D.inv q w w.2)
    refine ⟨⟨ρ q (w : V), D.inv q w w.2⟩, ?_, ?_⟩
    · exact hWinv q w hw
    · rw [h1]
      rfl
  have hXne : X ≠ ⊥ := by
    intro hXb
    have h1 : D.β ⟨w₀, hw₀U.1⟩ ∈ X := ⟨⟨w₀, hw₀U.1⟩, hw₀U, rfl⟩
    rw [hXb, Subgroup.mem_bot] at h1
    exact hw₀1 (congrArg Subtype.val (hinjβ (h1.trans (map_one D.β).symm)))
  have hpg : IsPGroup 2 (Multiplicative (Vt n)) := by
    apply IsPGroup.of_card (n := n)
    exact card_multiplicative_Vt n
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 (hpg.to_subgroup X))
  have hXY := eq_Yk_of_Ut_invariant hXinv hk
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, pow_zero, Subgroup.card_eq_one] at hk
    exact hXne hk
  have he0 : fstBasis n (by omega) ∈ X := by
    rw [hXY, mem_Yk]
    intro j hj
    have : j ≠ ⟨0, by omega⟩ := fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega
    simp [fstBasis, Pi.single_eq_of_ne this]
  obtain ⟨w, hw, hwe⟩ := he0
  have hxe : D.β ⟨u, hu⟩ = fstBasis n (by omega) := eq_e0_of_fixed (by omega) hx hf
  have hwu : w = ⟨u, hu⟩ := hinjβ (hwe.trans hxe.symm)
  have huW : u ∈ W := by
    have := hw
    rw [hwu] at this
    exact this
  obtain ⟨u'', hu''U, hu''a⟩ := huW.2
  have hau'' : a u'' = u := hu''a
  have hu''eq : u'' = a⁻¹ u := by
    rw [← hau'']
    show u'' = a⁻¹ (a u'')
    simp
  have hu''f : ∀ s ∈ Ut n, ρ s u'' = u'' := by
    intro s hs
    have hφ : h.phi ha s ∈ Ut n := by
      have : h.phi ha s ∈ (Ut n).map (h.phi ha).toMonoidHom := ⟨s, hs, rfl⟩
      rw [h.phi_Ut (by omega) ha] at this
      exact this
    have h1 : a (ρ s u'') = a u'' := by
      have e := h.rho_phi ha s
      have := huf _ hφ
      rw [e] at this
      calc a (ρ s u'') = (a * ρ s * a⁻¹) (a u'') := by simp [MulAut.mul_apply]
        _ = u := by rw [hau'']; exact this
        _ = a u'' := hau''.symm
    exact a.injective h1
  have hu''1 : u'' ≠ 1 := by
    intro h'
    rw [h', map_one] at hau''
    apply hx
    have : u = 1 := hau''.symm
    subst this
    exact (by
      have : (⟨(1 : V), hu⟩ : ↥U₁) = 1 := rfl
      rw [this, map_one])
  have hβu'' : D.β ⟨u'', hu''U⟩ = fstBasis n (by omega) := by
    apply eq_e0_of_fixed (by omega)
    · intro h'
      apply hu''1
      exact congrArg Subtype.val (hinjβ (h'.trans (map_one D.β).symm))
    · intro g hg
      have h1 := D.equiv g ⟨u'', hu''U⟩ (D.inv g u'' hu''U)
      have e : (⟨ρ g u'', D.inv g u'' hu''U⟩ : ↥U₁) = ⟨u'', hu''U⟩ := Subtype.ext (hu''f g hg)
      rw [e] at h1
      exact h1.symm
  have : (⟨u'', hu''U⟩ : ↥U₁) = ⟨u, hu⟩ := hinjβ (hβu''.trans hxe.symm)
  have hu''u : u'' = u := congrArg Subtype.val this
  apply hmoves
  calc a u = a u'' := by rw [hu''u]
    _ = u := hau''

end StSetting

theorem not_ff_sum_any [Finite V] {m : ℕ} (hm : 1 ≤ m) {ρ : SLt (m + 2) →* MulAut V}
    {Sst : Subgroup (MulAut V)} (h : StSetting (m + 2) ρ Sst) (hV2 : ∀ w : V, w ^ 2 = 1)
    {U₁ U₂ : Subgroup V} (hdisj : U₁ ⊓ U₂ = ⊥)
    (D₁ : VModel (m + 2) ρ U₁ ⊥ (Multiplicative (Vt (m + 2))) (fun g a => actM g a))
    (D₂ : VModel (m + 2) ρ U₂ ⊥ (Multiplicative (Vt (m + 2))) actDl)
    {Q : Subgroup (MulAut V)} (hQS : Q ≤ Sst)
    (hnormQ : ∀ x ∈ QI (m + 2) {1, m + 1}, ∀ a ∈ Q, ρ x * a * (ρ x)⁻¹ ∈ Q)
    {A : Subgroup (MulAut V)} (hAQ : A ≤ Q) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixV A) < Nat.card V := by
  have hn3 : 3 ≤ m + 2 := by omega
  have hinner : ∀ A' : Subgroup (MulAut V), A' ≤ Q → A' ≤ (Ut (m + 2)).map ρ → A' ≠ ⊥ →
      Nat.card A' * Nat.card (fixV A') < Nat.card V := by
    intro A' hA'Q hA'U hA'
    have hQin : Q ⊓ (Ut (m + 2)).map ρ ≤ (Ut (m + 2)).map ρ := inf_le_right
    have hnorm : ∀ x ∈ QI (m + 2) {1, m + 1}, ∀ a ∈ Q ⊓ (Ut (m + 2)).map ρ,
        ρ x * a * (ρ x)⁻¹ ∈ Q ⊓ (Ut (m + 2)).map ρ := by
      intro x hx a ha
      refine ⟨hnormQ x hx a ha.1, ?_⟩
      obtain ⟨u, hu, rfl⟩ := ha.2
      have hmem : ρ x * ρ u * (ρ x)⁻¹ = ρ (x * u * x⁻¹) := by simp [map_mul, map_inv]
      have hSst : ρ (x * u * x⁻¹) ∈ Sst := by
        rw [← hmem]
        exact hQS (hnormQ x hx _ ha.1)
      refine ⟨x * u * x⁻¹, h.inter (by omega) hSst, hmem.symm⟩
    exact not_ff_of_radical h.inj hQin hnorm
      (fun A'' hU hR hne => not_ff_sum h.inj hdisj D₁ D₂ A'' hU hR hne)
      (le_inf hA'Q hA'U) hA'
  by_cases hin : A ≤ (Ut (m + 2)).map ρ
  · exact hinner A hAQ hin hA
  ·
    obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ (Ut (m + 2)).map ρ := by
      by_contra hcon
      push Not at hcon
      exact hin hcon
    have haS : a ∈ Sst := hQS (hAQ haA)
    set A₀ : Subgroup (MulAut V) := A ⊓ (Ut (m + 2)).map ρ with hA₀
    have hidx : Nat.card A ≤ 2 * Nat.card A₀ := by
      classical
      let g₁ : ↥A → MulAut V := fun b =>
        if (b : MulAut V) ∈ (Ut (m + 2)).map ρ then (b : MulAut V) else a⁻¹ * b
      have hg₁ : ∀ b : ↥A, g₁ b ∈ A₀ := by
        intro b
        by_cases hb : (b : MulAut V) ∈ (Ut (m + 2)).map ρ
        · have e : g₁ b = b := by simp only [g₁, hb, ↓reduceIte]
          rw [e]
          exact ⟨b.2, hb⟩
        · have e : g₁ b = a⁻¹ * b := by simp only [g₁, hb, ↓reduceIte]
          rw [e]
          exact ⟨A.mul_mem (A.inv_mem haA) b.2,
            h.inner_of_outer_mul hn3 haS (hQS (hAQ b.2)) haU hb⟩
      have hinj : Function.Injective (fun b : ↥A =>
          ((⟨g₁ b, hg₁ b⟩ : ↥A₀), decide ((b : MulAut V) ∈ (Ut (m + 2)).map ρ))) := by
        intro b b' hbb
        have h1 : g₁ b = g₁ b' := congrArg (fun z : ↥A₀ × Bool => (z.1 : MulAut V)) hbb
        have h2 : decide ((b : MulAut V) ∈ (Ut (m + 2)).map ρ) =
            decide ((b' : MulAut V) ∈ (Ut (m + 2)).map ρ) := congrArg Prod.snd hbb
        by_cases hb : (b : MulAut V) ∈ (Ut (m + 2)).map ρ <;>
          by_cases hb' : (b' : MulAut V) ∈ (Ut (m + 2)).map ρ
        · have e1 : g₁ b = b := by simp only [g₁, hb, ↓reduceIte]
          have e2 : g₁ b' = b' := by simp only [g₁, hb', ↓reduceIte]
          exact Subtype.ext (e1.symm.trans (h1.trans e2))
        · simp [hb, hb'] at h2
        · simp [hb, hb'] at h2
        · have e1 : g₁ b = a⁻¹ * b := by simp only [g₁, hb, ↓reduceIte]
          have e2 : g₁ b' = a⁻¹ * b' := by simp only [g₁, hb', ↓reduceIte]
          exact Subtype.ext (mul_left_cancel (e1.symm.trans (h1.trans e2)))
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
      omega
    obtain ⟨u', hu'⟩ := D₁.surj (fstBasis (m + 2) (by omega))
    set u : V := (u' : V) with hu
    have huU : u ∈ U₁ := u'.2
    have hβu : D₁.β ⟨u, huU⟩ = fstBasis (m + 2) (by omega) := hu'
    have hx : D₁.β ⟨u, huU⟩ ≠ 1 := by rw [hβu]; exact e0_ne_one _
    have hf : ∀ g ∈ Ut (m + 2), actM g (D₁.β ⟨u, huU⟩) = D₁.β ⟨u, huU⟩ := by
      intro g hg
      rw [hβu]
      exact actM_e0_fixed _ g hg
    have hmoves := h.outer_moves hn3 hV2 D₁ huU hx hf haS haU
    have huf : ∀ s ∈ Ut (m + 2), ρ s u = u := by
      intro s hs
      have h1 := D₁.equiv s ⟨u, huU⟩ (D₁.inv s u huU)
      have h1' : D₁.β ⟨ρ s u, D₁.inv s u huU⟩ = D₁.β ⟨u, huU⟩ := by
        rw [h1]
        exact hf s hs
      exact congrArg Subtype.val (D₁.β_injective h1')
    by_cases hA₀b : A₀ = ⊥
    ·
      have hcardA₀ : Nat.card A₀ = 1 := by rw [hA₀b, Subgroup.card_bot]
      have hAle : Nat.card A ≤ 2 := by omega
      have hinfbot := h.outer_inf_eq_bot hn3 hV2 D₁ huU hx hf haS haU
      have hCU : fixV A ⊓ U₁ = ⊥ := by
        rw [eq_bot_iff, ← hinfbot]
        intro v hv
        exact ⟨hv.2, ⟨v, hv.2, hv.1 a haA⟩⟩
      have h0 := card_mul_card_le_inf U₁ (fixV A)
      rw [hCU, Subgroup.card_bot, mul_one] at h0
      have hU1 : Nat.card U₁ = 2 ^ (m + 2) := by
        rw [← card_multiplicative_Vt (m + 2)]
        exact Nat.card_congr (Equiv.ofBijective D₁.β ⟨D₁.β_injective, D₁.surj⟩)
      have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
      have h8 : 8 ≤ 2 ^ (m + 2) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hU1] at h0
      nlinarith
    ·
      have hA₀Q : A₀ ≤ Q := inf_le_left.trans hAQ
      have hA₀U : A₀ ≤ (Ut (m + 2)).map ρ := inf_le_right
      have hin₀ := hinner A₀ hA₀Q hA₀U hA₀b
      have hle : fixV A ≤ fixV A₀ := fun v hv b hb => hv b hb.1
      have hu₀ : u ∈ fixV A₀ := by
        intro b hb
        obtain ⟨s, hs, rfl⟩ := hb.2
        exact huf s hs
      have hlt : fixV A < fixV A₀ := by
        refine lt_of_le_of_ne hle fun heq => ?_
        have : u ∈ fixV A := heq ▸ hu₀
        exact hmoves (this a haA)
      have h2 : 2 * Nat.card (fixV A) ≤ Nat.card (fixV A₀) := by
        obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
        have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
        have hk1 : k ≠ 1 := by
          rintro rfl
          rw [mul_one] at hk
          exact absurd (Subgroup.eq_of_le_of_card_ge hle hk.le) hlt.ne
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hk
          exact absurd hk (Nat.card_pos (α := fixV A₀)).ne'
        rw [hk]
        have : 2 ≤ k := by omega
        calc 2 * Nat.card (fixV A) ≤ k * Nat.card (fixV A) := Nat.mul_le_mul_right _ this
          _ = Nat.card (fixV A) * k := by ring
      calc Nat.card A * Nat.card (fixV A) ≤ (2 * Nat.card A₀) * Nat.card (fixV A) :=
            Nat.mul_le_mul_right _ hidx
        _ = Nat.card A₀ * (2 * Nat.card (fixV A)) := by ring
        _ ≤ Nat.card A₀ * Nat.card (fixV A₀) := Nat.mul_le_mul_left _ h2
        _ < Nat.card V := hin₀

end CFSG.Quasithin.FLc
