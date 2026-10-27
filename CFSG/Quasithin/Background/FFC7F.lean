module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.Quasithin.Background.FFC7D

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5 Equiv Equiv.Perm
open scoped commutatorElement

namespace B510

section Finite5

@[expose] def e01 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

@[expose] def e23 : Fin 5 → ZMod 2 := ![0, 0, 1, 1, 0]

theorem fixed_of_stab : ∀ v : Fin 5 → ZMod 2,
    (∑ i, v i = 0 ∧ ∀ σ : Perm (Fin 5), (sign σ = 1 ∧ ∀ i, e01 (σ⁻¹ i) = e01 i) →
      ∀ i, v (σ⁻¹ i) = v i) → (v = 0 ∨ v = e01) := by
  decide +kernel

theorem span_orbit : ∀ m : Fin 5 → ZMod 2, ∑ i, m i = 0 →
    (m = 0 ∨ (∃ σ : Perm (Fin 5), sign σ = 1 ∧ m = fun i => e01 (σ⁻¹ i)) ∨
      ∃ σ : Perm (Fin 5), sign σ = 1 ∧ m = fun i => e01 (σ⁻¹ i) + e23 (σ⁻¹ i)) := by
  decide +kernel

theorem e23_orbit : ∃ τ : Perm (Fin 5), sign τ = 1 ∧ e23 = fun i => e01 (τ⁻¹ i) := by
  decide +kernel

theorem sum_e01 : ∑ i, e01 i = 0 := by decide

theorem sum_e23 : ∑ i, e23 i = 0 := by decide

theorem e01_ne_zero : e01 ≠ 0 := by decide

end Finite5

section Core5

@[expose] def actD (σ : Perm (Fin 5)) (x : ↥(G6.coreMod 5)) : ↥(G6.coreMod 5) :=
  ⟨G6.permAct 5 σ (x : G6.PermMod 5), G6.permAct_mem_coreMod σ x.2⟩

theorem actD_coe (σ : Perm (Fin 5)) (x : ↥(G6.coreMod 5)) :
    ((actD σ x : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 σ (x : G6.PermMod 5) := rfl

theorem actD_mul (σ τ : Perm (Fin 5)) (x : ↥(G6.coreMod 5)) :
    actD (σ * τ) x = actD σ (actD τ x) := by
  apply Subtype.ext
  show G6.permAct 5 (σ * τ) (x : G6.PermMod 5) = G6.permAct 5 σ (G6.permAct 5 τ (x : G6.PermMod 5))
  rw [map_mul]
  rfl

theorem actD_mul_vec (σ : Perm (Fin 5)) (x y : ↥(G6.coreMod 5)) :
    actD σ (x * y) = actD σ x * actD σ y := by
  apply Subtype.ext
  show G6.permAct 5 σ ((x : G6.PermMod 5) * (y : G6.PermMod 5)) =
    G6.permAct 5 σ (x : G6.PermMod 5) * G6.permAct 5 σ (y : G6.PermMod 5)
  rw [map_mul]

@[expose] def x01 : ↥(G6.coreMod 5) :=
  ⟨Multiplicative.ofAdd e01, by
    show ∑ i, Multiplicative.toAdd (Multiplicative.ofAdd e01) i = 0
    exact sum_e01⟩

@[expose] def x23 : ↥(G6.coreMod 5) :=
  ⟨Multiplicative.ofAdd e23, by
    show ∑ i, Multiplicative.toAdd (Multiplicative.ofAdd e23) i = 0
    exact sum_e23⟩

theorem toAdd_actD (σ : Perm (Fin 5)) (x : ↥(G6.coreMod 5)) (i : Fin 5) :
    Multiplicative.toAdd ((actD σ x : ↥(G6.coreMod 5)) : G6.PermMod 5) i =
      Multiplicative.toAdd (x : G6.PermMod 5) (σ⁻¹ i) := rfl

theorem eq_of_toAdd {x y : ↥(G6.coreMod 5)}
    (h : Multiplicative.toAdd (x : G6.PermMod 5) = Multiplicative.toAdd (y : G6.PermMod 5)) : x = y :=
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem cent_coreMod (c : MulAut ↥(G6.coreMod 5))
    (hc : ∀ σ : Perm (Fin 5), sign σ = 1 → ∀ x : ↥(G6.coreMod 5), c (actD σ x) = actD σ (c x)) :
    ∀ y : ↥(G6.coreMod 5), c y = y := by
  have hx01 : c x01 = x01 := by
    have hfix : ∀ σ : Perm (Fin 5), (sign σ = 1 ∧ ∀ i, e01 (σ⁻¹ i) = e01 i) →
        ∀ i, Multiplicative.toAdd ((c x01 : ↥(G6.coreMod 5)) : G6.PermMod 5) (σ⁻¹ i) =
          Multiplicative.toAdd ((c x01 : ↥(G6.coreMod 5)) : G6.PermMod 5) i := by
      rintro σ ⟨hσ, hfx⟩ i
      have h2 : actD σ x01 = x01 := eq_of_toAdd (funext fun j => hfx j)
      have h1 := hc σ hσ x01
      rw [h2] at h1
      have := congrArg (fun z : ↥(G6.coreMod 5) =>
        Multiplicative.toAdd (z : G6.PermMod 5) i) h1
      exact this.symm
    have hsum : ∑ i, Multiplicative.toAdd ((c x01 : ↥(G6.coreMod 5)) : G6.PermMod 5) i = 0 :=
      (c x01).2
    rcases fixed_of_stab _ ⟨hsum, hfix⟩ with h0 | h1
    · exfalso
      have hcx : c x01 = 1 := by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        exact h0
      have : x01 = 1 := c.injective (hcx.trans (map_one c).symm)
      have h3 := congrArg (fun z : ↥(G6.coreMod 5) => Multiplicative.toAdd (z : G6.PermMod 5)) this
      exact e01_ne_zero h3
    · exact eq_of_toAdd h1
  have horb : ∀ σ : Perm (Fin 5), sign σ = 1 → c (actD σ x01) = actD σ x01 := by
    intro σ hσ
    rw [hc σ hσ, hx01]
  obtain ⟨τ, hτ, hτe⟩ := e23_orbit
  have hx23 : x23 = actD τ x01 := eq_of_toAdd (funext fun i => congrFun hτe i)
  have hcx23 : c x23 = x23 := by rw [hx23]; exact horb τ hτ
  intro y
  have hsum : ∑ i, Multiplicative.toAdd (y : G6.PermMod 5) i = 0 := y.2
  rcases span_orbit _ hsum with h0 | ⟨σ, hσ, hσe⟩ | ⟨σ, hσ, hσe⟩
  · have : y = 1 := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      exact h0
    rw [this, map_one]
  · have : y = actD σ x01 := eq_of_toAdd (funext fun i => congrFun hσe i)
    rw [this]
    exact horb σ hσ
  · have : y = actD σ x01 * actD σ x23 := by
      apply eq_of_toAdd
      funext i
      exact congrFun hσe i
    rw [this, map_mul, horb σ hσ, hc σ hσ x23, hcx23]

end Core5

section CentW

variable {V : Type} [CommGroup V]

theorem cent_W {Y : Subgroup (MulAut V)} {W : Subgroup V} {π : Perm (Fin 5) →* ↥Y}
    (hπ : (FFModel.symDn 5).RealizesVia Y W ⊥ π) {c : MulAut V}
    (hcW : ∀ w : V, c w ∈ W ↔ w ∈ W)
    (hc : ∀ σ : Perm (Fin 5), sign σ = 1 →
      c * ((π σ : ↥Y) : MulAut V) = ((π σ : ↥Y) : MulAut V) * c) :
    ∀ w ∈ W, c w = w := by
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.secMap symDn_ker_five hπ
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  let e : ↥W ≃* ↥(G6.coreMod 5) := MulEquiv.ofBijective f ⟨hfinj, hfs⟩
  have hπW : ∀ σ : Perm (Fin 5), ∀ u : ↥W, ((π σ : ↥Y) : MulAut V) (u : V) ∈ W := fun σ u =>
    hπ.2.2.2.1 (π σ) u u.2
  have he : ∀ σ : Perm (Fin 5), ∀ u : ↥W,
      e ⟨((π σ : ↥Y) : MulAut V) (u : V), hπW σ u⟩ = actD σ (e u) := fun σ u =>
    Subtype.ext (hfe σ u (hπW σ u))
  let cW : MulAut ↥W := resHom W ⟨c, hcW⟩
  let c' : MulAut ↥(G6.coreMod 5) := (e.symm.trans cW).trans e
  have hc' : ∀ σ : Perm (Fin 5), sign σ = 1 → ∀ x : ↥(G6.coreMod 5),
      c' (actD σ x) = actD σ (c' x) := by
    intro σ hσ x
    obtain ⟨u, rfl⟩ := e.surjective x
    have h1 : e.symm (actD σ (e u)) = ⟨((π σ : ↥Y) : MulAut V) (u : V), hπW σ u⟩ := by
      rw [← he σ u]
      exact e.symm_apply_apply _
    have h2 : cW ⟨((π σ : ↥Y) : MulAut V) (u : V), hπW σ u⟩ =
        ⟨((π σ : ↥Y) : MulAut V) ((cW u : ↥W) : V), hπW σ (cW u)⟩ := by
      apply Subtype.ext
      show c (((π σ : ↥Y) : MulAut V) (u : V)) = ((π σ : ↥Y) : MulAut V) (c (u : V))
      have := congrArg (fun g : MulAut V => g (u : V)) (hc σ hσ)
      simpa [MulAut.mul_apply] using this
    show e (cW (e.symm (actD σ (e u)))) = actD σ (e (cW (e.symm (e u))))
    rw [h1, h2, he, e.symm_apply_apply]
  have hall := cent_coreMod c' hc'
  intro w hw
  have h1 := hall (e ⟨w, hw⟩)
  have h2 : e (cW ⟨w, hw⟩) = e ⟨w, hw⟩ := by
    have : c' (e ⟨w, hw⟩) = e (cW ⟨w, hw⟩) := by
      show e (cW (e.symm (e ⟨w, hw⟩))) = e (cW ⟨w, hw⟩)
      rw [e.symm_apply_apply]
    rw [← this]
    exact h1
  exact congrArg Subtype.val (e.injective h2)

end CentW

section AltIdent

variable {V : Type} [CommGroup V]

theorem mem_iff_alt {L Y : Subgroup (MulAut V)} (π : Perm (Fin 5) →* ↥Y)
    (hπi : Function.Injective π) (hπs : Function.Surjective π) (hLY : L ≤ Y)
    (hLperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (σ : Perm (Fin 5)) : ((π σ : ↥Y) : MulAut V) ∈ L ↔ σ ∈ alternatingGroup (Fin 5) := by
  set ρ : Perm (Fin 5) →* MulAut V := Y.subtype.comp π with hρ
  have hρi : Function.Injective ρ := Y.subtype_injective.comp hπi
  set M₀ : Subgroup (Perm (Fin 5)) := L.comap ρ with hM₀
  have hmap : M₀.map ρ = L := by
    rw [hM₀, Subgroup.map_comap_eq]
    have : ρ.range = Y := by
      ext x
      constructor
      · rintro ⟨τ, rfl⟩
        exact (π τ).2
      · intro hx
        obtain ⟨τ, hτ⟩ := hπs ⟨x, hx⟩
        exact ⟨τ, congrArg Subtype.val hτ⟩
    rw [this]
    exact inf_eq_right.2 hLY
  have hM₀n : M₀.Normal := ⟨fun τ hτ σ' => by
    show ρ (σ' * τ * σ'⁻¹) ∈ L
    rw [map_mul, map_mul, map_inv]
    exact hLn _ (π σ').2 _ hτ⟩
  have hM₀perf : ⁅M₀, M₀⁆ = M₀ := by
    apply Subgroup.map_injective hρi
    rw [Subgroup.map_commutator, hmap, hLperf]
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hle : M₀ ≤ alternatingGroup (Fin 5) := by
    calc M₀ = ⁅M₀, M₀⁆ := hM₀perf.symm
      _ ≤ commutator (Perm (Fin 5)) := Subgroup.commutator_mono le_top le_top
      _ = alternatingGroup (Fin 5) := alternatingGroup.commutator_perm_eq h5
  have hnt : Nontrivial ↥M₀ := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    apply hLne
    rw [← hmap, h, Subgroup.map_bot]
  have hge : alternatingGroup (Fin 5) ≤ M₀ := by
    have := hM₀n
    exact Equiv.Perm.alternatingGroup_le_of_normal h5 hnt
  have hM₀eq : M₀ = alternatingGroup (Fin 5) := le_antisymm hle hge
  rw [← hM₀eq]
  exact Iff.rfl

theorem exists_inner_of_conj {L Y : Subgroup (MulAut V)} (π : Perm (Fin 5) →* ↥Y)
    (hπi : Function.Injective π) (hπs : Function.Surjective π) (hLY : L ≤ Y)
    (hLperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    {g : MulAut V} (hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hg' : ∀ l ∈ L, g⁻¹ * l * g ∈ L) :
    ∃ s : Perm (Fin 5), ∀ σ ∈ alternatingGroup (Fin 5),
      g * ((π σ : ↥Y) : MulAut V) * g⁻¹ = ((π (s * σ * s⁻¹) : ↥Y) : MulAut V) := by
  have hmem := mem_iff_alt π hπi hπs hLY hLperf hLne hLn
  have hπV : Function.Injective (fun τ : Perm (Fin 5) => ((π τ : ↥Y) : MulAut V)) :=
    Y.subtype_injective.comp hπi
  have tex : ∀ (g' : MulAut V), (∀ l ∈ L, g' * l * g'⁻¹ ∈ L) →
      ∀ a : ↥(alternatingGroup (Fin 5)), ∃ b : ↥(alternatingGroup (Fin 5)),
        ((π (b : Perm (Fin 5)) : ↥Y) : MulAut V) =
          g' * ((π (a : Perm (Fin 5)) : ↥Y) : MulAut V) * g'⁻¹ := by
    intro g' hg'' a
    have hx : g' * ((π (a : Perm (Fin 5)) : ↥Y) : MulAut V) * g'⁻¹ ∈ L :=
      hg'' _ ((hmem a).2 a.2)
    obtain ⟨τ, hτ⟩ := hπs ⟨_, hLY hx⟩
    have hτ' : ((π τ : ↥Y) : MulAut V) =
        g' * ((π (a : Perm (Fin 5)) : ↥Y) : MulAut V) * g'⁻¹ := congrArg Subtype.val hτ
    exact ⟨⟨τ, (hmem τ).1 (hτ' ▸ hx)⟩, hτ'⟩
  choose tf htf using tex
  have hginv : ∀ l ∈ L, g⁻¹ * l * g⁻¹⁻¹ ∈ L := fun l hl => by simpa using hg' l hl
  let β : MulAut ↥(alternatingGroup (Fin 5)) :=
    { toFun := tf g hg
      invFun := tf g⁻¹ hginv
      left_inv := fun a => by
        apply Subtype.ext
        apply hπV
        show ((π ((tf g⁻¹ hginv (tf g hg a) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) : ↥Y) :
          MulAut V) = ((π (a : Perm (Fin 5)) : ↥Y) : MulAut V)
        rw [htf g⁻¹ hginv, htf g hg]
        group
      right_inv := fun a => by
        apply Subtype.ext
        apply hπV
        show ((π ((tf g hg (tf g⁻¹ hginv a) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) : ↥Y) :
          MulAut V) = ((π (a : Perm (Fin 5)) : ↥Y) : MulAut V)
        rw [htf g hg, htf g⁻¹ hginv]
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        apply hπV
        show ((π ((tf g hg (a * b) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) : ↥Y) :
          MulAut V) = ((π (((tf g hg a : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) *
            ((tf g hg b : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) : ↥Y) : MulAut V)
        rw [map_mul π, Subgroup.coe_mul, htf g hg (a * b), htf g hg a, htf g hg b]
        have : (π ((a * b : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) : ↥Y) =
            π (a : Perm (Fin 5)) * π (b : Perm (Fin 5)) := by
          rw [← map_mul]
          rfl
        rw [this, Subgroup.coe_mul]
        group }
  obtain ⟨s, hs⟩ := Semidihedral.Principal.CyclicAlternatingFive.conjNormal_surjective β
  refine ⟨s, fun σ hσ => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 5)) =>
    ((φ ⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hs
  simp only [MulAut.conjNormal_apply] at h1
  have h2 : (s * σ * s⁻¹ : Perm (Fin 5)) = ((tf g hg ⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) :
      Perm (Fin 5)) := h1
  rw [h2, htf g hg ⟨σ, hσ⟩]

end AltIdent

section Sym5

variable {V : Type} [CommGroup V]

theorem commV_sup_eq {L A : Subgroup (MulAut V)} (hn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L)
    (hsup : commV L ⊔ fixV A = ⊤) : commV (L ⊔ A) = commV L := by
  apply le_antisymm
  · refine B19.commV_le_iff.2 (sup_le ?_ ?_)
    · intro l hl v
      exact Subgroup.subset_closure ⟨l, hl, v, rfl⟩
    · intro a ha v
      obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ (Subgroup.mem_top v))
      have : a (u * c) * (u * c)⁻¹ = a u * u⁻¹ := by
        rw [map_mul, hc a ha]
        simp [mul_comm]
      rw [this]
      exact (commV L).mul_mem (commV_invariant (fun x hx => hn a ha x hx) hu)
        ((commV L).inv_mem hu)
  · rw [commV_eq_commSub, commV_eq_commSub]
    exact commSub_mono le_rfl le_sup_left

variable [Finite V]

theorem offenders_of_sym5 (hP4 : AsB15Part4) {G A L : Subgroup (MulAut V)} (hc : B56Counterex G)
    (hA : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (h2 : B59Case2 A L) :
    B510Offenders G (L ⊔ A) := by
  intro D hD d hd
  obtain ⟨-, -, hsym, hsupVA⟩ := h2
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 5) →* ↥(L ⊔ A),
      (FFModel.symDn 5).RealizesVia (L ⊔ A) (commV L) ⊥ π := by
    obtain ⟨π, hπ⟩ := hsym
    exact ⟨π, hπ⟩
  have hV := hc.hV
  have hJ : G = ffJ G := hc.hyp.2.1
  have hnG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B55.normalizes_comp hP4 hV hJ hL
  have hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    B19Aux.conj_mem_of_le_normalizer hnG hg hl
  have hAG : A ≤ G := hA.1.1
  have hLG : L ≤ G := hL.1
  have hYG : L ⊔ A ≤ G := sup_le hLG hAG
  have hGst : G ≤ stabSub (commV L) := le_stabSub_commV hn
  have hπi : Function.Injective π := injective_of_faithful_sec (symDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ⟨hLo.1⟩
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).1 (CFSG.ComponentClassification.Quasisimple.nontrivial hLo)
  have hLn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => hn y (hYG hy) l hl
  have claim : ∀ g ∈ G, ∃ y ∈ L ⊔ A, ∀ w ∈ commV L, g w = y w := by
    intro g hg
    have hg1 : ∀ l ∈ L, g * l * g⁻¹ ∈ L := hn g hg
    have hg2 : ∀ l ∈ L, g⁻¹ * l * g ∈ L := fun l hl => by
      simpa using hn g⁻¹ (G.inv_mem hg) l hl
    obtain ⟨s, hs⟩ := exists_inner_of_conj π hπi hπs le_sup_left hLperf hLne hLn hg1 hg2
    set y : MulAut V := ((π s : ↥(L ⊔ A)) : MulAut V) with hy
    have hyY : y ∈ L ⊔ A := (π s).2
    have hyG : y ∈ G := hYG hyY
    have hcomm : ∀ σ : Perm (Fin 5), sign σ = 1 → (y⁻¹ * g) * ((π σ : ↥(L ⊔ A)) : MulAut V) =
        ((π σ : ↥(L ⊔ A)) : MulAut V) * (y⁻¹ * g) := by
      intro σ hσ
      have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
      have h1 := hs σ hσA
      have h2 : ((π (s * σ * s⁻¹) : ↥(L ⊔ A)) : MulAut V) =
          y * ((π σ : ↥(L ⊔ A)) : MulAut V) * y⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [h2] at h1
      calc (y⁻¹ * g) * ((π σ : ↥(L ⊔ A)) : MulAut V)
          = y⁻¹ * (g * ((π σ : ↥(L ⊔ A)) : MulAut V) * g⁻¹) * g := by group
        _ = y⁻¹ * (y * ((π σ : ↥(L ⊔ A)) : MulAut V) * y⁻¹) * g := by rw [h1]
        _ = ((π σ : ↥(L ⊔ A)) : MulAut V) * (y⁻¹ * g) := by group
    have hcW : ∀ w : V, (y⁻¹ * g) w ∈ commV L ↔ w ∈ commV L :=
      hGst (G.mul_mem (G.inv_mem hyG) hg)
    have hfix := cent_W hπ hcW hcomm
    refine ⟨y, hyY, fun w hw => ?_⟩
    have h3 : y⁻¹ (g w) = w := hfix w hw
    have h4 := congrArg y h3
    simpa using h4
  obtain ⟨y, hy, hyW⟩ := claim d (hD.1 hd)
  refine ⟨y, hy, fun w hw => hyW w ?_⟩
  rwa [commV_sup_eq (fun a ha l hl => hn a (hAG ha) l hl) hsupVA] at hw

end Sym5

end B510

end FFC

end CFSG.Quasithin
