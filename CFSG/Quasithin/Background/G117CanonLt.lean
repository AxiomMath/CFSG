module

public import CFSG.Quasithin.Background.G117A6
public import CFSG.Quasithin.Background.G117CanonSetup
public import CFSG.Quasithin.Background.G117Inputs
public import CFSG.Quasithin.Background.G117Layer
public import CFSG.Quasithin.Background.G117Lt2
public import CFSG.Quasithin.Background.G117Lt3
public import CFSG.Quasithin.Background.G117Lt4
public import CFSG.Quasithin.Background.G117NoE9
public import CFSG.Quasithin.Background.G117StepsA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Open

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure LtFacts (Γ L X : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop where
  card_Γ : Nat.card ↥Γ = 2160
  card_H : Nat.card ↥(normalClosure Γ L) = 360
  simple_H : IsSimpleGroup ↥(normalClosure Γ L)
  card_C : Nat.card ↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) = 3
  layer : (genFittingLayer ↥Γ).map Γ.subtype = normalClosure Γ L
  pCore : (CFSG.pCore 3 ↥Γ).map Γ.subtype =
    Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))
  inter_stab : ∀ x ∈ Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)),
    conjSub x I = I → x = 1
  moves : ∀ p ∈ Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)), p ≠ 1 →
    ∀ J : IrrSet Γ L, conjSub p J.1 ≠ J.1
  inverts : ∀ x ∈ X, x ∉ normalClosure Γ L →
    ∀ p ∈ Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)), x * p * x⁻¹ = p⁻¹

theorem ltFacts (hE11 : E11Stmt) (hN6 : A6NormalizerBound) (hA6 : A6Facts)
    {Q : ConclPred} {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {m : ℕ}
    (c : QCtx Q B Γ v₁ W X X₀ L I m) (hH : Invariant (normalClosure Γ L) I)
    (hne : I ≠ ⊤) (hV8 : Module.finrank (ZMod 2) V = 8) (hm3 : m = 3)
    (hI4 : Module.finrank (ZMod 2) ↥I = 4)
    (hperm : IsPermCoreModule (restrictRange (normalClosure Γ L) I hH) (alternatingGroup (Fin 6)))
    (hend : EndIsField (restrictRange (normalClosure Γ L) I hH) 1) : LtFacts Γ L X I := by
  obtain ⟨hAut, hD8, hE9⟩ := hA6
  have h108 := c.h108
  have hIplus : IrrPlus (normalClosure Γ L) I := props_irrPlus c.props
  have hhom := props_homogeneous c.props
  have hfaithH : FaithfulOn (normalClosure Γ L) I := props_faithful c.props
  have hHΓ : normalClosure Γ L ≤ Γ := h108.H_le
  have hNorm := normalClosure_normal Γ L
  have hperm0 := hperm
  obtain ⟨φ', -⟩ := hperm0
  let e : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 6)) :=
    (restrictRangeEquiv hH hfaithH).trans φ'
  have hH360 : Nat.card ↥(normalClosure Γ L) = 360 := by
    rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_six]
  have hX8 : Nat.card ↥X = 8 := by
    rw [c.card, hm3]
    norm_num
  have hXH : ¬ X ≤ normalClosure Γ L := by
    intro hXle
    let D : Subgroup ↥(alternatingGroup (Fin 6)) :=
      (X.subgroupOf (normalClosure Γ L)).map e.toMonoidHom
    have hDcard : Nat.card ↥D = 8 := by
      have h1 : Nat.card ↥D = Nat.card ↥(X.subgroupOf (normalClosure Γ L)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv, hX8]
    obtain ⟨a, b, hab⟩ := hD8 D hDcard
    apply hab
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    show (a : ↥(alternatingGroup (Fin 6))) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h108.X_comm x.1 (Subgroup.mem_subgroupOf.1 hx) y.1
      (Subgroup.mem_subgroupOf.1 hy))

  have hcard3 : Nat.card (IrrSet Γ L) = 3 :=
    card_irrSet_eq_three h108 hE11 hIplus hhom hH hI4 hV8 hend
  have hne3 : ∀ J : IrrSet Γ L, J.1 ≠ ⊤ := by
    intro J hJ
    obtain ⟨φ, -⟩ := hhom I J.1 hIplus J.2
    have h1 : Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) ↥J.1 :=
      LinearEquiv.finrank_eq φ
    have h2 : Module.finrank (ZMod 2) ↥J.1 = Module.finrank (ZMod 2) V := by
      have h3 := LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hJ)
      rw [h3]
      exact finrank_top (ZMod 2) V
    omega
  have hΓI : Nat.card ↥Γ = 3 * Nat.card ↥(stabilizerOf Γ I) :=
    card_eq_three_mul_card_stabilizer h108 hcard3 hne3 ⟨I, hIplus⟩
  have hKle : normalClosure Γ L ⊔ X ≤ stabilizerOf Γ I :=
    sup_le (fun k hk => ⟨hHΓ hk, c.invariantH.conjSub_eq hk⟩)
      (fun k hk => ⟨h108.X_le hk, c.invariantX.conjSub_eq hk⟩)
  have hK720 : 720 ≤ Nat.card ↥(normalClosure Γ L ⊔ X) := by
    have hHK : normalClosure Γ L ≤ normalClosure Γ L ⊔ X := le_sup_left
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHK
    rw [hH360] at hk
    have hpos : 0 < Nat.card ↥(normalClosure Γ L ⊔ X) := Nat.card_pos
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hXH
      have : normalClosure Γ L = normalClosure Γ L ⊔ X :=
        Subgroup.eq_of_le_of_card_ge hHK (by rw [hk, hH360])
      rw [this]
      exact le_sup_right
    omega
  have hΓI720 : 720 ≤ Nat.card ↥(stabilizerOf Γ I) := hK720.trans (Subgroup.card_le_of_le hKle)
  have hΓ2160 : 2160 ≤ Nat.card ↥Γ := by omega
  set Cg : Subgroup (GLV V) := Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) with hCg
  have hAut1440 : Nat.card (MulAut ↥(normalClosure Γ L)) = 1440 := hAut _ ⟨e⟩
  have hle1 : Nat.card ↥Γ ≤ 1440 * Nat.card ↥Cg := by
    have := natCard_le_aut_mul_centralizer (Γ := Γ) hNorm
    rwa [hAut1440] at this
  have hC2 : 2 ≤ Nat.card ↥Cg := by
    by_contra hlt
    have h1 : Nat.card ↥Cg ≤ 1 := by omega
    have h2 := Nat.mul_le_mul_left 1440 h1
    omega
  let φ₃ : IrrSet Γ L ≃ Fin 3 := (Finite.equivFin (IrrSet Γ L)).trans (finCongr hcard3)
  let ρΓ : ↥Γ →* Equiv.Perm (Fin 3) :=
    (φ₃.permCongrHom : Equiv.Perm (IrrSet Γ L) →* Equiv.Perm (Fin 3)).comp (irrAct h108)
  have hρΓ : ∀ (γ : ↥Γ) (J : IrrSet Γ L), ρΓ γ (φ₃ J) = φ₃ (irrAct h108 γ J) := by
    intro γ J
    show φ₃ (irrAct h108 γ (φ₃.symm (φ₃ J))) = _
    rw [Equiv.symm_apply_apply]
  let ρ : ↥Cg →* Equiv.Perm (Fin 3) := ρΓ.comp (Subgroup.inclusion inf_le_left)
  have hρ : ∀ x : ↥Cg, ρ x = ρΓ ⟨(x : GLV V), x.2.1⟩ := fun x => rfl
  have hcommC : ∀ x : ↥Cg, ∀ h ∈ normalClosure Γ L, h * (x : GLV V) = (x : GLV V) * h :=
    fun x h hh => Subgroup.mem_centralizer_iff.1 x.2.2 h hh
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hfixall : ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J →
        conjSub (x : GLV V) J = J := by
      intro J hJ
      have h1 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (φ₃ ⟨J, hJ⟩)) (hρ x ▸ hx)
      simp only [Equiv.Perm.coe_one, id_eq, hρΓ] at h1
      have h2 := φ₃.injective h1
      exact congrArg Subtype.val h2
    exact Subtype.ext (eq_one_of_fixes_irr h108 hE11 hIplus hhom hH hend (hcommC x) hfixall)
  have hno2 : Nat.card ↥Cg ≠ 2 := by
    intro h2
    have hPn := normal_centralizer_subgroupOf (Γ := Γ) hNorm
    have hP2 : IsPGroup 2 ↥((Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf
        Γ) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Cg ≤ Γ)).toEquiv, h2]
      norm_num
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hPn hP2
    have hbot := pCoreOf_eq_bot_of_isIrr_top h108.irreducible
    have hmap : ((Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ).map
        Γ.subtype = Cg := Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hCbot : Cg = ⊥ := by
      rw [← hmap, ← le_bot_iff, ← hbot]
      exact Subgroup.map_mono hle
    rw [hCbot, Subgroup.card_bot] at h2
    omega
  have hno6 : Nat.card ↥Cg ≠ 6 := by
    intro h6
    obtain ⟨t, c', ht2, ht1, hc3, hc1, htc⟩ := exists_S3_of_card_six ρ hρinj h6
    obtain ⟨E, hE, hE9'⟩ := hE9 ↥(normalClosure Γ L) ⟨e⟩
    have hEcomm : ∀ a ∈ E.map (normalClosure Γ L).subtype, ∀ b ∈ E.map (normalClosure Γ L).subtype,
        a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg (fun x : ↥E => ((x : ↥(normalClosure Γ L)) : GLV V))
        (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hE3 : ∀ a ∈ E.map (normalClosure Γ L).subtype, a ^ 3 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg (fun x : ↥(normalClosure Γ L) => (x : GLV V)) (hE.2 a ha)
    have hEcard : Nat.card ↥(E.map (normalClosure Γ L).subtype) = 9 := by
      rw [← hE9']
      exact (Nat.card_congr (Subgroup.equivMapOfInjective E (normalClosure Γ L).subtype
        (normalClosure Γ L).subtype_injective).toEquiv).symm
    have hEΓ : E.map (normalClosure Γ L).subtype ≤ Γ := by
      rintro _ ⟨a, -, rfl⟩
      exact hHΓ a.2
    have hEC : ∀ a ∈ E.map (normalClosure Γ L).subtype, ∀ z : ↥Cg,
        a * (z : GLV V) = (z : GLV V) * a := by
      rintro _ ⟨a, -, rfl⟩ z
      exact hcommC z a a.2
    exact no_E9_S3 (A := GLV V) (Γ := Γ) c.setup.conf.sqtk (t := (t : GLV V)) (c := (c' : GLV V))
      t.2.1 c'.2.1 hEΓ (congrArg Subtype.val ht2)
      (fun h => ht1 (Subtype.ext h)) (by
        have := congrArg Subtype.val hc3
        simpa using this) (fun h => hc1 (Subtype.ext h))
      (by
        have := congrArg Subtype.val htc
        simpa using this) hEcomm hE3 hEcard (fun a ha => hEC a ha t) (fun a ha => hEC a ha c')
  have hC3 : Nat.card ↥Cg = 3 := card_eq_three_of_injective ρ hρinj hC2 hno2 hno6
  have hCI : ∀ x : ↥Cg, conjSub (x : GLV V) I = I → x = 1 := by
    intro x hxI
    have h3 : ρ x ^ 3 = 1 := by
      rw [← map_pow]
      have : x ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥Cg) (x := x)
        rwa [hC3] at this
      rw [this, map_one]
    have hfixpt : ∃ i, ρ x i = i := by
      refine ⟨φ₃ ⟨I, hIplus⟩, ?_⟩
      rw [hρ, hρΓ]
      exact congrArg φ₃ (Subtype.ext hxI)
    have hsq := perm3_fix_sq _ hfixpt
    have h1 : ρ x = 1 := by
      calc ρ x = ρ x ^ 3 * (ρ x * ρ x)⁻¹ := by group
        _ = 1 := by rw [h3, hsq]; simp
    exact hρinj (h1.trans (map_one ρ).symm)
  have hΓIinv : Invariant (stabilizerOf Γ I) I := fun k hk u hu => by
    have h1 : conjSub k I = I := hk.2
    rw [← h1]
    exact apply_mem_conjSub hu
  have hΓI720' : Nat.card ↥(stabilizerOf Γ I) ≤ 720 := by
    have hinj : Function.Injective (restrictHom (stabilizerOf Γ I) I hΓIinv) := by
      rw [injective_iff_map_eq_one]
      intro k hk1
      rw [restrictHom_eq_one_iff] at hk1
      have hkΓ : (k : GLV V) ∈ Γ := stabilizerOf_le_self Γ I k.2
      have hkC : (k : GLV V) ∈ Cg := by
        refine ⟨hkΓ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        have hconj : (k : GLV V) * h * (k : GLV V)⁻¹ = h := by
          have h1 : (k : GLV V) * h * (k : GLV V)⁻¹ * h⁻¹ = 1 := by
            refine faithfulOn_iff.1 hfaithH _ ?_ fun u hu => ?_
            · exact (normalClosure Γ L).mul_mem (hNorm k hkΓ h hh) ((normalClosure Γ L).inv_mem hh)
            · have hw : (h⁻¹ : GLV V) u ∈ I :=
                c.invariantH h⁻¹ ((normalClosure Γ L).inv_mem hh) u hu
              have e2 : (k : GLV V)⁻¹ ((h⁻¹ : GLV V) u) = (h⁻¹ : GLV V) u := by
                have := hk1 ((h⁻¹ : GLV V) u) hw
                have e3 : (k : GLV V)⁻¹ ((k : GLV V) ((h⁻¹ : GLV V) u)) = (h⁻¹ : GLV V) u := by simp
                rw [this] at e3
                exact e3
              show (k : GLV V) (h ((k : GLV V)⁻¹ ((h⁻¹ : GLV V) u))) = u
              rw [e2]
              have e4 : h ((h⁻¹ : GLV V) u) = u := by simp
              rw [e4]
              exact hk1 u hu
          exact mul_inv_eq_one.1 h1
        have : (k : GLV V) * h = h * (k : GLV V) := by
          rw [mul_inv_eq_iff_eq_mul] at hconj
          exact hconj
        exact this.symm
      have h2 := hCI ⟨k, hkC⟩ k.2.2
      have h3 : ((⟨k, hkC⟩ : ↥Cg) : GLV V) = 1 := congrArg Subtype.val h2
      exact Subtype.ext h3
    have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have hR : Nat.card ↥(restrictRange (stabilizerOf Γ I) I hΓIinv) ≤ 720 := by
      refine hN6 ↥I (restrictRange (normalClosure Γ L) I hH) _ hperm ?_
      intro r hr h' hh'
      obtain ⟨k, hk, rfl⟩ := (mem_restrictRange_iff' hΓIinv).1 hr
      obtain ⟨h₀, hh₀, rfl⟩ := (mem_restrictRange_iff' hH).1 hh'
      refine (mem_restrictRange_iff' hH).2
        ⟨k * h₀ * k⁻¹, hNorm k (stabilizerOf_le_self Γ I hk) h₀ hh₀, ?_⟩
      ext i
      show k (h₀ ((k⁻¹ : GLV V) (i : V))) = (k * h₀ * k⁻¹) (i : V)
      rfl
    rw [hcard]
    exact hR
  have hΓfinal : Nat.card ↥Γ = 2160 := by omega
  have hab : ∀ a ∈ Γ, (∀ h ∈ normalClosure Γ L, a * h = h * a) → ∀ b ∈ Γ,
      (∀ h ∈ normalClosure Γ L, b * h = h * b) → a * b = b * a := by
    intro a ha hac b hb hbc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hCcyc : IsCyclic ↥Cg := isCyclic_of_prime_card hC3
    let a' : ↥Cg := ⟨a, ha, Subgroup.mem_centralizer_iff.2 fun h hh => (hac h hh).symm⟩
    let b' : ↥Cg := ⟨b, hb, Subgroup.mem_centralizer_iff.2 fun h hh => (hbc h hh).symm⟩
    let _ := hCcyc.commGroup
    exact congrArg Subtype.val (mul_comm a' b')
  have hlayer := layer_map_eq_normalClosure h108.component hab
  let eL : ↥(genFittingLayer ↥Γ) ≃* ↥(alternatingGroup (Fin 6)) :=
    ((Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr hlayer)).trans e
  have hsimple : IsSimpleGroup ↥(normalClosure Γ L) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hH3 : ¬ IsPGroup 3 ↥(normalClosure Γ L) := by
    rw [IsPGroup.iff_card]
    rintro ⟨n, hn⟩
    rw [hH360] at hn
    have h5 : 5 ∣ 3 ^ n := hn ▸ (by norm_num : 5 ∣ 360)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
    omega
  have hC3p : IsPGroup 3 ↥Cg := IsPGroup.of_card (n := 1) (by rw [hC3]; norm_num)
  have hpc := pCore_three_eq hHΓ hNorm hsimple hH3 hC3p
  have hpcCard : Nat.card ↥(CFSG.pCore 3 ↥Γ) = 3 := by
    rw [hpc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Cg ≤ Γ)).toEquiv]
    exact hC3
  obtain ⟨x₀, hx₀X, J₀, hx₀move⟩ : ∃ x ∈ X, ∃ J : IrrSet Γ L, conjSub x J.1 ≠ J.1 := by
    by_contra hall
    push Not at hall
    have hall' : ∀ J : IrrSet Γ L, J.1 = I := by
      intro J
      refine props_unique c.props J.1 J.2 (fun x hx u hu => ?_)
      rw [← hall x hx J]
      exact apply_mem_conjSub hu
    have hnt : Nontrivial (IrrSet Γ L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨J₁, J₂, hJ⟩ := exists_pair_ne (IrrSet Γ L)
    exact hJ (Subtype.ext ((hall' J₁).trans (hall' J₂).symm))
  have hx₀Γ : x₀ ∈ Γ := h108.X_le hx₀X
  let x₀Γ : ↥Γ := ⟨x₀, hx₀Γ⟩
  have hτ2₀ : ρΓ x₀Γ * ρΓ x₀Γ = 1 := by
    rw [← map_mul]
    have : x₀Γ * x₀Γ = 1 := Subtype.ext (h108.X_sq x₀ hx₀X)
    rw [this, map_one]
  have hτ1₀ : ρΓ x₀Γ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (φ₃ J₀)) h1
    simp only [Equiv.Perm.coe_one, id_eq, hρΓ] at h2
    exact hx₀move (congrArg Subtype.val (φ₃.injective h2))
  have hkerH : ∀ y : ↥Γ, ρΓ y = 1 → (y : GLV V) ∈ normalClosure Γ L := by
    have hr3 : 3 ∣ Nat.card ρΓ.range := by
      have h1 : ρ.range ≤ ρΓ.range := by
        rintro _ ⟨c', rfl⟩
        exact ⟨⟨(c' : GLV V), c'.2.1⟩, rfl⟩
      have h2 : Nat.card ρ.range = 3 := by
        have h2' : Nat.card ρ.range = Nat.card ↥Cg :=
          (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
        rw [h2', hC3]
      have h3 := Subgroup.card_dvd_of_le h1
      rwa [h2] at h3
    have hr2 : 2 ∣ Nat.card ρΓ.range := by
      have hord : orderOf (ρΓ x₀Γ) = 2 :=
        orderOf_eq_prime (by rw [sq]; exact hτ2₀) hτ1₀
      have hmem : ρΓ x₀Γ ∈ ρΓ.range := MonoidHom.mem_range.2 ⟨x₀Γ, rfl⟩
      have h1 := orderOf_dvd_natCard (⟨ρΓ x₀Γ, hmem⟩ : ρΓ.range)
      have h2 : orderOf (⟨ρΓ x₀Γ, hmem⟩ : ρΓ.range) = 2 :=
        (Subgroup.orderOf_mk _ _).trans hord
      rwa [h2] at h1
    have hr_le : Nat.card ρΓ.range ≤ 6 := by
      have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        rfl
      exact (Nat.card_le_card_of_injective (Subtype.val : ρΓ.range → Equiv.Perm (Fin 3))
        Subtype.val_injective).trans h6.le
    have hpos : 0 < Nat.card ρΓ.range := Nat.card_pos
    have hr6 : Nat.card ρΓ.range = 6 := by omega
    have hk : Nat.card ρΓ.ker = 360 := by
      have := Subgroup.card_ker_mul_card_range ρΓ
      rw [hr6, hΓfinal] at this
      omega
    have hHker : (normalClosure Γ L).subgroupOf Γ ≤ ρΓ.ker := by
      intro h hh
      have hhH : (h : GLV V) ∈ normalClosure Γ L := hh
      rw [MonoidHom.mem_ker]
      refine Equiv.ext fun i => ?_
      obtain ⟨J, rfl⟩ := φ₃.surjective i
      rw [hρΓ, Equiv.Perm.coe_one, id_eq]
      refine congrArg φ₃ (Subtype.ext ?_)
      rw [irrAct_apply_val]
      exact (J.2.1).conjSub_eq hhH
    have hcardH : Nat.card ↥((normalClosure Γ L).subgroupOf Γ) = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHΓ).toEquiv, hH360]
    have heq : (normalClosure Γ L).subgroupOf Γ = ρΓ.ker :=
      Subgroup.eq_of_le_of_card_ge hHker (by omega)
    intro y hy
    have : y ∈ ρΓ.ker := hy
    rw [← heq] at this
    exact this
  have hPn := normal_centralizer_subgroupOf (Γ := Γ) hNorm
  have hinv : ∀ x ∈ X, x ∉ normalClosure Γ L → ∀ p ∈ Cg, x * p * x⁻¹ = p⁻¹ := by
    intro x hxX hxH y hyC
    have hxΓ : x ∈ Γ := h108.X_le hxX
    let xΓ : ↥Γ := ⟨x, hxΓ⟩
    have hτ2 : ρΓ xΓ * ρΓ xΓ = 1 := by
      rw [← map_mul]
      have : xΓ * xΓ = 1 := Subtype.ext (h108.X_sq x hxX)
      rw [this, map_one]
    have hτ1 : ρΓ xΓ ≠ 1 := fun h1 => hxH (hkerH xΓ h1)
    by_cases hy1 : y = 1
    · rw [hy1]
      simp
    · have hyΓ : y ∈ Γ := hyC.1
      have hy : (⟨y, hyΓ⟩ : ↥Γ) ∈
          (Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ := hyC
      have hz : xΓ * (⟨y, hyΓ⟩ : ↥Γ) * xΓ⁻¹ ∈
          (Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ :=
        hPn.conj_mem _ hy xΓ
      have hzC : ((xΓ * (⟨y, hyΓ⟩ : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V) ∈ Cg := hz
      have hwC : (((⟨y, hyΓ⟩ : ↥Γ)⁻¹ : ↥Γ) : GLV V) ∈ Cg := Cg.inv_mem hyC
      let yc : ↥Cg := ⟨y, hyC⟩
      have hyc1 : yc ≠ 1 := fun h => by
        have h' : ((yc : ↥Cg) : GLV V) = 1 := congrArg Subtype.val h
        exact hy1 h'
      have hσ1 : ρ yc ≠ 1 := fun h => hyc1 (hρinj (h.trans (map_one ρ).symm))
      have hσ3 : ρ yc ^ 3 = 1 := by
        rw [← map_pow]
        have : yc ^ 3 = 1 := by
          have := pow_card_eq_one' (G := ↥Cg) (x := yc)
          rwa [hC3] at this
        rw [this, map_one]
      have hconj := perm3_conj_inv _ _ hτ2 hτ1 hσ3 hσ1
      have heq : ρ ⟨((xΓ * (⟨y, hyΓ⟩ : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V), hzC⟩ =
          ρ ⟨(((⟨y, hyΓ⟩ : ↥Γ)⁻¹ : ↥Γ) : GLV V), hwC⟩ := by
        rw [hρ, hρ]
        show ρΓ (xΓ * (⟨y, hyΓ⟩ : ↥Γ) * xΓ⁻¹) = ρΓ (⟨y, hyΓ⟩ : ↥Γ)⁻¹
        rw [map_mul, map_mul, map_inv, map_inv]
        exact hconj
      have h8 := hρinj heq
      have h9 : ((xΓ * (⟨y, hyΓ⟩ : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V) =
          (((⟨y, hyΓ⟩ : ↥Γ)⁻¹ : ↥Γ) : GLV V) :=
        congrArg (fun z : ↥Cg => (z : GLV V)) h8
      exact h9
  have hmoves : ∀ p ∈ Cg, p ≠ 1 → ∀ J : IrrSet Γ L, conjSub p J.1 ≠ J.1 := by
    intro p hp hp1 J hJ
    let pc : ↥Cg := ⟨p, hp⟩
    have h3 : ρ pc ^ 3 = 1 := by
      rw [← map_pow]
      have : pc ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥Cg) (x := pc)
        rwa [hC3] at this
      rw [this, map_one]
    have hfixpt : ∃ i, ρ pc i = i := by
      refine ⟨φ₃ J, ?_⟩
      rw [hρ, hρΓ]
      exact congrArg φ₃ (Subtype.ext hJ)
    have hsq := perm3_fix_sq _ hfixpt
    have h1 : ρ pc = 1 := by
      calc ρ pc = ρ pc ^ 3 * (ρ pc * ρ pc)⁻¹ := by group
        _ = 1 := by rw [h3, hsq]; simp
    exact hp1 (congrArg Subtype.val (hρinj (h1.trans (map_one ρ).symm)))
  have hpmap : (CFSG.pCore 3 ↥Γ).map Γ.subtype = Cg := by
    rw [hpc]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  exact ⟨hΓfinal, hH360, hsimple, hC3, hlayer, hpmap,
    fun x hx hxI => congrArg Subtype.val (hCI ⟨x, hx⟩ hxI), hmoves, hinv⟩

end Canon

end G11

end CFSG.Quasithin
