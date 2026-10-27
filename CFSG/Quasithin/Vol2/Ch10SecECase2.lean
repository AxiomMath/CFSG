module

public import CFSG.Quasithin.Vol2.Ch10SecECase1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5 (pact)
open scoped commutatorElement IsMulCommutative

theorem RealizesVia.coordSec {V : Type*} [CommGroup V] {D : FFModel}
    (hk : ∀ m ∈ D.ker, m = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∃ β : ↥U →* ↥D.sec, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        ((β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥D.sec) : D.Amb) =
          D.act γ ((β u : ↥D.sec) : D.Amb) := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let κ : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* ↥D.sec :=
    QuotientGroup.lift (D.ker.subgroupOf D.sec) (MonoidHom.id _) (by
      intro x hx
      exact Subtype.ext (hk _ (Subgroup.mem_subgroupOf.mp hx)))
  have hκ : ∀ m : ↥D.sec, κ (QuotientGroup.mk m) = m := fun m => QuotientGroup.lift_mk _ _ _
  refine ⟨κ.comp β, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu, hκ]⟩
  · intro u
    rw [← hβk u]
    constructor
    · intro h1
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
      rw [MonoidHom.comp_apply, ← hm, hκ] at h1
      rw [← hm, h1]
      rfl
    · intro h1
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (hsec γ m m.2) hm.symm
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, hκ, ← hm, hκ]

variable {G : Type} [Group G]

theorem mk_mem_commV_of_mem_commutator {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ ⁅V, X⁆)
    (hvV : v ∈ V) : (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV) ∈ commV (autI hV X) := by
  have hle : ⁅V, X⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hXV
  suffices key : ∀ v ∈ ⁅V, X⁆, ∀ hvV : v ∈ V,
      (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV) ∈ commV (autI hV X) from key v hv hvV
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    intro hyV
    have hgen : convI hV ⟨x, hXV hx⟩ (IntMod.mk hV ⟨a⁻¹, V.inv_mem ha⟩) *
        (IntMod.mk hV ⟨a⁻¹, V.inv_mem ha⟩)⁻¹ ∈ commV (autI hV X) :=
      Subgroup.subset_closure ⟨_, convI_mem_autI hV hx (hXV hx), _, rfl⟩
    convert hgen using 1
    apply IntMod.val_injective
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
    show ⁅a, x⁆ = x * a⁻¹ * x⁻¹ * (a⁻¹)⁻¹
    rw [commutatorElement_def, inv_inv]
    have hcomm : x * a⁻¹ * x⁻¹ * a = a * (x * a⁻¹ * x⁻¹) := by
      have := hV.1
      exact setLike_mul_comm ((Subgroup.mem_normalizer_iff.mp (hXV hx) _).mp (V.inv_mem ha)) ha
    rw [hcomm]
    group
  | one => intro h1; exact Subgroup.one_mem _
  | mul a b ha' hb' ha hb =>
    intro hab
    have h1 := ha (hle ha')
    have h2 := hb (hle hb')
    have := Subgroup.mul_mem _ h1 h2
    convert this using 1
    exact IntMod.val_injective (by rw [IntMod.val_mul]; rfl)
  | inv a ha' ha =>
    intro hai
    have h1 := ha (hle ha')
    have := Subgroup.inv_mem _ h1
    convert this using 1
    exact IntMod.val_injective (by rw [IntMod.val_inv]; rfl)

theorem eq_one_or_eq_of_mem_zpowers {X : Type*} [Group X] {a x : X} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  have e : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [e, h, zpow_zero]
  · right; rw [e, h, zpow_one]

theorem altDn_five_ker : ∀ x ∈ (FFModel.altDn 5).ker, x = 1 := by
  rintro x ⟨hx1, hx2⟩
  have ha : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide +kernel
  rcases eq_one_or_eq_of_mem_zpowers ha hx1 with h | h
  · exact h
  · exfalso
    rw [h] at hx2
    have h3 : (∑ i : Fin 5, Multiplicative.toAdd (G6.allOnes 5) i) = 0 := hx2
    revert h3
    decide +kernel

theorem cThree_mem_alt : cThree ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem cThree'_mem_alt : cThree' ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

variable [Finite G] {T L I : Subgroup G}

theorem false_of_isL2Natural_case2 (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {K : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))} {m : ℕ}
    (hK : E2.IsL2Natural K (fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L))) m)
    (hAK : autI (SecA.isElemAbelian_fsuVM hyp) L ≤ K) : False := by
  obtain ⟨-, hcU, π, hπ⟩ := h2
  obtain ⟨β, hβs, hβk, hβe⟩ := RealizesVia.coordSec altDn_five_ker hπ
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hβinj : ∀ u u' : ↥(⊤ : Subgroup ↥(fsuUL T L I)), β u = β u' → u = u' := by
    intro u u' h
    have h1 : β (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 := (hβk _).mp h1
    rw [Subgroup.mem_bot] at h3
    have h4 : u⁻¹ * u' = 1 := Subtype.ext h3
    rw [← mul_left_cancel_iff (a := u⁻¹), h4, inv_mul_cancel]
  set γ3 : ↥(alternatingGroup (Fin 5)) := ⟨cThree, cThree_mem_alt⟩
  set γ3' : ↥(alternatingGroup (Fin 5)) := ⟨cThree', cThree'_mem_alt⟩
  obtain ⟨x, hxL, hx⟩ := SecA.mem_autOn_iff'.mp (π γ3).2
  obtain ⟨y, hyL, hy⟩ := SecA.mem_autOn_iff'.mp (π γ3').2
  obtain ⟨w, hw⟩ := hβs ⟨Multiplicative.ofAdd vThree, isEven_vThree⟩
  have hcoord : ∀ γ : ↥(alternatingGroup (Fin 5)),
      ((β ⟨((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) (w : ↥(fsuUL T L I)),
        Subgroup.mem_top _⟩ : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb) =
        Multiplicative.ofAdd (pact (γ : Equiv.Perm (Fin 5)) vThree) := by
    intro γ
    rw [hβe γ w (Subgroup.mem_top _), hw]
    rfl
  have hxw : (x : G) * ((w : ↥(fsuUL T L I)) : G) * (x : G)⁻¹ = ((w : ↥(fsuUL T L I)) : G) := by
    have h1 := hcoord γ3
    rw [show (γ3 : Equiv.Perm (Fin 5)) = cThree from rfl, pact_cThree_vThree] at h1
    have h3 := hβinj _ w (Subtype.ext (h1.trans (congrArg Subtype.val hw).symm))
    have h4 := congrArg (fun u : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((u : ↥(fsuUL T L I)) : G)) h3
    simp only at h4
    rw [← hx, SecA.coe_conjAct_apply'] at h4
    exact h4
  have hyw : (y : G) * ((w : ↥(fsuUL T L I)) : G) * (y : G)⁻¹ ≠ ((w : ↥(fsuUL T L I)) : G) := by
    intro h5
    apply pact_cThree'_vThree
    have h1 := hcoord γ3'
    have e : (⟨((π γ3' : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
        (w : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = w := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hy, SecA.coe_conjAct_apply']
      exact h5
    rw [e, hw] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  have hle : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hwU : ((w : ↥(fsuUL T L I)) : G) ∈ fsuUL T L I := (w : ↥(fsuUL T L I)).2
  set w' : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp) := IntMod.mk _ ⟨_, hle hwU⟩
  have hxN : (x : G) ∈ Subgroup.normalizer (fsuVM T L I : Set G) := hLN hxL
  have hyN : (y : G) ∈ Subgroup.normalizer (fsuVM T L I : Set G) := hLN hyL
  have hk : convI (SecA.isElemAbelian_fsuVM hyp) ⟨x, hxN⟩ ∈ K := hAK (convI_mem_autI _ hxL hxN)
  have hfix : convI (SecA.isElemAbelian_fsuVM hyp) ⟨x, hxN⟩ w' = w' :=
    (convI_fix_iff _ _ w').mpr hxw
  have hwK : w' ∈ commV K :=
    Subgroup.closure_mono (fun z hz => by obtain ⟨g, hg, v, e⟩ := hz; exact ⟨g, hAK hg, v, e⟩)
      (mk_mem_commV_of_mem_commutator _ hLN hwU (hle hwU))
  have hwC : w' ∉ fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L)) := fun h =>
    hyw ((convI_fix_iff _ _ w').mp (h _ (convI_mem_autI _ (SecA.le_fsuL0 T L hyL) hyN)))
  have hsq := mul_self_eq_one_of_isL2Natural hK hk hwK hwC hfix
  rw [← map_mul] at hsq
  have hxx := (convI_eq_one_iff _ _).mp hsq
  have hπ1 : ∀ v : ↥(fsuUL T L I), ((π γ3 : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
      (((π γ3 : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) v) = v := by
    intro v
    rw [← hx]
    apply Subtype.ext
    rw [SecA.coe_conjAct_apply', SecA.coe_conjAct_apply']
    have h1 := Subgroup.mem_centralizer_iff.mp hxx (v : G) (hle v.2)
    simp only [Subgroup.coe_mul] at h1
    calc (x : G) * ((x : G) * (v : G) * (x : G)⁻¹) * (x : G)⁻¹ =
        ((x : G) * x * v) * ((x : G) * x)⁻¹ := by group
      _ = v := by rw [← h1]; group
  obtain ⟨u, hu⟩ := hβs ⟨Multiplicative.ofAdd vTwo, isEven_vTwo⟩
  set u1 : ↥(⊤ : Subgroup ↥(fsuUL T L I)) :=
    ⟨((π γ3 : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) (u : ↥(fsuUL T L I)),
      Subgroup.mem_top _⟩
  have h1 := hβe γ3 u (Subgroup.mem_top _)
  have h2 := hβe γ3 u1 (Subgroup.mem_top _)
  have e : (⟨((π γ3 : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) (u1 : ↥(fsuUL T L I)),
      Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = u := Subtype.ext (hπ1 u)
  rw [e, hu] at h2
  rw [show u1 = ⟨((π γ3 : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
      (u : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ from rfl, h1, hu] at h2
  have h3 : Multiplicative.ofAdd vTwo = Multiplicative.ofAdd (pact cThree (pact cThree vTwo)) := h2
  apply pact_cThree_sq_vTwo
  rw [CFSG.QuasithinUnique.A5.Delta5.pact_mul]
  exact (Multiplicative.ofAdd.injective h3).symm

theorem ident_case2
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {I' : Finset (Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))}
    (hKJ : twoResidual (fsuL0 T L ⊔ T) ≤ thompsonJ (fsuL0 T L ⊔ T))
    (hcard : I'.card = 1 ∨ I'.card = 2)
    (hJeq : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = ⨆ K ∈ I', K)
    (hcomm : ∀ K ∈ I', ∀ K' ∈ I', K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hind : ∀ K ∈ I', K ⊓ ⨆ K' ∈ I', ⨆ (_ : K' ≠ K), K' = ⊥)
    (htrans : ∀ K ∈ I', ∀ K' ∈ I',
      ∃ s ∈ autI (SecA.isElemAbelian_fsuVM hyp) T, B1.conjAut s K = K')
    (htype : ∀ K ∈ I', (∃ m, E2.IsL2Natural K (fixV (autI (SecA.isElemAbelian_fsuVM hyp)
      (twoResidual (fsuL0 T L ⊔ T)))) m) ∨ E2.IsA5Module K) :
    (∀ K ∈ I', E2.IsA5Module K) ∧ ∃ K₁ ∈ I', ∃ K₂ ∈ I', (∀ K ∈ I', K = K₁ ∨ K = K₂) ∧
      K₁ ≠ K₂ ∧ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = K₁ ⊔ K₂ ∧
      oTwoUpper K₁ = autI (SecA.isElemAbelian_fsuVM hyp) L ∧
      oTwoUpper K₂ = autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) ∧
      (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ K₁ ⊓ K₂ = ⊥ := by
  rw [twoResidual_fsuL0_sup h37 h38 hyp] at htype
  have hid := ident_L0T h37 h38 h322 hyp ht htn hKJ hcard hJeq hcomm hind htrans
  have hA5 : ∀ K ∈ I', E2.IsA5Module K := by
    by_contra hne
    push Not at hne
    obtain ⟨K₀, hK₀, hn⟩ := hne
    have hall : ∀ K ∈ I', ∃ m, E2.IsL2Natural K
        (fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L))) m := by
      intro K hK
      rcases htype K hK with h | h5
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := (htype K₀ hK₀).resolve_right hn
        obtain ⟨s, -, hs⟩ := htrans K₀ hK₀ K hK
        have hc := SecA.card_of_isL2Natural hm
        rw [← SecA.card_conjAut s K₀, hs, SecA.card_of_isA5Module h5] at hc
        exact two_pow_mul_ne_120 m hc.symm
    rcases hid with ⟨K, hK, -, -, hO⟩ | ⟨K₁, hK₁, -, -, -, -, -, hO₁, -, -, -⟩
    · obtain ⟨m, hm⟩ := hall K hK
      exact false_of_isL2Natural_case2 hyp h2 hm
        (le_sup_left.trans (hO.symm.le.trans (oTwoUpper_le K)))
    · obtain ⟨m, hm⟩ := hall K₁ hK₁
      exact false_of_isL2Natural_case2 hyp h2 hm (hO₁ ▸ oTwoUpper_le K₁)
  refine ⟨hA5, ?_⟩
  rcases hid with ⟨K, hK, -, -, hO⟩ | h
  · exfalso
    obtain ⟨-, a, b, hab⟩ := SecA.isSimpleGroup_autOn h37 h38 h322 hyp
    obtain ⟨-, hBn⟩ := isSimpleGroup_autI_conjugate h37 h38 h322 hyp ht
    exact false_of_isSimpleGroup (isSimpleGroup_oTwoUpper_of_isA5Module (hA5 K hK))
      ⟨a.1, a.2, b.1, b.2, fun h => hab (Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h))⟩ hBn
      (autI_commute h37 h322 hyp ht htn) hO.ge hO.le
  · exact h

end CFSG.Quasithin.Vol2.Ch10.SecE
