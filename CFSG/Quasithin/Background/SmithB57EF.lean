module

public import CFSG.Quasithin.Background.SmithB57ED
public import CFSG.Quasithin.Background.SmithB57EE
public import CFSG.Quasithin.Background.S1549DA6Dict
public import CFSG.Quasithin.Background.F918D1

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC CFSG.Quasithin.S143 Equiv
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem not_mem_of_not_mem_centralizer {t : MulAut V}
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) : t ∉ L := by
  intro htL
  apply htX
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact S.commute_X x hx t htL

end Hyp

section Perms

abbrev t34 : Perm (Fin 6) := swap 3 4

abbrev c345 : Perm (Fin 6) := swap 3 4 * swap 4 5

abbrev c012 : Perm (Fin 6) := swap 0 1 * swap 1 2

theorem t34_not_mem : t34 ∉ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem c345_mem : c345 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem c012_mem : c012 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem perm_facts : t34 * t34 = 1 ∧ t34 ≠ 1 ∧ c345 ^ 3 = 1 ∧ c345 ≠ 1 ∧
    t34 * c345 * t34⁻¹ = c345⁻¹ ∧ c012 ^ 3 = 1 ∧ c012 ≠ 1 ∧ c012 * t34 = t34 * c012 ∧
    c012 * c345 = c345 * c012 := by
  decide

end Perms

structure SixData {G L : Subgroup (MulAut V)} (S : Hyp G L) (A : Subgroup (MulAut V)) where
  hP4 : AsB15Part4
  hA21 : AsA21SQTKSection
  hB51 : AsB51
  hA : IsFFStarOffender G A
  hAX : ¬ A ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))
  hI : commV L ∈ IrrPlus L ⊤
  π : Perm (Fin 6) ≃* ↥(L ⊔ A)
  real : (FFModel.symDn 6).RealizesVia (L ⊔ A) (commV L) (fixV L ⊓ commV L) π.toMonoidHom
  alt : ∀ σ, ((π σ : ↥(L ⊔ A)) : MulAut V) ∈ L ↔ σ ∈ alternatingGroup (Fin 6)

namespace SixData

variable {G L A : Subgroup (MulAut V)} {S : Hyp G L} (D : SixData S A)
include D

@[expose] def f (σ : Perm (Fin 6)) : MulAut V := ((D.π σ : ↥(L ⊔ A)) : MulAut V)

theorem f_mul (σ τ : Perm (Fin 6)) : D.f (σ * τ) = D.f σ * D.f τ := by simp [f]

theorem f_one : D.f 1 = 1 := by simp [f]

theorem f_inv (σ : Perm (Fin 6)) : D.f σ⁻¹ = (D.f σ)⁻¹ := by simp [f]

theorem f_pow (σ : Perm (Fin 6)) (n : ℕ) : D.f (σ ^ n) = D.f σ ^ n := by simp [f]

theorem f_injective : Function.Injective D.f := Subtype.val_injective.comp D.π.injective

theorem f_mem (σ : Perm (Fin 6)) : D.f σ ∈ L ⊔ A := (D.π σ).2

theorem hMG : L ⊔ A ≤ G := sup_le S.hLG D.hA.1

theorem f_mem_G (σ : Perm (Fin 6)) : D.f σ ∈ G := D.hMG (D.f_mem σ)

theorem f_surj {m : MulAut V} (hm : m ∈ L ⊔ A) : ∃ σ, D.f σ = m :=
  ⟨D.π.symm ⟨m, hm⟩, by simp [f]⟩

theorem mem_L_iff (σ : Perm (Fin 6)) : D.f σ ∈ L ↔ σ ∈ alternatingGroup (Fin 6) := D.alt σ

theorem commutator_eq : ⁅L ⊔ A, L ⊔ A⁆ = L := S.commutator_sup D.hP4 D.hA

theorem altNat : AlternatingNatural L (commV L) (fixV L ⊓ commV L) 6 := by
  have := B5.alternatingNatural_derived (by norm_num) ⟨D.π.toMonoidHom, D.real⟩
  rwa [D.commutator_eq] at this

theorem trivial_U : ∀ x ∈ pCoreOf 3 G, ∀ u ∈ commV L, x u = u := fun x hx =>
  trivial_on_commV_alt D.hI (by norm_num) D.altNat (fun l hl => S.commute_X x hx l hl)

theorem U_le_W : commV L ≤ fixV (pCoreOf 3 G) := fun u hu x hx => D.trivial_U x hx u hu

theorem exists_t : ∃ t ∈ A, t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)) := by
  by_contra h
  push Not at h
  exact D.hAX h

theorem t_sq {t : MulAut V} (ht : t ∈ A) : t * t = 1 := by
  simpa [sq] using D.hA.2.2.1.2 t ht

theorem mem_or_mul_mem {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) {m : MulAut V}
    (hm : m ∈ L ⊔ A) : m ∈ L ∨ m * t ∈ L := by
  by_cases hmL : m ∈ L
  · exact Or.inl hmL
  right
  obtain ⟨σ, rfl⟩ := D.f_surj hm
  obtain ⟨σt, hσt⟩ := D.f_surj ((le_sup_right : A ≤ L ⊔ A) ht)
  rw [← hσt, ← D.f_mul, D.mem_L_iff]
  have h1 : σ ∉ alternatingGroup (Fin 6) := fun h => hmL ((D.mem_L_iff σ).2 h)
  have h2 : σt ∉ alternatingGroup (Fin 6) := fun h =>
    S.not_mem_of_not_mem_centralizer htX (hσt ▸ (D.mem_L_iff σt).2 h)
  rw [Perm.mem_alternatingGroup] at h1 h2 ⊢
  rw [map_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact absurd h h1
  rcases Int.units_eq_one_or (Perm.sign σt) with h' | h'
  · exact absurd h' h2
  rw [h, h']
  rfl

theorem conj_eq_t {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) {m : MulAut V}
    (hm : m ∈ L ⊔ A) (hmL : m ∉ L) {x : MulAut V} (hx : x ∈ pCoreOf 3 G) :
    m * x * m⁻¹ = t * x * t⁻¹ := by
  have hmt : m * t ∈ L := (D.mem_or_mul_mem ht htX hm).resolve_left hmL
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (D.t_sq ht)
  exact S.conj_X_eq (by rw [htinv]; exact hmt) hx (D.hA.1 ht)

theorem inf_X : L ⊓ pCoreOf 3 G = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzL, hzX⟩
  rw [Subgroup.mem_bot]
  obtain ⟨σ, rfl⟩ := D.f_surj ((le_sup_left : L ≤ L ⊔ A) hzL)
  have hσA : σ ∈ alternatingGroup (Fin 6) := (D.mem_L_iff σ).1 hzL
  have hσ : σ = 1 := by
    refine center_alt6 σ fun τ hτ => D.f_injective ?_
    rw [D.f_mul, D.f_mul]
    exact S.commute_X _ hzX _ ((D.mem_L_iff τ).2 hτ)
  rw [hσ, D.f_one]

theorem eq_one_of_commute {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) {d : MulAut V}
    (hdX : d ∈ pCoreOf 3 G) (hdt : d * t = t * d) : d = 1 := by
  by_contra hd1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (pCore3_isPGroup G)) ⟨d, hdX⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hd1 hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set e := d ^ 3 ^ j with he
  have heX : e ∈ pCoreOf 3 G := (pCoreOf 3 G).pow_mem hdX _
  have hord : orderOf e = 3 := by
    rw [he, orderOf_pow_of_dvd (pow_ne_zero j (by norm_num))
      (by rw [hk]; exact pow_dvd_pow 3 (Nat.le_succ j)), hk, Nat.pow_div (Nat.le_succ j)
      (by norm_num)]
    simp
  have he3 : e ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one e
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have het : e * t = t * e := (Commute.pow_left hdt _ : Commute e t)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := perm_facts
  have hxL : D.f c012 ∈ L := (D.mem_L_iff _).2 c012_mem
  have hcL : D.f c345 ∈ L := (D.mem_L_iff _).2 c345_mem
  have htL : D.f t34 ∉ L := fun h => t34_not_mem ((D.mem_L_iff _).1 h)
  refine false_of_commuting_threes S.hq (t := D.f t34) (c := D.f c345) (x := D.f c012) (y := e)
    (D.f_mem_G _) (D.f_mem_G _) (D.f_mem_G _) ((pCore3_le G) heX) ?_ ?_ ?_ ?_ ?_ ?_ ?_ he3
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← D.f_mul, h1, D.f_one]
  · intro h
    exact h2 (D.f_injective (h.trans D.f_one.symm))
  · rw [← D.f_pow, h3, D.f_one]
  · intro h
    exact h4 (D.f_injective (h.trans D.f_one.symm))
  · rw [← D.f_inv, ← D.f_mul, ← D.f_mul, h5, D.f_inv]
  · intro h
    exact h7 (D.f_injective (h.trans D.f_one.symm))
  · rw [← D.f_pow, h6, D.f_one]
  · exact (S.commute_X e heX _ hxL).symm
  · intro hmem
    have hle : Subgroup.zpowers (D.f c012) ≤ L := (Subgroup.zpowers_le).2 hxL
    have : e ∈ L ⊓ pCoreOf 3 G := ⟨hle hmem, heX⟩
    rw [D.inf_X, Subgroup.mem_bot] at this
    exact he1 this
  · rw [← D.f_mul, ← D.f_mul, h8]
  · rw [← D.f_mul, ← D.f_mul, h9]
  · have hconj := D.conj_eq_t ht htX (D.f_mem t34) htL heX
    have h' : t * e * t⁻¹ = e := by rw [← het]; group
    rw [h'] at hconj
    calc e * D.f t34 = D.f t34 * e * (D.f t34)⁻¹ * D.f t34 := by rw [hconj]
      _ = D.f t34 * e := by group
  · exact S.commute_X e heX _ hcL

theorem conj_inv {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) :
    ∀ x ∈ pCoreOf 3 G, t * x * t⁻¹ = x⁻¹ := by
  set X := pCoreOf 3 G with hX
  have htt : t * t = 1 := D.t_sq ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) (D.hA.1 ht)) x).1 hx
  let φ : ↥X → ↥X := fun x => ⟨(x : MulAut V)⁻¹ * (t * x * t⁻¹), X.mul_mem (X.inv_mem x.2)
    (hconj _ x.2)⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    simp only [φ] at h
    set a : MulAut V := (x : MulAut V) with ha
    set b : MulAut V := (y : MulAut V) with hb
    have e1 : b * a⁻¹ = t * (b * a⁻¹) * t⁻¹ := by
      calc b * a⁻¹ = b * (a⁻¹ * (t * a * t⁻¹)) * (t * a⁻¹ * t⁻¹) := by group
        _ = b * (b⁻¹ * (t * b * t⁻¹)) * (t * a⁻¹ * t⁻¹) := by rw [h]
        _ = t * (b * a⁻¹) * t⁻¹ := by group
    have hc : b * a⁻¹ * t = t * (b * a⁻¹) := by
      calc b * a⁻¹ * t = t * (b * a⁻¹) * t⁻¹ * t := by rw [← e1]
        _ = t * (b * a⁻¹) := by group
    have h1 := D.eq_one_of_commute ht htX (X.mul_mem y.2 (X.inv_mem x.2)) hc
    exact (Subtype.ext (mul_inv_eq_one.1 h1)).symm
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  intro z hz
  obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
  have hz' : z = (x : MulAut V)⁻¹ * (t * x * t⁻¹) := (congrArg Subtype.val hx).symm
  set a : MulAut V := (x : MulAut V) with ha
  rw [hz', htinv]
  have lhs : t * (a⁻¹ * (t * a * t)) * t = t * a⁻¹ * t * a * (t * t) := by
    simp only [mul_assoc]
  have rhs : (a⁻¹ * (t * a * t))⁻¹ = t * a⁻¹ * t * a := by
    simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
  rw [lhs, rhs, htt, mul_one]

theorem commute_X {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) :
    ∀ x ∈ pCoreOf 3 G, ∀ y ∈ pCoreOf 3 G, x * y = y * x := by
  intro x hx y hy
  have h := D.conj_inv ht htX (x * y) ((pCoreOf 3 G).mul_mem hx hy)
  have hx' := D.conj_inv ht htX x hx
  have hy' := D.conj_inv ht htX y hy
  have e : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
  rw [e, hx', hy'] at h
  have h2 : (x * y)⁻¹ = (y * x)⁻¹ := by rw [← h, mul_inv_rev]
  exact inv_injective h2

theorem card_C_le : Nat.card ↥(fixV L ⊓ commV L) ≤ 2 := by
  have h := asI161A6_of V S.hV L (commV L) (fun l hl u hu => D.hI.2.1 ⟨l, hl⟩ u hu) D.hI.2.2.1
    (by rw [inf_comm]; exact D.altNat)
  rwa [inf_comm] at h

theorem fix_C {g : MulAut V} (hg : g ∈ G) {c : V} (hc : c ∈ fixV L ⊓ commV L) : g c = c := by
  by_cases hc1 : c = 1
  · rw [hc1, map_one]
  have hgc : g c ∈ fixV L ⊓ commV L := by
    refine ⟨FFC.fixV_invariant (fun x hx => ?_) hc.1,
      FFC.commV_invariant (S.conj_mem D.hP4 hg) hc.2⟩
    have := S.conj_mem D.hP4 (G.inv_mem hg) x hx
    simpa using this
  by_contra hne
  have hgc1 : g c ≠ 1 := fun h => hc1 (g.injective (h.trans (map_one g).symm))
  have h3 : 3 ≤ Nat.card ↥(fixV L ⊓ commV L) := by
    classical
    have := Fintype.ofFinite ↥(fixV L ⊓ commV L)
    have hsub : ({1, ⟨c, hc⟩, ⟨g c, hgc⟩} : Finset ↥(fixV L ⊓ commV L)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        exact hne (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hc1 (congrArg Subtype.val h).symm, fun h => hgc1 ?_⟩
        exact (congrArg Subtype.val h).symm
    rw [← hsub, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  have := D.card_C_le
  omega

theorem exists_theta : ∃ Θ : ↥(commV L) →* N6, Function.Surjective Θ ∧
    (∀ u, Θ u = 1 ↔ (u : V) ∈ fixV L ⊓ commV L) ∧
    ∀ (σ : Perm (Fin 6)) (u : ↥(commV L)) (hu : D.f σ u ∈ commV L),
      Θ ⟨D.f σ u, hu⟩ = n6Act σ (Θ u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := D.real
  refine ⟨S1549D.psiN6.toMonoidHom.comp β, S1549D.psiN6.surjective.comp hβs, fun u => ?_,
    fun σ u hu => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m₀, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hact : G6.permAct 6 σ m₀.1 ∈ G6.coreMod 6 := G6.permAct_mem_coreMod σ m₀.2
    have h1 := hβe σ u m₀ hu hact hm.symm
    show S1549D.psiN6 (β ⟨D.f σ u, hu⟩) = n6Act σ (S1549D.psiN6 (β u))
    have h1' : β ⟨D.f σ u, hu⟩ = (QuotientGroup.mk ⟨G6.permAct 6 σ m₀.1, hact⟩ :
        (FFModel.symDn 6).Mod) := h1
    rw [h1', ← hm]
    exact S1549D.n6Rep_permAct σ m₀

end SixData

end SmithB57E

end CFSG.Quasithin
