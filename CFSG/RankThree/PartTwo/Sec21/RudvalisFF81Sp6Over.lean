module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6OverGrp
import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.Quasithin.AppendixH.H14.H141Octad
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open CFSG.Quasithin.H13.MatNCert Matrix

section Rep

variable {X : Type} [Group X] {C T : Subgroup X}

@[expose] def conjT (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) (g : ↥C) : ↥T →* ↥T where
  toFun u := ⟨(g : X) * u * (g : X)⁻¹, hTn g g.2 u u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjT_apply (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) (g : ↥C) (u : ↥T) :
    ((conjT hTn g u : ↥T) : X) = (g : X) * u * (g : X)⁻¹ := rfl

@[expose] noncomputable def coordT (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T)
    (κ : ↥T ≃* Multiplicative V7) (g : ↥C) : V7 →ₗ[ZMod 2] V7 where
  toFun v := Multiplicative.toAdd (κ (conjT hTn g (κ.symm (Multiplicative.ofAdd v))))
  map_add' v w := by
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]
  map_smul' c v := by
    rw [RingHom.id_apply]
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key c with rfl | rfl
    · rw [zero_smul, zero_smul, ofAdd_zero, map_one, map_one, map_one, toAdd_one]
    · rw [one_smul, one_smul]

theorem coordT_apply (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) (κ : ↥T ≃* Multiplicative V7)
    (g : ↥C) (v : V7) : coordT hTn κ g v =
      Multiplicative.toAdd (κ (conjT hTn g (κ.symm (Multiplicative.ofAdd v)))) := rfl

@[expose] noncomputable def rhoT (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T)
    (κ : ↥T ≃* Multiplicative V7) : ↥C →* GL (Fin 7) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix' (coordT hTn κ g)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro v
        rw [coordT_apply, LinearMap.id_apply]
        have h : conjT hTn 1 (κ.symm (Multiplicative.ofAdd v)) =
            κ.symm (Multiplicative.ofAdd v) := Subtype.ext (by simp [conjT_apply])
        rw [h, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      map_mul' := fun g g' => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro v
        rw [LinearMap.comp_apply, coordT_apply, coordT_apply, coordT_apply, ofAdd_toAdd,
          MulEquiv.symm_apply_apply]
        congr 2
        apply Subtype.ext
        simp only [conjT_apply, Subgroup.coe_mul, _root_.mul_inv_rev]
        group }

theorem rhoT_mulVec (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) (κ : ↥T ≃* Multiplicative V7)
    (g : ↥C) (u : ↥T) : ((rhoT hTn κ g : GL (Fin 7) (ZMod 2)) : M7) *ᵥ
      Multiplicative.toAdd (κ u) = Multiplicative.toAdd (κ (conjT hTn g u)) := by
  show LinearMap.toMatrix' (coordT hTn κ g) *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec, coordT_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem rhoT_eq_one_iff (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T)
    (κ : ↥T ≃* Multiplicative V7) (g : ↥C) :
    rhoT hTn κ g = 1 ↔ (g : X) ∈ CenS T := by
  rw [Units.ext_iff, Units.val_one]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := rhoT_mulVec hTn κ g ⟨u, hu⟩
    rw [h, Matrix.one_mulVec] at h1
    have h2 := congrArg Subtype.val (κ.injective (Multiplicative.toAdd.injective h1))
    rw [conjT_apply] at h2
    simp only at h2
    rw [eq_mul_inv_iff_mul_eq] at h2
    exact h2
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro v
    obtain ⟨u, rfl⟩ : ∃ u : ↥T, Multiplicative.toAdd (κ u) = v :=
      ⟨κ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [rhoT_mulVec, Matrix.one_mulVec]
    congr 2
    apply Subtype.ext
    rw [conjT_apply, mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_centralizer_iff.mp h) u u.2).symm

end Rep

section Fix

variable {X : Type} [Group X] {C T : Subgroup X}

theorem card_T_inf_cen (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) (κ : ↥T ≃* Multiplicative V7)
    {b : X} (hb : b ∈ C) :
    Nat.card ↥(T ⊓ Cen b) =
      Nat.card {v : V7 // ((rhoT hTn κ ⟨b, hb⟩ : GL (Fin 7) (ZMod 2)) : M7) *ᵥ v = v} := by
  have hfix : ∀ u : ↥T, ((rhoT hTn κ ⟨b, hb⟩ : GL (Fin 7) (ZMod 2)) : M7) *ᵥ
      Multiplicative.toAdd (κ u) = Multiplicative.toAdd (κ u) ↔ (u : X) ∈ Cen b := by
    intro u
    rw [rhoT_mulVec, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h2 := congrArg Subtype.val (κ.injective (Multiplicative.toAdd.injective h))
      rw [conjT_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h
      congr 2
      apply Subtype.ext
      rw [conjT_apply]
      exact mul_inv_eq_iff_eq_mul.mpr h.symm
  refine Nat.card_congr
    { toFun := fun u => ⟨Multiplicative.toAdd (κ ⟨u, (Subgroup.mem_inf.mp u.2).1⟩),
        (hfix _).mpr (Subgroup.mem_inf.mp u.2).2⟩
      invFun := fun v => ⟨(κ.symm (Multiplicative.ofAdd v.1) : X), Subgroup.mem_inf.mpr
        ⟨(κ.symm (Multiplicative.ofAdd v.1)).2, (hfix _).mp (by simpa using v.2)⟩⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem card_fix_conj (A : M7) (P Q : M7) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Nat.card {v : V7 // (P * A * Q) *ᵥ v = v} = Nat.card {v : V7 // A *ᵥ v = v} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨Q *ᵥ v.1, ?_⟩
      invFun := fun v => ⟨P *ᵥ v.1, ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun v => Subtype.ext ?_ }
  · have h := congrArg (fun w => Q *ᵥ w) v.2
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at h
    rw [Matrix.mulVec_mulVec]
    exact h
  · rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (P * A) Q P, hQP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, v.2]
  · simp [Matrix.mulVec_mulVec, hPQ]
  · simp [Matrix.mulVec_mulVec, hQP]

theorem card_fix_decN {b : List ℕ} (hb : ValidN 7 b) :
    Nat.card {v : V7 // decN 7 b *ᵥ v = v} =
      ((List.range 128).filter fun v => mvN b v == v).length := by
  have hcard : Nat.card {v : V7 // decN 7 b *ᵥ v = v} =
      Nat.card {n : Fin 128 // mvN b n = n} := by
    refine Nat.card_congr
      { toFun := fun v => ⟨⟨codeN v.1, codeN_lt _⟩, ?_⟩
        invFun := fun n => ⟨vecN 7 n.1, ?_⟩
        left_inv := fun v => Subtype.ext ?_
        right_inv := fun n => Subtype.ext (Fin.ext ?_) }
    · refine vecN_inj (n := 7) (mvN_lt hb.2 _) (codeN_lt _) ?_
      rw [← decN_mulVec hb.1, vecN_codeN, v.2]
    · rw [decN_mulVec hb.1, n.2]
    · exact vecN_codeN _
    · exact codeN_vecN n.1.2
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter fun n : Fin 128 => mvN b n = n).card =
      ((Finset.range 128).filter fun v => mvN b v = v).card := by
    refine Finset.card_bij (fun n _ => n.1) (fun n hn => ?_) (fun a _ b _ h => Fin.ext h)
      (fun v hv => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.2, hn⟩
    · obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, Finset.mem_range.mp hv1⟩, by simpa using hv2, rfl⟩
  rw [e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]
  congr 1

end Fix

section Coprime

variable {X : Type} [Group X] [Finite X]

theorem exists_mul_mem_cen {C T : Subgroup X} (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T)
    {H : Type*} [Group H] (ψ : ↥C →* H) (hker : ∀ g : ↥C, ψ g = 1 ↔ (g : X) ∈ T)
    {b : X} (hb : b ∈ C) (hb3 : b ^ 3 = 1) (hT3 : ¬ 3 ∣ Nat.card T)
    {g : X} (hg : g ∈ C) (hcomm : ψ ⟨g, hg⟩ * ψ ⟨b, hb⟩ = ψ ⟨b, hb⟩ * ψ ⟨g, hg⟩) :
    ∃ t ∈ T, g * t ∈ Cen b := by
  classical
  have hd : g⁻¹ * b * g * b⁻¹ ∈ T := by
    have hmem : g⁻¹ * b * g * b⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hg) hb) hg) (C.inv_mem hb)
    refine (hker ⟨_, hmem⟩).mp ?_
    have e : (⟨g⁻¹ * b * g * b⁻¹, hmem⟩ : ↥C) =
        (⟨g, hg⟩ : ↥C)⁻¹ * ⟨b, hb⟩ * ⟨g, hg⟩ * (⟨b, hb⟩ : ↥C)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc (ψ ⟨g, hg⟩)⁻¹, ← hcomm]
    group
  have hτmem : ∀ t : ↥T, g⁻¹ * b * (g * t) * b⁻¹ ∈ T := by
    intro t
    have e : g⁻¹ * b * (g * t) * b⁻¹ = (g⁻¹ * b * g * b⁻¹) * (b * t * b⁻¹) := by group
    rw [e]
    exact T.mul_mem hd (hTn b hb t t.2)
  set τf : ↥T → ↥T := fun t => ⟨g⁻¹ * b * (g * t) * b⁻¹, hτmem t⟩ with hτf
  have hτ3 : ∀ t, τf (τf (τf t)) = t := by
    intro t
    apply Subtype.ext
    simp only [hτf]
    have hb3' : b * b * b = 1 := by rw [mul_assoc, ← pow_three]; exact hb3
    have e : ∀ x : X, g⁻¹ * b * (g * (g⁻¹ * b * (g * (g⁻¹ * b * (g * x) * b⁻¹)) * b⁻¹)) *
        b⁻¹ = g⁻¹ * (b * b * b) * g * x * (b * b * b)⁻¹ := fun x => by group
    rw [e, hb3']
    group
  let τ : Equiv.Perm ↥T :=
    { toFun := τf, invFun := fun t => τf (τf t), left_inv := hτ3, right_inv := hτ3 }
  have hτp : τ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    apply Equiv.ext
    intro t
    rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply]
    exact hτ3 t
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ↥T := Fintype.ofFinite _
  obtain ⟨t, ht⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rwa [← Nat.card_eq_fintype_card]) hτp
  refine ⟨t, t.2, ?_⟩
  have e := congrArg Subtype.val ht
  change g⁻¹ * b * (g * t) * b⁻¹ = t at e
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * t * b = g * (g⁻¹ * b * (g * t) * b⁻¹) * b := by rw [e]
    _ = b * (g * t) := by group

theorem card_inf_cen_eq {C T : Subgroup X} (hTC : T ≤ C)
    (hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) {H : Type*} [Group H] (ψ : ↥C →* H)
    (hker : ∀ g : ↥C, ψ g = 1 ↔ (g : X) ∈ T) {b : X} (hb : b ∈ C) (hb3 : b ^ 3 = 1)
    (hT3 : ¬ 3 ∣ Nat.card T) :
    Nat.card ↥(C ⊓ Cen b) = Nat.card ↥(T ⊓ Cen b) *
      Nat.card ↥(ψ.range ⊓ Subgroup.centralizer {ψ ⟨b, hb⟩}) := by
  set φ : ↥(C ⊓ Cen b) →* H := ψ.comp (Subgroup.inclusion inf_le_left) with hφ
  have hφa : ∀ d : ↥(C ⊓ Cen b), φ d = ψ ⟨d, (Subgroup.mem_inf.mp d.2).1⟩ := fun _ => rfl
  have hkerφ : Nat.card φ.ker = Nat.card ↥(T ⊓ Cen b) := by
    refine Nat.card_congr
      { toFun := fun d => ⟨d.1, Subgroup.mem_inf.mpr ⟨(hker _).mp (by rw [← hφa]; exact d.2),
          (Subgroup.mem_inf.mp d.1.2).2⟩⟩
        invFun := fun t => ⟨⟨t, Subgroup.mem_inf.mpr ⟨hTC (Subgroup.mem_inf.mp t.2).1,
          (Subgroup.mem_inf.mp t.2).2⟩⟩, by
            rw [MonoidHom.mem_ker, hφa]; exact (hker _).mpr (Subgroup.mem_inf.mp t.2).1⟩
        left_inv := fun d => rfl
        right_inv := fun t => rfl }
  have hrange : φ.range = ψ.range ⊓ Subgroup.centralizer {ψ ⟨b, hb⟩} := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨_, (hφa d).symm⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hφa, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).2
    · intro hy
      obtain ⟨⟨g', rfl⟩, hy2⟩ := Subgroup.mem_inf.mp hy
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hy2
      obtain ⟨t, ht, hgt⟩ := exists_mul_mem_cen hTn ψ hker hb hb3 hT3 g'.2 (by simpa using hc)
      refine ⟨⟨g' * t, Subgroup.mem_inf.mpr ⟨C.mul_mem g'.2 (hTC ht), hgt⟩⟩, ?_⟩
      rw [hφa]
      have e : (⟨(g' : X) * t, C.mul_mem g'.2 (hTC ht)⟩ : ↥C) = g' * ⟨t, hTC ht⟩ := rfl
      rw [e, map_mul, (hker ⟨t, hTC ht⟩).mpr ht, mul_one]
  rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, hkerφ, hrange]

end Coprime

section Main

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH zH_pow_three)

theorem card_inf_cen_conj {X : Type} [Group X] {C : Subgroup X} {l : X} (hl : l ∈ C) (b : X) :
    Nat.card ↥(C ⊓ Cen (l * b * l⁻¹)) = Nat.card ↥(C ⊓ Cen b) := by
  have hC : C.map (MulAut.conj l).toMonoidHom = C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.mul_mem (C.mul_mem hl hx) (C.inv_mem hl)
    · intro hy
      refine ⟨l⁻¹ * y * l, C.mul_mem (C.mul_mem (C.inv_mem hl) hy) hl, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h := Sp6Transv.card_map_inf_cen (f := (MulAut.conj l).toMonoidHom)
    (MulAut.conj l).injective C b
  rw [hC] at h
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h


theorem kf_sp6Overgroup : KF_Sp6Overgroup := by
  intro X _ _ C T L t₀ β hTC hTn hT hCT hLC hL ht₀ ht₀1 hCt₀ hβL hβ3 hβc hβ10
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated hL
  set f : H6 →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hfL : ∀ g, f g ∈ L := fun g => (e.symm g).2
  have hfC : ∀ g, f g ∈ C := fun g => hLC (hfL g)
  have hmapL : (⊤ : Subgroup H6).map f = L := by
    ext y
    constructor
    · rintro ⟨g, -, rfl⟩
      exact hfL g
    · intro hy
      exact ⟨e ⟨y, hy⟩, Subgroup.mem_top _, by simp [hfdef]⟩
  set x := e ⟨β, hβL⟩ with hxdef
  have hfx : f x = β := by simp [hfdef, hxdef]
  have hx3 : orderOf x = 3 := by rw [← orderOf_injective f hfinj x, hfx, hβ3]
  have hxc : Nat.card (Subgroup.centralizer {x}) = 2160 := by
    have h := Sp6Transv.card_map_inf_cen hfinj ⊤ x
    rw [hmapL, hfx, hβc, top_inf_eq] at h
    exact h.symm
  obtain ⟨m, hm⟩ := Sp6Transv.conj_z1_of_card hx3 hxc
  have hβ' : f m * β * (f m)⁻¹ = f (zH 1) := by rw [← hm, map_mul, map_mul, map_inv, hfx]
  have hβ'10 : ¬ 2 ^ 10 ∣ Nat.card ↥(C ⊓ Cen (f (zH 1))) := by
    rwa [← hβ', card_inf_cen_conj (hfC m)]
  have hTe : CFSG.Open.IsElemAbelian 2 T :=
    CFSG.Open.isElemAbelian_of_isElementaryAbelian (h := hT.1)
  obtain ⟨κ⟩ := CFSG.Quasithin.AppendixH.H14.exists_mulEquiv_elemAbelian_two T hTe 7 hT.2
  set ρ := rhoT hTn κ with hρ
  have hTcen : ∀ u ∈ T, u ∈ CenS T := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hTe.1.is_comm.comm (⟨v, hv⟩ : ↥T) ⟨u, hu⟩)
  have hker : ∀ g : ↥C, ρ g = 1 ↔ (g : X) ∈ T := fun g =>
    (rhoT_eq_one_iff hTn κ g).trans ⟨fun h => hCT (Subgroup.mem_inf.mpr ⟨g.2, h⟩), hTcen _⟩
  set f' : H6 →* ↥C := f.codRestrict C hfC with hf'def
  set x₀ : V7 := Multiplicative.toAdd (κ ⟨t₀, ht₀⟩) with hx₀def
  have hfix : ∀ g : ↥C, ((ρ g : GL7) : M7) *ᵥ x₀ = x₀ := by
    intro g
    rw [hx₀def, rhoT_mulVec]
    congr 2
    apply Subtype.ext
    rw [conjT_apply, mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hCt₀ g.2)
  set M : M7 := ((ρ (f' gamH) : GL7) : M7) with hMdef
  set N : M7 := ((ρ (f' hH) : GL7) : M7) with hNdef
  have hcoe : ∀ (g : H6) (k : ℕ), ((ρ (f' g) : GL7) : M7) ^ k =
      ((ρ (f' (g ^ k)) : GL7) : M7) := by
    intro g k
    rw [map_pow, map_pow, Units.val_pow_eq_pow_val]
  have hM7 : M ^ 7 = 1 := by rw [hMdef, hcoe, gamH_pow_seven, map_one, map_one, Units.val_one]
  have hN6 : N ^ 6 = 1 := by rw [hNdef, hcoe, hH_pow_six, map_one, map_one, Units.val_one]
  have hNM : N * M = M ^ 3 * N := by
    rw [hMdef, hNdef, hcoe, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, hH_mul_gamH]
  have hM1 : M ≠ 1 := by
    intro h
    have h1 : ρ (f' gamH) = 1 := Units.ext h
    have hT' : f gamH ∈ T := (hker _).mp h1
    have h2 : f (gamH ^ 2) = 1 := by rw [map_pow]; exact hTe.2 _ hT'
    have h3 : gamH ^ 2 = 1 := hfinj (by rw [h2, map_one])
    apply gamH_ne_one
    calc gamH = gamH ^ 7 * ((gamH ^ 2) ^ 3)⁻¹ := by group
      _ = 1 := by rw [gamH_pow_seven, h3, one_pow, inv_one, one_mul]
  have hx₀ : x₀ ≠ 0 := by
    intro h
    apply ht₀1
    have h1 : κ ⟨t₀, ht₀⟩ = 1 := by
      have e1 : κ ⟨t₀, ht₀⟩ = Multiplicative.ofAdd x₀ := rfl
      rw [e1, h, ofAdd_zero]
    have h2 : (⟨t₀, ht₀⟩ : ↥T) = 1 := κ.injective (h1.trans κ.map_one.symm)
    exact congrArg Subtype.val h2
  obtain ⟨P, hPu, hP0, hMP, hNP⟩ := normal_form hM7 hN6 hNM hM1 hx₀ (hfix _) (hfix _)
  set Pu : GL7 := hPu.unit with hPudef
  have hPuv : (Pu : M7) = P := hPu.unit_spec
  have hPinv1 : ((Pu⁻¹ : GL7) : M7) * P = 1 := by
    rw [← hPuv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPinv2 : P * ((Pu⁻¹ : GL7) : M7) = 1 := by
    rw [← hPuv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set ρ' : ↥C →* GL7 := (MulAut.conj Pu⁻¹).toMonoidHom.comp ρ with hρ'def
  have hρ' : ∀ g, ((ρ' g : GL7) : M7) = ((Pu⁻¹ : GL7) : M7) * ((ρ g : GL7) : M7) * P := by
    intro g
    simp only [hρ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, Units.val_mul, hPuv]
  have hρ'e : ∀ g, ((ρ' g : GL7) : M7) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro g
    rw [hρ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP0, hfix, ← hP0,
      Matrix.mulVec_mulVec, hPinv1, Matrix.one_mulVec]
  set σ : H6 →* GL7 := ρ'.comp f' with hσdef
  have hσg : ((σ gamH : GL7) : M7) = decN 7 nGc := by
    rw [← nG_eq]
    show ((ρ' (f' gamH) : GL7) : M7) = nG
    rw [hρ', Matrix.mul_assoc, ← hMdef, hMP, ← Matrix.mul_assoc, hPinv1, Matrix.one_mul]
  have hσh : ((σ hH : GL7) : M7) = decN 7 nHc := by
    rw [← nH_eq]
    show ((ρ' (f' hH) : GL7) : M7) = nH
    rw [hρ', Matrix.mul_assoc, ← hNdef, hNP, ← Matrix.mul_assoc, hPinv1, Matrix.one_mul]
  have hσc := pin σ hσg hσh (hρ'e _)
  have hSY : σ.range ≤ ρ'.range := by
    rintro _ ⟨g, rfl⟩
    exact ⟨f' g, rfl⟩
  have hY : ρ'.range ≤ stab7 := by
    rintro _ ⟨g, rfl⟩
    exact hρ'e g
  have hover := overgroup hσg hσh hσc hSY hY
  have hker' : ∀ g : ↥C, ρ' g = 1 ↔ (g : X) ∈ T := by
    intro g
    rw [← hker g, hρ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hb3 : (f (zH 1)) ^ 3 = 1 := by rw [← map_pow, zH_pow_three, map_one]
  have hT3 : ¬ 3 ∣ Nat.card T := by rw [hT.2]; decide
  have hcount := card_inf_cen_eq hTC hTn ρ' hker' (hfC (zH 1)) hb3 hT3
  have hbb : ρ' ⟨f (zH 1), hfC (zH 1)⟩ = σ (wordH wZ1) := by
    rw [← zH_one_eq]
    rfl
  rw [hbb] at hcount
  obtain ⟨xc, hxc, hcx⟩ : ∃ xc, (xc = xSc ∨ xc = xIc) ∧ ((σ cH : GL7) : M7) = decN 7 xc := by
    rcases hσc with h | h
    exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
  have hcT : Nat.card ↥(T ⊓ Cen (f (zH 1))) = 32 := by
    rw [card_T_inf_cen hTn κ (hfC (zH 1))]
    have e1 : ((ρ ⟨f (zH 1), hfC (zH 1)⟩ : GL7) : M7) =
        P * ((ρ' ⟨f (zH 1), hfC (zH 1)⟩ : GL7) : M7) * ((Pu⁻¹ : GL7) : M7) := by
      rw [hρ', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPinv2, Matrix.one_mul, Matrix.mul_assoc,
        hPinv2, Matrix.mul_one]
    have hxv := validN_of_case hxc
    rw [e1, card_fix_conj _ P _ hPinv2 hPinv1, hbb,
      coe_wordH σ validN_nGc.1 validN_nHc.1 hxv.1 hσg hσh hcx,
      card_fix_decN (validN_evalW _ (fun g hg => ?_) _)]
    · exact (case_parts hxc).2.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exacts [validN_nGc, validN_nHc, hxv]
  rcases hover with hYS | h32
  ·
    ext g
    simp only [setMul, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨t, ht, l, hl, rfl⟩
      exact C.mul_mem (hTC ht) (hLC hl)
    · intro hg
      have hmem : ρ' ⟨g, hg⟩ ∈ σ.range := hYS ▸ ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨h, hh⟩ := hmem
      have h1 : ρ' ((f' h)⁻¹ * ⟨g, hg⟩) = 1 := by
        rw [map_mul, map_inv, ← hh]
        exact inv_mul_cancel _
      have ht : (f h)⁻¹ * g ∈ T := (hker' _).mp h1
      exact ⟨f h * ((f h)⁻¹ * g) * (f h)⁻¹, hTn _ (hfC h) _ ht, f h, hfL h, by group⟩
  · exfalso
    apply hβ'10
    rw [hcount, hcT]
    obtain ⟨k, hk⟩ := h32
    exact ⟨k, by rw [hk]; ring⟩

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
