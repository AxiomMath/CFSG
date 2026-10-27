module

public import CFSG.Quasithin.Vol2.Ch10SecEN3d

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] def adjV (m : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := if m 0 = 1 then eFourSum 0 else 0

@[expose] def adjW (m : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := if m 2 = 1 then eFourSum 2 else 0

theorem isEven_adjV : ∀ m : Fin 5 → ZMod 2, isEven (adjV m) := by decide +kernel

theorem isEven_adjW : ∀ m : Fin 5 → ZMod 2, isEven (adjW m) := by decide +kernel

theorem adjust_model : ∀ m : Fin 5 → ZMod 2, isEven m → pact sA m = m → pact sB m = m →
    m + pact sB (adjW m) + adjV m = pact sA (adjV m) + adjW m ∧ pact sA (adjW m) = adjW m ∧
      pact sB (adjV m) = adjV m := by
  decide +kernel

section Coord

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem exists_adjust_coord (hβ : A5Equivariant θ β) {φx φy : ↥K} (hx : θ φx = sA)
    (hy : θ φy = sB) (c : ↥(commV K)) (hcx : (φx : MulAut W) c = c)
    (hcy : (φy : MulAut W) c = c) :
    ∃ v w : ↥(commV K), (φx : MulAut W) w = w ∧ (φy : MulAut W) v = v ∧
      (c : W) * (φy : MulAut W) w * v = (φx : MulAut W) v * w := by
  set m := ((Multiplicative.toAdd (β c) : evenWeight 5) : Fin 5 → ZMod 2) with hm
  have hfix : ∀ φ : ↥K, (φ : MulAut W) c = c → pact (θ φ) m = m := by
    intro φ hφ
    have h1 := coord_apply θ β hβ φ c
    have e : (⟨(φ : MulAut W) c, commV_invariant K _ φ.2 _ c.2⟩ : ↥(commV K)) = c :=
      Subtype.ext hφ
    rw [e] at h1
    exact h1.symm
  have hmx := hfix φx hcx
  have hmy := hfix φy hcy
  rw [hx] at hmx
  rw [hy] at hmy
  obtain ⟨heq, hw, hv⟩ := adjust_model m (Multiplicative.toAdd (β c)).2 hmx hmy
  set v : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨adjV m, isEven_adjV m⟩) with hvdef
  set w : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨adjW m, isEven_adjW m⟩) with hwdef
  have hcv : ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) = adjV m := by
    simp [v]
  have hcw : ((Multiplicative.toAdd (β w) : evenWeight 5) : Fin 5 → ZMod 2) = adjW m := by
    simp [w]
  refine ⟨v, w, fix_of_coord hβ φx w (by rw [hx, hcw]; exact hw),
    fix_of_coord hβ φy v (by rw [hy, hcv]; exact hv), ?_⟩
  have e1 : β (c * ⟨(φy : MulAut W) w, commV_invariant K _ φy.2 _ w.2⟩ * v) =
      β (⟨(φx : MulAut W) v, commV_invariant K _ φx.2 _ v.2⟩ * w) := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [map_mul, toAdd_mul, AddSubgroup.coe_add]
    rw [coord_apply θ β hβ φy w, coord_apply θ β hβ φx v, hx, hy, hcw, hcv]
    exact heq
  exact congrArg Subtype.val (β.injective e1)

theorem mem_commV_of_fix {K' : Subgroup (MulAut W)} {θ' : ↥K' ≃* Perm (Fin 5)}
    {β' : ↥(commV K') ≃* Multiplicative (evenWeight 5)} (hβ' : A5Equivariant θ' β')
    (htop : commV K ⊔ commV K' = ⊤) (htriv : ∀ φ ∈ K', ∀ u ∈ commV K, φ u = u) {u : W}
    (hu : ∀ φ ∈ oTwoUpper K', φ u = u) : u ∈ commV K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (A := commV K) (B := commV K')
    (fun a _ b _ => mul_comm a b) (htop ▸ Subgroup.mem_top u)
  have hbfix : ∀ φ ∈ oTwoUpper K', φ b = b := by
    intro φ hφ
    have h1 := hu φ hφ
    rw [map_mul, htriv φ (oTwoUpper_le K' hφ) a ha] at h1
    exact mul_left_cancel h1
  have h3 : ∀ σ ∈ alternatingGroup (Fin 5),
      pact σ ((Multiplicative.toAdd (β' ⟨b, hb⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
        ((Multiplicative.toAdd (β' ⟨b, hb⟩) : evenWeight 5) : Fin 5 → ZMod 2) := by
    intro σ hσ
    have h4 := coord_apply θ' β' hβ' (θ'.symm σ) ⟨b, hb⟩
    rw [MulEquiv.apply_symm_apply] at h4
    have e : (⟨((θ'.symm σ : ↥K') : MulAut W) b, commV_invariant K' _ (θ'.symm σ).2 _ hb⟩ :
        ↥(commV K')) = ⟨b, hb⟩ := Subtype.ext (hbfix _ (symm_mem_oTwoUpper θ' hσ))
    rw [e] at h4
    exact h4.symm
  have h0 := eq_zero_of_fix_cThree _ (Multiplicative.toAdd (β' ⟨b, hb⟩)).2
    (h3 _ cThree_mem_alt) (h3 _ cThree'_mem_alt)
  have h5 : β' ⟨b, hb⟩ = 1 := Multiplicative.toAdd.injective (Subtype.ext h0)
  have h6 : (⟨b, hb⟩ : ↥(commV K')) = 1 := β'.injective (h5.trans (map_one _).symm)
  have hb1 : b = 1 := congrArg Subtype.val h6
  rw [hb1, mul_one]
  exact ha

end Coord

variable {G : Type} [Group G]

theorem commute_of_adjust {x y c v w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y * x * y = c) (hcond : c * (y * w * y) * v = (x * v * x) * w) :
    x * w * (y * v) = y * v * (x * w) := by
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y = y * x * c := by
    rw [← hc]
    calc x * y = y * y * x * y := by rw [hy, one_mul]
      _ = y * (x * x) * y * x * y := by rw [hx, mul_one]
      _ = y * x * (x * y * x * y) := by group
  calc x * w * (y * v) = x * y * (y⁻¹ * w * y) * v := by group
    _ = x * y * (y * w * y) * v := by rw [hy']
    _ = y * x * c * (y * w * y) * v := by rw [h1]
    _ = y * x * (c * (y * w * y) * v) := by group
    _ = y * x * ((x * v * x) * w) := by rw [hcond]
    _ = y * (x * x) * v * x * w := by group
    _ = y * v * (x * w) := by rw [hx, mul_one]; group

theorem mem_centralizer_sup_of {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.centralizer (A : Set G)) (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp hA a ha).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp hB b hb).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (key hh) x rfl).symm

end CFSG.Quasithin.Vol2.Ch10.SecE
