module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Open Equiv

section Index

variable {G : Type*} [Group G]

theorem relIndex_inf_eq_relIndex_sup {K Q : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) :
    (K ⊓ Q).relIndex K = Q.relIndex (K ⊔ Q) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hK
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
  rw [Subgroup.inf_relIndex_left]
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient K Q hK).toEquiv

end Index

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_cocycle_mul_inv_mem {X S A B : Subgroup G} (hSX : S ≤ X)
    (hodd : ¬ 2 ∣ (S.subgroupOf X).index) (hA : IsElemAbelian 2 A)
    (hAn : X ≤ Subgroup.normalizer (A : Set G)) (hBA : B ≤ A)
    (hBn : X ≤ Subgroup.normalizer (B : Set G)) (c : G → G) (hcA : ∀ g ∈ X, c g ∈ A)
    (hcoc : ∀ g ∈ X, ∀ h ∈ X, c (g * h) = g * c h * g⁻¹ * c g) (hcS : ∀ s ∈ S, c s ∈ B) :
    ∃ w ∈ A, ∀ h ∈ X, c h * (h * w * h⁻¹ * w⁻¹)⁻¹ ∈ B := by
  classical
  have hAc : IsMulCommutative ↥A := hA.1
  let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hA.1.is_comm.comm }
  set S' : Subgroup ↥X := S.subgroupOf X with hS'
  have : Fintype (↥X ⧸ S') := Fintype.ofFinite _
  set B' : Subgroup ↥A := B.subgroupOf A with hB'
  have : B'.Normal := Subgroup.normal_of_isMulCommutative B'
  let cX : ↥X → ↥A := fun g => ⟨c g, hcA g g.2⟩
  let w : ↥A := ∏ x : ↥X ⧸ S', cX x.out
  refine ⟨w, w.2, fun h hh => ?_⟩
  set h' : ↥X := ⟨h, hh⟩ with hh'
  let φ : ↥A →* ↥A :=
    { toFun := fun a => ⟨h * a * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hAn hh) a).mp a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hφ : ∀ a : ↥A, ((φ a : ↥A) : G) = h * a * h⁻¹ := fun _ => rfl
  let mk : ↥A →* ↥A ⧸ B' := QuotientGroup.mk' B'
  have hmk1 : ∀ b : ↥A, (b : G) ∈ B → mk b = 1 := fun b hb =>
    (QuotientGroup.eq_one_iff b).mpr (Subgroup.mem_subgroupOf.mpr hb)
  have key : ∀ x : ↥X ⧸ S', mk (φ (cX x.out)) * mk (cX h') = mk (cX (h' • x).out) := by
    intro x
    set r := x.out with hr
    set r' := (h' • x).out with hr'
    have hs : r'⁻¹ * (h' * r) ∈ S' := by
      rw [← QuotientGroup.eq, hr', QuotientGroup.out_eq', hr]
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    set s : G := ((r'⁻¹ * (h' * r) : ↥X) : G) with hsdef
    have hsS : s ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hsX : s ∈ X := hSX hsS
    have hrs : (h : G) * (r : G) = (r' : G) * s := by
      rw [hsdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hh']; group
    have e1 := hcoc h hh r r.2
    have e2 := hcoc r' r'.2 s hsX
    rw [hrs] at e1
    have hbB : (r' : G) * c s * (r' : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hBn r'.2) (c s)).mp (hcS s hsS)
    have hbA : (r' : G) * c s * (r' : G)⁻¹ ∈ A := hBA hbB
    have hE : φ (cX r) * cX h' = ⟨_, hbA⟩ * cX r' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hφ]
      show h * c r * h⁻¹ * c h = (r' : G) * c s * (r' : G)⁻¹ * c r'
      rw [← e1, e2]
    rw [← map_mul, hE, map_mul, hmk1 _ hbB, one_mul]
  have hprod : mk (φ w) * mk (cX h') ^ Fintype.card (↥X ⧸ S') = mk w := by
    have h1 : mk (φ w) = ∏ x : ↥X ⧸ S', mk (φ (cX x.out)) := by
      rw [map_prod, map_prod]
    have h2 : mk w = ∏ x : ↥X ⧸ S', mk (cX (h' • x).out) := by
      rw [map_prod]
      exact (Equiv.prod_comp (MulAction.toPerm h') (fun x : ↥X ⧸ S' => mk (cX x.out))).symm
    rw [h1, h2, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => key x
  have hsq : mk (cX h') ^ 2 = 1 := by
    rw [← map_pow]
    have : cX h' ^ 2 = 1 := Subtype.ext (by simpa using hA.2 (c h) (hcA h hh))
    rw [this, map_one]
  have hcard : Odd (Fintype.card (↥X ⧸ S')) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  obtain ⟨k, hk⟩ := hcard
  have hpow : mk (cX h') ^ Fintype.card (↥X ⧸ S') = mk (cX h') := by
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [hpow] at hprod
  have hmem : cX h' * (φ w * w⁻¹)⁻¹ ∈ B' := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have e : (QuotientGroup.mk (φ w) : ↥A ⧸ B') = mk (φ w) := rfl
    have e' : (QuotientGroup.mk w : ↥A ⧸ B') = mk w := rfl
    have e'' : (QuotientGroup.mk (cX h') : ↥A ⧸ B') = mk (cX h') := rfl
    rw [e, e', e'', ← hprod]
    rw [mul_inv_rev, inv_inv, mul_comm (mk (φ w)) (mk (cX h')), mul_assoc (mk (cX h')),
      mul_inv_cancel, mul_one, ← pow_two, hsq]
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa [hφ, cX] using this

end Transfer

section Odd

variable {G : Type*} [Group G]

theorem commute_of_odd_of_conj_mem {C : Subgroup G} (hC2 : ∀ c ∈ C, c ^ 2 = 1) {x y : G}
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) (hxC : ∀ c ∈ C, x * c = c * x)
    (hy : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ * y⁻¹ ∈ C) : x * y = y * x := by
  set f : ℕ → G := fun k => x ^ k * y * (x ^ k)⁻¹ * y⁻¹ with hfdef
  have hf : ∀ k, f k = f 1 ^ k := by
    intro k
    induction k with
    | zero => simp [f]
    | succ k ih =>
      have e : f (k + 1) = x * f k * x⁻¹ * f 1 := by
        simp only [f, pow_succ']
        group
      have hc : x * f k * x⁻¹ = f k := by rw [hxC _ (hy k), mul_inv_cancel_right]
      rw [e, hc, ih, pow_succ]
  have h1 : f 1 ^ m = 1 := by
    rw [← hf]
    simp only [f, hxm, one_mul, inv_one, mul_one, mul_inv_cancel]
  obtain ⟨j, rfl⟩ := hm
  have h2 : f 1 ^ 2 = 1 := hC2 _ (hy 1)
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h1
  simp only [f, pow_one] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end Odd

section Perm5

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm] at h
  have e : Nat.card (Fin 5) = 5 := by simp
  rw [e, show Nat.factorial 5 = 120 from rfl] at h
  omega

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, show Nat.card (Fin 5) = 5 by simp]
  rfl

theorem perm5_eq_top_of_normal_of_card_eight (K P : Subgroup (Perm (Fin 5))) [K.Normal]
    (hPK : P ≤ K) (hP : Nat.card P = 8) : K = ⊤ := by
  have hK : K ≠ ⊥ := by
    rintro rfl
    rw [le_bot_iff.mp hPK, Subgroup.card_bot] at hP
    omega
  have h60 : 60 ∣ Nat.card K := card_alternatingGroup_five ▸
    Subgroup.card_dvd_of_le (CFSG.Quasithin.F53.normal_ge_alt5 K hK)
  have h8 : 8 ∣ Nat.card K := hP ▸ Subgroup.card_dvd_of_le hPK
  have h120 : Nat.card K ∣ 120 := card_perm_five ▸ Subgroup.card_subgroup_dvd_card K
  have hc : Nat.card K = 120 := by
    obtain ⟨a, ha⟩ := h60
    obtain ⟨b, hb⟩ := h8
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) h120
    omega
  exact Subgroup.eq_top_of_card_eq _ (by rw [hc, card_perm_five])

theorem perm5_sq_eq_one_of_sign_of_pow_eight :
    ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ^ 8 = 1 → σ ^ 2 = 1 := by
  decide +kernel

variable {A : Type*} [Group A]

theorem normalClosure_map_eq_top_five (ψ : A →* Perm (Fin 5)) (hψ : Function.Surjective ψ)
    (B : Subgroup A) (hB : Nat.card (B.map ψ) = 8) :
    (Subgroup.normalClosure (B : Set A)).map ψ = ⊤ := by
  have : ((Subgroup.normalClosure (B : Set A)).map ψ).Normal :=
    Subgroup.Normal.map inferInstance ψ hψ
  exact perm5_eq_top_of_normal_of_card_eight _ _
    (Subgroup.map_mono Subgroup.le_normalClosure) hB

theorem not_two_dvd_index_normalClosure_five (ψ : A →* Perm (Fin 5))
    (hψ : Function.Surjective ψ) (B : Subgroup A) (hB : Nat.card (B.map ψ) = 8)
    (hle : Subgroup.normalClosure (B : Set A) ⊓ ψ.ker ≤ B) :
    ¬ 2 ∣ (B.subgroupOf (Subgroup.normalClosure (B : Set A))).index := by
  set L := Subgroup.normalClosure (B : Set A) with hL
  have htop := normalClosure_map_eq_top_five ψ hψ B hB
  let φ : ↥L →* Perm (Fin 5) := ψ.comp L.subtype
  have hφ : Function.Surjective φ := by
    intro σ
    have : σ ∈ L.map ψ := by rw [htop]; trivial
    obtain ⟨l, hl, rfl⟩ := this
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : φ.ker ≤ B.subgroupOf L := fun x hx => hle ⟨x.2, hx⟩
  have h1 := Subgroup.index_map_eq (B.subgroupOf L) hφ hker
  have hmap : (B.subgroupOf L).map φ = B.map ψ := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalClosure]
  have h2 := ((B.subgroupOf L).map φ).card_mul_index
  rw [hmap] at h1
  rw [hmap, hB, h1, card_perm_five] at h2
  omega

end Perm5

end CFSG.Quasithin.F53.Stellmacher
