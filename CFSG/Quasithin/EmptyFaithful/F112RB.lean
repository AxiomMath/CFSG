module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F112RR

theorem card_mul_card_le_card_mul_card_inf {G : Type*} [Group G] [Finite G] {T E A : Subgroup G}
    (hE : E ≤ T) (hA : A ≤ T) :
    Nat.card E * Nat.card A ≤ Nat.card T * Nat.card ↥(E ⊓ A) := by
  have hi : ((E.subgroupOf T) ⊓ (A.subgroupOf T)).index ≤
      (E.subgroupOf T).index * (A.subgroupOf T).index := Subgroup.index_inf_le
  have hinf : (E ⊓ A).subgroupOf T = E.subgroupOf T ⊓ A.subgroupOf T :=
    Subgroup.ext fun _ => Iff.rfl
  rw [← hinf] at hi
  have e1 : Nat.card (E.subgroupOf T) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have e2 : Nat.card (A.subgroupOf T) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have e3 : Nat.card ((E ⊓ A).subgroupOf T) = Nat.card ↥(E ⊓ A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hE)).toEquiv
  have h1 := Subgroup.card_mul_index (E.subgroupOf T)
  have h2 := Subgroup.card_mul_index (A.subgroupOf T)
  have h3 := Subgroup.card_mul_index ((E ⊓ A).subgroupOf T)
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  set ie := (E.subgroupOf T).index
  set ia := (A.subgroupOf T).index
  set ii := ((E ⊓ A).subgroupOf T).index
  have hie : 0 < ie := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hia : 0 < ia := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : Nat.card E * Nat.card A * (ie * ia) ≤ Nat.card T * Nat.card ↥(E ⊓ A) * (ie * ia) := by
    calc Nat.card E * Nat.card A * (ie * ia) = (Nat.card E * ie) * (Nat.card A * ia) := by ring
      _ = Nat.card T * Nat.card T := by rw [h1, h2]
      _ = Nat.card T * (Nat.card ↥(E ⊓ A) * ii) := by rw [h3]
      _ = Nat.card T * Nat.card ↥(E ⊓ A) * ii := by ring
      _ ≤ Nat.card T * Nat.card ↥(E ⊓ A) * (ie * ia) := Nat.mul_le_mul_left _ hi
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hie hia)

theorem q8_exists_noncomm : ∃ a b : QuaternionGroup 2, a * b ≠ b * a := by decide

theorem q8_sq_eq_one (x : QuaternionGroup 2) (h : x ^ 2 = 1) : x = 1 ∨ x = QuaternionGroup.a 2 := by
  revert x
  decide

theorem card_le_two_of_sq_eq_one_q8 (S : Subgroup (QuaternionGroup 2)) (h : ∀ x ∈ S, x ^ 2 = 1) :
    Nat.card S ≤ 2 := by
  classical
  have hsub : (S : Set (QuaternionGroup 2)) ⊆ {1, QuaternionGroup.a 2} := fun x hx => by
    rcases q8_sq_eq_one x (h x hx) with rfl | rfl <;> simp
  have h1 : Nat.card (S : Set (QuaternionGroup 2)) =
      (S : Set (QuaternionGroup 2)).ncard := Nat.card_coe_set_eq _
  have h2 : (S : Set (QuaternionGroup 2)).ncard ≤
      ({1, QuaternionGroup.a 2} : Set (QuaternionGroup 2)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, QuaternionGroup.a 2} : Set (QuaternionGroup 2)).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have h4 : Nat.card S = Nat.card (S : Set (QuaternionGroup 2)) := rfl
  omega

theorem card_perm_fin_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem card_z2_perm_fin_four :
    Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
  rw [Nat.card_prod, card_perm_fin_four]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [this]

theorem card_z4_sq : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
  rw [Nat.card_eq_fintype_card]; rfl

theorem card_dihedral_six : Nat.card (DihedralGroup 6) = 12 := by
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

theorem card_q8 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_elemAbelian_lt_sixtyFour {D : Type*} [Group D] [Finite D] {H₁ H₂ : Subgroup D}
    (hp : F6.IsGoldschmidtVPair H₁ H₂) (h : F6.IsGoldCaseVICat H₁ H₂) {E : Subgroup D}
    (hE : E ≤ H₁ ⊓ H₂) (hEab : IsElemAbelian 2 E) : Nat.card E < 64 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc₁ := hp.card_left
  have hc₂ := hp.card_right
  have hd₂ := F6.GoldPair.card_eq_six_mul_pCoreOf hp.quotient₂
  have hET : Nat.card E ≤ Nat.card ↥(H₁ ⊓ H₂) := Subgroup.card_le_of_le hE
  rcases h with h | h | h | h | h | h
  · obtain ⟨-, -, ⟨e⟩, -⟩ := h
    have h1 := hc₁
    rw [Nat.card_congr e.toEquiv, card_perm_fin_four] at h1
    omega
  · obtain ⟨-, -, ⟨e⟩, -⟩ := h
    have h1 := hc₁
    rw [Nat.card_congr e.toEquiv, card_z2_perm_fin_four] at h1
    omega
  · obtain ⟨-, -, -, -, hsp, hcard⟩ := h
    have hT64 : Nat.card ↥(H₁ ⊓ H₂) = 64 := by
      rw [hcard] at hd₂
      omega
    by_contra hge
    push Not at hge
    have hEeq : E = H₁ ⊓ H₂ := Subgroup.eq_of_le_of_card_ge hE (by omega)
    have hR₁ : pCoreOf 2 H₁ ≤ E := hEeq ▸ F7.isSylowTwoOf_pCoreOf_le hp.sylow₁
    have := hEab.1
    have hcomm : ∀ x y : ↥(pCoreOf 2 H₁), x * y = y * x := by
      intro x y
      have := mul_comm' (⟨x, hR₁ x.2⟩ : E) ⟨y, hR₁ y.2⟩
      exact Subtype.ext (congrArg (fun z : E => (z : D)) this)
    have hcenter : Subgroup.center ↥(pCoreOf 2 H₁) = ⊤ :=
      Subgroup.eq_top_iff' _ |>.mpr fun x => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    have h2 := hsp.2.1
    rw [hcenter, Subgroup.card_top, hsp.1] at h2
    omega
  · obtain ⟨-, -, -, -, -, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, card_z4_sq] at hd₂
    omega
  · obtain ⟨-, -, -, -, hcp, hcard⟩ := h
    have hT64 : Nat.card ↥(H₁ ⊓ H₂) = 64 := by
      rw [hcard] at hd₂
      omega
    by_contra hge
    push Not at hge
    have hEeq : E = H₁ ⊓ H₂ := Subgroup.eq_of_le_of_card_ge hE (by omega)
    have hR₁ : pCoreOf 2 H₁ ≤ E := hEeq ▸ F7.isSylowTwoOf_pCoreOf_le hp.sylow₁
    have := hEab.1
    have hcomm : ∀ x y : ↥(pCoreOf 2 H₁), x * y = y * x := by
      intro x y
      have := mul_comm' (⟨x, hR₁ x.2⟩ : E) ⟨y, hR₁ y.2⟩
      exact Subtype.ext (congrArg (fun z : E => (z : D)) this)
    obtain ⟨A', B', -, -, -, ⟨eB⟩, -⟩ := hcp
    obtain ⟨a, b, hab⟩ := q8_exists_noncomm
    apply hab
    have hxy := hcomm (eB.symm a : ↥(pCoreOf 2 H₁)) (eB.symm b : ↥(pCoreOf 2 H₁))
    have hxy' : eB.symm a * eB.symm b = eB.symm b * eB.symm a := Subtype.ext hxy
    have := congrArg eB hxy'
    simpa using this
  · obtain ⟨-, -, -, -, hext, -, -, hc2⟩ := h
    obtain ⟨φ, hφ, A', B', -, -, ⟨eA⟩, -, -⟩ := hext
    have hT128 : Nat.card ↥(H₁ ⊓ H₂) = 128 := by
      rw [hc2] at hd₂
      omega
    by_contra hge
    push Not at hge
    have hker : Nat.card ↥φ.ker = 32 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        card_dihedral_six] at h1
      omega
    have hKp : φ.ker ≤ CFSG.Open.pCore 2 ↥H₁ :=
      le_pCore 2 (MonoidHom.normal_ker φ) (IsPGroup.of_card (n := 5) (by rw [hker]; norm_num))
    set ι : ↥φ.ker →* D := H₁.subtype.comp φ.ker.subtype with hι
    have hιinj : Function.Injective ι := H₁.subtype_injective.comp φ.ker.subtype_injective
    set A₂ : Subgroup D := A'.map ι with hA₂
    have hA₂R : A₂ ≤ pCoreOf 2 H₁ := by
      rintro _ ⟨a, -, rfl⟩
      exact ⟨(a : ↥φ.ker), hKp a.2, rfl⟩
    have hA₂T : A₂ ≤ H₁ ⊓ H₂ := hA₂R.trans (F7.isSylowTwoOf_pCoreOf_le hp.sylow₁)
    let e₂ : ↥A₂ ≃* QuaternionGroup 2 := (A'.equivMapOfInjective ι hιinj).symm.trans eA
    have hA₂card : Nat.card A₂ = 8 := by rw [Nat.card_congr e₂.toEquiv, card_q8]
    have hprod := card_mul_card_le_card_mul_card_inf hE hA₂T
    have h4 : 4 ≤ Nat.card ↥(E ⊓ A₂) := by
      rw [hA₂card, hT128] at hprod
      omega
    have hS : Nat.card ↥(((E ⊓ A₂).subgroupOf A₂).map e₂.toMonoidHom) ≤ 2 := by
      refine card_le_two_of_sq_eq_one_q8 _ ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxE : (x : D) ∈ E := (Subgroup.mem_inf.mp hx).1
      have hsq : (x : D) ^ 2 = 1 := hEab.2 _ hxE
      have : x ^ 2 = 1 := Subtype.ext hsq
      show e₂ x ^ 2 = 1
      rw [← map_pow, this, map_one]
    have hS2 : Nat.card ↥(((E ⊓ A₂).subgroupOf A₂).map e₂.toMonoidHom) =
        Nat.card ↥((E ⊓ A₂).subgroupOf A₂) :=
      Nat.card_congr ((Subgroup.equivMapOfInjective _ e₂.toMonoidHom e₂.injective).symm.toEquiv)
    have hS3 : Nat.card ↥((E ⊓ A₂).subgroupOf A₂) = Nat.card ↥(E ⊓ A₂) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    omega

end F112RR

end CFSG.Quasithin
