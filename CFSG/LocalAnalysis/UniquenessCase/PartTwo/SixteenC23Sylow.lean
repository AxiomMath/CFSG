module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23_exists_noncyclic_le_of_not_dvd_relIndex {p : ℕ} (hp : p.Prime) {K H B : Subgroup G}
    (hBK : B ≤ K) (hindex : ¬ p ∣ H.relIndex K) (hB : IsPGroup p B) (hBc : ¬ IsCyclic ↥B) :
    ∃ B' : Subgroup G, B' ≤ H ∧ IsPGroup p B' ∧ ¬ IsCyclic ↥B' := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Hk : Subgroup ↥K := H.subgroupOf K
  have hBk : IsPGroup p (B.subgroupOf K) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBK).symm
  have hBkc : ¬ IsCyclic ↥(B.subgroupOf K) := by
    intro hc
    haveI := hc
    exact hBc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hBK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBK).surjective)
  have hindexK : ¬ p ∣ Nat.card (↥K ⧸ Hk) := by
    rw [← Subgroup.index_eq_card (H := Hk)]
    exact hindex
  obtain ⟨q, hq⟩ := hBk.nonempty_fixed_point_of_prime_not_dvd_card (↥K ⧸ Hk) hindexK
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ x : B.subgroupOf K, k⁻¹ * (x : ↥K) * k ∈ Hk := by
    intro x
    have hb : ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      have := (MulAction.mem_fixedPoints.mp hq) x⁻¹
      simpa only [Subgroup.smul_def] using this
    have hb' : (QuotientGroup.mk (((x⁻¹ : B.subgroupOf K) : ↥K) * k) : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      change ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k
      exact hb
    have h := QuotientGroup.eq.mp hb'
    have heq : ((((x⁻¹ : B.subgroupOf K) : ↥K)) * k)⁻¹ * k = k⁻¹ * (x : ↥K) * k := by
      rw [Subgroup.coe_inv (x := x)]
      group
    rwa [heq] at h
  let Bk' : Subgroup ↥K := (B.subgroupOf K).map (MulAut.conj (k⁻¹)).toMonoidHom
  have hBk'le : Bk' ≤ Hk := by
    rintro x ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hfix ⟨b, hb⟩
  have hBk'p : IsPGroup p Bk' :=
    hBk.of_surjective
      (MulEquiv.subgroupMap (MulAut.conj (k⁻¹)) (B.subgroupOf K)).toMonoidHom
      (MulEquiv.subgroupMap (MulAut.conj (k⁻¹)) (B.subgroupOf K)).surjective
  have hBk'c : ¬ IsCyclic ↥Bk' := by
    intro hc
    exact hBkc (isCyclic_of_surjective (hH := hc)
      (MulEquiv.subgroupMap (MulAut.conj (k⁻¹)) (B.subgroupOf K)).symm.toMonoidHom
      (MulEquiv.subgroupMap (MulAut.conj (k⁻¹)) (B.subgroupOf K)).symm.surjective)
  refine ⟨Bk'.map K.subtype, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hBk'le hy)
  · exact hBk'p.of_equiv (Subgroup.equivMapOfInjective Bk' K.subtype K.subtype_injective)
  · intro hc
    haveI := hc
    exact hBk'c (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Bk' K.subtype K.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective Bk' K.subtype K.subtype_injective).symm.surjective)

theorem c23_not_isCyclic_inf_centralizer {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) {S : Set G} (hS : S.ncard ≤ 3)
    {w : G} (hSw : ∀ e ∈ E, e * w * e⁻¹ ∈ S) :
    ¬ IsCyclic ↥(E ⊓ centralizer ({w} : Set G)) := by
  classical
  let C : Subgroup G := E ⊓ centralizer ({w} : Set G)
  change ¬ IsCyclic ↥C
  have hCE : C ≤ E := inf_le_left
  have hC : IsElemAbelian p C := IsElemAbelian.mono hE hCE
  have hcard : p ^ 2 ≤ Nat.card C := by
    have hrel : C.relIndex E * Nat.card C = p ^ 3 := by
      have h := Subgroup.relIndex_mul_card C E
      rw [inf_of_le_left hCE] at h
      rw [hEcard] at h
      exact h
    have hle3 : C.relIndex E ≤ 3 := by
      let φ : ↥E → S := fun e => ⟨(e : G) * w * (e : G)⁻¹, hSw e e.2⟩
      have hφ : ∀ a b : ↥E, QuotientGroup.leftRel (C.subgroupOf E) a b → φ a = φ b := by
        intro a b hab
        rw [QuotientGroup.leftRel_apply] at hab
        apply Subtype.ext
        have hmemC : ((a⁻¹ * b : ↥E) : G) ∈ C := Subgroup.mem_subgroupOf.mp hab
        have hmemC' : ((a⁻¹ * b : ↥E) : G) ∈ E ⊓ centralizer ({w} : Set G) := hmemC
        have hcw : ((a⁻¹ * b : ↥E) : G) * w = w * ((a⁻¹ * b : ↥E) : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hmemC'.2
        have hcast : ((a⁻¹ * b : ↥E) : G) = (a : G)⁻¹ * (b : G) := by simp
        rw [hcast] at hcw
        have hweq : w = (a : G)⁻¹ * (b : G) * w * ((a : G)⁻¹ * (b : G))⁻¹ := by
          rw [hcw]; group
        show (a : G) * w * (a : G)⁻¹ = (b : G) * w * (b : G)⁻¹
        calc (a : G) * w * (a : G)⁻¹
            = (a : G) * ((a : G)⁻¹ * (b : G) * w * ((a : G)⁻¹ * (b : G))⁻¹) *
                (a : G)⁻¹ := by
              conv_lhs => rw [hweq]
          _ = (b : G) * w * (b : G)⁻¹ := by group
      let f : (↥E ⧸ C.subgroupOf E) → S := fun q => Quotient.liftOn' q φ hφ
      have hf : Function.Injective f := by
        intro q₁ q₂ h
        revert h
        refine Quotient.inductionOn₂' q₁ q₂ (fun a b hab => ?_)
        have hab' : φ a = φ b := hab
        apply Quotient.sound
        change QuotientGroup.leftRel (C.subgroupOf E) a b
        rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
        change ((a⁻¹ * b : ↥E) : G) ∈ E ⊓ centralizer ({w} : Set G)
        refine ⟨(a⁻¹ * b : ↥E).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have habG : (a : G) * w * (a : G)⁻¹ = (b : G) * w * (b : G)⁻¹ :=
          Subtype.ext_iff.mp hab'
        have hcast : ((a⁻¹ * b : ↥E) : G) = (a : G)⁻¹ * (b : G) := by simp
        rw [hcast]
        calc (a : G)⁻¹ * (b : G) * w
            = (a : G)⁻¹ * ((b : G) * w * (b : G)⁻¹) * (b : G) := by group
          _ = (a : G)⁻¹ * ((a : G) * w * (a : G)⁻¹) * (b : G) := by rw [← habG]
          _ = w * ((a : G)⁻¹ * (b : G)) := by group
      calc C.relIndex E = (C.subgroupOf E).index := rfl
        _ = Nat.card (↥E ⧸ C.subgroupOf E) := Subgroup.index_eq_card _
        _ ≤ Nat.card S := Nat.card_le_card_of_injective f hf
        _ = S.ncard := Nat.card_coe_set_eq S
        _ ≤ 3 := hS
    have key : p * p ^ 2 ≤ p * Nat.card C := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ = C.relIndex E * Nat.card C := hrel.symm
        _ ≤ p * Nat.card C := Nat.mul_le_mul_right _ (le_trans hle3 hp3)
    exact Nat.le_of_mul_le_mul_left key hp.pos
  exact s16c7_not_isCyclic_of_elemAbelian hp hC hcard

theorem c23_exists_elemAbelian_card_pow {p : ℕ} (hp : p.Prime) {M : Subgroup G} {k : ℕ}
    (hk : k ≤ pRank p M) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbot : CFSG.IsElementaryAbelian p (⊥ : Subgroup ↥M) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  have hne : {r : ℕ | ∃ A : Subgroup ↥M, CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ r}.Nonempty :=
    ⟨0, ⊥, hbot, by rw [Subgroup.card_bot, pow_zero]⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup ↥M, CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ r} := by
    refine ⟨Nat.card ↥M, ?_⟩
    rintro r ⟨A, -, hAcard⟩
    have hlt : r < Nat.card ↥M := by
      calc r < p ^ r := Nat.lt_pow_self hp.one_lt
        _ = Nat.card A := hAcard.symm
        _ ≤ Nat.card ↥M := Subgroup.card_le_card_group A
    exact hlt.le
  obtain ⟨A₀, hA₀ea, hA₀card⟩ := Nat.sSup_mem hne hbdd
  haveI : CFSG.IsElementaryAbelian p ↥A₀ := hA₀ea
  have hle : p ^ k ≤ Nat.card A₀ := by
    have hk' : k ≤ sSup {r : ℕ | ∃ A : Subgroup ↥M, CFSG.IsElementaryAbelian p A ∧
        Nat.card A = p ^ r} := by
      unfold pRank at hk
      exact hk
    calc p ^ k ≤ p ^ sSup {r : ℕ | ∃ A : Subgroup ↥M, CFSG.IsElementaryAbelian p A ∧
            Nat.card A = p ^ r} := Nat.pow_le_pow_right hp.pos hk'
      _ = Nat.card A₀ := hA₀card.symm
  obtain ⟨F, -, hFcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n := k) hp
      (CFSG.IsElementaryAbelian.isPGroup p ↥A₀) (H := ⊤) (by
      rw [Subgroup.card_top]
      exact hle)
  have hA₀ea_open : IsElemAbelian p A₀ := by
    haveI := hA₀ea
    exact isElemAbelian_of_isElementaryAbelian
  refine ⟨(F.map A₀.subtype).map M.subtype, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le (F.map A₀.subtype)
  · exact IsElemAbelian.map (IsElemAbelian.mono hA₀ea_open (Subgroup.map_subtype_le F))
      M.subtype
  · rw [Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective A₀.subtype_injective, hFcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
