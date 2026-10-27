module

public import CFSG.Quasithin.Background.HMathieuCent
public import CFSG.Monster.B.TwoA.Base.M22
public import CFSG.Monster.CodeAut.Bridge
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2202
public import Certificates.Certificate2204
public import Certificates.Certificate2205
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3046
public import Certificates.Certificate3157
public import CFSG.Quasithin.Background.HMathieuNormInputs
public import Certificates.Certificate7065
public import Certificates.Certificate7060

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.Blueprint

theorem normalizer_map_eq {G : Type*} [Group G] [Finite G] {Γ' : Type*} [Group Γ'] [Finite Γ']
    (ψ : Γ' →* G) (hψ : Function.Injective ψ) (N : Subgroup Γ') [N.Normal]
    (hC : Subgroup.centralizer ((N.map ψ : Subgroup G) : Set G) = ⊥)
    (hcard : Nat.card (MulAut N) ≤ Nat.card Γ') :
    Subgroup.normalizer ((N.map ψ : Subgroup G) : Set G) = ψ.range := by
  refine normalizer_eq_of_card hC ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, Subgroup.Normal.conj_mem inferInstance y hy x, by
        rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨x⁻¹ * y * x, ?_, ?_⟩
      · have := Subgroup.Normal.conj_mem inferInstance y hy x⁻¹
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hxy]
        group
  · have e1 : MulAut ↥(N.map ψ) ≃ MulAut N :=
      (MulAut.congr (N.equivMapOfInjective ψ hψ).symm).toEquiv
    rw [Nat.card_congr e1, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
    exact hcard

theorem card_mulAut_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (MulAut A) = Nat.card (MulAut B) :=
  Nat.card_congr (MulAut.congr e).toEquiv

theorem mog22_eq_map_P0 : mog22 = CFSG.Monster.B.TwoA.P0.map AutPerm.subtype := by
  ext σ
  constructor
  · rintro ⟨⟨hσ, h0⟩, h1⟩
    exact ⟨⟨σ, hσ⟩, (CFSG.Monster.B.TwoA.mem_P0_iff _).2
      ⟨(mem_stab_iff 0 σ).1 h0, (mem_stab_iff 1 σ).1 h1⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h0, h1⟩ := (CFSG.Monster.B.TwoA.mem_P0_iff p).1 hp
    exact ⟨⟨p.2, (mem_stab_iff 0 _).2 h0⟩, (mem_stab_iff 1 _).2 h1⟩

theorem mog22plus_eq_map_Ppair : mog22plus = CFSG.Monster.B.TwoA.Ppair.map AutPerm.subtype := by
  ext σ
  constructor
  · rintro ⟨hσ, h⟩
    exact ⟨⟨σ, hσ⟩, (CFSG.Monster.B.TwoA.mem_Ppair_iff _).2 h, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, (CFSG.Monster.B.TwoA.mem_Ppair_iff p).1 hp⟩

@[expose] noncomputable def mog22EquivM22 :
    ↥mog22 ≃* NativeSporadic.M22 :=
  (MulEquiv.subgroupCongr mog22_eq_map_P0).trans
    ((CFSG.Monster.B.TwoA.P0.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans
      CFSG.Monster.B.TwoA.m22EquivP0.symm)

theorem card_mog22plus : Nat.card mog22plus = 887040 := by
  rw [mog22plus_eq_map_Ppair, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    CFSG.Monster.B.TwoA.natCard_Ppair]

theorem perm_apply_of_inv_eq {σ : Equiv.Perm (Fin 24)} {a b : Fin 24} (h : σ⁻¹ a = b) :
    σ b = a := by
  rw [← h]
  simp

theorem mog22_normal_in_plus {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus) (hτ : τ ∈ mog22) :
    σ * τ * σ⁻¹ ∈ mog22 := by
  obtain ⟨⟨hτA, h0⟩, h1⟩ := hτ
  have h0' := (mem_stab_iff 0 τ).1 h0
  have h1' := (mem_stab_iff 1 τ).1 h1
  have hσi : σ⁻¹ ∈ mog22plus := mog22plus.inv_mem hσ
  refine ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem hσ.1 hτA) hσi.1, (mem_stab_iff 0 _).2 ?_⟩,
    (mem_stab_iff 1 _).2 ?_⟩
  · rcases hσi.2 with ⟨e0, -⟩ | ⟨e0, -⟩
    · simp only [Equiv.Perm.mul_apply, e0, h0']
      exact perm_apply_of_inv_eq e0
    · simp only [Equiv.Perm.mul_apply, e0, h1']
      exact perm_apply_of_inv_eq e0
  · rcases hσi.2 with ⟨-, e1⟩ | ⟨-, e1⟩
    · simp only [Equiv.Perm.mul_apply, e1, h1']
      exact perm_apply_of_inv_eq e1
    · simp only [Equiv.Perm.mul_apply, e1, h0']
      exact perm_apply_of_inv_eq e1

instance mog22_subgroupOf_normal : (mog22.subgroupOf mog22plus).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using mog22_normal_in_plus g.2 hn

theorem range_rho10_mog22 : (rho10 mog22 mog22_le_mog22plus).range =
    (mog22.subgroupOf mog22plus).map (rho10 mog22plus le_rfl) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨σ, mog22_le_mog22plus σ.2⟩, by simp [Subgroup.mem_subgroupOf],
      MulEquiv.ext fun w => rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, (Subgroup.mem_subgroupOf).1 hσ⟩, MulEquiv.ext fun w => rfl⟩

theorem normalizer_rho10_mog22 :
    Subgroup.normalizer ((rho10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) =
      (rho10 mog22plus le_rfl).range := by
  have := finite_mulAut W10
  rw [range_rho10_mog22]
  refine normalizer_map_eq _ rho10_mog22plus_injective _ ?_ ?_
  · rw [← range_rho10_mog22]
    exact centralizer_rho10_mog22
  · rw [card_mulAut_congr ((Subgroup.subgroupOfEquivOfLe mog22_le_mog22plus).trans mog22EquivM22),
      card_mog22plus]
    have h := CFSG.Sporadic.Schreier.m22_mulAut_card
    rw [CFSG.Sporadic.Schreier.m22_card] at h
    exact h

@[expose] def j23 : Fin 23 → Fin 24 :=
  ![1, 2, 3, 4, 5, 8, 14, 22, 10, 18, 6, 12, 21, 9, 13, 17, 7, 20, 11, 15, 23, 19, 16]

@[expose] def j23Split : Fin 24 ≃ Option (Fin 23) where
  toFun := ![none, some 0, some 1, some 2, some 3, some 4, some 10, some 16, some 5, some 13,
    some 8, some 18, some 11, some 14, some 6, some 19, some 22, some 15, some 9, some 21,
    some 17, some 12, some 7, some 20]
  invFun o := o.elim 0 j23
  left_inv := by decide
  right_inv := by decide

@[expose] def psi23 : Equiv.Perm (Fin 23) →* Equiv.Perm (Fin 24) where
  toFun g := (j23Split.trans (Equiv.optionCongr g)).trans j23Split.symm
  map_one' := Equiv.ext fun x => by
    simp only [Equiv.trans_apply, Equiv.Perm.one_apply]
    rcases h : j23Split x with _ | i <;> simp [← h]
  map_mul' g h := Equiv.ext fun x => by
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    rcases j23Split x with _ | i <;> rfl

theorem psi23_injective : Function.Injective psi23 := by
  intro g h hgh
  refine Equiv.ext fun i => ?_
  have := congrArg (fun σ : Equiv.Perm (Fin 24) => j23Split (σ (j23Split.symm (some i)))) hgh
  simpa [psi23] using this

theorem psi23_zero (g : Equiv.Perm (Fin 23)) : psi23 g 0 = 0 := rfl

theorem psi23_a_arr : HasArr (psi23 (List.formPerm [0, 1] * List.formPerm [2, 3] *
    List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
    List.formPerm [18, 19] * List.formPerm [20, 21])) m23AArr := by
  intro i
  revert i
  decide

theorem psi23_b_arr : HasArr (psi23 (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
    List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
    List.formPerm [14, 16])) m23BArr := by
  intro i
  revert i
  decide

theorem m23_arrs_ok :
    inAutOK m23AArr = true ∧ inAutOK m23BArr = true :=
  Certificates.certificate7065

theorem eq_of_hasArr {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans (hτ i).symm)

theorem mem_autPerm_of_hasArr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (h : inAutOK a = true) : σ ∈ AutPerm := by
  obtain ⟨τ, hτ, hτa⟩ := exists_of_inAutOK h
  rw [eq_of_hasArr hσ hτa]
  exact hτ

theorem card_mog23 : Nat.card mog23 = 10200960 := by
  have htrans : MulAction.IsPretransitive ↥AutPerm (Fin 24) := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : Fin 24, ∃ p : ↥AutPerm, p • (0 : Fin 24) = z := by
      intro z
      by_cases hz : z = 0
      · exact ⟨1, by rw [hz, one_smul]⟩
      · obtain ⟨τ, hτ, h0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two z 0 hz
        exact ⟨⟨τ, hτ⟩, h0⟩
    obtain ⟨a, ha⟩ := key x
    obtain ⟨b, hb⟩ := key y
    exact ⟨b * a⁻¹, by rw [← ha, ← hb, mul_smul, inv_smul_smul]⟩
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥AutPerm (0 : Fin 24))
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin,
    card_AutPerm] at h1
  have h2 : mog23 = (MulAction.stabilizer ↥AutPerm (0 : Fin 24)).map AutPerm.subtype := by
    ext σ
    constructor
    · rintro ⟨hσ, h0⟩
      exact ⟨⟨σ, hσ⟩, (mem_stab_iff 0 σ).1 h0, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, (mem_stab_iff 0 _).2 hp⟩
  rw [h2, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  omega

theorem map_psi23_M23 :
    NativeSporadic.M23.map psi23 = mog23 := by
  have hle : NativeSporadic.M23.map psi23 ≤ mog23 := by
    rw [NativeSporadic.M23, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨mem_autPerm_of_hasArr psi23_a_arr m23_arrs_ok.1, (mem_stab_iff 0 _).2 rfl⟩
    · exact ⟨mem_autPerm_of_hasArr psi23_b_arr m23_arrs_ok.2, (mem_stab_iff 0 _).2 rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_mog23, Subgroup.card_map_of_injective psi23_injective,
    CFSG.Sporadic.Schreier.m23_card]

@[expose] noncomputable def mog23EquivM23 :
    ↥mog23 ≃* NativeSporadic.M23 :=
  (MulEquiv.subgroupCongr map_psi23_M23.symm).trans
    (NativeSporadic.M23.equivMapOfInjective _ psi23_injective).symm

theorem range_rho11_eq_map_top (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    (rho11 Γ hΓ).range = (⊤ : Subgroup ↥Γ).map (rho11 Γ hΓ) := by
  rw [MonoidHom.range_eq_map]

theorem normalizer_rho11_mog23 :
    Subgroup.normalizer ((rho11 mog23 inf_le_left).range : Set (MulAut W11)) =
      (rho11 mog23 inf_le_left).range := by
  have := finite_mulAut W11
  have hcard : Nat.card (MulAut ↥(⊤ : Subgroup ↥mog23)) ≤ Nat.card ↥mog23 := by
    rw [card_mulAut_congr (Subgroup.topEquiv.trans mog23EquivM23)]
    have h := CFSG.Sporadic.Schreier.m23_mulAut_card
    rw [CFSG.Sporadic.Schreier.m23_card] at h
    rw [card_mog23]
    exact h
  have h := normalizer_map_eq (rho11 mog23 inf_le_left) (rho11_injective _ _) ⊤
    (by rw [← range_rho11_eq_map_top]; exact centralizer_rho11_mog23) hcard
  rwa [← range_rho11_eq_map_top] at h

@[expose] noncomputable def autPermEquivM24' :
    ↥AutPerm ≃* NativeSporadic.M24 :=
  (MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)).trans
    (NativeSporadic.M24.equivMapOfInjective _ (MulAut.conj bridgeQ⁻¹).injective).symm

theorem normalizer_rho11_autPerm :
    Subgroup.normalizer ((rho11 AutPerm le_rfl).range : Set (MulAut W11)) =
      (rho11 AutPerm le_rfl).range := by
  have := finite_mulAut W11
  have hcard : Nat.card (MulAut ↥(⊤ : Subgroup ↥AutPerm)) ≤ Nat.card ↥AutPerm := by
    rw [card_mulAut_congr (Subgroup.topEquiv.trans autPermEquivM24')]
    have h := CFSG.Sporadic.Schreier.m24_mulAut_card
    rw [CFSG.Sporadic.Schreier.m24_card] at h
    rw [card_AutPerm]
    exact h
  have h := normalizer_map_eq (rho11 AutPerm le_rfl) (rho11_injective _ _) ⊤
    (by rw [← range_rho11_eq_map_top]; exact centralizer_rho11_autPerm) hcard
  rwa [← range_rho11_eq_map_top] at h

end CFSG.Quasithin.H.Mathieu
