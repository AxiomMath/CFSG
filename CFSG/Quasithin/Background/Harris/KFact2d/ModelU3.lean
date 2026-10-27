module

public import CFSG.Quasithin.Background.Harris.KFact2d.Transport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Cen

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups Matrix

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]


variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

@[expose] noncomputable def scF (F : Type) [Field F] : Fˣ →* GL (Fin 2) F :=
  Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom

theorem coe_scF (a : Fˣ) :
    ((scF F a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a : F) := rfl

theorem scF_comm (a : Fˣ) (B : GL (Fin 2) F) : scF F a * B = B * scF F a := by
  apply Units.ext
  simp only [Units.val_mul, coe_scF]
  exact (Matrix.scalar_commute (n := Fin 2) (a : F) (fun _ => Commute.all _ _) _)

theorem scF_mem_gu2 (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) : scF F a ∈ GU2Stated (p ^ 1) F := by
  apply Subgroup.subset_closure
  show (((scF F a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map (· ^ (p ^ 1)))ᵀ *
    ((scF F a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
  rw [coe_scF]
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : j = i
  · subst h
    simp [Matrix.one_apply, ← pow_succ, ha]
  · have h' : ¬ i = j := fun e => h e.symm
    simp [Matrix.one_apply, h, h', zero_pow (Fact.out : p.Prime).ne_zero]


theorem isSylowTwoOf_map_top' {X : Type} [Group X] {K S : Subgroup X} {L' : Type} [Group L']
    (e : ↥K ≃* L') (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf ((S.subgroupOf K).map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, (A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1).map _, ?_⟩
  have h1 : (((S.subgroupOf K).map e.toMonoidHom).subgroupOf ⊤).index =
      ((S.subgroupOf K).map e.toMonoidHom).index := Subgroup.relIndex_top_right _
  rw [h1]
  have h2 := Subgroup.index_map_equiv (S.subgroupOf K) e
  exact fun hd => hS.2.2 (h2 ▸ hd)

@[expose] def SpecialSylowU (hF : Nat.card F = p ^ 2) [Finite F] (U : Subgroup (PSU3F p F)) : Prop :=
  IsSylowTwoOf U ⊤ ∧ U ≤ leviCU hF ∧ ∃ c d : ↥(StatedSU 2 (p ^ 1) F), QuatPair c d ∧
    piU p F (ofSU2 hF c) ∈ U ∧ piU p F (ofSU2 hF d) ∈ U

theorem exists_equiv_special_u {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp2 : p ≠ 2)
    (hK : IsPSU 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : Nat.card F = p ^ 2) (e : ↥K ≃* PSU3F p F)
      (U₀ : Subgroup (PSU3F p F)), SpecialSylowU hF U₀ ∧
        (S.subgroupOf K).map e.toMonoidHom = U₀ := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := exists_equiv_psu3 hK
  have hU := isSylowTwoOf_map_top' e₀ hS
  obtain ⟨U₀, c, d, hU₀, hU₀B, hQ, hc, hd⟩ := exists_special_sylow_u hp2 hF
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hU₀ hU
  refine ⟨F, inferInstance, inferInstance, hF, e₀.trans (MulAut.conj g⁻¹), U₀,
    ⟨hU₀, hU₀B, c, d, hQ, hc, hd⟩, ?_⟩
  ext x
  have h1 : x ∈ (S.subgroupOf K).map (e₀.trans (MulAut.conj g⁻¹)).toMonoidHom ↔
      (MulAut.conj g) x ∈ (S.subgroupOf K).map e₀.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp [MulEquiv.symm_trans_apply]
  rw [h1, hg, B6.mem_conjSub]
  simp [MulAut.conj_apply]
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]


@[expose] noncomputable def scU (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) : ↥(GU2Stated (p ^ 1) F) :=
  ⟨scF F a, scF_mem_gu2 a ha⟩

@[expose] noncomputable def rhoU (hF : Nat.card F = p ^ 2) (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) :
    PSU3F p F :=
  piU p F (Lemma41aU3.blkU (uniData hF) (scU a ha))

theorem scU_comm (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) (B : ↥(GU2Stated (p ^ 1) F)) :
    scU a ha * B = B * scU a ha :=
  Subtype.ext (scF_comm a B.1)

theorem rhoU_comm (hF : Nat.card F = p ^ 2) (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1)
    (B : ↥(GU2Stated (p ^ 1) F)) :
    rhoU hF a ha * piU p F (Lemma41aU3.blkU (uniData hF) B) =
      piU p F (Lemma41aU3.blkU (uniData hF) B) * rhoU hF a ha := by
  unfold rhoU
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, scU_comm]

theorem rhoU_ne_one [Finite F] (hF : Nat.card F = p ^ 2) {a : Fˣ} (ha : (a : F) ^ (p + 1) = 1)
    (ha3 : a ^ 3 ≠ 1) : rhoU hF a ha ≠ 1 := by
  intro h
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr h)
  have h00 := congrFun (congrFun hr 0) 0
  have h22 := congrFun (congrFun hr 2) 2
  rw [matU_blkU hF] at h00 h22
  simp [Lemma41aL3.blkMat, scU, coe_scF, Matrix.scalar_apply] at h00 h22
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  rw [← h00] at h22
  field_simp at h22
  apply ha3
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  linear_combination -h22


theorem pow_prop {a : Fˣ} (ha : (a : F) ^ (p + 1) = 1) (n : ℕ) : ((a ^ n : Fˣ) : F) ^ (p + 1) = 1 := by
  rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ha, one_pow]

theorem rhoU_of_eq_one (hF : Nat.card F = p ^ 2) (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1)
    (h : a = 1) : rhoU hF a ha = 1 := by
  have h1 : scU a ha = 1 := Subtype.ext (by subst h; simp [scU])
  unfold rhoU
  rw [h1, map_one, map_one]

theorem scU_pow (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) (n : ℕ) :
    scU a ha ^ n = scU (a ^ n) (pow_prop ha n) :=
  Subtype.ext (by simp [scU, map_pow])

theorem rhoU_pow (hF : Nat.card F = p ^ 2) (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) (n : ℕ) :
    rhoU hF a ha ^ n = rhoU hF (a ^ n) (pow_prop ha n) := by
  unfold rhoU
  rw [← map_pow, ← map_pow, scU_pow]

theorem exists_unit_odd_u [Finite F] (hF : Nat.card F = p ^ 2) (hp4 : p % 4 = 1) (hp11 : 11 ≤ p) :
    ∃ a : Fˣ, (a : F) ^ (p + 1) = 1 ∧ a ^ 3 ≠ 1 ∧ Odd (orderOf a) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = p ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  rw [hcard] at hg
  have hpp : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have : 1 ≤ p := by omega
    zify [this, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hdvd : 2 * (p - 1) ∣ p ^ 2 - 1 := by
    rw [hpp]
    obtain ⟨k, hk⟩ : 2 ∣ p + 1 := ⟨(p + 1) / 2, by omega⟩
    exact ⟨k, by rw [hk]; ring⟩
  set a := g ^ (2 * (p - 1)) with ha
  have hord : orderOf a = (p + 1) / 2 := by
    rw [ha, orderOf_pow_of_dvd (by omega) (by rwa [hg]), hg, hpp]
    have : (p - 1) * (p + 1) = (2 * (p - 1)) * ((p + 1) / 2) := by
      have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
      calc (p - 1) * (p + 1) = (p - 1) * (2 * ((p + 1) / 2)) := by rw [h2]
        _ = _ := by ring
    rw [this, Nat.mul_div_cancel_left _ (by omega)]
  refine ⟨a, ?_, ?_, ?_⟩
  · have h1 : a ^ ((p + 1) / 2 * 2) = 1 := by
      rw [pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have h2 : (p + 1) / 2 * 2 = p + 1 := by omega
    rw [h2] at h1
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Fˣ => (u : F)) h1
  · intro h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · rw [hord]
    exact Nat.odd_iff.2 (by omega)


theorem f2At_special_u [Finite F] (hF : Nat.card F = p ^ 2) (hp4 : p % 4 = 1) (hp11 : 11 ≤ p)
    {U : Subgroup (PSU3F p F)} (hU : SpecialSylowU hF U) : F2At (PSU3F p F) U := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨a, ha, ha3, hao⟩ := exists_unit_odd_u hF hp4 hp11
  have hC : Subgroup.centralizer (E2P.zOf U : Set (PSU3F p F)) = leviCU hF :=
    centralizer_zOf_eq_leviCU hp2 hF hU.1 hU.2.1
  refine ⟨rhoU hF a ha, ⟨?_, ?_⟩, rhoU_ne_one hF ha ha3, ?_⟩
  · rw [hC]; exact ⟨_, ⟨scU a ha, rfl⟩, rfl⟩
  · rw [hC]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hy
    exact (rhoU_comm hF a ha B).symm
  · have hx : rhoU hF a ha ^ orderOf a = 1 := by
      rw [rhoU_pow]
      exact rhoU_of_eq_one hF _ _ (pow_orderOf_eq_one a)
    exact hao.of_dvd_nat (orderOf_dvd_of_pow_eq_one hx)


theorem f2_psu {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp4 : p % 4 = 1)
    (hp11 : 11 ≤ p) (hK : IsPSU 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∃ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), b ≠ 1 ∧ Odd (orderOf b) := by
  obtain ⟨F, _, _, hF, e, U₀, hU₀, hmap⟩ := exists_equiv_special_u (p := p) (by omega) hK hS
  have h := f2At_special_u hF hp4 hp11 hU₀
  rw [← hmap] at h
  exact f2_of_model hS.1 (F2At.of_map e _ h)

end CFSG.Quasithin.Background.Harris.KFact2d
