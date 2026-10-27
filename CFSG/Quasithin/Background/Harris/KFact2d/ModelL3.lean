module

public import CFSG.Quasithin.Background.Harris.KFact2d.Transport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3
open scoped MatrixGroups


theorem isSylowTwoOf_map_top {X : Type} [Group X] {K S : Subgroup X} {L' : Type} [Group L']
    (e : ↥K ≃* L') (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf ((S.subgroupOf K).map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, (A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1).map _, ?_⟩
  have h1 : (((S.subgroupOf K).map e.toMonoidHom).subgroupOf ⊤).index =
      ((S.subgroupOf K).map e.toMonoidHom).index := Subgroup.relIndex_top_right _
  rw [h1]
  have h2 := Subgroup.index_map_equiv (S.subgroupOf K) e
  exact fun hd => hS.2.2 (h2 ▸ hd)

variable {p : ℕ} [Fact p.Prime]

@[expose] def SpecialSylowL (p : ℕ) [Fact p.Prime] (U : Subgroup (PSL3 p)) : Prop :=
  IsSylowTwoOf U ⊤ ∧ U ≤ leviC p ∧ ∃ c d : SL(2, ZMod p), QuatPair c d ∧ ofSL2 p c ∈ U ∧ ofSL2 p d ∈ U

theorem exists_equiv_special {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp2 : p ≠ 2)
    (hK : IsPSL 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∃ (e : ↥K ≃* PSL3 p) (U₀ : Subgroup (PSL3 p)), SpecialSylowL p U₀ ∧
      (S.subgroupOf K).map e.toMonoidHom = U₀ := by
  obtain ⟨e₀⟩ := exists_equiv_psl3 hK
  have hU := isSylowTwoOf_map_top e₀ hS
  obtain ⟨U₀, c, d, hU₀, hU₀B, hQ, hc, hd⟩ := exists_special_sylow hp2
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hU₀ hU
  refine ⟨e₀.trans (MulAut.conj g⁻¹), U₀, ⟨hU₀, hU₀B, c, d, hQ, hc, hd⟩, ?_⟩
  ext x
  have h1 : x ∈ (S.subgroupOf K).map (e₀.trans (MulAut.conj g⁻¹)).toMonoidHom ↔
      (MulAut.conj g) x ∈ (S.subgroupOf K).map e₀.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp [MulEquiv.symm_trans_apply]
  rw [h1, hg, B6.mem_conjSub]
  simp [MulAut.conj_apply]
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]




@[expose] noncomputable def rhoL (p : ℕ) [Fact p.Prime] : GL (Fin 2) (ZMod p) →* PSL3 p :=
  (piL p).comp (leviHom p)

@[expose] noncomputable def scL (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* GL (Fin 2) (ZMod p) :=
  Units.map (Matrix.scalar (Fin 2) : ZMod p →+* Matrix (Fin 2) (Fin 2) (ZMod p)).toMonoidHom

theorem coe_scL (a : (ZMod p)ˣ) :
    ((scL p a : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      Matrix.scalar (Fin 2) (a : ZMod p) := rfl

theorem scL_comm (a : (ZMod p)ˣ) (B : GL (Fin 2) (ZMod p)) : scL p a * B = B * scL p a := by
  apply Units.ext
  simp only [Units.val_mul, coe_scL]
  exact (Matrix.scalar_commute (n := Fin 2) (a : ZMod p) (fun _ => Commute.all _ _) _)

theorem rhoL_scL_comm (a : (ZMod p)ˣ) (B : GL (Fin 2) (ZMod p)) :
    rhoL p (scL p a) * rhoL p B = rhoL p B * rhoL p (scL p a) := by
  rw [← map_mul, ← map_mul, scL_comm]

theorem rhoL_scL_ne_one {a : (ZMod p)ˣ} (ha : a ^ 3 ≠ 1) : rhoL p (scL p a) ≠ 1 := by
  intro h
  have hk : leviHom p (scL p a) ∈ (piL p).ker := h
  rw [ker_piL] at hk
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have h00 := congrFun (congrFun hr 0) 0
  have h22 := congrFun (congrFun hr 2) 2
  simp [coe_leviHom, coe_scL, Matrix.scalar_apply] at h00 h22
  have ha0 : (a : ZMod p) ≠ 0 := a.ne_zero
  rw [h00] at h22
  field_simp at h22
  apply ha
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  linear_combination h22

theorem rhoL_scL_pow (a : (ZMod p)ˣ) (n : ℕ) : rhoL p (scL p a) ^ n = rhoL p (scL p (a ^ n)) := by
  simp [map_pow]

theorem exists_unit_odd (hp4 : p % 4 = 3) (hp11 : 11 ≤ p) :
    ∃ a : (ZMod p)ˣ, a ^ 3 ≠ 1 ∧ Odd (orderOf a) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out] at hg
  have h2 : 2 ∣ p - 1 := by omega
  have hord : orderOf (g ^ 2) = (p - 1) / 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rwa [hg]), hg]
  refine ⟨g ^ 2, ?_, ?_⟩
  · intro h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · rw [hord]
    exact Nat.odd_iff.2 (by omega)


theorem f2At_special (hp4 : p % 4 = 3) (hp11 : 11 ≤ p) {U : Subgroup (PSL3 p)}
    (hU : SpecialSylowL p U) : F2At (PSL3 p) U := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨a, ha3, hao⟩ := exists_unit_odd (p := p) hp4 hp11
  have hC : Subgroup.centralizer (E2P.zOf U : Set (PSL3 p)) = leviC p :=
    centralizer_zOf_eq_leviC hp2 hU.1 hU.2.1
  have hmem : ∀ B : GL (Fin 2) (ZMod p), rhoL p B ∈ leviC p := fun B =>
    ⟨leviHom p B, ⟨B, rfl⟩, rfl⟩
  refine ⟨rhoL p (scL p a), ⟨?_, ?_⟩, rhoL_scL_ne_one ha3, ?_⟩
  · rw [hC]; exact hmem _
  · rw [hC]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hy
    exact (rhoL_scL_comm a B).symm
  · have hd : orderOf (rhoL p (scL p a)) ∣ orderOf a :=
      orderOf_map_dvd ((rhoL p).comp (scL p)) a
    exact hao.of_dvd_nat hd

theorem f2_psl {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp4 : p % 4 = 3)
    (hp11 : 11 ≤ p) (hK : IsPSL 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∃ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), b ≠ 1 ∧ Odd (orderOf b) := by
  obtain ⟨e, U₀, hU₀, hmap⟩ := exists_equiv_special (p := p) (by omega) hK hS
  have h := f2At_special hp4 hp11 hU₀
  rw [← hmap] at h
  exact f2_of_model hS.1 (F2At.of_map e _ h)

end CFSG.Quasithin.Background.Harris.KFact2d
