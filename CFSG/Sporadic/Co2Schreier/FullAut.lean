module

public import CFSG.Sporadic.Co2Schreier.Kernel
public import CFSG.Sporadic.Co2Schreier.QAut
public import CFSG.Sporadic.Co2Schreier.SylowNode

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert

@[expose] def restrictC (β : MulAut co2P)
    (h1 : ∀ x : locC, ((β ⟨x, locC_le_P x.2⟩ : co2P) : Equiv.Perm (Fin 2300)) ∈ locC)
    (h2 : ∀ x : locC, ((β.symm ⟨x, locC_le_P x.2⟩ : co2P) : Equiv.Perm (Fin 2300)) ∈ locC) :
    MulAut locC where
  toFun x := ⟨β ⟨x, locC_le_P x.2⟩, h1 x⟩
  invFun x := ⟨β.symm ⟨x, locC_le_P x.2⟩, h2 x⟩
  left_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (⟨(x : Equiv.Perm (Fin 2300)) * y, locC_le_P (x * y).2⟩ : co2P) =
      ⟨x, locC_le_P x.2⟩ * ⟨y, locC_le_P y.2⟩ from rfl, map_mul]
    rfl

theorem restrictC_apply (β : MulAut co2P) (h1 h2) (x : locC) :
    ((restrictC β h1 h2 x : locC) : Equiv.Perm (Fin 2300)) = β ⟨x, locC_le_P x.2⟩ := rfl

theorem mem_C_iff
    (x : co2P) : (x : Equiv.Perm (Fin 2300)) ∈ locC ↔ zP * x = x * zP := by
  rw [locC_eq_centralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h.symm
  · intro h
    exact ⟨x.2, (congrArg Subtype.val h).symm⟩

theorem comm_of_fix_C (β : MulAut co2P) {g x : co2P} (hg : β g = g) (hx : g * x = x * g) :
    g * β x = β x * g := by
  have h := congrArg β hx
  rwa [map_mul, map_mul, hg] at h

theorem factorization_card_co2P :
    (Nat.card co2P).factorization 2 = 18 := by
  rw [card_co2P, show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem co2_sylow_normalize
    (α : MulAut co2P) : ∃ g : co2P, ∀ y : co2P,
    (y : Equiv.Perm (Fin 2300)) ∈ locS ↔
      ∃ x : co2P, (x : Equiv.Perm (Fin 2300)) ∈ locS ∧ y = (MulAut.conj g * α) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥((locS.subgroupOf co2P).map α.toMonoidHom) =
      2 ^ (Nat.card co2P).factorization 2 := by
    rw [Subgroup.card_map_of_injective α.injective, card_locS_subgroupOf, factorization_card_co2P]
    norm_num
  let S₂ : Sylow 2 co2P := Sylow.ofCard _ hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq co2P S₂ locSylow
  refine ⟨g, fun y => ?_⟩
  have hy : y ∈ (locSylow : Subgroup co2P) ↔ y ∈ ((g • S₂ : Sylow 2 co2P) : Subgroup co2P) := by
    rw [hg]
  rw [coe_locSylow, Subgroup.mem_subgroupOf, Sylow.coe_subgroup_smul,
    Subgroup.mem_smul_pointwise_iff_exists] at hy
  rw [hy]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ (locS.subgroupOf co2P).map α.toMonoidHom := hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hs'
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨α x, (Subgroup.mem_map_of_mem α.toMonoidHom (Subgroup.mem_subgroupOf.mpr hx) : _), rfl⟩

theorem co2_fix_z
    (β : MulAut co2P) (hg : ∀ y : co2P, (y : Equiv.Perm (Fin 2300)) ∈ locS ↔
    ∃ x : co2P, (x : Equiv.Perm (Fin 2300)) ∈ locS ∧ y = β x) : β zP = zP := by
  have hzc : ∀ y ∈ locS, y * locZ = locZ * y :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ((mem_centerIn_S_iff locZ).2
      (Or.inr rfl))).2
  have h1 : ((β zP : co2P) : Equiv.Perm (Fin 2300)) ∈ locS := (hg _).2 ⟨zP, locZ_mem_S, rfl⟩
  have h2 : ∀ y ∈ locS,
      y * ((β zP : co2P) : Equiv.Perm (Fin 2300)) = (β zP : co2P) * y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hg ⟨y, locS_le_P hy⟩).1 hy
    have hzx : x * zP = zP * x := Subtype.ext (hzc x hx)
    have h3 := congrArg (fun w => ((β w : co2P) : Equiv.Perm (Fin 2300))) hzx
    simp only [map_mul, Subgroup.coe_mul] at h3
    have hy' : y = ((β x : co2P) : Equiv.Perm (Fin 2300)) := congrArg Subtype.val hxy
    rw [hy']
    exact h3
  have hmem : ((β zP : co2P) : Equiv.Perm (Fin 2300)) ∈ CFSG.centerIn locS :=
    Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_iff.2 h2⟩
  rcases (mem_centerIn_S_iff _).1 hmem with h | h
  · exfalso
    have h0 : β zP = 1 := Subtype.ext (by rw [h, Subgroup.coe_one])
    rw [MulEquiv.map_eq_one_iff] at h0
    exact locZ_ne_one (congrArg Subtype.val h0)
  · exact Subtype.ext h

theorem co2_inner_on_C
    (β : MulAut co2P) (hβz : β zP = zP) :
    ∃ m : co2P, ∀ x : co2P, (x : Equiv.Perm (Fin 2300)) ∈ locC →
      (MulAut.conj m⁻¹ * β) x = x := by
  have hβz' : β.symm zP = zP := by rw [MulEquiv.symm_apply_eq, hβz]
  have h1 : ∀ x : locC, ((β ⟨x, locC_le_P x.2⟩ : co2P) : Equiv.Perm (Fin 2300)) ∈ locC :=
    fun x => by
      rw [mem_C_iff]
      exact comm_of_fix_C β hβz ((mem_C_iff ⟨x, locC_le_P x.2⟩).1 x.2)
  have h2 : ∀ x : locC, ((β.symm ⟨x, locC_le_P x.2⟩ : co2P) : Equiv.Perm (Fin 2300)) ∈ locC :=
    fun x => by
      rw [mem_C_iff]
      exact comm_of_fix_C β.symm hβz' ((mem_C_iff ⟨x, locC_le_P x.2⟩).1 x.2)
  obtain ⟨m, hm⟩ := locC_perfect_and_inner.2 (restrictC β h1 h2)
  refine ⟨⟨m, locC_le_P m.2⟩, fun x hx => ?_⟩
  have h3 := congrArg (fun φ : MulAut locC => ((φ ⟨x, hx⟩ : locC) : Equiv.Perm (Fin 2300))) hm
  simp only [restrictC_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    Subtype.coe_eta] at h3
  apply Subtype.ext
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h3]
  group

theorem CTUC_Co2_full_automorphisms_inner :
    ∀ α : MulAut CFSG.Sporadic.Co2Cert.co2P, ∃ g : CFSG.Sporadic.Co2Cert.co2P,
      α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := co2_sylow_normalize α
  obtain ⟨m, hm⟩ := co2_inner_on_C (MulAut.conj g * α) (co2_fix_z _ hg)
  have hmem : MulAut.conj m⁻¹ * (MulAut.conj g * α) ∈
      {α : MulAut co2P | ∀ c : co2P, (c : Equiv.Perm (Fin 2300)) ∈ locC → α c = c} := hm
  rw [CTUC_Co2_pointwise_first_centralizer_kernel.1] at hmem
  have key : ∀ γ : MulAut co2P, MulAut.conj m⁻¹ * (MulAut.conj g * α) = γ →
      α = MulAut.conj (g⁻¹ * m) * γ := by
    intro γ h
    rw [← h, map_mul, map_inv, map_inv]
    group
  rcases hmem with h | h
  · exact ⟨g⁻¹ * m, by rw [key 1 h, mul_one]⟩
  · exact ⟨g⁻¹ * m * zP, by rw [key (MulAut.conj zP) h, ← map_mul]⟩

theorem range_conj_co2P :
    (MulAut.conj : co2P →* MulAut co2P).range = ⊤ :=
  eq_top_iff.2 fun α _ => by
    obtain ⟨g, hg⟩ := CTUC_Co2_full_automorphisms_inner α
    exact ⟨g, hg.symm⟩

theorem forall_inner_of_mulEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H)
    (h : ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g) :
    ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((e.symm.trans α).trans e)
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut H => β (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem CTUC_Co2_full_automorphisms_inner_model
    (K : Type*) [Group K]
    (e : K ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g :=
  forall_inner_of_mulEquiv (e.trans co2PermEquiv) CTUC_Co2_full_automorphisms_inner

end CFSG.Sporadic.Co2Schreier
