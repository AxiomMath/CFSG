module

public import CFSG.Quasithin.Vol2.Ch10SecAFactsSzMat
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrthCoord
public import CFSG.Quasithin.Vol2.Ch10SecAFactsTorus

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.QuasithinUnique

theorem factSzTorus_holds : FactSzTorus := by
  intro V _ H f hSz P hP φ hφH hφN hφodd v hv hPv hφv
  obtain ⟨a, ha, rfl, K, _, _, hK, π, hR⟩ := hSz
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπinj := FFModel.RealizesVia.injective_of_faithful (FFModel.nat_faithful _) hR
  have hπs := hR.1
  let M : ↥(suzukiGroup a K) →* Matrix (Fin 4) (Fin 4) K :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (suzukiGroup a K).subtype
  have hMv : ∀ γ, M γ = ((γ : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) := fun γ => rfl
  obtain ⟨eρ, β, hβinj, hβeq⟩ : ∃ (eρ : ↥(suzukiGroup a K) ≃* ↥H)
      (β : V →* Multiplicative (Fin 4 → K)), Function.Injective β ∧
        ∀ γ w, Multiplicative.toAdd (β (((eρ γ : ↥H) : MulAut V) w)) =
          (M γ).mulVec (Multiplicative.toAdd (β w)) := by
    obtain ⟨β, h1, -, h2⟩ := exists_beta_of_realizesVia_bot rfl hR
    exact ⟨MulEquiv.ofBijective π ⟨hπinj, hπs⟩, β, h1,
      fun γ w => congrArg Multiplicative.toAdd (h2 γ w)⟩
  obtain ⟨P0, hP0, hNB, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.Suzuki_model_opposite_root_interface ha hK
  obtain ⟨P', hP'mem⟩ : ∃ P' : Subgroup ↥(suzukiGroup a K),
      ∀ y, y ∈ P' ↔ ((eρ y : ↥H) : MulAut V) ∈ P :=
    ⟨(P.subgroupOf H).comap eρ.toMonoidHom, fun y => Iff.rfl⟩
  have hP'eq : P' = (P.subgroupOf H).comap eρ.toMonoidHom := by
    ext y
    exact hP'mem y
  have hP'2 : IsPGroup 2 P' := by
    rw [hP'eq]
    exact (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hP'idx : ¬ 2 ∣ P'.index := by
    rw [hP'eq, Subgroup.index_comap_of_surjective (P.subgroupOf H) eρ.surjective]
    exact hP.2.2
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥(suzukiGroup a K) (hP'2.toSylow hP'idx) P0
  have hxU : ∀ s, s ∈ suzukiU a K ↔ x⁻¹ * s * x ∈ P' := by
    intro s
    have h1 : ((x • hP'2.toSylow hP'idx : Sylow 2 ↥(suzukiGroup a K)) :
        Subgroup ↥(suzukiGroup a K)) = suzukiU a K := by
      rw [hx, hP0]
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h2 := (IsPGroup.mem_toSylow hP'2 hP'idx).mp hp
      have e : x⁻¹ * (x * p * x⁻¹) * x = p := by group
      show x⁻¹ * (x * p * x⁻¹) * x ∈ P'
      rw [e]
      exact h2
    · intro h
      refine ⟨x⁻¹ * s * x, (IsPGroup.mem_toSylow hP'2 hP'idx).mpr h, ?_⟩
      show x * (x⁻¹ * s * x) * x⁻¹ = s
      group
  obtain ⟨γ, hγ⟩ : ∃ γ, eρ γ = ⟨φ, hφH⟩ := ⟨eρ.symm ⟨φ, hφH⟩, MulEquiv.apply_symm_apply _ _⟩
  have hγN : ∀ y, y ∈ P' ↔ γ * y * γ⁻¹ ∈ P' := by
    intro y
    rw [hP'mem, hP'mem, map_mul, map_mul, map_inv, hγ, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hφN _
  have hψN : x * γ * x⁻¹ ∈ Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hxU, hxU, show x⁻¹ * (x * γ * x⁻¹ * s * (x * γ * x⁻¹)⁻¹) * x =
      γ * (x⁻¹ * s * x) * γ⁻¹ by group, ← hγN]
  rw [hNB] at hψN
  obtain ⟨u, w, l, hψe⟩ := (mem_suzukiB_iff hK).mp hψN
  obtain ⟨X, hX⟩ : ∃ X, X = Multiplicative.toAdd (β v) := ⟨_, rfl⟩
  have hX0 : X ≠ 0 := by
    intro h0
    apply hv
    apply hβinj
    rw [map_one]
    exact toAdd_eq_zero.mp (hX ▸ h0)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (M x).mulVec X := ⟨_, rfl⟩
  have hYfix : ∀ u' w' : K, (suzukiS a u' w').mulVec Y = Y := by
    intro u' w'
    have hp : x⁻¹ * suzukiSElt a K u' w' * x ∈ P' :=
      (hxU _).mp (suzukiSElt_mem_suzukiU a K u' w')
    have h1 := hβeq (x⁻¹ * suzukiSElt a K u' w' * x) v
    rw [hPv _ ((hP'mem _).mp hp), ← hX] at h1
    have e : M (suzukiSElt a K u' w') * M x = M x * M (x⁻¹ * suzukiSElt a K u' w' * x) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have hs : suzukiS a u' w' = M (suzukiSElt a K u' w') := (coe_suzukiSElt a K u' w').symm
    rw [hs, hY, Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, ← h1]
  have hY0 : Y ≠ 0 := by
    intro h0
    apply hX0
    have h1 : (M x⁻¹).mulVec Y = X := by
      rw [hY, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  obtain ⟨hY0', hY1', hY2'⟩ := fixed_suzukiS hYfix
  have hYe : Y = ![0, 0, 0, Y 3] := by
    ext i
    fin_cases i <;> simp [hY0', hY1', hY2']
  have hY3 : Y 3 ≠ 0 := fun h => hY0 (by
    rw [hYe, h]
    ext i
    fin_cases i <;> rfl)
  have hψY : (M (x * γ * x⁻¹)).mulVec Y = Y := by
    have h1 := hβeq γ v
    rw [hγ, show ((⟨φ, hφH⟩ : ↥H) : MulAut V) v = v from hφv, ← hX] at h1
    rw [hY, Matrix.mulVec_mulVec, ← map_mul, show x * γ * x⁻¹ * x = x * γ by group, map_mul,
      ← Matrix.mulVec_mulVec, ← h1]
  rw [hψe, map_mul, show M (suzukiSElt a K u w) = suzukiS a u w from coe_suzukiSElt a K u w,
    show M (suzukiDElt a K l) = suzukiD a l from coe_suzukiDElt a K l, hYe,
    ← Matrix.mulVec_mulVec, suzukiD_mulVec_e4, suzukiS_mulVec_e4] at hψY
  have hd : ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1 := by
    have h1 := congrFun hψY 3
    simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at h1
    exact (mul_eq_right₀ hY3).mp h1
  have hl : l = 1 := eq_one_of_zpow_eq_one hK (Units.ext hd)
  rw [hl, suzukiDElt_one, mul_one] at hψe
  have hψU : x * γ * x⁻¹ ∈ suzukiU a K := hψe ▸ suzukiSElt_mem_suzukiU a K u w
  have hψodd : Odd (orderOf (x * γ * x⁻¹)) := by
    rw [show x * γ * x⁻¹ = (MulAut.conj x).toMonoidHom γ from rfl,
      orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,
      ← MulEquiv.orderOf_eq eρ, hγ, Subgroup.orderOf_mk]
    exact hφodd
  have hU2 : IsPGroup 2 ↥(suzukiU a K) := hP0 ▸ P0.isPGroup'
  obtain ⟨k, hk⟩ := hU2 ⟨x * γ * x⁻¹, hψU⟩
  have hk' : (x * γ * x⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hψ1 : x * γ * x⁻¹ = 1 := orderOf_eq_one_iff.mp
    (((Nat.coprime_two_right.mpr hψodd).pow_right k).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one hk'))
  rw [conj_eq_one_iff] at hψ1
  have h1 := congrArg (fun y => ((eρ y : ↥H) : MulAut V)) hψ1
  simp only [hγ, map_one, OneMemClass.coe_one] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch10.SecA
