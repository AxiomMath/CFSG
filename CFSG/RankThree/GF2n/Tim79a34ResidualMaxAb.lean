module

public import CFSG.RankThree.GF2n.Tim79a34QEOut
public import CFSG.RankThree.GF2n.Tim79a34QEOrder
public import CFSG.RankThree.GF2n.Tim79a34ResidualCfg

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 1}
  {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

theorem le_V_of_normalized (cfg : ResCfg M V Q P H Φ ψ a T) (hX : xOf V H ≤ pResidual 2 G)
    {A : Subgroup G} (hVA : V ≤ A) (hAP : A ≤ P)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAn : ∀ m ∈ M ⊓ pResidual 2 G, ∀ x ∈ A, m * x * m⁻¹ ∈ A) : A ≤ V := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hVn : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun m hm v hv => by
    have hmN : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hm
    exact (Subgroup.mem_normalizer_iff.mp hmN v).mp hv
  have hPn : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P := fun m hm p hp =>
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
  rcases classify_abelian cfg hX hVA hAP hAab hAn with hAV | hAF
  · exact hAV.le
  · have hMn : ∀ m ∈ M, ∀ x ∈ A, m * x * m⁻¹ ∈ A := by
      intro m hm x hx
      have hxc : m * x * m⁻¹ ∈ conjSubgroup m A :=
        mem_conjSubgroup.mpr (by rw [show m⁻¹ * (m * x * m⁻¹) * m = x by group]; exact hx)
      have hcl := classify_abelian cfg hX (A := conjSubgroup m A)
        (fun v hv => mem_conjSubgroup.mpr (by
          have h := hVA (hVn m⁻¹ (M.inv_mem hm) v hv)
          rwa [inv_inv] at h))
        (fun y hy => by
          have h := hAP (mem_conjSubgroup.mp hy)
          have h' := hPn m hm _ h
          rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h')
        (fun y hy z hz => by
          have h1 := mem_conjSubgroup.mp hy
          have h2 := mem_conjSubgroup.mp hz
          have h3 := hAab _ h1 _ h2
          have e1 : m⁻¹ * (y * z) * m = (m⁻¹ * y * m) * (m⁻¹ * z * m) := by group
          have e2 : m⁻¹ * (z * y) * m = (m⁻¹ * z * m) * (m⁻¹ * y * m) := by group
          have h4 : y * z = z * y := by
            have h5 : m⁻¹ * (y * z) * m = m⁻¹ * (z * y) * m := by rw [e1, e2, h3]
            simpa using h5
          exact h4)
        (fun m' hm' y hy => by
          have h1 := mem_conjSubgroup.mp hy
          have hm'' : m⁻¹ * m' * m ∈ M ⊓ pResidual 2 G := by
            refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · exact M.mul_mem (M.mul_mem (M.inv_mem hm) (Subgroup.mem_inf.mp hm').1) hm
            · have := (inferInstance : (pResidual 2 G).Normal).conj_mem m'
                (Subgroup.mem_inf.mp hm').2 m⁻¹
              simpa [mul_assoc] using this
          have h2 := hAn _ hm'' _ h1
          refine mem_conjSubgroup.mpr ?_
          have e : m⁻¹ * (m' * y * m'⁻¹) * m = (m⁻¹ * m' * m) * (m⁻¹ * y * m) * (m⁻¹ * m' * m)⁻¹ :=
            by group
          rw [e]
          exact h2)
      rcases hcl with h | h
      · rw [h] at hxc
        exact hVA hxc
      · rw [h, ← hAF] at hxc
        exact hxc
    have hAM : A ≤ M := hAP.trans (hc.P_le_Q.trans hQM)
    have hMA : M ≤ Subgroup.normalizer (A : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hMn m hm x
      · intro hx
        have h := hMn m⁻¹ (M.inv_mem hm) _ hx
        rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h
    have hAc : IsMulCommutative ↥A :=
      IsMulCommutative.of_comm fun x y => Subtype.ext (hAab _ x.2 _ y.2)
    exact hc.maxAb.le_of_ge ⟨hAM, hMA, hAc⟩ hVA

theorem le_V_of_abelian_normalized (cfg : ResCfg M V Q P H Φ ψ a T)
    (hX : xOf V H ≤ pResidual 2 G) (hQP : Q ⊓ pResidual 2 G = P) (hPG : P ≤ pResidual 2 G)
    {U : Subgroup G} (hUM : U ≤ M ⊓ pResidual 2 G) (hVU : V ≤ U)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hUn : ∀ m ∈ M ⊓ pResidual 2 G, ∀ x ∈ U, m * x * m⁻¹ ∈ U) : U ≤ V := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M ⊓ pResidual 2 G := le_inf (hc.P_le_Q.trans hQM) hPG
  have hPn : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P := fun m hm p hp =>
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
  have hUPV : U ⊓ P ≤ V := by
    refine le_V_of_normalized cfg hX (le_inf hVU hc.V_le_P) inf_le_right
      (fun x hx y hy => hUab x hx.1 y hy.1) (fun m hm x hx => ?_)
    exact ⟨hUn m hm x hx.1, hPn m (Subgroup.mem_inf.mp hm).1 x hx.2⟩
  have hcomm : ∀ u ∈ U, ∀ p ∈ P, u * p * u⁻¹ * p⁻¹ ∈ V := by
    intro u hu p hp
    refine hUPV ⟨?_, ?_⟩
    · have h1 := hUn p (hPM hp) u⁻¹ (U.inv_mem hu)
      have h2 := U.mul_mem hu h1
      have e : u * (p * u⁻¹ * p⁻¹) = u * p * u⁻¹ * p⁻¹ := by group
      rwa [e] at h2
    · exact P.mul_mem (hPn u (hUM hu).1 p hp) (P.inv_mem hp)
  have hsq : ∀ u ∈ U, u * u ∈ V := by
    intro u hu
    rw [← cfg.hPc]
    refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    have hc1 := hcomm u hu p hp
    have hcu : u * (u * p * u⁻¹ * p⁻¹) = (u * p * u⁻¹ * p⁻¹) * u := hUab _ hu _ (hVU hc1)
    have hcc : (u * p * u⁻¹ * p⁻¹) * (u * p * u⁻¹ * p⁻¹) = 1 := by
      have h := hc.elemAb.2 _ hc1
      rwa [sq] at h
    have key : (u * u) * p * (u * u)⁻¹ * p⁻¹ = 1 := by
      calc (u * u) * p * (u * u)⁻¹ * p⁻¹
          = (u * (u * p * u⁻¹ * p⁻¹) * u⁻¹) * (u * p * u⁻¹ * p⁻¹) := by group
        _ = ((u * p * u⁻¹ * p⁻¹) * u * u⁻¹) * (u * p * u⁻¹ * p⁻¹) := by rw [hcu]
        _ = 1 := by rw [mul_assoc _ u, mul_inv_cancel, mul_one, hcc]
    have key2 : (u * u) * p * (u * u)⁻¹ = p := by
      have := congrArg (· * p) key
      simpa [mul_assoc] using this
    calc p * (u * u) = ((u * u) * p * (u * u)⁻¹) * (u * u) := by rw [key2]
      _ = (u * u) * p := by group
  have hU2 : IsPGroup 2 U := by
    intro x
    refine ⟨2, ?_⟩
    have h := hc.elemAb.2 _ (hsq x x.2)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    calc (x : G) ^ 2 ^ 2 = ((x : G) * x) ^ 2 := by rw [← sq, ← pow_mul]; norm_num
      _ = 1 := h
  have hUQ : U ≤ inSubgroup (pCore 2) M := le_pCore_of_normal_inf hUM hUn hU2
  rw [← hc.hQ] at hUQ
  exact (le_inf le_rfl (hQP ▸ le_inf hUQ (hUM.trans inf_le_right) : U ≤ P)).trans hUPV

theorem residualMaxAbStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
      Subgroup.center (Xbar V H) = ⊥ →
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
      P.relIndex Q = 2 →
      (∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) →
      Maximal (fun U : Subgroup ↥(pResidual 2 G) =>
        U ≤ M.subgroupOf (pResidual 2 G) ∧
          M.subgroupOf (pResidual 2 G) ≤ Subgroup.normalizer (U : Set ↥(pResidual 2 G)) ∧
          IsMulCommutative U) (V.subgroupOf (pResidual 2 G)) := by
  intro G _ _ M V Q P H hH hZ hn hrel hOut
  obtain ⟨n, Φ, ψ, a, T, hn3, cfg⟩ := exists_resCfg hH hZ hn
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQP : Q ⊓ pResidual 2 G = P := inf_pResidual_eq_P hH hZ hn hrel hOut
  have hPG : P ≤ pResidual 2 G := P_le_pResidual hH hZ hn
  have hV : V ≤ pResidual 2 G := hc.V_le_P.trans hPG
  have hX : xOf V H ≤ pResidual 2 G := by
    obtain ⟨n', hn'3, ⟨e⟩⟩ := hn
    exact xOf_le_pResidual hH hn'3 e
  refine ⟨⟨?_, ?_, ?_⟩, fun U hU hVU => ?_⟩
  · exact fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hc.maxAb.prop.1 (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hx
    have hN : (x : G) ∈ Subgroup.normalizer (V : Set G) := hc.maxAb.prop.2.1 hxM
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp hN (y : G)
  · let e : ↥(V.subgroupOf (pResidual 2 G)) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hV
    exact IsMulCommutative.of_comm fun x y => by
      apply e.injective
      apply Subtype.ext
      simpa using congrArg Subtype.val (hc.elemAb.1.is_comm.comm (e x) (e y))
  · obtain ⟨hUM, hMU, hUc⟩ := hU
    have hU'M : U.map (pResidual 2 G).subtype ≤ M ⊓ pResidual 2 G := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (hUM hu), u.2⟩
    have hVU' : V ≤ U.map (pResidual 2 G).subtype := fun v hv =>
      ⟨⟨v, hV hv⟩, hVU (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
    have hU'ab : ∀ x ∈ U.map (pResidual 2 G).subtype, ∀ y ∈ U.map (pResidual 2 G).subtype,
        x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h := hUc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      have h2 := congrArg (fun z : ↥U => ((z : ↥(pResidual 2 G)) : G)) h
      simpa using h2
    have hU'n : ∀ m ∈ M ⊓ pResidual 2 G, ∀ x ∈ U.map (pResidual 2 G).subtype,
        m * x * m⁻¹ ∈ U.map (pResidual 2 G).subtype := by
      intro m hm
      rintro _ ⟨x, hx, rfl⟩
      have hm' : (⟨m, (Subgroup.mem_inf.mp hm).2⟩ : ↥(pResidual 2 G)) ∈
          M.subgroupOf (pResidual 2 G) := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hm).1
      have h := (Subgroup.mem_normalizer_iff.mp (hMU hm') x).mp hx
      exact ⟨_, h, rfl⟩
    have h := le_V_of_abelian_normalized cfg hX hQP hPG hU'M hVU' hU'ab hU'n
    intro u hu
    exact Subgroup.mem_subgroupOf.mpr (h ⟨u, hu, rfl⟩)

end CFSG.RankThree.GF2n.Tim79a
