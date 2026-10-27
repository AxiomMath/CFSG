module

public import CFSG.RankThree.GF2n.Smith81.S81YGenX

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

variable {G : Type} [Group G]

section Point

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {V : Type} [AddCommGroup V]
  [Module K V] {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
  {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
  {IsRt : (V ≃ₗ[K] V) → Prop} {z : G}


theorem exists_point_centralized_gen (Dt : GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z) {x y : G}
    (hxc : IsConj z x) (hxM : x ∈ M) (hxQ : x ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M)
    (hyQ : y ∉ Q) {r s : V ≃ₗ[K] V} (hr : IsRt r) (hs : IsRt s) (hx : Acts φ x r)
    (hy : Acts φ y s) (hB : ¬ (Odd (orderOf (r * s)) ∧ r * s ≠ 1))
    (hA : ∀ X : Subgroup G, Sit M Q Z X x →
      ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ A ≤ QB X) :
    ∃ D : Subgroup G, IsZConjugate Z D ∧ x ∈ QB D ∧ y ∈ Subgroup.centralizer (D : Set G) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X, hXs, Tx, hII, hRs⟩ := Dt.xdata_gen hxc hxM hxQ hr hx
  obtain ⟨Y, hYs, Ty, hIIy, -⟩ := Dt.xdata_gen hyc hyM hyQ hs hy
  have hXc : IsZConjugate Z X := hXs.conj
  obtain ⟨A, hAZc, hAQ, hAne, hAX⟩ := hA X hXs
  obtain ⟨gA, hgAΓ, himg, -⟩ := Dt.d.point A hAZc hAQ hAne
  have hpure : IsPurePt Γ p₀ (gA p₀) := ⟨gA, hgAΓ, 1, one_ne_zero, by rw [one_smul]⟩
  have hmemimg : gA p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := by
    rw [himg]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a₁, ha₁A, ha₁eq⟩ := hmemimg
  have hπR : M₀.π a₁ ∈ Rs Tx :=
    caseII_piD_le_R Dt.hD hXs Tx hII (Subgroup.mem_inf.mpr ⟨hAQ ha₁A, hAX ha₁A⟩)
  have hmem : gA p₀ ∈ LinearMap.range ((r : V →ₗ[K] V) - 1) := by
    rw [← ha₁eq]
    exact (hRs _).mp hπR
  obtain ⟨c, hcΓ, hcomm, hkey⟩ := Dt.mrf.move r s hr hs hB (gA p₀) hpure hmem
  obtain ⟨u, hu⟩ := MinuscT.exists_lift_E Dt.d hcΓ
  have hxL := hx.mem_Lgen
  have hu0 : (u : G) ∈ H0 M Z := Lgen_le_H0 Dt.ctx u.2
  have hux : ⁅(u : G), x⁆ ∈ Q := MinuscT.comm_mem_Q_of_lift_E Dt.d hxL u.2 (hx.phi hxL) hu hcomm
  have hNFx : ∀ y' : G, IsConj x y' → y' ∈ M → y' ∉ Q → ∀ w ∈ Z, w ≠ 1 →
      ¬ IsConj y' (y' * w) :=
    fun y' hyc' hyM' hyQ' w hw hw1 => Dt.nf y' (hxc.trans hyc') hyM' hyQ' w hw hw1
  obtain ⟨q₀, hq₀, hconj⟩ := E3LRoot.conj_eq_of_comm_mem_Q Dt.hD hXs Tx hII hNFx hu0 hux
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : G, u₀ = (u : G) := ⟨_, rfl⟩
  rw [← hu₀] at hu0 hconj
  have hmx : u₀ * x = q₀ * x * q₀⁻¹ * u₀ := by
    rw [← hconj]
    group
  have hyx : q₀⁻¹ * u₀ * x = x * (q₀⁻¹ * u₀) := by
    calc q₀⁻¹ * u₀ * x = q₀⁻¹ * (u₀ * x) := by group
      _ = q₀⁻¹ * (q₀ * x * q₀⁻¹ * u₀) := by rw [hmx]
      _ = x * (q₀⁻¹ * u₀) := by group
  have hnorm : q₀⁻¹ * u₀ ∈ Subgroup.normalizer (X : Set G) :=
    IsZConjugate.mem_normalizer_of_commute H hXc hXs.ne_one hXs.mem
      (show Commute (q₀⁻¹ * u₀) x from hyx)
  have hq₀M : q₀ ∈ M := H.Q_normal.1 hq₀
  have hcM : q₀⁻¹ * u₀ ∈ M := M.mul_mem (M.inv_mem hq₀M) (Subgroup.mem_inf.mp hu0).1
  have hu₀M : u₀ ∈ M := (Subgroup.mem_inf.mp hu0).1
  refine ⟨conjSubgroup (q₀⁻¹ * u₀) A, hAZc.conj _, ?_, ?_⟩
  ·
    have hDX : conjSubgroup (q₀⁻¹ * u₀) A ≤ QB X := by
      intro d₁ hd₁
      have h1 : (q₀⁻¹ * u₀)⁻¹ * d₁ * (q₀⁻¹ * u₀) ∈ A := mem_conjSubgroup.mp hd₁
      have h2 := IsZConjugate.conj_mem_QB H hXc hnorm (hAX h1)
      have e : q₀⁻¹ * u₀ * ((q₀⁻¹ * u₀)⁻¹ * d₁ * (q₀⁻¹ * u₀)) * (q₀⁻¹ * u₀)⁻¹ = d₁ := by
        group
      rwa [e] at h2
    have hXD : X ≤ QB (conjSubgroup (q₀⁻¹ * u₀) A) :=
      ((hAZc.conj (q₀⁻¹ * u₀)).le_QB_iff H hXc).mpr hDX
    exact hXD hXs.mem
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro d₁ hd₁
    have h1 : (q₀⁻¹ * u₀)⁻¹ * d₁ * (q₀⁻¹ * u₀) ∈ A := mem_conjSubgroup.mp hd₁
    obtain ⟨a₂, ha₂, hd₁eq⟩ : ∃ a₂ ∈ A, d₁ = q₀⁻¹ * u₀ * a₂ * (q₀⁻¹ * u₀)⁻¹ :=
      ⟨_, h1, by group⟩
    have ha₂Q : a₂ ∈ Q := hAQ ha₂
    have hd₁Q : d₁ ∈ Q := by
      rw [hd₁eq]
      exact conj_mem_Q H hcM ha₂Q
    have hπd : ψ (M₀.π d₁) = c (ψ (M₀.π a₂)) := by
      have e : d₁ = q₀⁻¹ * (u₀ * a₂ * u₀⁻¹) * q₀⁻¹⁻¹ := by rw [hd₁eq]; group
      have hw : u₀ * a₂ * u₀⁻¹ ∈ Q := conj_mem_Q H hu₀M ha₂Q
      rw [e, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (Q.inv_mem hq₀) hw]
      have hev := Dt.d.equivariant u a₂ ha₂Q
      rw [hu₀, hev, hu]
    obtain ⟨κ, hκ⟩ : ∃ κ : K, ψ (M₀.π a₂) = κ • gA p₀ := by
      have hm : ψ (M₀.π a₂) ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := ⟨a₂, ha₂, rfl⟩
      rw [himg] at hm
      obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hm
      exact ⟨κ, hκ.symm⟩
    have hfix : s (ψ (M₀.π d₁)) = ψ (M₀.π d₁) := by
      rw [hπd, hκ]
      simp only [map_smul, hkey]
    have hyL := hy.mem_Lgen
    have hTy : Ty.T (M₀.π d₁) = M₀.π d₁ := by
      apply ψ.injective
      rw [MinuscT.psi_T_E Dt.d hyL Ty (hy.phi hyL)]
      exact hfix
    have hZ : ⁅d₁, y⁆ ∈ Z := (comm_mem_Z_iff hYs Ty hd₁Q).mpr (mem_Cs.mpr hTy)
    exact commutatorElement_eq_one_iff_mul_comm.mp (hIIy d₁ hd₁Q hZ)

end Point

end CFSG.RankThree.GF2n.Smith81.RootGen
