module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalSz2
public import CFSG.Quasithin.Background.SzAutBorelPf
public import CFSG.StronglyEmbedded.UniqueCosetEnd

public section

open scoped Pointwise LinearAlgebra.Projectivization

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP CFSG.Quasithin.SzAutBorelPf
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ABGLocalTools

theorem isSylowOf_suzukiU_suzukiB {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSylowOf 2 (suzukiU a K) (suzukiB a K) := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_suzukiU hK
  have htop : IsSylowOf 2 (suzukiU a K) (⊤ : Subgroup (suzukiGroup a K)) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hP₀ ▸ P₀.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hP₀]
    exact P₀.not_dvd_index
  exact htop.of_le (suzukiU_le_suzukiB a K) le_top

theorem map_suzukiU_eq_self_of_map_suzukiB_eq_self {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (γ : MulAut (suzukiGroup a K))
    (hγB : (suzukiB a K).map γ.toMonoidHom = suzukiB a K) :
    (suzukiU a K).map γ.toMonoidHom = suzukiU a K := by
  classical
  let B := suzukiB a K
  let U := suzukiU a K
  let V : Subgroup (suzukiGroup a K) := U.map γ.toMonoidHom
  have hUB : U ≤ B := suzukiU_le_suzukiB a K
  have hU_sylow : IsSylowOf 2 U B := isSylowOf_suzukiU_suzukiB hK
  have hVB : V ≤ B := by
    calc V ≤ B.map γ.toMonoidHom := Subgroup.map_mono hUB
      _ = B := hγB
  have hVcard : Nat.card V = Nat.card U :=
    Subgroup.card_map_of_injective γ.injective
  have hVrel : V.relIndex B = U.relIndex B := by
    have hV := Subgroup.relIndex_mul_card V B
    have hU := Subgroup.relIndex_mul_card U B
    rw [inf_eq_left.mpr hVB] at hV
    rw [inf_eq_left.mpr hUB] at hU
    rw [hVcard] at hV
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := U)) (hV.trans hU.symm)
  have hVp : IsPGroup 2 V := hU_sylow.isPGroup.map γ.toMonoidHom
  have hV_sylow : IsSylowOf 2 V B := by
    rw [isSylowOf_iff]
    exact ⟨hVB, hVp, by rw [hVrel]; exact (isSylowOf_iff.mp hU_sylow).2.2⟩
  have hBn : B ≤ Subgroup.normalizer (U : Set (suzukiGroup a K)) := by
    exact sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have hinf_sylow : IsSylowOf 2 (V ⊓ U) U :=
    hV_sylow.inf_of_le_normalizer hUB hBn
  have hUV : U ≤ V := by
    have hEq : U = V ⊓ U :=
      IsSylowOf.eq_of_le hinf_sylow inf_le_right le_rfl hU_sylow.isPGroup
    rw [hEq]
    exact inf_le_left
  have hVU : V = U :=
    IsSylowOf.eq_of_le (P := U) (Q := V) (K := B) hU_sylow hUV hVB hVp
  exact hVU

theorem inner_of_map_suzukiB_eq_self_centralizes_suzukiT {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (γ : MulAut (suzukiGroup a K))
    (hγB : (suzukiB a K).map γ.toMonoidHom = suzukiB a K)
    (hγT : ∀ t ∈ suzukiT a K, γ t = t) :
    ∃ y : suzukiGroup a K, γ = MulAut.conj y := by
  have hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K :=
    map_suzukiU_eq_self_of_map_suzukiB_eq_self hK γ hγB
  apply inner_of_torus_trivial ha hK γ hγU
  intro l
  rw [hγT _ (suzukiDElt_mem_suzukiT a K l), inv_mul_cancel]
  exact one_mem _

theorem mem_of_fixes_base_centralizes_torus
    {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal)
    (ω β : Ω) (Q T : Subgroup N) (ψ : N ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (P : SuzukiPointAction N Ω (2 ^ (2 * a + 1)) ω β Q T)
    (hψT : T.map ψ.toMonoidHom = suzukiT a (GaloisField 2 (2 * a + 1)))
    (hψB : (MulAction.stabilizer N ω).map ψ.toMonoidHom =
      suzukiB a (GaloisField 2 (2 * a + 1)))
    {g : X} (hgω : g • ω = ω)
    (hT : ∀ t ∈ T, g * (t : N) = (t : N) * g) : g ∈ N := by
  classical
  letI : N.Normal := hN
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  have hperfG : Group.IsPerfect (suzukiGroup a K) :=
    (suzuki_perfect (a := a) (K := K) ha hK).2
  have hperfN : Group.IsPerfect N :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  haveI : Nontrivial (suzukiGroup a K) := (suzuki_simple (a := a) (K := K) ha hK).2.1
  letI : Nontrivial N := ψ.toEquiv.nontrivial
  have hNnonab : ¬ IsMulCommutative N := hperfN.not_isMulCommutative
  have hCbot : Subgroup.centralizer (N : Set X) = ⊥ :=
    centralizer_eq_bot_of_isMultiplyPretransitive hNnonab h2
  let α : MulAut N := MulAut.conjNormal (H := N) g
  have hαB : (MulAction.stabilizer N ω).map α.toMonoidHom =
      MulAction.stabilizer N ω := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_map]
    have hcomp : N.subtype.comp α.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp N.subtype := by
      ext n
      change N.subtype (α n) = g * (N.subtype n) * g⁻¹
      rfl
    rw [hcomp, ← Subgroup.map_map]
    have hNω : (MulAction.stabilizer N ω).map N.subtype =
        N ⊓ MulAction.stabilizer X ω := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_inf, and_comm]
    have hNmap : N.map (MulAut.conj g).toMonoidHom = N := by
      simpa using Subgroup.Normal.map_conj_eq (H := N) g
    rw [hNω, Subgroup.map_inf_eq N (MulAction.stabilizer X ω)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hNmap]
    rw [show (MulAction.stabilizer X ω).map (MulAut.conj g).toMonoidHom =
        MulAction.stabilizer X ω from by
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hgω]]
  have hαT : ∀ t ∈ T, α t = t := by
    intro t ht
    apply Subtype.ext
    change g * (t : N) * g⁻¹ = (t : N)
    rw [hT t ht]
    group
  let γ : MulAut (suzukiGroup a K) := MulAut.congr ψ α
  have hγB : (suzukiB a K).map γ.toMonoidHom = suzukiB a K := by
    rw [← hψB, Subgroup.map_map]
    change (MulAction.stabilizer N ω).map (γ.toMonoidHom.comp ψ.toMonoidHom) =
      (MulAction.stabilizer N ω).map ψ.toMonoidHom
    have hcomp : γ.toMonoidHom.comp ψ.toMonoidHom =
        ψ.toMonoidHom.comp α.toMonoidHom := by
      ext n
      simp [γ, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hαB]
  have hγT : ∀ t ∈ suzukiT a K, γ t = t := by
    intro t ht
    rw [← hψT] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change (MulAut.congr ψ α) (ψ s) = ψ s
    simp [MulAut.congr_apply, hαT s hs]
  obtain ⟨y, hy⟩ := inner_of_map_suzukiB_eq_self_centralizes_suzukiT ha hK γ hγB hγT
  have hαeq : α = MulAut.conj (ψ.symm y) := by
    apply (MulAut.congr ψ).injective
    rw [show MulAut.congr ψ α = MulAut.conj y from hy]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  exact mem_of_conjNormal_mem_inner hCbot
    ⟨ψ.symm y, by
      change MulAut.conj (ψ.symm y) = MulAut.conjNormal (H := N) g
      exact hαeq.symm⟩

theorem szCentralizerLe_of_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    SzCentralizerLe X Ω N := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  obtain ⟨ω, β, Q, T, ψ, P, hψT, hψQ, hψB⟩ :=
    exists_szPointAction (X := X) (Ω := Ω) h2 ha N hN e hΩ
  haveI : MulAction.IsMultiplyPretransitive N Ω 2 := P.isMultiplyPretransitive
  delta SzCentralizerLe
  intro x y hxy g hg hcomm
  obtain ⟨n, hx, hy, hTxy⟩ := exists_conj_torus P hxy
  let g₀ : X := n⁻¹ * g * n
  have hg₀ω : g₀ • ω = ω := by
    change (n⁻¹ * g * n) • ω = ω
    rw [mul_smul, mul_smul, show (↑n : X) • ω = x from hx,
      show g • x = x from hg.1, ← show (↑n : X) • ω = x from hx]
    exact inv_smul_smul (n : N) ω
  have hg₀β : g₀ • β = β := by
    change (n⁻¹ * g * n) • β = β
    rw [mul_smul, mul_smul, show (↑n : X) • β = y from hy,
      show g • y = y from hg.2, ← show (↑n : X) • β = y from hy]
    exact inv_smul_smul (n : N) β
  have hcommT : ∀ t ∈ T, g₀ * (t : N) = (t : N) * g₀ := by
    intro t ht
    let t' : N := n * t * n⁻¹
    have ht' : t' ∈ T.map (MulAut.conj n).toMonoidHom := ⟨t, ht, rfl⟩
    have htfield : ((t' : N) : X) ∈
        N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y := by
      rw [inf_stabilizer_eq_map_subtype hTxy]
      exact ⟨t', ht', rfl⟩
    have hg' := hcomm ((t' : N) : X) htfield
    have hcalc : g₀ * (t : N) = n⁻¹ * (g * ((t' : N) : X)) * n := by
      change n⁻¹ * g * n * (t : X) = n⁻¹ * (g * ((n * t * n⁻¹ : N) : X)) * n
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcalc, hg']
    change n⁻¹ * (((n * t * n⁻¹ : N) : X) * g) * n = (t : X) * (n⁻¹ * g * n)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hg₀N : g₀ ∈ N :=
    mem_of_fixes_base_centralizes_torus h2 a ha N hN ω β Q T ψ P hψT hψB hg₀ω hcommT
  change g ∈ N
  have : g = n * g₀ * n⁻¹ := by
    change g = n * (n⁻¹ * g * n) * n⁻¹
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this]
  exact N.mul_mem (N.mul_mem n.2 hg₀N) (N.inv_mem n.2)

theorem rankOneZassenhaus_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    RankOneZassenhaus X Ω N :=
  rankOneZassenhaus_sz_of_centralizer h2 a ha N hN e hΩ
    (szCentralizerLe_of_sz h2 a ha N hN e hΩ)

end CFSG.Quasithin.Stroth.WeissDelta
