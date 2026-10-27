module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocal
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorEquivariant
public import CFSG.Timmesfeld.RankOne.Basic

public section

open scoped Pointwise LinearAlgebra.Projectivization

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.CTP

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem rankOneData_suzukiGroup
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RankOneData (suzukiGroup a K) (suzukiU a K) (suzukiB a K) := by
  classical
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUcard : Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 :=
    (suzuki_unipotent_structure hK).2.1
  have hTcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
    (suzuki_borel_structure hK).2.2.1
  have hTnorm : suzukiT a K ≤
      Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    suzukiT_le_normalizer hK
  have hUbot : suzukiU a K ≠ ⊥ := by
    intro h
    have h1 : Nat.card (suzukiU a K) = 1 := by rw [h, Subgroup.card_bot]
    rw [hUcard] at h1
    have h2 : 1 < (2 ^ (2 * a + 1)) ^ 2 := by
      calc 1 < 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) :=
          Nat.pow_le_pow_right (n := 2) (i := 1) (j := 2 * a + 1) (by norm_num) (by omega)
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := by
          calc 2 ^ (2 * a + 1) = 2 ^ (2 * a + 1) * 1 := by ring
            _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            _ = (2 ^ (2 * a + 1)) ^ 2 := by ring
    omega
  have hnT : ∀ t ∈ suzukiT a K,
      (suzukiWElt a K)⁻¹ * t * suzukiWElt a K ∈ suzukiT a K := by
    intro t ht
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    rw [suzukiWElt_inv, suzukiWElt_D_W hK]
    exact suzukiDElt_mem_suzukiT a K l⁻¹
  have hbruhat : ∀ g : suzukiGroup a K,
      g ∈ suzukiB a K ∨ ∃ b₁ ∈ suzukiB a K, ∃ b₂ ∈ suzukiB a K,
        g = b₁ * suzukiWElt a K * b₂ := by
    intro g
    rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, h⟩ |
      ⟨u, v, l, c, d, h⟩
    · exact Or.inl ((mem_suzukiB_iff hK).2 ⟨u, v, l, h⟩)
    · refine Or.inr ⟨suzukiSElt a K u v * suzukiDElt a K l,
        (mem_suzukiB_iff hK).2 ⟨u, v, l, rfl⟩, suzukiSElt a K c d,
        suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K c d), ?_⟩
      simpa [h]
  refine ⟨CFSG.LieType.SteinbergBR.isPGroup_suzukiU hK, hUbot,
    exists_sylow_eq_suzukiU hK, suzukiU_le_suzukiB a K, ?_, ?_, ?_⟩
  · haveI : IsSimpleGroup (suzukiGroup a K) := (suzuki_simple ha hK).2.2
    intro M hUM hM
    rcases le_B_or_eq_top_of_bruhat (B := suzukiB a K) (U := suzukiU a K)
      (T := suzukiT a K) (n := suzukiWElt a K) rfl hTnorm hnT
      (suzukiWElt_mul_self (a := a) (K := K)) hUbot hbruhat M hUM with h | h
    · exact h
    · exact absurd h hM.ne
  · haveI : MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 :=
      (suzukiPointAction_suzukiGroup hK).isMultiplyPretransitive
    haveI : MulAction.IsPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) :=
      MulAction.isPretransitive_of_is_two_pretransitive
    rw [show suzukiB a K = MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) from
        (suzukiPointAction_suzukiGroup hK).sup_eq_stabilizer,
      MulAction.index_stabilizer_of_transitive, (suzukiPointAction_suzukiGroup hK).card_eq,
      hUcard]
    omega
  · have hle : (suzukiU a K).relIndex (suzukiB a K) ≤ Nat.card (suzukiT a K) :=
      relIndex_le_card_right_of_sup_eq rfl hTnorm
    rw [hTcard] at hle
    rw [hUcard]
    have h1 : 2 ^ (2 * a + 1) - 1 < 2 ^ (2 * a + 1) := Nat.sub_one_lt (by positivity)
    have h2 : 2 ^ (2 * a + 1) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
      calc 2 ^ (2 * a + 1) = 2 ^ (2 * a + 1) * 1 := by ring
        _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (2 ^ (2 * a + 1)) ^ 2 := by ring
    exact lt_of_le_of_lt hle (lt_of_lt_of_le h1 h2)

end CFSG.Quasithin.Stroth.WeissDelta

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.LieType.Ree
  CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.CTP

noncomputable def szToSuzukiGroup (a : ℕ) :
    Sz a ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
  Classical.choice
    (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a)


private theorem map_conj_map_symm {N G : Type*} [Group N] [Group G] (φ : N ≃* G) (g : G)
    (H : Subgroup G) :
    ((H.map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom).map
      (φ.trans (MulAut.conj g⁻¹)).toMonoidHom = H := by
  rw [Subgroup.map_map, Subgroup.map_map]
  convert Subgroup.map_id H using 2
  apply MonoidHom.ext
  intro x
  simp [MulAut.conj_apply, mul_assoc]


theorem fix_two_of_pointAction {N Ω : Type*} [Group N] [MulAction N Ω] {q : ℕ}
    {ω β : Ω} {Q T : Subgroup N} (P : SuzukiPointAction N Ω q ω β Q T)
    (hCQ : ∀ t ∈ T, t ≠ 1 → ∀ r ∈ Q, r * t = t * r → r = 1) :
    ∀ t ∈ T, t ≠ 1 → ∀ x : Ω, t • x = x → x = ω ∨ x = β := by
  intro t ht ht1 x hx
  by_cases hxω : x = ω
  · exact Or.inl hxω
  · right
    have hTleω : T ≤ MulAction.stabilizer N ω := by
      rw [← P.sup_eq_stabilizer]
      exact le_sup_right
    have hTleβ : T ≤ MulAction.stabilizer N β := by
      rw [← P.stabilizer_inf_stabilizer]
      exact inf_le_right
    have hβne : β ≠ ω := P.ne.symm
    have htβ : t • β = β := hTleβ ht
    obtain ⟨r, hr, huniq⟩ := P.regular β x hβne hxω
    have hTnormQ : T ≤ Subgroup.normalizer (Q : Set N) :=
      hTleω.trans P.stabilizer_le_normalizer
    have hr' : t * (r : N) * t⁻¹ ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff''.mp (hTnormQ (T.inv_mem ht)) (r : N)).mp r.2
    have htβinv : t⁻¹ • β = β := by
      calc t⁻¹ • β = t⁻¹ • (t • β) := by rw [htβ]
        _ = β := inv_smul_smul t β
    have hr'β : ((⟨t * (r : N) * t⁻¹, hr'⟩ : Q) : N) • β = x := by
      calc (t * (r : N) * t⁻¹) • β
          = t • ((r : N) • (t⁻¹ • β)) := by rw [mul_smul, mul_smul]
        _ = t • ((r : N) • β) := by rw [htβinv]
        _ = t • x := by rw [hr]
        _ = x := hx
    have hr'eq : (⟨t * (r : N) * t⁻¹, hr'⟩ : Q) = r := huniq _ (by simpa using hr'β)
    have hcomm : (r : N) * t = t * (r : N) := by
      have hval := congrArg Subtype.val hr'eq
      change t * (r : N) * t⁻¹ = (r : N) at hval
      calc (r : N) * t = (t * (r : N) * t⁻¹) * t := by rw [hval]
        _ = t * (r : N) := by group
    have hr1 : r = 1 := Subtype.ext (hCQ t ht ht1 (r : N) r.2 hcomm)
    rw [hr1] at hr
    simpa using hr.symm

theorem centralizer_trivial_on_root {N G : Type*} [Group N] [Group G]
    (ψ : N ≃* G) {T Q : Subgroup N} {T₀ U₀ : Subgroup G}
    (hψT : T.map ψ.toMonoidHom = T₀) (hψQ : Q.map ψ.toMonoidHom = U₀)
    (hcent : ∀ t ∈ T₀, t ≠ 1 → Subgroup.centralizer {t} = T₀)
    (hdisj : U₀ ⊓ T₀ = ⊥) :
    ∀ t ∈ T, t ≠ 1 → ∀ q ∈ Q, q * t = t * q → q = 1 := by
  intro t ht ht1 q hq hcomm
  have hψcomm : ψ q * ψ t = ψ t * ψ q := by
    rw [← map_mul, ← map_mul, hcomm]
  have hψtT : ψ t ∈ T₀ := by
    have hmem : ψ t ∈ T.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ ht
    rwa [hψT] at hmem
  have hψqU : ψ q ∈ U₀ := by
    have hmem : ψ q ∈ Q.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hq
    rwa [hψQ] at hmem
  have hψt1 : ψ t ≠ 1 := fun h => ht1 (ψ.injective (by simpa using h))
  have hψqT : ψ q ∈ T₀ := by
    rw [← hcent (ψ t) hψtT hψt1]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hψcomm.symm
  have hmem : ψ q ∈ U₀ ⊓ T₀ := ⟨hψqU, hψqT⟩
  rw [hdisj, Subgroup.mem_bot] at hmem
  exact ψ.injective (by simpa using hmem)


theorem root_normal_in_pointStabilizer {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} [N.Normal] {ω : Ω} {Q : Subgroup N}
    (hQ2 : IsPGroup 2 Q) (hQsyl : ∃ S : Sylow 2 N, (S : Subgroup N) = Q)
    (hQle : Q ≤ MulAction.stabilizer N ω)
    (hQnormal : MulAction.stabilizer N ω ≤ Subgroup.normalizer (Q : Set N)) :
    MulAction.stabilizer X ω ≤
      Subgroup.normalizer ((Q.map N.subtype : Subgroup X) : Set X) := by
  classical
  obtain ⟨S, hS⟩ := hQsyl
  have hQmax : ∀ R : Subgroup N, IsPGroup 2 R → Q ≤ R → R = Q := by
    intro R hR hQR
    have hQR' : (S : Subgroup N) ≤ R := by rwa [hS]
    have h := S.is_maximal' hR hQR'
    rwa [hS] at h
  intro x hx
  let M : Subgroup N := MulAction.stabilizer N ω
  let Qx : Subgroup N := Q.map (MulAut.conjNormal (H := N) x).toMonoidHom
  have hxω : x • ω = ω := hx
  have hQxM : Qx ≤ M := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (x * ((q : N) : X) * x⁻¹) • ω = ω
    have hxinv : x⁻¹ • ω = ω := by
      calc x⁻¹ • ω = x⁻¹ • (x • ω) := by rw [hxω]
        _ = ω := inv_smul_smul x ω
    have hqω : ((q : N) : X) • ω = ω := hQle hq
    rw [mul_smul, mul_smul, hxinv, hqω, hxω]
  have hQx2 : IsPGroup 2 Qx := hQ2.map _
  let Qm : Subgroup M := Q.comap (Subgroup.subtype M)
  let Qxm : Subgroup M := Qx.comap (Subgroup.subtype M)
  have hQm2 : IsPGroup 2 Qm := hQ2.comap_subtype (K := M)
  have hQxm2 : IsPGroup 2 Qxm := hQx2.comap_subtype (K := M)
  have hQmN : Qm.Normal := by
    change (Q.subgroupOf M).Normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr hQnormal
  have hQxm_le : Qxm ≤ Subgroup.normalizer (Qm : Set M) := by
    haveI : Qm.Normal := hQmN
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hsup2 : IsPGroup 2 (Qm ⊔ Qxm : Subgroup M) :=
    hQm2.to_sup_of_normal_left' hQxm2 hQxm_le
  have hQmap : Qm.map (Subgroup.subtype M) = Q :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hQle)
  have hQxmap : Qxm.map (Subgroup.subtype M) = Qx :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hQxM)
  have hsupN : IsPGroup 2 (Q ⊔ Qx : Subgroup N) := by
    have h := hsup2.map (Subgroup.subtype M)
    rwa [Subgroup.map_sup, hQmap, hQxmap] at h
  have hsupQ : Q ⊔ Qx = Q := hQmax _ hsupN le_sup_left
  have hQxeq : Qx = Q := by
    refine Subgroup.eq_of_le_of_card_ge (hsupQ ▸ le_sup_right) ?_
    rw [show Nat.card Qx = Nat.card Q from
      Subgroup.card_map_of_injective (MulAut.conjNormal (H := N) x).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_map]
  change Subgroup.map ((MulAut.conj x).toMonoidHom.comp N.subtype) Q =
    Subgroup.map N.subtype Q
  have hcomp : (MulAut.conj x).toMonoidHom.comp N.subtype =
      N.subtype.comp (MulAut.conjNormal (H := N) x).toMonoidHom := by
    apply MonoidHom.ext
    intro y
    simp [MulAut.conj_apply, MulAut.conjNormal_apply]
  rw [hcomp, ← Subgroup.map_map]
  change Subgroup.map N.subtype Qx = Subgroup.map N.subtype Q
  rw [hQxeq]

variable {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]

theorem exists_szPointAction
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) {a : ℕ} (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    ∃ (ω β : Ω) (Q T : Subgroup N) (ψ : N ≃* suzukiGroup a (GaloisField 2 (2 * a + 1))),
      SuzukiPointAction N Ω (2 ^ (2 * a + 1)) ω β Q T ∧
      T.map ψ.toMonoidHom = suzukiT a (GaloisField 2 (2 * a + 1)) ∧
      Q.map ψ.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1)) ∧
      (MulAction.stabilizer N ω).map ψ.toMonoidHom =
        suzukiB a (GaloisField 2 (2 * a + 1)) := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 _ (by omega)
  let G := suzukiGroup a K
  let φ : N ≃* G := e.trans (szToSuzukiGroup a)
  let U₀ := suzukiU a K
  let B₀ := suzukiB a K
  let T₀ := suzukiT a K
  haveI : Finite G := (suzuki_simple ha hK).1
  have hdata₀ : RankOneData G U₀ B₀ := rankOneData_suzukiGroup ha hK
  let U_N : Subgroup N := U₀.map φ.symm.toMonoidHom
  let B_N : Subgroup N := B₀.map φ.symm.toMonoidHom
  have hdataN : RankOneData N U_N B_N := hdata₀.map φ.symm
  have hU_Ncard : Nat.card U_N = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective,
      (suzuki_unipotent_structure hK).2.1]
  have hNbot : N ≠ ⊥ := by
    intro hbot
    apply hdataN.ne_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hyN : ((y : N) : X) ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact y.2
    rw [Subgroup.mem_bot] at hyN
    exact hyN
  have hΩpos : 0 < Fintype.card Ω := by
    rw [hΩ]
    positivity
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp hΩpos
  let ω : Ω := Classical.arbitrary Ω
  have hcard : Fintype.card Ω = 1 + Nat.card U_N := by
    rw [hΩ, hU_Ncard, ← pow_mul, mul_comm]
    omega
  obtain ⟨x, hx⟩ := exists_stabilizer_eq_conj_of_rankOneData (Y := X) N hNbot h2 hdataN
    hcard ω
  let g : G := φ x
  have hcomp : φ.toMonoidHom.comp ((MulAut.conj x).toMonoidHom.comp φ.symm.toMonoidHom) =
      (MulAut.conj g).toMonoidHom := by
    apply MonoidHom.ext
    intro y
    simp [g, MulAut.conj_apply, map_mul, map_inv]
  have hmapB : ((MulAction.stabilizer X ω).subgroupOf N).map φ.toMonoidHom =
      B₀.map (MulAut.conj g).toMonoidHom := by
    rw [hx, Subgroup.map_map]
    change (B₀.map φ.symm.toMonoidHom).map
      (φ.toMonoidHom.comp (MulAut.conj x).toMonoidHom) = _
    rw [Subgroup.map_map]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      have hz' := congrArg (fun f : G →* G => f z) hcomp
      simp only [MonoidHom.comp_apply, MulAut.conj_apply] at hz'
      exact hz'.symm
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by
        have hz' := congrArg (fun f : G →* G => f z) hcomp
        simpa only [MonoidHom.comp_apply, MulAut.conj_apply] using hz'⟩
  let α₀ : suzukiOmegaSub hK :=
    ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩
  let β₀ : suzukiOmegaSub hK :=
    ⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩
  let P₀ : SuzukiPointAction G (suzukiOmegaSub hK) (2 ^ (2 * a + 1)) α₀ β₀ U₀ T₀ :=
    suzukiPointAction_suzukiGroup hK
  have hP₀B : MulAction.stabilizer G α₀ = B₀ := P₀.sup_eq_stabilizer.symm
  let P₁ : SuzukiPointAction G (suzukiOmegaSub hK) (2 ^ (2 * a + 1))
      (g • α₀) (g • β₀) (U₀.map (MulAut.conj g).toMonoidHom)
      (T₀.map (MulAut.conj g).toMonoidHom) := P₀.conj g
  let U₂ : Subgroup N := (U₀.map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom
  let T₂ : Subgroup N := (T₀.map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom
  letI : MulAction N (suzukiOmegaSub hK) := MulAction.compHom _ φ.toMonoidHom
  let P₂ : SuzukiPointAction N (suzukiOmegaSub hK) (2 ^ (2 * a + 1))
      (g • α₀) (g • β₀) U₂ T₂ :=
    P₁.of_mulEquiv φ.symm (by intro n y; rfl)
  have hstabG : MulAction.stabilizer G (g • α₀) = B₀.map (MulAut.conj g).toMonoidHom := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hP₀B]
  have hmapStab : (MulAction.stabilizer N (g • α₀)).map φ.toMonoidHom =
      MulAction.stabilizer G (g • α₀) := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      change φ (φ.symm y) • (g • α₀) = g • α₀
      simpa using hy
  have hstabN : MulAction.stabilizer N (g • α₀) =
      (MulAction.stabilizer X ω).subgroupOf N := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hmapStab, hmapB]
    exact hstabG
  haveI : MulAction.IsPreprimitive X Ω := MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive X Ω := inferInstance
  have hNfixed : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
    intro y
    have hy : y ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ y
    simpa using hy ⟨n, hn⟩
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hNfixed
  let Bc : Subgroup N := MulAction.stabilizer N (g • α₀)
  have hBc : Bc = (MulAction.stabilizer X ω).subgroupOf N := hstabN
  obtain ⟨β, hβ⟩ := P₂.exists_quotient (B := Bc) rfl
  let Q : Subgroup N := U₂
  let T : Subgroup N := T₂
  have hstab_coset : MulAction.stabilizer N (QuotientGroup.mk 1 : N ⧸ Bc) = Bc :=
    MulAction.stabilizer_quotient Bc
  have hstab_omega : MulAction.stabilizer N ω = Bc := by
    rw [hBc]
    rfl
  obtain ⟨f, hfω, hf⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.transitive_action_equiv_of_stabilizer_eq
      (G := N) inferInstance inferInstance (QuotientGroup.mk 1 : N ⧸ Bc) ω
      (by rw [hstab_coset, hstab_omega])
  let Pc : SuzukiPointAction N (N ⧸ Bc) (2 ^ (2 * a + 1))
      (QuotientGroup.mk 1) β Q T := hβ.1
  let P : SuzukiPointAction N Ω (2 ^ (2 * a + 1)) ω (f β) Q T := by
    rw [← hfω]
    exact Pc.of_equiv f hf
  let ψ : N ≃* G := φ.trans (MulAut.conj g⁻¹)
  have hψT : T.map ψ.toMonoidHom = T₀ :=
    map_conj_map_symm φ g T₀
  have hψQ : Q.map ψ.toMonoidHom = U₀ :=
    map_conj_map_symm φ g U₀
  have hψB : (MulAction.stabilizer N ω).map ψ.toMonoidHom = B₀ := by
    rw [hstab_omega, hBc]
    rw [show ψ.toMonoidHom = (MulAut.conj g⁻¹).toMonoidHom.comp φ.toMonoidHom by rfl]
    rw [← Subgroup.map_map, hmapB]
    exact CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj B₀ g
  refine ⟨ω, f β, Q, T, ψ, P, hψT, hψQ, hψB⟩

end CFSG.Quasithin.Stroth.WeissDelta
