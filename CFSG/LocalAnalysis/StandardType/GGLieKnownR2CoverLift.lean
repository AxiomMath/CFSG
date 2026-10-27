module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType.LieKnownR2.Cover

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2
open scoped commutatorElement

private theorem l10scov_eq_one_of_mem_inf_of_isPGroup_two_of_odd_card {G : Type*} [Group G]
    {K R : Subgroup G} (hKodd : Odd (Nat.card K)) (hR : IsPGroup 2 R)
    {x : G} (hxR : x ∈ R) (hxK : x ∈ K) : x = 1 := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hR) ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hKodd.coprime_two_left.pow_left k) hk hdvd)

private theorem l10scov_le_of_isPGroup_le_sup_of_odd_central {G : Type*} [Group G]
    {K R S : Subgroup G} [K.Normal] (hKc : K ≤ Subgroup.center G) (hKodd : Odd (Nat.card K))
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S) (hSR : S ≤ R ⊔ K) : S ≤ R := by
  intro g hgS
  obtain ⟨j, hj⟩ := hS ⟨g, hgS⟩
  have hgj : g ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨r, hrR, z, hzK, hrz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := R) (t := K)).mp (hSR hgS)
  have hcomm : Commute r z := Subgroup.mem_center_iff.mp (hKc hzK) r
  have hpow : (r * z) ^ 2 ^ j = r ^ 2 ^ j * z ^ 2 ^ j := hcomm.mul_pow _
  have hrp : r ^ 2 ^ j * z ^ 2 ^ j = 1 := by rw [← hpow, hrz, hgj]
  have hzpowR : z ^ 2 ^ j ∈ R := by
    have hz : z ^ 2 ^ j = (r ^ 2 ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hrp
    rw [hz]
    exact R.inv_mem (R.pow_mem hrR _)
  have hzpowK : z ^ 2 ^ j ∈ K := K.pow_mem hzK _
  have hzpow1 : z ^ 2 ^ j = 1 :=
    l10scov_eq_one_of_mem_inf_of_isPGroup_two_of_odd_card hKodd hR hzpowR hzpowK
  have hz1 : z = 1 := by
    have hdvd1 : orderOf z ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hzpow1
    have hdvd2 : orderOf z ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hzK
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hKodd.coprime_two_left.pow_left j) hdvd1 hdvd2)
  rw [← hrz, hz1, mul_one]
  exact hrR

private noncomputable def l10scov_inducedMulAut {U X : Type} [Group U] [Group X]
    (π : U →* X) (hπ : Function.Surjective π) (hZ : π.ker = Subgroup.center U)
    (y : MulAut U) : MulAut X :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.congr π.ker π.ker y (by rw [hZ, Subgroup.map_center_eq y])).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ))

private theorem l10scov_inducedMulAut_apply {U X : Type} [Group U] [Group X]
    (π : U →* X) (hπ : Function.Surjective π) (hZ : π.ker = Subgroup.center U)
    (y : MulAut U) (u : U) :
    l10scov_inducedMulAut π hπ hZ y (π u) = π (y u) := by
  have he : ∀ v : U, (QuotientGroup.quotientKerEquivOfSurjective π hπ)
      (QuotientGroup.mk' π.ker v) = π v := fun v => rfl
  unfold l10scov_inducedMulAut
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [← he u, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk', he (y u)]

private theorem l10scov_inducedMulAut_pow_apply {U X : Type} [Group U] [Group X]
    (π : U →* X) (hπ : Function.Surjective π) (hZ : π.ker = Subgroup.center U)
    (y : MulAut U) (n : ℕ) (u : U) :
    (l10scov_inducedMulAut π hπ hZ y ^ n) (π u) = π ((y ^ n) u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      calc (l10scov_inducedMulAut π hπ hZ y ^ (n + 1)) (π u)
          = (l10scov_inducedMulAut π hπ hZ y ^ n * l10scov_inducedMulAut π hπ hZ y)
              (π u) := by rw [pow_succ]
        _ = (l10scov_inducedMulAut π hπ hZ y ^ n)
              (l10scov_inducedMulAut π hπ hZ y (π u)) := by rw [MulAut.mul_apply]
        _ = (l10scov_inducedMulAut π hπ hZ y ^ n) (π (y u)) := by
              rw [l10scov_inducedMulAut_apply]
        _ = π ((y ^ n) (y u)) := ih (y u)
        _ = π ((y ^ (n + 1)) u) := by rw [pow_succ, MulAut.mul_apply]

private theorem l10scov_eq_one_of_forall_mul_inv_mem_center {S : Type*} [Group S]
    [Group.IsPerfect S] {τ : MulAut S} (h : ∀ s : S, s⁻¹ * τ s ∈ Subgroup.center S) :
    τ = 1 := by
  let z : S →* S :=
    { toFun := fun s => s⁻¹ * τ s
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (h s)
        calc (s * t)⁻¹ * τ (s * t) = t⁻¹ * (s⁻¹ * τ s) * τ t := by
              rw [map_mul]
              group
          _ = s⁻¹ * τ s * (t⁻¹ * τ t) := by
              rw [ht t⁻¹]
              group }
  have hzc : ∀ s, z s ∈ Subgroup.center S := h
  have hcomm : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab := Subgroup.mem_center_iff.mp (hzc a) (z b)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hab.symm
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * τ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

private theorem l10scov_mulAut_eq_of_inv_mul_mem_center {S : Type*} [Group S]
    [Group.IsPerfect S] {τ σ : MulAut S}
    (h : ∀ s : S, (τ s)⁻¹ * σ s ∈ Subgroup.center S) : τ = σ := by
  have hω : σ * τ⁻¹ = 1 := by
    apply l10scov_eq_one_of_forall_mul_inv_mem_center
    intro u
    have := h (τ⁻¹ u)
    simpa using this
  exact (mul_inv_eq_one.mp hω).symm

theorem ggRootNormInner_of_map_surjective {U X : Type} [Group U] [Group X] [Finite U]
    [Group.IsPerfect U] (π : U →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    (hX : Subgroup.center X = ⊥) {R : Subgroup U} (hR : IsPGroup 2 R)
    (h : GGRootNormInner (R.map π)) : GGRootNormInner R := by
  haveI : Finite X := Finite.of_surjective π hπ
  have hcenter_le : Subgroup.center U ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzX : π z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨u, rfl⟩ := hπ x
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz u).symm]
    rw [hX] at hzX
    exact Subgroup.mem_bot.mp hzX
  have hker_eq : π.ker = Subgroup.center U := le_antisymm hker hcenter_le
  intro y hy2 hyR hymod
  let ybar : MulAut X := l10scov_inducedMulAut π hπ hker_eq y
  have hybar_apply : ∀ u : U, ybar (π u) = π (y u) :=
    l10scov_inducedMulAut_apply π hπ hker_eq y
  have hybar_pow : ∀ (n : ℕ) (u : U), (ybar ^ n) (π u) = π ((y ^ n) u) :=
    l10scov_inducedMulAut_pow_apply π hπ hker_eq y
  have hybar2 : ∃ k : ℕ, ybar ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy2
    refine ⟨k, MulEquiv.ext fun x => ?_⟩
    obtain ⟨u, rfl⟩ := hπ x
    rw [hybar_pow (2 ^ k) u, hk]
    simp
  have hybarR : (R.map π).map ybar.toMonoidHom = R.map π := by
    have hcomp : ybar.toMonoidHom.comp π = π.comp y.toMonoidHom := by
      ext u
      exact hybar_apply u
    calc (R.map π).map ybar.toMonoidHom
        = R.map (ybar.toMonoidHom.comp π) :=
            Subgroup.map_map (K := R) (g := ybar.toMonoidHom) (f := π)
      _ = R.map (π.comp y.toMonoidHom) := by rw [hcomp]
      _ = (R.map y.toMonoidHom).map π :=
            (Subgroup.map_map (K := R) (g := π) (f := y.toMonoidHom)).symm
      _ = R.map π := by rw [hyR]
  have hN : (Subgroup.normalizer (R : Set U)).map π =
      Subgroup.normalizer ((R.map π : Subgroup X) : Set X) := by
    have h1 := map_normalizer_eq_range_inf_normalizer_map (ψ := π) hker hodd hR
    rw [MonoidHom.range_eq_top.mpr hπ, top_inf_eq] at h1
    exact h1
  have hP : (pCoreOf 2 (Subgroup.normalizer (R : Set U))).map π =
      pCoreOf 2 (Subgroup.normalizer ((R.map π : Subgroup X) : Set X)) := by
    have h1 := map_pCoreOf_eq_of_odd_central_ker (ψ := π) hker hodd
      (M := Subgroup.normalizer (R : Set U))
      (hker.trans (Subgroup.center_le_normalizer (R : Set U)))
    rw [hN] at h1
    exact h1
  have hybarmod : ∀ n ∈ Subgroup.normalizer ((R.map π : Subgroup X) : Set X),
      ybar n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer ((R.map π : Subgroup X) : Set X)) := by
    intro n hn
    rw [← hN] at hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have h1 : ybar (π m) * (π m)⁻¹ = π (y m * m⁻¹) := by
      rw [hybar_apply, map_mul, map_inv]
    rw [h1, ← hP]
    exact Subgroup.mem_map_of_mem π (hymod m hm)
  obtain ⟨c, hc⟩ := h ybar hybar2 hybarR hybarmod
  obtain ⟨u₀, hu₀⟩ := hπ c
  have key : ∀ g : U, ((MulAut.conj u₀) g)⁻¹ * y g ∈ Subgroup.center U := by
    intro g
    refine hker ?_
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, MulAut.conj_apply, hu₀, ← hybar_apply g, hc]
    group
  exact ⟨u₀, (l10scov_mulAut_eq_of_inv_mul_mem_center key).symm⟩

theorem ggRootNoCentralAt_top_of_map_surjective {U X : Type} [Group U] [Group X] [Finite U]
    (π : U →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) {R : Subgroup U} (hR : IsPGroup 2 R)
    (h : GGRootNoCentralAt (⊤ : Subgroup X) (R.map π)) :
    GGRootNoCentralAt (⊤ : Subgroup U) R := by
  haveI : Finite X := Finite.of_surjective π hπ
  intro A B hRA hAB hBp hNA hNB hcomm
  simp only [top_inf_eq] at hBp hNA hNB hcomm
  have hN : (Subgroup.normalizer (R : Set U)).map π =
      Subgroup.normalizer ((R.map π : Subgroup X) : Set X) := by
    have h1 := map_normalizer_eq_range_inf_normalizer_map (ψ := π) hker hodd hR
    rw [MonoidHom.range_eq_top.mpr hπ, top_inf_eq] at h1
    exact h1
  have hP : (pCoreOf 2 (Subgroup.normalizer (R : Set U))).map π =
      pCoreOf 2 (Subgroup.normalizer ((R.map π : Subgroup X) : Set X)) := by
    have h1 := map_pCoreOf_eq_of_odd_central_ker (ψ := π) hker hodd
      (M := Subgroup.normalizer (R : Set U))
      (hker.trans (Subgroup.center_le_normalizer (R : Set U)))
    rw [hN] at h1
    exact h1
  have hA2 : IsPGroup 2 A :=
    (GGRootNorm.isPGroup_pCoreOf (Subgroup.normalizer (R : Set U))).to_le (hAB.trans hBp)
  have hB2 : IsPGroup 2 B :=
    (GGRootNorm.isPGroup_pCoreOf (Subgroup.normalizer (R : Set U))).to_le hBp
  have hNAmap : Subgroup.normalizer ((R.map π : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((A.map π : Subgroup X) : Set X) := by
    rw [← hN]
    exact (Subgroup.map_mono hNA).trans (Subgroup.le_normalizer_map (f := π))
  have hNBmap : Subgroup.normalizer ((R.map π : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((B.map π : Subgroup X) : Set X) := by
    rw [← hN]
    exact (Subgroup.map_mono hNB).trans (Subgroup.le_normalizer_map (f := π))
  have hcommmap : ⁅B.map π, Subgroup.normalizer ((R.map π : Subgroup X) : Set X)⁆
      ≤ A.map π := by
    rw [← hN]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm
  have hBmapA : B.map π ≤ A.map π :=
    h (A.map π) (B.map π) (Subgroup.map_mono hRA) (Subgroup.map_mono hAB)
      (by rw [top_inf_eq, ← hP]; exact Subgroup.map_mono hBp)
      (by rw [top_inf_eq]; exact hNAmap)
      (by rw [top_inf_eq]; exact hNBmap)
      (by rw [top_inf_eq]; exact hcommmap)
  have hBS : B ≤ A ⊔ π.ker := by
    intro b hb
    have hb' : π b ∈ A.map π := hBmapA (Subgroup.mem_map_of_mem π hb)
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hb'
    rw [Subgroup.mem_sup_of_normal_right (s := A) (t := π.ker)]
    refine ⟨a, ha, a⁻¹ * b, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hax, inv_mul_cancel]
  exact fun b hb =>
    (l10scov_le_of_isPGroup_le_sup_of_odd_central hker hodd hA2 hB2 hBS) hb

theorem pCoreOf_normalizer_le_of_map_surjective {U X : Type} [Group U] [Group X] [Finite U]
    (π : U →* X) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) {R Q : Subgroup U} (hR : IsPGroup 2 R) (hQ : IsPGroup 2 Q)
    (h : pCoreOf 2 (Subgroup.normalizer ((R.map π : Subgroup X) : Set X)) ≤ Q.map π) :
    pCoreOf 2 (Subgroup.normalizer (R : Set U)) ≤ Q := by
  haveI : Finite X := Finite.of_surjective π hπ
  have hN : (Subgroup.normalizer (R : Set U)).map π =
      Subgroup.normalizer ((R.map π : Subgroup X) : Set X) := by
    have h1 := map_normalizer_eq_range_inf_normalizer_map (ψ := π) hker hodd hR
    rw [MonoidHom.range_eq_top.mpr hπ, top_inf_eq] at h1
    exact h1
  have hP : (pCoreOf 2 (Subgroup.normalizer (R : Set U))).map π =
      pCoreOf 2 (Subgroup.normalizer ((R.map π : Subgroup X) : Set X)) := by
    have h1 := map_pCoreOf_eq_of_odd_central_ker (ψ := π) hker hodd
      (M := Subgroup.normalizer (R : Set U))
      (hker.trans (Subgroup.center_le_normalizer (R : Set U)))
    rw [hN] at h1
    exact h1
  have hle : pCoreOf 2 (Subgroup.normalizer (R : Set U)) ≤ Q ⊔ π.ker := by
    intro x hx
    have hx' : π x ∈ Q.map π := h (hP ▸ Subgroup.mem_map_of_mem π hx)
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx'
    rw [Subgroup.mem_sup_of_normal_right (s := Q) (t := π.ker)]
    refine ⟨q, hq, q⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
  exact fun x hx =>
    (l10scov_le_of_isPGroup_le_sup_of_odd_central hker hodd hQ
      (GGRootNorm.isPGroup_pCoreOf (Subgroup.normalizer (R : Set U))) hle) hx

end CFSG.StandardType.LieKnownR2.Cover
