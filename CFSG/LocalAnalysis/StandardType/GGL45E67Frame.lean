module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift
public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45E67_mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem ggL45E67_conj_injective {G : Type*} [Group G]
    (hcenter : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hcent : r ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 := congrArg (fun f : MulAut G => f s) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc s * r = (r * s * r⁻¹) * r := by rw [h1]
      _ = r * s := by group
  exact Subgroup.mem_bot.mp (hcenter ▸ hcent)

private theorem ggL45E67_zpow_eq_self {G : Type*} [Group G] {t : G} {c : ℤ}
    (ht : t ^ 3 = 1) (hc : c ≡ 1 [ZMOD 3]) : t ^ c = t := by
  have hdvd : (3 : ℤ) ∣ c - 1 := by
    have h : (3 : ℤ) ∣ (1 : ℤ) - c := Int.modEq_iff_dvd.mp hc
    have h2 : (1 : ℤ) - c = -(c - 1) := by ring
    rw [h2] at h
    exact dvd_neg.mp h
  obtain ⟨m, hm⟩ := hdvd
  have hc' : c = 1 + ((3 : ℕ) : ℤ) * m := by
    have h3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
    rw [h3]; linarith
  have ht' : t ^ (((3 : ℕ)) : ℤ) = 1 := by rw [zpow_natCast]; exact ht
  rw [hc', zpow_add, zpow_one, zpow_mul, ht', one_zpow, mul_one]

private theorem ggL45E67_isPElt_pPart {K : Type*} [Group K] [Finite K] (α : MulAut K) :
    GGL45IsPElt 3 (TauCeti.pPart 3 α) := by
  have h := TauCeti.orderOf_pPart (p := 3) (x := α) Nat.prime_three (orderOf_pos α).ne'
  exact ⟨(orderOf α).factorization 3, orderOf_dvd_iff_pow_eq_one.mp (by rw [h])⟩

private theorem ggL45E67_isPGroup_zpowers {K : Type*} [Group K] {a : MulAut K}
    (ha : GGL45IsPElt 3 a) : IsPGroup 3 (Subgroup.zpowers a) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  have hg : (g : MulAut K) = a ^ n := hn.symm
  have hN : (a : MulAut K) ^ ((3 ^ k : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hk]
  have h1 : ((g : MulAut K)) ^ 3 ^ k = 1 := by
    rw [hg, ← zpow_natCast (a ^ n) (3 ^ k), ← zpow_mul, mul_comm, zpow_mul, hN, one_zpow]
  exact Subtype.ext h1

private theorem ggL45E67_aut_fixes_center {K : Type*} [Group K] [Finite K]
    (hZ : Nat.card (Subgroup.center K) ∣ 3) {ψ : MulAut K} (hψ : ψ ^ 3 = 1) :
    ∀ z ∈ Subgroup.center K, ψ z = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(Subgroup.center K) := Subtype.finite
  have h3 : (MulAut.characteristic (Subgroup.center K) ψ) ^ 3 = 1 := by
    rw [← map_pow, hψ, map_one]
  have hdvd3 : orderOf (MulAut.characteristic (Subgroup.center K) ψ) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h3
  have hdvd2 : orderOf (MulAut.characteristic (Subgroup.center K) ψ) ∣ 2 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hZ with h1 | h3card
    · haveI : Subsingleton ↥(Subgroup.center K) := by
        rw [Subgroup.card_eq_one.mp h1]
        refine ⟨fun a b => Subtype.ext ?_⟩
        rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
      have hone : MulAut.characteristic (Subgroup.center K) ψ = 1 := by
        apply MulEquiv.ext
        intro w
        exact Subsingleton.elim _ _
      rw [hone, orderOf_one]
      exact one_dvd 2
    · haveI : IsCyclic ↥(Subgroup.center K) := isCyclic_of_prime_card h3card
      have hcard : Nat.card (MulAut ↥(Subgroup.center K)) = 2 := by
        rw [IsCyclic.card_mulAut, h3card]
        decide
      exact hcard ▸ orderOf_dvd_natCard _
  have hdvd1 : orderOf (MulAut.characteristic (Subgroup.center K) ψ) ∣ 1 := by
    have h := Nat.dvd_gcd hdvd2 hdvd3
    rwa [show Nat.gcd 2 3 = 1 from by decide] at h
  have hρ : MulAut.characteristic (Subgroup.center K) ψ = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  intro z hz
  have h2 := congrArg
    (fun f : MulAut ↥(Subgroup.center K) => ((f ⟨z, hz⟩ : ↥(Subgroup.center K)) : K)) hρ
  rw [MulAut.characteristic_apply_apply_coe] at h2
  simpa using h2

private theorem ggL45E67_eq_one_of_pow_eq_one {K : Type*} [Group K]
    (hcenter3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1) {N : ℕ} (hN : Nat.Coprime N 3) {z : K}
    (hz : z ∈ Subgroup.center K) (hzN : z ^ N = 1) : z = 1 := by
  have hdvd : orderOf z ∣ 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr (hcenter3 z hz))
      (orderOf_dvd_iff_pow_eq_one.mpr hzN)
    rwa [← Nat.gcd_comm, hN.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

private abbrev ggL45E67_pi {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : K →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))

private theorem ggL45E67_pi_apply {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (x : K) :
    ggL45E67_pi θ x = θ (x : K ⧸ Subgroup.center K) := rfl

private theorem ggL45E67_pi_surjective {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : Function.Surjective (ggL45E67_pi θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

private theorem ggL45E67_pi_ker {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : (ggL45E67_pi θ).ker = Subgroup.center K := by
  ext x
  rw [MonoidHom.mem_ker, ggL45E67_pi_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

private theorem ggL45E67_pi_card_ker {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Nat.card (Subgroup.center K) ∣ 3) :
    Nat.card (ggL45E67_pi θ).ker = 1 ∨ Nat.card (ggL45E67_pi θ).ker = 3 := by
  rw [ggL45E67_pi_ker]
  exact (Nat.dvd_prime Nat.prime_three).mp hZ

private theorem ggL45E67_center_pow_three {K : Type*} [Group K]
    (hZ : Nat.card (Subgroup.center K) ∣ 3) {z : K} (hz : z ∈ Subgroup.center K) : z ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hz).trans hZ)

private theorem ggL45E67_inducedAut_pi {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (π : K →* R)
    (hπ : ∀ x : K, π x = θ (x : K ⧸ Subgroup.center K)) (a : MulAut K) (x : K) :
    ggInducedAut θ a (π x) = π (a x) := by
  rw [hπ, hπ]
  exact ggInducedAut_apply θ a x

private theorem ggL45E67_inducedAut_conj {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (x : K) :
    ggInducedAut θ (MulAut.conj x) = MulAut.conj (θ (x : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    show ggInducedAut θ (MulAut.conj x) (θ (l : K ⧸ Subgroup.center K)) =
      MulAut.conj (θ (x : K ⧸ Subgroup.center K)) (θ (l : K ⧸ Subgroup.center K))
    rw [ggInducedAut_apply, MulAut.conj_apply x l, MulAut.conj_apply]
    simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

private structure QuotFrame (R : Type) [Group R] (D : E6ThreeModel.FrameData R) (K : Type)
    [Group K] (θ : K ⧸ Subgroup.center K ≃* R) where
  π : K →* R
  π_apply : ∀ x : K, π x = θ (x : K ⧸ Subgroup.center K)
  surj : Function.Surjective π
  ker_eq : π.ker = Subgroup.center K
  w : Fin 6 → K
  w_spec : ∀ i, π (w i) = D.nb i
  noInvFunc : GGNoInvFunc π (Set.range w) D.Tor
  noInvAlt : GGNoInvAlt π (Set.range w) D.Tor

private theorem QuotFrame.inducedAut {R K : Type} [Group R] [Group K]
    {D : E6ThreeModel.FrameData R} {θ : K ⧸ Subgroup.center K ≃* R} (S : QuotFrame R D K θ)
    (a : MulAut K) (x : K) : ggInducedAut θ a (S.π x) = S.π (a x) :=
  ggL45E67_inducedAut_pi θ S.π S.π_apply a x

private abbrev ggL45E67_THat {R K : Type} [Group R] [Group K] (D : E6ThreeModel.FrameData R)
    (π : K →* R) : Subgroup K :=
  D.Tor.comap π

private theorem ggL45E67_mem_THat {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (π : K →* R) (x : K) :
    x ∈ ggL45E67_THat D π ↔ π x ∈ D.Tor := Iff.rfl

private theorem ggL45E67_lift_normalizes {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (hD : D.Good) {π : K →* R} {w : Fin 6 → K}
    (hw : ∀ i, π (w i) = D.nb i) :
    ∀ n ∈ Set.range w, ∀ t ∈ D.Tor, π n * t * (π n)⁻¹ ∈ D.Tor := by
  obtain ⟨-, hnbT, -, -⟩ := hD.weyl
  rintro _ ⟨i, rfl⟩ t ht
  rw [hw i]
  exact hnbT i t ht

private theorem ggL45E67_exists_N {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) (π : K →* R) :
    ∃ v N : ℕ, ¬ 3 ∣ N ∧ Nat.card ↥(ggL45E67_THat D π) = 3 ^ v * N ∧ Nat.Coprime N 3 := by
  haveI : Finite ↥(ggL45E67_THat D π) := Subtype.finite
  haveI : Nonempty ↥(ggL45E67_THat D π) := ⟨1⟩
  obtain ⟨v, N, hN3, hTcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := ↥(ggL45E67_THat D π))).ne' 3
      (by norm_num)
  exact ⟨v, N, hN3, hTcard, ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3).symm⟩

private theorem ggL45E67_pow_N_isPElt {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {π : K →* R} {v N : ℕ}
    (hTcard : Nat.card ↥(ggL45E67_THat D π) = 3 ^ v * N) :
    ∀ x : ↥(ggL45E67_THat D π), ((x : K) ^ N) ^ 3 ^ v = 1 := by
  intro x
  have h1 : ((x : K)) ^ Nat.card ↥(ggL45E67_THat D π) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := x))
  rw [← pow_mul, mul_comm, ← hTcard]
  exact h1

private theorem ggL45E67_isElemAbelian_comm {K : Type*} [Group K] {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
  haveI : IsMulCommutative ↥E := hE.1
  intro e he e' he'
  exact congrArg Subtype.val (mul_comm' ⟨e, he⟩ ⟨e', he'⟩)

private theorem ggL45E67_isElemAbelian_isPElt {K : Type*} [Group K] {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) : ∀ e ∈ E, GGL45IsPElt 3 e :=
  fun e he => ⟨1, by simpa using hE.2 e he⟩

private theorem ggL45E67_E_fixes_torus {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hEI : ∀ e ∈ E, GGL45InducesIn θ I e)
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ t ∈ D.Tor, u t = t) :
    ∀ e ∈ E, ∀ t ∈ D.Tor, ggInducedAut θ e t = t := by
  intro e he t ht
  have heI : ggInducedAut θ e ∈ I := (ggL45_inducesIn_iff θ I e).mp (hEI e he)
  refine hC _ heI (fun e' he' => ?_) t ht
  rw [← map_mul, ← map_mul, ggL45E67_isElemAbelian_comm hE e he e' he']

private theorem ggL45E67_H1_torus {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    {E : Subgroup (MulAut K)} {ψ : MulAut K} {s : ℕ} {c : ℤ}
    (hcenter : Subgroup.center R = ⊥) (hTI : ∀ t ∈ D.Tor, MulAut.conj t ∈ I)
    (hEfix : ∀ e ∈ E, ∀ t ∈ D.Tor, ggInducedAut θ e t = t)
    (hH1 : GGL45HOne 3 I θ E (ggInducedAut θ ψ) s c) :
    ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 →
      t ^ 3 ^ s = 1 ∧ ggInducedAut θ ψ t = t ^ c := by
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    ggL45E67_conj_injective hcenter
  intro t htT k htk
  have hIn : GGL45InCIp 3 I θ E (MulAut.conj t) := by
    refine ⟨hTI t htT, ?_, ⟨k, ?_⟩⟩
    · intro e he
      have h1 : ggInducedAut θ e * MulAut.conj t * (ggInducedAut θ e)⁻¹ = MulAut.conj t := by
        rw [ggL45E67_mul_conj_mul_inv, hEfix e he t htT]
      have h2 : ggInducedAut θ e * MulAut.conj t = MulAut.conj t * ggInducedAut θ e := by
        have h3 := congrArg (fun x : MulAut R => x * ggInducedAut θ e) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    · rw [← map_pow, htk, map_one]
  obtain ⟨h1, h2⟩ := hH1.2 (MulAut.conj t) hIn
  refine ⟨?_, ?_⟩
  · have h1' : MulAut.conj (t ^ 3 ^ s) = MulAut.conj (1 : R) := by
      rw [map_pow, h1]
      exact (map_one MulAut.conj).symm
    exact hconj_inj h1'
  · have h2' : MulAut.conj (ggInducedAut θ ψ t) = MulAut.conj (t ^ c) := by
      rw [← ggL45E67_mul_conj_mul_inv, h2, map_zpow]
    exact hconj_inj h2'

private theorem ggL45E67_psi_three {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K} {s : ℕ}
    {c : ℤ} (hc : c ≡ 1 [ZMOD 3])
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 →
      t ^ 3 ^ s = 1 ∧ ggInducedAut θ ψ t = t ^ c) :
    ∀ t ∈ D.Tor, t ^ 3 = 1 → ggInducedAut θ ψ t = t := by
  intro t htT ht3
  rw [(hStep3 t htT 1 (by simpa using ht3)).2]
  exact ggL45E67_zpow_eq_self ht3 hc

private theorem ggL45E67_weyl_psi {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (hD : D.Good) (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (hPsi3 : ∀ t ∈ D.Tor, t ^ 3 = 1 → ggInducedAut θ ψ t = t) :
    ∀ i, (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) ∈ D.Tor := by
  obtain ⟨-, hnbT, -, -⟩ := hD.weyl
  intro i
  refine (hD.cent _).mp ?_
  intro v hv
  obtain ⟨r, hrT, hr3, hrv⟩ := hD.inner v hv
  have hnrT : D.nb i * r * (D.nb i)⁻¹ ∈ D.Tor := hnbT i r hrT
  have hnr3 : (D.nb i * r * (D.nb i)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hr3, mul_one, mul_inv_cancel]
  have hfixr : ggInducedAut θ ψ r = r := hPsi3 r hrT hr3
  have hfixnr : ggInducedAut θ ψ (D.nb i * r * (D.nb i)⁻¹) = D.nb i * r * (D.nb i)⁻¹ :=
    hPsi3 _ hnrT hnr3
  have hmul : ggInducedAut θ ψ (D.nb i * r * (D.nb i)⁻¹) =
      ggInducedAut θ ψ (D.nb i) * r * (ggInducedAut θ ψ (D.nb i))⁻¹ := by
    rw [map_mul, map_mul, map_inv, hfixr]
  rw [hmul] at hfixnr
  have key : (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) * r *
      ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i))⁻¹ = r := by
    calc (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) * r *
          ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i))⁻¹
        = (D.nb i)⁻¹ * (ggInducedAut θ ψ (D.nb i) * r * (ggInducedAut θ ψ (D.nb i))⁻¹) *
            D.nb i := by group
      _ = (D.nb i)⁻¹ * (D.nb i * r * (D.nb i)⁻¹) * D.nb i := by rw [hfixnr]
      _ = r := by group
  have hcomm : r * ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i)) =
      ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i)) * r := by
    have h1 : (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) * r =
        r * ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i)) := by
      calc (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) * r
          = ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) * r *
              ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i))⁻¹) *
              (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) := by group
        _ = r * ((D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i)) := by rw [key]; group
    exact h1.symm
  rw [← hrv, MulAut.conj_apply, hcomm]
  group

private theorem ggL45E67_weyl_I {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (hD : D.Good) (θ : K ⧸ Subgroup.center K ≃* R)
    {I : Set (MulAut R)} {E : Subgroup (MulAut K)}
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ t ∈ D.Tor, u t = t) :
    ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ i, (D.nb i)⁻¹ * u (D.nb i) ∈ D.Tor := by
  obtain ⟨-, hnbT, -, -⟩ := hD.weyl
  intro u hu hcomm i
  refine (hD.cent _).mp ?_
  intro v hv
  obtain ⟨r, hrT, hr3, hrv⟩ := hD.inner v hv
  have hfixr : u r = r := hC u hu hcomm r hrT
  have hnrT : D.nb i * r * (D.nb i)⁻¹ ∈ D.Tor := hnbT i r hrT
  have hfixnr : u (D.nb i * r * (D.nb i)⁻¹) = D.nb i * r * (D.nb i)⁻¹ :=
    hC u hu hcomm _ hnrT
  have hmul : u (D.nb i * r * (D.nb i)⁻¹) = u (D.nb i) * r * (u (D.nb i))⁻¹ := by
    rw [map_mul, map_mul, map_inv, hfixr]
  rw [hmul] at hfixnr
  have key : (D.nb i)⁻¹ * u (D.nb i) * r * ((D.nb i)⁻¹ * u (D.nb i))⁻¹ = r := by
    calc (D.nb i)⁻¹ * u (D.nb i) * r * ((D.nb i)⁻¹ * u (D.nb i))⁻¹
        = (D.nb i)⁻¹ * (u (D.nb i) * r * (u (D.nb i))⁻¹) * D.nb i := by group
      _ = (D.nb i)⁻¹ * (D.nb i * r * (D.nb i)⁻¹) * D.nb i := by rw [hfixnr]
      _ = r := by group
  have hcomm' : r * ((D.nb i)⁻¹ * u (D.nb i)) = ((D.nb i)⁻¹ * u (D.nb i)) * r := by
    have h1 : (D.nb i)⁻¹ * u (D.nb i) * r = r * ((D.nb i)⁻¹ * u (D.nb i)) := by
      calc (D.nb i)⁻¹ * u (D.nb i) * r
          = ((D.nb i)⁻¹ * u (D.nb i) * r * ((D.nb i)⁻¹ * u (D.nb i))⁻¹) *
              (D.nb i)⁻¹ * u (D.nb i) := by group
        _ = r * ((D.nb i)⁻¹ * u (D.nb i)) := by rw [key]; group
    exact h1.symm
  rw [← hrv, MulAut.conj_apply, hcomm']
  group

private theorem ggL45E67_THat_abelian {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) (hD : D.Good) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) (hcard : Nat.card S.π.ker = 1 ∨ Nat.card S.π.ker = 3) :
    ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x := by
  obtain ⟨hTab, -, -⟩ := hD.torus
  obtain ⟨hab, -, -⟩ := ggAbelianLift K R S.π S.surj S.ker_eq.le hcard D.Tor (Set.range S.w)
    hTab (ggL45E67_lift_normalizes D hD S.w_spec) S.noInvFunc S.noInvAlt
    (⊥ : Subgroup (MulAut K)) IsPGroup.of_bot
    (by intro a ha; rw [Subgroup.mem_bot] at ha; subst ha; intro l hl; rfl)
    (by intro a ha; rw [Subgroup.mem_bot] at ha; subst ha; intro n hn; simpa using D.Tor.one_mem)
  exact hab

private theorem ggL45E67_fix3 {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) (hD : D.Good) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) {I : Set (MulAut R)}
    (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I) {E : Subgroup (MulAut K)}
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ t ∈ D.Tor, u t = t)
    (hWeylI : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ i, (D.nb i)⁻¹ * u (D.nb i) ∈ D.Tor)
    (hcard : Nat.card S.π.ker = 1 ∨ Nat.card S.π.ker = 3) :
    ∀ a : MulAut K, GGL45IsPElt 3 a → ggInducedAut θ a ∈ I →
      (∀ e ∈ E, a * e = e * a) → ∀ x ∈ ggL45E67_THat D S.π, a x = x := by
  obtain ⟨J, hJ⟩ := hI
  have hIJ : ∀ u : MulAut R, u ∈ I ↔ u ∈ J := fun u => by rw [← hJ]; rfl
  obtain ⟨hTab, -, -⟩ := hD.torus
  intro a ha3 haI haE x hx
  have hAp : IsPGroup 3 (Subgroup.zpowers a) := ggL45E67_isPGroup_zpowers ha3
  have haJ : ggInducedAut θ a ∈ J := (hIJ _).mp haI
  have hfixT : ∀ b ∈ Subgroup.zpowers a, ∀ l : K, S.π l ∈ D.Tor → S.π (b l) = S.π l := by
    intro b hb l hl
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbI : ggInducedAut θ b ∈ I := by
      rw [← hn, map_zpow]
      exact (hIJ _).mpr (J.zpow_mem haJ n)
    have hbcomm : ∀ e ∈ E, ggInducedAut θ b * ggInducedAut θ e =
        ggInducedAut θ e * ggInducedAut θ b := by
      intro e he
      have hcommE : ggInducedAut θ a * ggInducedAut θ e =
          ggInducedAut θ e * ggInducedAut θ a := by
        rw [← map_mul, ← map_mul, haE e he]
      rw [← hn, map_zpow]
      exact (Commute.zpow_left (m := n) hcommE).eq
    rw [← S.inducedAut b l]
    exact hC _ hbI hbcomm _ hl
  have hAN : ∀ b ∈ Subgroup.zpowers a, ∀ n ∈ Set.range S.w, S.π (n⁻¹ * b n) ∈ D.Tor := by
    intro b hb n hn
    obtain ⟨i, rfl⟩ := hn
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbI : ggInducedAut θ b ∈ I := by
      rw [← hm, map_zpow]
      exact (hIJ _).mpr (J.zpow_mem haJ m)
    have hbcomm : ∀ e ∈ E, ggInducedAut θ b * ggInducedAut θ e =
        ggInducedAut θ e * ggInducedAut θ b := by
      intro e he
      have hcommE : ggInducedAut θ a * ggInducedAut θ e =
          ggInducedAut θ e * ggInducedAut θ a := by
        rw [← map_mul, ← map_mul, haE e he]
      rw [← hm, map_zpow]
      exact (Commute.zpow_left (m := m) hcommE).eq
    have h := hWeylI _ hbI hbcomm i
    have hπ' : S.π ((S.w i)⁻¹ * b (S.w i)) =
        (S.π (S.w i))⁻¹ * ggInducedAut θ b (S.π (S.w i)) := by
      rw [map_mul, map_inv, ← S.inducedAut b (S.w i)]
    rw [hπ', S.w_spec i]
    exact h
  obtain ⟨-, hfix, -⟩ := ggAbelianLift K R S.π S.surj S.ker_eq.le hcard D.Tor (Set.range S.w)
    hTab (ggL45E67_lift_normalizes D hD S.w_spec) S.noInvFunc S.noInvAlt
    (Subgroup.zpowers a) hAp hfixT hAN
  exact hfix a (Subgroup.mem_zpowers a) x hx

private theorem ggL45E67_S_mem_THat {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R)
    {S : QuotFrame R D K θ} {E : Subgroup (MulAut K)}
    (hCR : ∀ r : R, (∀ e ∈ E, ggInducedAut θ e r = r) → r ∈ D.Tor) :
    ∀ x : K, GGL45InS 3 E x → x ∈ ggL45E67_THat D S.π := by
  rintro x ⟨⟨k, hk⟩, hfix⟩
  rw [ggL45E67_mem_THat]
  exact hCR (S.π x) (fun e he => by rw [S.inducedAut, hfix e he])

private theorem ggL45E67_S_exp_center {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R)
    {S : QuotFrame R D K θ} {E : Subgroup (MulAut K)} {s : ℕ}
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 → t ^ 3 ^ s = 1)
    (hS_mem : ∀ x : K, GGL45InS 3 E x → x ∈ ggL45E67_THat D S.π) :
    ∀ h : K, GGL45InS 3 E h → h ^ 3 ^ s ∈ Subgroup.center K := by
  intro h hh
  have hmem := hS_mem h hh
  obtain ⟨⟨k, hk⟩, -⟩ := hh
  have h1 := hStep3 (S.π h) hmem k (by rw [← map_pow, hk, map_one])
  rw [← S.ker_eq, MonoidHom.mem_ker, map_pow]
  exact h1

private theorem ggL45E67_S_psi_center {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K}
    {c : ℤ} {S : QuotFrame R D K θ} {E : Subgroup (MulAut K)}
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 → ggInducedAut θ ψ t = t ^ c)
    (hS_mem : ∀ x : K, GGL45InS 3 E x → x ∈ ggL45E67_THat D S.π) :
    ∀ h : K, GGL45InS 3 E h → ψ h * (h ^ c)⁻¹ ∈ Subgroup.center K := by
  intro h hh
  have hmem := hS_mem h hh
  obtain ⟨⟨k, hk⟩, -⟩ := hh
  have h1 := hStep3 (S.π h) hmem k (by rw [← map_pow, hk, map_one])
  rw [← S.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ← S.inducedAut ψ h, h1,
    mul_inv_cancel]

private theorem ggL45E67_one_le_s {R : Type} [Group R] (D : E6ThreeModel.FrameData R) {s : ℕ}
    (hH3 : ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    1 ≤ s := by
  obtain ⟨t₁, -, t₂, -, h1, -, hind⟩ := hH3
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have h := hind 1 0 (by simpa using h1)
    exact absurd h.1 (by norm_num)
  · exact hs

private theorem ggL45E67_exp_center {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) {v N s : ℕ}
    (hpowT : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ v = 1)
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 → t ^ 3 ^ s = 1) :
    ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ s ∈ Subgroup.center K := by
  intro x
  have hv : (S.π ((x : K) ^ N)) ^ 3 ^ v = 1 := by rw [← map_pow, hpowT x, map_one]
  have h1 := hStep3 (S.π ((x : K) ^ N))
    (by rw [map_pow]; exact D.Tor.pow_mem x.2 N) v hv
  rw [← S.ker_eq, MonoidHom.mem_ker, map_pow]
  exact h1

private theorem ggL45E67_psi_center {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) {ψ : MulAut K} {c : ℤ} {v N : ℕ}
    (hpowT : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ v = 1)
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 → ggInducedAut θ ψ t = t ^ c) :
    ∀ x : ↥(ggL45E67_THat D S.π),
      ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K := by
  intro x
  have hv : (S.π ((x : K) ^ N)) ^ 3 ^ v = 1 := by rw [← map_pow, hpowT x, map_one]
  have h1 := hStep3 (S.π ((x : K) ^ N))
    (by rw [map_pow]; exact D.Tor.pow_mem x.2 N) v hv
  rw [← S.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ← S.inducedAut ψ ((x : K) ^ N),
    h1, mul_inv_cancel]

private theorem ggL45E67_functional_trivial {R : Type} {K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) (π : K →* R) (hπ : Function.Surjective π)
    (w : Fin 6 → K)
    (hF : GGNoInvFunc π (Set.range w) D.Tor)
    (φ : ↥(ggL45E67_THat D π) →* Multiplicative (ZMod 3))
    (hφker : ∀ x : ↥(ggL45E67_THat D π), π (x : K) = 1 → φ x = 1)
    (hφN : ∀ (i : Fin 6) (x : ↥(ggL45E67_THat D π)),
      ∀ hx : w i * (x : K) * (w i)⁻¹ ∈ ggL45E67_THat D π,
      φ ⟨w i * (x : K) * (w i)⁻¹, hx⟩ = φ x) :
    ∀ x : ↥(ggL45E67_THat D π), φ x = 1 := by
  haveI : Finite ↥(ggL45E67_THat D π) := Subtype.finite
  haveI : Nonempty ↥(ggL45E67_THat D π) := ⟨1⟩
  intro x₀
  obtain ⟨v, N, hN3, hTcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := ↥(ggL45E67_THat D π))).ne' 3
      (by norm_num)
  have hNcop : Nat.Coprime N 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3).symm
  have hpowT : ∀ x : ↥(ggL45E67_THat D π), ((x : K) ^ N) ^ 3 ^ v = 1 :=
    ggL45E67_pow_N_isPElt D hTcard
  have hfib : ∀ (x y : K), ∀ (hx : x ∈ ggL45E67_THat D π) (hy : y ∈ ggL45E67_THat D π),
      π x = π y → φ ⟨x, hx⟩ = φ ⟨y, hy⟩ := by
    intro x y hx hy hxy
    have hmem : x * y⁻¹ ∈ ggL45E67_THat D π := by
      rw [ggL45E67_mem_THat, map_mul, map_inv, hxy, mul_inv_cancel]
      exact D.Tor.one_mem
    have hz : φ ⟨x * y⁻¹, hmem⟩ = 1 := by
      apply hφker
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hxeq : (⟨x, hx⟩ : ↥(ggL45E67_THat D π)) = ⟨x * y⁻¹, hmem⟩ * ⟨y, hy⟩ := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      group
    rw [hxeq, map_mul, hz, one_mul]
  let s : R → K := Function.surjInv hπ
  have hs : ∀ r : R, π (s r) = r := fun r => Function.surjInv_eq hπ r
  have hsT : ∀ r : R, r ∈ D.Tor → s r ∈ ggL45E67_THat D π := by
    intro r hr
    rw [ggL45E67_mem_THat, hs]
    exact hr
  let G : ↥D.Tor →* Multiplicative (ZMod 3) :=
    MonoidHom.mk' (fun t => φ ⟨s (t : R), hsT _ t.2⟩) (by
      intro a b
      have hmem : s (a : R) * s (b : R) ∈ ggL45E67_THat D π := by
        rw [ggL45E67_mem_THat, map_mul, hs, hs]
        exact D.Tor.mul_mem a.2 b.2
      have h1 : φ ⟨s ((a * b : ↥D.Tor) : R), hsT _ (a * b).2⟩
          = φ ⟨s (a : R) * s (b : R), hmem⟩ := by
        apply hfib
        rw [hs, map_mul, hs, hs, Subgroup.coe_mul]
      have h2 : (⟨s (a : R) * s (b : R), hmem⟩ : ↥(ggL45E67_THat D π))
          = ⟨s (a : R), hsT _ a.2⟩ * ⟨s (b : R), hsT _ b.2⟩ := rfl
      rw [h1, h2]
      exact map_mul φ _ _)
  have hG_apply : ∀ (x : K) (hx : x ∈ ggL45E67_THat D π), G ⟨π x, hx⟩ = φ ⟨x, hx⟩ := by
    intro x hx
    exact hfib _ _ _ _ (by rw [hs])
  have hGinv : ∀ n ∈ Set.range w, ∀ t t' : ↥D.Tor,
      (t' : R) = π n * (t : R) * (π n)⁻¹ → G t' = G t := by
    rintro _ ⟨i, rfl⟩ t t' ht'
    have hxT : s (t : R) ∈ ggL45E67_THat D π := hsT _ t.2
    have hmem : w i * s (t : R) * (w i)⁻¹ ∈ ggL45E67_THat D π := by
      rw [ggL45E67_mem_THat, map_mul, map_mul, map_inv, hs, ← ht']
      exact t'.2
    calc G t' = φ ⟨s (t' : R), hsT _ t'.2⟩ := rfl
      _ = φ ⟨w i * s (t : R) * (w i)⁻¹, hmem⟩ := by
          apply hfib
          rw [hs, map_mul, map_mul, map_inv, hs, ← ht']
      _ = φ ⟨s (t : R), hxT⟩ := hφN i ⟨s (t : R), hxT⟩ hmem
      _ = G t := rfl
  have hG1 : G = 1 := hF G hGinv
  calc φ x₀ = G ⟨π (x₀ : K), x₀.2⟩ := (hG_apply _ x₀.2).symm
    _ = 1 := by rw [hG1]; rfl

private noncomputable def ggL45E67_centerEquiv {K : Type*} [Group K]
    (h3 : Nat.card (Subgroup.center K) = 3) : ↥(Subgroup.center K) ≃* Multiplicative (ZMod 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥(Subgroup.center K) := isCyclic_of_prime_card h3
  have hcardZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact mulEquivOfCyclicCardEq (by rw [h3, hcardZ3])

private theorem ggL45E67_eq_one_of_ker_card_one {R K : Type} [Group R] [Group K] {π : K →* R}
    (hker : π.ker = Subgroup.center K) (h1 : Nat.card π.ker = 1) {z : K}
    (hz : z ∈ Subgroup.center K) : z = 1 := by
  have hbot : Subgroup.center K = ⊥ := by
    rw [← hker]
    exact Subgroup.card_eq_one.mp h1
  rw [hbot, Subgroup.mem_bot] at hz
  exact hz

private theorem ggL45E67_H2_exp {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R} (S : QuotFrame R D K θ)
    {s N : ℕ}
    (eZ : ↥(Subgroup.center K) ≃* Multiplicative (ZMod 3)) (hN : Nat.Coprime N 3) (hs1 : 1 ≤ s)
    (hcenter3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
    (hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x)
    (hExpCenter : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ s ∈ Subgroup.center K)
    {h : K} (hSh : h ∈ ggL45E67_THat D S.π) (hcent : h ^ 3 ^ s ∈ Subgroup.center K) :
    h ^ 3 ^ s = 1 := by
  let φ₁ : ↥(ggL45E67_THat D S.π) →* Multiplicative (ZMod 3) :=
    { toFun := fun x => eZ ⟨((x : K) ^ N) ^ 3 ^ s, hExpCenter x⟩
      map_one' := by
        exact (congrArg eZ (Subtype.ext (by simp))).trans (map_one eZ)
      map_mul' := by
        intro x y
        rw [← map_mul eZ]
        refine congrArg eZ (Subtype.ext ?_)
        show (((x : K) * (y : K)) ^ N) ^ 3 ^ s
          = (((x : K) ^ N) ^ 3 ^ s) * (((y : K) ^ N) ^ 3 ^ s)
        have hXY : Commute ((x : K) ^ N) ((y : K) ^ N) :=
          Commute.pow_pow ((commute_iff_eq _ _).mpr (hTabT (x : K) x.2 (y : K) y.2)) N N
        rw [Commute.mul_pow ((commute_iff_eq _ _).mpr (hTabT (x : K) x.2 (y : K) y.2)) N,
          Commute.mul_pow hXY (3 ^ s)] }
  have hφ₁ker : ∀ x : ↥(ggL45E67_THat D S.π), S.π (x : K) = 1 → φ₁ x = 1 := by
    intro x hx
    have hxZ : (x : K) ∈ Subgroup.center K := by
      rw [← S.ker_eq, MonoidHom.mem_ker]; exact hx
    have hx3 : (x : K) ^ 3 = 1 := hcenter3 _ hxZ
    have hx1 : ((x : K) ^ N) ^ 3 ^ s = 1 := by
      have h3dvd : (3 : ℕ) ∣ N * 3 ^ s := by
        have h : (3 : ℕ) ∣ 3 ^ s := pow_dvd_pow 3 (by omega)
        simpa [mul_comm] using dvd_mul_of_dvd_right h N
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_iff_pow_eq_one.mpr hx3).trans h3dvd)
    have h2 : (⟨((x : K) ^ N) ^ 3 ^ s, hExpCenter x⟩ : ↥(Subgroup.center K)) = 1 :=
      Subtype.ext hx1
    exact (congrArg eZ h2).trans (map_one eZ)
  have hφ₁N : ∀ (i : Fin 6) (x : ↥(ggL45E67_THat D S.π)),
      ∀ hx : S.w i * (x : K) * (S.w i)⁻¹ ∈ ggL45E67_THat D S.π,
      φ₁ ⟨S.w i * (x : K) * (S.w i)⁻¹, hx⟩ = φ₁ x := by
    intro i x hx
    have hconj : ((S.w i * (x : K) * (S.w i)⁻¹) ^ N) = S.w i * ((x : K) ^ N) * (S.w i)⁻¹ := by
      rw [conj_pow]
    have hcen : ((x : K) ^ N) ^ 3 ^ s ∈ Subgroup.center K := hExpCenter x
    have hfix : (S.w i * ((x : K) ^ N) * (S.w i)⁻¹) ^ 3 ^ s = ((x : K) ^ N) ^ 3 ^ s := by
      rw [conj_pow]
      have h := Subgroup.mem_center_iff.mp hcen (S.w i)
      rw [h]
      group
    have hgoal : (⟨((S.w i * (x : K) * (S.w i)⁻¹) ^ N) ^ 3 ^ s,
        hExpCenter ⟨S.w i * (x : K) * (S.w i)⁻¹, hx⟩⟩ : ↥(Subgroup.center K))
        = ⟨((x : K) ^ N) ^ 3 ^ s, hExpCenter x⟩ := by
      apply Subtype.ext
      show ((S.w i * (x : K) * (S.w i)⁻¹) ^ N) ^ 3 ^ s = ((x : K) ^ N) ^ 3 ^ s
      rw [hconj, hfix]
    exact congrArg eZ hgoal
  have hφ₁ := ggL45E67_functional_trivial D S.π S.surj S.w S.noInvFunc φ₁ hφ₁ker hφ₁N
  have h1 : ((h : K) ^ N) ^ 3 ^ s = 1 := by
    have h2 : eZ ⟨((h : K) ^ N) ^ 3 ^ s, hExpCenter ⟨h, hSh⟩⟩ = 1 := hφ₁ ⟨h, hSh⟩
    have h3 : (⟨((h : K) ^ N) ^ 3 ^ s, hExpCenter ⟨h, hSh⟩⟩ :
        ↥(Subgroup.center K)) = 1 :=
      eZ.injective (h2.trans (map_one eZ).symm)
    exact congrArg Subtype.val h3
  have hzN : (h ^ 3 ^ s) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact h1
  exact ggL45E67_eq_one_of_pow_eq_one hcenter3 hN hcent hzN

private theorem ggL45E67_psi_hom_mul {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) {ψ : MulAut K} {c : ℤ} {N : ℕ}
    (hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x)
    (hPsiCenter : ∀ x : ↥(ggL45E67_THat D S.π),
      ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K)
    (x y : ↥(ggL45E67_THat D S.π)) :
    ψ (((x : K) * (y : K)) ^ N) * ((((x : K) * (y : K)) ^ N) ^ c)⁻¹
      = (ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹) *
        (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹) := by
  have hXY : Commute ((x : K) ^ N) ((y : K) ^ N) :=
    Commute.pow_pow ((commute_iff_eq _ _).mpr (hTabT (x : K) x.2 (y : K) y.2)) N N
  have hBD : ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K := hPsiCenter y
  have hcomm : (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹) * (((x : K) ^ N) ^ c)⁻¹
      = (((x : K) ^ N) ^ c)⁻¹ * (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹) :=
    (Subgroup.mem_center_iff.mp hBD (((x : K) ^ N) ^ c)⁻¹).symm
  rw [Commute.mul_pow ((commute_iff_eq _ _).mpr (hTabT (x : K) x.2 (y : K) y.2)) N,
    map_mul, Commute.mul_zpow hXY c, mul_inv_rev]
  calc ψ ((x : K) ^ N) * ψ ((y : K) ^ N) *
        ((((y : K) ^ N) ^ c)⁻¹ * (((x : K) ^ N) ^ c)⁻¹)
      = ψ ((x : K) ^ N) * (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹) *
          (((x : K) ^ N) ^ c)⁻¹ := by group
    _ = ψ ((x : K) ^ N) * ((((x : K) ^ N) ^ c)⁻¹ *
          (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹)) := by
          rw [mul_assoc, hcomm]
    _ = ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ *
          (ψ ((y : K) ^ N) * (((y : K) ^ N) ^ c)⁻¹) := by group

private theorem ggL45E67_psi_hom_conj {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R}
    (S : QuotFrame R D K θ) {ψ : MulAut K} {s : ℕ} {c : ℤ} {v N : ℕ}
    (hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x)
    (hpowT : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ v = 1)
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 →
      t ^ 3 ^ s = 1 ∧ ggInducedAut θ ψ t = t ^ c)
    (hWeylψ : ∀ i, (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) ∈ D.Tor)
    (hPsiCenter : ∀ x : ↥(ggL45E67_THat D S.π),
      ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K)
    (i : Fin 6) (x : ↥(ggL45E67_THat D S.π)) :
    ψ ((S.w i * (x : K) * (S.w i)⁻¹) ^ N) *
        (((S.w i * (x : K) * (S.w i)⁻¹) ^ N) ^ c)⁻¹
      = ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ := by
  have hconj : ((S.w i * (x : K) * (S.w i)⁻¹) ^ N) = S.w i * ((x : K) ^ N) * (S.w i)⁻¹ := by
    rw [conj_pow]
  have hψzT : ψ ((x : K) ^ N) ∈ ggL45E67_THat D S.π := by
    rw [ggL45E67_mem_THat, ← S.inducedAut ψ ((x : K) ^ N),
      (hStep3 (S.π ((x : K) ^ N))
        (by rw [map_pow]; exact D.Tor.pow_mem x.2 N) v
        (by rw [← map_pow, hpowT x, map_one])).2]
    exact D.Tor.zpow_mem (by rw [map_pow]; exact D.Tor.pow_mem x.2 N) c
  have hmT : (S.w i)⁻¹ * ψ (S.w i) ∈ ggL45E67_THat D S.π := by
    rw [ggL45E67_mem_THat, map_mul, map_inv, S.w_spec i, ← S.inducedAut ψ (S.w i), S.w_spec i]
    exact hWeylψ i
  have hψw : ψ (S.w i) = S.w i * ((S.w i)⁻¹ * ψ (S.w i)) := by group
  have hmψz : Commute ((S.w i)⁻¹ * ψ (S.w i)) (ψ ((x : K) ^ N)) :=
    (commute_iff_eq _ _).mpr (hTabT _ hmT _ hψzT)
  have hmz : (S.w i)⁻¹ * ψ (S.w i) * ψ ((x : K) ^ N) * ((S.w i)⁻¹ * ψ (S.w i))⁻¹
      = ψ ((x : K) ^ N) := by
    rw [hmψz.eq]
    group
  have h1 : ψ (S.w i * ((x : K) ^ N) * (S.w i)⁻¹) =
      S.w i * ψ ((x : K) ^ N) * (S.w i)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hψw, mul_inv_rev]
    calc S.w i * ((S.w i)⁻¹ * ψ (S.w i)) * ψ ((x : K) ^ N) *
          (((S.w i)⁻¹ * ψ (S.w i))⁻¹ * (S.w i)⁻¹)
        = S.w i * ((S.w i)⁻¹ * ψ (S.w i) * ψ ((x : K) ^ N) *
            ((S.w i)⁻¹ * ψ (S.w i))⁻¹) * (S.w i)⁻¹ := by group
      _ = S.w i * ψ ((x : K) ^ N) * (S.w i)⁻¹ := by rw [hmz]
  have h2 : (S.w i * ((x : K) ^ N) * (S.w i)⁻¹) ^ c =
      S.w i * (((x : K) ^ N) ^ c) * (S.w i)⁻¹ := conj_zpow
  rw [hconj, h1, h2]
  have h3 : (S.w i * (((x : K) ^ N) ^ c) * (S.w i)⁻¹)⁻¹
      = S.w i * ((((x : K) ^ N) ^ c)⁻¹) * (S.w i)⁻¹ := by group
  rw [h3]
  calc S.w i * ψ ((x : K) ^ N) * (S.w i)⁻¹ *
        (S.w i * (((x : K) ^ N) ^ c)⁻¹ * (S.w i)⁻¹)
      = S.w i * (ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹) * (S.w i)⁻¹ := by group
    _ = ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ := by
        rw [Subgroup.mem_center_iff.mp (hPsiCenter x) (S.w i)]
        group

private theorem ggL45E67_psi_pow_key {K : Type*} [Group K] {ψ : MulAut K} {c : ℤ} {N : ℕ}
    {h : K} (hcent : ψ h * (h ^ c)⁻¹ ∈ Subgroup.center K) :
    ψ (h ^ N) * ((h ^ N) ^ c)⁻¹ = (ψ h * (h ^ c)⁻¹) ^ N := by
  have hcomm : Commute (ψ h * (h ^ c)⁻¹) (h ^ c) :=
    (commute_iff_eq _ _).mpr ((Subgroup.mem_center_iff.mp hcent (h ^ c)).symm)
  have h1 : (h ^ c) ^ N = h ^ (c * (N : ℤ)) := by
    rw [← zpow_natCast (h ^ c) N, ← zpow_mul]
  have h2 : (h ^ N) ^ c = h ^ ((N : ℤ) * c) := by
    rw [← zpow_natCast h N, ← zpow_mul]
  have hψh : ψ h = (ψ h * (h ^ c)⁻¹) * (h ^ c) := by group
  calc ψ (h ^ N) * ((h ^ N) ^ c)⁻¹
      = (ψ h) ^ N * ((h ^ N) ^ c)⁻¹ := by rw [map_pow]
    _ = ((ψ h * (h ^ c)⁻¹) * (h ^ c)) ^ N * ((h ^ N) ^ c)⁻¹ :=
          congrArg (fun x : K => x ^ N * ((h ^ N) ^ c)⁻¹) hψh
    _ = ((ψ h * (h ^ c)⁻¹) ^ N * (h ^ c) ^ N) * ((h ^ N) ^ c)⁻¹ := by
          rw [Commute.mul_pow hcomm]
    _ = ((ψ h * (h ^ c)⁻¹) ^ N * h ^ (c * (N : ℤ))) * (h ^ ((N : ℤ) * c))⁻¹ := by
          rw [h1, h2]
    _ = (ψ h * (h ^ c)⁻¹) ^ N := by
          rw [mul_comm (N : ℤ) c, mul_assoc, mul_inv_cancel, mul_one]

private theorem ggL45E67_H2_psi {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R} (S : QuotFrame R D K θ)
    {ψ : MulAut K} {s : ℕ} {c : ℤ} {v N : ℕ}
    (eZ : ↥(Subgroup.center K) ≃* Multiplicative (ZMod 3)) (hψ : ψ ^ 3 = 1)
    (hc : c ≡ 1 [ZMOD 3]) (hZ : Nat.card (Subgroup.center K) ∣ 3) (hN : Nat.Coprime N 3)
    (hcenter3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
    (hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x)
    (hpowT : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ v = 1)
    (hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 →
      t ^ 3 ^ s = 1 ∧ ggInducedAut θ ψ t = t ^ c)
    (hWeylψ : ∀ i, (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) ∈ D.Tor)
    (hPsiCenter : ∀ x : ↥(ggL45E67_THat D S.π),
      ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K)
    {h : K} (hSh : h ∈ ggL45E67_THat D S.π)
    (hcent : ψ h * (h ^ c)⁻¹ ∈ Subgroup.center K) : ψ h = h ^ c := by
  let φ₂ : ↥(ggL45E67_THat D S.π) →* Multiplicative (ZMod 3) :=
    { toFun := fun x => eZ ⟨ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹, hPsiCenter x⟩
      map_one' := by
        exact (congrArg eZ (Subtype.ext (by simp))).trans (map_one eZ)
      map_mul' := by
        intro x y
        rw [← map_mul eZ]
        refine congrArg eZ (Subtype.ext ?_)
        exact ggL45E67_psi_hom_mul D S hTabT hPsiCenter x y }
  have hφ₂ker : ∀ x : ↥(ggL45E67_THat D S.π), S.π (x : K) = 1 → φ₂ x = 1 := by
    intro x hx
    have hxZ : (x : K) ∈ Subgroup.center K := by
      rw [← S.ker_eq, MonoidHom.mem_ker]; exact hx
    have hx3 : (x : K) ^ 3 = 1 := hcenter3 _ hxZ
    have hψx : ψ (x : K) = x := ggL45E67_aut_fixes_center hZ hψ (x : K) hxZ
    have hxN3 : ((x : K) ^ N) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    have hval : ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ = 1 := by
      rw [map_pow, hψx, ggL45E67_zpow_eq_self hxN3 hc, mul_inv_cancel]
    have h2 : (⟨ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹, hPsiCenter x⟩ :
        ↥(Subgroup.center K)) = 1 := Subtype.ext hval
    exact (congrArg eZ h2).trans (map_one eZ)
  have hφ₂N : ∀ (i : Fin 6) (x : ↥(ggL45E67_THat D S.π)),
      ∀ hx : S.w i * (x : K) * (S.w i)⁻¹ ∈ ggL45E67_THat D S.π,
      φ₂ ⟨S.w i * (x : K) * (S.w i)⁻¹, hx⟩ = φ₂ x := by
    intro i x hx
    have hgoal : (⟨ψ ((S.w i * (x : K) * (S.w i)⁻¹) ^ N) *
        (((S.w i * (x : K) * (S.w i)⁻¹) ^ N) ^ c)⁻¹,
        hPsiCenter ⟨S.w i * (x : K) * (S.w i)⁻¹, hx⟩⟩ : ↥(Subgroup.center K))
        = ⟨ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹, hPsiCenter x⟩ :=
      Subtype.ext (ggL45E67_psi_hom_conj D S hTabT hpowT hStep3 hWeylψ hPsiCenter i x)
    exact congrArg eZ hgoal
  have hφ₂ := ggL45E67_functional_trivial D S.π S.surj S.w S.noInvFunc φ₂ hφ₂ker hφ₂N
  have hφ₂h : φ₂ ⟨h, hSh⟩ = 1 := hφ₂ _
  have hkey := ggL45E67_psi_pow_key (ψ := ψ) (c := c) (N := N) hcent
  have hwN : (ψ h * (h ^ c)⁻¹) ^ N = 1 := by
    have h1 : (⟨ψ (h ^ N) * ((h ^ N) ^ c)⁻¹, hPsiCenter ⟨h, hSh⟩⟩ :
        ↥(Subgroup.center K)) = 1 := by
      refine eZ.injective ?_
      exact hφ₂h.trans (map_one eZ).symm
    have h2 : ψ (h ^ N) * ((h ^ N) ^ c)⁻¹ = 1 := congrArg Subtype.val h1
    rw [← hkey]
    exact h2
  exact mul_inv_eq_one.mp (ggL45E67_eq_one_of_pow_eq_one hcenter3 hN hcent hwN)

private theorem ggL45E67_H2_fix {R K : Type} [Group R] [Group K] [Finite K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R} (S : QuotFrame R D K θ)
    {I : Set (MulAut R)}
    (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I) (hK : commutator K = ⊤)
    {E : Subgroup (MulAut K)}
    (hFix3 : ∀ a : MulAut K, GGL45IsPElt 3 a → ggInducedAut θ a ∈ I →
      (∀ e ∈ E, a * e = e * a) → ∀ x ∈ ggL45E67_THat D S.π, a x = x)
    (h3' : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      Nat.Coprime 3 (orderOf u) → ∃ t ∈ D.Tor, u = MulAut.conj t)
    (hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x)
    (hS_mem : ∀ x : K, GGL45InS 3 E x → x ∈ ggL45E67_THat D S.π) :
    ∀ α : MulAut K, GGL45InducesIn θ I α → (∀ e ∈ E, α * e = e * α) →
      ∀ h : K, GGL45InS 3 E h → α h = h := by
  obtain ⟨J, hJ⟩ := hI
  have hIJ : ∀ u : MulAut R, u ∈ I ↔ u ∈ J := fun u => by rw [← hJ]; rfl
  intro α hα hαE h hh
  have hhT : h ∈ ggL45E67_THat D S.π := hS_mem h hh
  have hαI : ggInducedAut θ α ∈ I := (ggL45_inducesIn_iff θ I α).mp hα
  have hαJ : ggInducedAut θ α ∈ J := (hIJ _).mp hαI
  have hpowI : ∀ (β : MulAut K) (n : ℤ), β = α ^ n → ggInducedAut θ β ∈ I := by
    intro β n hn
    rw [hn, map_zpow]
    exact (hIJ _).mpr (J.zpow_mem hαJ n)
  have hpowE : ∀ (β : MulAut K) (n : ℤ), β = α ^ n → ∀ e ∈ E, β * e = e * β := by
    intro β n hn e he
    rw [hn]
    exact (Commute.zpow_left (m := n) (hαE e he)).eq
  obtain ⟨n₃, hn₃⟩ := Subgroup.mem_zpowers_iff.mp (TauCeti.pPart_mem_zpowers 3 α)
  have hfix3 : ∀ x ∈ ggL45E67_THat D S.π, TauCeti.pPart 3 α x = x :=
    hFix3 _ (ggL45E67_isPElt_pPart α) (hpowI _ n₃ hn₃.symm) (hpowE _ n₃ hn₃.symm)
  obtain ⟨n₃', hn₃'⟩ := Subgroup.mem_zpowers_iff.mp (TauCeti.pFreePart_mem_zpowers 3 α)
  have h3'I : ggInducedAut θ (TauCeti.pFreePart 3 α) ∈ I := hpowI _ n₃' hn₃'.symm
  have h3'E : ∀ e ∈ E, TauCeti.pFreePart 3 α * e = e * TauCeti.pFreePart 3 α :=
    hpowE _ n₃' hn₃'.symm
  have h3'cop : Nat.Coprime 3 (orderOf (ggInducedAut θ (TauCeti.pFreePart 3 α))) := by
    have hdvd : orderOf (ggInducedAut θ (TauCeti.pFreePart 3 α)) ∣
        orderOf (TauCeti.pFreePart 3 α) := orderOf_map_dvd (ggInducedAut θ) _
    have hnd : ¬ 3 ∣ orderOf (TauCeti.pFreePart 3 α) :=
      TauCeti.not_dvd_orderOf_pFreePart (p := 3) Nat.prime_three (orderOf_pos α).ne'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => hnd (h.trans hdvd))
  have h3'E' : ∀ e ∈ E, ggInducedAut θ (TauCeti.pFreePart 3 α) * ggInducedAut θ e =
      ggInducedAut θ e * ggInducedAut θ (TauCeti.pFreePart 3 α) := by
    intro e he
    rw [← map_mul, ← map_mul, h3'E e he]
  obtain ⟨t, htT, htconj⟩ := h3' _ h3'I h3'E' h3'cop
  obtain ⟨tLift, htLift⟩ : ∃ tLift : K, S.π tLift = t := S.surj t
  have htLiftT : tLift ∈ ggL45E67_THat D S.π := by
    rw [ggL45E67_mem_THat, htLift]; exact htT
  have hinner : TauCeti.pFreePart 3 α = MulAut.conj tLift := by
    apply ggInducedAut_injective_of_perfect hK θ
    rw [ggL45E67_inducedAut_conj, ← S.π_apply tLift, htLift, htconj]
  have hfix3' : ∀ x ∈ ggL45E67_THat D S.π, TauCeti.pFreePart 3 α x = x := by
    intro x hx
    rw [hinner, MulAut.conj_apply, hTabT tLift htLiftT x hx]
    group
  calc α h = (TauCeti.pPart 3 α * TauCeti.pFreePart 3 α) h := by
        rw [TauCeti.pPart_mul_pFreePart]
    _ = TauCeti.pPart 3 α (TauCeti.pFreePart 3 α h) := rfl
    _ = TauCeti.pPart 3 α h := by rw [hfix3' h hhT]
    _ = h := hfix3 h hhT

private theorem ggL45E67_H3 {R K : Type} [Group R] [Group K]
    (D : E6ThreeModel.FrameData R) {θ : K ⧸ Subgroup.center K ≃* R} (S : QuotFrame R D K θ)
    {I : Set (MulAut R)}
    {E : Subgroup (MulAut K)} {s : ℕ} (hE : IsElemAbelian 3 E)
    (hEI : ∀ e ∈ E, GGL45InducesIn θ I e)
    (hcenter3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1)
    (hFix3 : ∀ a : MulAut K, GGL45IsPElt 3 a → ggInducedAut θ a ∈ I →
      (∀ e ∈ E, a * e = e * a) → ∀ x ∈ ggL45E67_THat D S.π, a x = x)
    (hH3 : ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    GGL45HThree 3 E s := by
  obtain ⟨t₁, ht₁, t₂, ht₂, ht₁pow, ht₂pow, hind⟩ := hH3
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : K, S.π x₁ = t₁ := S.surj t₁
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : K, S.π x₂ = t₂ := S.surj t₂
  have hx₁T : x₁ ∈ ggL45E67_THat D S.π := by rw [ggL45E67_mem_THat, hx₁]; exact ht₁
  have hx₂T : x₂ ∈ ggL45E67_THat D S.π := by rw [ggL45E67_mem_THat, hx₂]; exact ht₂
  have hx₁cent : x₁ ^ 3 ^ s ∈ Subgroup.center K := by
    rw [← S.ker_eq, MonoidHom.mem_ker, map_pow, hx₁]
    exact ht₁pow
  have hx₂cent : x₂ ^ 3 ^ s ∈ Subgroup.center K := by
    rw [← S.ker_eq, MonoidHom.mem_ker, map_pow, hx₂]
    exact ht₂pow
  have hx₁3 : x₁ ^ 3 ^ (s + 1) = 1 := by
    rw [pow_succ, pow_mul]
    exact hcenter3 _ hx₁cent
  have hx₂3 : x₂ ^ 3 ^ (s + 1) = 1 := by
    rw [pow_succ, pow_mul]
    exact hcenter3 _ hx₂cent
  have hx₁fix : ∀ e ∈ E, e x₁ = x₁ := fun e he =>
    hFix3 e (ggL45E67_isElemAbelian_isPElt hE e he)
      ((ggL45_inducesIn_iff θ I e).mp (hEI e he)) (ggL45E67_isElemAbelian_comm hE e he) x₁ hx₁T
  have hx₂fix : ∀ e ∈ E, e x₂ = x₂ := fun e he =>
    hFix3 e (ggL45E67_isElemAbelian_isPElt hE e he)
      ((ggL45_inducesIn_iff θ I e).mp (hEI e he)) (ggL45E67_isElemAbelian_comm hE e he) x₂ hx₂T
  have hx₁S : GGL45InS 3 E x₁ := ⟨⟨s + 1, hx₁3⟩, hx₁fix⟩
  have hx₂S : GGL45InS 3 E x₂ := ⟨⟨s + 1, hx₂3⟩, hx₂fix⟩
  have hb₁Z : x₁ ^ 3 ^ (s - 1) ∉ Subgroup.center K := by
    intro hmem
    have h1 : t₁ ^ 3 ^ (s - 1) = 1 := by
      rw [← hx₁, ← map_pow]
      exact MonoidHom.mem_ker.mp (S.ker_eq ▸ hmem)
    have hcontra := hind 1 0 (by rw [h1, pow_one, pow_zero, mul_one])
    exact absurd hcontra.1 (by norm_num)
  have hb_ind : ∀ i j : ℕ, (x₁ ^ 3 ^ (s - 1)) ^ i * (x₂ ^ 3 ^ (s - 1)) ^ j = 1 →
      3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    have h0 : S.π ((x₁ ^ 3 ^ (s - 1)) ^ i * (x₂ ^ 3 ^ (s - 1)) ^ j) = 1 := by
      rw [hij, map_one]
    simp only [map_mul, map_pow, hx₁, hx₂] at h0
    exact hind i j h0
  refine ⟨⟨x₁, hx₁S, hb₁Z⟩, x₁ ^ 3 ^ (s - 1), x₂ ^ 3 ^ (s - 1), ⟨x₁, hx₁S, rfl⟩,
    ⟨x₂, hx₂S, rfl⟩, hb₁Z, hb_ind⟩

theorem ggL45HTwo_HThree_of_frame {R : Type} [Group R] (D : E6ThreeModel.FrameData R)
    (hD : D.Good) {I : Set (MulAut R)} (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)
    (hTI : ∀ t ∈ D.Tor, MulAut.conj t ∈ I)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    (hZ : Nat.card (Subgroup.center K) ∣ 3) (ψ : MulAut K) (hψ : ψ ^ 3 = 1)
    (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E) (hEI : ∀ e ∈ E, GGL45InducesIn θ I e)
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) → ∀ t ∈ D.Tor, u t = t)
    (h3' : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      Nat.Coprime 3 (orderOf u) → ∃ t ∈ D.Tor, u = MulAut.conj t)
    (hCR : ∀ r : R, (∀ e ∈ E, ggInducedAut θ e r = r) → r ∈ D.Tor)
    {s : ℕ} {c : ℤ} (hc : c ≡ 1 [ZMOD 3])
    (hH1 : GGL45HOne 3 I θ E (ggInducedAut θ ψ) s c)
    (hH3 : ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    GGL45HTwo 3 I θ ψ E s c ∧ GGL45HThree 3 E s := by
  classical
  let π : K →* R := ggL45E67_pi θ
  have hπval : ∀ x : K, π x = θ (x : K ⧸ Subgroup.center K) := fun x => rfl
  have hπ : Function.Surjective π := ggL45E67_pi_surjective θ
  have hker : π.ker = Subgroup.center K := ggL45E67_pi_ker θ
  have hcard : Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := ggL45E67_pi_card_ker θ hZ
  have hcenter3 : ∀ z ∈ Subgroup.center K, z ^ 3 = 1 :=
    fun z hz => ggL45E67_center_pow_three hZ hz
  let w : Fin 6 → K := fun i => Function.surjInv hπ (D.nb i)
  have hw : ∀ i, π (w i) = D.nb i := fun i => Function.surjInv_eq hπ (D.nb i)
  obtain ⟨hF, hAlt, -⟩ := hD.modules π (Set.range w) (fun i => ⟨w i, ⟨i, rfl⟩, hw i⟩)
  let S : QuotFrame R D K θ :=
    { π := π, π_apply := hπval, surj := hπ, ker_eq := hker, w := w, w_spec := hw,
      noInvFunc := hF, noInvAlt := hAlt }
  have hEfix : ∀ e ∈ E, ∀ t ∈ D.Tor, ggInducedAut θ e t = t :=
    ggL45E67_E_fixes_torus D θ hE hEI hC
  have hStep3 : ∀ t ∈ D.Tor, ∀ k : ℕ, t ^ 3 ^ k = 1 →
      t ^ 3 ^ s = 1 ∧ ggInducedAut θ ψ t = t ^ c :=
    ggL45E67_H1_torus D θ hD.center hTI hEfix hH1
  have hPsi3 : ∀ t ∈ D.Tor, t ^ 3 = 1 → ggInducedAut θ ψ t = t :=
    ggL45E67_psi_three D θ hc hStep3
  have hWeylψ : ∀ i, (D.nb i)⁻¹ * ggInducedAut θ ψ (D.nb i) ∈ D.Tor :=
    ggL45E67_weyl_psi D hD θ ψ hPsi3
  have hWeylI : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      ∀ i, (D.nb i)⁻¹ * u (D.nb i) ∈ D.Tor :=
    ggL45E67_weyl_I D hD θ hC
  have hTabT : ∀ x ∈ ggL45E67_THat D S.π, ∀ y ∈ ggL45E67_THat D S.π, x * y = y * x :=
    ggL45E67_THat_abelian D hD S hcard
  have hFix3 : ∀ a : MulAut K, GGL45IsPElt 3 a → ggInducedAut θ a ∈ I →
      (∀ e ∈ E, a * e = e * a) → ∀ x ∈ ggL45E67_THat D S.π, a x = x :=
    ggL45E67_fix3 D hD S hI hC hWeylI hcard
  have hS_mem : ∀ x : K, GGL45InS 3 E x → x ∈ ggL45E67_THat D S.π :=
    ggL45E67_S_mem_THat D θ hCR
  have hScent : ∀ h : K, ∀ (hh : GGL45InS 3 E h), h ^ 3 ^ s ∈ Subgroup.center K :=
    ggL45E67_S_exp_center D θ (fun t ht k hk => (hStep3 t ht k hk).1) hS_mem
  have hSpsi : ∀ h : K, ∀ (hh : GGL45InS 3 E h), ψ h * (h ^ c)⁻¹ ∈ Subgroup.center K :=
    ggL45E67_S_psi_center D θ (fun t ht k hk => (hStep3 t ht k hk).2) hS_mem
  obtain ⟨v, N, hN3, hTcard, hNcop⟩ := ggL45E67_exists_N D S.π
  have hpowT : ∀ x : ↥(ggL45E67_THat D S.π), ((x : K) ^ N) ^ 3 ^ v = 1 :=
    ggL45E67_pow_N_isPElt D hTcard
  have hExpCenter : ∀ x : ↥(ggL45E67_THat D S.π),
      ((x : K) ^ N) ^ 3 ^ s ∈ Subgroup.center K :=
    ggL45E67_exp_center D S hpowT (fun t ht k hk => (hStep3 t ht k hk).1)
  have hPsiCenter : ∀ x : ↥(ggL45E67_THat D S.π),
      ψ ((x : K) ^ N) * (((x : K) ^ N) ^ c)⁻¹ ∈ Subgroup.center K :=
    ggL45E67_psi_center D S hpowT (fun t ht k hk => (hStep3 t ht k hk).2)
  have hs1 : 1 ≤ s := ggL45E67_one_le_s D hH3
  have hH2comm : ∀ h t : K, GGL45InS 3 E h → GGL45InS 3 E t → h * t = t * h :=
    fun h t hh ht => hTabT h (hS_mem h hh) t (hS_mem t ht)
  have hH2exp : ∀ h : K, GGL45InS 3 E h → h ^ 3 ^ s = 1 := by
    intro h hh
    have hcent := hScent h hh
    rcases hcard with h1 | h3
    · exact ggL45E67_eq_one_of_ker_card_one hker h1 hcent
    · have h3c : Nat.card ↥(Subgroup.center K) = 3 := by rwa [hker] at h3
      exact ggL45E67_H2_exp D S (ggL45E67_centerEquiv h3c) hNcop hs1 hcenter3 hTabT hExpCenter
        (hS_mem h hh) hcent
  have hH2psi : ∀ h : K, GGL45InS 3 E h → ψ h = h ^ c := by
    intro h hh
    have hcent := hSpsi h hh
    rcases hcard with h1 | h3
    · exact mul_inv_eq_one.mp (ggL45E67_eq_one_of_ker_card_one hker h1 hcent)
    · have h3c : Nat.card ↥(Subgroup.center K) = 3 := by rwa [hker] at h3
      exact ggL45E67_H2_psi D S (ggL45E67_centerEquiv h3c) hψ hc hZ hNcop hcenter3 hTabT hpowT
        (fun t ht k hk => hStep3 t ht k hk) hWeylψ hPsiCenter (hS_mem h hh) hcent
  refine ⟨⟨hH2comm, fun h hh => ⟨hH2exp h hh, hH2psi h hh⟩,
    ggL45E67_H2_fix D S hI hK hFix3 h3' hTabT hS_mem⟩, ?_⟩
  exact ggL45E67_H3 D S hE hEI hcenter3 hFix3 hH3

end CFSG.StandardType
