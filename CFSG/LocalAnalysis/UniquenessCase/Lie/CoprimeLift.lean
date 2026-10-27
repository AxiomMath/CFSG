module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22pwlie_borelWit_of_central_quotient {K : Type} [Group K] [Finite K] {Z : Subgroup K} [Z.Normal]
    (hZ : Z ≤ center K) {ℓ k : ℕ} (hℓ : ℓ.Prime) (hcop : ¬ ℓ ∣ Nat.card Z)
    (h : uc22p20oBorelWit (K ⧸ Z) ℓ k) : uc22p20oBorelWit K ℓ k := by
  intro P
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  obtain ⟨Pb, hPb⟩ : ∃ Pb : Sylow 2 (K ⧸ Z), (Pb : Subgroup (K ⧸ Z)) = (P : Subgroup K).map π :=
    ⟨P.mapSurjective hπ, Sylow.coe_mapSurjective _ _⟩
  obtain ⟨Fb, hFbN, hFbE, hFbc⟩ := h Pb
  let Ft : Subgroup K := Fb.comap π
  have hZFt : Z ≤ Ft := fun z hz => by
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    show π z ∈ Fb
    rw [h1]
    exact Fb.one_mem
  let ψ : Ft →* K ⧸ Z := π.comp Ft.subtype
  have hψr : ψ.range = Fb := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨⟨x, hy⟩, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : K), (QuotientGroup.eq_one_iff _).1 x.2⟩
        invFun := fun z => ⟨⟨z, hZFt z.2⟩, (QuotientGroup.eq_one_iff _).2 z.2⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have hindex : ψ.ker.index = ℓ ^ k := by
    rw [Subgroup.index_ker, hψr, hFbc]
  have hcopr : (Nat.card ψ.ker).Coprime ψ.ker.index := by
    rw [hker, hindex]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hcop).symm
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcopr
  have hHinf : ∀ x ∈ H, ψ x = 1 → x = 1 := fun x hx h1 =>
    Subgroup.disjoint_def.1 hH.disjoint (MonoidHom.mem_ker.2 h1) hx
  have hψH : ∀ x ∈ H, ψ x ∈ Fb := fun x _ => hψr ▸ ⟨x, rfl⟩
  have hHE : IsElemAbelian ℓ H := by
    refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, fun x hx => ?_⟩
    · haveI := hFbE.1
      have hcomm : ψ x * ψ y = ψ y * ψ x := setLike_mul_comm (hψH x hx) (hψH y hy)
      have h1 : (x * y) * (y * x)⁻¹ = 1 := hHinf _
        (H.mul_mem (H.mul_mem hx hy) (H.inv_mem (H.mul_mem hy hx)))
        (by rw [map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel])
      exact mul_inv_eq_one.1 h1
    · exact hHinf (x ^ ℓ) (H.pow_mem hx ℓ) (by rw [map_pow]; exact hFbE.2 _ (hψH x hx))
  have hHc : Nat.card H = ℓ ^ k := by
    have h1 := hH.card_mul
    have h2 := Subgroup.card_ker_mul_card_range ψ
    rw [hψr, hFbc] at h2
    have h3 : Nat.card ψ.ker * Nat.card H = Nat.card ψ.ker * ℓ ^ k := h1.trans h2.symm
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  have hclaim : ∀ g ∈ Ft, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    have hgN := Subgroup.mem_normalizer_iff.1 (hFbN (show π g ∈ Fb from hg)) (π x)
    have hπx : π x ∈ (Pb : Subgroup (K ⧸ Z)) := by
      rw [hPb]
      exact ⟨x, hx, rfl⟩
    have h2 : π g * π x * (π g)⁻¹ ∈ (Pb : Subgroup (K ⧸ Z)) := hgN.1 hπx
    rw [hPb] at h2
    obtain ⟨p, hp, hpe⟩ := h2
    have hpy : π p = π (g * x * g⁻¹) := by rw [hpe, map_mul, map_mul, map_inv]
    have hz : p⁻¹ * (g * x * g⁻¹) ∈ Z := QuotientGroup.eq.1 hpy
    set z := p⁻¹ * (g * x * g⁻¹) with hzdef
    have hzc : z ∈ center K := hZ hz
    have hy' : g * x * g⁻¹ = p * z := by rw [hzdef]; group
    obtain ⟨n₁, hn₁⟩ := P.isPGroup' ⟨x, hx⟩
    obtain ⟨n₂, hn₂⟩ := P.isPGroup' ⟨p, hp⟩
    have hx1 : x ^ (2 ^ n₁) = 1 := congrArg Subtype.val hn₁
    have hp1 : p ^ (2 ^ n₂) = 1 := congrArg Subtype.val hn₂
    have hxN : x ^ (2 ^ (n₁ + n₂)) = 1 := by rw [pow_add, pow_mul, hx1, one_pow]
    have hpN : p ^ (2 ^ (n₁ + n₂)) = 1 := by
      rw [add_comm, pow_add, pow_mul, hp1, one_pow]
    have hyN : (g * x * g⁻¹) ^ (2 ^ (n₁ + n₂)) = 1 := by rw [conj_pow, hxN]; simp
    have hcp : Commute p z := Subgroup.mem_center_iff.1 hzc p
    have hzN : z ^ (2 ^ (n₁ + n₂)) = 1 := by
      have h1 : (p * z) ^ (2 ^ (n₁ + n₂)) = p ^ (2 ^ (n₁ + n₂)) * z ^ (2 ^ (n₁ + n₂)) := hcp.mul_pow _
      rw [← hy', hyN, hpN, one_mul] at h1
      exact h1.symm
    have hzP : z ∈ P := by
      have hcard : orderOf z ∣ 2 ^ (n₁ + n₂) := orderOf_dvd_of_pow_eq_one hzN
      obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcard
      have hnorm : (Subgroup.zpowers z).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hzc)
      have hpg : IsPGroup 2 (Subgroup.zpowers z) :=
        IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, ha])
      exact hpg.le_sylow_of_normal P (Subgroup.mem_zpowers _)
    rw [hy']
    exact P.mul_mem hp hzP
  refine ⟨H.map Ft.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun y => ?_
    constructor
    · exact fun hy => hclaim x x.2 y hy
    · intro hy
      have h3 : y ∈ P := by
        have := hclaim x⁻¹ (Ft.inv_mem x.2) _ hy
        simpa [mul_assoc] using this
      exact h3
  · exact uc22p20d_isElemAbelian_map Ft.subtype Ft.subtype_injective hHE
  · rw [Subgroup.card_map_of_injective Ft.subtype_injective, hHc]

end CFSG.LocalAnalysis.UniquenessCase.UC22
