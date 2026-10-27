module

public import CFSG.Quasithin.Background.C35InspLevi
public import CFSG.Quasithin.Background.C35InspL45C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C35Pf

variable {A : Type} [Group A]

structure C35Base (K Y M₀ V : Subgroup A) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple ↥K
  center : IsPGroup 2 ↥(centerOf K)
  parabolic : IsParabolic2 K Y
  ne_top : Y ≠ K
  normalizer_eq : K ⊓ Subgroup.normalizer (pCoreOf 2 Y : Set A) = Y
  center_le : centerOf K ≤ pCoreOf 2 Y
  eq_perfectCore : M₀ = perfectCore Y
  ne_bot : M₀ ≠ ⊥
  V_le : V ≤ M₀
  pCoreOf_le : pCoreOf 2 M₀ ≤ Subgroup.centralizer (V : Set A)
  V_elem : IsElemAbelian 2 V
  V_comm : ⁅V, M₀⁆ = V
  V_ne : V ≠ ⊥

variable {K Y M₀ V : Subgroup A}

theorem C35Data.toBase [Finite A] (hD : C35Data K Y M₀ V) : C35Base K Y M₀ V where
  quasisimple := hD.quasisimple
  center := hD.center
  parabolic := hD.parabolic
  ne_top := hD.ne_top
  normalizer_eq := hD.normalizer_eq
  center_le := hD.center_le
  eq_perfectCore := hD.eq_perfectCore
  ne_bot := hD.ne_bot
  V_le := hD.V_le
  pCoreOf_le := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hD.V_le_center hv).2 x
      ((le_pCoreOf_of_data hD).2 hx)).symm
  V_elem := hD.V_elem
  V_comm := hD.V_comm
  V_ne := hD.V_ne

namespace C35Base

theorem perfectCore_ne_bot (hD : C35Base K Y M₀ V) : perfectCore Y ≠ ⊥ :=
  hD.eq_perfectCore ▸ hD.ne_bot

theorem exists_conj_normalizer [Finite A] (hD : C35Base K Y M₀ V) {G' : Type} [Group G']
    [Finite G'] (φ : ↥K →* G') (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ)
    {U₀ : Subgroup G'} (hU₀ : IsSylowTwoOf U₀ ⊤) :
    ∃ g : G', Subgroup.normalizer (U₀ : Set G') ≤
        img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y ≠ ⊤ ∧
      ¬ Group.IsSolvable ↥(img ((MulAut.conj g⁻¹).toMonoidHom.comp φ) Y) :=
  C35Levi.exists_conj_normalizer hD.center hD.parabolic hD.ne_top hD.perfectCore_ne_bot φ hker
    hφ hU₀

theorem le_pCoreOf [Finite A] (hD : C35Base K Y M₀ V) :
    V ≤ pCoreOf 2 M₀ ∧ pCoreOf 2 M₀ ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY : M₀ ≤ Y := hD.eq_perfectCore ▸ perfectCore_le Y
  have hYN : Y ≤ Subgroup.normalizer (M₀ : Set A) := by
    rw [hD.eq_perfectCore]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Y)
  refine ⟨?_, ?_⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hD.V_le ?_ ?_
    · exact le_normalizer_of_comm hD.V_comm
    · exact fun x => ⟨1, Subtype.ext (by simpa using hD.V_elem.2 x x.2)⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans hMY) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀)
    exact hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M₀)

theorem comm_of_pCore (hD : C35Base K Y M₀ V) {G' : Type} [Group G'] (θ : ↥K →* G')
    (hθker : θ.ker ≤ Subgroup.center ↥K) {Q : Subgroup G'} (hQM : Q ≤ img θ M₀)
    (hQn : img θ M₀ ≤ Subgroup.normalizer (Q : Set G')) (hQ2 : IsPGroup 2 ↥Q) {v : A}
    (hv : v ∈ V) (hvK : v ∈ K) {q : G'} (hq : q ∈ Q) :
    q * θ ⟨v, hvK⟩ = θ ⟨v, hvK⟩ * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMK : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hD.parabolic.1
  let R : Subgroup A := (Q.comap θ).map K.subtype ⊓ M₀
  have hRM : R ≤ M₀ := inf_le_right
  have hMR : M₀ ≤ Subgroup.normalizer (R : Set A) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y' ∈ M₀, ∀ r ∈ R, y' * r * y'⁻¹ ∈ R := by
      intro y' hy' r hr
      obtain ⟨⟨r', hr'Q, hr'r⟩, hrM⟩ := hr
      refine ⟨⟨⟨y', hMK hy'⟩ * r' * ⟨y', hMK hy'⟩⁻¹, ?_, ?_⟩, ?_⟩
      · show θ (⟨y', hMK hy'⟩ * r' * ⟨y', hMK hy'⟩⁻¹) ∈ Q
        have hθy : θ ⟨y', hMK hy'⟩ ∈ img θ M₀ := ⟨_, Subgroup.mem_subgroupOf.2 hy', rfl⟩
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 (hQn hθy) _).1 hr'Q
      · rw [← hr'r]
        rfl
      · exact M₀.mul_mem (M₀.mul_mem hy' hrM) (M₀.inv_mem hy')
    intro r
    refine ⟨key y hy r, fun h => ?_⟩
    have := key y⁻¹ (M₀.inv_mem hy) _ h
    simpa [mul_assoc] using this
  have hR2 : IsPGroup 2 ↥R := by
    rintro ⟨r, ⟨r', hr'Q, hr'r⟩, hrM⟩
    obtain ⟨k, hk⟩ := hQ2 ⟨θ r', hr'Q⟩
    have hk' : θ (r' ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hZ : ((r' ^ 2 ^ k : ↥K) : A) ∈ centerOf K := mem_centerOf_iff.2 (hθker hk')
    obtain ⟨l, hl⟩ := hD.center ⟨_, hZ⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    have hl' : ((r' : A) ^ 2 ^ k) ^ 2 ^ l = 1 := by
      have := congrArg Subtype.val hl
      simpa using this
    show r ^ 2 ^ (k + l) = 1
    rw [← hr'r, pow_add, pow_mul]
    exact hl'
  have hRO : R ≤ pCoreOf 2 M₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRM hMR hR2
  obtain ⟨y, hy, hyq⟩ := hQM hq
  have hyM : (y : A) ∈ M₀ := Subgroup.mem_subgroupOf.1 hy
  have hyR : (y : A) ∈ R := ⟨⟨y, show θ y ∈ Q by rw [hyq]; exact hq, rfl⟩, hyM⟩
  have hc : v * y = y * v := Subgroup.mem_centralizer_iff.1 (hD.pCoreOf_le (hRO hyR)) v hv
  rw [← hyq, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc.symm

end C35Base

end CFSG.Quasithin
