module

public import CFSG.Quasithin.EmptyFaithful.S146F6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_oTwoPIn_of_pSec_P20 {p : ℕ} {H X : Subgroup G} (hXH : X ≤ H)
    (hn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hp : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H) : X ≤ oTwoPIn p H := by
  classical
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := S146A.le_normalizer_of_forall_conj_mem hn
  have hWn : ((X.subgroupOf H).map π).Normal :=
    Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX) π
      (QuotientGroup.mk'_surjective _)
  have hWp : IsPGroup p ↥((X.subgroupOf H).map π) := by
    intro w
    obtain ⟨z, hz, hzw⟩ := w.2
    obtain ⟨k, hk⟩ := hp (z : G) (Subgroup.mem_subgroupOf.mp hz)
    refine ⟨k, Subtype.ext ?_⟩
    obtain ⟨y, hy, hyz⟩ := hk
    have hyz' : y = z ^ p ^ k := Subtype.ext hyz
    have h1 : π (z ^ p ^ k) = 1 := (QuotientGroup.eq_one_iff _).mpr (hyz' ▸ hy)
    show (w : OTwoQuot H) ^ p ^ k = 1
    rw [← hzw, ← map_pow]
    exact h1
  have hWle : (X.subgroupOf H).map π ≤ CFSG.pCore p (OTwoQuot H) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hWn hWp
  intro x hx
  exact mem_oTwoPIn_of_mem_pCore (hXH hx)
    (hWle (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)))

section Kz

variable [Finite G] {T M : Subgroup G}

theorem oTwoUpper_le_oTwoPIn_of_kz_P20 (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hK : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) :
    oTwoUpper H ≤ oTwoPIn p (mcOf T) := by
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hKPQ : oTwoUpper H ≤ PQ := hred.oTwoUpper_le_pq hT2
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKG : oTwoUpper H ≤ mcOf T := hKH.trans hHG
  have hKn : ∀ g ∈ mcOf T, ∀ k ∈ oTwoUpper H, g * k * g⁻¹ ∈ oTwoUpper H := by
    intro g hg k hk
    have := mem_conjClosure hg hk
    rwa [hK] at this
  have hRn : mcOf T ≤ Subgroup.normalizer ((pCoreOf 2 (oTwoUpper H) : Subgroup G) : Set G) :=
    (S146A.le_normalizer_of_forall_conj_mem hKn).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hRG : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (mcOf T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKG) hRn (pCoreOf_isPGroup 2 _)
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hKQR : ∀ c ∈ oTwoUpper H, c ∈ pCoreOf 2 H → c ∈ pCoreOf 2 (oTwoUpper H) := by
    intro c hcK hcQ
    have hn : oTwoUpper H ≤
        Subgroup.normalizer ((oTwoUpper H ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      S146A.le_normalizer_of_forall_conj_mem fun g hg x hx =>
        ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem hg hx.1) ((oTwoUpper H).inv_mem hg),
          hQn g (hKH hg) x hx.2⟩
    have hle : oTwoUpper H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (oTwoUpper H) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hn (IsPGroup.to_le (pCoreOf_isPGroup 2 H) inf_le_right)
    exact hle ⟨hcK, hcQ⟩
  refine le_oTwoPIn_of_pSec_P20 hKG hKn fun x hx => ?_
  obtain ⟨k, hk⟩ := hred.pSec x (hKPQ hx)
  exact ⟨k, hRG (hKQR _ ((oTwoUpper H).pow_mem hx _) hk)⟩

theorem oTwoUpper_le_oTwoFstarIn_of_kz_P20 (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hK : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) :
    oTwoUpper H ≤ oTwoFstarIn (mcOf T) :=
  (oTwoUpper_le_oTwoPIn_of_kz_P20 S hred hK).trans (oTwoPIn_le_oTwoFstarIn hred.prime _)

end Kz

@[expose] def Input14617FstarK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      Stage14614At T H p → conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H →
        oTwoUpper H ≤ oTwoFstarIn (mcOf T)

theorem input14617Fstar_of_K (i : Input14617FstarK) : Input14617Fstar := by
  intro G _ _ T M S H PQ p hred hmax hAt
  by_cases hK : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H
  · exact oTwoUpper_le_oTwoFstarIn_of_kz_P20 S hred hK
  · exact i G T M S H PQ p hred hmax hAt hK

end CFSG.Quasithin
