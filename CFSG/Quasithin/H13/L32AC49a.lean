module

public import CFSG.Quasithin.H13.L32AC48b
public import CFSG.Quasithin.H13.L32AC47g
public import CFSG.Quasithin.H13.L32AC47h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section Setting

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem comm_pCoreOf_mem {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ pCoreOf 2 H) {k : G} (hk : k ∈ K) : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hxH : x ∈ H := Subgroup.map_subtype_le _ hx
  have hPn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := fun h hh =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (Subgroup.le_normalizer hh)
  refine pCoreOf_inf_le_of_le hKH ⟨?_, ?_⟩
  · have h1 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hPn (hKH hk)) _).mp ((pCoreOf 2 H).inv_mem hx)
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hx h1
  · have h1 : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hxH) k).mp hk
    exact K.mul_mem h1 (K.inv_mem hk)

theorem mem_pCoreOf_of_comm (h28 : Lemma14_7_28) (S : Setting147 G T L V H) {K : Subgroup G}
    (hcK : cComp H = {K}) (hL1K : l1 T L V ≤ K) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (cStar K) = ⊥) {x : G} (hx : x ∈ H)
    (hxc : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : x ∈ pCoreOf 2 H := by
  have hK : K ∈ cComp H := by rw [hcK]; exact Set.mem_singleton K
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set N := CFSG.pCore 2 ↥H with hN
  set Kb := modO2Image H K with hKb
  have hK'n : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKbn : Kb.Normal := hK'n.map _ (QuotientGroup.mk'_surjective _)
  have hZb : Subgroup.center ↥Kb = ⊥ := by
    have hc := card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)
    rw [hZ, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc.symm
  have hC := centralizer_eq_bot h28 S hcK hL1K hKbn hZb
  have hxC : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N) ∈
      Subgroup.centralizer (Kb : Set (↥H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hkK' : k ∈ K := hkK
    have h1 := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) (hxc k hkK')
    have h2 : (⟨x, hx⟩ : ↥H) * ⟨k, hkH⟩ * (⟨x, hx⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ : ↥H)⁻¹ ∈ N := by
      rw [hN]
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = (⟨x, hx⟩ : ↥H) * ⟨k, hkH⟩ * (⟨x, hx⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ : ↥H)⁻¹ :=
        Subtype.ext hyx
      rw [← this]
      exact hy
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h2
    show QuotientGroup.mk' N ⟨k, hkH⟩ * QuotientGroup.mk ⟨x, hx⟩ =
      QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk' N ⟨k, hkH⟩
    rw [QuotientGroup.mk'_apply]
    have h3 := mul_inv_eq_one.mp h2
    calc (QuotientGroup.mk (⟨k, hkH⟩ : ↥H) : ↥H ⧸ N) * QuotientGroup.mk ⟨x, hx⟩ =
        (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk (⟨k, hkH⟩ : ↥H) *
          (QuotientGroup.mk ⟨x, hx⟩)⁻¹) * QuotientGroup.mk ⟨x, hx⟩ := by rw [h3]
      _ = QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨k, hkH⟩ := by group
  rw [hC, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hN] at hxC
  exact ⟨_, hxC, rfl⟩

end Setting

section Range

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}

theorem quotIso_of_range {X Y : Type} [Group X] [Group Y] [Finite X] (π : ↥K →* X)
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) (c : Y →* MulAut X)
    (hc : Function.Injective c) (hr : ∀ y : ↥H, indHom π hπ hker hKn hHN y ∈ c.range)
    (hcent : ∀ x ∈ H, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → x ∈ pCoreOf 2 H) :
    ∃ ψ : ↥H →* Y, (∀ y, c (ψ y) = indHom π hπ hker hKn hHN y) ∧
      ψ.ker = CFSG.Open.pCore 2 ↥H := by
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  let e := MonoidHom.ofInjective hc
  set ψ : ↥H →* Y := e.symm.toMonoidHom.comp (β.codRestrict _ hr) with hψdef
  have hψ : ∀ y : ↥H, c (ψ y) = β y := by
    intro y
    have := congrArg Subtype.val (e.apply_symm_apply (β.codRestrict _ hr y))
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  refine ⟨ψ, hψ, ?_⟩
  ext y
  rw [MonoidHom.mem_ker]
  have hiff : ψ y = 1 ↔ β y = 1 := by
    rw [← hψ, ← map_one c]
    exact hc.eq_iff.symm
  rw [hiff]
  constructor
  · intro h1
    have hmem : (y : G) ∈ pCoreOf 2 H := by
      refine hcent y y.2 fun k hk => ?_
      have h2 := hβ y ⟨k, hk⟩
      rw [h1, MulAut.one_apply] at h2
      have h3 : π (conjK (hKn y.2) ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_inv, ← h2, mul_inv_cancel]
      exact (hker _).mp h3
    obtain ⟨y', hy', hyy'⟩ := hmem
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  · intro hy
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := hπ a
    rw [hβ, MulAut.one_apply]
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hker]
    have hy' : (y : G) ∈ pCoreOf 2 H := ⟨y, hy, rfl⟩
    have := comm_pCoreOf_mem hKH hKn hy' k.2
    simpa [conjK_apply] using this

end Range

end CFSG.Quasithin.H13.L32A.C
