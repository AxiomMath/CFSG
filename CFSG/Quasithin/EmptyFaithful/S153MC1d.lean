module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoK
public import CFSG.Quasithin.EmptyFaithful.S153MStrong2

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

namespace S153M

section StrongTwo

theorem false_of_strong_two {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (hJ : ffJ X = L₁ ⊔ L₂)
    (h : TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hstrong : IsStrongFFModule X) : False := by
  obtain ⟨A, hAX, hA1, hA2, hlt⟩ := hstrong
  have hAA : IsA2 X A := ⟨hAX, hA1, hA2⟩
  obtain ⟨B, -, hB, hBr⟩ := B1_4_4_lt hV hAA ((rAV_lt_one_iff hV hAA).2 hlt)
  have hlt' : Nat.card V < Nat.card B * Nat.card (fixV B) := (rAV_lt_one_iff hV hB.isA2).1 hBr
  have hBL : B ≤ L₁ ⊔ L₂ := hJ ▸ B6.le_ffJ hB
  have h4 := not_strong_of_twoNat hV h hcomm hBL hB.2.1 hB.2.2.1
  omega

end StrongTwo

section Two

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem noStrong_two_of_hyp (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hF : HypF918 T V L V₁ Vp H K) (M' : Subgroup G)
    (hHK : H = K ⊔ T) (hS : SQTKGroup ↥H) (hK0 : conjClosure K T ≠ K)
    (hker : kerIn M' H = pCoreOf 2 H) {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n)
    (hKs : IsPSL 2 2 n ↥(E2.star M' H K) ∨ IsSz n ↥(E2.star M' H K))
    (hB : E2.IsBorelIn (E2.star M' H K) (E2.star M' H (M' ⊓ K)))
    {I : Subgroup G} (hIU : I ≤ conjClosure Vp H)
    (hWK : tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H))
    (hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥)
    (hs : F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I H))
      (hF.isElemAbelian_tilde_of_le (conjClosure_le_conjClosure_U hIU le_rfl))) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hWU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hFE : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))) :=
    ⟨hF.isElemAbelian_tilde_of_le hWU⟩
  have hWN : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUN : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hUW : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hK0
    refine le_antisymm (conjClosure_le fun t ht z hz => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
  obtain ⟨hKt, hK₀eq, hcomm, hperm⟩ := (five_group_data hF hS hA37 hA38 hK0).2 t htT htK
  set φ := actH hWN hUN with hφ
  have hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    hF.actH_eq_one_of_mem_pCoreOf hIU hx
  have hnt : ¬ (conjClosure K T).subgroupOf H ≤ φ.ker := by
    intro h
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have h1 := h (Subgroup.mem_subgroupOf.mpr hk : (⟨k, hF.K₀_le_H hk⟩ : ↥H) ∈
        (conjClosure K T).subgroupOf H)
      have h2 := (actE_eq_one_iff hWN hUN hUW ⟨k, hF.K₀_le_H hk⟩).mp h1 u hu
      have h3 := V₁.inv_mem h2
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at h3
    apply hW0
    rw [← hWK, eq_bot_iff]
    intro y hy
    obtain ⟨a, haJ, rfl⟩ := mem_secImg.mp hy
    exact Subgroup.mem_bot.mpr (secMk_eq_one_iff.mpr (hle haJ))
  have hXH : conjClosure K T ⊔ T ≤ H := hF.K₀T_le_H
  have h3 : (conjClosure K T ⊔ T).subgroupOf H = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    exact hHK ▸ sup_le_sup_right (le_conjClosure K T) T
  have hSt : IsStrongFFModule φ.range := by
    have h1 : IsStrongFFModule (autOn (tildeOf V₁ (conjClosure K T ⊔ T))
        (tildeOf V₁ (conjClosure I H))) := hs
    rw [autOn_tilde_eq_map_actH hWN hUN hXH, h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  have hFF : IsFFModule φ.range := by
    have h1 : IsFFModule (autOn (tildeOf V₁ (conjClosure K T ⊔ T))
        (tildeOf V₁ (conjClosure I H))) := F9.IsStrongFFInt.isFFInt hs
    rw [autOn_tilde_eq_map_actH hWN hUN hXH, h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  have hV : ∀ v : ↥(tildeOf V₁ (conjClosure I H)), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hFE.out.2 v v.2)
  obtain ⟨⟨hJ, hTwo, hc, -, -, -⟩, -⟩ :=
    kActionTwo_data hA21 h56 hF M' hS hHK htT hKt hK₀eq hcomm hperm hker hn3 hnodd hKs hB hWN hUN
      hQ hnt hFF
  exact false_of_strong_two hV hJ hTwo hc hSt

end Two

end S153M

end CFSG.Quasithin
