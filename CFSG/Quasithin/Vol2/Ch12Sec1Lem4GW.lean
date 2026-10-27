module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4G
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4EW
public import CFSG.Quasithin.Vol2.Ch10SecKHL4L5
public import CFSG.Quasithin.Vol2.Ch10SecKHLk2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

namespace Sec1214

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem false_of_component_linW (hFF : LemH9FF4) (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (h134 : C134L32CorrM) {X : Subgroup G} (hX : IsXSub T L V V₁ X)
    (hnc : ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ X,
      a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 X)
    {K : Subgroup G} (hK : K ∈ cComp (T₀ ⊔ X ⊔ T))
    (hHK : T₀ ⊔ X ⊔ T ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ K) {k : ℕ}
    (hk : k = 4 ∨ k = 5)
    (hlin : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL k 2 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := T₀ ⊔ X ⊔ T with hH
  have hTH : T ≤ H := le_sup_right
  have hT₀H : T₀ ≤ H := le_sup_left.trans le_sup_left
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo c.S.ctx.hyp.sylow hTH
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hHK
  have hXo : X = oTwoUpper X := hX.xi.1
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := hX.xi.2.1
  have hcube : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X := by
    obtain ⟨p, hp, -, hpow, hidx, -⟩ := hX.xi.2.2.2
    have hp3 : p = 3 := by
      rcases hidx with h | ⟨h, -⟩
      · rw [hX.relIndex] at h
        have h2 : p ^ 2 = 3 ^ 2 := by rw [← h]; norm_num
        exact Nat.pow_left_injective (by norm_num) h2
      · rw [hX.relIndex] at h
        exfalso
        have h1 : 2 ≤ p := hp.two_le
        rcases Nat.lt_or_ge p 3 with h2 | h2
        · interval_cases p; norm_num at h
        · have : 27 ≤ p ^ 3 := by
            calc 27 = 3 ^ 3 := by norm_num
              _ ≤ p ^ 3 := Nat.pow_le_pow_left h2 3
          omega
    exact hp3 ▸ hpow
  have hAut := Vol2.Ch10.SecB.nonempty_aut_of Vol2.Ch10.SecB.factL4L5 hsyl hK hTK hk hlin hXK hXo
    hTX hcube hX.relIndex hnc
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTKsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hsyl hKH hHK
  obtain ⟨hwc, h3⟩ := Vol2.Ch10.SecB.fact10_2_5Lk2 G K T X k hk hlin hsyl.2.1 hTK hTKsyl hAut hXK
    hTX hXo.symm hX.relIndex hcube
  set W := pCoreOf 2 (X ⊔ T ⊓ K) with hW
  have hUN : T ⊓ K ≤ Subgroup.normalizer ((X ⊔ T ⊓ K : Subgroup G) : Set G) :=
    sup_le_iff.mp (le_refl (X ⊔ T ⊓ K)) |>.2.trans Subgroup.le_normalizer
  have hWU : W ≤ T ⊓ K := Vol2.Ch10.SecB.C10KH.pCoreOf_le_of_isSylowTwoOf' hTKsyl
    (sup_le hXK inf_le_right) hUN
  have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T ⊓ K))
  have hWT₁ : W ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
    intro w hw
    have hwT : w ∈ T := (hWU hw).1
    refine ⟨hwT, hX.ker w hwT fun x hx => ?_⟩
    have h1 : w * x * w⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTX hwT) x).mp hx) (X.inv_mem hx)
    have h2 : w * x * w⁻¹ * x⁻¹ ∈ W := by
      have h3 : x * w⁻¹ * x⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hXW hx) _).mp (W.inv_mem hw)
      have : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
      rw [this]
      exact W.mul_mem hw h3
    have hXWn : X ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hXW hy⟩
    have hXW2 : IsPGroup 2 ↥(X ⊓ W) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXWn hXW2 ⟨h1, h2⟩
  have hT₀W : ∀ t ∈ T₀, t ∈ Subgroup.normalizer (W : Set G) := by
    intro t ht
    have htK : t ∈ Subgroup.normalizer (K : Set G) := hHK (hT₀H ht)
    have hle : W.map (MulAut.conj t).toMonoidHom ≤ T ⊓ K := by
      rintro _ ⟨w, hw, rfl⟩
      have hw₁ := hWT₁ hw
      have h1 : t * w * t⁻¹ ∈ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (c.hT₀N ht) w).mp hw₁
      exact ⟨h1.1, (Subgroup.mem_normalizer_iff.mp htK w).mp (hWU hw).2⟩
    have heq := hwc t htK hle
    refine Sec121Swap.mem_normalizer_of_conj_mem fun w hw => ?_
    rw [← heq]
    exact ⟨w, hw, rfl⟩
  have hT₀X : T₀ ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht
    refine mem_normalizer_of_three hXo hcube fun x hx hx3 => ?_
    have htK : t ∈ Subgroup.normalizer (K : Set G) := hHK (hT₀H ht)
    refine h3 _ ⟨(Subgroup.mem_normalizer_iff.mp htK x).mp (hXK hx), ?_⟩ ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT₀W t ht) (hXW hx))
        (Subgroup.inv_mem _ (hT₀W t ht))
    · rw [show t * x * t⁻¹ = MulAut.conj t x from rfl, MulEquiv.orderOf_eq, hx3]
  exact c.not_le_normalizer_XW hFF hA21 h51 h134 hX
    (sup_le (sup_le hT₀X Subgroup.le_normalizer) hTX)

end Setting

end Sec1214

end CFSG.Quasithin.H13
