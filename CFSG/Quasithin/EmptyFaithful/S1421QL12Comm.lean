module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_solvRad_of_ne {H L K : Subgroup G} (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (hne : L ≠ K) : ⁅L, K⁆ ≤ solvRad H := by
  rcases cComp_commutator_dichotomy_of_le hL (le_of_mem_cComp hK) with ⟨h, -⟩ | h
  · exact h
  · exfalso
    have hLN : L ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hL
    have hLK : L ≤ K :=
      calc L ≤ conjClosure L K := le_conjClosure L K
        _ = ⁅L, K⁆ := h.symm
        _ ≤ K := Subgroup.le_normalizer_iff_commutator_le_right.mp hLN
    exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hLK hne) (ne_bot_of_mem_cComp hL)
      (perfect_of_mem_cComp hL) (subnormal_of_mem_cComp hL)

theorem inf_solvRad_le_solvRad {H K : Subgroup G} (hKH : K ≤ H) : K ⊓ solvRad H ≤ solvRad K := by
  have hs : Group.IsSolvable ↥(solvRad H) := solvRad_isSolvable H
  refine le_solvRad inf_le_left ?_ (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_right : K ⊓ solvRad H ≤ solvRad H))
    (Subgroup.inclusion_injective _))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk,
    normalizer_le_normalizer_solvRad H (Subgroup.le_normalizer (hKH hk))⟩

theorem mem_solvRad_of_commutator_mem {H K : Subgroup G} (hK : K ∈ cComp H) {b : G} (hb : b ∈ K)
    (h : ∀ k ∈ K, k⁻¹ * b⁻¹ * k * b ∈ solvRad K) : b ∈ solvRad K := by
  set R : Subgroup ↥K := (solvRad K).subgroupOf K with hR
  set π : ↥K →* ↥K ⧸ R := QuotientGroup.mk' R with hπ
  set P : Subgroup ↥K := (Subgroup.center (↥K ⧸ R)).comap π with hP
  have hPn : P.Normal := Subgroup.Normal.comap inferInstance π
  rcases normal_eq_top_or_map_le_solvRad hK P with htop | hle
  · exfalso
    obtain ⟨-, ⟨-, a, c, hac⟩, -⟩ := cComp_structure hK
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hx : x ∈ P := htop ▸ Subgroup.mem_top x
    exact hac (Subgroup.mem_center_iff.mp hx c).symm
  · have hbP : (⟨b, hb⟩ : ↥K) ∈ P := by
      rw [hP, Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro w
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
      refine Eq.symm ?_
      change π ⟨b, hb⟩ * (k : ↥K ⧸ R) = (k : ↥K ⧸ R) * π ⟨b, hb⟩
      rw [hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq, hR, Subgroup.mem_subgroupOf]
      have e : ((((⟨b, hb⟩ : ↥K) * k)⁻¹ * (k * ⟨b, hb⟩) : ↥K) : G) = (k : G)⁻¹ * b⁻¹ * k * b := by
        simp [mul_assoc]
      rw [e]
      exact h (k : G) k.2
    exact hle ⟨_, hbP, rfl⟩

theorem mem_solvRad_of_odd_of_conj {H K Q : Subgroup G} (hK : K ∈ cComp H) {x : G} (hxH : x ∈ H)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) (hQ : IsPGroup 2 Q) (hxQ : x ∈ Q) {b : G}
    (hbK : b ∈ K) (hbQ : b ∈ Subgroup.normalizer (Q : Set G)) (hbodd : Odd (orderOf b)) :
    b ∈ solvRad K := by
  have hK' : cjSub x K ∈ cComp H := map_conj_mem_cComp hK hxH
  have hne : K ≠ cjSub x K := fun h => hxK (B2F.mem_normalizer_iff_cjSub_eq.mpr h.symm)
  have hKN : K ≤ Subgroup.normalizer ((cjSub x K : Subgroup G) : Set G) :=
    le_normalizer_of_mem_cComp hK' hK
  have hc : x * b * x⁻¹ * b⁻¹ ∈ Q := by
    have h1 : b * x⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hbQ x⁻¹).mp (Q.inv_mem hxQ)
    simpa [mul_assoc] using Q.mul_mem hxQ h1
  obtain ⟨s, hs⟩ := hQ ⟨_, hc⟩
  have hcs : (x * b * x⁻¹ * b⁻¹) ^ 2 ^ s = 1 := congrArg Subtype.val hs
  have hu : x * b * x⁻¹ ∈ cjSub x K := by
    rw [mem_cjSub]
    simpa [mul_assoc] using hbK
  have hind : ∀ j : ℕ, (x * b * x⁻¹ * b⁻¹) ^ j * b ^ j ∈ cjSub x K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hbj : (b ^ j)⁻¹ ∈ Subgroup.normalizer ((cjSub x K : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ (Subgroup.pow_mem _ (hKN hbK) j)
      have hw : (b ^ j)⁻¹ * (x * b * x⁻¹) * b ^ j ∈ cjSub x K := by
        have := (Subgroup.mem_normalizer_iff.mp hbj _).mp hu
        simpa using this
      have := (cjSub x K).mul_mem ih hw
      convert this using 1
      simp only [pow_succ]
      group
  have h2s : b ^ 2 ^ s ∈ cjSub x K := by
    have := hind (2 ^ s)
    rwa [hcs, one_mul] at this
  have hbK' : b ∈ cjSub x K := by
    have hcop : Nat.Coprime (2 ^ s) (orderOf b) :=
      Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hbodd)
    obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : b ^ (A * ((2 ^ s : ℕ) : ℤ)) * b ^ (B * (orderOf b : ℤ)) = b := by
      rw [← zpow_add, hAB, zpow_one]
    rw [zpow_mul', zpow_natCast, zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow,
      mul_one] at h1
    rw [← h1]
    exact Subgroup.zpow_mem _ h2s A
  refine mem_solvRad_of_commutator_mem hK hbK fun k hk => ?_
  have h1 : ⁅k⁻¹, b⁻¹⁆ ∈ solvRad H :=
    commutator_le_solvRad_of_ne hK hK' hne
      (Subgroup.commutator_mem_commutator (K.inv_mem hk) ((cjSub x K).inv_mem hbK'))
  have h2 : ⁅k⁻¹, b⁻¹⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hk) (K.inv_mem hbK))
      (K.inv_mem (K.inv_mem hk))) (K.inv_mem (K.inv_mem hbK))
  have h3 := inf_solvRad_le_solvRad (le_of_mem_cComp hK) ⟨h2, h1⟩
  simpa [commutatorElement_def] using h3

end CFSG.Quasithin
