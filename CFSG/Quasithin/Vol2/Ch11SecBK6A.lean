module

public import CFSG.Quasithin.Vol2.Ch11SecBK2J
public import CFSG.Quasithin.Vol2.Ch11SecBK7G
public import CFSG.Quasithin.Vol2.Ch11SecA14Delta

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem isPGroup_cLT (hfl : Flag24 L V X T V₁ V₂ n) :
    IsPGroup 2 ↥((LOf L V₂ ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := hfl.sylow.2.1
  have hN : LOf L V₂ ⊔ T ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
    (K7.lOf_sup_le hfl).trans inf_le_right
  have hq := B6.isTwoQuotient_of_sup_eq hT2 hN (sup_comm T (LOf L V₂))
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  intro x
  obtain ⟨k, hk⟩ := hq x (Subgroup.mem_inf.mp x.2).1
  have hxk : (x : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨hL₂L hk, Subgroup.pow_mem _ (Subgroup.mem_inf.mp x.2).2 _⟩
  obtain ⟨j, hj⟩ := hfl.cL_two ⟨_, hxk⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, hj']

omit [Finite G] in
theorem conj_mem_centralizer {h y : G} (hh : h ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    h * y * h⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have h1 : h⁻¹ * v * h ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) v).mp hv
    rwa [inv_inv] at this
  have h2 := hy _ h1
  calc v * (h * y * h⁻¹) = h * ((h⁻¹ * v * h) * y) * h⁻¹ := by group
    _ = h * (y * (h⁻¹ * v * h)) * h⁻¹ := by rw [h2]
    _ = h * y * h⁻¹ * v := by group

theorem cLT_le_r2 (hfl : Flag24 L V X T V₁ V₂ n) :
    (LOf L V₂ ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (LOf L V₂ ⊔ T) := by
  have key : ∀ h ∈ LOf L V₂ ⊔ T, ∀ y ∈ (LOf L V₂ ⊔ T) ⊓ Subgroup.centralizer (V : Set G),
      h * y * h⁻¹ ∈ (LOf L V₂ ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun h hh y hy =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hy.1) (Subgroup.inv_mem _ hh),
      conj_mem_centralizer ((K7.lOf_sup_le hfl) hh).1.1.1 hy.2⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun h hh => ?_)
    (isPGroup_cLT hfl)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key h hh x hx, fun hx => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hx
  simpa [mul_assoc] using this

theorem pCoreOf_lOf_le_r2 (hfl : Flag24 L V X T V₁ V₂ n) :
    pCoreOf 2 (LOf L V₂) ≤ pCoreOf 2 (LOf L V₂ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact ((K7.lOf_sup_le hfl).trans inf_le_right).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem mem_r2_of_conjV (hfl : Flag24 L V X T V₁ V₂ n) {a : G} (ha : a ∈ LOf L V₂ ⊔ T)
    (haV : a ∈ Subgroup.normalizer (V : Set G))
    (h : SecA.conjV V a haV ∈
      pCoreOf 2 (perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V)))) :
    a ∈ pCoreOf 2 (LOf L V₂ ⊔ T) := by
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  rw [← SecA.autOn_lOf hfl.le_normalizer hfl.le₂,
    ← SecA.autOn_pCoreOf (hL₂L.trans hfl.le_normalizer)
      (hfl.cL_two.to_le (inf_le_inf_right _ hL₂L))] at h
  obtain ⟨l, hl, hlV, hEq⟩ := SecA.mem_autOn_iff.mp h
  have hlL₂ : l ∈ LOf L V₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hl
  have hc : l⁻¹ * a ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hEq
    simp only [SecA.conjV_apply_coe] at h1
    calc v * (l⁻¹ * a) = l⁻¹ * (l * v * l⁻¹) * a := by group
      _ = l⁻¹ * (a * v * a⁻¹) * a := by rw [h1]
      _ = l⁻¹ * a * v := by group
  have hmem : l⁻¹ * a ∈ pCoreOf 2 (LOf L V₂ ⊔ T) :=
    cLT_le_r2 hfl ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_sup_left (α := Subgroup G) hlL₂))
      ha, hc⟩
  have := Subgroup.mul_mem _ (pCoreOf_lOf_le_r2 hfl hl) hmem
  rwa [mul_inv_cancel_left] at this

omit [Finite G] in
theorem autOn_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : autOn Y V ≤ autOn Y' V :=
  CFSG.Quasithin.AutOn.autOn_mono h

omit [Finite G] in
theorem isPGroup_autOn {Y : Subgroup G} (hY : IsPGroup 2 ↥Y) : IsPGroup 2 ↥(autOn Y V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hY

theorem autOn_le_sylow (hfl : Flag24 L V X T V₁ V₂ n) {A : Subgroup G} (hAT : A ≤ T)
    (hAL : autOn A V ≤ autOn L V) : autOn A V ≤ autOn (T ⊓ L) V := by
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  have hP := SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL'
  have hQ2 : IsPGroup 2 ↥(autOn T V ⊓ autOn L V) :=
    (isPGroup_autOn hfl.sylow.2.1).to_le inf_le_left
  have hQ := QuasithinUnique.IsSylowTwoOf.eq_of_le hP
    (le_inf (autOn_mono inf_le_left) (autOn_mono inf_le_right)) inf_le_right hQ2
  rw [← hQ]
  exact le_inf (autOn_mono hAT) hAL

theorem aSet_two_of {W : Type*} [CommGroup W] {Y A : Subgroup (MulAut W)} (hn : 2 ≤ n)
    (h : A ∈ E3.aSet n Y) : A ∈ E3.aSet 2 Y :=
  ⟨h.1, h.2.1, h.2.2.1, fun B hB hm => h.2.2.2 B hB (by omega)⟩

theorem autOn_le_of_aSet (hfl : Flag24 L V X T V₁ V₂ n) {A : Subgroup G}
    (hA : autI hfl.elem A ∈ E3.aSet n (autI hfl.elem X)) : autOn A V ≤ autOn L V :=
  factA2InL_holds G L V X n hfl.elem hfl.two_le hfl.le_normalizer hfl.commutator_eq hfl.nat
    hfl.le_X hfl.normalizer_le _ (aSet_two_of hfl.two_le hA)

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
