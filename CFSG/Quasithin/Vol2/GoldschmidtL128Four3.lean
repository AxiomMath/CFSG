module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Four1
public import CFSG.Quasithin.Vol2.GoldschmidtL128Four2
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L128Four

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem le_normalizer_conjClosure_of {Z H K : Subgroup G}
    (hZ : K ≤ Subgroup.normalizer (Z : Set G)) (hH : K ≤ Subgroup.normalizer (H : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ conjClosure Z H, k * x * k⁻¹ ∈ conjClosure Z H := by
    intro k hk x hx
    refine conjClosure_le (K := (conjClosure Z H).comap (MulAut.conj k).toMonoidHom)
      (fun h hh z hz => ?_) hx
    show k * (h * z * h⁻¹) * k⁻¹ ∈ conjClosure Z H
    have e : k * (h * z * h⁻¹) * k⁻¹ = (k * h * k⁻¹) * (k * z * k⁻¹) * (k * h * k⁻¹)⁻¹ := by group
    rw [e]
    exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp (hH hk) h).mp hh)
      ((Subgroup.mem_normalizer_iff.mp (hZ hk) z).mp hz)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨key k hk x, fun hx => ?_⟩
  have h := key k⁻¹ (K.inv_mem hk) _ hx
  have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [e] at h

omit [Finite G] in
theorem autOn_eq_of_normal [IsSimpleGroup ↥(autOn L V)] {X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hAB : autOn X V ≤ autOn L V)
    (hXn : L ≤ Subgroup.normalizer (X : Set G)) (hX1 : ¬ X ≤ Subgroup.centralizer (V : Set G)) :
    autOn X V = autOn L V := by
  set A' := (autOn X V).subgroupOf (autOn L V) with hA'
  have hn : A'.Normal := by
    refine ⟨fun φ hφ ψ => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hφ ⊢
    obtain ⟨⟨x, hxN⟩, hxX, hx⟩ := hφ
    obtain ⟨⟨l, hlN⟩, hlL, hl⟩ := ψ.2
    refine ⟨⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hXn hlL) x).mp hxX
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hx, hl]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A' with hb | ht
  · exfalso
    apply hX1
    intro x hxX
    have hmemB : conjAct V ⟨x, hXV hxX⟩ ∈ autOn X V := ⟨⟨x, hXV hxX⟩, hxX, rfl⟩
    have hmem : (⟨conjAct V ⟨x, hXV hxX⟩, hAB hmemB⟩ : ↥(autOn L V)) ∈ A' :=
      Subgroup.mem_subgroupOf.mpr hmemB
    rw [hb, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val hmem)
  · refine le_antisymm hAB fun φ hφ => ?_
    have : (⟨φ, hφ⟩ : ↥(autOn L V)) ∈ A' := by rw [ht]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem le_conjClosure_u128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) (hn : n = 3) : L ≤ conjClosure (u128 V V₁) L := by
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hs.almostSpecial h1222 h12213
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hs.hyp.hyp.irrPlus.2.2.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := (isTwoReducedIn h1222 hs.hyp).2.1
  have hUT : u128 V V₁ ≤ T := hA.G22_three.1
  obtain ⟨hc, hnat⟩ := hs.hyp.natural
  have hsimple : IsSimpleGroup ↥(autOn L V) := isSimpleGroup_of_binaryNaturalSL hnat
  have hIT : conjClosure (u128 V V₁) L ≤ L ⊔ T := conjClosure_le fun l hl z hz =>
    mul_mem (mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (hUT hz)))
      (inv_mem (Subgroup.mem_sup_left hl))
  have hLI : L ≤ Subgroup.normalizer (conjClosure (u128 V V₁) L : Set G) :=
    le_normalizer_conjClosure _ _
  have hTI : T ≤ Subgroup.normalizer (conjClosure (u128 V V₁) L : Set G) :=
    le_normalizer_conjClosure_of (hA.T_le_normV₁.trans (le_normalizer_conjClosure V _))
      hA.T_le_normL
  have hLT : autOn (L ⊔ T) V ≤ autOn L V := by
    rw [← (lemma12_8_3 h12213 G T L V 3 hs.hyp).1.2]
    exact A4.autOn_mono (le_inf (sup_le Subgroup.le_normalizer hA.T_le_normL) hLTV)
  have hB : autOn (conjClosure (u128 V V₁) L) V = autOn L V :=
    autOn_eq_of_normal (hIT.trans hLTV) ((A4.autOn_mono hIT).trans hLT) hLI
      fun h => not_U_le_centralizer h1222 h12213 hs ((le_conjClosure _ _).trans h)
  have hpow : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ conjClosure (u128 V V₁) L := by
    intro x hx
    have hmem : conjAct V ⟨x, hLV hx⟩ ∈ autOn (conjClosure (u128 V V₁) L) V := by
      rw [hB]
      exact ⟨⟨x, hLV hx⟩, hx, rfl⟩
    obtain ⟨⟨y, hyN⟩, hyI, hy⟩ := hmem
    have hyx : y⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : conjAct V ((⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨x, hLV hx⟩) =
          1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have hyxR : y⁻¹ * x ∈ pCoreOf 2 (L ⊔ T) :=
      inf_centralizer_le_pCoreOf h1222 hs.hyp
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hIT hyI)) (Subgroup.mem_sup_left hx), hyx⟩
    have hxIR : x ∈ conjClosure (u128 V V₁) L ⊔ pCoreOf 2 (L ⊔ T) := by
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left hyI) (Subgroup.mem_sup_right hyxR)
    exact L1286.exists_two_pow_mem_of_mem_sup (LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
      ((pCoreOf_two_le_of_isSylowTwoOf hA.sylow_LT).trans hTI) hxIR
  calc L = oTwoUpper L := hA.oTwo_eq
    _ ≤ conjClosure (u128 V V₁) L := oTwoUpper_le_of_pow_mem hpow

theorem almostSpecialL3Hyp (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) (hn : n = 3) :
    AlmostSpecialL3Hyp 1 V V₁ L T (Subgroup.normalizer (V₁ : Set G)) := by
  subst hn
  obtain ⟨hc, K, hF, hfin, hK, π, hπ⟩ := hs.hyp.natural
  refine ⟨hs.almostSpecial h1222 h12213, one_pos, V_eq_conjClosure h12213 hs, ?_,
    not_U_le_pCoreOf h1222 h12213 hs⟩
  have h := inf_centralizer_eq_inf_pCoreOf h1222 hs.hyp
  refine isNaturalSL3Module_of_realizes hs.hyp.hyp.irrPlus.2.2.1 (by simpa using hK) π hπ
    (fun a ha => ?_) hs.v1.1 (by simpa using hs.v1.2.1)
  have h1 : a ∈ L ⊓ Subgroup.centralizer (V : Set G) ↔ a ∈ L ⊓ pCoreOf 2 (L ⊔ T) := by rw [h]
  exact ⟨fun h2 => (h1.mp ⟨ha, h2⟩).2, fun h2 => (h1.mpr ⟨ha, h2⟩).2⟩

end L128Four

theorem lemma12_8_8_four_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_8_four := by
  intro G _ _ T L V n V₁ V₂ hs hn
  have hn3 : n = 3 := by rcases hs.hyp.n_mem with h | h | h <;> omega
  exact ⟨L128Four.le_conjClosure_u128 h1222 h12213 hs hn3,
    L128Four.almostSpecialL3Hyp h1222 h12213 hs hn3⟩

end CFSG.Quasithin.H13
