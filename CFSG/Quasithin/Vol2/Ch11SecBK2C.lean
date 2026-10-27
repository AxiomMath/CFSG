module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts24
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecAVi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open scoped IsMulCommutative

namespace BK2

section Lin

variable {D : FFModel} {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]
  {G : Type} [Group G] [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]
  {LM : KGNat.LinModel D K M} {π : D.Gam →* ↥(autOn L V)} {f : ↥V → M}

omit [Finite K] [Finite G] in
theorem lin_injective {Z : Subgroup ↥V} (hf : KGNat.IsCoord LM (autOn L V) Z π f) (γ : D.Gam) :
    Function.Injective (LM.lin γ) := by
  have hleft : ∀ x, LM.lin γ⁻¹ (LM.lin γ x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← hf.act, ← hf.act, ← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel,
      map_one, Subgroup.coe_one, MulAut.one_apply]
  exact Function.LeftInverse.injective hleft

omit [Finite G] in
theorem exists_line
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    (hsq : ∀ w : ↥V, w ^ 2 = 1) (hLV : L ≤ Subgroup.normalizer (V : Set G)) {U : Subgroup G}
    (hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤ U) (hUV : U ≤ V)
    (hst : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U)
    (hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = Nat.card K) :
    ∃ u₀ : M, u₀ ≠ 0 ∧ ∀ w : ↥V, (w : G) ∈ U ↔ ∃ c : K, f w = c • u₀ := by
  have hZU : (Subgroup.centralizer (L : Set G)).subgroupOf V ≤ U.subgroupOf V :=
    fun z hz => hCU ⟨z.2, hz⟩
  have hst' : SecA.EndStableW (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V)
      (U.subgroupOf V) := by
    have := (SecA.isEndStable_iff hLV _ U).mp hst
    rwa [SecA.inf_centralizer_subgroupOf] at this
  have hsc := (hf.endStableW_iff hsq hcomm hZU).mp hst'
  have hcard : Nat.card (hf.img (U.subgroupOf V)) = Nat.card K := by
    rw [hf.card_img, ← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx]
  have h1K : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨u₀, hu₀, hne⟩ : ∃ u₀ ∈ hf.img (U.subgroupOf V), u₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : hf.img (U.subgroupOf V) = ⊥ := (AddSubgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, AddSubgroup.card_bot] at hcard
    omega
  let φ : K → ↥(hf.img (U.subgroupOf V)) := fun c => ⟨c • u₀, hsc c u₀ hu₀⟩
  have hφ : Function.Injective φ := by
    intro c c' h
    have h1 : (c - c') • u₀ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact congrArg Subtype.val h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hne)
  have : Finite ↥(hf.img (U.subgroupOf V)) := Nat.finite_of_card_ne_zero (by omega)
  have hφs : Function.Surjective φ :=
    (hφ.bijective_of_nat_card_le hcard.le).2
  refine ⟨u₀, hne, fun w => ?_⟩
  rw [show (w : G) ∈ U ↔ w ∈ U.subgroupOf V from Iff.rfl, hf.mem_iff hZU]
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hφs ⟨f w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, hc⟩
    rw [hc]
    exact hsc c u₀ hu₀

omit [Finite G] in
theorem exists_conj_eq
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    (htrans : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ γ : D.Gam, LM.lin γ x = y)
    (hsq : ∀ w : ↥V, w ^ 2 = 1) (hLV : L ≤ Subgroup.normalizer (V : Set G)) {U U₁ : Subgroup G}
    (hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤ U) (hUV : U ≤ V)
    (hst : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U)
    (hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = Nat.card K)
    (hCU₁ : V ⊓ Subgroup.centralizer (L : Set G) ≤ U₁) (hU₁V : U₁ ≤ V)
    (hst₁ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U₁)
    (hidx₁ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U₁ = Nat.card K) :
    ∃ l ∈ L, conjSubgroup U l = U₁ := by
  obtain ⟨u₀, hu₀, hU⟩ := exists_line hf hcomm hsq hLV hCU hUV hst hidx
  obtain ⟨v₀, hv₀, hU₁⟩ := exists_line hf hcomm hsq hLV hCU₁ hU₁V hst₁ hidx₁
  obtain ⟨γ, hγ⟩ := htrans v₀ u₀ hv₀ hu₀
  obtain ⟨l, hl, hlV, hlγ⟩ := SecA.mem_autOn_iff.mp (π γ).2
  refine ⟨l, hl, ?_⟩
  ext w
  rw [mem_conjSubgroup_iff]
  by_cases hw : w ∈ V
  · have h1 : l * w * l⁻¹ = (((π γ : ↥(autOn L V)) : MulAut ↥V) ⟨w, hw⟩ : G) := by
      rw [hlγ, SecA.conjV_apply_coe]
    rw [h1, hU, show w ∈ U₁ ↔ (⟨w, hw⟩ : ↥V).1 ∈ U₁ from Iff.rfl, hU₁, hf.act]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, lin_injective hf γ ?_⟩
      rw [hc, LinearMap.map_smul, hγ]
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, LinearMap.map_smul, hγ]⟩
  · have h1 : l * w * l⁻¹ ∉ V := fun h =>
      hw ((Subgroup.mem_normalizer_iff.mp (hLV hl) w).mpr h)
    exact ⟨fun h => absurd (hUV h) h1, fun h => absurd (hU₁V h) hw⟩

end Lin

end BK2

theorem factPointTrans_holds : FactPointTrans := by
  intro G _ _ L V X T V₁ V₂ n hfl U hCU hUV hst hidx
  obtain ⟨_, hnat⟩ := hfl.nat
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hV₁ : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  have hidx₁ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₁ = 2 ^ n := hfl.index₁
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact BK2.exists_conj_eq hf (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT)
      KGNat.exists_sl3_lin_eq hsq hfl.le_normalizer hCU hUV hst (hidx.trans hK.symm)
      hfl.cV_le hV₁ hfl.stable₁ (hidx₁.trans hK.symm)
  · obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact BK2.exists_conj_eq hf (fun T hT => KGNat.commutant_statedSp T hT)
      KGNat.exists_sp4_lin_eq hsq hfl.le_normalizer hCU hUV hst (hidx.trans hK.symm)
      hfl.cV_le hV₁ hfl.stable₁ (hidx₁.trans hK.symm)
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    exact BK2.exists_conj_eq hf
      (fun T hT => G2Q8.commutant_g2Derived hc0 hc1 G2Q8.g2Derived_le T hT)
      (fun x y hx hy => KGNat.exists_g2_lin_eq hc0 hc1 x y hx hy) hsq hfl.le_normalizer hCU
      hUV hst (hidx.trans hK.symm) hfl.cV_le hV₁ hfl.stable₁ (hidx₁.trans hK.symm)

end CFSG.Quasithin.Vol2.Ch11.SecB
