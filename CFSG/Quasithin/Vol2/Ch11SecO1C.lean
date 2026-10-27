module

public import CFSG.Quasithin.Vol2.Ch11SecO1A
public import CFSG.Quasithin.Vol2.Ch11SecDFacts2
public import CFSG.Quasithin.Vol2.Ch11SecGFacts
public import CFSG.Quasithin.Vol2.KGNatVec
public import CFSG.Quasithin.Vol2.KGNatTI

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Point

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M] {LM : LinModel D K M}

theorem IsCoord.lin_injective {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : D.Gam →* ↥H} {f : W → M} (hf : IsCoord LM H ⊥ π f) (γ : D.Gam) :
    Function.Injective (LM.lin γ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, hf.ker, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hx
  rw [hx, hf.map_one]

variable {L V : Subgroup G} {f : ↥V → M}

theorem card_imgSub (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') (hbij : Function.Bijective f)
    (hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v))
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {U : Subgroup G} (hUV : U ≤ V)
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U) :
    Nat.card (imgSub hLV hmul hbij hlin hC hU) = Nat.card U := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun u : ↥U => (⟨f ⟨u, hUV u.2⟩, ⟨_, u.2, rfl⟩⟩ : imgSub hLV hmul hbij hlin hC hU))
      ⟨?_, ?_⟩)).symm
  · intro u u' h
    have h2 := hbij.1 (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun w : ↥V => (w : G)) h2)
  · rintro ⟨_, ⟨u, hu, rfl⟩⟩
    exact ⟨⟨u, hu⟩, rfl⟩

theorem mem_imgSub_iff (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') (hbij : Function.Bijective f)
    (hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v))
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {U : Subgroup G}
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U) (v : ↥V) :
    f v ∈ imgSub hLV hmul hbij hlin hC hU ↔ (v : G) ∈ U := by
  refine ⟨?_, fun hv => ⟨v, hv, rfl⟩⟩
  rintro ⟨u, hu, hfu⟩
  rw [← hbij.1 hfu]
  exact hu

theorem exists_conj_eq_of_card [Finite G] [Finite K]
    (htr : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ γ : D.Gam, LM.lin γ x = y) [IsMulCommutative ↥V]
    {π : D.Gam →* ↥(autOn L V)} (hf : IsCoord LM (autOn L V) ⊥ π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {P Q : Subgroup G} (hPV : P ≤ V) (hQV : Q ≤ V)
    (hPs : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) P)
    (hQs : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) Q)
    (hPc : Nat.card P = Nat.card K) (hQc : Nat.card Q = Nat.card K) :
    ∃ l ∈ L, P = conjSubgroup Q l := by
  have hbij : Function.Bijective f := ⟨IsCoord.injective_of_bot hf, hf.surj⟩
  have hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v) :=
    fun l hl => (IsCoord.exists_conj hf hLV hl).elim fun γ hγ => ⟨LM.lin γ, hγ⟩
  have : Finite M := Finite.of_surjective f hbij.2
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hne : ∀ {U : Subgroup G}, U ≤ V → Nat.card U = Nat.card K →
      ∃ u : ↥V, (u : G) ∈ U ∧ f u ≠ 0 := by
    intro U hUV hU
    have hU1 : U ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hU
      omega
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    refine ⟨⟨u, hUV u.2⟩, u.2, fun h0 => hu1 ?_⟩
    rw [← hf.map_one] at h0
    have h1 := congrArg Subtype.val (hbij.1 h0)
    exact Subtype.ext h1
  obtain ⟨p, hpP, hp0⟩ := hne hPV hPc
  obtain ⟨q, hqQ, hq0⟩ := hne hQV hQc
  have hSP := eq_span_of_card ((card_imgSub hLV hf.map_mul hbij hlin hC hPV hPs).trans hPc)
    ((mem_imgSub_iff hLV hf.map_mul hbij hlin hC hPs p).mpr hpP) hp0
  have hSQ := eq_span_of_card ((card_imgSub hLV hf.map_mul hbij hlin hC hQV hQs).trans hQc)
    ((mem_imgSub_iff hLV hf.map_mul hbij hlin hC hQs q).mpr hqQ) hq0
  obtain ⟨γ, hγ⟩ := htr (f p) (f q) hp0 hq0
  obtain ⟨l, hl, hlV, -, hact⟩ := IsCoord.exists_mem hf γ
  refine ⟨l, hl, ?_⟩
  ext z
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hz
    have hw : l * z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlV z).mp (hPV hz)
    have h1 := (mem_imgSub_iff hLV hf.map_mul hbij hlin hC hPs ⟨z, hPV hz⟩).mpr hz
    rw [hSP, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : f ⟨_, hw⟩ ∈ imgSub hLV hf.map_mul hbij hlin hC hQs := by
      rw [hact ⟨z, hPV hz⟩ ⟨_, hw⟩ rfl, ← hc, LinearMap.map_smul, hγ, hSQ]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    exact (mem_imgSub_iff hLV hf.map_mul hbij hlin hC hQs ⟨_, hw⟩).mp h2
  · intro hz
    have hzV : z ∈ V := (Subgroup.mem_normalizer_iff.mp hlV z).mpr (hQV hz)
    have h1 := (mem_imgSub_iff hLV hf.map_mul hbij hlin hC hQs ⟨_, hQV hz⟩).mpr hz
    rw [hSQ, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    rw [hact ⟨z, hzV⟩ ⟨_, hQV hz⟩ rfl, ← hγ, ← LinearMap.map_smul] at hc
    have h2 : f ⟨z, hzV⟩ ∈ imgSub hLV hf.map_mul hbij hlin hC hPs := by
      rw [← IsCoord.lin_injective hf γ hc, hSP]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    exact (mem_imgSub_iff hLV hf.map_mul hbij hlin hC hPs ⟨z, hzV⟩).mp h2

end Point

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecD.cardVFact_holds : SecD.CardVFact := by
  intro G _ _ T L I n hS
  have := isMulCommutative hS
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sl3 hS hk
    rw [Nat.card_congr (Equiv.ofBijective f ⟨IsCoord.injective_of_bot hf, hf.surj⟩), Nat.card_fun,
      Nat.card_fin, hK, ← pow_mul, mul_comm]
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sp4 hS hk
    rw [Nat.card_congr (Equiv.ofBijective f ⟨IsCoord.injective_of_bot hf, hf.surj⟩), Nat.card_fun,
      Nat.card_sum, Nat.card_fin, hK, ← pow_mul, mul_comm]

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecG.pointConjFact_holds : SecG.PointConjFact := by
  intro G _ _ T L I n V₁ P hS hk hV₁ hPV hPs hPc
  have := isMulCommutative hS
  obtain ⟨⟨-, hV₁V, hst, hidx, -⟩, -⟩ := hV₁
  have hcard : Nat.card V₁ = 2 ^ n := by
    rw [hS.cV, Subgroup.relIndex_bot_left, mul_one] at hidx
    exact hidx
  rcases hk with hk | hk
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sl3 hS hk
    exact exists_conj_eq_of_card exists_sl3_lin_eq hf hS.le_normalizer hS.cV hPV hV₁V hPs hst
      (hPc.trans hK.symm) (hcard.trans hK.symm)
  · obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sp4 hS hk
    exact exists_conj_eq_of_card exists_sp4_lin_eq hf hS.le_normalizer hS.cV hPV hV₁V hPs hst
      (hPc.trans hK.symm) (hcard.trans hK.symm)

end CFSG.Quasithin.Vol2.Ch11.SecO1
