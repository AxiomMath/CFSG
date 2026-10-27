module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LKey
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Fx
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Core
public import CFSG.Quasithin.EmptyFaithful.S146zClaim
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.ThreeC
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem centralizerMod_inf_eq {Z U : Subgroup G} (c : G) (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hcU : c ∈ Subgroup.normalizer (U : Set G)) :
    centralizerMod (Z ⊓ U) U (Subgroup.zpowers c) = centralizerMod Z U (Subgroup.zpowers c) := by
  have hz : Subgroup.zpowers c ≤ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.mpr hcU
  ext u
  rw [mem_centralizerMod, mem_centralizerMod]
  constructor
  · rintro ⟨huU, -, hu⟩
    exact ⟨huU, hUZ huU, fun s hs => (Subgroup.mem_inf.mp (hu s hs)).1⟩
  · rintro ⟨huU, huZ, hu⟩
    refine ⟨huU, ?_, fun s hs => Subgroup.mem_inf.mpr ⟨hu s hs, ?_⟩⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.mp huZ h)
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer huU) h)
    · have h1 : s * u⁻¹ * s⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hz hs) u⁻¹).mp (U.inv_mem huU)
      have e : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
      rw [e]
      exact U.mul_mem huU h1

theorem a2_ksBounds
    (hG1 : Leaf_G1) (hG2 : Leaf_G2) (hG3 : Leaf_G3)
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T →
      4 ≤ a2Off (a2Z T) (a2UH L T H K) (Subgroup.zpowers r)) ∧
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T ⊔ K → r ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom →
      5 ≤ a2Off (a2Z T) (a2UH L T H K) (Subgroup.zpowers r)) := by
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  have hUT : a2UH L T H K ≤ a2TC K T := c.UH_le_TC h5 h7 h9 h128 h37 h38 h39
  have hTCX : a2TC K T ≤ a2G2 K T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hUX : a2UH L T H K ≤ a2G2 K T := hUT.trans hTCX
  have hXU : a2G2 K T ≤ Subgroup.normalizer (a2UH L T H K : Set G) :=
    le_normalizer_conjClosure (⁅vPlus L T, oTwoUpper H⁆) (conjClosure K T ⊔ T)
  have hG2Z : a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36
  have hZN : a2G2 K T ≤ Subgroup.normalizer (a2Z T : Set G) :=
    hG2Z.trans (Subgroup.centralizer_le_normalizer _)
  have hKX : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  have hx : ∃ u ∈ a2UH L T H K, x * u * x⁻¹ * u⁻¹ ∉ a2Z T ⊓ a2UH L T H K := by
    by_contra hcon
    push Not at hcon
    have hxC : x ∈ centralizerMod (a2Z T) (a2G2 K T) (⁅vPlus L T, oTwoUpper H⁆) := by
      refine ⟨hKX hxK, hZN (hKX hxK), fun u hu => ?_⟩
      exact (Subgroup.mem_inf.mp (hcon u (le_conjClosure (⁅vPlus L T, oTwoUpper H⁆)
        (conjClosure K T ⊔ T) hu))).1
    have hb : Subgroup.zpowers x ≤
        centralizerMod (a2Z T) (a2G2 K T) (⁅vPlus L T, oTwoUpper H⁆) := Subgroup.zpowers_le.mpr hxC
    apply c.not_comm_le_Z (leaf_LSCV_of h7 h9 hGA) hxY hx3
    rw [Subgroup.commutator_le]
    intro u hu b hb'
    have h1 := (mem_centralizerMod.mp (hb hb')).2.2 u hu
    have e : ⁅u, b⁆ = (b * u * b⁻¹ * u⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (a2Z T).inv_mem h1
  have hkey := a2_keyBounds hG1 hG2 hG3 h5 h7 h9 h128 h37 h38 h39 c ht htK
    (A := a2UH L T H K) (Z₀ := a2Z T ⊓ a2UH L T H K) (hUX |> fun _ =>
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (a2G2 K T)).to_le hUT) hUX hXU
    (F7.le_normalizer_inf hZN hXU) inf_le_right hxK (by rw [hx3]; decide) hx
  have hnorm : ∀ r ∈ pCoreOf 2 H, r ∈ Subgroup.normalizer (a2UH L T H K : Set G) := fun r hr =>
    hXU (c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H hr))
  have hUZ : a2UH L T H K ≤ Subgroup.normalizer (a2Z T : Set G) := hUX.trans hZN
  refine ⟨fun r hr hrT => ?_, fun r hr h1 h2 => ?_⟩
  · have := hkey.1 r hr hrT
    rw [centralizerMod_inf_eq r hUZ (hnorm r hr)] at this
    exact this
  · have := hkey.2 r hr h1 h2
    rw [centralizerMod_inf_eq r hUZ (hnorm r hr)] at this
    exact this

theorem leaf_KS1_of
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_KS1 := by
  intro hG1 hG2 hG3 G _ _ T M L D H K q c _ r hr hrT
  obtain ⟨t, ht, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.nf.TK hcon
  have := (a2_ksBounds hG1 hG2 hG3 h36 h5 h7 h9 hGA h128 h37 h38 h39 c ht htK).1 r hr hrT
  omega

theorem leaf_KS2_of
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_KS2 := by
  intro hG1 hG2 hG3 G _ _ T M L D H K q c _
  obtain ⟨t, ht, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.nf.TK hcon
  obtain ⟨a, hd⟩ := c.exists_AData h5 h7 h9 h128 h37 h38 h39 ht
  obtain ⟨c₀, hc₀R, hc₀1, hc₀2⟩ := hd.exists_type_two h37 h38 ht htK
  have h5' := (a2_ksBounds hG1 hG2 hG3 h36 h5 h7 h9 hGA h128 h37 h38 h39 c ht htK).2 c₀ hc₀R hc₀1 hc₀2
  have hle : Subgroup.zpowers c₀ ≤ a2R H := Subgroup.zpowers_le.mpr hc₀R
  exact h5'.trans (mIdx_anti_of_le (centralizerMod_anti_right _ hle))

end CFSG.Quasithin.H13.NFa2
