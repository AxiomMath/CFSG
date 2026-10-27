module

public import CFSG.Quasithin.Background.F918P6
public import CFSG.Quasithin.Background.B1MoreElevenC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section SecPre

variable {G : Type*} [Group G] (A B : Subgroup G) [(B.subgroupOf A).Normal]

@[expose] def secPre (Y : Subgroup (SecQuot A B)) : Subgroup G :=
  (Y.comap (secMk A B)).map A.subtype

variable {A B}

theorem mem_secPre {Y : Subgroup (SecQuot A B)} {g : G} :
    g ∈ secPre A B Y ↔ ∃ a : A, (a : G) = g ∧ secMk A B a ∈ Y := by
  simp only [secPre, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, h, ha⟩, fun ⟨a, h, ha⟩ => ⟨a, ha, h⟩⟩

theorem secImg_secPre (Y : Subgroup (SecQuot A B)) : secImg A B (secPre A B Y) = Y := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := mem_secImg.1 hy
    obtain ⟨a', ha', hY⟩ := mem_secPre.1 ha
    have : a' = a := Subtype.ext ha'
    rw [← this]
    exact hY
  · intro hy
    obtain ⟨a, rfl⟩ := secMk_surjective (A := A) (B := B) y
    exact secMk_mem_secImg (mem_secPre.2 ⟨a, rfl, hy⟩)

theorem le_secPre (hBA : B ≤ A) (Y : Subgroup (SecQuot A B)) : B ≤ secPre A B Y := by
  intro b hb
  refine mem_secPre.2 ⟨⟨b, hBA hb⟩, rfl, ?_⟩
  rw [(secMk_eq_one_iff (A := A) (B := B) (x := ⟨b, hBA hb⟩)).2 hb]
  exact Y.one_mem

theorem secPre_le {X : Subgroup G} (hBX : B ≤ X) {Y : Subgroup (SecQuot A B)}
    (hY : Y ≤ secImg A B X) : secPre A B Y ≤ X := by
  intro g hg
  obtain ⟨a, rfl, ha⟩ := mem_secPre.1 hg
  exact (secMk_mem_secImg_iff hBX).1 (hY ha)

end SecPre

section Existence

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem exists_isIrrPlusTildeU (h : HypF918 T V L V₁ Vp H K) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ I ≤ conjClosure Vp H ∧
      ∃ W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)),
        (∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) ∧ IsIrrPlusTildeU h I W := by
  have hF := factElem h (le_conjClosure Vp H)
  have hperf : ⁅autIH V₁ Vp H (conjClosure K T), autIH V₁ Vp H (conjClosure K T)⁆ =
      autIH V₁ Vp H (conjClosure K T) := by
    rw [autIH_eq_map h h.K₀_le_H]
    have hA : ⁅(conjClosure K T).subgroupOf H, (conjClosure K T).subgroupOf H⁆ =
        (conjClosure K T).subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.K₀_le_H, h.K₀_perfect]
    rw [← Subgroup.map_commutator, hA]
  have hne : commV (autIH V₁ Vp H (conjClosure K T)) ≠ ⊥ := by
    intro h0
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h0
    have hK₀ : conjClosure K T ≤ pCoreOf 2 H := by
      intro k hk
      have hkH : k ∈ H := h.K₀_le_H hk
      refine mem_pCoreOf_of_actH_eq_one h (x := ⟨k, hkH⟩) ?_
      refine MulEquiv.ext fun w => ?_
      rw [MulAut.one_apply]
      refine h0 (Subgroup.mem_top w) _ ?_
      rw [autIH_eq_map h h.K₀_le_H]
      exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKp : IsPGroup 2 ↥K :=
      (pCoreOf_isPGroup 2 H).to_le ((le_conjClosure K T).trans hK₀)
    have : Group.IsNilpotent ↥K := hKp.isNilpotent
    exact not_isSolvable_of_mem_cComp h.K_cComp inferInstance
  obtain ⟨I₀, hI₀⟩ := B1Red.exists_mem_irrPlus hperf hne
  have hTH : T ≤ H := h.T_le_H
  have hT2 : IsPGroup 2 ↥(autIH V₁ Vp H T) := by
    rw [autIH_eq_map h hTH]
    exact (h.sylow_H.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  have hV : ∀ v : ↥(tildeOf V₁ (conjClosure Vp H)), v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))).2
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
    simpa using this
  obtain ⟨I', hI'⟩ := irrPlusOn_nonempty hV (autIH_T_le_normalizer h Vp) hT2 hI₀
  have hV₁U : V₁ ≤ conjClosure Vp H := h.toHypF98.toHypF91.V₁_le_Vp.trans (le_conjClosure Vp H)
  set Y : Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) :=
    I'.map (tildeOf V₁ (conjClosure Vp H)).subtype with hY
  have hYU : Y ≤ tildeOf V₁ (conjClosure Vp H) := Subgroup.map_subtype_le _
  have hsub : subM V₁ (conjClosure Vp H) (secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y) =
      I' := by
    unfold subM tildeOf
    rw [secImg_secPre]
    exact map_subtype_subgroupOf' I'
  refine ⟨secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y, le_secPre Subgroup.le_normalizer Y,
    secPre_le hV₁U hYU, ⨆ y ∈ autIH V₁ Vp H T, y • I₀,
    fun t ht w hw => smul_mem_biSup_smul ht hw, ?_⟩
  show subM V₁ (conjClosure Vp H) _ ∈ _
  rw [hsub]
  exact hI'

end Existence

end CFSG.Quasithin
