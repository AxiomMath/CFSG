module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFData
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFTwist
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFLemC
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFlipD

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k n j : ℕ}

@[expose] def FlipProp (D : StdData G T L I K m k n j) (g : G)
    (U : AddSubgroup (Fin n → ZMod 2)) (ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2))
    (θ : (Fin n → ZMod 2) → (Fin j → ZMod 2)) : Prop :=
  ∀ u ∈ U, ∀ x : Fin j → ZMod 2, ∀ c ∈ uZero I K, coG D c = tens u x →
    g * c * g⁻¹ ∈ uZero I K ∧ coG D (g * c * g⁻¹) = tens (ι x) (θ u)

theorem exists_flip_group (h22 : ASC22Three G) (hc : Conf4212 G T M L I H K) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hn : 0 < n) (hn5 : n ≤ 5) (hj3 : 3 ≤ j)
    (D : StdData G T L I K m k n j) (hRΓ : pCoreOf 2 I ≤ gammaZero T M L I) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (h3 : ∃ u ∈ uZero I K, g⁻¹ * u * g ∉ kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :
    ∃ (U : AddSubgroup (Fin n → ZMod 2)) (ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2))
      (θ : (Fin n → ZMod 2) → (Fin j → ZMod 2)),
      Nat.card U = 2 ^ j ∧ Function.Injective ι ∧ FlipProp D g U ι θ := by
  have hP0 := exists_nonfix_of_h3 h22 hc hIH hHK hn (by omega) D hRΓ h1 h3
  obtain ⟨F, hS, hT⟩ := exists_flipHyp hn (by omega) hIH hHK D h1 h2 hP0
  obtain ⟨U, ι, θ, hU, hι, hflip⟩ := F.flip_structure hj3 hn5
  refine ⟨U, ι, θ, hU, hι, fun u hu x c hcU hcc => ?_⟩
  obtain ⟨hSmem, hTeq⟩ := hflip u hu x
  obtain ⟨c', hc', hgc', hcc'⟩ := (hS _).mp hSmem
  have hcc'' : c' = c := coG_injOn D hc' hcU (by rw [hcc', hcc])
  subst hcc''
  refine ⟨hgc', ?_⟩
  have := hT c' hc' hgc'
  rw [hcc, hTeq] at this
  exact this.symm

theorem coG_conjK (D : StdData G T L I K m k n j)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) (x : ↥K) {z : G}
    (hz : z ∈ uZero I K) :
    (x : G) * z * (x : G)⁻¹ ∈ uZero I K ∧
      coG D ((x : G) * z * (x : G)⁻¹) =
        actM ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) (coG D z) := by
  refine ⟨hKU x z hz, ?_⟩
  funext i
  exact coG_conj_K D hz (hKU x z hz) i

section Pure

variable {D : StdData G T L I K m k n j}
  (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) {g : G}
  {U : AddSubgroup (Fin n → ZMod 2)} {ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2)}
  {θ : (Fin n → ZMod 2) → (Fin j → ZMod 2)} (hCF : FlipProp D g U ι θ)
  (κ kk : ↥K) {f : (Fin j → ZMod 2) →+ ZMod 2} {w₀ : Fin j → ZMod 2}

include hKU hCF

theorem z1_pure
    (hκ : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
      ((D.α κ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec a ∈ U)
    (hkk : ∀ x : Fin j → ZMod 2,
      ((D.α kk : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ι x) =
        ι (x + f x • w₀))
    {z₁ : G} (hz₁ : z₁ = (κ : G)⁻¹ * g⁻¹ * (kk : G) * g * (κ : G))
    {a₀ : Fin n → ZMod 2} (ha₀ : ∀ b : Fin n, m ≤ b.val → a₀ b = 0) (x : Fin j → ZMod 2) :
    z₁ * zEn D (tens a₀ x) * z₁⁻¹ ∈ uZero I K ∧
      coG D (z₁ * zEn D (tens a₀ x) * z₁⁻¹) = tens a₀ (x + f x • w₀) := by
  set c := zEn D (tens a₀ x) with hc
  have hcU : c ∈ uZero I K := zEn_mem D _
  have hcc : coG D c = tens a₀ x := coG_zEn D _
  set κ' : Matrix (Fin n) (Fin n) (ZMod 2) :=
    ((D.α κ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) with hκ'
  obtain ⟨hc₁, hcc₁⟩ := coG_conjK D hKU κ hcU
  set c₁ := (κ : G) * c * (κ : G)⁻¹ with hc₁def
  have hcc₁' : coG D c₁ = tens (κ'.mulVec a₀) x := by rw [hcc₁, hcc, actM_tens]
  have huU : κ'.mulVec a₀ ∈ U := hκ a₀ ha₀
  obtain ⟨hc₂, hcc₂⟩ := hCF _ huU x c₁ hc₁ hcc₁'
  set c₂ := g * c₁ * g⁻¹ with hc₂def
  obtain ⟨hc₃, hcc₃⟩ := coG_conjK D hKU kk hc₂
  set c₃ := (kk : G) * c₂ * (kk : G)⁻¹ with hc₃def
  have hcc₃' : coG D c₃ = tens (ι (x + f x • w₀)) (θ (κ'.mulVec a₀)) := by
    rw [hcc₃, hcc₂, actM_tens, hkk x]
  set c₄ := zEn D (tens (κ'.mulVec a₀) (x + f x • w₀)) with hc₄
  have hc₄U : c₄ ∈ uZero I K := zEn_mem D _
  have hcc₄ : coG D c₄ = tens (κ'.mulVec a₀) (x + f x • w₀) := coG_zEn D _
  obtain ⟨hc₅, hcc₅⟩ := hCF _ huU (x + f x • w₀) c₄ hc₄U hcc₄
  have hgc₄ : g * c₄ * g⁻¹ = c₃ := coG_injOn D hc₅ hc₃ (by rw [hcc₅, hcc₃'])
  have hgc₃ : g⁻¹ * c₃ * g = c₄ := by rw [← hgc₄]; group
  obtain ⟨hc₆, hcc₆⟩ := coG_conjK D hKU κ⁻¹ hc₄U
  have hz : z₁ * c * z₁⁻¹ = ((κ⁻¹ : ↥K) : G) * c₄ * ((κ⁻¹ : ↥K) : G)⁻¹ := by
    have : z₁ * c * z₁⁻¹ = (κ : G)⁻¹ * (g⁻¹ * c₃ * g) * (κ : G) := by
      simp only [hz₁, hc₃def, hc₂def, hc₁def]
      group
    rw [this, hgc₃]
    simp
  rw [hz]
  refine ⟨hc₆, ?_⟩
  rw [hcc₆, hcc₄, actM_tens]
  congr 1
  rw [map_inv, Matrix.mulVec_mulVec]
  have h1 : (((D.α κ)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * κ' = 1 := by
    rw [hκ']
    exact Units.inv_mul _
  rw [h1, Matrix.one_mulVec]


theorem z1_conj_B
    (hκ : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
      ((D.α κ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec a ∈ U)
    (hkk : ∀ x : Fin j → ZMod 2,
      ((D.α kk : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ι x) =
        ι (x + f x • w₀))
    {z₁ : G} (hz₁ : z₁ = (κ : G)⁻¹ * g⁻¹ * (kk : G) * g * (κ : G))
    {c : G} (hcU : c ∈ uZero I K) (hcB : ∀ i b, m ≤ b.val → coG D c i b = 0) :
    z₁ * c * z₁⁻¹ ∈ uZero I K ∧ coG D (z₁ * c * z₁⁻¹) = twistM f w₀ (coG D c) := by
  classical
  let Bpure : Set (Fin j → Fin n → ZMod 2) :=
    {Y | ∃ (a : Fin n → ZMod 2) (x : Fin j → ZMod 2), (∀ b : Fin n, m ≤ b.val → a b = 0) ∧
      Y = tens a x}
  have hP : ∀ Y ∈ AddSubgroup.closure Bpure, ∃ c ∈ uZero I K, coG D c = Y ∧
      z₁ * c * z₁⁻¹ ∈ uZero I K ∧ coG D (z₁ * c * z₁⁻¹) = twistM f w₀ Y := by
    intro Y hY
    induction hY using AddSubgroup.closure_induction with
    | mem Y hY =>
      obtain ⟨a, x, ha, rfl⟩ := hY
      obtain ⟨hU', hc'⟩ := z1_pure hKU hCF κ kk hκ hkk hz₁ ha x
      exact ⟨zEn D (tens a x), zEn_mem D _, coG_zEn D _, hU', by rw [hc', twistM_tens]⟩
    | zero =>
      refine ⟨1, one_mem _, coG_one D, by simpa using one_mem _, ?_⟩
      have h1 : z₁ * (1 : G) * z₁⁻¹ = 1 := by group
      rw [h1, coG_one D, twistM_zero]
    | add Y₁ Y₂ _ _ ih₁ ih₂ =>
      obtain ⟨c₁, hc₁, hcc₁, hz₁U, hz₁c⟩ := ih₁
      obtain ⟨c₂, hc₂, hcc₂, hz₂U, hz₂c⟩ := ih₂
      refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, by rw [coG_mul D hc₁ hc₂, hcc₁, hcc₂], ?_, ?_⟩
      · have : z₁ * (c₁ * c₂) * z₁⁻¹ = (z₁ * c₁ * z₁⁻¹) * (z₁ * c₂ * z₁⁻¹) := by group
        rw [this]
        exact mul_mem hz₁U hz₂U
      · have : z₁ * (c₁ * c₂) * z₁⁻¹ = (z₁ * c₁ * z₁⁻¹) * (z₁ * c₂ * z₁⁻¹) := by group
        rw [this, coG_mul D hz₁U hz₂U, hz₁c, hz₂c, twistM_add]
    | neg Y _ ih =>
      obtain ⟨c₁, hc₁, hcc₁, hz₁U, hz₁c⟩ := ih
      refine ⟨c₁, hc₁, hcc₁.trans (tm_neg_eq_self Y).symm, hz₁U, ?_⟩
      rw [hz₁c]
      exact congrArg (twistM f w₀) (tm_neg_eq_self Y).symm
  have hYB : coG D c ∈ AddSubgroup.closure Bpure := by
    have hsum := sum_tens (coG D c)
    rw [hsum]
    refine AddSubgroup.sum_mem _ fun b _ => ?_
    by_cases hb : m ≤ b.val
    · have : (fun i => coG D c i b) = (0 : Fin j → ZMod 2) := by
        funext i
        exact hcB i b hb
      rw [this, tens_zero_right]
      exact AddSubgroup.zero_mem _
    · refine AddSubgroup.subset_closure ⟨_, _, ?_, rfl⟩
      intro b' hb'
      have hne : b' ≠ b := by
        intro h
        subst h
        exact hb hb'
      simp [Pi.single_apply, hne]
  obtain ⟨c', hc', hcc', hU', hc''⟩ := hP _ hYB
  have hcc : c' = c := coG_injOn D hc' hcU hcc'
  subst hcc
  exact ⟨hU', hc''⟩

end Pure


theorem false_of_flip_data (h323 : Lemma323') (hd : NoSumBigData G T M L Mm I H K m k)
    (hVU : vV T L ≤ uZero I K)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) (hn : 0 < n)
    (D : StdData G T L I K m k n j) (hm3 : m = 3) (hj3 : 3 ≤ j) {g : G}
    {U : AddSubgroup (Fin n → ZMod 2)} {ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2)}
    {θ : (Fin n → ZMod 2) → (Fin j → ZMod 2)} (hU : Nat.card U = 2 ^ j)
    (hι : Function.Injective ι) (hCF : FlipProp D g U ι θ)
    {w₀ w₁ : Fin j → ZMod 2} (hw₀ : w₀ ≠ 0) (hw₁ : w₁ ≠ 0) (hw₁₀ : w₁ ≠ w₀)
    (hV₀ : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
      ∃ v ∈ vV T L, coG D v = tens a w₀)
    (hV₁ : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
      ∃ v ∈ vV T L, coG D v = tens a w₁) : False := by
  subst hm3
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨A₁, hA₁, hA₁U⟩ := exists_submodule_finrank_three U hU hj3
  obtain ⟨κ', hκ'⟩ := exists_gl_map_std A₁ hA₁
  obtain ⟨κ, hκ⟩ := D.surj κ'
  obtain ⟨f, hf0, hf1⟩ := exists_functional_sep hw₁ hw₁₀
  obtain ⟨Mgl, hM⟩ := exists_gl_extend_transvection ι hι w₀ f hf0
  obtain ⟨kk, hkk⟩ := D.surj Mgl
  set z₁ : G := (κ : G)⁻¹ * g⁻¹ * (kk : G) * g * (κ : G) with hz₁
  have hκU : ∀ a : Fin n → ZMod 2, (∀ b : Fin n, 3 ≤ b.val → a b = 0) →
      ((D.α κ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec a ∈ U := by
    intro a ha
    rw [hκ]
    exact hA₁U _ (hκ' a ha)
  have hkkι : ∀ x : Fin j → ZMod 2,
      ((D.α kk : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ι x) =
        ι (x + f x • w₀) := by
    intro x
    rw [hkk]
    exact hM x
  have hconj : ∀ c ∈ uZero I K, (∀ i b, 3 ≤ b.val → coG D c i b = 0) →
      z₁ * c * z₁⁻¹ ∈ uZero I K ∧ coG D (z₁ * c * z₁⁻¹) = twistM f w₀ (coG D c) :=
    fun c hcU hcB => z1_conj_B hKU hCF κ kk hκU hkkι hz₁ hcU hcB
  have hVB : ∀ v ∈ vV T L, ∀ i b, 3 ≤ b.val → coG D v i b = 0 := by
    intro v hv i b hb
    have h := D.vcoord ⟨v, hVU hv⟩ hv i b hb
    rw [← coG_of_mem D ⟨v, hVU hv⟩] at h
    exact h
  have hastar : ∀ Y : Fin j → Fin n → ZMod 2, (∀ i b, 3 ≤ b.val → Y i b = 0) →
      ∀ b : Fin n, 3 ≤ b.val → (∑ i, f (Pi.single i 1) • Y i) b = 0 := by
    intro Y hY b hb
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [hY i b hb, smul_zero]
  have hVinv : ∀ v ∈ vV T L, z₁ * v * z₁⁻¹ ∈ vV T L := by
    intro v hv
    obtain ⟨hzU, hzc⟩ := hconj v (hVU hv) (hVB v hv)
    obtain ⟨v', hv'V, hv'c⟩ := hV₀ _ (hastar (coG D v) (hVB v hv))
    have h : z₁ * v * z₁⁻¹ = v * v' :=
      coG_injOn D hzU (mul_mem (hVU hv) (hVU hv'V)) (by
        rw [hzc, coG_mul D (hVU hv) (hVU hv'V), hv'c]
        rfl)
    rw [h]
    exact mul_mem hv hv'V
  have hz₁sq : ∀ v ∈ vV T L, z₁ * (z₁ * v * z₁⁻¹) * z₁⁻¹ = v := by
    intro v hv
    obtain ⟨hzU, hzc⟩ := hconj v (hVU hv) (hVB v hv)
    obtain ⟨hzU', hzc'⟩ := hconj _ hzU (hVB _ (hVinv v hv))
    apply coG_injOn D hzU' (hVU hv)
    rw [hzc', hzc, twistM_twistM f hf0]
  have hnontriv : ∃ v ∈ vV T L, z₁ * v * z₁⁻¹ ≠ v := by
    set a₁ : Fin n → ZMod 2 := Pi.single ⟨0, hn⟩ 1 with ha₁
    have ha₁ne : a₁ ≠ 0 := by
      intro h
      have := congrFun h ⟨0, hn⟩
      simp [ha₁] at this
    have ha₁A : ∀ b : Fin n, 3 ≤ b.val → a₁ b = 0 := by
      intro b hb
      have hne : b ≠ ⟨0, hn⟩ := by
        intro h
        subst h
        simp at hb
      simp [ha₁, Pi.single_apply, hne]
    obtain ⟨v₁, hv₁V, hv₁c⟩ := hV₁ a₁ ha₁A
    refine ⟨v₁, hv₁V, fun heq => ?_⟩
    obtain ⟨hzU, hzc⟩ := hconj v₁ (hVU hv₁V) (hVB v₁ hv₁V)
    rw [heq, hv₁c, twistM_tens, hf1, one_smul] at hzc
    have h1 : w₁ + w₀ = w₁ := tens_right_injective ha₁ne hzc.symm
    exact hw₀ (by simpa using h1)
  have hcommV : ∀ a ∈ perfectCore (L ⊓ H), ∀ t ∈ vV T L,
      z₁ * (a * t * a⁻¹) * z₁⁻¹ = a * (z₁ * t * z₁⁻¹) * a⁻¹ := by
    intro a ha t ht
    have haK : a ∈ K := hc.LH_le ha
    set a' : ↥K := ⟨a, haK⟩ with ha'
    have haN := hc.LH_le_normalizer_V ha
    have hat : a * t * a⁻¹ ∈ vV T L := (Subgroup.mem_normalizer_iff.mp haN t).mp ht
    obtain ⟨h1U, h1c⟩ := coG_conjK D hKU a' (hVU ht)
    obtain ⟨h2U, h2c⟩ := hconj (a * t * a⁻¹) h1U (hVB _ hat)
    obtain ⟨h3U, h3c⟩ := hconj t (hVU ht) (hVB t ht)
    obtain ⟨h4U, h4c⟩ := coG_conjK D hKU a' h3U
    apply coG_injOn D h2U h4U
    rw [h2c, h1c, h4c, h3c, twistM_actM]
  have hz₁N : z₁ ∈ Subgroup.normalizer (vV T L : Set G) := A4.mem_normalizer_of_conj_mem hVinv
  have hzL : ∀ l ∈ L, ⁅z₁, l⁆ ∈ Subgroup.centralizer (vV T L : Set G) := by
    intro l hl
    obtain ⟨a, haLH, ha⟩ := hc.exists_act_L hl
    have haN := hc.LH_le_normalizer_V haLH
    have hlN : l ∈ Subgroup.normalizer (vV T L : Set G) :=
      A4.mem_normalizer_of_conj_mem (fun t ht => by
        rw [ha t ht]
        exact (Subgroup.mem_normalizer_iff.mp haN t).mp ht)
    refine comm_centralizes_nsbkfd hz₁N hlN (fun t ht => ?_)
    have hz₁t : z₁ * t * z₁⁻¹ ∈ vV T L := hVinv t ht
    calc (z₁ * l) * t * (z₁ * l)⁻¹ = z₁ * (l * t * l⁻¹) * z₁⁻¹ := by group
      _ = z₁ * (a * t * a⁻¹) * z₁⁻¹ := by rw [ha t ht]
      _ = a * (z₁ * t * z₁⁻¹) * a⁻¹ := hcommV a haLH t ht
      _ = l * (z₁ * t * z₁⁻¹) * l⁻¹ := (ha _ hz₁t).symm
      _ = (l * z₁) * t * (l * z₁)⁻¹ := by group
  obtain ⟨e, he, hze⟩ := h323 G T M L Mm I H K 3 k hd z₁ hz₁N hzL
  have hsq : z₁ ^ 2 ∈ Subgroup.centralizer (vV T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hz₁sq v hv
    have h2 : (z₁ * z₁) * v * (z₁ * z₁)⁻¹ = v := by
      calc (z₁ * z₁) * v * (z₁ * z₁)⁻¹ = z₁ * (z₁ * v * z₁⁻¹) * z₁⁻¹ := by group
        _ = v := h
    have h3 : (z₁ * z₁) * v = v * (z₁ * z₁) := mul_inv_eq_iff_eq_mul.mp h2
    rw [pow_two]
    exact h3.symm
  obtain ⟨f', rfl⟩ := he
  have hyC : z₁ ∈ Subgroup.centralizer (vV T L : Set G) := by
    have e1 : z₁ = z₁ ^ (2 * f' + 1) * (z₁ ^ 2)⁻¹ ^ f' := by group
    rw [e1]
    exact Subgroup.mul_mem _ hze (Subgroup.pow_mem _ (Subgroup.inv_mem _ hsq) f')
  obtain ⟨v, hv, hne⟩ := hnontriv
  apply hne
  have h1 := Subgroup.mem_centralizer_iff.mp hyC v hv
  calc z₁ * v * z₁⁻¹ = (v * z₁) * z₁⁻¹ := by rw [h1]
    _ = v := by group

end CFSG.Quasithin.H13.Ch4.NSB
