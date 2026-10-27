module

public import CFSG.RankThree.GF2n.Smith81.LinOddDefs
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.Sec1Main

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem InZClass.conj {Z : Subgroup G} {v : G} (h : InZClass Z v) (g : G) :
    InZClass Z (g * v * g⁻¹) := by
  obtain ⟨a, z, hz, hz1, rfl⟩ := h
  exact ⟨g * a, z, hz, hz1, by group⟩

theorem inZClass_conj_iff {Z : Subgroup G} {v : G} (g : G) :
    InZClass Z (g * v * g⁻¹) ↔ InZClass Z v := by
  refine ⟨fun h => ?_, fun h => h.conj g⟩
  have := h.conj g⁻¹
  simpa [mul_assoc] using this

section Basic

variable [Finite G] {M Q Z : Subgroup G}

theorem root_le_Q (H : StrothHyp M Q Z) {Y : Subgroup G} (hY : IsZConjugate Z Y) {y : G}
    (hyY : y ∈ Y) (hyQ : y ∈ Q) (hy1 : y ≠ 1) : Y ≤ Q := by
  by_cases hYZ : Y = Z
  · rw [hYZ]; exact H.Z_normal.1
  obtain ⟨g, hg⟩ := hY
  have hY' : IsZConjugate Z Y := ⟨g, hg⟩
  have hZN : Z ≤ Subgroup.normalizer (Y : Set G) := fun z hz =>
    hY'.mem_normalizer_of_commute H hy1 hyY (Z_central H hz hyQ)
  by_cases hZQB : Z ≤ QB Y
  · have := (IsZConjugate.le_QB_iff H hY' (IsZConjugate.self Z)).mp hZQB
    rwa [StrothHyp.QB_Z H] at this
  · obtain ⟨z, hz, hzQB⟩ : ∃ z ∈ Z, z ∉ QB Y := by
      by_contra hcon
      push Not at hcon
      exact hZQB hcon
    have hz1 : z ≠ 1 := fun h => hzQB (h ▸ (QB Y).one_mem)
    have hzM : g⁻¹ * z * g ∈ M := by
      have : z ∈ conjSubgroup g M := by
        rw [← normalizer_conj_eq H g, ← hg]; exact hZN hz
      exact mem_conjSubgroup.mp this
    have hzQ : g⁻¹ * z * g ∉ Q := by
      intro h
      apply hzQB
      rw [hg, QB_conj_eq H g, mem_conjSubgroup]; exact h
    have hs := Sit.of_conj H (g := g⁻¹) hz hz1 (by simpa using hzM) (by simpa using hzQ)
    have h12 := smith_1_12 hs
    have hYC : ∀ y' ∈ Y, ∀ z' ∈ Z, y' * z' = z' * y' := by
      intro y' hy' z' hz'
      rw [hg, mem_conjSubgroup] at hy'
      have hmem : g⁻¹ * z' * g ∈ conjSubgroup g⁻¹ Z := by
        rw [mem_conjSubgroup]; simpa [mul_assoc] using hz'
      have hc := Subgroup.mem_centralizer_iff.mp (h12.1 hmem).2 (g⁻¹ * y' * g) hy'
      have : g * (g⁻¹ * y' * g * (g⁻¹ * z' * g)) * g⁻¹ =
          g * (g⁻¹ * z' * g * (g⁻¹ * y' * g)) * g⁻¹ := by rw [hc]
      simpa [mul_assoc] using this
    have hYM : Y ≤ M := by
      have h1 : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_of_comm hYC
      rw [H.normalizer_Z.1] at h1
      exact h1
    have hYQ : ∀ y' ∈ Y, y' ∈ Q := by
      intro y' hy'
      by_contra hy'Q
      have hy'1 : y' ≠ 1 := fun h => hy'Q (h ▸ Q.one_mem)
      have hs' : Sit M Q Z Y y' := ⟨H, ⟨g, hg⟩, hy', hy'1, hYM hy', hy'Q⟩
      have h12' := smith_1_12 hs'
      have : y ∈ Y ⊓ Q := ⟨hyY, hyQ⟩
      rw [h12'.2, Subgroup.mem_bot] at this
      exact hy1 this
    exact fun y' hy' => hYQ y' hy'

theorem QB_conj_of_isZConjugate (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X)
    (g : G) : QB (conjSubgroup g X) = conjSubgroup g (QB X) := by
  obtain ⟨h, rfl⟩ := hX
  rw [← conjSubgroup_mul, QB_conj_eq H, QB_conj_eq H, conjSubgroup_mul]

omit [Finite G] in
theorem conjSubgroup_eq_bot_iff (g : G) (T : Subgroup G) : conjSubgroup g T = ⊥ ↔ T = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro t ht
    have : g * t * g⁻¹ ∈ conjSubgroup g T := by
      rw [mem_conjSubgroup]; simpa [mul_assoc] using ht
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    have h1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h1, this]; group
  · intro h
    rw [h]
    exact Subgroup.map_bot _

theorem QB_inf_conj_eq_bot_iff (H : StrothHyp M Q Z) {A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) (g : G) :
    QB (conjSubgroup g A) ⊓ QB (conjSubgroup g X) = ⊥ ↔ QB A ⊓ QB X = ⊥ := by
  rw [QB_conj_of_isZConjugate H hA, QB_conj_of_isZConjugate H hX, ← conjSubgroup_inf,
    conjSubgroup_eq_bot_iff]

theorem sit_conj_back (H : StrothHyp M Q Z) {g : G} {X : Subgroup G} {x : G}
    (hX : IsZConjugate Z X) (hx : x ∈ X) (hx1 : x ≠ 1)
    (hxN : x ∈ Subgroup.normalizer (conjSubgroup g Z : Set G))
    (hxQ : x ∉ QB (conjSubgroup g Z)) :
    Sit M Q Z (conjSubgroup g⁻¹ X) (g⁻¹ * x * g) := by
  obtain ⟨h, rfl⟩ := hX
  refine ⟨H, ⟨g⁻¹ * h, by rw [conjSubgroup_mul]⟩, ?_, ?_, ?_, ?_⟩
  · rw [mem_conjSubgroup]; simpa [mul_assoc] using hx
  · intro h1
    apply hx1
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]; group
  · rw [normalizer_conj_eq H g] at hxN
    exact mem_conjSubgroup.mp hxN
  · intro h1
    apply hxQ
    rw [QB_conj_eq H g, mem_conjSubgroup]; exact h1

theorem cond_conj {B V₁ V₂ : Subgroup G} (hcond : Lin212CondProp M Q Z B V₁ V₂)
    (H : StrothHyp M Q Z) {g : G} {X : Subgroup G} {x : G} (hX : IsZConjugate Z X) (hx : x ∈ X)
    (hx1 : x ≠ 1) (hxN : x ∈ Subgroup.normalizer (conjSubgroup g Z : Set G))
    (hxQ : x ∉ QB (conjSubgroup g Z))
    (hne : QB (conjSubgroup g Z) ⊓ QB X ≠ ⊥) :
    g⁻¹ * x * g ∈ Lgen M (LB M Q B) ∧ HasDimOn V₁ Z 1 (g⁻¹ * x * g) ∧
    HasDimOn V₂ Z 1 (g⁻¹ * x * g) ∧
    (∀ z' ∈ Z, InZClass Z (g⁻¹ * x * g * z') → z' = 1) ∧
    (∀ h q : G, q ∈ Q → h * (g⁻¹ * x * g) * h⁻¹ = (g⁻¹ * x * g) * q →
      ∃ q' ∈ Q, h * (g⁻¹ * x * g) * h⁻¹ = q' * (g⁻¹ * x * g) * q'⁻¹) := by
  have hs := sit_conj_back H hX hx hx1 hxN hxQ
  refine hcond _ _ hs ?_
  have hZ : IsZConjugate Z Z := IsZConjugate.self Z
  have hA : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have h1 := (QB_inf_conj_eq_bot_iff H hA hX g⁻¹).not.mpr hne
  have e1 : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul]; simp [conjSubgroup_one]
  rw [e1, StrothHyp.QB_Z H] at h1
  exact h1

theorem commutator_zpowers_le {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) : ⁅V, Subgroup.zpowers x⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv k hk
  have hkN : k ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hx) hk
  have h1 : k * v⁻¹ * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkN _).mp (V.inv_mem hv)
  have e : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv h1

theorem comm_Q_inf_V (H : StrothHyp M Q Z) {V₁ V₂ : Subgroup G} (hZ₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q)
    (hZ₂ : Z ≤ V₂) (hV₂Q : V₂ ≤ Q) (hint : V₁ ⊓ V₂ = Z)
    (hQ : ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b ∈ V₂, q = a * b) {x : G} (hx2 : x * x = 1)
    (hx₁ : x ∈ Subgroup.normalizer (V₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (V₂ : Set G))
    {y : G} (hy : y ∈ ⁅Q, Subgroup.zpowers x⁆ ⊔ Z) (hyV : y ∈ V₁) :
    y ∈ ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z := by
  set P₁ : Subgroup G := ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z with hP₁
  set P₂ : Subgroup G := ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z with hP₂
  have hP₁V : P₁ ≤ V₁ := sup_le (commutator_zpowers_le hx₁) hZ₁
  have hP₂V : P₂ ≤ V₂ := sup_le (commutator_zpowers_le hx₂) hZ₂
  have hZP₁ : Z ≤ P₁ := le_sup_right
  have hP₁conj : ∀ q ∈ Q, ∀ p ∈ P₁, q * p * q⁻¹ ∈ P₁ := by
    intro q hq p hp
    have hc : ⁅q, p⁆ ∈ Z := comm_mem_Z H hq (hV₁Q (hP₁V hp))
    have e : q * p * q⁻¹ = ⁅q, p⁆ * p := by simp only [commutatorElement_def]; group
    rw [e]
    exact P₁.mul_mem (hZP₁ hc) hp
  let T : Subgroup G :=
    { carrier := {g | ∃ p₁ ∈ P₁, ∃ p₂ ∈ P₂, g = p₁ * p₂}
      one_mem' := ⟨1, P₁.one_mem, 1, P₂.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
        refine ⟨a₁ * (a₂ * b₁ * a₂⁻¹), P₁.mul_mem ha₁ (hP₁conj a₂ (hV₂Q (hP₂V ha₂)) b₁ hb₁),
          a₂ * b₂, P₂.mul_mem ha₂ hb₂, by group⟩
      inv_mem' := by
        rintro _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        refine ⟨a₂⁻¹ * a₁⁻¹ * a₂, ?_, a₂⁻¹, P₂.inv_mem ha₂, by group⟩
        have := hP₁conj a₂⁻¹ (Q.inv_mem (hV₂Q (hP₂V ha₂))) a₁⁻¹ (P₁.inv_mem ha₁)
        simpa [mul_assoc] using this }
  have hgen : ∀ q ∈ Q, ⁅q, x⁆ ∈ T := by
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hQ q hq
    have hbx : ⁅b, x⁆ ∈ P₂ :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers x))
    have hax : ⁅a, x⁆ ∈ P₁ :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers x))
    have hbxQ : ⁅b, x⁆ ∈ Q := hV₂Q (hP₂V hbx)
    have hz : ⁅a, ⁅b, x⁆⁆ ∈ Z := comm_mem_Z H (hV₁Q ha) hbxQ
    have e : ⁅a * b, x⁆ = (⁅a, ⁅b, x⁆⁆ * (⁅b, x⁆ * ⁅a, x⁆ * ⁅b, x⁆⁻¹)) * ⁅b, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine ⟨_, P₁.mul_mem (hZP₁ hz) ?_, ⁅b, x⁆, hbx, rfl⟩
    have := hP₁conj ⁅b, x⁆ hbxQ _ hax
    simpa [mul_assoc] using this
  have hcomm : ⁅Q, Subgroup.zpowers x⁆ ≤ T := by
    rw [commutator_zpowers_eq_closure hx2, Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact hgen q hq
  have hZT : Z ≤ T := fun z hz => ⟨z, hZP₁ hz, 1, P₂.one_mem, by simp⟩
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := (sup_le hcomm hZT) hy
  have hp₂V₁ : p₂ ∈ V₁ := by
    have := V₁.mul_mem (V₁.inv_mem (hP₁V hp₁)) hyV
    simpa using this
  have hp₂Z : p₂ ∈ Z := by
    rw [← hint]; exact ⟨hp₂V₁, hP₂V hp₂⟩
  exact P₁.mul_mem hp₁ (hZP₁ hp₂Z)

omit [Finite G] in
theorem commutator_zpowers_conj (g : G) (V : Subgroup G) (x : G) :
    ⁅conjSubgroup g V, Subgroup.zpowers (g * x * g⁻¹)⁆ =
      conjSubgroup g ⁅V, Subgroup.zpowers x⁆ := by
  have h1 : Subgroup.zpowers (g * x * g⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]; rfl
  rw [h1]
  exact (Subgroup.map_commutator (H₁ := V) (H₂ := Subgroup.zpowers x)
    (MulAut.conj g).toMonoidHom).symm

omit [Finite G] in
theorem conjSubgroup_sup (g : G) (A C : Subgroup G) :
    conjSubgroup g (A ⊔ C) = conjSubgroup g A ⊔ conjSubgroup g C :=
  Subgroup.map_sup _ _ _

theorem card_sup_of_comm_inf_bot {A C : Subgroup G} (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hAC : A ⊓ C = ⊥) : Nat.card ↥(A ⊔ C) = Nat.card A * Nat.card C := by
  have h := card_sup_mul_card_inf_of_normalizer (A := A) (C := C)
    (le_normalizer_of_comm fun c hc a ha => (hcomm a ha c hc).symm)
  rw [hAC, Subgroup.card_bot, mul_one] at h
  exact h

omit [Finite G] in
theorem decomp_swap {Q V₁ V₂ : Subgroup G} (hZ₁ : ∀ a ∈ V₁, ∀ q ∈ Q, q * a * q⁻¹ ∈ V₁)
    (hV₂Q : V₂ ≤ Q) (hQ : ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b ∈ V₂, q = a * b) :
    ∀ q ∈ Q, ∃ b ∈ V₂, ∃ a ∈ V₁, q = b * a := by
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := hQ q hq
  refine ⟨b, hb, b⁻¹ * a * b, ?_, by group⟩
  have := hZ₁ a ha b⁻¹ (Q.inv_mem (hV₂Q hb))
  simpa using this

theorem c4_conj (h4 : Lin212C4Prop M Q Z) (H : StrothHyp M Q Z) {g : G} {X : Subgroup G} {x : G}
    (hX : IsZConjugate Z X) (hx : x ∈ X) (hx1 : x ≠ 1)
    (hxN : x ∈ Subgroup.normalizer (conjSubgroup g Z : Set G))
    (hxQ : x ∉ QB (conjSubgroup g Z)) (hne : QB (conjSubgroup g Z) ⊓ QB X ≠ ⊥) :
    ∀ z' ∈ Z, InZClass Z (g⁻¹ * x * g * z') → z' = 1 := by
  have hs := sit_conj_back H hX hx hx1 hxN hxQ
  refine h4 _ _ hs ?_
  have hA : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have h1 := (QB_inf_conj_eq_bot_iff H hA hX g⁻¹).not.mpr hne
  have e1 : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul]; simp [conjSubgroup_one]
  rw [e1, StrothHyp.QB_Z H] at h1
  exact h1

end Basic

end CFSG.RankThree.GF2n.Smith81
