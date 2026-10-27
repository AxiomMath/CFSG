module

public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

theorem lOne_inner [Finite G] (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : n ≠ 3) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyV₁ : y ∈ Subgroup.normalizer (V₁ : Set G)) :
    ∃ b ∈ lOne L V₁, ∀ x ∈ lOne L V₁,
      (b⁻¹ * y) * x * (b⁻¹ * y)⁻¹ * x⁻¹ ∈ pCoreOf 2 (lOne L V₁) := by
  obtain ⟨Q, _, ρX, hsurj, hker, htriv, -⟩ := exists_lOne_rep h1222 h hn hV₁
  have hL₁X : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  have hXL₁ : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_oTwoUpper _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hmemP : ∀ (z : G) (hz : z ∈ lOne L V₁), ρX ⟨z, hL₁X hz⟩ = 1 →
      z ∈ pCoreOf 2 (lOne L V₁) := by
    intro z hz h1
    have h2 : (⟨z, hz⟩ : ↥(lOne L V₁)) ∈ CFSG.pCore 2 ↥(lOne L V₁) := by
      rw [← hker]
      exact MonoidHom.mem_ker.2 h1
    exact ⟨_, h2, rfl⟩
  have hyA : conjAct V ⟨y, hyV⟩ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hle⟩ := hyA
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hlL
  have hlv : ∀ v ∈ V, l * v * l⁻¹ = y * v * y⁻¹ := fun v hv => by
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hle ⟨v, hv⟩)
    rwa [A1b.conjAct_coe, A1b.conjAct_coe] at h1
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [hlv v (hV₁.1 hv)]
      exact (Subgroup.mem_normalizer_iff.1 hyV₁ v).1 hv
    · intro hv
      have hvV : v ∈ V := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hlN) _).1 (hV₁.1 hv)
        rwa [show l⁻¹ * (l * v * l⁻¹) * l⁻¹⁻¹ = v by group] at h1
      rw [hlv v hvV] at hv
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hyV₁) _).1 hv
      rwa [show y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ = v by group] at h1
  have hlX : l ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨hlL, hlV₁⟩
  obtain ⟨b, hb⟩ := hsurj (ρX ⟨l, hlX⟩)
  refine ⟨b, b.2, fun x hx => ?_⟩
  have hcV : ∀ u ∈ V, (l⁻¹ * y) * u * (l⁻¹ * y)⁻¹ = u := fun u hu => by
    calc (l⁻¹ * y) * u * (l⁻¹ * y)⁻¹ = l⁻¹ * (y * u * y⁻¹) * l := by group
      _ = l⁻¹ * (l * u * l⁻¹) * l := by rw [hlv u hu]
      _ = u := by group
  have hcV' : ∀ u ∈ V, (l⁻¹ * y)⁻¹ * u * (l⁻¹ * y) = u := fun u hu => by
    calc (l⁻¹ * y)⁻¹ * u * (l⁻¹ * y) =
          (l⁻¹ * y)⁻¹ * ((l⁻¹ * y) * u * (l⁻¹ * y)⁻¹) * (l⁻¹ * y) := by rw [hcV u hu]
      _ = u := by group
  have hyL₁ : y ∈ Subgroup.normalizer (lOne L V₁ : Set G) :=
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hyL, Subgroup.le_normalizer hyV₁⟩)
  have hcN : l⁻¹ * y ∈ Subgroup.normalizer (lOne L V₁ : Set G) :=
    Subgroup.mul_mem _ (inv_mem (hXL₁ hlX)) hyL₁
  have hbN : (b : G) ∈ Subgroup.normalizer (lOne L V₁ : Set G) := hXL₁ (hL₁X b.2)
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hLV (hL₁X hx).1
  have hwL₁ : (l⁻¹ * y) * x * (l⁻¹ * y)⁻¹ * x⁻¹ ∈ lOne L V₁ :=
    (lOne L V₁).mul_mem ((Subgroup.mem_normalizer_iff.1 hcN x).1 hx) (inv_mem hx)
  have hw : ∀ v ∈ V, ((l⁻¹ * y) * x * (l⁻¹ * y)⁻¹ * x⁻¹) * v *
      ((l⁻¹ * y) * x * (l⁻¹ * y)⁻¹ * x⁻¹)⁻¹ * v⁻¹ ∈ V₁ := by
    intro v hv
    have hv' : x⁻¹ * v * x ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hxV) v).1 hv
      rwa [inv_inv] at h1
    have e1 : ((l⁻¹ * y) * x * (l⁻¹ * y)⁻¹ * x⁻¹) * v * ((l⁻¹ * y) * x * (l⁻¹ * y)⁻¹ * x⁻¹)⁻¹ =
        (l⁻¹ * y) * x * ((l⁻¹ * y)⁻¹ * (x⁻¹ * v * x) * (l⁻¹ * y)) * x⁻¹ * (l⁻¹ * y)⁻¹ := by
      group
    rw [e1, hcV' _ hv',
      show (l⁻¹ * y) * x * (x⁻¹ * v * x) * x⁻¹ * (l⁻¹ * y)⁻¹ = (l⁻¹ * y) * v * (l⁻¹ * y)⁻¹ by
        group, hcV v hv, mul_inv_cancel]
    exact V₁.one_mem
  set wX : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G)) := ⟨_, hL₁X hwL₁⟩ with hwX
  have hρw : ρX wX = 1 := htriv _ hw
  set dX : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    (Subgroup.inclusion hL₁X b)⁻¹ * ⟨l, hlX⟩ with hdX
  have hρd : ρX dX = 1 := by
    rw [hdX, map_mul, map_inv]
    have h1 : ρX (Subgroup.inclusion hL₁X b) = ρX ⟨l, hlX⟩ := hb
    rw [h1, inv_mul_cancel]
  set xX : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G)) := ⟨x, hL₁X hx⟩ with hxX
  have hzL₁ : ((b : G)⁻¹ * y) * x * ((b : G)⁻¹ * y)⁻¹ * x⁻¹ ∈ lOne L V₁ := by
    have hdN : (b : G)⁻¹ * y ∈ Subgroup.normalizer (lOne L V₁ : Set G) :=
      Subgroup.mul_mem _ (inv_mem hbN) hyL₁
    exact (lOne L V₁).mul_mem ((Subgroup.mem_normalizer_iff.1 hdN x).1 hx) (inv_mem hx)
  apply hmemP _ hzL₁
  have hzeq : (⟨_, hL₁X hzL₁⟩ : ↥(L ⊓ Subgroup.normalizer (V₁ : Set G))) =
      dX * wX * dX⁻¹ * (dX * xX * dX⁻¹ * xX⁻¹) := by
    apply Subtype.ext
    simp only [hdX, hwX, hxX, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  rw [hzeq]
  simp [hρd, hρw]

@[expose] def S3OvergroupFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K S B Y : Subgroup G), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf S X → K ⊔ S = X →
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    B ≤ K → S ≤ Subgroup.normalizer (B : Set G) →
    (Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) →
    (∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B) →
    B ⊔ S ≤ Y → Y ≤ X → Y ≠ X →
      ∃ H : Subgroup G, S ≤ H ∧ H ≤ X ∧ ¬ H ≤ Y ∧
        Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))

theorem final1291_of (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h1295 : Lemma12_9_5) (hS3 : S3OvergroupFact) : Final1291 := by
  intro G _ _ T L V n hcx V₁ K₁ hV₁ hLK hK
  have hyp := hcx.hyp.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨⟨-, hHz⟩, hiso, -⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK hK
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) :=
    hV₁.2.2.trans (normalizer_le_of_lOne_le h1222 h37 h38 hcx.hyp hn hV₁ hLK hK)
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hL₁M : lOne L V₁ ≤ Subgroup.normalizer (L : Set G) :=
    (oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := (hyp.le_and_normalizes h1222).2
  obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 hcx.hyp hn hV₁
  have hL₁iso : Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
    rcases hcx.n45 with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  have hinner : ∀ t ∈ T, ∃ b ∈ lOne L V₁, ∀ x ∈ lOne L V₁,
      (b⁻¹ * t) * x * (b⁻¹ * t)⁻¹ * x⁻¹ ∈ pCoreOf 2 (lOne L V₁) := fun t ht =>
    lOne_inner h1222 hcx.hyp hn hV₁ (hyp.normalizes ht) (hTV ht) (hV₁.2.2 ht)
  have hne : Subgroup.normalizer (L : Set G) ⊓ (K₁ ⊔ T) ≠ K₁ ⊔ T := fun heq =>
    hHz.2.2 (by rw [← heq]; exact inf_le_left)
  obtain ⟨H, hTH, hHX, hHY, hH⟩ := hS3 G (K₁ ⊔ T) K₁ T (lOne L V₁)
    (Subgroup.normalizer (L : Set G) ⊓ (K₁ ⊔ T)) le_sup_left
    (sup_le Subgroup.le_normalizer hTK)
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right) rfl hiso hLK hTL₁ hL₁iso hinner
    (sup_le (le_inf hL₁M (hLK.trans le_sup_left)) (le_inf hyp.normalizes le_sup_right))
    inf_le_right hne
  exact ⟨H, hTH, hHX, fun hHM => hHY (le_inf hHM hHX), hH⟩

end CFSG.Quasithin.H13
