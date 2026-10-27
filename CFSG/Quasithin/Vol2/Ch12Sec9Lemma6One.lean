module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6Rad
public import CFSG.Quasithin.Vol2.Ch12Sec9Final1291
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Core

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

@[expose] def ParabolicFact1296 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K S B Q : Subgroup G), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf S X → K ⊔ S = X →
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    B ≤ K → S ≤ Subgroup.normalizer (B : Set G) →
    (∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B) →
    ((Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Nat.card ↥(pCoreOf 2 (B ⊔ S)) ≤ 2 ^ 3 * Nat.card Q ∧
        (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
          ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
            ((B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map φ.toMonoidHom =
              Subgroup.centralizer ({transvection15} : Set _))) ∨
      (Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nat.card ↥(pCoreOf 2 (B ⊔ S)) ≤ 2 ^ 4 * Nat.card Q)) →
    Q < pCoreOf 2 (B ⊔ S) → B ⊔ S ≤ Subgroup.normalizer (Q : Set G) →
    centralizerMod (pCoreOf 2 K) X K ≤ Q → ¬ X ≤ Subgroup.normalizer (Q : Set G) →
      ∃ P : Subgroup G, S ≤ P ∧ P ≤ X ∧ P ≤ Subgroup.normalizer (Q : Set G) ∧
        ¬ P ≤ Subgroup.normalizer (B : Set G)

variable {G : Type} [Group G] [Finite G]

namespace L1296

omit [Finite G] in
theorem mem_pCoreOf_of_central {K : Subgroup G} (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) {k : G} (hk : k ∈ K)
    (hc : ∀ u ∈ K, k * u * k⁻¹ * u⁻¹ ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K := by
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hone : ∀ x : ↥K, π x = 1 ↔ (x : G) ∈ pCoreOf 2 K := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hcent : π ⟨k, hk⟩ ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
    have h1 := (hone (⟨k, hk⟩ * u * ⟨k, hk⟩⁻¹ * u⁻¹)).2 (hc u u.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π ⟨k, hk⟩ * π u = π u * π ⟨k, hk⟩ := by
      calc π ⟨k, hk⟩ * π u = (π ⟨k, hk⟩ * π u * (π ⟨k, hk⟩)⁻¹ * (π u)⁻¹) * (π u * π ⟨k, hk⟩) := by
            group
        _ = π u * π ⟨k, hk⟩ := by rw [h1, one_mul]
    exact h2.symm
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  rw [hZ, Subgroup.mem_bot] at hcent
  exact (hone ⟨k, hk⟩).1 hcent

theorem isPGroup_centralizerMod {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) :
    IsPGroup 2 ↥(centralizerMod (pCoreOf 2 K) (K ⊔ T) K) := by
  intro x
  obtain ⟨hxX, hxN, hxc⟩ := x.2
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup hT hTK hxX
  have hxk : (x : G) ^ 2 ^ k ∈ centralizerMod (pCoreOf 2 K) (K ⊔ T) K :=
    Subgroup.pow_mem _ x.2 _
  have hP := mem_pCoreOf_of_central hs hnab hk hxk.2.2
  obtain ⟨m, hm⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, hP⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
  rw [pow_add, pow_mul]
  exact h1

end L1296


theorem commutator_ne_bot_of_cx (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1295 : Lemma12_9_5) (hKG : ParabolicFact1296) {T L V : Subgroup G}
    {n : ℕ} (hcx : Cx1291 G T L V n) {V₁ V₂ K₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hV₁₂ : V₁ ≤ V₂) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    ⁅V₂, pCoreOf 2 K₁⁆ ≠ ⊥ := by
  intro hbot
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  obtain ⟨⟨-, hHz⟩, hiso, h3⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK hK
  obtain ⟨hsK, hnabK⟩ := isSimpleGroup_and_nonabelian_of_mulEquiv hiso
  have hK₁n : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) :=
    normalizer_le_of_lOne_le h1222 h37 h38 h hn hV₁ hLK hK
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := hV₁.2.2.trans hK₁n
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hK₁Q₁ : K₁ ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 K₁
  have hTQ₁ : T ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
    hTK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁)
  have hQ₁V : pCoreOf 2 K₁ ≤ Subgroup.centralizer (V : Set G) := by
    have hV₂C : V₂ ≤ Subgroup.centralizer (pCoreOf 2 K₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    set W := V ⊓ Subgroup.centralizer (pCoreOf 2 K₁ : Set G) with hWdef
    have hLW : lOne L V₁ ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨L1296.lOne_le_normalizer h V₁ hl,
        normalizer_le_normalizer_centralizer' _ (hK₁Q₁ (hLK hl))⟩
    rcases eq_or_eq_of_lOne_le_normalizer h hV₁ (le_inf hV₁.1 (hV₁₂.trans hV₂C)) inf_le_left
        hLW with hW | hW
    · exfalso
      have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from by
        rw [← hW]
        exact le_inf hV₂.1 hV₂C)
      rw [hV₂.2.1, hV₁.2.1] at h1
      norm_num at h1
    · have hVC : V ≤ Subgroup.centralizer (pCoreOf 2 K₁ : Set G) := by
        rw [← hW]
        exact inf_le_right
      exact Subgroup.le_centralizer_iff.1 hVC
  set D := centralizerMod (pCoreOf 2 K₁) (K₁ ⊔ T) K₁ with hDdef
  have hDp : IsPGroup 2 D := L1296.isPGroup_centralizerMod hT2 hTK hsK hnabK
  have hTD : T ≤ Subgroup.normalizer (D : Set G) :=
    L1296.le_normalizer_centralizerMod (le_sup_right.trans Subgroup.le_normalizer) hTQ₁ hTK
  have hDT : D ≤ T := L1296.le_of_isPGroup hyp.sylow hDp hTD
  have hLD : lOne L V₁ ≤ Subgroup.normalizer (D : Set G) :=
    L1296.le_normalizer_centralizerMod ((hLK.trans le_sup_left).trans Subgroup.le_normalizer)
      (hLK.trans hK₁Q₁) ((hLK.trans hK₁G₁).trans hK₁n)
  have hDV : D ≤ Subgroup.centralizer (V : Set G) := by
    refine L1296.le_centralizer_of_le_T h1222 h hV₁ hDT hTD hLD fun l hl d hd => ?_
    have h1 := (pCoreOf 2 K₁).inv_mem (hd.2.2 l (hLK hl))
    rw [show (d * l * d⁻¹ * l⁻¹)⁻¹ = l * d * l⁻¹ * d⁻¹ by group] at h1
    exact hQ₁V h1
  have hQN := (inf_centralizer_eq_sup_inf_centralizer h1222 h).2
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hBSQ : lOne L V₁ ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    (sup_le_sup_right hL₁L T).trans hQN
  have hNQM : Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G) :=
    (isUniqueM_normalizer_inf_centralizer h1222 h37 h38 h39 h).1.2
  have hcase : (Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      Nat.card ↥(pCoreOf 2 (lOne L V₁ ⊔ T)) ≤
        2 ^ 3 * Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G)) ∧
      (Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        ∃ φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
          (((lOne L V₁).subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map
              φ.toMonoidHom = Subgroup.centralizer ({transvection15} : Set _))) ∨
      (Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nat.card ↥(pCoreOf 2 (lOne L V₁ ⊔ T)) ≤
          2 ^ 4 * Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G))) := by
    obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 h hn hV₁
    have hc := L1296.card_pCoreOf_le h1222 h hV₁
    rcases hcx.n45 with rfl | rfl
    · exact Or.inl ⟨⟨e⟩, hc, h3 rfl⟩
    · exact Or.inr ⟨⟨e⟩, hc⟩
  have hinner : ∀ t ∈ T, ∃ b ∈ lOne L V₁, ∀ x ∈ lOne L V₁,
      (b⁻¹ * t) * x * (b⁻¹ * t)⁻¹ * x⁻¹ ∈ pCoreOf 2 (lOne L V₁) := fun t ht =>
    lOne_inner h1222 h hn hV₁ (hyp.normalizes ht) (hTV ht) (hV₁.2.2 ht)
  obtain ⟨P, hTP, hPX, hPQ, hPL₁⟩ := hKG G (K₁ ⊔ T) K₁ T (lOne L V₁)
    (T ⊓ Subgroup.centralizer (V : Set G)) le_sup_left (sup_le Subgroup.le_normalizer hTK)
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right) rfl hiso hLK hTL₁ hinner hcase
    (L1296.inf_centralizer_lt_pCoreOf h1222 h hV₁) hBSQ (le_inf hDT hDV)
    (fun hX => hHz.2.2 (hX.trans hNQM))
  exact hPL₁ (le_normalizer_lOne (hPQ.trans hNQM) (hPX.trans (sup_le hK₁G₁ hV₁.2.2)))

end CFSG.Quasithin.H13
