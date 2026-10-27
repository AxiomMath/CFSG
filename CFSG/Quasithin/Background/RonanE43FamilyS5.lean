module

public import CFSG.Quasithin.Background.RonanE43Lift
public import CFSG.Quasithin.Background.RonanE43S5Member

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E2P B6
  CFSG.Quasithin.E2P.SporB

@[expose] def IsA5Ext {X : Type*} [Group X] (A V : Subgroup X) : Prop :=
  V ≤ A ∧ IsPGroup 2 V ∧
    ∃ φ : ↥A →* alternatingGroup (Fin 5), Function.Surjective φ ∧ φ.ker = V.subgroupOf A

theorem IsA5Ext.map {X Y : Type*} [Group X] [Group Y] {A V : Subgroup X} (h : IsA5Ext A V)
    (f : X →* Y) (hf : Function.Injective f) : IsA5Ext (A.map f) (V.map f) := by
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := h
  refine ⟨Subgroup.map_mono hVA, hV2.map f, ?_⟩
  let eA : ↥A ≃* ↥(A.map f) := Subgroup.equivMapOfInjective A f hf
  refine ⟨φ.comp eA.symm.toMonoidHom, hφs.comp eA.symm.surjective, ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := eA.surjective x
  have h1 : (φ.comp eA.symm.toMonoidHom) (eA a) = φ a := by
    simp
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  have h2 : ((eA a : ↥(A.map f)) : Y) = f (a : X) := rfl
  rw [h2]
  exact (Subgroup.mem_map_iff_mem hf).symm

theorem IsA5Ext.subgroupOf {X : Type*} [Group X] {A V M : Subgroup X} (h : IsA5Ext A V)
    (hAM : A ≤ M) : IsA5Ext (A.subgroupOf M) (V.subgroupOf M) := by
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := h
  refine ⟨Subgroup.subgroupOf_mono M hVA, ?_, ?_⟩
  · exact hV2.of_equiv (Subgroup.subgroupOfEquivOfLe (hVA.trans hAM)).symm
  · let eA : ↥(A.subgroupOf M) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAM
    refine ⟨φ.comp eA.toMonoidHom, hφs.comp eA.surjective, ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl

theorem le_ker_of_normal_pGroup {B : Type*} [Group B] (φ : B →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ) {N : Subgroup B} (hNn : N.Normal) (hN : IsPGroup 2 N) :
    N ≤ φ.ker := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI hmapn : (N.map φ).Normal := hNn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  · intro w hw
    have := Subgroup.mem_map_of_mem φ hw
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have h2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := htop ▸ hN.map φ
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp h2
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Subgroup.card_top, h60] at hm
    have h3 : (3 : ℕ) ∣ 2 ^ m := by rw [← hm]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem IsA5Ext.pCoreOf_eq {X : Type*} [Group X] [Finite X] {A V : Subgroup X}
    (h : IsA5Ext A V) : pCoreOf 2 A = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := h
  apply le_antisymm
  · have hC := le_ker_of_normal_pGroup φ hφs (CFSG.LieType.BorelTits.pCore_normal 2)
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥A))
    rw [hφk] at hC
    have := Subgroup.map_mono (f := A.subtype) hC
    rwa [Subgroup.map_subgroupOf_eq_of_le hVA] at this
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 hVA ?_ hV2
    rw [← hφk]
    exact MonoidHom.normal_ker φ

variable {G : Type} [Group G] [Finite G]

theorem goodFamily_of_normal_S5 {T L : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hK : L.Normal)
    (hLT : L ⊔ T = ⊤) {Γ : Type} [Group Γ] [Finite Γ] (e₀ : ↥L ≃* Γ) {S₀ : Subgroup Γ}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {A V P : Subgroup Γ} (hA5 : IsA5Ext A V) (hSP : S₀ ≤ P)
    (hP3 : Nat.card P = 3 * Nat.card S₀) (hgen : (A ⊔ S₀) ⊔ P = ⊤)
    (hinv : ∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ →
      A.map α.toMonoidHom = A ∧ P.map α.toMonoidHom = P) :
    GoodFamily T 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e, he⟩ := exists_equiv_sylow e₀ hSK hS₀
  have hα : ∀ t ∈ T, S₀.map (autK e t).toMonoidHom = S₀ := fun t ht => by
    rw [← he]
    exact map_autK_of_mem_normalizer' e inf_le_right (le_normalizer_inf hK ht)
  let pull : Subgroup Γ → Subgroup G := fun P => (P.map e.symm.toMonoidHom).map L.subtype
  have hpullS : pull S₀ = T ⊓ L := by
    show (S₀.map e.symm.toMonoidHom).map L.subtype = T ⊓ L
    rw [← he]
    exact pull_map e inf_le_right
  have hpullcard : ∀ P : Subgroup Γ, Nat.card (pull P) = Nat.card P := fun P => by
    show Nat.card ((P.map e.symm.toMonoidHom).map L.subtype) = Nat.card P
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hTn : ∀ Y : Subgroup Γ,
      (∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ → Y.map α.toMonoidHom = Y) →
      T ≤ Subgroup.normalizer ((pull Y : Subgroup G) : Set G) :=
    fun Y hY t ht => mem_normalizer_pull e (hY _ (hα t ht))
  let f : Γ →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hpull_eq : ∀ Y : Subgroup Γ, pull Y = Y.map f := fun Y => by
    show (Y.map e.symm.toMonoidHom).map L.subtype = Y.map f
    rw [Subgroup.map_map]
  have hA5G : IsA5Ext (pull A) (pull V) := by
    rw [hpull_eq, hpull_eq]
    exact hA5.map f hf
  have hVG : pull V = pCoreOf 2 (pull A) := hA5G.pCoreOf_eq.symm
  have hAGn : T ≤ Subgroup.normalizer ((pull A : Subgroup G) : Set G) :=
    hTn A fun α hα' => (hinv α hα').1
  set H₂ : Subgroup G := pull A ⊔ T with hH₂
  set H₃ : Subgroup G := pull P ⊔ T with hH₃
  have hH₂n : H₂ ≤ Subgroup.normalizer ((pull A : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_normalizer) hAGn
  have hH₂V : H₂ ≤ Subgroup.normalizer ((pull V : Subgroup G) : Set G) := by
    rw [hVG]
    exact hH₂n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (pull A))
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := hA5G
  have hgood₂ : GoodAt T H₂ := fun Y hYH hYn hYT =>
    s5_good hT le_sup_right le_sup_left hVA hH₂n hH₂V hV2 φ hφs hφk rfl hYH hYn hYT
  have hrank₂ : CFSG.Open.pRank 2 (⊤ : Subgroup (↥H₂ ⧸ CFSG.pCore 2 ↥H₂)) ≤ 2 :=
    s5_pRank hT le_sup_left hVA hH₂n hH₂V hV2 φ hφs hφk rfl
  have hPL : pull P ≤ L := pull_le e P
  have hSP' : T ⊓ L ≤ pull P := by
    rw [← hpullS]
    exact pull_mono e hSP
  have hPT : pull P ⊓ T = T ⊓ L := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.2, hPL hx.1⟩
    · exact le_inf hSP' inf_le_left
  have hPinvP : ∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ → P.map α.toMonoidHom = P :=
    fun α hα' => (hinv α hα').2
  have hcardH : Nat.card ↥(pull P ⊔ T) = 3 * Nat.card T := by
    rw [card_sup_eq_relIndex_mul (hTn P hPinvP), hpullcard, hP3]
    have h1 := Subgroup.relIndex_mul_card (H := pull P) (K := T)
    rw [hPT] at h1
    have hS : Nat.card ↥(T ⊓ L) = Nat.card S₀ := by rw [← hpullS, hpullcard]
    rw [hS] at h1
    calc (pull P).relIndex T * (3 * Nat.card S₀) = 3 * ((pull P).relIndex T * Nat.card S₀) := by
          ring
      _ = 3 * Nat.card T := by rw [h1]
  have h2₃ : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H₃) :=
    card_le_two_mul_pCoreOf le_sup_right hT.isPGroup hcardH
  have hgood₃ : GoodAt T H₃ := goodAt_of_card_le hT le_sup_right h2₃
  have hrank₃ : CFSG.Open.pRank 2 (⊤ : Subgroup (↥H₃ ⧸ CFSG.pCore 2 ↥H₃)) ≤ 1 :=
    pRank_le_one_of_card_le hT le_sup_right h2₃
  have hLle : L ≤ H₂ ⊔ H₃ := by
    have h1 : pull ((A ⊔ S₀) ⊔ P) = L := by
      rw [hgen]
      exact pull_top e
    have h2 : pull ((A ⊔ S₀) ⊔ P) = (pull A ⊔ pull S₀) ⊔ pull P := by
      simp only [pull, Subgroup.map_sup]
    rw [← h1, h2, hpullS]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_sup_left : pull A ≤ H₂).trans le_sup_left
    · exact (inf_le_left : T ⊓ L ≤ T).trans (le_sup_right.trans le_sup_left)
    · exact (le_sup_left : pull P ≤ H₃).trans le_sup_right
  refine ⟨{H₂, H₃}, ⟨H₂, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH'
    · exact le_sup_right
    · rw [Finset.mem_singleton.mp hH']
      exact le_sup_right
  · rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [eq_top_iff, ← hLT]
    exact sup_le hLle (le_sup_right.trans le_sup_left)
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH'
    · exact hgood₂
    · rw [Finset.mem_singleton.mp hH']
      exact hgood₃
  · by_cases hEq : H₂ = H₃
    · rw [hEq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
      omega
    · rw [Finset.sum_pair hEq]
      omega

end CFSG.Quasithin.RonanE43
