module

public import CFSG.Quasithin.Vol2.KGFact12617LieSp
public import CFSG.Quasithin.Vol2.KGFact12617LieG2
public import CFSG.Quasithin.Vol2.KGFact12617Lie
public import CFSG.Quasithin.Vol2.KGFact12618Lie
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Quasithin.Vol2.KGFact12617

public section

namespace CFSG.Quasithin.H13.KG12617Lie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem quasithinO2QuotientIso_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    {B : Subgroup G} {B' : Subgroup G'} {X : Type*} [Group X] (ι : ↥B ≃* ↥B')
    (h : quasithinO2QuotientIso B X) : quasithinO2QuotientIso B' X := by
  obtain ⟨φ, hφs, hφk⟩ := h
  refine ⟨φ.comp ι.symm.toMonoidHom, hφs.comp ι.symm.surjective, ?_⟩
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ι, ← hφk]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    exact ⟨ι.symm x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem false_of_model {Γ : Type} [Group Γ] [Finite Γ] {Y K T T₀ B : Subgroup Γ} {M : Type}
    [Group M] (e : ↥K ≃* M)
    (hmodel : ∀ B' W' : Subgroup M, quasithinO2QuotientIso B' ↥(alternatingGroup (Fin 6)) →
      W' ≠ ⊥ → IsPGroup 2 ↥W' → B' ≤ Subgroup.normalizer (W' : Set M) → False)
    (hKY : K ≤ Y) (hYK : Y ≤ Subgroup.normalizer (K : Set Γ)) (hT : IsSylowTwoOf T Y)
    (hBK : B ≤ K) (hT₀T : T₀ ≤ T) (hT₀4 : T₀.relIndex T ≤ 4)
    (hT₀N : T₀ ≤ Subgroup.normalizer (B : Set Γ))
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) {m : ℕ} (hm : 8 ≤ m)
    (hK : 2 ^ m ∣ Nat.card ↥K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hcard⟩ := two_pow_le_card hKY hYK hT hT₀T hT₀4 hK
  have h256 : 2 ^ 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hP64 : 2 ^ 6 ≤ Nat.card ↥(T₀ ⊓ K) := by omega
  obtain ⟨W, hW, hW2, hWBP, hBW⟩ :=
    exists_pGroup_normalized hBiso hP2 (inf_le_left.trans hT₀N) hP64
  have hWK : W ≤ K := hWBP.trans (sup_le hBK inf_le_right)
  set B' := (B.subgroupOf K).map e.toMonoidHom with hB'
  set W' := (W.subgroupOf K).map e.toMonoidHom with hW'
  have ιB : ↥B ≃* ↥B' := (Subgroup.subgroupOfEquivOfLe hBK).symm.trans
    ((B.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)
  refine hmodel B' W' (quasithinO2QuotientIso_of_mulEquiv ιB hBiso) ?_
    ((hW2.comap_subtype (K := K)).map _) ?_
  · intro h
    apply hW
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective, Subgroup.subgroupOf_eq_bot,
      disjoint_iff, inf_eq_left.2 hWK] at h
    exact h
  · rw [hB', hW', ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hBW hb) x

theorem two_pow_dvd_card_sp4 {Γ : Type} [Group Γ] {K : Subgroup Γ} {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (e : ↥K ≃* ↥(StatedSp 2 F)) :
    2 ^ (n * 4) ∣ Nat.card ↥K := by
  rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    hF, ← pow_mul]
  exact dvd_mul_right _ _

theorem two_pow_dvd_card_g2 {Γ : Type} [Group Γ] {K : Subgroup Γ} {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (e : ↥K ≃* ↥(quasithinG2 F)) :
    2 ^ (n * 6) ∣ Nat.card ↥K := by
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  rw [Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hF, ← pow_mul]
  exact dvd_mul_right _ _

theorem false_of_lieFam
    {Γ : Type} [Group Γ] [Finite Γ] {Y K T T₀ B : Subgroup Γ}
    (hKY : K ≤ Y) (hYK : Y ≤ Subgroup.normalizer (K : Set Γ))
    (hfam : (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(Assembly.LowTwoRank.StatedSp 2 F))) ∨
      (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Even n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(CFSG.Open.quasithinG2 F))))
    (hT : IsSylowTwoOf T Y) (hBK : B ≤ K) (hT₀T : T₀ ≤ T) (hT₀4 : T₀.relIndex T ≤ 4)
    (hT₀N : T₀ ≤ Subgroup.normalizer (B : Set Γ))
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) : False := by
  rcases hfam with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨n, F, _, _, hn, -, hF, ⟨e⟩⟩
  · have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
    exact false_of_model e (fun B' W' h1 h2 h3 h4 => false_of_normalizes_sp4 h1 h2 h3 h4)
      hKY hYK hT hBK hT₀T hT₀4 hT₀N hBiso (by omega) (two_pow_dvd_card_sp4 hF e)
  · exact false_of_model e (fun B' W' h1 h2 h3 h4 => false_of_normalizes_g2 hF hn h1 h2 h3 h4)
      hKY hYK hT hBK hT₀T hT₀4 hT₀N hBiso (by omega) (two_pow_dvd_card_g2 hF e)

theorem factKv12617LieFam_holds :
    FactKv12617LieFam := by
  intro Γ _ _ Y K T T₀ B R hconf hfam
  obtain ⟨hKY, hYK, -, hT, -, -, hBK, hT₀T, hT₀4, hT₀N, -, hBiso, -⟩ := hconf
  exact false_of_lieFam hKY hYK hfam hT hBK.le hT₀T hT₀4 hT₀N hBiso

theorem factKv12618LieFam_holds :
    FactKv12618LieFam := by
  intro Γ _ _ Y K T T₀ B hKY hYK _ hfam hT _ _ hBK hT₀T hT₀4 hT₀N _ hBiso _
  exact false_of_lieFam hKY hYK hfam hT hBK.le hT₀T hT₀4 hT₀N hBiso

end CFSG.Quasithin.H13.KG12617Lie
