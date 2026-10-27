module

public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4Four
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

theorem wClos_zero_eq {T V : Subgroup G} (hV2 : IsPGroup 2 V) :
    E3.wClos V 0 T = ⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).1 hm
    have hAT' : CFSG.conjugate V g ≤ T := by
      rw [hAeq] at hAT
      exact hAT
    rw [hAeq]
    exact le_iSup₂ (f := fun g (_ : CFSG.conjugate V g ≤ T) => CFSG.conjugate V g) g hAT'
  · refine iSup₂_le fun g hg => ?_
    refine le_iSup₂ (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) (CFSG.conjugate V g)
      ⟨hg, g, le_rfl, (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) (le_refl _)).2 rfl⟩

omit [Finite G] in
theorem exists_two_pow_mem_of_mem_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {c : G} (hc : c ∈ L ⊔ T) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hc' : c ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc'
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hTL (pow_mem ht m)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, htk, mul_one]; exact hl'⟩

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  refine LinearS3.le_normalizer_of_conj_mem fun g hg x hx => ?_
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have h1 : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) v).1 hv
    rwa [inv_inv] at this
  have h2 := hx _ h1
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
    _ = g * x * g⁻¹ * v := by group

theorem inf_centralizer_eq_sup_inf_centralizer (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    {n : ℕ} (h : Hyp1281One G T L V n) :
    T ⊓ Subgroup.centralizer (V : Set G) = (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have hyp := h.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [inf_centralizer_eq_pCoreOf h1222 h]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup hT2 hyp.normalizes c.2.1
    have hkC : (c : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hk, pow_mem c.2.2 _⟩
    obtain ⟨m, hm⟩ := hCL ⟨_, hkC⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']
  have hEV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hCN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hEV.trans (normalizer_le_normalizer_centralizer' V))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCO : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCN hC2
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := by
    have := pCoreOf_two_le_sylow (L ⊔ T) S (hS ▸ le_sup_right)
    rwa [hS] at this
  have heq : T ⊓ Subgroup.centralizer (V : Set G) =
      (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf (hCO.trans hOT) inf_le_right)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hCN

theorem isUniqueM_normalizer_inf_centralizer (h1222 : Stmt12_2_2) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) :
    IsUniqueM (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  have hyp := h.hyp
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hVT, -⟩ := hyp.le_and_normalizes h1222
  have hU := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow
    hyp.maximal
  rw [hyp.conjClosure_eq] at hU
  have hLT := (inf_centralizer_eq_sup_inf_centralizer h1222 h).2
  have hVP : V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf hVT fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hab y hy x hx
  have hVne : V ≠ ⊥ := by
    intro hb
    have := h.card_sq.1
    rw [hb, Subgroup.card_bot] at this
    have h2 := Nat.one_lt_two_pow (n := n) (by rcases h.n_mem with rfl | rfl | rfl <;> omega)
    omega
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    ⟨T ⊓ Subgroup.centralizer (V : Set G), fun hb => hVne (le_bot_iff.1 (hb ▸ hVP)),
      hyp.sylow.1.to_le inf_le_left, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := hU.2 M' ⟨hM', hLT.trans hle⟩
  refine ⟨⟨hU.1.1, hM'eq ▸ hle⟩, fun M'' hM'' => hU.2 M'' ⟨hM''.1, hLT.trans hM''.2⟩⟩

theorem normalizer_wZero_le (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n)
    (hW₀ : (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
      Subgroup.centralizer (V : Set G)) :
    Subgroup.normalizer
        ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes h1222
  have hV : IsElemAbelian 2 V := ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, hsq⟩
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2)⟩
  have hT : E3.HypE322 T V :=
    ⟨⟨le_top, hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hyp.sylow.2⟩, hVT, hTV⟩
  have hrk : 0 < rk ↥V := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hb := (rk_eq_zero_iff_of_isPGroup hV2).1 h0
    rw [hb, Subgroup.card_bot] at hcard
    have h2 := Nat.one_lt_two_pow (n := n) (by rcases hcx.n45 with h | h <;> omega)
    omega
  have hWT : (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤ T :=
    iSup₂_le fun g hg => hg
  have hw : (0 : ℕ∞) < E3.wParam T V := by
    have h1 := E3.le_wParam_of_wClos_le (T := T) (V := V) (n := 1) fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [wClos_zero_eq hV2]
      exact le_inf hWT hW₀
    exact lt_of_lt_of_le (by norm_num) h1
  have h34 := E3.e3_34_two hV hT
    (isUniqueM_normalizer_inf_centralizer h1222 h37 h38 h39 hcx.hyp) (i := 0) hrk
    (by simpa using hw)
  rw [← wClos_zero_eq hV2]
  exact h34.1

end CFSG.Quasithin.H13
