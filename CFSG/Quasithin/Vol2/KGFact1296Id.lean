module

public import CFSG.Quasithin.Vol2.KGFact1296Par
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics

public section

namespace CFSG.Quasithin.H13.KG1296

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.SLnTwo
open scoped Pointwise

variable {n : ℕ}

theorem map_graphAut_last (hn : 2 ≤ n) :
    (flagStabilizer n (ZMod 2) {n - 1}).map (BinaryParabolic.graphAut n).toMonoidHom =
      Pone n := by
  set A := (flagStabilizer n (ZMod 2) {n - 1}).map (BinaryParabolic.graphAut n).toMonoidHom
    with hA
  have hU : upperTriangular n (ZMod 2) ≤ A := by
    rw [BinaryParabolic.upperTriangular_eq_unitriangular,
      ← BinaryParabolic.map_graphAut_unitriangular]
    refine Subgroup.map_mono ?_
    rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
    exact upperTriangular_le_flagStabilizer _
  have hmem : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      reflection n (ZMod 2) i hi hin ∈ A ↔ i ≠ 1 := by
    intro i hi hin
    rw [hA, Subgroup.mem_map_equiv]
    show BinaryParabolic.graphFun (reflection n (ZMod 2) i hi hin) ∈ _ ↔ _
    rw [BinaryParabolic.graphFun_reflection,
      (subflag_stabilizer_generation (K := ZMod 2) (n := n) {n - 1}).2.2, Set.mem_singleton_iff]
    constructor <;> intro h <;> omega
  obtain ⟨hA1, -⟩ := borel_overgroups A hU
  rw [hA1]
  congr 1
  ext i
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hi, hin, hr⟩
    by_contra h1
    exact hr ((hmem i hi hin).2 h1)
  · rintro rfl
    exact ⟨le_refl 1, by omega, fun h => (hmem 1 (le_refl 1) (by omega)).1 h rfl⟩

theorem map_graphAut_map_graphAut (H : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
    (H.map (BinaryParabolic.graphAut n).toMonoidHom).map
      (BinaryParabolic.graphAut n).toMonoidHom = H := by
  have h : (BinaryParabolic.graphAut n).toMonoidHom.comp (BinaryParabolic.graphAut n).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun g => BinaryParabolic.graphFun_graphFun g
  rw [Subgroup.map_map, h, Subgroup.map_id]

theorem exists_big_block (hn : 1 ≤ n) {J : Set ℕ} {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ flagStabilizer n (ZMod 2) J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpx : orderOf x = p) (hGL : ∀ m, m + 2 ≤ n → ¬ p ∣ Nat.card (GL (Fin m) (ZMod 2))) :
    ∃ a m : ℕ, a + m ≤ n ∧ (a = 0 ∨ a ∈ J) ∧ (a + m = n ∨ a + m ∈ J) ∧
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) ∧ n ≤ m + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hxp : (⟨x, hx⟩ : ↥(flagStabilizer n (ZMod 2) J)) ^ p = 1 := by
    rw [← hpx, ← Subgroup.orderOf_mk x hx]
    exact pow_orderOf_eq_one _
  have hU : x ∈ unitriangular n (ZMod 2) := by
    refine mem_unitriangular_of_blocks hx fun a m h ha hb hno => ?_
    have hm : m + 1 < n := by
      by_contra hlt
      exact hcon ⟨a, m, h, ha, hb, hno, by omega⟩
    set φ := blkMon (flagStabilizer n (ZMod 2) J) a m h (blockLeft_of_cut m ha)
      (blockRight_of_cut hb) with hφ
    set u := φ.toHomUnits ⟨x, hx⟩ with hu
    have hup : u ^ p = 1 := by
      rw [hu, ← map_pow, hxp, map_one]
    have hu1 : orderOf u = 1 := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hup) with h1 | hpu
      · exact h1
      · exfalso
        apply hGL m (by omega)
        rw [← hpu]
        exact orderOf_dvd_natCard u
    rw [orderOf_eq_one_iff] at hu1
    have := congrArg Units.val hu1
    rw [hu, MonoidHom.coe_toHomUnits, Units.val_one] at this
    exact this
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 (isPGroup_unitriangular_charTwo (K := ZMod 2) hn))
    ⟨x, hU⟩
  rw [Subgroup.orderOf_mk, hpx] at hj
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ j by rw [hj])
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem cuts_cases {J : Set ℕ} (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < n) {a m : ℕ} (h : a + m ≤ n)
    (hno : ∀ c ∈ J, ¬ (a < c ∧ c < a + m)) (hm : n ≤ m + 1) :
    J = ∅ ∨ J = {1} ∨ J = {n - 1} := by
  have ha1 : a ≤ 1 := by omega
  have key : (∀ c ∈ J, c = 1) ∨ ∀ c ∈ J, c = n - 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with rfl | rfl
    · right
      intro c hc
      have := hJ c hc
      have := hno c hc
      omega
    · left
      intro c hc
      have := hJ c hc
      have := hno c hc
      omega
  rcases key with h1 | h1
  · rcases Set.subset_singleton_iff_eq.1 (fun c hc => h1 c hc) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases Set.subset_singleton_iff_eq.1 (fun c hc => h1 c hc) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem nonempty_modO2_map {G H : Type} [Group G] [Group H] (e : G ≃* H) (B : Subgroup G) :
    Nonempty (ModO2 B ≃* ModO2 (B.map e.toMonoidHom)) := by
  refine nonempty_modO2_equiv (e.toMonoidHom.subgroupMap B)
    (MonoidHom.subgroupMap_surjective _ _) ?_
  have h : (e.toMonoidHom.subgroupMap B).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  rw [h]
  exact IsPGroup.of_bot

theorem exists_primes {k : ℕ} (hk : k = 3 ∨ k = 4) :
    ∃ p q : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (SpecialLinearGroup (Fin k) (ZMod 2)) ∧
      (∀ m, m + 2 ≤ k + 1 → ¬ p ∣ Nat.card (GL (Fin m) (ZMod 2))) ∧ q.Prime ∧ q ≠ 2 ∧
      q ∣ Nat.card (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) ∧
      ¬ q ∣ Nat.card (SpecialLinearGroup (Fin k) (ZMod 2)) := by
  rcases hk with rfl | rfl
  · refine ⟨7, 5, by norm_num, by norm_num, ?_, fun m hm => ?_, by norm_num, by norm_num, ?_, ?_⟩
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    · have hm' : m ≤ 2 := by omega
      rw [card_GL_eq, Nat.card_zmod]
      interval_cases m <;> decide
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
  · refine ⟨5, 31, by norm_num, by norm_num, ?_, fun m hm => ?_, by norm_num, by norm_num, ?_, ?_⟩
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    · have hm' : m ≤ 3 := by omega
      rw [card_GL_eq, Nat.card_zmod]
      interval_cases m <;> decide
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    · rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide

theorem eq_Pone_or_graph {k : ℕ} (hk : k = 3 ∨ k = 4)
    {B : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))}
    (hU : unitriangular (k + 1) (ZMod 2) ≤
      Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))))
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin k) (ZMod 2))) :
    B = Pone (k + 1) ∨ B = (Pone (k + 1)).map (BinaryParabolic.graphAut (k + 1)).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk3 : 3 ≤ k := by omega
  obtain ⟨p, q, hp, hp2, hpSL, hpGL, hq, hq2, hqSL, hqSL'⟩ := exists_primes hk
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hB
  set A := B ⊔ unitriangular (k + 1) (ZMod 2) with hAdef
  have hAU : upperTriangular (k + 1) (ZMod 2) ≤ A := by
    rw [BinaryParabolic.upperTriangular_eq_unitriangular]
    exact le_sup_right
  have hBA : B ≤ A := le_sup_left
  have hAN : A ≤ Subgroup.normalizer (B : Set _) := sup_le Subgroup.le_normalizer hU
  obtain ⟨hAJ, -⟩ := borel_overgroups A hAU
  set J := borelOvergroupCuts A with hJdef
  have hJ : ∀ i ∈ J, 1 ≤ i ∧ i < k + 1 := fun i hi => by
    obtain ⟨hi1, hin, -⟩ := hi
    exact ⟨hi1, hin⟩
  have hcardB : Nat.card B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcardM : Nat.card (ModO2 B) = Nat.card (SpecialLinearGroup (Fin k) (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) p (by
    rw [hcardB, hcardM]
    exact Dvd.dvd.mul_right hpSL _)
  rw [← Subgroup.orderOf_coe] at hx
  have hxJ : (x : SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) ∈ flagStabilizer (k + 1) (ZMod 2) J :=
    hAJ ▸ hBA x.2
  obtain ⟨a, m, h, -, -, hno, hm⟩ := exists_big_block (by omega) hxJ hp hp2 hx hpGL
  rcases cuts_cases hJ h hno hm with hJ0 | hJ1 | hJ2
  ·
    exfalso
    have hAtop : A = ⊤ := by rw [hAJ, hJ0, flagStabilizer_empty]
    have hBn : B.Normal := ⟨fun y hy g =>
      (Subgroup.mem_normalizer_iff.1 (hAN (hAtop ▸ Subgroup.mem_top g)) y).1 hy⟩
    have hsimple := sl_isSimple_of_card_two (K := ZMod 2) (Nat.card_zmod 2) (show 3 ≤ k + 1 by
      omega)
    have hsimple' := sl_isSimple_of_card_two (K := ZMod 2) (Nat.card_zmod 2) hk3
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with hbot | htop
    · exact not_isPGroup_of_modO2 ⟨e⟩ (hbot ▸ IsPGroup.of_bot)
    · obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
      have hc : Nat.card (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) =
          Nat.card (SpecialLinearGroup (Fin k) (ZMod 2)) * 2 ^ r := by
        rw [← hcardM, ← hr, ← hcardB, htop, Subgroup.card_top]
      rw [hc] at hqSL
      rcases (Nat.Prime.dvd_mul hq).1 hqSL with h1 | h1
      · exact hqSL' h1
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h1))
  ·
    left
    have hAP : A = Pone (k + 1) := by rw [hAJ, hJ1]
    exact eq_Pone_of_normal hk3 (hAP ▸ hBA) (hAP ▸ hAN) ⟨e⟩
  ·
    right
    have hAP : A.map (BinaryParabolic.graphAut (k + 1)).toMonoidHom = Pone (k + 1) := by
      rw [hAJ, hJ2]
      exact map_graphAut_last (by omega)
    set γ := BinaryParabolic.graphAut (k + 1) with hγ
    have h1 : B.map γ.toMonoidHom = Pone (k + 1) := by
      refine eq_Pone_of_normal hk3 (hAP ▸ Subgroup.map_mono hBA) ?_ ?_
      · rw [← hAP]
        exact map_le_normalizer_map γ hAN
      · obtain ⟨e'⟩ := nonempty_modO2_map γ B
        exact ⟨e'.symm.trans e⟩
    rw [← h1, map_graphAut_map_graphAut]

theorem exists_mulAut_Pone {k : ℕ} (hk : k = 3 ∨ k = 4)
    {B : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))}
    (T : Sylow 2 (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)))
    (hT : (T : Subgroup (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))) ≤
      Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin (k + 1)) (ZMod 2))))
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin k) (ZMod 2))) :
    ∃ ι : MulAut (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)),
      B = (Pone (k + 1)).map ι.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := k + 1) (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin (k + 1)) (ZMod 2)) P T
  set c := MulAut.conj g with hc
  have hcU : ∀ u ∈ unitriangular (k + 1) (ZMod 2), c u ∈ (T : Subgroup _) := by
    intro u hu
    have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) (P : Subgroup _) (hP ▸ hu)
    have h2 : c u ∈ ((g • P : Sylow 2 _) : Subgroup _) := h1
    rwa [hg] at h2
  set B₀ := B.map c.symm.toMonoidHom with hB₀
  have hU : unitriangular (k + 1) (ZMod 2) ≤ Subgroup.normalizer (B₀ : Set _) := by
    refine le_trans (fun u hu => ?_) (map_le_normalizer_map c.symm hT)
    exact ⟨c u, hcU u hu, c.symm_apply_apply u⟩
  have hB₀' : Nonempty (ModO2 B₀ ≃* SpecialLinearGroup (Fin k) (ZMod 2)) := by
    obtain ⟨e⟩ := hB
    obtain ⟨e'⟩ := nonempty_modO2_map c.symm B
    exact ⟨e'.symm.trans e⟩
  have hBB₀ : B = B₀.map c.toMonoidHom := by
    rw [hB₀, Subgroup.map_map]
    convert (Subgroup.map_id B).symm
    ext x
    simp
  rcases eq_Pone_or_graph hk hU hB₀' with h | h
  · exact ⟨c, by rw [hBB₀, h]⟩
  · refine ⟨(BinaryParabolic.graphAut (k + 1)).trans c, ?_⟩
    rw [hBB₀, h, Subgroup.map_map]
    rfl

end CFSG.Quasithin.H13.KG1296
