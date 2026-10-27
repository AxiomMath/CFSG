module

public import CFSG.Quasithin.H13.L32AVmod
public import CFSG.Quasithin.H13.L32ARuTwo
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace L32A

@[expose] def stabSL (p : Fin 3 → ZMod 2) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p}
  one_mem' := by simp
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at hA hB ⊢
    rw [← Matrix.mulVec_mulVec, hB, hA]
  inv_mem' {A} hA := by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    calc ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p =
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p) := by rw [hA]
      _ = p := by
        rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

instance (p : Fin 3 → ZMod 2) : DecidablePred (· ∈ stabSL p) := fun A =>
  inferInstanceAs (Decidable ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p))

theorem card_stabSL' : ∀ p : Fin 3 → ZMod 2, p ≠ 0 →
    Fintype.card ↥(stabSL p) = 24 := by
  decide +kernel

theorem index_stabSL {p : Fin 3 → ZMod 2} (hp : p ≠ 0) : (stabSL p).index = 7 := by
  have h1 := (stabSL p).card_mul_index
  rw [Nat.card_eq_fintype_card, card_stabSL' p hp, card_SL_three_two'] at h1
  omega

variable {G : Type} [Group G]

theorem conjSub_eq_self_iff {g : G} {N : Subgroup G} :
    conjSub g N = N ↔ g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact mul_mem_conjSub hx
    · intro hx
      rw [← h, mem_conjSub] at hx
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at hx
  · intro h
    ext x
    rw [mem_conjSub]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have := h (g⁻¹ * x * g)
    rw [e] at this
    exact this

variable {T L V : Subgroup G}

theorem exists_gen_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) :
    ∃ z ∈ A, z ≠ 1 ∧ ∀ x ∈ A, x = 1 ∨ x = z := by
  obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  refine ⟨y, y.2, fun h => hy1 (Subtype.ext h), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have := hy ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem mem_normalizer_iff_of_gen {A : Subgroup G} {z : G} (hz : z ∈ A) (hz1 : z ≠ 1)
    (hgen : ∀ x ∈ A, x = 1 ∨ x = z) {g : G} :
    g ∈ Subgroup.normalizer (A : Set G) ↔ g * z * g⁻¹ = z := by
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    rcases hgen _ h1 with h | h
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases hgen x hx with rfl | rfl
      · simp
      · rw [hg]; exact hz
    · intro hx
      rcases hgen _ hx with h | h
      · have : x = 1 := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [this]
        exact A.one_mem
      · have : x = z := by
          have h2 : g * x * g⁻¹ = g * z * g⁻¹ := by rw [h, hg]
          have := congrArg (fun y => g⁻¹ * y * g) h2
          simpa [mul_assoc] using this
        rw [this]
        exact hz

theorem index_inf_normalizer_V1 [Finite G] (h : Hyp1281One G T L V 3)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hAV : A ≤ V) {z : G}
    (hz : z ∈ A) (hz1 : z ≠ 1) (hgen : ∀ x ∈ A, x = 1 ∨ x = z) :
    ((L ⊓ Subgroup.normalizer (A : Set G)).subgroupOf L).index = 7 := by
  obtain ⟨hcard, hsq, hcomm⟩ := h.card_sq
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hp0 : Multiplicative.toAdd (e ⟨z, hAV hz⟩) ≠ 0 := by
    intro h0
    apply hz1
    have h1 : e ⟨z, hAV hz⟩ = 1 := by rw [← ofAdd_toAdd (e ⟨z, hAV hz⟩), h0]; rfl
    have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    simpa using this
  have hsurj := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h)
  have heq : (L ⊓ Subgroup.normalizer (A : Set G)).subgroupOf L =
      (stabSL (Multiplicative.toAdd (e ⟨z, hAV hz⟩))).comap (repV hLV e) := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
    have hlz : (l : G) * z * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV l.2) z).mp (hAV hz)
    have hrep := repV_mulVec hLV e l ⟨z, hAV hz⟩ ⟨_, hlz⟩ rfl
    show (l : G) ∈ L ∧ (l : G) ∈ Subgroup.normalizer (A : Set G) ↔
      ((repV hLV e l : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (e ⟨z, hAV hz⟩)) =
          Multiplicative.toAdd (e ⟨z, hAV hz⟩)
    rw [mem_normalizer_iff_of_gen hz hz1 hgen]
    constructor
    · rintro ⟨-, hl⟩
      have h1 : (⟨(l : G) * z * (l : G)⁻¹, hlz⟩ : ↥V) = ⟨z, hAV hz⟩ := Subtype.ext hl
      rw [h1] at hrep
      have h2 := congrArg Multiplicative.toAdd hrep
      rw [toAdd_ofAdd] at h2
      exact h2.symm
    · intro hl
      refine ⟨l.2, ?_⟩
      have h1 : e ⟨(l : G) * z * (l : G)⁻¹, hlz⟩ = e ⟨z, hAV hz⟩ := by
        rw [hrep, hl, ofAdd_toAdd]
      exact congrArg Subtype.val (e.injective h1)
  rw [heq, Subgroup.index_comap_of_surjective _ hsurj, index_stabSL hp0]


theorem inf_normalizer_fsuU [Finite G] (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) :
    L ⊓ Subgroup.normalizer (fsuU T V : Set G) =
      L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  obtain ⟨z, hz, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hidx := index_inf_normalizer_V1 (S.hyp.hyp1281One h13322 hMod) hLV inf_le_left hz hz1 hgen
  have hNC := normalizer_eq_centralizer_of_card_two hV1
  have hle : (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)).subgroupOf L ≤
      (L ⊓ Subgroup.normalizer (fsuU T V : Set G)).subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
      le_normalizer_conjClosure V _ (Subgroup.mem_inf.mp hx).2⟩
  have hco : IsCoatom ((L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)).subgroupOf L) :=
    Subgroup.isCoatom_of_index_prime (by rw [hidx]; norm_num)
  rcases hco.le_iff.mp hle with htop | heq
  · exfalso
    have hLU : L ≤ Subgroup.normalizer (fsuU T V : Set G) := by
      intro l hl
      have h1 : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ Subgroup.normalizer (fsuU T V : Set G)).subgroupOf L := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at h1
      exact (Subgroup.mem_inf.mp h1).2
    have hHU : L32A.hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
      show Subgroup.centralizer (fsuV1 T V : Set G) ≤ _
      rw [← hNC]
      exact le_normalizer_conjClosure V _
    have hTH : T ≤ L32A.hz T V := le_sup_right.trans hF.L₁T_le_H
    have hX : (L ⊔ T) ⊔ L32A.hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
      sup_le (sup_le hLU (hTH.trans hHU)) hHU
    have hUeq : fsuU T V = conjClosure V (L32A.hz T V) := by
      show conjClosure V (Subgroup.normalizer (fsuV1 T V : Set G)) = _
      rw [hNC]
    have hUX : fsuU T V ≤ (L ⊔ T) ⊔ L32A.hz T V := by
      rw [hUeq]
      exact (conjClosure_le fun k hk v hv =>
        mul_mem (mul_mem hk (hF.V_le_H hv)) (inv_mem hk)).trans le_sup_right
    have hp : IsPGroup 2 ↥(fsuU T V) := by
      intro u
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have := hF.F911_2.2 u (by rw [← hUeq]; exact u.2)
      simpa using this
    have h1 := le_pCoreOf_of_le_normalizer 2 hUX hX hp
    rw [hF.o2_trivial] at h1
    exact hF.V_ne_bot (le_bot_iff.mp ((le_conjClosure V _).trans h1))
  · have h1 := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr inf_le_left, inf_eq_left.mpr inf_le_left] at h1

theorem conjSub_fsuU_eq_iff
    (hN : L ⊓ Subgroup.normalizer (fsuU T V : Set G) =
      L ⊓ Subgroup.normalizer (fsuV1 T V : Set G))
    {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hgen : ∀ x ∈ fsuV1 T V, x = 1 ∨ x = z)
    {l l' : G} (hl : l ∈ L) (hl' : l' ∈ L) :
    conjSub l (fsuU T V) = conjSub l' (fsuU T V) ↔ l * z * l⁻¹ = l' * z * l'⁻¹ := by
  have key : conjSub l (fsuU T V) = conjSub l' (fsuU T V) ↔
      conjSub (l'⁻¹ * l) (fsuU T V) = fsuU T V := by
    constructor
    · intro h
      rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    · intro h
      rw [show l = l' * (l'⁻¹ * l) by group, conjSub_mul, h]
  rw [key, conjSub_eq_self_iff]
  have hmem : l'⁻¹ * l ∈ L := mul_mem (inv_mem hl') hl
  constructor
  · intro h
    have h1 : l'⁻¹ * l ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
      rw [← hN]
      exact Subgroup.mem_inf.mpr ⟨hmem, h⟩
    have h2 := (mem_normalizer_iff_of_gen hz hz1 hgen).mp (Subgroup.mem_inf.mp h1).2
    calc l * z * l⁻¹ = l' * ((l'⁻¹ * l) * z * (l'⁻¹ * l)⁻¹) * l'⁻¹ := by group
      _ = l' * z * l'⁻¹ := by rw [h2]
  · intro h
    have h2 : (l'⁻¹ * l) * z * (l'⁻¹ * l)⁻¹ = z := by
      calc (l'⁻¹ * l) * z * (l'⁻¹ * l)⁻¹ = l'⁻¹ * (l * z * l⁻¹) * l' := by group
        _ = z := by rw [h]; group
    have h1 : l'⁻¹ * l ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hmem, (mem_normalizer_iff_of_gen hz hz1 hgen).mpr h2⟩
    rw [← hN] at h1
    exact (Subgroup.mem_inf.mp h1).2

theorem lemma14_7_12_one [Finite G] (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {l₁ l₂ l₃ l₄ : G} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (h₃ : l₃ ∈ L)
    (h₄ : l₄ ∈ L) (h₁₂ : conjSub l₁ (fsuU T V) ≠ conjSub l₂ (fsuU T V))
    (h₃₄ : conjSub l₃ (fsuU T V) ≠ conjSub l₄ (fsuU T V)) :
    ∃ l ∈ L, conjSub (l * l₁) (fsuU T V) = conjSub l₃ (fsuU T V) ∧
      conjSub (l * l₂) (fsuU T V) = conjSub l₄ (fsuU T V) := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  obtain ⟨z, hz, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hN := inf_normalizer_fsuU S hF h13322 hMod
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hpt : ∀ {l : G}, l ∈ L → l * z * l⁻¹ ∈ V ∧ l * z * l⁻¹ ≠ 1 := fun hl =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hLV hl) z).mp hzV, fun h1 => hz1 (conj_eq_one_iff.mp h1)⟩
  have hne : ∀ {l l' : G}, l ∈ L → l' ∈ L → conjSub l (fsuU T V) ≠ conjSub l' (fsuU T V) →
      l * z * l⁻¹ ≠ l' * z * l'⁻¹ := fun hl hl' h h' =>
    h ((conjSub_fsuU_eq_iff hN hz hz1 hgen hl hl').mpr h')
  obtain ⟨l, hl, hl₁, hl₂⟩ := exists_conj_eq_pair (S.hyp.hyp1281One h13322 hMod)
    (hpt h₁).1 (hpt h₂).1 (hpt h₃).1 (hpt h₄).1 (hpt h₁).2 (hpt h₂).2 (hpt h₃).2 (hpt h₄).2
    (hne h₁ h₂ h₁₂) (hne h₃ h₄ h₃₄)
  refine ⟨l, hl, (conjSub_fsuU_eq_iff hN hz hz1 hgen (mul_mem hl h₁) h₃).mpr ?_,
    (conjSub_fsuU_eq_iff hN hz hz1 hgen (mul_mem hl h₂) h₄).mpr ?_⟩
  · rw [← hl₁]; group
  · rw [← hl₂]; group

end L32A

end CFSG.Quasithin.H13
