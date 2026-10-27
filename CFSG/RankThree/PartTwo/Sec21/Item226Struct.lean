module

public import CFSG.RankThree.PartTwo.Sec21.Item226Config
public import CFSG.RankThree.PartTwo.Sec21.Item226LocalRank
import CFSG.RankThree.PartOne.FIS.SymBuild
public import CFSG.RankThree.PartTwo.Sec21.Item226Coord

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)

variable {G : Type} [Group G]

theorem perm_four_transp_subset {X : Set (Equiv.Perm (Fin 4))}
    (hinv : ∀ g : Equiv.Perm (Fin 4), ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, x * x = 1 ∧ x ≠ 1) (hgen : Subgroup.closure X = ⊤) :
    ∀ σ ∈ transp4, σ ∈ X := by
  by_contra hno
  push Not at hno
  obtain ⟨σ, hσ, hσX⟩ := hno
  have hT : ∀ y ∈ X, y ∉ transp4 := by
    intro y hy hyT
    obtain ⟨g, hg⟩ := perm_four_transp_class y hyT σ hσ
    exact hσX (hg ▸ hinv g y hy)
  let K : Subgroup (Equiv.Perm (Fin 4)) :=
    { carrier := ↑(insert 1 dtransp4)
      mul_mem' := fun ha hb => perm_four_dtransp_closed _ ha _ hb
      one_mem' := Finset.mem_insert_self _ _
      inv_mem' := fun {a} ha => by
        revert a
        decide +kernel }
  have hXK : Subgroup.closure X ≤ K := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases perm_four_involution y (h2 y hy).1 (h2 y hy).2 with ht | hd
    · exact (hT y hy ht).elim
    · exact Finset.mem_insert_of_mem hd
  have h01 : Equiv.swap (0 : Fin 4) 1 ∈ K := hXK (hgen ▸ Subgroup.mem_top _)
  have h01' : Equiv.swap (0 : Fin 4) 1 ∈ insert 1 dtransp4 := h01
  revert h01'
  decide +kernel

theorem mem_dStar_of_mem_transp4 [Finite G] {A L : Subgroup G}
    (e : starOf A L ≃* Equiv.Perm (Fin 4))
    (hgen : starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A)) :
    ∀ σ ∈ transp4, ((e.symm σ : starOf A L) : MulAut A) ∈ dStar A := by
  set S : Set (starOf A L) := {x | (x : MulAut A) ∈ dStar A} with hS
  have hSgen : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map (starOf A L).subtype =
        Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxH, hxD⟩
        exact ⟨⟨x, hxH⟩, hxD, rfl⟩
    rw [← hgen] at hmap
    rw [eq_top_iff]
    intro y _
    have : (y : MulAut A) ∈ (Subgroup.closure S).map (starOf A L).subtype := by
      rw [hmap]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [show y = z from Subtype.ext hzy.symm]
  have key := perm_four_transp_subset (X := e '' S)
    (by
      rintro g _ ⟨s, hs, rfl⟩
      refine ⟨e.symm g * s * (e.symm g)⁻¹, ?_, ?_⟩
      · exact conj_mem_dStar_of_mem_wStar (starOf_le_wStar A L (e.symm g).2) hs
      · simp)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, fun h => ?_⟩
      · rw [← map_mul, ← map_one e]
        exact congrArg e (Subtype.ext (mul_self_of_mem_dStar hs))
      · rw [MulEquiv.map_eq_one_iff] at h
        have h1 := hs.1.1
        rw [h, OneMemClass.coe_one, orderOf_one] at h1
        norm_num at h1)
    (by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, hSgen,
        Subgroup.map_top_of_surjective _ e.surjective])
  intro σ hσ
  obtain ⟨s, hs, hsσ⟩ := key σ hσ
  rw [← hsσ, MulEquiv.symm_apply_apply]
  exact hs

theorem exists_eq_vecMulVec_of_card_range (N : Mat4)
    (h : Nat.card (Set.range fun v : Fin 4 → ZMod 3 => N *ᵥ v) = 3) :
    ∃ a b : Fin 4 → ZMod 3, N = vecMulVec a b := by
  classical
  obtain ⟨v₀, hv₀⟩ : ∃ v, N *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    have hR : (Set.range fun v : Fin 4 → ZMod 3 => N *ᵥ v) = {0} := by
      ext w
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨v, hv⟩ => hv ▸ hall v, fun hw => ⟨0, by rw [hw, mulVec_zero]⟩⟩
    rw [hR, Nat.card_unique] at h
    norm_num at h
  set a := N *ᵥ v₀ with ha
  have hsub : (Set.range fun k : ZMod 3 => k • a) ⊆ Set.range fun v => N *ᵥ v := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k • v₀, by simp only [mulVec_smul, ha]⟩
  have hinj : Function.Injective fun k : ZMod 3 => k • a := by
    intro k k' hk
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv₀ (funext hall)
    have hki := congrFun hk i
    simp only [Pi.smul_apply, smul_eq_mul] at hki
    have key : ∀ k k' t : ZMod 3, t ≠ 0 → k * t = k' * t → k = k' := by decide
    exact key k k' (a i) hi hki
  have hcardS : Nat.card (Set.range fun k : ZMod 3 => k • a) = 3 := by
    rw [← Nat.card_congr (Equiv.ofInjective _ hinj), Nat.card_eq_fintype_card, ZMod.card]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h, hcardS])
  have hmul : ∀ j : Fin 4, ∃ k : ZMod 3, N *ᵥ Pi.single j 1 = k • a := by
    intro j
    have : N *ᵥ Pi.single j 1 ∈ Set.range fun k : ZMod 3 => k • a := by
      rw [heq]
      exact ⟨_, rfl⟩
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk.symm⟩
  choose b hb using hmul
  refine ⟨a, b, ?_⟩
  ext i j
  have := congrFun (hb j) i
  rw [mulVec_single_one] at this
  rw [vecMulVec_apply, mul_comm]
  simpa [Matrix.col_apply] using this

theorem exists_coord_sec21 [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) :
    ∃ F : Multiplicative (Fin 4 → ZMod 3) ≃* A, ∃ τ : Fin 6 → MulAut A,
      (∀ i, τ i ∈ dStar A) ∧ (∀ i, τ i ∈ starOf A L) ∧
      (∀ i, ((coordGL4 F (τ i) : GL (Fin 4) (ZMod 3)) : Mat4) = t0Mat i) ∧
      (∀ φ ∈ starOf A L, φ (F (Multiplicative.ofAdd (Pi.single 0 1))) =
        F (Multiplicative.ofAdd (Pi.single 0 1))) ∧
      ((F (Multiplicative.ofAdd (Pi.single 0 1)) : A) : G) = c := by
  obtain ⟨φ₀, -, -, n, -, -, -, -, ⟨eS⟩⟩ := exists_case_five h222 hpair hA81
  have hgen := (h222 G A E U c L hpair).1
  have hT := mem_dStar_of_mem_transp4 eS hgen
  obtain ⟨⟨hcE, -⟩, hc1, hLc, -⟩ := hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := by
    have hLc' : L ∈ thetaComponentsAt 3 c := hLc.1
    obtain ⟨L', -, hL'⟩ := hLc'
    rw [← hL']
    exact Subgroup.map_subtype_le _
  set c' : A := ⟨c, hcA⟩ with hc'
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hfixL : ∀ φ ∈ starOf A L, φ c' = c' := by
    rintro _ ⟨w, hw, rfl⟩
    apply Subtype.ext
    change (w : G) * c * (w : G)⁻¹ = c
    have hwc := Subgroup.mem_centralizer_singleton_iff.mp (hLC (Subgroup.mem_subgroupOf.mp hw))
    rw [hwc, mul_inv_cancel_right]
  set σ₄ : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 1 2 with hσ₄
  set ι : Equiv.Perm (Fin 4) →* MulAut A := (starOf A L).subtype.comp eS.symm.toMonoidHom
    with hι
  have hιinj : Function.Injective ι := (starOf A L).subtype_injective.comp eS.symm.injective
  have hιL : ∀ g, ι g ∈ starOf A L := fun g => (eS.symm g).2
  set x := ι (Equiv.swap 0 1 * Equiv.swap 2 3)
  set y := ι (Equiv.swap 0 2 * Equiv.swap 1 3)
  set σ := ι σ₄
  set r := ι (Equiv.swap 0 1)
  have hrel : ∀ g h : Equiv.Perm (Fin 4), g = h → ι g = ι h := fun g h e => by rw [e]
  have hx2 : x * x = 1 := by rw [← map_mul, ← map_one ι]; exact hrel _ _ (by decide)
  have hy2 : y * y = 1 := by rw [← map_mul, ← map_one ι]; exact hrel _ _ (by decide)
  have hxy : x * y = y * x := by rw [← map_mul, ← map_mul]; exact hrel _ _ (by decide)
  have hσ3 : σ * σ * σ = 1 := by
    rw [← map_mul, ← map_mul, ← map_one ι]; exact hrel _ _ (by decide)
  have hσx : σ * x = y * σ := by rw [← map_mul, ← map_mul]; exact hrel _ _ (by decide)
  have hσy : σ * y = x * y * σ := by
    rw [← map_mul, ← map_mul, ← map_mul]; exact hrel _ _ (by decide)
  have hne : x ≠ y := fun h => absurd (hιinj h) (by decide)
  have hrx : r * x = x * r := by rw [← map_mul, ← map_mul]; exact hrel _ _ (by decide)
  have hry : r * y = x * y * r := by
    rw [← map_mul, ← map_mul, ← map_mul]; exact hrel _ _ (by decide)
  have hr2 : r * r = 1 := by rw [← map_mul, ← map_one ι]; exact hrel _ _ (by decide)
  have hrσ : r * σ * (r * σ) ≠ 1 := by
    rw [← map_mul, ← map_mul, ← map_one ι]
    exact fun h => absurd (hιinj h) (by decide)
  have hrD : r ∈ dStar A := hT _ (by decide)
  obtain ⟨F, hF0, hX, hY, hS, hR⟩ := exists_coord_four hpair.mem_S.1.1 hA81 hx2 hy2 hxy hσ3 hσx
    hσy hne hrx hry hr2 hrσ hrD.1.2 hc'1 (hfixL _ (hιL _)) (hfixL _ (hιL _)) (hfixL _ (hιL _))
    (hfixL _ (hιL _))
  set τ : Fin 6 → MulAut A := fun i => ι (![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3,
    Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3] i) with hτ
  refine ⟨F, τ, fun i => ?_, fun i => hιL _, fun i => ?_, fun φ hφ => by rw [hF0]; exact hfixL φ hφ,
    by rw [hF0]⟩
  · exact hT _ (by fin_cases i <;> decide)
  · fin_cases i
    · change (coordGL4 F r : Mat4) = reflAt 0
      rw [hR]
      decide
    · have h1 : ι (Equiv.swap 0 2) = σ * r * (σ * σ) := by
        simp only [σ, r, ← map_mul]
        exact hrel _ _ (by decide)
      change (coordGL4 F (ι (Equiv.swap 0 2)) : Mat4) = reflAt 1
      rw [h1]
      simp only [map_mul, Units.val_mul, hS, hR]
      decide
    · have h1 : ι (Equiv.swap 0 3) = σ * σ * r * σ := by
        simp only [σ, r, ← map_mul]
        exact hrel _ _ (by decide)
      change (coordGL4 F (ι (Equiv.swap 0 3)) : Mat4) = reflAt 2
      rw [h1]
      simp only [map_mul, Units.val_mul, hS, hR]
      decide
    · have h1 : ι (Equiv.swap 1 2) = r * (σ * r * (σ * σ)) * r := by
        simp only [σ, r, ← map_mul]
        exact hrel _ _ (by decide)
      change (coordGL4 F (ι (Equiv.swap 1 2)) : Mat4) = reflAt 3
      rw [h1]
      simp only [map_mul, Units.val_mul, hS, hR]
      decide
    · have h1 : ι (Equiv.swap 1 3) = r * (σ * σ * r * σ) * r := by
        simp only [σ, r, ← map_mul]
        exact hrel _ _ (by decide)
      change (coordGL4 F (ι (Equiv.swap 1 3)) : Mat4) = reflAt 4
      rw [h1]
      simp only [map_mul, Units.val_mul, hS, hR]
      decide
    · have h1 : ι (Equiv.swap 2 3) =
          σ * r * (σ * σ) * (σ * σ * r * σ) * (σ * r * (σ * σ)) := by
        simp only [σ, r, ← map_mul]
        exact hrel _ _ (by decide)
      change (coordGL4 F (ι (Equiv.swap 2 3)) : Mat4) = reflAt 5
      rw [h1]
      simp only [map_mul, Units.val_mul, hS, hR]
      decide

theorem iSup_commOf_dStar_eq_top [Finite G] (h2130 : Item2130) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) :
    ⨆ φ ∈ dStar A, commOf φ = ⊤ := by
  set R : Subgroup A := ⨆ φ ∈ dStar A, commOf φ
  have hle : ∀ ψ ∈ wStar A, R.map ψ.toMonoidHom ≤ R := by
    rintro ψ ⟨w, rfl⟩
    rw [Subgroup.map_iSup]
    refine iSup_le fun φ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hφ => ?_
    rw [← commOf_conj]
    exact le_iSup₂_of_le _ (conj_mem_dStar w hφ) le_rfl
  have hR : ∀ ψ ∈ wStar A, R.map ψ.toMonoidHom = R := fun ψ hψ =>
    Subgroup.eq_of_le_of_card_ge (hle ψ hψ)
      (le_of_eq (Subgroup.card_map_of_injective ψ.injective).symm)
  rcases h2130 G A E U c L hpair R hR with hbot | htop
  · exfalso
    obtain ⟨-, ⟨φ, -, hφ⟩, -⟩ := h222 G A E U c L hpair
    have hφR : commOf φ ≤ R := le_iSup₂_of_le φ hφ le_rfl
    rw [hbot, le_bot_iff] at hφR
    have h3 := hφ.1.2
    rw [hφR, Subgroup.card_bot] at h3
    norm_num at h3
  · exact htop

theorem pow_two_or_three_of_orderOf_le {X : Type*} [Monoid X] {g : X} (h : orderOf g ≤ 3)
    (hpos : 0 < orderOf g) : g * g = 1 ∨ g * g * g = 1 := by
  have hpow := pow_orderOf_eq_one g
  interval_cases hk : orderOf g
  · left
    rw [pow_one] at hpow
    rw [hpow, one_mul]
  · left
    rw [← pow_two]
    exact hpow
  · right
    rw [← pow_three', ← hpow]

theorem exists_reflAt_of_mem_dStar_of_s3 [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hS3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))
    (F : Multiplicative (Fin 4 → ZMod 3) ≃* A) {τ : Fin 6 → MulAut A}
    (hτD : ∀ i, τ i ∈ dStar A)
    (hτM : ∀ i, ((coordGL4 F (τ i) : GL (Fin 4) (ZMod 3)) : Mat4) = t0Mat i)
    {d : MulAut A} (hd : d ∈ dStar A) :
    ∃ i < 45, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt i := by
  set M := ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) with hM
  have hcoe : ∀ g h : MulAut A, ((coordGL4 F (g * h) : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F g : Mat4) * (coordGL4 F h : Mat4) := fun g h => by rw [map_mul, Units.val_mul]
  have hM2 : M * M = 1 := by
    rw [hM, ← hcoe, mul_self_of_mem_dStar hd, map_one, Units.val_one]
  have hM1 : M ≠ 1 := by
    intro h1
    have : d = 1 := coordGL4_injective F (Units.ext (by rw [map_one, Units.val_one]; exact h1))
    have h2 := hd.1.1
    rw [this, orderOf_one] at h2
    norm_num at h2
  have hcomp : CompatT0 M := by
    intro i
    have hle := orderOf_mul_le_three_of_s3 hS3 hd (hτD i)
    rcases pow_two_or_three_of_orderOf_le hle (orderOf_pos _) with h | h
    · left
      rw [← hτM i, ← hcoe, ← hcoe, h, map_one, Units.val_one]
    · right
      rw [← hτM i, ← hcoe, ← hcoe, ← hcoe, h, map_one, Units.val_one]
  have hcard := card_commOf_eq_card_range4 hpair.mem_S.1.1.1 F d
  rw [hd.1.2] at hcard
  obtain ⟨a, b, hab⟩ := exists_eq_vecMulVec_of_card_range (M - 1) hcard.symm
  have hMab : M = 1 + vecMulVec a b := by rw [← hab]; abel
  have hmem := reflCheck_of_rankOne a b (hMab ▸ hM2) (hMab ▸ hM1) (hMab ▸ hcomp)
  rw [← hMab] at hmem
  obtain ⟨i, hi, hiM⟩ := List.mem_iff_getElem.mp hmem
  have hlen : reflList.length = 45 := rfl
  refine ⟨i, hlen ▸ hi, ?_⟩
  rw [reflAt, List.getD_eq_getElem _ _ hi, hiM]

theorem exists_reflAt_of_mem_dStar [Finite G] (h223 : Item223)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    {n : ℕ} (eL : L ≃* projSU 4 2 n) (F : Multiplicative (Fin 4 → ZMod 3) ≃* A)
    {τ : Fin 6 → MulAut A} (hτD : ∀ i, τ i ∈ dStar A)
    (hτM : ∀ i, ((coordGL4 F (τ i) : GL (Fin 4) (ZMod 3)) : Mat4) = t0Mat i)
    {d : MulAut A} (hd : d ∈ dStar A) :
    ∃ i < 45, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt i :=
  exists_reflAt_of_mem_dStar_of_s3 hpair (s3_of_item223 h223 hpair hA81 eL) F hτD hτM hd

theorem apply_coord4 {A' : Subgroup G} (F : Multiplicative (Fin 4 → ZMod 3) ≃* A') (φ : MulAut A')
    (v : Fin 4 → ZMod 3) :
    φ (F (Multiplicative.ofAdd v)) =
      F (Multiplicative.ofAdd (((coordGL4 F φ : GL (Fin 4) (ZMod 3)) : Mat4) *ᵥ v)) := by
  rw [coordGL4_mulVec, coordLin4_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem dStar_matrices_eq_s5 [Finite G] (h2130 : Item2130) (h222 : Item222) (h223 : Item223)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    (hK : KOfWellDefined A)
    (htr : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ)
    (F : Multiplicative (Fin 4 → ZMod 3) ≃* A) {τ : Fin 6 → MulAut A} (hτD : ∀ i, τ i ∈ dStar A)
    (hτM : ∀ i, ((coordGL4 F (τ i) : GL (Fin 4) (ZMod 3)) : Mat4) = t0Mat i) :
    (∀ M, (∃ d ∈ dStar A, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = M) ↔
        ∃ i ∈ s5aL, M = reflAt i) ∨
      (∀ M, (∃ d ∈ dStar A, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = M) ↔
        ∃ i ∈ s5bL, M = reflAt i) := by
  obtain ⟨φ₀, -, -, n, -, -, ⟨eL⟩, -, -⟩ := exists_case_five h222 hpair hA81
  set 𝒟 : Set Mat4 := {M | ∃ d ∈ dStar A, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = M}
    with h𝒟
  have hcoe : ∀ g h : MulAut A, ((coordGL4 F (g * h) : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F g : Mat4) * (coordGL4 F h : Mat4) := fun g h => by rw [map_mul, Units.val_mul]
  have hinj : ∀ g h : MulAut A, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F h : Mat4) → g = h := fun g h e => coordGL4_injective F (Units.ext e)
  refine config_eq_s5 𝒟 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨i, hi, he⟩ := exists_reflAt_of_mem_dStar h223 hpair hA81 eL F hτD hτM hd
    exact ⟨i, hi, he⟩
  · intro i hi
    have hi6 := List.mem_range.mp hi
    exact ⟨τ ⟨i, hi6⟩, hτD _, hτM _⟩
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    refine ⟨d * e * d, ?_, by rw [hcoe, hcoe]⟩
    have h := conj_mem_dStar_of_mem_wStar (dStar_subset_wStar A hd) he
    rwa [inv_eq_of_mul_eq_one_right (mul_self_of_mem_dStar hd)] at h
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    have hle := orderOf_mul_le_three_of_four h223 hpair hA81 eL hd he
    rcases pow_two_or_three_of_orderOf_le hle (orderOf_pos _) with h | h
    · left
      rw [← hcoe, ← hcoe, h, map_one, Units.val_one]
    · right
      rw [← hcoe, ← hcoe, ← hcoe, h, map_one, Units.val_one]
  · rintro i j k ⟨di, hdi, hi⟩ ⟨dj, hdj, hj⟩ ⟨dk, hdk, hk⟩ ⟨hij, hik, hjk, cij, cik, cjk⟩
    have hc : ∀ {g h : MulAut A} {a b : ℕ}, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
        reflAt a → ((coordGL4 F h : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt b → CommAt a b →
        g * h = h * g := fun {g h a b} ha hb hab => hinj _ _ (by rw [hcoe, hcoe, ha, hb]; exact hab)
    have hn : ∀ {g h : MulAut A} {a b : ℕ}, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
        reflAt a → ((coordGL4 F h : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt b →
        reflAt a ≠ reflAt b → g ≠ h := fun {g h a b} ha hb hab e => hab (by rw [← ha, ← hb, e])
    exact false_of_three_commuting_dStar h222 h223 hpair hA81 hK htr hdi hdj hdk
      (hn hi hj hij) (hn hi hk hik) (hn hj hk hjk) (hc hi hj cij) (hc hi hk cik) (hc hj hk cjk)
  · by_contra hall
    push Not at hall
    have hfix : ∀ φ ∈ dStar A, φ (F (Multiplicative.ofAdd (Pi.single 0 1))) =
        F (Multiplicative.ofAdd (Pi.single 0 1)) := fun φ hφ => by
      rw [apply_coord4, hall _ ⟨φ, hφ, rfl⟩]
    have h1 := fixed_dStar_eq_one h2130 h222 hpair hfix
    rw [MulEquiv.map_eq_one_iff] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp at h2
  · by_contra hall
    push Not at hall
    set W : Subgroup A :=
      { carrier := {a | Multiplicative.toAdd (F.symm a) 0 = 0}
        mul_mem' := fun {a b} ha hb => by
          change Multiplicative.toAdd (F.symm a) 0 = 0 at ha
          change Multiplicative.toAdd (F.symm b) 0 = 0 at hb
          change Multiplicative.toAdd (F.symm (a * b)) 0 = 0
          rw [map_mul, toAdd_mul, Pi.add_apply, ha, hb, add_zero]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          change Multiplicative.toAdd (F.symm a) 0 = 0 at ha
          change Multiplicative.toAdd (F.symm a⁻¹) 0 = 0
          rw [map_inv, toAdd_inv, Pi.neg_apply, ha]
          rfl } with hW
    have hcW : ∀ φ ∈ dStar A, commOf φ ≤ W := by
      intro φ hφ
      rw [commOf, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      change Multiplicative.toAdd (F.symm (a⁻¹ * φ a)) 0 = 0
      set v := Multiplicative.toAdd (F.symm a) with hv
      have ha : a = F (Multiplicative.ofAdd v) := by simp [hv]
      rw [ha, apply_coord4, ← map_inv, ← map_mul, MulEquiv.symm_apply_apply, toAdd_mul,
        toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
      have hrow := hall _ ⟨φ, hφ, rfl⟩
      have : ((((coordGL4 F φ : GL (Fin 4) (ZMod 3)) : Mat4) - 1) *ᵥ v) 0 = 0 := by
        simp only [mulVec, dotProduct, hrow, zero_mul, Finset.sum_const_zero]
      rw [sub_mulVec, one_mulVec, Pi.sub_apply] at this
      rw [Pi.add_apply, Pi.neg_apply]
      linear_combination this
    have htop := iSup_commOf_dStar_eq_top h2130 h222 hpair
    have hle : (⨆ φ ∈ dStar A, commOf φ) ≤ W := iSup₂_le hcW
    rw [htop] at hle
    have hmem : F (Multiplicative.ofAdd (Pi.single 0 1)) ∈ W := hle (Subgroup.mem_top _)
    change Multiplicative.toAdd (F.symm (F (Multiplicative.ofAdd (Pi.single 0 1)))) 0 = 0 at hmem
    simp at hmem

open CFSG.Permutation.SymmetricCoxeter in
theorem nonempty_mulEquiv_perm_five_of_chain {A : Subgroup G}
    (F : Multiplicative (Fin 4 → ZMod 3) ≃* A) (cfg : List ℕ) (a₀ a₁ a₂ a₃ : ℕ)
    (cert : List (ℕ × ℕ × ℕ))
    (hspec : reflAt a₀ * reflAt a₁ * reflAt a₀ = reflAt a₁ * reflAt a₀ * reflAt a₁ ∧
      reflAt a₁ * reflAt a₂ * reflAt a₁ = reflAt a₂ * reflAt a₁ * reflAt a₂ ∧
      reflAt a₂ * reflAt a₃ * reflAt a₂ = reflAt a₃ * reflAt a₂ * reflAt a₃ ∧
      CommAt a₀ a₂ ∧ CommAt a₀ a₃ ∧ CommAt a₁ a₃ ∧ reflAt a₀ ≠ reflAt a₁)
    (hgen : checkDeriv [a₀, a₁, a₂, a₃] cert = true ∧
      ∀ i ∈ cfg, i ∈ [a₀, a₁, a₂, a₃] ++ cert.map Prod.fst)
    (hD : ∀ M, (∃ d ∈ dStar A, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) = M) ↔
      ∃ i ∈ cfg, M = reflAt i)
    (hch : a₀ ∈ cfg ∧ a₁ ∈ cfg ∧ a₂ ∈ cfg ∧ a₃ ∈ cfg) :
    Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨b01, b12, b23, c02, c03, c13, hne⟩ := hspec
  have hcoe : ∀ g h : MulAut A, ((coordGL4 F (g * h) : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F g : Mat4) * (coordGL4 F h : Mat4) := fun g h => by rw [map_mul, Units.val_mul]
  have hinj : ∀ g h : MulAut A, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F h : Mat4) → g = h := fun g h e => coordGL4_injective F (Units.ext e)
  have hpre : ∀ a ∈ cfg, ∃ d ∈ dStar A, ((coordGL4 F d : GL (Fin 4) (ZMod 3)) : Mat4) =
      reflAt a := fun a ha => (hD _).mpr ⟨a, ha, rfl⟩
  obtain ⟨d₀, hd₀, e₀⟩ := hpre a₀ hch.1
  obtain ⟨d₁, hd₁, e₁⟩ := hpre a₁ hch.2.1
  obtain ⟨d₂, hd₂, e₂⟩ := hpre a₂ hch.2.2.1
  obtain ⟨d₃, hd₃, e₃⟩ := hpre a₃ hch.2.2.2
  have hbr : ∀ {g h : MulAut A} {a b : ℕ}, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
      reflAt a → ((coordGL4 F h : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt b →
      reflAt a * reflAt b * reflAt a = reflAt b * reflAt a * reflAt b → g * h * g = h * g * h :=
    fun {g h a b} ha hb hab => hinj _ _ (by rw [hcoe, hcoe, hcoe, hcoe, ha, hb]; exact hab)
  have hcm : ∀ {g h : MulAut A} {a b : ℕ}, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
      reflAt a → ((coordGL4 F h : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt b → CommAt a b →
      g * h = h * g := fun {g h a b} ha hb hab => hinj _ _ (by rw [hcoe, hcoe, ha, hb]; exact hab)
  set Z := Subgroup.closure (dStar A) with hZ
  set z₀ : Z := ⟨d₀, Subgroup.subset_closure hd₀⟩
  set z₁ : Z := ⟨d₁, Subgroup.subset_closure hd₁⟩
  set z₂ : Z := ⟨d₂, Subgroup.subset_closure hd₂⟩
  set z₃ : Z := ⟨d₃, Subgroup.subset_closure hd₃⟩
  set x : ℕ → Z := fun i => if i = 0 then z₀ else if i = 1 then z₁ else if i = 2 then z₂
    else if i = 3 then z₃ else 1 with hx
  have hsq : ∀ {d : MulAut A}, d ∈ dStar A → ∀ h : d ∈ Z, (⟨d, h⟩ : Z) * ⟨d, h⟩ = 1 :=
    fun hd h => Subtype.ext (mul_self_of_mem_dStar hd)
  have hcox : IsCoxeterA 4 x := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · interval_cases i
      · exact hsq hd₀ _
      · exact hsq hd₁ _
      · exact hsq hd₂ _
      · exact hsq hd₃ _
    · have hi3 : i < 3 := by omega
      interval_cases i
      · exact Subtype.ext (hbr e₀ e₁ b01)
      · exact Subtype.ext (hbr e₁ e₂ b12)
      · exact Subtype.ext (hbr e₂ e₃ b23)
    · have hi2 : i < 2 := by omega
      interval_cases i
      · interval_cases j
        · exact Subtype.ext (hcm e₀ e₂ c02)
        · exact Subtype.ext (hcm e₀ e₃ c03)
      · interval_cases j
        exact Subtype.ext (hcm e₁ e₃ c13)
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 4 x hcox
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    set S : Subgroup (MulAut A) := Subgroup.closure ({d₀, d₁, d₂, d₃} : Set (MulAut A))
    have hS : ∀ i ∈ [a₀, a₁, a₂, a₃] ++ cert.map Prod.fst, reflAt i ∈
        {M | ∃ g ∈ S, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) = M} := by
      refine checkDeriv_sound _ ?_ cert [a₀, a₁, a₂, a₃] ?_ hgen.1
      · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
        exact ⟨g * h * g, S.mul_mem (S.mul_mem hg hh) hg, by rw [hcoe, hcoe]⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact ⟨d₀, Subgroup.subset_closure (by simp), e₀⟩
        · exact ⟨d₁, Subgroup.subset_closure (by simp), e₁⟩
        · exact ⟨d₂, Subgroup.subset_closure (by simp), e₂⟩
        · exact ⟨d₃, Subgroup.subset_closure (by simp), e₃⟩
    have hDS : dStar A ⊆ S := by
      intro d hd
      obtain ⟨i, hi, hiM⟩ := (hD _).mp ⟨d, hd, rfl⟩
      obtain ⟨g, hg, hgM⟩ := hS i (hgen.2 i hi)
      rwa [← hinj g d (by rw [hgM, hiM])]
    have hrange : ∀ k : Fin 4, x k ∈ ψ.range := fun k => ⟨_, hψ k k.2⟩
    rw [eq_top_iff]
    intro w _
    have hw : (w : MulAut A) ∈ S := (Subgroup.closure_le S).mpr hDS w.2
    have hmapS : (Subgroup.closure ({z₀, z₁, z₂, z₃} : Set Z)).map Z.subtype = S := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq, z₀, z₁, z₂, z₃]
    rw [← hmapS] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    have hww : w = w' := Subtype.ext hww'.symm
    rw [hww]
    refine (Subgroup.closure_le _).mpr ?_ hw'
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hrange 0
    · exact hrange 1
    · exact hrange 2
    · exact hrange 3
  have hinjψ : Function.Injective ψ := by
    refine CFSG.RankThree.PartOne.FIS.injective_of_ne_one (m := 2) le_rfl ψ ?_
    rw [hψ 0 (by norm_num), hψ 1 (by norm_num)]
    intro h
    apply hne
    have h' : d₀ * d₁ = 1 := congrArg Subtype.val h
    have h01 : d₀ = d₁ := by
      calc d₀ = d₀ * (d₁ * d₁) := by rw [mul_self_of_mem_dStar hd₁, mul_one]
        _ = d₁ := by rw [← mul_assoc, h', one_mul]
    rw [← e₀, ← e₁, h01]
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinjψ, hsurj⟩).symm⟩

theorem nonempty_closure_dStar_mulEquiv_perm_five [Finite G] (h2130 : Item2130) (h222 : Item222)
    (h223 : Item223) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA81 : Nat.card A = 3 ^ 4) (hK : KOfWellDefined A)
    (htr : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ) :
    Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨F, τ, hτD, -, hτM, -, -⟩ := exists_coord_sec21 h222 hpair hA81
  rcases dStar_matrices_eq_s5 h2130 h222 h223 hpair hA81 hK htr F hτD hτM with hD | hD
  · exact nonempty_mulEquiv_perm_five_of_chain F s5aL 0 1 5 43 s5aChainCert s5aChain_spec
      s5aChain_gen hD (by decide)
  · exact nonempty_mulEquiv_perm_five_of_chain F s5bL 0 1 5 38 s5bChainCert s5bChain_spec
      s5bChain_gen hD (by decide)

theorem reflAt_central : ∀ i ∈ List.range 45, (∀ j ∈ List.range 6, CommAt i j) → i = 36 := by
  decide +kernel

theorem reflAt_36_sub_one_mulVec : ∀ v0 v1 v2 v3 : ZMod 3,
    (reflAt 36 - 1) *ᵥ ![v0, v1, v2, v3] = v0 • Pi.single 0 1 := by
  decide +kernel

theorem centralReflection_of_s3 [Finite G] (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    (hS3 : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ * φ ≠ φ * ψ →
      Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))
    {d : MulAut A} (hd : d ∈ dStar A) (hdL : ∀ x ∈ starOf A L, x * d = d * x) :
    (commOf d).map A.subtype = Subgroup.zpowers c ∧
      ∀ d' ∈ dStar A, (∀ x ∈ starOf A L, x * d' = d' * x) → d' = d := by
  obtain ⟨F, τ, hτD, hτL, hτM, -, hFc⟩ := exists_coord_sec21 h222 hpair hA81
  have hcoe : ∀ g h : MulAut A, ((coordGL4 F (g * h) : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F g : Mat4) * (coordGL4 F h : Mat4) := fun g h => by rw [map_mul, Units.val_mul]
  have hinj : ∀ g h : MulAut A, ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4) =
      (coordGL4 F h : Mat4) → g = h := fun g h e => coordGL4_injective F (Units.ext e)
  have hM36 : ∀ {d' : MulAut A}, d' ∈ dStar A → (∀ x ∈ starOf A L, x * d' = d' * x) →
      ((coordGL4 F d' : GL (Fin 4) (ZMod 3)) : Mat4) = reflAt 36 := by
    intro d' hd' hd'L
    obtain ⟨i, hi, hiM⟩ := exists_reflAt_of_mem_dStar_of_s3 hpair hS3 F hτD hτM hd'
    have h36 : i = 36 := reflAt_central i (List.mem_range.mpr hi) fun j hj => by
      have hj6 := List.mem_range.mp hj
      have h := hd'L _ (hτL ⟨j, hj6⟩)
      have hm := congrArg (fun g => ((coordGL4 F g : GL (Fin 4) (ZMod 3)) : Mat4)) h
      simp only [hcoe, hiM, hτM] at hm
      exact hm.symm
    rw [hiM, h36]
  have hdM := hM36 hd hdL
  refine ⟨?_, fun d' hd' hd'L => hinj _ _ (by rw [hM36 hd' hd'L, hdM])⟩
  set c₀ := F (Multiplicative.ofAdd (Pi.single 0 1)) with hc₀
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hpair.mem_S.1.1.2 a a.2)
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    rw [hc₀, MulEquiv.map_eq_one_iff] at h
    have h2 := congrFun (congrArg Multiplicative.toAdd h) 0
    simp at h2
  have hle : commOf d ≤ Subgroup.zpowers c₀ := by
    rw [commOf, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    set v := Multiplicative.toAdd (F.symm a) with hv
    have ha : a = F (Multiplicative.ofAdd v) := by simp [hv]
    have hve : v = ![v 0, v 1, v 2, v 3] := by
      ext i
      fin_cases i <;> rfl
    have hkey : a⁻¹ * d a = c₀ ^ (v 0).val := by
      rw [ha, apply_coord4, hdM, ← map_inv, ← map_mul]
      have h1 : -v + reflAt 36 *ᵥ v = v 0 • Pi.single 0 1 := by
        have := reflAt_36_sub_one_mulVec (v 0) (v 1) (v 2) (v 3)
        rw [← hve, sub_mulVec, one_mulVec] at this
        rw [← this]
        abel
      rw [hc₀, ← map_pow, ← ofAdd_nsmul]
      congr 1
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
      exact h1
    show a⁻¹ * d a ∈ Subgroup.zpowers c₀
    rw [hkey]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c₀) _
  have hcard : Nat.card (Subgroup.zpowers c₀) ≤ Nat.card (commOf d) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hA3 c₀) hc₀1, hd.1.2]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq, MonoidHom.map_zpowers, Subgroup.coe_subtype, hc₀, hFc]

theorem rank3II_22_6_centralReflection (h222 : Item222)
    (h223 : Item223) : Item226CentralReflection := by
  intro G _ _ A E U c L hpair hA81 d hd hdL
  obtain ⟨-, -, -, n, -, -, ⟨eL⟩, -, -⟩ := exists_case_five h222 hpair hA81
  exact centralReflection_of_s3 h222 hpair hA81 (s3_of_item223 h223 hpair hA81 eL) hd hdL

@[expose] def finThreeEquivTail : Fin 3 ≃ {x : Fin 5 // 2 ≤ x.val} where
  toFun i := ⟨⟨i.val + 2, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 2, by omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    ext
    have := x.2
    simp only
    omega

@[expose] def permThreeTail : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 5) :=
  Equiv.Perm.extendDomainHom finThreeEquivTail

theorem permThreeTail_swap01 : permThreeTail (Equiv.swap 0 1) = Equiv.swap 2 3 := by
  decide

theorem permThreeTail_swap12 : permThreeTail (Equiv.swap 1 2) = Equiv.swap 3 4 := by
  decide

theorem localSet_transp5_swap01 :
    Sec7.localSet (↑transp5 : Set (Equiv.Perm (Fin 5))) (Equiv.swap 0 1) =
      {Equiv.swap 2 3, Equiv.swap 2 4, Equiv.swap 3 4} := by
  have key : ∀ a : Equiv.Perm (Fin 5), (a ∈ transp5 ∧ a * Equiv.swap 0 1 = Equiv.swap 0 1 * a ∧
      a ≠ Equiv.swap 0 1) ↔ (a = Equiv.swap 2 3 ∨ a = Equiv.swap 2 4 ∨ a = Equiv.swap 3 4) := by
    decide +kernel
  ext a
  simp only [Sec7.localSet, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
  exact key a

theorem nonempty_closure_localSet_swap01 :
    Nonempty (Subgroup.closure (Sec7.localSet (↑transp5 : Set (Equiv.Perm (Fin 5)))
      (Equiv.swap 0 1)) ≃* Equiv.Perm (Fin 3)) := by
  have hgen3 : Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3))) =
      ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 2 =>
        (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 3))) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have hsub : (Set.range fun i : Fin 2 =>
        (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 3))) =
        {Equiv.swap 0 1, Equiv.swap 1 2} := by
      ext τ
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
      constructor
      · rintro (h | h) <;> [left; right] <;> rw [← h] <;> decide
      · rintro (h | h) <;> [left; right] <;> rw [h] <;> decide
    rw [hsub] at hσ
    exact (Submonoid.closure_le.mpr Subgroup.subset_closure :
      Submonoid.closure _ ≤ (Subgroup.closure _).toSubmonoid) hσ
  have hrange : permThreeTail.range = Subgroup.closure (Sec7.localSet
      (↑transp5 : Set (Equiv.Perm (Fin 5))) (Equiv.swap 0 1)) := by
    rw [localSet_transp5_swap01]
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← hgen3, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨τ, hτ, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
      rcases hτ with rfl | rfl
      · rw [permThreeTail_swap01]
        exact Subgroup.subset_closure (by simp)
      · rw [permThreeTail_swap12]
        exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      intro τ hτ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
      rcases hτ with rfl | rfl | rfl
      · exact ⟨_, permThreeTail_swap01⟩
      · exact ⟨Equiv.swap 0 2, by decide⟩
      · exact ⟨_, permThreeTail_swap12⟩
  exact ⟨((MonoidHom.ofInjective (Equiv.Perm.extendDomainHom_injective finThreeEquivTail)).trans
    (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonempty_closure_localSet_transp5 {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ transp5) :
    Nonempty (Subgroup.closure (Sec7.localSet (↑transp5 : Set (Equiv.Perm (Fin 5))) σ) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨g, rfl⟩ := perm_five_transp_class σ hσ
  have hconj : ∀ g : Equiv.Perm (Fin 5), ∀ τ ∈ transp5, g * τ * g⁻¹ ∈ transp5 := by
    decide +kernel
  have himg : Sec7.localSet (↑transp5 : Set (Equiv.Perm (Fin 5))) (g * Equiv.swap 0 1 * g⁻¹) =
      (MulAut.conj g).toMonoidHom '' Sec7.localSet (↑transp5 : Set (Equiv.Perm (Fin 5)))
        (Equiv.swap 0 1) := by
    ext b
    simp only [Sec7.localSet, Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hb, hbc, hne⟩
      refine ⟨g⁻¹ * b * g, ⟨?_, ?_, ?_⟩, by group⟩
      · have := hconj g⁻¹ b hb
        simpa using this
      · calc g⁻¹ * b * g * Equiv.swap 0 1 = g⁻¹ * (b * (g * Equiv.swap 0 1 * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * Equiv.swap 0 1 * g⁻¹) * b) * g := by rw [hbc]
          _ = Equiv.swap 0 1 * (g⁻¹ * b * g) := by group
      · intro h
        apply hne
        rw [← h]
        group
    · rintro ⟨a, ⟨ha, hac, hne⟩, rfl⟩
      refine ⟨hconj g a ha, ?_, ?_⟩
      · calc g * a * g⁻¹ * (g * Equiv.swap 0 1 * g⁻¹) = g * (a * Equiv.swap 0 1) * g⁻¹ := by
              group
          _ = g * (Equiv.swap 0 1 * a) * g⁻¹ := by rw [hac]
          _ = g * Equiv.swap 0 1 * g⁻¹ * (g * a * g⁻¹) := by group
      · intro h
        apply hne
        have := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using this
  obtain ⟨e⟩ := nonempty_closure_localSet_swap01
  rw [himg, ← MonoidHom.map_closure]
  exact ⟨((Subgroup.closure _).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e⟩

theorem nonempty_closure_localSet_map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (D : Set X) (d : X) :
    Nonempty (Subgroup.closure (Sec7.localSet D d) ≃*
      Subgroup.closure (Sec7.localSet (φ '' D) (φ d))) := by
  have himg : φ.toMonoidHom '' Sec7.localSet D d = Sec7.localSet (φ '' D) (φ d) := by
    ext b
    simp only [Sec7.localSet, Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨a, ⟨ha, had, hne⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by rw [← map_mul, had, map_mul], fun h => hne (φ.injective h)⟩
    · rintro ⟨⟨a, ha, rfl⟩, had, hne⟩
      refine ⟨a, ⟨ha, φ.injective (by rw [map_mul, map_mul, had]), fun h => hne (h ▸ rfl)⟩, rfl⟩
  rw [← himg, ← MonoidHom.map_closure]
  exact ⟨(Subgroup.closure _).equivMapOfInjective _ φ.injective⟩

theorem nonempty_closure_localSet_dStar_equiv {A : Subgroup G} (t : Subgroup.closure (dStar A)) :
    Nonempty (Subgroup.closure (Sec7.localSet (dStar A) (t : MulAut A)) ≃*
      Subgroup.closure (Sec7.localSet (dStarIn A) t)) := by
  have himg : (Subgroup.closure (dStar A)).subtype '' Sec7.localSet (dStarIn A) t =
      Sec7.localSet (dStar A) (t : MulAut A) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyD, hyt, hne⟩, rfl⟩
      exact ⟨hyD, congrArg Subtype.val hyt, fun h => hne (Subtype.ext h)⟩
    · rintro ⟨hxD, hxt, hne⟩
      exact ⟨⟨x, Subgroup.subset_closure hxD⟩,
        ⟨hxD, Subtype.ext hxt, fun h => hne (congrArg Subtype.val h)⟩, rfl⟩
  rw [← himg, ← MonoidHom.map_closure]
  exact ⟨((Subgroup.closure _).equivMapOfInjective _
    (Subgroup.closure (dStar A)).subtype_injective).symm⟩

theorem rank3II_22_6_localSetS3 (h2130 : Item2130) (h222 : Item222) (h223 : Item223)
    (hKW : KOfWellDefinedAll) : Item226LocalSetS3 := by
  intro G _ _ A E U c L hpair hA81 htr t ht
  have hK := hKW G A E U c L hpair
  obtain ⟨e5⟩ := nonempty_closure_dStar_mulEquiv_perm_five h2130 h222 h223 hpair hA81 hK htr
  obtain ⟨φ₀, -, hφ₀D, n, -, -, ⟨eL⟩, -, -⟩ := exists_case_five h222 hpair hA81
  have hD3 := isThreeTranspositions_dStarIn_of_four h223 hpair hA81 eL
  have hX5 : e5 '' dStarIn A = ↑transp5 := by
    apply perm_five_eq_transp
    · rintro g _ ⟨y, hy, rfl⟩
      refine ⟨e5.symm g * y * (e5.symm g)⁻¹, hD3.1.1 _ y hy, ?_⟩
      simp
    · rintro _ ⟨y, hy, rfl⟩
      have hy2 := hD3.1.2.1 y hy
      refine ⟨by rw [← map_mul, Sec7.mul_self_eq_one_of_orderOf_eq_two hy2, map_one],
        fun h => ?_⟩
      rw [MulEquiv.map_eq_one_iff] at h
      rw [h, orderOf_one] at hy2
      norm_num at hy2
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, MulEquiv.orderOf_eq]
      exact hD3.2 x hx y hy
    · exact ⟨_, ⟨⟨φ₀, Subgroup.subset_closure hφ₀D⟩, hφ₀D, rfl⟩⟩
  set t' : Subgroup.closure (dStar A) := ⟨t, Subgroup.subset_closure ht⟩ with ht'
  have hσ : e5 t' ∈ transp5 := by
    have h : e5 t' ∈ e5 '' dStarIn A := ⟨t', ht, rfl⟩
    rw [hX5] at h
    exact h
  obtain ⟨e1⟩ := nonempty_closure_localSet_dStar_equiv t'
  obtain ⟨e2⟩ := nonempty_closure_localSet_map e5 (dStarIn A) t'
  obtain ⟨e3⟩ := nonempty_closure_localSet_transp5 hσ
  exact ⟨e1.trans (e2.trans ((MulEquiv.subgroupCongr (by rw [hX5])).trans e3))⟩

end CFSG.RankThree.PartTwo.Sec21
