module

public import CFSG.Quasithin.Vol2.Ch12Sec6Nc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N Equiv
open scoped IsMulCommutative

@[expose] def NoFuse1261926 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V →
      ∀ v z g : G, F.Nonsing v →
        Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        z ∈ V ⊓ Subgroup.centralizer (L : Set G) → z ≠ 1 → g * v * g⁻¹ ≠ v * z

@[expose] def FactA8SolvNormPartition : Prop :=
  ∀ Y P : Subgroup (Equiv.Perm (Fin 8)), Y ≤ alternatingGroup (Fin 8) → 9 ∣ Nat.card Y →
    ¬ 5 ∣ Nat.card Y → P ≤ alternatingGroup (Fin 8) → IsPGroup 2 P → 32 ≤ Nat.card P →
    P ≤ Subgroup.normalizer (Y : Set (Equiv.Perm (Fin 8))) →
      ∃ S : Finset (Fin 8), S.card = 4 ∧
        ∀ y ∈ Y, (∀ i, y i ∈ S ↔ i ∈ S) ∨ (∀ i, y i ∈ S ↔ i ∉ S)

namespace S126L19

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem lt_four_of_maps {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, i.val < 4 → (σ i).val < 4)
    {i : Fin 8} (hi : (σ i).val < 4) : i.val < 4 := by
  by_contra hc
  set A : Finset (Fin 8) := Finset.univ.filter fun j => j.val < 4 with hA
  have hiA : i ∉ A := by simp [hA, hc]
  have hcard : (insert i A).card ≤ A.card := by
    refine Finset.card_le_card_of_injOn σ (fun j hj => ?_) σ.injective.injOn
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hA]
    rcases hj with rfl | hj
    · exact hi
    · exact h j (by simpa [hA] using hj)
  rw [Finset.card_insert_of_notMem hiA] at hcard
  omega

theorem lt_four_of_maps' {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, i.val < 4 → 4 ≤ (σ i).val)
    {i : Fin 8} (hi : 4 ≤ (σ i).val) : i.val < 4 := by
  by_contra hc
  set A : Finset (Fin 8) := Finset.univ.filter fun j => j.val < 4 with hA
  set B : Finset (Fin 8) := Finset.univ.filter fun j => 4 ≤ j.val with hB
  have hAB : A.card = B.card := by decide
  have hiA : i ∉ A := by simp [hA, hc]
  have hcard : (insert i A).card ≤ B.card := by
    refine Finset.card_le_card_of_injOn σ (fun j hj => ?_) σ.injective.injOn
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hB]
    rcases hj with rfl | hj
    · exact hi
    · exact h j (by simpa [hA] using hj)
  rw [Finset.card_insert_of_notMem hiA] at hcard
  omega

theorem blocks_of_presPart {σ : Perm (Fin 8)} (hσ : PresPart σ) :
    (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)) := by
  rcases hσ.2 with h | h
  · exact Or.inl fun i => ⟨h i, lt_four_of_maps h⟩
  · exact Or.inr fun i => ⟨h i, lt_four_of_maps' h⟩

theorem e0123_mem : eset {0, 1, 2, 3} ∈ coreMod 8 := by
  rw [mem_coreMod]
  decide

@[expose] noncomputable def e0123 : D8 :=
  QuotientGroup.mk (⟨eset {0, 1, 2, 3}, e0123_mem⟩ : ↥(coreMod 8))

theorem hasWt_e0123 : HasWt 4 e0123 := ⟨_, rfl, by decide⟩

theorem permAct_eset_swap {σ : Perm (Fin 8)} (hσ : ∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)) :
    permAct 8 σ (eset {0, 1, 2, 3}) = eset {0, 1, 2, 3} * allOnes 8 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply, toAdd_mul]
  simp only [eset, toAdd_ofAdd, Pi.add_apply]
  have h1 := hσ (σ⁻¹ i)
  rw [S126Ex.perm_apply_inv] at h1
  have key : σ⁻¹ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) ↔ ¬ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) := by
    rw [mem_0123, mem_0123, h1]
    omega
  split_ifs with ha hb hb
  · exact absurd hb (key.1 ha)
  · rfl
  · show (0 : ZMod 2) = 1 + 1
    decide
  · exact absurd (key.2 hb) ha

theorem dAct_e0123 {σ : Perm (Fin 8)} (hσ : PresPart σ) : dAct σ e0123 = e0123 := by
  rw [e0123, dAct_mk]
  rcases blocks_of_presPart hσ with h | h
  · congr 1
    exact Subtype.ext (by rw [coreAct_coe]; exact permAct_eset h)
  · rw [mk_eq_iff]
    right
    rw [coreAct_coe]
    exact permAct_eset_swap h

omit [IsMulCommutative ↥V] in
theorem sylow_conj {S : Subgroup G} (hS : quasithinIsSylowTwo S) (g : G) :
    quasithinIsSylowTwo (S.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hS.1.map _, ?_⟩
  rw [Subgroup.index_map_eq _ (MulAut.conj g).surjective (by
    rw [MonoidHom.ker_eq_bot_iff _ |>.mpr (MulAut.conj g).injective]
    exact bot_le)]
  exact hS.2

omit [IsMulCommutative ↥V] in
theorem conj_le_centralizer {S : Subgroup G} {u g : G}
    (h : S ≤ Subgroup.centralizer ({u} : Set G)) :
    S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 (h hs)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * s * g⁻¹ * (g * u * g⁻¹) = g * (s * u) * g⁻¹ := by group
    _ = g * (u * s) * g⁻¹ := by rw [h1]
    _ = g * u * g⁻¹ * (g * s * g⁻¹) := by group

theorem beta_inj (F : Frame126 T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {v w : ↥V} (h : F.β v = F.β w) : v = w := by
  have h1 : F.β (v * w⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : ((v * w⁻¹ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨(v * w⁻¹).2, (F.β_ker _).1 h1⟩
  rw [hZ, Subgroup.mem_bot] at h2
  have h3 : v * w⁻¹ = 1 := Subtype.ext h2
  exact mul_inv_eq_one.1 h3

theorem central_of_wt4 [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {u : ↥V} (hu : HasWt 4 (F.β u)) :
    ∃ S : Subgroup G, quasithinIsSylowTwo S ∧ S ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
  obtain ⟨σ, hσ⟩ := exists_dAct (by norm_num) hu hasWt_e0123
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π σ).2
  set v₁ : ↥V := conjAct V ⟨l, hl⟩ u with hv₁def
  have hv₁ : F.β v₁ = e0123 := by
    rw [hv₁def, hla, F.equi, hσ]
  have hT : ∀ t ∈ T, t * (v₁ : G) = v₁ * t := by
    intro t ht
    obtain ⟨τ, hτP, hτ⟩ := actsAs_of_mem_T F ht
    have hw : t * (v₁ : G) * t⁻¹ ∈ V := conj_mem (hTV ht) v₁
    have h1 := hτ v₁ ⟨_, hw⟩ rfl
    rw [hv₁, dAct_e0123 hτP, ← hv₁] at h1
    have h2 : t * (v₁ : G) * t⁻¹ = v₁ := congrArg Subtype.val (beta_inj F hZ h1)
    calc t * (v₁ : G) = t * (v₁ : G) * t⁻¹ * t := by group
      _ = v₁ * t := by rw [h2]
  have hTc : T ≤ Subgroup.centralizer ({(v₁ : G)} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hT t ht
  have h1 := conj_le_centralizer (g := l⁻¹) hTc
  have hu' : l⁻¹ * (v₁ : G) * l⁻¹⁻¹ = u := by
    change l⁻¹ * (l * u * l⁻¹) * l⁻¹⁻¹ = u
    group
  rw [hu'] at h1
  exact ⟨_, sylow_conj hH.hyp.sylow l⁻¹, h1⟩

theorem fusion_of_bot [Finite G] (h1262 : Theorem12_6_2) (h1222 : Stmt12_2_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹ := by
  intro u hu g hy
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  by_cases hu1 : u = 1
  · exact ⟨1, L.one_mem, by rw [hu1]; group⟩
  set u' : ↥V := ⟨u, hu⟩ with hu'def
  set y' : ↥V := ⟨g * u * g⁻¹, hy⟩ with hy'def
  have hne : ∀ w : ↥V, (w : G) ≠ 1 → F.β w ≠ 1 := fun w hw h =>
    hw (congrArg Subtype.val (beta_inj F hZ (h.trans (map_one F.β).symm)))
  have hβu : F.β u' ≠ 1 := hne u' hu1
  have hβy : F.β y' ≠ 1 := hne y' (fun h => hu1 (by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [show g * u * g⁻¹ = 1 from h]; group))
  have hcent : ∀ (a b : ↥V) (h : G), (b : G) = h * a * h⁻¹ → HasWt 4 (F.β a) →
      IsNonsing (F.β b) → False := by
    intro a b h hb ha hbn
    obtain ⟨S, hS, hSa⟩ := central_of_wt4 F hH hTV hZ ha
    have h1 := conj_le_centralizer (g := h) hSa
    rw [← hb] at h1
    exact not_two_central h1262 h1222 F hH ⟨b.2, hbn⟩ (sylow_conj hS h) h1
  have hp1 := part1 F u' y' hβu hβy
  have key : (IsNonsing (F.β u') ↔ IsNonsing (F.β y')) := by
    rcases cases_of_ne_one hβu with hun | hu4 <;> rcases cases_of_ne_one hβy with hyn | hy4
    · exact iff_of_true hun hyn
    · exact (hcent y' u' g⁻¹ (by change u = g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹; group) hy4 hun).elim
    · exact (hcent u' y' g rfl hu4 hyn).elim
    · exact iff_of_false (fun h => not_nonsing_and_wt4 h hu4) (fun h => not_nonsing_and_wt4 h hy4)
  obtain ⟨l, hlL, hl, hlw⟩ := hp1.2 key
  exact ⟨l, hlL, congrArg Subtype.val (beta_inj F hZ hlw)⟩

end S126L19

end CFSG.Quasithin.H13
