module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreDefs
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrth3
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.Uniqueness.Section4Lift
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Prop38
public import CFSG.GH74.Uniqueness.Setup
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem vec_nsmul (B : Basis3 G k) (m : ℕ) (e : Coords k) : B.vec (m • e) = B.vec e ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, B.vec_zero]
  | succ m ih => rw [succ_nsmul, B.vec_add, ih, pow_succ]

theorem vec_smul_single (B : Basis3 G k) (c : ZMod 3) (i : Fin k) :
    B.vec (c • Pi.single i 1) = B.b i ^ c.val := by
  rw [show c • (Pi.single i 1 : Coords k) = c.val • Pi.single i 1 by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val], B.vec_nsmul, B.vec_single]

theorem vec_mem_of_zero {n : ℕ} (B : Basis3 G (n + 1)) {K : Subgroup G}
    (hK : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ K) {e : Coords (n + 1)} (he : e 0 = 0) :
    B.vec e ∈ K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  by_cases hi : i = 0
  · subst hi
    rw [he, ZMod.val_zero, pow_zero]
    exact K.one_mem
  · exact K.pow_mem (hK i hi) _

theorem coords_zero_of_mem {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} {K : Subgroup G}
    (hb0 : B.b 0 = b₀) (hord : orderOf b₀ = 3) (hK : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ K)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K)) (y : ↥B.span) (hy : (y : G) ∈ K) :
    B.coords y 0 = 0 := by
  set e := B.coords y with he
  set e' : Coords (n + 1) := e - e 0 • Pi.single 0 1 with he'
  have he'0 : e' 0 = 0 := by simp [he']
  have hsplit : B.vec e = B.vec (e 0 • Pi.single 0 1) * B.vec e' := by
    rw [← B.vec_add, he', add_sub_cancel]
  rw [B.vec_smul_single, hb0] at hsplit
  have hpowK : b₀ ^ (e 0).val ∈ K := by
    have : b₀ ^ (e 0).val = B.vec e * (B.vec e')⁻¹ := by rw [hsplit]; group
    rw [this, he, B.vec_coords]
    exact K.mul_mem hy (K.inv_mem (B.vec_mem_of_zero hK he'0))
  have hpowE : b₀ ^ (e 0).val ∈ B.span := B.span.pow_mem (hb0 ▸ B.b_mem_span 0) _
  have h1 : b₀ ^ (e 0).val = 1 := by
    have hmem : b₀ ^ (e 0).val ∈ Subgroup.zpowers b₀ ⊓ (B.span ⊓ K) :=
      ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _, hpowE, hpowK⟩
    have := disjoint_iff_inf_le.mp hdisj hmem
    exact (Subgroup.mem_bot.mp this)
  have h3 : 3 ∣ (e 0).val := by
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [hord] at this
  have hlt : (e 0).val < 3 := ZMod.val_lt _
  have h0 : (e 0).val = 0 := by omega
  exact (ZMod.val_eq_zero _).mp h0

end Basis3

theorem evenFix0_subset_monoFix0 (n : ℕ) : evenFix0 n ⊆ monoFix0 n := by
  rintro _ ⟨σ, s, hs, ⟨h0, hs0, -⟩, rfl⟩
  exact ⟨σ, s, hs, ⟨h0, hs0⟩, rfl⟩

namespace Basis3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_of_mem_xg {k : ℕ} (B : Basis3 G k) {x : GL (Fin k) (ZMod 3)}
    (hx : x ∈ (ggAutomizer ⊤ B.span).map B.glHom) :
    ∃ φ : MulAut ↥B.span, ∃ g ∈ Subgroup.normalizer (B.span : Set G),
      (∀ b : ↥B.span, ((φ b : ↥B.span) : G) = g * b * g⁻¹) ∧ B.glHom φ = x := by
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφ
  exact ⟨φ, g, hgN, hg, rfl⟩

theorem exists_xg_of_realized {k : ℕ} (B : Basis3 G k) (H : Subgroup G)
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : A ∈ B.realized H) :
    ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom, (x : Matrix (Fin k) (Fin k) (ZMod 3)) = A := by
  obtain ⟨φ, ⟨g, -, hgN, hg⟩, hφA⟩ := (B.mem_realized_iff _ _).mp hA
  exact ⟨B.glHom φ, Subgroup.mem_map_of_mem _ (mem_ggAutomizer_iff.mpr ⟨g, trivial, hgN, hg⟩), hφA⟩

omit [Finite G] in
theorem conj_b_of_mulVec_single {k : ℕ} (B : Basis3 G k) {φ : MulAut ↥B.span} {g : G}
    (hg : ∀ b : ↥B.span, ((φ b : ↥B.span) : G) = g * b * g⁻¹) {i : Fin k} {c : ZMod 3}
    (h : B.matOf φ *ᵥ Pi.single i 1 = c • Pi.single i 1) : g * B.b i * g⁻¹ = B.b i ^ c.val := by
  have hcoord : B.coords (φ (B.bS i)) = c • Pi.single i 1 := by
    rw [B.coords_apply, B.coords_bS]
    exact h
  rw [← B.vec_smul_single, ← hcoord, B.vec_coords, hg]
  rfl

theorem mem_normalizer_zpowers_of_conj {a g : G} (h : g * a * g⁻¹ ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers a := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    exact h
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

omit [Finite G] in
theorem mem_centralizer_of_fix {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    {φ : MulAut ↥B.span} {g : G} (hg : ∀ b : ↥B.span, ((φ b : ↥B.span) : G) = g * b * g⁻¹)
    (h : B.matOf φ *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    g ∈ Subgroup.centralizer ({b₀} : Set G) := by
  have h1 := B.conj_b_of_mulVec_single hg (c := 1) (by rw [one_smul]; exact h)
  rw [ZMod.val_one, pow_one, hb0] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  calc b₀ * g = (g * b₀ * g⁻¹) * g := by rw [h1]
    _ = g * b₀ := by group

theorem fix_mem_realized {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    {x : GL (Fin (n + 1)) (ZMod 3)} (hx : x ∈ (ggAutomizer ⊤ B.span).map B.glHom)
    (hxe : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈
      B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
  obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hx
  exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, B.mem_centralizer_of_fix hb0 hg hxe, hgN, hg⟩, rfl⟩

theorem stab_mem_realized {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    {x : GL (Fin (n + 1)) (ZMod 3)} (hx : x ∈ (ggAutomizer ⊤ B.span).map B.glHom)
    (hxe : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    {i : Fin (n + 1)}
    (hxi : ∃ c : ZMod 3, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single i 1 =
      c • Pi.single i 1) :
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈
      B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers (B.b i) : Set G)) := by
  obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hx
  obtain ⟨c, hc⟩ := hxi
  have hgi : g ∈ Subgroup.normalizer (Subgroup.zpowers (B.b i) : Set G) := by
    refine mem_normalizer_zpowers_of_conj ?_
    rw [B.conj_b_of_mulVec_single hg hc]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact (B.mem_realized_iff _ _).mpr
    ⟨φ, ⟨g, ⟨B.mem_centralizer_of_fix hb0 hg hxe, hgi⟩, hgN, hg⟩, rfl⟩

theorem exists_xg_moves_e0 {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hfus : Fus42 B b₀) :
    ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom, ∃ i : Fin (n + 1), i ≠ 0 ∧
      ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i ≠ 0 := by
  obtain ⟨g, hgN, hgn⟩ := Set.not_subset.mp hfus.1
  set φ := B.span.normalizerMonoidHom ⟨g, hgN⟩ with hφ
  have hφX : φ ∈ ggAutomizer ⊤ B.span :=
    mem_ggAutomizer_iff.mpr ⟨g, trivial, hgN, fun b =>
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
  refine ⟨B.glHom φ, Subgroup.mem_map_of_mem _ hφX, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hgn
  have hc : B.matOf φ *ᵥ Pi.single 0 1 = (B.matOf φ *ᵥ Pi.single 0 1) 0 • Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [show (B.matOf φ *ᵥ Pi.single 0 1) i = 0 from hcon i hi]
      simp [hi]
  have himg := B.conj_b_of_mulVec_single (fun b => Subgroup.normalizerMonoidHom_apply_apply_coe
    (H := B.span) ⟨g, hgN⟩ b) hc
  rw [hb0] at himg
  have hmem : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ := by
    rw [himg]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
  exact mem_normalizer_zpowers_of_conj hmem

omit [Finite G] in
theorem fix_preserves_A {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} {K : Subgroup G}
    (hb0 : B.b 0 = b₀) (hord : orderOf b₀ = 3) (hK : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ K)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K))
    (hKn : ∀ g ∈ Subgroup.centralizer ({b₀} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    {x : GL (Fin (n + 1)) (ZMod 3)} (hx : x ∈ (ggAutomizer ⊤ B.span).map B.glHom)
    (hxe : (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (v : Fin (n + 1) → ZMod 3) (hv : v 0 = 0) :
    ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 = 0 := by
  obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hx
  have himg : ((φ ⟨B.vec v, B.vec_mem_span v⟩ : ↥B.span) : G) ∈ K := by
    rw [hg]
    exact hKn g (B.mem_centralizer_of_fix hb0 hg hxe) _ (B.vec_mem_of_zero hK hv)
  have h0 := B.coords_zero_of_mem hb0 hord hK hdisj _ himg
  rwa [B.coords_apply_vec] at h0

end Basis3

theorem transvAll_of_mat {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) (hodd : ¬ OddCoreTrivial E)
    (hstep : ∀ {Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))},
      Mg ≤ (ggAutomizer ⊤ B.span).map B.glHom →
      (∀ g ∈ (ggAutomizer ⊤ B.span).map B.glHom, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg) →
      (∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a) → Mg ≠ ⊥ →
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → (∀ m ∈ Mg, m ^ p = 1) →
        (∀ x ∈ (ggAutomizer ⊤ B.span).map B.glHom, ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
          ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 = 0) ∧
        ∀ β : Fin (n + 1) → ZMod 3, β 0 = 0 → ∃ m ∈ Mg,
          (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
            Pi.single 0 1 + β ∧
          ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
            (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v) :
    TransvAll b₀ K E := by
  obtain ⟨hspan, hb0, hK⟩ := hB
  subst hspan
  set X := ggAutomizer ⊤ B.span with hX
  set Xg := X.map B.glHom with hXg
  have hnorm : ∀ g (hg : g ∈ Subgroup.normalizer (B.span : Set G)),
      B.span.normalizerMonoidHom ⟨g, hg⟩ ∈ X := fun g hg =>
    mem_ggAutomizer_iff.mpr ⟨g, trivial, hg, fun b =>
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
  have hcoordsb0 : B.coords (B.bS 0) = Pi.single 0 1 := B.coords_bS 0
  have hbS0 : ((B.bS 0 : ↥B.span) : G) = b₀ := hb0
  obtain ⟨N, hNn, hNodd, hNne⟩ : ∃ N : Subgroup ↥X, N.Normal ∧ Odd (Nat.card N) ∧ N ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hodd fun N hN hodd' => h N hN hodd'
  have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  obtain ⟨p, hp, B', hB'n, hB'ne, hB'N, hB'p, hB'c⟩ :=
    CFSG.GH74.Uniqueness.exists_abelian_elemental_normal_of_solvable hNn hsolv hNne
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB'ne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hord2 : orderOf (b : ↥X) = 2 := orderOf_eq_prime (hB'p b hbB) hb1'
    have hdvd : 2 ∣ Nat.card N := by
      have h1 : orderOf (⟨(b : ↥X), hB'N hbB⟩ : ↥N) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hord2
      rw [← h1]
      exact orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
  set ψ : ↥X →* GL (Fin (n + 1)) (ZMod 3) := B.glHom.comp X.subtype with hψ
  have hψinj : Function.Injective ψ := B.glHom_injective.comp Subtype.val_injective
  set Mg := B'.map ψ with hMg
  have hMX : Mg ≤ Xg := by
    rintro _ ⟨b, -, rfl⟩
    exact Subgroup.mem_map_of_mem _ b.2
  have hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg := by
    intro g hg m hm
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨φ, hφ⟩ * b * ⟨φ, hφ⟩⁻¹, hB'n.conj_mem b hb _, ?_⟩
    simp [hψ]
  have hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hB'c a ha b hb]
  have hMp : ∀ m ∈ Mg, m ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB'p b hb, map_one]
  have hMne : Mg ≠ ⊥ := by
    intro h
    apply hB'ne
    rw [eq_bot_iff]
    intro b hb
    have : ψ b ∈ Mg := Subgroup.mem_map_of_mem _ hb
    rw [h, Subgroup.mem_bot, ← map_one ψ] at this
    exact Subgroup.mem_bot.mpr (hψinj this)
  obtain ⟨hAinv, hTr⟩ := hstep hMX hMn hMc hMne hp hp2 hMp
  refine ⟨fun g hg a ha => ?_, fun β hβ => ?_⟩
  · set φ := B.span.normalizerMonoidHom ⟨g, hg⟩ with hφ
    have ha0 : B.coords ⟨a, ha.1⟩ 0 = 0 := B.coords_zero_of_mem hb0 hord hK hdisj _ ha.2
    have himg0 : B.coords (φ ⟨a, ha.1⟩) 0 = 0 := by
      rw [B.coords_apply]
      exact hAinv (B.glHom φ) (Subgroup.mem_map_of_mem _ (hnorm g hg)) _ ha0
    have hval : ((φ ⟨a, ha.1⟩ : ↥B.span) : G) = g * a * g⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    rw [← hval]
    refine ⟨(φ ⟨a, ha.1⟩).2, ?_⟩
    rw [← B.vec_coords (φ ⟨a, ha.1⟩)]
    exact B.vec_mem_of_zero hK himg0
  · have hw0 : B.coords ⟨β, hβ.1⟩ 0 = 0 := B.coords_zero_of_mem hb0 hord hK hdisj _ hβ.2
    obtain ⟨m, hm, hme, hmA⟩ := hTr _ hw0
    obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg (hMX hm)
    refine ⟨g, hgN, fun a ha => ?_, ?_⟩
    · have ha0 : B.coords ⟨a, ha.1⟩ 0 = 0 := B.coords_zero_of_mem hb0 hord hK hdisj _ ha.2
      have hfix : φ ⟨a, ha.1⟩ = ⟨a, ha.1⟩ := by
        apply B.coords_injective
        rw [B.coords_apply]
        exact hmA _ ha0
      have := congrArg Subtype.val hfix
      rw [hg] at this
      exact this
    · have hfix : φ (B.bS 0) = B.bS 0 * ⟨β, hβ.1⟩ := by
        apply B.coords_injective
        rw [B.coords_apply, hcoordsb0, B.coords_mul, hcoordsb0]
        exact hme
      have := congrArg Subtype.val hfix
      rw [hg, Subgroup.coe_mul, hbS0] at this
      exact this

theorem transvAll_of_orth {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} {n : ℕ}
    (hn : 3 ≤ n) (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K))
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    (hfus : Fus42 B b₀) (hodd : ¬ OddCoreTrivial E)
    (hstep1 : ∀ {Xg Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))},
      (∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        Pi.single 0 1 → (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoFix0 n) →
      (∀ A ∈ evenFix0 n, ∃ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = A) →
      Mg ≤ Xg → (∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg) → (∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a) →
      ∀ {p : ℕ}, p.Prime → 5 ≤ p → (∀ m ∈ Mg, m ^ p = 1) → Mg = ⊥) :
    TransvAll b₀ K E := by
  have hb0 := hB.2.1
  refine transvAll_of_mat B hB hord hdisj hodd fun {Mg} hMX hMn hMc hMne {p} hp hp2 hMp => ?_
  have hC : ∀ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoFix0 n := by
    intro x hx hxe
    have h := B.fix_mem_realized hb0 hx hxe
    rcases hCm with h' | h'
    · rwa [h'] at h
    · rw [h'] at h
      exact evenFix0_subset_monoFix0 n h
  have hW : ∀ A ∈ evenFix0 n, ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = A := by
    intro A hA
    refine B.exists_xg_of_realized (Subgroup.centralizer ({b₀} : Set G)) ?_
    rcases hCm with h | h
    · rw [h]
      exact evenFix0_subset_monoFix0 n hA
    · rw [h]
      exact hA
  by_cases hp3 : p = 3
  · subst hp3
    exact orth_transv_of_normal3 hn hW (B.exists_xg_moves_e0 hb0 hfus) hMn hMp hMne
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have h4 : p = 4 := by omega
      rw [h4] at hp
      exact absurd hp (by norm_num)
    exact absurd (hstep1 hC hW hMX hMn hMc hp hp5 hMp) hMne

theorem oddCoreTransvAt_D6 : OddCoreTransvAt Row.D6 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus hodd
  obtain ⟨-, ⟨⟨hord, -⟩, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 6 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 6 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  exact transvAll_of_orth (n := 6) (by norm_num) B hB hord hdisj hCm hfus hodd
    (fun {_ _} hC hW hMX hMn hMc {_} hp hp5 hMp => orth_eq_bot_D6 hC hW hMX hMn hMc hp hp5 hMp)

theorem oddCoreTransvAt_twD7 : OddCoreTransvAt Row.twD7 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus hodd
  obtain ⟨-, ⟨⟨hord, -⟩, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 7 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 7 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  exact transvAll_of_orth (n := 7) (by norm_num) B hB hord hdisj hCm hfus hodd
    (fun {_ _} hC hW hMX hMn hMc {_} hp hp5 hMp => orth_eq_bot_twD7 hC hW hMX hMn hMc hp hp5 hMp)

end CFSG.StandardType.FrameRoute.FS81

end
