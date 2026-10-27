module

public import CFSG.Quasithin.Vol2.Ch11SecBK4X
public import CFSG.Quasithin.H13.NQCatParabolicSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (borelSubgroup isoFlag unipotent)
open scoped IsMulCommutative Pointwise

namespace BK4

variable {K : Type} [Field K]

variable (K) in
@[expose] def flag4 (i : ℕ) : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  if i = 0 then ⊥ else if i = 1 then KGNat.spLine K else if i = 2 then KGNat.spPlane K
    else if i = 3 then KGNat.spHyp K else ⊤

theorem flag4_zero : flag4 K 0 = ⊥ := by simp [flag4]

theorem flag4_one : flag4 K 1 = KGNat.spLine K := by simp [flag4]

theorem flag4_two : flag4 K 2 = KGNat.spPlane K := by simp [flag4]

theorem flag4_three : flag4 K 3 = KGNat.spHyp K := by simp [flag4]

theorem flag4_top {i : ℕ} (hi : 4 ≤ i) : flag4 K i = ⊤ := by
  simp [flag4, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
    show i ≠ 3 by omega]

theorem hstep_flag4 : ∀ i < 4, ∃ e ∈ flag4 K (i + 1), e ∉ flag4 K i ∧
    ∀ y ∈ flag4 K (i + 1), ∃ c : K, y - c • e ∈ flag4 K i := by
  intro i hi
  interval_cases i
  · rw [flag4_zero, flag4_one]
    refine ⟨KGNat.vec4 1 0 0 0, ⟨rfl, rfl, rfl⟩, fun h => ?_, fun y hy => ⟨y (.inl 0), ?_⟩⟩
    · have := congrFun ((Submodule.mem_bot K).mp h) (.inl 0)
      simp [KGNat.vec4] at this
    · obtain ⟨h1, h2, h3⟩ := hy
      rw [Submodule.mem_bot]
      refine KGNat.vec4_eq ?_ ?_ ?_ ?_ <;> simp [KGNat.vec4, h1, h2, h3]
  · rw [flag4_one, flag4_two]
    refine ⟨KGNat.vec4 0 1 0 0, ⟨rfl, rfl⟩, fun h => ?_, fun y hy => ⟨y (.inl 1), ?_⟩⟩
    · have := h.1
      simp [KGNat.vec4] at this
    · obtain ⟨h2, h3⟩ := hy
      refine ⟨?_, ?_, ?_⟩ <;> simp [KGNat.vec4, h2, h3]
  · rw [flag4_two, flag4_three]
    refine ⟨KGNat.vec4 0 0 0 1, rfl, fun h => ?_, fun y hy => ⟨y (.inr 1), ?_⟩⟩
    · have := h.2
      simp [KGNat.vec4] at this
    · have h2 : y (.inr 0) = 0 := hy
      refine ⟨?_, ?_⟩ <;> simp [KGNat.vec4, h2]
  · rw [flag4_three, flag4_top le_rfl]
    refine ⟨KGNat.vec4 0 0 1 0, Submodule.mem_top, fun h => ?_, fun y _ => ⟨y (.inr 0), ?_⟩⟩
    · have : (KGNat.vec4 (0 : K) 0 1 0) (.inr 0) = 0 := h
      simp [KGNat.vec4] at this
    · refine KGNat.mem_spHyp.mpr ?_
      simp [KGNat.vec4]

theorem isoFlag_one : isoFlag 2 K 1 = KGNat.spLine K := by
  ext x
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.mem_isoFlag, KGNat.mem_spLine]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 1 (by decide), h1 0, h1 1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h2
      · exact h3
    · fin_cases j
      · exact absurd hj (by decide)
      · exact h1

theorem isoFlag_two : isoFlag 2 K 2 = KGNat.spPlane K := by
  ext x
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.mem_isoFlag, KGNat.mem_spPlane]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => absurd hj (by have := j.2; omega)⟩
    fin_cases j
    · exact h1
    · exact h2

theorem mulVec_mem_isoFlag {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ 2) {x : Fin 2 ⊕ Fin 2 → K} (hx : x ∈ isoFlag 2 K i) :
    mat 2 K b *ᵥ x ∈ isoFlag 2 K i := by
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.mem_stabilizer.mp
    ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.mem_borelSubgroup_iff_isoFlag.mp hb)
      i hi1 hi2)
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem eq_smul_of_mem_spLine {x : Fin 2 ⊕ Fin 2 → K} (hx : x ∈ KGNat.spLine K) :
    x = x (.inl 0) • KGNat.vec4 1 0 0 0 := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine KGNat.vec4_eq ?_ ?_ ?_ ?_ <;> simp [KGNat.vec4, h1, h2, h3]

theorem mulVec_mem_spHyp {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K)
    {x : Fin 2 ⊕ Fin 2 → K} (hx : x ∈ KGNat.spHyp K) : mat 2 K b *ᵥ x ∈ KGNat.spHyp K := by
  have he : mat 2 K b⁻¹ *ᵥ KGNat.vec4 1 0 0 0 ∈ KGNat.spLine K := by
    rw [← isoFlag_one]
    exact mulVec_mem_isoFlag ((borelSubgroup 2 K).inv_mem hb) le_rfl (by norm_num)
      (by rw [isoFlag_one]; exact ⟨rfl, rfl, rfl⟩)
  have hce := eq_smul_of_mem_spLine he
  rw [KGNat.mem_spHyp, ← KGNat.spB_e0 (mat 2 K b *ᵥ x)]
  have := KGNat.spB_mat b (mat 2 K b⁻¹ *ᵥ KGNat.vec4 1 0 0 0) x
  rw [KGNat.mat_mulVec_inv, hce] at this
  rw [this, LinearMap.map_smul₂, KGNat.spB_e0, show x (.inr 0) = 0 from hx, smul_zero]

theorem mulVec_mem_flag4 {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) {i : ℕ}
    {x : Fin 2 ⊕ Fin 2 → K} (hx : x ∈ flag4 K i) : mat 2 K b *ᵥ x ∈ flag4 K i := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · rw [flag4_zero, Submodule.mem_bot] at hx ⊢
      rw [hx, Matrix.mulVec_zero]
    · rw [flag4_one, ← isoFlag_one] at hx ⊢
      exact mulVec_mem_isoFlag hb le_rfl (by norm_num) hx
    · rw [flag4_two, ← isoFlag_two] at hx ⊢
      exact mulVec_mem_isoFlag hb (by norm_num) le_rfl hx
    · rw [flag4_three] at hx ⊢
      exact mulVec_mem_spHyp hb hx
  · rw [flag4_top hi]
    exact Submodule.mem_top

theorem mapsTo_sp4 [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : StatedSp 2 K} (hg : ∀ x : MulAut W, x ∈ P ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    {A : Subgroup (MulAut W)} (hAH : A ≤ H) (hPA : P ≤ A) (hA : Group.IsSolvable A)
    {a : MulAut W} (ha : a ∈ A) (i : ℕ) (w : W) (hw : f w ∈ KGNat.gmapSp g (flag4 K i)) :
    f (a w) ∈ KGNat.gmapSp g (flag4 K i) := by
  let φ : StatedSp 2 K →* MulAut W := H.subtype.comp (π.comp (MulAut.conj g).toMonoidHom)
  have hφ : ∀ b, φ b = ((π (g * b * g⁻¹) : ↥H) : MulAut W) := fun b => rfl
  have hφinj : Function.Injective φ := H.subtype_injective.comp
    (hf.injective_nat.comp (MulAut.conj g).injective)
  have hU : unipotent 2 K ≤ A.comap φ := by
    rw [← SecS.C11P9A.Usp_eq_unipotent]
    intro u hu
    rw [Subgroup.mem_comap, hφ]
    exact hPA ((hg _).mpr ⟨u, hu, rfl⟩)
  have hB : Group.IsSolvable ↥(A.comap φ) := by
    have := hA
    refine Group.isSolvable_of_isSolvable_injective (f := φ.subgroupComap A) fun x y h => ?_
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (hφinj h1)
  have hBU := H13.NQCat.Sp4.le_borelSubgroup_of_isSolvable hK4 hU hB
  obtain ⟨b', hb'⟩ : ∃ b' : StatedSp 2 K, π b' = ⟨a, hAH ha⟩ := hf.onto ⟨a, hAH ha⟩
  have hb : g⁻¹ * b' * g ∈ A.comap φ := by
    rw [Subgroup.mem_comap, hφ, show g * (g⁻¹ * b' * g) * g⁻¹ = b' by group, hb']
    exact ha
  have e1 : a w = ((π b' : ↥H) : MulAut W) w := by rw [hb']
  rw [e1, hf.act4, KGNat.mem_gmapSp, show b' = g * (g⁻¹ * b' * g) * g⁻¹ by group,
    KGNat.conj_mulVec_sp]
  exact mulVec_mem_flag4 (hBU hb) (KGNat.mem_gmapSp.mp hw)

variable {G : Type} [Group G] {L V T D : Subgroup G}

theorem cartanPower_sp4 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    {π : ↥(StatedSp 2 K) →* ↥(autOn L V)} {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDL : D ≤ L) (hD : IsElemAbelian p D) (hDT : (D : Set G) * T = T * D) {t : G}
    (ht : t ∈ T) (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := KGNat.exists_sylow_eq_conj_Usp hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL')
  have hK4 := exists_finset_card_four (four_le_of_card hK hn)
  have hΨΦ : ∀ x, Matrix.toLin' (mat 2 K g⁻¹) (Matrix.toLin' (mat 2 K g) x) = x := fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, KGNat.mat_inv_mulVec]
  have hΦΨ : ∀ x, Matrix.toLin' (mat 2 K g) (Matrix.toLin' (mat 2 K g⁻¹) x) = x := fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, KGNat.mat_mulVec_inv]
  refine cartanPower_of_flag hf hLV (fun T hT => KGNat.commutant_statedSp T hT)
    (x₀ := KGNat.vec4 (1 : K) 0 0 0) (fun h => one_ne_zero (congrFun h (.inl 0)))
    (fun x hxV hxL hx => mem_centralizer_of_sp4 hLV hVL hf hxV hxL hx) hTS.2.1 hTV hTL
    (m := 4) (fun i => KGNat.gmapSp g (flag4 K i)) ?_ ?_ (hstep_map _ _ hΨΦ hΦΨ hstep_flag4) ?_
    ?_ ?_ hDL hp hp2 hD hDT ht htD
  · show KGNat.gmapSp g (flag4 K 0) = ⊥
    rw [flag4_zero, KGNat.gmapSp, Submodule.map_bot]
  · intro i hi
    show KGNat.gmapSp g (flag4 K i) = ⊤
    rw [flag4_top hi]
    exact eq_top_iff.mpr fun x _ => KGNat.mem_gmapSp.mpr Submodule.mem_top
  · intro i hi0 hi4
    show SecA.IsFlagW _ _ _ _ i (hf.pre (KGNat.gmapSp g (flag4 K i)).toAddSubgroup)
    interval_cases i
    · rw [flag4_one]
      exact KGNat.isFlagW_pre_sp hW hf hg KGNat.spLine_stable (by rw [KGNat.card_spLine, pow_one])
    · rw [flag4_two]
      exact KGNat.isFlagW_pre_sp hW hf hg KGNat.spPlane_stable KGNat.card_spPlane
    · rw [flag4_three]
      exact KGNat.isFlagW_pre_sp hW hf hg KGNat.spHyp_stable KGNat.card_spHyp
  · intro i hi0 hi4 U hU
    show U = hf.pre (KGNat.gmapSp g (flag4 K i)).toAddSubgroup
    obtain ⟨S, hS, hcard, rfl⟩ := KGNat.exists_eq_pre_of_isFlagW_sp hW hf hg hU
    interval_cases i
    · rw [(KGNat.eq_std_of_stable_sp hS).1 (by rw [hcard, pow_one]), flag4_one]
    · rw [(KGNat.eq_std_of_stable_sp hS).2.1 hcard, flag4_two]
    · rw [(KGNat.eq_std_of_stable_sp hS).2.2 hcard, flag4_three]
  · intro A hAH hPA hA a ha i w hw
    exact mapsTo_sp4 hK4 hf hg hAH hPA hA ha i w hw

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
