module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Facts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL diagSL_conj)

variable {G : Type} [Group G]

namespace Setting516

variable {T L D R N : Subgroup G}

theorem sup_inf_centralizer_le [Finite G] (hS : Setting516 T L D R)
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G))
    (hN : ¬ L ≤ Subgroup.centralizer (N : Set G)) :
    (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN := hS.le_normalizer
  have hCL : L ⊓ Subgroup.centralizer (N : Set G) ≤ pCoreOf 2 L := by
    have hnorm : L ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
        F7.normalizer_le_normalizer_centralizer N ((le_sup_left.trans hLTN) hl)⟩
    rcases hS.simple _ inf_le_left hnorm with hle | heq
    · exact hle
    · exact absurd (heq.symm.le.trans inf_le_right) hN
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (N : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hS.isPGroup ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (N : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨l', hCL ⟨hl', hC⟩⟩
    have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']
  have hle : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Hyp5_0_1.le_normalizer_inf_centralizer hLTN) hC2
  exact hle.trans (F7.isSylowTwoOf_pCoreOf_le hS.sylow_sup)

end Setting516

structure QCoord (L N S : Subgroup G) (F : Type) [Field F] (ψ : ↥(autOn L N) ≃* SL(2, F))
    (Y : ↥N →* Multiplicative (Fin 2 → F)) : Prop where
  le_normalizer : L ≤ Subgroup.normalizer (N : Set G)
  surj : Function.Surjective Y
  ker : ∀ x : ↥N, Y x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G)
  intertwine : ∀ (x : ↥(autOn L N)) (w : ↥N), Multiplicative.toAdd (Y ((x : MulAut ↥N) w)) =
    (ψ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w))
  sylow : ∀ x : ↥(autOn L N), (x : MulAut ↥N) ∈ autOn S N ↔ ∃ b : F, ψ x = unipSL b

theorem IsNatQuotCh5.exists_qcoord [Finite G] {L N S : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L N n) (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (ψ : ↥(autOn L N) ≃* SL(2, F)) (Y : ↥N →* Multiplicative (Fin 2 → F)),
        QCoord L N S F ψ Y := by
  obtain ⟨F, _, _, _, hF, ψ, Y, h1, h2, h3, h4⟩ := h.exists_sylowCoord hS
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ψ, Y, ⟨h.1, h1, h2, h3, h4⟩⟩

namespace QCoord

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)} (hc : QCoord L N S F ψ Y)
include hc

theorem toAdd_Y_conj {g : G} (hg : g ∈ L) (x : ↥N) :
    Multiplicative.toAdd (Y (((autHom hc.le_normalizer ⟨g, hg⟩ : ↥(autOn L N)) :
      MulAut ↥N) x)) =
      (ψ (autHom hc.le_normalizer ⟨g, hg⟩) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (Y x)) :=
  hc.intertwine _ x

theorem snd_eq_zero_iff (hSL : S ≤ L) (x : ↥N) :
    (Multiplicative.toAdd (Y x)) 1 = 0 ↔
      ∀ s ∈ S, s * (x : G) * s⁻¹ * (x : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have hLN := hc.le_normalizer
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSL.trans hLN
  have hconj : ∀ (s : G) (hs : s ∈ S), (((autHom hLN ⟨s, hSL hs⟩ : ↥(autOn L N)) :
      MulAut ↥N) x : G) = s * x * s⁻¹ := fun s hs => autHom_apply_coe hLN _ x
  constructor
  · intro h0 s hs
    have hsS : ((autHom hLN ⟨s, hSL hs⟩ : ↥(autOn L N)) : MulAut ↥N) ∈ autOn S N :=
      mem_autOn_iff.mpr ⟨⟨s, hSN hs⟩, hs, rfl⟩
    obtain ⟨b, hb⟩ := (hc.sylow _).mp hsS
    have h1 := hc.toAdd_Y_conj (hSL hs) x
    rw [hb, coe_unipSL] at h1
    have hfix : Y (((autHom hLN ⟨s, hSL hs⟩ : ↥(autOn L N)) : MulAut ↥N) x) = Y x := by
      apply Multiplicative.toAdd.injective
      rw [h1]
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    have h2 : Y (((autHom hLN ⟨s, hSL hs⟩ : ↥(autOn L N)) : MulAut ↥N) x * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hfix, mul_inv_cancel]
    have := (hc.ker _).mp h2
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, hconj s hs] at this
  · intro h
    obtain ⟨b, hb⟩ : ∃ s : ↥(autOn L N), ψ s = unipSL 1 := ⟨ψ.symm (unipSL 1), by simp⟩
    have hbS : ((b : ↥(autOn L N)) : MulAut ↥N) ∈ autOn S N := (hc.sylow b).mpr ⟨1, hb⟩
    obtain ⟨s, hs, hsb⟩ := mem_autOn_iff.mp hbS
    have hsx : Y (((b : ↥(autOn L N)) : MulAut ↥N) x) = Y x := by
      have h1 : ((s : G) * x * (s : G)⁻¹) * (x : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
        h s hs
      have h2 : (((b : ↥(autOn L N)) : MulAut ↥N) x : G) = s * x * (s : G)⁻¹ := by
        rw [← hsb, conjAct_apply_coe]
      have h3 : Y (((b : ↥(autOn L N)) : MulAut ↥N) x * x⁻¹) = 1 := by
        rw [hc.ker, Subgroup.coe_mul, Subgroup.coe_inv, h2]
        exact h1
      rw [map_mul, map_inv, mul_inv_eq_one] at h3
      exact h3
    have h1 := hc.intertwine b x
    rw [hsx, hb, coe_unipSL] at h1
    have := congrFun h1 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this

theorem upper {g : G} (hg : g ∈ L) (hgS : g ∈ Subgroup.normalizer (S : Set G)) :
    (ψ (autHom hc.le_normalizer ⟨g, hg⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  upper_of_mem_normalizer ψ hc.sylow _
    (conjAct_mem_normalizer_autOn ⟨g, hc.le_normalizer hg⟩ hgS)

theorem toAdd_Y_line {g : G} (hg : g ∈ L) (hgS : g ∈ Subgroup.normalizer (S : Set G)) (x : ↥N)
    (hx : (Multiplicative.toAdd (Y x)) 1 = 0) :
    Multiplicative.toAdd (Y (((autHom hc.le_normalizer ⟨g, hg⟩ : ↥(autOn L N)) :
      MulAut ↥N) x)) =
      (ψ (autHom hc.le_normalizer ⟨g, hg⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 •
        Multiplicative.toAdd (Y x) := by
  rw [hc.toAdd_Y_conj hg x]
  have hu := hc.upper hg hgS
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu, hx]

end QCoord

namespace QCoord

variable {L N : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem exists_mem_borel [Finite G] {T : Subgroup G} (hc : QCoord L N (T ⊓ L) F ψ Y)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T) {c : F} (hc0 : c ≠ 0) :
    ∃ (g : G) (hg : g ∈ borelL T L),
      (ψ (autHom hc.le_normalizer ⟨g, hg.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  have hLN := hc.le_normalizer
  obtain ⟨g', hg'L, hg'⟩ := mem_autOn_iff.mp (ψ.symm (diagSL hc0)).2
  set g : G := (g' : G) with hgdef
  have hψg : ψ (autHom hLN ⟨g, hg'L⟩) = diagSL hc0 := by
    have : autHom hLN ⟨g, hg'L⟩ = ψ.symm (diagSL hc0) := Subtype.ext hg'
    rw [this, MulEquiv.apply_symm_apply]
  have hgN : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun s hs => ?_
    have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
    have hgs : g * s * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg'L hsL) (L.inv_mem hg'L)
    refine Subgroup.mem_inf.mpr ⟨?_, hgs⟩
    have hsS : ((autHom hLN ⟨s, hsL⟩ : ↥(autOn L N)) : MulAut ↥N) ∈ autOn (T ⊓ L) N :=
      mem_autOn_iff.mpr ⟨⟨s, hLN hsL⟩, hs, rfl⟩
    obtain ⟨b, hb⟩ := (hc.sylow _).mp hsS
    have hgsb : ψ (autHom hLN ⟨g * s * g⁻¹, hgs⟩) = unipSL (c ^ 2 * b) := by
      have : (autHom hLN ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L N)) =
          autHom hLN ⟨g, hg'L⟩ * autHom hLN ⟨s, hsL⟩ * (autHom hLN ⟨g, hg'L⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this, map_mul, map_mul, map_inv, hψg, hb, diagSL_conj]
    have hmem : ((autHom hLN ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L N)) : MulAut ↥N) ∈
        autOn (T ⊓ L) N := (hc.sylow _).mpr ⟨_, hgsb⟩
    exact mem_of_conjAct_mem_autOn hC ⟨g * s * g⁻¹, hLN hgs⟩ (Subgroup.mem_sup_left hgs) hmem
  refine ⟨g, Subgroup.mem_inf.mpr ⟨hg'L, hgN⟩, ?_⟩
  rw [hψg, coe_diagSL]
  simp

theorem exists_mem_D [Finite G] {T D : Subgroup G} (hc : QCoord L N (T ⊓ L) F ψ Y)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {c : F} (hc0 : c ≠ 0) :
    ∃ (δ : G) (hδ : δ ∈ D),
      (ψ (autHom hc.le_normalizer ⟨δ, (Subgroup.mem_inf.mp (hD.1 hδ)).1⟩) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  have hLN := hc.le_normalizer
  obtain ⟨g, hg, hgc⟩ := hc.exists_mem_borel hC hc0
  have hSB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono hS (Hyp5_0_1.inf_le_borel T L) inf_le_left
  have hB : D ⊔ (T ⊓ L) = borelL T L := sup_eq_of_isHall_isSylow hD hSB
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hD.1.trans inf_le_right
  have hgmem : g ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
    rw [hB]
    exact hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDN] at hgmem
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hgmem
  refine ⟨δ, hδ, ?_⟩
  have hδL : δ ∈ L := (Subgroup.mem_inf.mp (hD.1 hδ)).1
  have hδN : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hDN hδ
  have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
  have hsN : s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := Subgroup.le_normalizer hs
  have hmul : (autHom hLN ⟨δ * s, (Subgroup.mem_inf.mp hg).1⟩ : ↥(autOn L N)) =
      autHom hLN ⟨δ, hδL⟩ * autHom hLN ⟨s, hsL⟩ := by
    rw [← map_mul]
    rfl
  have hsS : ((autHom hLN ⟨s, hsL⟩ : ↥(autOn L N)) : MulAut ↥N) ∈ autOn (T ⊓ L) N :=
    mem_autOn_iff.mpr ⟨⟨s, hLN hsL⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (hc.sylow _).mp hsS
  have h1 := (upper_mul (hc.upper hδL hδN) (hc.upper hsL hsN)).2
  rw [← map_mul, ← hmul, hgc, hb, coe_unipSL] at h1
  simpa using h1.symm

end QCoord

end CFSG.Quasithin.H13
