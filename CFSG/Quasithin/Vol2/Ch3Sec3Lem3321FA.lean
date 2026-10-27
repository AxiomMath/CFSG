module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Three
public import CFSG.Quasithin.Background.FLcModel
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318C
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2C

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement

theorem card_sl3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field, ZMod.card]
  decide

theorem index_ut3 : (unitriangular 3 (ZMod 2)).index = 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := 3) (by norm_num)
  have hodd : ¬ 2 ∣ (unitriangular 3 (ZMod 2)).index := by
    have := hS.2.2
    rwa [show ((unitriangular 3 (ZMod 2)).subgroupOf ⊤).index =
      (unitriangular 3 (ZMod 2)).index from Subgroup.relIndex_top_right _] at this
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hmul := Subgroup.card_mul_index (unitriangular 3 (ZMod 2))
  rw [hk, card_sl3] at hmul
  have hk3 : k ≤ 3 := by
    by_contra h4
    have h1 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h2 : 2 ^ k ∣ 168 := ⟨_, hmul.symm⟩
    have := Nat.dvd_trans h1 h2
    norm_num at this
  interval_cases k <;> omega

theorem index_ge_of_le_normalizer {H : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2))}
    (hH : H ≤ Subgroup.normalizer
      (unitriangular 3 (ZMod 2) : Set (SpecialLinearGroup (Fin 3) (ZMod 2)))) :
    21 ∣ H.index := by
  rw [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at hH
  rw [← index_ut3]
  exact Subgroup.index_dvd_of_le hH

variable {G : Type} [Group G] [Finite G]

theorem not_case5_of {T Y : Subgroup G} (hT : IsSylowTwoOf T (Y ⊔ T))
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y)
    (hψU : ∀ y : ↥Y, (y : G) ∈ T → ψ y ∈ unitriangular 3 (ZMod 2))
    (h5 : IsC134Case5 (Y ⊔ T) T Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, q, G₁, -, -, hG₁, hidx, hTG₁, hTO⟩ := h5.2 T hT le_rfl
  have hG₁le : G₁ ≤ Y ⊔ T := fun g hg => ((hG₁ g).1 hg).1
  have hGN : G₁ ≤ Subgroup.normalizer (T : Set G) := by
    rw [hTO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁
  have hS₀ : IsSylowTwoOf (T ⊓ Y) Y :=
    A4.isSylowTwoOf_inf_normal hT le_sup_left (sup_le Subgroup.le_normalizer hTY)
  have hP₀ : IsSylowTwoOf (T.subgroupOf Y) ⊤ := by
    refine ⟨le_top, ?_, fun h2 => hS₀.2.2 ?_⟩
    · rw [← Subgroup.inf_subgroupOf_right]
      exact hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm
    · rwa [show ((T.subgroupOf Y).subgroupOf ⊤).index = (T.subgroupOf Y).index from
        Subgroup.relIndex_top_right _, ← Subgroup.inf_subgroupOf_right] at h2
  have hP := L3312.isSylowTwoOf_map_range ψ hP₀
  rw [MonoidHom.range_eq_top.mpr hψs] at hP
  have hPU : (T.subgroupOf Y).map ψ ≤ unitriangular 3 (ZMod 2) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hψU s (Subgroup.mem_subgroupOf.1 hs)
  have hPeq : (T.subgroupOf Y).map ψ = unitriangular 3 (ZMod 2) := by
    have hrel := Subgroup.relIndex_mul_index hPU
    have hodd : ¬ 2 ∣ ((T.subgroupOf Y).map ψ).index := by
      have := hP.2.2
      rwa [show (((T.subgroupOf Y).map ψ).subgroupOf ⊤).index = ((T.subgroupOf Y).map ψ).index
        from Subgroup.relIndex_top_right _] at this
    have hU2 := (SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := 3) (by norm_num)).2.1
    have hdvd : ((T.subgroupOf Y).map ψ).relIndex (unitriangular 3 (ZMod 2)) ∣
        Nat.card (unitriangular 3 (ZMod 2)) := Subgroup.relIndex_dvd_card _ _
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      apply hodd
      rw [← hrel, hj]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 hj0) _
    rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact le_antisymm hPU hj
  set H₁ := G₁.subgroupOf Y with hH₁
  have hH₁N : H₁.map ψ ≤ Subgroup.normalizer
      (unitriangular 3 (ZMod 2) : Set (SpecialLinearGroup (Fin 3) (ZMod 2))) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgG : (g : G) ∈ G₁ := Subgroup.mem_subgroupOf.1 hg
    rw [← hPeq]
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective
        (MulAut.conj (ψ g)).injective).ge)
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨g * s * g⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    have hs' : (s : G) ∈ T := Subgroup.mem_subgroupOf.1 hs
    exact (Subgroup.mem_normalizer_iff.mp (hGN hgG) s).mp hs'
  have hkH : ψ.ker ≤ H₁ := by
    rw [hψk]
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 Y := (Lem3328.mem_pCore_iff x).1 hx
    exact Subgroup.mem_subgroupOf.2
      (hTG₁ ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left h1))
  have hidx' : (H₁.map ψ).index ≤ 7 := by
    rw [Subgroup.index_map_eq H₁ hψs hkH, ← hidx]
    exact Subgroup.relIndex_le_of_le_right le_sup_left (by rw [hidx]; norm_num)
  have h21 := index_ge_of_le_normalizer hH₁N
  have hpos : 0 < (H₁.map ψ).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd hpos h21
  omega

structure FData (G : Type) [Group G] [Finite G] (T M L D : Subgroup G) (α : ↥L →* SL4) :
    Prop where
  hyp : Hyp331 G T M L D
  TL : T ≤ Subgroup.normalizer (L : Set G)
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  kerV : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G)
  mapU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4
  inner : InducesInnerOn T L

namespace FData

variable {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem exists_conj (hD : FData G T M L D α) {t : G} (ht : t ∈ T) :
    ∃ y : ↥L, α y ∈ FLc.Ut 4 ∧ ∀ (x : ↥L) (hx : t * (x : G) * t⁻¹ ∈ L),
      α ⟨t * x * t⁻¹, hx⟩ = α y * α x * (α y)⁻¹ := by
  obtain ⟨y, hyL, hy⟩ := hD.inner t ht
  have key : ∀ (x : ↥L) (hx : t * (x : G) * t⁻¹ ∈ L),
      α ⟨t * x * t⁻¹, hx⟩ = α ⟨y, hyL⟩ * α x * (α ⟨y, hyL⟩)⁻¹ := by
    intro x hx
    have h2 : (⟨t * x * t⁻¹, hx⟩ : ↥L) * (⟨y, hyL⟩ * x * (⟨y, hyL⟩ : ↥L)⁻¹)⁻¹ ∈
        CFSG.pCore 2 ↥L := (Lem3328.mem_pCore_iff _).2 (hy x x.2)
    rw [← hD.ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h2
    rw [h2, map_mul, map_mul, map_inv]
  refine ⟨⟨y, hyL⟩, ?_, key⟩
  have hle : (FLc.Ut 4).map (MulAut.conj (α ⟨y, hyL⟩)).toMonoidHom ≤ FLc.Ut 4 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← hD.mapU] at hu ⊢
    obtain ⟨s, hs, rfl⟩ := hu
    have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
    have hx : t * (s : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) s).mp s.2
    refine ⟨⟨t * s * t⁻¹, hx⟩, Subgroup.mem_subgroupOf.2
      ⟨T.mul_mem (T.mul_mem ht hs'.1) (T.inv_mem ht), hx⟩, ?_⟩
    rw [key s hx]
    rfl
  have hfin : Finite ↥(FLc.Ut 4) := Subtype.finite
  have hc : Nat.card ↥((FLc.Ut 4).map (MulAut.conj (α ⟨y, hyL⟩)).toMonoidHom) =
      Nat.card ↥(FLc.Ut 4) :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  have heq : (FLc.Ut 4).map (MulAut.conj (α ⟨y, hyL⟩)).toMonoidHom = FLc.Ut 4 :=
    Subgroup.eq_of_le_of_card_ge hle hc.ge
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  rwa [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at h1

theorem le_normalizer_liftPre (hD : FData G T M L D α) (I : Set ℕ) :
    T ≤ Subgroup.normalizer (liftPre α (FLc.QI 4 I) : Set G) := by
  intro t ht
  obtain ⟨y, hyU, hy⟩ := hD.exists_conj ht
  have hyI : α y ∈ FLc.QI 4 I := FLc.Ut_le_QI 4 I hyU
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj t).injective).ge)
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hx : t * (l : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) l).mp l.2
  refine ⟨⟨t * l * t⁻¹, hx⟩, ?_, rfl⟩
  show α ⟨t * l * t⁻¹, hx⟩ ∈ FLc.QI 4 I
  rw [hy l hx]
  exact (FLc.QI 4 I).mul_mem ((FLc.QI 4 I).mul_mem hyI hl) ((FLc.QI 4 I).inv_mem hyI)

theorem le_normalizer_Y (hD : FData G T M L D α) (I : Set ℕ) :
    T ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G) := fun _ ht =>
  L3316.mem_normalizer_perfectCore (hD.le_normalizer_liftPre I ht)

theorem mem_lFamilyOf_one (hD : FData G T M L D α) :
    liftCore α (FLc.QI 4 {1}) ∈ lFamilyOf L T := by
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  exact Ln2.liftCore_mem_lFamilyOf hD.hyp.sylow hD.hyp.toSetup331.pCoreOf_ne_bot
    (Nat.card_zmod 2) (by norm_num) hD.surj hD.ker (I := {1}) (a := 1) (m := 3) (by norm_num)
    le_rfl (Or.inr rfl) (Or.inl rfl) hno (hD.le_normalizer_liftPre {1})

theorem mem_lFamilyOf_three (hD : FData G T M L D α) :
    liftCore α (FLc.QI 4 {3}) ∈ lFamilyOf L T := by
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  exact Ln2.liftCore_mem_lFamilyOf hD.hyp.sylow hD.hyp.toSetup331.pCoreOf_ne_bot
    (Nat.card_zmod 2) (by norm_num) hD.surj hD.ker (I := {3}) (a := 0) (m := 3) (by norm_num)
    le_rfl (Or.inl rfl) (Or.inr rfl) hno (hD.le_normalizer_liftPre {3})

theorem pCoreOf_le (hD : FData G T M L D α) : pCoreOf 2 L ≤ T := by
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hD.hyp.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hD.TL)
  exact (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left

theorem sup_eq (hD : FData G T M L D α) :
    L ⊔ T = liftCore α (FLc.QI 4 {1}) ⊔ liftCore α (FLc.QI 4 {3}) ⊔ T := by
  have hkT : α.ker.map L.subtype ≤ T := by
    rw [hD.ker]
    rintro _ ⟨l, hl, rfl⟩
    exact hD.pCoreOf_le ((Lem3328.mem_pCore_iff l).mp hl)
  exact Ln2.sup_liftCore_eq (Nat.card_zmod 2) le_rfl (by norm_num) hD.surj hkT hD.mapU

theorem isPGroup_ker (hD : FData G T M L D α) : IsPGroup 2 ↥α.ker := by
  rw [hD.ker]
  exact CFSG.pCore_isPGroup

theorem exists_levi_one (hD : FData G T M L D α) :
    ∃ ψ : ↥(liftCore α (FLc.QI 4 {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1})) ∧
      ∀ y : ↥(liftCore α (FLc.QI 4 {1})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 1 3 (by norm_num)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  obtain ⟨ψ, hψs, hψk, hψe⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hD.surj
    hD.isPGroup_ker (I := {1}) (a := 1) (m := 3) (by norm_num) le_rfl (Or.inr rfl) (Or.inl rfl)
    hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk, hψe⟩

theorem exists_levi_three (hD : FData G T M L D α) :
    ∃ ψ : ↥(liftCore α (FLc.QI 4 {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {3})) ∧
      ∀ y : ↥(liftCore α (FLc.QI 4 {3})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 0 3 (by norm_num)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  obtain ⟨ψ, hψs, hψk, hψe⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hD.surj
    hD.isPGroup_ker (I := {3}) (a := 0) (m := 3) (by norm_num) le_rfl (Or.inl rfl) (Or.inr rfl)
    hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk, hψe⟩

theorem mem_Ut (hD : FData G T M L D α) (l : ↥L) (hl : (l : G) ∈ T) : α l ∈ FLc.Ut 4 := by
  rw [← hD.mapU]
  exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨hl, l.2⟩, rfl⟩

theorem blkAt_mem_ut {a : ℕ} (h : a + 3 ≤ 4) {g : SL4} (hg : g ∈ FLc.Ut 4)
    {x : SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      blkAt a 3 h (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) :
    x ∈ unitriangular 3 (ZMod 2) := by
  rw [mem_unitriangular] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hx, blkAt_apply]
    exact hg.1 _ _ (by rw [Fin.lt_def] at hij ⊢; simp only; omega)
  · rw [hx, blkAt_apply]
    exact hg.2 _

end FData

end CFSG.Quasithin.H13.L3321
