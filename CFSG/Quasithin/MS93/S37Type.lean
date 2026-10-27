module

public import CFSG.Quasithin.MS93.S37T1
public import CFSG.Quasithin.MS93.MSPBT

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_of_sup {K H M : Subgroup G} (hKM : K ≤ M) (hHM : H ≤ M)
    (hn : M ≤ Subgroup.normalizer (K : Set G)) (hsup : K ⊔ H = M) :
    H.relIndex K = H.relIndex M := by
  have c1 := Subgroup.relIndex_mul_card H K
  have c2 := Subgroup.relIndex_mul_card H M
  have c3 := Subgroup.relIndex_mul_card K M
  have c4 := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.2 hHM] at c2
  rw [inf_eq_left.2 hKM] at c3
  have hKn : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hn
  have c5 : K.relIndex M = K.relIndex H := by
    have h1 := Subgroup.relIndex_sup_right (H.subgroupOf M) (K.subgroupOf M)
    rw [← Subgroup.subgroupOf_sup hHM hKM, sup_comm, hsup, Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hHM] at h1
    rw [Subgroup.relIndex, h1]
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have hHK0 : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  rw [c5] at c3
  rw [inf_comm] at c4
  have e1 : Nat.card M * Nat.card ↥(H ⊓ K) = Nat.card K * Nat.card H := by
    rw [← c3, ← c4]
    ring
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hH0 hHK0) ?_
  calc H.relIndex K * (Nat.card H * Nat.card ↥(H ⊓ K))
      = (H.relIndex K * Nat.card ↥(H ⊓ K)) * Nat.card H := by ring
    _ = Nat.card K * Nat.card H := by rw [c1]
    _ = Nat.card M * Nat.card ↥(H ⊓ K) := e1.symm
    _ = H.relIndex M * (Nat.card H * Nat.card ↥(H ⊓ K)) := by rw [← c2]; ring

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem rho_surjective : Function.Surjective C.rho := fun g => by
  obtain ⟨l, hl⟩ := C.hα g
  exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, by rw [C.rho_of_mem_L l.2]; exact hl⟩

theorem le_normalizer_sup : M ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
  (le_inf C.h.le_normalizer (le_normalizer_pCoreOf M)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup L (pCoreOf 2 M))

theorem exists_type (hodd : IsOddRadical M T) :
    ∃ g : Sp4 F, C.T0bar = (sylS F).map (MulAut.conj g).toMonoidHom ∨
      C.T0bar = (Q₁ F).map (MulAut.conj g).toMonoidHom ∨
      C.T0bar = (Q₂ F).map (MulAut.conj g).toMonoidHom ∨ C.T0bar = ⊥ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := L ⊔ pCoreOf 2 M with hK
  set N : Subgroup G := M ⊓ Subgroup.normalizer (T : Set G) with hN
  have hKM : K ≤ M := C.sup_le_M
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := C.le_normalizer_sup
  have hNM : N ≤ M := inf_le_left
  have hNnN : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  have hNnK : N ≤ Subgroup.normalizer ((N ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_inf hNnN (hNM.trans hMK)
  have hTN : T ≤ N := le_inf C.h.le Subgroup.le_normalizer
  have hP₀ : pCoreOf 2 (N ⊓ K) ≤ T1 M T L := by
    set P₀ := pCoreOf 2 (N ⊓ K) with hP₀def
    have hP₀N : P₀ ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
    have hNP : N ≤ Subgroup.normalizer (P₀ : Set G) :=
      hNnK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (N ⊓ K))
    have hPT : IsPGroup 2 (P₀ ⊔ T : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_sup_of_normal_right' C.h.isPGroup
        (hP₀N.trans inf_le_right)
    have hle : P₀ ⊔ T ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (sup_le hP₀N hTN)
        ((le_inf hNP (inf_le_right : N ≤ Subgroup.normalizer (T : Set G))).trans
          (Subgroup.inf_normalizer_le_normalizer_sup P₀ T)) hPT
    rw [← hodd.1] at hle
    exact le_inf (le_sup_left.trans hle)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
  set X : Subgroup ↥K := (N ⊓ K).subgroupOf K with hX
  set Y : Subgroup (Sp4 F) := X.map C.rho with hY
  have hT1NK : T1 M T L ≤ N ⊓ K := le_inf (T1_le_T.trans hTN) T1_le_sup
  have hT0Y : C.T0bar ≤ Y := by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨(t : G), T1_le_sup t.2⟩, Subgroup.mem_subgroupOf.2 (hT1NK t.2), rfl⟩
  have hT0O : C.T0bar ≤ pCoreOf 2 Y := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hT0Y ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      have hyN : (y : G) ∈ N ⊓ K := Subgroup.mem_subgroupOf.1 hy
      have key : ∀ z : ↥(L ⊔ pCoreOf 2 M), (z : G) ∈ N ⊓ K → ∀ t ∈ C.T0bar,
          C.rho z * t * (C.rho z)⁻¹ ∈ C.T0bar := by
        rintro z hz _ ⟨t, rfl⟩
        have hzt : (z : G) * t * (z : G)⁻¹ ∈ T1 M T L := by
          refine ⟨(Subgroup.mem_normalizer_iff.1 (hz.1.2) t).1 (T1_le_T t.2), ?_⟩
          exact (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem z.2 (T1_le_sup t.2))
            ((L ⊔ pCoreOf 2 M).inv_mem z.2)
        refine ⟨⟨_, hzt⟩, ?_⟩
        rw [C.rho1_apply, C.rho1_apply, ← map_inv, ← map_mul, ← map_mul]
        rfl
      intro t
      refine ⟨key y hyN t, fun ht => ?_⟩
      have hyN' : ((y⁻¹ : ↥(L ⊔ pCoreOf 2 M)) : G) ∈ N ⊓ K := by
        rw [Subgroup.coe_inv]
        exact inv_mem hyN
      have := key y⁻¹ hyN' _ ht
      rw [map_inv, inv_inv] at this
      simpa [mul_assoc] using this
    · exact (C.h.isPGroup.to_le T1_le_T).of_surjective C.rho1.rangeRestrict
        C.rho1.rangeRestrict_surjective
  have hOT : pCoreOf 2 Y ≤ C.T0bar := by
    set O := pCoreOf 2 Y with hO
    let P : Subgroup G := ((O.comap C.rho) ⊓ X).map K.subtype
    have hPNK : P ≤ N ⊓ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx.2
    have key : ∀ y ∈ N ⊓ K, ∀ z ∈ P, y * z * y⁻¹ ∈ P := by
      rintro y hy _ ⟨x, ⟨hxO, hxX⟩, rfl⟩
      have hyK : y ∈ K := hy.2
      refine ⟨⟨y, hyK⟩ * x * ⟨y, hyK⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
      · show C.rho (⟨y, hyK⟩ * x * ⟨y, hyK⟩⁻¹) ∈ O
        rw [map_mul, map_mul, map_inv]
        have hyY : C.rho ⟨y, hyK⟩ ∈ Y := ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hyY) _).1 hxO
      · show (⟨y, hyK⟩ * x * ⟨y, hyK⟩⁻¹ : ↥K) ∈ (N ⊓ K).subgroupOf K
        rw [Subgroup.mem_subgroupOf]
        have hxNK : (x : G) ∈ N ⊓ K := Subgroup.mem_subgroupOf.1 hxX
        exact (N ⊓ K).mul_mem ((N ⊓ K).mul_mem hy hxNK) ((N ⊓ K).inv_mem hy)
    have hPn : N ⊓ K ≤ Subgroup.normalizer (P : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨key y hy z, fun h => ?_⟩
      have := key y⁻¹ ((N ⊓ K).inv_mem hy) _ h
      simpa [mul_assoc] using this
    have hP2 : IsPGroup 2 P := by
      rintro ⟨_, ⟨x, ⟨hxO, -⟩, rfl⟩⟩
      obtain ⟨e, he⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨C.rho x, hxO⟩
      have h1 : C.rho (x ^ 2 ^ e) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val he
      rw [C.rho_eq_one_iff] at h1
      obtain ⟨e', he'⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, h1⟩
      refine ⟨e + e', Subtype.ext ?_⟩
      have he2 : (((x : G) ^ 2 ^ e) ^ 2 ^ e') = 1 := by simpa using congrArg Subtype.val he'
      simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_subtype]
      rw [pow_add, pow_mul, he2]
    have hPle : P ≤ pCoreOf 2 (N ⊓ K) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPNK hPn hP2
    intro o ho
    obtain ⟨x, hxX, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y ho
    have hxP : (x : G) ∈ P := ⟨x, ⟨ho, hxX⟩, rfl⟩
    have hxT1 : (x : G) ∈ T1 M T L := hP₀ (hPle hxP)
    exact ⟨⟨x, hxT1⟩, by rw [C.rho1_apply]⟩
  have hsup : K ⊔ N = M := by
    refine le_antisymm (sup_le hKM hNM) ?_
    rw [C.h.eq_sup]
    exact sup_le (le_sup_left.trans le_sup_left) (hTN.trans le_sup_right)
  have hidx : ¬ 2 ∣ Y.index := by
    have h1 : Y.index ∣ X.index := Subgroup.index_map_dvd X C.rho_surjective
    have h2 : X.index = (Subgroup.normalizer (T : Set G)).relIndex M := by
      show (N ⊓ K).relIndex K = _
      rw [Subgroup.inf_relIndex_right, relIndex_eq_of_sup hKM hNM hMK hsup, hN,
        Subgroup.inf_relIndex_left]
    exact fun h => hodd.2 (h2 ▸ h.trans h1)
  obtain ⟨S₁⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  set P₁ : Subgroup (Sp4 F) := (S₁ : Subgroup ↥Y).map Y.subtype with hP₁
  have hP₁Y : P₁ ≤ Y := Subgroup.map_subtype_le _
  have hP₁2 : IsPGroup 2 P₁ := S₁.isPGroup'.map Y.subtype
  have hP₁idx : ¬ 2 ∣ P₁.index := by
    rw [← Subgroup.relIndex_mul_index hP₁Y]
    have e : P₁.relIndex Y = (S₁ : Subgroup ↥Y).index := by
      rw [Subgroup.relIndex, hP₁, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
    rw [e]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h' | h'
    · exact S₁.not_dvd_index h'
    · exact hidx h'
  obtain ⟨g, -, hcases⟩ := pCoreOf_of_sylow_le (Y := Y) (hP₁2.toSylow hP₁idx) (by
    rw [IsPGroup.toSylow_coe]
    exact hP₁Y)
  have hEq : C.T0bar = pCoreOf 2 Y := le_antisymm hT0O hOT
  exact ⟨g, by rw [hEq]; exact hcases⟩

omit C [Finite G] [Fintype F] in
theorem isSum_conj {A U Z : Subgroup G} {α : ↥A →* ↥(StatedSp 2 F)}
    (hn : IsSumOfNaturalModulesVia A U Z α false 1) (g : Sp4 F) :
    IsSumOfNaturalModulesVia A U Z ((MulAut.conj g⁻¹).toMonoidHom.comp α) false 1 := by
  obtain ⟨hAU, hZU, β, hβs, hβk, hβe⟩ := hn
  let f : (Fin 1 → V4 F) →+ (Fin 1 → V4 F) :=
    { toFun := fun w i => mat g⁻¹ *ᵥ w i
      map_zero' := by funext i; simp
      map_add' := fun w w' => by funext i; simp [Matrix.mulVec_add] }
  have hf : ∀ w i, f w i = mat g⁻¹ *ᵥ w i := fun _ _ => rfl
  refine ⟨hAU, hZU, (AddMonoidHom.toMultiplicative f).comp β, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun i => mat g *ᵥ Multiplicative.toAdd x i)
    refine ⟨u, ?_⟩
    rw [MonoidHom.comp_apply, hu]
    apply Multiplicative.toAdd.injective
    funext i
    show f (fun i => mat g *ᵥ Multiplicative.toAdd x i) i = Multiplicative.toAdd x i
    rw [hf, mat_inv_mulVec]
  · ext u
    rw [MonoidHom.mem_ker, ← hβk, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      have := congrFun (congrArg Multiplicative.toAdd h) i
      have h2 : mat g⁻¹ *ᵥ Multiplicative.toAdd (β u) i = 0 := this
      have h3 := congrArg (fun v => mat g *ᵥ v) h2
      simp only [Matrix.mulVec_zero, mat_mulVec_inv] at h3
      exact h3
    · intro h
      rw [h, map_one]
  · intro a u v huv i
    have h1 := hβe a u v huv i
    show f (Multiplicative.toAdd (β v)) i = _
    rw [hf, h1]
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show mat g⁻¹ *ᵥ (mat (α a) *ᵥ Multiplicative.toAdd (β u) i) =
      mat (g⁻¹ * α a * g⁻¹⁻¹) *ᵥ (f (Multiplicative.toAdd (β u)) i)
    rw [hf, inv_inv, mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv]

@[expose] noncomputable def conjG (g : Sp4 F) : Cfg M T L F where
  h := C.h
  hVU := C.hVU
  k := C.k
  hk := C.hk
  hF := C.hF
  α := (MulAut.conj g⁻¹).toMonoidHom.comp C.α
  hα := (MulAut.conj g⁻¹).surjective.comp C.hα
  hnat := isSum_conj C.hnat g

theorem rho1_conjG (g : Sp4 F) (t : ↥(T1 M T L)) :
    (C.conjG g).rho1 t = g⁻¹ * C.rho1 t * g := by
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_T1 t.2
  have ht : t = ⟨l * q, e ▸ t.2⟩ := Subtype.ext e.symm
  rw [ht, C.rho1_apply, (C.conjG g).rho1_apply, C.rho_mul hl.2 hq, (C.conjG g).rho_mul hl.2 hq]
  show g⁻¹ * C.α ⟨l, hl.2⟩ * g⁻¹⁻¹ = _
  rw [inv_inv]

theorem T0bar_conjG (g : Sp4 F) :
    (C.conjG g).T0bar = C.T0bar.map (MulAut.conj g⁻¹).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨C.rho1 t, ⟨t, rfl⟩, ?_⟩
    rw [C.rho1_conjG g t]
    simp
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    rw [C.rho1_conjG g t]
    simp

omit C [Finite G] [Fintype F] in
theorem map_conj_inv_map_conj (X : Subgroup (Sp4 F)) (g : Sp4 F) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id X]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

theorem exists_std (hodd : IsOddRadical M T) :
    ∃ C' : Cfg M T L F, C'.T0bar = sylS F ∨ C'.T0bar = Q₁ F ∨ C'.T0bar = Q₂ F ∨ C'.T0bar = ⊥ := by
  obtain ⟨g, hg⟩ := C.exists_type hodd
  refine ⟨C.conjG g, ?_⟩
  rw [C.T0bar_conjG]
  rcases hg with h | h | h | h <;> rw [h]
  · exact Or.inl (map_conj_inv_map_conj _ g)
  · exact Or.inr (Or.inl (map_conj_inv_map_conj _ g))
  · exact Or.inr (Or.inr (Or.inl (map_conj_inv_map_conj _ g)))
  · exact Or.inr (Or.inr (Or.inr (Subgroup.map_bot _)))

end Cfg

end CFSG.Quasithin.MS93.S37
