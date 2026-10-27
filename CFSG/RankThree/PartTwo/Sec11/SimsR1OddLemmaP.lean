module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1LemP
public import CFSG.RankThree.PartTwo.Sec11.Item116ResidueT
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Assembly.RankThreeEven (projSL)

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

section Frattini

variable {H : Type} [Group H] [Finite H]

private def conjAut (P : Subgroup H) (n : H) (hn : ∀ y, y ∈ P ↔ n * y * n⁻¹ ∈ P) : P ≃* P where
  toFun x := ⟨n * x * n⁻¹, (hn x).mp x.2⟩
  invFun x := ⟨n⁻¹ * x * n, (hn _).mpr (by simpa [mul_assoc] using x.2)⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

private theorem exists_mem_conj_le {p : ℕ} [Fact p.Prime] {K : Subgroup H} (Q : Sylow p K)
    {X : Subgroup H} (hXK : X ≤ K) (hX : IsPGroup p X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ (Q : Subgroup K).map K.subtype := by
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

private theorem exists_mem_mul_normalizes {p : ℕ} [Fact p.Prime] {K : Subgroup H} (Q : Sylow p K)
    {g : H} (hg : ∀ y, y ∈ K ↔ g * y * g⁻¹ ∈ K) :
    ∃ k ∈ K, ∀ y, y ∈ (Q : Subgroup K).map K.subtype ↔
      (k⁻¹ * g) * y * (k⁻¹ * g)⁻¹ ∈ (Q : Subgroup K).map K.subtype := by
  set P : Subgroup H := (Q : Subgroup K).map K.subtype with hP
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hXK : P.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hg y).mp (hPK hy)
  have hXp : IsPGroup p (P.map (MulAut.conj g).toMonoidHom) := (Q.2.map K.subtype).map _
  obtain ⟨k, hkK, hk⟩ := exists_mem_conj_le Q hXK hXp
  have hfwd : ∀ z ∈ P, (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ ∈ P := by
    intro z hz
    have h1 := hk (g * z * g⁻¹) ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have e : (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * z * g⁻¹) * k := by group
    rw [e]
    exact h1
  refine ⟨k, hkK, fun y => ⟨hfwd y, fun hy => ?_⟩⟩
  have hle : P.map (MulAut.conj (k⁻¹ * g)).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hfwd z hz
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj (k⁻¹ * g)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (k⁻¹ * g)).injective).ge
  have hy' : (k⁻¹ * g) * y * (k⁻¹ * g)⁻¹ ∈ P.map (MulAut.conj (k⁻¹ * g)).toMonoidHom := by
    rw [Subgroup.eq_of_le_of_card_ge hle hcard]
    exact hy
  obtain ⟨z, hz, hzy⟩ := hy'
  exact mul_left_cancel (mul_right_cancel (show (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ =
    (k⁻¹ * g) * y * (k⁻¹ * g)⁻¹ from hzy)) ▸ hz

end Frattini

namespace LemmaP

section Abstract

variable {H : Type} [Group H] [Finite H] {L : Type} [Group L]

theorem exists_elemAbelian_of_surjective_of_irreducible (hB : KFacts.BlackburnRankTwo) {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) {φ : H →* L} (hφ : Function.Surjective φ) {U : Subgroup L}
    (hU : CFSG.Assembly.IsElemAbelian p U) (hUc : Nat.card U = p ^ 3) {t : L}
    (ht : ∀ x, x ∈ U ↔ t * x * t⁻¹ ∈ U)
    (hirr : ∀ W : Subgroup L, W ≤ U → (∀ x ∈ W, t * x * t⁻¹ ∈ W) → W = ⊥ ∨ W = U) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  classical
  have hUp : IsPGroup p U := CFSG.Open.IsElemAbelian.isPGroup hU
  have hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set K : Subgroup H := U.comap φ with hK
  have hφK : Function.Surjective (φ.subgroupComap U) := by
    intro u
    obtain ⟨x, hx⟩ := hφ u
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact u.2⟩, Subtype.ext hx⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p K))
  set P : Subgroup H := (S : Subgroup K).map K.subtype with hP
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := S.2.map K.subtype
  have hPU : ∀ x ∈ P, φ x ∈ U := fun x hx => Subgroup.mem_comap.mp (hPK hx)
  have hPmap : ∀ u ∈ U, ∃ x ∈ P, φ x = u := by
    intro u hu
    have hS : ((S.mapSurjective hφK : Sylow p U) : Subgroup U) = ⊤ :=
      ((S.mapSurjective hφK).is_maximal' (hUp.to_subgroup ⊤) le_top).symm
    have hmem : (⟨u, hu⟩ : U) ∈ (S : Subgroup K).map (φ.subgroupComap U) := by
      rw [← Sylow.coe_mapSurjective hφK, hS]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxu⟩ := hmem
    exact ⟨x.1, ⟨x, hx, rfl⟩, congrArg Subtype.val hxu⟩
  obtain ⟨g, hg⟩ := hφ t
  have hgK : ∀ y, y ∈ K ↔ g * y * g⁻¹ ∈ K := by
    intro y
    simp only [hK, Subgroup.mem_comap, map_mul, map_inv, hg]
    exact ht _
  obtain ⟨k, hkK, hn⟩ := exists_mem_mul_normalizes S hgK
  set n : H := k⁻¹ * g with hn_def
  have hkU : φ k ∈ U := Subgroup.mem_comap.mp hkK
  have hφn : ∀ x ∈ P, φ (n * x * n⁻¹) = t * φ x * t⁻¹ := by
    intro x hx
    have h1 : t * φ x * t⁻¹ ∈ U := (ht _).mp (hPU x hx)
    have e : φ (n * x * n⁻¹) = (φ k)⁻¹ * (t * φ x * t⁻¹) * φ k := by
      simp only [hn_def, map_mul, map_inv, hg]
      group
    rw [e, hc _ (U.inv_mem hkU) _ h1]
    group
  set M : Subgroup P := (φ.comp P.subtype).ker with hM
  have hpow : ∀ x : P, x ^ p ∈ M := by
    intro x
    rw [hM, MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, map_pow]
    exact hU.2 _ (hPU x x.2)
  have hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ M := by
    intro x y
    rw [hM, MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, map_mul, map_inv]
    have := hc _ (hPU x x.2) _ (hPU y y.2)
    calc φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = φ y * φ x * (φ x)⁻¹ * (φ y)⁻¹ := by rw [this]
      _ = 1 := by group
  have hidx : M.index = p ^ 3 := by
    have hrange : (φ.comp P.subtype).range = U := by
      ext u
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        exact hPU x x.2
      · intro hu
        obtain ⟨x, hx, hxu⟩ := hPmap u hu
        exact ⟨⟨x, hx⟩, hxu⟩
    rw [hM, Subgroup.index_ker, hrange]
    exact hUc
  let h : P ≃* P := conjAut P n hn
  have hφh : ∀ x : P, φ (h x : H) = t * φ x * t⁻¹ := fun x => hφn x x.2
  have hMh : ∀ x : P, h x ∈ M ↔ x ∈ M := fun x => by simp [hM, hφh]
  have hmap : M.map h.toMonoidHom = M := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hMh x).mpr hx
    · intro hy
      exact ⟨h.symm y, (hMh _).mp (by simpa using hy), by simp⟩
  have hirr' : ∀ N : Subgroup P, M ≤ N → N.map h.toMonoidHom = N → N = M ∨ N = ⊤ := by
    intro N hMN hNh
    set W : Subgroup L := N.map (φ.comp P.subtype) with hW
    have hWU : W ≤ U := by
      rintro _ ⟨x, -, rfl⟩
      exact hPU x x.2
    have hWt : ∀ x ∈ W, t * x * t⁻¹ ∈ W := by
      rintro _ ⟨x, hx, rfl⟩
      have hhx : h x ∈ N := by
        rw [← hNh]
        exact ⟨x, hx, rfl⟩
      refine ⟨h x, hhx, ?_⟩
      exact hφh x
    rcases hirr W hWU hWt with hW0 | hWU'
    · left
      refine le_antisymm (fun x hx => ?_) hMN
      have : (φ.comp P.subtype) x ∈ W := ⟨x, hx, rfl⟩
      rw [hW0, Subgroup.mem_bot] at this
      exact this
    · right
      rw [eq_top_iff]
      intro x _
      have hxW : (φ.comp P.subtype) x ∈ W := by
        rw [hWU']
        exact hPU x x.2
      obtain ⟨y, hy, hyx⟩ := hxW
      have hyM : y⁻¹ * x ∈ M := by
        rw [hM, MonoidHom.mem_ker]
        simp only [MonoidHom.comp_apply, map_mul, map_inv] at hyx ⊢
        rw [hyx]
        group
      have := N.mul_mem hy (hMN hyM)
      simpa using this
  obtain ⟨E, hE, hE3⟩ := exists_elemAbelian_of_irreducible hB hp hPp M hpow hcomm hidx h hmap hirr'
  exact ⟨E.map P.subtype, CFSG.Open.IsElemAbelian.map hE _, by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hE3⟩

end Abstract

end LemmaP

section PSL2

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

private theorem projSL_eq_range :
    projSL 2 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

private noncomputable def toProjSL : SL(2, F) →* projSL 2 F :=
  (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).codRestrict
    (projSL 2 F) (fun A => by rw [projSL_eq_range]; exact ⟨A, rfl⟩)

private def uSL (s : F) : SL(2, F) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem uSL_mul (s s' : F) : uSL s * uSL s' = uSL (s + s') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [uSL, Matrix.mul_fin_two, add_comm]

private theorem uSL_zero : uSL (0 : F) = 1 := by
  apply Subtype.ext
  simp [uSL, Matrix.one_fin_two]

private def tSL (l : Fˣ) : SL(2, F) :=
  ⟨!![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

private theorem tSL_mul_uSL (l : Fˣ) (s : F) :
    tSL l * uSL s = uSL ((l : F) ^ 2 * s) * tSL l := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hl : (l : F) ≠ 0 := l.ne_zero
  simp [tSL, uSL, Matrix.mul_fin_two]
  field_simp

private noncomputable def uHom : Multiplicative F →* projSL 2 F where
  toFun s := toProjSL (uSL (Multiplicative.toAdd s))
  map_one' := by simp [uSL_zero]
  map_mul' a b := by
    rw [toAdd_mul, ← map_mul, uSL_mul]

private theorem uHom_apply (s : F) :
    uHom (Multiplicative.ofAdd s) = toProjSL (uSL s) := rfl

private theorem uHom_injective : Function.Injective (uHom (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have h1 : (Matrix.SpecialLinearGroup.toPGL (uSL (Multiplicative.toAdd s)) :
      ProjGenLinGroup (Fin 2) F) = 1 := congrArg Subtype.val hs
  have h2 : uSL (Multiplicative.toAdd s) ∈
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).ker := h1
  rw [Matrix.SpecialLinearGroup.toPGL_ker, Matrix.SpecialLinearGroup.mem_center_iff] at h2
  obtain ⟨r, -, hr⟩ := h2
  have h3 := congrFun (congrFun hr 0) 1
  simp [uSL, Matrix.scalar_apply, Matrix.diagonal] at h3
  exact h3.symm

private theorem exists_borel_data {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) [Finite F] [CharP F p]
    (hF : Nat.card F = p ^ 3) :
    ∃ (U : Subgroup (projSL 2 F)) (t : projSL 2 F),
      CFSG.Assembly.IsElemAbelian p U ∧ Nat.card U = p ^ 3 ∧ (∀ x, x ∈ U ↔ t * x * t⁻¹ ∈ U) ∧
      ∀ W : Subgroup (projSL 2 F), W ≤ U → (∀ x ∈ W, t * x * t⁻¹ ∈ W) → W = ⊥ ∨ W = U := by
  classical
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hpp : p.Prime := Fact.out
  obtain ⟨l, hl⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ)
  rw [Nat.card_units, hF] at hl
  set μ : F := (l : F) ^ 2 with hμ
  have hμ0 : μ ≠ 0 := pow_ne_zero 2 l.ne_zero
  have hμbot : μ ∉ Set.range (algebraMap (ZMod p) F) := by
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact hμ0 hc.symm
    have h1 : (l : F) ^ (2 * (p - 1)) = 1 := by
      rw [pow_mul, ← hμ, ← hc, ← map_pow, ZMod.pow_card_sub_one_eq_one hc0, map_one]
    have h2 : l ^ (2 * (p - 1)) = 1 := Units.ext (by simpa using h1)
    have h3 : orderOf l ∣ 2 * (p - 1) := orderOf_dvd_of_pow_eq_one h2
    rw [hl] at h3
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 : 25 * p ≤ p ^ 3 := by
      have : 25 ≤ p * p := by nlinarith
      calc 25 * p ≤ (p * p) * p := Nat.mul_le_mul_right p this
        _ = p ^ 3 := by ring
    omega
  have hfin : Module.finrank (ZMod p) F = 3 := by
    have h := FiniteField.pow_finrank_eq_natCard p F
    rw [hF] at h
    exact Nat.pow_right_injective hpp.two_le h
  have hsimple : IsSimpleOrder (Subalgebra (ZMod p) F) :=
    Subalgebra.isSimpleOrder_of_finrank_prime (ZMod p) F (by rw [hfin]; exact Nat.prime_three)
  set u : Multiplicative F →* projSL 2 F := uHom with hu
  have huinj : Function.Injective u := uHom_injective
  set U : Subgroup (projSL 2 F) := (⊤ : Subgroup (Multiplicative F)).map u with hU
  set t : projSL 2 F := toProjSL (tSL l) with ht
  have hmemU : ∀ x, x ∈ U ↔ ∃ s : F, u (Multiplicative.ofAdd s) = x := by
    intro x
    rw [hU, Subgroup.mem_map]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨Multiplicative.toAdd y, hy⟩, fun ⟨s, hs⟩ => ⟨_, trivial, hs⟩⟩
  have hu_add : ∀ a b : F, u (Multiplicative.ofAdd (a + b)) =
      u (Multiplicative.ofAdd a) * u (Multiplicative.ofAdd b) := fun a b => by
    rw [ofAdd_add, map_mul]
  have hu_zero : u (Multiplicative.ofAdd (0 : F)) = 1 := by
    rw [ofAdd_zero, map_one]
  have hu_neg : ∀ a : F, u (Multiplicative.ofAdd (-a)) = (u (Multiplicative.ofAdd a))⁻¹ :=
    fun a => by rw [ofAdd_neg, map_inv]
  have hconj : ∀ s : F, t * u (Multiplicative.ofAdd s) * t⁻¹ = u (Multiplicative.ofAdd (μ * s)) := by
    intro s
    rw [mul_inv_eq_iff_eq_mul, hu, uHom_apply, uHom_apply, ← map_mul, ← map_mul]
    exact congrArg toProjSL (tSL_mul_uSL l s)
  have hTop : CFSG.Assembly.IsElemAbelian p (⊤ : Subgroup (Multiplicative F)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  refine ⟨U, t, hTop.map u, ?_, ?_, ?_⟩
  · rw [hU, Subgroup.card_map_of_injective huinj, Subgroup.card_top]
    exact hF
  · intro x
    rw [hmemU, hmemU]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨μ * s, (hconj s).symm ▸ rfl⟩
    · rintro ⟨s, hs⟩
      refine ⟨μ⁻¹ * s, ?_⟩
      have h1 := hconj (μ⁻¹ * s)
      rw [mul_inv_cancel_left₀ hμ0, hs] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  · intro W hWU hWt
    by_cases hW1 : ∀ w ∈ W, w = 1
    · exact Or.inl ((Subgroup.eq_bot_iff_forall W).mpr hW1)
    · right
      push Not at hW1
      obtain ⟨w, hwW, hw1⟩ := hW1
      obtain ⟨s₀, hs₀⟩ := (hmemU w).mp (hWU hwW)
      let S : AddSubgroup F :=
        { carrier := {s | u (Multiplicative.ofAdd s) ∈ W}
          add_mem' := fun {a b} ha hb => by
            show u (Multiplicative.ofAdd (a + b)) ∈ W
            rw [hu_add]
            exact W.mul_mem ha hb
          zero_mem' := by
            show u (Multiplicative.ofAdd (0 : F)) ∈ W
            rw [hu_zero]
            exact W.one_mem
          neg_mem' := fun {a} ha => by
            show u (Multiplicative.ofAdd (-a)) ∈ W
            rw [hu_neg]
            exact W.inv_mem ha }
      have hS : ∀ s, s ∈ S ↔ u (Multiplicative.ofAdd s) ∈ W := fun s => Iff.rfl
      let R : Subalgebra (ZMod p) F :=
        { carrier := {c | ∀ s ∈ S, c * s ∈ S}
          mul_mem' := fun {a b} ha hb s hs => by simpa [mul_assoc] using ha _ (hb s hs)
          one_mem' := fun s hs => by simpa using hs
          add_mem' := fun {a b} ha hb s hs => by
            simpa [add_mul] using S.add_mem (ha s hs) (hb s hs)
          zero_mem' := fun s _ => by simpa using S.zero_mem
          algebraMap_mem' := fun r s hs => by
            have h1 : algebraMap (ZMod p) F r = ((r.val : ℕ) : F) := by
              rw [← map_natCast (algebraMap (ZMod p) F), ZMod.natCast_zmod_val]
            show algebraMap (ZMod p) F r * s ∈ S
            rw [h1, ← nsmul_eq_mul]
            exact S.nsmul_mem hs _ }
      have hμR : μ ∈ R := fun s hs => by
        show u (Multiplicative.ofAdd (μ * s)) ∈ W
        rw [← hconj]
        exact hWt _ hs
      have hRtop : R = ⊤ := by
        rcases hsimple.eq_bot_or_eq_top R with h | h
        · exact absurd (Algebra.mem_bot.mp (h ▸ hμR)) hμbot
        · exact h
      have hs₀S : s₀ ∈ S := by
        rw [hS, hs₀]
        exact hwW
      have hs₀0 : s₀ ≠ 0 := by
        rintro rfl
        exact hw1 (hs₀ ▸ hu_zero)
      refine le_antisymm hWU (fun x hx => ?_)
      obtain ⟨s, rfl⟩ := (hmemU x).mp hx
      have hc : s * s₀⁻¹ ∈ R := hRtop ▸ Algebra.mem_top
      have := hc s₀ hs₀S
      rw [inv_mul_cancel_right₀ hs₀0] at this
      exact this

private theorem exists_elemAbelian_of_surjective_PSL2 (hB : KFacts.BlackburnRankTwo) {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) [Finite F] [CharP F p] (hF : Nat.card F = p ^ 3) {H : Type}
    [Group H] [Finite H] (φ : H →* projSL 2 F) (hφ : Function.Surjective φ) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  obtain ⟨U, t, hU, hUc, ht, hirr⟩ := exists_borel_data hp hF
  exact LemmaP.exists_elemAbelian_of_surjective_of_irreducible hB hp hφ hU hUc ht hirr

end PSL2

theorem exists_elemAbelian_of_surjective_L2Cube (hB : KFacts.BlackburnRankTwo) {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) {H : Type} [Group H] [Finite H]
    (φ : H →* projSL 2 (GaloisField p (3 * 1))) (hφ : Function.Surjective φ) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E :=
  exists_elemAbelian_of_surjective_PSL2 hB hp
    (by rw [GaloisField.card p (3 * 1) (by norm_num)]) φ hφ

section Residue


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem eq_bot_of_normalized_by_elemAbelian (h : ResidueConfig G A c L a R Y d) {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) {X E : Subgroup G} (hX : IsPGroup 2 X)
    (hE : CFSG.Assembly.IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  by_contra hne
  have hp' : p.Prime := Fact.out
  have hX2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hne, hX, rfl⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
  have h3 : 3 ≤ n := by
    by_contra hn3
    have := Nat.pow_lt_pow_right hp'.one_lt (not_le.mp hn3)
    omega
  have h1 := Sec5.le_pRank_of_elemAbelian hp' hEX hE hn
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank hp'.one_lt hX2
  have h4 := h.localRank_lt p hp' (by omega)
  omega

end Residue

end CFSG.RankThree.PartTwo.Sec11.SimsR1
