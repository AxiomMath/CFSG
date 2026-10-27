module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22Two
public import CFSG.Quasithin.Vol2.KGFactC31NoM22SL3

public section

namespace CFSG.Quasithin.KGC31.NoM22

open Function CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31.KG443
open scoped MatrixGroups

@[expose] def sqHom {B : Type*} [Group B] (A : Subgroup B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : ↥A →* ↥A where
  toFun x := x ^ 2
  map_one' := by simp
  map_mul' x y := by
    have h : x * y = y * x := Subtype.ext (hA x x.2 y y.2)
    rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← h, mul_assoc, mul_assoc]

theorem card_eq_ker_mul_range {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

theorem not_surj_elem {B E : Type} [Group B] [Finite B] [Group E] [Finite E] (A : Subgroup B)
    (hA : A.index ≤ 2) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA4 : Nat.card (sqHom A hAc).ker ≤ 4) (hE2 : ∀ e : E, e ^ 2 = 1) (hE16 : 16 ≤ Nat.card E)
    {ψ : B →* E} (hψ : Surjective ψ) : False := by
  have hAi : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (A.map ψ).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hAi) (Subgroup.index_map_dvd A hψ)).trans hA
  have hcE := (A.map ψ).card_mul_index
  have h8 : 8 ≤ Nat.card (A.map ψ) := by
    rcases Nat.lt_or_ge (Nat.card (A.map ψ)) 8 with h | h
    · exfalso
      have : Nat.card (A.map ψ) * (A.map ψ).index ≤ 7 * 2 :=
        Nat.mul_le_mul (by omega) hidx
      omega
    · exact h
  let ψA : ↥A →* E := ψ.comp A.subtype
  have hrange : Nat.card ψA.range = Nat.card (A.map ψ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := card_eq_ker_mul_range ψA
  have h2 := card_eq_ker_mul_range (sqHom A hAc)
  have h3 : (sqHom A hAc).range ≤ ψA.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    show ψ ((x : B) ^ 2) = 1
    rw [map_pow, hE2]
  have h4 : Nat.card (sqHom A hAc).range ≤ Nat.card ψA.ker := Subgroup.card_le_of_le h3
  have hk0 : 0 < Nat.card ψA.ker := Nat.card_pos
  rw [hrange] at h1
  have h5 : Nat.card ψA.ker * Nat.card (A.map ψ) ≤ Nat.card ψA.ker * 4 := by
    calc Nat.card ψA.ker * Nat.card (A.map ψ) = Nat.card ↥A := h1.symm
      _ = Nat.card (sqHom A hAc).ker * Nat.card (sqHom A hAc).range := h2
      _ ≤ 4 * Nat.card ψA.ker := Nat.mul_le_mul hA4 h4
      _ = Nat.card ψA.ker * 4 := mul_comm _ _
  have := Nat.le_of_mul_le_mul_left h5 hk0
  omega

@[expose] def e16W : Fin 4 → List ℤ := ![
  [2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2],
  [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2],
  [1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
  [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2,
    2, 1, 2, 2, 2, 1]]

@[expose] def e16T (c : ℕ) : Table :=
  compT 22 (compT 22 (compT 22 (powT 22 (c % 2) (wordT 22 M22.gensT (e16W 0)))
    (powT 22 (c / 2 % 2) (wordT 22 M22.gensT (e16W 1))))
    (powT 22 (c / 4 % 2) (wordT 22 M22.gensT (e16W 2))))
    (powT 22 (c / 8 % 2) (wordT 22 M22.gensT (e16W 3)))

@[expose] def e16G (c : ℕ) : M22.G₀ :=
  M22.elt (e16W 0) ^ (c % 2) * M22.elt (e16W 1) ^ (c / 2 % 2) * M22.elt (e16W 2) ^ (c / 4 % 2) *
    M22.elt (e16W 3) ^ (c / 8 % 2)

theorem rep_e16 (c : ℕ) : Rep 22 (e16T c) ((e16G c : M22.G₀) : Equiv.Perm (Fin 22)) := by
  unfold e16T e16G
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  exact ((((M22.rep_elt _).powT M22.hn22 _).compT ((M22.rep_elt _).powT M22.hn22 _)).compT
    ((M22.rep_elt _).powT M22.hn22 _)).compT ((M22.rep_elt _).powT M22.hn22 _)

theorem e16T_nodup : ((List.range 16).map fun c => (List.range 22).map (ap (e16T c))).Nodup := by
  decide +kernel

@[expose] def e16Tab (i : Fin 4) : Table := wordT 22 M22.gensT (e16W i)

theorem e16Tab_sq : ∀ i : Fin 4, powT 22 2 (e16Tab i) = idT 22 := by decide +kernel

theorem e16Tab_comm :
    ∀ i j : Fin 4, compT 22 (e16Tab i) (e16Tab j) = compT 22 (e16Tab j) (e16Tab i) := by
  decide +kernel

theorem e16_sq (i : Fin 4) : M22.elt (e16W i) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact perm_eq_of_rep ((M22.rep_elt (e16W i)).powT M22.hn22 2) (Rep.idT M22.hn22)
    (e16Tab_sq i)

theorem e16_comm (i j : Fin 4) :
    M22.elt (e16W i) * M22.elt (e16W j) = M22.elt (e16W j) * M22.elt (e16W i) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact perm_eq_of_rep ((M22.rep_elt (e16W i)).compT (M22.rep_elt (e16W j)))
    ((M22.rep_elt (e16W j)).compT (M22.rep_elt (e16W i))) (e16Tab_comm i j)

@[expose] def e16Sub : Subgroup M22.G₀ :=
  Subgroup.closure (Set.range fun i : Fin 4 => M22.elt (e16W i))

theorem e16W_mem (i : Fin 4) : M22.elt (e16W i) ∈ e16Sub :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem e16Sub_sq : ∀ x ∈ e16Sub, x ^ 2 = 1 := by
  have hcomm : (Set.range fun i : Fin 4 => M22.elt (e16W i)).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact e16_comm i j
  have : IsMulCommutative ↥e16Sub := Subgroup.isMulCommutative_closure hcomm
  let c : CommGroup ↥e16Sub :=
    { (inferInstance : Group ↥e16Sub) with mul_comm := this.is_comm.comm }
  let π : ↥e16Sub →* ↥e16Sub := @powMonoidHom ↥e16Sub c.toCommMonoid 2
  have hle : e16Sub ≤ (π.ker).map e16Sub.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨_, e16W_mem i⟩, Subtype.ext (by simpa [π] using e16_sq i), rfl⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hle hx
  have : π y = 1 := hy
  exact congrArg Subtype.val this

theorem e16G_mem (c : ℕ) : e16G c ∈ e16Sub := by
  unfold e16G
  refine e16Sub.mul_mem (e16Sub.mul_mem (e16Sub.mul_mem ?_ ?_) ?_) ?_ <;>
    exact e16Sub.pow_mem (e16W_mem _) _

theorem card_e16Sub : 16 ≤ Nat.card e16Sub := by
  have hinj : Set.InjOn e16G (Set.Iio 16) := by
    intro c hc c' hc' h
    have hl : (List.range 22).map (ap (e16T c)) = (List.range 22).map (ap (e16T c')) := by
      refine List.map_congr_left fun i hi => ?_
      have hi' : i < 22 := List.mem_range.mp hi
      rw [rep_e16 c i hi', rep_e16 c' i hi', h]
    exact List.inj_on_of_nodup_map e16T_nodup (List.mem_range.mpr hc) (List.mem_range.mpr hc') hl
  let f : Fin 16 → e16Sub := fun c => ⟨e16G c, e16G_mem c⟩
  have hf : Injective f := fun c c' h => Fin.ext (hinj c.2 c'.2 (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem not_secOnto_of_sylow {X : Type} [Group X] [Finite X] {W D : Subgroup X}
    (hW : IsPGroup 2 W) (hWi : ¬ 2 ∣ W.index) (hDi : D.relIndex W ≤ 2)
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD4 : Nat.card {x : ↥D // x ^ 2 = 1} ≤ 4) :
    ¬ SecOnto X (NativeSporadic.Carrier .M22) := by
  classical
  rintro ⟨Y, φ, hφ⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (NativeSporadic.Carrier .M22) := (inferInstance : Finite M22.G₀)
  let E : Subgroup (NativeSporadic.Carrier .M22) := e16Sub
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := e16Sub_sq
  have hEp : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x x.2)⟩
  let Q : Subgroup ↥Y := E.comap φ
  let φQ : ↥Q →* ↥E := (φ.comp Q.subtype).codRestrict E fun q => q.2
  have hφQ : Surjective φQ := fun e => by
    obtain ⟨y, hy⟩ := hφ (e : NativeSporadic.Carrier .M22)
    exact ⟨⟨y, show φ y ∈ E from hy ▸ e.2⟩, Subtype.ext hy⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥Q))
  have hPE : (P₀ : Subgroup ↥Q).map φQ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφQ P₀]
    exact ((Sylow.mapSurjective hφQ P₀).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  let ι : ↥Q →* X := Y.subtype.comp Q.subtype
  have hι : Injective ι := Y.subtype_injective.comp Q.subtype_injective
  let R : Subgroup X := (P₀ : Subgroup ↥Q).map ι
  have hR : IsPGroup 2 R := P₀.isPGroup'.map ι
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hW.toSylow hWi) P
  let c : X →* X := (MulAut.conj g⁻¹).toMonoidHom
  have hc : Injective c := (MulAut.conj g⁻¹).injective
  let R' : Subgroup X := R.map c
  have hR'W : R' ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ (P : Subgroup X) := hRP hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
    obtain ⟨w, hw, hwx⟩ := hxP
    rw [← hwx]
    have : c (MulAut.conj g • w) = w := by
      show (MulAut.conj g⁻¹) ((MulAut.conj g) w) = w
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [this]
    exact hw
  let e₁ : ↥R ≃* ↥R' := R.equivMapOfInjective c hc
  let e₂ : ↥(P₀ : Subgroup ↥Q) ≃* ↥R := (P₀ : Subgroup ↥Q).equivMapOfInjective ι hι
  let ψ₀ : ↥(P₀ : Subgroup ↥Q) →* ↥E := φQ.comp (P₀ : Subgroup ↥Q).subtype
  have hψ₀ : Surjective ψ₀ := fun e => by
    have he : e ∈ (P₀ : Subgroup ↥Q).map φQ := by rw [hPE]; exact Subgroup.mem_top e
    obtain ⟨x, hx, rfl⟩ := he
    exact ⟨⟨x, hx⟩, rfl⟩
  let ψ : ↥R' →* ↥E := (ψ₀.comp e₂.symm.toMonoidHom).comp e₁.symm.toMonoidHom
  have hψ : Surjective ψ := hψ₀.comp (e₂.symm.surjective.comp e₁.symm.surjective)
  let A : Subgroup ↥R' := D.subgroupOf R'
  have hAi : A.index ≤ 2 := by
    have h0 : D.relIndex W ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Subgroup.relIndex_le_of_le_right hR'W h0).trans hDi
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hDc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hA4 : Nat.card (sqHom A hAc).ker ≤ 4 := by
    let f : ↥(sqHom A hAc).ker → {x : ↥D // x ^ 2 = 1} := fun k =>
      ⟨⟨(((k : ↥A) : ↥R') : X), Subgroup.mem_subgroupOf.mp (k : ↥A).2⟩, by
        have hk : (k : ↥A) ^ 2 = 1 := k.2
        exact Subtype.ext (by
          have := congrArg (fun a : ↥A => (((a : ↥R') : X))) hk
          simpa using this)⟩
    have hf : Injective f := fun k k' h => by
      have := congrArg (fun x : {x : ↥D // x ^ 2 = 1} => ((x : ↥D) : X)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    exact (Nat.card_le_card_of_injective f hf).trans hD4
  have hE2' : ∀ e : ↥E, e ^ 2 = 1 := fun e => Subtype.ext (by simpa using hE2 e e.2)
  exact not_surj_elem A hAi hAc hA4 hE2' card_e16Sub hψ

theorem not_secOnto_sl3 {L : Type} [Field L] [Fintype L] [DecidableEq L]
    (hL : 4 ∣ Fintype.card L - 1) : ¬ SecOnto SL(3, L) (NativeSporadic.Carrier .M22) := by
  obtain ⟨W, D, hW, hWi, hDi, hDc, hD4⟩ := sl3_sylow_data hL
  exact not_secOnto_of_sylow hW hWi hDi hDc hD4

theorem not_secOnto_of_det {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (H : Subgroup (GL (Fin n) K))
    (hH : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) K).det = 1) :
    ¬ SecOnto ↥H (NativeSporadic.Carrier .M22) := fun h => by
  obtain ⟨L, _, _, _, f, hL⟩ := exists_ext_four_dvd hK
  rcases hn with rfl | rfl
  · exact not_secOnto_sl3 hL (h.of_injective
      (blockHom.comp ((Matrix.SpecialLinearGroup.map f).comp (toSL H hH)))
      (blockHom_injective.comp ((slMap_injective f).comp (toSL_injective H hH))))
  · exact not_secOnto_sl3 hL (h.of_injective ((Matrix.SpecialLinearGroup.map f).comp (toSL H hH))
      ((slMap_injective f).comp (toSL_injective H hH)))

theorem not_secOnto_of_det_quot {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (H : Subgroup (GL (Fin n) K))
    (hH : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) K).det = 1) (N : Subgroup ↥H) [N.Normal] :
    ¬ SecOnto (↥H ⧸ N) (NativeSporadic.Carrier .M22) := fun h =>
  not_secOnto_of_det hK hn H hH (SecOnto.of_quot h)

end CFSG.Quasithin.KGC31.NoM22

end
