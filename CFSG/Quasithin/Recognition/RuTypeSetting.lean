module

public import CFSG.Quasithin.Recognition.RuTypeSL3

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

abbrev ruS (L : Subgroup G) : Subgroup G := pCoreOf 2 L

abbrev ruV (L : Subgroup G) : Subgroup G := centerOf (ruS L)

abbrev ruZ (T : Sylow 2 G) : Subgroup G := centerOf (T : Subgroup G)

abbrev ruH (T : Sylow 2 G) : Subgroup G := Subgroup.centralizer (ruZ T : Set G)

abbrev ruQ (T : Sylow 2 G) : Subgroup G := pCoreOf 2 (ruH T)

abbrev ruU (L : Subgroup G) (T : Sylow 2 G) : Subgroup G := conjClosure (ruV L) (ruH T)

structure RuData (G : Type*) [Group G] where
  L : Subgroup G
  T : Sylow 2 G
  one : RuOne L
  two : RuTwo L T
  θ : L →* SL(3, ZMod 2)
  θ_surj : Function.Surjective θ
  θ_ker : θ.ker = (ruS L).subgroupOf L
  ψV : ruV L ≃* Multiplicative (Fin 3 → ZMod 2)
  ψV_equiv : ∀ (l : L) (v w : ruV L), (w : G) = l * v * (l : G)⁻¹ →
    ψV w = Multiplicative.ofAdd (natAct3 (θ l) (Multiplicative.toAdd (ψV v)))
  χ : ruS L →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))
  χ_ker : χ.ker = (ruV L).subgroupOf (ruS L)
  χ_trace : ∀ s, IsTraceZero (Multiplicative.toAdd (χ s))
  χ_surj : ∀ A, IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A
  χ_equiv : ∀ (l : L) (s t : ruS L), (t : G) = l * s * (l : G)⁻¹ →
    χ t = Multiplicative.ofAdd (stAct (θ l) (Multiplicative.toAdd (χ s)))
  σ5 : ruH T →* Equiv.Perm (Fin 5)
  σ5_surj : Function.Surjective σ5
  σ5_ker : σ5.ker = (ruQ T).subgroupOf (ruH T)
  φ : ruH T →* SigmaL2F4
  φ_surj : Function.Surjective φ
  φ_ker : φ.ker = (ruQ T).subgroupOf (ruH T)
  ψU : ruU L T →* Multiplicative (Fin 2 → F4)
  ψU_surj : Function.Surjective ψU
  ψU_ker : ψU.ker = (ruZ T).subgroupOf (ruU L T)
  ψU_equiv : ∀ (h : ruH T) (u u' : ruU L T), (u' : G) = h * u * (h : G)⁻¹ →
    ψU u' = Multiplicative.ofAdd (sigmaAct (φ h) (Multiplicative.toAdd (ψU u)))

theorem nonempty_ruData {G : Type*} [Group G] (h : IsTypeRu G) : Nonempty (RuData G) := by
  obtain ⟨L, h1, T, h2⟩ := h
  obtain ⟨θ, hθs, hθk, ⟨ψV, hψV⟩, ⟨χ, hχk, hχt, hχs, hχe⟩⟩ := h1.modules
  obtain ⟨σ5, hσs, hσk⟩ := h2.symmetric
  obtain ⟨φ, ψU, hφs, hφk, hψs, hψk, hψe⟩ := h2.natural
  exact ⟨⟨L, T, h1, h2, θ, hθs, hθk, ψV, hψV, χ, hχk, hχt, hχs, hχe, σ5, hσs, hσk, φ, hφs, hφk,
    ψU, hψs, hψk, hψe⟩⟩

theorem card_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

namespace RuData

variable (R : RuData G)

theorem card_SL3 : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem card_F4sq : Nat.card (Multiplicative (Fin 2 → F4)) = 16 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_traceZero :
    Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsTraceZero A} = 256 := by
  let f : Matrix (Fin 3) (Fin 3) (ZMod 2) →+ ZMod 2 := Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)
  have hf : Function.Surjective f := fun c =>
    ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by
      simp [f, Matrix.trace]⟩
  have h := AddSubgroup.card_ker_mul_card_of_surjective hf
  have hM : Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 512 := by
    rw [Nat.card_eq_fintype_card]
    show Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 512
    rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hk : Nat.card f.ker = Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsTraceZero A} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun A => by
      simp [f, IsTraceZero, AddMonoidHom.mem_ker])
  rw [h2, hM, hk] at h
  omega

theorem card_V : Nat.card (ruV R.L) = 8 := by
  rw [Nat.card_congr R.ψV.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem card_S : Nat.card (ruS R.L) = 2 ^ 11 := by
  have hker := Subgroup.card_ker_mul_card_range R.χ
  have hrange : Nat.card R.χ.range = 256 := by
    rw [← card_traceZero]
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative _), by
            obtain ⟨s, hs⟩ := x.2
            rw [← hs]
            exact R.χ_trace s⟩
        invFun := fun A => ⟨Multiplicative.ofAdd A.1, by
            obtain ⟨s, hs⟩ := R.χ_surj A.1 A.2
            exact ⟨s, hs⟩⟩
        left_inv := fun x => rfl
        right_inv := fun A => rfl }
  rw [hrange, R.χ_ker] at hker
  have hV : Nat.card ((ruV R.L).subgroupOf (ruS R.L)) = 8 := by
    rw [card_subgroupOf_of_le (show ruV R.L ≤ ruS R.L from inf_le_left), R.card_V]
  rw [hV] at hker
  omega

theorem card_L : Nat.card R.L = 2 ^ 11 * 168 := by
  have h := Subgroup.card_ker_mul_card_of_surjective R.θ_surj
  rw [R.θ_ker, card_SL3, card_subgroupOf_of_le (pCoreOf_le 2 R.L), R.card_S] at h
  omega

theorem S_le_L : ruS R.L ≤ R.L := pCoreOf_le 2 R.L

theorem V_le_S : ruV R.L ≤ ruS R.L := inf_le_left

theorem V_le_L : ruV R.L ≤ R.L := R.V_le_S.trans R.S_le_L

theorem Z_le_T : ruZ R.T ≤ (R.T : Subgroup G) := inf_le_left

theorem mem_V_iff {v : G} : v ∈ ruV R.L ↔ v ∈ ruS R.L ∧ ∀ s ∈ ruS R.L, s * v = v * s := by
  unfold ruV centerOf
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem mem_Z_iff {z : G} : z ∈ ruZ R.T ↔ z ∈ (R.T : Subgroup G) ∧ ∀ t ∈ (R.T : Subgroup G),
    t * z = z * t := by
  unfold ruZ centerOf
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem mem_H_iff {h : G} : h ∈ ruH R.T ↔ ∀ z ∈ ruZ R.T, z * h = h * z := by
  unfold ruH
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem T_le_H : (R.T : Subgroup G) ≤ ruH R.T := fun t ht =>
  R.mem_H_iff.mpr fun _ hz => ((R.mem_Z_iff.mp hz).2 t ht).symm

theorem mem_S_of_centralizes {l : G} (hl : l ∈ R.L) (hc : ∀ v ∈ ruV R.L, l * v = v * l) :
    l ∈ ruS R.L := by
  have h1 : R.θ ⟨l, hl⟩ = 1 := by
    apply SL3.eq_one_of_fix_all
    intro x
    have := R.ψV_equiv ⟨l, hl⟩ (R.ψV.symm (Multiplicative.ofAdd x))
      (R.ψV.symm (Multiplicative.ofAdd x)) (by
        have e := hc _ (R.ψV.symm (Multiplicative.ofAdd x)).2
        simp only
        rw [e, mul_inv_cancel_right])
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
    exact (congrArg Multiplicative.toAdd this).symm
  have : (⟨l, hl⟩ : R.L) ∈ R.θ.ker := h1
  rwa [R.θ_ker, Subgroup.mem_subgroupOf] at this

abbrev TL : Subgroup G := (R.T : Subgroup G) ⊓ R.L

theorem TL_isPGroup : IsPGroup 2 R.TL := R.T.isPGroup'.to_le inf_le_left

variable [Finite G]

theorem two_pow_eq_of_mul_odd {k a m b : ℕ} (hm : ¬ 2 ∣ m) (hb : ¬ 2 ∣ b)
    (h : m * 2 ^ k = b * 2 ^ a) : k = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero 2)
  have e := congrArg (padicValNat 2) h
  rw [padicValNat.mul hm0 (by positivity), padicValNat.mul hb0 (by positivity),
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm,
    padicValNat.eq_zero_of_not_dvd hb] at e
  omega

theorem card_TL : Nat.card R.TL = 2 ^ 14 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := R.TL_isPGroup.exists_card_eq
  have h := Subgroup.relIndex_mul_card R.TL R.L
  rw [inf_eq_left.mpr (inf_le_right : R.TL ≤ R.L), R.card_L, hk] at h
  have hk14 : k = 14 :=
    two_pow_eq_of_mul_odd (m := R.TL.relIndex R.L) (b := 21) R.two.sylow_inf (by norm_num)
      (by rw [h]; norm_num)
  rw [hk, hk14]

@[expose] noncomputable def sylowTL : Sylow 2 R.L :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow (P := R.TL.subgroupOf R.L)
    (R.TL_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm)
    R.two.sylow_inf

theorem S_le_TL : ruS R.L ≤ R.TL := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 R.L).Normal := pCore_normal 2
  have hle : pCore 2 R.L ≤ (R.sylowTL : Subgroup R.L) :=
    (pCore_isPGroup (G := R.L) 2).le_sylow_of_normal R.sylowTL
  have h := Subgroup.map_mono (f := R.L.subtype) hle
  have e : ((R.sylowTL : Subgroup R.L)).map R.L.subtype = R.TL :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  rw [e] at h
  exact h

theorem S_le_T : ruS R.L ≤ (R.T : Subgroup G) := R.S_le_TL.trans inf_le_left

omit [Finite G] in
theorem Z_centralizes_V {z v : G} (hz : z ∈ ruZ R.T) (hv : v ∈ ruV R.L) : z * v = v * z :=
  (Subgroup.mem_centralizer_iff.mp (R.two.V_le_H hv) z hz)

omit [Finite G] in
theorem Z_le_L : ruZ R.T ≤ R.L := by
  intro z hz
  rw [R.one.eq_normalizer, Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    rw [R.Z_centralizes_V hz hv, mul_inv_cancel_right]
    exact hv
  · intro hw
    have e := R.Z_centralizes_V hz hw
    have : v = z * v * z⁻¹ := by
      calc v = z⁻¹ * (z * v * z⁻¹) * z := by group
        _ = z⁻¹ * (z * (z * v * z⁻¹)) := by rw [mul_assoc, ← e]
        _ = z * v * z⁻¹ := by group
    rw [this]
    exact hw

omit [Finite G] in
theorem Z_le_S : ruZ R.T ≤ ruS R.L := fun _ hz =>
  R.mem_S_of_centralizes (R.Z_le_L hz) fun _ hv => R.Z_centralizes_V hz hv

theorem Z_le_V : ruZ R.T ≤ ruV R.L := fun _ hz =>
  R.mem_V_iff.mpr ⟨R.Z_le_S hz, fun s hs => (R.mem_Z_iff.mp hz).2 s (R.S_le_T hs)⟩

abbrev CVTL : Subgroup G := ruV R.L ⊓ Subgroup.centralizer (R.TL : Set G)

theorem card_θTL : Nat.card ((R.TL.subgroupOf R.L).map R.θ) = 8 := by
  have h1 := Subgroup.relIndex_ker (K := R.TL.subgroupOf R.L) R.θ
  have h2 := Subgroup.relIndex_mul_card R.θ.ker (R.TL.subgroupOf R.L)
  have hker : R.θ.ker ≤ R.TL.subgroupOf R.L := by
    rw [R.θ_ker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact R.S_le_TL hx
  rw [inf_eq_left.mpr hker, h1, R.θ_ker, card_subgroupOf_of_le inf_le_right, R.card_TL,
    card_subgroupOf_of_le R.S_le_L, R.card_S] at h2
  omega

omit [Finite G] in
theorem conj_mem_V {t v : G} (ht : t ∈ R.L) (hv : v ∈ ruV R.L) : t * v * t⁻¹ ∈ ruV R.L := by
  have htn : t ∈ Subgroup.normalizer (ruV R.L : Set G) := R.one.eq_normalizer ▸ ht
  exact (Subgroup.mem_normalizer_iff.mp htn v).mp hv

omit [Finite G] in
theorem conj_eq_iff (t : R.L) (v : ruV R.L) :
    (t : G) * v * (t : G)⁻¹ = v ↔
      natAct3 (R.θ t) (Multiplicative.toAdd (R.ψV v)) = Multiplicative.toAdd (R.ψV v) := by
  have hmem := R.conj_mem_V t.2 v.2
  have e := R.ψV_equiv t v ⟨_, hmem⟩ rfl
  constructor
  · intro h
    have hw : (⟨_, hmem⟩ : ruV R.L) = v := Subtype.ext h
    rw [hw] at e
    exact (congrArg Multiplicative.toAdd e).symm
  · intro h
    rw [h] at e
    exact congrArg Subtype.val (R.ψV.injective e)

theorem card_CVTL : Nat.card R.CVTL = 2 := by
  rw [← SL3.card_fix_of_card_eq_eight R.card_θTL]
  have key : ∀ v : ruV R.L, (v : G) ∈ R.CVTL ↔
      ∀ g ∈ (R.TL.subgroupOf R.L).map R.θ,
        natAct3 g (Multiplicative.toAdd (R.ψV v)) = Multiplicative.toAdd (R.ψV v) := by
    intro v
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [v.2, true_and, SetLike.mem_coe]
    constructor
    · rintro h _ ⟨⟨t, htL⟩, ht, rfl⟩
      have ht' : t ∈ R.TL := Subgroup.mem_subgroupOf.mp ht
      refine (R.conj_eq_iff ⟨t, htL⟩ v).mp ?_
      simp only
      rw [h t ht', mul_inv_cancel_right]
    · intro h t ht
      have := (R.conj_eq_iff ⟨t, (Subgroup.mem_inf.mp ht).2⟩ v).mpr
        (h _ ⟨⟨t, (Subgroup.mem_inf.mp ht).2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
      calc t * (v : G) = t * v * t⁻¹ * t := by group
        _ = v * t := by rw [this]
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (R.ψV ⟨x, (Subgroup.mem_inf.mp x.2).1⟩),
        (key _).mp x.2⟩
      invFun := fun w => ⟨R.ψV.symm (Multiplicative.ofAdd w.1),
        (key _).mpr (by simpa using w.2)⟩
      left_inv := fun x => by simp
      right_inv := fun w => by simp }

theorem Z_le_CVTL : ruZ R.T ≤ R.CVTL := fun _ hz =>
  ⟨R.Z_le_V hz, Subgroup.mem_centralizer_iff.mpr fun t ht => (R.mem_Z_iff.mp hz).2 t ht.1⟩

theorem one_lt_card_Z : 1 < Nat.card (ruZ R.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Nontrivial (R.T : Subgroup G) := by
    have h : 1 < Nat.card (R.T : Subgroup G) := by
      have := Subgroup.card_le_of_le (inf_le_left : R.TL ≤ (R.T : Subgroup G))
      rw [R.card_TL] at this
      omega
    exact Finite.one_lt_card_iff_nontrivial.mp h
  have := (R.T.isPGroup').center_nontrivial
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : Subgroup.center (R.T : Subgroup G))
  have hcmem : (c : G) ∈ ruZ R.T := R.mem_Z_iff.mpr ⟨c.2, fun t ht => by
    have := Subgroup.mem_center_iff.mp hc ⟨t, ht⟩
    simpa using congrArg Subtype.val this⟩
  have hne : (⟨c, hcmem⟩ : ruZ R.T) ≠ 1 := by
    intro h
    apply hc1
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne⟩⟩

theorem card_Z : Nat.card (ruZ R.T) = 2 := by
  have h := Subgroup.card_le_of_le R.Z_le_CVTL
  rw [R.card_CVTL] at h
  have := R.one_lt_card_Z
  omega

theorem Z_eq_CVTL : ruZ R.T = R.CVTL :=
  Subgroup.eq_of_le_of_card_ge R.Z_le_CVTL (by rw [R.card_CVTL, R.card_Z])

theorem card_U : Nat.card (ruU R.L R.T) = 32 := by
  have h := Subgroup.card_ker_mul_card_of_surjective R.ψU_surj
  rw [R.ψU_ker, card_subgroupOf_of_le R.two.Z_le_U, R.card_Z, card_F4sq] at h
  omega

theorem card_Q : Nat.card (ruQ R.T) = 2 ^ 11 := by
  have h := Subgroup.relIndex_mul_card (ruU R.L R.T) (ruQ R.T)
  rw [inf_eq_left.mpr R.two.U_le_Q, R.two.QU_card, R.card_U] at h
  omega

theorem card_H : Nat.card (ruH R.T) = 2 ^ 11 * 120 := by
  have h := Subgroup.card_ker_mul_card_of_surjective R.σ5_surj
  rw [R.σ5_ker, card_subgroupOf_of_le (pCoreOf_le 2 _), R.card_Q] at h
  rw [← h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem T_le_L : (R.T : Subgroup G) ≤ R.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := R.T.isPGroup'.exists_card_eq
  have hdvd : Nat.card (R.T : Subgroup G) ∣ Nat.card (ruH R.T) := Subgroup.card_dvd_of_le R.T_le_H
  rw [hk, R.card_H] at hdvd
  have hk14 : k ≤ 14 := by
    have : 2 ^ k ∣ 2 ^ 14 := by
      have hc : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left _ (by norm_num)
      exact hc.dvd_of_dvd_mul_right
        (by rw [show 2 ^ 14 * 15 = 2 ^ 11 * 120 by norm_num]; exact hdvd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hle : Nat.card (R.T : Subgroup G) ≤ Nat.card R.TL := by
    rw [hk, R.card_TL]
    exact Nat.pow_le_pow_right (by norm_num) hk14
  have heq : R.TL = (R.T : Subgroup G) := Subgroup.eq_of_le_of_card_ge inf_le_left hle
  rw [← heq]
  exact inf_le_right

theorem TL_eq : R.TL = (R.T : Subgroup G) := inf_eq_left.mpr R.T_le_L

theorem Z_eq : ruZ R.T = ruV R.L ⊓ Subgroup.centralizer ((R.T : Subgroup G) : Set G) := by
  rw [R.Z_eq_CVTL, CVTL, R.TL_eq]

end RuData

end CFSG.Quasithin.RuType
