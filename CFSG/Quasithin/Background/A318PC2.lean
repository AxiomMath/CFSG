module

public import CFSG.Quasithin.Background.A318PC1
public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars StatedProj)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Lifts

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : L ≃* slPi π 3 (p ^ f) K}

theorem isPGLAt_inv {g : G} {y : GL (Fin 3) K} (hy : IsPGLAt e g y) : IsPGLAt e g⁻¹ y⁻¹ := by
  refine ⟨inv_mem hy.1, fun s => ?_⟩
  set t := slAct e ⟨g⁻¹, mem_normalizer_of_normal g⁻¹⟩ s with ht
  have h1 : slAct e ⟨g, mem_normalizer_of_normal g⟩ t = s := by
    have : (⟨g⁻¹, mem_normalizer_of_normal g⁻¹⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨g, mem_normalizer_of_normal g⟩)⁻¹ := rfl
    rw [ht, this, map_inv, MulAut.apply_inv_self]
  have h2 := hy.2 t
  rw [h1] at h2
  calc (t : GL (Fin 3) K) = y⁻¹ * (y * t * y⁻¹) * y := by group
    _ = y⁻¹ * s * y := by rw [← h2]
    _ = y⁻¹ * s * y⁻¹⁻¹ := by rw [inv_inv]

variable (e) in
@[expose] def pglSubgroup : Subgroup G where
  carrier := {g | ∃ y, IsPGLAt e g y}
  mul_mem' := fun ⟨y, hy⟩ ⟨z, hz⟩ => ⟨y * z, isPGLAt_mul e hy hz⟩
  one_mem' := ⟨1, isPGLAt_of_mem_centralizer e (Subgroup.one_mem _)⟩
  inv_mem' := fun ⟨y, hy⟩ => ⟨y⁻¹, isPGLAt_inv hy⟩

end Lifts

section Cent

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K] {p f : ℕ}
  {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

theorem mem_centralizer_iff_of_isPGLAt {x : X} {y : GL (Fin 3) K} (hxy : IsPGLAt e x y)
    (t : ↥S) :
    (t : X) ∈ Subgroup.centralizer ({x} : Set X) ↔
      ((e t : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈
        Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have h1 : (t : X) * x = x * t ↔ x * (t : X) * x⁻¹ = t := by
    constructor
    · intro h
      calc x * (t : X) * x⁻¹ = (t : X) * x * x⁻¹ := by rw [← h]
        _ = t := by group
    · intro h
      calc (t : X) * x = x * (t : X) * x⁻¹ * x := by rw [h]
        _ = x * t := by group
  have h2 : (e t : GL (Fin 3) K) * y = y * (e t : GL (Fin 3) K) ↔
      y * (e t : GL (Fin 3) K) * y⁻¹ = (e t : GL (Fin 3) K) := by
    constructor
    · intro h
      calc y * (e t : GL (Fin 3) K) * y⁻¹ = (e t : GL (Fin 3) K) * y * y⁻¹ := by rw [← h]
        _ = e t := by group
    · intro h
      calc (e t : GL (Fin 3) K) * y = y * (e t : GL (Fin 3) K) * y⁻¹ * y := by rw [h]
        _ = y * (e t : GL (Fin 3) K) := by group
  rw [h1, h2]
  have h3 : slAct e ⟨x, mem_normalizer_of_normal x⟩ (e t) = e t ↔
      x * (t : X) * x⁻¹ = t := by
    constructor
    · intro h
      have := conj_eq_of_slAct_eq e x (e t) h
      simpa using this
    · intro h
      rw [slAct_apply, MulEquiv.symm_apply_apply]
      congr 1
      exact Subtype.ext h
  have h4 : slAct e ⟨x, mem_normalizer_of_normal x⟩ (e t) = e t ↔
      y * (e t : GL (Fin 3) K) * y⁻¹ = (e t : GL (Fin 3) K) := by
    constructor
    · intro h
      have := hxy.2 (e t)
      rw [h] at this
      exact this.symm
    · intro h
      apply Subtype.ext
      rw [hxy.2 (e t), h]
  rw [← h3, ← h4]

@[expose] noncomputable def centEquiv {x : X} {y : GL (Fin 3) K} (hxy : IsPGLAt e x y) :
    ↥(S ⊓ Subgroup.centralizer ({x} : Set X)) ≃*
      ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) := by
  have hmap : ((S ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf S).map e.toMonoidHom =
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))).subgroupOf
        (slPi π 3 (p ^ f) K) := by
    ext s
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_iff_of_isPGLAt hxy,
      MulEquiv.apply_symm_apply]
    exact ⟨fun h => ⟨s.2, h.2⟩, fun h => ⟨(e.symm s).2, h.2⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ Subgroup.centralizer ({x} : Set X) ≤ S)).symm.trans
    ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hmap).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : slPi π 3 (p ^ f) K ⊓
          Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) ≤ slPi π 3 (p ^ f) K))))

end Cent

section Arith

variable {π : Bool}

theorem qSubPi_cube_div {q : ℕ} (hq : ModThree π q) (h0 : qSubPi π q ≠ 0) :
    qSubPi π (q ^ 3) / qSubPi π q = if π = true then q ^ 2 + q + 1 else q ^ 2 - q + 1 := by
  rw [qSubPi_cube_eq hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h0)]
  cases π
  · change q % 3 = 2 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    have ht : (3 * t + 2) / 3 = t := by omega
    have hsq : (3 * t + 2) ^ 2 = 9 * t ^ 2 + 12 * t + 4 := by ring
    rw [ht]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · change q % 3 = 1 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
    have ht : (3 * t + 1) / 3 = t := by omega
    have hsq : (3 * t + 1) ^ 2 = 9 * t ^ 2 + 6 * t + 1 := by ring
    rw [ht]
    simp only [↓reduceIte]
    omega

end Arith

section Decomp

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_eq_one_of_units {g : GL (Fin 3) K} (hg : GeneralLinearGroup.det g = 1) :
    (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have := congrArg Units.val hg
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem exists_decomp_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z)
    {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    ∃ k : ℕ, k < 3 ∧ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, h = l * y ^ k * z := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  have hN0 : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  set T := rootsOfUnity (qSubPi π (p ^ f)) K with hT
  have hTcyc : IsCyclic T := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  set d : T := ⟨GeneralLinearGroup.det y, det_mem_rootsOfUnity hK hyH⟩ with hd
  set dh : T := ⟨GeneralLinearGroup.det h, det_mem_rootsOfUnity hK hh⟩ with hdh
  have hzH : ∀ c : T, GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) ∈ glPi π 3 (p ^ f) K := fun c =>
    (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ scalar_mem_zPi hK hq hτ hτ1 c.2)).1
  have hdnc : ¬ ∃ c : T, c ^ 3 = d := by
    rintro ⟨c, hc⟩
    apply hnon
    refine ⟨y * (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹, ?_,
      GeneralLinearGroup.scalar (Fin 3) (c : Kˣ), scalar_mem_zPi hK hq hτ hτ1 c.2, by group⟩
    rw [mem_slPi_iff hπ]
    refine ⟨mul_mem hyH (inv_mem (hzH c)), det_eq_one_of_units ?_⟩
    have hc' : (c : Kˣ) ^ 3 = GeneralLinearGroup.det y := congrArg (fun t : T => (t : Kˣ)) hc
    rw [map_mul, map_inv, det_scalar_three, hc', mul_inv_cancel]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := T)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hγ d)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (hγ dh)
  have ha3 : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨a', rfl⟩
    refine hdnc ⟨γ ^ a', ?_⟩
    rw [← ha, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  obtain ⟨k, hk, j, hj⟩ : ∃ k : ℕ, k < 3 ∧ ∃ j : ℤ, b - a * k = 3 * j := by
    have h3 : (3 : ℤ) ∣ b ∨ (3 : ℤ) ∣ b - a ∨ (3 : ℤ) ∣ b - 2 * a := by
      have ha' : a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hb' : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' | hb' <;> omega
    rcases h3 with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨0, by norm_num, j, by simpa using hj⟩
    · exact ⟨1, by norm_num, j, by simpa using hj⟩
    · exact ⟨2, by norm_num, j, by push_cast; linarith⟩
  have hdh_eq : dh = d ^ k * (γ ^ j) ^ 3 := by
    rw [← hb, ← ha, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 1
    push_cast
    linarith
  set c : T := γ ^ j with hc
  have hdetl : GeneralLinearGroup.det (h * (y ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹) = 1 := by
    have h1 : (GeneralLinearGroup.det h) = GeneralLinearGroup.det y ^ k * (c : Kˣ) ^ 3 :=
      congrArg (fun t : T => (t : Kˣ)) hdh_eq
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, det_scalar_three, h1, mul_inv_cancel_comm,
      mul_inv_cancel]
  have hlH : h * (y ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹ ∈
      glPi π 3 (p ^ f) K :=
    mul_mem (mul_mem hh (inv_mem (pow_mem hyH k))) (inv_mem (hzH c))
  have hzZ := scalar_mem_zPi hK hq hτ hτ1 c.2
  have hzs : GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) ∈ StatedScalars (Fin 3) K :=
    ⟨c, rfl⟩
  refine ⟨k, hk, _, (mem_slPi_iff hπ).2 ⟨hlH, det_eq_one_of_units hdetl⟩,
    GeneralLinearGroup.scalar (Fin 3) (c : Kˣ), hzZ, ?_⟩
  have hcomm := commute_of_mem_statedScalars hzs (y ^ k)
  calc h = h * (y ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹ * (
        GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) * y ^ k) := by group
    _ = h * (y ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹ * (
        y ^ k * GeneralLinearGroup.scalar (Fin 3) (c : Kˣ)) := by rw [hcomm]
    _ = _ := by group

end Decomp

section Group

@[expose] noncomputable def statedProjEquivMapMk' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) :
    StatedProj H ≃* H.map (QuotientGroup.mk' (StatedScalars ι K)) := by
  let φ : H →* GL ι K ⧸ StatedScalars ι K := (QuotientGroup.mk' (StatedScalars ι K)).comp H.subtype
  have hker : φ.ker = (StatedScalars ι K).subgroupOf H := by
    ext h
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : φ.range = H.map (QuotientGroup.mk' (StatedScalars ι K)) := by
    simp [φ, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal]

theorem normal_map_center : ((Subgroup.center ↥S).map S.subtype).Normal := by
  constructor
  rintro _ ⟨z, hz, rfl⟩ g
  have hgz : g * (z : X) * g⁻¹ ∈ S := hSn.conj_mem _ z.2 g
  refine ⟨⟨g * (z : X) * g⁻¹, hgz⟩, ?_, rfl⟩
  have hz' : z ∈ Subgroup.center ↥S := hz
  rw [Subgroup.mem_center_iff] at hz'
  show _ ∈ Subgroup.center ↥S
  rw [Subgroup.mem_center_iff]
  intro s
  have hs : g⁻¹ * (s : X) * g ∈ S := by simpa using hSn.conj_mem _ s.2 g⁻¹
  have h1 := congrArg Subtype.val (hz' ⟨g⁻¹ * (s : X) * g, hs⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul] at h1 ⊢
  calc (s : X) * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * s := by group

theorem mem_sup_zpowers_cube [Finite X] {x : X} (hx : orderOf x = 3) {a : X}
    (ha : a ∈ S ⊔ Subgroup.zpowers x) : ∃ l ∈ S, ∃ n : ℕ, n < 3 ∧ a = l * x ^ n := by
  obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hu)
  refine ⟨l, hl, n % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  have := pow_mod_orderOf x n
  rw [hx] at this
  rw [this]

variable {K : Type} [Field K] {p f : ℕ} {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

theorem mem_of_mem_sup_of_centralizes [Finite X] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : X} (hx : orderOf x = 3) {y : GL (Fin 3) K} (hxy : IsPGLAt e x y)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z) {a : X}
    (ha : a ∈ S ⊔ Subgroup.zpowers x) (hc : a ∈ Subgroup.centralizer (S : Set X)) : a ∈ S := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨l, hl, n, hn, rfl⟩ := mem_sup_zpowers_cube hx ha
  have h1 : IsPGLAt e (l * x ^ n) ((e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ n) :=
    isPGLAt_mul e (isPGLAt_of_mem e hπ hl) (isPGLAt_pow hxy n)
  have h2 : IsPGLAt e (l * x ^ n) 1 := isPGLAt_of_mem_centralizer e hc
  have h3 := isPGLAt_inv_mul_mem hK hq h1 h2
  have hzs : (e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ n ∈ StatedScalars (Fin 3) K := by
    have := inv_mem h3
    simpa using this
  have hzH : (e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ n ∈ glPi π 3 (p ^ f) K :=
    mul_mem (slPi_le_glPi hπ (e ⟨l, hl⟩).2) (pow_mem hxy.1 n)
  have hzZ : (e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ n ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.2 ⟨hzH, hzs⟩
  have hE : (e ⟨l, hl⟩ : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := (e ⟨l, hl⟩).2
  interval_cases n
  · simpa using hl
  · exfalso
    exact hnon ⟨(e ⟨l, hl⟩ : GL (Fin 3) K)⁻¹, inv_mem hE, _, hzZ, by group⟩
  · exfalso
    have hzc := commute_of_mem_statedScalars hzs (e ⟨l, hl⟩ : GL (Fin 3) K)⁻¹
    refine hnon ⟨(e ⟨l, hl⟩ : GL (Fin 3) K)⁻¹ ^ 2, pow_mem (inv_mem hE) 2,
      ((e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ 2) ^ 2 * (y ^ 3)⁻¹,
      mul_mem (pow_mem hzZ 2) (inv_mem hy3), ?_⟩
    have hy2 : y ^ 2 = (e ⟨l, hl⟩ : GL (Fin 3) K)⁻¹ * ((e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ 2) := by
      group
    calc y = (y ^ 2) ^ 2 * (y ^ 3)⁻¹ := by group
      _ = ((e ⟨l, hl⟩ : GL (Fin 3) K)⁻¹ * ((e ⟨l, hl⟩ : GL (Fin 3) K) * y ^ 2)) ^ 2 *
          (y ^ 3)⁻¹ := by rw [← hy2]
      _ = _ := by rw [(show Commute _ _ from hzc).mul_pow, mul_assoc]

end Group

section Assembly

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : ↥S ≃* slPi π 3 (p ^ f) K}

theorem isPGLModCenter_of_type_iii (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x : X}
    (hx : orderOf x = 3) {y : GL (Fin 3) K} (hxy : IsPGLAt e x y)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hnon : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z) :
    IsPGLModCenter π (p ^ f) S (S ⊔ Subgroup.zpowers x) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set A : Subgroup X := S ⊔ Subgroup.zpowers x with hA
  have hAle : A ≤ pglSubgroup e :=
    sup_le (fun s hs => ⟨_, isPGLAt_of_mem e hπ hs⟩) (Subgroup.zpowers_le.2 ⟨y, hxy⟩)
  have hA' : ∀ a ∈ A, ∃ y, IsPGLAt e a y := fun a ha => hAle ha
  have hnormZ : ((Subgroup.center ↥S).map S.subtype).Normal := normal_map_center
  refine ⟨Subgroup.Normal.subgroupOf hnormZ A, ?_⟩
  have hker : (pglHom hK hq A hA').ker = ((Subgroup.center ↥S).map S.subtype).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, pglHom_eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hc
      have hS' : (a : X) ∈ S := mem_of_mem_sup_of_centralizes hK hq hx hxy hy3 hnon a.2 hc
      refine ⟨⟨a, hS'⟩, Subgroup.mem_center_iff.2 fun s => ?_, rfl⟩
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) s s.2)
    · rintro ⟨z, hz, hza⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hza]
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨h, hh⟩)
  have hrange : (pglHom hK hq A hA').range =
      (glPi π 3 (p ^ f) K).map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      obtain ⟨y', hy'⟩ := hA' a a.2
      refine ⟨y', hy'.1, ?_⟩
      rw [pglHom_apply a hy']
      rfl
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨k, hk, l, hl, z, hz, rfl⟩ := exists_decomp_glPi hK hq hτ hτ1 hxy.1 hnon hh
      have hzs : z ∈ StatedScalars (Fin 3) K :=
        (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
      have hlS : ((e.symm ⟨l, hl⟩ : ↥S) : X) ∈ A := Subgroup.mem_sup_left (e.symm ⟨l, hl⟩).2
      have hxk : x ^ k ∈ A := pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) k
      have haA : ((e.symm ⟨l, hl⟩ : ↥S) : X) * x ^ k ∈ A := mul_mem hlS hxk
      have hlift : IsPGLAt e (((e.symm ⟨l, hl⟩ : ↥S) : X) * x ^ k) (l * y ^ k) := by
        have h1 := isPGLAt_mul e (isPGLAt_of_mem e hπ (e.symm ⟨l, hl⟩).2) (isPGLAt_pow hxy k)
        have h2 : (e ⟨((e.symm ⟨l, hl⟩ : ↥S) : X), (e.symm ⟨l, hl⟩).2⟩ : slPi π 3 (p ^ f) K) =
            ⟨l, hl⟩ := by
          have : (⟨((e.symm ⟨l, hl⟩ : ↥S) : X), (e.symm ⟨l, hl⟩).2⟩ : ↥S) = e.symm ⟨l, hl⟩ := rfl
          rw [this, MulEquiv.apply_symm_apply]
        rw [h2] at h1
        exact h1
      refine ⟨⟨_, haA⟩, ?_⟩
      rw [pglHom_apply ⟨_, haA⟩ hlift]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      have hz1 : (l * y ^ k)⁻¹ * (l * y ^ k * z) = z := by group
      rw [hz1]
      exact hzs
  have hiso : Nonempty (↥A ⧸ ((Subgroup.center ↥S).map S.subtype).subgroupOf A ≃*
      StatedProj (glPi π 3 (p ^ f) K)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (pglHom hK hq A hA')).trans
        ((MulEquiv.subgroupCongr hrange).trans (statedProjEquivMapMk' _).symm))⟩
  have := hK.finite
  cases π
  · exact ⟨K, inferInstance, hK.finite, hK.card, hiso⟩
  · exact ⟨K, inferInstance, hK.finite, hK.card, hiso⟩

end Assembly

end A318P

end CFSG.Quasithin
