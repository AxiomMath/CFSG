module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

section Comm

variable {G : Type*} [Group G]

theorem inv_commutator_of_central {u v : G} (hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center G) :
    u⁻¹ * v * u * v⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
  have e := Subgroup.mem_center_iff.mp hc u⁻¹
  refine eq_inv_of_mul_eq_one_right ?_
  calc (u * v * u⁻¹ * v⁻¹) * (u⁻¹ * v * u * v⁻¹)
      = ((u * v * u⁻¹ * v⁻¹) * u⁻¹) * (v * u * v⁻¹) := by group
    _ = (u⁻¹ * (u * v * u⁻¹ * v⁻¹)) * (v * u * v⁻¹) := by rw [e]
    _ = 1 := by group

theorem pow_conj_eq_of_central {u v : G} (hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center G) (n : ℕ) :
    u ^ n * v * (u ^ n)⁻¹ = (u * v * u⁻¹ * v⁻¹) ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcn : (u * v * u⁻¹ * v⁻¹) ^ n ∈ Subgroup.center G := Subgroup.pow_mem _ hc n
    have e := Subgroup.mem_center_iff.mp hcn u
    calc u ^ (n + 1) * v * (u ^ (n + 1))⁻¹ = u * (u ^ n * v * (u ^ n)⁻¹) * u⁻¹ := by group
      _ = u * ((u * v * u⁻¹ * v⁻¹) ^ n * v) * u⁻¹ := by rw [ih]
      _ = (u * (u * v * u⁻¹ * v⁻¹) ^ n) * v * u⁻¹ := by group
      _ = ((u * v * u⁻¹ * v⁻¹) ^ n * u) * v * u⁻¹ := by rw [e]
      _ = (u * v * u⁻¹ * v⁻¹) ^ (n + 1) * v := by rw [pow_succ]; group

theorem conj_mul_central {z a g : G} (hz : z ∈ Subgroup.center G) :
    (z * a) * g * (z * a)⁻¹ = a * g * a⁻¹ := by
  have e := Subgroup.mem_center_iff.mp hz (a * g * a⁻¹)
  calc (z * a) * g * (z * a)⁻¹ = z * (a * g * a⁻¹) * z⁻¹ := by group
    _ = (a * g * a⁻¹) * z * z⁻¹ := by rw [← e]
    _ = a * g * a⁻¹ := by group

theorem commutator_mul_central {z₁ z₂ a b : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) :
    (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  rw [conj_mul_central h₁]
  have e := Subgroup.mem_center_iff.mp h₂ a
  have e' := Subgroup.mem_center_iff.mp h₂ (a * b * a⁻¹ * b⁻¹)
  calc a * (z₂ * b) * a⁻¹ * (z₂ * b)⁻¹ = (a * z₂) * b * a⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = (z₂ * a) * b * a⁻¹ * b⁻¹ * z₂⁻¹ := by rw [e]
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z₂ * z₂⁻¹ := by rw [← e']
    _ = a * b * a⁻¹ * b⁻¹ := by group

end Comm

section Lift

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem commute_lift_of_inverting (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ} (hp : Odd p) {x y : L'}
    (hxy : Commute (ψ x) (ψ y)) (hxp : ψ x ^ p = 1) {w : R} (hwx : w * ψ x * w⁻¹ = (ψ x)⁻¹)
    (hwy : w * ψ y * w⁻¹ = ψ y) : Commute x y := by
  obtain ⟨w', rfl⟩ := hψ w
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcker : c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hxy.eq]
    group
  have hcZ := hker hcker
  set z₁ := w' * x * w'⁻¹ * x with hz₁
  set z₂ := w' * y * w'⁻¹ * y⁻¹ with hz₂
  have h₁ : z₁ ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, hz₁, map_mul, map_mul, map_mul, map_inv, hwx, inv_mul_cancel])
  have h₂ : z₂ ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, hz₂, map_mul, map_mul, map_mul, map_inv, map_inv, hwy, mul_inv_cancel])
  have hx' : w' * x * w'⁻¹ = z₁ * x⁻¹ := by rw [hz₁]; group
  have hy' : w' * y * w'⁻¹ = z₂ * y := by rw [hz₂]; group
  have hconj : w' * c * w'⁻¹ = c⁻¹ := by
    calc w' * c * w'⁻¹ = (w' * x * w'⁻¹) * (w' * y * w'⁻¹) * (w' * x * w'⁻¹)⁻¹ *
          (w' * y * w'⁻¹)⁻¹ := by rw [hc]; group
      _ = (z₁ * x⁻¹) * (z₂ * y) * (z₁ * x⁻¹)⁻¹ * (z₂ * y)⁻¹ := by rw [hx', hy']
      _ = x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ := commutator_mul_central h₁ h₂
      _ = c⁻¹ := by rw [inv_inv]; exact inv_commutator_of_central hcZ
  have hcc : w' * c * w'⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hcZ w']
    group
  have hc2 : c ^ 2 = 1 := by
    have h := hcc.symm.trans hconj
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h
  have hxpZ : x ^ p ∈ Subgroup.center L' := hker (by rw [MonoidHom.mem_ker, map_pow, hxp])
  have hcp : c ^ p = 1 := by
    have h := pow_conj_eq_of_central hcZ p
    rw [← hc, ← Subgroup.mem_center_iff.mp hxpZ y, mul_assoc, mul_inv_cancel, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hp
    have h' : c ^ p = (c ^ 2) ^ m * c := by rw [hm, pow_succ, pow_mul]
    rw [hc2, one_pow, one_mul, hcp] at h'
    exact h'.symm
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := hc1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem exists_lift_pow_eq_one (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {p : ℕ} (hp : Odd p) {e w : R} (he : e ^ p = 1) (hw : w * e * w⁻¹ = e⁻¹)
    {A : Subgroup L'} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hkerA : ψ.ker ≤ A) {x : L'}
    (hx : ψ x = e) (hxA : x ∈ A) : ∃ t ∈ A, ψ t = e ∧ t ^ p = 1 := by
  obtain ⟨w', rfl⟩ := hψ w
  obtain ⟨m, hm⟩ := hp
  set a := x ^ (m + 1) with ha
  have haA : a ∈ A := Subgroup.pow_mem _ hxA _
  set y := w' * a⁻¹ * w'⁻¹ with hy
  have hψa : ψ a = e ^ (m + 1) := by rw [ha, map_pow, hx]
  have hψy : ψ y = e ^ (m + 1) := by
    have h1 : ψ w' * e⁻¹ * (ψ w')⁻¹ = e := by
      rw [show ψ w' * e⁻¹ * (ψ w')⁻¹ = (ψ w' * e * (ψ w')⁻¹)⁻¹ by group, hw, inv_inv]
    rw [hy, map_mul, map_mul, map_inv, map_inv, hψa, ← inv_pow, ← conj_pow, h1]
  have hyA : y ∈ A := by
    have hk : a⁻¹ * y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψa, hψy, inv_mul_cancel]
    have := Subgroup.mul_mem _ haA (hkerA hk)
    rwa [mul_inv_cancel_left] at this
  refine ⟨a * y, Subgroup.mul_mem _ haA hyA, ?_, ?_⟩
  · rw [map_mul, hψa, hψy, ← pow_add]
    have : m + 1 + (m + 1) = p + 1 := by omega
    rw [this, pow_succ, he, one_mul]
  · have hcomm : Commute a y := hA a haA y hyA
    rw [hcomm.mul_pow]
    have hapZ : a ^ p ∈ Subgroup.center L' := by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_pow, hψa, ← pow_mul, mul_comm, pow_mul, he, one_pow]
    have hyp : y ^ p = (a ^ p)⁻¹ := by
      rw [hy, conj_pow, inv_pow, Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hapZ) w']
      group
    rw [hyp, mul_inv_cancel]

end Lift

section Section

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

@[expose] def torusBasis {p k : ℕ} (τ : (Fin k → Multiplicative (ZMod p)) →* R) (i : Fin k) : R :=
  τ (Pi.mulSingle i (Multiplicative.ofAdd 1))

theorem torusBasis_pow {p k : ℕ} (τ : (Fin k → Multiplicative (ZMod p)) →* R) (i : Fin k) :
    torusBasis τ i ^ p = 1 := by
  rw [torusBasis, ← map_pow, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_self, ofAdd_zero, Pi.mulSingle_one, map_one]

theorem torusBasis_pow_val {p k : ℕ} [NeZero p] (τ : (Fin k → Multiplicative (ZMod p)) →* R)
    (i : Fin k) (a : Multiplicative (ZMod p)) :
    torusBasis τ i ^ (Multiplicative.toAdd a).val = τ (Pi.mulSingle i a) := by
  rw [torusBasis, ← map_pow, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val,
    ofAdd_toAdd]

@[expose] noncomputable def zmodPowHom {p : ℕ} {t : L'} (ht : t ^ p = 1) :
    Multiplicative (ZMod p) →* L' :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift p ⟨zmultiplesHom (Additive L') (Additive.ofMul t),
    by rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, ht, ofMul_one]⟩)

theorem zmodPowHom_natCast {p : ℕ} {t : L'} (ht : t ^ p = 1) (n : ℕ) :
    zmodPowHom ht (Multiplicative.ofAdd (n : ZMod p)) = t ^ n := by
  have hn : ((n : ℕ) : ZMod p) = ((n : ℤ) : ZMod p) := (Int.cast_natCast n).symm
  rw [zmodPowHom, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
    toAdd_ofAdd, hn, ZMod.lift_coe]
  show Additive.toMul (zmultiplesHom (Additive L') (Additive.ofMul t) (n : ℤ)) = t ^ n
  rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, toMul_ofMul]

theorem zmodPowHom_apply {p : ℕ} [NeZero p] {t : L'} (ht : t ^ p = 1)
    (a : Multiplicative (ZMod p)) : zmodPowHom ht a = t ^ (Multiplicative.toAdd a).val := by
  have := zmodPowHom_natCast ht (Multiplicative.toAdd a).val
  rwa [ZMod.natCast_zmod_val, ofAdd_toAdd] at this

theorem zmodPowHom_mem {p : ℕ} [NeZero p] {t : L'} (ht : t ^ p = 1) {H : Subgroup L'} (htH : t ∈ H)
    (a : Multiplicative (ZMod p)) : zmodPowHom ht a ∈ H := by
  rw [zmodPowHom_apply]
  exact Subgroup.pow_mem _ htH _

theorem exists_torus_section (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {p k : ℕ} (hp : Odd p) (τ : (Fin k → Multiplicative (ZMod p)) →* R)
    (hinv : ∀ i j : Fin k, ∃ w : R, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j)) :
    ∃ σ : (Fin k → Multiplicative (ZMod p)) →* L', ψ.comp σ = τ := by
  classical
  have : NeZero p := ⟨by rintro rfl; exact (Nat.not_odd_zero hp)⟩
  choose x hx using fun i => hψ (torusBasis τ i)
  have hT : ∀ a b : Fin k → Multiplicative (ZMod p), Commute (τ a) (τ b) :=
    fun a b => (Commute.all a b).map τ
  have hxx : ∀ i j, Commute (x i) (x j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    obtain ⟨w, hw1, hw2⟩ := hinv i j
    refine commute_lift_of_inverting hψ hker hp (w := w) ?_ ?_ ?_ ?_
    · rw [hx, hx]
      exact hT _ _
    · rw [hx]
      exact torusBasis_pow τ i
    · rw [hx]
      exact hw1
    · rw [hx]
      exact hw2 (Ne.symm hij)
  set S : Set L' := Set.range x ∪ (ψ.ker : Set L') with hS
  have hSc : S.Pairwise Commute := by
    rintro a ha b hb -
    rcases ha with ⟨i, rfl⟩ | ha
    · rcases hb with ⟨j, rfl⟩ | hb
      · exact hxx i j
      · exact Subgroup.mem_center_iff.mp (hker hb) (x i)
    · exact (Subgroup.mem_center_iff.mp (hker ha) b).symm
  set A := Subgroup.closure S with hA
  have hAc : IsMulCommutative A := Subgroup.isMulCommutative_closure hSc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hkerA : ψ.ker ≤ A := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hxA : ∀ i, x i ∈ A := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hlift : ∀ i, ∃ t ∈ A, ψ t = torusBasis τ i ∧ t ^ p = 1 := by
    intro i
    obtain ⟨w, hw, -⟩ := hinv i i
    exact exists_lift_pow_eq_one hψ hker hp (torusBasis_pow τ i) hw hAcomm hkerA (hx i) (hxA i)
  choose t htA hψt htp using hlift
  set φ : ∀ i : Fin k, Multiplicative (ZMod p) →* L' := fun i => zmodPowHom (htp i) with hφ
  have hcomm : Pairwise fun i j => ∀ a b, Commute (φ i a) (φ j b) := fun i j _ a b =>
    hAcomm _ (zmodPowHom_mem (htp i) (htA i) a) _ (zmodPowHom_mem (htp j) (htA j) b)
  refine ⟨MonoidHom.noncommPiCoprod φ hcomm, MonoidHom.pi_ext fun i a => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_mulSingle, hφ, zmodPowHom_apply, map_pow,
    hψt, torusBasis_pow_val]

end Section

section TwoLift

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_twoSubgroup_lift [Finite L'] (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    {E : Subgroup L'} (hEU : ∀ e ∈ E, ∀ u ∈ U, ψ e * u * (ψ e)⁻¹ ∈ U) :
    ∃ T : Subgroup L', T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set L') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup L' := U.comap ψ with hH
  let f : H →* U := (ψ.comp H.subtype).codRestrict U (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨⟨l, hr⟩, rfl⟩
  have hfker : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 := hker h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Finite U := Finite.of_surjective _ hf
  have : Group.IsNilpotent U := hU2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hfker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have htop : (⊤ : Subgroup U) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hU2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (n := j) (G := Subgroup.zpowers h)
      (by rw [Nat.card_zpowers, hj])).exists_le_sylow
    have hQP : Q = P := Subsingleton.elim (α := Sylow 2 H) Q P
    rw [← hQP]
    exact hQ (Subgroup.mem_zpowers h)
  refine ⟨(P : Subgroup H).map H.subtype, ?_, P.isPGroup'.map _, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ E, ∀ q ∈ (P : Subgroup H).map H.subtype,
        g * q * g⁻¹ ∈ (P : Subgroup H).map H.subtype := by
      rintro g hg _ ⟨q, hq, rfl⟩
      have hgH : g * (q : L') * g⁻¹ ∈ H := by
        show ψ (g * (q : L') * g⁻¹) ∈ U
        rw [map_mul, map_mul, map_inv]
        exact hEU g hg _ q.2
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨q, hq⟩
      have hqk : (q : L') ^ 2 ^ k = 1 := by
        have := congrArg (fun z : (P : Subgroup H) => ((z : H) : L')) hk
        simpa using this
      refine ⟨⟨_, hgH⟩, hmemP _ k (Subtype.ext ?_), rfl⟩
      show (g * (q : L') * g⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hqk, mul_one, mul_inv_cancel]
    intro q
    constructor
    · exact key e he q
    · intro hq
      have := key e⁻¹ (E.inv_mem he) _ hq
      simpa [mul_assoc] using this

end TwoLift

theorem ggTorusLift_of_torus {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (τ : (Fin k → Multiplicative (ZMod p)) →* R) (hτ : Function.Injective τ)
    (hinv : ∀ i j : Fin k, ∃ w : R, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j))
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hTU : ∀ d, ∀ u ∈ U, τ d * u * (τ d)⁻¹ ∈ U) : GGTorusLift p k R := by
  intro L' _ _ ψ hψ hker _
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨σ, hσ⟩ := exists_torus_section hψ hker hodd τ hinv
  have hσi : Function.Injective σ := by
    intro a b hab
    apply hτ
    rw [← hσ, MonoidHom.comp_apply, MonoidHom.comp_apply, hab]
  obtain ⟨T, hT, hT2, hET⟩ := exists_twoSubgroup_lift (E := σ.range) hψ hker hU hU2 (by
    rintro _ ⟨d, rfl⟩ u hu
    have := hTU d u hu
    rwa [← hσ] at this)
  refine ⟨T, σ.range, hT, hT2, hET, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show σ a * σ b = σ b * σ a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul, ofAdd_zero]
      rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hσi).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
      Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨d, rfl⟩, hd⟩
    have hd' : ψ (σ d) = 1 := hd
    rw [← MonoidHom.comp_apply, hσ] at hd'
    rw [Subgroup.mem_bot, hτ (hd'.trans (map_one τ).symm), map_one]

end TableBSymp

end CFSG.StandardType
