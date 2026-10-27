module

public import CFSG.Quasithin.EmptyFaithful.R3c16TriC
public import CFSG.Quasithin.EmptyFaithful.R3c9Alt4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c9
  CFSG.Quasithin.R3c16
open scoped commutatorElement

section Perm

theorem perm3_sq_of_twoPow (σ : Equiv.Perm (Fin 3)) (j : ℕ) (h : σ ^ (2 ^ j) = 1) : σ ^ 2 = 1 := by
  have hc : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by decide +kernel
  rcases hc σ with h2 | h3
  · exact h2
  · have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
    have := pow_gcd_eq_one.2 ⟨h3, h⟩
    rw [hcop] at this
    rw [pow_one] at this
    rw [this]
    simp

theorem perm3_key : ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 3 = 1 →
    ¬ (a * (b * a * b⁻¹)) ^ 2 = 1 := by decide +kernel

end Perm

section Action

variable {G : Type} [Group G]

theorem two_group_trivial_action {M U W V : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hV4 : Nat.card V = 4) (hU2 : IsPGroup 2 ↥U) (hUW : U ≤ W) (hWM : W ≤ M)
    (hWn : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (hW : ∀ w ∈ W, ∃ u ∈ U, ∀ v ∈ V, w * v * w⁻¹ = u * v * u⁻¹)
    {y : G} (hy : y ∈ M) {k : ℕ} (hk : y ^ (3 ^ k) = 1) (hyn : ¬ ∀ v ∈ V, y * v = v * y) :
    ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := by
  classical
  have hVfin : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨ι, hιinj, -⟩ := exists_mulAut_embedding ↥V hV4
  let ρ : ↥M →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hMV)
  have hρ : ∀ (g : ↥M) (v : ↥V), ((ρ g v : ↥V) : G) = (g : G) * (v : G) * (g : G)⁻¹ :=
    fun g v => Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion hMV g) v
  have hUM : U ≤ M := hUW.trans hWM
  intro u hu v hv
  by_contra hne
  set uM : ↥M := ⟨u, hUM hu⟩ with huM
  set yM : ↥M := ⟨y, hy⟩ with hyM
  have hτ : ρ uM ≠ 1 := by
    intro h1
    apply hne
    have h2 := hρ uM ⟨v, hv⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 : v = u * v * u⁻¹ := h2
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v * u := by rw [← h3]
  have hψ : ρ yM ≠ 1 := by
    intro h1
    apply hyn
    intro v hv
    have h2 := hρ yM ⟨v, hv⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 : v = y * v * y⁻¹ := h2
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [← h3]
  have hyuW : y * u * y⁻¹ ∈ W := hWn y hy u (hUW hu)
  obtain ⟨u', hu'U, hu'⟩ := hW _ hyuW
  set u'M : ↥M := ⟨u', hUM hu'U⟩ with hu'M
  have hρ' : ρ u'M = ρ yM * ρ uM * (ρ yM)⁻¹ := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have e : ((yM * uM * yM⁻¹ : ↥M) : G) = y * u * y⁻¹ := rfl
    have h1 : ρ (yM * uM * yM⁻¹) = ρ yM * ρ uM * (ρ yM)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← h1, hρ, hρ, e]
    exact (hu' x x.2).symm
  obtain ⟨j₁, hj₁⟩ := hU2 ⟨u, hu⟩
  have hu2 : u ^ (2 ^ j₁) = 1 := congrArg Subtype.val hj₁
  obtain ⟨j₂, hj₂⟩ := hU2 ⟨u * u', (Subgroup.mul_mem _ hu hu'U)⟩
  have huu2 : (u * u') ^ (2 ^ j₂) = 1 := congrArg Subtype.val hj₂
  have ha2 : (ι (ρ uM)) ^ 2 = 1 := by
    apply perm3_sq_of_twoPow _ j₁
    rw [← map_pow, ← map_pow]
    have : uM ^ (2 ^ j₁) = 1 := Subtype.ext (by simpa using hu2)
    rw [this, map_one, map_one]
  have hb3 : (ι (ρ yM)) ^ 3 = 1 := by
    apply perm3_pow3_of_threePow (k := k)
    rw [← map_pow, ← map_pow]
    have : yM ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one, map_one]
  have ha1 : ι (ρ uM) ≠ 1 := fun h => hτ (hιinj (by rw [h, map_one]))
  have hb1 : ι (ρ yM) ≠ 1 := fun h => hψ (hιinj (by rw [h, map_one]))
  have hp2 : (ι (ρ (uM * u'M))) ^ 2 = 1 := by
    apply perm3_sq_of_twoPow _ j₂
    rw [← map_pow, ← map_pow]
    have : (uM * u'M) ^ (2 ^ j₂) = 1 := Subtype.ext (by simpa using huu2)
    rw [this, map_one, map_one]
  rw [map_mul, map_mul, hρ', map_mul, map_mul, map_inv] at hp2
  exact perm3_key _ _ ha1 ha2 hb1 hb3 hp2

theorem act_eq_of_mem_sup_perfect {M U L V : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hV4 : Nat.card V = 4) (hUM : U ≤ M) (hLM : L ≤ M) (hL : Group.IsPerfect ↥L) {w : G}
    (hw : w ∈ U ⊔ L) : ∃ u ∈ U, ∀ v ∈ V, w * v * w⁻¹ = u * v * u⁻¹ := by
  classical
  have hVfin : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
  let ρ : ↥M →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hMV)
  have hρ : ∀ (g : ↥M) (v : ↥V), ((ρ g v : ↥V) : G) = (g : G) * (v : G) * (g : G)⁻¹ :=
    fun g v => Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion hMV g) v
  have hsolv : Group.IsSolvable (MulAut ↥V) := by
    have hP : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV4.le
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      (fun a b h => MulEquiv.ext fun x => Equiv.congr_fun h x)
  have hL1 : ∀ l : ↥L, ρ (Subgroup.inclusion hLM l) = 1 := by
    set ρL : ↥L →* MulAut ↥V := ρ.comp (Subgroup.inclusion hLM) with hρL
    have := hL
    have := hsolv
    have hrange : ρL.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥ρL.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      have : Group.IsPerfect ↥ρL.range := Group.IsPerfect.range ρL
      exact Group.IsPerfect.not_isSolvable ↥ρL.range inferInstance
    intro l
    have : ρL l ∈ ρL.range := ⟨l, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact this
  have hwM : w ∈ M := (sup_le hUM hLM) hw
  set w' : ↥M := ⟨w, hwM⟩ with hw'
  have hw'mem : w' ∈ (U ⊔ L).subgroupOf M := hw
  rw [Subgroup.subgroupOf_sup hUM hLM] at hw'mem
  have hLker : ∀ x ∈ L.subgroupOf M, ρ x = 1 := fun x hx => hL1 ⟨(x : G), hx⟩
  have hmem : ρ w' ∈ (U.subgroupOf M).map ρ := by
    have h1 : ρ w' ∈ (U.subgroupOf M ⊔ L.subgroupOf M).map ρ := Subgroup.mem_map_of_mem ρ hw'mem
    rw [Subgroup.map_sup] at h1
    have h2 : (L.subgroupOf M).map ρ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [hLker x hx]
      exact Subgroup.one_mem _
    rwa [h2, sup_bot_eq] at h1
  obtain ⟨u', hu', hu'ρ⟩ := hmem
  refine ⟨(u' : G), Subgroup.mem_subgroupOf.mp hu', fun v hv => ?_⟩
  have h1 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) hu'ρ
  simp only [hρ] at h1
  exact h1.symm

end Action

section Zeta

variable {G : Type} [Group G] [Finite G]

theorem zeta_central_of_elData {T V H : Subgroup G} {ζ : MulAut G} (hT : IsSylowTwoOf T ⊤)
    (hA : ∀ β : G ≃* G, (∀ q ∈ T, β q = q) → ∃ x : G, ∀ y : G, β y = x⁻¹ * y * x)
    (hOdd : ∀ φ : MulAut G, (∀ u ∈ T, φ u = u) → Odd (orderOf φ) → φ = 1)
    (hZ : ∀ g : G, (∀ y : G, g * y = y * g) → g = 1) (h : ElData T V H ζ) :
    ∃ x ∈ T, x ≠ 1 ∧ (∀ t ∈ T, t * x = x * t) ∧ ∀ k ∈ H, k * x = x * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  obtain ⟨x, hx⟩ := hA ζ h.fixT
  have hxT : ∀ t ∈ T, t * x = x * t := fun t ht => by
    have h1 := hx t
    rw [h.fixT t ht] at h1
    calc t * x = x * (x⁻¹ * t * x) := by group
      _ = x * t := by rw [← h1]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply h.ne
    ext y
    rw [hx y]
    simp
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hg : x ^ (2 ^ k) = 1 := by
    have hgo : orderOf (x ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hkm]; exact dvd_mul_right _ _),
        hkm, Nat.mul_div_cancel_left _ (by positivity)]
    have hcomm : ∀ t ∈ T, t * x ^ (2 ^ k) = x ^ (2 ^ k) * t := fun t ht =>
      ((show Commute t x from hxT t ht).pow_right (2 ^ k)).eq
    have hodd : Odd (orderOf (MulAut.conj (x ^ (2 ^ k)))) :=
      Odd.of_dvd_nat (hgo ▸ hm) (orderOf_map_dvd (MulAut.conj : G →* MulAut G) (x ^ (2 ^ k)))
    have h1 := hOdd (MulAut.conj (x ^ (2 ^ k))) (fun u hu => by
      rw [MulAut.conj_apply]
      calc x ^ (2 ^ k) * u * (x ^ (2 ^ k))⁻¹ = (u * x ^ (2 ^ k)) * (x ^ (2 ^ k))⁻¹ := by
            rw [← hcomm u hu]
        _ = u := by group) hodd
    refine hZ _ fun y => ?_
    have h2 := DFunLike.congr_fun h1 y
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    calc x ^ (2 ^ k) * y = (x ^ (2 ^ k) * y * (x ^ (2 ^ k))⁻¹) * x ^ (2 ^ k) := by group
      _ = y * x ^ (2 ^ k) := by rw [h2]
  have hZ2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    rintro ⟨g, hg'⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxT)
  have hsup : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers x) :=
    hp.to_sup_of_normal_left' hZ2 (Subgroup.zpowers_le.2 hxN)
  have hxTT : x ∈ T := by
    have hmax : T ⊔ Subgroup.zpowers x = T := (hp.toSylow hi).is_maximal' hsup le_sup_left
    have hx' : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hmax] at hx'
  refine ⟨x, hxTT, hx1, hxT, fun k hk => ?_⟩
  have hk' := h.fixH k hk
  rw [hx k] at hk'
  calc k * x = x * (x⁻¹ * k * x) := by group
    _ = x * k := by rw [hk']

@[expose] def CentralScalar (X : Type) [Group X] : Prop :=
  ∀ {T V : Subgroup X}, IsSylowTwoOf T ⊤ → V ≤ T → Nat.card V = 4 →
    T ≤ Subgroup.normalizer (V : Set X) → ∀ {y : X}, y ∈ Subgroup.normalizer (V : Set X) →
      ∀ {k : ℕ}, y ^ (3 ^ k) = 1 → (¬ ∀ v ∈ V, y * v = v * y) →
        (∀ v ∈ V, ∀ t ∈ T, t * v = v * t) ∧
        ∀ g ∈ Subgroup.normalizer (V : Set X), ∀ z ∈ T, (∀ t ∈ T, t * z = z * t) → z ≠ 1 →
          g * z = z * g → ∀ v ∈ V, g * v = v * g

theorem not_elData_of_centralScalar {T V H : Subgroup G} {ζ : MulAut G} (hT : IsSylowTwoOf T ⊤)
    (hA : ∀ β : G ≃* G, (∀ q ∈ T, β q = q) → ∃ x : G, ∀ y : G, β y = x⁻¹ * y * x)
    (hOdd : ∀ φ : MulAut G, (∀ u ∈ T, φ u = u) → Odd (orderOf φ) → φ = 1)
    (hZ : ∀ g : G, (∀ y : G, g * y = y * g) → g = 1) (hX : CentralScalar G)
    (h : ElData T V H ζ) : False := by
  obtain ⟨x, hxT, hx1, hxc, hxH⟩ := zeta_central_of_elData hT hA hOdd hZ h
  obtain ⟨y, hyH, hy3, hyn⟩ := h.y3
  obtain ⟨-, hb⟩ := hX hT h.VT h.V4 h.TV (h.HV hyH) (k := 1) (by simpa using hy3) hyn
  exact hyn (hb y (h.HV hyH) x hxT hxc hx1 (hxH y hyH))

end Zeta

end CFSG.Quasithin.R3c17
