module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.HyperplaneOrbit
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Translations
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem exists_zpow_of_card_prime {Z : Subgroup G} (hZr : (Nat.card Z).Prime) {ζ : G}
    (hζ : ζ ∈ Z) (hζ1 : ζ ≠ 1) {ζ' : G} (hζ' : ζ' ∈ Z) : ∃ s : ℤ, ζ' = ζ ^ s := by
  have hle : zpowers ζ ≤ Z := zpowers_le.mpr hζ
  have heq : zpowers ζ = Z := by
    apply Subgroup.eq_of_le_of_card_ge hle
    have hd : Nat.card (zpowers ζ) ∣ Nat.card Z := Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hZr).mp hd with h | h
    · exfalso
      have hb := Subgroup.eq_bot_of_card_eq _ h
      have := mem_zpowers ζ
      rw [hb, mem_bot] at this
      exact hζ1 this
    · exact h.ge
  rw [← heq] at hζ'
  obtain ⟨s, hs⟩ := mem_zpowers_iff.mp hζ'
  exact ⟨s, hs.symm⟩

theorem sum_smul_conj (V : Subgroup G) [Fintype V] {g : G} (hg : ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (m : M) : ∑ v : V, (v : G) • g • m = g • ∑ v : V, (v : G) • m := by
  let φ : V → V := fun v => ⟨g * v * g⁻¹, hg v v.2⟩
  have hφ : Function.Injective φ := fun a b h => by
    have : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using this)
  rw [Finset.smul_sum]
  have : ∀ v : V, g • (v : G) • m = ((φ v : V) : G) • g • m := fun v => by
    simp only [φ, smul_smul]; congr 1; group
  simp_rw [this]
  exact (Equiv.sum_comp (Equiv.ofBijective φ hφ.bijective_of_finite) (fun w : V => (w : G) • g • m)).symm

theorem false_of_moving_translations {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M)) (hMnt : ∃ m : M, m ≠ 0)
    {V Z : Subgroup G} {Vi : Fin 3 → Subgroup G} {z y : Fin 3 → G} {c : G}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVr : ∀ v ∈ V, v ^ r = 1)
    (hVodd : Odd (Nat.card V))
    (hZc : Z ≤ center G) (hZr : Nat.card Z = r)
    (hZM : ∀ ζ ∈ Z, ζ ≠ 1 → ∀ m : M, ζ • m = m → m = 0)
    (hViV : ∀ a, Vi a ≤ V)
    (hc : c * c = 1) (hz : ∀ a, z a * z a = 1) (hz2 : z 2 = z 0 * z 1)
    (hcz : ∀ a, c * z a = z a * c) (h01 : z 0 * z 1 = z 1 * z 0)
    (hcV : ∀ v ∈ V, c * v * c⁻¹ = v⁻¹) (hzV : ∀ a, ∀ v ∈ V, z a * v * (z a)⁻¹ ∈ V)
    (hzinv : ∀ a b, a ≠ b → ∀ v ∈ Vi b, z a * v * (z a)⁻¹ = v⁻¹)
    (hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0)
    (hyV : ∀ a, ∀ v ∈ V, y a * v * (y a)⁻¹ * v⁻¹ ∈ Z)
    (hyV' : ∀ a, ∀ v ∈ V, (y a)⁻¹ * v * y a * v⁻¹ ∈ Z)
    (hfix : ∀ a b, a ≠ b → ∀ v ∈ Vi b, y a * v * (y a)⁻¹ = v)
    (hZfix : ∀ a, ∀ ζ ∈ Z, y a * ζ * (y a)⁻¹ = ζ)
    (hmove : ∀ a, ∃ v ∈ Vi a, y a * v * (y a)⁻¹ * v⁻¹ ∈ Z ∧ y a * v * (y a)⁻¹ * v⁻¹ ≠ 1) :
    False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hZr' : (Nat.card Z).Prime := hZr ▸ hr
  have hZcomm : ∀ ζ ∈ Z, ∀ g : G, g * ζ = ζ * g := fun ζ hζ g => Subgroup.mem_center_iff.mp (hZc hζ) g
  haveI hZn : Z.Normal := ⟨fun n hn g => by rw [hZcomm n hn g, mul_inv_cancel_right]; exact hn⟩
  have memVZ : ∀ x ∈ V ⊔ Z, ∃ v ∈ V, ∃ ζ ∈ Z, v * ζ = x := fun x hx =>
    Subgroup.mem_sup_of_normal_right.mp hx
  have commVZ : ∀ x ∈ V ⊔ Z, ∀ x' ∈ V ⊔ Z, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨v, hv, ζ, hζ, rfl⟩ := memVZ x hx
    obtain ⟨v', hv', ζ', hζ', rfl⟩ := memVZ x' hx'
    exact (Commute.mul_left (Commute.mul_right (hVab v hv v' hv') (hZcomm ζ' hζ' v))
      (hZcomm ζ hζ (v' * ζ')).symm).eq
  have hcop : Nat.Coprime (Nat.card V) (Nat.card M) := by
    have hVp : IsPGroup r V := fun g => ⟨1, Subtype.ext (by simpa using hVr g g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVp
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrM)
  let 𝒦 : Subgroup G → Prop := fun K => (∀ k ∈ K, k ∈ V ⊔ Z) ∧ (∀ ζ ∈ Z, ζ ∈ K → ζ = 1) ∧
    (∀ v ∈ V, ∃ k ∈ K, ∃ ζ ∈ Z, v = k * ζ) ∧ ∃ m : M, m ≠ 0 ∧ ∀ k ∈ K, k • m = m
  have hconj : ∀ a K, 𝒦 K → 𝒦 (K.map (MulAut.conj (y a)).toMonoidHom) := by
    intro a K ⟨h1, h2, h3, m, hm0, hm⟩
    have hmem : ∀ x, x ∈ K.map (MulAut.conj (y a)).toMonoidHom ↔ ∃ k ∈ K, y a * k * (y a)⁻¹ = x := by
      intro x; simp [MulAut.conj_apply]
    refine ⟨?_, ?_, ?_, y a • m, ?_, ?_⟩
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := (hmem x).mp hx
      obtain ⟨v, hv, ζ, hζ, rfl⟩ := memVZ k (h1 k hk)
      have e : y a * (v * ζ) * (y a)⁻¹ = (y a * v * (y a)⁻¹ * v⁻¹) * v * ζ := by
        rw [show y a * (v * ζ) * (y a)⁻¹ = (y a * v * (y a)⁻¹) * (y a * ζ * (y a)⁻¹) by group,
          hZfix a ζ hζ]
        group
      rw [e]
      exact mul_mem (mul_mem (mem_sup_right (hyV a v hv)) (mem_sup_left hv)) (mem_sup_right hζ)
    · intro ζ hζ hx
      obtain ⟨k, hk, hkx⟩ := (hmem ζ).mp hx
      have hk' : y a * k * (y a)⁻¹ = y a * ζ * (y a)⁻¹ := hkx.trans (hZfix a ζ hζ).symm
      have : k = ζ := by simpa using hk'
      exact h2 ζ hζ (this ▸ hk)
    · intro v hv
      obtain ⟨k, hk, ζ, hζ, hvk⟩ := h3 v hv
      have hζ₁ := hyV' a v hv
      set ζ₁ := (y a)⁻¹ * v * y a * v⁻¹ with hζ₁d
      refine ⟨y a * k * (y a)⁻¹, (hmem _).mpr ⟨k, hk, rfl⟩, ζ₁ * ζ, mul_mem hζ₁ hζ, ?_⟩
      have hw : (y a)⁻¹ * v * y a = k * (ζ₁ * ζ) := by
        have : (y a)⁻¹ * v * y a = ζ₁ * v := by rw [hζ₁d]; group
        rw [this, hvk, ← mul_assoc, ← hZcomm ζ₁ hζ₁ k, mul_assoc]
      calc v = y a * ((y a)⁻¹ * v * y a) * (y a)⁻¹ := by group
        _ = (y a * k * (y a)⁻¹) * (y a * (ζ₁ * ζ) * (y a)⁻¹) := by rw [hw]; group
        _ = y a * k * (y a)⁻¹ * (ζ₁ * ζ) := by rw [hZfix a _ (mul_mem hζ₁ hζ)]
    · intro h
      apply hm0
      have := congrArg (fun x => (y a)⁻¹ • x) h
      simpa using this
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := (hmem x).mp hx
      rw [mul_smul, mul_smul, inv_smul_smul, hm k hk]
  haveI : Fintype V := Fintype.ofFinite V
  let e : M →+ M := AddMonoidHom.mk' (fun x => ∑ v : V, (v : G) • x)
    (fun x x' => by simp [smul_add, Finset.sum_add_distrib])
  have he : ∀ x, e x = ∑ v : V, (v : G) • x := fun x => rfl
  have hM₁g : ∀ g : G, (∀ v ∈ V, g * v * g⁻¹ ∈ V) → ∀ m ∈ e.ker, g • m ∈ e.ker := by
    intro g hg m hm
    rw [AddMonoidHom.mem_ker] at hm ⊢
    rw [he] at hm ⊢
    rw [sum_smul_conj V hg, hm, smul_zero]
  have hM₁0 : ∀ m ∈ e.ker, (∀ v ∈ V, v • m = m) → m = 0 := by
    intro m hm hmV
    rw [AddMonoidHom.mem_ker, he, sum_smul_const V hmV] at hm
    by_contra h0
    exact nsmul_ne_zero_of_coprime hcop h0 hm
  have hP : ∀ K, 𝒦 K → ∃ a b, a ≠ b ∧ Vi a ≤ K ∧ Vi b ≤ K := by
    intro K ⟨h1, h2, h3, m, hm0, hm⟩
    by_cases hVK : V ≤ K
    · exact ⟨0, 1, by decide, (hViV 0).trans hVK, (hViV 1).trans hVK⟩
    obtain ⟨v₀, hv₀, hv₀K⟩ := SetLike.not_le_iff_exists.mp hVK
    obtain ⟨k₀, hk₀, ζ₀, hζ₀, hv₀e⟩ := h3 v₀ hv₀
    have hζ₀1 : ζ₀ ≠ 1 := by
      rintro rfl; rw [mul_one] at hv₀e; exact hv₀K (hv₀e ▸ hk₀)
    have hZVK : ∀ ζ ∈ Z, ζ ∈ V ⊔ K := by
      intro ζ hζ
      obtain ⟨s, rfl⟩ := exists_zpow_of_card_prime hZr' hζ₀ hζ₀1 hζ
      have : ζ₀ = k₀⁻¹ * v₀ := by rw [hv₀e]; group
      rw [this]
      exact zpow_mem (mul_mem (mem_sup_right (inv_mem hk₀)) (mem_sup_left hv₀)) s
    have hcommK : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k := fun k hk v hv =>
      commVZ k (h1 k hk) v (mem_sup_left hv)
    have hmM₁ : m ∈ e.ker := by
      rw [AddMonoidHom.mem_ker]
      set E := e m with hE
      have hEV : V ⊔ K ≤ MulAction.stabilizer G E := by
        refine sup_le (fun v hv => ?_) (fun k hk => ?_)
        · rw [MulAction.mem_stabilizer_iff, hE, he]; exact sum_smul_fix V hv m
        · rw [MulAction.mem_stabilizer_iff, hE, he, ← sum_smul_conj V (fun v hv => by
            rw [hcommK k hk v hv, mul_inv_cancel_right]; exact hv), hm k hk]
      exact hZM ζ₀ hζ₀ hζ₀1 E (MulAction.mem_stabilizer_iff.mp (hEV (hZVK ζ₀ hζ₀)))
    have hHmax : ∀ L : Subgroup G, K ⊓ V ≤ L → L ≤ V → L = K ⊓ V ∨ L = V := by
      intro L hHL hLV
      by_cases hLH : L ≤ K ⊓ V
      · exact Or.inl (le_antisymm hLH hHL)
      right
      apply le_antisymm hLV
      obtain ⟨l, hl, hlH⟩ := SetLike.not_le_iff_exists.mp hLH
      have hlK : l ∉ K := fun h => hlH ⟨h, hLV hl⟩
      obtain ⟨k, hk, ζ, hζ, hle⟩ := h3 l (hLV hl)
      have hζ1 : ζ ≠ 1 := by
        rintro rfl; rw [mul_one] at hle; exact hlK (hle ▸ hk)
      intro w hw
      obtain ⟨k', hk', ζ', hζ', hwe⟩ := h3 w hw
      obtain ⟨s, rfl⟩ := exists_zpow_of_card_prime hZr' hζ hζ1 hζ'
      have hkey : w * l ^ (-s) = k' * k ^ (-s) := by
        have hc' := hZcomm (ζ ^ s) (zpow_mem hζ s) (k ^ (-s))
        rw [hwe, hle, (show Commute k ζ from hZcomm ζ hζ k).mul_zpow, mul_assoc, ← mul_assoc (ζ ^ s), ← hc', mul_assoc,
          ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      have hH : w * l ^ (-s) ∈ K ⊓ V :=
        ⟨by rw [hkey]; exact mul_mem hk' (zpow_mem hk _), mul_mem hw (zpow_mem (hLV hl) _)⟩
      have : w = w * l ^ (-s) * l ^ s := by group
      rw [this]
      exact mul_mem (hHL hH) (zpow_mem hl s)
    have hHV' : K ⊓ V ≠ V := fun h => hVK (by rw [← h]; exact inf_le_left)
    have hLA' : ∀ m : M, ∀ u ∈ ({z 0, z 1, z 0 * z 1} : Set G), c • m = m → u • m = -m → m = 0 := by
      intro m u hu
      rcases hu with rfl | rfl | rfl
      · exact hLA m 0
      · exact hLA m 1
      · rw [← hz2]; exact hLA m 2
    obtain ⟨u, hu, -, huV⟩ := exists_fix_hyperplane hcop hModd hVab hVodd inf_le_right hHmax hHV'
      (fun v hv m hm => hM₁g v (fun w hw => mul_mem (mul_mem hv hw) (inv_mem hv)) m hm) hM₁0
      (hM₁g c (fun v hv => by rw [hcV v hv]; exact inv_mem hv)) (hM₁g (z 0) (hzV 0))
      (hM₁g (z 1) (hzV 1)) hc (hz 0) (hz 1) (hcz 0) (hcz 1) h01 hcV (hzV 0) (hzV 1) hLA' hmM₁
      (fun h hh => hm h hh.1) hm0
    have hVjK : ∀ i j, i ≠ j → (∀ v ∈ V, z i * v * (z i)⁻¹ * v⁻¹ ∈ K ⊓ V) → Vi j ≤ K := by
      intro i j hij hi v hv
      have h' := hi v (hViV j hv)
      rw [hzinv i j hij v hv] at h'
      obtain ⟨n, hn⟩ := exists_pow_sq hVodd (hViV j hv)
      have h2' : v ^ 2 ∈ K := by
        have := K.inv_mem h'.1
        rwa [mul_inv_rev, inv_inv, ← sq] at this
      rw [← hn]
      exact pow_mem h2' n
    rcases hu with rfl | rfl | rfl
    · exact ⟨1, 2, by decide, hVjK 0 1 (by decide) huV, hVjK 0 2 (by decide) huV⟩
    · exact ⟨0, 2, by decide, hVjK 1 0 (by decide) huV, hVjK 1 2 (by decide) huV⟩
    · rw [← hz2] at huV
      exact ⟨0, 1, by decide, hVjK 2 0 (by decide) huV, hVjK 2 1 (by decide) huV⟩
  have hK₀ : ∃ K₀, 𝒦 K₀ := by
    set A := V ⊔ Z with hA
    letI iC : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (commVZ a a.2 b b.2) }
    haveI : CFSG.IsElementaryAbelian r A :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (commVZ a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
          obtain ⟨v, hv, ζ, hζ, hg⟩ := memVZ g g.2
          apply Subtype.ext
          have hζr : ζ ^ r = 1 := by
            have := pow_card_eq_one' (G := Z) (x := ⟨ζ, hζ⟩)
            rw [hZr] at this
            simpa using congrArg Subtype.val this
          rw [Subgroup.coe_pow, ← hg, (show Commute v ζ from hZcomm ζ hζ v).mul_pow, hVr v hv,
            hζr, one_mul, Subgroup.coe_one] }
    haveI : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (hZr ▸ hr.one_lt)
    obtain ⟨⟨ζ, hζ⟩, hne⟩ := exists_ne (1 : Z)
    have hζ1 : ζ ≠ 1 := fun h => hne (Subtype.ext h)
    haveI : Nontrivial A := ⟨⟨⟨ζ, mem_sup_right hζ⟩, 1, fun h => hζ1 (congrArg Subtype.val h)⟩⟩
    let α : A →* MulAut (Multiplicative M) :=
      { toFun := fun a =>
          { toFun := fun x => Multiplicative.ofAdd ((a : G) • x.toAdd)
            invFun := fun x => Multiplicative.ofAdd ((a : G)⁻¹ • x.toAdd)
            left_inv := fun x => by simp
            right_inv := fun x => by simp
            map_mul' := fun x x' => by simp [smul_add] }
        map_one' := by ext x; simp
        map_mul' := fun a b => by ext x; simp [mul_smul] }
    have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top r hr α
      (by rwa [show Nat.card (Multiplicative M) = Nat.card M from
        Nat.card_congr Multiplicative.toAdd])
    obtain ⟨m₀, hm₀⟩ := hMnt
    have hex : ∃ B : Subgroup A, B.index = r ∧
        ∃ x ∈ CFSG.SolvableSignalizer.fixedBySubgroup α B, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hle : (⨆ (B : Subgroup A) (_ : B.index = r),
          CFSG.SolvableSignalizer.fixedBySubgroup α B) ≤ ⊥ :=
        iSup₂_le fun B hB x hx => (Subgroup.mem_bot).mpr (hcon B hB x hx)
      rw [hgen] at hle
      have := hle (Subgroup.mem_top (Multiplicative.ofAdd m₀))
      rw [Subgroup.mem_bot] at this
      exact hm₀ (by simpa using congrArg Multiplicative.toAdd this)
    obtain ⟨B, hB, x, hx, hx1⟩ := hex
    have hxfix : ∀ b ∈ B, (b : G) • x.toAdd = x.toAdd := fun b hb =>
      congrArg Multiplicative.toAdd
        ((CFSG.SolvableSignalizer.mem_fixedBySubgroup α B x).mp hx b hb)
    have hxne : x.toAdd ≠ 0 := fun h => hx1 (by simpa using congrArg Multiplicative.ofAdd h)
    refine ⟨B.map A.subtype, ?_, ?_, ?_, x.toAdd, hxne, ?_⟩
    · intro k hk
      obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hk
      exact b.2
    · intro ζ' hζ' hk
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hk
      by_contra h1
      exact hxne (hZM _ hζ' h1 _ (hxfix b hb))
    · intro v hv
      let Z' := Z.subgroupOf A
      haveI : Z'.Normal := hZn.subgroupOf A
      have hBc : IsCoatom B := Subgroup.isCoatom_of_index_prime (by rw [hB]; exact hr)
      have hZ'B : ¬ Z' ≤ B := fun h =>
        hxne (hZM ζ hζ hζ1 _ (hxfix ⟨ζ, mem_sup_right hζ⟩ (h (Subgroup.mem_subgroupOf.mpr hζ))))
      have hsup : B ⊔ Z' = ⊤ := hBc.2 _ (lt_of_le_of_ne le_sup_left (fun h => hZ'B (by
        rw [h]; exact le_sup_right)))
      have hvA : (⟨v, mem_sup_left hv⟩ : A) ∈ B ⊔ Z' := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨b, hb, z', hz', hbz⟩ := Subgroup.mem_sup_of_normal_right.mp hvA
      refine ⟨A.subtype b, Subgroup.mem_map_of_mem _ hb, z', Subgroup.mem_subgroupOf.mp hz', ?_⟩
      have := congrArg Subtype.val hbz
      simp only [Subgroup.coe_mul] at this
      simpa using this.symm
    · intro k hk
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hk
      exact hxfix b hb
  obtain ⟨K₀, hK₀⟩ := hK₀
  exact false_of_translations (V := Vi) (Z := Z) (y := y) (𝒦 := 𝒦) hconj hP
    (fun K hK => hK.2.1) hfix hZfix hmove hK₀

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

