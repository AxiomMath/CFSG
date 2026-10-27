module

public import CFSG.Walter.ReeOrder.JT.Basic

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section Torus

variable {X : Type*} [Group X] {L U : Subgroup X} {w : X}

theorem TorusData.mem_sup_iff (hU : TorusData L U w) {x : X} :
    x ∈ U ⊔ Subgroup.zpowers w ↔ x ∈ U ∨ x * w ∈ U := by
  have hw2 := hU.w_mul_self
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h1 : ∀ u ∈ U, w * u * w ∈ U := fun u hu => by
    have := hU.inv u hu
    rw [hwinv] at this
    rw [this]
    exact U.inv_mem hu
  constructor
  · intro hx
    let H : Subgroup X :=
      { carrier := {y | y ∈ U ∨ y * w ∈ U}
        one_mem' := Or.inl U.one_mem
        mul_mem' := by
          intro a b ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (U.mul_mem ha hb)
          · right
            rw [mul_assoc]
            exact U.mul_mem ha hb
          · right
            have : a * b * w = (a * w) * (w * b * w) := by
              rw [show (a * w) * (w * b * w) = a * (w * w) * b * w by group, hw2, mul_one]
            rw [this]
            exact U.mul_mem ha (h1 b hb)
          · left
            have : a * b = (a * w) * (w * (b * w) * w) := by
              rw [show (a * w) * (w * (b * w) * w) = a * (w * w) * b * (w * w) by group, hw2,
                mul_one, mul_one]
            rw [this]
            exact U.mul_mem ha (h1 _ hb)
        inv_mem' := by
          intro a ha
          rcases ha with ha | ha
          · exact Or.inl (U.inv_mem ha)
          · right
            have : a⁻¹ * w = w * (a * w)⁻¹ * w := by
              rw [mul_inv_rev, show w * (w⁻¹ * a⁻¹) * w = a⁻¹ * w by group]
            rw [this]
            exact h1 _ (U.inv_mem ha) }
    have hle : U ⊔ Subgroup.zpowers w ≤ H := by
      refine sup_le (fun y hy => Or.inl hy) ?_
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [hw2]; exact U.one_mem)
    exact hle hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : x = (x * w) * w⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers w)))

theorem TorusData.mul_self_of_mul_mem (hU : TorusData L U w) {x : X} (hx : x * w ∈ U) :
    x * x = 1 := by
  have hw2 := hU.w_mul_self
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h := hU.inv _ hx
  rw [hwinv] at h
  have : w * x * (w * w) = w⁻¹ * x⁻¹ := by
    rw [← mul_inv_rev, ← h]
    group
  rw [hw2, mul_one, hwinv] at this
  have := congrArg (w⁻¹ * ·) this
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
  calc x * x = x * x⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel x

end Torus

section General

variable {X : Type*} [Group X]

theorem mul_self_of_isKleinFour' {V : Subgroup X} (hV : IsKleinFour V) {x : X} (hx : x ∈ V) :
    x * x = 1 := by
  have := congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨x, hx⟩ : V))
  rw [hV.exponent_two, pow_two] at this
  exact this

theorem mem_normalizer_of_conj_mem [Finite X] {H : Subgroup X} {g : X}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  let φ : H → H := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
  have hφ : Function.Injective φ := by
    intro y z hyz
    have := congrArg Subtype.val hyz
    change g * y * g⁻¹ = g * z * g⁻¹ at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨_, hx⟩
  have := congrArg Subtype.val hy
  change g * y * g⁻¹ = g * x * g⁻¹ at this
  have hyx : (y : X) = x := by simpa using this
  rw [← hyx]
  exact y.2

theorem eq_one_of_conj_eq_of_orderOf_eq_three {V : Subgroup X} (hV : IsKleinFour V) {z : X}
    (hz : orderOf z = 3) (hzN : z ∈ Subgroup.normalizer (V : Set X))
    (hzC : z ∉ Subgroup.centralizer (V : Set X)) {v : X} (hv : v ∈ V)
    (hzv : z * v * z⁻¹ = v) : v = 1 := by
  by_contra hv1
  have hconj : ∀ x ∈ V, z * x * z⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hzN x).mp hx
  obtain ⟨u, huV, hzu⟩ : ∃ u ∈ V, z * u * z⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * z = z * (z⁻¹ * x * z) := by group
      _ = z * x := by
        congr 1
        have := hcon x hx
        calc z⁻¹ * x * z = z⁻¹ * (z * x * z⁻¹) * z := by rw [this]
          _ = x := by group
  set w := z * u * z⁻¹
  have hwV : w ∈ V := hconj u huV
  have hu1 : u ≠ 1 := fun h1 => hzu (by simp [w, h1])
  have huv : u ≠ v := by
    rintro rfl
    exact hzu hzv
  have hw1 : w ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg (fun y => z⁻¹ * y * z) h1
    simpa [w, mul_assoc] using this
  have hwv : w ≠ v := by
    intro h1
    apply huv
    have := congrArg (fun y => z⁻¹ * y * z) h1
    have h2 : z⁻¹ * v * z = v := by
      calc z⁻¹ * v * z = z⁻¹ * (z * v * z⁻¹) * z := by rw [hzv]
        _ = v := by group
    simpa [w, mul_assoc, h2] using this
  have hwvu : w = v * u := by
    have := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨v, hv⟩) (y := ⟨u, huV⟩)
      (z := ⟨w, hwV⟩) (fun h1 => hv1 (congrArg Subtype.val h1))
      (fun h1 => hu1 (congrArg Subtype.val h1))
      (fun h1 => huv (congrArg Subtype.val h1).symm)
      (fun h1 => hw1 (congrArg Subtype.val h1))
      (fun h1 => hwv (congrArg Subtype.val h1))
      (fun h1 => hzu (congrArg Subtype.val h1))
    exact congrArg Subtype.val this
  have hvv : v * v = 1 := mul_self_of_isKleinFour' hV hv
  have hzw : z * w * z⁻¹ = u := by
    rw [hwvu, show z * (v * u) * z⁻¹ = (z * v * z⁻¹) * (z * u * z⁻¹) by group, hzv]
    change v * w = u
    rw [hwvu, ← mul_assoc, hvv, one_mul]
  have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
  apply hzu
  calc z * u * z⁻¹ = z * (z * w * z⁻¹) * z⁻¹ := by rw [hzw]
    _ = z ^ 3 * u * (z ^ 3)⁻¹ := by simp only [w]; rw [pow_three]; group
    _ = u := by rw [hz3]; group

theorem map_conj_mul (H : Subgroup X) (a b : X) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (H : Subgroup X) : H.map (MulAut.conj (1 : X)).toMonoidHom = H := by
  conv_rhs => rw [← Subgroup.map_id H]
  congr 1
  ext x
  simp

end General

namespace PSL2Facts

variable {G : Type*} [Group G] {F : Subgroup G} {p f : ℕ}

theorem card_sylow_two [Finite G] (hF : PSL2Facts F p f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (P : Sylow 2 F) : Nat.card (P : Subgroup F) = 4 := by
  have hqodd : Odd (p ^ f) := hF.odd_p.pow
  have hq1 : 1 < p ^ f := by have := hF.seven_le; omega
  rw [Sylow.card_eq_multiplicity, hF.card,
    (factorization_two_psl2_card_eq_two_iff hqodd hq1).mpr h8]
  norm_num

theorem card_dvd_four [Finite G] (hF : PSL2Facts F p f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {W : Subgroup G} (hWF : W ≤ F) (hW : IsPGroup 2 W) : Nat.card W ∣ 4 := by
  have e : W.subgroupOf F ≃* W := Subgroup.subgroupOfEquivOfLe hWF
  obtain ⟨P, hP⟩ := (hW.of_equiv e.symm).exists_le_sylow
  rw [← Nat.card_congr e.toEquiv, ← hF.card_sylow_two h8 P]
  exact Subgroup.card_dvd_of_le hP

theorem orderOf_ne_four (hF : PSL2Facts F p f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {x : G} (hx : x ∈ F) : orderOf x ≠ 4 := by
  intro hx4
  have hv2 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow' x (by norm_num), hx4]
    norm_num
  obtain ⟨U, w, hU, hvU, hcard⟩ := hF.even_torus (x ^ 2) (F.pow_mem hx 2) hv2
  have hxC : x ∈ F ⊓ Subgroup.centralizer ({x ^ 2} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr (by rw [pow_two, mul_assoc])⟩
  rw [hU.centralizer_eq hvU hv2, hU.mem_sup_iff] at hxC
  rcases hxC with hxU | hxU
  · have h4 : 4 ∣ Nat.card U := hx4 ▸ Subgroup.orderOf_dvd_natCard U hxU
    omega
  · have hxx : x ^ 2 = 1 := by
      rw [pow_two]
      exact hU.mul_self_of_mul_mem hxU
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hxx
    rw [hx4] at h2
    omega

theorem isKleinFour_of_card [Finite G] (hF : PSL2Facts F p f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {V : Subgroup G} (hVF : V ≤ F) (hV : Nat.card V = 4) : IsKleinFour V := by
  refine ⟨hV, ?_⟩
  have hpow : ∀ y : V, y ^ 2 = 1 := by
    intro y
    have hd : orderOf y ∣ 4 := hV ▸ orderOf_dvd_natCard y
    have hne : orderOf y ≠ 4 := by
      rw [← Subgroup.orderOf_coe]
      exact hF.orderOf_ne_four h8 (hVF y.2)
    have : orderOf y ∣ 2 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4] at hd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      interval_cases k
      · rw [hk']; exact one_dvd 2
      · rw [hk']; norm_num
      · exact absurd (by rw [hk']; norm_num) hne
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdvd : Monoid.exponent V ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton V := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := V)
    rw [hV] at this
    omega
  · exact h2

theorem card_mulAut_of_isKleinFour (V : Type*) [Group V] [IsKleinFour V] :
    Nat.card (MulAut V) = 6 := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four (G := V)]; decide)
  let : Fintype V := Fintype.ofFinite V
  let φ : MulAut V →* Equiv.Perm {v : V // v ≠ 1} :=
    { toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rfl }
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun σ => ?_⟩
    · ext v
      by_cases hv : v = 1
      · simp [hv]
      · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
    · let e := Equiv.Perm.ofSubtype σ
      have he : e 1 = 1 := Equiv.Perm.ofSubtype_apply_of_not_mem σ (by simp)
      refine ⟨IsKleinFour.mulEquiv e he, ?_⟩
      ext v
      exact Equiv.Perm.ofSubtype_apply_coe σ v
  have hthree : Fintype.card {v : V // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, IsKleinFour.card_four']
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_perm,
    hthree]
  decide

theorem card_inf_normalizer [Finite G] (hF : PSL2Facts F p f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup G} (hVF : V ≤ F) (hV : IsKleinFour V) :
    Nat.card (F ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) = 12 := by
  classical
  set N₀ := F ⊓ Subgroup.normalizer (V : Set G) with hN₀
  have hVN₀ : V ≤ N₀ := le_inf hVF Subgroup.le_normalizer
  let := conjAct N₀ V inf_le_right
  let φ : N₀ →* MulAut V := MulDistribMulAction.toMulAut N₀ V
  have hker : φ.ker = V.subgroupOf N₀ := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      have hnC : (n : G) ∈ F ⊓ Subgroup.centralizer (V : Set G) := by
        refine ⟨n.2.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨v, hv⟩)
        change (n : G) * v * (n : G)⁻¹ = v at this
        calc v * n = ((n : G) * v * (n : G)⁻¹) * n := by rw [this]
          _ = n * v := by group
      rw [hF.kleinFour V hVF hV] at hnC
      exact hnC
    · intro hn
      ext v
      change (n : G) * v * (n : G)⁻¹ = v
      have := hV.isMulCommutative.is_comm.comm ⟨(n : G), hn⟩ v
      have := congrArg Subtype.val this
      change (n : G) * v = v * n at this
      rw [this, mul_inv_cancel_right]
  have hcard : Nat.card N₀ = 4 * Nat.card φ.range := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN₀).toEquiv,
      hV.card_four] at h1
    exact h1.symm
  have hdvd6 : Nat.card φ.range ∣ 6 := by
    rw [← card_mulAut_of_isKleinFour V]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ Nat.card φ.range := by
    rintro ⟨k, hk⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := N₀) 2 (n := 3)
      (by rw [hcard, hk]; exact ⟨k, by ring⟩)
    have hKF : K.map N₀.subtype ≤ F := (Subgroup.map_subtype_le K).trans inf_le_left
    have hK2 : IsPGroup 2 (K.map N₀.subtype) :=
      (IsPGroup.of_card hK).map N₀.subtype
    have := hF.card_dvd_four h8 hKF hK2
    rw [Subgroup.card_map_of_injective N₀.subtype_injective, hK] at this
    omega
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    rw [h1] at hcard
    have hN₀V : N₀ = V := (Subgroup.eq_of_le_of_card_ge hVN₀ (by rw [hcard, hV.card_four])).symm
    have hfac : (Nat.card F).factorization 2 = 2 := by
      have hqodd : Odd (p ^ f) := hF.odd_p.pow
      have hq1 : 1 < p ^ f := by have := hF.seven_le; omega
      rw [hF.card, (factorization_two_psl2_card_eq_two_iff hqodd hq1).mpr h8]
    have hVcard : Nat.card (V.subgroupOf F) = 2 ^ (Nat.card F).factorization 2 := by
      rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv, hV.card_four]
      norm_num
    let P : Sylow 2 F := Sylow.ofCard (V.subgroupOf F) hVcard
    have hPV : (P : Subgroup F) = V.subgroupOf F := rfl
    have hPab : IsMulCommutative (P : Subgroup F) := by
      rw [hPV]
      exact ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
        have := hV.isMulCommutative.is_comm.comm ⟨((a : F) : G), a.2⟩ ⟨((b : F) : G), b.2⟩
        have h2 := congrArg Subtype.val this
        exact h2))⟩⟩
    have hNC : Subgroup.normalizer ((P : Subgroup F) : Set F) ≤
        Subgroup.centralizer ((P : Subgroup F) : Set F) := by
      intro n hn
      have hnN₀ : (n : G) ∈ N₀ := by
        refine ⟨n.2, mem_normalizer_of_conj_mem fun v hv => ?_⟩
        have := (Subgroup.mem_normalizer_iff.mp hn ⟨v, hVF hv⟩).mp (by
          rw [hPV, Subgroup.mem_subgroupOf]
          exact hv)
        rw [hPV, Subgroup.mem_subgroupOf] at this
        exact this
      rw [hN₀V] at hnN₀
      have hnP : n ∈ (P : Subgroup F) := by
        rw [hPV, Subgroup.mem_subgroupOf]
        exact hnN₀
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact hPab.is_comm.comm ⟨m, hm⟩ ⟨n, hnP⟩ |> congrArg Subtype.val
    have := hF.simple
    have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
    have hcardP : Nat.card (P : Subgroup F) = 4 := by
      rw [hPV, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv, hV.card_four]
    have hFbig : 4 < Nat.card F := by
      rw [hF.card]
      have h7 := hF.seven_le
      have : 7 * (7 ^ 2 - 1) ≤ p ^ f * ((p ^ f) ^ 2 - 1) :=
        Nat.mul_le_mul h7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h7 2) 1)
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hNC).ker with
      hb | ht
    · have := hcomp.card_mul_card
      rw [hb, Subgroup.card_bot, one_mul, hcardP] at this
      omega
    · have := hcomp.card_mul_card
      rw [ht, Subgroup.card_top, hcardP] at this
      omega
  have h3 : Nat.card φ.range = 3 := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases (Nat.card φ.range) <;> simp_all
  rw [hcard, h3]

theorem exists_orderOf_eq_three [Finite G] (hF : PSL2Facts F p f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup G} (hVF : V ≤ F) (hV : IsKleinFour V) :
    ∃ z ∈ F, orderOf z = 3 ∧ z ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ v ∈ V, z * v * z⁻¹ = v → v = 1 := by
  set N₀ := F ⊓ Subgroup.normalizer (V : Set G)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N₀) 3
    (by rw [hF.card_inf_normalizer h8 hVF hV]; norm_num)
  have hz' : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzC : (z : G) ∉ Subgroup.centralizer (V : Set G) := by
    intro hzC
    have : (z : G) ∈ F ⊓ Subgroup.centralizer (V : Set G) := ⟨z.2.1, hzC⟩
    rw [hF.kleinFour V hVF hV] at this
    have h3 : orderOf (z : G) ∣ 4 := hV.card_four ▸ Subgroup.orderOf_dvd_natCard V this
    rw [hz'] at h3
    omega
  exact ⟨z, z.2.1, hz', z.2.2, fun v hv hzv =>
    eq_one_of_conj_eq_of_orderOf_eq_three hV hz' z.2.2 hzC hv hzv⟩

end PSL2Facts

theorem JTHyp.exists_not_commute {G : Type} [Group G] [Finite G] (h : JTHyp G) (S : Sylow 2 G)
    {z : G} (hzS : z ∈ S) (hz1 : z ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * z ≠ z * n := by
  by_contra hcon
  push Not at hcon
  obtain ⟨H, -, hH⟩ := exists_normal_index_eq_of_commute_normalizer S (h.abelian_sylow S) hzS
    hz1 hcon
  exact h.index_ne_two H hH

theorem disjoint_orbit_of_not_mem {A X : Type*} [Group A] [MulAction A X] {x y : X}
    (hy : y ∉ MulAction.orbit A x) : Disjoint (MulAction.orbit A x) (MulAction.orbit A y) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  exact hy (MulAction.orbit_eq_iff.mp ((MulAction.orbit_eq_iff.mpr h2).symm.trans
    (MulAction.orbit_eq_iff.mpr h1)))

theorem orbit_eq_of_ncard_eq_seven {A X : Type*} [Group A] [MulAction A X] [Finite X]
    (T : Set X) (hT : T.ncard = 7) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hodd : ∀ x ∈ T, Odd (MulAction.orbit A x).ncard ∧ (MulAction.orbit A x).ncard ≠ 1) :
    ∀ x ∈ T, MulAction.orbit A x = T := by
  have hsub : ∀ x ∈ T, MulAction.orbit A x ⊆ T := by
    rintro x hx _ ⟨a, rfl⟩
    exact hTinv a x hx
  have hge : ∀ x ∈ T, 3 ≤ (MulAction.orbit A x).ncard := by
    intro x hx
    obtain ⟨⟨k, hk⟩, h1⟩ := hodd x hx
    omega
  intro x hx
  by_contra hne
  obtain ⟨y, hyT, hyx⟩ : ∃ y ∈ T, y ∉ MulAction.orbit A x := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm (hsub x hx) h)
  have hxy := Set.ncard_union_eq (disjoint_orbit_of_not_mem hyx)
  have hxyle : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (hsub x hx) (hsub y hyT))
  have hx3 : (MulAction.orbit A x).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd x hx
    have := hge y hyT
    omega
  have hy3 : (MulAction.orbit A y).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd y hyT
    have := hge x hx
    omega
  obtain ⟨z, hzT, hzxy⟩ : ∃ z ∈ T, z ∉ MulAction.orbit A x ∪ MulAction.orbit A y := by
    by_contra h
    push Not at h
    have := Set.ncard_le_ncard h
    omega
  have hdz : Disjoint (MulAction.orbit A x ∪ MulAction.orbit A y) (MulAction.orbit A z) :=
    Disjoint.union_left (disjoint_orbit_of_not_mem fun h => hzxy (Or.inl h))
      (disjoint_orbit_of_not_mem fun h => hzxy (Or.inr h))
  have hall := Set.ncard_union_eq hdz
  have hallle : (MulAction.orbit A x ∪ MulAction.orbit A y ∪ MulAction.orbit A z).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (Set.union_subset (hsub x hx) (hsub y hyT))
      (hsub z hzT))
  have := hge z hzT
  omega

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G)

theorem mod_eight
    (hp : h.p ≠ 2) : h.q % 8 = 3 ∨ h.q % 8 = 5 :=
  (h.facts hp).mod_eight fun P _ hP => by
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have := h.abelian_sylow S
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hab := congrArg Subtype.val (this.is_comm.comm ⟨a, hS a.2⟩ ⟨b, hS b.2⟩)
    exact hab

theorem relIndex_inf_F (S : Sylow 2 G) (htS : h.t ∈ S) :
    ((S : Subgroup G) ⊓ h.F).relIndex S = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨h.t, htS⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbS : (b : G) ∈ (S : Subgroup G) := b.2
  have hbC := h.sylow_le_centralizer S htS hbS
  by_cases hb : (b : G) ∈ h.F
  · refine Or.inr ⟨⟨hbS, hb⟩, fun ⟨_, hbt⟩ => h.t_not_mem ?_⟩
    have : h.t = (b : G)⁻¹ * (b * h.t) := by group
    rw [this]
    exact h.F.mul_mem (h.F.inv_mem hb) hbt
  · refine Or.inl ⟨⟨(S : Subgroup G).mul_mem hbS htS, ?_⟩, fun ⟨_, hb'⟩ => hb hb'⟩
    rcases h.mem_centralizer_t.mp hbC with hb' | hb'
    · exact absurd hb' hb
    · rw [h.commute_of_mem hbC]
      exact hb'

theorem card_inf_F
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) = 4 := by
  have hF := h.facts hp
  have h8 := h.mod_eight hp
  set V := (S : Subgroup G) ⊓ h.F with hVdef
  have hVF : V ≤ h.F := inf_le_right
  have hVp : IsPGroup 2 V := S.isPGroup'.to_le inf_le_left
  have e : V.subgroupOf h.F ≃* V := Subgroup.subgroupOfEquivOfLe hVF
  obtain ⟨P, hP⟩ := (hVp.of_equiv e.symm).exists_le_sylow
  set W := (P : Subgroup h.F).map h.F.subtype
  have hWcard : Nat.card W = 4 := by
    rw [Subgroup.card_map_of_injective h.F.subtype_injective]
    exact hF.card_sylow_two h8 P
  have hVW : V ≤ W := fun x hx => ⟨⟨x, hVF hx⟩, hP hx, rfl⟩
  have hWF : W ≤ h.F := Subgroup.map_subtype_le _
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  have hWN : W ≤ Subgroup.normalizer ((Subgroup.zpowers h.t : Subgroup G) : Set G) := by
    rw [normalizer_zpowers_of_orderOf_eq_two h.orderOf_t]
    exact hWF.trans h.le_centralizer
  have hSW : (S : Subgroup G) ≤ Subgroup.zpowers h.t ⊔ W := by
    intro x hx
    rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer S htS hx) with hxF | hxF
    · exact Subgroup.mem_sup_right (hVW ⟨hx, hxF⟩)
    · have : x = h.t⁻¹ * (h.t * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _
        (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_right (hVW ⟨(S : Subgroup G).mul_mem htS hx, hxF⟩))
  have heq := S.is_maximal' (IsPGroup.to_sup_of_normal_left' ht2 (P.isPGroup'.map _) hWN) hSW
  have hWV : W ≤ V := fun x hx => ⟨heq ▸ Subgroup.mem_sup_right hx, hWF hx⟩
  rw [le_antisymm hVW hWV]
  exact hWcard

theorem card_sylow
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card (S : Subgroup G) = 8 := by
  have h1 := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓ h.F) S
  rw [h.relIndex_inf_F S htS, inf_assoc, inf_comm h.F, ← inf_assoc, inf_idem,
    h.card_inf_F hp S htS] at h1
  omega

theorem isKleinFour_inf_F
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    IsKleinFour ((S : Subgroup G) ⊓ h.F : Subgroup G) :=
  (h.facts hp).isKleinFour_of_card (h.mod_eight hp) inf_le_right (h.card_inf_F hp S htS)

theorem _root_.CFSG.Walter.JT.mul_self_of_isKleinFour {X : Type*} [Group X] {V : Subgroup X}
    (hV : IsKleinFour V) {x : X} (hx : x ∈ V) : x * x = 1 := by
  have := congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨x, hx⟩ : V))
  rw [hV.exponent_two, pow_two] at this
  exact this

theorem mul_self_of_mem_sylow
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) {x : G}
    (hx : x ∈ S) : x * x = 1 := by
  have hV := h.isKleinFour_inf_F hp S htS
  rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer S htS hx) with hxF | hxF
  · exact mul_self_of_isKleinFour hV ⟨hx, hxF⟩
  · have hy := mul_self_of_isKleinFour hV ⟨(S : Subgroup G).mul_mem htS hx, hxF⟩
    have hc : h.t * x = x * h.t := (h.commute_of_mem (h.sylow_le_centralizer S htS hx)).symm
    calc x * x = (h.t * h.t) * (x * x) := by rw [h.t_mul_t, one_mul]
      _ = h.t * (h.t * x) * x := by group
      _ = h.t * (x * h.t) * x := by rw [hc]
      _ = (h.t * x) * (h.t * x) := by group
      _ = 1 := hy

theorem isElementaryAbelian_sylow
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    IsElementaryAbelian 2 (S : Subgroup G) := by
  have := h.abelian_sylow S
  refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_two]
  exact h.mul_self_of_mem_sylow hp S htS x.2

theorem centralizer_sylow
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    Subgroup.centralizer ((S : Subgroup G) : Set G) = S := by
  have hab := h.abelian_sylow S
  have hV := h.isKleinFour_inf_F hp S htS
  have hCV := (h.facts hp).kleinFour _ inf_le_right hV
  apply le_antisymm
  · intro x hx
    have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx h.t htS).symm)
    have hcV : ∀ y, y ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        y ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
      fun y hy => Subgroup.centralizer_le (fun z hz => hz.1) hy
    rcases h.mem_centralizer_t.mp hxt with hxF | hxF
    · have : x ∈ h.F ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
        ⟨hxF, hcV x hx⟩
      rw [hCV] at this
      exact this.1
    · have htC : h.t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨h.t, htS⟩)
      have : h.t * x ∈ h.F ⊓
          Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
        ⟨hxF, hcV _ (Subgroup.mul_mem _ htC hx)⟩
      rw [hCV] at this
      have hx' : x = h.t * (h.t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [hx']
      exact (S : Subgroup G).mul_mem htS this.1
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem exists_conj_of_mem_sylow
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) {x y : G}
    (hx : x ∈ S) (hx1 : x ≠ 1) (hy : y ∈ S) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  have hab := h.abelian_sylow S
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let := conjAct N S le_rfl
  set T : Set (S : Subgroup G) := {z | z ≠ 1}
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set (S : Subgroup G)) \ {1} := by
      ext
      simp [T]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      h.card_sylow hp S htS]
  have hTinv : ∀ a : N, ∀ z ∈ T, a • z ∈ T := by
    intro a z hz h1
    apply hz
    have h1' : ((a • z : (S : Subgroup G)) : G) = 1 := congrArg Subtype.val h1
    change (a : G) * z * (a : G)⁻¹ = 1 at h1'
    apply Subtype.ext
    change (z : G) = 1
    have := congrArg (fun w => (a : G)⁻¹ * w * a) h1'
    simpa [mul_assoc] using this
  have horbit : ∀ z ∈ T, MulAction.orbit N z = T := by
    apply orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro z hz
    rw [← MulAction.index_stabilizer]
    have hle : (S : Subgroup G).subgroupOf N ≤ MulAction.stabilizer N z := by
      intro s hs
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      change (s : G) * z * (s : G)⁻¹ = z
      have := congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ z)
      change (s : G) * z = z * s at this
      rw [this, mul_inv_cancel_right]
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.index_dvd_of_le hle
      have h2 : ((S : Subgroup G).subgroupOf N).index ∣ (S : Subgroup G).index :=
        Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact fun h3 => S.not_dvd_index (h3.trans (h1.trans h2))
    · intro h1
      rw [Subgroup.index_eq_one] at h1
      obtain ⟨n, hn, hnz⟩ := h.exists_not_commute S z.2 (fun h0 => hz (Subtype.ext h0))
      apply hnz
      have hmem : (⟨n, hn⟩ : N) ∈ MulAction.stabilizer N z := by
        rw [h1]
        exact Subgroup.mem_top _
      have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hmem)
      change n * z * n⁻¹ = z at this
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [this]
  have hxT : (⟨x, hx⟩ : (S : Subgroup G)) ∈ T := fun h0 => hx1 (congrArg Subtype.val h0)
  have hyT : (⟨y, hy⟩ : (S : Subgroup G)) ∈ T := fun h0 => hy1 (congrArg Subtype.val h0)
  rw [← horbit _ hxT] at hyT
  obtain ⟨n, hn⟩ := hyT
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

theorem exists_conj_eq_t
    (hp : h.p ≠ 2) {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g * x * g⁻¹ = h.t := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨S', hS'⟩ := hx2.exists_le_sylow
  obtain ⟨S, hS⟩ := ht2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have htS : h.t ∈ S := hS (Subgroup.mem_zpowers _)
  have hgx : g * x * g⁻¹ ∈ S := by
    rw [← hg]
    change g * x * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G)
      (hS' (Subgroup.mem_zpowers x))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    have := congrArg (fun w => g⁻¹ * w * g) h1
    simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at this
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨n, -, hn⟩ := h.exists_conj_of_mem_sylow hp S htS hgx hgx1 htS h.t_ne_one
  exact ⟨n * g, by rw [← hn]; group⟩

theorem isConj_of_orderOf_eq_two
    (hp : h.p ≠ 2) {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hx
  obtain ⟨k, hk⟩ := h.exists_conj_eq_t hp hy
  refine isConj_iff.mpr ⟨k⁻¹ * g, ?_⟩
  rw [show k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group, hg, ← hk]
  group

theorem mem_normalizer_sylow_of_mem_F (S : Sylow 2 G) (htS : h.t ∈ S) {y : G} (hyF : y ∈ h.F)
    (hyN : y ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun s hs => ?_
  have hc := h.commute_of_mem_F hyF
  rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer S htS hs) with hsF | hsF
  · exact ((Subgroup.mem_normalizer_iff.mp hyN s).mp ⟨hs, hsF⟩).1
  · have h1 := ((Subgroup.mem_normalizer_iff.mp hyN _).mp ⟨(S : Subgroup G).mul_mem htS hs,
      hsF⟩).1
    have : y * s * y⁻¹ = h.t * (y * (h.t * s) * y⁻¹) := by
      calc y * s * y⁻¹ = y * (h.t * (h.t * s)) * y⁻¹ := by
            rw [← mul_assoc h.t, h.t_mul_t, one_mul]
        _ = (y * h.t) * (h.t * s) * y⁻¹ := by group
        _ = h.t * (y * (h.t * s) * y⁻¹) := by rw [hc]; group
    rw [this]
    exact (S : Subgroup G).mul_mem htS h1

theorem mem_normalizer_inf_F_of_mem_F (S : Sylow 2 G) {y : G} (hyF : y ∈ h.F)
    (hyN : y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hyN x).mp hx.1,
      h.F.mul_mem (h.F.mul_mem hyF hx.2) (h.F.inv_mem hyF)⟩

theorem card_normalizer_inf_centralizer
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = 24 := by
  set V := (S : Subgroup G) ⊓ h.F
  set N₀ := h.F ⊓ Subgroup.normalizer (V : Set G)
  set M := Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({h.t} : Set G)
  have hN₀ : Nat.card N₀ = 12 := (h.facts hp).card_inf_normalizer (h.mod_eight hp)
    inf_le_right (h.isKleinFour_inf_F hp S htS)
  have hN₀M : N₀ ≤ M := fun y hy =>
    ⟨h.mem_normalizer_sylow_of_mem_F S htS hy.1 hy.2, h.le_centralizer hy.1⟩
  have htN : h.t ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.le_normalizer htS
  have hidx : N₀.relIndex M = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨h.t, htN, h.t_mem_centralizer⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hbN := b.2.1
    have hbC := b.2.2
    by_cases hbF : (b : G) ∈ h.F
    · refine Or.inr ⟨⟨hbF, h.mem_normalizer_inf_F_of_mem_F S hbF hbN⟩, fun hbt => h.t_not_mem ?_⟩
      have : h.t = (b : G)⁻¹ * (b * h.t) := by group
      rw [this]
      exact h.F.mul_mem (h.F.inv_mem hbF) hbt.1
    · have hbtF : (b : G) * h.t ∈ h.F := by
        rcases h.mem_centralizer_t.mp hbC with hb' | hb'
        · exact absurd hb' hbF
        · rw [h.commute_of_mem hbC]
          exact hb'
      refine Or.inl ⟨⟨hbtF, h.mem_normalizer_inf_F_of_mem_F S hbtF
        (Subgroup.mul_mem _ hbN htN)⟩, fun hb' => hbF hb'.1⟩
  have h1 := Subgroup.relIndex_mul_card N₀ M
  rw [hidx, inf_eq_left.mpr hN₀M, hN₀] at h1
  omega

theorem index_sylow_normalizer
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 21 := by
  classical
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let := conjAct N S le_rfl
  set t' : (S : Subgroup G) := ⟨h.t, htS⟩
  have hstab : MulAction.stabilizer N t' = (Subgroup.centralizer ({h.t} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hn
      have := congrArg Subtype.val hn
      change (n : G) * h.t * (n : G)⁻¹ = h.t at this
      calc (n : G) * h.t = ((n : G) * h.t * (n : G)⁻¹) * n := by group
        _ = h.t * n := by rw [this]
    · intro hn
      apply Subtype.ext
      change (n : G) * h.t * (n : G)⁻¹ = h.t
      rw [hn, mul_inv_cancel_right]
  have horbit : MulAction.orbit N t' = {z | z ≠ 1} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩ h1
      have := congrArg Subtype.val h1
      change (n : G) * h.t * (n : G)⁻¹ = 1 at this
      apply h.t_ne_one
      have := congrArg (fun w => (n : G)⁻¹ * w * n) this
      simpa [mul_assoc] using this
    · intro hz
      obtain ⟨n, hn, hnz⟩ := h.exists_conj_of_mem_sylow hp S htS htS h.t_ne_one z.2
        (fun h0 => hz (Subtype.ext h0))
      exact ⟨⟨n, hn⟩, Subtype.ext hnz⟩
  have h7 : (MulAction.orbit N t').ncard = 7 := by
    have : ({z | z ≠ 1} : Set (S : Subgroup G)) = (Set.univ : Set (S : Subgroup G)) \ {1} := by
      ext
      simp
    rw [horbit, this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      h.card_sylow hp S htS]
  have hidx : (MulAction.stabilizer N t').index = 7 := by
    rw [MulAction.index_stabilizer, h7]
  have hstabcard : Nat.card (MulAction.stabilizer N t') = 24 := by
    rw [hstab, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm,
      h.card_normalizer_inf_centralizer hp S htS]
  have hNcard : Nat.card N = 168 := by
    have := (MulAction.stabilizer N t').card_mul_index
    rw [hstabcard, hidx] at this
    exact this.symm
  have hScard : Nat.card ((S : Subgroup G).subgroupOf N) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
      h.card_sylow hp S htS]
  have := ((S : Subgroup G).subgroupOf N).card_mul_index
  rw [hScard, hNcard] at this
  omega

theorem not_isCyclic_normalizer_quotient
    (hp : h.p ≠ 2) (S : Sylow 2 G) (htS : h.t ∈ S) :
    ¬ IsCyclic (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))) := by
  intro hcyc
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  have hab := h.abelian_sylow S
  obtain ⟨z, hzF, hz3, hzN, -⟩ := (h.facts hp).exists_orderOf_eq_three (h.mod_eight hp)
    inf_le_right (h.isKleinFour_inf_F hp S htS)
  have hzNS : z ∈ N := h.mem_normalizer_sylow_of_mem_F S htS hzF hzN
  have hzt : z * h.t = h.t * z := h.commute_of_mem_F hzF
  have hzC : z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    obtain ⟨n, hn, rfl⟩ := h.exists_conj_of_mem_sylow hp S htS htS h.t_ne_one hs hs1
    have hcomm := mul_comm' (QuotientGroup.mk (⟨n, hn⟩ : N) : N ⧸ (S : Subgroup G).subgroupOf N)
      (QuotientGroup.mk (⟨z, hzNS⟩ : N))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hcomm
    set c : G := (n * z)⁻¹ * (z * n)
    have hcS : c ∈ (S : Subgroup G) := by simpa [c] using hcomm
    have hzn : z * n = n * z * c := by simp only [c]; group
    have hct : c * h.t = h.t * c :=
      congrArg Subtype.val (hab.is_comm.comm ⟨c, hcS⟩ ⟨h.t, htS⟩)
    symm
    calc z * (n * h.t * n⁻¹) = (z * n) * h.t * n⁻¹ := by group
      _ = (n * z * c) * h.t * n⁻¹ := by rw [hzn]
      _ = n * z * (c * h.t) * n⁻¹ := by group
      _ = n * z * (h.t * c) * n⁻¹ := by rw [hct]
      _ = n * (z * h.t) * c * n⁻¹ := by group
      _ = n * (h.t * z) * c * n⁻¹ := by rw [hzt]
      _ = n * h.t * n⁻¹ * (n * z * c * n⁻¹) := by group
      _ = n * h.t * n⁻¹ * (z * n * n⁻¹) := by rw [← hzn]
      _ = n * h.t * n⁻¹ * z := by group
  have : z ∈ (S : Subgroup G) := by
    rw [← h.centralizer_sylow hp S htS]
    exact hzC
  have h8 : orderOf z ∣ 8 := h.card_sylow hp S htS ▸ Subgroup.orderOf_dvd_natCard _ this
  rw [hz3] at h8
  omega

theorem _root_.CFSG.Walter.JT.orderOf_eq_two_of_isKleinFour {X : Type*} [Group X]
    {V : Subgroup X} (hV : IsKleinFour V) {x : X} (hx : x ∈ V) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hx) hx1

theorem exists_conj_kleinFour_eq
    (hp : h.p ≠ 2) {v : G} (hvF : v ∈ h.F) (hv : v * v = 1)
    (hv1 : v ≠ 1) {W : Subgroup G} (hW : IsKleinFour W) :
    ∃ g : G, W.map (MulAut.conj g).toMonoidHom =
      GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hv
        (h.commute_of_mem_F hvF).symm := by
  classical
  have hcard4 : Nat.card W = 4 := hW.card_four
  have : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard4]
    norm_num
  obtain ⟨⟨w, hwW⟩, hw1⟩ := exists_ne (1 : W)
  have hw1' : w ≠ 1 := fun h0 => hw1 (Subtype.ext h0)
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp (orderOf_eq_two_of_isKleinFour hW hwW hw1')
  set W' := W.map (MulAut.conj g).toMonoidHom
  have eW : W ≃* W' := W.equivMapOfInjective _ (MulAut.conj g).injective
  have hW' : IsKleinFour W' := ⟨by rw [← Nat.card_congr eW.toEquiv, hcard4],
    by rw [← Monoid.exponent_eq_of_mulEquiv eW, hW.exponent_two]⟩
  have htW' : h.t ∈ W' := ⟨w, hwW, by simp [MulAut.conj_apply, hg]⟩
  obtain ⟨x, hxW', hx1, hxt⟩ : ∃ x ∈ W', x ≠ 1 ∧ x ≠ h.t := by
    by_contra hcon
    push Not at hcon
    have hsub : (W' : Set G) ⊆ {1, h.t} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm h.t_ne_one), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      hW'.card_four] at this
    omega
  have hxC : x ∈ Subgroup.centralizer ({h.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hW'.isMulCommutative.is_comm.comm ⟨x, hxW'⟩ ⟨h.t, htW'⟩))
  obtain ⟨y, hyF, hyW', hy1⟩ : ∃ y ∈ h.F, y ∈ W' ∧ y ≠ 1 := by
    rcases h.mem_centralizer_t.mp hxC with hxF | hxF
    · exact ⟨x, hxF, hxW', hx1⟩
    · refine ⟨h.t * x, hxF, W'.mul_mem htW' hxW', fun h1 => hxt ?_⟩
      have : x = h.t⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, h.t_inv]
  obtain ⟨f, hfF, hfy⟩ := (h.facts hp).isConj y hyF v hvF
    (orderOf_eq_two_of_isKleinFour hW' hyW' hy1) (orderOf_eq_prime (by rw [pow_two]; exact hv) hv1)
  set T₀ := GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hv
    (h.commute_of_mem_F hvF).symm
  have hT₀ : IsKleinFour T₀ := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _
    _ _ h.t_ne_one hv1 (fun h0 => h.t_not_mem (h0 ▸ hvF)) _
  set W'' := W'.map (MulAut.conj f).toMonoidHom
  have hftf : f * h.t * f⁻¹ = h.t := by rw [h.commute_of_mem_F hfF]; group
  have htW'' : h.t ∈ W'' := ⟨h.t, htW', by simp [MulAut.conj_apply, hftf]⟩
  have hvW'' : v ∈ W'' := ⟨y, hyW', by simp [MulAut.conj_apply, hfy]⟩
  have hT₀W'' : T₀ ≤ W'' := by
    intro x hx
    change x ∈ ({h.t * v, h.t, v, 1} : Set G) at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact W''.mul_mem htW'' hvW''
    · exact htW''
    · exact hvW''
    · exact W''.one_mem
  have hcard'' : Nat.card W'' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj f).injective, hW'.card_four]
  refine ⟨f * g, ?_⟩
  have hmap : W.map (MulAut.conj (f * g)).toMonoidHom = W'' := map_conj_mul W f g
  rw [hmap]
  exact (Subgroup.eq_of_le_of_card_ge hT₀W'' (by rw [hcard'', hT₀.card_four])).symm

end JTHyp

theorem lemma_2_1
    {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp : h.p ≠ 2) :
    (h.q % 8 = 3 ∨ h.q % 8 = 5) ∧
    (∀ S : Sylow 2 G, IsElementaryAbelian 2 (S : Subgroup G) ∧ Nat.card (S : Subgroup G) = 8) ∧
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    (∀ S : Sylow 2 G, Subgroup.centralizer ((S : Subgroup G) : Set G) = S) ∧
    (∀ S : Sylow 2 G,
      ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 21 ∧
      ¬ IsCyclic (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
        (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)))) ∧
    (∀ V W : Subgroup G, IsKleinFour V → IsKleinFour W →
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom = W) := by
  have hconjS : ∀ S : Sylow 2 G, ∃ g : G, (h.conj g).t ∈ S := by
    intro S
    have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, h.orderOf_t, pow_one])
    obtain ⟨S₀, hS₀⟩ := ht2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
    refine ⟨g, ?_⟩
    rw [← hg, JTHyp.conj_t]
    change g * h.t * g⁻¹ ∈ MulAut.conj g • (S₀ : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul h.t (MulAut.conj g) (S₀ : Subgroup G)
      (hS₀ (Subgroup.mem_zpowers h.t))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  refine ⟨h.mod_eight hp, fun S => ?_, fun x y hx hy => h.isConj_of_orderOf_eq_two hp hx hy,
    fun S => ?_, fun S => ?_, fun V W hV hW => ?_⟩
  · obtain ⟨g, hg⟩ := hconjS S
    exact ⟨(h.conj g).isElementaryAbelian_sylow hp S hg, (h.conj g).card_sylow hp S hg⟩
  · obtain ⟨g, hg⟩ := hconjS S
    exact (h.conj g).centralizer_sylow hp S hg
  · obtain ⟨g, hg⟩ := hconjS S
    exact ⟨(h.conj g).index_sylow_normalizer hp S hg,
      (h.conj g).not_isCyclic_normalizer_quotient hp S hg⟩
  ·
    have hF := h.facts hp
    obtain ⟨U, w, hU, -⟩ := hF.odd_torus
    have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ U.one_mem)
    obtain ⟨g₁, hg₁⟩ := h.exists_conj_kleinFour_eq hp hU.w_mem hU.w_mul_self hw1 hV
    obtain ⟨g₂, hg₂⟩ := h.exists_conj_kleinFour_eq hp hU.w_mem hU.w_mul_self hw1 hW
    refine ⟨g₂⁻¹ * g₁, ?_⟩
    rw [map_conj_mul, hg₁, ← hg₂, ← map_conj_mul, inv_mul_cancel, map_conj_one]

end CFSG.Walter.JT
