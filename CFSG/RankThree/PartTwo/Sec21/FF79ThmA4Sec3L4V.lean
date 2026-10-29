module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4In
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem v_card_sup_le {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) ≤ Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))

theorem v_sup_eq_of_index_three {M P : Subgroup G} (hMP : M ≤ P) (hc : Nat.card P = 3 * Nat.card M)
    {c : G} (hcP : c ∈ P) (hcM : c ∉ M) : M ⊔ Subgroup.zpowers c = P := by
  have hle : M ⊔ Subgroup.zpowers c ≤ P :=
    sup_le hMP ((Subgroup.zpowers_le).mpr hcP)
  have h1 : Nat.card M ∣ Nat.card (M ⊔ Subgroup.zpowers c : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card (M ⊔ Subgroup.zpowers c : Subgroup G) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le hle
  obtain ⟨s, hs⟩ := h1
  have hMpos : 0 < Nat.card M := Nat.card_pos
  rw [hs, hc] at h2
  have h3 : s ∣ 3 := by
    obtain ⟨t, ht⟩ := h2
    exact ⟨t, by nlinarith [hMpos]⟩
  have hne : M ≠ M ⊔ Subgroup.zpowers c := by
    intro h
    apply hcM
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hs1 : s ≠ 1 := by
    intro h
    apply hne
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hs, h, mul_one]
  have hs3 : s = 3 := by
    have : s ∣ 3 := h3
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
    · exact absurd h hs1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hs, hs3, hc, mul_comm])

theorem v_zpowers_inf_eq_bot {M : Subgroup G} {c : G} (hc : orderOf c = 3) (hcM : c ∉ M) :
    Subgroup.zpowers c ⊓ M = ⊥ := by
  have hd : Nat.card (Subgroup.zpowers c ⊓ M : Subgroup G) ∣ 3 := by
    rw [← hc, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    apply hcM
    have : Subgroup.zpowers c ⊓ M = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, ← hc, Nat.card_zpowers])
    have hh : c ∈ Subgroup.zpowers c ⊓ M := by rw [this]; exact Subgroup.mem_zpowers c
    exact hh.2

theorem v_cenb_gen {M : Subgroup G} (hM : IsMulCommutative M) {c : G} (hc : orderOf c = 3)
    (hcN : c ∈ Subgroup.normalizer (M : Set G)) (hcM : c ∉ M)
    (hZ : Nat.card (M ⊓ Cen c : Subgroup G) = 9) :
    ∀ T : Subgroup G, T ≤ (M ⊔ Subgroup.zpowers c) ⊓ Cen c →
      Nat.card T ≤ 27 ∧ (Nat.card T = 27 → c ∈ T) := by
  intro T hT
  set W : Subgroup G := (M ⊓ Cen c) ⊔ Subgroup.zpowers c with hW
  have hcomm : ∀ x ∈ (M ⊓ Cen c : Subgroup G), ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x c := by
      have := (Subgroup.mem_centralizer_iff.mp hx.2) c rfl
      exact this.symm
    exact (this.zpow_right n).eq
  have hinf : (M ⊓ Cen c : Subgroup G) ⊓ Subgroup.zpowers c = ⊥ := by
    have := v_zpowers_inf_eq_bot hc hcM
    refine le_bot_iff.mp (fun x hx => ?_)
    have h1 : x ∈ Subgroup.zpowers c ⊓ M := ⟨hx.2, hx.1.1⟩
    rw [this] at h1
    exact h1
  have hWcard : Nat.card W = 27 := by
    obtain ⟨h, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hZ, Nat.card_zpowers, hc] at h
    simpa using h
  have hTW : T ≤ W := by
    intro t ht
    have h1 := hT ht
    have hm : (t : G) ∈ (↑(M ⊔ Subgroup.zpowers c) : Set G) := h1.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M _ ((Subgroup.zpowers_le).mpr hcN)] at hm
    obtain ⟨m, hm, y, hy, rfl⟩ := hm
    have hy' : y ∈ Cen c := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ((Commute.refl x).zpow_right n).eq
    have hm' : m ∈ Cen c := by
      have := Subgroup.mul_mem _ h1.2 (Subgroup.inv_mem _ hy')
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hm, hm'⟩) (Subgroup.mem_sup_right hy)
  refine ⟨hWcard ▸ Subgroup.card_le_of_le hTW, fun h27 => ?_⟩
  have : T = W := Subgroup.eq_of_le_of_card_ge hTW (by rw [h27, hWcard])
  rw [this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

@[expose] noncomputable def vCommMap {A : Subgroup G} (hA : IsMulCommutative A) {b : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) : ↥A →* G :=
  MonoidHom.mk' (fun x => ⁅b, (x : G)⁆) fun x y => by
    have hx := (Subgroup.mem_normalizer_iff.mp hb x.1).mp x.2
    have hy := (Subgroup.mem_normalizer_iff.mp hb y.1).mp y.2
    have hc : ∀ u v : G, u ∈ A → v ∈ A → u * v = v * u := fun u v hu hv =>
      congrArg Subtype.val (hA.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    simp only [commutatorElement_def, Subgroup.coe_mul]
    have h1 := hc _ _ (A.inv_mem x.2) hy
    have h2 := hc _ _ x.2 y.2
    calc b * (↑x * ↑y) * b⁻¹ * (↑x * ↑y)⁻¹
        = (b * ↑x * b⁻¹) * (b * ↑y * b⁻¹) * (↑y)⁻¹ * (↑x)⁻¹ := by group
      _ = (b * ↑x * b⁻¹) * ((b * ↑y * b⁻¹) * (↑y)⁻¹) * (↑x)⁻¹ := by group
      _ = (b * ↑x * b⁻¹) * ((↑x)⁻¹ * ((b * ↑y * b⁻¹) * (↑y)⁻¹)) := by
          have hcc := hc _ _ (A.mul_mem hy (A.inv_mem y.2)) (A.inv_mem x.2)
          have aux : ∀ u w z : G, w * z = z * w → u * w * z = u * (z * w) := by
            intro u w z h; rw [mul_assoc, h]
          exact aux _ _ _ hcc
      _ = (b * ↑x * b⁻¹ * (↑x)⁻¹) * (b * ↑y * b⁻¹ * (↑y)⁻¹) := by group

theorem v_commMap_apply {A : Subgroup G} (hA : IsMulCommutative A) {b : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) (x : A) : vCommMap hA hb x = ⁅b, (x : G)⁆ := rfl

theorem v_comm_le_range {A : Subgroup G} (hA : IsMulCommutative A) {b : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) :
    (⁅Subgroup.zpowers b, A⁆ : Subgroup G) ≤ (vCommMap hA hb).range := by
  set φ := vCommMap hA hb with hφ
  have hφx : ∀ x : A, φ x = ⁅b, (x : G)⁆ := fun _ => rfl
  rw [Subgroup.commutator_le]
  have key : ∀ n : ℕ, ∀ x ∈ A, b ^ n * x * (b ^ n)⁻¹ ∈ A ∧ ⁅b ^ n, x⁆ ∈ φ.range := by
    intro n
    induction n with
    | zero => intro x hx; simp [hx, Subgroup.one_mem]
    | succ n ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hb _).mp h1
        simpa [pow_succ', mul_assoc] using this
      · have e : ⁅b ^ (n + 1), x⁆ = ⁅b, b ^ n * x * (b ^ n)⁻¹⁆ * ⁅b ^ n, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ⟨⟨_, h1⟩, rfl⟩ h2
  intro g hg x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨m, hm⟩ : ∃ m : ℕ, b ^ n = b ^ m := by
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨m, hm.symm⟩
  rw [hm]
  exact (key m x hx).2

theorem v_cen_card_mul_le {A : Subgroup G} (hA : IsMulCommutative A) {b : G}
    (hb : b ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊓ Cen b : Subgroup G) * Nat.card (⁅Subgroup.zpowers b, A⁆ : Subgroup G) ≤
      Nat.card A := by
  set φ := vCommMap hA hb with hφ
  have hφx : ∀ x : A, φ x = ⁅b, (x : G)⁆ := fun _ => rfl
  have hker : Nat.card φ.ker = Nat.card (A ⊓ Cen b : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, ?_⟩
        invFun := fun z => ⟨⟨z, z.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
    · have := x.2
      rw [MonoidHom.mem_ker, hφx, commutatorElement_def] at this
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h2 : h * (x.1 : G) * h⁻¹ = (x.1 : G) := by
        rw [mul_inv_eq_one] at this
        exact this
      calc h * (x.1 : G) = h * (x.1 : G) * h⁻¹ * h := by group
        _ = (x.1 : G) * h := by rw [h2]
    · have := z.2.2
      rw [MonoidHom.mem_ker, hφx, commutatorElement_def]
      have h1 : (z : G) * b = b * z := ((Subgroup.mem_centralizer_iff.mp this) b rfl).symm
      show b * (z : G) * b⁻¹ * (z : G)⁻¹ = 1
      rw [← h1]
      group
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card (⁅Subgroup.zpowers b, A⁆ : Subgroup G) ≤ Nat.card φ.range :=
    Subgroup.card_le_of_le (v_comm_le_range hA hb)
  rw [← hker]
  calc Nat.card φ.ker * Nat.card (⁅Subgroup.zpowers b, A⁆ : Subgroup G)
      ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul_left _ h2
    _ = Nat.card A := h1

theorem v_comm {X : Subgroup G} (hX : IsMulCommutative X) {u v : G} (hu : u ∈ X) (hv : v ∈ X) :
    u * v = v * u :=
  congrArg Subtype.val (hX.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem v_inf_cen_eq {M : Subgroup G} (hM : IsMulCommutative M) (c : G) :
    M ⊓ Cen c = M ⊓ CenS (M ⊔ Subgroup.zpowers c : Subgroup G) := by
  ext s
  constructor
  · rintro ⟨hs, hsc⟩
    refine ⟨hs, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hle : M ⊔ Subgroup.zpowers c ≤ Cen s := by
      refine sup_le (fun m hm => ?_) ?_
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh; subst hh; exact v_comm hM hs hm
      · refine (Subgroup.zpowers_le).mpr ?_
        refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh; subst hh
        exact ((Subgroup.mem_centralizer_iff.mp hsc) c rfl).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hy)) s rfl).symm
  · rintro ⟨hs, hsc⟩
    refine ⟨hs, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh; subst hh
    exact (Subgroup.mem_centralizer_iff.mp hsc) h
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers h))

variable {b : G} {J B A P D : Subgroup G}

theorem v_card27 (h : FF79Sec34In4 b J B A P D) {X : Subgroup G} (hX : X ≤ Cen b)
    (hX3 : IsPGroup 3 X) : Nat.card X ≤ 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := L41.isSylowOf_card_p h.sylB
  have h27 : Nat.card B = 27 := by rw [h.elemB.2]; norm_num
  obtain ⟨k, hk⟩ := hX3.exists_card_eq
  have hd : 3 ^ k ∣ Nat.card (Cen b) := hk ▸ Subgroup.card_dvd_of_le hX
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hd
  rw [hk]
  calc 3 ^ k ≤ 3 ^ (Nat.card (Cen b)).factorization 3 := Nat.pow_le_pow_right (by norm_num) this
    _ = 27 := by rw [← hB, h27]

theorem v_A_cen (h : FF79Sec34In4 b J B A P D) : A ⊓ Cen b = B ⊓ J := by
  have hB := h.elemB.1.toIsMulCommutative
  have hbB : b ∈ B := h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hle : B ⊓ J ≤ A ⊓ Cen b := by
    intro x hx
    refine ⟨h.B0A hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact v_comm hB hbB hx.1
  have h1 := v_cen_card_mul_le h.elemA.1.toIsMulCommutative h.bA
  rw [h.commbA, h.elemB0.2, h.elemA.2] at h1
  have h2 : Nat.card (A ⊓ Cen b : Subgroup G) ≤ Nat.card (B ⊓ J : Subgroup G) := by
    rw [h.elemB0.2]; norm_num at h1 ⊢; omega
  exact (Subgroup.eq_of_le_of_card_ge hle h2).symm

theorem v_As_cen (h : FF79Sec34In4 b J B A P D) {As : Subgroup G} (hAs : FF79AStar b D A As) :
    As ⊓ Cen b = B ⊓ J := by
  apply le_antisymm
  · rintro s ⟨hs, hsb⟩
    have hc : s * b = b * s := ((Subgroup.mem_centralizer_iff.mp hsb) b rfl).symm
    have : ⁅⁅s, b⁆, b⁆ = 1 := by
      have : ⁅s, b⁆ = 1 := by rw [commutatorElement_def, hc]; group
      rw [this]; simp
    have hsA := (hAs.2.2.2.2.2.2.2 s hs).mp this
    rw [← v_A_cen h]
    exact ⟨hsA, hsb⟩
  · intro x hx
    have := (v_A_cen h).symm ▸ hx
    exact ⟨hAs.1 this.1, this.2⟩

theorem v_b_not_mem (h : FF79Sec34In4 b J B A P D) {As : Subgroup G} (hAs : FF79AStar b D A As) :
    b ∉ As := by
  intro hb
  have hcen : As ≤ CenS A := hAs.2.1.1
  have h1 : ⁅Subgroup.zpowers b, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.zpowers_le).mpr (by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      exact ((Subgroup.mem_centralizer_iff.mp (hcen hb)) x hx))
  have h2 := h.commbA
  rw [h1] at h2
  have := congrArg (fun X : Subgroup G => Nat.card X) h2
  rw [Subgroup.card_bot, h.elemB0.2] at this
  norm_num at this

theorem v_card_P0 (h : FF79Sec34In4 b J B A P D) {As : Subgroup G} (hAs : FF79AStar b D A As) :
    Nat.card (As ⊔ Subgroup.zpowers b : Subgroup G) = 3 * Nat.card As := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb := v_b_not_mem h hAs
  have hle : Nat.card (Subgroup.zpowers b ⊔ As : Subgroup G) ≤ 3 * Nat.card As := by
    have := v_card_sup_le (H := Subgroup.zpowers b) (N := As)
      ((Subgroup.zpowers_le).mpr hAs.2.2.2.1)
    rwa [Nat.card_zpowers, h.hyp.ord] at this
  rw [sup_comm] at hle
  have hP3 := hAs.2.2.2.2.2.2.1.2.1
  obtain ⟨k, hk⟩ := hP3.exists_card_eq
  have hAs3 : IsPGroup 3 As := hAs.2.1.2.1
  obtain ⟨j, hj⟩ := hAs3.exists_card_eq
  have hdvd : Nat.card As ∣ Nat.card (As ⊔ Subgroup.zpowers b : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card As ≠ Nat.card (As ⊔ Subgroup.zpowers b : Subgroup G) := by
    intro he
    have := Subgroup.eq_of_le_of_card_ge (le_sup_left : As ≤ As ⊔ Subgroup.zpowers b) he.ge
    exact hb (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hlt : Nat.card As < Nat.card (As ⊔ Subgroup.zpowers b : Subgroup G) :=
    lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
  rw [hk, hj] at hlt hle ⊢
  have hjk : j < k := by
    by_contra hh
    push Not at hh
    exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hh))
  have hkj : k ≤ j + 1 := by
    by_contra hh
    push Not at hh
    have : 3 ^ (j + 1) < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) hh
    rw [pow_succ] at this
    omega
  have : k = j + 1 := by omega
  rw [this, pow_succ]; ring

theorem sec34_cenb_syl (h : FF79Sec34In4 b J B A P D) :
    ∀ S : Subgroup G, IsSylowOf 3 S ⊤ → b ∈ S → ∀ T : Subgroup G, T ≤ S → T ≤ Cen b →
      Nat.card T ≤ 27 ∧ (Nat.card T = 27 → b ∈ T) := by
  intro S hS hbS T hTS hTb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨As, hAs⟩ := h.star
  have hcommAs : IsMulCommutative As := hAs.2.2.1
  have hbN : b ∈ Nor As := hAs.2.2.2.1
  have hP0 : IsSylowOf 3 (As ⊔ Subgroup.zpowers b) ⊤ := hAs.2.2.2.2.2.2.1
  obtain ⟨g, -, hg⟩ := L41.exists_conjBy_eq_sylowOf hS hP0
  have hbS' : b ∈ conjBy g (As ⊔ Subgroup.zpowers b) := hg ▸ hbS
  obtain ⟨x, hxP0, hxb⟩ := Subgroup.mem_map.mp hbS'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxb
  have hxN : x ∈ Nor As := by
    have : As ⊔ Subgroup.zpowers b ≤ Nor As :=
      sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).mpr hbN)
    exact this hxP0
  have hxo : orderOf x = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    rw [MulAut.conj_apply, hxb, h.hyp.ord] at this
    exact this.symm
  have h81 : 81 ≤ Nat.card As := by
    have := Subgroup.card_le_of_le (hAs.1)
    rw [h.elemA.2] at this
    simpa using this
  have hxAs : x ∉ As := by
    intro hx
    have hle : conjBy g As ≤ Cen b := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz; subst hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := v_comm hcommAs hx hy
      rw [← hxb]
      calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        _ = g * (y * x) * g⁻¹ := by rw [this]
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
    obtain ⟨k, hk⟩ := hAs.2.1.2.1.exists_card_eq
    have h3 : IsPGroup 3 (conjBy g As) :=
      IsPGroup.of_card (n := k) (by rw [L41.card_conjBy, hk])
    have := v_card27 h hle h3
    rw [L41.card_conjBy] at this
    omega
  have hsup : As ⊔ Subgroup.zpowers x = As ⊔ Subgroup.zpowers b :=
    v_sup_eq_of_index_three le_sup_left (v_card_P0 h hAs) hxP0 hxAs
  have hZ : Nat.card (As ⊓ Cen x : Subgroup G) = 9 := by
    rw [v_inf_cen_eq hcommAs, hsup, ← v_inf_cen_eq hcommAs, v_As_cen h hAs, h.elemB0.2]
    norm_num
  have key := v_cenb_gen hcommAs hxo hxN hxAs hZ
  set T' : Subgroup G := T.map (MulAut.conj g⁻¹).toMonoidHom with hT'
  have hT'card : Nat.card T' = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hT'le : T' ≤ (As ⊔ Subgroup.zpowers x) ⊓ Cen x := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have htS : t ∈ conjBy g (As ⊔ Subgroup.zpowers b) := hg ▸ hTS ht
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp htS
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ht ⊢
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e, hsup]
    refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz; subst hz
    have hc := (Subgroup.mem_centralizer_iff.mp (hTb ht)) b rfl
    rw [← hxb] at hc
    have : g * z * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * z * g⁻¹) := hc
    calc z * y = g⁻¹ * (g * z * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * z * g⁻¹)) * g := by rw [this]
      _ = y * z := by group
  obtain ⟨k1, k2⟩ := key T' hT'le
  refine ⟨hT'card ▸ k1, fun h27 => ?_⟩
  have hxT' := k2 (hT'card ▸ h27)
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hxT'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hte
  have : b = t := by
    rw [← hxb, ← hte]; group
  exact this ▸ ht

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
