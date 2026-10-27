module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsDefs
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Y
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Frat
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open scoped MatrixGroups Pointwise

variable {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y] {p : ℕ}

theorem Res1L2Abs.orderOf_rho_j (D : Res1L2Abs P Y p) : orderOf (D.ρ D.j) = p := by
  have := Fact.mk D.hp
  exact orderOf_eq_prime (by rw [← map_pow, D.hj, map_one]) D.hρj

theorem Res1L2Abs.eq_one_of_mem_zpowers (D : Res1L2Abs P Y p) {x : P}
    (hx : x ∈ Subgroup.zpowers D.j) (h : D.ρ x = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow] at h
  have hdvd : (orderOf (D.ρ D.j) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [D.orderOf_rho_j] at hdvd
  obtain ⟨m, rfl⟩ := hdvd
  rw [zpow_mul, zpow_natCast, D.hj, one_zpow]

theorem Res1L2Abs.conj_eq_inv (D : Res1L2Abs P Y p) {w : P}
    (hw : w * D.j * w⁻¹ ∈ Subgroup.zpowers D.j)
    (hρ : D.ρ w * D.ρ D.j * (D.ρ w)⁻¹ = (D.ρ D.j)⁻¹) : w * D.j * w⁻¹ = D.j⁻¹ := by
  have h1 : (w * D.j * w⁻¹) * D.j ∈ Subgroup.zpowers D.j :=
    Subgroup.mul_mem _ hw (Subgroup.mem_zpowers _)
  have h2 : D.ρ ((w * D.j * w⁻¹) * D.j) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hρ, inv_mul_cancel]
  exact eq_inv_of_mul_eq_one_left (D.eq_one_of_mem_zpowers h1 h2)

theorem res1L2A_l2_finite {n : ℕ}
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) : Finite Y :=
  Finite.of_equiv (PSL(2, GaloisField 2 n))
    (e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n))).symm.toEquiv

theorem res1L2A_l2_conj_injective {n : ℕ} (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  let φ : Y ≃* SL(2, GaloisField 2 n) :=
    (e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n))).trans
      (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2EquivPSL2
        (F := GaloisField 2 n)).symm
  rw [injective_iff_map_eq_one]
  intro y hy
  have hc : ∀ g : Y, g * y = y * g := fun g => by
    have h := congrArg (fun a : MulAut Y => a g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hmem : φ y ∈ Subgroup.center SL(2, GaloisField 2 n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hc g']
  rw [CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2_center_eq_bot,
    Subgroup.mem_bot] at hmem
  exact φ.injective (by rw [hmem, map_one])

theorem res1L2A_mem_normalizer_zpowers {G : Type*} [Group G] {x g : G}
    (h : g * x * g⁻¹ = x⁻¹) : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have h1 : ∀ k : ℤ, g * x ^ k * g⁻¹ = (x ^ k)⁻¹ := fun k => by
    rw [← conj_zpow, h, inv_zpow]
  have h3 : g⁻¹ * x⁻¹ * g = x := by
    calc g⁻¹ * x⁻¹ * g = g⁻¹ * (g * x * g⁻¹) * g := by rw [h]
      _ = x := by group
  have h2 : g⁻¹ * x * g = x⁻¹ := by
    calc g⁻¹ * x * g = (g⁻¹ * x⁻¹ * g)⁻¹ := by group
      _ = x⁻¹ := by rw [h3]
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [h1]
    exact (Subgroup.zpowers x).inv_mem (Subgroup.zpow_mem_zpowers x k)
  · intro ht
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ht
    have : t = g⁻¹ * x ^ m * g := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * x ^ m * g := by rw [← hm]
    have h4 : g⁻¹ * x ^ m * g = (g⁻¹ * x * g) ^ m := by
      have := conj_zpow (a := g⁻¹) (b := x) (i := m)
      simpa only [inv_inv] using this.symm
    rw [this, h4, h2, inv_zpow]
    exact (Subgroup.zpowers x).inv_mem (Subgroup.zpow_mem_zpowers x m)

theorem res1L2A_exists_conj_mem_of_maximal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B S T : Subgroup G) (hSB : S ≤ B) (hTB : T ≤ B) (hS : IsPGroup p S) (hT : IsPGroup p T)
    (hSmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → S ≤ X → X = S) :
    ∃ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ S := by
  let SB : Sylow p B :=
    { toSubgroup := S.subgroupOf B
      isPGroup' := hS.comap_subtype
      is_maximal' := fun {Q} hQ hle => by
        have hSQ : S ≤ Q.map B.subtype := fun s hs => ⟨⟨s, hSB hs⟩, hle hs, rfl⟩
        have heq := hSmax (Q.map B.subtype) (Subgroup.map_subtype_le Q) (hQ.map _) hSQ
        calc Q = (Q.map B.subtype).comap B.subtype :=
              (Subgroup.comap_map_eq_self_of_injective B.subtype_injective Q).symm
          _ = S.subgroupOf B := by rw [heq]; rfl }
  obtain ⟨Q, hQ⟩ := (hT.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B Q SB
  refine ⟨b, b.2, fun t ht => ?_⟩
  have h1 : (⟨t, hTB ht⟩ : B) ∈ (Q : Subgroup B) := hQ ht
  have h2 : MulAut.conj b • (⟨t, hTB ht⟩ : B) ∈ MulAut.conj b • (Q : Subgroup B) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [← Sylow.coe_subgroup_smul, hb] at h2
  simpa [SB, Subgroup.mem_subgroupOf] using h2

theorem res1L2A_card_le_of_maximal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B S X : Subgroup G) (hSB : S ≤ B) (hXB : X ≤ B) (hS : IsPGroup p S) (hX : IsPGroup p X)
    (hSmax : ∀ Z : Subgroup G, Z ≤ B → IsPGroup p Z → S ≤ Z → Z = S) :
    Nat.card X ≤ Nat.card S := by
  obtain ⟨b, -, hb⟩ := res1L2A_exists_conj_mem_of_maximal B S X hSB hXB hS hX hSmax
  have hle : X.map (MulAut.conj b).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hb x hx
  calc Nat.card X = Nat.card (X.map (MulAut.conj b).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj b).injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hle

theorem res1L2A_card_eq_card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (X : Subgroup G) :
    Nat.card X = Nat.card (X.map f) * Nat.card (f.ker ⊓ X : Subgroup G) := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

theorem Res1L2Abs.false_of_inner_inverter (D : Res1L2Abs P Y p) {w : P}
    (hw : w * D.j * w⁻¹ = D.j⁻¹) (hwinn : ∃ y : Y, D.ρ w = MulAut.conj y) : False := by
  have := Fact.mk D.hp
  obtain ⟨e⟩ := D.e
  have hn2 : 2 ≤ D.n := by have := D.hn4; omega
  have : Finite Y := res1L2A_l2_finite e
  have hinj := res1L2A_l2_conj_injective e
  obtain ⟨y, hy⟩ := hwinn
  obtain ⟨yj, hyj⟩ := D.hjinn
  have hconj : (D.z * w) * D.j * (D.z * w)⁻¹ = D.j := by
    calc (D.z * w) * D.j * (D.z * w)⁻¹ = D.z * (w * D.j * w⁻¹) * D.z⁻¹ := by group
      _ = D.z * D.j⁻¹ * D.z⁻¹ := by rw [hw]
      _ = (D.z * D.j * D.z⁻¹)⁻¹ := by group
      _ = D.j := by rw [D.hzj, inv_inv]
  have hzw : D.z * w ∈ Subgroup.centralizer ({D.j} : Set P) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hwM : w ∈ D.M := by
    have := D.M.mul_mem (D.M.inv_mem D.hzM) (D.hCM hzw)
    rwa [inv_mul_cancel_left] at this
  have hyU : y ∈ Subgroup.normalizer ((D.U : Subgroup Y) : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have := D.hBorel w hwM u hu
    rwa [hy, MulAut.conj_apply] at this
  have hyjU : yj ∈ Subgroup.normalizer ((D.U : Subgroup Y) : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have := D.hBorel D.j D.hjM u hu
    rwa [hyj, MulAut.conj_apply] at this
  have hcomm : y * yj * y⁻¹ = yj⁻¹ := by
    apply hinj
    have h := congrArg D.ρ hw
    rw [map_mul, map_mul, map_inv, map_inv, hy, hyj] at h
    simpa [map_mul, map_inv] using h
  have hmem := l2_borel_commutator_mem hn2 e D.U hyU hyjU
  rw [hcomm] at hmem
  have hyjp : yj ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hyj, ← map_pow, D.hj, map_one, map_one]
  have hyj1 : yj ≠ 1 := by
    rintro rfl
    exact D.hρj (by rw [hyj, map_one])
  have hord : orderOf yj = p := orderOf_eq_prime hyjp hyj1
  have hcop : Nat.Coprime (orderOf yj) 2 := by
    rw [hord]
    exact (Nat.coprime_primes D.hp Nat.prime_two).mpr (by have := D.hp5; omega)
  have hg : orderOf (yj⁻¹ * yj⁻¹) = p := by
    have h1 : yj⁻¹ * yj⁻¹ = (yj ^ 2)⁻¹ := by group
    rw [h1, orderOf_inv, Nat.Coprime.orderOf_pow hcop, hord]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp D.U.isPGroup' ⟨yj⁻¹ * yj⁻¹, hmem⟩
  rw [Subgroup.orderOf_mk, hg] at hk
  have h2p : 2 ∣ p := by
    rw [hk]
    refine dvd_pow_self 2 ?_
    rintro rfl
    have := D.hp5
    simp at hk
    omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two D.hp).mp h2p
  have := D.hp5
  omega


theorem Res1L2Abs.exists_inverter (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ)
    (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → R ≤ X → X = R)
    (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) :
    ∃ w : P, (∀ s ∈ R ⊔ Subgroup.zpowers D.j, w * s * w⁻¹ ∈ R ⊔ Subgroup.zpowers D.j) ∧
      (∃ y : Y, D.ρ w = MulAut.conj y) ∧
      D.ρ w * D.ρ D.j * (D.ρ w)⁻¹ = (D.ρ D.j)⁻¹ := by
  have := Fact.mk D.hp
  obtain ⟨e⟩ := D.e
  have hn2 : 2 ≤ D.n := by have := D.hn4; omega
  have : Finite Y := res1L2A_l2_finite e
  have hinj := res1L2A_l2_conj_injective e
  obtain ⟨yj, hyj⟩ := D.hjinn
  have hyj1 : yj ≠ 1 := by
    rintro rfl
    exact D.hρj (by rw [hyj, map_one])
  have hyjp : yj ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hyj, ← map_pow, D.hj, map_one, map_one]
  have hord : orderOf yj = p := orderOf_eq_prime hyjp hyj1
  have hodd : Odd (orderOf yj) := by
    rw [hord]
    exact D.hp.odd_of_ne_two (by have := D.hp5; omega)
  set T : Subgroup (MulAut Y) := Subgroup.zpowers (D.ρ D.j) with hT
  have hTcard : Nat.card T = p := by rw [hT, Nat.card_zpowers, D.orderOf_rho_j]
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hRker : R ≤ D.ρ.ker := hRΘ.trans D.hΘker
  let Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range
  have hTInn : T ≤ Inn := Subgroup.zpowers_le.mpr ⟨yj, hyj.symm⟩
  let K₁ : Subgroup P := T.comap D.ρ
  let Y₁ : Subgroup P := (Inn ⊓ Subgroup.normalizer (T : Set (MulAut Y))).comap D.ρ
  let S : Subgroup P := R ⊔ Subgroup.zpowers D.j
  have hKY : K₁ ≤ Y₁ := fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨hTInn hk, Subgroup.le_normalizer hk⟩)
  have hKn : ∀ y ∈ Y₁, ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁ := by
    intro y hy k hk
    have hy' : D.ρ y ∈ Subgroup.normalizer (T : Set (MulAut Y)) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)).2
    show D.ρ (y * k * y⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hy' _).mp (Subgroup.mem_comap.mp hk)
  have hSK : S ≤ K₁ := by
    refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
    · show D.ρ r ∈ T
      rw [MonoidHom.mem_ker.mp (hRker hr)]
      exact T.one_mem
    · show D.ρ D.j ∈ T
      exact Subgroup.mem_zpowers _
  have hLE : R ≤ Subgroup.normalizer (Subgroup.zpowers D.j : Set P) := by
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute r D.j := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
    have : r * D.j ^ k * r⁻¹ = D.j ^ k := by
      rw [(hc.zpow_right k).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  have hSker : D.ρ.ker ⊓ S = R := by
    apply le_antisymm
    · rintro s ⟨hs1, hs2⟩
      have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right R (Subgroup.zpowers D.j) hLE
      have hs3 : s ∈ (↑(R ⊔ Subgroup.zpowers D.j) : Set P) := hs2
      rw [hcoe] at hs3
      obtain ⟨r, hr, c, hc, rfl⟩ := hs3
      have hρc : D.ρ c = 1 := by
        have h1 := MonoidHom.mem_ker.mp hs1
        rwa [map_mul, MonoidHom.mem_ker.mp (hRker hr), one_mul] at h1
      have hc1 := D.eq_one_of_mem_zpowers hc hρc
      subst hc1
      simpa using hr
    · exact le_inf hRker le_sup_left
  have hSmap : S.map D.ρ = T := by
    have hR1 : R.map D.ρ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨r, hr, rfl⟩
      exact MonoidHom.mem_ker.mp (hRker hr)
    show (R ⊔ Subgroup.zpowers D.j).map D.ρ = T
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hR1, bot_sup_eq]
  have hScard : Nat.card S = p * Nat.card R := by
    rw [res1L2A_card_eq_card_map_mul_card_inf_ker D.ρ S, hSmap, hSker, hTcard]
  have hSp : IsPGroup p S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    exact IsPGroup.of_card (n := k + 1) (by rw [hScard, hk, pow_succ, mul_comm])
  have hSmax : ∀ X : Subgroup P, X ≤ K₁ → IsPGroup p X → Nat.card X ≤ Nat.card S := by
    intro X hXK hXp
    have h1 : Nat.card (X.map D.ρ) ≤ p := by
      have h := Subgroup.card_le_of_le (Subgroup.map_le_iff_le_comap.mpr hXK)
      rwa [hTcard] at h
    have h2 : Nat.card (D.ρ.ker ⊓ X : Subgroup P) ≤ Nat.card R := by
      have hp2 : IsPGroup p (D.ρ.ker ⊓ X : Subgroup P) := hXp.to_inf_right
      have hΘ2 : (D.ρ.ker ⊓ X : Subgroup P) ≤ D.Θ := D.hker _ inf_le_left hp2
      exact res1L2A_card_le_of_maximal D.Θ R _ hRΘ hΘ2 hR hp2 hRmax
    rw [res1L2A_card_eq_card_map_mul_card_inf_ker D.ρ X, hScard]
    exact Nat.mul_le_mul h1 h2
  obtain ⟨v, hv⟩ := l2_exists_inverter hn2 e yj hyj1 hodd
  have hvj : v * yj * v⁻¹ = yj⁻¹ := hv yj (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨u, hu⟩ := D.hinn v
  have hu_inv : D.ρ u * D.ρ D.j * (D.ρ u)⁻¹ = (D.ρ D.j)⁻¹ := by
    calc D.ρ u * D.ρ D.j * (D.ρ u)⁻¹ = MulAut.conj (v * yj * v⁻¹) := by
          rw [hu, hyj]
          simp [map_mul, map_inv]
      _ = (D.ρ D.j)⁻¹ := by rw [hvj, map_inv, hyj]
  have huY : u ∈ Y₁ := by
    refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [hu]
      exact ⟨v, rfl⟩
    · exact res1L2A_mem_normalizer_zpowers hu_inv
  have hyT : ¬ ∀ t ∈ T, D.ρ u * t = t * D.ρ u := by
    intro h
    have h1 : D.ρ u * D.ρ D.j = D.ρ D.j * D.ρ u := h _ (Subgroup.mem_zpowers _)
    have h2 : D.ρ D.j = (D.ρ D.j)⁻¹ := by
      rw [← hu_inv, h1]
      group
    have h3 : D.ρ D.j ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h2]
      exact inv_mul_cancel _
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [D.orderOf_rho_j] at h4
    have := Nat.le_of_dvd two_pos h4
    have := D.hp5
    omega
  obtain ⟨w, hwY, hwS, hwT⟩ := exists_normalizes_not_commute_of_frattini D.ρ Y₁ K₁ S hKY hKn hSK
    hSp hSmax T hTcomm (fun k hk => Subgroup.mem_comap.mp hk) huY hyT
  obtain ⟨hwInn, hwNorm⟩ := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hwY)
  obtain ⟨y₀, hy₀⟩ := hwInn
  have hy₀N : y₀ ∈ Subgroup.normalizer (Subgroup.zpowers yj : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hnT : MulAut.conj n ∈ T := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [map_zpow, ← hyj]
      exact Subgroup.zpow_mem_zpowers _ _
    have h1 : D.ρ w * MulAut.conj n * (D.ρ w)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hwNorm _).mp hnT
    rw [← hy₀] at h1
    have h2 : MulAut.conj (y₀ * n * y₀⁻¹) ∈ T := by simpa [map_mul, map_inv] using h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h2
    rw [hyj, ← map_zpow] at hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, hinj hm⟩
  rcases l2_normalizer_dichotomy hn2 e yj hyj1 hodd (Subgroup.zpowers yj)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (fun h => hyj1 (Subgroup.zpowers_eq_bot.mp h)) hy₀N with hc | hi
  · exfalso
    apply hwT
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hcomm : Commute (D.ρ w) (D.ρ D.j) := by
      rw [← hy₀, hyj]
      have h5 := Subgroup.mem_centralizer_singleton_iff.mp hc
      show _ = _
      rw [← map_mul, ← map_mul, h5]
    exact (hcomm.zpow_right k).eq
  · have hyji := hi yj (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    refine ⟨w, hwS, ⟨y₀, hy₀.symm⟩, ?_⟩
    calc D.ρ w * D.ρ D.j * (D.ρ w)⁻¹ = MulAut.conj (y₀ * yj * y₀⁻¹) := by
          rw [← hy₀, hyj]
          simp [map_mul, map_inv]
      _ = (D.ρ D.j)⁻¹ := by rw [hyji, map_inv, hyj]

theorem Res1L2Abs.false_of_theta_pfree (D : Res1L2Abs P Y p)
    (hΘ : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → X = ⊥) : False := by
  have := Fact.mk D.hp
  obtain ⟨w, hwS, hwinn, hwinv⟩ := D.exists_inverter ⊥ bot_le
    (IsPGroup.of_card (n := 0) (by simp)) (fun X hX hXp _ => hΘ X hX hXp) bot_le
  have hmem : w * D.j * w⁻¹ ∈ Subgroup.zpowers D.j := by
    have := hwS D.j (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rwa [bot_sup_eq] at this
  exact D.false_of_inner_inverter (D.conj_eq_inv hmem hwinv) hwinn

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
