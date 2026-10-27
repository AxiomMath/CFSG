module

public import CFSG.Quasithin.SteinbergBSDihedralPair
public import CFSG.Quasithin.SteinbergBSOddCentralCoverExact
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.Quasithin.H13.QRCShortGeneratedResidualKernel

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem le_of_isPGroup_of_not_dvd_relIndex [Finite G] {p : ℕ} [Fact p.Prime]
    {C K P : Subgroup G} (hC : IsPGroup p C) (hCK : C ≤ K) (hidx : ¬ p ∣ C.relIndex K)
    (hP : IsPGroup p P) (hPK : P ≤ K) (hPC : P ≤ normalizer (C : Set G)) : P ≤ C := by
  obtain ⟨n, hn⟩ := (IsPGroup.to_sup_of_normal_right' hP hC hPC).exists_card_eq
  have h1 : C.relIndex (P ⊔ C) ∣ C.relIndex K :=
    Dvd.intro _ (relIndex_mul_relIndex C (P ⊔ C) K le_sup_right (sup_le hPK hCK))
  have h2 : C.relIndex (P ⊔ C) ∣ p ^ n := by
    rw [← hn]
    exact (C.subgroupOf (P ⊔ C)).index_dvd_card
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h2
  rcases m with _ | m
  · rw [pow_zero, relIndex_eq_one] at hm
    exact le_sup_left.trans hm
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero m)).trans (hm ▸ h1)) hidx

theorem commutator_sup_right_le {D X Y Q : Subgroup G} (hXQ : X ≤ normalizer (Q : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G)) (hX : ⁅D, X⁆ ≤ Q) (hY : ⁅D, Y⁆ ≤ Q) :
    ⁅D, X ⊔ Y⁆ ≤ Q := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ normalizer (Q : Set G) ∧ ∀ d ∈ D, ⁅d, y⁆ ∈ Q}
      one_mem' := ⟨one_mem _, fun d _ => by
        show ⁅d, (1 : G)⁆ ∈ Q
        rw [commutatorElement_one_right]
        exact Q.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun d hd => ?_⟩
        have e : ⁅d, a * b⁆ = ⁅d, a⁆ * (a * ⁅d, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (ha' d hd) ((mem_normalizer_iff.1 ha _).1 (hb' d hd))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun d hd => ?_⟩
        have e : ⁅d, a⁻¹⁆ = a⁻¹ * (⁅d, a⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (Q.inv_mem (ha' d hd)) }
  have hXY : X ⊔ Y ≤ C := sup_le (fun x hx => ⟨hXQ hx, fun d hd => hX
    (commutator_mem_commutator hd hx)⟩) fun y hy => ⟨hYQ hy, fun d hd => hY
    (commutator_mem_commutator hd hy)⟩
  rw [commutator_le]
  exact fun d hd z hz => (hXY hz).2 d hd

theorem eq_of_mul_eq_mul_of_inf_eq_bot {H K : Subgroup G} (hb : H ⊓ K = ⊥) {h₁ h₂ k₁ k₂ : G}
    (h₁H : h₁ ∈ H) (h₂H : h₂ ∈ H) (k₁K : k₁ ∈ K) (k₂K : k₂ ∈ K) (he : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have h1 : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by group
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by rw [he]
      _ = k₂ * k₁⁻¹ := by group
  have h2 : h₂⁻¹ * h₁ ∈ H ⊓ K :=
    ⟨H.mul_mem (H.inv_mem h₂H) h₁H, h1 ▸ K.mul_mem k₂K (K.inv_mem k₁K)⟩
  rw [hb, mem_bot] at h2
  have h3 : h₁ = h₂ := by
    calc h₁ = h₂ * (h₂⁻¹ * h₁) := by group
      _ = h₂ := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at he
  exact mul_left_cancel he

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {y : G} (hy : y ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = y := by
  have hc : ∀ (h : ↥H) (k : ↥K), Commute (H.subtype h) (K.subtype k) := fun h k =>
    hHK h h.2 k k.2
  have hr : (H.subtype.noncommCoprod K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hr] at hy
  obtain ⟨⟨h, k⟩, rfl⟩ := hy
  exact ⟨h, h.2, k, k.2, rfl⟩

theorem sup_inf_eq_of_le {H K P : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hb : H ⊓ K = ⊥) (hPH : P ≤ H) : (P ⊔ K) ⊓ H = P := by
  refine le_antisymm (fun y hy => ?_) (le_inf le_sup_left hPH)
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (fun p hp k hk => hHK p (hPH hp) k hk) hy.1
  obtain ⟨-, hk1⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hb (hPH hp) hy.2 hk K.one_mem
    (mul_one (p * k)).symm
  rw [hk1, mul_one]
  exact hp

theorem card_sup_of_commute [Finite G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hb : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hc : ∀ (h : ↥H) (k : ↥K), Commute (H.subtype h) (K.subtype k) := fun h k =>
    hHK h h.2 k k.2
  set μ := H.subtype.noncommCoprod K.subtype hc with hμ
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨h, k⟩ hhk
    obtain ⟨h1, k1⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hb h.2 H.one_mem k.2 K.one_mem
      (hhk.trans (one_mul 1).symm)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext k1)
  have hr : μ.range = H ⊔ K := by
    rw [hμ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hr, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_prodHom_of_range_eq {X : Type*} [Group X] {F A : Subgroup G}
    (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f) (hFAb : F ⊓ A = ⊥) (φ : X →* G)
    (hφ : φ.range = F ⊔ A) :
    ∃ θ : X →* ↥F × ↥A, Function.Surjective θ ∧ θ.ker = φ.ker ∧
      ∀ x, φ x = ((θ x).1 : G) * (θ x).2 := by
  have hc : ∀ (f : ↥F) (a : ↥A), Commute (F.subtype f) (A.subtype a) := fun f a =>
    hFA f f.2 a a.2
  set μ : ↥F × ↥A →* G := F.subtype.noncommCoprod A.subtype hc with hμdef
  have hμ : ∀ p, μ p = (p.1 : G) * p.2 := fun p => rfl
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨f, a⟩ h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hFAb f.2 F.one_mem a.2 A.one_mem
      (h.trans (one_mul 1).symm)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hμr : μ.range = F ⊔ A := by
    rw [hμdef, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hmem : ∀ x, φ x ∈ μ.range := fun x => by
    rw [hμr, ← hφ]
    exact ⟨x, rfl⟩
  set e := MonoidHom.ofInjective hμinj with hedef
  set φ' := φ.codRestrict μ.range hmem with hφ'def
  refine ⟨e.symm.toMonoidHom.comp φ', ?_, ?_, ?_⟩
  · intro p
    obtain ⟨x, hx⟩ : μ p ∈ φ.range := by
      rw [hφ, ← hμr]
      exact ⟨p, rfl⟩
    refine ⟨x, ?_⟩
    have h1 : φ' x = e p := Subtype.ext (by rw [hedef, MonoidHom.ofInjective_apply]; exact hx)
    rw [MonoidHom.comp_apply, h1]
    exact e.symm_apply_apply p
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro x
    have h1 : μ (e.symm (φ' x)) = φ x := by
      have := MonoidHom.ofInjective_apply hμinj (x := e.symm (φ' x))
      rw [← hedef, MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [← h1, hμ]
    rfl

theorem card_map_mk'_eq_relIndex [Finite G] (N K : Subgroup G) [N.Normal] :
    Nat.card ↥(K.map (QuotientGroup.mk' N)) = N.relIndex K := by
  have h1 := card_inf_ker_mul_card_map (QuotientGroup.mk' N) K
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := relIndex_mul_card N K
  rw [inf_comm] at h2
  have hpos : 0 < Nat.card ↥(K ⊓ N) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos ((h1.trans h2.symm).trans (mul_comm _ _))

theorem isPGroup_of_pow_mem {p : ℕ} {P R : Subgroup G} (hR : IsPGroup p R)
    (h : ∀ x ∈ P, ∃ n : ℕ, x ^ p ^ n ∈ R) : IsPGroup p P := by
  intro x
  obtain ⟨n, hn⟩ := h x x.2
  obtain ⟨m, hm⟩ := hR ⟨_, hn⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have h1 : ((x : G) ^ p ^ n) ^ p ^ m = 1 := congrArg Subtype.val hm
  rw [coe_pow, pow_add, pow_mul, h1, coe_one]

theorem sq_eq_one_of_mem_center_of_closure_pair {Y : Type*} [Group Y] {v w : Y}
    (hv : v * v = 1) (hw : w * w = 1) (hgen : closure ({v, w} : Set Y) = ⊤) {z : Y}
    (hz : z ∈ center Y) : z * z = 1 ∨ ∀ a b : Y, a * b = b * a := by
  set r := v * w with hr
  have hvi : v⁻¹ = v := (eq_inv_of_mul_eq_one_left hv).symm
  have hwi : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw).symm
  have hvrv : v * r * v = r⁻¹ := by
    rw [hr, mul_inv_rev, hvi, hwi]
    calc v * (v * w) * v = (v * v) * w * v := by group
      _ = w * v := by rw [hv, one_mul]
  have hrk : ∀ k : ℤ, r ^ k * v = v * r ^ (-k) := fun k => by
    have h1 : v * r ^ k * v⁻¹ = (v * r * v⁻¹) ^ k := conj_zpow.symm
    rw [hvi, hvrv, inv_zpow'] at h1
    rw [← h1]
    calc r ^ k * v = (v * v) * r ^ k * v := by rw [hv, one_mul]
      _ = v * (v * r ^ k * v) := by group
  let S : Subgroup Y :=
    { carrier := {y | ∃ k : ℤ, y = r ^ k ∨ y = v * r ^ k}
      one_mem' := ⟨0, Or.inl (zpow_zero r).symm⟩
      mul_mem' := by
        rintro a b ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
        · exact ⟨i + j, Or.inl (zpow_add r i j).symm⟩
        · refine ⟨-i + j, Or.inr ?_⟩
          rw [← mul_assoc, hrk, mul_assoc, ← zpow_add]
        · exact ⟨i + j, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
        · refine ⟨-i + j, Or.inl ?_⟩
          calc v * r ^ i * (v * r ^ j) = v * (r ^ i * v) * r ^ j := by simp only [mul_assoc]
            _ = v * (v * r ^ (-i)) * r ^ j := by rw [hrk]
            _ = (v * v) * (r ^ (-i) * r ^ j) := by simp only [mul_assoc]
            _ = r ^ (-i + j) := by rw [hv, one_mul, ← zpow_add]
      inv_mem' := by
        rintro a ⟨i, rfl | rfl⟩
        · exact ⟨-i, Or.inl (zpow_neg r i).symm⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [mul_inv_rev, hvi, ← zpow_neg, hrk, neg_neg] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
    · exact ⟨1, Or.inr (by rw [zpow_one, hr, ← mul_assoc, hv, one_mul])⟩
  have hmemS : ∀ y : Y, y ∈ S := fun y => hS ▸ mem_top y
  obtain ⟨k, hk | hk⟩ := hmemS z
  · left
    have h1 : v * z = z * v := mem_center_iff.1 hz v
    rw [hk, hrk] at h1
    have h2 : r ^ k = r ^ (-k) := mul_left_cancel h1
    rw [hk]
    nth_rw 2 [h2]
    rw [← zpow_add, add_neg_cancel, zpow_zero]
  · right
    have h1 : r * z = z * r := mem_center_iff.1 hz r
    rw [hk] at h1
    have hc : r ^ k * r = r * r ^ k := (Commute.self_zpow r k).eq.symm
    have hvr1 : Commute v r := by
      have h2 : v * r * r ^ k = r * v * r ^ k := by
        calc v * r * r ^ k = v * (r * r ^ k) := mul_assoc _ _ _
          _ = v * (r ^ k * r) := by rw [hc]
          _ = v * r ^ k * r := (mul_assoc _ _ _).symm
          _ = r * (v * r ^ k) := h1.symm
          _ = r * v * r ^ k := (mul_assoc _ _ _).symm
      exact mul_right_cancel h2
    have hv' : ∀ i : ℤ, Commute v (r ^ i) := fun i => hvr1.zpow_right i
    have hr' : ∀ i j : ℤ, Commute (r ^ i) (r ^ j) := fun i j => Commute.zpow_zpow_self r i j
    intro a b
    obtain ⟨i, rfl | rfl⟩ := hmemS a <;> obtain ⟨j, rfl | rfl⟩ := hmemS b
    · exact (hr' i j).eq
    · exact ((hv' i).symm.mul_right (hr' i j)).eq
    · exact (((hv' j).symm.mul_right (hr' j i)).symm).eq
    · exact (Commute.mul_left ((Commute.refl v).mul_right (hv' j))
        ((hv' i).symm.mul_right (hr' i j))).eq

theorem dihedral_not_comm {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∀ a b : DihedralGroup n, a * b = b * a := by
  intro h
  have h1 := h (DihedralGroup.r 1) (DihedralGroup.sr 0)
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  have h2 : (0 : ZMod n) - 1 = 0 + 1 := DihedralGroup.sr.inj h1
  have h3 : ((2 : ℕ) : ZMod n) = 0 := by
    have h4 : (2 : ZMod n) = 0 := by linear_combination -h2
    exact_mod_cast h4
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd two_pos h3
  omega

end Helpers

theorem qrc_original_pair_lift_retains_central_second_factor
    {H : Type*} [Group H] [Finite H]
    (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H) (hTn : ¬ (T : Subgroup H).Normal)
    {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M) (hMH : M < ⊤)
    (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : ¬ V ≤ pCore 2 H) {F A : Subgroup (H ⧸ kerIn M ⊤)} [IsElementaryAbelian 2 A]
    (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f) (hFAb : F ⊓ A = ⊥) {x : H ⧸ kerIn M ⊤}
    (hxL : x ∈ F ⊔ A)
    (hL : F ⊔ A = V.map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
      conjugate (V.map (QuotientGroup.mk' (kerIn M ⊤))) x)
    (hF : (∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ a ∧ Nonempty (F ≃* DihedralGroup (ℓ ^ a)) ∧
        Nat.card ↥((V.map (QuotientGroup.mk' (kerIn M ⊤)) ⊔ A) ⊓ F) = 2) ∨
      (∃ (f : ℕ) (k : Type) (_ : Field k), 2 ≤ f ∧ Nat.card k = 2 ^ f ∧
        Nonempty (F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) ∨
      ∃ (b : ℕ) (k : Type) (_ : Field k), 1 ≤ b ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
        Nonempty (F ≃* CFSG.Blueprint.suzukiGroup b k))
    {SF PF : Subgroup (H ⧸ kerIn M ⊤)} (hSF : IsSylowOf 2 SF F) (hPF : PF ≤ F)
    (hPFcore : kerIn PF F = ⊥) (hFO : inSubgroup (pCore 2) F = ⊥)
    (hPFO : inSubgroup (pCore 2) PF = SF)
    (hSL : (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ (F ⊔ A) = SF ⊔ A)
    (hBL : M.map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ (F ⊔ A) = PF ⊔ A) :
    ∃ g : H, g ∈ V ⊔ conjugate V g ∧ V < V ⊔ conjugate V g ∧
      QuotientGroup.mk' (kerIn M ⊤) g = x ∧
      let π := QuotientGroup.mk' (kerIn M ⊤)
      let Q := pCore 2 H
      let I := V ⊔ conjugate V g
      let H₀ := (F ⊔ A).comap π
      let RI := I ⊓ Q
      let J := I ⊓ A.comap π
      I.map π = F ⊔ A ∧ H₀ = kerIn M ⊤ ⊔ I ∧
      (I.subgroupOf (Q ⊔ I)).Normal ∧ Q ⊔ I ≤ H₀ ∧ ((Q ⊔ I).subgroupOf H₀).Normal ∧
      Q ≤ normalizer (I : Set H) ∧ ⁅kerIn M ⊤, I⁆ ≤ Q ∧
      IsSylowOf 2 ((T : Subgroup H) ⊓ I) I ∧ I ⊓ kerIn M ⊤ = RI ∧
      (∃ θ : I →* ↥F × ↥A, Function.Surjective θ ∧ θ.ker = RI.subgroupOf I ∧
        ∀ i : I, π (i : H) = ((θ i).1 : H ⧸ kerIn M ⊤) * (θ i).2) ∧
      J = kerIn (M ⊓ I) I ∧ J = inSubgroup (pCore 2) I ∧
      (∃ κ : J →* A, Function.Surjective κ ∧ κ.ker = RI.subgroupOf J ∧
        ∀ j : J, π (j : H) = κ j) ∧
      inSubgroup (pCore 2) (Q ⊔ I) = Q ⊔ J ∧ IsCharacteristicP 2 I ∧
      inSubgroup (pCore 2) (M ⊓ I) = (T : Subgroup H) ⊓ I ∧
      I ⊓ normalizer (V : Set H) ≤ M ⊓ I ∧
      ∃ ψ : I →* F, Function.Surjective ψ ∧ ψ.ker = J.subgroupOf I ∧
        (∀ i : I, ∃ a ∈ A, π (i : H) = (ψ i : H ⧸ kerIn M ⊤) * a) ∧
        ((M ⊓ I).subgroupOf I).map ψ = PF.subgroupOf F ∧
        (((T : Subgroup H) ⊓ I).subgroupOf I).map ψ = SF.subgroupOf F ∧
        (V.subgroupOf I).map ψ = ((V.map π ⊔ A) ⊓ F).subgroupOf F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (kerIn M ⊤) with hπdef
  set Q := pCore 2 H with hQdef
  set E := V.map π with hEdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective (kerIn M ⊤)
  have hπker : π.ker = kerIn M ⊤ := QuotientGroup.ker_mk' (kerIn M ⊤)
  have hπ1 : ∀ y : H, π y = 1 ↔ y ∈ kerIn M ⊤ := fun y => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hQn : Q.Normal := pCore_normal
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  have hQnorm : ∀ y : H, y ∈ normalizer (Q : Set H) := fun y => by
    rw [normalizer_eq_top_iff.2 hQn]
    exact mem_top y
  have hDn : (kerIn M ⊤).Normal := inferInstance
  have hTsyl : IsSylowTwoOf (T : Subgroup H) ⊤ := ⟨le_top, T.isPGroup', by
    show ¬ 2 ∣ (T : Subgroup H).relIndex ⊤
    rw [relIndex_top_right]
    exact T.not_dvd_index⟩
  obtain ⟨⟨hRJ, -⟩, ⟨-, hodd, -⟩, -⟩ :=
    Setup.qt_A7_unique_Sylow_overgroup_core_and_simple_section hTsyl hTn hTM hMH hmax
  have hQR : Q = CFSG.Open.pCore 2 H := CFSG.pCore_eq_open H 2
  have hQD : Q ≤ kerIn M ⊤ := hQR ▸ hRJ
  have hDQ : ¬ 2 ∣ Q.relIndex (kerIn M ⊤) := by
    have h3 := card_map_mk'_eq_relIndex (CFSG.Open.pCore 2 H) (kerIn M ⊤)
    rw [hQR, ← h3]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hD2 : ∀ P : Subgroup H, IsPGroup 2 P → P ≤ kerIn M ⊤ → P ≤ Q := fun P hP hPD =>
    le_of_isPGroup_of_not_dvd_relIndex hQ2 hQD hDQ hP hPD fun y _ => hQnorm y
  have hQT : Q ≤ T := hQ2.le_sylow_of_normal T
  have hDM : kerIn M ⊤ ≤ M := kerIn_le
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hVp : IsPGroup 2 V := (T.isPGroup').to_le hVT
  have hO2 : IsPGroup 2 (inSubgroup (pCore 2) M) :=
    (pCore_isPGroup (p := 2) (G := M)).map M.subtype
  have hMO : M ≤ normalizer (inSubgroup (pCore 2) M : Set H) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic M (pCore 2 M))
  have hDV : ⁅kerIn M ⊤, V⁆ ≤ Q := by
    refine (commutator_le.2 fun d hd v hv => ?_ :
      ⁅kerIn M ⊤, V⁆ ≤ kerIn M ⊤ ⊓ inSubgroup (pCore 2) M).trans
        (hD2 _ (hO2.to_le inf_le_right) inf_le_left)
    have h1 : d * v * d⁻¹ * v⁻¹ ∈ kerIn M ⊤ := by
      have e : d * v * d⁻¹ * v⁻¹ = d * (v * d⁻¹ * v⁻¹) := by group
      rw [e]
      exact (kerIn M ⊤).mul_mem hd (hDn.conj_mem _ ((kerIn M ⊤).inv_mem hd) v)
    have h2 : d * v * d⁻¹ * v⁻¹ ∈ inSubgroup (pCore 2) M :=
      (inSubgroup (pCore 2) M).mul_mem ((mem_normalizer_iff.1 (hMO (hDM hd)) v).1 (hVM hv))
        ((inSubgroup (pCore 2) M).inv_mem (hVM hv))
    rw [commutatorElement_def]
    exact mem_inf.2 ⟨h1, h2⟩
  have hDW : ∀ h : H, ⁅kerIn M ⊤, conjugate V h⁆ ≤ Q := fun h => by
    rw [commutator_le]
    intro d hd w hw
    have hv : h * w * h⁻¹ ∈ V := mem_conjugate_iff.1 hw
    have hd' : h * d * h⁻¹ ∈ kerIn M ⊤ := hDn.conj_mem d hd h
    have h1 := hDV (commutator_mem_commutator hd' hv)
    have e : ⁅d, w⁆ = h⁻¹ * ⁅h * d * h⁻¹, h * w * h⁻¹⁆ * h⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hQn.conj_mem _ h1 h⁻¹
  have hmapI : ∀ h : H, π h = x → (V ⊔ conjugate V h).map π = F ⊔ A := fun h hh => by
    rw [Subgroup.map_sup, map_conjugate, hh, hL]
  obtain ⟨g₀, hg₀, hmin⟩ := Set.exists_min_image {h : H | π h = x}
    (fun h => Nat.card ↥(V ⊔ conjugate V h)) (Set.toFinite _) (hπs x)
  obtain ⟨g, hgI₀, hgx⟩ : ∃ g ∈ V ⊔ conjugate V g₀, π g = x := by
    have h1 : x ∈ (V ⊔ conjugate V g₀).map π := (hmapI g₀ hg₀).symm ▸ hxL
    obtain ⟨g, hg, hgx⟩ := h1
    exact ⟨g, hg, hgx⟩
  have hconjle : conjugate V g ≤ V ⊔ conjugate V g₀ := fun y hy => by
    have h1 := (le_sup_left : V ≤ V ⊔ conjugate V g₀) (mem_conjugate_iff.1 hy)
    have h2 := mul_mem (mul_mem (inv_mem hgI₀) h1) hgI₀
    simpa [mul_assoc] using h2
  set I := V ⊔ conjugate V g with hIdef
  have hIeq : I = V ⊔ conjugate V g₀ :=
    eq_of_le_of_card_ge (sup_le le_sup_left hconjle) (hmin g hgx)
  have hgI : g ∈ I := hIeq ▸ hgI₀
  have hVI : V ≤ I := le_sup_left
  have hWI : conjugate V g ≤ I := le_sup_right
  have hIπ : I.map π = F ⊔ A := hmapI g hgx
  have hπI : ∀ i ∈ I, π i ∈ F ⊔ A := fun i hi => hIπ ▸ mem_map_of_mem π hi
  have hH₀ : (F ⊔ A).comap π = kerIn M ⊤ ⊔ I := by
    rw [← hIπ, comap_map_eq, hπker, sup_comm]
  have hAc : ∀ y ∈ F ⊔ A, ∀ a ∈ A, y * a = a * y := by
    intro y hy a ha
    have hA' : F ⊔ A ≤ centralizer (A : Set (H ⧸ kerIn M ⊤)) := sup_le
      (fun f hf => mem_centralizer_iff.2 fun a ha => (hFA f hf a ha).symm)
      (fun a' ha' => mem_centralizer_iff.2 fun a ha =>
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨a', ha'⟩))
    exact (mem_centralizer_iff.1 (hA' hy) a ha).symm
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : H ⧸ kerIn M ⊤) a.2)⟩
  have hFnt : F ≠ ⊥ := by
    rw [← nontrivial_iff_ne_bot]
    rcases hF with ⟨ℓ, a, -, -, -, ⟨e⟩, -⟩ | ⟨f, k, _, -, -, ⟨e⟩⟩ | ⟨b, k, _, -, hk, ⟨e⟩⟩
    · exact e.toEquiv.nontrivial
    · exact e.toEquiv.nontrivial
    · have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
      have hq : 2 ≤ 2 ^ (2 * b + 1) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : 1 < Nat.card ↥(CFSG.Blueprint.suzukiGroup b k) := by
        rw [CFSG.LieType.Ree.suzuki_order hk]
        have h2 : 4 ≤ (2 ^ (2 * b + 1)) ^ 2 := by nlinarith
        calc 1 < 4 * 1 * 1 := by norm_num
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h2 (by omega)) (by omega)
      have : Finite ↥(CFSG.Blueprint.suzukiGroup b k) := Nat.finite_of_card_ne_zero (by omega)
      have : Nontrivial ↥(CFSG.Blueprint.suzukiGroup b k) :=
        Finite.one_lt_card_iff_nontrivial.1 h1
      exact e.toEquiv.nontrivial
  have hVltI : V < I := by
    refine lt_of_le_of_ne hVI fun h => hFnt ?_
    have hL2 : IsPGroup 2 ↥(F ⊔ A) := by
      rw [← hIπ, ← h]
      exact hVp.map π
    have hF2 : IsPGroup 2 F := hL2.to_le le_sup_left
    rw [eq_bot_iff, ← hFO]
    exact le_inSubgroup_pCore le_rfl le_normalizer hF2
  have hDI : ⁅kerIn M ⊤, I⁆ ≤ Q :=
    commutator_sup_right_le (fun y _ => hQnorm y) (fun y _ => hQnorm y) hDV (hDW g)
  have hQV : Q ≤ normalizer (V : Set H) := hQT.trans hTV
  have hQnormI : Q ≤ normalizer (I : Set H) := by
    intro q hq
    apply mem_normalizer_of_conjugate_eq
    have hgq : g * q * g⁻¹ ∈ normalizer (V : Set H) := hQV (hQn.conj_mem q hq g)
    have h1 : conjugate (conjugate V g) q = conjugate V g := by
      rw [← conjugate_mul, show g * q = (g * q * g⁻¹) * g by group, conjugate_mul,
        conjugate_of_mem_normalizer hgq]
    rw [hIdef, conjugate_sup, conjugate_of_mem_normalizer (hQV hq), h1]
  have hInorm : (I.subgroupOf (Q ⊔ I)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 (sup_le hQnormI le_normalizer)
  have hDQI : kerIn M ⊤ ≤ normalizer ((Q ⊔ I : Subgroup H) : Set H) := by
    refine le_normalizer_of_forall_conj_mem fun d hd b hb => ?_
    have hle : Q ⊔ I ≤ (Q ⊔ I).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (fun i hi => ?_)
      · exact mem_sup_left (hQn.conj_mem q hq d)
      · have h1 : ⁅d, i⁆ ∈ Q := hDI (commutator_mem_commutator hd hi)
        have e : (MulAut.conj d).toMonoidHom i = ⁅d, i⁆ * i := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
        show (MulAut.conj d).toMonoidHom i ∈ Q ⊔ I
        rw [e]
        exact mul_mem (mem_sup_left h1) (mem_sup_right hi)
    exact hle hb
  have hQIH₀ : Q ⊔ I ≤ (F ⊔ A).comap π := by
    rw [hH₀]
    exact sup_le (hQD.trans le_sup_left) le_sup_right
  have hH₀QI : (F ⊔ A).comap π ≤ normalizer ((Q ⊔ I : Subgroup H) : Set H) := by
    rw [hH₀]
    exact sup_le hDQI (le_sup_right.trans le_normalizer)
  have hQIn : ((Q ⊔ I).subgroupOf ((F ⊔ A).comap π)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQIH₀).2 hH₀QI
  have hDH₀ : kerIn M ⊤ ≤ (F ⊔ A).comap π := fun d hd => by
    show π d ∈ F ⊔ A
    rw [(hπ1 d).2 hd]
    exact one_mem _
  have hcardH₀ : Nat.card ↥((F ⊔ A).comap π) = Nat.card (kerIn M ⊤) * Nat.card ↥(F ⊔ A) := by
    have h1 := card_inf_ker_mul_card_map π ((F ⊔ A).comap π)
    rw [hπker, inf_eq_right.2 hDH₀, map_comap_eq_self_of_surjective hπs] at h1
    exact h1.symm
  have hTD : (T : Subgroup H) ⊓ kerIn M ⊤ = Q :=
    le_antisymm (hD2 _ (T.isPGroup'.to_le inf_le_left) inf_le_right) (le_inf hQT hQD)
  have hT₀map : ((T : Subgroup H) ⊓ (F ⊔ A).comap π).map π = SF ⊔ A := by
    rw [← hSL]
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨mem_map_of_mem π ht.1, ht.2⟩
    · rintro y ⟨⟨t, ht, rfl⟩, hy⟩
      exact ⟨t, ⟨ht, hy⟩, rfl⟩
  have hcardT₀ : Nat.card ↥((T : Subgroup H) ⊓ (F ⊔ A).comap π) =
      Nat.card Q * Nat.card ↥(SF ⊔ A) := by
    have h1 := card_inf_ker_mul_card_map π ((T : Subgroup H) ⊓ (F ⊔ A).comap π)
    have h2 : (T : Subgroup H) ⊓ (F ⊔ A).comap π ⊓ π.ker = Q := by
      rw [hπker, inf_assoc, inf_eq_right.2 hDH₀, hTD]
    rw [h2, hT₀map] at h1
    exact h1.symm
  have hcardL : Nat.card ↥(F ⊔ A) = Nat.card F * Nat.card A := card_sup_of_commute hFA hFAb
  have hcardSA : Nat.card ↥(SF ⊔ A) = Nat.card SF * Nat.card A :=
    card_sup_of_commute (fun s hs a ha => hFA s (hSF.le hs) a ha)
      (le_bot_iff.1 (hFAb ▸ inf_le_inf_right A hSF.le))
  have hD' : Q.relIndex (kerIn M ⊤) * Nat.card Q = Nat.card (kerIn M ⊤) := by
    have := relIndex_mul_card Q (kerIn M ⊤)
    rwa [inf_eq_left.2 hQD] at this
  have hF' : SF.relIndex F * Nat.card SF = Nat.card F := by
    have := relIndex_mul_card SF F
    rwa [inf_eq_left.2 hSF.le] at this
  have hT₀' := relIndex_mul_card ((T : Subgroup H) ⊓ (F ⊔ A).comap π) ((F ⊔ A).comap π)
  rw [inf_eq_left.2 (inf_le_right : (T : Subgroup H) ⊓ (F ⊔ A).comap π ≤ (F ⊔ A).comap π),
    hcardT₀, hcardSA, hcardH₀, hcardL, ← hD', ← hF'] at hT₀'
  have hidx : ((T : Subgroup H) ⊓ (F ⊔ A).comap π).relIndex ((F ⊔ A).comap π) =
      Q.relIndex (kerIn M ⊤) * SF.relIndex F := by
    have hpos : 0 < Nat.card Q * (Nat.card SF * Nat.card A) :=
      Nat.mul_pos Nat.card_pos (Nat.mul_pos Nat.card_pos Nat.card_pos)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hT₀']
    ring
  have hT₀syl : IsSylowOf 2 ((T : Subgroup H) ⊓ (F ⊔ A).comap π) ((F ⊔ A).comap π) := by
    rw [isSylowOf_iff]
    refine ⟨inf_le_right, T.isPGroup'.to_le inf_le_left, ?_⟩
    rw [hidx, Nat.Prime.dvd_mul Nat.prime_two]
    rintro (h | h)
    · exact hDQ h
    · exact ((isSylowOf_iff).1 hSF).2.2 h
  have hT₂ := (hT₀syl.inf_of_le_normalizer hQIH₀ hH₀QI).inf_of_le_normalizer le_sup_right
    (sup_le hQnormI le_normalizer)
  have hTIsyl : IsSylowOf 2 ((T : Subgroup H) ⊓ I) I := by
    have e : (T : Subgroup H) ⊓ (F ⊔ A).comap π ⊓ (Q ⊔ I) ⊓ I = (T : Subgroup H) ⊓ I := by
      rw [inf_assoc, inf_assoc, inf_eq_right.2 (le_sup_right : I ≤ Q ⊔ I),
        inf_eq_right.2 (le_sup_right.trans hQIH₀)]
    rwa [e] at hT₂
  have hIsub : (π.comp I.subtype).range = F ⊔ A := by
    rw [MonoidHom.range_comp, range_subtype, hIπ]
  obtain ⟨θ, hθs, hθker, hθ⟩ := exists_prodHom_of_range_eq hFA hFAb (π.comp I.subtype) hIsub
  have hθker' : θ.ker = (kerIn M ⊤).subgroupOf I := by
    rw [hθker]
    ext i
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply]
    exact hπ1 _
  set ψ : I →* F := (MonoidHom.fst ↥F ↥A).comp θ with hψdef
  have hψs : Function.Surjective ψ := Prod.fst_surjective.comp hθs
  have hdec : ∀ i : I, π (i : H) = (ψ i : H ⧸ kerIn M ⊤) * (θ i).2 := hθ
  have hψeq : ∀ (i : I) (f a : H ⧸ kerIn M ⊤), f ∈ F → a ∈ A → π (i : H) = f * a →
      (ψ i : H ⧸ kerIn M ⊤) = f := fun i f a hf ha he =>
    (eq_of_mul_eq_mul_of_inf_eq_bot hFAb (ψ i).2 hf (θ i).2.2 ha ((hdec i).symm.trans he)).1
  have hψe : ∀ i : I, (ψ i : H ⧸ kerIn M ⊤) = π (i : H) * ((θ i).2 : H ⧸ kerIn M ⊤)⁻¹ := fun i => by
    rw [hdec i, mul_inv_cancel_right]
  set J := I ⊓ A.comap π with hJdef
  have hJI : J ≤ I := inf_le_left
  have hψker : ψ.ker = J.subgroupOf I := by
    ext i
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      refine ⟨i.2, ?_⟩
      show π (i : H) ∈ A
      rw [hdec i, show (ψ i : H ⧸ kerIn M ⊤) = 1 from congrArg Subtype.val h, one_mul]
      exact (θ i).2.2
    · intro h
      exact Subtype.ext (hψeq i 1 (π (i : H)) F.one_mem h.2 (one_mul _).symm)
  have hJmap : J.map π = A := by
    apply le_antisymm
    · rintro _ ⟨j, hj, rfl⟩
      exact hj.2
    · intro a ha
      obtain ⟨i, hi, rfl⟩ : a ∈ I.map π := by
        rw [hIπ]
        exact mem_sup_right ha
      exact ⟨i, ⟨hi, ha⟩, rfl⟩
  have hNJ : kerIn M ⊤ ⊓ I ≤ J := fun y hy => ⟨hy.2, by
    show π y ∈ A
    rw [(hπ1 y).2 hy.1]
    exact A.one_mem⟩
  have hRJ' : I ⊓ Q ≤ J := fun y hy => hNJ ⟨hQD hy.2, hy.1⟩
  have hIJ : I ≤ normalizer (J : Set H) :=
    le_normalizer_of_forall_conj_mem fun i hi j hj =>
      ⟨I.mul_mem (I.mul_mem hi hj.1) (I.inv_mem hi), by
        show π (i * j * i⁻¹) ∈ A
        rw [map_mul, map_mul, map_inv, hAc (π i) (hπI i hi) (π j) hj.2, mul_inv_cancel_right]
        exact hj.2⟩
  have hDJidx : (kerIn M ⊤).relIndex J = Nat.card A := by
    have h1 := index_ker (π.comp J.subtype)
    have hk : (π.comp J.subtype).ker = (kerIn M ⊤).subgroupOf J := by
      ext j
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply]
      exact hπ1 _
    rw [hk, MonoidHom.range_comp, range_subtype, hJmap] at h1
    exact h1
  obtain ⟨P₀, hP₀⟩ := (hQ2.to_le (inf_le_right : I ⊓ Q ≤ Q)).comap_subtype (K := J)
    |>.exists_le_sylow
  set C₀ : Subgroup H := (P₀ : Subgroup J).map J.subtype with hC₀def
  have hC₀syl : IsSylowOf 2 C₀ J := ⟨P₀, rfl⟩
  have hC₀J : C₀ ≤ J := hC₀syl.le
  have hC₀2 : IsPGroup 2 C₀ := hC₀syl.isPGroup
  have hC₀idx : ¬ 2 ∣ C₀.relIndex J := ((isSylowOf_iff).1 hC₀syl).2.2
  have hRC₀ : I ⊓ Q ≤ C₀ := fun y hy => ⟨⟨y, hRJ' hy⟩, hP₀ hy, rfl⟩
  have hJNC : J ≤ (kerIn M ⊤ ⊓ J) ⊔ C₀ := by
    have h1 : ((kerIn M ⊤ ⊓ J) ⊔ C₀).relIndex J ∣ (kerIn M ⊤ ⊓ J).relIndex J :=
      relIndex_dvd_of_le_left J le_sup_left
    have h2 : ((kerIn M ⊤ ⊓ J) ⊔ C₀).relIndex J ∣ C₀.relIndex J :=
      relIndex_dvd_of_le_left J le_sup_right
    obtain ⟨n, hn⟩ := hA2.exists_card_eq
    have h4 : ((kerIn M ⊤ ⊓ J) ⊔ C₀).relIndex J ∣ 2 ^ n := by
      rw [← hn, ← hDJidx, ← inf_relIndex_right (kerIn M ⊤) J]
      exact h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    rcases m with _ | m
    · rw [pow_zero, relIndex_eq_one] at hm
      exact hm
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero m)).trans (hm ▸ h2)) hC₀idx
  have hNI : ⁅kerIn M ⊤ ⊓ J, I⁆ ≤ C₀ := by
    rw [commutator_le]
    intro n hn i hi
    refine hRC₀ ⟨?_, hDI (commutator_mem_commutator hn.1 hi)⟩
    rw [commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem (hJI hn.2) hi) (I.inv_mem (hJI hn.2))) (I.inv_mem hi)
  have hJC₀ : J ≤ normalizer (C₀ : Set H) := by
    refine hJNC.trans (sup_le ?_ le_normalizer)
    refine le_normalizer_of_forall_conj_mem fun n hn c hc => ?_
    have h1 : ⁅n, c⁆ ∈ C₀ := hNI (commutator_mem_commutator hn (hJI (hC₀J hc)))
    have e : n * c * n⁻¹ = ⁅n, c⁆ * c := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact C₀.mul_mem h1 hc
  have hIC₀ : I ≤ normalizer (C₀ : Set H) := by
    refine le_normalizer_of_forall_conj_mem fun i hi c hc => ?_
    have hle : C₀.map (MulAut.conj i).toMonoidHom ≤ C₀ := by
      refine le_of_isPGroup_of_not_dvd_relIndex hC₀2 hC₀J hC₀idx (hC₀2.map _) ?_ ?_
      · rintro _ ⟨c', hc', rfl⟩
        exact (mem_normalizer_iff.1 (hIJ hi) c').1 (hC₀J hc')
      · rintro _ ⟨c', hc', rfl⟩
        exact hJC₀ ((mem_normalizer_iff.1 (hIJ hi) c').1 (hC₀J hc'))
    exact hle ⟨c, hc, rfl⟩
  have hC₀I : ⁅C₀, I⁆ ≤ C₀ := by
    rw [commutator_le]
    intro c hc i hi
    have h1 : i * c⁻¹ * i⁻¹ ∈ C₀ := (mem_normalizer_iff.1 (hIC₀ hi) c⁻¹).1 (C₀.inv_mem hc)
    have e : ⁅c, i⁆ = c * (i * c⁻¹ * i⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact C₀.mul_mem hc h1
  have hJIc : ⁅J, I⁆ ≤ C₀ := by
    rw [commutator_comm]
    refine (commutator_mono le_rfl hJNC).trans (commutator_sup_right_le
      (inf_le_right.trans hJC₀) le_normalizer ?_ ?_)
    · rw [commutator_comm]
      exact hNI
    · rw [commutator_comm]
      exact hC₀I
  have hVJC₀ : V ⊓ J ≤ C₀ := le_of_isPGroup_of_not_dvd_relIndex hC₀2 hC₀J hC₀idx
    (hVp.to_le inf_le_left) inf_le_right (inf_le_right.trans hJC₀)
  have hC₀I' : C₀ ≤ I := hC₀J.trans hJI
  have hC₀n : (C₀.subgroupOf I).Normal := (normal_subgroupOf_iff_le_normalizer hC₀I').2 hIC₀
  have hJn : (J.subgroupOf I).Normal := (normal_subgroupOf_iff_le_normalizer hJI).2 hIJ
  set q := QuotientGroup.mk' (C₀.subgroupOf I) with hqdef
  set Zb := (J.subgroupOf I).map q with hZbdef
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq1 : ∀ i : I, q i = 1 ↔ (i : H) ∈ C₀ := fun i => by
    rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hZc : Zb ≤ center (↥I ⧸ C₀.subgroupOf I) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_center_iff]
    intro z
    obtain ⟨i, rfl⟩ := hqs z
    have h1 : ⁅(j : H), (i : H)⁆ ∈ C₀ := hJIc (commutator_mem_commutator hj i.2)
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hq1]
    have e : ((i * j * (j * i)⁻¹ : I) : H) = (⁅(j : H), (i : H)⁆)⁻¹ := by
      simp only [coe_mul, coe_inv, commutatorElement_def]
      group
    rw [e]
    exact C₀.inv_mem h1
  have hZbn : Zb.Normal := ⟨fun z hz y => by
    rw [mem_center_iff.1 (hZc hz) y, mul_inv_cancel_right]
    exact hz⟩
  have hZodd : Odd (Nat.card Zb) := by
    rw [hZbdef, hqdef, card_map_mk'_eq_relIndex, relIndex_subgroupOf hJI]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hC₀idx)
  have eYF : (↥I ⧸ C₀.subgroupOf I) ⧸ Zb ≃* ↥F :=
    (QuotientGroup.quotientQuotientEquivQuotient (C₀.subgroupOf I) (J.subgroupOf I)
      fun y hy => hC₀J hy).trans ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))
  have hW2 : ∀ w ∈ conjugate V g, w * w = 1 := fun w hw => by
    have h1 := hV2 _ (mem_conjugate_iff.1 hw)
    have e : g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [e] at h1
    calc w * w = g⁻¹ * (g * (w * w) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hgenY : closure {y : ↥I ⧸ C₀.subgroupOf I | orderOf y = 2} = ⊤ := by
    set S := closure {y : ↥I ⧸ C₀.subgroupOf I | orderOf y = 2} with hSdef
    have hinv : ∀ i : I, (i : H) * i = 1 → q i ∈ S := fun i hi => by
      by_cases h1 : q i = 1
      · rw [h1]
        exact S.one_mem
      · apply Subgroup.subset_closure
        show orderOf (q i) = 2
        apply orderOf_eq_prime _ h1
        have hii : i * i = 1 := Subtype.ext hi
        rw [pow_two, ← map_mul, hii, map_one]
    have hle : I ≤ (S.comap q).map I.subtype := sup_le
      (fun v hv => ⟨⟨v, hVI hv⟩, hinv _ (hV2 v hv), rfl⟩)
      (fun w hw => ⟨⟨w, hWI hw⟩, hinv _ (hW2 w hw), rfl⟩)
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, rfl⟩ := hqs y
    obtain ⟨i', hi', he⟩ := hle i.2
    have : i' = i := Subtype.ext he
    rw [← this]
    exact hi'
  have hEA : ∀ e ∈ E, ∀ a ∈ A, e * a = a * e := fun e he a ha =>
    hAc e (by rw [hL]; exact mem_sup_left he) a ha
  have hψV : (V.subgroupOf I).map ψ = ((E ⊔ A) ⊓ F).subgroupOf F := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      show (ψ v : H ⧸ kerIn M ⊤) ∈ (E ⊔ A) ⊓ F
      refine ⟨?_, (ψ v).2⟩
      rw [hψe v]
      exact mul_mem (mem_sup_left ⟨v, hv, rfl⟩) (mem_sup_right (A.inv_mem (θ v).2.2))
    · intro f hf
      obtain ⟨e', he', a, ha, hea⟩ := exists_mul_of_mem_sup_of_commute hEA hf.1
      obtain ⟨v, hv, rfl⟩ := he'
      have hea' : π v * a = (f : H ⧸ kerIn M ⊤) := hea
      refine ⟨⟨v, hVI hv⟩, hv, ?_⟩
      apply Subtype.ext
      exact hψeq ⟨v, hVI hv⟩ f a⁻¹ f.2 (A.inv_mem ha) (by rw [← hea', mul_inv_cancel_right])
  have hdih : ∀ ℓ a : ℕ, ℓ.Prime → ℓ ≠ 2 → 1 ≤ a → Nonempty (F ≃* DihedralGroup (ℓ ^ a)) →
      Nat.card ↥((E ⊔ A) ⊓ F) = 2 → Zb = ⊥ := by
    intro ℓ a hℓ hℓ2 ha ⟨e⟩ hcard
    have hcardψ : Nat.card ((V.subgroupOf I).map ψ) = 2 := by
      rw [hψV, ← hcard]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v₀ : I, (v₀ : H) ∈ V ∧ ψ v₀ ≠ 1 := by
      by_contra hcon
      have h1 : (V.subgroupOf I).map ψ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨v, hv, rfl⟩
        by_contra hv1
        exact hcon ⟨v, hv, hv1⟩
      rw [h1, card_bot] at hcardψ
      omega
    have hVq : ∀ v : I, (v : H) ∈ V → q v = 1 ∨ q v = q v₀ := by
      intro v hv
      by_cases h1 : ψ v = 1
      · left
        rw [hq1]
        refine hVJC₀ ⟨hv, ?_⟩
        have h2 : v ∈ J.subgroupOf I := hψker ▸ (MonoidHom.mem_ker.2 h1)
        exact h2
      · right
        have h2 : ψ v = ψ v₀ := eq_of_card_le_two hcardψ.le ⟨v, hv, rfl⟩ ⟨v₀, hv₀V, rfl⟩ h1 hv₀
        have h3 : ψ (v₀⁻¹ * v) = 1 := by rw [map_mul, map_inv, h2, inv_mul_cancel]
        have h4 : ((v₀⁻¹ * v : I) : H) ∈ C₀ := by
          refine hVJC₀ ⟨?_, ?_⟩
          · rw [coe_mul, coe_inv]
            exact V.mul_mem (V.inv_mem hv₀V) hv
          · have h5 : v₀⁻¹ * v ∈ J.subgroupOf I := hψker ▸ (MonoidHom.mem_ker.2 h3)
            exact h5
        have h5 : q (v₀⁻¹ * v) = 1 := (hq1 _).2 h4
        rw [map_mul, map_inv, inv_mul_eq_one] at h5
        exact h5.symm
    set gI : I := ⟨g, hgI⟩ with hgIdef
    set vb := q v₀ with hvbdef
    set wb := (q gI)⁻¹ * vb * q gI with hwbdef
    have hvb2 : vb * vb = 1 := by
      have hvv : v₀ * v₀ = 1 := Subtype.ext (hV2 _ hv₀V)
      rw [hvbdef, ← map_mul, hvv, map_one]
    have hwb2 : wb * wb = 1 := by
      rw [hwbdef]
      calc (q gI)⁻¹ * vb * q gI * ((q gI)⁻¹ * vb * q gI) = (q gI)⁻¹ * (vb * vb) * q gI := by
            group
        _ = 1 := by rw [hvb2]; group
    have hgen2 : closure ({vb, wb} : Set (↥I ⧸ C₀.subgroupOf I)) = ⊤ := by
      set S := closure ({vb, wb} : Set (↥I ⧸ C₀.subgroupOf I)) with hSdef
      have hle : I ≤ (S.comap q).map I.subtype := by
        refine sup_le (fun v hv => ⟨⟨v, hVI hv⟩, ?_, rfl⟩) (fun w hw => ⟨⟨w, hWI hw⟩, ?_, rfl⟩)
        · show q ⟨v, hVI hv⟩ ∈ S
          rcases hVq ⟨v, hVI hv⟩ hv with h | h
          · rw [h]
            exact S.one_mem
          · rw [h]
            exact Subgroup.subset_closure (Set.mem_insert _ _)
        · show q ⟨w, hWI hw⟩ ∈ S
          have hv : g * w * g⁻¹ ∈ V := mem_conjugate_iff.1 hw
          have e : (⟨w, hWI hw⟩ : I) = gI⁻¹ * ⟨g * w * g⁻¹, hVI hv⟩ * gI := by
            apply Subtype.ext
            rw [coe_mul, coe_mul, coe_inv, hgIdef]
            group
          rw [e, map_mul, map_mul, map_inv]
          rcases hVq ⟨_, hVI hv⟩ hv with h | h
          · rw [h, mul_one, inv_mul_cancel]
            exact S.one_mem
          · rw [h]
            exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      rw [eq_top_iff]
      intro y _
      obtain ⟨i, rfl⟩ := hqs y
      obtain ⟨i', hi', he⟩ := hle i.2
      have : i' = i := Subtype.ext he
      rw [← this]
      exact hi'
    rw [eq_bot_iff]
    intro z hz
    rcases sq_eq_one_of_mem_center_of_closure_pair hvb2 hwb2 hgen2 (hZc hz) with h | h
    · have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      have h2 : orderOf z ∣ Nat.card Zb := by
        rw [← orderOf_mk z hz]
        exact orderOf_dvd_natCard _
      have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hZodd) h1 h2
      exact mem_bot.2 (orderOf_eq_one_iff.1 h3)
    · exfalso
      have hℓ3 : 3 ≤ ℓ ^ a := by
        have h1 : 3 ≤ ℓ := by
          have := hℓ.two_le
          rcases Nat.lt_or_ge ℓ 3 with h3 | h3
          · interval_cases ℓ
            exact absurd rfl hℓ2
          · exact h3
        calc 3 ≤ ℓ := h1
          _ = ℓ ^ 1 := (pow_one ℓ).symm
          _ ≤ ℓ ^ a := Nat.pow_le_pow_right hℓ.pos ha
      refine dihedral_not_comm hℓ3 fun u u' => ?_
      obtain ⟨y, rfl⟩ := (eYF.trans e).surjective u
      obtain ⟨y', rfl⟩ := (eYF.trans e).surjective u'
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective Zb y
      obtain ⟨y₀', rfl⟩ := QuotientGroup.mk'_surjective Zb y'
      have := congrArg (fun t => (eYF.trans e) (QuotientGroup.mk' Zb t)) (h y₀ y₀')
      simpa only [map_mul] using this
  have hZb : Zb = ⊥ := by
    rcases hF with ⟨ℓ, a, hℓ, hℓ2, ha, he, hcard⟩ | ⟨f, k, _, hf, hk, ⟨e⟩⟩ |
        ⟨b, k, _, hb, hk, ⟨e⟩⟩
    · exact hdih ℓ a hℓ hℓ2 ha he hcard
    · exact (unique_involution_generated_odd_central_linear_or_suzuki_cover_is_exact.{_, 0}
        hgenY Zb hZc hZodd (Or.inl ⟨f, k, inferInstance, hf, hk, ⟨eYF.trans e⟩⟩)).1
    · exact (unique_involution_generated_odd_central_linear_or_suzuki_cover_is_exact.{_, 0}
        hgenY Zb hZc hZodd (Or.inr ⟨b, k, inferInstance, hb, hk, ⟨eYF.trans e⟩⟩)).1
  have hJC₀' : J ≤ C₀ := fun y hy => by
    have h1 : q ⟨y, hJI hy⟩ ∈ Zb := ⟨⟨y, hJI hy⟩, hy, rfl⟩
    rw [hZb, mem_bot, hq1] at h1
    exact h1
  have hID : I ⊓ kerIn M ⊤ = I ⊓ Q := by
    apply le_antisymm
    · intro y hy
      exact ⟨hy.1, hD2 (C₀ ⊓ kerIn M ⊤) (hC₀2.to_le inf_le_left) inf_le_right
        ⟨hJC₀' (hNJ ⟨hy.2, hy.1⟩), hy.2⟩⟩
    · exact inf_le_inf_left I hQD
  have hθker'' : θ.ker = (I ⊓ Q).subgroupOf I := by
    rw [hθker']
    ext i
    rw [mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro h
      exact hID ▸ (⟨i.2, h⟩ : (i : H) ∈ I ⊓ kerIn M ⊤)
    · intro h
      exact hQD h.2
  have hcomapM : ∀ y : H, π y ∈ M.map π → y ∈ M := fun y hy => by
    obtain ⟨m, hm, he⟩ := hy
    have h1 : m⁻¹ * y ∈ kerIn M ⊤ := (hπ1 _).1 (by rw [map_mul, map_inv, he, inv_mul_cancel])
    have h2 := M.mul_mem hm (hDM h1)
    rwa [mul_inv_cancel_left] at h2
  have hJker : J = kerIn (M ⊓ I) I := by
    apply le_antisymm
    · intro j hj
      rw [mem_kerIn]
      intro b hb
      have hbj : b * j * b⁻¹ ∈ I := I.mul_mem (I.mul_mem hb (hJI hj)) (I.inv_mem hb)
      refine ⟨hcomapM _ ?_, hbj⟩
      have h1 : π (b * j * b⁻¹) = π j := by
        rw [map_mul, map_mul, map_inv, hAc (π b) (hπI b hb) (π j) hj.2, mul_inv_cancel_right]
      have h2 : π j ∈ M.map π ⊓ (F ⊔ A) := by
        rw [hBL]
        exact mem_sup_right hj.2
      rw [h1]
      exact h2.1
    · intro y hy
      rw [mem_kerIn] at hy
      have hyMI : y ∈ M ⊓ I := by simpa using hy 1 (one_mem I)
      refine ⟨hyMI.2, ?_⟩
      show π y ∈ A
      set yI : I := ⟨y, hyMI.2⟩ with hyIdef
      have hf : (ψ yI : H ⧸ kerIn M ⊤) ∈ kerIn PF F := by
        rw [mem_kerIn]
        intro f' hf'
        obtain ⟨b, hb, rfl⟩ : f' ∈ I.map π := by
          rw [hIπ]
          exact mem_sup_left hf'
        have h1 := hy b hb
        have h2 : π (b * y * b⁻¹) ∈ PF ⊔ A := by
          rw [← hBL]
          exact ⟨⟨_, h1.1, rfl⟩, hπI _ h1.2⟩
        have hcomm : ((θ yI).2 : H ⧸ kerIn M ⊤) * (π b)⁻¹ = (π b)⁻¹ * (θ yI).2 :=
          (hAc (π b)⁻¹ (inv_mem (hπI b hb)) _ (θ yI).2.2).symm
        have e : π (b * y * b⁻¹) = π b * ψ yI * (π b)⁻¹ * (θ yI).2 := by
          rw [map_mul, map_mul, map_inv, show π y = π (yI : H) from rfl, hdec yI]
          calc π b * ((ψ yI : H ⧸ kerIn M ⊤) * (θ yI).2) * (π b)⁻¹ =
                π b * ψ yI * (((θ yI).2 : H ⧸ kerIn M ⊤) * (π b)⁻¹) := by simp only [mul_assoc]
            _ = π b * ψ yI * ((π b)⁻¹ * (θ yI).2) := by rw [hcomm]
            _ = π b * ψ yI * (π b)⁻¹ * (θ yI).2 := by simp only [mul_assoc]
        rw [e] at h2
        have h3 : π b * ψ yI * (π b)⁻¹ ∈ (PF ⊔ A) ⊓ F := by
          refine ⟨?_, F.mul_mem (F.mul_mem hf' (ψ yI).2) (F.inv_mem hf')⟩
          have := mul_mem h2 (mem_sup_right (A.inv_mem (θ yI).2.2) : _ ∈ PF ⊔ A)
          rwa [mul_inv_cancel_right] at this
        rwa [sup_inf_eq_of_le hFA hFAb hPF] at h3
      rw [hPFcore, mem_bot] at hf
      rw [show π y = π (yI : H) from rfl, hdec yI, hf, one_mul]
      exact (θ yI).2.2
  have hJ2 : IsPGroup 2 J := hC₀2.to_le hJC₀'
  have hJO : J = inSubgroup (pCore 2) I := by
    refine le_antisymm (le_inSubgroup_pCore hJI hIJ hJ2) ?_
    have hFO' : pCore 2 ↥F = ⊥ := (map_eq_bot_iff_of_injective _ F.subtype_injective).1 hFO
    have hn : ((pCore 2 ↥I).map ψ).Normal := (pCore_normal (p := 2) (G := ↥I)).map ψ hψs
    have hbot : (pCore 2 ↥I).map ψ ≤ pCore 2 ↥F :=
      le_pCore_of_normal ((pCore_isPGroup (p := 2) (G := ↥I)).map ψ)
    have h1 : pCore 2 ↥I ≤ J.subgroupOf I := by
      rw [← hψker]
      intro i hi
      have h3 := hbot (mem_map_of_mem ψ hi)
      rw [hFO', mem_bot] at h3
      exact MonoidHom.mem_ker.2 h3
    calc inSubgroup (pCore 2) I = (pCore 2 ↥I).map I.subtype := rfl
      _ ≤ (J.subgroupOf I).map I.subtype := map_mono h1
      _ = J := map_subgroupOf_eq_of_le hJI
  let κ : J →* A := (π.comp J.subtype).codRestrict A fun j => j.2.2
  have hκs : Function.Surjective κ := by
    intro a
    obtain ⟨i, hi, hia⟩ : (a : H ⧸ kerIn M ⊤) ∈ I.map π := by
      rw [hIπ]
      exact mem_sup_right a.2
    exact ⟨⟨i, hi, by show π i ∈ A; rw [hia]; exact a.2⟩, Subtype.ext hia⟩
  have hκker : κ.ker = (I ⊓ Q).subgroupOf J := by
    ext j
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : π (j : H) = 1 := congrArg Subtype.val h
      exact hID ▸ (⟨hJI j.2, (hπ1 _).1 h1⟩ : (j : H) ∈ I ⊓ kerIn M ⊤)
    · intro h
      exact Subtype.ext ((hπ1 _).2 (hQD h.2))
  have hQJ : Q ≤ normalizer (J : Set H) := by
    refine le_normalizer_of_forall_conj_mem fun q hq j hj => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.1 (hQnormI hq) j).1 (hJI hj)
    · show π (q * j * q⁻¹) ∈ A
      rw [map_mul, map_mul, map_inv, (hπ1 q).2 (hQD hq), one_mul, inv_one, mul_one]
      exact hj.2
  have hQJ2 : IsPGroup 2 ↥(Q ⊔ J) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hJ2 fun j _ => hQnorm j
  have hQIO : inSubgroup (pCore 2) (Q ⊔ I) = Q ⊔ J := by
    have hO'2 : IsPGroup 2 (inSubgroup (pCore 2) (Q ⊔ I)) :=
      (pCore_isPGroup (p := 2) (G := ↥(Q ⊔ I))).map _
    have hQIO' : Q ⊔ I ≤ normalizer (inSubgroup (pCore 2) (Q ⊔ I) : Set H) :=
      le_normalizer.trans (normalizer_le_normalizer_map_characteristic (Q ⊔ I) (pCore 2 _))
    have hQO : Q ≤ inSubgroup (pCore 2) (Q ⊔ I) :=
      le_inSubgroup_pCore le_sup_left (fun y _ => hQnorm y) hQ2
    apply le_antisymm
    · intro o ho
      have hoQI : o ∈ ((Q ⊔ I : Subgroup H) : Set H) := map_subtype_le _ ho
      rw [normal_mul Q I, Set.mem_mul] at hoQI
      obtain ⟨q, hq, i, hi, rfl⟩ := hoQI
      have hiO : i ∈ inSubgroup (pCore 2) (Q ⊔ I) := by
        have := mul_mem (inv_mem (hQO hq)) ho
        rwa [inv_mul_cancel_left] at this
      have hiJ : i ∈ J := by
        rw [hJO]
        exact le_inSubgroup_pCore inf_le_right
          (fun y hy => inf_normalizer_le_normalizer_inf
            ⟨hQIO' (mem_sup_right hy), le_normalizer hy⟩)
          (hO'2.to_le inf_le_left) ⟨hiO, hi⟩
      exact mul_mem_sup hq hiJ
    · refine le_inSubgroup_pCore (sup_le le_sup_left (hJI.trans le_sup_right)) (sup_le ?_ ?_) hQJ2
      · exact fun y hy => C1.mem_normalizer_sup (hQnorm y) (hQJ hy)
      · exact fun y hy => C1.mem_normalizer_sup (hQnorm y) (hIJ hy)
  have hchar' : centralizer (Q : Set H) ≤ Q := hchar
  have hcharL : centralizer (CFSG.Open.pCore 2 ↥(Q ⊔ I) : Set ↥(Q ⊔ I)) ≤
      CFSG.Open.pCore 2 ↥(Q ⊔ I) := by
    have hQL : Q.subgroupOf (Q ⊔ I) ≤ pCore 2 ↥(Q ⊔ I) :=
      le_pCore_of_normal (pCore_isPGroup (p := 2) (G := H)).comap_subtype
    intro c hc
    have hcQ : (c : H) ∈ centralizer (Q : Set H) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hqL : (⟨q, mem_sup_left hq⟩ : ↥(Q ⊔ I)) ∈ pCore 2 ↥(Q ⊔ I) := hQL hq
      exact congrArg Subtype.val (mem_centralizer_iff.1 hc _ hqL)
    exact hQL (show c ∈ Q.subgroupOf (Q ⊔ I) from hchar' hcQ)
  have hcharI : IsCharacteristicP 2 I := by
    change centralizer (pCore 2 I : Set I) ≤ pCore 2 I
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroupOf_self_centralizing_pCore 2
      Nat.prime_two I (Q ⊔ I) le_sup_right hInorm hcharL
  have hSFPF : SF ≤ PF := hPFO ▸ map_subtype_le _
  have hcentN : ∀ K : Subgroup (H ⧸ kerIn M ⊤), ∀ y : H ⧸ kerIn M ⊤,
      (∀ k ∈ K, y * k = k * y) → y ∈ normalizer (K : Set (H ⧸ kerIn M ⊤)) := by
    intro K y hy
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hy k hk, mul_inv_cancel_right]
      exact hk
    · intro hk
      have h1 := hy _ hk
      have e : k = y * k * y⁻¹ := by
        calc k = y⁻¹ * ((y * k * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * k * y⁻¹)) := by rw [h1]
          _ = y * k * y⁻¹ := by group
      rw [e]
      exact hk
  have hPFAn : PF ⊔ A ≤ normalizer ((SF ⊔ A : Subgroup (H ⧸ kerIn M ⊤)) : Set (H ⧸ kerIn M ⊤)) := by
    have hPFSF : PF ≤ normalizer (SF : Set (H ⧸ kerIn M ⊤)) := by
      rw [← hPFO]
      exact le_normalizer.trans (normalizer_le_normalizer_map_characteristic PF (pCore 2 PF))
    refine sup_le (fun y hy => C1.mem_normalizer_sup (hPFSF hy) (hcentN A y fun a ha =>
      hFA y (hPF hy) a ha)) (fun a ha => C1.mem_normalizer_sup (hcentN SF a fun s hs =>
      (hFA s (hSF.le hs) a ha).symm) (le_normalizer ha))
  have hSFA2 : IsPGroup 2 ↥(SF ⊔ A) :=
    IsPGroup.to_sup_of_normal_left' hSF.isPGroup hA2 fun a ha =>
      hcentN SF a fun s hs => (hFA s (hSF.le hs) a ha).symm
  set P := (M ⊓ I) ⊓ (SF ⊔ A).comap π with hPdef
  have hTIP : (T : Subgroup H) ⊓ I ≤ P := fun t ht => ⟨⟨hTM ht.1, ht.2⟩, by
    show π t ∈ SF ⊔ A
    rw [← hSL]
    exact ⟨⟨t, ht.1, rfl⟩, hπI t ht.2⟩⟩
  have hP2 : IsPGroup 2 P := by
    refine isPGroup_of_pow_mem (hQ2.to_le (inf_le_right : I ⊓ Q ≤ Q)) fun y hy => ?_
    obtain ⟨n, hn⟩ := hSFA2 ⟨π y, hy.2⟩
    have h1 : π (y ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    exact ⟨n, hID ▸ (⟨I.pow_mem hy.1.2 _, (hπ1 _).1 h1⟩ : y ^ 2 ^ n ∈ I ⊓ kerIn M ⊤)⟩
  have hPeq : P = (T : Subgroup H) ⊓ I :=
    hTIsyl.eq_of_le hTIP (inf_le_left.trans inf_le_right) hP2
  have hPn : M ⊓ I ≤ normalizer (P : Set H) := by
    refine le_normalizer_of_forall_conj_mem fun m hm y hy =>
      ⟨⟨M.mul_mem (M.mul_mem hm.1 hy.1.1) (M.inv_mem hm.1),
        I.mul_mem (I.mul_mem hm.2 hy.1.2) (I.inv_mem hm.2)⟩, ?_⟩
    show π (m * y * m⁻¹) ∈ SF ⊔ A
    rw [map_mul, map_mul, map_inv]
    have hm' : π m ∈ PF ⊔ A := by
      rw [← hBL]
      exact ⟨⟨m, hm.1, rfl⟩, hπI m hm.2⟩
    exact (mem_normalizer_iff.1 (hPFAn hm') (π y)).1 hy.2
  have hO2MI : inSubgroup (pCore 2) (M ⊓ I) = (T : Subgroup H) ⊓ I := by
    apply le_antisymm
    · obtain ⟨S', hS'⟩ := hTIsyl.of_le (inf_le_inf_right I hTM) inf_le_right
      rw [← hS']
      exact map_mono ((pCore_isPGroup (p := 2) (G := ↥(M ⊓ I))).le_sylow_of_normal S')
    · rw [← hPeq]
      exact le_inSubgroup_pCore inf_le_left hPn hP2
  have hNV : I ⊓ normalizer (V : Set H) ≤ M ⊓ I := by
    have hlt : normalizer (V : Set H) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hVQ ?_
      have hVn : V.Normal := normalizer_eq_top_iff.1 htop
      exact le_sSup ⟨hVn, hVp⟩
    have hNM := hmax _ hTV hlt
    exact fun y hy => ⟨hNM hy.2, hy.1⟩
  have hψM : ((M ⊓ I).subgroupOf I).map ψ = PF.subgroupOf F := by
    apply le_antisymm
    · rintro _ ⟨i, hi, rfl⟩
      show (ψ i : H ⧸ kerIn M ⊤) ∈ PF
      have h1 : π (i : H) ∈ PF ⊔ A := by
        rw [← hBL]
        exact ⟨⟨i, hi.1, rfl⟩, hπI i i.2⟩
      rw [← sup_inf_eq_of_le hFA hFAb hPF]
      refine ⟨?_, (ψ i).2⟩
      rw [hψe i]
      exact mul_mem h1 (mem_sup_right (A.inv_mem (θ i).2.2))
    · intro f hf
      have hfB : (f : H ⧸ kerIn M ⊤) ∈ M.map π := by
        have h1 : (f : H ⧸ kerIn M ⊤) ∈ M.map π ⊓ (F ⊔ A) := by
          rw [hBL]
          exact mem_sup_left hf
        exact h1.1
      obtain ⟨i, hi, hif⟩ : (f : H ⧸ kerIn M ⊤) ∈ I.map π := by
        rw [hIπ]
        exact mem_sup_left f.2
      refine ⟨⟨i, hi⟩, ⟨hcomapM i (hif ▸ hfB), hi⟩, ?_⟩
      apply Subtype.ext
      exact hψeq ⟨i, hi⟩ f 1 f.2 A.one_mem (by rw [mul_one]; exact hif)
  have hψT : (((T : Subgroup H) ⊓ I).subgroupOf I).map ψ = SF.subgroupOf F := by
    apply le_antisymm
    · rintro _ ⟨i, hi, rfl⟩
      show (ψ i : H ⧸ kerIn M ⊤) ∈ SF
      have h1 : π (i : H) ∈ SF ⊔ A := by
        rw [← hSL]
        exact ⟨⟨i, hi.1, rfl⟩, hπI i i.2⟩
      rw [← sup_inf_eq_of_le hFA hFAb hSF.le]
      refine ⟨?_, (ψ i).2⟩
      rw [hψe i]
      exact mul_mem h1 (mem_sup_right (A.inv_mem (θ i).2.2))
    · intro f hf
      obtain ⟨i, hi, hif⟩ : (f : H ⧸ kerIn M ⊤) ∈ I.map π := by
        rw [hIπ]
        exact mem_sup_left f.2
      have hiM : i ∈ M := by
        refine hcomapM i ?_
        have h1 : (f : H ⧸ kerIn M ⊤) ∈ M.map π ⊓ (F ⊔ A) := by
          rw [hBL]
          exact mem_sup_left (hSFPF hf)
        rw [hif]
        exact h1.1
      have hiP : i ∈ P := ⟨⟨hiM, hi⟩, by
        show π i ∈ SF ⊔ A
        rw [hif]
        exact mem_sup_left hf⟩
      refine ⟨⟨i, hi⟩, hPeq ▸ hiP, ?_⟩
      apply Subtype.ext
      exact hψeq ⟨i, hi⟩ f 1 f.2 A.one_mem (by rw [mul_one]; exact hif)
  refine ⟨g, hgI, hVltI, hgx, ?_⟩
  exact ⟨hIπ, hH₀, hInorm, hQIH₀, hQIn, hQnormI, hDI, hTIsyl, hID,
    ⟨θ, hθs, hθker'', hθ⟩, hJker, hJO, ⟨κ, hκs, hκker, fun j => rfl⟩, hQIO, hcharI, hO2MI,
    hNV, ψ, hψs, hψker, fun i => ⟨(θ i).2, (θ i).2.2, hdec i⟩, hψM, hψT, hψV⟩

end CFSG.Quasithin.H13.QRC
