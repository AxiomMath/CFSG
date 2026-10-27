module

public import CFSG.Quasithin.H13.NQS13410L
public import CFSG.Quasithin.H13.NQS13410F
public import CFSG.Quasithin.H13.NQS13410H
public import CFSG.Quasithin.H13.U3S13227

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G]

omit [Group G] in
theorem eq_of_mul_eq_mul {G : Type} [Group G] {I₀ I₁ : Subgroup G} (hinf : I₀ ⊓ I₁ = ⊥)
    {a a' b b' : G} (ha : a ∈ I₀) (ha' : a' ∈ I₀) (hb : b ∈ I₁) (hb' : b' ∈ I₁)
    (h : a' * b' = a * b) : a' = a ∧ b' = b := by
  have h1 : a⁻¹ * a' = b * b'⁻¹ := by
    calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
      _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
      _ = b * b'⁻¹ := by group
  have h2 : a⁻¹ * a' ∈ I₀ ⊓ I₁ :=
    mem_inf.2 ⟨mul_mem (inv_mem ha) ha', h1 ▸ mul_mem hb (inv_mem hb')⟩
  rw [hinf, mem_bot] at h2
  have h3 : a' = a := by
    calc a' = a * (a⁻¹ * a') := by group
      _ = a := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

omit [Group G] in
theorem conj_eq_of_mul {G : Type} [Group G] {I₀ I₁ : Subgroup G} (hinf : I₀ ⊓ I₁ = ⊥) {g a b : G}
    (ha : a ∈ I₀) (hb : b ∈ I₁) (hg₀ : g ∈ normalizer (I₀ : Set G))
    (hg₁ : g ∈ normalizer (I₁ : Set G)) (h : g * (a * b) * g⁻¹ = a * b) :
    g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b := by
  refine eq_of_mul_eq_mul hinf ha ((mem_normalizer_iff.mp hg₀ a).mp ha) hb
    ((mem_normalizer_iff.mp hg₁ b).mp hb) ?_
  rw [← h]
  group

theorem card_mul_le_card_sup [Finite G] {I₀ I₁ : Subgroup G} (hinf : I₀ ⊓ I₁ = ⊥) :
    Nat.card ↥I₀ * Nat.card ↥I₁ ≤ Nat.card ↥(I₀ ⊔ I₁) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun ab : ↥I₀ × ↥I₁ => (⟨ab.1 * ab.2, mul_mem (mem_sup_left ab.1.2)
      (mem_sup_right ab.2.2)⟩ : ↥(I₀ ⊔ I₁))) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
  obtain ⟨h2, h3⟩ := eq_of_mul_eq_mul hinf a'.2 a.2 b'.2 b.2 h1
  exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)

theorem card_inf_centralizer_le [Finite G] {I₀ I₁ A : Subgroup G} (hinf : I₀ ⊓ I₁ = ⊥)
    (hI₁ : I₁ ≤ normalizer (I₀ : Set G)) (hA₀ : A ≤ normalizer (I₀ : Set G))
    (hA₁ : A ≤ normalizer (I₁ : Set G)) :
    Nat.card ↥((I₀ ⊔ I₁) ⊓ centralizer (A : Set G)) ≤
      Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) * Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun ab : ↥(I₀ ⊓ centralizer (A : Set G)) × ↥(I₁ ⊓ centralizer (A : Set G)) =>
      (⟨ab.1 * ab.2, mem_inf.2 ⟨mul_mem (mem_sup_left (mem_inf.1 ab.1.2).1)
        (mem_sup_right (mem_inf.1 ab.2.2).1),
        mul_mem (mem_inf.1 ab.1.2).2 (mem_inf.1 ab.2.2).2⟩⟩ :
          ↥((I₀ ⊔ I₁) ⊓ centralizer (A : Set G)))) ?_
  rintro ⟨u, hu⟩
  obtain ⟨hu₁, hu₂⟩ := mem_inf.1 hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁ hu₁
  have hfix : ∀ g ∈ A, g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b := fun g hg =>
    conj_eq_of_mul hinf ha hb (hA₀ hg) (hA₁ hg) (by
      rw [mem_centralizer_iff.mp hu₂ g hg, mul_inv_cancel_right])
  have haC : a ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun g hg => by
    have h1 := (hfix g hg).1
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h1]
  have hbC : b ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun g hg => by
    have h1 := (hfix g hg).2
    calc g * b = g * b * g⁻¹ * g := by group
      _ = b * g := by rw [h1]
  exact ⟨(⟨a, mem_inf.2 ⟨ha, haC⟩⟩, ⟨b, mem_inf.2 ⟨hb, hbC⟩⟩), rfl⟩

theorem card_le_four_of_lt [Finite G] {I Y : Subgroup G} (hI : Nat.card ↥I = 8) (hYI : Y ≤ I)
    (hne : Y ≠ I) : Nat.card ↥Y ≤ 4 := by
  have h1 : Nat.card ↥Y ∣ Nat.card ↥I := Subgroup.card_dvd_of_le hYI
  rw [hI] at h1
  have h2 : Nat.card ↥Y ≠ 8 := fun h => hne (Subgroup.eq_of_le_of_card_ge hYI (by rw [h, hI]))
  have h3 : Nat.card ↥Y ≤ 8 := Nat.le_of_dvd (by norm_num) h1
  interval_cases (Nat.card ↥Y) <;> simp_all

theorem card_eq_eight_of_l32 [Finite G] {K X : Subgroup G} [IsMulCommutative ↥X]
    (hnat : BinaryNaturalSL (V := ↥X) (autOn K X) ⊤ ⊥ 3 1) : Nat.card ↥X = 8 := by
  classical
  obtain ⟨D⟩ := hnat.toL3Coord
  have hinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (mem_bot.1 ((D.ker_β u).1 hu))
  have h2 := Nat.card_congr (Equiv.ofBijective D.β ⟨hinj, D.β_surj⟩)
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_fin] at h2
  rw [h2]
  norm_num

theorem exists_mem_centralizer_ne_one [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hUn : T ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ u ∈ U, u ∈ centralizer (T : Set G) ∧ u ≠ 1 := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, mem_centralizer_iff.2 fun t ht =>
    (congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)), fun h => hy1 ?_⟩
  exact Subtype.ext (Subtype.ext h)

variable [Finite G] {T L V : Subgroup G}

theorem not_case1ii_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnatW : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hWU : W ≤ ⁅reducedAggregate (K ⊔ T), K⁆) (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    [IsMulCommutative ↥(reducedAggregate (K ⊔ T))]
    {J : Subgroup (MulAut ↥(reducedAggregate (K ⊔ T)))}
    (hii : B51Case1ii J (autOn K (reducedAggregate (K ⊔ T))))
    (hZ : quasithinOmegaOneCenter T ≤ ⁅reducedAggregate (K ⊔ T), K⁆ ⊔ U3.cZ T K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R2 := reducedAggregate (K ⊔ T) with hR2def
  set U := ⁅R2, K⁆ with hUdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hRdef
  set Q := pCoreOf 2 (K ⊔ T) with hQdef
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hred := twoReduced_R2 (K ⊔ T)
  have hR2e : IsElemAbelian 2 R2 := hred.2.2.1
  have hcomm : ∀ a ∈ R2, ∀ b ∈ R2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR2e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKR2 : K ≤ normalizer (R2 : Set G) := le_sup_left.trans hred.2.1
  have hR2Q : R2 ≤ Q := R2_le_pCoreOf (K ⊔ T)
  have hQC : Q ≤ centralizer (R2 : Set G) := pCoreOf_le_centralizer_R2 (K ⊔ T)
  have hQT : Q ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl
  have hQ2 : IsPGroup 2 ↥Q := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hKTQ : K ⊔ T ≤ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have h168 : Nat.card ↥(autOn K R2) ≤ 168 := by
    have h1 := U3.card_autOn_le_card_quot hKR2
      ((A6.pCoreOf_le_pCoreOf_sup hTK).trans hQC)
    rwa [card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 hK3)] at h1
  obtain ⟨I₀, I₁, hI₀R, hI₁R, hKI₀, hKI₁, hinf, hsup, ⟨hc₀, hnat₀⟩, φ, hφ⟩ :=
    exists_two_copies hKR2 hii h168
  have hc₁ : IsMulCommutative ↥I₁ := isMulCommutative_of_le' hI₁R
  have hsup' : I₀ ⊔ I₁ = U := hsup
  have hUR2 : U ≤ R2 := by rw [← hsup']; exact sup_le hI₀R hI₁R
  have hI₀U : I₀ ≤ U := by rw [← hsup']; exact le_sup_left
  have hI₁U : I₁ ≤ U := by rw [← hsup']; exact le_sup_right
  have hUe : IsElemAbelian 2 U := ⟨isMulCommutative_of_le' hUR2, fun u hu => hR2e.2 u (hUR2 hu)⟩
  have hU2 : IsPGroup 2 ↥U := fun u => ⟨1, Subtype.ext (by simpa using hUe.2 u u.2)⟩
  have hnorm : ∀ {A B : Subgroup G}, A ≤ R2 → B ≤ R2 → B ≤ normalizer (A : Set G) :=
    fun {A B} hA hB => A5.le_normalizer_of_forall_conj_mem fun b hb a ha => by
      rw [hcomm b (hB hb) a (hA ha), mul_inv_cancel_right]
      exact ha
  have hI₁N : I₁ ≤ normalizer (I₀ : Set G) := hnorm hI₀R hI₁R
  have h8₀ : Nat.card ↥I₀ = 8 := card_eq_eight_of_l32 hnat₀
  have h8₁ : Nat.card ↥I₁ = 8 := by
    have := Nat.card_congr φ.toEquiv
    rw [← this, h8₀]
  have hU64 : 64 ≤ Nat.card ↥U := by
    have := card_mul_le_card_sup hinf
    rw [h8₀, h8₁, hsup'] at this
    exact this
  have htopW := autOn_eq_top_of_l32 hnatW
  have hCW2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
    rw [← ho2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  have hTact : ∀ t ∈ T, ∃ k ∈ K, ∀ u ∈ R2, t * u * t⁻¹ = k * u * k⁻¹ := fun t ht =>
    exists_conj_R2 hTsyl hTK hKW hTW htopW hCW2 ht
  have hTI : ∀ {I : Subgroup G}, I ≤ R2 → K ≤ normalizer (I : Set G) →
      T ≤ normalizer (I : Set G) := fun {I} hIR hKI =>
    A5.le_normalizer_of_forall_conj_mem fun t ht x hx => by
      obtain ⟨k, hk, hkt⟩ := hTact t ht
      rw [hkt x (hIR hx)]
      exact (mem_normalizer_iff.mp (hKI hk) x).mp hx
  have hTI₀ := hTI hI₀R hKI₀
  have hTI₁ := hTI hI₁R hKI₁
  have hKU : K ≤ normalizer (U : Set G) := A5.le_normalizer_of_forall_conj_mem fun k hk x hx => by
    rw [← hsup'] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hKI₀ hk) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hKI₁ hk) b).mp hb))
  have hTU : T ≤ normalizer (U : Set G) := A5.le_normalizer_of_forall_conj_mem fun t ht x hx => by
    rw [← hsup'] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have e : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hTI₀ ht) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hTI₁ ht) b).mp hb))
  have hφT : ∀ t ∈ T, ∀ (u : ↥I₀) (hu : t * (u : G) * t⁻¹ ∈ I₀),
      ((φ ⟨t * u * t⁻¹, hu⟩ : ↥I₁) : G) = t * (φ u : G) * t⁻¹ := by
    intro t ht u hu
    obtain ⟨k, hk, hkt⟩ := hTact t ht
    have hu' : k * (u : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp u.2
    have e1 : (⟨t * u * t⁻¹, hu⟩ : ↥I₀) = ⟨k * u * k⁻¹, hu'⟩ := Subtype.ext (hkt u (hI₀R u.2))
    rw [e1, hφ k hk u hu', hkt _ (hI₁R (φ u).2)]
  have hCI₀₁ : ∀ k ∈ K, k ∈ centralizer (I₀ : Set G) → k ∈ centralizer (I₁ : Set G) := by
    intro k hk hkC
    rw [mem_centralizer_iff]
    intro v hv
    set u : ↥I₀ := φ.symm ⟨v, hv⟩ with hu
    have hφu : φ u = ⟨v, hv⟩ := by rw [hu, MulEquiv.apply_symm_apply]
    have hku : k * (u : G) * k⁻¹ = u := by
      rw [← mem_centralizer_iff.mp hkC u u.2, mul_inv_cancel_right]
    have hu' : k * (u : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp u.2
    have h1 := hφ k hk u hu'
    have h2 : (⟨k * (u : G) * k⁻¹, hu'⟩ : ↥I₀) = u := Subtype.ext hku
    rw [h2, hφu] at h1
    have h3 : k * v * k⁻¹ = v := h1.symm
    calc v * k = k * v * k⁻¹ * k := by rw [h3]
      _ = k * v := by group
  have hCI₁₀ : ∀ k ∈ K, k ∈ centralizer (I₁ : Set G) → k ∈ centralizer (I₀ : Set G) := by
    intro k hk hkC
    rw [mem_centralizer_iff]
    intro u hu
    have hu' : k * u * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp hu
    have h1 := hφ k hk ⟨u, hu⟩ hu'
    have h2 : k * (φ ⟨u, hu⟩ : G) * k⁻¹ = φ ⟨u, hu⟩ := by
      rw [← mem_centralizer_iff.mp hkC _ (φ ⟨u, hu⟩).2, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 := φ.injective (Subtype.ext h1)
    have h4 : k * u * k⁻¹ = u := congrArg Subtype.val h3
    calc u * k = k * u * k⁻¹ * k := by rw [h4]
      _ = k * u := by group
  have hCKU : ∀ k ∈ K, k ∈ centralizer (I₀ : Set G) → k ∈ centralizer (U : Set G) := by
    intro k hk hkC
    have hk₁ := hCI₀₁ k hk hkC
    rw [mem_centralizer_iff]
    intro x hx
    rw [← hsup'] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    calc a * b * k = a * (k * b) := by rw [mul_assoc, mem_centralizer_iff.mp hk₁ b hb]
      _ = k * (a * b) := by rw [← mul_assoc, mem_centralizer_iff.mp hkC a ha, mul_assoc]
  have hCK₀ : IsPGroup 2 ↥(K ⊓ centralizer (I₀ : Set G)) := hCW2.to_le fun k hk =>
    mem_inf.2 ⟨(mem_inf.1 hk).1, centralizer_le (SetLike.coe_subset_coe.mpr hWU)
      (hCKU k (mem_inf.1 hk).1 (mem_inf.1 hk).2)⟩
  have hCK₁ : IsPGroup 2 ↥(K ⊓ centralizer (I₁ : Set G)) := hCK₀.to_le fun k hk =>
    mem_inf.2 ⟨(mem_inf.1 hk).1, hCI₁₀ k (mem_inf.1 hk).1 (mem_inf.1 hk).2⟩
  have hQ₀ : T ⊓ centralizer (I₀ : Set G) = Q :=
    U3.inf_centralizer_eq_pCoreOf_sup hTsyl hTK hKI₀ hTI₀
      (le_centralizer_iff.mp (hQC.trans (centralizer_le hI₀R))) hCK₀
  have hQ₁ : T ⊓ centralizer (I₁ : Set G) = Q :=
    U3.inf_centralizer_eq_pCoreOf_sup hTsyl hTK hKI₁ hTI₁
      (le_centralizer_iff.mp (hQC.trans (centralizer_le hI₁R))) hCK₁
  have hQU : Q ≤ centralizer (U : Set G) := hQC.trans (centralizer_le hUR2)
  have hI₀T : I₀ ≤ T := hI₀R.trans (hR2Q.trans hQT)
  have hI₀1 : I₀ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at h8₀; omega
  obtain ⟨x₀', hx₀I, hx₀T, hx₀1'⟩ :=
    exists_mem_centralizer_ne_one hKf.1.1 hI₀T hTI₀ hI₀1
  set x₀ : ↥I₀ := ⟨x₀', hx₀I⟩ with hx₀def
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (congrArg Subtype.val h)
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyI₀, hy3I₀, hyfix₀⟩ := exists_three_of_l32 hKI₀ hnat₀ hsyl
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨s, hs⟩ := hCK₀ ⟨_, mem_inf.2 ⟨pow_mem hyK 3, hy3I₀⟩⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have h2 := congrArg Subtype.val hs
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyI₀ (h ▸ one_mem _)
  have hyfix₁ : ∀ v ∈ I₁, v ∈ centralizer (T : Set G) → y * v = v * y := by
    intro v hv hvT
    set u : ↥I₀ := φ.symm ⟨v, hv⟩ with hu
    have hφu : φ u = ⟨v, hv⟩ := by rw [hu, MulEquiv.apply_symm_apply]
    have huT : (u : G) ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      have htu : t * (u : G) * t⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hTI₀ ht) u).mp u.2
      have h1 := hφT t ht u htu
      rw [hφu] at h1
      have h2 : t * v * t⁻¹ = v := by rw [mem_centralizer_iff.mp hvT t ht, mul_inv_cancel_right]
      have h3 : φ ⟨t * (u : G) * t⁻¹, htu⟩ = φ u := by
        rw [hφu]
        apply Subtype.ext
        rw [h1]
        exact h2
      have h4 : t * (u : G) * t⁻¹ = u := congrArg Subtype.val (φ.injective h3)
      calc t * (u : G) = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [h4]
    have h1 := hyfix₀ u u.2 huT
    have hyu : y * (u : G) * y⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hyK) u).mp u.2
    have h2 := hφ y hyK u hyu
    have h3 : (⟨y * (u : G) * y⁻¹, hyu⟩ : ↥I₀) = u :=
      Subtype.ext (show y * (u : G) * y⁻¹ = u by rw [h1, mul_inv_cancel_right])
    rw [h3, hφu] at h2
    have h2' : y * v * y⁻¹ = v := h2.symm
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [h2']
  have hyfixU : ∀ u ∈ U, u ∈ centralizer (T : Set G) → y * u = u * y := by
    intro x hx hxT
    rw [← hsup'] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have hab : ∀ t ∈ T, t * a * t⁻¹ = a ∧ t * b * t⁻¹ = b := fun t ht =>
      conj_eq_of_mul hinf ha hb (hTI₀ ht) (hTI₁ ht) (by
        rw [mem_centralizer_iff.mp hxT t ht, mul_inv_cancel_right])
    have haT : a ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      calc t * a = t * a * t⁻¹ * t := by group
        _ = a * t := by rw [(hab t ht).1]
    have hbT : b ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      calc t * b = t * b * t⁻¹ * t := by group
        _ = b * t := by rw [(hab t ht).2]
    calc y * (a * b) = (y * a) * b := by group
      _ = a * (y * b) := by rw [hyfix₀ a ha haT, mul_assoc]
      _ = a * b * y := by rw [hyfix₁ b hb hbT, mul_assoc]
  have hyZ := mem_centralizer_Z_of hTU hZ hyK hyfixU
  have hyL1 : y ∈ L₁ := mem_L1_of_pow_three h1332 h1228 S he hyZ (k := 1) (by simpa using hy3)
  have hL1K' : L₁ ≤ K :=
    L1_le_of_pow_three h1332 h1228 S he hL1K hyK hyZ hy1 (k := 1) (by simpa using hy3)
  have hRT : R ≤ T := s134_R_le_T S
  have hR2' : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQR : Q ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (sup_le (hL1K'.trans (le_sup_left.trans hKTQ)) (le_sup_right.trans hKTQ)) hQ2
  have hUR : U ≤ R := hUR2.trans (hR2Q.trans hQR)
  have hyR : y ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
  have hyQ : y ∈ normalizer (Q : Set G) := hKTQ (mem_sup_left hyK)
  have hRN₀ : R ≤ normalizer (I₀ : Set G) := hRT.trans hTI₀
  have hRCQ : R ⊓ centralizer (I₀ : Set G) ≤ Q := fun r hr => by
    rw [← hQ₀]
    exact mem_inf.2 ⟨hRT (mem_inf.1 hr).1, (mem_inf.1 hr).2⟩
  obtain ⟨C⟩ := exists_l3Coords hnat₀
  set yN : ↥(normalizer (I₀ : Set G)) := ⟨y, hKI₀ hyK⟩ with hyN
  have hρy3 : C.ρ yN ^ 3 = 1 := by
    rw [← map_pow]
    have : yN ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hyN, Subgroup.coe_one]
      exact hy3)
    rw [this, map_one]
  have hρy1 : C.ρ yN ≠ 1 := fun h => hyI₀ ((C.ker yN).1 h)
  have hρyp : L3.act (C.ρ yN) (C.c x₀) = C.c x₀ := by
    refine (C.fix_iff yN x₀).1 ?_
    show y * x₀' * y⁻¹ = x₀'
    rw [hyfix₀ x₀' hx₀I hx₀T, mul_inv_cancel_right]
  have hRfix : ∀ r ∈ R, r * (x₀ : G) * r⁻¹ = x₀ := fun r hr => by
    show r * x₀' * r⁻¹ = x₀'
    rw [mem_centralizer_iff.mp hx₀T r (hRT hr), mul_inv_cancel_right]
  have hRE : ∀ r : ↥(normalizer (I₀ : Set G)), (r : G) ∈ R → C.ρ r ∈ L3.AS {0, C.c x₀} :=
    fun r hr => C.rho_mem_AS hR2' hx₀1 hRfix yN hρy3 hρy1 hρyp hyR r hr
  have hp0 : C.c x₀ ≠ 0 := C.c_ne_zero hx₀1
  have hcontra : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ T → L ⊔ T ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → False := by
    intro X hX1 hXT hLX hKX
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨X, hX1, S.h13.sylow.1.to_le hXT, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
    have hM := S.uniqueM.2 M' ⟨hM', hLX.trans hle⟩
    exact hKM (hKX.trans (hM ▸ hle))
  have hRR1 : R = U3.r1Of T L V := (U3.s134Plus_L1 S he).pCoreOf_eq_r1Of
  rcases U3.s134_lemma13_2_2_seven hC137 h1332 S with ⟨Cc, hCB, hC1, hCchar, hCN⟩ | hB
  ·
    have hJ : thompsonJ R ≤ R ⊓ centralizer (U : Set G) := by
      refine iSup₂_le fun A hA => le_inf hA.1 ?_
      by_contra hAC
      have hAR := hA.1
      have hA₀ : ¬ A ≤ centralizer (I₀ : Set G) := fun h => hAC fun a ha =>
        hQU (hQ₀ ▸ mem_inf.2 ⟨hRT (hAR ha), h ha⟩)
      have hA₁ : ¬ A ≤ centralizer (I₁ : Set G) := fun h => hAC fun a ha =>
        hQU (hQ₁ ▸ mem_inf.2 ⟨hRT (hAR ha), h ha⟩)
      have hle := card_le_relIndex_mul_card hUe hUR hA
      have hAU : A ⊓ centralizer (U : Set G) = A ⊓ centralizer (I₀ : Set G) := by
        refine le_antisymm (inf_le_inf_left _ (centralizer_le hI₀U)) fun a ha => ?_
        refine mem_inf.2 ⟨(mem_inf.1 ha).1, hQU ?_⟩
        rw [← hQ₀]
        exact mem_inf.2 ⟨hRT (hAR (mem_inf.1 ha).1), (mem_inf.1 ha).2⟩
      have h1 := C.relIndex_mul_card_le (hAR.trans hRN₀) hp0 (fun a ha => hRE a (hAR ha)) hA₀
      have h2 : Nat.card ↥(U ⊓ centralizer (A : Set G)) ≤
          Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) * Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) := by
        have := card_inf_centralizer_le hinf hI₁N (hAR.trans hRN₀) (hAR.trans (hRT.trans hTI₁))
        rwa [hsup'] at this
      have h3 : Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) ≤ 4 := by
        refine card_le_four_of_lt h8₁ inf_le_left fun h => hA₁ ?_
        intro a ha
        rw [mem_centralizer_iff]
        intro v hv
        have hv' : v ∈ I₁ ⊓ centralizer (A : Set G) := by rw [h]; exact hv
        exact (mem_centralizer_iff.mp (mem_inf.1 hv').2 a ha).symm
      rw [hAU] at hle
      have h4 : Nat.card ↥U ≤ 8 * 4 := by
        calc Nat.card ↥U ≤ (A ⊓ centralizer (I₀ : Set G)).relIndex A *
              Nat.card ↥(U ⊓ centralizer (A : Set G)) := hle
          _ ≤ (A ⊓ centralizer (I₀ : Set G)).relIndex A *
              (Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) *
                Nat.card ↥(I₁ ⊓ centralizer (A : Set G))) := Nat.mul_le_mul_left _ h2
          _ = (A ⊓ centralizer (I₀ : Set G)).relIndex A *
              Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) *
                Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) := by ring
          _ ≤ 8 * 4 := Nat.mul_le_mul h1 h3
      omega
    have hRCU : R ⊓ centralizer (U : Set G) = Q := by
      refine le_antisymm (fun r hr => hRCQ (mem_inf.2 ⟨(mem_inf.1 hr).1,
        centralizer_le hI₀U (mem_inf.1 hr).2⟩)) (le_inf hQR hQU)
    have hBQ : baum R = baum Q := by rw [baum_eq_baum_centralizer hUe hUR hJ, hRCU]
    rw [← hRR1, hBQ] at hCB hCchar
    have := hCchar
    refine hcontra Cc hC1 (hCB.trans (inf_le_left.trans hQT)) hCN ?_
    have h2 : normalizer (baum Q : Set G) ≤ normalizer (Cc : Set G) := by
      have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Cc.subgroupOf (baum Q))
      rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at h3
    exact (le_sup_left.trans hKTQ).trans ((normalizer_le_normalizer_baum Q).trans h2)
  ·
    have hc16 : (centralizer ({y} : Set G)).relIndex R ≤ 16 :=
      s134_relIndex_R_le_sixteen S hB hyL1 hy3
    have hRQn : R ≤ normalizer (Q : Set G) := hRT.trans (le_sup_right.trans hKTQ)
    have hRCy : R ⊓ centralizer ({y} : Set G) ≤ Q := by
      intro r hr
      obtain ⟨hrR, hry⟩ := mem_inf.1 hr
      have hrN : r ∈ normalizer (I₀ : Set G) := hRN₀ hrR
      have hcomm' : C.ρ ⟨r, hrN⟩ * C.ρ yN = C.ρ yN * C.ρ ⟨r, hrN⟩ := by
        have h1 : (⟨r, hrN⟩ * yN : ↥(normalizer (I₀ : Set G))) = yN * ⟨r, hrN⟩ :=
          Subtype.ext (mem_centralizer_singleton_iff.mp hry)
        have h2 := congrArg C.ρ h1
        rwa [map_mul, map_mul] at h2
      have h1 := l3_AS_comm _ hp0 _ hρy3 hρy1 hρyp _ (hRE ⟨r, hrN⟩ hrR) hcomm'
      exact hRCQ (mem_inf.2 ⟨hrR, (C.ker ⟨r, hrN⟩).1 h1⟩)
    have hsup' : Q ⊔ (R ⊓ centralizer ({y} : Set G)) = Q := sup_eq_left.2 hRCy
    have hcRQ : (centralizer ({y} : Set G)).relIndex R =
        Q.relIndex R * (centralizer ({y} : Set G)).relIndex Q := by
      have h1 := U3.relIndex_centralizer_eq_mul (x := y) hQR hRQn
      rwa [hsup'] at h1
    have hRQ : ¬ R ≤ Q := by
      intro hle
      obtain ⟨s, hsTK, hsE, hs1⟩ := C.exists_mem_AS hKI₀ hsyl hx₀1 hx₀T
      have hsT : (s : G) ∈ T := (mem_inf.1 hsTK).1
      set g₁ := (s : G) * y * (s : G)⁻¹ * y⁻¹ with hg₁
      have hg₁L1 : g₁ ∈ L₁ :=
        mul_mem ((mem_normalizer_iff.mp (U3.s134_T_le_normalizer_L1 S hsT) y).mp hyL1)
          (inv_mem hyL1)
      have hg₁N : g₁ ∈ normalizer (I₀ : Set G) :=
        mul_mem (mul_mem (mul_mem s.2 yN.2) (inv_mem s.2)) (inv_mem yN.2)
      have hρg₁ : C.ρ ⟨g₁, hg₁N⟩ = C.ρ s * (C.ρ yN * C.ρ s * (C.ρ yN)⁻¹) := by
        have e : (⟨g₁, hg₁N⟩ : ↥(normalizer (I₀ : Set G))) = s * yN * s⁻¹ * yN⁻¹ := rfl
        have hss : (C.ρ s)⁻¹ = C.ρ s := by
          rw [inv_eq_iff_mul_eq_one]
          exact (L3.AS_elem _ hp0 _ hsE _ hsE).2
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hss]
        group
      obtain ⟨hcE, hc1⟩ := l3_comm_ne _ hp0 _ hρy3 hρy1 hρyp _ hsE hs1
      rw [← hρg₁] at hcE hc1
      obtain ⟨a, m₁, hm₁, hn₁⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₁).ne'
      have hua : (g₁ ^ m₁) ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm m₁, ← hn₁, pow_orderOf_eq_one]
      have huL1 : g₁ ^ m₁ ∈ L₁ := pow_mem hg₁L1 _
      have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
      have huV : g₁ ^ m₁ ∈ normalizer (V : Set G) := S.frame.L_le (hL1L huL1)
      have hρu : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ∈ A6.K4L := by
        have h16 : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ^ 16 = 1 := by
          refine U3.pow_sixteen_of_two_pow (k := a) ?_
          rw [← map_pow]
          have h1 : (⟨g₁ ^ m₁, huV⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ a = 1 :=
            Subtype.ext (by simpa using hua)
          rw [h1, map_one]
        exact U3.A4_two_K4 _ (U3.s134_rho_L1 S huV huL1) h16
      have huR : g₁ ^ m₁ ∈ R := s134_pCoreOf_L1_le_R S
        ((U3.s134Plus_L1 S he).mem_pCoreOf_of_K4 (x := ⟨g₁ ^ m₁, huV⟩) huL1 hρu)
      have h1 := (C.ker (⟨g₁, hg₁N⟩ ^ m₁)).2 (mem_inf.1 (hQ₀ ▸ hle huR)).2
      rw [map_pow] at h1
      obtain ⟨b, hb⟩ := hm₁
      have hsq : C.ρ ⟨g₁, hg₁N⟩ * C.ρ ⟨g₁, hg₁N⟩ = 1 := (L3.AS_elem _ hp0 _ hcE _ hcE).2
      rw [hb, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at h1
      exact hc1 h1
    have hRQ4 : 4 ≤ Q.relIndex R := by
      have h1 := U3.relIndex_sup_eq_one_or hy3 hR2' hQR hRQn hyQ hyR
      rw [hsup'] at h1
      exact h1.resolve_left fun h => hRQ (relIndex_eq_one.mp h)
    have hyN₀ : y ∈ normalizer (I₀ : Set G) := hKI₀ hyK
    have hyN₁ : y ∈ normalizer (I₁ : Set G) := hKI₁ hyK
    have hyU : y ∈ normalizer (U : Set G) := hKU hyK
    have hI₀2 : IsPGroup 2 ↥I₀ := hU2.to_le hI₀U
    have hc₀4 : 4 ≤ (centralizer ({y} : Set G)).relIndex I₀ :=
      U3.four_le_relIndex_centralizer hy3 hyN₀ hI₀2 fun h => hyI₀ (mem_centralizer_iff.mpr
        fun w hw => mem_centralizer_singleton_iff.mp (h hw))
    have hUN₀ : U ≤ normalizer (I₀ : Set G) := hnorm hI₀R hUR2
    have hcU16 : 16 ≤ (centralizer ({y} : Set G)).relIndex U := by
      have h1 := U3.relIndex_centralizer_eq_mul (x := y) hI₀U hUN₀
      have h2 := U3.relIndex_sup_eq_one_or hy3 hU2 hI₀U hUN₀ hyN₀ hyU
      rcases h2 with h2 | h2
      · exfalso
        have h3 : U ≤ I₀ ⊔ (U ⊓ centralizer ({y} : Set G)) := relIndex_eq_one.mp h2
        apply hy1
        have hyC₁ : y ∈ centralizer (I₁ : Set G) := by
          rw [mem_centralizer_iff]
          intro b hb
          obtain ⟨a, ha, c, hc, hac⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
            (inf_le_left.trans hUN₀) (h3 (hI₁U hb))
          have hcy : c * y = y * c := mem_centralizer_singleton_iff.mp (mem_inf.1 hc).2
          have hyb : y * b * y⁻¹ * b⁻¹ ∈ I₀ ⊓ I₁ := by
            refine mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.mp hyN₁ b).mp hb) (inv_mem hb)⟩
            rw [hac]
            have hcy' : c * y⁻¹ = y⁻¹ * c := by
              calc c * y⁻¹ = y⁻¹ * (y * c) * y⁻¹ := by group
                _ = y⁻¹ * (c * y) * y⁻¹ := by rw [← hcy]
                _ = y⁻¹ * c := by group
            have e : y * (a * c) * y⁻¹ * (a * c)⁻¹ = y * a * y⁻¹ * a⁻¹ := by
              calc y * (a * c) * y⁻¹ * (a * c)⁻¹ = y * a * (c * y⁻¹) * c⁻¹ * a⁻¹ := by group
                _ = y * a * (y⁻¹ * c) * c⁻¹ * a⁻¹ := by rw [hcy']
                _ = y * a * y⁻¹ * a⁻¹ := by group
            rw [e]
            exact mul_mem ((mem_normalizer_iff.mp hyN₀ a).mp ha) (inv_mem ha)
          rw [hinf, mem_bot] at hyb
          calc b * y = (y * b * y⁻¹ * b⁻¹)⁻¹ * (y * b) := by group
            _ = y * b := by rw [hyb, inv_one, one_mul]
        have h4 := hCK₁ ⟨y, mem_inf.2 ⟨hyK, hyC₁⟩⟩
        obtain ⟨s, hs⟩ := h4
        have hs' : y ^ 2 ^ s = 1 := by
          have h5 := congrArg Subtype.val hs
          simp only [Subgroup.coe_pow, Subgroup.coe_one] at h5
          exact h5
        exact mem_bot.1 (mem_of_pow_odd_mem (m := 3) hs' (Nat.odd_iff.2 rfl)
          (by rw [hy3]; exact one_mem _))
      · rw [h1]
        calc 16 = 4 * 4 := by norm_num
          _ ≤ _ := Nat.mul_le_mul h2 hc₀4
    have hcQ : 16 ≤ (centralizer ({y} : Set G)).relIndex Q :=
      hcU16.trans (U3.relIndex_centralizer_le (hUR2.trans hR2Q))
    have h1 : 4 * 16 ≤ (centralizer ({y} : Set G)).relIndex R := by
      rw [hcRQ]
      exact Nat.mul_le_mul hRQ4 hcQ
    omega

end CFSG.Quasithin.H13.NQS134
