module

public import CFSG.Quasithin.H13.A7BlkAct

public section

namespace CFSG.Quasithin.H13.A7Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

structure AltData (K : Subgroup G) where
  α : ↥K →* alternatingGroup (Fin 7)
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥K
  β : ↥(blockU K) →* Multiplicative ↥(evenWeight 7)
  βsurj : Function.Surjective β
  βker : β.ker = (blockZ K).subgroupOf (blockU K)
  βeq : ∀ (ℓ : ↥K) (u v : ↥(blockU K)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 7 (α ℓ) (Multiplicative.toAdd (β u))

theorem nonempty_altData {K : Subgroup G} (h : IsAltType K 7) : Nonempty (AltData K) := by
  obtain ⟨α, hα, hker, β, hβ, hβk, hβe⟩ := h
  refine ⟨⟨α, hα, hker, β, hβ, hβk, fun ℓ u v huv => Subtype.ext (funext fun i => ?_)⟩⟩
  exact hβe ℓ u v huv i

variable {K : Subgroup G} (D : AltData K)

noncomputable abbrev AltData.act : ↥(Subgroup.normalizer (K : Set G)) →* Perm (Fin 7) :=
  permAct D.α D.surj D.ker (by norm_num) (by norm_num)

@[expose] def omega (j : Fin 7) : ↥(evenWeight 7) :=
  ⟨fun i => if i = j then 0 else 1, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    fin_cases j <;> decide⟩

theorem permWeight_omega (σ : Perm (Fin 7)) (j : Fin 7) :
    permWeight 7 σ (omega j) = omega (σ j) := by
  apply Subtype.ext
  funext i
  simp only [permWeight, omega]
  by_cases h : i = σ j
  · subst h
    simp
  · have : σ.symm i ≠ j := fun h' => h (by rw [← h']; simp)
    simp [h, this]

variable (hshort : IsShort2 K)
include hshort

theorem blockU_le_blockQ : blockU K ≤ blockQ K := fun _ hu => (hshort.2.2.1.1 hu).1

theorem comm_blockU_blockQ {u q : G} (hu : u ∈ blockU K) (hq : q ∈ blockQ K) : u * q = q * u :=
  (Subgroup.mem_centralizer_iff.mp (hshort.2.2.1.1 hu).2 q hq).symm

theorem comm_blockU {u u' : G} (hu : u ∈ blockU K) (hu' : u' ∈ blockU K) : u * u' = u' * u :=
  comm_blockU_blockQ hshort hu (blockU_le_blockQ hshort hu')

theorem sq_blockU {u : G} (hu : u ∈ blockU K) : u ^ 2 = 1 := hshort.2.2.1.2 u hu

omit hshort in
theorem comm_blockZ {z k : G} (hz : z ∈ blockZ K) (hk : k ∈ K) : k * z = z * k :=
  Subgroup.mem_centralizer_iff.mp hz.2 k hk

omit hshort in
theorem conj_mem_blockU {k u : G} (hk : k ∈ K) (hu : u ∈ blockU K) : k * u * k⁻¹ ∈ blockU K :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hk)) u).mp hu

omit hshort in
@[expose] noncomputable def conjU (g : ↥(Subgroup.normalizer (K : Set G))) :
    ↥(blockU K) →* ↥(blockU K) where
  toFun u := ⟨g * u * (g : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU g.2) u).mp u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit hshort in
theorem coe_conjU (g : ↥(Subgroup.normalizer (K : Set G))) (u : ↥(blockU K)) :
    ((conjU g u : ↥(blockU K)) : G) = g * u * (g : G)⁻¹ := rfl

omit hshort in
include D in
theorem mem_blockQ_of_ker {k : ↥K} (hk : D.α k = 1) : (k : G) ∈ blockQ K := by
  have h : k ∈ CFSG.pCore 2 ↥K := D.ker ▸ hk
  refine ⟨k, ?_, rfl⟩
  exact h

include D in
theorem conj_eq_of_ker {k : ↥K} (hk : D.α k = 1) {u : G} (hu : u ∈ blockU K) :
    (k : G) * u * (k : G)⁻¹ = u := by
  rw [← comm_blockU_blockQ hshort hu (mem_blockQ_of_ker D hk), mul_inv_cancel_right]

omit hshort in
theorem toAdd_β_conj (ℓ : ↥K) (u : ↥(blockU K)) :
    Multiplicative.toAdd (D.β ⟨ℓ * u * (ℓ : G)⁻¹, conj_mem_blockU ℓ.2 u.2⟩) =
      permWeight 7 (D.α ℓ) (Multiplicative.toAdd (D.β u)) :=
  D.βeq ℓ u _ rfl

theorem exists_fixed_lift [Finite G] (j : Fin 7) :
    ∃ y : ↥(blockU K), Multiplicative.toAdd (D.β y) = omega j ∧
      ∀ h ∈ ptPre D.α j, h * (y : G) * h⁻¹ = y := by
  obtain ⟨x, hx⟩ := D.βsurj (Multiplicative.ofAdd (omega j))
  have hxj : Multiplicative.toAdd (D.β x) = omega j := by rw [hx]; rfl
  refine ⟨x, hxj, ?_⟩
  have hz : ∀ a ∈ ptPre D.α j, (x : G)⁻¹ * (a * x * a⁻¹) ∈ blockZ K := by
    intro a ha
    obtain ⟨haK, hai⟩ := (mem_ptPre D.α).mp ha
    have h1 := toAdd_β_conj D ⟨a, haK⟩ x
    rw [hxj, permWeight_omega, hai] at h1
    have hU : (x : G)⁻¹ * (a * x * a⁻¹) ∈ blockU K :=
      (blockU K).mul_mem ((blockU K).inv_mem x.2) (conj_mem_blockU haK x.2)
    have hker : (⟨(x : G)⁻¹ * (a * x * a⁻¹), hU⟩ : ↥(blockU K)) ∈ D.β.ker := by
      rw [MonoidHom.mem_ker]
      have e : (⟨(x : G)⁻¹ * (a * x * a⁻¹), hU⟩ : ↥(blockU K)) =
          x⁻¹ * ⟨a * x * a⁻¹, conj_mem_blockU haK x.2⟩ := rfl
      rw [e, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, h1, hxj, toAdd_one, neg_add_cancel]
    rw [D.βker] at hker
    exact hker
  let f : ↥(ptPre D.α j) →* ↥(blockZ K) :=
    { toFun := fun a => ⟨(x : G)⁻¹ * (a * x * (a : G)⁻¹), hz a a.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc : (a : G) * ((x : G)⁻¹ * (b * x * (b : G)⁻¹)) =
            ((x : G)⁻¹ * (b * x * (b : G)⁻¹)) * a :=
          comm_blockZ (hz b b.2) (ptPre_le D.α j a.2)
        show (x : G)⁻¹ * ((a * b : G) * x * ((a : G) * b)⁻¹) =
          ((x : G)⁻¹ * (a * x * (a : G)⁻¹)) * ((x : G)⁻¹ * (b * x * (b : G)⁻¹))
        calc (x : G)⁻¹ * ((a * b : G) * x * ((a : G) * b)⁻¹)
            = (x : G)⁻¹ * (a * x * (a : G)⁻¹) * ((a : G) * ((x : G)⁻¹ * (b * x * (b : G)⁻¹)) *
                (a : G)⁻¹) := by group
          _ = _ := by rw [hc, mul_inv_cancel_right] }
  have hfZ : ∀ a b : ↥(ptPre D.α j), f a * f b = f b * f a := fun a b =>
    Subtype.ext (comm_blockU hshort (f a).2.1 (f b).2.1)
  have hf1 : ∀ a b : ↥(ptPre D.α j), f ⁅a, b⁆ = 1 := fun a b => by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hfZ]
  have hfix : ∀ a : ↥(ptPre D.α j), f a = 1 → (a : G) * x * (a : G)⁻¹ = x := fun a ha => by
    have h1 := congrArg Subtype.val ha
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h1
    calc (a : G) * x * (a : G)⁻¹ = x * ((x : G)⁻¹ * (a * x * (a : G)⁻¹)) := by group
      _ = x := by rw [h1, mul_one]
  have hcore : ptCore D.α j ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    show perfectCore (ptPre D.α j) ≤ _
    rw [← perfectCore_perfect (ptPre D.α j), Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have haP := ptCore_le_ptPre D.α j ha
    have hbP := ptCore_le_ptPre D.α j hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    set a' : ↥(ptPre D.α j) := ⟨a, haP⟩
    set b' : ↥(ptPre D.α j) := ⟨b, hbP⟩
    have h1 := hfix ⁅a', b'⁆ (hf1 a' b')
    have h2 : ((⁅a', b'⁆ : ↥(ptPre D.α j)) : G) = ⁅a, b⁆ := rfl
    rw [h2] at h1
    calc ⁅a, b⁆ * (x : G) = ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
      _ = x * ⁅a, b⁆ := by rw [h1]
  intro h hh
  obtain ⟨hhK, hhi⟩ := (mem_ptPre D.α).mp hh
  have hs : D.α ⟨h, hhK⟩ ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) j := hhi
  rw [← map_ptCore D.α D.surj (by norm_num) j] at hs
  obtain ⟨c, hc, hcα⟩ := hs
  have hcC : (c : G) * x = x * c := (Subgroup.mem_centralizer_singleton_iff.mp (hcore hc))
  have hker : D.α (c⁻¹ * ⟨h, hhK⟩) = 1 := by rw [map_mul, map_inv, hcα, inv_mul_cancel]
  have h2 := conj_eq_of_ker D hshort hker x.2
  have e : h = (c : G) * ((c : G)⁻¹ * h) := by group
  calc h * (x : G) * h⁻¹ = (c : G) * (((c : G)⁻¹ * h) * x * ((c : G)⁻¹ * h)⁻¹) * (c : G)⁻¹ := by
        group
    _ = (c : G) * x * (c : G)⁻¹ := by
        rw [show ((c : G)⁻¹ * h) = ((c⁻¹ * ⟨h, hhK⟩ : ↥K) : G) from rfl, h2]
    _ = x := by rw [hcC, mul_inv_cancel_right]

abbrev commU : CommGroup ↥(blockU K) :=
  { (inferInstance : Group ↥(blockU K)) with
    mul_comm := fun a b => Subtype.ext (comm_blockU hshort a.2 b.2) }

omit hshort in
theorem exists_alt_apply (i j : Fin 7) :
    ∃ σ : alternatingGroup (Fin 7), (σ : Perm (Fin 7)) i = j := by
  have : MulAction.IsPretransitive (alternatingGroup (Fin 7)) (Fin 7) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) i j
  exact ⟨σ, hσ⟩

variable [Finite G]

@[expose] noncomputable def y6 : ↥(blockU K) := (exists_fixed_lift D hshort 6).choose

theorem y6_spec : Multiplicative.toAdd (D.β (y6 D hshort)) = omega 6 ∧
    ∀ h ∈ ptPre D.α 6, h * (y6 D hshort : G) * h⁻¹ = y6 D hshort :=
  (exists_fixed_lift D hshort 6).choose_spec

omit hshort [Finite G] in
include D in
theorem exists_kj (j : Fin 7) : ∃ k : ↥K, (D.α k : Perm (Fin 7)) 6 = j := by
  obtain ⟨σ, hσ⟩ := exists_alt_apply 6 j
  obtain ⟨k, hk⟩ := D.surj σ
  exact ⟨k, by rw [hk, hσ]⟩

@[expose] noncomputable def kj (j : Fin 7) : ↥K := (exists_kj D j).choose

omit hshort [Finite G] in
theorem kj_spec (j : Fin 7) : (D.α (kj D j) : Perm (Fin 7)) 6 = j := (exists_kj D j).choose_spec

@[expose] noncomputable def yj (j : Fin 7) : ↥(blockU K) :=
  ⟨(kj D j : G) * y6 D hshort * ((kj D j : G))⁻¹, conj_mem_blockU (kj D j).2 (y6 D hshort).2⟩

theorem β_yj (j : Fin 7) : Multiplicative.toAdd (D.β (yj D hshort j)) = omega j := by
  have h := toAdd_β_conj D (kj D j) (y6 D hshort)
  rw [(y6_spec D hshort).1, permWeight_omega, kj_spec] at h
  exact h

theorem conj_yj (k : ↥K) (j : Fin 7) :
    (k : G) * yj D hshort j * (k : G)⁻¹ = yj D hshort ((D.α k : Perm (Fin 7)) j) := by
  set j' := (D.α k : Perm (Fin 7)) j
  set h : ↥K := (kj D j')⁻¹ * k * kj D j with hh
  have hfix : (D.α h : Perm (Fin 7)) 6 = 6 := by
    rw [hh, map_mul, map_mul, map_inv]
    show ((D.α (kj D j') : Perm (Fin 7)))⁻¹ ((D.α k : Perm (Fin 7))
      ((D.α (kj D j) : Perm (Fin 7)) 6)) = 6
    rw [kj_spec, Perm.inv_eq_iff_eq, kj_spec]
  have hP : (h : G) ∈ ptPre D.α 6 := (mem_ptPre D.α).mpr ⟨h.2, hfix⟩
  have h1 := (y6_spec D hshort).2 _ hP
  have e : (k : G) = kj D j' * h * (kj D j : G)⁻¹ := by
    rw [hh]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  show (k : G) * ((kj D j : G) * y6 D hshort * ((kj D j : G))⁻¹) * (k : G)⁻¹ =
    (kj D j' : G) * y6 D hshort * ((kj D j' : G))⁻¹
  rw [e]
  calc (kj D j' * h * (kj D j : G)⁻¹ : G) * ((kj D j : G) * y6 D hshort * ((kj D j : G))⁻¹) *
        (kj D j' * h * (kj D j : G)⁻¹ : G)⁻¹ =
      (kj D j' : G) * ((h : G) * y6 D hshort * (h : G)⁻¹) * ((kj D j' : G))⁻¹ := by group
    _ = _ := by rw [h1]

omit hshort [Finite G] in
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] noncomputable def psi (f : Fin 7 → ZMod 2) : ↥(blockU K) :=
  @Finset.prod (Fin 7) ↥(blockU K) (commU hshort).toCommMonoid Finset.univ
    fun j => if f j = 1 then yj D hshort j else 1

theorem yj_mul_self (j : Fin 7) : yj D hshort j * yj D hshort j = 1 := by
  have h := sq_blockU hshort (yj D hshort j).2
  rw [pow_two] at h
  exact Subtype.ext h

theorem psi_add (f g : Fin 7 → ZMod 2) :
    psi D hshort (f + g) = psi D hshort f * psi D hshort g := by
  let _ := commU hshort
  unfold psi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases zmod2_cases (f j) with hf | hf <;> rcases zmod2_cases (g j) with hg | hg
  · simp [hf, hg]
  · simp [hf, hg]
  · simp [hf, hg]
  · have h2 : (f + g) j = 0 := by rw [Pi.add_apply, hf, hg]; decide
    rw [h2, hf, hg, ite_eq_right (by decide), ite_eq_left rfl]
    exact (yj_mul_self D hshort j).symm

theorem psi_zero : psi D hshort 0 = 1 := by
  let _ := commU hshort
  unfold psi
  simp

theorem psi_mul_self (f : Fin 7 → ZMod 2) : psi D hshort f * psi D hshort f = 1 := by
  rw [← psi_add, show f + f = 0 from funext fun i => CharTwo.add_self_eq_zero (f i), psi_zero]

theorem conj_psi (k : ↥K) (f : Fin 7 → ZMod 2) :
    conjU ⟨(k : G), Subgroup.le_normalizer k.2⟩ (psi D hshort f) =
      psi D hshort (fun i => f ((D.α k : Perm (Fin 7))⁻¹ i)) := by
  let _ := commU hshort
  set σ : Perm (Fin 7) := (D.α k : Perm (Fin 7)) with hσ
  unfold psi
  rw [map_prod]
  have h1 : ∀ j, conjU ⟨(k : G), Subgroup.le_normalizer k.2⟩
      (if f j = 1 then yj D hshort j else 1) = if f j = 1 then yj D hshort (σ j) else 1 := by
    intro j
    split_ifs
    · exact Subtype.ext (conj_yj D hshort k j)
    · exact map_one _
  simp only [h1]
  rw [← Equiv.prod_comp σ (fun i => if f (σ⁻¹ i) = 1 then yj D hshort i else 1)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show σ⁻¹ (σ j) = j by rw [Perm.inv_def, Equiv.symm_apply_apply]]

theorem β_psi (f : Fin 7 → ZMod 2) (hf : ∑ i, f i = 0) :
    ((Multiplicative.toAdd (D.β (psi D hshort f)) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) = f := by
  let _ := commU hshort
  have h1 : D.β (psi D hshort f) = ∏ j, D.β (if f j = 1 then yj D hshort j else 1) := map_prod _ _ _
  rw [h1, toAdd_prod]
  funext i
  have hs := map_sum (evenWeight 7).subtype
    (fun j => Multiplicative.toAdd (D.β (if f j = 1 then yj D hshort j else 1))) Finset.univ
  simp only [AddSubgroup.coe_subtype] at hs
  rw [hs, Finset.sum_apply]
  have h2 : ∀ j, ((Multiplicative.toAdd (D.β (if f j = 1 then yj D hshort j else 1)) :
      ↥(evenWeight 7)) : Fin 7 → ZMod 2) i = f j * (if i = j then 0 else 1) := by
    intro j
    rcases zmod2_cases (f j) with h | h
    · simp [h]
    · simp only [h, ite_true, β_yj D hshort j, one_mul]
      rfl
  simp only [h2]
  have e : ∀ j, f j * (if i = j then (0 : ZMod 2) else 1) =
      f j - (if i = j then f j else 0) := by
    intro j
    split_ifs <;> ring
  calc ∑ j, f j * (if i = j then (0 : ZMod 2) else 1)
      = ∑ j, (f j - if i = j then f j else 0) := Finset.sum_congr rfl fun j _ => e j
    _ = ∑ j, f j - ∑ j, (if i = j then f j else 0) := Finset.sum_sub_distrib _ _
    _ = 0 - f i := by rw [hf, Finset.sum_ite_eq]; simp
    _ = f i := by rcases zmod2_cases (f i) with h | h <;> rw [h] <;> decide

end CFSG.Quasithin.H13.A7Blk

end
