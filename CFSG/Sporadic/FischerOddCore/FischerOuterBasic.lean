module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Order
public import CFSG.Sporadic.FischerOddCore.NoCompLemmas
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG CFSG.LocalCores CFSG.ComponentClassification.OuterAutomorphisms CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier (fixSub)

section Components

variable {H : Type*} [Group H]

theorem le_of_isPerfect_of_isSolvable_quotient {N : Subgroup H} [N.Normal]
    (hsolv : Group.IsSolvable (H ⧸ N)) {B : Subgroup H} (hB : Group.IsPerfect B) : B ≤ N := by
  have := hsolv
  have := hB
  have hp : Group.IsPerfect (B.map (QuotientGroup.mk' N)) := Group.IsPerfect.map _
  have hbot : B.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    have : Nontrivial (B.map (QuotientGroup.mk' N)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (B.map (QuotientGroup.mk' N)) inferInstance
  intro b hb
  have : QuotientGroup.mk' N b ∈ B.map (QuotientGroup.mk' N) := ⟨b, hb, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff b).1 this

theorem card_quotient_center_of_component_of_normal_simple [Finite H] {N : Subgroup H}
    [N.Normal] (hsolv : Group.IsSolvable (H ⧸ N)) (hN : IsSimpleGroup N)
    (hNc : ∃ a b : N, a * b ≠ b * a) {B : Subgroup H} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = Nat.card N := by
  have hle : B ≤ N := le_of_isPerfect_of_isSolvable_quotient hsolv hB.1.1
  have hB' := component_overgroup hB hle
  rw [card_quotient_center_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm]
  refine card_quotient_center_of_component_simple (MonoidHom.id N) Function.surjective_id ?_ hN
    hNc hB'
  rw [(MonoidHom.ker_eq_bot_iff _).2 Function.injective_id]
  infer_instance

theorem no_component_of_selfCentralizing {L : Type*} [Group L] [Finite L] {Q : Subgroup L}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hQc : Subgroup.centralizer (Q : Set L) ≤ Q)
    (B : Subgroup L) : ¬ IsComponent B :=
  not_isComponent_of_surj_selfCentralizing (MonoidHom.id L) Function.surjective_id
    (fun x hx => by rw [show x = 1 from hx, one_mul]) hQn hQ2 hQc B

end Components

theorem normal_subgroupOf_of_conj {G : Type*} [Group G] [Finite G] {N K : Subgroup G}
    {T : Set G} (hK : K = Subgroup.closure T) (hNK : N ≤ K)
    (hT : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) : (N.subgroupOf K).Normal := by
  have hnorm : ∀ t ∈ T, t ∈ Subgroup.normalizer (N : Set G) := by
    intro t ht
    have hle : N.map (MulAut.conj t).toMonoidHom ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact hT t ht x hx
    have hcard : Nat.card (N.map (MulAut.conj t).toMonoidHom) = Nat.card N :=
      Nat.card_congr (N.equivMapOfInjective _ (MulAut.conj t).injective).toEquiv.symm
    have heq : N.map (MulAut.conj t).toMonoidHom = N :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hT t ht x
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have e : y = x := by
        have h1 : t * y * t⁻¹ = t * x * t⁻¹ := hyx
        simpa using h1
      exact e ▸ hy
  have hKle : K ≤ Subgroup.normalizer (N : Set G) := by
    rw [hK, Subgroup.closure_le]
    exact hnorm
  rw [Subgroup.normal_subgroupOf_iff hNK]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.1 (hKle hk) h).1 hh

theorem exists_selfCentralizing_of_conjCert {n m r : ℕ} {K : Subgroup (Equiv.Perm (Fin n))}
    {t : Fin r → Equiv.Perm (Fin n)} (hK : K = Subgroup.closure (Set.range t))
    {s : Fin m → Equiv.Perm (Fin n)} (hs : Function.Injective s) (hsK : ∀ j, s j ∈ K)
    (hcomm : ∀ j k, s j * s k = s k * s j) (π : Fin r → Equiv.Perm (Fin m))
    (hπ : ∀ i j, t i * s j * (t i)⁻¹ = s (π i j)) {P : Subgroup (Equiv.Perm (Fin m))}
    (hP : P = Subgroup.closure (Set.range π)) :
    ∃ N : Subgroup K, N.Normal ∧ Nat.card N * Nat.card P = Nat.card K ∧
      Subgroup.centralizer (N : Set K) ≤ N := by
  have hTK : ∀ i, t i ∈ K := fun i => hK ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hinv : ∀ g ∈ K, ∀ j, ∃ j', s j' = conjPerm g (s j) := by
    intro g hg
    rw [hK] at hg
    refine famInv_closure conjPerm hs ?_ hg
    rintro _ ⟨i, rfl⟩ j
    exact ⟨π i j, (hπ i j).symm⟩
  obtain ⟨φ, hφ⟩ := exists_famHom (conjPerm.comp K.subtype) hs (fun h j => hinv h h.2 j)
  have hφ' : ∀ (h : K) j, s (φ h j) = (h : Equiv.Perm (Fin n)) * s j *
      (h : Equiv.Perm (Fin n))⁻¹ := hφ
  have hφT : ∀ i, φ ⟨t i, hTK i⟩ = π i := fun i =>
    Equiv.ext fun j => hs (by rw [hφ']; exact hπ i j)
  have hrange : φ.range = P := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      have key : ∀ x ∈ Subgroup.closure (Set.range t), ∀ hx : x ∈ K, φ ⟨x, hx⟩ ∈ P := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          intro hx'
          obtain ⟨i, rfl⟩ := hx
          rw [show (⟨t i, hx'⟩ : K) = ⟨t i, hTK i⟩ from rfl, hφT i, hP]
          exact Subgroup.subset_closure ⟨i, rfl⟩
        | one =>
          intro hx
          rw [show (⟨1, hx⟩ : K) = 1 from rfl, map_one]
          exact P.one_mem
        | mul x y hx' hy' ihx ihy =>
          intro hxy
          have hx2 : x ∈ K := by rw [hK]; exact hx'
          have hy2 : y ∈ K := by rw [hK]; exact hy'
          rw [show (⟨x * y, hxy⟩ : K) = ⟨x, hx2⟩ * ⟨y, hy2⟩ from rfl, map_mul]
          exact P.mul_mem (ihx hx2) (ihy hy2)
        | inv x hx' ihx =>
          intro hxi
          have hx2 : x ∈ K := by rw [hK]; exact hx'
          rw [show (⟨x⁻¹, hxi⟩ : K) = (⟨x, hx2⟩ : K)⁻¹ from rfl, map_inv]
          exact P.inv_mem (ihx hx2)
      have hh : (h : Equiv.Perm (Fin n)) ∈ Subgroup.closure (Set.range t) := by
        rw [← hK]
        exact h.2
      exact key h hh h.2
    · rw [hP, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, hφT i⟩
  have hsN : ∀ j, (⟨s j, hsK j⟩ : K) ∈ φ.ker := fun j => by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun k => hs ?_
    rw [hφ', Equiv.Perm.one_apply]
    show s j * s k * (s j)⁻¹ = s k
    rw [hcomm j k, mul_inv_cancel_right]
  refine ⟨φ.ker, φ.normal_ker, ?_, fun z hz => ?_⟩
  · have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange] at h
    exact h
  · rw [MonoidHom.mem_ker]
    refine Equiv.ext fun j => hs ?_
    have hc := Subgroup.mem_centralizer_iff.1 hz _ (hsN j)
    have hc' : s j * (z : Equiv.Perm (Fin n)) = (z : Equiv.Perm (Fin n)) * s j :=
      congrArg Subtype.val hc
    rw [hφ', Equiv.Perm.one_apply, ← hc', mul_inv_cancel_right]

section Simple

variable {m : ℕ}

theorem fix_of_mem_closure {Hs : Set (Equiv.Perm (Fin m))} {x₀ : Fin m}
    (hHs : ∀ h ∈ Hs, h x₀ = x₀) {h : Equiv.Perm (Fin m)} (hh : h ∈ Subgroup.closure Hs) :
    h x₀ = x₀ := by
  induction hh using Subgroup.closure_induction with
  | mem h hh => exact hHs h hh
  | one => rfl
  | mul g h _ _ hg hh => rw [Equiv.Perm.mul_apply, hh, hg]
  | inv g _ hg => rw [Equiv.Perm.inv_eq_iff_eq, hg]

theorem lab_of_mem_closure {k : ℕ} {Hs : Set (Equiv.Perm (Fin m))} {lab : Fin m → Fin k}
    (hlab : ∀ h ∈ Hs, ∀ p, lab (h p) = lab p) {h : Equiv.Perm (Fin m)}
    (hh : h ∈ Subgroup.closure Hs) : ∀ p, lab (h p) = lab p := by
  induction hh using Subgroup.closure_induction with
  | mem h hh => exact hlab h hh
  | one => exact fun p => rfl
  | mul g h _ _ hg hh => exact fun p => by rw [Equiv.Perm.mul_apply, hg, hh]
  | inv g _ hg =>
    intro p
    have := hg (g⁻¹ p)
    rw [Equiv.Perm.eq_inv_iff_eq.1 rfl] at this
    exact this.symm

theorem isSimpleGroup_of_permCert (hm : 2 ≤ m) {P : Subgroup (Equiv.Perm (Fin m))}
    {a b : Equiv.Perm (Fin m)} (hP : P = Subgroup.closure {a, b}) (x₀ : Fin m)
    (htrans : ∀ p : Fin m, ∃ g ∈ P, g x₀ = p) {Hs : Set (Equiv.Perm (Fin m))}
    (hHs : ∀ h ∈ Hs, h ∈ P ∧ h x₀ = x₀) {k : ℕ} (lab : Fin m → Fin k)
    (hlab : ∀ h ∈ Hs, ∀ p, lab (h p) = lab p)
    (horb : ∀ p q : Fin m, lab p = lab q → ∃ h ∈ Subgroup.closure Hs, h p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x₀ ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ m →
      S = {lab x₀} ∨ S = Finset.univ)
    (hab : (orderOf a).Coprime (orderOf b))
    (hprod : (orderOf (a * b)).Coprime (Nat.card P / m)) : IsSimpleGroup P := by
  classical
  have haP : a ∈ P := hP ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbP : b ∈ P := hP ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hHP : Subgroup.closure Hs ≤ P := (Subgroup.closure_le _).2 fun h hh => (hHs h hh).1
  have : MulAction.IsPretransitive P (Fin m) := ⟨fun p q => by
    obtain ⟨g, hg, hgp⟩ := htrans p
    obtain ⟨g', hg', hgq⟩ := htrans q
    refine ⟨⟨g' * g⁻¹, P.mul_mem hg' (P.inv_mem hg)⟩, ?_⟩
    show (g' * g⁻¹) p = q
    rw [Equiv.Perm.mul_apply, ← hgp, Equiv.Perm.inv_eq_iff_eq.2 rfl, hgq]⟩
  have : MulAction.IsPreprimitive P (Fin m) := by
    refine isPreprimitive_of_suborbit_labels x₀ ((Subgroup.closure Hs).subgroupOf P)
      (fun h hh => fix_of_mem_closure (fun h hh => (hHs h hh).2) (Subgroup.mem_subgroupOf.1 hh))
      lab (fun h hh p => lab_of_mem_closure hlab (Subgroup.mem_subgroupOf.1 hh) p)
      (fun p q hpq => ?_) (fun S hS hd => hdiv S hS (by rwa [Fintype.card_fin] at hd))
    obtain ⟨h, hh, hhp⟩ := horb p q hpq
    exact ⟨⟨h, hHP hh⟩, Subgroup.mem_subgroupOf.2 hh, hhp⟩
  have hstab : Nat.card (MulAction.stabilizer P x₀) = Nat.card P / m := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer P x₀)
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_fin] at h1
    rw [← h1, Nat.mul_div_cancel _ (by omega)]
  have hgen : Subgroup.closure ({⟨a, haP⟩, ⟨b, hbP⟩} : Set P) = ⊤ := by
    subst hP
    have e : ({⟨a, haP⟩, ⟨b, hbP⟩} : Set (Subgroup.closure ({a, b} : Set _))) =
        (Subtype.val ⁻¹' ({a, b} : Set (Equiv.Perm (Fin m)))) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl) <;> simp
      · rintro (h | h)
        · left; exact Subtype.ext h
        · right; exact Subtype.ext h
    rw [e]
    exact Subgroup.closure_closure_coe_preimage
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin m) (by rw [Nat.card_fin]; exact hm)
    ⟨a, haP⟩ ⟨b, hbP⟩ hgen x₀ ?_ ?_
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hab
  · rw [hstab, show (⟨a, haP⟩ : P) * ⟨b, hbP⟩ = ⟨a * b, P.mul_mem haP hbP⟩ from rfl,
      Subgroup.orderOf_mk]
    exact hprod

theorem isSimpleGroup_of_famHom {n : ℕ} {X : Type*} (f : Equiv.Perm (Fin n) →* Equiv.Perm X)
    {s : Fin m → X} (hs : Function.Injective s) {a b : Equiv.Perm (Fin n)}
    {pa pb : Equiv.Perm (Fin m)} (ha : ∀ j, s (pa j) = f a (s j))
    (hb : ∀ j, s (pb j) = f b (s j)) {N : Subgroup (Equiv.Perm (Fin n))}
    (hN : N = Subgroup.closure {a, b}) {P : Subgroup (Equiv.Perm (Fin m))}
    (hP : P = Subgroup.closure {pa, pb}) (hcard : Nat.card N = Nat.card P)
    (hPs : IsSimpleGroup P) : IsSimpleGroup N := by
  have haN : a ∈ N := hN ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbN : b ∈ N := hN ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hinv : ∀ g ∈ N, ∀ j, ∃ j', s j' = f g (s j) := by
    intro g hg
    rw [hN] at hg
    refine famInv_closure f hs ?_ hg
    rintro t (rfl | rfl) j
    · exact ⟨pa j, ha j⟩
    · exact ⟨pb j, hb j⟩
  obtain ⟨φ, hφ⟩ := exists_famHom (f.comp N.subtype) hs (fun h j => hinv h h.2 j)
  have hφ' : ∀ (h : N) j, s (φ h j) = f h (s j) := hφ
  have hφa : φ ⟨a, haN⟩ = pa := Equiv.ext fun j => hs (by rw [hφ']; exact (ha j).symm)
  have hφb : φ ⟨b, hbN⟩ = pb := Equiv.ext fun j => hs (by rw [hφ']; exact (hb j).symm)
  have hrange : φ.range = P := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      have key : ∀ x ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))),
          ∀ hx : x ∈ N, φ ⟨x, hx⟩ ∈ P := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem t ht =>
          intro hx
          rcases ht with rfl | rfl
          · rw [hφa, hP]
            exact Subgroup.subset_closure (Set.mem_insert _ _)
          · rw [hφb, hP]
            exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        | one =>
          intro hx
          rw [show (⟨1, hx⟩ : N) = 1 from rfl, map_one]
          exact P.one_mem
        | mul x y hx' hy' ihx ihy =>
          intro hxy
          have hx2 : x ∈ N := by rw [hN]; exact hx'
          have hy2 : y ∈ N := by rw [hN]; exact hy'
          rw [show (⟨x * y, hxy⟩ : N) = ⟨x, hx2⟩ * ⟨y, hy2⟩ from rfl, map_mul]
          exact P.mul_mem (ihx hx2) (ihy hy2)
        | inv x hx' ihx =>
          intro hxi
          have hx2 : x ∈ N := by rw [hN]; exact hx'
          rw [show (⟨x⁻¹, hxi⟩ : N) = (⟨x, hx2⟩ : N)⁻¹ from rfl, map_inv]
          exact P.inv_mem (ihx hx2)
      have hh : (h : Equiv.Perm (Fin n)) ∈ Subgroup.closure {a, b} := by
        rw [← hN]
        exact h.2
      exact key h hh h.2
    · rw [hP, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨_, hφa⟩
      · exact ⟨_, hφb⟩
  have hinj : Function.Injective φ := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, ← hcard] at h
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hk : Nat.card φ.ker = 1 := by
      have := h
      nlinarith
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hk
  have e : N ≃* P := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact e.isSimpleGroup

end Simple

section Transport

variable {G Q : Type*} [Group G] [Group Q]

theorem congr_apply_apply (e : G ≃* Q) (α : MulAut G) (x : Q) :
    MulAut.congr e α x = e (α (e.symm x)) := rfl

@[expose] def fixSubCongr (e : G ≃* Q) (α : MulAut G) :
    fixSub α ≃* fixSub (MulAut.congr e α) where
  toFun g := ⟨e g, by
    show MulAut.congr e α (e g) = e g
    rw [congr_apply_apply, MulEquiv.symm_apply_apply]
    exact congrArg e g.2⟩
  invFun h := ⟨e.symm h, by
    have h2 : MulAut.congr e α h = h := h.2
    rw [congr_apply_apply] at h2
    show α (e.symm h) = e.symm h
    have h3 := congrArg e.symm h2
    rwa [MulEquiv.symm_apply_apply] at h3⟩
  left_inv g := Subtype.ext (e.symm_apply_apply (g : G))
  right_inv h := Subtype.ext (e.apply_symm_apply (h : Q))
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

theorem congr_mem_inner_iff (e : G ≃* Q) (α : MulAut G) :
    MulAut.congr e α ∈ inner Q ↔ α ∈ inner G := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.symm q, MulEquiv.ext fun g => e.injective ?_⟩
    have h := congrArg (fun β : MulAut Q => β (e g)) hq
    simp only [MulAut.conj_apply, congr_apply_apply, MulEquiv.symm_apply_apply] at h
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]
  · rintro ⟨g, rfl⟩
    refine ⟨e g, MulEquiv.ext fun q => ?_⟩
    simp only [MulAut.conj_apply, congr_apply_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem congr_mul_self (e : G ≃* Q) (α : MulAut G) (h : α * α = 1) :
    MulAut.congr e α * MulAut.congr e α = 1 := by
  rw [← map_mul, h, map_one]

end Transport

end CFSG.Sporadic.FischerOddCore
