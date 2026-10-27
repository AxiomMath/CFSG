module

public import CFSG.Quasithin.EmptyFaithful.T1515hA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def a7ConjU (L : Subgroup G) (ℓ : ↥L) (u : ↥(blockU L)) : ↥(blockU L) :=
  ⟨(ℓ : G) * u * (ℓ : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) u).mp u.2⟩

@[expose] def a7UL {L : Subgroup G} (hL : IsShort2 L) (x : ↥(blockU L)) : ↥L :=
  ⟨x, C1.blockQ_le L (C1.blockU_le_blockQ hL x.2)⟩

structure A7Coh (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7)) (h : G) : Prop where
  short : IsShort2 L
  α_surj : Function.Surjective α
  α_ker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : G) ∈ blockQ L
  hC3 : ¬ 3 ∣ Nat.card α.ker
  γ_surj : Function.Surjective γ
  γ_ker : ∀ u : ↥(blockU L), γ u = 1 ↔ (u : G) ∈ blockZ L
  γ_equi : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (γ v) =
      permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ u))
  norm : h ∈ Subgroup.normalizer (L : Set G)
  ind : ∀ ℓ ℓ' : ↥L, (ℓ' : G) = h * ℓ * h⁻¹ → α ℓ' = α ℓ

namespace A7Coh

variable {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7)} {h : G}

omit [Finite G] in
theorem d_mem_Q (H : A7Coh L α γ h) {l : G} (hl : l ∈ L) : h * l * h⁻¹ * l⁻¹ ∈ blockQ L := by
  have hl' : h * l * h⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp H.norm l).mp hl
  have e := H.ind ⟨l, hl⟩ ⟨h * l * h⁻¹, hl'⟩ rfl
  have h1 : α (⟨h * l * h⁻¹, hl'⟩ * (⟨l, hl⟩ : ↥L)⁻¹) = 1 := by
    rw [map_mul, map_inv, e, mul_inv_cancel]
  exact (H.α_ker _).mp h1

theorem d_mem_U (H : A7Coh L α γ h) {l : G} (hl : l ∈ L) : h * l * h⁻¹ * l⁻¹ ∈ blockU L :=
  C1.commutator_mem_blockU_of_mem_blockQ H.short (fun _ hl' => H.d_mem_Q hl') l hl

@[expose] def Dd (H : A7Coh L α γ h) (l : ↥L) : ↥(blockU L) :=
  ⟨h * l * h⁻¹ * (l : G)⁻¹, H.d_mem_U l.2⟩

@[expose] def F (H : A7Coh L α γ h) (l : ↥L) : ↥(evenWeight 7) :=
  Multiplicative.toAdd (γ (H.Dd l))

theorem F_one (H : A7Coh L α γ h) : H.F 1 = 0 := by
  have : H.Dd 1 = 1 := Subtype.ext (by simp [Dd])
  simp [F, this]

theorem F_mul (H : A7Coh L α γ h) (l₁ l₂ : ↥L) :
    H.F (l₁ * l₂) = H.F l₁ + permWeight 7 (α l₁ : Equiv.Perm (Fin 7)) (H.F l₂) := by
  have e : H.Dd (l₁ * l₂) = H.Dd l₁ * a7ConjU L l₁ (H.Dd l₂) :=
    Subtype.ext (by simp only [Dd, a7ConjU, Subgroup.coe_mul]; group)
  unfold F
  rw [e, map_mul, toAdd_mul]
  congr 1
  exact H.γ_equi l₁ (H.Dd l₂) (a7ConjU L l₁ (H.Dd l₂)) rfl

theorem F_Q_mul (H : A7Coh L α γ h) (q l : ↥L) (hq : (q : G) ∈ blockQ L) :
    H.F (q * l) = H.F q + H.F l := by
  have hα : α q = 1 := (H.α_ker q).mpr hq
  rw [F_mul, hα]
  have : ((1 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 1 := rfl
  rw [this, a7_permWeight_one]

theorem F_conj_Q (H : A7Coh L α γ h) (ℓ q : ↥L) (hq : (q : G) ∈ blockQ L) :
    H.F (ℓ * q * ℓ⁻¹) = permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (H.F q) := by
  have h1 : H.F (ℓ * ℓ⁻¹) = 0 := by rw [mul_inv_cancel, F_one]
  rw [F_mul] at h1
  rw [mul_assoc, F_mul, F_Q_mul H q ℓ⁻¹ hq, a7_permWeight_add]
  calc _ = (H.F ℓ + permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (H.F ℓ⁻¹)) +
        permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (H.F q) := by abel
    _ = _ := by rw [h1, zero_add]

theorem uL_conj (H : A7Coh L α γ h) (ℓ : ↥L) (x : ↥(blockU L)) :
    a7UL H.short (a7ConjU L ℓ x) = ℓ * a7UL H.short x * ℓ⁻¹ := rfl

noncomputable def PhiU (H : A7Coh L α γ h) : ↥(blockU L) →* Multiplicative ↥(evenWeight 7) where
  toFun x := Multiplicative.ofAdd (H.F (a7UL H.short x))
  map_one' := by
    have : a7UL H.short (1 : ↥(blockU L)) = 1 := rfl
    simp [this, F_one]
  map_mul' x y := by
    have hq : ((a7UL H.short x : ↥L) : G) ∈ blockQ L := C1.blockU_le_blockQ H.short x.2
    have e : a7UL H.short (x * y) = a7UL H.short x * a7UL H.short y := rfl
    show Multiplicative.ofAdd (H.F (a7UL H.short (x * y))) = _
    rw [e, F_Q_mul H _ _ hq]
    rfl

theorem PhiU_ker (H : A7Coh L α γ h) : γ.ker ≤ (PhiU H).ker := by
  intro x hx
  have hxZ : (x : G) ∈ blockZ L := (H.γ_ker x).mp hx
  have hxQ : ((a7UL H.short x : ↥L) : G) ∈ blockQ L := C1.blockU_le_blockQ H.short x.2
  have hfix : ∀ a : alternatingGroup (Fin 7),
      permWeight 7 (a : Equiv.Perm (Fin 7)) (H.F (a7UL H.short x)) = H.F (a7UL H.short x) := by
    intro a
    obtain ⟨ℓ, rfl⟩ := H.α_surj a
    rw [← F_conj_Q H ℓ _ hxQ]
    have e : ℓ * a7UL H.short x * ℓ⁻¹ = a7UL H.short x := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hxZ.2 ℓ ℓ.2
      show (ℓ : G) * (x : G) * (ℓ : G)⁻¹ = (x : G)
      rw [this, mul_inv_cancel_right]
    rw [e]
  have h0 := a7_fixed_zero' _ hfix
  show Multiplicative.ofAdd (H.F (a7UL H.short x)) = 1
  rw [h0]
  rfl

theorem PhiU_act (H : A7Coh L α γ h) (a : alternatingGroup (Fin 7)) (x : ↥(blockU L)) :
    ∃ x' : ↥(blockU L),
      Multiplicative.toAdd (γ x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ x)) ∧
        Multiplicative.toAdd (PhiU H x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (PhiU H x)) := by
  obtain ⟨ℓ, rfl⟩ := H.α_surj a
  refine ⟨a7ConjU L ℓ x, H.γ_equi ℓ x _ rfl, ?_⟩
  show H.F (a7UL H.short (a7ConjU L ℓ x)) =
    permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (H.F (a7UL H.short x))
  rw [uL_conj H]
  exact F_conj_Q H ℓ _ (C1.blockU_le_blockQ H.short x.2)

theorem PhiU_dichotomy (H : A7Coh L α γ h) : (∀ x, PhiU H x = 1) ∨ (∀ x, PhiU H x = γ x) :=
  a7_schur_hom γ (PhiU H) H.γ_surj (PhiU_ker H) (PhiU_act H)

theorem PhiU_ne_gamma (H : A7Coh L α γ h) : ¬ ∀ x, PhiU H x = γ x := by
  intro hΦ
  have hall : ∀ x : ↥(blockU L), γ x = 1 := by
    intro x
    have hw : γ (H.Dd (a7UL H.short x) * x) = 1 := by
      rw [map_mul]
      have e1 : γ (H.Dd (a7UL H.short x)) = PhiU H x := rfl
      rw [e1, hΦ x]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul]
      exact a7_two_nsmul _
    have hwZ : ((H.Dd (a7UL H.short x) * x : ↥(blockU L)) : G) ∈ blockZ L := (H.γ_ker _).mp hw
    have e2 : ((H.Dd (a7UL H.short x) * x : ↥(blockU L)) : G) = h * x * h⁻¹ := by
      simp only [Dd, a7UL, Subgroup.coe_mul]
      group
    rw [e2] at hwZ
    have hxc : (x : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : h * l * h⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp H.norm l).mp hl
      have e3 : (h * l * h⁻¹) * (h * x * h⁻¹) = (h * x * h⁻¹) * (h * l * h⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hwZ.2 _ hl'
      calc l * x = h⁻¹ * ((h * l * h⁻¹) * (h * x * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * x * h⁻¹) * (h * l * h⁻¹)) * h := by rw [e3]
        _ = x * l := by group
    exact (H.γ_ker x).mpr ⟨x.2, hxc⟩
  obtain ⟨u, hu⟩ := H.γ_surj (Multiplicative.ofAdd (a7PairVec 0 1))
  have := hall u
  rw [hu] at this
  exact a7PairVec_ne_zero (ofAdd_eq_one.mp this)

theorem F_U (H : A7Coh L α γ h) (x : ↥(blockU L)) : H.F (a7UL H.short x) = 0 := by
  rcases PhiU_dichotomy H with h0 | h1
  · have := h0 x
    exact ofAdd_eq_one.mp this
  · exact absurd h1 (PhiU_ne_gamma H)

theorem F_Q (H : A7Coh L α γ h) (q : ↥L) (hq : (q : G) ∈ blockQ L) : H.F q = 0 := by
  have hfix : ∀ a : alternatingGroup (Fin 7),
      permWeight 7 (a : Equiv.Perm (Fin 7)) (H.F q) = H.F q := by
    intro a
    obtain ⟨ℓ, rfl⟩ := H.α_surj a
    rw [← F_conj_Q H ℓ q hq]
    have hu' : ((q : G))⁻¹ * ((ℓ : G) * q * (ℓ : G)⁻¹) ∈ blockU L := by
      have := C1.commutator_mem_blockU (L := L) (a := (q : G)⁻¹) (l := ℓ)
        (Subgroup.inv_mem _ hq) ℓ.2
      simpa [mul_assoc] using this
    let u' : ↥(blockU L) := ⟨_, hu'⟩
    have e : ℓ * q * ℓ⁻¹ = q * a7UL H.short u' := Subtype.ext (by simp [a7UL, u'])
    rw [e, F_Q_mul H q _ hq, F_U H u', add_zero]
  exact a7_fixed_zero' _ hfix

theorem F_eq_of_α_eq (H : A7Coh L α γ h) {l l' : ↥L} (hll : α l = α l') : H.F l = H.F l' := by
  have hq : α (l⁻¹ * l') = 1 := by rw [map_mul, map_inv, hll, inv_mul_cancel]
  have hq' : ((l⁻¹ * l' : ↥L) : G) ∈ blockQ L := (H.α_ker _).mp hq
  have e : l * (l⁻¹ * l') = l' := mul_inv_cancel_left l l'
  rw [← e, F_mul, F_Q H _ hq', a7_permWeight_zero, add_zero]

noncomputable def fbar (H : A7Coh L α γ h) (a : alternatingGroup (Fin 7)) : ↥(evenWeight 7) :=
  H.F (Function.surjInv H.α_surj a)

theorem fbar_apply (H : A7Coh L α γ h) (l : ↥L) : H.fbar (α l) = H.F l :=
  F_eq_of_α_eq H (Function.surjInv_eq H.α_surj (α l))

theorem fbar_mul (H : A7Coh L α γ h) (a b : alternatingGroup (Fin 7)) :
    H.fbar (a * b) = H.fbar a + permWeight 7 (a : Equiv.Perm (Fin 7)) (H.fbar b) := by
  obtain ⟨l₁, rfl⟩ := H.α_surj a
  obtain ⟨l₂, rfl⟩ := H.α_surj b
  rw [← map_mul, fbar_apply, fbar_apply, fbar_apply, F_mul]

theorem coboundary (H : A7Coh L α γ h) :
    ∃ y : ↥(evenWeight 7), ∀ l : ↥L,
      H.F l = permWeight 7 (α l : Equiv.Perm (Fin 7)) y - y := by
  obtain ⟨y, hy⟩ := a7_cocycle_coboundary H.fbar (fbar_mul H)
  exact ⟨y, fun l => by rw [← fbar_apply]; exact hy (α l)⟩

theorem centralizes (H : A7Coh L α γ h) {y : ↥(evenWeight 7)}
    (hy : ∀ l : ↥L, H.F l = permWeight 7 (α l : Equiv.Perm (Fin 7)) y - y)
    {x : ↥(blockU L)} (hx : Multiplicative.toAdd (γ x) = y) :
    (x : G) * h ∈ Subgroup.centralizer (L : Set G) := by
  have hZ : ∀ l ∈ L, ((x : G) * h) * l * ((x : G) * h)⁻¹ * l⁻¹ ∈ blockZ L := by
    intro l hl
    let ℓ : ↥L := ⟨l, hl⟩
    let w : ↥(blockU L) := x * H.Dd ℓ * a7ConjU L ℓ x⁻¹
    have hw : (w : G) = ((x : G) * h) * l * ((x : G) * h)⁻¹ * l⁻¹ := by
      simp only [w, Dd, a7ConjU, Subgroup.coe_mul, Subgroup.coe_inv, ℓ]
      group
    have hγw : γ w = 1 := by
      apply Multiplicative.toAdd.injective
      have h1 : Multiplicative.toAdd (γ w) = Multiplicative.toAdd (γ x) + H.F ℓ +
          Multiplicative.toAdd (γ (a7ConjU L ℓ x⁻¹)) := by
        simp only [w, map_mul, toAdd_mul]
        rfl
      have h2 : Multiplicative.toAdd (γ (a7ConjU L ℓ x⁻¹)) =
          permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (-y) := by
        rw [H.γ_equi ℓ x⁻¹ _ rfl, map_inv, toAdd_inv, hx]
      rw [h1, h2, hx, hy ℓ, a7_permWeight_neg]
      show _ = 0
      abel
    rw [← hw]
    exact (H.γ_ker w).mp hγw
  have hM : IsPGroup 2 ↥(blockZ L) :=
    (C1.isPGroup_blockU H.short).to_le (show blockZ L ≤ blockU L from inf_le_left)
  have hbot := C1.commutator_mem_of_noTwoQuotient (L := L) (M := blockZ L) (N := ⊥) H.short.1 hM
    (fun m _ n hn => by
      rw [Subgroup.mem_bot] at hn ⊢
      simp [hn])
    (fun l hl w hw => by
      rw [Subgroup.mem_bot]
      have := Subgroup.mem_centralizer_iff.mp hw.2 l hl
      rw [this]
      group)
    (y := (x : G) * h) hZ
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hbot l hl
  rw [Subgroup.mem_bot] at h1
  have e : ((x : G) * h) * l * ((x : G) * h)⁻¹ = l := mul_inv_eq_one.mp h1
  calc l * ((x : G) * h) = (((x : G) * h) * l * ((x : G) * h)⁻¹) * ((x : G) * h) := by rw [e]
    _ = ((x : G) * h) * l := by group

theorem final (H : A7Coh L α γ h) (u : ↥(blockU L)) (d : Fin 7)
    (hu : Multiplicative.toAdd (γ u) = a7ETheta d) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) (hd : {d} ∈ P)
    (hY : h ∈ Subgroup.centralizer (a7Y1Of L α P : Set G)) :
    ∃ c ∈ Subgroup.centralizer (L : Set G), ∃ k : ℤ, h = c * (u : G) ^ k := by
  obtain ⟨y, hy⟩ := H.coboundary
  obtain ⟨x, hx⟩ := H.γ_surj (Multiplicative.ofAdd y)
  have hx' : Multiplicative.toAdd (γ x) = y := by rw [hx]; rfl
  have hcent := H.centralizes hy hx'
  have hyfix : ∀ a : Equiv.Perm (Fin 7), a ∈ alternatingGroup (Fin 7) → StabilizesPartition a P →
      a ^ 3 = 1 → permWeight 7 a y = y := by
    intro a ha hst ha3
    obtain ⟨t, hta, htmem⟩ := a7_exists_Y1_gen H.α_surj H.hC3 ha hst ha3
    have hcomm : (t : G) * h = h * t := Subgroup.mem_centralizer_iff.mp hY t htmem
    have hFt : H.F t = 0 := by
      have : H.Dd t = 1 := Subtype.ext (by
        show h * (t : G) * h⁻¹ * (t : G)⁻¹ = 1
        rw [← hcomm]
        group)
      simp [F, this]
    have h1 := hy t
    rw [hFt, hta] at h1
    exact (sub_eq_zero.mp h1.symm)
  have hUL : (u : G) ∈ L := C1.blockQ_le L (C1.blockU_le_blockQ H.short u.2)
  rcases a7_fixed_of_partition hP hd y hyfix with h0 | h1
  ·
    have hγx : γ x = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hx', h0]
      rfl
    have hxZ : (x : G) ∈ blockZ L := (H.γ_ker x).mp hγx
    have hh : h ∈ Subgroup.centralizer (L : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxZ.2) hcent
      simpa using this
    exact ⟨h, hh, 0, by simp⟩
  ·
    have hγz : γ (x * u⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hx', hu, h1]
      exact add_neg_cancel _
    have hzZ : ((x * u⁻¹ : ↥(blockU L)) : G) ∈ blockZ L := (H.γ_ker _).mp hγz
    have hc : ((x * u⁻¹ : ↥(blockU L)) : G)⁻¹ * ((x : G) * h) ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hzZ.2) hcent
    refine ⟨_, hc, -1, ?_⟩
    have hcomm : (u : G)⁻¹ * (((x * u⁻¹ : ↥(blockU L)) : G)⁻¹ * ((x : G) * h)) =
        (((x * u⁻¹ : ↥(blockU L)) : G)⁻¹ * ((x : G) * h)) * (u : G)⁻¹ :=
      Subgroup.mem_centralizer_iff.mp hc _ (Subgroup.inv_mem _ hUL)
    rw [zpow_neg_one, ← hcomm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end A7Coh

theorem a7CohomStep : A7CohomStep := by
  intro G _ _ L α β hshort hstr P d hP hd u hu h hn hind hY
  obtain ⟨γ, hγ⟩ := a7_exists_gamma hstr
  have hC3 : ¬ 3 ∣ Nat.card α.ker := a7_hC3 hstr
  have hαker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : G) ∈ blockQ L := by
    intro ℓ
    rw [← MonoidHom.mem_ker, hstr.2.1]
    exact CFSG.QuasithinUnique.L246A7.mem_pCore_iff_mem_blockQ ℓ
  have H : A7Coh L α γ h :=
    { short := hshort
      α_surj := hstr.1
      α_ker := hαker
      hC3 := hC3
      γ_surj := hγ.surj
      γ_ker := hγ.ker
      γ_equi := hγ.equi
      norm := hn
      ind := fun ℓ ℓ' h' => Subtype.ext (by simpa using hind ℓ ℓ' h') }
  have hu' : Multiplicative.toAdd (γ u) = a7ETheta d := by
    have h1 : (QuotientAddGroup.mk (Multiplicative.toAdd (γ u)) : AltHeart 7) =
        QuotientAddGroup.mk (a7ETheta d) := by rw [hγ.mk_eq u, hu]
    have := congrArg a7E h1
    rwa [a7E_mk, a7E_mk] at this
  exact H.final u d hu' hP hd hY

end CFSG.Quasithin
