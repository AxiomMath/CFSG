module

public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.Timmesfeld.Bridge.Asc72YU3
public import CFSG.Timmesfeld.Bridge.Asc72ZAlt
public import CFSG.CharacterTheory.Semidihedral.Principal.OddCentralAlternatingFiveSplit

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Semidihedral.Principal
  (odd_central_alternating_five_extension_splits_over_derived_subgroup)

private theorem natCard_le_sq_of_fixed {X : Type*} [Group X] [Finite X] {Z F : Subgroup X}
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hsq : ∀ y ∈ Z, y * y = 1) (α : X ≃* X)
    (hαZ : ∀ y ∈ Z, α y ∈ Z) (hα2 : ∀ y ∈ Z, α (α y) = y)
    (hF : ∀ y ∈ Z, α y = y → y ∈ F) (hFZ : F ≤ Z) : Nat.card Z ≤ Nat.card F ^ 2 := by
  let ψ : Z →* Z :=
    { toFun := fun y => ⟨y * α y, Z.mul_mem y.2 (hαZ y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => Subtype.ext (by
        change (y₁ : X) * y₂ * α (y₁ * y₂) = y₁ * α y₁ * (y₂ * α y₂)
        rw [map_mul]
        have h := hcomm _ y₂.2 _ (hαZ _ y₁.2)
        calc (y₁ : X) * y₂ * (α y₁ * α y₂) = y₁ * (y₂ * α y₁) * α y₂ := by group
          _ = y₁ * (α y₁ * y₂) * α y₂ := by rw [h]
          _ = y₁ * α y₁ * (y₂ * α y₂) := by group) }
  have hker : ψ.ker ≤ F.subgroupOf Z := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (y : X) * α y = 1 := congrArg Subtype.val hy
    have h2 : α y = y := by
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (hsq y y.2)]
    exact Subgroup.mem_subgroupOf.mpr (hF y y.2 h2)
  have hrange : ψ.range ≤ F.subgroupOf Z := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr (hF _ (Z.mul_mem y.2 (hαZ y y.2)) ?_)
    change α ((y : X) * α y) = y * α y
    rw [map_mul, hα2 y y.2]
    exact hcomm _ (hαZ y y.2) _ y.2
  have hcardF : Nat.card (F.subgroupOf Z) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFZ).toEquiv
  rw [← Subgroup.card_ker_mul_card_range ψ, pow_two, ← hcardF]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)

private theorem natCard_le_two_of_unique {X : Type*} [Group X] {F : Subgroup X}
    (h : ∀ y ∈ F, ∀ y' ∈ F, y ≠ 1 → y' ≠ 1 → y = y') : Nat.card F ≤ 2 := by
  classical
  by_cases hex : ∃ y₀ ∈ F, y₀ ≠ 1
  · obtain ⟨y₀, hy₀, hy₀1⟩ := hex
    have hsub : (F : Set X) ⊆ {1, y₀} := by
      intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (h y hy y₀ hy₀ hy1 hy₀1)
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le 1 {y₀}).trans ?_
    rw [Set.ncard_singleton]
  · have hex' : ∀ y ∈ F, y = 1 := fun y hy => by
      by_contra h1
      exact hex ⟨y, hy, h1⟩
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hex'
    rw [this, Subgroup.card_bot]
    norm_num

variable {G : Type} [Group G]

private noncomputable def conjInv {K₁ : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haK : a ∈ Subgroup.normalizer (K₁ : Set G)) : K₁ ≃* K₁ where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK x).mp x.2⟩
  invFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK x).mp x.2⟩
  left_inv x := Subtype.ext (by
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    simp only [this]
    calc a * (a * (x : G) * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group)
  right_inv x := Subtype.ext (by
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    simp only [this]
    calc a * (a * (x : G) * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group)
  map_mul' x y := Subtype.ext (by
    change a * ((x : G) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹)
    group)

private theorem conjInv_apply {K₁ : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haK : a ∈ Subgroup.normalizer (K₁ : Set G)) (x : K₁) :
    ((conjInv ha2 haK x : K₁) : G) = a * x * a⁻¹ := rfl

variable [Finite G]

theorem alt5_and_outer_of_fix_center {K₁ T₁ : Subgroup G}
    (hperf : commutator K₁ = ⊤) (hodd : Odd (Nat.card (Subgroup.center K₁)))
    (hB : CFSG.BenderSuzuki.IsBenderGroup (K₁ ⧸ Subgroup.center K₁))
    (hT₁K : T₁ ≤ K₁) (hT₁ : IsPGroup 2 T₁)
    (hT₁max : ∀ P : Subgroup G, IsPGroup 2 P → T₁ ≤ P → P ≤ K₁ → P = T₁)
    {a : G} (ha2 : a * a = 1) (haK : a ∈ Subgroup.normalizer (K₁ : Set G))
    (haT : ∀ t ∈ T₁, a * t * a⁻¹ ∈ T₁)
    (hfix : ∀ t ∈ T₁, ∀ t' ∈ T₁, (∀ s ∈ T₁, Commute t s) → (∀ s ∈ T₁, Commute t' s) →
      t * t = 1 → t' * t' = 1 → Commute a t → Commute a t' → t ≠ 1 → t' ≠ 1 → t = t') :
    Nonempty (K₁ ≃* alternatingGroup (Fin 5)) ∧
      ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, a * x * a⁻¹ = k * x * k⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zc := Subgroup.center K₁ with hZc
  set π : K₁ →* K₁ ⧸ Zc := QuotientGroup.mk' Zc with hπ
  have hdisj : ∀ x : K₁, x ∈ Zc → (x : G) ∈ T₁ → x = 1 := by
    intro x hxZ hxT
    obtain ⟨n, hn⟩ := hT₁ ⟨x, hxT⟩
    have hx : x ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    have hxc : x ^ Nat.card Zc = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hxZ⟩ : Zc)))
      rwa [Subgroup.coe_pow] at h
    have hcop : Nat.Coprime (2 ^ n) (Nat.card Zc) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    have hdvd := hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx)
    exact orderOf_eq_one_iff.mp (hdvd.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hxc))
  have hT₁p : IsPGroup 2 (T₁.subgroupOf K₁) :=
    hT₁.comap_of_injective K₁.subtype K₁.subtype_injective
  let T₁s : Sylow 2 K₁ :=
    { toSubgroup := T₁.subgroupOf K₁
      isPGroup' := hT₁p
      is_maximal' := fun {Q'} hQ' hle => by
        have hP := hT₁max (Q'.map K₁.subtype) (hQ'.map K₁.subtype)
          (fun t ht => ⟨⟨t, hT₁K ht⟩, hle (Subgroup.mem_subgroupOf.mpr ht), rfl⟩)
          (Subgroup.map_subtype_le Q')
        rw [← hP]
        exact (Subgroup.comap_map_eq_self_of_injective K₁.subtype_injective Q').symm }
  let Q : Sylow 2 (K₁ ⧸ Zc) := T₁s.mapSurjective (QuotientGroup.mk'_surjective Zc)
  have hQmem : ∀ y, y ∈ (Q : Subgroup (K₁ ⧸ Zc)) ↔ ∃ t : K₁, (t : G) ∈ T₁ ∧ π t = y := by
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  set φ := conjInv ha2 haK with hφ
  have hφZ : Zc.map φ.toMonoidHom = Zc :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set α : MulAut (K₁ ⧸ Zc) := QuotientGroup.congr Zc Zc φ hφZ with hα
  have hαπ : ∀ x : K₁, α (π x) = π (φ x) := fun x => rfl
  have hφφ : ∀ x : K₁, φ (φ x) = x := by
    intro x
    apply Subtype.ext
    rw [conjInv_apply, conjInv_apply, inv_eq_of_mul_eq_one_right ha2]
    calc a * (a * (x : G) * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group
  have hαα : α * α = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Zc y
    rw [MulAut.mul_apply, hαπ, hαπ, hφφ, MulAut.one_apply]
  have hα2 : ∀ y, α (α y) = y := fun y => by
    rw [← MulAut.mul_apply, hαα, MulAut.one_apply]
  have hαQ : ∀ s ∈ (Q : Subgroup (K₁ ⧸ Zc)), α s ∈ (Q : Subgroup (K₁ ⧸ Zc)) := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (hQmem s).mp hs
    rw [hαπ]
    exact (hQmem _).mpr ⟨φ t, by rw [conjInv_apply]; exact haT _ ht, rfl⟩
  set ZQ : Subgroup (K₁ ⧸ Zc) :=
    (Subgroup.center (Q : Subgroup (K₁ ⧸ Zc))).map (Q : Subgroup (K₁ ⧸ Zc)).subtype with hZQ
  have hZQcard : Nat.card ZQ = Nat.card (Subgroup.center (Q : Subgroup (K₁ ⧸ Zc))) :=
    Subgroup.card_map_of_injective (Q : Subgroup (K₁ ⧸ Zc)).subtype_injective
  have hZQ_mem : ∀ y ∈ ZQ, y ∈ (Q : Subgroup (K₁ ⧸ Zc)) ∧
      ∀ s ∈ (Q : Subgroup (K₁ ⧸ Zc)), Commute y s := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c.2, fun s hs => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨s, hs⟩)).symm
  have hZQ_of : ∀ y ∈ (Q : Subgroup (K₁ ⧸ Zc)),
      (∀ s ∈ (Q : Subgroup (K₁ ⧸ Zc)), Commute y s) → y ∈ ZQ := by
    intro y hy hc
    exact ⟨⟨y, hy⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm, rfl⟩
  have hlift : ∀ y ∈ ZQ, ∃ t : K₁, (t : G) ∈ T₁ ∧ (∀ s ∈ T₁, Commute (t : G) s) ∧ π t = y := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := hZQ_mem y hy
    obtain ⟨t, ht, rfl⟩ := (hQmem _).mp hyQ
    refine ⟨t, ht, fun s hs => ?_, rfl⟩
    set s' : K₁ := ⟨s, hT₁K hs⟩
    have hc := hyc _ ((hQmem _).mpr ⟨s', hs, rfl⟩)
    have hmem : t * s' * t⁻¹ * s'⁻¹ ∈ Zc := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
        map_inv, map_inv, ← hπ, hc.eq]
      group
    have hT : ((t * s' * t⁻¹ * s'⁻¹ : K₁) : G) ∈ T₁ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact T₁.mul_mem (T₁.mul_mem (T₁.mul_mem ht hs) (T₁.inv_mem ht)) (T₁.inv_mem hs)
    have h1 := hdisj _ hmem hT
    have h2 : t * s' = s' * t := commutatorElement_eq_one_iff_mul_comm.mp
      (by rw [commutatorElement_def]; exact h1)
    exact congrArg Subtype.val h2
  have hfixlift : ∀ t : K₁, (t : G) ∈ T₁ → α (π t) = π t → Commute a t := by
    intro t ht hαt
    rw [hαπ] at hαt
    have hmem : φ t * t⁻¹ ∈ Zc := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, ← hπ, hαt,
        mul_inv_cancel]
    have hT : ((φ t * t⁻¹ : K₁) : G) ∈ T₁ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjInv_apply]
      exact T₁.mul_mem (haT _ ht) (T₁.inv_mem ht)
    have h2 : a * t * a⁻¹ = t := by
      have := congrArg Subtype.val (mul_inv_eq_one.mp (hdisj _ hmem hT))
      rwa [conjInv_apply] at this
    show a * t = t * a
    calc a * (t : G) = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [h2]
  have hZsq : ∀ y ∈ ZQ, y * y = 1 := fun y hy =>
    IsBenderGroup.mul_self_eq_one_of_commute hB Q (hZQ_mem y hy).1 (hZQ_mem y hy).2
  have hsqlift : ∀ t : K₁, (t : G) ∈ T₁ → π t * π t = 1 → (t : G) * t = 1 := by
    intro t ht h
    have hmem : t * t ∈ Zc := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, ← hπ]
      exact h
    have hT : ((t * t : K₁) : G) ∈ T₁ := by
      rw [Subgroup.coe_mul]
      exact T₁.mul_mem ht ht
    exact congrArg Subtype.val (hdisj _ hmem hT)
  let F : Subgroup (K₁ ⧸ Zc) :=
    { carrier := {y | y ∈ ZQ ∧ α y = y}
      mul_mem' := fun hx hy => ⟨ZQ.mul_mem hx.1 hy.1, by rw [map_mul, hx.2, hy.2]⟩
      one_mem' := ⟨ZQ.one_mem, map_one α⟩
      inv_mem' := fun hx => ⟨ZQ.inv_mem hx.1, by rw [map_inv, hx.2]⟩ }
  have hF2 : Nat.card F ≤ 2 := by
    apply natCard_le_two_of_unique
    rintro y ⟨hyZ, hyα⟩ y' ⟨hy'Z, hy'α⟩ hy1 hy'1
    obtain ⟨t, htT, htc, rfl⟩ := hlift y hyZ
    obtain ⟨t', ht'T, ht'c, rfl⟩ := hlift y' hy'Z
    have ht1 : (t : G) ≠ 1 := fun h => hy1 (by rw [show t = 1 from Subtype.ext h, map_one])
    have ht'1 : (t' : G) ≠ 1 := fun h => hy'1 (by rw [show t' = 1 from Subtype.ext h, map_one])
    rw [show t = t' from Subtype.ext (hfix t htT t' ht'T htc ht'c
      (hsqlift t htT (hZsq _ hyZ)) (hsqlift t' ht'T (hZsq _ hy'Z)) (hfixlift t htT hyα)
      (hfixlift t' ht'T hy'α) ht1 ht'1)]
  have hZcomm : ∀ x ∈ ZQ, ∀ y ∈ ZQ, x * y = y * x := fun x hx y hy =>
    ((hZQ_mem x hx).2 y (hZQ_mem y hy).1).eq
  have hαZ : ∀ y ∈ ZQ, α y ∈ ZQ := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := hZQ_mem y hy
    refine hZQ_of _ (hαQ y hyQ) fun s hs => ?_
    have h := (hyc _ (hαQ s hs)).eq
    show α y * s = s * α y
    calc α y * s = α y * α (α s) := by rw [hα2]
      _ = α (y * α s) := by rw [map_mul]
      _ = α (α s * y) := by rw [h]
      _ = s * α y := by rw [map_mul, hα2]
  have hle4 : Nat.card ZQ ≤ 4 := by
    have h := natCard_le_sq_of_fixed hZcomm hZsq α hαZ (fun y _ => hα2 y)
      (F := F) (fun y hy h => ⟨hy, h⟩) (fun y hy => hy.1)
    calc Nat.card ZQ ≤ Nat.card F ^ 2 := h
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_left hF2 2
      _ = 4 := by norm_num
  have h4 : 4 ≤ Nat.card ZQ := hZQcard ▸ IsBenderGroup.four_le_card_center hB Q
  have hnotall : ¬ ∀ y ∈ ZQ, α y = y := by
    intro hall
    have := Subgroup.card_le_of_le (show ZQ ≤ F from fun y hy => ⟨hy, hall y hy⟩)
    omega
  rcases mulEquiv_of_card_center_le_four hB Q (hZQcard ▸ hle4) with he | he
  ·
    obtain ⟨e⟩ := he
    obtain ⟨e5⟩ := AltFive.nonempty_psl2Model_two_equiv
    obtain ⟨-, -, -, -, -, ⟨eA⟩, -⟩ :=
      odd_central_alternating_five_extension_splits_over_derived_subgroup (α := Fin 5)
        (by simp) Zc le_rfl hodd ⟨e.trans e5⟩
    let eK : K₁ ≃* alternatingGroup (Fin 5) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hperf.symm).trans eA)
    refine ⟨⟨eK⟩, ?_⟩
    rintro ⟨k, hk, hak⟩
    apply hnotall
    have hZ1 : ∀ c : K₁, c ∈ Zc → c = 1 := by
      intro c hc
      have hc' : eK c ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨m, rfl⟩ := eK.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc m]
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
        MulEquiv.map_eq_one_iff] at hc'
      exact hc'
    have hkk : k * k = 1 := by
      have hc : (⟨k * k, K₁.mul_mem hk hk⟩ : K₁) ∈ Zc := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        show (g : G) * (k * k) = k * k * g
        have hag : a * g * a⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp haK g).mp g.2
        have h3 : k * k * g * (k * k)⁻¹ = g := by
          calc k * k * g * (k * k)⁻¹ = k * (k * g * k⁻¹) * k⁻¹ := by group
            _ = k * (a * g * a⁻¹) * k⁻¹ := by rw [hak g g.2]
            _ = a * (a * g * a⁻¹) * a⁻¹ := (hak _ hag).symm
            _ = (a * a) * g * (a * a)⁻¹ := by group
            _ = g := by rw [ha2]; group
        calc (g : G) * (k * k) = k * k * g * (k * k)⁻¹ * (k * k) := by rw [h3]
          _ = k * k * g := by group
      have := congrArg Subtype.val (hZ1 _ hc)
      exact this
    have hkT : k ∈ T₁ := by
      have hkN : Subgroup.zpowers k ≤ Subgroup.normalizer (T₁ : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
        intro t
        constructor
        · intro ht
          rw [← hak t (hT₁K ht)]
          exact haT t ht
        · intro ht
          have hy := haT _ ht
          rw [hak _ (hT₁K ht)] at hy
          have e1 : k * (k * t * k⁻¹) * k⁻¹ = t := by
            calc k * (k * t * k⁻¹) * k⁻¹ = (k * k) * t * (k * k)⁻¹ := by group
              _ = t := by rw [hkk]; group
          rwa [e1] at hy
      have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
        have h2 : orderOf k ∣ 2 ^ 1 :=
          orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hkk)
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
        exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
      have hP := hT₁max (T₁ ⊔ Subgroup.zpowers k) (hT₁.to_sup_of_normal_left' hkp hkN)
        le_sup_left (sup_le hT₁K ((Subgroup.zpowers_le).mpr hk))
      rw [← hP]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
    intro y hy
    obtain ⟨t, -, htc, rfl⟩ := hlift y hy
    rw [hαπ]
    congr 1
    apply Subtype.ext
    rw [conjInv_apply, hak t t.2]
    calc k * (t : G) * k⁻¹ = t * k * k⁻¹ := by rw [(htc k hkT).eq]
      _ = t := by group
  ·
    exfalso
    obtain ⟨e⟩ := he
    apply hnotall
    intro y hy
    obtain ⟨hyQ, hyc⟩ := hZQ_mem y hy
    have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 :=
      CFSG.Models.benderPSU3Model_eq_psu3 2
    let e' : K₁ ⧸ Zc ≃* CFSG.Open.PSU3 2 2 := e.trans (MulEquiv.subgroupCongr hmodel)
    exact YU3.fix_center_of_mulEquiv_psu3 le_rfl e' Q α hαα hαQ hyQ hyc

theorem alt5_and_outer_of_fix_center_inf {K₁ S' : Subgroup G}
    (hperf : commutator K₁ = ⊤) (hodd : Odd (Nat.card (Subgroup.center K₁)))
    (hB : CFSG.BenderSuzuki.IsBenderGroup (K₁ ⧸ Subgroup.center K₁))
    (hS' : IsPGroup 2 S' ∧ ∀ P : Subgroup G, IsPGroup 2 P → S' ≤ P → P = S')
    (hS'K : S' ≤ Subgroup.normalizer (K₁ : Set G)) {a : G} (ha2 : a * a = 1) (haS' : a ∈ S')
    (hfix : ∀ t ∈ S' ⊓ K₁, ∀ t' ∈ S' ⊓ K₁, (∀ s ∈ S' ⊓ K₁, Commute t s) →
      (∀ s ∈ S' ⊓ K₁, Commute t' s) → t * t = 1 → t' * t' = 1 → Commute a t → Commute a t' →
      t ≠ 1 → t' ≠ 1 → t = t') :
    Nonempty (K₁ ≃* alternatingGroup (Fin 5)) ∧
      ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, a * x * a⁻¹ = k * x * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S' (S' ⊔ K₁) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hS'.1, fun hdvd => ?_⟩
    let S : Sylow 2 G := ⟨S', hS'.1, fun {Q} hQ hle => hS'.2 Q hQ hle⟩
    exact S.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hT := hSyl.inf_of_le_normalizer le_sup_right (sup_le hS'K Subgroup.le_normalizer)
  have haK : a ∈ Subgroup.normalizer (K₁ : Set G) := hS'K haS'
  refine alt5_and_outer_of_fix_center hperf hodd hB inf_le_right hS'.1.to_inf_left
    (fun P hP hle hPK => hT.eq_of_le hle hPK hP) ha2 haK (fun t ht => ?_) hfix
  exact ⟨S'.mul_mem (S'.mul_mem haS' ht.1) (S'.inv_mem haS'),
    (Subgroup.mem_normalizer_iff.mp haK t).mp ht.2⟩

end CFSG.OddTranspositions
