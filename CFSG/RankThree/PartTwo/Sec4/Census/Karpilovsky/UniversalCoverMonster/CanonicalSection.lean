module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.AGLEmbedding
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def PerfectCoreOf (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ L : Subgroup G, L ≤ H ∧ (∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) ∧ Group.IsPerfect L ∧
    Nat.Coprime (L.relIndex H) p

@[expose] def PerfectCoreCell (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ L : Subgroup G, L ≤ H ∧ (∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) ∧ Group.IsPerfect L ∧
    Nat.Coprime (L.relIndex H) p ∧ KernelTrivialAt L p

end Defs

section Sections

variable {G E : Type} [Group G] [Group E] (π : E →* G)

@[expose] def sectionDiff (hC : π.ker ≤ Subgroup.center E) {H : Subgroup G} (σ₁ σ₂ : H →* E)
    (h₁ : ∀ h, π (σ₁ h) = h) (h₂ : ∀ h, π (σ₂ h) = h) : H →* π.ker where
  toFun h := ⟨(σ₁ h)⁻¹ * σ₂ h, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, h₂, inv_mul_cancel]⟩
  map_one' := by ext; simp
  map_mul' a b := by
    have hc : (σ₁ a)⁻¹ * σ₂ a ∈ Subgroup.center E := hC (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, h₂, inv_mul_cancel])
    have := Subgroup.mem_center_iff.1 hc ((σ₁ b)⁻¹)
    ext
    simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
    calc (σ₁ b)⁻¹ * (σ₁ a)⁻¹ * (σ₂ a * σ₂ b)
        = (σ₁ b)⁻¹ * ((σ₁ a)⁻¹ * σ₂ a) * σ₂ b := by simp only [mul_assoc]
      _ = ((σ₁ a)⁻¹ * σ₂ a) * (σ₁ b)⁻¹ * σ₂ b := by rw [← this]
      _ = _ := by simp only [mul_assoc]

theorem sectionDiff_apply (hC : π.ker ≤ Subgroup.center E) {H : Subgroup G} (σ₁ σ₂ : H →* E)
    (h₁ : ∀ h, π (σ₁ h) = h) (h₂ : ∀ h, π (σ₂ h) = h) (h : H) :
    ((sectionDiff π hC σ₁ σ₂ h₁ h₂ h : π.ker) : E) = (σ₁ h)⁻¹ * σ₂ h := rfl

end Sections

section Uniqueness

variable {G E : Type} [Group G] [Group E]

theorem hom_eq_one_of_perfect_core {p : ℕ} {H L : Subgroup G} (hLH : L ≤ H)
    (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hL : Group.IsPerfect L)
    (hcop : Nat.Coprime (L.relIndex H) p) {Z : Subgroup E} (hZc : Z ≤ Subgroup.center E)
    (hZp : IsPGroup p Z) (δ : H →* Z) : δ = 1 := by
  have hLker : ∀ x : L, δ (Subgroup.inclusion hLH x) = 1 := by
    let δL : L →* Z := δ.comp (Subgroup.inclusion hLH)
    have hcomm : commutator L ≤ δL.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      refine Subtype.ext ?_
      change ⁅((δL g₁ : Z) : E), ((δL g₂ : Z) : E)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hZc (δL g₂).2) ((δL g₁ : Z) : E)
    rw [Group.IsPerfect.commutator_eq_top (G := L)] at hcomm
    intro x
    exact hcomm (Subgroup.mem_top x)
  have : (L.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn g g.2 n hn⟩
  refine MonoidHom.ext fun h => ?_
  have hmem : h ^ (L.subgroupOf H).index ∈ L.subgroupOf H := Subgroup.pow_index_mem _ h
  have h1 : δ (h ^ (L.subgroupOf H).index) = 1 := by
    have := hLker ⟨((h ^ (L.subgroupOf H).index : H) : G), hmem⟩
    have e : Subgroup.inclusion hLH ⟨((h ^ (L.subgroupOf H).index : H) : G), hmem⟩ =
        h ^ (L.subgroupOf H).index := Subtype.ext rfl
    rwa [e] at this
  rw [map_pow] at h1
  obtain ⟨k, hk⟩ := hZp (δ h)
  have hm : Nat.Coprime (L.subgroupOf H).index (p ^ k) := Nat.Coprime.pow_right k hcop
  have hord1 : orderOf (δ h) ∣ (L.subgroupOf H).index := orderOf_dvd_of_pow_eq_one h1
  have hord2 : orderOf (δ h) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have : orderOf (δ h) = 1 := Nat.eq_one_of_dvd_coprimes hm hord1 hord2
  rw [orderOf_eq_one_iff] at this
  simpa using this

variable (π : E →* G)

theorem sectionDiff_eq_one {p : ℕ} (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker)
    {H L : Subgroup G} (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L)
    (hL : Group.IsPerfect L) (hcop : Nat.Coprime (L.relIndex H) p) (σ₁ σ₂ : H →* E)
    (h₁ : ∀ h, π (σ₁ h) = h) (h₂ : ∀ h, π (σ₂ h) = h) : σ₁ = σ₂ := by
  have h := hom_eq_one_of_perfect_core hLH hLn hL hcop hC hp (sectionDiff π hC σ₁ σ₂ h₁ h₂)
  refine MonoidHom.ext fun x => ?_
  have := congrArg (fun f : H →* π.ker => ((f x : π.ker) : E)) h
  simp only [sectionDiff_apply, MonoidHom.one_apply, Subgroup.coe_one] at this
  exact mul_left_cancel (a := (σ₁ x)⁻¹) (by rw [inv_mul_cancel]; exact this.symm ▸ rfl)

end Uniqueness

section Existence

variable {G E : Type} [Group G] [Group E] [Finite E] (π : E →* G)

theorem exists_perfect_lift {p : ℕ} (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hp : IsPGroup p π.ker) {L : Subgroup G} (hL : Group.IsPerfect L) (hKT : KernelTrivialAt L p) :
    ∃ D : Subgroup E, D ≤ L.comap π ∧ (∀ n ∈ L.comap π, ∃ d ∈ D, ∃ z ∈ π.ker, n = d * z) ∧
      D ⊓ π.ker = ⊥ := by
  set N := L.comap π with hN
  set D := ⁅N, N⁆ with hD
  have hDN : D ≤ N := by
    rw [hD, Subgroup.commutator_le]
    exact fun g₁ h₁ g₂ h₂ => N.mul_mem (N.mul_mem (N.mul_mem h₁ h₂) (N.inv_mem h₁)) (N.inv_mem h₂)
  have hNmap : N.map π = L := Subgroup.map_comap_eq_self_of_surjective hπ L
  have hLL : ⁅L, L⁆ = L := by
    have h1 := Subgroup.map_subtype_commutator L
    rw [Group.IsPerfect.commutator_eq_top (G := L), Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1.symm
  have hDmap : D.map π = L := by
    rw [hD, Subgroup.map_commutator, hNmap, hLL]
  have hND : ∀ n ∈ N, ∃ d ∈ D, ∃ z ∈ π.ker, n = d * z := by
    intro n hn
    have : π n ∈ D.map π := by rw [hDmap]; exact hn
    obtain ⟨d, hd, hdn⟩ := this
    refine ⟨d, hd, d⁻¹ * n, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdn, inv_mul_cancel]
  have hDD : D ≤ ⁅D, D⁆ := by
    rw [hD, Subgroup.commutator_le]
    intro n₁ h₁ n₂ h₂
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hND n₁ h₁
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hND n₂ h₂
    rw [CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hC hz₁) (hC hz₂)]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂
  have hDperf : Group.IsPerfect D := by
    rw [Group.isPerfect_def]
    have h1 := Subgroup.map_subtype_commutator D
    have h2 : ⁅D, D⁆ = D := le_antisymm
      (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
        D.mul_mem (D.mul_mem (D.mul_mem h₁ h₂) (D.inv_mem h₁)) (D.inv_mem h₂)) hDD
    rw [h2] at h1
    refine Subgroup.map_injective D.subtype_injective ?_
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  let πD : D →* L := (π.comp D.subtype).codRestrict L fun d => hDN d.2
  have hπD : Function.Surjective πD := by
    intro l
    have : (l : G) ∈ D.map π := by rw [hDmap]; exact l.2
    obtain ⟨d, hd, hdl⟩ := this
    exact ⟨⟨d, hd⟩, Subtype.ext hdl⟩
  have hker : πD.ker ≤ Subgroup.center D := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext (Subgroup.mem_center_iff.1 (hC ?_) (g : E))
    have : πD d = 1 := hd
    have h3 : π (d : E) = 1 := congrArg Subtype.val this
    exact h3
  have hpD : IsPGroup p πD.ker := by
    let f : πD.ker →* π.ker :=
      { toFun := fun x => ⟨((x : D) : E), by
          have : πD x = 1 := x.2
          exact congrArg Subtype.val this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hp.of_injective f (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : π.ker => (x : E)) h)))
  have hbot : πD.ker = ⊥ := hKT D πD hπD hker hpD
  refine ⟨D, hDN, hND, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxk⟩
  have : (⟨x, hxD⟩ : D) ∈ πD.ker := Subtype.ext hxk
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem exists_section_top {p : ℕ} [Fact p.Prime] (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hp : IsPGroup p π.ker) {L : Subgroup G} [L.Normal] (hL : Group.IsPerfect L)
    (hcop : Nat.Coprime L.index p) (hKT : KernelTrivialAt L p) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  obtain ⟨D, hDN, hND, hDker⟩ := exists_perfect_lift π hπ hC hp hL hKT
  have hVc : IsMulCommutative π.ker :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hC b.2) a)⟩⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcop' : Nat.Coprime (L.comap π).index (Nat.card π.ker) := by
    rw [Subgroup.index_comap_of_surjective L hπ, hk]
    exact Nat.Coprime.pow_right k hcop
  have hsup : π.ker ⊔ D = L.comap π := by
    refine le_antisymm (sup_le (fun z hz => ?_) hDN) (fun n hn => ?_)
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact L.one_mem
    · obtain ⟨d, hd, z, hz, rfl⟩ := hND n hn
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hd) (Subgroup.mem_sup_left hz)
  obtain ⟨D', -, hD'inf, hD'sup⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting π.ker (L.comap π) D hcop'
      (by rw [inf_comm]; exact hDker) hsup
  have hinj : Function.Injective (π.comp D'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : E) ∈ π.ker := hx
    have : (x : E) ∈ π.ker ⊓ D' := ⟨h1, x.2⟩
    rw [hD'inf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hsurj : Function.Surjective (π.comp D'.subtype) := by
    intro g
    obtain ⟨e, rfl⟩ := hπ g
    have : e ∈ π.ker ⊔ D' := hD'sup ▸ Subgroup.mem_top e
    obtain ⟨v, hv, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
    refine ⟨⟨d, hd⟩, ?_⟩
    simp [MonoidHom.mem_ker.1 hv]
  let e := MulEquiv.ofBijective (π.comp D'.subtype) ⟨hinj, hsurj⟩
  refine ⟨D'.subtype.comp e.symm.toMonoidHom, fun g => ?_⟩
  exact e.apply_symm_apply g

theorem exists_section_of_cell {p : ℕ} [Fact p.Prime] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) {H : Subgroup G}
    (hH : PerfectCoreCell p H) : ∃ σ : H →* E, ∀ h, π (σ h) = h := by
  obtain ⟨L, hLH, hLn, hL, hcop, hKT⟩ := hH
  let πH : H.comap π →* H := π.subgroupComap H
  have hπH : Function.Surjective πH := π.subgroupComap_surjective H hπ
  have hker : πH.ker ≤ Subgroup.center (H.comap π) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext (Subgroup.mem_center_iff.1 (hC ?_) (g : E))
    have : πH x = 1 := hx
    exact congrArg Subtype.val this
  have hpH : IsPGroup p πH.ker := by
    let f : πH.ker →* π.ker :=
      { toFun := fun x => ⟨((x : H.comap π) : E), by
          have : πH x = 1 := x.2
          exact congrArg Subtype.val this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hp.of_injective f (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : π.ker => (x : E)) h)))
  have : (L.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn g g.2 n hn⟩
  let eL : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have : Group.IsPerfect L := hL
  have hLperf : Group.IsPerfect (L.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hKT' : KernelTrivialAt (L.subgroupOf H) p := (kernelTrivialAt_iff_of_mulEquiv eL p).2 hKT
  obtain ⟨σ, hσ⟩ := exists_section_top πH hπH hker hpH hLperf hcop hKT'
  exact ⟨(H.comap π).subtype.comp σ, fun h => by
    have := congrArg Subtype.val (hσ h)
    exact this⟩

end Existence

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
