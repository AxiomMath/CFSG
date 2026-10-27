module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.CanonicalSection

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open scoped commutatorElement

section Agree

variable {G E : Type} [Group G] [Group E] (π : E →* G)

theorem section_agree_of_pow_mem {p m : ℕ} (hcop : Nat.Coprime m p)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) {I N : Subgroup G} (hNI : N ≤ I)
    (hpow : ∀ g ∈ I, g ^ m ∈ N) (σ₁ σ₂ : I →* E) (h₁ : ∀ h, π (σ₁ h) = h)
    (h₂ : ∀ h, π (σ₂ h) = h) (hagree : ∀ n (hn : n ∈ N), σ₁ ⟨n, hNI hn⟩ = σ₂ ⟨n, hNI hn⟩) :
    σ₁ = σ₂ := by
  set δ := sectionDiff π hC σ₁ σ₂ h₁ h₂ with hδ
  refine MonoidHom.ext fun g => ?_
  have hδ1 : δ (g ^ m) = 1 := by
    have hm : ((g ^ m : I) : G) ∈ N := by
      have := hpow g g.2
      simpa using this
    have := hagree _ hm
    apply Subtype.ext
    simp only [hδ, sectionDiff, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one]
    have e : (⟨((g ^ m : I) : G), hNI hm⟩ : I) = g ^ m := Subtype.ext rfl
    rw [e] at this
    rw [this, inv_mul_cancel]
  rw [map_pow] at hδ1
  obtain ⟨k, hk⟩ := hp (δ g)
  have hord1 : orderOf (δ g) ∣ m := orderOf_dvd_of_pow_eq_one hδ1
  have hord2 : orderOf (δ g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop' : Nat.Coprime m (p ^ k) := Nat.Coprime.pow_right k hcop
  have h1 : orderOf (δ g) = 1 := Nat.eq_one_of_dvd_coprimes hcop' hord1 hord2
  rw [orderOf_eq_one_iff] at h1
  have := congrArg (fun x : π.ker => (x : E)) h1
  simp only [hδ, sectionDiff, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  exact mul_left_cancel (a := (σ₁ g)⁻¹) (by rw [inv_mul_cancel]; exact this.symm)

end Agree

section Extend

variable {G E : Type} [Group G] [Group E] [Finite E] (π : E →* G)

omit [Finite E] in
theorem exists_section_of_compl (hπ : Function.Surjective π) {D : Subgroup E} (h1 : π.ker ⊓ D = ⊥) (h2 : π.ker ⊔ D = ⊤) :
    ∃ σ : G →* E, (∀ g, π (σ g) = g) ∧ ∀ g, σ g ∈ D := by
  have hinj : Function.Injective (π.comp D.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1' : (x : E) ∈ π.ker := hx
    have : (x : E) ∈ π.ker ⊓ D := ⟨h1', x.2⟩
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hsurj : Function.Surjective (π.comp D.subtype) := by
    intro g
    obtain ⟨e, rfl⟩ := hπ g
    have : e ∈ π.ker ⊔ D := h2 ▸ Subgroup.mem_top e
    obtain ⟨v, hv, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
    refine ⟨⟨d, hd⟩, ?_⟩
    simp [MonoidHom.mem_ker.1 hv]
  let e := MulEquiv.ofBijective (π.comp D.subtype) ⟨hinj, hsurj⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, fun g => e.apply_symm_apply g, fun g => ?_⟩
  exact (e.symm g).2

theorem exists_section_extend_top {p : ℕ} [Fact p.Prime] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) {K : Subgroup G} [K.Normal]
    (hcop : Nat.Coprime K.index p) (σK : K →* E) (hσK : ∀ k, π (σK k) = k)
    (hKu : ∀ τ : K →* E, (∀ k, π (τ k) = k) → τ = σK) :
    ∃ σ : G →* E, (∀ g, π (σ g) = g) ∧ ∀ k : K, σ k = σK k := by
  have hVc : IsMulCommutative π.ker :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hC b.2) a)⟩⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcop' : Nat.Coprime (K.comap π).index (Nat.card π.ker) := by
    rw [Subgroup.index_comap_of_surjective K hπ, hk]
    exact Nat.Coprime.pow_right k hcop
  have hsup : π.ker ⊔ σK.range = K.comap π := by
    refine le_antisymm (sup_le (fun z hz => ?_) ?_) (fun n hn => ?_)
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact K.one_mem
    · rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_comap, hσK]; exact k.2
    · have hn' : π n ∈ K := hn
      have h1 : n * (σK ⟨π n, hn'⟩)⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσK, mul_inv_cancel]
      have h2 : σK ⟨π n, hn'⟩ ∈ σK.range := ⟨_, rfl⟩
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
      simpa using this
  have hinf : π.ker ⊓ σK.range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hz, ⟨k, rfl⟩⟩
    have h1 : π (σK k) = 1 := hz
    rw [hσK] at h1
    have : (k : K) = 1 := Subtype.ext h1
    rw [Subgroup.mem_bot, this, map_one]
  obtain ⟨D', -, hD'inf, hD'sup⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting π.ker (K.comap π)
      σK.range hcop' hinf hsup
  obtain ⟨σ, hσ, -⟩ := exists_section_of_compl π hπ hD'inf hD'sup
  refine ⟨σ, hσ, fun k => ?_⟩
  have := hKu (σ.comp K.subtype) (fun k => hσ k)
  exact congrArg (fun f : K →* E => f k) this

theorem exists_section_extend {p : ℕ} [Fact p.Prime] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) {H K : Subgroup G} (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hcop : Nat.Coprime (K.relIndex H) p)
    (σK : K →* E) (hσK : ∀ k, π (σK k) = k)
    (hKu : ∀ τ : K →* E, (∀ k, π (τ k) = k) → τ = σK) :
    ∃ σ : H →* E, (∀ h, π (σ h) = h) ∧ ∀ k : K, σ (Subgroup.inclusion hKH k) = σK k := by
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
    exact hp.of_injective f
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : π.ker => (x : E)) h)))
  have hnormal : (K.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKn g g.2 n hn⟩
  let eK : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let σ' : K.subgroupOf H →* H.comap π :=
    { toFun := fun x => ⟨σK (eK x), by
        show π (σK (eK x)) ∈ H
        rw [hσK]; exact hKH (eK x).2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hσ' : ∀ x, πH (σ' x) = (x : H) := fun x => by
    apply Subtype.ext
    show π (σK (eK x)) = (x : G)
    rw [hσK]; rfl
  have hu : ∀ τ : K.subgroupOf H →* H.comap π, (∀ x, πH (τ x) = (x : H)) → τ = σ' := by
    intro τ hτ
    have := hKu ((H.comap π).subtype.comp (τ.comp eK.symm.toMonoidHom)) (fun k => by
      have h3 := congrArg (fun x : H => (x : G)) (hτ (eK.symm k))
      exact h3)
    refine MonoidHom.ext fun x => ?_
    apply Subtype.ext
    have h2 := congrArg (fun f : K →* E => f (eK x)) this
    simpa [σ'] using h2
  obtain ⟨σ, hσ, hres⟩ := exists_section_extend_top (G := H) πH hπH hker hpH
    (K := K.subgroupOf H) hcop σ' hσ' hu
  refine ⟨(H.comap π).subtype.comp σ, fun h => ?_, fun k => ?_⟩
  · have := congrArg Subtype.val (hσ h)
    exact this
  · have h4 := hres (eK.symm k)
    have e : Subgroup.inclusion hKH k = ((eK.symm k : K.subgroupOf H) : H) := rfl
    show (((σ (Subgroup.inclusion hKH k) : H.comap π) : E)) = σK k
    rw [e, h4]
    show σK (eK (eK.symm k)) = σK k
    rw [MulEquiv.apply_symm_apply]

end Extend

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
