module

public import CFSG.RankThree.PartTwo.Sec21.FF81S59Ext
public import CFSG.RankThree.PartTwo.Sec21.FF81S59Sec
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec21.FF79

section Prod

variable {G : Type} [Group G] [Finite G] {T₀ T₁ : Subgroup G}

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hcen : A ≤ CenS B) {u : G} (hu : u ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ c ∈ B, u = a * c := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      have : a * x = x * a := (Subgroup.mem_centralizer_iff.mp (hcen ha) x hx).symm
      rw [this, mul_inv_cancel_right]
      exact hx
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hu' : u ∈ (↑(A ⊔ B) : Set G) := hu
  rw [h] at hu'
  obtain ⟨a, ha, c, hc, rfl⟩ := hu'
  exact ⟨a, ha, c, hc, rfl⟩

theorem le_cenS_of_le {A B : Subgroup G} (h : A ≤ CenS B) : B ≤ CenS A := fun b hb =>
  Subgroup.mem_centralizer_iff.mpr fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm

theorem card_Z₁ (hext : IsExtraspecialPGroup 2 ↥T₁) : Nat.card ↥(T₁ ⊓ CenS T₁) = 2 := by
  have := hext.2.2.2
  rw [center_eq] at this
  rw [← this]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem sq_Z₁ (hext : IsExtraspecialPGroup 2 ↥T₁) {z : G} (hz : z ∈ T₁ ⊓ CenS T₁) :
    z ^ 2 = 1 := by
  have hz' : (⟨z, hz.1⟩ : ↥T₁) ∈ Subgroup.center ↥T₁ := mem_center_iff'.mpr hz
  have := ext_center_sq hext hz'
  exact congrArg Subtype.val this

theorem sq_mem_Z₁ (hext : IsExtraspecialPGroup 2 ↥T₁) {c : G} (hc : c ∈ T₁) :
    c ^ 2 ∈ T₁ ⊓ CenS T₁ := by
  have := mem_center_iff'.mp (ext_sq_mem_center hext ⟨c, hc⟩)
  simpa using this

theorem comm_mem_Z₁ (hext : IsExtraspecialPGroup 2 ↥T₁) {c c' : G} (hc : c ∈ T₁)
    (hc' : c' ∈ T₁) : c * c' * c⁻¹ * c'⁻¹ ∈ T₁ ⊓ CenS T₁ := by
  have := mem_center_iff'.mp (ext_commutator_mem_center hext.2.1 (⟨c, hc⟩ : ↥T₁) ⟨c', hc'⟩)
  simpa [commutatorElement_def] using this

theorem comm_elemAb {p k : ℕ} {B : Subgroup G} (hB : IsElemAb p k B) :
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hB.1.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)

theorem pow_elemAb {p k : ℕ} {B : Subgroup G} (hB : IsElemAb p k B) :
    ∀ a ∈ B, a ^ p = 1 := by
  haveI := hB.1
  exact fun a ha => elemPow_eq_one_of_isElementaryAbelian (A := B) a ha

end Prod

section Facts

variable {G : Type} [Group G] [Finite G] {T₀ T₁ : Subgroup G}
variable (hT0 : IsElemAb 2 6 T₀) (hT1 : IsExtraspecialPlus 4 T₁) (hinf : T₀ ⊓ T₁ = ⊥)
  (hcen : T₀ ≤ CenS T₁)
include hT0 hT1 hinf hcen

theorem comm_T₀ : ∀ a ∈ T₀, ∀ a' ∈ T₀, a * a' = a' * a := comm_elemAb hT0

theorem sq_T₀ : ∀ a ∈ T₀, a ^ 2 = 1 := pow_elemAb hT0

theorem comm_T₁T₀ : ∀ c ∈ T₁, ∀ a ∈ T₀, c * a = a * c := fun c hc a ha =>
  Subgroup.mem_centralizer_iff.mp (hcen ha) c hc

theorem card_sup : Nat.card ↥(T₀ ⊔ T₁) = 2 ^ 15 := by
  have hle : T₀ ≤ Subgroup.normalizer (T₁ : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      have : a * x = x * a := (Subgroup.mem_centralizer_iff.mp (hcen ha) x hx).symm
      rw [this, mul_inv_cancel_right]
      exact hx
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hle
  rw [hinf, Subgroup.card_bot, mul_one, hT0.2, hT1.2.1] at h
  rw [h]
  norm_num

theorem center_sup : (T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁) = T₀ ⊔ (T₁ ⊓ CenS T₁) := by
  have hZ1 : T₁ ⊓ CenS T₁ ≤ T₁ := inf_le_left
  have hcen' : T₀ ≤ CenS (T₁ ⊓ CenS T₁) := fun a ha =>
    Subgroup.centralizer_le hZ1 (hcen ha)
  ext x
  constructor
  · rintro ⟨hxT, hxc⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcen hxT
    have hcZ : c ∈ T₁ ⊓ CenS T₁ := by
      refine ⟨hc, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxc d
        (Subgroup.mem_sup_right hd)
      have h2 : d * a = a * d := comm_T₁T₀ hT0 hT1 hinf hcen d hd a ha
      calc d * c = a⁻¹ * (a * d * c) := by group
        _ = a⁻¹ * (d * a * c) := by rw [h2]
        _ = a⁻¹ * (d * (a * c)) := by group
        _ = a⁻¹ * ((a * c) * d) := by rw [h1]
        _ = c * d := by group
    exact Subgroup.mul_mem_sup ha hcZ
  · intro hx
    obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup hcen' hx
    have hxT : a * z ∈ T₀ ⊔ T₁ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hz.1)
    refine ⟨hxT, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    obtain ⟨a', ha', c', hc', rfl⟩ := exists_mul_of_mem_sup hcen ht
    have h1 : c' * z = z * c' := (Subgroup.mem_centralizer_iff.mp hz.2 c' hc')
    have h2 : c' * a = a * c' := comm_T₁T₀ hT0 hT1 hinf hcen c' hc' a ha
    have h3 : z * a' = a' * z := comm_T₁T₀ hT0 hT1 hinf hcen z hz.1 a' ha'
    have h4 : a' * a = a * a' := comm_T₀ hT0 hT1 hinf hcen a' ha' a ha
    calc a' * c' * (a * z) = a' * (c' * a) * z := by group
      _ = a' * (a * c') * z := by rw [h2]
      _ = (a' * a) * (c' * z) := by group
      _ = (a' * a) * (z * c') := by rw [h1]
      _ = (a * a') * (z * c') := by rw [h4]
      _ = a * (a' * z) * c' := by group
      _ = a * (z * a') * c' := by rw [h3]
      _ = a * z * (a' * c') := by group

theorem sq_prod {a c : G} (ha : a ∈ T₀) (hc : c ∈ T₁) : (a * c) ^ 2 = c ^ 2 := by
  have h1 : c * a = a * c := comm_T₁T₀ hT0 hT1 hinf hcen c hc a ha
  calc (a * c) ^ 2 = a * (c * a) * c := by simp only [pow_two]; group
    _ = a * (a * c) * c := by rw [h1]
    _ = a ^ 2 * c ^ 2 := by simp only [pow_two]; group
    _ = c ^ 2 := by rw [sq_T₀ hT0 hT1 hinf hcen a ha, one_mul]

theorem card_center : Nat.card ↥((T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁)) = 2 ^ 7 := by
  rw [center_sup hT0 hT1 hinf hcen]
  have hZ1 : Nat.card ↥(T₁ ⊓ CenS T₁) = 2 := card_Z₁ hT1.1
  have hZ1le : T₁ ⊓ CenS T₁ ≤ T₁ := inf_le_left
  have hle : T₀ ≤ Subgroup.normalizer ((T₁ ⊓ CenS T₁ : Subgroup G) : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      have : a * x = x * a :=
        (Subgroup.mem_centralizer_iff.mp (hcen ha) x hx.1).symm
      rw [this, mul_inv_cancel_right]
      exact hx
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hle
  have hinf' : T₀ ⊓ (T₁ ⊓ CenS T₁) = ⊥ :=
    le_antisymm (le_trans (inf_le_inf_left T₀ hZ1le) (le_of_eq hinf)) bot_le
  rw [hinf', Subgroup.card_bot, mul_one, hT0.2, hZ1] at h
  rw [h]
  norm_num

theorem sq_center : ∀ z ∈ (T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁), z ^ 2 = 1 := by
  intro z hz
  rw [center_sup hT0 hT1 hinf hcen] at hz
  have hcen' : T₀ ≤ CenS (T₁ ⊓ CenS T₁) := fun a ha =>
    Subgroup.centralizer_le (inf_le_left : T₁ ⊓ CenS T₁ ≤ T₁) (hcen ha)
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup hcen' hz
  have h1 : w * a = a * w := comm_T₁T₀ hT0 hT1 hinf hcen w hw.1 a ha
  calc (a * w) ^ 2 = a * (w * a) * w := by simp only [pow_two]; group
    _ = a * (a * w) * w := by rw [h1]
    _ = a ^ 2 * w ^ 2 := by simp only [pow_two]; group
    _ = 1 := by rw [sq_T₀ hT0 hT1 hinf hcen a ha, sq_Z₁ hT1.1 hw, one_mul]

theorem Z₁_le_center : T₁ ⊓ CenS T₁ ≤ (T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁) := by
  rw [center_sup hT0 hT1 hinf hcen]
  exact le_sup_right

theorem sq_mem_center : ∀ u ∈ T₀ ⊔ T₁, u ^ 2 ∈ (T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁) := by
  intro u hu
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcen hu
  rw [sq_prod hT0 hT1 hinf hcen ha hc]
  exact Z₁_le_center hT0 hT1 hinf hcen (sq_mem_Z₁ hT1.1 hc)

theorem comm_mem_center : ∀ u ∈ T₀ ⊔ T₁, ∀ v ∈ T₀ ⊔ T₁,
    u * v * u⁻¹ * v⁻¹ ∈ (T₀ ⊔ T₁) ⊓ CenS (T₀ ⊔ T₁) := by
  intro u hu v hv
  have hZ : ∀ a ∈ T₀, ∀ t ∈ T₀ ⊔ T₁, a * t = t * a := by
    intro a ha t ht
    obtain ⟨a', ha', c', hc', rfl⟩ := exists_mul_of_mem_sup hcen ht
    have h2 : c' * a = a * c' := comm_T₁T₀ hT0 hT1 hinf hcen c' hc' a ha
    calc a * (a' * c') = (a * a') * c' := by group
      _ = (a' * a) * c' := by rw [comm_T₀ hT0 hT1 hinf hcen a ha a' ha']
      _ = a' * (a * c') := by group
      _ = a' * (c' * a) := by rw [h2]
      _ = a' * c' * a := by group
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcen hu
  obtain ⟨a', ha', c', hc', rfl⟩ := exists_mul_of_mem_sup hcen hv
  have hcT : c ∈ T₀ ⊔ T₁ := Subgroup.mem_sup_right hc
  have hc'T : c' ∈ T₀ ⊔ T₁ := Subgroup.mem_sup_right hc'
  have hvT : a' * c' ∈ T₀ ⊔ T₁ := hv
  have e1 : a * c * (a' * c') * (a * c)⁻¹ * (a' * c')⁻¹ =
      (a * (c * (a' * c') * c⁻¹) * a⁻¹) * (a' * c')⁻¹ := by group
  have h1 : a * (c * (a' * c') * c⁻¹) * a⁻¹ = c * (a' * c') * c⁻¹ := by
    rw [hZ a ha _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcT hvT) (Subgroup.inv_mem _ hcT)),
      mul_inv_cancel_right]
  have e2 : c * (a' * c') * c⁻¹ * (a' * c')⁻¹ =
      (c * a' * c⁻¹) * (c * c' * c⁻¹ * c'⁻¹) * a'⁻¹ := by group
  have h2 : c * a' * c⁻¹ = a' := by
    rw [(comm_T₁T₀ hT0 hT1 hinf hcen c hc a' ha'), mul_inv_cancel_right]
  have hk : c * c' * c⁻¹ * c'⁻¹ ∈ T₀ ⊔ T₁ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcT hc'T)
      (Subgroup.inv_mem _ hcT)) (Subgroup.inv_mem _ hc'T)
  have h3 : a' * (c * c' * c⁻¹ * c'⁻¹) * a'⁻¹ = c * c' * c⁻¹ * c'⁻¹ := by
    rw [hZ a' ha' _ hk, mul_inv_cancel_right]
  rw [e1, h1, e2, h2, h3]
  exact Z₁_le_center hT0 hT1 hinf hcen (comm_mem_Z₁ hT1.1 hc hc')


theorem card_sq_T : Nat.card {u : G // u ∈ T₀ ⊔ T₁ ∧ u ^ 2 = 1} = 17408 := by
  have hT1' := hT1
  obtain ⟨hext, hcard1, A, hAle, hA⟩ := hT1'
  have hA2 : ∀ a ∈ A.subgroupOf T₁, a ^ 2 = 1 := fun a ha => Subtype.ext (by
    simpa using pow_elemAb hA (a : G) (Subgroup.mem_subgroupOf.mp ha))
  have hAc : ∀ a ∈ A.subgroupOf T₁, ∀ b ∈ A.subgroupOf T₁, a * b = b * a := fun a ha b hb =>
    Subtype.ext (comm_elemAb hA (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G)
      (Subgroup.mem_subgroupOf.mp hb))
  have hAcard : Nat.card ↥(A.subgroupOf T₁) = 2 ^ 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv).trans hA.2
  have hN1' := card_sq_eq_one_extraspecial hext (by simpa using hcard1) (A.subgroupOf T₁) hA2
    hAc hAcard
  have hN1 : Nat.card {c : G // c ∈ T₁ ∧ c ^ 2 = 1} = 272 := by
    rw [← hN1']
    exact Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, c.2.1⟩, Subtype.ext (by simpa using c.2.2)⟩
        invFun := fun x => ⟨x.1.1, x.1.2, by simpa using congrArg Subtype.val x.2⟩
        left_inv := fun c => rfl
        right_inv := fun x => rfl }
  let f : T₀ × {c : G // c ∈ T₁ ∧ c ^ 2 = 1} → {u : G // u ∈ T₀ ⊔ T₁ ∧ u ^ 2 = 1} := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2.1), by
        rw [sq_prod hT0 hT1 hinf hcen p.1.2 p.2.2.1]
        exact p.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, c, hc, hc2⟩ ⟨a', c', hc', hc2'⟩ h
      have h' : (a : G) * c = a' * c' := congrArg Subtype.val h
      have hmem : (a' : G)⁻¹ * a ∈ T₀ ⊓ T₁ := by
        refine ⟨T₀.mul_mem (T₀.inv_mem a'.2) a.2, ?_⟩
        have : (a' : G)⁻¹ * a = c' * c⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * c) * c⁻¹ := by group
            _ = (a' : G)⁻¹ * (a' * c') * c⁻¹ := by rw [h']
            _ = c' * c⁻¹ := by group
        rw [this]
        exact T₁.mul_mem hc' (T₁.inv_mem hc)
      rw [hinf, Subgroup.mem_bot] at hmem
      have haa : (a : G) = a' := by
        have := congrArg (fun x => (a' : G) * x) hmem
        simpa using this
      have hcc : c = c' := by
        rw [haa] at h'
        exact mul_left_cancel h'
      have haa' : a = a' := Subtype.ext haa
      subst haa'
      subst hcc
      rfl
    · rintro ⟨u, hu, hu2⟩
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcen hu
      refine ⟨(⟨a, ha⟩, ⟨c, hc, ?_⟩), rfl⟩
      rw [← sq_prod hT0 hT1 hinf hcen ha hc]
      exact hu2
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, hN1, hT0.2]
  norm_num

end Facts

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
