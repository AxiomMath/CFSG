module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open

theorem false_of_E9_elt {Q : Type} [Group Q] [Finite Q] {H A : Subgroup Q} {p : Q}
    (hrank : CFSG.Open.pRank 3 H ≤ 2) (hAH : A ≤ H) (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 9) (hpH : p ∈ H) (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) (hpA : p ∉ A)
    (hcomm : ∀ a ∈ A, a * p = p * a) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcord : orderOf p = 3 := orderOf_eq_prime hp3 hp1
  have hCc : Nat.card ↥(Subgroup.zpowers p) = 3 := by rw [Nat.card_zpowers, hcord]
  have hCH : Subgroup.zpowers p ≤ H := Subgroup.zpowers_le.mpr hpH
  have hAC : ∀ c ∈ Subgroup.zpowers p, c ∈ A → c = 1 := by
    intro c hcC hcA
    by_contra hc1
    have hc3 : c ^ 3 = 1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcC
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3, one_zpow]
    have hcord' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have heq : Subgroup.zpowers c = Subgroup.zpowers p :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcC)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hcord, hcord']))
    apply hpA
    have hpz : p ∈ Subgroup.zpowers c := by rw [heq]; exact Subgroup.mem_zpowers p
    exact (Subgroup.zpowers_le.mpr hcA) hpz
  have hcomm' : ∀ (a : ↥A) (c : Q), c ∈ Subgroup.zpowers p → (a : Q) * c = c * (a : Q) := by
    intro a c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute (a : Q) p from hcomm _ a.2) n).eq
  have hmul : ∀ x y : ↥A × ↥(Subgroup.zpowers p),
      ((x * y).1 : Q) * ((x * y).2 : Q) = ((x.1 : Q) * (x.2 : Q)) * ((y.1 : Q) * (y.2 : Q)) := by
    intro x y
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h := hcomm' y.1 (x.2 : Q) x.2.2
    calc (x.1 : Q) * (y.1 : Q) * ((x.2 : Q) * (y.2 : Q))
        = (x.1 : Q) * ((y.1 : Q) * (x.2 : Q)) * (y.2 : Q) := by group
      _ = (x.1 : Q) * ((x.2 : Q) * (y.1 : Q)) * (y.2 : Q) := by rw [h]
      _ = (x.1 : Q) * (x.2 : Q) * ((y.1 : Q) * (y.2 : Q)) := by group
  let φ : (↥A × ↥(Subgroup.zpowers p)) →* Q :=
    MonoidHom.mk' (fun x => (x.1 : Q) * (x.2 : Q)) (fun x y => hmul x y)
  have hφ : ∀ x, φ x = (x.1 : Q) * (x.2 : Q) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ] at hx
    have h2 : (x.2 : Q) = ((x.1 : Q))⁻¹ := eq_inv_of_mul_eq_one_right hx
    have h2A : (x.2 : Q) ∈ A := by rw [h2]; exact A.inv_mem x.1.2
    have h2one : (x.2 : Q) = 1 := hAC _ x.2.2 h2A
    have h1one : (x.1 : Q) = 1 := by
      rw [h2one, mul_one] at hx
      exact hx
    exact Prod.ext (Subtype.ext h1one) (Subtype.ext h2one)
  set R : Subgroup Q := φ.range with hRdef
  have hRc : Nat.card ↥R = 27 := by
    rw [hRdef, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hAc, hCc]
  have hRH : R ≤ H := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    exact H.mul_mem (hAH x.1.2) (hCH x.2.2)
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    have hxy : (x.1 : Q) * (y.1 : Q) = (y.1 : Q) * (x.1 : Q) :=
      congrArg Subtype.val (hA.1.is_comm.comm x.1 y.1)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2.2
    have hcc : (x.2 : Q) * (y.2 : Q) = (y.2 : Q) * (x.2 : Q) := by
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self p m n).eq
    congr 1
    exact Prod.ext (Subtype.ext hxy) (Subtype.ext hcc)
  have hpow : ∀ y ∈ Subgroup.zpowers p, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3, one_zpow]
  have hRexp : ∀ x ∈ R, x ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    have hc : Commute (x.1 : Q) (x.2 : Q) := hcomm' x.1 x.2 x.2.2
    rw [hc.mul_pow, hA.2 _ x.1.2, hpow _ x.2.2, one_mul]
  have hRel : CFSG.Open.IsElemAbelian 3 R :=
    ⟨⟨⟨fun x y => Subtype.ext (hRcomm x.1 x.2 y.1 y.2)⟩⟩, hRexp⟩
  have hk := le_pRank_of_elemAbelian_card (k := 3) hRH hRel (by rw [hRc]; norm_num)
  omega

theorem mem_sup_decomp {Γ : Type} [Group Γ] {J J' : Subgroup Γ}
    (hcomm : ∀ j ∈ J, ∀ j' ∈ J', j * j' = j' * j) {x : Γ} (hx : x ∈ J ⊔ J') :
    ∃ j ∈ J, ∃ j' ∈ J', x = j * j' := by
  let S : Subgroup Γ :=
    { carrier := {y | ∃ j ∈ J, ∃ j' ∈ J', y = j * j'}
      mul_mem' := by
        rintro _ _ ⟨j1, hj1, j1', hj1', rfl⟩ ⟨j2, hj2, j2', hj2', rfl⟩
        refine ⟨j1 * j2, J.mul_mem hj1 hj2, j1' * j2', J'.mul_mem hj1' hj2', ?_⟩
        calc j1 * j1' * (j2 * j2') = j1 * (j1' * j2) * j2' := by group
          _ = j1 * (j2 * j1') * j2' := by rw [← hcomm j2 hj2 j1' hj1']
          _ = j1 * j2 * (j1' * j2') := by group
      one_mem' := ⟨1, J.one_mem, 1, J'.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨j, hj, j', hj', rfl⟩
        refine ⟨j⁻¹, J.inv_mem hj, j'⁻¹, J'.inv_mem hj', ?_⟩
        have hc : Commute j j' := hcomm j hj j' hj'
        rw [mul_inv_rev]
        exact (Commute.inv_inv hc).eq.symm }
  have hle : J ⊔ J' ≤ S := by
    refine sup_le (fun j hj => ⟨j, hj, 1, J'.one_mem, by group⟩)
      (fun j' hj' => ⟨1, J.one_mem, j', hj', by group⟩)
  exact hle hx

end CFSG.Quasithin.H13.Ch4.J4KX

end
