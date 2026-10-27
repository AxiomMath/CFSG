module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MStruct2
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem m42_card_pair2_le {e f : G} (he : orderOf e = 2) (hf : orderOf f = 2) (hc : Commute e f) :
    Nat.card (Subgroup.closure ({e, f} : Set G)) ≤ 4 := by
  let g : Fin 2 × Fin 2 → G := fun p => e ^ (p.1 : ℕ) * f ^ (p.2 : ℕ)
  have hred : ∀ (x : G) (n : ℕ), orderOf x = n → 0 < n → ∀ i : ℤ,
      ∃ k : Fin n, x ^ i = x ^ (k : ℕ) := by
    intro x n hx hn i
    have h := zpow_mod_orderOf x i
    rw [hx] at h
    refine ⟨⟨(i % n).toNat, ?_⟩, ?_⟩
    · have := Int.emod_lt_of_pos i (show (0 : ℤ) < n by exact_mod_cast hn)
      omega
    · rw [← h, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))).symm
  have hsub : ((Subgroup.closure ({e, f} : Set G) : Subgroup G) : Set G) ⊆ Set.range g := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := m42_closure_pair_zpow hc hx
    obtain ⟨a, ha⟩ := hred e 2 he (by norm_num) i
    obtain ⟨b, hb⟩ := hred f 2 hf (by norm_num) j
    exact ⟨(a, b), by simp [g, ha, hb]⟩
  have h1 : ((Subgroup.closure ({e, f} : Set G) : Subgroup G) : Set G).ncard ≤
      (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.finite_range g)
  have h2 : (Set.range g).ncard ≤ 4 := by
    have := Set.ncard_image_le (f := g) (Set.finite_univ (α := Fin 2 × Fin 2))
    rw [← Set.image_univ]
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this
  rw [← Nat.card_coe_set_eq] at h1
  simpa using h1.trans h2

theorem m42_card_pair2 {e f : G} (he : orderOf e = 2) (hf : orderOf f = 2) (hc : Commute e f)
    (hint : Subgroup.zpowers e ⊓ Subgroup.zpowers f = ⊥) :
    Nat.card (Subgroup.closure ({e, f} : Set G)) = 4 := by
  let g : Fin 2 × Fin 2 → G := fun p => e ^ (p.1 : ℕ) * f ^ (p.2 : ℕ)
  have hup := m42_card_pair2_le he hf hc
  have hlow : 4 ≤ Nat.card (Subgroup.closure ({e, f} : Set G)) := by
    let ι : Fin 2 × Fin 2 → ↥(Subgroup.closure ({e, f} : Set G)) := fun p =>
      ⟨g p, Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
    have hinj : Function.Injective ι := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h0 : e ^ (a : ℕ) * f ^ (b : ℕ) = e ^ (c : ℕ) * f ^ (d : ℕ) :=
        congrArg Subtype.val h
      have h1 : e ^ ((a : ℤ) - c) = f ^ ((d : ℤ) - b) := by
        have hc1 : f ^ (b : ℤ) * f ^ (-(d : ℤ)) = e ^ (-(a : ℤ)) * e ^ (c : ℤ) := by
          have : e ^ (a : ℤ) * f ^ (b : ℤ) = e ^ (c : ℤ) * f ^ (d : ℤ) := by
            simpa [zpow_natCast] using h0
          calc f ^ (b : ℤ) * f ^ (-(d : ℤ))
              = e ^ (-(a : ℤ)) * (e ^ (a : ℤ) * f ^ (b : ℤ)) * f ^ (-(d : ℤ)) := by group
            _ = e ^ (-(a : ℤ)) * (e ^ (c : ℤ) * f ^ (d : ℤ)) * f ^ (-(d : ℤ)) := by rw [this]
            _ = e ^ (-(a : ℤ)) * e ^ (c : ℤ) := by group
        have h2 : e ^ ((a : ℤ) - c) = (e ^ (-(a : ℤ)) * e ^ (c : ℤ))⁻¹ := by group
        rw [h2, ← hc1]
        group
      have hm1 : e ^ ((a : ℤ) - c) ∈ Subgroup.zpowers e ⊓ Subgroup.zpowers f :=
        ⟨⟨_, rfl⟩, ⟨_, h1.symm⟩⟩
      rw [hint, Subgroup.mem_bot] at hm1
      have hm2 : f ^ ((d : ℤ) - b) = 1 := by rw [← h1]; exact hm1
      have h3 := (orderOf_dvd_iff_zpow_eq_one.mpr hm1)
      have h4 := (orderOf_dvd_iff_zpow_eq_one.mpr hm2)
      rw [he] at h3
      rw [hf] at h4
      have h3' : (2 : ℤ) ∣ (a : ℤ) - c := by exact_mod_cast h3
      have h4' : (2 : ℤ) ∣ (d : ℤ) - b := by exact_mod_cast h4
      have ha := a.2
      have hb := b.2
      have hc2 := c.2
      have hd := d.2
      have e1 : (a : ℕ) = c := by omega
      have e2 : (b : ℕ) = d := by omega
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have := Nat.card_le_card_of_injective ι hinj
    simpa using this
  omega

theorem m42_Op_isPGroup (p : ℕ) [Fact p.Prime] (M : Subgroup G) : IsPGroup p (Op p M) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥M)).map M.subtype

theorem m42_Op_le (p : ℕ) (M : Subgroup G) : Op p M ≤ M := Subgroup.map_subtype_le _

theorem m42_Op_conj_mem {p : ℕ} {M : Subgroup G} {g z : G} (hg : g ∈ M) (hz : z ∈ Op p M) :
    g * z * g⁻¹ ∈ Op p M := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pCore_normal (p := p) (G := ↥M)).conj_mem z' hz' ⟨g, hg⟩

theorem m42_le_Op {p : ℕ} {M P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup p P)
    (hn : ∀ m ∈ M, ∀ x ∈ P, m * x * m⁻¹ ∈ P) : P ≤ Op p M := by
  let P' : Subgroup ↥M := P.subgroupOf M
  haveI : P'.Normal := ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn g.1 g.2 n hn'⟩
  have hp : IsPGroup p P' := hP.comap_subtype
  have hle : P' ≤ CFSG.pCore p ↥M := le_sSup ⟨inferInstance, hp⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hPM hx⟩, hle hx, rfl⟩

theorem m42_char2 (hc : IsCharacteristicPType G 2) {U : Subgroup G} (hU : IsPGroup 2 U)
    (hne : U ≠ ⊥) : ∀ g ∈ Nor U, (∀ v ∈ Op 2 (Nor U), v * g = g * v) → g ∈ Op 2 (Nor U) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsPLocal 2 (Nor U) := ⟨U, hne, hU, rfl⟩
  have := hc _ hloc
  intro g hg hcomm
  have hmem : (⟨g, hg⟩ : ↥(Nor U)) ∈
      Subgroup.centralizer (CFSG.pCore 2 ↥(Nor U) : Set ↥(Nor U)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (hcomm z.1 (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩))
  obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp (Subgroup.mem_map.mpr ⟨_, this hmem, rfl⟩ :
    g ∈ (CFSG.pCore 2 ↥(Nor U)).map (Nor U).subtype)
  exact Subgroup.mem_map.mpr ⟨z, hz, hzg⟩

theorem m42_conj_sylow (p : ℕ) [Fact p.Prime] {M P Q : Subgroup G} (hP : P ≤ M) (hQ : Q ≤ M)
    (hcP : Nat.card P = p ^ (Nat.card M).factorization p)
    (hcQ : Nat.card Q = p ^ (Nat.card M).factorization p) :
    ∃ g ∈ M, P.map (MulAut.conj g).toMonoidHom = Q := by
  let P' : Subgroup ↥M := P.subgroupOf M
  let Q' : Subgroup ↥M := Q.subgroupOf M
  have hP' : Nat.card P' = p ^ (Nat.card M).factorization p := by
    rw [← hcP]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have hQ' : Nat.card Q' = p ^ (Nat.card M).factorization p := by
    rw [← hcQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) (Sylow.ofCard P' hP') (Sylow.ofCard Q' hQ')
  have hQeq : ((g • Sylow.ofCard P' hP' : Sylow p ↥M) : Subgroup ↥M) = Q' :=
    congrArg (fun S : Sylow p ↥M => (S : Subgroup ↥M)) hg
  refine ⟨g.1, g.2, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have : (g * (⟨x, hP hx⟩ : ↥M) * g⁻¹) ∈ Q' := by
      rw [← hQeq, Sylow.coe_subgroup_smul]
      exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp this
  · rw [Subgroup.card_map_of_injective (MulAut.conj g.1).injective, hcP, hcQ]

theorem m42_comm_le {Z Y : Subgroup G} {β : G} (hβ : β ∈ Z) (hc : ∀ z ∈ Z, β * z = z * β)
    (hYZ : Y ≤ Z) (hdec : ∀ z ∈ Z, ∃ i : ℤ, ∃ y ∈ Y, z = β ^ i * y) : ⁅Z, Z⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨i, y, hy, rfl⟩ := hdec g₁ hg₁
  obtain ⟨j, y', hy', rfl⟩ := hdec g₂ hg₂
  have hcen : ∀ (k : ℤ) (w : G), w ∈ Z → β ^ k * w = w * β ^ k := fun k w hw =>
    ((show Commute β w from hc w hw).zpow_left k).eq
  have hZ : ∀ k : ℤ, β ^ k ∈ Z := fun k => Subgroup.zpow_mem _ hβ k
  rw [commutatorElement_def]
  have hw : y * (β ^ j) * y⁻¹ = β ^ j := by
    have := hcen j y (hYZ hy)
    rw [← this]; group
  have e1 : β ^ i * y * (β ^ j * y') * (β ^ i * y)⁻¹ * (β ^ j * y')⁻¹ =
      β ^ i * (y * β ^ j * y' * y⁻¹) * (β ^ i)⁻¹ * (y'⁻¹ * (β ^ j)⁻¹) := by group
  have hmem : y * β ^ j * y' * y⁻¹ ∈ Z :=
    Z.mul_mem (Z.mul_mem (Z.mul_mem (hYZ hy) (hZ j)) (hYZ hy')) (Z.inv_mem (hYZ hy))
  have e2 : β ^ i * (y * β ^ j * y' * y⁻¹) * (β ^ i)⁻¹ = y * β ^ j * y' * y⁻¹ := by
    rw [hcen i _ hmem]; group
  rw [e1, e2]
  have e3 : y * β ^ j * y' * y⁻¹ * (y'⁻¹ * (β ^ j)⁻¹) = (β ^ j) * (y * y' * y⁻¹ * y'⁻¹) *
      (β ^ j)⁻¹ := by
    have h4 : y * β ^ j = β ^ j * y := (hcen j y (hYZ hy)).symm
    calc y * β ^ j * y' * y⁻¹ * (y'⁻¹ * (β ^ j)⁻¹)
        = (y * β ^ j) * y' * y⁻¹ * y'⁻¹ * (β ^ j)⁻¹ := by group
      _ = (β ^ j * y) * y' * y⁻¹ * y'⁻¹ * (β ^ j)⁻¹ := by rw [h4]
      _ = _ := by group
  rw [e3]
  have hmem2 : y * y' * y⁻¹ * y'⁻¹ ∈ Z :=
    Z.mul_mem (Z.mul_mem (Z.mul_mem (hYZ hy) (hYZ hy')) (Z.inv_mem (hYZ hy)))
      (Z.inv_mem (hYZ hy'))
  rw [hcen j _ hmem2]
  have : y * y' * y⁻¹ * y'⁻¹ * β ^ j * (β ^ j)⁻¹ = y * y' * y⁻¹ * y'⁻¹ := by group
  rw [this]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy') (Y.inv_mem hy)) (Y.inv_mem hy')

theorem m42_Lay_le_Lay {Z Y : Subgroup G} (hYZ : Y ≤ Z) (h : Lay Z ≤ Y) : Lay Z ≤ Lay Y := by
  have hcomp : ∀ C : Subgroup ↥Z, CFSG.IsComponent C → C.map Z.subtype ≤ Lay Y := by
    intro C hC
    refine m42_comp_le_Lay hYZ hC ?_
    exact le_trans (Subgroup.map_mono (CFSG.LocalCores.component_le_layer hC)) h
  have : CFSG.layer ↥Z ≤ (Lay Y).comap Z.subtype :=
    sSup_le fun C hC => fun x hx => hcomp C hC ⟨x, hx, rfl⟩
  exact (Subgroup.map_mono this).trans (Subgroup.map_comap_le _ _)

theorem m42_zpowers_two {x : G} (hx : x * x = 1) : ∀ z ∈ Subgroup.zpowers x, z = 1 ∨ z = x := by
  intro z hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have hmod : x ^ (i % (2 : ℤ)) = x ^ i := by
    have := zpow_mod_orderOf x i
    have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · have : x = 1 := orderOf_eq_one_iff.mp h1
      subst this
      simp
    · rwa [h2] at this
  rw [← hmod]
  have : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases this with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

end CFSG.RankThree.PartTwo.Sec21.FF79
