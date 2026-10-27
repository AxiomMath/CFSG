module

public import CFSG.Quasithin.Vol2.Asc94.HeJ10

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

theorem perm5_eq_alternating {H : Subgroup (Equiv.Perm (Fin 5))} (h : Nat.card H = 60) :
    H = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h1 := Subgroup.index_mul_card H
  rw [Nat.card_perm, h] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h5 : (5 : ℕ).factorial = 120 := by decide
  rw [h5] at h1
  omega

theorem exists_perm_index {L K : Subgroup G} (hKL : K ≤ L) {n : ℕ} [NeZero n]
    (hidx : K.relIndex L = n) :
    ∃ φ : ↥L →* Equiv.Perm (Fin n),
      (∀ k : ↥L, φ k = 1 ↔ ∀ l : ↥L, (l : G)⁻¹ * (k : G) * (l : G) ∈ K) ∧
      (∀ k : ↥L, φ k 0 = 0 ↔ (k : G) ∈ K) := by
  set K' : Subgroup ↥L := K.subgroupOf L with hK'
  have hQ : Nat.card (↥L ⧸ K') = n := by rw [← hidx]; rfl
  set e₀ : (↥L ⧸ K') ≃ Fin n := (Finite.equivFin (↥L ⧸ K')).trans (finCongr hQ) with he₀
  set base : ↥L ⧸ K' := ((1 : ↥L) : ↥L ⧸ K') with hbase
  set e : (↥L ⧸ K') ≃ Fin n := e₀.trans (Equiv.swap (e₀ base) 0) with he
  have heb : e base = 0 := by simp [he]
  refine ⟨e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥L (↥L ⧸ K')), ?_, ?_⟩
  · intro k
    have h1 : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥L (↥L ⧸ K'))) k = 1 ↔
        MulAction.toPermHom ↥L (↥L ⧸ K') k = 1 := by
      simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      exact e.permCongrHom.map_eq_one_iff
    rw [h1, ← MonoidHom.mem_ker, ← Subgroup.normalCore_eq_ker]
    constructor
    · intro hk l
      have := hk l⁻¹
      simpa [hK', Subgroup.mem_subgroupOf] using this
    · intro hk b
      have := hk b⁻¹
      simpa [hK', Subgroup.mem_subgroupOf] using this
  · intro k
    have h1 : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥L (↥L ⧸ K'))) k 0 =
        e (k • base) := by
      have hsymm : e.symm 0 = base := e.symm_apply_eq.2 heb.symm
      simp [Equiv.permCongrHom, Equiv.permCongr_apply, hsymm]
    rw [h1, ← heb, e.apply_eq_iff_eq]
    show ((k * 1 : ↥L) : ↥L ⧸ K') = ((1 : ↥L) : ↥L ⧸ K') ↔ _
    rw [QuotientGroup.eq]
    simp [hK', Subgroup.mem_subgroupOf]

theorem exists_perm_five {L K : Subgroup G} (hKL : K ≤ L) (hidx : K.relIndex L = 5) :
    ∃ φ : ↥L →* Equiv.Perm (Fin 5),
      (∀ k : ↥L, φ k = 1 ↔ ∀ l : ↥L, (l : G)⁻¹ * (k : G) * (l : G) ∈ K) ∧
      (∀ k : ↥L, φ k 0 = 0 ↔ (k : G) ∈ K) :=
  exists_perm_index hKL hidx

theorem gl2_inv_ne : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → g⁻¹ ≠ g := by
  decide +kernel

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

theorem Data40.card_Z : Nat.card ↥(A ⊓ A') = 16 := by
  have h : Nat.card ↥(A ⊓ A') = Nat.card M2 :=
    Nat.card_congr (Equiv.ofBijective (fun y => m y.1) ⟨fun y y' hyy => Subtype.ext
      (hD.hT.minj _ y.2 _ y'.2 hyy), fun M => by
        obtain ⟨y, hy, hym⟩ := hD.hT.msurj M
        exact ⟨⟨y, hy⟩, hym⟩⟩)
  rw [h, Nat.card_eq_fintype_card]
  decide +kernel

theorem Data40.card_A : Nat.card ↥A = 64 := by
  let f : ↥A →* Multiplicative V2 :=
    { toFun := fun y => Multiplicative.ofAdd (u y.1)
      map_one' := by
        show Multiplicative.ofAdd (u 1) = 1
        rw [hD.hT.cu.map_one]; rfl
      map_mul' := fun y y' => by
        show Multiplicative.ofAdd (u (y.1 * y'.1)) = _
        rw [hD.hT.cu.mul _ y.2 _ y'.2]; rfl }
  have hker : f.ker = (A ⊓ A').subgroupOf A := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have : u y.1 = 0 := h
      exact ⟨y.2, (hD.hT.cu.zero _ y.2).1 this⟩
    · intro h
      show Multiplicative.ofAdd (u y.1) = 1
      rw [(hD.hT.cu.zero _ y.2).2 h.2]; rfl
  have hrange : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro v
    obtain ⟨y, hy, hyv⟩ := hD.hT.cu.surj (Multiplicative.toAdd v)
    exact ⟨⟨y, hy⟩, by simp [f, hyv]⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥A ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range = 4 := by
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    decide +kernel
  have h4 : Nat.card f.ker = 16 := by
    rw [hker]
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ A' ≤ A)).toEquiv
    rw [this, hD.card_Z]
  rw [h1, h2, h3, h4]

theorem Data40.alt5 (hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G))
    {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)
    {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G))
    (hbm : m b = ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val) :
    b ≠ 1 ∧ b ≠ a ∧
      Nat.card ↥(Lg A a b) = 3840 ∧ Nat.card ↥(Kg N a b) = 768 ∧
      ∃ φ : ↥(Lg A a b) →* Equiv.Perm (Fin 5), φ.ker = A.subgroupOf (Lg A a b) ∧
        φ.range = alternatingGroup (Fin 5) ∧
        ∀ k : ↥(Lg A a b), φ k 0 = 0 ↔ (k : G) ∈ Kg N a b := by
  have hbZ : b ∈ A ⊓ A' := ((hD.mem_B_iff hxN hxa hx3).1 hb).1
  obtain ⟨d, hdD, hdm⟩ := hD.exists_d hxN hxa hx3 hbZ hbm
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  have hg3 := hD.g_pow_three hxN hxa hx3
  have hg1 := hD.g_ne_one hxN hxa hx3
  have hb1 : b ≠ 1 := by
    rintro rfl
    have h := hD.hT.m_one
    rw [hbm] at h
    have h2 : (g : M2) * ((g⁻¹ : GL2) : M2) = 1 := Units.mul_inv g
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hba : b ≠ a := by
    rintro rfl
    rw [hD.ham] at hbm
    exact hg1 (Units.ext hbm.symm)
  have hdb : d * b * d⁻¹ ≠ b := by
    intro h
    have h2 := congrArg m h
    rw [hdm, hbm] at h2
    exact gl2_inv_ne g hg3 hg1 (Units.ext h2)
  have hL : Nat.card ↥(Lg A a b) = 3840 := hD.card_L hxN hxa hx3 hb hb1 hba hdD hdb
  have hK : Nat.card ↥(Kg N a b) = 768 := hD.card_K hxN hxa hx3 hb hb1 hba hdD hdb
  have hKL : Kg N a b ≤ Lg A a b := hD.Kg_le_Lg hxN hxa hx3 hb hbm
  have hidx : (Kg N a b).relIndex (Lg A a b) = 5 := by
    have h := Subgroup.relIndex_mul_card (H := Kg N a b) (K := Lg A a b)
    rw [inf_eq_left.mpr hKL] at h
    have h' : (Kg N a b).relIndex (Lg A a b) * 768 = 3840 := by
      rw [← hK, ← hL]; exact h
    omega
  have hLK : Nat.card ↥(Kg N a b) < Nat.card ↥(Lg A a b) := by
    have : Nat.card ↥(Kg N a b) = 768 := hK
    have : Nat.card ↥(Lg A a b) = 3840 := hL
    omega
  obtain ⟨φ, hφ1, hφ2⟩ := exists_perm_five hKL hidx
  have hker : φ.ker = A.subgroupOf (Lg A a b) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ1]
    constructor
    · intro hk
      exact hD.core_le_A hxN hxa hx3 hb hbm hN hLK ⟨k.2, fun l hl => hk ⟨l, hl⟩⟩
    · intro hk l
      exact (hD.A_core hxN hxa hx3 hb hbm hk).2 l l.2
  have hAL : A ≤ Lg A a b := fun y hy =>
    hKL (hD.A_le_Kg hxN hxa hx3 hb hbm hy)
  have hrange : Nat.card φ.range = 60 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (↥(Lg A a b) ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = 64 := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hD.card_A]
    rw [hL, h2, h3] at h1
    omega
  exact ⟨hb1, hba, hL, hK, φ, hker, perm5_eq_alternating hrange, hφ2⟩

theorem Data40.exists_alt5 (hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G))
    {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3) :
    ∃ b : G, b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) ∧ b ≠ 1 ∧ b ≠ a ∧
      Nat.card ↥(Lg A a b) = 3840 ∧ Nat.card ↥(Kg N a b) = 768 ∧
      ∃ φ : ↥(Lg A a b) →* Equiv.Perm (Fin 5), φ.ker = A.subgroupOf (Lg A a b) ∧
        φ.range = alternatingGroup (Fin 5) ∧
        ∀ k : ↥(Lg A a b), φ k 0 = 0 ↔ (k : G) ∈ Kg N a b := by
  obtain ⟨b, hb, hbm⟩ := hD.exists_b hxN hxa hx3
  obtain ⟨hb1, hba, h3⟩ := hD.alt5 hN hxN hxa hx3 hb hbm
  exact ⟨b, hb, hb1, hba, h3⟩

end D40

end CFSG.Quasithin.A94.HeJ
