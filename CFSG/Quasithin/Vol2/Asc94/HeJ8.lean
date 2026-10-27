module

public import CFSG.Quasithin.Vol2.Asc94.HeJ4

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gl2_order_three_eq : ∀ g g' : GL2, g ^ 3 = 1 → g ≠ 1 → g' ^ 3 = 1 → g' ≠ 1 →
    g' = g ∨ g' = g⁻¹ := by
  set_option synthInstance.maxSize 1000 in
  set_option synthInstance.maxHeartbeats 200000 in
  decide +kernel

theorem gl2_comm_conj : ∀ g h : GL2, g ^ 3 = 1 → ∀ M : M2,
    (g.val * (h.val * M * (h⁻¹ : GL2).val) = (h.val * M * (h⁻¹ : GL2).val) * g.val ↔
      g.val * M = M * g.val) := by
  decide +kernel

theorem gl2_comm_inv : ∀ (g : GL2) (M : M2),
    ((g⁻¹ : GL2).val * M = M * (g⁻¹ : GL2).val ↔ g.val * M = M * g.val) := by
  decide +kernel

theorem gl2_exists_inverting : ∀ g : GL2, g ^ 3 = 1 → ∃ h : GL2, h * g * h⁻¹ = g⁻¹ := by
  decide +kernel

theorem exists_conj_mem_of_relIndex_five {H K : Subgroup G} (hHK : H ≤ K) (hidx : H.relIndex K = 5)
    {x : G} (hx : x ∈ H) (hx3 : orderOf x = 3) : ∃ l ∈ K, l ∉ H ∧ l⁻¹ * x * l ∈ H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set x' : K := ⟨x, hHK hx⟩ with hx'
  have hox : orderOf x' = 3 := by
    rw [← hx3, ← Subgroup.orderOf_coe]
  have hcardP : Nat.card (Subgroup.zpowers x') = 3 ^ 1 := by
    rw [Nat.card_zpowers, hox]; norm_num
  have hP : IsPGroup 3 (Subgroup.zpowers x') := IsPGroup.of_card hcardP
  have hmod := hP.card_modEq_card_fixedPoints (K ⧸ H.subgroupOf K)
  have hq : Nat.card (K ⧸ H.subgroupOf K) = 5 := by
    rw [← hidx]
    rfl
  rw [hq] at hmod
  set Fx := MulAction.fixedPoints (Subgroup.zpowers x') (K ⧸ H.subgroupOf K) with hFx
  have h1mem : ((1 : K) : K ⧸ H.subgroupOf K) ∈ Fx := by
    rw [hFx, MulAction.mem_fixedPoints]
    rintro ⟨m, hm⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    show ((x' ^ k : K) • ((1 : K) : K ⧸ H.subgroupOf K)) = ((1 : K) : K ⧸ H.subgroupOf K)
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    simp only [inv_one, one_mul, mul_one]
    rw [Subgroup.mem_subgroupOf]
    have : (((x' ^ k)⁻¹ : K) : G) = (x ^ k)⁻¹ := by simp [hx']
    rw [this]
    exact H.inv_mem (H.zpow_mem hx k)
  have hge : 1 < Nat.card Fx := by
    have hpos : 0 < Nat.card Fx := Nat.card_pos_iff.2 ⟨⟨⟨_, h1mem⟩⟩, inferInstance⟩
    by_contra hlt
    have h1 : Nat.card Fx = 1 := by omega
    rw [h1] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨c, hc⟩, hcne⟩ : ∃ c : Fx, c ≠ ⟨_, h1mem⟩ := by
    haveI : Finite Fx := inferInstance
    obtain ⟨c, d, hcd⟩ := (Finite.one_lt_card_iff_nontrivial.1 hge).exists_pair_ne
    by_cases hc1 : c = ⟨_, h1mem⟩
    · exact ⟨d, fun hd => hcd (hc1.trans hd.symm)⟩
    · exact ⟨c, hc1⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨l, l.2, ?_, ?_⟩
  · intro hl
    apply hcne
    apply Subtype.ext
    show ((l : K) : K ⧸ H.subgroupOf K) = ((1 : K) : K ⧸ H.subgroupOf K)
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using H.inv_mem hl
  · have hfix := (MulAction.mem_fixedPoints.1 hc) ⟨x', Subgroup.mem_zpowers x'⟩
    have : ((x' * l : K) : K ⧸ H.subgroupOf K) = (l : K ⧸ H.subgroupOf K) := hfix
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    have e : (((x' * l)⁻¹ * l : K) : G) = ((l : K) : G)⁻¹ * x⁻¹ * ((l : K) : G) *
      (((l : K) : G)⁻¹ * ((l : K) : G)) := by
      simp [hx', mul_assoc]
    have h2 : ((l : K) : G)⁻¹ * x⁻¹ * ((l : K) : G) ∈ H := by
      have := this
      simpa [hx', mul_assoc] using this
    have := H.inv_mem h2
    simpa [mul_assoc] using this

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hD hxN hxa hx3

theorem Data40.mem_B_iff {y : G} :
    y ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) ↔
      y ∈ A ⊓ A' ∧ ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val * m y =
        m y * ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val := by
  set g := (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 with hg
  have hconj : ∀ v ∈ A ⊓ A', m (x * v * x⁻¹) = (g : M2) * m v * ((g⁻¹ : GL2) : M2) :=
    fun v hv => hD.m_conj_D (n := ⟨x, hxN⟩) hxa hv
  constructor
  · rintro ⟨hyZ, hyc⟩
    refine ⟨hyZ, ?_⟩
    have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hyc).symm
    have hc : x * y * x⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact hxy
    have h1 := hconj y hyZ
    rw [hc] at h1
    have h2 : (g : M2) * m y = m y * (g : M2) := by
      calc (g : M2) * m y = ((g : M2) * m y * ((g⁻¹ : GL2) : M2)) * (g : M2) := by
            rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]
        _ = m y * (g : M2) := by rw [← h1]
    exact h2
  · rintro ⟨hyZ, hym⟩
    refine ⟨hyZ, ?_⟩
    have hZ : x * y * x⁻¹ ∈ A ⊓ A' := hD.mem_Z_conj hxN hyZ
    have h1 := hconj y hyZ
    have h3 : m (x * y * x⁻¹) = m y := by
      rw [h1, hym, mul_assoc, Units.mul_inv, mul_one]
    have h4 : x * y * x⁻¹ = y := hD.hT.minj _ hZ _ hyZ h3
    show y ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    have : x * y = y * x := by
      rw [mul_inv_eq_iff_eq_mul] at h4; exact h4
    exact this.symm

theorem Data40.a_mem_B : a ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) :=
  ⟨hD.ha, mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hxa).symm⟩

theorem Data40.card_B : Nat.card ↥((A ⊓ A') ⊓ centralizer ({x} : Set G)) = 4 := by
  set g := (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 with hg
  have hgc := gl2_cent_card g (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3)
  have hbij : Nat.card ↥((A ⊓ A') ⊓ centralizer ({x} : Set G)) =
      Nat.card {M : M2 // (g : M2) * M = M * (g : M2)} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨m y.1, ((hD.mem_B_iff hxN hxa hx3).1 y.2).2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      have h' : m y.1 = m y'.1 := congrArg Subtype.val h
      exact Subtype.ext (hD.hT.minj _ ((hD.mem_B_iff hxN hxa hx3).1 y.2).1 _
        ((hD.mem_B_iff hxN hxa hx3).1 y'.2).1 h')
    · rintro ⟨M, hM⟩
      obtain ⟨y, hy, hym⟩ := hD.hT.msurj M
      exact ⟨⟨y, (hD.mem_B_iff hxN hxa hx3).2 ⟨hy, by rw [hym]; exact hM⟩⟩, Subtype.ext hym⟩
  rw [hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert hgc

theorem Data40.cent_A_eq :
    A ⊓ centralizer ({x} : Set G) = (A ⊓ A') ⊓ centralizer ({x} : Set G) := by
  set g := (hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 with hg
  ext y
  constructor
  · rintro ⟨hyA, hyc⟩
    refine ⟨⟨hyA, ?_⟩, hyc⟩
    have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hyc).symm
    have hc : x * y * x⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact hxy
    have h1 : u (x * y * x⁻¹) = (g : M2) *ᵥ u y := hD.hT.u_conj N hD.hK.norm ⟨x, hxN⟩ hyA
    rw [hc] at h1
    have h3 := gl2_order_three_fpf g (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3)
      (u y) h1.symm
    exact (hD.hT.cu.zero y hyA).1 h3
  · rintro ⟨⟨hyA, -⟩, hyc⟩
    exact ⟨hyA, hyc⟩

theorem Data40.D_le_normalizer_B :
    N ⊓ centralizer ({a} : Set G) ≤
      normalizer (((A ⊓ A') ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rintro d ⟨hdN, hda⟩
  apply Subgroup.mem_normalizer_fintype
  intro y hy
  have hy' := (hD.mem_B_iff hxN hxa hx3).1 hy
  have hdZ : d * y * d⁻¹ ∈ A ⊓ A' := hD.mem_Z_conj hdN hy'.1
  show d * y * d⁻¹ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G)
  rw [hD.mem_B_iff hxN hxa hx3]
  refine ⟨hdZ, ?_⟩
  have hm := hD.m_conj_D (n := ⟨d, hdN⟩) hda hy'.1
  have hm' : m (d * y * d⁻¹) = (((hD.hT.rho N hD.hK.norm ⟨d, hdN⟩).1 : GL2) : M2) * m y *
      (((hD.hT.rho N hD.hK.norm ⟨d, hdN⟩).1⁻¹ : GL2) : M2) := hm
  rw [hm']
  exact (gl2_comm_conj _ _ (hD.g_pow_three hxN hxa hx3) (m y)).2 hy'.2

end X

section XX

variable {x x' : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)
  (hx'N : x' ∈ N) (hx'a : x' ∈ centralizer ({a} : Set G)) (hx'3 : orderOf x' = 3)

include hD hxN hxa hx3 hx'N hx'a hx'3

theorem Data40.B_eq :
    (A ⊓ A') ⊓ centralizer ({x'} : Set G) = (A ⊓ A') ⊓ centralizer ({x} : Set G) := by
  ext y
  rw [hD.mem_B_iff hxN hxa hx3, hD.mem_B_iff hx'N hx'a hx'3]
  refine and_congr_right fun _ => ?_
  rcases gl2_order_three_eq _ _ (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3)
      (hD.g_pow_three hx'N hx'a hx'3) (hD.g_ne_one hx'N hx'a hx'3) with h | h
  · rw [h]
  · rw [h]
    exact gl2_comm_inv _ _

end XX

section X2

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hD hxN hxa hx3

theorem Data40.I_le_normalizer_B :
    normalizer (A : Set G) ⊓ centralizer ({a} : Set G) ≤
      normalizer (((A ⊓ A') ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  set B : Subgroup G := (A ⊓ A') ⊓ centralizer ({x} : Set G) with hB
  have hxD : x ∈ N ⊓ centralizer ({a} : Set G) := ⟨hxN, hxa⟩
  obtain ⟨l, hlI, hlD, hlx⟩ := exists_conj_mem_of_relIndex_five hD.D_le_I hD.relIndex_D_I hxD hx3
  set x'' : G := l⁻¹ * x * l with hx''
  have hx''N : x'' ∈ N := hlx.1
  have hx''a : x'' ∈ centralizer ({a} : Set G) := hlx.2
  have hx''3 : orderOf x'' = 3 := by
    rw [← hx3]
    exact (SemiconjBy.orderOf_eq l⁻¹ (show SemiconjBy l⁻¹ x x'' by
      show l⁻¹ * x = (l⁻¹ * x * l) * l⁻¹; group)).symm
  have hBeq := hD.B_eq hxN hxa hx3 hx''N hx''a hx''3
  have hAeq := hD.cent_A_eq hx''N hx''a hx''3
  have hlN : l ∈ normalizer (B : Set G) := by
    have hinv : l⁻¹ ∈ normalizer (B : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have hyB := (hD.mem_B_iff hxN hxa hx3).1 hy
      have hyA : y ∈ A := hyB.1.1
      have hyc : y ∈ centralizer ({x} : Set G) := hy.2
      have h1 : l⁻¹ * y * l ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hlI.1) y).1 hyA
        simpa using this
      have h2 : l⁻¹ * y * l ∈ centralizer ({x''} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have hxy : y * x = x * y := mem_centralizer_singleton_iff.1 hyc
        calc l⁻¹ * y * l * x'' = l⁻¹ * (y * x) * l := by rw [hx'']; group
          _ = l⁻¹ * (x * y) * l := by rw [hxy]
          _ = x'' * (l⁻¹ * y * l) := by rw [hx'']; group
      have h3 : l⁻¹ * y * l ∈ A ⊓ centralizer ({x''} : Set G) := ⟨h1, h2⟩
      rw [hAeq, hBeq] at h3
      have h4 : l⁻¹ * y * l ∈ B := h3
      rw [inv_inv]
      exact h4
    have := inv_mem hinv
    simpa using this
  have hDK : N ⊓ centralizer ({a} : Set G) ≤
      (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ normalizer (B : Set G) :=
    le_inf hD.D_le_I (hD.D_le_normalizer_B hxN hxa hx3)
  have hKI : (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ normalizer (B : Set G) ≤
      normalizer (A : Set G) ⊓ centralizer ({a} : Set G) := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hDK hKI
  rw [hD.relIndex_D_I] at hmul
  have hp : Nat.Prime 5 := by norm_num
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hmul) with h1 | h5
  · exfalso
    have := Subgroup.relIndex_eq_one.1 h1
    exact hlD (this ⟨hlI, hlN⟩)
  · rw [h5] at hmul
    have h1 : ((normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ normalizer (B : Set G)).relIndex
        (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) = 1 := by omega
    intro y hy
    exact (Subgroup.relIndex_eq_one.1 h1 hy).2

end X2

end D40

end CFSG.Quasithin.A94.HeJ
