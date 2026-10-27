module

public import CFSG.Quasithin.Vol2.Ch10SecCBasic
public import CFSG.Quasithin.Vol2.Ch10SecABasicL0
public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem subnormal_of_le_normalizer {T L X : Subgroup G} (hX : X ≤ fsuL0 T L)
    (hn : fsuL0 T L ≤ Subgroup.normalizer (X : Set G)) : IsSubnormal X (fsuM T L) :=
  IsSubnormal.step hX ((Subgroup.normal_subgroupOf_iff_le_normalizer hX).mpr hn)
    (IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer (IsSubnormal.refl _))

theorem commutator_self_of_local {T L : Subgroup G} (h : quasithinIsLocal T L) : ⁅L, L⁆ = L :=
  h.2.1.2.1

theorem fsuL0_le_oPrimeResidualOf {T L : Subgroup G} {t : G} {p : ℕ}
    (hL0 : fsuL0 T L = L ⊔ CFSG.conjugate L t) (hLp : oPrimeResidualOf p L = L) :
    fsuL0 T L ≤ oPrimeResidualOf p (fsuL0 T L) := by
  have hLt : oPrimeResidualOf p (CFSG.conjugate L t) = CFSG.conjugate L t := by
    rw [SecA.conjugate_eq_map, oPrimeResidualOf_map, hLp]
  rw [hL0]
  refine sup_le ?_ ?_
  · calc L = oPrimeResidualOf p L := hLp.symm
      _ ≤ _ := oPrimeResidualOf_mono p le_sup_left
  · calc CFSG.conjugate L t = oPrimeResidualOf p (CFSG.conjugate L t) := hLt.symm
      _ ≤ _ := oPrimeResidualOf_mono p le_sup_right

theorem card_conjugate (X : Subgroup G) (g : G) : Nat.card (CFSG.conjugate X g) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

variable [Finite G]

theorem inf_conjSubgroup_eq_bot {T L I : Subgroup G} (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) (h1029 : Stmt10_2_9)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (hL0 : fsuL0 T L = L ⊔ CFSG.conjugate L t)
    (hn : fsuL0 T L ≤ Subgroup.normalizer (L : Set G))
    (hnt : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G)) {g : G}
    (hg : g ∉ fsuM T L) :
    ⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊓ conjSubgroup ⁅fsuVM T L I, CFSG.conjugate L t⁆ g = ⊥ := by
  set V := fsuVM T L I with hV
  set Lt := CFSG.conjugate L t with hLt
  obtain ⟨hVM, hR, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2L, -⟩ := hdec t ht htn
  have hLperf : ⁅L, L⁆ = L := commutator_self_of_local hyp.fsu.faithful.1
  have hLi : IsLi T L Lt := Or.inr ⟨t, ht, htn, rfl⟩
  have hMV : fsuM T L ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_conjClosure (fsuV T I) (fsuM T L)
  have hLtL0 : Lt ≤ fsuL0 T L := SecA.conjugate_le_fsuL0 ht
  have hV2V : ⁅V, Lt⁆ ≤ V :=
    commutator_le_left_of_le_normalizer (hLtL0.trans (Subgroup.le_normalizer.trans hMV))
  rw [eq_bot_iff]
  rintro x ⟨hx2, hxg⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hgx : g * x * g⁻¹ ∈ ⁅V, Lt⁆ := mem_conjSubgroup_iff.mp hxg
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group
  have hC1 := (h1029 G T L I hyp Lt hLi).1 x hx2 hx1
  have hC2 := (h1029 G T L I hyp Lt hLi).1 (g * x * g⁻¹) hgx hgx1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := mem_centralizer_iff_le.mp (hV2L hx2)
  have hLgx : CFSG.conjugate L g ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hc := Subgroup.mem_centralizer_iff.mp (hV2L hgx) l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have : g⁻¹ * l * g * x = g⁻¹ * (l * (g * x * g⁻¹)) * g := by group
    rw [this, hc]
    group
  have hCxg : Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup (fsuM T L) g := by
    intro y hy
    rw [mem_conjSubgroup_iff]
    apply hC2
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hc := Subgroup.mem_centralizer_iff.mp hy x rfl
    have : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    rw [this, hc]
    group
  obtain ⟨p, hp, hp2, hpd⟩ :=
    exists_odd_prime_dvd_card hsimp (nonabelian_of_isQuasisimple hyp.fsu.quasisimple)
  have hM : oPrimeResidualOf p (fsuM T L) = fsuL0 T L := h1013 G T L I hyp p hp hp2 hpd
  have hLp : oPrimeResidualOf p L = L := oPrimeResidualOf_eq_self hp hLperf hsimp hpd
  have hLgL0 : CFSG.conjugate L g ≤ fsuL0 T L := by
    have hLgp : oPrimeResidualOf p (CFSG.conjugate L g) = CFSG.conjugate L g := by
      rw [SecA.conjugate_eq_map, oPrimeResidualOf_map, hLp]
    rw [← hLgp, ← hM]
    exact oPrimeResidualOf_mono p (hLgx.trans hC1)
  by_cases hxL0 : x ∈ Subgroup.centralizer (fsuL0 T L : Set G)
  ·
    have hL0g : fsuL0 T L ≤ conjSubgroup (fsuL0 T L) g := by
      have hconj : conjSubgroup (fsuL0 T L) g = oPrimeResidualOf p (conjSubgroup (fsuM T L) g) := by
        rw [conjSubgroup, conjSubgroup, oPrimeResidualOf_map, hM]
      rw [hconj]
      exact (fsuL0_le_oPrimeResidualOf hL0 hLp).trans
        (oPrimeResidualOf_mono p ((mem_centralizer_iff_le.mp hxL0).trans hCxg))
    have hc : Nat.card (conjSubgroup (fsuL0 T L) g) = Nat.card (fsuL0 T L) :=
      card_conjugate (fsuL0 T L) g
    have heq : CFSG.conjugate (fsuL0 T L) g = fsuL0 T L :=
      (Subgroup.eq_of_le_of_card_ge hL0g hc.le).symm
    exact hg (SecA.conjugate_eq_self_iff.mp heq)
  ·
    have hxLt : x ∉ Subgroup.centralizer (Lt : Set G) := fun h =>
      hxL0 (hL0 ▸ mem_centralizer_sup (hV2L hx2) h)
    have hOA : pCoreOf 2 Lt ≤ Subgroup.centralizer (V : Set G) :=
      pCoreOf_le_centralizer_of_subnormal hR hVM (subnormal_of_le_normalizer hLtL0 hnt)
    have hLgL : CFSG.conjugate L g ≤ L :=
      le_of_le_fsuL0_of_le_centralizer hLperf hsimp hL0 hn hnt ⟨t, rfl⟩ ⟨g, rfl⟩ hOA (hV2V hx2)
        hLx hxLt hLgL0 hLgx
    have heq : CFSG.conjugate L g = L :=
      Subgroup.eq_of_le_of_card_ge hLgL (card_conjugate L g).ge
    exact hg ((h1026 G T L I hyp).2.2 (SecA.conjugate_eq_self_iff.mp heq))

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {V L : Subgroup G} {g : G}
    (hV : g ∈ Subgroup.normalizer (V : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rw [← Subgroup.mem_normalizer_iff.mp hV y]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hL) l).mp hl
    have := h _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * l := by group
  · intro h l hl
    have hl' : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hL l).mp hl
    have := h _ hl'
    have e1 : l * y = g⁻¹ * ((g * l * g⁻¹) * (g * y * g⁻¹)) * g := by group
    have e2 : y * l = g⁻¹ * ((g * y * g⁻¹) * (g * l * g⁻¹)) * g := by group
    rw [e1, e2, this]

omit [Finite G] in
theorem inf_centralizer_eq_of_cvm_eq_bot {T L I A B : Subgroup G}
    (hVc : IsMulCommutative ↥(fsuVM T L I)) (hcv : fsuCVM T L I = ⊥) (hBA : fsuL0 T L = B ⊔ A)
    (hdec : fsuVM T L I = ⁅fsuVM T L I, A⁆ ⊔ ⁅fsuVM T L I, B⁆)
    (hAB : ⁅fsuVM T L I, A⁆ ≤ Subgroup.centralizer (B : Set G))
    (hBA' : ⁅fsuVM T L I, B⁆ ≤ Subgroup.centralizer (A : Set G))
    (hAV : ⁅fsuVM T L I, A⁆ ≤ fsuVM T L I) (hBV : ⁅fsuVM T L I, B⁆ ≤ fsuVM T L I) :
    fsuVM T L I ⊓ Subgroup.centralizer (B : Set G) = ⁅fsuVM T L I, A⁆ := by
  set V := fsuVM T L I
  apply le_antisymm _ (le_inf hAV hAB)
  rintro v ⟨hv, hvB⟩
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVc.is_comm.comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hn : ⁅V, A⁆ ≤ Subgroup.normalizer ((⁅V, B⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm a (hAV ha) y (hBV hy)]
      simpa using hy
    · intro hy
      have : a * y * a⁻¹ = y := by
        have hyV : y ∈ V := by
          have h1 : a * y * a⁻¹ ∈ V := hBV hy
          have h2 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
          rw [← h2]
          exact V.mul_mem (V.mul_mem (V.inv_mem (hAV ha)) h1) (hAV ha)
        rw [hcomm a (hAV ha) y hyV]
        group
      rwa [this] at hy
  have hv' : v ∈ (↑(⁅V, A⁆ ⊔ ⁅V, B⁆) : Set G) := by rw [← hdec]; exact hv
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hv'
  obtain ⟨a, ha, b, hb, rfl⟩ := hv'
  have hbB : b ∈ Subgroup.centralizer (B : Set G) := by
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAB ha)) hvB
  have hbL0 : b ∈ fsuCVM T L I := by
    refine ⟨hBV hb, ?_⟩
    rw [hBA, sup_comm]
    exact mem_centralizer_sup (hBA' hb) hbB
  rw [hcv, Subgroup.mem_bot] at hbL0
  subst hbL0
  simpa using ha

omit [Finite G] in
theorem conjugate_le_centralizer {X : Subgroup G} {g x : G}
    (h : X ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set G)) :
    CFSG.conjugate X g ≤ Subgroup.centralizer ({x} : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hc := Subgroup.mem_centralizer_iff.mp (h hl) _ rfl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have e1 : x * (g⁻¹ * l * g) = g⁻¹ * ((g * x * g⁻¹) * l) * g := by group
  have e2 : g⁻¹ * l * g * x = g⁻¹ * (l * (g * x * g⁻¹)) * g := by group
  rw [e1, e2, hc]

end CFSG.Quasithin.Vol2.Ch10.SecC
