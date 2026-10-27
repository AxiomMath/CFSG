module

public import CFSG.Milestones.ASVolI.C31.J4NP.PlaneNative
public import Certificates.Certificate7850
public import CFSG.Quasithin.Vol2.KGFactJ4M4Card
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Fac

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Sporadic.J4.QT2A Matrix
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open scoped Pointwise

@[expose] noncomputable def burnsideJ4NP_piRow (k : ℕ) : Row :=
  toRow (((burnsideJ4NP_piVecs ())[k]?.getD V2.zero)).toVec

theorem burnsideJ4NP_Mx_gJ_inv (hM : MatFacts) :
    Mx gJ⁻¹ = rowsMatrix (burnsideJ4NP_gInvRows ()) := by
  rw [gJ, ← CFSG.Quasithin.KGC31.J4M4.wordProd_invW _ (by decide)]
  exact Mx_wordProd_baseJ hM _

theorem burnsideJ4NP_piVecs_get {k : ℕ} (hk : k < 31) :
    (burnsideJ4NP_piVecs ())[k]?.getD V2.zero =
      frApply (frTable (burnsideJ4NP_gInvRows ())) (kwVecs.getD k V2.zero) := by
  simp [burnsideJ4NP_piVecs, Array.getElem?_range, hk]

theorem burnsideJ4NP_piRow_eq (hM : MatFacts) {k : ℕ} (hk : k < 31) :
    burnsideJ4NP_piRow k = gJ • kwRow k := by
  apply ofRow_inj.mp
  rw [smul_row, ← Mx_apply, burnsideJ4NP_Mx_gJ_inv hM]
  show ((burnsideJ4NP_piVecs ())[k]?.getD V2.zero).toVec =
    (kwVecs.getD k V2.zero).toVec ᵥ* rowsMatrix (burnsideJ4NP_gInvRows ())
  rw [burnsideJ4NP_piVecs_get hk, frApply_toVec_eq_vecMul]

theorem burnsideJ4NP_piRow_zero :
    burnsideJ4NP_piRow 0 = w₀ := by
  have hM := j4Facts.mat
  rw [burnsideJ4NP_piRow_eq hM (by norm_num), kwRow_zero chkKW_true hM, smul_inv_smul]

@[expose] noncomputable def burnsideJ4NP_PiSet : Set Row :=
  {v | ∃ k < 31, v = burnsideJ4NP_piRow k}

theorem burnsideJ4NP_PiSet_eq (hM : MatFacts) :
    burnsideJ4NP_PiSet = {v : Row | ∃ k < 31, v = gJ • kwRow k} := by
  ext v
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, burnsideJ4NP_piRow_eq hM hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (burnsideJ4NP_piRow_eq hM hk).symm⟩

theorem burnsideJ4NP_mem_fix_iff (hM : MatFacts) {x : J} :
    x ∈ fixingSubgroup J burnsideJ4NP_PiSet ↔ ∀ k < 31, x • (gJ • kwRow k) = gJ • kwRow k := by
  rw [mem_fixingSubgroup_iff, burnsideJ4NP_PiSet_eq hM]
  constructor
  · intro h k hk
    exact h _ ⟨k, hk, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

@[expose] noncomputable def burnsideJ4NP_Stab : Subgroup J :=
  MulAction.stabilizer J burnsideJ4NP_PiSet

theorem burnsideJ4NP_le_Stab {K : Subgroup J}
    (h : ∀ x ∈ K, ∀ v ∈ burnsideJ4NP_PiSet, x • v ∈ burnsideJ4NP_PiSet) :
    K ≤ burnsideJ4NP_Stab := by
  intro x hx
  rw [burnsideJ4NP_Stab, MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hw
    exact h x hx u hu
  · intro v hv
    exact Set.mem_smul_set.mpr ⟨x⁻¹ • v, h _ (K.inv_mem hx) v hv, smul_inv_smul x v⟩

theorem burnsideJ4NP_Stab_smul {x : J} (hx : x ∈ burnsideJ4NP_Stab) {v : Row}
    (hv : v ∈ burnsideJ4NP_PiSet) : x • v ∈ burnsideJ4NP_PiSet := by
  have h : x • burnsideJ4NP_PiSet = burnsideJ4NP_PiSet := MulAction.mem_stabilizer_iff.mp hx
  rw [← h]
  exact Set.smul_mem_smul_set hv

@[expose] noncomputable def burnsideJ4NP_M4c : Subgroup J :=
  CFSG.Quasithin.KGJ4.M4.map (MulAut.conj gJ).toMonoidHom

theorem burnsideJ4NP_M4c_le_Stab :
    burnsideJ4NP_M4c ≤ burnsideJ4NP_Stab := by
  have hM := j4Facts.mat
  apply burnsideJ4NP_le_Stab
  rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩
  obtain ⟨k', hk', e⟩ := CFSG.Quasithin.J4M4Card.M4_smul_kwRow hm k hk
  refine ⟨k', hk', ?_⟩
  rw [burnsideJ4NP_piRow_eq hM hk, burnsideJ4NP_piRow_eq hM hk']
  show (gJ * m * gJ⁻¹) • gJ • kwRow k = gJ • kwRow k'
  rw [mul_smul, mul_smul, inv_smul_smul, e]

theorem burnsideJ4NP_w₀_mem :
    w₀ ∈ burnsideJ4NP_PiSet :=
  ⟨0, by norm_num, burnsideJ4NP_piRow_zero.symm⟩

theorem burnsideJ4NP_card_Stab_le :
    Nat.card ↥burnsideJ4NP_Stab ≤ 31 * Nat.card ↥(burnsideJ4NP_Stab ⊓ Hj) := by
  classical
  have hF := j4Facts
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥burnsideJ4NP_Stab w₀)
  rw [MulAction.index_stabilizer] at h1
  have h2 : (MulAction.orbit ↥burnsideJ4NP_Stab w₀).ncard ≤ 31 := by
    have hsub : MulAction.orbit ↥burnsideJ4NP_Stab w₀ ⊆
        ((Finset.range 31).image burnsideJ4NP_piRow : Set Row) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨k, hk, e⟩ := burnsideJ4NP_Stab_smul x.2 burnsideJ4NP_w₀_mem
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, e.symm⟩)
    calc (MulAction.orbit ↥burnsideJ4NP_Stab w₀).ncard
        ≤ ((Finset.range 31).image burnsideJ4NP_piRow : Set Row).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((Finset.range 31).image burnsideJ4NP_piRow).card := Set.ncard_coe_finset _
      _ ≤ (Finset.range 31).card := Finset.card_image_le
      _ = 31 := Finset.card_range 31
  have h3 : Nat.card ↥(MulAction.stabilizer ↥burnsideJ4NP_Stab w₀) =
      Nat.card ↥(burnsideJ4NP_Stab ⊓ Hj) := by
    have e : (MulAction.stabilizer ↥burnsideJ4NP_Stab w₀).map burnsideJ4NP_Stab.subtype =
        burnsideJ4NP_Stab ⊓ Hj := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : J) • w₀ = w₀ := hy
        exact ⟨y.2, mem_Hj_of_smul_root hF hy'⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hx1⟩, smul_root_of_mem_Hj hF.mat hx2, rfl⟩
    rw [← e, Subgroup.card_map_of_injective burnsideJ4NP_Stab.subtype_injective]
  rw [← h1, h3, mul_comm 31]
  exact Nat.mul_le_mul_left _ h2

@[expose] noncomputable def burnsideJ4NP_Y8 : Subgroup J :=
  Eg uJ 11 ⊓ fixingSubgroup J burnsideJ4NP_PiSet

theorem burnsideJ4NP_Y8_le_E : burnsideJ4NP_Y8 ≤ Eg uJ 11 := inf_le_left

@[expose] noncomputable def burnsideJ4NP_N8 : Subgroup J :=
  Hj ⊓ Subgroup.normalizer (burnsideJ4NP_Y8 : Set J)

theorem burnsideJ4NP_mem_N8 {x : J} :
    x ∈ burnsideJ4NP_N8 ↔ x ∈ Hj ∧ x ∈ Subgroup.normalizer (burnsideJ4NP_Y8 : Set J) :=
  Subgroup.mem_inf

theorem burnsideJ4NP_mem_Y8 {x : J} :
    x ∈ burnsideJ4NP_Y8 ↔ x ∈ Eg uJ 11 ∧ x ∈ fixingSubgroup J burnsideJ4NP_PiSet :=
  Subgroup.mem_inf

theorem burnsideJ4NP_StabHj_le_N8 :
    burnsideJ4NP_Stab ⊓ Hj ≤ burnsideJ4NP_N8 := by
  have hN : ∀ t ∈ burnsideJ4NP_Stab ⊓ Hj, ∀ y ∈ burnsideJ4NP_Y8,
      t * y * t⁻¹ ∈ burnsideJ4NP_Y8 := by
    intro t ht y hy
    obtain ⟨htS, htH⟩ := Subgroup.mem_inf.mp ht
    obtain ⟨hyE, hyF⟩ := burnsideJ4NP_mem_Y8.mp hy
    refine burnsideJ4NP_mem_Y8.mpr ⟨?_, ?_⟩
    · have := (normalizer_Eg_eq_Hj j4Facts).ge htH
      exact (Subgroup.mem_normalizer_iff.mp this y).mp hyE
    · rw [mem_fixingSubgroup_iff] at hyF ⊢
      intro v hv
      have h1 : t⁻¹ • v ∈ burnsideJ4NP_PiSet :=
        burnsideJ4NP_Stab_smul (burnsideJ4NP_Stab.inv_mem htS) hv
      rw [mul_smul, mul_smul, hyF _ h1, smul_inv_smul]
  intro s hs
  obtain ⟨hsS, hsH⟩ := Subgroup.mem_inf.mp hs
  refine burnsideJ4NP_mem_N8.mpr ⟨hsH, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hN s hs y
  · intro hy
    have := hN s⁻¹ (Subgroup.mem_inf.mpr ⟨burnsideJ4NP_Stab.inv_mem hsS, Hj.inv_mem hsH⟩) _ hy
    simpa [mul_assoc] using this

theorem burnsideJ4NP_eta4_mem_N8 :
    eta uJ 11 4 ∈ burnsideJ4NP_N8 := by
  have hM := j4Facts.mat
  have h4 : eta uJ 11 4 ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl 4
  refine burnsideJ4NP_mem_N8.mpr ⟨Eg_le_Hj h4, ?_⟩
  have hc : ∀ y ∈ Eg uJ 11, eta uJ 11 4 * y * (eta uJ 11 4)⁻¹ = y := by
    intro y hy
    rw [Eg_comm (elem_uJ hM) h4 hy, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hc y (burnsideJ4NP_Y8_le_E hy)]
    exact hy
  · intro hy
    have hyE : y ∈ Eg uJ 11 := by
      have e : y = (eta uJ 11 4)⁻¹ * (eta uJ 11 4 * y * (eta uJ 11 4)⁻¹) * eta uJ 11 4 := by
        group
      rw [e]
      exact (Eg uJ 11).mul_mem ((Eg uJ 11).mul_mem ((Eg uJ 11).inv_mem h4)
        (burnsideJ4NP_Y8_le_E hy)) h4
    rw [hc y hyE] at hy
    exact hy

theorem burnsideJ4NP_eta4_not_mem_Stab :
    eta uJ 11 4 ∉ burnsideJ4NP_Stab := by
  have hM := j4Facts.mat
  intro hS
  obtain ⟨i, hi, hni⟩ := Certificates.certificate7850.2.2.2.1
  obtain ⟨k, hk, e⟩ := burnsideJ4NP_Stab_smul hS ⟨i, hi, rfl⟩
  rw [burnsideJ4NP_piRow_eq hM hi, burnsideJ4NP_piRow_eq hM hk] at e
  exact hni k hk e

theorem burnsideJ4NP_two_mul_card_le :
    2 * Nat.card ↥(burnsideJ4NP_Stab ⊓ Hj) ≤ Nat.card ↥burnsideJ4NP_N8 := by
  have hle := burnsideJ4NP_StabHj_le_N8
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card ↥burnsideJ4NP_N8 := Nat.card_pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    omega
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hd
    have heq := Subgroup.eq_of_le_of_card_ge hle hd.le
    apply burnsideJ4NP_eta4_not_mem_Stab
    have h4 : eta uJ 11 4 ∈ burnsideJ4NP_Stab ⊓ Hj := heq ▸ burnsideJ4NP_eta4_mem_N8
    exact (Subgroup.mem_inf.mp h4).1
  rw [hd, mul_comm _ d]
  exact Nat.mul_le_mul_right _ (by omega)

theorem burnsideJ4NP_card_N8_le :
    759 * Nat.card ↥burnsideJ4NP_N8 ≤ Nat.card ↥Hj := by
  have hM := j4Facts.mat
  have h := Certificates.certificate7850.2.2.1
  rw [← burnsideJ4NP_PiSet_eq hM] at h
  exact h

theorem burnsideJ4NP_Stab_eq :
    burnsideJ4NP_Stab = burnsideJ4NP_M4c := by
  have hF := j4Facts
  have h1 := burnsideJ4NP_card_Stab_le
  have h2 := burnsideJ4NP_two_mul_card_le
  have h3 := burnsideJ4NP_card_N8_le
  have h4 := card_Hj hF
  have h5 : Nat.card ↥burnsideJ4NP_M4c = 10239344640 := by
    rw [burnsideJ4NP_M4c, Subgroup.card_map_of_injective (f := (MulAut.conj gJ).toMonoidHom)
      (MulAut.conj gJ).injective]
    exact CFSG.Quasithin.J4M4Card.card_M4
  refine (Subgroup.eq_of_le_of_card_ge burnsideJ4NP_M4c_le_Stab ?_).symm
  rw [h5]
  omega

@[expose] noncomputable def burnsideJ4NP_F4c :
    Subgroup J :=
  (F4 j4Facts.mat chkF_true).map (MulAut.conj gJ).toMonoidHom

theorem burnsideJ4NP_F4c_le_fix :
    burnsideJ4NP_F4c ≤ fixingSubgroup J burnsideJ4NP_PiSet := by
  have hM := j4Facts.mat
  rw [burnsideJ4NP_F4c, F4, eSub_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine (burnsideJ4NP_mem_fix_iff hM).mpr fun k hk => ?_
  change (gJ * fJn j.1 * gJ⁻¹) • gJ • kwRow k = gJ • kwRow k
  rw [mul_smul, mul_smul, inv_smul_smul, Certificates.certificate7850.1 j.1 j.2 k hk]

theorem burnsideJ4NP_fix_F4c_subset
    {g : J}
    (hfix : ∀ x ∈ burnsideJ4NP_F4c, x • (g • w₀) = g • w₀) : g • w₀ ∈ burnsideJ4NP_PiSet := by
  have hM := j4Facts.mat
  obtain ⟨k, hk, e⟩ := Certificates.certificate7850.2.2.2.2 g fun j hj =>
    hfix _ ⟨fJn j, mem_eSub (fJ_basis hM chkF_true) ⟨j, hj⟩, rfl⟩
  exact ⟨k, hk, by rw [burnsideJ4NP_piRow_eq hM hk]; exact e⟩

theorem burnsideJ4NP_normalizer_F4c_le_Stab :
    Subgroup.normalizer (burnsideJ4NP_F4c : Set J) ≤ burnsideJ4NP_Stab := by
  have hM := j4Facts.mat
  apply burnsideJ4NP_le_Stab
  rintro n hn _ ⟨k, hk, rfl⟩
  have hpt : burnsideJ4NP_piRow k = (gJ * CFSG.Quasithin.J4M4Card.tJ k * gJ⁻¹) • w₀ := by
    rw [burnsideJ4NP_piRow_eq hM hk, mul_smul, mul_smul, ← kwRow_zero chkKW_true hM,
      CFSG.Quasithin.J4M4Card.tJ_smul hk]
  have hfixv : ∀ x ∈ burnsideJ4NP_F4c, x • (n • burnsideJ4NP_piRow k) = n • burnsideJ4NP_piRow k := by
    intro x hx
    have hx' : n⁻¹ * x * n ∈ burnsideJ4NP_F4c := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
      simpa using this
    have h1 := ((mem_fixingSubgroup_iff J).mp (burnsideJ4NP_F4c_le_fix hx')) _ ⟨k, hk, rfl⟩
    calc x • (n • burnsideJ4NP_piRow k)
        = n • ((n⁻¹ * x * n) • burnsideJ4NP_piRow k) := by
          rw [smul_smul, smul_smul, show x * n = n * (n⁻¹ * x * n) by group]
      _ = n • burnsideJ4NP_piRow k := by rw [h1]
  have hg : n • burnsideJ4NP_piRow k =
      (n * (gJ * CFSG.Quasithin.J4M4Card.tJ k * gJ⁻¹)) • w₀ := by
    rw [hpt]
    exact (mul_smul _ _ _).symm
  rw [hg] at hfixv ⊢
  exact burnsideJ4NP_fix_F4c_subset hfixv

theorem burnsideJ4NP_mem_map_conj {G : Type*} [Group G] {X : Subgroup G} {c x : G} :
    x ∈ X.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨c⁻¹ * x * c, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem burnsideJ4NP_map_conj_inv_map_conj {G : Type*} [Group G] (X : Subgroup G) (c : G) :
    (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = X := by
  ext x
  rw [burnsideJ4NP_mem_map_conj, burnsideJ4NP_mem_map_conj]
  simp [mul_assoc]

theorem burnsideJ4NP_normalizer_map_conj {G : Type*} [Group G] (X : Subgroup G) (c : G) :
    Subgroup.normalizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (X : Set G)).map (MulAut.conj c).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq X (MulAut.conj c)).symm

theorem burnsideJ4NP_M4_le_normalizer :
    CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer (F4 j4Facts.mat chkF_true : Set J) :=
  M4_le_eNorm j4Facts.mat chkF_true

theorem burnsideJ4NP_normalizer_F4c :
    Subgroup.normalizer (burnsideJ4NP_F4c : Set J) = burnsideJ4NP_M4c := by
  apply le_antisymm
  · rw [← burnsideJ4NP_Stab_eq]
    exact burnsideJ4NP_normalizer_F4c_le_Stab
  · rw [burnsideJ4NP_F4c, burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_M4c]
    exact Subgroup.map_mono burnsideJ4NP_M4_le_normalizer

theorem burnsideJ4NP_normalizer_F4 :
    Subgroup.normalizer (F4 j4Facts.mat chkF_true : Set J) = CFSG.Quasithin.KGJ4.M4 := by
  have h := congrArg (fun K : Subgroup J => K.map (MulAut.conj gJ⁻¹).toMonoidHom)
    burnsideJ4NP_normalizer_F4c
  simp only [burnsideJ4NP_F4c, burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_M4c,
    burnsideJ4NP_map_conj_inv_map_conj] at h
  exact h

theorem burnsideJ4NP_centralizer_F4 :
    Subgroup.centralizer (F4 j4Facts.mat chkF_true : Set J) = F4 j4Facts.mat chkF_true := by
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ CFSG.Quasithin.KGJ4.M4 :=
      burnsideJ4NP_normalizer_F4 ▸ Subgroup.centralizer_le_normalizer _ hx
    exact m4_CE j4Facts.mat chkF_true CFSG.Quasithin.J4M4Card.card_M4 ⟨hxM, hx⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact eSub_comm (fJ_basis j4Facts.mat chkF_true) y x hy hx

end CFSG.ASVolI
