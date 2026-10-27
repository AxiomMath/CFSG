module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.QuasithinUnique CFSG.Open
  CFSG.RankThree.PartOne.KCRootAxis

section Dec

variable {D : Type} [Group D]

theorem map_eq_of_mem_autStab {P : Subgroup D} {φ : MulAut D} (h : φ ∈ autStab P) :
    P.map φ.toMonoidHom = P := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mp hx
  · intro hy
    refine ⟨φ⁻¹ y, ?_, by simp⟩
    exact (h (φ⁻¹ y)).mpr (by simpa using hy)

theorem mem_autStab_of_map_eq {P : Subgroup D} {φ : MulAut D} (h : P.map φ.toMonoidHom = P) :
    φ ∈ autStab P := by
  intro x
  constructor
  · intro hx
    have : φ x ∈ P.map φ.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := φ.injective hzx
    rwa [this] at hz

theorem isYAmalgamPair_symm {TD P Q : Subgroup D} (h : IsYAmalgamPair TD P Q) :
    IsYAmalgamPair TD Q P :=
  ⟨h.1, h.2.1.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem exists_conj_stab [Finite D] {TD P Q : Subgroup D} (hY : IsYAmalgamPair TD P Q)
    {φ : MulAut D} (hφ : φ ∈ autStab P) :
    ∃ u ∈ P, (MulAut.conj u)⁻¹ * φ ∈ autStab P ∧ (MulAut.conj u)⁻¹ * φ ∈ autStab Q := by
  have hTDP : TD ≤ P :=
    Subgroup.le_normalizer.trans ((hY.2.2 P).mpr (Or.inl rfl)).2
  have hTD'syl : IsSylowTwoOf (TD.map φ.toMonoidHom) ⊤ := (IsYAmalgamPair.map φ hY).1
  have hmapP : P.map φ.toMonoidHom = P := map_eq_of_mem_autStab hφ
  have hTD'P : TD.map φ.toMonoidHom ≤ P := by
    rw [← hmapP]
    exact Subgroup.map_mono hTDP
  have hS : IsSylowTwoOf TD P := isSylowTwoOf_mono_right hY.1 hTDP le_top
  have hS' : IsSylowTwoOf (TD.map φ.toMonoidHom) P := isSylowTwoOf_mono_right hTD'syl hTD'P le_top
  obtain ⟨u, hu, hconj⟩ := IsSylowTwoOf.exists_conj hS hS'
  have hφ'x : ∀ x : D, ((MulAut.conj u)⁻¹ * φ) x = u⁻¹ * φ x * u := fun x => by
    simp [MulAut.mul_apply]
  have hPstab : (MulAut.conj u)⁻¹ * φ ∈ autStab P := by
    intro x
    rw [hφ'x]
    have := (hφ x)
    constructor
    · intro hx
      exact P.mul_mem (P.mul_mem (P.inv_mem hu) (this.mp hx)) hu
    · intro hx
      apply this.mpr
      have := P.mul_mem (P.mul_mem hu hx) (P.inv_mem hu)
      simpa [mul_assoc] using this
  have hTDstab : (MulAut.conj u)⁻¹ * φ ∈ autStab TD := by
    intro x
    rw [hφ'x]
    constructor
    · intro hx
      have h1 : φ x ∈ TD.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [hconj] at h1
      obtain ⟨t, ht, hte⟩ := h1
      have : u⁻¹ * φ x * u = t := by
        rw [← hte]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]
      exact ht
    · intro hx
      have h1 : φ x ∈ TD.map (MulAut.conj u).toMonoidHom := by
        refine ⟨u⁻¹ * φ x * u, hx, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      rw [← hconj] at h1
      obtain ⟨x', hx', hx'e⟩ := h1
      have : x' = x := φ.injective hx'e
      rwa [this] at hx'
  refine ⟨u, hu, hPstab, ?_⟩
  have hY' := IsYAmalgamPair.map ((MulAut.conj u)⁻¹ * φ) hY
  rw [map_eq_of_mem_autStab hTDstab, map_eq_of_mem_autStab hPstab] at hY'
  obtain ⟨hmax, hN⟩ := (hY'.2.2 (Q.map ((MulAut.conj u)⁻¹ * φ).toMonoidHom)).mpr (Or.inr rfl)
  rcases (hY.2.2 (Q.map ((MulAut.conj u)⁻¹ * φ).toMonoidHom)).mp ⟨hmax, hN⟩ with h | h
  · exfalso
    apply hY.2.1
    have hinj : Function.Injective (((MulAut.conj u)⁻¹ * φ).toMonoidHom) :=
      ((MulAut.conj u)⁻¹ * φ).injective
    refine Subgroup.map_injective hinj ?_
    rw [map_eq_of_mem_autStab hPstab]
    exact h.symm
  · exact mem_autStab_of_map_eq h

variable [Finite D] (A : LieAmalgamExt D)

theorem LieAmalgamExt.N1_le_inn_sup :
    A.N1 ≤ (MulAut.conj : D →* MulAut D).range ⊔ (A.N1 ⊓ A.N2) := by
  intro k hk
  obtain ⟨u, hu, h1, h2⟩ := exists_conj_stab A.yam hk.2
  have hmem : (MulAut.conj u)⁻¹ * k ∈ A.Mbar := by
    refine A.Mbar.mul_mem (A.Mbar.inv_mem (A.inn_le ⟨u, rfl⟩)) hk.1
  have hk' : (MulAut.conj u)⁻¹ * k ∈ A.N1 ⊓ A.N2 := ⟨⟨hmem, h1⟩, ⟨hmem, h2⟩⟩
  have hu' : MulAut.conj u ∈ (MulAut.conj : D →* MulAut D).range := ⟨u, rfl⟩
  have := Subgroup.mul_mem_sup hu' hk'
  simpa using this

theorem LieAmalgamExt.N2_le_inn_sup :
    A.N2 ≤ (MulAut.conj : D →* MulAut D).range ⊔ (A.N1 ⊓ A.N2) := by
  intro k hk
  obtain ⟨u, hu, h2, h1⟩ := exists_conj_stab (isYAmalgamPair_symm A.yam) hk.2
  have hmem : (MulAut.conj u)⁻¹ * k ∈ A.Mbar := by
    refine A.Mbar.mul_mem (A.Mbar.inv_mem (A.inn_le ⟨u, rfl⟩)) hk.1
  have hk' : (MulAut.conj u)⁻¹ * k ∈ A.N1 ⊓ A.N2 := ⟨⟨hmem, h1⟩, ⟨hmem, h2⟩⟩
  have hu' : MulAut.conj u ∈ (MulAut.conj : D →* MulAut D).range := ⟨u, rfl⟩
  have := Subgroup.mul_mem_sup hu' hk'
  simpa using this

theorem LieAmalgamExt.K_le_inn_sup :
    A.K ≤ (MulAut.conj : D →* MulAut D).range ⊔ (A.N1 ⊓ A.N2) :=
  sup_le (LieAmalgamExt.N1_le_inn_sup A) (LieAmalgamExt.N2_le_inn_sup A)

end Dec

section Transport

variable {D X : Type} [Group D] [Group X]

theorem conj_mem_autStab_iff (E : D ≃* X) {P : Subgroup D} {R : Subgroup X}
    (hP : P.map E.toMonoidHom = Subgroup.normalizer (R : Set X))
    (hc : pCoreOf 2 (Subgroup.normalizer (R : Set X)) = R) (y : X) :
    MulAut.conj (E.symm y) ∈ autStab P ↔ y ∈ Subgroup.normalizer (R : Set X) := by
  set S : Subgroup D := R.map E.symm.toMonoidHom with hS
  have hnS : (Subgroup.normalizer (R : Set X)).map E.symm.toMonoidHom =
      Subgroup.normalizer (S : Set D) := by
    ext g
    rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map E.symm R g]
  have hPS : P = Subgroup.normalizer (S : Set D) := by
    rw [← hnS, ← hP, Subgroup.map_map]
    ext g
    simp
  have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
    rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hc]
  rw [hPS, mem_autStab_iff_of_normalizer hcoreS]
  have h1 : (∀ x, x ∈ S ↔ MulAut.conj (E.symm y) x ∈ S) ↔
      E.symm y ∈ Subgroup.normalizer (S : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    simp only [MulAut.conj_apply]
  rw [h1, hS, mem_normalizer_map E.symm R (E.symm y)]
  simp

@[expose] noncomputable def innHom (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (E : D ≃* X) : X →* ↥A.K :=
  ((MulAut.conj : D →* MulAut D).codRestrict A.K (fun d => hgen ⟨d, rfl⟩)).comp
    E.symm.toMonoidHom

theorem innHom_coe (A : LieAmalgamExt D) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (E : D ≃* X) (y : X) : ((innHom A hgen E y : ↥A.K) : MulAut D) = MulAut.conj (E.symm y) :=
  rfl

theorem conj_injective_of_center (hcen : Subgroup.center D = ⊥) :
    Function.Injective (MulAut.conj : D →* MulAut D) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hdc : d ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut D => φ g) hd
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hcen] at hdc
  exact Subgroup.mem_bot.mp hdc

end Transport

section Datum

variable {D X : Type} [Group D] [Group X] (A : LieAmalgamExt D) (hfin : Finite D)
  (pm : ℕ) (hpm : 3 ≤ pm)

theorem xdatum_of_inn (E : D ≃* X) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (hcen : Subgroup.center D = ⊥) {R₁ R₂ : Subgroup X}
    (hP1 : A.P1.map E.toMonoidHom = Subgroup.normalizer (R₁ : Set X))
    (hP2 : A.P2.map E.toMonoidHom = Subgroup.normalizer (R₂ : Set X))
    (hc1 : pCoreOf 2 (Subgroup.normalizer (R₁ : Set X)) = R₁)
    (hc2 : pCoreOf 2 (Subgroup.normalizer (R₂ : Set X)) = R₂)
    {V : Type} [MulAction X V] (ΓM : SimpleGraph V) (v₁ v₂ : V)
    (s1 : ∀ y : X, y • v₁ = v₁ ↔ y ∈ Subgroup.normalizer (R₁ : Set X))
    (s2 : ∀ y : X, y • v₂ = v₂ ↔ y ∈ Subgroup.normalizer (R₂ : Set X))
    (disj : ∀ y z : X, y • v₁ ≠ z • v₂) (noadj1 : ∀ y z : X, ¬ ΓM.Adj (y • v₁) (z • v₁))
    (noadj2 : ∀ y z : X, ¬ ΓM.Adj (y • v₂) (z • v₂)) (adj12 : ΓM.Adj v₁ v₂) :
    XDatum (A.setting hfin pm hpm) (phiG0 A hfin pm hpm (innHom A hgen E)) ΓM v₁ v₂ := by
  have hinj := conj_injective_of_center hcen
  have hΦinj : Function.Injective (innHom A hgen E) := fun a b h => by
    have := congrArg (fun k : ↥A.K => (k : MulAut D)) h
    simp only [innHom_coe] at this
    exact E.symm.injective (hinj this)
  have hΦr : ∀ k : ↥A.K, k ∈ (innHom A hgen E).range ↔
      (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range := by
    intro k
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨d, hd⟩
      refine ⟨E d, ?_⟩
      apply Subtype.ext
      rw [innHom_coe, E.symm_apply_apply]
      exact hd
  have hs1 : ∀ y, phiG0 A hfin pm hpm (innHom A hgen E) y • (A.setting hfin pm hpm).ι.xv =
      (A.setting hfin pm hpm).ι.xv ↔ y ∈ Subgroup.normalizer (R₁ : Set X) := by
    intro y
    refine (smul_xv_iff (A.setting hfin pm hpm).ι (phiG0 A hfin pm hpm (innHom A hgen E) y)).trans
      ?_
    refine (mem_range_φ1_iff A hfin pm hpm (innHom A hgen E y)).trans ?_
    rw [innHom_coe]
    exact ⟨fun h => (conj_mem_autStab_iff E hP1 hc1 y).mp h.2,
      fun h => ⟨A.inn_le ⟨_, rfl⟩, (conj_mem_autStab_iff E hP1 hc1 y).mpr h⟩⟩
  have hs2 : ∀ y, phiG0 A hfin pm hpm (innHom A hgen E) y • (A.setting hfin pm hpm).ι.lv =
      (A.setting hfin pm hpm).ι.lv ↔ y ∈ Subgroup.normalizer (R₂ : Set X) := by
    intro y
    refine (smul_lv_iff (A.setting hfin pm hpm).ι (phiG0 A hfin pm hpm (innHom A hgen E) y)).trans
      ?_
    refine (mem_range_φ2_iff A hfin pm hpm (innHom A hgen E y)).trans ?_
    rw [innHom_coe]
    exact ⟨fun h => (conj_mem_autStab_iff E hP2 hc2 y).mp h.2,
      fun h => ⟨A.inn_le ⟨_, rfl⟩, (conj_mem_autStab_iff E hP2 hc2 y).mpr h⟩⟩
  refine ⟨?_, ?_, ?_, fun y => (hs1 y).trans (s1 y).symm, fun y => (hs2 y).trans (s2 y).symm,
    disj, noadj1, noadj2, adj12⟩
  · intro a b h
    exact hΦinj (congrArg Subtype.val h)
  · ext g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := (hΦr g.1).mpr hg
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact (hΦr _).mp ⟨x, rfl⟩
  · intro g
    have : ((MulAut.conj : D →* MulAut D).range).Normal := innRange_normal
    obtain ⟨gk, hgk⟩ : ∃ gk : ↥A.K, gk = g.1 := ⟨g.1, rfl⟩
    have hg : (gk : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range ⊔ (A.N1 ⊓ A.N2) :=
      LieAmalgamExt.K_le_inn_sup A gk.2
    obtain ⟨n, ⟨d, rfl⟩, b, hb, hnb⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hbK : b ∈ A.K := A.N1_le_K hb.1
    have hmem : (⟨b, hbK⟩ : ↥A.K) ∈ (A.setting hfin pm hpm).ι.φ1.range ⊔
        (A.setting hfin pm hpm).ι.φ2.range := by
      rw [(A.setting hfin pm hpm).ι.gen]
      exact Subgroup.mem_top _
    refine ⟨E d, ⟨⟨b, hbK⟩, hmem⟩, ?_, ?_, ?_⟩
    · exact (smul_xv_iff (A.setting hfin pm hpm).ι ⟨⟨b, hbK⟩, hmem⟩).mpr
        ((mem_range_φ1_iff A hfin pm hpm ⟨b, hbK⟩).mpr hb.1)
    · exact (smul_lv_iff (A.setting hfin pm hpm).ι ⟨⟨b, hbK⟩, hmem⟩).mpr
        ((mem_range_φ2_iff A hfin pm hpm ⟨b, hbK⟩).mpr hb.2)
    · apply Subtype.ext
      apply Subtype.ext
      have h1 : (gk : MulAut D) = (innHom A hgen E (E d) : MulAut D) * b := by
        rw [innHom_coe, E.symm_apply_apply, hnb]
      rw [hgk] at h1
      exact h1

end Datum

end CFSG.Quasithin.H13.F431.F45
