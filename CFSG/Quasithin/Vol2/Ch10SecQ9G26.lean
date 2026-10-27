module

public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecC9Irr
public import CFSG.Quasithin.Vol2.Ch10SecC9S4b
public import CFSG.Quasithin.Vol2.Ch10SecQ9G17

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def piJ {J : Subgroup G} {S : Type*} [Group S]
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S) : ↥J →* S :=
  eJ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))

omit [Finite G] in
theorem piJ_surjective {J : Subgroup G} {S : Type*} [Group S] (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S) :
    Function.Surjective (piJ eJ) :=
  eJ.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem piJ_eq_one {J : Subgroup G} {S : Type*} [Group S] (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S)
    (j : ↥J) : piJ eJ j = 1 ↔ j ∈ CFSG.pCore 2 ↥J := by
  rw [piJ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite G] in
theorem piJ_ker {J : Subgroup G} {S : Type*} [Group S] (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S)
    (j : ↥J) (hj : piJ eJ j = 1) : ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥J) ⟨j, (piJ_eq_one eJ j).mp hj⟩
  exact ⟨m, by simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥J) => ((x : ↥J) : G)) hm⟩

theorem exists_inner_of_aut {J L : Subgroup G} {S : Type*} [Group S]
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* S) (hLJ : L ≤ J)
    (hfact : ∀ α : MulAut S, (∀ x ∈ (piL (piJ eJ) hLJ).range, α x ∈ (piL (piJ eJ) hLJ).range) →
      ∃ g ∈ (piL (piJ eJ) hLJ).range, ∀ x ∈ (piL (piJ eJ) hLJ).range, α x = g * x * g⁻¹)
    {s : G} (hsJ : s ∈ Subgroup.normalizer (J : Set G))
    (hsL : s ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l₀ ∈ L, ∀ l ∈ L, s * l * s⁻¹ * (l₀ * l * l₀⁻¹)⁻¹ ∈ pCoreOf 2 L := by
  set π := piJ eJ with hπ
  set σ : MulAut ↥J := conjAct J ⟨s, hsJ⟩ with hσ
  have hσc : (CFSG.pCore 2 ↥J).map (σ : ↥J →* ↥J) = CFSG.pCore 2 ↥J :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  set q := QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥J) σ hσc with hq
  set α : MulAut S := (eJ.symm.trans q).trans eJ with hα
  have hαπ : ∀ j : ↥J, α (π j) = π (σ j) := by
    intro j
    rw [hα, hπ, piJ, MulEquiv.trans_apply, MulEquiv.trans_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, hq,
      QuotientGroup.congr_mk]
    rfl
  have hσl : ∀ l : ↥L, σ ⟨(l : G), hLJ l.2⟩ =
      ⟨s * l * s⁻¹, hLJ ((Subgroup.mem_normalizer_iff.mp hsL l).mp l.2)⟩ :=
    fun l => Subtype.ext (coe_conjAct_apply J ⟨s, hsJ⟩ ⟨(l : G), hLJ l.2⟩)
  have hαX : ∀ x ∈ (piL π hLJ).range, α x ∈ (piL π hLJ).range := by
    rintro _ ⟨l, rfl⟩
    refine ⟨⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsL l).mp l.2⟩, ?_⟩
    rw [piL_apply, piL_apply, hαπ, hσl]
  obtain ⟨g, ⟨l₀, rfl⟩, hg⟩ := hfact α hαX
  refine ⟨l₀, l₀.2, fun l hl => ?_⟩
  have h1 := hg (piL π hLJ ⟨l, hl⟩) ⟨⟨l, hl⟩, rfl⟩
  rw [piL_apply, hαπ, hσl] at h1
  simp only [piL_apply] at h1
  have h2 : π (⟨s * l * s⁻¹, hLJ ((Subgroup.mem_normalizer_iff.mp hsL l).mp hl)⟩ *
      (⟨(l₀ : G), hLJ l₀.2⟩ * ⟨l, hLJ hl⟩ * ⟨(l₀ : G), hLJ l₀.2⟩⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, h1]
    group
  rw [piJ_eq_one] at h2
  have hmem : s * l * s⁻¹ * ((l₀ : G) * l * (l₀ : G)⁻¹)⁻¹ ∈ L := by
    have h3 := (Subgroup.mem_normalizer_iff.mp hsL l).mp hl
    exact L.mul_mem h3 (L.inv_mem (L.mul_mem (L.mul_mem l₀.2 hl) (L.inv_mem l₀.2)))
  have hLO : L ⊓ pCoreOf 2 J ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf' (Subgroup.le_normalizer hx)
        ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (Subgroup.le_normalizer
          (hLJ hx)))) ?_
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_right
  refine hLO ⟨hmem, ?_⟩
  exact ⟨_, h2, rfl⟩

theorem Conf.Tw_eq_T1_of_flag {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {x : G}
    (hT1 : T1 T L ≤ Subgroup.centralizer ({x * w * x⁻¹} : Set G)) :
    T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTw
  set P := CFSG.conjugate (T1 T L) x with hP
  have hPC : P ≤ Subgroup.centralizer ({w} : Set G) := by
    intro p hp
    rw [hP, SecA.mem_conjugate_iff] at hp
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hT1 hp)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : x * (p * w) * x⁻¹ = x * (w * p) * x⁻¹ := by
      calc x * (p * w) * x⁻¹ = x * p * x⁻¹ * (x * w * x⁻¹) := by group
        _ = x * w * x⁻¹ * (x * p * x⁻¹) := h1
        _ = x * (w * p) * x⁻¹ := by group
    simpa using h2
  have hcard : Nat.card P = Nat.card (T1 T L) :=
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hP2 : IsPGroup 2 P :=
    (c.hyp.fsu.sylow.1.to_le inf_le_left).map (MulAut.conj x⁻¹).toMonoidHom
  obtain ⟨a, ha⟩ := hP2.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card Tw := by
    have h1 : Nat.card P ∣ Nat.card (Subgroup.centralizer ({w} : Set G)) :=
      Subgroup.card_dvd_of_le hPC
    have h2 := Subgroup.card_mul_index (Tw.subgroupOf (Subgroup.centralizer ({w} : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.sylow.1).toEquiv] at h2
    rw [← h2] at h1
    have hodd : Nat.Coprime (Nat.card P)
        (Tw.subgroupOf (Subgroup.centralizer ({w} : Set G))).index := by
      rw [ha]
      exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr c.sylow.2.2)
    exact hodd.dvd_of_dvd_mul_right h1
  have hle : Nat.card (T1 T L) ≤ Nat.card Tw := hcard ▸ Nat.le_of_dvd Nat.card_pos hdvd
  exact Subgroup.eq_of_le_of_card_ge (c.Tw_le_T1 h37 h38) hle

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
