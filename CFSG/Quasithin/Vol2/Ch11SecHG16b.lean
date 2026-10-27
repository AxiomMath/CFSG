module

public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Vol2.Ch11SecHG16
public import CFSG.Quasithin.Vol2.Ch11SecHSchur2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_fixV_autOn_iff {X P : Subgroup G} [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (u : ↥P) :
    u ∈ fixV (autOn X P) ↔ (u : G) ∈ Subgroup.centralizer (X : Set G) :=
  CFSG.Quasithin.AutOn.mem_fixV_autOn_iff hXP u

variable [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem card_autOn_V_P (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    Nat.card (autOn (fsuV T I) (pOf T I H h)) = 2 ^ n := by
  have hVN := d.fsuV_le_normalizer_P i
  have h1 := Nat.card_congr (SecC.autOnEquiv (fsuV T I) (pOf T I H h) hVN).toEquiv
  rw [SecC.ker_autOnHom] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (fsuV T I))
  rw [← h1] at h2
  have h3 : Nat.card ((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (fsuV T I)) =
      Nat.card (bOf T I H) := by
    rw [← Subgroup.inf_subgroupOf_left, d.fsuV_inf_centralizer_P i hF hπ]
    exact card_B_subgroupOf T I H
  rw [h3, d.card_fsuV] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2.symm

theorem sylow_autOn_V_P (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    QuasithinUnique.IsSylowTwoOf (autOn (fsuV T I) (pOf T I H h))
      (autOn (oTwoUpper H) (pOf T I H h)) := by
  obtain ⟨F', _, _, hF', ⟨e⟩⟩ := d.gm_equiv i (d.B_ne_bot_sl3 hF hπ)
  have hp : IsPGroup 2 ↥(autOn (fsuV T I) (pOf T I H h)) :=
    ((SecA.isPGroup_fsuV d.c.s.hyp).comap_of_injective _
      (Subgroup.normalizer (pOf T I H h : Set G)).subtype_injective).map _
  exact isSylowTwoOf_of_card (by have := d.c.two_le; omega) hF' e (d.autOn_V_le_autOn_K i) hp
    (d.card_autOn_V_P i hF hπ)

theorem exists_two_natural (i : Inp32) [IsMulCommutative ↥(fsuV T I)]
    [IsMulCommutative ↥(pOf T I H h)] {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    ∃ W₀ W₁ : Subgroup ↥(pOf T I H h), W₀ ⊓ W₁ = ⊥ ∧
      BinaryNaturalSL (autOn (oTwoUpper H) (pOf T I H h)) W₀ ⊥ 2 n ∧
      BinaryNaturalSL (autOn (oTwoUpper H) (pOf T I H h)) W₁ ⊥ 2 n := by
  have hB := d.B_ne_bot_sl3 hF hπ
  obtain ⟨F', _, _, hF', ⟨e⟩⟩ := d.gm_equiv i hB
  have hPab := d.isElemAbelian_P i
  have hsq : ∀ u : ↥(pOf T I H h), u ^ 2 = 1 := fun u =>
    Subtype.ext (by simpa using hPab.2 u u.2)
  have hVP := d.fsuV_le_normalizer_P i
  have hKP := d.K_le_normalizer_P i
  have hfixR : ∀ u : ↥(pOf T I H h), u ∈ fixV (autOn (fsuV T I) (pOf T I H h)) ↔
      (u : G) ∈ bOf T I H := by
    intro u
    rw [mem_fixV_autOn_iff hVP, ← d.P_inf_centralizer_V i]
    exact ⟨fun hu => ⟨u.2, hu⟩, fun hu => hu.2⟩
  have hgen : (⨆ x ∈ autOn (oTwoUpper H) (pOf T I H h),
      (fixV (autOn (fsuV T I) (pOf T I H h))).map (x : MulAut ↥(pOf T I H h)).toMonoidHom) =
        ⊤ := by
    rw [eq_top_iff]
    rintro u -
    obtain ⟨b, hb, b', hb', hu⟩ := (d.mem_P_iff i).mp u.2
    obtain ⟨k, hk, t, ht, hkt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
      (d.c.s.T_le.trans (le_normalizer_oTwoUpper H))).mp (d.c.s.sup_eq.ge (H.inv_mem d.c.hH))
    have hb₁ : h * b' * h⁻¹ ∈ bOf T I H := mem_conjSubgroup_iff.mp hb'
    have hb₀ : t * (h * b' * h⁻¹) * t⁻¹ ∈ bOf T I H := by
      rw [d.bOf_eq i] at hb₁ ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp (SecA.T_le_normalizer_fsuV T I ht) _).mp hb₁.1,
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (d.c.s.T_le ht)) _).mp hb₁.2⟩
    have hb'eq : b' = k * (t * (h * b' * h⁻¹) * t⁻¹) * k⁻¹ := by
      have : k * (t * (h * b' * h⁻¹) * t⁻¹) * k⁻¹ = (k * t) * (h * b' * h⁻¹) * (k * t)⁻¹ := by
        group
      rw [this, ← hkt]
      group
    have hkN := hKP hk
    have hkGm : conjAct (pOf T I H h) ⟨k, hkN⟩ ∈ autOn (oTwoUpper H) (pOf T I H h) :=
      ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hbP : b ∈ pOf T I H h := Subgroup.mem_sup_left hb
    have hb₀P : t * (h * b' * h⁻¹) * t⁻¹ ∈ pOf T I H h := Subgroup.mem_sup_left hb₀
    have h1 : (⟨b, hbP⟩ : ↥(pOf T I H h)) ∈ (fixV (autOn (fsuV T I) (pOf T I H h))).map
        (1 : MulAut ↥(pOf T I H h)).toMonoidHom := ⟨⟨b, hbP⟩, (hfixR _).mpr hb, by simp⟩
    have h2 : conjAct (pOf T I H h) ⟨k, hkN⟩ ⟨_, hb₀P⟩ ∈
        (fixV (autOn (fsuV T I) (pOf T I H h))).map
          (conjAct (pOf T I H h) ⟨k, hkN⟩).toMonoidHom := ⟨⟨_, hb₀P⟩, (hfixR _).mpr hb₀, rfl⟩
    have hueq : u = ⟨b, hbP⟩ * conjAct (pOf T I H h) ⟨k, hkN⟩ ⟨_, hb₀P⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, conjAct_apply_coe, hu]
      exact congrArg (b * ·) hb'eq
    rw [hueq]
    exact Subgroup.mul_mem _
      (Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (Subgroup.one_mem _) h1))
      (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hkGm h2))
  have hfix : ∀ r ∈ autOn (fsuV T I) (pOf T I H h), r ≠ 1 →
      fixV (Subgroup.zpowers r) = fixV (autOn (fsuV T I) (pOf T I H h)) := by
    rintro _ ⟨z, hz, rfl⟩ hr
    have hvV := Subgroup.mem_subgroupOf.mp hz
    have hvB : (z : G) ∉ bOf T I H := by
      intro hvB
      apply hr
      refine (conjAct_eq_one_iff _ _).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact comm_of_isElemAbelian hPab hp (Subgroup.mem_sup_left hvB)
    ext u
    rw [hfixR]
    constructor
    · intro hu
      have h2 := congrArg Subtype.val (hu _ (Subgroup.mem_zpowers _))
      rw [conjAct_apply_coe] at h2
      exact d.mem_B_of_comm i hF hπ hvV hvB u.2 (by
        calc (z : G) * u = (z * u * (z : G)⁻¹) * z := by group
          _ = u * z := by rw [h2])
    · intro hu x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine zpow_apply_eq_of_apply_eq' ?_ k
      apply Subtype.ext
      rw [conjAct_apply_coe, comm_of_isElemAbelian (SecA.isElemAbelian_fsuV d.c.s.hyp) hvV
        ((inf_le_left : bOf T I H ≤ fsuV T I) hu), mul_inv_cancel_right]
  have hfixGm : fixV (autOn (oTwoUpper H) (pOf T I H h)) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [mem_fixV_autOn_iff hKP] at hu
    have : (u : G) ∈ pOf T I H h ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := ⟨u.2, hu⟩
    rw [d.P_inf_centralizer_K i, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  obtain ⟨s, W, -, hWind, hWtop, hWnat⟩ := i.hG16 ↥(pOf T I H h) hsq
    (autOn (oTwoUpper H) (pOf T I H h)) (autOn (fsuV T I) (pOf T I H h)) n
    (by have := d.c.two_le; omega) ⟨F', inferInstance, inferInstance, hF', ⟨e⟩⟩
    (d.sylow_autOn_V_P i hF hπ) hgen hfix
  rw [hfixGm] at hWind hWtop hWnat
  have hcardP : (2 ^ n) ^ 2 < Nat.card ↥(pOf T I H h) := by
    obtain ⟨b', hb', hb'1⟩ := exists_conj_ne_one hB h
    have hlt : bOf T I H < pOf T I H h := by
      refine lt_of_le_of_ne le_sup_left (fun heq => hb'1 ?_)
      have hb'B : b' ∈ bOf T I H := heq ▸ Subgroup.mem_sup_right hb'
      have : b' ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) h :=
        ⟨(inf_le_left : bOf T I H ≤ fsuV T I) hb'B, E3.conjSubgroup_mono_left _ inf_le_left hb'⟩
      rw [d.fsuV_inf_Vh i, Subgroup.mem_bot] at this
      exact this
    have := Subgroup.card_lt_of_lt hlt
    rwa [d.card_B_sl3 hF hπ] at this
  have hs : 2 ≤ s := by
    by_contra hs
    interval_cases s
    · have h0 : (⊤ : Subgroup ↥(pOf T I H h)) = ⊥ := by
        rw [← hWtop]
        simp
      have : Nat.card ↥(pOf T I H h) = 1 := by
        rw [← Subgroup.card_top (G := ↥(pOf T I H h)), h0, Subgroup.card_bot]
      have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    · have hW0 : W 0 = ⊤ := by simpa using hWtop
      obtain ⟨K₀, _, _, hK₀, π₀, hπ₀⟩ := hWnat 0
      have hc := G64.RealizesVia.card_eq hπ₀
      rw [G64.card_natMod, Subgroup.card_bot, mul_one, hK₀, hW0, Subgroup.card_top] at hc
      omega
  refine ⟨W ⟨0, by omega⟩, W ⟨1, by omega⟩, ?_, hWnat _, hWnat _⟩
  have h0 := hWind ⟨0, by omega⟩
  rw [bot_sup_eq] at h0
  rw [eq_bot_iff, ← h0]
  exact inf_le_inf_left _ (le_iSup₂_of_le (f := fun (j : Fin s) (_ : j ≠ ⟨0, by omega⟩) => W j)
    ⟨1, by omega⟩ (by simp [Fin.ext_iff]) le_rfl)

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
