module

public import CFSG.Quasithin.H13.AS91Sec4Setting
public import CFSG.LargeExtraspecial.SettingRhoM
public import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel

public section

namespace CFSG.Quasithin.H13.J4

theorem IsAutTripleM22.exists_of_normal_card_three
    {X : Type*} [Group X] [Finite X] (h : IsAutTripleM22 X)
    {Y : Subgroup X} (hYn : Y.Normal) (hYcard : Nat.card Y = 3) :
    ∃ (D : Subgroup X) (ψ : D →* M22), D.index = 2 ∧ Function.Surjective ψ ∧
      (∀ d : D, ψ d = 1 ↔ (d : X) ∈ Y) ∧
      (∀ g : X, (∀ y ∈ Y, g * y * g⁻¹ = y) → g ∈ D) ∧ Y ≤ D := by
  obtain ⟨Z, -, hZcard, hDindex, -, -, -, ψ, -, hψsurj, hψker, -, -, -, -⟩ := h
  haveI : (Subgroup.centralizer (Z : Set X)).Normal :=
    Subgroup.normal_of_index_eq_two hDindex
  have hYleD : Y ≤ Subgroup.centralizer (Z : Set X) := by
    intro y hy
    have hdvd : orderOf y ∣ 3 := by
      rw [← hYcard]
      exact Subgroup.orderOf_dvd_natCard Y hy
    have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat (by decide : Odd 3) hdvd
    exact CFSG.QuasiDihedralFusion.le_of_odd_of_two_pow_index _
      ⟨1, by rw [hDindex, pow_one]⟩ (Subgroup.zpowers y) hodd (Subgroup.mem_zpowers y)
  let I : Subgroup M22 := (Y.subgroupOf (Subgroup.centralizer (Z : Set X))).map ψ
  have hIcard : Nat.card I ∣ 3 := by
    change Nat.card ↥((Y.subgroupOf (Subgroup.centralizer (Z : Set X))).map ψ) ∣ 3
    have h1 := Subgroup.card_map_dvd (Y.subgroupOf (Subgroup.centralizer (Z : Set X))) ψ
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleD).toEquiv, hYcard] at h1
  have hInormal : I.Normal :=
    (hYn.subgroupOf (Subgroup.centralizer (Z : Set X))).map ψ hψsurj
  haveI : I.Normal := hInormal
  have hIbot : I = ⊥ := by
    rcases (CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2).eq_bot_or_eq_top_of_normal I with h | h
    · exact h
    · exfalso
      have hle : Nat.card I ≤ 3 := Nat.le_of_dvd (by norm_num) hIcard
      rw [h, Subgroup.card_top, CFSG.Sporadic.Mathieu.card_M22] at hle
      norm_num at hle
  have hYleZ : Y ≤ Z := by
    have hker : Y.subgroupOf (Subgroup.centralizer (Z : Set X)) ≤ ψ.ker :=
      (Subgroup.map_eq_bot_iff (f := ψ)
        (Y.subgroupOf (Subgroup.centralizer (Z : Set X)))).mp (by simpa [I] using hIbot)
    rw [hψker] at hker
    intro y hy
    have hyD : y ∈ Subgroup.centralizer (Z : Set X) := hYleD hy
    have hy' : (⟨y, hyD⟩ : Subgroup.centralizer (Z : Set X)) ∈
        Y.subgroupOf (Subgroup.centralizer (Z : Set X)) :=
      Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_subgroupOf.mp (hker hy')
  have hYZ : Y = Z := by
    refine Subgroup.eq_of_le_of_card_ge hYleZ ?_
    rw [hZcard, hYcard]
  subst Z
  refine ⟨Subgroup.centralizer (Y : Set X), ψ, hDindex, hψsurj, ?_, ?_, hYleD⟩
  · intro d
    rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : g * y * g⁻¹ = y := hg y hy
    calc y * g = (g * y * g⁻¹) * g := by rw [h1]
      _ = g * y := by group
end CFSG.Quasithin.H13.J4

namespace CFSG.Quasithin.H13.AS91
open Subgroup CFSG.Open CFSG.LargeExtraspecial

theorem exists_normal_card_three_of_sup {G : Type} [Group G] [Finite G] (S : Setting G)
    (X : Subgroup G) (hX : X ≤ S.M) (hXcard : Nat.card X = 3) (hwidth : S.width = 6)
    (hQX : ∀ h ∈ S.M, ∀ y ∈ S.QG ⊔ X, h * y * h⁻¹ ∈ S.QG ⊔ X) :
    ∃ Xbar : Subgroup S.Mbar, Xbar.Normal ∧ Nat.card Xbar = 3 ∧
      Xbar = (X.subgroupOf S.M).map S.ρM ∧
      Xbar.comap S.ρM = S.Q ⊔ X.subgroupOf S.M := by
  classical
  let X' : Subgroup S.M := X.subgroupOf S.M
  let Xbar : Subgroup S.Mbar := X'.map S.ρM
  have hX'card : Nat.card X' = 3 := by
    rw [← hXcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hQcard : Nat.card S.Q = 2 ^ 13 := by
    rw [S.card_Q_eq, hwidth]
  have hX'Q : X' ⊓ S.Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    have hord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard X' hx.1
        rwa [hX'card] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxne
      · exact h
    have hdvdQ : 3 ∣ Nat.card S.Q := by
      have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.2)
      rwa [Nat.card_zpowers, hord] at h
    rw [hQcard] at hdvdQ
    norm_num at hdvdQ
  let fX : X' →* S.Mbar := S.ρM.comp X'.subtype
  have hfXker : fX.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxQ : (x : S.M) ∈ S.Q := by
      refine S.mem_Q_of_ρ_eq_one ?_
      exact congrArg Subtype.val hx
    exact Subtype.ext (Subgroup.mem_bot.mp (hX'Q ▸ Subgroup.mem_inf.mpr ⟨x.2, hxQ⟩))
  have hfXrange : fX.range = Xbar := by
    change (S.ρM.comp X'.subtype).range = Xbar
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hXbar_card : Nat.card Xbar = 3 := by
    have h := Subgroup.card_ker_mul_card_range fX
    rw [hfXker, Subgroup.card_bot, one_mul, hfXrange, hX'card] at h
    exact h
  have hsup_map : (S.Q ⊔ X').map S.M.subtype = S.QG ⊔ X := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hX]
    rfl
  have hXbar_normal : Xbar.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm⟩ := S.ρM_surjective g
    rw [← hm]
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    have hx0G : (x0 : G) ∈ X := Subgroup.mem_subgroupOf.mp hx0
    have hy : (m * x0 * m⁻¹ : S.M) ∈ S.Q ⊔ X' := by
      rw [← Subgroup.mem_map_iff_mem S.M.subtype_injective, hsup_map]
      exact hQX (m : G) m.2 (x0 : G) (Subgroup.mem_sup_right hx0G)
    haveI : S.Q.Normal := S.normal
    obtain ⟨q, hq, x1, hx1, hqx⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hq1 : S.ρM q = 1 := Subtype.ext (S.ρ_eq_one_of_mem_Q hq)
    have hmul : S.ρM m * S.ρM x0 * (S.ρM m)⁻¹ = S.ρM (m * x0 * m⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hmul, ← hqx, map_mul, hq1, one_mul]
    exact Subgroup.mem_map.mpr ⟨x1, hx1, rfl⟩
  have hpre : Xbar.comap S.ρM = S.Q ⊔ X' := by
    change ((X'.map S.ρM).comap S.ρM) = _
    rw [Subgroup.comap_map_eq, S.ker_ρM, sup_comm]
  exact ⟨Xbar, hXbar_normal, hXbar_card, rfl, hpre⟩

theorem mem_of_commutes_of_setting {G : Type} [Group G] [Finite G] {z : G} (S : Setting G)
    (hSM : S.M = H z) (hSQG : S.QG = Q z) (d : Loc41 G z)
    {Xbar D : Subgroup S.Mbar} (hXbar_eq : Xbar = (d.X.subgroupOf S.M).map S.ρM)
    (hDcomm : ∀ g : S.Mbar, (∀ y ∈ Xbar, g * y * g⁻¹ = y) → g ∈ D) :
    ∀ h ∈ H z, (∀ x ∈ d.X, h * x * h⁻¹ * x⁻¹ ∈ Q z) →
      h ∈ (D.comap S.ρM).map S.M.subtype := by
  intro h hh hcomm
  have hhS : h ∈ S.M := hSM.symm ▸ hh
  let hS : S.M := ⟨h, hhS⟩
  have hmemD : S.ρM hS ∈ D := by
    apply hDcomm
    intro z hz
    rw [hXbar_eq] at hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hxG : (x : G) ∈ d.X := Subgroup.mem_subgroupOf.mp hx
    have hqG : h * (x : G) * h⁻¹ * (x : G)⁻¹ ∈ Q z := hcomm (x : G) hxG
    let qS : S.M := ⟨h * (x : G) * h⁻¹ * (x : G)⁻¹,
      S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hhS x.2) (S.M.inv_mem hhS)) (S.M.inv_mem x.2)⟩
    have hqS : qS ∈ S.Q := by
      have hqQG : (qS : G) ∈ S.QG := by rwa [hSQG]
      exact (S.mem_QG_iff.mp hqQG).2
    have hρq : S.ρM qS = 1 := Subtype.ext (S.ρ_eq_one_of_mem_Q hqS)
    have hconj : hS * x * hS⁻¹ = qS * x := by
      apply Subtype.ext
      change (h : G) * (x : G) * (h : G)⁻¹ =
        (h * (x : G) * h⁻¹ * (x : G)⁻¹) * (x : G)
      group
    calc S.ρM hS * S.ρM x * (S.ρM hS)⁻¹
        = S.ρM (hS * x * hS⁻¹) := by simp only [map_mul, map_inv]
      _ = S.ρM (qS * x) := by rw [hconj]
      _ = S.ρM qS * S.ρM x := map_mul ..
      _ = S.ρM x := by rw [hρq, one_mul]
  exact Subgroup.mem_map.mpr ⟨hS, Subgroup.mem_comap.mpr hmemD, rfl⟩

theorem mem_of_odd_of_setting {G : Type} [Group G] [Finite G] {z : G}
    {N : Subgroup G} (hNrel : N.relIndex (H z) = 2) :
    ∀ h ∈ H z, Odd (orderOf h) → h ∈ N := by
  intro h hh hodd
  have hsubidx : (N.subgroupOf (H z)).index = 2 := by
    simpa [Subgroup.relIndex] using hNrel
  haveI : (N.subgroupOf (H z)).Normal := Subgroup.normal_of_index_eq_two hsubidx
  have hoddH : Odd (Nat.card (Subgroup.zpowers (⟨h, hh⟩ : H z))) := by
    rw [Nat.card_zpowers]
    simpa using hodd
  exact Subgroup.mem_subgroupOf.mp
    (CFSG.QuasiDihedralFusion.le_of_odd_of_two_pow_index (N.subgroupOf (H z))
      ⟨1, by rw [hsubidx, pow_one]⟩ (Subgroup.zpowers (⟨h, hh⟩ : H z)) hoddH
      (Subgroup.mem_zpowers _))

theorem Loc41.exists_linear_M22_of_setting
    {G : Type} [Group G] [Finite G] {z : G} (S : Setting G)
    (hSM : S.M = H z) (hSQG : S.QG = Q z) (hSwidth : S.width = 6)
    (hautTriple : J4.IsAutTripleM22 S.Mbar) (d : Loc41 G z) :
    ∃ (N : Subgroup G) (π : ↥N →* J4.M22), N ≤ H z ∧ Q z ⊔ d.X ≤ N ∧
      N.relIndex (H z) = 2 ∧ Function.Surjective π ∧
      (∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ d.X) ∧
      (∀ h ∈ H z, (∀ x ∈ d.X, h * x * h⁻¹ * x⁻¹ ∈ Q z) → h ∈ N) ∧
      (∀ h ∈ H z, Odd (orderOf h) → h ∈ N) := by
  classical
  have hQX : ∀ h ∈ S.M, ∀ y ∈ S.QG ⊔ d.X, h * y * h⁻¹ ∈ S.QG ⊔ d.X := by
    intro h hh y hy
    have hy' : y ∈ Q z ⊔ d.X := by rwa [hSQG] at hy
    have hh' : h ∈ H z := by rwa [hSM] at hh
    have := d.QX_normal h hh' y hy'
    rwa [hSQG]
  obtain ⟨Xbar, hXbar_normal, hXbar_card, hXbar_eq, hpreY⟩ :=
    exists_normal_card_three_of_sup S d.X (by rw [hSM]; exact d.X_le) d.card_X hSwidth hQX
  haveI : Finite S.Mbar := Bridge.finite_Mbar S
  obtain ⟨D, ψ, hDindex, hψsurj, hψker, hDcomm, hYleD⟩ :=
    J4.IsAutTripleM22.exists_of_normal_card_three hautTriple hXbar_normal hXbar_card
  let M0 : Subgroup S.M := D.comap S.ρM
  let π₀ : ↥M0 →* J4.M22 := ψ.comp (S.ρM.subgroupComap D)
  have hπ₀surj : Function.Surjective π₀ :=
    hψsurj.comp (S.ρM.subgroupComap_surjective D S.ρM_surjective)
  have hM0index : M0.index = 2 := by
    rw [Subgroup.index_comap_of_surjective (H := D) S.ρM_surjective, hDindex]
  let N : Subgroup G := M0.map S.M.subtype
  let eN : ↥M0 ≃* ↥N := Subgroup.equivMapOfInjective M0 S.M.subtype S.M.subtype_injective
  let π : ↥N →* J4.M22 := π₀.comp eN.symm.toMonoidHom
  have hN_le_H : N ≤ H z := by
    rintro _ ⟨m, -, rfl⟩; rw [← hSM]; exact m.2
  have hNrel : N.relIndex (H z) = 2 := by
    have htop : (⊤ : Subgroup S.M).map S.M.subtype = S.M := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hSM, ← htop, Subgroup.relIndex_map_map_of_injective M0 ⊤ S.M.subtype_injective,
      Subgroup.relIndex_top_right, hM0index]
  have hsup_map : (S.Q ⊔ d.X.subgroupOf S.M).map S.M.subtype = Q z ⊔ d.X := by
    rw [Subgroup.map_sup, show S.Q.map S.M.subtype = Q z from hSQG,
      Subgroup.map_subgroupOf_eq_of_le (by rw [hSM]; exact d.X_le)]
  have hQX_le_N : Q z ⊔ d.X ≤ N := by
    apply sup_le
    · intro x hx
      have hx' : x ∈ S.QG := by rwa [hSQG]
      obtain ⟨hxM, hxQ⟩ := S.mem_QG_iff.mp hx'
      refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap,
        show S.ρM ⟨x, hxM⟩ = 1 from Subtype.ext (S.ρ_eq_one_of_mem_Q hxQ)]
      exact D.one_mem
    · intro x hx
      have hxM : x ∈ S.M := hSM.symm ▸ d.X_le hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      apply hYleD
      rw [hXbar_eq]
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hπ_surj : Function.Surjective π := hπ₀surj.comp eN.symm.surjective
  have hπ_ker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ d.X := by
    intro n
    let m : M0 := eN.symm n
    have hmn : ((m : S.M) : G) = (n : G) := by
      have h1 : eN m = n := eN.apply_symm_apply n
      calc ((m : S.M) : G) = ((eN m : ↥N) : G) := rfl
        _ = (n : G) := congrArg (fun x : ↥N => (x : G)) h1
    have h1 : π n = 1 ↔ ψ ⟨S.ρM (m : S.M), m.2⟩ = 1 := by
      exact Iff.rfl
    have h2 : ψ ⟨S.ρM (m : S.M), m.2⟩ = 1 ↔ S.ρM (m : S.M) ∈ Xbar :=
      hψker ⟨S.ρM (m : S.M), m.2⟩
    have h3 : S.ρM (m : S.M) ∈ Xbar ↔
        (m : S.M) ∈ S.Q ⊔ d.X.subgroupOf S.M := by
      rw [← hpreY, Subgroup.mem_comap]
    have h4 : (m : S.M) ∈ S.Q ⊔ d.X.subgroupOf S.M ↔
        ((m : S.M) : G) ∈ Q z ⊔ d.X := by
      rw [← Subgroup.mem_map_iff_mem S.M.subtype_injective, hsup_map]
      rfl
    rw [h1, h2, h3, h4, hmn]
  exact ⟨N, π, hN_le_H, hQX_le_N, hNrel, hπ_surj, hπ_ker,
    mem_of_commutes_of_setting S hSM hSQG d hXbar_eq hDcomm,
    mem_of_odd_of_setting hNrel⟩

theorem Loc41.exists_linear_M22 {G : Type} [Group G] [Finite G]
    {z : G} (hJ : HypJ4 G z) (d : Loc41 G z) :
    ∃ (N : Subgroup G) (π : ↥N →* J4.M22), N ≤ H z ∧ Q z ⊔ d.X ≤ N ∧
      N.relIndex (H z) = 2 ∧ Function.Surjective π ∧
      (∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ d.X) ∧
      (∀ h ∈ H z, (∀ x ∈ d.X, h * x * h⁻¹ * x⁻¹ ∈ Q z) → h ∈ N) ∧
      (∀ h ∈ H z, Odd (orderOf h) → h ∈ N) :=
  Loc41.exists_linear_M22_of_setting hJ.setting hJ.setting_M hJ.setting_QG hJ.setting_width
    hJ.autTriple_Mbar d
end CFSG.Quasithin.H13.AS91