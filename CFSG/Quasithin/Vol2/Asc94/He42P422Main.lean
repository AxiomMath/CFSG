module

public import CFSG.Quasithin.Vol2.Asc94.He42P422K
public import CFSG.Quasithin.Vol2.Asc94.He42SE8
public import CFSG.Quasithin.Recognition.M12AscEx166
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.A94
namespace He42

open Matrix Subgroup CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem card_of_alt_422 {X : Subgroup G}
    (h : Nonempty (↥X ≃* alternatingGroup (Fin 4)) ∨ Nonempty (↥X ≃* alternatingGroup (Fin 5))) :
    Nat.card ↥X = 12 ∨ Nat.card ↥X = 60 := by
  rcases h with h | h
  · left
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  · right
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide

theorem X_le_L1_422 (S : HeSetup G) {y₁ y₀ l₁ : G} (hy₀K : y₀ ∈ S.K)
    (hy₀y₁ : y₀ * y₁ = y₁ * y₀) (hy₀ord : orderOf y₀ = 3)
    (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hl₁L1 : l₁ ∈ S.L1) (hl₁K : l₁ ∉ S.K) (hl₁y : l₁ * y₁ = y₁ * l₁)
    (hX : Nonempty (↥(centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ≃*
        alternatingGroup (Fin 4)) ∨
      Nonempty (↥(centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ≃*
        alternatingGroup (Fin 5))) :
    centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) ≤ S.L1 := by
  have hB := S.baseFacts
  have hBA' : ∀ b ∈ S.B, b ∈ S.A' := fun b hb => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2
  have hRX : S.A' ⊓ centralizer ({y₁} : Set G) ≤
      centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) := by
    intro x hx
    obtain ⟨hxA', hxy⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxy,
      mem_centralizer_iff.mpr (fun b hb => hB.A'_comm b (hBA' b hb) x hxA')⟩
  have hRK : S.A' ⊓ centralizer ({y₁} : Set G) ≤ S.K := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨S.hD.hK.JN (le_sup_right (a := S.A) (b := S.A') (Subgroup.mem_inf.mp hx).1),
      (Subgroup.mem_inf.mp (hRX hx)).2⟩
  have hy₀X : y₀ ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hy₀y₁, (Subgroup.mem_inf.mp hy₀K).2⟩
  have hl₁X : l₁ ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hl₁y, mem_centralizer_iff.mpr
      (fun b hb => (mem_centralizer_iff.mp (hB.L1_le_centralizer hl₁L1) b hb))⟩
  let H : Subgroup G := (S.A' ⊓ centralizer ({y₁} : Set G)) ⊔ Subgroup.zpowers y₀
  have hHX : H ≤ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
    sup_le hRX (Subgroup.zpowers_le.mpr hy₀X)
  have hHK : H ≤ S.K := sup_le hRK (Subgroup.zpowers_le.mpr hy₀K)
  have hH4 : 4 ∣ Nat.card ↥H := by
    rw [← hR4]
    exact Subgroup.card_dvd_of_le (le_sup_left : S.A' ⊓ centralizer ({y₁} : Set G) ≤ H)
  have hH3 : 3 ∣ Nat.card ↥H := by
    have hmem : y₀ ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀)
    have h := orderOf_dvd_natCard (⟨y₀, hmem⟩ : ↥H)
    rwa [Subgroup.orderOf_mk, hy₀ord] at h
  have hH12 : 12 ∣ Nat.card ↥H := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) hH4 hH3
    simpa using h
  have hXc := card_of_alt_422 hX
  have hHM : H ≤ (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1 :=
    le_inf hHX (hHK.trans hB.K_le_L1)
  have hl₁M : l₁ ∈ (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1 :=
    Subgroup.mem_inf.mpr ⟨hl₁X, hl₁L1⟩
  have h12M : 12 ∣ Nat.card ↥((centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1) :=
    hH12.trans (Subgroup.card_dvd_of_le hHM)
  have hMX : Nat.card ↥((centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1) ∣
      Nat.card ↥(centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) :=
    Subgroup.card_dvd_of_le inf_le_left
  rcases hXc with hX12 | hX60
  ·
    exfalso
    have hHX12 : Nat.card ↥H ∣ 12 := by
      rw [← hX12]
      exact Subgroup.card_dvd_of_le hHX
    have heqH : Nat.card ↥H = 12 := Nat.dvd_antisymm hHX12 hH12
    have hHeq : H = centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
      Subgroup.eq_of_le_of_card_ge hHX (le_of_eq (by rw [heqH, hX12]))
    have hl₁H : l₁ ∈ H := by
      rw [hHeq]
      exact hl₁X
    exact hl₁K (hHK hl₁H)
  ·
    have key : ∀ m : ℕ, 12 ∣ m → m ∣ 60 → m = 12 ∨ m = 60 := by
      intro m h1 h2
      have hm : m ≤ 60 := Nat.le_of_dvd (by norm_num) h2
      obtain ⟨k, rfl⟩ := h1
      have hk : k ≤ 5 := by omega
      revert h2
      interval_cases k <;> decide
    have hMX60 : Nat.card ↥((centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1) ∣ 60 := by
      rw [← hX60]
      exact hMX
    rcases key _ h12M hMX60 with hm12 | hm60
    ·
      exfalso
      have hHM12 : Nat.card ↥H ∣ 12 := by
        rw [← hm12]
        exact Subgroup.card_dvd_of_le hHM
      have heqH : Nat.card ↥H = 12 := Nat.dvd_antisymm hHM12 hH12
      have hHMeq : H = (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1 :=
        Subgroup.eq_of_le_of_card_ge hHM (le_of_eq (by rw [heqH, hm12]))
      have hl₁H : l₁ ∈ H := by
        rw [hHMeq]
        exact hl₁M
      exact hl₁K (hHK hl₁H)
    · have hXM : (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1 =
          centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hm60, hX60]))
      intro x hx
      have hxM : x ∈ (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) ⊓ S.L1 := by
        rw [hXM]
        exact hx
      exact (Subgroup.mem_inf.mp hxM).2

theorem open422_of_setup
    (S : HeSetup G) {z : G} (hzZ : z ∈ S.Z) (hzB : z ∉ S.B)
    (hPz : IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer (S.B : Set G)))
    {y₁ y₂ : G} (hY : YSpec S y₁ y₂) : Open422 S y₁ y₂ := by
  have hB := S.baseFacts
  have hP := S.stepPsi hB
  have hn := S.stepYnorm hB hY
  have hf := S.stepYfpf hB hY
  have h0 := S.stepY0 hB hY
  have hR := S.stepR hB hY
  have hZm := S.stepZmat hB hY
  obtain ⟨hc, l₁, l₂, hW⟩ := S.exists_wspec hB hP hY hn hf h0
  have hSp := S.stepSpread hB hP hY hn h0 hR hZm hc
  have hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4 := hR.1.1
  have hRA : S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥ := hR.1.2
  have hSp2 := hSp.2
  have hy₁ord : orderOf y₁ = 3 := hY.ord₁
  have hy0K : y₁ * y₂⁻¹ ∈ S.K := h0.1
  have hy0ord : orderOf (y₁ * y₂⁻¹) = 3 := h0.2.2
  have hy₀N : y₁ * y₂⁻¹ ∈ S.N := hB.K_le_N hy0K
  have hcomm' : y₂⁻¹ * y₁ = y₁ * y₂⁻¹ := by
    calc y₂⁻¹ * y₁ = y₂⁻¹ * (y₁ * y₂) * y₂⁻¹ := by group
      _ = y₂⁻¹ * (y₂ * y₁) * y₂⁻¹ := by rw [hY.comm]
      _ = y₁ * y₂⁻¹ := by group
  have hy₀y₁ : (y₁ * y₂⁻¹) * y₁ = y₁ * (y₁ * y₂⁻¹) := by rw [mul_assoc, hcomm']
  have hy₀B : ∀ b ∈ S.B, b * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * b :=
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy0K).2
  have hy₀3 : (y₁ * y₂⁻¹) * (y₁ * y₂⁻¹) * (y₁ * y₂⁻¹) = 1 := by
    have h := pow_orderOf_eq_one (y₁ * y₂⁻¹)
    rw [hy0ord] at h
    exact (pow_three' _).symm.trans h
  have hl₁L1 : l₁ ∈ S.L1 := hW.mem₁
  have hl₁K : l₁ ∉ S.K := hW.nmem₁
  have hl₁y : l₁ * y₁ = y₁ * l₁ := hW.cent₁
  have hRnt : Nontrivial ↥(S.A' ⊓ centralizer ({y₁} : Set G)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hR4]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥(S.A' ⊓ centralizer ({y₁} : Set G)))
  have hτR : (t : G) ∈ S.A' ⊓ centralizer ({y₁} : Set G) := t.2
  have hτ1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  have hτA' : (t : G) ∈ S.A' := (Subgroup.mem_inf.mp hτR).1
  have hτB : (t : G) ∉ S.B := by
    intro hτB
    have hτA : (t : G) ∈ S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) :=
      ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hτB).1).1, hτR⟩
    rw [hRA, Subgroup.mem_bot] at hτA
    exact hτ1 hτA
  obtain ⟨g, hg, hτE⟩ := S.covering_422 hSp2 hτA' hτB
  have hJ : ∀ c : G, (∀ w ∈ S.Z, w * c = c * w) → c ∈ S.J :=
    fun c hc => S.centralizer_Z_le_J_422 hzZ hPz c hc
  have h2 : (S.rhoG y₁).2 = 1 := by rw [hY.rho₁]
  have hc1 : Commute (S.rhoG y₁).1 S.g := by
    rw [hY.rho₁]
  have hRE := S.R_le_conjZ_422 hZm hY.mem₁ h2 hc1 hSp2 hJ hy₁ord hR4 hRA hg hτR hτ1 hτE
  have hzE : g * z * g⁻¹ ∈ S.conjZ_422 g := (HeSetup.mem_conjZ_422 S).mpr ⟨z, hzZ, rfl⟩
  obtain ⟨r, hrR, β, hβ, hrβ⟩ := S.factor_R_B_422 hg hR4 hRA hRE hzE
  have hgb : β * g = g * β := mem_centralizer_iff.mp (hB.L2_le_centralizer hg) β hβ
  have hr1 : r ≠ 1 := by
    intro hr
    apply hzB
    rw [hr, one_mul] at hrβ
    have hzβ : z = β := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * β * g := by rw [hrβ]
        _ = g⁻¹ * (β * g) := by group
        _ = g⁻¹ * (g * β) := by rw [hgb]
        _ = β := by group
    rw [hzβ]
    exact hβ
  have hrE : r ∈ S.conjZ_422 g := hRE hrR
  have hrB : r ∉ S.B := by
    intro hrB
    have hrA : r ∈ S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) :=
      ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hrB).1).1, hrR⟩
    rw [hRA, Subgroup.mem_bot] at hrA
    exact hr1 hrA
  have hry : y₁ * r = r * y₁ :=
    (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hrR).2).symm
  obtain ⟨hyN, hyord⟩ := S.y_conj_N_422 hZm hY.mem₁ h2 hc1 hSp2 hJ hy₁ord hg hrE hrB hry
  have hcentr := S.cent_R_422 hyN hyord hg hzZ hPz hrβ hβ hrR hR4
  have hk := S.kleinCore_422 hy₀N hy₀y₁ hy₀B hy₀3 hy0ord hRA hR4 hrR hr1 hcentr
  have hX := exists_alt_equiv_of_kleinCore hk
  have hXL1 := X_le_L1_422 S hy0K hy₀y₁ hy0ord hR4 hl₁L1 hl₁K hl₁y hX
  intro c hcy1 _ hcB
  exact hXL1 (Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hcy1,
    mem_centralizer_iff.mpr (fun b hb => (hcB b hb).symm)⟩)

end He42

open Subgroup CFSG.CGT.M24S CFSG.Open in
theorem he42Input422_holds :
    ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
      IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
      ∀ (S : Setting G z e) (h1 : normalizer (tr e L52.U1 : Set G) = Cz z)
        (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a x : G)
        (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
        (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
        (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3) (y₁ y₂ : G),
        He42.YSpec (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁ y₂ →
          He42.Open422 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁ y₂ := by
  intro hF6 G _ _ z e hs hK S h1 h2 a x ha ham hxN hxa hx3 y₁ y₂ hY
  obtain ⟨hzZ, hzB, -⟩ := z_facts_426 e hF6 S h1 h2 ha ham hxN hxa hx3
  exact He42.open422_of_setup _ hzZ hzB (isPGroup_cent_z_B e hF6 S h1 h2 ha ham hxN hxa hx3) hY

end CFSG.Quasithin.A94
