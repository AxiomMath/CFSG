module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_conj_mem_H0 (hc : Ctx M Q Z B) {y h : G} (hy : y ∈ M) (hh : h ∈ H0 M Z) :
    y * h * y⁻¹ ∈ H0 M Z := by
  refine ⟨M.mul_mem (M.mul_mem hy hh.1) (M.inv_mem hy), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro z hz
  have hz' : y⁻¹ * z * y ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hy)) z).mp hz
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hh.2 (y⁻¹ * z * y) hz'
  calc z * (y * h * y⁻¹) = y * ((y⁻¹ * z * y) * h) * y⁻¹ := by group
    _ = y * (h * (y⁻¹ * z * y)) * y⁻¹ := by rw [h1]
    _ = y * h * y⁻¹ * z := by group

theorem sec8_normV_of_comm (hc : Ctx M Q Z B) {t x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) :
    x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hle : conjSubgroup x (Vt M (LB M Q B) B Z t) ≤ Vt M (LB M Q B) B Z t := by
    refine Subgroup.map_le_iff_le_comap.mpr (sec39_Vt_le (fun z hz => ?_) fun m hm htm y hy => ?_)
    · show x * z * x⁻¹ ∈ Vt M (LB M Q B) B Z t
      exact sec39_Z_le_Vt ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) z).mp hz)
    · show x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t
      have hxm : x * m ∈ M := M.mul_mem hxM hm
      have hq : x⁻¹ * ⁅x, t⁆⁻¹ * x ∈ Q := by
        have := hQn x⁻¹ (M.inv_mem hxM) _ (Q.inv_mem hxt)
        simpa using this
      have htxm : t ∈ conjSubgroup (x * m) (LB M Q B) := by
        rw [mem_conjSubgroup]
        have hq' : m⁻¹ * (x⁻¹ * ⁅x, t⁆⁻¹ * x) * m ∈ Q := by
          have := hQn m⁻¹ (M.inv_mem hm) _ hq
          simpa using this
        have e : (x * m)⁻¹ * t * (x * m) =
            (m⁻¹ * (x⁻¹ * ⁅x, t⁆⁻¹ * x) * m) * (m⁻¹ * t * m) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (LB M Q B).mul_mem (sec39_Q_le_LB hq') (mem_conjSubgroup.mp htm)
      have hmem : x * y * x⁻¹ ∈ conjSubgroup (x * m) B := by
        rw [mem_conjSubgroup]
        have e : (x * m)⁻¹ * (x * y * x⁻¹) * (x * m) = m⁻¹ * y * m := by group
        rw [e]
        exact mem_conjSubgroup.mp hy
      exact sec39_conjB_le_Vt hxm htxm hmem
  exact conjSubgroup_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]))

theorem sec8_conj_V_eq_Ut (hc : Ctx M Q Z B) {t : G}
    (hV : Vt M (LB M Q B) B Z t = Ut Q Z t) {g : G} (hg : g ∈ M) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * t * g⁻¹) := by
  rw [Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) t, hV]


theorem sec8_comm_mul_Q_mem_iff (hc : Ctx M Q Z B) {x q t : G} (hxM : x ∈ M) (htM : t ∈ M)
    (hq : q ∈ Q) : ⁅x * q, t⁆ ∈ Q ↔ ⁅x, t⁆ ∈ Q := by
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hqt : ⁅q, t⁆ ∈ Q := by
    have e : ⁅q, t⁆ = q * (t * q⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hq (hQn t htM _ (Q.inv_mem hq))
  have e : ⁅x * q, t⁆ = (x * ⁅q, t⁆ * x⁻¹) * ⁅x, t⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem_cancel_left (hQn x hxM _ hqt)

theorem step81Vanish_of (hCanon : Sec8CanonStatement) (hD' : Sec8DPrimeStatement)
    (hInv : Sec8InvolStatement) (h310chi : Stroth310ChiStatement) (h53 : Stroth53Statement) :
    Step81VanishStatement := by
  intro G _ _ M Q Z B hc n t hs r hr hna x hx hxt v hv
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs.toSec5 (Or.inl hs.spNat)).1
  obtain ⟨hxM, g, hg, hq⟩ := hx
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀ = g * t * g⁻¹ := ⟨_, rfl⟩
  have hx₀M : x₀ ∈ M := by
    rw [hx₀]
    exact M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hq' : x₀⁻¹ * x ∈ Q := by
    have h1 := hQn x₀⁻¹ (M.inv_mem hx₀M) _ hq
    rw [← hx₀] at h1
    have e : x₀⁻¹ * (x * x₀⁻¹) * x₀⁻¹⁻¹ = x₀⁻¹ * x := by group
    rwa [e] at h1
  have hxe : x = x₀ * (x₀⁻¹ * x) := by group
  have hx₀t : ⁅x₀, t⁆ ∈ Q := by
    have h1 := hxt
    rw [hxe] at h1
    exact (sec8_comm_mul_Q_mem_iff hc hx₀M htM hq').mp h1
  have hx₀Z : x₀ ∈ conjSubgroup g (Subgroup.zpowers t) := by
    rw [mem_conjSubgroup, hx₀]
    have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [e]
    exact Subgroup.mem_zpowers t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine le_inf sec39_Z_le_Vt ?_
    have h1 : conjSubgroup g Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono sec39_Z_le_Vt
    rwa [hc.conj_Z_eq hg] at h1
  by_cases hVV : Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)
  ·
    obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
    obtain ⟨h, hh, hsub⟩ := hD' G M Q Z B hc n t hs hna Z0 hZ0 g hg hVV
    have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
    have hx₀Z0 : x₀ ∈ conjSubgroup g Z0 := by
      rw [mem_conjSubgroup, hx₀]
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [e]
      exact htZ0
    have hx₀N : x₀ ∈ hc.CN t := (hsub hx₀Z0).2
    have hxN : x ∈ hc.CN t := by
      rw [hxe]
      exact (hc.CN t).mul_mem hx₀N (sec8_Q_le_CN hc ht hq')
    have hd := (h53.2.2.2.1 G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
      (conjSubgroup r B) (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t)
      (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl).1
    exact hd x hxN v hv
  ·
    have hVV' : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z := by
      by_contra hne
      exact hVV (lt_of_le_of_ne hZV (Ne.symm hne))
    have hxV : x₀ ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      sec8_normV_of_comm hc hx₀M hx₀t
    have hxV₁ : x₀ ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
      hCanon G M Q Z B hc n t hs r hr x₀ hx₀M hxV
    have hx₀H : x₀ ∈ H0 M Z := by
      rw [hx₀]
      exact sec8_conj_mem_H0 hc hg (hc.LB_le_H0 ht)
    have hx₀sq : x₀ ^ 2 ∈ Q := by
      have h1 := hQn g hg _ (hc.sq_mem_Q_of_mem_LB ht)
      have e : x₀ ^ 2 = g * t ^ 2 * g⁻¹ := by rw [hx₀, pow_two, pow_two]; group
      rwa [e]
    have hUt : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z x₀ := by
      rw [hx₀]
      exact sec8_conj_V_eq_Ut hc hV hg
    have hmemVg : ∀ w ∈ Q, ⁅x₀, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      intro w hw
      rw [hUt]
      have h1 : ⁅w, x₀⁆ ∈ ⁅Q, Subgroup.zpowers x₀⁆ :=
        Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers x₀)
      rw [← commutatorElement_inv]
      exact (Ut Q Z x₀).inv_mem (Subgroup.mem_sup_left h1)
    have hmemV : ∀ w ∈ Vt M (LB M Q B) B Z t, ⁅x₀, w⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro w hw
      have h1 := (Subgroup.mem_normalizer_iff.mp hxV w).mp hw
      have e : ⁅x₀, w⁆ = (x₀ * w * x₀⁻¹) * w⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem h1 ((Vt M (LB M Q B) B Z t).inv_mem hw)
    have hV0 : ∀ w ∈ Vt M (LB M Q B) B Z t, ⁅x₀, w⁆ ∈ Z := by
      intro w hw
      have h1 : ⁅x₀, w⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
        ⟨hmemV w hw, hmemVg w (hVQ hw)⟩
      rwa [hVV'] at h1
    have h2 := hInv G M Q Z B hc n t hs r hr x₀ hx₀H hx₀sq hxV₁ hV0 v hv
    have h3 : ⁅x₀, v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      ⟨h2, hmemVg v (hV1Q hv)⟩
    rw [hVV'] at h3
    rw [hxe]
    exact (comm_mul_Q_mem_Z_iff hc hx₀M hq' (hV1Q hv)).mpr h3


theorem sec8_conjMod_decomp (hc : Ctx M Q Z B) {t x : G} (htM : t ∈ M) (hx : ConjMod M Q t x) :
    ∃ g ∈ M, (g * t * g⁻¹)⁻¹ * x ∈ Q := by
  obtain ⟨-, g, hg, hq⟩ := hx
  refine ⟨g, hg, ?_⟩
  have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hx₀M)) _).mp hq
  have e : (g * t * g⁻¹)⁻¹ * (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹⁻¹ =
      (g * t * g⁻¹)⁻¹ * x := by group
  rwa [e] at h1

theorem sec8_conjMod_conj {t : G} (htM : t ∈ M) {g : G} (hg : g ∈ M) :
    ConjMod M Q t (g * t * g⁻¹) :=
  ⟨M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg), g, hg, by
    rw [mul_inv_cancel]
    exact Q.one_mem⟩

theorem step81Type_of (hCanon : Sec8CanonStatement) (hT : Sec8TypeCountStatement)
    (hV : Step81VanishStatement) : Step81TypeStatement := by
  intro G _ _ M Q Z B hc n t hs r hr hna hex
  obtain ⟨x, hx, hxt, w, hw, hxw⟩ := hex
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  obtain ⟨g, hg, hq'⟩ := sec8_conjMod_decomp hc htM hx
  have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hxe : x = (g * t * g⁻¹) * ((g * t * g⁻¹)⁻¹ * x) := by group
  have hx₀t : ⁅g * t * g⁻¹, t⁆ ∈ Q := by
    have h1 := hxt
    rw [hxe] at h1
    exact (sec8_comm_mul_Q_mem_iff hc hx₀M htM hq').mp h1
  have hvan := hV G M Q Z B hc n t hs r hr hna (g * t * g⁻¹) (sec8_conjMod_conj htM hg) hx₀t
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec39_Z_le_Vt.trans (le_inf le_sup_right le_sup_right)
  have hxV₁ : g * t * g⁻¹ ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    hCanon G M Q Z B hc n t hs r hr _ hx₀M (sec8_normV_of_comm hc hx₀M hx₀t)
  refine hT G M Q Z B hc n t hs r hr hna g hg hx₀t hxV₁ hvan ⟨w, hw, fun h => hxw ?_⟩
  rw [hxe]
  exact (comm_mul_Q_mem_iff hc hZV₁ hx₀M hq' hw.1).mpr h

theorem close81E_of (hD : Sec8LemmaDStatement) (hD' : Sec8DPrimeStatement)
    (hN : Sec8CommNStatement) : Close81EStatement := by
  intro G _ _ M Q Z B hc n t r h Z0 hZ0
  obtain ⟨hs, hr, hna, hcl⟩ := h
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hEN : Egen M Q Z0 ≤ hc.CN t := by
    unfold Egen
    refine iSup₂_le fun g hg => iSup_le fun hcond => ?_
    have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
    have hx₀Z0 : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [e]
      exact htZ0
    have hx₀t : ⁅g * t * g⁻¹, t⁆ ∈ Q := by
      have h1 := hcond t htZ0 _ hx₀Z0
      rw [← commutatorElement_inv]
      exact Q.inv_mem h1
    have hW := hcl _ (sec8_conjMod_conj htM hg) hx₀t
    obtain ⟨m, -, hmsp⟩ := hs.sp
    obtain ⟨hlt, -⟩ := hD G M Q Z B hc n t hs r hr m hmsp g hg hW
    obtain ⟨h', -, hsub⟩ := hD' G M Q Z B hc n t hs hna Z0 hZ0 g hg hlt
    exact fun y hy => (hsub hy).2
  exact (Subgroup.commutator_mono hEN hEN).trans (hN G M Q Z B hc n t hs Z0 hZ0)

end CFSG.RankThree.GF2n.Stroth80
