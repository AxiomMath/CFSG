module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442H
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442C
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section CaseD


variable {G : Type} [Group G] [Finite G] {X Y V U R K P : Subgroup G} {z t : G}

theorem Loc442UCore.false_of_lt (D : Loc442UCore X Y V U R K P z t) {W : Subgroup G}
    (htW : t ∈ W) (hWU : W < U) (hlt : nS X W < nS Y W)
    (hmax : ∀ W', Qual X Y U t W' → W ≤ W' → W' ≤ W) : False := by
  have hWU' : W ≤ U := hWU.le
  have hUX : U ≤ X := D.U_V.trans D.V_X
  have hWX : W ≤ X := hWU'.trans hUX
  have hWY : W ≤ Y := hWX.trans D.XY
  have : (W.subgroupOf (nS Y W)).Normal := normal_subgroupOf_nS hWY
  have hUN : U ≤ nS Y W := le_nS_of_comm (hUX.trans D.XY) fun a ha w hw =>
    D.V_ab a (D.U_V ha) w (D.U_V (hWU' hw))
  have hRN : R ≤ nS Y W := le_nS_of_comm ((D.R_V.trans D.V_X).trans D.XY) fun a ha w hw =>
    D.V_ab a (D.R_V ha) w (D.U_V (hWU' hw))
  have hKN : K ≤ nS Y W := le_nS_of_comm (D.K_X.trans D.XY) fun a ha w hw =>
    D.K_cent a ha w (hWU' hw)
  have hX : qimg (nS Y W) W X ≠ ⊤ := by
    obtain ⟨g, hg, hgX⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hlt).2
    intro h
    have hmem : qmk (nS Y W) W ⟨g, hg⟩ ∈ qimg (nS Y W) W X := by
      rw [h]
      exact Subgroup.mem_top _
    exact hgX ⟨hg.1, (qmk_mem_qimg_iff hWX hg).mp hmem⟩
  have hU1 : qimg (nS Y W) W U ≠ ⊥ := by
    obtain ⟨u, hu, huW⟩ := IsConcreteLE.not_le_iff_exists.mp (not_le_of_gt hWU)
    intro h
    have hmem : qmk (nS Y W) W ⟨u, hUN hu⟩ ∈ qimg (nS Y W) W U := mem_subImg_of_mem _ (hUN hu) hu
    rw [h, Subgroup.mem_bot] at hmem
    exact huW ((qmk_eq_one_iff (hUN hu)).mp hmem)
  have hUn : ∀ x ∈ qimg (nS Y W) W X, ∀ u ∈ qimg (nS Y W) W U, x * u * x⁻¹ ∈ qimg (nS Y W) W U :=
    fun x hx u hu => (Subgroup.mem_normalizer_iff.mp
      (subImg_le_normalizer (qmk (nS Y W) W) D.X_le_normalizer_U hx) u).mp hu
  have hfix : ∀ u ∈ qimg (nS Y W) W U, u ≠ 1 → ∀ g : ↥(nS Y W) ⧸ W.subgroupOf (nS Y W),
      g⁻¹ * u * g ∈ qimg (nS Y W) W X → g ∈ qimg (nS Y W) W X := by
    intro u hu hu1 g hg
    obtain ⟨u₀, hu₀N, hu₀U, rfl⟩ := mem_subImg.mp hu
    obtain ⟨g₀, hg₀N, rfl⟩ := qmk_surj g
    have hu₀W : u₀ ∉ W := fun h => hu1 ((qmk_eq_one_iff hu₀N).mpr h)
    have hm : g₀⁻¹ * u₀ * g₀ ∈ nS Y W :=
      (nS Y W).mul_mem ((nS Y W).mul_mem ((nS Y W).inv_mem hg₀N) hu₀N) hg₀N
    have h1 : g₀⁻¹ * u₀ * g₀ ∈ X := by
      refine (qmk_mem_qimg_iff hWX hm).mp ?_
      rw [qmk_conj_inv _ _ hg₀N hu₀N hm]
      exact hg
    exact mem_subImg_of_mem _ hg₀N (D.fix_core hWU' htW hmax hu₀U hu₀W hg₀N h1)
  have hNX : Subgroup.normalizer ((qimg (nS Y W) W U : Subgroup _) : Set _) ≤
      qimg (nS Y W) W X := by
    intro q hq
    obtain ⟨g, hg, rfl⟩ := qmk_surj q
    have hnorm : ∀ (g' : G) (hg' : g' ∈ nS Y W), qmk (nS Y W) W ⟨g', hg'⟩ ∈
        Subgroup.normalizer ((qimg (nS Y W) W U : Subgroup _) : Set _) →
        ∀ u ∈ U, g' * u * g'⁻¹ ∈ U := by
      intro g' hg' hq' u hu
      have hmem := (Subgroup.mem_normalizer_iff.mp hq' (qmk (nS Y W) W ⟨u, hUN hu⟩)).mp
        (mem_subImg_of_mem _ (hUN hu) hu)
      have hm : g' * u * g'⁻¹ ∈ nS Y W :=
        (nS Y W).mul_mem ((nS Y W).mul_mem hg' (hUN hu)) ((nS Y W).inv_mem hg')
      rw [← qmk_conj _ _ hg' (hUN hu) hm] at hmem
      exact (qmk_mem_qimg_iff hWU' hm).mp hmem
    have hq2 : qmk (nS Y W) W ⟨g⁻¹, (nS Y W).inv_mem hg⟩ ∈
        Subgroup.normalizer ((qimg (nS Y W) W U : Subgroup _) : Set _) := by
      rw [qmk_inv _ hg ((nS Y W).inv_mem hg)]
      exact Subgroup.inv_mem _ hq
    have hgU : g ∈ nS Y U := ⟨mem_normalizer_of_conj_mem (hnorm g hg hq) fun w hw => by
      simpa using hnorm g⁻¹ ((nS Y W).inv_mem hg) hq2 w hw, hg.2⟩
    exact mem_subImg_of_mem _ hg (D.nS_U_le hWU hmax hgU)
  have hR2 : ∃ a ∈ qimg (nS Y W) W R, ∃ b ∈ qimg (nS Y W) W R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := D.R_two
    refine ⟨qmk (nS Y W) W ⟨a, hRN ha⟩, mem_subImg_of_mem _ (hRN ha) ha,
      qmk (nS Y W) W ⟨b, hRN hb⟩, mem_subImg_of_mem _ (hRN hb) hb, ?_, ?_, ?_⟩
    · exact fun h => ha1 (D.R_U a ha (hWU' ((qmk_eq_one_iff (hRN ha)).mp h)))
    · exact fun h => hb1 (D.R_U b hb (hWU' ((qmk_eq_one_iff (hRN hb)).mp h)))
    · intro h
      have h1 : a⁻¹ * b = 1 :=
        D.R_U _ (R.mul_mem (R.inv_mem ha) hb) (hWU' ((qmk_eq_iff (hRN ha) (hRN hb)).mp h))
      exact hab (inv_mul_eq_one.mp h1)
  have hRU : ∀ r ∈ qimg (nS Y W) W R, r ∈ qimg (nS Y W) W U → r = 1 := by
    intro r hr hrU
    obtain ⟨r₀, hr₀N, hr₀R, rfl⟩ := mem_subImg.mp hr
    have h0 := D.R_U r₀ hr₀R ((qmk_mem_qimg_iff hWU' hr₀N).mp hrU)
    subst h0
    exact qmk_one hr₀N
  have hRC : ∀ r ∈ qimg (nS Y W) W R, r ≠ 1 → ∀ g : ↥(nS Y W) ⧸ W.subgroupOf (nS Y W),
      g * r = r * g → g ∈ qimg (nS Y W) W X := by
    intro r hr hr1 g hgr
    obtain ⟨r₀, hr₀N, hr₀R, rfl⟩ := mem_subImg.mp hr
    obtain ⟨g₀, hg₀N, rfl⟩ := qmk_surj g
    have hr₀1 : r₀ ≠ 1 := fun h => hr1 (by subst h; exact qmk_one hr₀N)
    obtain ⟨x, hx, hrx⟩ := D.R_cls r₀ hr₀R hr₀1
    have hm : g₀ * r₀ * g₀⁻¹ ∈ nS Y W :=
      (nS Y W).mul_mem ((nS Y W).mul_mem hg₀N hr₀N) ((nS Y W).inv_mem hg₀N)
    have hconj : qmk (nS Y W) W ⟨g₀ * r₀ * g₀⁻¹, hm⟩ = qmk (nS Y W) W ⟨r₀, hr₀N⟩ := by
      rw [qmk_conj _ _ hg₀N hr₀N hm, hgr]
      group
    have hw := (qmk_eq_iff hm hr₀N).mp hconj
    have h1 : g₀ * r₀ * g₀⁻¹ ∈ X := by
      have e : g₀ * r₀ * g₀⁻¹ = r₀ * ((g₀ * r₀ * g₀⁻¹)⁻¹ * r₀)⁻¹ := by group
      rw [e]
      exact X.mul_mem (D.V_X (D.R_V hr₀R)) (X.inv_mem (hWX hw))
    have h2 : g₀⁻¹ ∈ X := D.H1 x hx g₀⁻¹ (Y.inv_mem hg₀N.2) (by rw [← hrx]; simpa using h1)
    exact mem_subImg_of_mem _ hg₀N (by simpa using X.inv_mem h2)
  have hKp : ⁅qimg (nS Y W) W K, qimg (nS Y W) W K⁆ = qimg (nS Y W) W K := by
    unfold qimg
    rw [subImg_commutator hKN, D.K_perf]
  have hKc : ∀ k ∈ qimg (nS Y W) W K, ∀ u ∈ qimg (nS Y W) W U, k * u = u * k := by
    intro k hk u hu
    obtain ⟨k₀, hk₀N, hk₀K, rfl⟩ := mem_subImg.mp hk
    obtain ⟨u₀, hu₀N, hu₀U, rfl⟩ := mem_subImg.mp hu
    rw [← map_mul, ← map_mul]
    exact congrArg (qmk (nS Y W) W) (Subtype.ext (D.K_cent k₀ hk₀K u₀ hu₀U))
  exact loc442U_final (H := ↥(nS Y W) ⧸ W.subgroupOf (nS Y W)) hX hU1 (subImg_mono _ hUX) hUn
    (subImg_comm fun a ha b hb => D.V_ab a (D.U_V ha) b (D.U_V hb))
    (subImg_sq fun a ha => D.V_sq a (D.U_V ha)) hfix hNX hR2
    (subImg_comm fun a ha b hb => D.V_ab a (D.R_V ha) b (D.R_V hb))
    (subImg_sq fun a ha => D.V_sq a (D.R_V ha)) hRU hRC (subImg_mono _ D.K_X) hKp
    (subImg_mono _ (D.U_V.trans D.V_K)) hKc

end CaseD

end CFSG.Quasithin.H13.F431.Un
