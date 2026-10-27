module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalSelVolU
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private lemma plh_span_singleton_inf_eq_bot_iff {u : Fin 4 → K} (hu : u ≠ 0) :
    (K ∙ u : Submodule K (Fin 4 → K)) ⊓ Vsub 4 2 = ⊥ ↔ u ∉ Vsub 4 2 := by
  rw [← disjoint_iff, disjoint_comm, Submodule.disjoint_span_singleton' hu]

private lemma plh_map_span_singleton (u : Fin 4 → K) :
    (K ∙ u : Submodule K (Fin 4 → K)).map rho = K ∙ (rho u) := by
  rw [Submodule.map_span, Set.image_singleton]

private lemma plh_mem_three_images {α β : Type*} [DecidableEq β] {A B C : Finset α}
    {f g k : α → β} {y : β} :
    y ∈ (A.image f ∪ B.image g) ∪ C.image k ↔
      (∃ a ∈ A, f a = y) ∨ (∃ b ∈ B, g b = y) ∨ (∃ c ∈ C, k c = y) := by
  simp only [Finset.mem_union, Finset.mem_image, or_assoc]

private lemma plh_adj_facts (D : ClsData K) {x y : Submodule K (Fin 4 → K)}
    (h : AdmAdj (AdmS D) x y) :
    x ≠ y ∧ finrank K x = 1 ∧ finrank K y = 1 ∧ x ⊓ Vsub 4 2 = ⊥ ∧
      y ⊓ Vsub 4 2 = ⊥ ∧ (x ⊔ y) ⊓ Vsub 4 2 = ⊥ ∧ D.ok (x.map rho) ∧
      D.ok (y.map rho) ∧ finrank K (x.map rho) = 1 ∧ finrank K (y.map rho) = 1 ∧
      x.map rho ≠ y.map rho := by
  obtain ⟨hxy, L, H, hxch, hych⟩ := h
  obtain ⟨hxflag, hxadm⟩ := hxch
  obtain ⟨hyflag, hyadm⟩ := hych
  obtain ⟨hx1, hL2, hH3, hxL, hLH⟩ := hxflag
  obtain ⟨hy1, -, -, hyL, -⟩ := hyflag
  obtain ⟨hLbot, hox, -⟩ := hxadm
  obtain ⟨-, hoy, -⟩ := hyadm
  have hx2 : x ⊓ Vsub 4 2 = ⊥ := by
    have hle : x ⊓ Vsub 4 2 ≤ L ⊓ Vsub 4 2 := inf_le_inf_right _ hxL
    rw [hLbot] at hle
    exact le_bot_iff.mp hle
  have hy2 : y ⊓ Vsub 4 2 = ⊥ := by
    have hle : y ⊓ Vsub 4 2 ≤ L ⊓ Vsub 4 2 := inf_le_inf_right _ hyL
    rw [hLbot] at hle
    exact le_bot_iff.mp hle
  have hsup : (x ⊔ y) ⊓ Vsub 4 2 = ⊥ := by
    have hle : (x ⊔ y) ⊓ Vsub 4 2 ≤ L ⊓ Vsub 4 2 :=
      inf_le_inf_right _ (sup_le hxL hyL)
    rw [hLbot] at hle
    exact le_bot_iff.mp hle
  exact ⟨hxy, hx1, hy1, hx2, hy2, hsup, hox, hoy, finrank_map_rho hx1 hx2,
    finrank_map_rho hy1 hy2, (map_rho_ne_iff hx1 hy1 hxy hx2 hy2).mp hsup⟩

private lemma plh_admPlanar_of_side (D : ClsData K) {a b t : Submodule K (Fin 4 → K)}
    (M : Submodule K (Fin 4 → K))
    (ha1 : finrank K a = 1) (hb1 : finrank K b = 1) (ht1 : finrank K t = 1)
    (ha2 : a ⊓ Vsub 4 2 = ⊥) (hb2 : b ⊓ Vsub 4 2 = ⊥) (ht2 : t ⊓ Vsub 4 2 = ⊥)
    (hab2 : (a ⊔ b) ⊓ Vsub 4 2 = ⊥) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hoa : D.ok (a.map rho)) (hob : D.ok (b.map rho)) (hot : D.ok (t.map rho))
    (hnat : a.map rho ≠ t.map rho) (hnbt : b.map rho ≠ t.map rho)
    (hM : M ≤ Vsub 4 2) (hM1 : finrank K M = 1) (htM : t ≤ (a ⊔ b) ⊔ M)
    (hga : D.good (a.map rho) M) (hgb : D.good (b.map rho) M) (hgt : D.good (t.map rho) M) :
    AdmPlanar (AdmS D) a b t := by
  have hL1 : finrank K (a ⊔ b : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts ha1 hb1 hab
  have hL2 : finrank K (b ⊔ t : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts hb1 ht1 hbt
  have hL3 : finrank K (t ⊔ a : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts ht1 ha1 hat.symm
  have hH3 : finrank K ((a ⊔ b) ⊔ M : Submodule K (Fin 4 → K)) = 3 :=
    finrank_sup_trace hL1 hab2 hM hM1
  have htrace : ((a ⊔ b) ⊔ M : Submodule K (Fin 4 → K)) ⊓ Vsub 4 2 = M :=
    sup_trace_inf hL1 hab2 hM hM1
  have hL2bot : (b ⊔ t : Submodule K (Fin 4 → K)) ⊓ Vsub 4 2 = ⊥ :=
    (map_rho_ne_iff hb1 ht1 hbt hb2 ht2).mpr hnbt
  have hL3bot : (t ⊔ a : Submodule K (Fin 4 → K)) ⊓ Vsub 4 2 = ⊥ :=
    (map_rho_ne_iff ht1 ha1 hat.symm ht2 ha2).mpr hnat.symm
  have hL2H : (b ⊔ t : Submodule K (Fin 4 → K)) ≤ (a ⊔ b) ⊔ M :=
    sup_le (le_trans le_sup_right le_sup_left) htM
  have hL3H : (t ⊔ a : Submodule K (Fin 4 → K)) ≤ (a ⊔ b) ⊔ M :=
    sup_le htM (le_trans le_sup_left le_sup_left)
  refine ⟨(a ⊔ b) ⊔ M, a ⊔ b, b ⊔ t, t ⊔ a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨ha1, hL1, hH3, le_sup_left, le_sup_left⟩, hab2, hoa,
      by rw [htrace]; exact hga⟩
  · exact ⟨⟨hb1, hL1, hH3, le_sup_right, le_sup_left⟩, hab2, hob,
      by rw [htrace]; exact hgb⟩
  · exact ⟨⟨hb1, hL2, hH3, le_sup_left, hL2H⟩, hL2bot, hob,
      by rw [htrace]; exact hgb⟩
  · exact ⟨⟨ht1, hL2, hH3, le_sup_right, hL2H⟩, hL2bot, hot,
      by rw [htrace]; exact hgt⟩
  · exact ⟨⟨ht1, hL3, hH3, le_sup_left, hL3H⟩, hL3bot, hot,
      by rw [htrace]; exact hgt⟩
  · exact ⟨⟨ha1, hL3, hH3, le_sup_right, hL3H⟩, hL3bot, hoa,
      by rw [htrace]; exact hga⟩

theorem cls_coneTri [Finite K] (D : ClsData K) {β : ℕ} (h : ClsHyp D β) :
    AdmConeTri (AdmS D) := by
  classical
  intro x y z hxy hyz hzx
  obtain ⟨hxy_ne, hx1, hy1, hx2, hy2, hxy2, hox, hoy, hfx, hfy, hcxy⟩ :=
    plh_adj_facts D hxy
  obtain ⟨hyz_ne, -, hz1, -, hz2, hyz2, -, hoz, -, hfz, hcyz⟩ := plh_adj_facts D hyz
  obtain ⟨hzx_ne, -, -, -, -, hzx2, -, -, -, -, hczx⟩ := plh_adj_facts D hzx
  have hcolcard : ({x.map rho, y.map rho, z.map rho} :
      Finset (Submodule K (Fin 2 → K))).card ≤ 4 := by
    have h1 := Finset.card_insert_le (x.map rho)
      ({y.map rho, z.map rho} : Finset (Submodule K (Fin 2 → K)))
    have h2 := Finset.card_insert_le (y.map rho)
      ({z.map rho} : Finset (Submodule K (Fin 2 → K)))
    simp only [Finset.card_singleton] at h2
    omega
  obtain ⟨d, hdok, hd1, hdnotin⟩ :=
    h.col ({x.map rho, y.map rho, z.map rho} : Finset (Submodule K (Fin 2 → K))) hcolcard
  have hd_cx : d ≠ x.map rho := fun hh => hdnotin (by simp [hh])
  have hd_cy : d ≠ y.map rho := fun hh => hdnotin (by simp [hh])
  have hd_cz : d ≠ z.map rho := fun hh => hdnotin (by simp [hh])
  obtain ⟨u, hu0, hd_eq⟩ := exists_eq_span_of_finrank_eq_one hd1
  obtain ⟨t₀, ht₀⟩ := rho_surjective u
  have hLxy : finrank K (x ⊔ y : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts hx1 hy1 hxy_ne
  obtain ⟨lxy, hlxy, wxy, hwxy, hdecxy⟩ := exists_decomp hLxy hxy2 t₀
  have hLyz : finrank K (y ⊔ z : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts hy1 hz1 hyz_ne
  obtain ⟨lyz, hlyz, wyz, hwyz, hdecyz⟩ := exists_decomp hLyz hyz2 t₀
  have hLzx : finrank K (z ⊔ x : Submodule K (Fin 4 → K)) = 2 :=
    finrank_sup_of_ne_pts hz1 hx1 hzx_ne
  obtain ⟨lzx, hlzx, wzx, hwzx, hdeczx⟩ := exists_decomp hLzx hzx2 t₀
  obtain ⟨Bxy, -, hBxy_card, hBxy_lines, hBxy_good⟩ :=
    h.bad (x.map rho) (y.map rho) d hox hoy hdok hfx hfy hd1 hcxy hd_cy.symm hd_cx
  obtain ⟨Byz, -, hByz_card, hByz_lines, hByz_good⟩ :=
    h.bad (y.map rho) (z.map rho) d hoy hoz hdok hfy hfz hd1 hcyz hd_cz.symm hd_cy
  obtain ⟨Bzx, -, hBzx_card, hBzx_lines, hBzx_good⟩ :=
    h.bad (z.map rho) (x.map rho) d hoz hox hdok hfz hfx hd1 hczx hd_cx.symm hd_cz
  let s : Finset (Submodule K (Fin 4 → K) × (Fin 4 → K)) :=
    (Bxy.image (fun m => (m, wxy))) ∪ (Byz.image (fun m => (m, wyz))) ∪
      (Bzx.image (fun m => (m, wzx)))
  have hT : ∀ i ∈ s, i.1 ≤ Vsub 4 2 := by
    rintro ⟨m, w⟩ hi
    change m ≤ Vsub 4 2
    dsimp only [s] at hi
    rw [plh_mem_three_images] at hi
    rcases hi with ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hBxy_lines m' hm').1
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hByz_lines m' hm').1
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hBzx_lines m' hm').1
  have hc : ∀ i ∈ s, -i.2 ∈ Vsub 4 2 := by
    rintro ⟨m, w⟩ hi
    change -w ∈ Vsub 4 2
    dsimp only [s] at hi
    rw [plh_mem_three_images] at hi
    rcases hi with ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩
    · rw [Prod.mk.injEq] at h'
      rw [← h'.2]
      exact neg_mem hwxy
    · rw [Prod.mk.injEq] at h'
      rw [← h'.2]
      exact neg_mem hwyz
    · rw [Prod.mk.injEq] at h'
      rw [← h'.2]
      exact neg_mem hwzx
  have hTfin : ∀ i ∈ s, finrank K i.1 = 1 := by
    rintro ⟨m, w⟩ hi
    change finrank K m = 1
    dsimp only [s] at hi
    rw [plh_mem_three_images] at hi
    rcases hi with ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩ | ⟨m', hm', h'⟩
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hBxy_lines m' hm').2
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hByz_lines m' hm').2
    · rw [Prod.mk.injEq] at h'
      rw [← h'.1]
      exact (hBzx_lines m' hm').2
  have hs_card : s.card ≤ 3 * β := by
    dsimp only [s]
    have hA : (Bxy.image (fun m => (m, wxy))).card ≤ β :=
      le_trans Finset.card_image_le hBxy_card
    have hB : (Byz.image (fun m => (m, wyz))).card ≤ β :=
      le_trans Finset.card_image_le hByz_card
    have hC : (Bzx.image (fun m => (m, wzx))).card ≤ β :=
      le_trans Finset.card_image_le hBzx_card
    have hAB : ((Bxy.image (fun m => (m, wxy))) ∪
        (Byz.image (fun m => (m, wyz)))).card ≤
        (Bxy.image (fun m => (m, wxy))).card + (Byz.image (fun m => (m, wyz))).card :=
      Finset.card_union_le _ _
    have h3 : ((Bxy.image (fun m => (m, wxy))) ∪ (Byz.image (fun m => (m, wyz))) ∪
        (Bzx.image (fun m => (m, wzx)))).card ≤
        ((Bxy.image (fun m => (m, wxy))) ∪ (Byz.image (fun m => (m, wyz)))).card +
          (Bzx.image (fun m => (m, wzx))).card :=
      Finset.card_union_le _ _
    omega
  have hsum_eq : ∑ i ∈ s, Nat.card K ^ finrank K i.1 = s.card * Nat.card K :=
    Finset.sum_const_nat (fun i hi => by rw [hTfin i hi, pow_one])
  have hsum_lt : (∑ i ∈ s, Nat.card K ^ finrank K i.1) <
      Nat.card K ^ finrank K (Vsub (K := K) 4 2) := by
    rw [hsum_eq, finrank_Vsub (K := K) (by norm_num : (2 : ℕ) ≤ 4)]
    have hcard3 : s.card * Nat.card K ≤ 3 * β * Nat.card K :=
      Nat.mul_le_mul_right _ hs_card
    have hsmall : 3 * β < Nat.card K := h.small
    have hKpos : 0 < Nat.card K := by omega
    have hsmall2 : 3 * β * Nat.card K < Nat.card K * Nat.card K :=
      Nat.mul_lt_mul_of_pos_right h.small hKpos
    rw [pow_two]
    exact lt_of_le_of_lt hcard3 hsmall2
  obtain ⟨τ, hτU, hτ⟩ := exists_mem_notMem_affine_of_sum_lt (K := K) (Vsub 4 2) s
    (fun i : Submodule K (Fin 4 → K) × (Fin 4 → K) => i.1)
    (fun i : Submodule K (Fin 4 → K) × (Fin 4 → K) => -i.2) hT hc hsum_lt
  have hgood_xy : wxy + τ ≠ 0 ∧ D.good (x.map rho) (K ∙ (wxy + τ)) ∧
      D.good (y.map rho) (K ∙ (wxy + τ)) ∧ D.good d (K ∙ (wxy + τ)) := by
    refine hBxy_good (wxy + τ) ((Vsub 4 2).add_mem hwxy hτU) (fun m hm => ?_)
    have hmem : (m, wxy) ∈ s := by
      dsimp only [s]
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
    have hh := hτ (m, wxy) hmem
    rw [add_comm]
    simpa [sub_neg_eq_add] using hh
  have hgood_yz : wyz + τ ≠ 0 ∧ D.good (y.map rho) (K ∙ (wyz + τ)) ∧
      D.good (z.map rho) (K ∙ (wyz + τ)) ∧ D.good d (K ∙ (wyz + τ)) := by
    refine hByz_good (wyz + τ) ((Vsub 4 2).add_mem hwyz hτU) (fun m hm => ?_)
    have hmem : (m, wyz) ∈ s := by
      dsimp only [s]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
    have hh := hτ (m, wyz) hmem
    rw [add_comm]
    simpa [sub_neg_eq_add] using hh
  have hgood_zx : wzx + τ ≠ 0 ∧ D.good (z.map rho) (K ∙ (wzx + τ)) ∧
      D.good (x.map rho) (K ∙ (wzx + τ)) ∧ D.good d (K ∙ (wzx + τ)) := by
    refine hBzx_good (wzx + τ) ((Vsub 4 2).add_mem hwzx hτU) (fun m hm => ?_)
    have hmem : (m, wzx) ∈ s := by
      dsimp only [s]
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    have hh := hτ (m, wzx) hmem
    rw [add_comm]
    simpa [sub_neg_eq_add] using hh
  have hrhoτ : rho τ = 0 := (LinearMap.mem_ker).mp (by rw [ker_rho]; exact hτU)
  have hrho_t0τ : rho (t₀ + τ) = u := by rw [map_add, ht₀, hrhoτ, add_zero]
  have ht0τ_ne : t₀ + τ ≠ 0 := fun hh => by
    have h0 : rho (t₀ + τ) = 0 := by rw [hh, map_zero]
    rw [hrho_t0τ] at h0
    exact hu0 h0
  let t : Submodule K (Fin 4 → K) := K ∙ (t₀ + τ)
  have ht1 : finrank K t = 1 := finrank_span_singleton ht0τ_ne
  have ht2 : t ⊓ Vsub 4 2 = ⊥ := by
    change (K ∙ (t₀ + τ)) ⊓ Vsub 4 2 = ⊥
    refine (plh_span_singleton_inf_eq_bot_iff ht0τ_ne).mpr (fun hmem => ?_)
    have h0 : rho (t₀ + τ) = 0 := (LinearMap.mem_ker).mp (by rw [ker_rho]; exact hmem)
    rw [hrho_t0τ] at h0
    exact hu0 h0
  have htmap : t.map rho = d := by
    change (K ∙ (t₀ + τ)).map rho = d
    rw [plh_map_span_singleton, hrho_t0τ, hd_eq]
  have hot : D.ok (t.map rho) := by rw [htmap]; exact hdok
  have hnat : x.map rho ≠ t.map rho := by rw [htmap]; exact fun hh => hd_cx hh.symm
  have hnbt : y.map rho ≠ t.map rho := by rw [htmap]; exact fun hh => hd_cy hh.symm
  have hnct : z.map rho ≠ t.map rho := by rw [htmap]; exact fun hh => hd_cz hh.symm
  have hxt_ne : x ≠ t := fun hh => hnat (by rw [hh])
  have hyt_ne : y ≠ t := fun hh => hnbt (by rw [hh])
  have hzt_ne : z ≠ t := fun hh => hnct (by rw [hh])
  have htM_xy : t ≤ (x ⊔ y) ⊔ (K ∙ (wxy + τ)) := by
    change K ∙ (t₀ + τ) ≤ (x ⊔ y) ⊔ (K ∙ (wxy + τ))
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have h1 : lxy ∈ (x ⊔ y : Submodule K (Fin 4 → K)) := hlxy
    have h2 : wxy + τ ∈ (K ∙ (wxy + τ) : Submodule K (Fin 4 → K)) :=
      Submodule.mem_span_singleton_self _
    rw [hdecxy, add_assoc]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  have htM_yz : t ≤ (y ⊔ z) ⊔ (K ∙ (wyz + τ)) := by
    change K ∙ (t₀ + τ) ≤ (y ⊔ z) ⊔ (K ∙ (wyz + τ))
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have h1 : lyz ∈ (y ⊔ z : Submodule K (Fin 4 → K)) := hlyz
    have h2 : wyz + τ ∈ (K ∙ (wyz + τ) : Submodule K (Fin 4 → K)) :=
      Submodule.mem_span_singleton_self _
    rw [hdecyz, add_assoc]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  have htM_zx : t ≤ (z ⊔ x) ⊔ (K ∙ (wzx + τ)) := by
    change K ∙ (t₀ + τ) ≤ (z ⊔ x) ⊔ (K ∙ (wzx + τ))
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have h1 : lzx ∈ (z ⊔ x : Submodule K (Fin 4 → K)) := hlzx
    have h2 : wzx + τ ∈ (K ∙ (wzx + τ) : Submodule K (Fin 4 → K)) :=
      Submodule.mem_span_singleton_self _
    rw [hdeczx, add_assoc]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  have hpxy : AdmPlanar (AdmS D) x y t :=
    plh_admPlanar_of_side D (K ∙ (wxy + τ)) hx1 hy1 ht1 hx2 hy2 ht2 hxy2 hxy_ne hxt_ne
      hyt_ne hox hoy hot hnat hnbt
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ((Vsub 4 2).add_mem hwxy hτU))
      (finrank_span_singleton hgood_xy.1) htM_xy hgood_xy.2.1 hgood_xy.2.2.1
      (by rw [htmap]; exact hgood_xy.2.2.2)
  have hpyz : AdmPlanar (AdmS D) y z t :=
    plh_admPlanar_of_side D (K ∙ (wyz + τ)) hy1 hz1 ht1 hy2 hz2 ht2 hyz2 hyz_ne hyt_ne
      hzt_ne hoy hoz hot hnbt hnct
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ((Vsub 4 2).add_mem hwyz hτU))
      (finrank_span_singleton hgood_yz.1) htM_yz hgood_yz.2.1 hgood_yz.2.2.1
      (by rw [htmap]; exact hgood_yz.2.2.2)
  have hpzx : AdmPlanar (AdmS D) z x t :=
    plh_admPlanar_of_side D (K ∙ (wzx + τ)) hz1 hx1 ht1 hz2 hx2 ht2 hzx2 hzx_ne hzt_ne
      hxt_ne hoz hox hot hnct hnat
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ((Vsub 4 2).add_mem hwzx hτU))
      (finrank_span_singleton hgood_zx.1) htM_zx hgood_zx.2.1 hgood_zx.2.2.1
      (by rw [htmap]; exact hgood_zx.2.2.2)
  have hpxy_saved : AdmPlanar (AdmS D) x y t := hpxy
  obtain ⟨Hxy, L1xy, L2xy, L3xy, c1xy, c2xy, c3xy, c4xy, c5xy, c6xy⟩ := hpxy
  have hxt : AdmAdj (AdmS D) x t := ⟨hxt_ne, L3xy, Hxy, c6xy, c5xy⟩
  have hyt : AdmAdj (AdmS D) y t := ⟨hyt_ne, L2xy, Hxy, c3xy, c4xy⟩
  have hpyz_saved : AdmPlanar (AdmS D) y z t := hpyz
  obtain ⟨Hyz, -, L2yz, -, -, -, c3yz, c4yz, -, -⟩ := hpyz
  have hzt : AdmAdj (AdmS D) z t := ⟨hzt_ne, L2yz, Hyz, c3yz, c4yz⟩
  exact ⟨t, hxt, hyt, hzt, hpxy_saved, hpyz_saved, hpzx⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
