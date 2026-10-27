module

public import CFSG.Quasithin.H13.GoldschmidtU43CData
public import CFSG.Quasithin.H13.GoldschmidtU43CPlanes2
public import CFSG.Quasithin.H13.GoldschmidtU43CRel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem zp_mem {M : Type} [Group M] (S : Subgroup M) {g : M} (hg : g ∈ S) (e : ZMod 2) :
    zp g e ∈ S := by
  rcases zmod_two_cases e with rfl | rfl
  · rw [zp_zero]
    exact one_mem _
  · rw [zp_one]
    exact hg

namespace Hyp

variable {z : G} (h : Hyp z)

theorem tv_zp (g : ↥(Uz z)) (e : ZMod 2) : h.tv (zp g e) = e • h.tv g := by
  rcases zmod_two_cases e with rfl | rfl
  · rw [zp_zero, h.tv_one, zero_smul]
  · rw [zp_one, one_smul]

end Hyp

namespace Two

variable [Finite G] {z t w a a' : G} (e : Two z t w a a')
  {R : Subgroup ↥(Hz z)} {u u' σ₁ : ↥(Hz z)} {x : ↥(Uz z)} {n₁ : V4}
  (hR : SylR e.swap.hyp R) (d : JWData e R u u' σ₁ x n₁)
include hR d

theorem ker_le_closure :
    e.swap.hyp.act.ker ≤ Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) := by
  have h := e.swap.hyp
  set X := Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) with hX
  have hxX : uK x ∈ X := Subgroup.subset_closure (by simp)
  have hσX : σ₁ ∈ X := Subgroup.subset_closure (by simp)
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  let YU : Subgroup ↥(Uz z) := X.comap (Subgroup.inclusion (Uz_le_Hz z))
  have hYU : ∀ y : ↥(Uz z), y ∈ YU ↔ uK y ∈ X := fun y => Iff.rfl
  have hsi : h.act u⁻¹ = h.act u := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right d.hp.2.2.1
  have hσ3 : σ₁ * (σ₁ * σ₁) = 1 := by rw [← pow_three]; exact hR.pow_three d.hσR
  have hσinv : h.act σ₁⁻¹ = h.act σ₁ * h.act σ₁ := by
    rw [inv_eq_of_mul_eq_one_right hσ3, map_mul]
  have hqx : q (h.tv x) = 1 := by
    rw [d.hx]
    exact q_plane1 n₁ d.hn₁ d.hn₁0
  set b₁ := conjU σ₁⁻¹ x with hb₁
  set a₂ := conjU u⁻¹ x with ha₂
  set b₂ := conjU u⁻¹ b₁ with hb₂
  have hxY : x ∈ YU := (hYU x).2 hxX
  have hb₁Y : b₁ ∈ YU := by
    rw [hYU, hb₁, uK_conjU]
    exact mul_mem (mul_mem (inv_mem hσX) hxX) (inv_mem (inv_mem hσX))
  have ha₂Y : a₂ ∈ YU := by
    rw [hYU, ha₂, uK_conjU]
    exact mul_mem (mul_mem (inv_mem huX) hxX) (inv_mem (inv_mem huX))
  have hb₂Y : b₂ ∈ YU := by
    rw [hYU, hb₂, uK_conjU]
    exact mul_mem (mul_mem (inv_mem huX) ((hYU b₁).1 hb₁Y)) (inv_mem (inv_mem huX))
  have hzY : h.zU ∈ YU := by
    rw [← h.mul_self_of_q_one hqx]
    exact mul_mem hxY hxY
  have htb₁ : h.tv b₁ = vapp (h.act σ₁) (vapp (h.act σ₁) n₁) := by
    rw [hb₁, h.tv_conj, hσinv, Swap.vapp_mul, d.hx]
  have hta₂ : h.tv a₂ = vapp (h.act u) n₁ := by
    rw [ha₂, h.tv_conj, hsi, d.hx]
  have htb₂ : h.tv b₂ = vapp (h.act u) (vapp (h.act σ₁) (vapp (h.act σ₁) n₁)) := by
    rw [hb₂, h.tv_conj, hsi, htb₁]
  have hσW : h.act σ₁ ∈ Rbar := h.mem_Wsub.1 (hR.le_W d.hσR)
  intro y hy
  have hyU : (y : G) ∈ Uz z := h.mem_U_of_act_eq_one y (MonoidHom.mem_ker.mp hy)
  obtain ⟨e₁, e₂, e₃, e₄, he⟩ := span_fourA (h.act_mem_Oq u) hσW d.hp.1 d.hp.2.2.1 d.hρ1
    d.hρfix d.hn₁ d.hn₁0 (h.tv ⟨y, hyU⟩)
  set y' : ↥(Uz z) := zp x e₁ * zp b₁ e₂ * zp a₂ e₃ * zp b₂ e₄ with hy'
  have hy'Y : y' ∈ YU :=
    mul_mem (mul_mem (mul_mem (zp_mem YU hxY e₁) (zp_mem YU hb₁Y e₂)) (zp_mem YU ha₂Y e₃))
      (zp_mem YU hb₂Y e₄)
  have htv : h.tv ⟨y, hyU⟩ = h.tv y' := by
    rw [hy', h.tv_mul, h.tv_mul, h.tv_mul, h.tv_zp, h.tv_zp, h.tv_zp, h.tv_zp, d.hx, htb₁, hta₂,
      htb₂]
    exact he
  have hmem : (⟨y, hyU⟩ : ↥(Uz z)) ∈ YU := by
    rcases h.eq_of_tv_eq' htv with h1 | h1
    · rw [h1]
      exact hy'Y
    · rw [h1]
      exact mul_mem hzY hy'Y
  exact (hYU _).1 hmem

omit hR d in
theorem pwA_mem {M : Type} [Group M] (S : Subgroup M) {g : M} (hg : g ∈ S) (i : ℕ) :
    pwA g i ∈ S := by
  rcases i with _ | _ | i
  · exact one_mem _
  · exact hg
  · exact mul_mem hg hg

omit hR d in
theorem map_pwA {M N : Type} [Group M] [Group N] (f : M →* N) (g : M) (i : ℕ) :
    f (pwA g i) = pwA (f g) i := by
  rcases i with _ | _ | i
  · exact map_one f
  · rfl
  · exact map_mul f g g

theorem Tk_le_closure :
    (Tn z t).subgroupOf (Hz z) ≤
      Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) := by
  classical
  have h := e.swap.hyp
  set X := Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) with hX
  have hker : h.act.ker ≤ X := e.ker_le_closure hR d
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hvX : u * u' ∈ X := Subgroup.subset_closure (by simp)
  have hu'X : u' ∈ X := by
    have : u' = u⁻¹ * (u * u') := by group
    rw [this]
    exact mul_mem (inv_mem huX) hvX
  have hlift : ∀ {k g : ↥(Hz z)}, g ∈ X → h.act k = h.act g → k ∈ X := by
    intro k g hg hk
    have : g⁻¹ * k ∈ h.act.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk]
      simp
    have h2 := hker this
    have : k = g * (g⁻¹ * k) := by group
    rw [this]
    exact mul_mem hg h2
  set Tk := (Tn z t).subgroupOf (Hz z) with hTk
  have hcard : Nat.card (Tk.map h.act) = 4 := by
    have := h.card_map_act_mul (Tn z t) e.swap.U_le_T inf_le_left
    rw [← hTk, h.card_Tn e.swap.ht] at this
    omega
  have hm1 : e.swap.mK e.ha ∈ Tk := e.swap.B_le_T (e.swap.m_mem_B e.ha)
  have hm2 : e.swap.mK e.ha' ∈ Tk := e.swap.B_le_T (e.swap.m_mem_B e.ha')
  set s := h.act u with hs
  set s' := h.act u' with hs'
  have hsΦ : s ∈ Tk.map h.act := ⟨e.swap.mK e.ha, hm1, d.hact.symm⟩
  have hs'Φ : s' ∈ Tk.map h.act := ⟨e.swap.mK e.ha', hm2, d.hact'.symm⟩
  have hs1 : s ≠ 1 := by rw [hs, d.hact]; exact e.swap.act_mK_ne_one e.ha
  have hs'1 : s' ≠ 1 := by rw [hs', d.hact']; exact e.swap.act_mK_ne_one e.ha'
  have hss' : s ≠ s' := d.hp.2.2.2.2.2
  have hss2 : s * s = 1 := d.hp.2.2.1
  have e1 : s * s' ≠ 1 := fun hh => hss' (by
    rw [eq_inv_of_mul_eq_one_right hh]
    exact (inv_eq_of_mul_eq_one_right hss2).symm)
  have e2 : s * s' ≠ s := fun hh => hs'1 (by simpa using hh)
  have e3 : s * s' ≠ s' := fun hh => hs1 (by simpa using hh)
  have hfour : ∀ g ∈ Tk.map h.act, g = 1 ∨ g = s ∨ g = s' ∨ g = s * s' := by
    intro g hg
    by_contra hcon
    push Not at hcon
    obtain ⟨g1, g2, g3, g4⟩ := hcon
    let P : Finset (MulAut (Multiplicative V4)) := {g, 1, s, s', s * s'}
    have n1 : s' ∉ ({s * s'} : Finset (MulAut (Multiplicative V4))) := by
      simp only [Finset.mem_singleton]
      exact fun hh => e3 hh.symm
    have n2 : s ∉ ({s', s * s'} : Finset (MulAut (Multiplicative V4))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hss', fun hh => e2 hh.symm⟩
    have n3 : (1 : MulAut (Multiplicative V4)) ∉
        ({s, s', s * s'} : Finset (MulAut (Multiplicative V4))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun hh => hs1 hh.symm, fun hh => hs'1 hh.symm, fun hh => e1 hh.symm⟩
    have n4 : g ∉ ({1, s, s', s * s'} : Finset (MulAut (Multiplicative V4))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨g1, g2, g3, g4⟩
    have hP : P.card = 5 := by
      simp only [P]
      rw [Finset.card_insert_of_notMem n4, Finset.card_insert_of_notMem n3,
        Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1, Finset.card_singleton]
    have hsub : (P : Set (MulAut (Multiplicative V4))) ⊆ (Tk.map h.act : Set _) := by
      intro y hy
      simp only [P, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hg
      · exact one_mem _
      · exact hsΦ
      · exact hs'Φ
      · exact mul_mem hsΦ hs'Φ
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hP, ← Nat.card_coe_set_eq] at this
    have h4 : Nat.card ↥(Tk.map h.act : Set (MulAut (Multiplicative V4))) = 4 := hcard
    omega
  intro k hk
  have hkΦ : h.act k ∈ Tk.map h.act := ⟨k, hk, rfl⟩
  rcases hfour _ hkΦ with h1 | h1 | h1 | h1
  · exact hker (MonoidHom.mem_ker.mpr h1)
  · exact hlift huX h1
  · exact hlift hu'X h1
  · exact hlift hvX (by rw [map_mul]; exact h1)

theorem R_le_closure :
    R ≤ Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) := by
  have h := e.swap.hyp
  set X := Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) with hX
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hσX : σ₁ ∈ X := Subgroup.subset_closure (by simp)
  have hsi : h.act u⁻¹ = h.act u := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right d.hp.2.2.1
  have hσ₂R : u⁻¹ * σ₁ * u ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem d.hu) σ₁).mp d.hσR
    simpa using this
  have hσ₂X : u⁻¹ * σ₁ * u ∈ X := mul_mem (mul_mem (inv_mem huX) hσX) huX
  have hactσ₂ : h.act (u⁻¹ * σ₁ * u) = h.act u * h.act σ₁ * h.act u := by
    rw [map_mul, map_mul, hsi]
  have hσW : h.act σ₁ ∈ Rbar := h.mem_Wsub.1 (hR.le_W d.hσR)
  intro r hr
  have hrW : h.act r ∈ Rbar := h.mem_Wsub.1 (hR.le_W hr)
  obtain ⟨i, -, j, -, hij⟩ := Rbar_gen (h.act_mem_Oq u) d.hp.1 d.hp.2.2.1 hσW d.hρ1 d.hρfix hrW
  have hrr : r = pwA σ₁ i * pwA (u⁻¹ * σ₁ * u) j := by
    refine hR.act_inj' hr (mul_mem (pwA_mem R d.hσR i) (pwA_mem R hσ₂R j)) ?_
    rw [map_mul, map_pwA, map_pwA, hactσ₂, hij]
  rw [hrr]
  exact mul_mem (pwA_mem X hσX i) (pwA_mem X hσ₂X j)

theorem closure_eq_top :
    Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) = ⊤ := by
  have h := e.swap.hyp
  set X := Subgroup.closure ({uK x, σ₁, u, u * u'} : Set ↥(Hz z)) with hX
  have hT := e.Tk_le_closure hR d
  have hR' := e.R_le_closure hR d
  have h128 : Nat.card ((Tn z t).subgroupOf (Hz z)) = 128 := by
    rw [← h.card_Tn e.swap.ht]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hd1 : 128 ∣ Nat.card X := h128 ▸ Subgroup.card_dvd_of_le hT
  have hd2 : 9 ∣ Nat.card X := hR.card ▸ Subgroup.card_dvd_of_le hR'
  have hd : 128 * 9 ∣ Nat.card X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd1 hd2
  have hle : Nat.card X ∣ Nat.card ↥(Hz z) := Subgroup.card_subgroup_dvd_card X
  rw [h.card_H] at hle
  have hcard : Nat.card X = 1152 := Nat.dvd_antisymm hle (by simpa using hd)
  exact Subgroup.eq_top_of_card_eq X (by rw [hcard, h.card_H])

end Two

end CFSG.Quasithin.H13.U43
