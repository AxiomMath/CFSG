module

public import CFSG.Quasithin.H13.GoldschmidtU43EBasic

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

set_option synthInstance.maxSize 1024

theorem cube1_centralizer : ∀ x : OC, (∀ r : OC, Cube1 r.cols →
    comp x.cols r.cols = comp r.cols x.cols) → Cube1 x.cols := by
  decide +kernel

theorem Rbar_centralizer {g : MulAut (Multiplicative V4)} (hg : g ∈ Oq)
    (hc : ∀ r ∈ Rbar, g * r = r * g) : g ∈ Rbar := by
  have key := cube1_centralizer (toOC ⟨g, hg⟩) (fun r hr => by
    have hr' : ofOC r ∈ Rbar := ⟨ofOC_mem r, by rw [← cube1_iff, colsOf_ofOC]; exact hr⟩
    have := congrArg colsOf (hc _ hr')
    rw [colsOf_mul, colsOf_mul, colsOf_ofOC] at this
    rw [toOC_mk_cols g hg]
    exact this)
  rw [toOC_mk_cols g hg, cube1_iff] at key
  exact ⟨hg, key⟩

theorem sq_eq_one_of_card_four {Q : Type} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) {a b : Q}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1) (hb2 : b * b = 1) (q : Q) :
    q * q = 1 := by
  classical
  have := Fintype.ofFinite Q
  by_contra hq
  have hdvd : orderOf q ∣ 4 := hQ ▸ orderOf_dvd_natCard q
  have hq4 : orderOf q = 4 := by
    have hle : orderOf q ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf q
    · exact absurd hdvd (by norm_num)
    · exact absurd (orderOf_eq_one_iff.mp h) (by rintro rfl; exact hq (by simp))
    · exact absurd (by rw [← pow_two]; exact pow_orderOf_eq_one q ▸ (by rw [h]) : q * q = 1) hq
    · exact absurd hdvd (by norm_num)
    · rfl
  have hcyc : IsCyclic Q := isCyclic_of_orderOf_eq_card q (by rw [hq4, hQ])
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Q) ⊆ Finset.univ.filter (fun x : Q => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rwa [pow_two]
    · rwa [pow_two]
  have h3 : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem not_mem_Rbar_of_sq {g : MulAut (Multiplicative V4)} (h2 : g * g = 1) (h1 : g ≠ 1) :
    g ∉ Rbar := by
  intro hg
  apply h1
  have h3 : g * g * g = 1 := by rw [← pow_three']; exact hg.2
  calc g = (g * g * g) * (g * g)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem mem_of_act_mem_Rbar {n : ↥(Hz z)} (hn : n ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)))
    (hg : S.hyp.act n ∈ Rbar) : ∃ r ∈ S.R, n = r ∨ n = zK z * r := by
  obtain ⟨r, hr, hrn⟩ := S.hR.act_onto hg
  have hx : r⁻¹ * n ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) :=
    mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hr)) hn
  have hxk : r⁻¹ * n ∈ S.hyp.act.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrn]
    simp
  refine ⟨r, hr, ?_⟩
  rcases S.hR.normalizer_inf_ker hx hxk with h1 | h1
  · left
    have : r⁻¹ * n = 1 := Subtype.ext h1
    calc n = r * (r⁻¹ * n) := by group
      _ = r := by rw [this, mul_one]
  · right
    have : r⁻¹ * n = zK z := Subtype.ext h1
    calc n = r * (r⁻¹ * n) := by group
      _ = r * zK z := by rw [this]
      _ = zK z * r := (zK_comm r).symm

theorem centralizer_R {x : ↥(Hz z)} (hx : ∀ r ∈ S.R, x * r = r * x) :
    ∃ r ∈ S.R, x = r ∨ x = zK z * r := by
  have h := S.hyp
  have hxN : x ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have : x * r * x⁻¹ = r := by rw [hx r hr]; group
      rw [this]
      exact hr
    · intro hr
      have hy := hx _ hr
      have e1 : x⁻¹ * (x * r * x⁻¹) * x = x * r * x⁻¹ := by
        calc x⁻¹ * (x * r * x⁻¹) * x = x⁻¹ * ((x * r * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * r * x⁻¹)) := by rw [← hy]
          _ = x * r * x⁻¹ := by group
      have e2 : r = x⁻¹ * (x * r * x⁻¹) * x := by group
      rw [e2, e1]
      exact hr
  refine S.mem_of_act_mem_Rbar hxN ?_
  refine Rbar_centralizer (h.act_mem_Oq x) fun g hg => ?_
  obtain ⟨r, hr, rfl⟩ := S.hR.act_onto hg
  rw [← map_mul, ← map_mul, hx r hr]

theorem act_zK : S.hyp.act (zK z) = 1 := by
  have : (zK z : ↥(Hz z)) ∈ S.hyp.act.ker := by
    rw [S.hyp.ker_act]
    exact S.hyp.zU.2
  exact MonoidHom.mem_ker.mp this

theorem act_u_ne_one : S.hyp.act S.u ≠ 1 := by
  intro h1
  have hk : S.u ∈ S.hyp.act.ker := MonoidHom.mem_ker.mpr h1
  rcases S.hR.normalizer_inf_ker S.hu hk with h | h
  · have hu1 : S.u = 1 := Subtype.ext h
    apply S.σ₂_ne_σ₁
    unfold σ₂
    rw [hu1]
    simp
  · have hu1 : S.u = zK z := Subtype.ext h
    apply S.σ₂_ne_σ₁
    unfold σ₂
    have hzi : (zK z)⁻¹ = zK z := inv_eq_of_mul_eq_one_right (zK_mul_zK S.hyp)
    rw [hu1, hzi]
    calc zK z * S.σ₁ * zK z = S.σ₁ * zK z * zK z := by rw [zK_comm S.σ₁]
      _ = S.σ₁ := by rw [mul_assoc, zK_mul_zK S.hyp, mul_one]

theorem act_v_ne_one : S.hyp.act S.v ≠ 1 := by
  intro h1
  have hk : S.v ∈ S.hyp.act.ker := MonoidHom.mem_ker.mpr h1
  rcases S.hR.normalizer_inf_ker S.hv hk with h | h
  · have hv1 : S.v = 1 := Subtype.ext h
    have := S.vv
    rw [hv1, one_mul] at this
    exact zK_ne_one S.hyp this.symm
  · have hv1 : S.v = zK z := Subtype.ext h
    have := S.vv
    rw [hv1, zK_mul_zK S.hyp] at this
    exact zK_ne_one S.hyp this.symm

theorem act_uv_ne_one : S.hyp.act (S.u * S.v) ≠ 1 := by
  intro h1
  have hk : S.u * S.v ∈ S.hyp.act.ker := MonoidHom.mem_ker.mpr h1
  rcases S.hR.normalizer_inf_ker S.huv hk with h | h
  · have huv1 : S.u * S.v = 1 := Subtype.ext h
    have hv : S.v = S.u := by
      calc S.v = S.u⁻¹ * (S.u * S.v) := by group
        _ = S.u := by rw [huv1, mul_one, S.ui]
    have := S.vv
    rw [hv, S.uu] at this
    exact zK_ne_one S.hyp this.symm
  · have huv1 : S.u * S.v = zK z := Subtype.ext h
    have hv : S.v = S.u * zK z := by
      calc S.v = S.u⁻¹ * (S.u * S.v) := by group
        _ = S.u * zK z := by rw [huv1, S.ui]
    have h2 : S.v * S.v = 1 := by
      calc S.v * S.v = S.u * zK z * (S.u * zK z) := by rw [hv]
        _ = S.u * (zK z * S.u) * zK z := by group
        _ = S.u * (S.u * zK z) * zK z := by rw [zK_comm S.u]
        _ = (S.u * S.u) * (zK z * zK z) := by group
        _ = 1 := by rw [S.uu, zK_mul_zK S.hyp, one_mul]
    rw [S.vv] at h2
    exact zK_ne_one S.hyp h2

theorem sq_mem {n : ↥(Hz z)} (hn : n ∈ Subgroup.normalizer (S.R : Set ↥(Hz z))) :
    ∃ r ∈ S.R, n * n = r ∨ n * n = zK z * r := by
  classical
  have h := S.hyp
  set Φ := h.act.range with hΦ
  have hRΦ : Rbar ≤ Φ := fun g hg => by
    obtain ⟨r, -, hr⟩ := S.hR.act_onto hg
    exact ⟨r, hr⟩
  have hΦO : ∀ g ∈ Φ, g ∈ Oq := by
    rintro g ⟨x, rfl⟩
    exact h.act_mem_Oq x
  let Rb : Subgroup ↥Φ := Rbar.subgroupOf Φ
  have : Rb.Normal := ⟨fun r hr g => by
    have hr' : (r : MulAut (Multiplicative V4)) ∈ Rbar := hr
    exact conj_mem_Rbar (hΦO g g.2) hr'⟩
  have hcardRb : Nat.card Rb = 9 := by
    rw [← card_Rbar]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΦ).toEquiv
  have hcardQ : Nat.card (↥Φ ⧸ Rb) = 4 := by
    have h1 := Subgroup.card_mul_index Rb
    have h2 : Nat.card ↥Φ = 36 := h.card_range_act
    rw [hcardRb, h2] at h1
    rw [← Subgroup.index_eq_card]
    omega
  let au : ↥Φ := ⟨h.act S.u, ⟨S.u, rfl⟩⟩
  let av : ↥Φ := ⟨h.act S.v, ⟨S.v, rfl⟩⟩
  have hau2 : au * au = 1 := Subtype.ext (by
    show h.act S.u * h.act S.u = 1
    rw [← map_mul, S.uu, map_one])
  have hav2 : av * av = 1 := Subtype.ext (by
    show h.act S.v * h.act S.v = 1
    rw [← map_mul, S.vv, S.act_zK])
  have hau1 : (QuotientGroup.mk au : ↥Φ ⧸ Rb) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_Rbar_of_sq (by simpa using congrArg Subtype.val hau2) S.act_u_ne_one
  have hav1 : (QuotientGroup.mk av : ↥Φ ⧸ Rb) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_Rbar_of_sq (by simpa using congrArg Subtype.val hav2) S.act_v_ne_one
  have hauv : (QuotientGroup.mk au : ↥Φ ⧸ Rb) ≠ QuotientGroup.mk av := by
    rw [Ne, QuotientGroup.eq]
    have e : ((au⁻¹ * av : ↥Φ) : MulAut (Multiplicative V4)) = h.act (S.u * S.v) := by
      show (h.act S.u)⁻¹ * h.act S.v = h.act (S.u * S.v)
      rw [← map_inv, S.ui, map_mul]
    intro hmem
    have hmem' : ((au⁻¹ * av : ↥Φ) : MulAut (Multiplicative V4)) ∈ Rbar := hmem
    rw [e] at hmem'
    exact not_mem_Rbar_of_sq (by rw [← map_mul, S.uvuv, map_one]) S.act_uv_ne_one hmem'
  have hq := sq_eq_one_of_card_four hcardQ hau1 hav1 hauv
    (by rw [← QuotientGroup.mk_mul, hau2, QuotientGroup.mk_one])
    (by rw [← QuotientGroup.mk_mul, hav2, QuotientGroup.mk_one])
    (QuotientGroup.mk (⟨h.act n, ⟨n, rfl⟩⟩ : ↥Φ))
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hq
  have hq' : h.act n * h.act n ∈ Rbar := hq
  rw [← map_mul] at hq'
  exact S.mem_of_act_mem_Rbar (mul_mem hn hn) hq'

end JWSetup

end CFSG.Quasithin.H13.U43
