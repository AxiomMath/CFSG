module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Uniq

public section

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D : Type*} [Group D]

theorem RhoRel.conj_emb {a b s ρ : D} (h : RhoRel a b s ρ) (hT : TRel a b s) (w : Tc) :
    ρ * hT.emb w * ρ = hT.emb (sigma w) := by
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right h.hρ
  have hgen : ∀ w : Tc, w ∈ Subgroup.closure ({tA, tB, tS} : Set Tc) →
      ρ * hT.emb w * ρ = hT.emb (sigma w) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hT.emb_tA, sigma_tA, map_inv, hT.emb_tA]; exact h.hρa
      · rw [hT.emb_tB, sigma_tB, map_inv, hT.emb_tB]; exact h.hρb
      · rw [hT.emb_tS, sigma_tS, hT.emb_tS]; exact h.hρs
    | one => rw [map_one, sigma_one, map_one, mul_one, h.hρ]
    | mul x y hx hy ihx ihy =>
      have e : ρ * (hT.emb x * hT.emb y) * ρ = (ρ * hT.emb x * ρ) * (ρ * hT.emb y * ρ) := by
        calc ρ * (hT.emb x * hT.emb y) * ρ
            = ρ * hT.emb x * (ρ * ρ) * hT.emb y * ρ := by rw [h.hρ]; group
          _ = (ρ * hT.emb x * ρ) * (ρ * hT.emb y * ρ) := by group
      rw [map_mul, sigma_mul, map_mul, e, ihx, ihy]
    | inv x hx ih =>
      have e : sigma x⁻¹ = (sigma x)⁻¹ := map_inv sigmaHom x
      rw [map_inv, e, map_inv, ← ih]
      rw [mul_inv_rev, mul_inv_rev, hρinv]
      group
  exact hgen w (tc_closure ▸ Subgroup.mem_top w)

theorem rho_y_eq_of {a b s y ρ : D} (hB : BRel a b s y) (hρ2 : ρ * ρ = 1)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32) (τ : Tc → Tc)
    (hτ : ∀ w : Tc, ρ * hB.toTRel'.emb w * ρ = hB.toTRel'.emb (τ w))
    (hτm : ∀ w ∈ m2Sub, τ w ∈ m2Sub) (u : Tc) (hu : u ∈ m2Sub)
    (hFF1 : ∀ w ∈ m2Sub, τ (Fu alpha0 (τ w)) = Fu alpha0 (u⁻¹ * w * u))
    (hFF2 : u * Fu alpha0 (Fu alpha0 u) *
      Fu alpha0 (Fu alpha0 (Fu alpha0 (Fu alpha0 u))) = 1)
    (hy₂ : ρ * y * ρ ∈ Subgroup.closure ({a, b, s, y} : Set D))
    (hC : ∀ g ∈ Subgroup.closure ({a, b, s, y} : Set D),
      (∀ q ∈ m2Sub.map hB.toTRel'.emb, g * q = q * g) → g ∈ m2Sub.map hB.toTRel'.emb) :
    ρ * y * ρ = hB.toTRel'.emb u * y := by
  have hT := hB.toTRel'
  have hinj := hT.emb_injective hcard
  have hvB : VertexSpec hT m2Sub tT0 y (Fu alpha0) tT0 tT0 := hB.vertexSpec hinj
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hyinv : y⁻¹ * y = 1 := inv_mul_cancel y
  have hmemM : ∀ w ∈ m2Sub, hT.emb w ∈ m2Sub.map hT.emb := fun w hw =>
    Subgroup.mem_map_of_mem _ hw
  have hconj₂ : ∀ w ∈ m2Sub, (ρ * y * ρ)⁻¹ * hT.emb w * (ρ * y * ρ) =
      hT.emb (τ (Fu alpha0 (τ w))) := by
    intro w hw
    have e : (ρ * y * ρ)⁻¹ * hT.emb w * (ρ * y * ρ) =
        ρ * (y⁻¹ * (ρ * hT.emb w * ρ) * y) * ρ := by
      rw [mul_inv_rev, mul_inv_rev, hρinv]; group
    rw [e, hτ w, hvB.conj (τ w) (hτm w hw), hτ]
  have hconj' : ∀ w ∈ m2Sub, (hT.emb u * y)⁻¹ * hT.emb w * (hT.emb u * y) =
      hT.emb (Fu alpha0 (u⁻¹ * w * u)) := by
    intro w hw
    have hw' : u⁻¹ * w * u ∈ m2Sub :=
      m2Sub.mul_mem (m2Sub.mul_mem (m2Sub.inv_mem hu) hw) hu
    have e : (hT.emb u * y)⁻¹ * hT.emb w * (hT.emb u * y) =
        y⁻¹ * hT.emb (u⁻¹ * w * u) * y := by
      rw [map_mul, map_mul, map_inv, mul_inv_rev]; group
    rw [e, hvB.conj _ hw']
  have hceq : ∀ w ∈ m2Sub, (ρ * y * ρ)⁻¹ * hT.emb w * (ρ * y * ρ) =
      (hT.emb u * y)⁻¹ * hT.emb w * (hT.emb u * y) := fun w hw => by
    rw [hconj₂ w hw, hconj' w hw, hFF1 w hw]
  have hy3 : y ^ 3 = 1 := hvB.y_cube
  have hy'3 : (hT.emb u * y) ^ 3 = 1 := by
    have h1 : y * hT.emb u * y⁻¹ = hT.emb (Fu alpha0 (Fu alpha0 u)) := hvB.conj_pos hu
    have hm1 : Fu alpha0 (Fu alpha0 u) ∈ m2Sub := hvB.act_mem _ (hvB.act_mem _ hu)
    have h2 : y * hT.emb (Fu alpha0 (Fu alpha0 u)) * y⁻¹ =
        hT.emb (Fu alpha0 (Fu alpha0 (Fu alpha0 (Fu alpha0 u)))) := hvB.conj_pos hm1
    calc (hT.emb u * y) ^ 3 = (hT.emb u * y) * (hT.emb u * y) * (hT.emb u * y) := by
          rw [pow_three']
      _ = hT.emb u * (y * hT.emb u * y⁻¹) * (y * (y * hT.emb u * y⁻¹) * y⁻¹) *
            (y * y * y) := by group
      _ = hT.emb (u * Fu alpha0 (Fu alpha0 u) *
            Fu alpha0 (Fu alpha0 (Fu alpha0 (Fu alpha0 u)))) * y ^ 3 := by
          rw [h1, h2, map_mul, map_mul, pow_three']
      _ = 1 := by rw [hFF2, map_one, hy3, one_mul]
  have hy₂3 : (ρ * y * ρ) ^ 3 = 1 := by
    calc (ρ * y * ρ) ^ 3 = ρ * y * ρ * (ρ * y * ρ) * (ρ * y * ρ) := by rw [pow_three']
      _ = ρ * y * (ρ * ρ) * y * (ρ * ρ) * y * ρ := by group
      _ = ρ * (y * y * y) * ρ := by rw [hρ2]; group
      _ = 1 := by rw [← pow_three', hy3]; simp [hρ2]
  have hyB : y ∈ Subgroup.closure ({a, b, s, y} : Set D) := mem_closure_four_v a b s y
  have hu_mem : hT.emb u ∈ Subgroup.closure ({a, b, s, y} : Set D) := by
    have : hT.emb u ∈ Subgroup.closure ({a, b, s} : Set D) := by
      rw [← hT.emb_range]; exact ⟨u, rfl⟩
    exact closure_three_le_four a b s y this
  have hy'B : hT.emb u * y ∈ Subgroup.closure ({a, b, s, y} : Set D) :=
    Subgroup.mul_mem _ hu_mem hyB
  have hzB : (ρ * y * ρ) * (hT.emb u * y)⁻¹ ∈ Subgroup.closure ({a, b, s, y} : Set D) :=
    Subgroup.mul_mem _ hy₂ (Subgroup.inv_mem _ hy'B)
  have hzc : ∀ q ∈ m2Sub.map hT.emb, ((ρ * y * ρ) * (hT.emb u * y)⁻¹) * q =
      q * ((ρ * y * ρ) * (hT.emb u * y)⁻¹) := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    have h1 := hceq w hw
    set y₂ := ρ * y * ρ
    set y' := hT.emb u * y
    calc y₂ * y'⁻¹ * hT.emb w = y₂ * (y'⁻¹ * hT.emb w * y') * y'⁻¹ := by group
      _ = y₂ * (y₂⁻¹ * hT.emb w * y₂) * y'⁻¹ := by rw [h1]
      _ = hT.emb w * (y₂ * y'⁻¹) := by group
  have hzM := hC _ hzB hzc
  obtain ⟨wz, hwz, hwze⟩ := Subgroup.mem_map.mp hzM
  have hwzc : ∀ v ∈ m2Sub, wz * v = v * wz := by
    intro v hv
    apply hinj
    rw [map_mul, map_mul, hwze]
    exact hzc _ (hmemM v hv)
  obtain ⟨k, hk⟩ := m2_center wz hwz hwzc
  have hzk : (ρ * y * ρ) * (hT.emb u * y)⁻¹ = (a * b) ^ k.val := by
    rw [← hwze, hk, map_pow, hT.emb_tC]
  have hyc : y⁻¹ * (a * b) * y = a * b := hB.hyc
  have hyz : y⁻¹ * (a * b) ^ k.val * y = (a * b) ^ k.val := by
    have := conj_pow (a := y⁻¹) (b := a * b) (i := k.val)
    simp only [inv_inv] at this
    rw [← this, hyc]
  have hzy : (a * b) ^ k.val * y = y * (a * b) ^ k.val := by
    calc (a * b) ^ k.val * y = y * (y⁻¹ * (a * b) ^ k.val * y) := by group
      _ = y * (a * b) ^ k.val := by rw [hyz]
  have hzu : (a * b) ^ k.val * hT.emb u = hT.emb u * (a * b) ^ k.val := by
    have hc : tC ^ k.val * u = u * tC ^ k.val :=
      ((show Commute tC u from tC_central u).pow_left k.val).eq
    rw [← hT.emb_tC, ← map_pow, ← map_mul, ← map_mul, hc]
  have hcomm : Commute ((a * b) ^ k.val) (hT.emb u * y) := by
    show (a * b) ^ k.val * (hT.emb u * y) = hT.emb u * y * (a * b) ^ k.val
    calc (a * b) ^ k.val * (hT.emb u * y) = ((a * b) ^ k.val * hT.emb u) * y := by group
      _ = hT.emb u * ((a * b) ^ k.val * y) := by rw [hzu]; group
      _ = hT.emb u * (y * (a * b) ^ k.val) := by rw [hzy]
      _ = hT.emb u * y * (a * b) ^ k.val := by group
  have hy₂eq : ρ * y * ρ = (a * b) ^ k.val * (hT.emb u * y) := by
    rw [← hzk]; group
  have hz3 : ((a * b) ^ k.val) ^ 3 = 1 := by
    have := hy₂3
    rw [hy₂eq, hcomm.mul_pow, hy'3, mul_one] at this
    exact this
  have hz4 : ((a * b) ^ k.val) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : (a * b) ^ 4 = 1 := by
      rw [← hT.emb_tC, ← map_pow, tC_pow_four, map_one]
    rw [this, one_pow]
  have hz1 : (a * b) ^ k.val = 1 := by
    calc (a * b) ^ k.val = ((a * b) ^ k.val) ^ 4 * (((a * b) ^ k.val) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hz4, hz3]; simp
  rw [hy₂eq, hz1, one_mul]

theorem rho_y_eq {a b s y ρ : D} (hB : BRel a b s y) (hR : RhoRel a b s ρ)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hy₂ : ρ * y * ρ ∈ Subgroup.closure ({a, b, s, y} : Set D))
    (hC : ∀ g ∈ Subgroup.closure ({a, b, s, y} : Set D),
      (∀ q ∈ m2Sub.map hB.toTRel'.emb, g * q = q * g) → g ∈ m2Sub.map hB.toTRel'.emb) :
    ρ * y * ρ = a * b⁻¹ * y := by
  have hT := hB.toTRel'
  have hu : hT.emb tU = a * b⁻¹ := by rw [tU_eq, map_mul, map_inv, hT.emb_tA, hT.emb_tB]
  rw [← hu]
  exact rho_y_eq_of hB hR.hρ hcard sigma (fun w => hR.conj_emb hT w) sigma_m2 tU tU_mem
    sigma_alpha0_sigma tU_norm hy₂ hC

theorem rho_y_eq_one {a b s y ρ : D} (hB : BRel a b s y) (hρ2 : ρ * ρ = 1)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hρa : ρ * a = a * ρ) (hρb : ρ * b = b * ρ) (hρs : ρ * s = s * ρ)
    (hy₂ : ρ * y * ρ ∈ Subgroup.closure ({a, b, s, y} : Set D))
    (hC : ∀ g ∈ Subgroup.closure ({a, b, s, y} : Set D),
      (∀ q ∈ m2Sub.map hB.toTRel'.emb, g * q = q * g) → g ∈ m2Sub.map hB.toTRel'.emb) :
    ρ * y * ρ = y := by
  have hT := hB.toTRel'
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hconj : ∀ w : Tc, ρ * hT.emb w * ρ = hT.emb w := by
    intro w
    have hgen : ∀ w : Tc, w ∈ Subgroup.closure ({tA, tB, tS} : Set Tc) →
        ρ * hT.emb w = hT.emb w * ρ := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · rw [hT.emb_tA]; exact hρa
        · rw [hT.emb_tB]; exact hρb
        · rw [hT.emb_tS]; exact hρs
      | one => rw [map_one, mul_one, one_mul]
      | mul x y hx hy ihx ihy =>
        rw [map_mul]
        calc ρ * (hT.emb x * hT.emb y) = (ρ * hT.emb x) * hT.emb y := by group
          _ = (hT.emb x * ρ) * hT.emb y := by rw [ihx]
          _ = hT.emb x * (ρ * hT.emb y) := by group
          _ = hT.emb x * (hT.emb y * ρ) := by rw [ihy]
          _ = hT.emb x * hT.emb y * ρ := by group
      | inv x hx ih =>
        rw [map_inv]
        have h1 : ρ * (hT.emb x)⁻¹ = (hT.emb x)⁻¹ * ρ := by
          calc ρ * (hT.emb x)⁻¹ = (hT.emb x)⁻¹ * (hT.emb x * ρ) * (hT.emb x)⁻¹ := by group
            _ = (hT.emb x)⁻¹ * (ρ * hT.emb x) * (hT.emb x)⁻¹ := by rw [ih]
            _ = (hT.emb x)⁻¹ * ρ := by group
        exact h1
    calc ρ * hT.emb w * ρ = (hT.emb w * ρ) * ρ := by rw [hgen w (tc_closure ▸ Subgroup.mem_top w)]
      _ = hT.emb w := by rw [mul_assoc, hρ2, mul_one]
  have h := rho_y_eq_of hB hρ2 hcard id hconj (fun w hw => hw) 1 (m2Sub.one_mem)
    (fun w hw => by simp) alpha0_norm_one hy₂ hC
  rw [h, map_one, one_mul]

theorem closure_ab_eq {a b s : D} (hT : TRel a b s) :
    Subgroup.closure ({a, b} : Set D) = baseSub.map hT.emb := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨tA, mem_baseSub.mpr rfl, hT.emb_tA⟩
    · exact ⟨tB, mem_baseSub.mpr rfl, hT.emb_tB⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [hT.emb_apply, mem_baseSub.mp hw]
    have ha : a ∈ Subgroup.closure ({a, b} : Set D) := Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b} : Set D) := Subgroup.subset_closure (by simp)
    simpa using Subgroup.mul_mem _ (Subgroup.pow_mem _ ha w.i.val) (Subgroup.pow_mem _ hb w.j.val)

theorem exists_rho_A {a b s x ρ₀ : D} (hA : ARel a b s x)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (n1 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ₀ * e * ρ₀⁻¹ ∈ Subgroup.closure ({a, b} : Set D))
    (n2 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ₀⁻¹ * e * ρ₀ ∈ Subgroup.closure ({a, b} : Set D))
    (n3 : ∀ t ∈ Subgroup.closure ({a, b, s} : Set D),
      ρ₀ * t * ρ₀⁻¹ ∈ Subgroup.closure ({a, b, s} : Set D))
    (c1 : ρ₀⁻¹ * x * ρ₀ * x⁻¹ ∈ Subgroup.closure ({a, b} : Set D))
    (c2 : ρ₀ * ρ₀ ∈ Subgroup.closure ({a, b} : Set D)) :
    ∃ r ∈ Subgroup.closure ({a, b} : Set D),
      (ρ₀ * r) * (ρ₀ * r) = 1 ∧ (ρ₀ * r) * x * (ρ₀ * r) = x ∧ (ρ₀ * r) * s * (ρ₀ * r) = s ∧
        (((ρ₀ * r) * a * (ρ₀ * r) = a⁻¹ ∧ (ρ₀ * r) * b * (ρ₀ * r) = b⁻¹) ∨
          ((ρ₀ * r) * a = a * (ρ₀ * r) ∧ (ρ₀ * r) * b = b * (ρ₀ * r))) := by
  have hT := hA.toTRel
  have hinj := hT.emb_injective hcard
  have hvA := hA.vertexSpec hinj
  have hE := closure_ab_eq hT
  have hET : Subgroup.closure ({a, b} : Set D) ≤ Subgroup.closure ({a, b, s} : Set D) := by
    apply Subgroup.closure_mono
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto
  obtain ⟨w', hw', hw'e⟩ : ∃ w' ∈ baseSub, hT.emb w' = ρ₀⁻¹ * x * ρ₀ * x⁻¹ := by
    rw [hE] at c1
    exact Subgroup.mem_map.mp c1
  obtain ⟨v, hv, hve⟩ := xAct_surj w' hw'
  obtain ⟨r, hrdef⟩ : ∃ r, r = hT.emb v := ⟨_, rfl⟩
  have hrE : r ∈ Subgroup.closure ({a, b} : Set D) := by
    rw [hE, hrdef]; exact Subgroup.mem_map_of_mem _ hv
  have hr : r * x * r⁻¹ * x⁻¹ = ρ₀⁻¹ * x * ρ₀ * x⁻¹ := by
    have h1 : x * hT.emb v⁻¹ * x⁻¹ = hT.emb (xAct (xAct v⁻¹)) :=
      hvA.conj_pos (baseSub.inv_mem hv)
    calc r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
      _ = hT.emb v * (x * hT.emb v⁻¹ * x⁻¹) := by rw [hrdef, map_inv]
      _ = hT.emb (v * xAct (xAct v⁻¹)) := by rw [h1, map_mul]
      _ = ρ₀⁻¹ * x * ρ₀ * x⁻¹ := by rw [hve, hw'e]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = ρ₀ * r := ⟨_, rfl⟩
  refine ⟨r, hrE, ?_⟩
  rw [← hρdef]
  have hrx : r * x * r⁻¹ = ρ₀⁻¹ * x * ρ₀ := mul_right_cancel hr
  have hρx : ρ * x * ρ⁻¹ = x := by
    rw [hρdef]
    calc ρ₀ * r * x * (ρ₀ * r)⁻¹ = ρ₀ * (r * x * r⁻¹) * ρ₀⁻¹ := by group
      _ = x := by rw [hrx]; group
  have hρxc : ρ * x = x * ρ := by
    calc ρ * x = (ρ * x * ρ⁻¹) * ρ := by group
      _ = x * ρ := by rw [hρx]
  have N1 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ * e * ρ⁻¹ ∈ Subgroup.closure ({a, b} : Set D) := by
    intro e he
    have h1 : r * e * r⁻¹ ∈ Subgroup.closure ({a, b} : Set D) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hrE he) (Subgroup.inv_mem _ hrE)
    have := n1 _ h1
    rwa [show ρ₀ * (r * e * r⁻¹) * ρ₀⁻¹ = ρ * e * ρ⁻¹ by rw [hρdef]; group] at this
  have N2 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ⁻¹ * e * ρ ∈ Subgroup.closure ({a, b} : Set D) := by
    intro e he
    have h1 := n2 e he
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hrE) h1) hrE
    rwa [show r⁻¹ * (ρ₀⁻¹ * e * ρ₀) * r = ρ⁻¹ * e * ρ by rw [hρdef]; group] at this
  have N3 : ∀ t ∈ Subgroup.closure ({a, b, s} : Set D),
      ρ * t * ρ⁻¹ ∈ Subgroup.closure ({a, b, s} : Set D) := by
    intro t ht
    have h1 : r * t * r⁻¹ ∈ Subgroup.closure ({a, b, s} : Set D) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hET hrE) ht) (Subgroup.inv_mem _ (hET hrE))
    have := n3 _ h1
    rwa [show ρ₀ * (r * t * r⁻¹) * ρ₀⁻¹ = ρ * t * ρ⁻¹ by rw [hρdef]; group] at this
  have hρ2E : ρ * ρ ∈ Subgroup.closure ({a, b} : Set D) := by
    have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (n1 r hrE) c2) hrE
    rwa [show ρ₀ * r * ρ₀⁻¹ * (ρ₀ * ρ₀) * r = ρ * ρ by rw [hρdef]; group] at h1
  have hρ2 : ρ * ρ = 1 := by
    rw [hE] at hρ2E
    obtain ⟨w₂, hw₂, hw₂e⟩ := Subgroup.mem_map.mp hρ2E
    have hcomm2 : (ρ * ρ) * x = x * (ρ * ρ) := by
      calc ρ * ρ * x = ρ * (ρ * x) := by group
        _ = ρ * (x * ρ) := by rw [hρxc]
        _ = (ρ * x) * ρ := by group
        _ = (x * ρ) * ρ := by rw [hρxc]
        _ = x * (ρ * ρ) := by group
    have hfix : hT.emb (xAct w₂) = hT.emb w₂ := by
      rw [← hA.conj_emb w₂ hw₂, hw₂e]
      rw [mul_assoc, hcomm2]
      group
    have := xAct_fixed w₂ hw₂ (hinj hfix)
    rw [← hw₂e, this, map_one]
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  rw [hρinv] at hρx N1 N2 N3
  have hs_mem : s ∈ Subgroup.closure ({a, b, s} : Set D) := Subgroup.subset_closure (by simp)
  have hsE : s ∉ Subgroup.closure ({a, b} : Set D) := by
    intro h
    rw [hE] at h
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp h
    have : w = tS := hinj (by rw [hwe, hT.emb_tS])
    rw [this] at hw
    exact absurd (mem_baseSub.mp hw) (by decide +kernel)
  obtain ⟨w₁, hw₁⟩ : ρ * s * ρ ∈ hT.emb.range := by
    rw [hT.emb_range]; exact N3 s hs_mem
  have hw₁b : w₁ ∉ baseSub := by
    intro hb
    apply hsE
    have h1 : hT.emb w₁ ∈ Subgroup.closure ({a, b} : Set D) := by
      rw [hE]; exact Subgroup.mem_map_of_mem _ hb
    rw [hw₁] at h1
    have := N2 _ h1
    rwa [show ρ * (ρ * s * ρ) * ρ = s by
      calc ρ * (ρ * s * ρ) * ρ = (ρ * ρ) * s * (ρ * ρ) := by group
        _ = s := by rw [hρ2]; group] at this
  obtain ⟨w₀, hw₀, hw₀e⟩ := exists_base_mul_tS w₁ hw₁b
  obtain ⟨e₁, he₁def⟩ : ∃ e₁, e₁ = hT.emb w₀ := ⟨_, rfl⟩
  have hρs₀ : ρ * s * ρ = e₁ * s := by
    rw [← hw₁, hw₀e, map_mul, hT.emb_tS, he₁def]
  have hsxs : s * x * s⁻¹ = x⁻¹ := by
    have h2 : s⁻¹ = s := hT.s_inv
    have hss : s * s = 1 := hT.ss
    rw [h2]
    calc s * x * s = (x⁻¹ * (x * s * x)) * s := by group
      _ = x⁻¹ * s * s := by rw [hA.hxs]
      _ = x⁻¹ := by rw [mul_assoc, hss, mul_one]
  have hρinv_s : ρ * s⁻¹ * ρ = (ρ * s * ρ)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hρinv]; group
  have hρxinv : ρ * x⁻¹ * ρ = x⁻¹ := by
    have : ρ * x⁻¹ * ρ = (ρ * x * ρ)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hρinv]; group
    rw [this, hρx]
  have he₁1 : e₁ = 1 := by
    have h1 : ρ * (s * x * s⁻¹) * ρ = (ρ * s * ρ) * (ρ * x * ρ) * (ρ * s⁻¹ * ρ) := by
      have : ρ * (s * x * s⁻¹) * ρ = ρ * s * (ρ * ρ) * x * (ρ * ρ) * s⁻¹ * ρ := by
        rw [hρ2]; group
      rw [this]; group
    rw [hsxs, hρxinv, hρinv_s, hρs₀, hρx] at h1
    have h3 : x⁻¹ = e₁ * (s * x * s⁻¹) * e₁⁻¹ := by
      rw [h1]; group
    rw [hsxs] at h3
    have hcomm : x⁻¹ * e₁ = e₁ * x⁻¹ := by
      calc x⁻¹ * e₁ = (e₁ * x⁻¹ * e₁⁻¹) * e₁ := by rw [← h3]
        _ = e₁ * x⁻¹ := by group
    have he₁E : e₁ ∈ baseSub.map hT.emb := ⟨w₀, hw₀, he₁def.symm⟩
    have hfix : hT.emb (xAct w₀) = hT.emb w₀ := by
      rw [← hA.conj_emb w₀ hw₀, ← he₁def]
      calc x⁻¹ * e₁ * x = (e₁ * x⁻¹) * x := by rw [hcomm]
        _ = e₁ := by group
    have := xAct_fixed w₀ hw₀ (hinj hfix)
    rw [he₁def, this, map_one]
  have hρs : ρ * s * ρ = s := by rw [hρs₀, he₁1, one_mul]
  refine ⟨hρ2, hρx, hρs, ?_⟩
  have haE : a ∈ Subgroup.closure ({a, b} : Set D) := Subgroup.subset_closure (by simp)
  have hfA : ρ * a * ρ ∈ Subgroup.closure ({a, b} : Set D) := N1 a haE
  obtain ⟨wA, hwA, hwAe⟩ : ∃ wA ∈ baseSub, hT.emb wA = ρ * a * ρ := by
    rw [hE] at hfA; exact Subgroup.mem_map.mp hfA
  have hb_s : b = s * a * s⁻¹ := by rw [hT.s_inv]; exact hT.hsa.symm
  have hb_x : b = x⁻¹ * a * x := hA.hxa.symm
  have hρb_s : ρ * b * ρ = s * (ρ * a * ρ) * s⁻¹ := by
    calc ρ * b * ρ = ρ * (s * a * s⁻¹) * ρ := by rw [← hb_s]
      _ = (ρ * s * ρ) * (ρ * a * ρ) * (ρ * s⁻¹ * ρ) := by
          have : ρ * (s * a * s⁻¹) * ρ = ρ * s * (ρ * ρ) * a * (ρ * ρ) * s⁻¹ * ρ := by
            rw [hρ2]; group
          rw [this]; group
      _ = s * (ρ * a * ρ) * s⁻¹ := by rw [hρinv_s, hρs]
  have hρb_x : ρ * b * ρ = x⁻¹ * (ρ * a * ρ) * x := by
    calc ρ * b * ρ = ρ * (x⁻¹ * a * x) * ρ := by rw [← hb_x]
      _ = (ρ * x⁻¹ * ρ) * (ρ * a * ρ) * (ρ * x * ρ) := by
          have : ρ * (x⁻¹ * a * x) * ρ = ρ * x⁻¹ * (ρ * ρ) * a * (ρ * ρ) * x * ρ := by
            rw [hρ2]; group
          rw [this]; group
      _ = x⁻¹ * (ρ * a * ρ) * x := by rw [hρxinv, hρx]
  have hswap : tS * wA * tS⁻¹ = xAct wA := by
    have e1 : hT.emb (tS * wA * tS⁻¹) = s * (ρ * a * ρ) * s⁻¹ := by
      rw [map_mul, map_mul, map_inv, hT.emb_tS, hwAe]
    have e2 : hT.emb (xAct wA) = x⁻¹ * (ρ * a * ρ) * x := by
      rw [← hA.conj_emb wA hwA, hwAe]
    exact hinj (e1.trans ((hρb_s.symm.trans hρb_x).trans e2.symm))
  have hwA' : wA = tA ^ wA.i.val := swap_xAct wA hwA hswap
  have hfA_eq : ρ * a * ρ = a ^ wA.i.val := by
    calc ρ * a * ρ = hT.emb wA := hwAe.symm
      _ = hT.emb (tA ^ wA.i.val) := congrArg hT.emb hwA'
      _ = a ^ wA.i.val := by rw [map_pow, hT.emb_tA]
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, ρ * a * ρ = a ^ i.val := ⟨wA.i, hfA_eq⟩
  have hconjpow : ∀ n : ℕ, ρ * a ^ n * ρ = (ρ * a * ρ) ^ n := fun n => by
    have := conj_pow (a := ρ) (b := a) (i := n)
    rw [hρinv] at this
    exact this.symm
  have hsq : tA ^ (i.val * i.val) = tA := by
    apply hinj
    rw [map_pow, hT.emb_tA]
    calc a ^ (i.val * i.val) = (a ^ i.val) ^ i.val := by rw [← pow_mul]
      _ = (ρ * a * ρ) ^ i.val := by rw [hi]
      _ = ρ * a ^ i.val * ρ := (hconjpow i.val).symm
      _ = ρ * (ρ * a * ρ) * ρ := by rw [hi]
      _ = a := by
        calc ρ * (ρ * a * ρ) * ρ = (ρ * ρ) * a * (ρ * ρ) := by group
          _ = a := by rw [hρ2]; group
  have hρb : ρ * b * ρ = s * (a ^ i.val) * s⁻¹ := by rw [hρb_s, hi]
  rcases odd_of_sq i hsq with rfl | rfl
  ·
    have ha1 : ρ * a * ρ = a := by simpa using hi
    have hb1 : ρ * b * ρ = b := by
      rw [hρb]
      simp only [Fin.val_one, pow_one]
      rw [hb_s]
    right
    constructor
    · calc ρ * a = (ρ * a * ρ) * ρ := by
            calc ρ * a = ρ * a * (ρ * ρ) := by rw [hρ2, mul_one]
              _ = (ρ * a * ρ) * ρ := by group
        _ = a * ρ := by rw [ha1]
    · calc ρ * b = (ρ * b * ρ) * ρ := by
            calc ρ * b = ρ * b * (ρ * ρ) := by rw [hρ2, mul_one]
              _ = (ρ * b * ρ) * ρ := by group
        _ = b * ρ := by rw [hb1]
  ·
    have h3 : a ^ (3 : Fin 4).val = a⁻¹ := by
      show a ^ 3 = a⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hT.ha
    have ha1 : ρ * a * ρ = a⁻¹ := by rw [hi, h3]
    have hb1 : ρ * b * ρ = b⁻¹ := by
      rw [hρb, h3, hb_s]; group
    left
    exact ⟨ha1, hb1⟩

end CFSG.Quasithin.F6.GoldAmL4
