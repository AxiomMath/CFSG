module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] {A B : Subgroup D} {V V₂ : Subgroup D}

theorem commutator_mem_Fx {γ δ : CosetGeom (A ⊔ B) A B} (hV : GoodV V V₂ γ) (hE : GoodE V V₂ γ δ)
    {u v : D} (hu : u ∈ stab γ ⊓ stab δ) (hun : u ∉ ballStab 1 γ)
    (hv : v ∈ Nm A B V V₂ γ) : v⁻¹ * u⁻¹ * v * u ∈ Fx V V₂ γ δ := by
  have hu1 : u ∈ stab γ := hu.1
  have hNm : ∀ x ∈ Nm A B V V₂ γ, ∀ g ∈ stab γ, g * x * g⁻¹ ∈ Nm A B V V₂ γ := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (hV.norm hg) x).mp hx
  have hconj : u⁻¹ * v * u ∈ Nm A B V V₂ γ := by
    have := hNm v hv u⁻¹ ((stab γ).inv_mem hu1)
    simpa using this
  have hh : v⁻¹ * u⁻¹ * v * u ∈ Nm A B V V₂ γ := by
    have := (Nm A B V V₂ γ).mul_mem ((Nm A B V V₂ γ).inv_mem hv) hconj
    simpa [mul_assoc] using this
  have hu2 : u * u ∈ ballStab 1 γ := by
    have hinv : u⁻¹ ∈ stab γ ⊓ stab δ := (stab γ ⊓ stab δ).inv_mem hu
    have hinvn : u⁻¹ ∉ ballStab 1 γ := fun h => hun (by simpa using (ballStab 1 γ).inv_mem h)
    have := hE.index u⁻¹ u hinv hu hinvn hun
    simpa using this
  have hc2 : v * (u * u) = (u * u) * v := hV.qv_cent _ hu2 v hv
  have key1 : u⁻¹ * v * u = u * v * u⁻¹ := by
    have : u * (u⁻¹ * v * u) * u = u * (u * v * u⁻¹) * u := by
      calc u * (u⁻¹ * v * u) * u = v * (u * u) := by group
        _ = (u * u) * v := hc2
        _ = u * (u * v * u⁻¹) * u := by group
    exact mul_left_cancel (mul_right_cancel this)
  have key2 : u * (u * v * u⁻¹) * u⁻¹ = v := by
    calc u * (u * v * u⁻¹) * u⁻¹ = (u * u) * v * (u * u)⁻¹ := by group
      _ = v := by rw [← hc2]; group
  have hsq : (v⁻¹ * u⁻¹ * v * u) * (v⁻¹ * u⁻¹ * v * u) = 1 := hV.sq _ hh
  have hfix : u * (v⁻¹ * u⁻¹ * v * u) * u⁻¹ = v⁻¹ * u⁻¹ * v * u := by
    have h1 : u * (v⁻¹ * u⁻¹ * v * u) * u⁻¹ = (v⁻¹ * u⁻¹ * v * u)⁻¹ := by
      calc u * (v⁻¹ * u⁻¹ * v * u) * u⁻¹
          = (u * v * u⁻¹)⁻¹ * (u * (u⁻¹ * v * u) * u⁻¹) := by group
        _ = (u * v * u⁻¹)⁻¹ * (u * (u * v * u⁻¹) * u⁻¹) := by rw [key1]
        _ = (u * v * u⁻¹)⁻¹ * v := by rw [key2]
        _ = (u⁻¹ * v * u)⁻¹ * v := by rw [key1]
        _ = (v⁻¹ * u⁻¹ * v * u)⁻¹ := by group
    rw [h1]
    exact (eq_inv_of_mul_eq_one_left hsq).symm
  rw [mem_Fx]
  refine ⟨hh, fun w hw => ?_⟩
  by_cases hwn : w ∈ ballStab 1 γ
  · exact (hV.qv_cent w hwn _ hh).symm
  · have hm : u⁻¹ * w ∈ ballStab 1 γ := hE.index u w hu hw hun hwn
    have hcm := hV.qv_cent _ hm _ hh
    have hcomm : u * (v⁻¹ * u⁻¹ * v * u) = (v⁻¹ * u⁻¹ * v * u) * u := by
      calc u * (v⁻¹ * u⁻¹ * v * u) = (u * (v⁻¹ * u⁻¹ * v * u) * u⁻¹) * u := by group
        _ = (v⁻¹ * u⁻¹ * v * u) * u := by rw [hfix]
    calc w * (v⁻¹ * u⁻¹ * v * u)
        = u * ((u⁻¹ * w) * (v⁻¹ * u⁻¹ * v * u)) := by group
      _ = u * ((v⁻¹ * u⁻¹ * v * u) * (u⁻¹ * w)) := by rw [← hcm]
      _ = (u * (v⁻¹ * u⁻¹ * v * u)) * (u⁻¹ * w) := by group
      _ = ((v⁻¹ * u⁻¹ * v * u) * u) * (u⁻¹ * w) := by rw [hcomm]
      _ = (v⁻¹ * u⁻¹ * v * u) * w := by group

theorem not_nm_le_symm {x y : CosetGeom (A ⊔ B) A B} (hVx : GoodV V V₂ x) (hVy : GoodV V V₂ y)
    (hle : Nm A B V V₂ x ≤ stab y) (hnot : ¬ Nm A B V V₂ x ≤ ballStab 1 y) :
    ¬ Nm A B V V₂ y ≤ ballStab 1 x := by
  intro h
  apply hnot
  intro a ha
  refine hVy.cent_le a (hle ha) fun b hb => ?_
  exact (hVx.qv_cent b (h hb) a ha).symm

variable [Finite D] {z c : D}

theorem exists_commutator (h : TwoNat A B z V c V₂) {x y p q : CosetGeom (A ⊔ B) A B}
    (hq : (graph (A ⊔ B) A B).Adj y q) (hp : (graph (A ⊔ B) A B).Adj p x)
    (hxq : Nm A B V V₂ x ≤ ballStab 1 q) (hyp : Nm A B V V₂ y ≤ ballStab 1 p)
    (hnot : ¬ Nm A B V V₂ x ≤ ballStab 1 y) :
    ∃ t : D, t ∈ Nm A B V V₂ x ∧ t ∈ Nm A B V V₂ y ∧ t ≠ 1 ∧ t ∈ Fx V V₂ y q := by
  have hVx := goodV_all h x
  have hVy := goodV_all h y
  have hEyq := goodE_all h hq
  have hxy : Nm A B V V₂ x ≤ stab y := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := q) (δ := y)
      (dist_eq_one_iff_adj.mpr hq.symm).le (hxq ha)
  have hyx : Nm A B V V₂ y ≤ stab x := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := p) (δ := x)
      (dist_eq_one_iff_adj.mpr hp).le (hyp ha)
  have hxq' : Nm A B V V₂ x ≤ stab q := fun a ha => ballStab_le_stab 1 q (hxq ha)
  have hnot' : ¬ Nm A B V V₂ y ≤ ballStab 1 x := not_nm_le_symm hVx hVy hxy hnot
  obtain ⟨f, hfx, hfn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨g, hgy, hgn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot'
  have hfE : f ∈ stab y ⊓ stab q := ⟨hxy hfx, hxq' hfx⟩
  have hNy : ∀ w ∈ Nm A B V V₂ y, ∀ k ∈ stab y, k * w * k⁻¹ ∈ Nm A B V V₂ y := fun w hw k hk =>
    (Subgroup.mem_normalizer_iff.mp (hVy.norm hk) w).mp hw
  have hNx : ∀ w ∈ Nm A B V V₂ x, ∀ k ∈ stab x, k * w * k⁻¹ ∈ Nm A B V V₂ x := fun w hw k hk =>
    (Subgroup.mem_normalizer_iff.mp (hVx.norm hk) w).mp hw
  refine ⟨f⁻¹ * g⁻¹ * f * g, ?_, ?_, ?_, ?_⟩
  · have h1 := hNx f hfx g⁻¹ ((stab x).inv_mem (hyx hgy))
    have := (Nm A B V V₂ x).mul_mem ((Nm A B V V₂ x).inv_mem hfx) h1
    simpa [mul_assoc] using this
  · have h1 := hNy g⁻¹ ((Nm A B V V₂ y).inv_mem hgy) f⁻¹ ((stab y).inv_mem (hxy hfx))
    have := (Nm A B V V₂ y).mul_mem h1 hgy
    simpa [mul_assoc] using this
  · intro h1
    have h2 : g⁻¹ * f * g = f := by
      calc g⁻¹ * f * g = f * (f⁻¹ * g⁻¹ * f * g) := by group
        _ = f := by rw [h1, mul_one]
    have hcomm : f * g = g * f := by
      calc f * g = g * (g⁻¹ * f * g) := by group
        _ = g * f := by rw [h2]
    apply hgn
    refine hVx.cent_le g (hyx hgy) fun k hk => ?_
    by_cases hkn : k ∈ ballStab 1 y
    · exact (hVy.qv_cent k hkn g hgy).symm
    · have hkE : k ∈ stab y ⊓ stab q := ⟨hxy hk, hxq' hk⟩
      have hk' : f⁻¹ * k ∈ ballStab 1 y := hEyq.index f k hfE hkE hfn hkn
      have hc := hVy.qv_cent _ hk' g hgy
      calc k * g = f * ((f⁻¹ * k) * g) := by group
        _ = f * (g * (f⁻¹ * k)) := by rw [← hc]
        _ = (f * g) * (f⁻¹ * k) := by group
        _ = (g * f) * (f⁻¹ * k) := by rw [hcomm]
        _ = g * k := by group
  · have := commutator_mem_Fx hVy hEyq hfE hfn hgy
    have h2 := (Fx V V₂ y q).inv_mem this
    have e : (g⁻¹ * f⁻¹ * g * f)⁻¹ = f⁻¹ * g⁻¹ * f * g := by group
    rwa [e] at h2

theorem exists_crit (h : TwoNat A B z V c V₂) :
    ∃ x y : CosetGeom (A ⊔ B) A B, ¬ Nm A B V V₂ x ≤ ballStab 1 y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, -, hn⟩ := exists_ballStab_eq_bot h.gold.amalgamHyp
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hV : V ≤ ballStab n (γ₀ (A ⊔ B) A B) := by
    intro a ha
    rw [mem_ballStab]
    intro δ _
    have ha' : a ∈ Nm A B V V₂ (γ₀ (A ⊔ B) A B) := by rw [Nm_γ₀ hA]; exact ha
    exact ballStab_le_stab 1 δ (hcon _ δ ha')
  rw [hn] at hV
  exact h.nat.z_ne (Subgroup.mem_bot.mp (hV h.nat.z_mem_V))

end GoldAmLab6

end F6

end CFSG.Quasithin
