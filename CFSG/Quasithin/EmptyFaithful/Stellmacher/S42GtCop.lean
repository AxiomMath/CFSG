module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtGrp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S42Gt

open CosetGeom F53 S42B1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

private theorem perm_three_conj :
    ∀ σ c : Equiv.Perm (Fin 3), c * c * c = 1 → σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹ := by
  decide +kernel

theorem conj_cases (hA : F53Amalgam H M S) (hv : vtype β = true) {d g : G} (hd : d ∈ stab β)
    (hd3 : d * d * d = 1) (hg : g ∈ stab β) :
    ∃ q ∈ Qv β, g * d * g⁻¹ = d * q ∨ g * d * g⁻¹ = d⁻¹ * q := by
  obtain ⟨θ, -, hθk⟩ := exists_quotHom_true hA hv
  have hcube : θ ⟨d, hd⟩ * θ ⟨d, hd⟩ * θ ⟨d, hd⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have : (⟨d, hd⟩ * ⟨d, hd⟩ * ⟨d, hd⟩ : ↥(stab β)) = 1 := Subtype.ext hd3
    rw [this, map_one]
  have hg' : (⟨g, hg⟩ * ⟨d, hd⟩ * ⟨g, hg⟩⁻¹ : ↥(stab β)) = ⟨g * d * g⁻¹, by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hd) (Subgroup.inv_mem _ hg)⟩ := rfl
  have hgd : g * d * g⁻¹ ∈ stab β :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hd) (Subgroup.inv_mem _ hg)
  rcases perm_three_conj (θ ⟨g, hg⟩) (θ ⟨d, hd⟩) hcube with h | h
  · refine ⟨d⁻¹ * (g * d * g⁻¹), ?_, Or.inl (by group)⟩
    have hdi : d⁻¹ ∈ stab β := Subgroup.inv_mem _ hd
    have := (hθk ⟨d⁻¹ * (g * d * g⁻¹), Subgroup.mul_mem _ hdi hgd⟩).mp ?_
    · exact this
    · have e : (⟨d⁻¹ * (g * d * g⁻¹), Subgroup.mul_mem _ hdi hgd⟩ : ↥(stab β)) =
          ⟨d, hd⟩⁻¹ * (⟨g, hg⟩ * ⟨d, hd⟩ * ⟨g, hg⟩⁻¹) := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h, inv_mul_cancel]
  · refine ⟨d * (g * d * g⁻¹), ?_, Or.inr (by group)⟩
    have := (hθk ⟨d * (g * d * g⁻¹), Subgroup.mul_mem _ hd hgd⟩).mp ?_
    · exact this
    · have e : (⟨d * (g * d * g⁻¹), Subgroup.mul_mem _ hd hgd⟩ : ↥(stab β)) =
          ⟨d, hd⟩ * (⟨g, hg⟩ * ⟨d, hd⟩ * ⟨g, hg⟩⁻¹) := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, h, mul_inv_cancel]

omit [Finite G] in
theorem omega_le (Q : Subgroup G) :
    quasithinOmegaOneCenter Q ≤ Q ⊓ Subgroup.centralizer (Q : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hy => hy.1

omit [Finite G] in
theorem omega_sq (Q : Subgroup G) : ∀ z ∈ quasithinOmegaOneCenter Q, z * z = 1 := by
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem x hx => rw [← pow_two]; exact hx.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxT : x ∈ Q := (omega_le Q hx).1
    have hyC : y ∈ Subgroup.centralizer (Q : Set G) := (omega_le Q hy).2
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hyC x hxT).symm
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

omit [Finite G] in
theorem omega_norm {g : G} (hg : g ∈ stab β) {x : G} (hx : x ∈ quasithinOmegaOneCenter (Qv β)) :
    g * x * g⁻¹ ∈ quasithinOmegaOneCenter (Qv β) := by
  have hc : conjSub g (quasithinOmegaOneCenter (Qv β)) = quasithinOmegaOneCenter (Qv β) := by
    rw [conjSub_omegaOneCenter, conjSub_Qv_of_mem_stab (g := ⟨g, stab_le β hg⟩) hg]
  have := (conj_mem_conjSub_iff (g := g) (y := x) (C := quasithinOmegaOneCenter (Qv β))).mpr hx
  rwa [hc] at this

namespace Sit

theorem centralizes_omega (hs : Sit H M S α a₂ a₃ β) {d : G} (hd : d ∈ stab β)
    (hd3 : d * d * d = 1) : ∀ w ∈ quasithinOmegaOneCenter (Qv β), d * w * d⁻¹ = w := by
  have hWQ : quasithinOmegaOneCenter (Qv β) ≤ Qv β := fun x hx => (omega_le _ hx).1
  have hWC : ∀ x ∈ quasithinOmegaOneCenter (Qv β), ∀ y ∈ Qv β, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (omega_le _ hx).2 y hy).symm
  have hE : ElemNorm (quasithinOmegaOneCenter (Qv β)) d :=
    ⟨fun x hx y hy => Subgroup.mem_centralizer_iff.mp (omega_le _ hy).2 x (hWQ hx),
      omega_sq _, fun x hx => omega_norm hd hx, hd3⟩
  by_contra hcon
  push Not at hcon
  have hne : dCom _ d hE ≠ ⊥ := fun hb => by
    obtain ⟨w, hw, hwne⟩ := hcon
    exact hwne ((dCom_eq_bot_iff hE).mp hb w hw)
  have hT2 : IsPGroup 2 ((stab β ⊓ stab α : Subgroup G)) := (sylow_stab_inf_left hs.amalg hs.n₁).2.1
  have hQT : Qv β ≤ stab β ⊓ stab α := Qv_le_inf hs.amalg hs.n₁
  have hUT : dCom _ d hE ≤ stab β ⊓ stab α := (dCom_le hE).trans (hWQ.trans hQT)
  have key : ∀ t ∈ stab β ⊓ stab α, ∀ u ∈ dCom _ d hE, t * u * t⁻¹ ∈ dCom _ d hE := by
    intro t ht
    obtain ⟨q, hq, hdq⟩ := conj_cases hs.amalg hs.vβ hd hd3 ht.1
    refine dCom_conj_of_mem hE (fun x hx => omega_norm ht.1 hx) (fun x hx => ?_) hdq
    rw [← hWC x hx q hq]
    group
  have hTn : stab β ⊓ stab α ≤ Subgroup.normalizer ((dCom _ d hE : Subgroup G) : Set G) := by
    intro t ht
    exact F53B3.O1.mem_normalizer_of_conj (key t ht)
      (fun x hx => by simpa using key t⁻¹ (Subgroup.inv_mem _ ht) x hx)
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (F53B3.O1.inf_centralizer_ne_bot_of_normalized hT2 hUT hTn hne)
  obtain ⟨heU, heC⟩ := Subgroup.mem_inf.mp he
  have heW : e ∈ quasithinOmegaOneCenter (Qv β) := dCom_le hE heU
  have heΩ : e ∈ quasithinOmegaOneCenter (stab β ⊓ stab α) :=
    Subgroup.subset_closure ⟨⟨hUT heU, heC⟩, by rw [pow_two]; exact omega_sq _ e heW⟩
  have heZ : e ∈ Zv β := by
    rw [(Zv_eq_omegaOneCenter_inf hs.amalg hs.n₁ hs.hz).1]
    exact heΩ
  have hfix : d * e * d⁻¹ = e := by
    have := Subgroup.mem_centralizer_iff.mp (hs.hz heZ).2 d hd
    rw [this]
    group
  exact he1 (Subtype.ext (eq_one_of_fix hE heU hfix))

end Sit

end F53.Stellmacher.S42Gt

end CFSG.Quasithin
