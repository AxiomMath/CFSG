module

public import CFSG.Sporadic.Co1Patterson.AmalgamGlue

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

variable {G X : Type*} [Group G] [Group X]

@[expose] def coreOf (K : Subgroup G) : Subgroup G := (CFSG.pCore 2 K).map K.subtype

theorem coreOf_le (K : Subgroup G) : coreOf K ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_coreOf_coe {K : Subgroup G} (x : K) : (x : G) ∈ coreOf K ↔ x ∈ CFSG.pCore 2 K := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem IsoOn.map_mem_coreOf {A : G → X} {K : Subgroup G} {K' : Subgroup X} (hA : IsoOn A K K')
    {x : G} (hx : x ∈ coreOf K) : A x ∈ coreOf K' := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h := CFSG.pCore_map_iso 2 hA.toMulEquiv
  have hy' : hA.toMulEquiv y ∈ CFSG.pCore 2 K' := h ▸ ⟨y, hy, rfl⟩
  exact ⟨hA.toMulEquiv y, hy', rfl⟩

theorem conj_mem_inf_iff {a w s : G} (hs1 : s * a * s⁻¹ = w) (hs2 : s * w * s⁻¹ = a) (x : G) :
    x ∈ C[a] ⊓ C[w] ↔ s⁻¹ * x * s⁻¹⁻¹ ∈ C[a] ⊓ C[w] := by
  have e1 : s⁻¹ * a * s⁻¹⁻¹ = w := by rw [inv_inv, ← hs2]; group
  have e2 : s⁻¹ * w * s⁻¹⁻¹ = a := by rw [inv_inv, ← hs1]; group
  rw [mem_inf, mem_inf, mem_cent_conj_iff s⁻¹ x a, mem_cent_conj_iff s⁻¹ x w, e1, e2]
  exact and_comm

theorem exists_isoOn_agree {A : G → X} {a w s : G} {t W g : X} (hA : IsoOn A C[a] C[t])
    (hAa : A a = t) (hwa : w ∈ C[a]) (hAw : A w = W) (hs1 : s * a * s⁻¹ = w)
    (hs2 : s * w * s⁻¹ = a) (hg1 : g * t * g⁻¹ = W) (hg2 : g * W * g⁻¹ = t)
    (hsO : ∀ k ∈ C[a] ⊓ C[w], s⁻¹ * k * s * k⁻¹ ∈ coreOf (C[a] ⊓ C[w]))
    (hgO : ∀ k ∈ C[t] ⊓ C[W], g * k * g⁻¹ * k⁻¹ ∈ coreOf (C[t] ⊓ C[W]))
    (hrig : AutInnerModAt a w) :
    ∃ Z : G → X, IsoOn Z C[w] C[W] ∧ (∀ x ∈ C[a] ⊓ C[w], Z x = A x) ∧ Z w = W := by
  have hAK : IsoOn A (C[a] ⊓ C[w]) (C[t] ⊓ C[W]) := by
    have := hA.inf_cent hwa
    rwa [hAw] at this
  have haw : a ∈ C[a] ⊓ C[w] :=
    mem_inf.2 ⟨mem_cent_iff.2 rfl, mem_cent_iff.2 (mem_cent_iff.1 hwa).symm⟩
  have hww : w ∈ C[a] ⊓ C[w] := mem_inf.2 ⟨hwa, mem_cent_iff.2 rfl⟩
  have hc0 : IsoOn (fun x => s⁻¹ * x * s) (C[a] ⊓ C[w]) (C[a] ⊓ C[w]) :=
    (isoOn_conj s⁻¹ (conj_mem_inf_iff hs1 hs2)).congr fun x _ => by rw [inv_inv]
  have e1 : g⁻¹ * t * g⁻¹⁻¹ = W := by rw [inv_inv, ← hg2]; group
  have e2 : g⁻¹ * W * g⁻¹⁻¹ = t := by rw [inv_inv, ← hg1]; group
  have hcX : IsoOn (fun y => g * y * g⁻¹) (C[t] ⊓ C[W]) (C[t] ⊓ C[W]) :=
    isoOn_conj g fun y => by simpa only [inv_inv] using conj_mem_inf_iff e1 e2 y
  have hf := ((hc0.comp hAK).comp hcX).comp hAK.isoOn_inv
  have hfa : hAK.inv (g * A (s⁻¹ * a * s) * g⁻¹) = a := by
    have := hAK.inv_apply haw
    rw [hAa] at this
    rw [show s⁻¹ * a * s = w by rw [← hs2]; group, hAw, hg2, this]
  have hfw : hAK.inv (g * A (s⁻¹ * w * s) * g⁻¹) = w := by
    have := hAK.inv_apply hww
    rw [hAw] at this
    rw [show s⁻¹ * w * s = a by rw [← hs1]; group, hAa, hg1, this]
  obtain ⟨h, hh, hconj⟩ := hrig hf.toMulEquiv
    (fun k hk => Subtype.ext (by rw [IsoOn.toMulEquiv_apply, hk]; exact hfa))
    (fun k hk => Subtype.ext (by rw [IsoOn.toMulEquiv_apply, hk]; exact hfw))
    (fun k => by
      rw [← mem_coreOf_coe]
      push_cast
      rw [IsoOn.toMulEquiv_apply]
      set k' := s⁻¹ * (k : G) * s with hk'
      have hk'K : k' ∈ C[a] ⊓ C[w] := hc0.map_mem _ k.2
      have hy := hAK.map_mem _ hk'K
      have ho := hgO _ hy
      have e : g * A k' * g⁻¹ = (g * A k' * g⁻¹ * (A k')⁻¹) * A k' := by group
      show hAK.inv (g * A k' * g⁻¹) * (k : G)⁻¹ ∈ _
      rw [e, hAK.isoOn_inv.map_mul _ (coreOf_le _ ho) _ hy, hAK.inv_apply hk'K, mul_assoc]
      exact mul_mem (hAK.isoOn_inv.map_mem_coreOf ho) (hsO _ k.2))
  have hhw : h⁻¹ * w * h = w := by
    have := mem_cent_iff.1 (mem_inf.1 hh).2
    calc h⁻¹ * w * h = h⁻¹ * (w * h) := by group
      _ = h⁻¹ * (h * w) := by rw [this]
      _ = w := by group
  have hhs : (h * s)⁻¹ * w * (h * s)⁻¹⁻¹ = a := by
    calc (h * s)⁻¹ * w * (h * s)⁻¹⁻¹ = s⁻¹ * (h⁻¹ * w * h) * s := by group
      _ = s⁻¹ * (s * a * s⁻¹) * s := by rw [hhw, hs1]
      _ = a := by group
  have hc1 : IsoOn (fun y => (h * s)⁻¹ * y * (h * s)⁻¹⁻¹) C[w] C[a] :=
    isoOn_conj (h * s)⁻¹ fun y => by rw [mem_cent_conj_iff (h * s)⁻¹ y w, hhs]
  have hc2 : IsoOn (fun y => g * y * g⁻¹) C[t] C[W] :=
    isoOn_conj g fun y => by rw [mem_cent_conj_iff g y t, hg1]
  refine ⟨fun y => g * A ((h * s)⁻¹ * y * (h * s)) * g⁻¹,
    ((hc1.comp hA).comp hc2).congr fun y _ => by simp only [inv_inv], fun x hx => ?_, ?_⟩
  · have hk : h⁻¹ * x * h ∈ C[a] ⊓ C[w] :=
      mul_mem (mul_mem (inv_mem hh) hx) hh
    have e : hAK.inv (g * A (s⁻¹ * (h⁻¹ * x * h) * s) * g⁻¹) = h * (h⁻¹ * x * h) * h⁻¹ :=
      hconj ⟨_, hk⟩
    have e3 : s⁻¹ * (h⁻¹ * x * h) * s = (h * s)⁻¹ * x * (h * s) := by group
    have hmem : g * A ((h * s)⁻¹ * x * (h * s)) * g⁻¹ ∈ C[t] ⊓ C[W] := by
      rw [← e3]
      exact hcX.map_mem _ (hAK.map_mem _ (hc0.map_mem _ hk))
    rw [e3, show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at e
    show g * A ((h * s)⁻¹ * x * (h * s)) * g⁻¹ = A x
    rw [← hAK.apply_inv hmem, e]
  · show g * A ((h * s)⁻¹ * w * (h * s)) * g⁻¹ = W
    rw [show (h * s)⁻¹ * w * (h * s) = a by simpa only [inv_inv] using hhs, hAa, hg1]

end CFSG.Sporadic.Co1Patterson
