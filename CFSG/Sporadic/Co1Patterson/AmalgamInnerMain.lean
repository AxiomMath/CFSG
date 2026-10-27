module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Conj

variable {G : Type*} [Group G]

theorem map_conj_inf (c x y : G) :
    (C[x] ⊓ C[y]).map (MulAut.conj c).toMonoidHom = C[c * x * c⁻¹] ⊓ C[c * y * c⁻¹] := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := mem_inf.1 hk
    exact mem_inf.2 ⟨(mem_cent_conj_iff c k x).1 h1, (mem_cent_conj_iff c k y).1 h2⟩
  · intro hg
    obtain ⟨h1, h2⟩ := mem_inf.1 hg
    have e : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    refine ⟨c⁻¹ * g * c, mem_inf.2 ⟨(mem_cent_conj_iff c _ x).2 (by rw [e]; exact h1),
      (mem_cent_conj_iff c _ y).2 (by rw [e]; exact h2)⟩, ?_⟩
    show c * (c⁻¹ * g * c) * c⁻¹ = g
    exact e

theorem AutInnerModAt.conj {x y : G} (h : AutInnerModAt x y) (c : G) :
    AutInnerModAt (c * x * c⁻¹) (c * y * c⁻¹) := by
  intro ψ' hx' hy' hcore'
  let κ : ↥(C[x] ⊓ C[y]) ≃* ↥(C[c * x * c⁻¹] ⊓ C[c * y * c⁻¹]) :=
    ((MulAut.conj c).subgroupMap (C[x] ⊓ C[y])).trans
      (MulEquiv.subgroupCongr (map_conj_inf c x y))
  have hκ : ∀ g, (κ g : G) = c * g * c⁻¹ := fun _ => rfl
  let ψ := κ.trans (ψ'.trans κ.symm)
  have hψ : ∀ g, ψ g = κ.symm (ψ' (κ g)) := fun _ => rfl
  have hfix : ∀ (t : G) (ht : ∀ g' : ↥(C[c * x * c⁻¹] ⊓ C[c * y * c⁻¹]),
      (g' : G) = c * t * c⁻¹ → ψ' g' = g'),
      ∀ g : ↥(C[x] ⊓ C[y]), (g : G) = t → ψ g = g := by
    intro t ht g hg
    rw [hψ, ht (κ g) (by rw [hκ, hg]), MulEquiv.symm_apply_apply]
  obtain ⟨h₀, hh₀, hconj⟩ := h ψ (hfix x hx') (hfix y hy') (fun g => by
    have hmap := CFSG.pCore_map_iso 2 κ.symm
    have e : ψ g * g⁻¹ = κ.symm (ψ' (κ g) * (κ g)⁻¹) := by
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply, hψ]
    rw [e, ← hmap]
    exact ⟨_, hcore' (κ g), rfl⟩)
  refine ⟨c * h₀ * c⁻¹, ?_, fun g' => ?_⟩
  · rw [← map_conj_inf c x y]
    exact ⟨h₀, hh₀, rfl⟩
  · have h1 := hconj (κ.symm g')
    have h2 : (ψ' g' : G) = c * (ψ (κ.symm g') : G) * c⁻¹ := by
      rw [hψ, MulEquiv.apply_symm_apply, ← hκ, MulEquiv.apply_symm_apply]
    have h3 : c * ((κ.symm g' : ↥(C[x] ⊓ C[y])) : G) * c⁻¹ = g' := by
      rw [← hκ, MulEquiv.apply_symm_apply]
    rw [h2, h1, ← h3]
    group

end Conj

namespace InnerNative

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.GMS
open CFSG.Blueprint (NativeSporadic.Co1)

local macro "CA" : term => `(centralizer ({aNC} : Set NativeSporadic.Co1))


theorem coreData_native : CoreData K₀ R₀ vSub where
  le_K := R₀_le_K₀
  le_R := vSub_le_R₀
  central := vSub_central
  mul_self := vSub_mul_self
  conj_mem := fun _ hk _ hr => conj_mem_R₀ hk hr
  comm_mem := by
    have hV : ∀ r ∈ K₀, vSub ≤ vCent vSub_central r := fun r hr v hv => by
      refine ⟨R₀_le_K₀ (vSub_le_R₀ hv), ?_⟩
      rw [← vSub_central v hv r hr, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    have hsymm : ∀ r s : CA, r * s * r⁻¹ * s⁻¹ ∈ vSub → s * r * s⁻¹ * r⁻¹ ∈ vSub := by
      intro r s h
      have e : s * r * s⁻¹ * r⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h
    have ht : ∀ i < 12, R₀ ≤ vCent vSub_central (tE i) := fun i hi =>
      R₀_le_of_tE_mem _ (hV _ (R₀_le_K₀ (tE_mem_R₀ i))) fun j hj => by
        obtain ⟨v, hv, e⟩ := comm_tE_tE hi hj
        refine ⟨R₀_le_K₀ (tE_mem_R₀ j), ?_⟩
        have e2 : tE i * tE j * (tE i)⁻¹ * (tE j)⁻¹ = v := by
          rw [e]
          group
        rw [e2]
        exact hv
    intro r hr s hs
    refine (R₀_le_of_tE_mem (vCent vSub_central r) (hV r (R₀_le_K₀ hr)) (fun j hj =>
      ⟨R₀_le_K₀ (tE_mem_R₀ j), hsymm _ _ (ht j hj hr).2⟩) hs).2
  mem_of_comm := fun r hr h => mem_vSub_of_comm hr fun j _ => h _ (tE_mem_R₀ j)

theorem rx_mul_self : rx * rx = typeSystemC.z := by
  have h := rep_rx.mul rep_rx
  rw [innerElemOK_parts.2.2.1, ← map_mul] at h
  exact centEmb_injective (h.eq rep_z')

theorem ry_mul_self : ry * ry = yH 0 := by
  have h := rep_ry.mul rep_ry
  rw [innerElemOK_parts.2.2.2.1, ← map_mul] at h
  exact centEmb_injective (h.eq rep_w')

theorem kH_one_pow : kH 1 ^ 15 = 1 := by
  have h := (rep_kH (j := 1) (by norm_num)).pow 15
  rw [innerElemOK_parts.2.1, ← map_pow] at h
  exact centEmb_injective (h.eq rep_one')

theorem stabWords_lt (i : ℕ) : ∀ j ∈ stabWords.getD i [], j < 2 := by
  by_cases hi : i < 2
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [stabWords]; omega)]
    simp

@[expose] noncomputable def stabSet : Set CA :=
  {kW (stabWords.getD 0 []), kW (stabWords.getD 1 [])}

theorem stabSet_le : stabSet ⊆ K₀ := by
  rintro g (rfl | rfl)
  · exact kW_mem_K₀ (stabWords_lt 0)
  · exact kW_mem_K₀ (stabWords_lt 1)

theorem comm_mem_of_eq {g r v : CA} (e : g * r = v * (r * g)) : g * r * g⁻¹ * r⁻¹ = v := by
  rw [e]
  group

theorem eq_of_comm_mem {g r : CA} : g * r = (g * r * g⁻¹ * r⁻¹) * (r * g) := by group

theorem stab_fix {r₀ : CA} (hr₀ : r₀ = rx ∨ r₀ = ry) :
    ∀ g ∈ stabSet, g * r₀ * g⁻¹ * r₀⁻¹ ∈ vSub := by
  have h := innerElemOK_parts.2.2.2.2
  have key : ∀ i < 2, ∀ g, g = kW (stabWords.getD i []) →
      g * r₀ * g⁻¹ * r₀⁻¹ ∈ vSub := by
    intro i hi g hg
    have hw : stabWords.getD i [] ∈ stabWords := by interval_cases i <;> decide
    obtain ⟨h1, h2⟩ := h _ hw
    rcases hr₀ with rfl | rfl
    · obtain ⟨v, hv, e⟩ := stab_of_stabR (rep_kW (stabWords_lt i)) rep_rx h1
      rw [hg, comm_mem_of_eq e]
      exact hv
    · obtain ⟨v, hv, e⟩ := stab_of_stabR (rep_kW (stabWords_lt i)) rep_ry h2
      rw [hg, comm_mem_of_eq e]
      exact hv
  rintro g (rfl | rfl)
  · exact key 0 (by norm_num) _ rfl
  · exact key 1 (by norm_num) _ rfl

theorem exists_conj_native {f : CA → CA} (hf : IsoOn f K₀ K₀) (hfV : ∀ v ∈ vSub, f v = v)
    (hfR : ∀ g ∈ K₀, f g * g⁻¹ ∈ R₀) : ∃ s ∈ R₀, ∀ g ∈ K₀, f g = s * g * s⁻¹ := by
  have hS : ∀ r₀ ∈ ({rx, ry} : Set CA), r₀ = rx ∨ r₀ = ry := fun r₀ h => h
  refine coreData_native.exists_conj hf hfV hfR (S := {rx, ry})
    (fun r₀ h => (hS r₀ h).elim (fun e => e ▸ rx_mem_R₀) (fun e => e ▸ ry_mem_R₀))
    (fun r₀ h => (hS r₀ h).elim
      (fun e => by rw [e, rx_mul_self]; exact mem_vSub.2 (Or.inr (Or.inl rfl)))
      (fun e => by rw [e, ry_mul_self]; exact mem_vSub.2 (Or.inr (Or.inr (Or.inl rfl)))))
    (fun r₀ h => ⟨stabSet, stabSet_le, stab_fix (hS r₀ h), fun r hr hfix hsq => ?_⟩)
    (fun F hV hSF hinv => R₀_le_of_tE_mem F hV fun j _ => ?_)
    (kH_mem_K₀ (by norm_num)) (by decide : Odd 15) kH_one_pow
    (fun t ht h => mem_vSub_of_fix ht ⟨_, h, by group⟩)
    (mul_mem (kH_mem_K₀ (by norm_num)) (kH_mem_K₀ (by norm_num))) (by decide : Odd 3)
    pow_three_mem_R₀ K₀_le_of_gens
  · have h₁ : ∃ v ∈ vSub, kW (stabWords.getD 0 []) * r = v * (r * kW (stabWords.getD 0 [])) :=
      ⟨_, hfix _ (Or.inl rfl), eq_of_comm_mem⟩
    have h₂ : ∃ v ∈ vSub, kW (stabWords.getD 1 []) * r = v * (r * kW (stabWords.getD 1 [])) :=
      ⟨_, hfix _ (Or.inr rfl), eq_of_comm_mem⟩
    obtain ⟨hx, hy⟩ := stab_uniq hr h₁ h₂
    rcases hS r₀ h with rfl | rfl
    · rw [rx_mul_self] at hsq
      obtain ⟨v, hv, e⟩ := hx hsq
      rw [e, mul_inv_cancel_right]
      exact hv
    · rw [ry_mul_self] at hsq
      obtain ⟨v, hv, e⟩ := hy hsq
      rw [e, mul_inv_cancel_right]
      exact hv
  · rw [tE]
    refine hinv _ (kW_mem_K₀ (conjWords_lt _)) _ ?_ ?_
    · split_ifs
      · exact hSF (Or.inl rfl)
      · exact hSF (Or.inr rfl)
    · split_ifs
      · exact rx_mem_R₀
      · exact ry_mem_R₀

theorem mem_K₀_iff_coe {x : CA} :
    x ∈ K₀ ↔ (x : NativeSporadic.Co1) ∈ C[((yH 0 : CA) : NativeSporadic.Co1)] := by
  rw [mem_K₀, mem_centralizer_singleton_iff, ← Subtype.coe_inj, Subgroup.coe_mul,
    Subgroup.coe_mul]

theorem isoOn_val : IsoOn (fun x : CA => (x : NativeSporadic.Co1)) K₀
    (C[aNC] ⊓ C[((yH 0 : CA) : NativeSporadic.Co1)]) where
  map_mem x hx := mem_inf.2 ⟨x.2, mem_K₀_iff_coe.1 hx⟩
  map_mul x _ y _ := Subgroup.coe_mul _ x y
  injOn _ _ _ _ h := Subtype.ext h
  surjOn y hy := ⟨⟨y, (mem_inf.1 hy).1⟩, mem_K₀_iff_coe.2 (mem_inf.1 hy).2, rfl⟩

theorem coreOf_K₀_le : coreOf K₀ ≤ R₀ :=
  le_R₀ (coreOf_le K₀)
    (fun k hk _ hp => conj_mem_coreOf (fun y => ⟨fun hy => mul_mem (mul_mem hk hy) (inv_mem hk),
      fun hy => by
        have e : y = k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hk) hy) (inv_mem (inv_mem hk))⟩) hp)
    ((CFSG.pCore_isPGroup (p := 2)).map K₀.subtype)

theorem autInnerModAt_w₀ : AutInnerModAt aNC ((yH 0 : CA) : NativeSporadic.Co1) := by
  intro ψ hψa hψw hψc
  have hj := isoOn_val
  have hE := isoOn_extFun ψ
  have hf : IsoOn (fun x : CA => hj.inv (extFun ψ (x : NativeSporadic.Co1))) K₀ K₀ :=
    (hj.comp hE).comp hj.isoOn_inv
  have hfix : ∀ x : CA, x ∈ K₀ →
      (∀ g : ↥(C[aNC] ⊓ C[((yH 0 : CA) : NativeSporadic.Co1)]),
        (g : NativeSporadic.Co1) = x → ψ g = g) →
      hj.inv (extFun ψ (x : NativeSporadic.Co1)) = x := by
    intro x hx hψx
    have hxK := hj.map_mem x hx
    rw [extFun_of_mem ψ hxK, hψx ⟨_, hxK⟩ rfl]
    exact hj.inv_apply hx
  have hfV : ∀ v ∈ vSub, hj.inv (extFun ψ (v : NativeSporadic.Co1)) = v := by
    intro v hv
    have hz := hfix _ z_mem_K₀ hψa
    have hw := hfix _ yH_zero_mem_K₀ hψw
    rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
    · exact hf.map_one
    · exact hz
    · exact hw
    · rw [hf.map_mul _ yH_zero_mem_K₀ _ z_mem_K₀, hz, hw]
  have hfR : ∀ g ∈ K₀, hj.inv (extFun ψ (g : NativeSporadic.Co1)) * g⁻¹ ∈ R₀ := by
    intro g hg
    have hgK := hj.map_mem g hg
    have hc : extFun ψ (g : NativeSporadic.Co1) * (g : NativeSporadic.Co1)⁻¹ ∈
        coreOf (C[aNC] ⊓ C[((yH 0 : CA) : NativeSporadic.Co1)]) := by
      have h1 := (mem_coreOf_coe _).2 (hψc ⟨_, hgK⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [extFun_of_mem ψ hgK]
      exact h1
    have hcK := coreOf_le _ hc
    have h2 := hj.isoOn_inv.map_mem_coreOf hc
    have e : hj.inv (extFun ψ (g : NativeSporadic.Co1) * (g : NativeSporadic.Co1)⁻¹) =
        hj.inv (extFun ψ (g : NativeSporadic.Co1)) * g⁻¹ := by
      rw [hj.isoOn_inv.map_mul _ (hE.map_mem _ hgK) _ (inv_mem hgK),
        hj.isoOn_inv.map_inv hgK, hj.inv_apply hg]
    rw [e] at h2
    exact coreOf_K₀_le h2
  obtain ⟨s, hs, hfs⟩ := exists_conj_native hf hfV hfR
  refine ⟨(s : NativeSporadic.Co1), hj.map_mem s (R₀_le_K₀ hs), fun g' => ?_⟩
  have hg'K := g'.2
  have hgK₀ := hj.inv_mem hg'K
  have h1 := congrArg Subtype.val (hfs _ hgK₀)
  have e1 : ((hj.inv (extFun ψ ((hj.inv (g' : NativeSporadic.Co1) : CA) :
      NativeSporadic.Co1)) : CA) : NativeSporadic.Co1) = (ψ g' : NativeSporadic.Co1) := by
    rw [hj.apply_inv hg'K, hj.apply_inv (hE.map_mem _ hg'K), extFun_of_mem ψ hg'K]
  have e2 : ((s * hj.inv (g' : NativeSporadic.Co1) * s⁻¹ : CA) : NativeSporadic.Co1) =
      (s : NativeSporadic.Co1) * (g' : NativeSporadic.Co1) * (s : NativeSporadic.Co1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hj.apply_inv hg'K]
  rw [← e1, ← e2]
  exact h1

theorem autInnerModAt_of_mem {w : Vt} (hw : w ∈ cOrb (repV 0)) :
    AutInnerModAt aNC (w : NativeSporadic.Co1) := by
  obtain ⟨k, hk, rfl⟩ := hw
  have h := autInnerModAt_w₀.conj k
  have e1 : k * aNC * k⁻¹ = aNC := by
    rw [mem_centralizer_singleton_iff.1 hk, mul_inv_cancel_right]
  have e2 : k * ((yH 0 : CA) : NativeSporadic.Co1) * k⁻¹ =
      ((k • repV 0 : Vt) : NativeSporadic.Co1) := by
    rw [coe_smul_conjVert, coe_repV_zero]
  rw [e1, e2] at h
  exact h

theorem autInnerModAt_native : AutInnerModAt aNC ((wT 2 : Vt) : NativeSporadic.Co1) :=
  autInnerModAt_of_mem (mem_cOrb_of_contains exact_orbQ nrep_zRows (nrep_wT 2)
    innerOrbOK_parts.2)

end InnerNative

end CFSG.Sporadic.Co1Patterson
