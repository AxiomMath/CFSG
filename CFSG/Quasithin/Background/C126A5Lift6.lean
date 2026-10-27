module

public import CFSG.Quasithin.Background.C126A5Lift5

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_not_comm_alt_five : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
  let a : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  refine ⟨a, b, fun hab => ?_⟩
  have : (swap 0 1 * swap 0 2 : Perm (Fin 5)) * (swap 0 1 * swap 0 3) =
      (swap 0 1 * swap 0 3) * (swap 0 1 * swap 0 2) := congrArg Subtype.val hab
  revert this
  decide

theorem center_alt_five : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 5)))
    with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_comm_alt_five
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b |>.symm)

theorem center_eq_bot_of_alt_five {Γ : Type*} [Group Γ] (e : Γ ≃* ↥(alternatingGroup (Fin 5))) :
    Subgroup.center Γ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
  rw [center_alt_five, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem isQuasisimple_of_alt_five {Γ : Type*} [Group Γ] (e : Γ ≃* ↥(alternatingGroup (Fin 5))) :
    CFSG.IsQuasisimple Γ := by
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup Γ := e.isSimpleGroup
  have hcenter : Subgroup.center Γ = ⊥ := center_eq_bot_of_alt_five e
  let coord : (Γ ⧸ Subgroup.center Γ) ≃* Γ :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, coord.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Γ) with h | h
    · exfalso
      have h1 : Subgroup.center Γ = ⊤ := (commutator_eq_bot_iff_center_eq_top Γ).1 h
      rw [hcenter] at h1
      have : Nontrivial Γ := e.toEquiv.nontrivial
      exact bot_ne_top h1
    · exact h
  · obtain ⟨a, b, hab⟩ := exists_not_comm_alt_five
    refine ⟨coord.symm (e.symm a), coord.symm (e.symm b), fun h => hab ?_⟩
    have := congrArg (fun z => e (coord z)) h
    simpa using this

omit [Finite G] in
theorem coe_mem_pCoreOf_iff' (H : Subgroup G) (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem cv_mem_L {k : G} (hk : k ∈ Khat s d x) : cv hV k ∈ d.L :=
  (mem_A₁.1 (hx.Khat_le_A₁ hk)).2

@[expose] noncomputable def phi : ↥(Khat s d x) →* Perm (Fin 5) where
  toFun k := d.th (cv hV (k : G))
  map_one' := by
    show d.th (cv hV (1 : G)) = 1
    rw [cv_one, d.th_one]
  map_mul' k k' := by
    show d.th (cv hV ((k : G) * (k' : G))) = d.th (cv hV (k : G)) * d.th (cv hV (k' : G))
    have hkN := s.H_le_N (hx.Khat_le_H k.2)
    have hk'N := s.H_le_N (hx.Khat_le_H k'.2)
    rw [cv_mul hV hkN hk'N, d.th_mul (hx.cv_mem_L k.2) (hx.cv_mem_L k'.2)]

theorem phi_mem_alt (k : ↥(Khat s d x)) : hx.phi k ∈ alternatingGroup (Fin 5) := by
  let Alt1 : Subgroup G :=
    { carrier := {g | g ∈ A₁ s d ∧ d.th (cv hV g) ∈ alternatingGroup (Fin 5)}
      one_mem' := ⟨(A₁ s d).one_mem, by
        rw [cv_one, d.th_one]
        exact Subgroup.one_mem _⟩
      mul_mem' := fun {a b} ha hb => ⟨(A₁ s d).mul_mem ha.1 hb.1, by
        have haH := (mem_A₁.1 ha.1).1
        have hbH := (mem_A₁.1 hb.1).1
        rw [cv_mul hV (s.H_le_N haH) (s.H_le_N hbH),
          d.th_mul (mem_A₁.1 ha.1).2 (mem_A₁.1 hb.1).2]
        exact Subgroup.mul_mem _ ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨(A₁ s d).inv_mem ha.1, by
        have haH := (mem_A₁.1 ha.1).1
        rw [cv_inv hV (s.H_le_N haH), d.th_inv (mem_A₁.1 ha.1).2]
        exact Subgroup.inv_mem _ ha.2⟩ }
  have hxA : x ∈ Alt1 := ⟨hx.x_mem_A₁, by
    rw [hx.th_eq]; exact cyc3_mem_alternatingGroup d.π⟩
  have hz : Subgroup.zpowers x ≤ Alt1 := by rw [Subgroup.zpowers_le]; exact hxA
  have hK : Khat s d x ≤ Alt1 := by
    show conjClosure (Subgroup.zpowers x) (A₁ s d) ≤ Alt1
    refine conjClosure_le fun a ha z hz' => ?_
    have haH := (mem_A₁.1 ha).1
    have hzA := hx.zpowers_le_A₁ hz'
    refine ⟨(A₁ s d).mul_mem ((A₁ s d).mul_mem ha hzA) ((A₁ s d).inv_mem ha), ?_⟩
    have hzH := (mem_A₁.1 hzA).1
    rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N haH) (s.H_le_N hzH)) (s.H_le_N (H.inv_mem haH)),
      cv_mul hV (s.H_le_N haH) (s.H_le_N hzH), cv_inv hV (s.H_le_N haH),
      d.th_mul (d.L.mul_mem (mem_A₁.1 ha).2 (mem_A₁.1 hzA).2) (d.L.inv_mem (mem_A₁.1 ha).2),
      d.th_mul (mem_A₁.1 ha).2 (mem_A₁.1 hzA).2, d.th_inv (mem_A₁.1 ha).2]
    have hzalt : d.th (cv hV z) ∈ alternatingGroup (Fin 5) := (hz hz').2
    exact Subgroup.Normal.conj_mem (inferInstance : (alternatingGroup (Fin 5)).Normal) _ hzalt _
  exact (hK k.2).2

@[expose] noncomputable def alpha : ↥(Khat s d x) →* ↥(alternatingGroup (Fin 5)) :=
  hx.phi.codRestrict (alternatingGroup (Fin 5)) hx.phi_mem_alt

theorem alpha_apply (k : ↥(Khat s d x)) : ((hx.alpha k : ↥(alternatingGroup (Fin 5))) :
    Perm (Fin 5)) = d.th (cv hV (k : G)) := rfl

theorem alpha_surj : Function.Surjective hx.alpha := by
  intro g
  have hg : (g : Perm (Fin 5)) ∈ alts := mem_alts.2 (Equiv.Perm.mem_alternatingGroup.1 g.2)
  obtain ⟨h, hhF, hθ⟩ := hx.coversAlt (g : Perm (Fin 5)) hg
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  obtain ⟨k, hk, hkh⟩ := (mem_autI_iff hV hKN).1 hhF
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  rw [alpha_apply, hkh, d.th_of_mem h.2]
  exact hθ

theorem alpha_eq_one_iff (k : ↥(Khat s d x)) : hx.alpha k = 1 ↔ cv hV (k : G) = 1 := by
  rw [Subtype.ext_iff, alpha_apply]
  show d.th (cv hV (k : G)) = (1 : Perm (Fin 5)) ↔ _
  constructor
  · intro h
    exact d.th_inj (hx.cv_mem_L k.2) d.L.one_mem (by rw [h, d.th_one])
  · intro h
    rw [h, d.th_one]

theorem alpha_ker_C :
    hx.alpha.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (Khat s d x) := by
  ext k
  rw [MonoidHom.mem_ker, alpha_eq_one_iff, Subgroup.mem_subgroupOf]
  exact cv_eq_one_iff hV (s.H_le_N (hx.Khat_le_H k.2))

theorem alpha_ker (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    hx.alpha.ker = CFSG.pCore 2 ↥(Khat s d x) := by
  ext k
  rw [← coe_mem_pCoreOf_iff', hx.pCoreOf_Khat, hx.alpha_ker_C, Subgroup.mem_subgroupOf]
  constructor
  · intro hc
    exact ⟨k.2, hx.Khat_inf_C hRad ⟨k.2, hc⟩⟩
  · intro hq
    exact s.Q_le_C hq.2

end XData

end Lift

end CFSG.Quasithin.C126.A5
