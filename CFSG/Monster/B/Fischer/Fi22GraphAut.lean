
module

public import CFSG.Monster.B.Fischer.Fi22GraphAutBase1

public import CFSG.Monster.B.Fischer.Fi22Centralizer
public import CFSG.Monster.B.Fischer.Fi22GraphAutBase

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates

@[expose] def fi22ZClass :
    Set fi22P := Set.range fun g : fi22P => g * fi22OuterZP * g⁻¹

theorem fi22_fix_zero_iff
    (k : fi22P) :
    (k : Equiv.Perm (Fin 3510)) 0 = 0 ↔ k * fi22OuterZP = fi22OuterZP * k := by
  rw [← Subgroup.mem_centralizer_singleton_iff, ← fi22OuterM_subgroupOf_eq,
    Subgroup.mem_subgroupOf, fi22OuterM_eq, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    Equiv.Perm.smul_def]
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

theorem fi22_conj_eq_iff
    (g h : fi22P) :
    g * fi22OuterZP * g⁻¹ = h * fi22OuterZP * h⁻¹ ↔
      (g : Equiv.Perm (Fin 3510)) 0 = (h : Equiv.Perm (Fin 3510)) 0 := by
  have key : g * fi22OuterZP * g⁻¹ = h * fi22OuterZP * h⁻¹ ↔
      (h⁻¹ * g) * fi22OuterZP = fi22OuterZP * (h⁻¹ * g) := by
    constructor
    · intro e
      calc (h⁻¹ * g) * fi22OuterZP = h⁻¹ * (g * fi22OuterZP * g⁻¹) * g := by group
        _ = h⁻¹ * (h * fi22OuterZP * h⁻¹) * g := by rw [e]
        _ = fi22OuterZP * (h⁻¹ * g) := by group
    · intro e
      calc g * fi22OuterZP * g⁻¹ = h * ((h⁻¹ * g) * fi22OuterZP) * g⁻¹ := by group
        _ = h * (fi22OuterZP * (h⁻¹ * g)) * g⁻¹ := by rw [e]
        _ = h * fi22OuterZP * h⁻¹ := by group
  rw [key, ← fi22_fix_zero_iff, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq]

@[expose] def fi22ThetaFun
    (i : Fin 3510) : fi22ZClass :=
  ⟨fi22Sec i * fi22OuterZP * (fi22Sec i)⁻¹, ⟨_, rfl⟩⟩

theorem fi22ThetaFun_eq
    {g : fi22P} {i : Fin 3510} (h : (g : Equiv.Perm (Fin 3510)) 0 = i) :
    (fi22ThetaFun i : fi22P) = g * fi22OuterZP * g⁻¹ :=
  (fi22_conj_eq_iff _ _).2 (by rw [fi22Sec_apply, h])

theorem fi22ThetaFun_bijective :
    Function.Bijective fi22ThetaFun := by
  refine ⟨fun i j hij => ?_, ?_⟩
  · have h := (fi22_conj_eq_iff _ _).1 (congrArg Subtype.val hij)
    rwa [fi22Sec_apply, fi22Sec_apply] at h
  · rintro ⟨_, ⟨g, rfl⟩⟩
    exact ⟨(g : Equiv.Perm (Fin 3510)) 0, Subtype.ext (fi22ThetaFun_eq rfl)⟩

@[expose] def fi22Theta :

    Fin 3510 ≃ fi22ZClass := Equiv.ofBijective _ fi22ThetaFun_bijective

theorem fi22Theta_apply
    (i : Fin 3510) : fi22Theta i = fi22ThetaFun i := rfl

theorem fi22Theta_eq
    {g : fi22P} {i : Fin 3510} (h : (g : Equiv.Perm (Fin 3510)) 0 = i) :
    (fi22Theta i : fi22P) = g * fi22OuterZP * g⁻¹ :=
  fi22ThetaFun_eq h

theorem fi22Theta_zero :
    (fi22Theta 0 : fi22P) = fi22OuterZP := by
  rw [fi22Theta_eq (g := 1) (i := 0) rfl]
  group

theorem fi22Theta_equivariant
    (g : fi22P) (i : Fin 3510) :
    (fi22Theta ((g : Equiv.Perm (Fin 3510)) i) : fi22P) = g * fi22Theta i * g⁻¹ := by
  rw [fi22Theta_eq (g := g * fi22Sec i) (by rw [Subgroup.coe_mul, Equiv.Perm.mul_apply,
    fi22Sec_apply]), fi22Theta_eq (fi22Sec_apply i)]
  group

theorem fi22Theta_unique
    (θ' : Fin 3510 ≃ fi22ZClass) (h0 : (θ' 0 : fi22P) = fi22OuterZP)
    (hθ' : ∀ (g : fi22P) (i : Fin 3510),
      (θ' ((g : Equiv.Perm (Fin 3510)) i) : fi22P) = g * θ' i * g⁻¹) : θ' = fi22Theta := by
  ext i
  have h := hθ' (fi22Sec i) 0
  rw [fi22Sec_apply, h0] at h
  rw [h, fi22Theta_eq (fi22Sec_apply i)]

theorem fi22OuterZP_coe :
    ((fi22OuterZP : fi22P) : Equiv.Perm (Fin 3510)) = fi22OuterZ := by
  rw [fi22OuterZP_eq]

theorem fi22_commute_zero_iff
    (k : Fin 3510) :
    Commute fi22OuterZP (fi22Theta k : fi22P) ↔ fi22OuterZ k = k := by
  have h := fi22Theta_equivariant fi22OuterZP k
  rw [fi22OuterZP_coe] at h
  constructor
  · intro hc
    have e : fi22OuterZP * (fi22Theta k : fi22P) * fi22OuterZP⁻¹ = fi22Theta k := by
      rw [hc.eq, mul_inv_cancel_right]
    rw [e] at h
    exact fi22Theta.injective (Subtype.ext h)
  · intro hk
    rw [hk] at h
    have e : fi22OuterZP * (fi22Theta k : fi22P) = (fi22Theta k : fi22P) * fi22OuterZP := by
      rw [eq_mul_inv_iff_mul_eq.1 h]
    exact e

theorem fi22Graph_adj_iff_commute
    {i j : Fin 3510} (hij : i ≠ j) :
    fi22Graph.Adj i j ↔ Commute (fi22Theta i : fi22P) (fi22Theta j) := by
  set s := fi22Sec i
  set k := (s⁻¹ : Equiv.Perm (Fin 3510)) j
  have hs : (s : Equiv.Perm (Fin 3510)) 0 = i := fi22Sec_apply i
  have hj : (s : Equiv.Perm (Fin 3510)) k = j := perm_apply_inv_self _ j
  have hk : k ≠ 0 := fun h => hij (by rw [← hs, ← hj, h])
  have hθi : (fi22Theta i : fi22P) = s * fi22OuterZP * s⁻¹ := fi22Theta_eq hs
  have hθj : (fi22Theta j : fi22P) = s * fi22Theta k * s⁻¹ := by
    rw [← hj, fi22Theta_equivariant]
  rw [← hs, ← hj, fi22Graph_adj_inv s.2, fi22Graph_adj_zero, hs, hj, hθi, hθj,
    Commute.conj_iff, fi22_commute_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩

theorem fi22ZClass_aut
    (α : MulAut fi22P) {y : fi22P} (hy : y ∈ fi22ZClass) :
    α y ∈ fi22ZClass := by
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨c, hc⟩ := isConj_iff.1 (fi22P_aut_class α).1
  refine ⟨α g * c, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hc]
  group

@[expose] def fi22ClassPerm
    (α : MulAut fi22P) : Equiv.Perm fi22ZClass where
  toFun y := ⟨α y, fi22ZClass_aut α y.2⟩
  invFun y := ⟨α⁻¹ y, fi22ZClass_aut α⁻¹ y.2⟩
  left_inv _ := Subtype.ext (MulAut.inv_apply_self _ _ _)
  right_inv _ := Subtype.ext (MulAut.apply_inv_self _ _ _)

@[expose] def fi22PhiPerm
    (α : MulAut fi22P) : Equiv.Perm (Fin 3510) :=
  (fi22Theta.trans (fi22ClassPerm α)).trans fi22Theta.symm

theorem fi22Theta_phiPerm
    (α : MulAut fi22P) (i : Fin 3510) :
    (fi22Theta (fi22PhiPerm α i) : fi22P) = α (fi22Theta i) := by
  rw [fi22PhiPerm, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem fi22PhiPerm_adj
    (α : MulAut fi22P) (i j : Fin 3510) :
    fi22Graph.Adj (fi22PhiPerm α i) (fi22PhiPerm α j) ↔ fi22Graph.Adj i j := by
  by_cases hij : i = j
  · subst hij
    simp only [SimpleGraph.irrefl]
  · have hij' : fi22PhiPerm α i ≠ fi22PhiPerm α j := fun h => hij ((fi22PhiPerm α).injective h)
    rw [fi22Graph_adj_iff_commute hij, fi22Graph_adj_iff_commute hij', fi22Theta_phiPerm,
      fi22Theta_phiPerm]
    constructor
    · intro h
      have := h.map (α⁻¹ : MulAut fi22P)
      simpa only [MulAut.inv_apply_self] using this
    · exact fun h => h.map α

@[expose] def fi22Phi :
    MulAut fi22P →* (fi22Graph ≃g fi22Graph) where
  toFun α := ⟨fi22PhiPerm α, fun {i j} => fi22PhiPerm_adj α i j⟩
  map_one' := by
    refine RelIso.ext fun i => fi22Theta.injective (Subtype.ext ?_)
    change (fi22Theta (fi22PhiPerm 1 i) : fi22P) = fi22Theta i
    rw [fi22Theta_phiPerm]
    rfl
  map_mul' α β := by
    refine RelIso.ext fun i => fi22Theta.injective (Subtype.ext ?_)
    change (fi22Theta (fi22PhiPerm (α * β) i) : fi22P) =
      fi22Theta (fi22PhiPerm α (fi22PhiPerm β i))
    rw [fi22Theta_phiPerm, fi22Theta_phiPerm, fi22Theta_phiPerm]
    rfl

theorem fi22Theta_phi
    (α : MulAut fi22P) (i : Fin 3510) :
    (fi22Theta (fi22Phi α i) : fi22P) = α (fi22Theta i) :=
  fi22Theta_phiPerm α i

theorem fi22Phi_conj
    (g : fi22P) (i : Fin 3510) :
    fi22Phi (MulAut.conj g) i = (g : Equiv.Perm (Fin 3510)) i := by
  apply fi22Theta.injective
  apply Subtype.ext
  rw [fi22Theta_phi, fi22Theta_equivariant, MulAut.conj_apply]

theorem fi22Phi_injective :
    Function.Injective fi22Phi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  rw [Subgroup.mem_bot]
  have hfix : ∀ y ∈ fi22ZClass, α y = y := by
    intro y hy
    obtain ⟨i, hi⟩ := fi22Theta.surjective ⟨y, hy⟩
    have h := fi22Theta_phi α i
    rw [hα, show (1 : fi22Graph ≃g fi22Graph) i = i from rfl, hi] at h
    exact h.symm
  have hnc : Subgroup.normalClosure ({fi22OuterZP} : Set fi22P) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id fi22P) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    exact hfix _ ⟨c, rfl⟩
  have htop : Subgroup.normalClosure ({fi22OuterZP} : Set fi22P) = ⊤ := by
    have := isSimpleGroup_fi22P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({fi22OuterZP} : Set fi22P)) with h | h
    · exfalso
      have hz : fi22OuterZP ∈ Subgroup.normalClosure ({fi22OuterZP} : Set fi22P) :=
        Subgroup.subset_normalClosure rfl
      rw [h, Subgroup.mem_bot] at hz
      have ho : orderOf fi22OuterZP = 2 := by
        rw [fi22OuterZP_eq, Subgroup.orderOf_mk, orderOf_fi22OuterZ]
      rw [hz, orderOf_one] at ho
      exact absurd ho (by norm_num)
    · exact h
  rw [htop] at hnc
  refine MulEquiv.ext fun y => ?_
  exact hnc (Subgroup.mem_top y)

theorem CTUC_Fi22_faithful_automorphism_action_on_commuting_graph :
    ∃ θ : Fin 3510 ≃ fi22ZClass,
      (θ 0 : fi22P) = fi22OuterZP ∧
      (∀ (g : fi22P) (i : Fin 3510),
        (θ ((g : Equiv.Perm (Fin 3510)) i) : fi22P) = g * θ i * g⁻¹) ∧
      (∀ θ' : Fin 3510 ≃ fi22ZClass, (θ' 0 : fi22P) = fi22OuterZP →
        (∀ (g : fi22P) (i : Fin 3510),
          (θ' ((g : Equiv.Perm (Fin 3510)) i) : fi22P) = g * θ' i * g⁻¹) → θ' = θ) ∧
      (∀ i j : Fin 3510, i ≠ j → (fi22Graph.Adj i j ↔ Commute (θ i : fi22P) (θ j))) ∧
      (∀ (α : MulAut fi22P), ∀ y ∈ fi22ZClass, α y ∈ fi22ZClass) ∧
      ∃ Φ : MulAut fi22P →* (fi22Graph ≃g fi22Graph),
        (∀ (α : MulAut fi22P) (i : Fin 3510), (θ (Φ α i) : fi22P) = α (θ i)) ∧
        Function.Injective Φ ∧
        (∀ (g : fi22P) (i : Fin 3510), Φ (MulAut.conj g) i = (g : Equiv.Perm (Fin 3510)) i) ∧
        Nat.card (MulAut fi22P) ≤ Nat.card (fi22Graph ≃g fi22Graph) :=
  ⟨fi22Theta, fi22Theta_zero, fi22Theta_equivariant, fi22Theta_unique,
    fun _ _ hij => fi22Graph_adj_iff_commute hij, fun α _ hy => fi22ZClass_aut α hy, fi22Phi,
    fi22Theta_phi, fi22Phi_injective, fi22Phi_conj,
    Nat.card_le_card_of_injective _ fi22Phi_injective⟩

end CFSG.Monster.B.Fischer
