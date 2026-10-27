module

public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Sporadic.SchreierLemmas

open CFSG.OrderReductions.FrattiniAutomorphisms

theorem isSolvable_stabilizer_of_card_eight {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ x y : V, x * y = y * x) (hcard : Nat.card V = 8) {c : V} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 = 1) : Group.IsSolvable (MulAction.stabilizer (MulAut V) c) := by
  classical
  set C := Subgroup.zpowers c
  have hCn : C.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hmap : ∀ T ∈ MulAction.stabilizer (MulAut V) c, C.map (T : V →* V) = C := fun T hT => by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hT
  let σ : MulAction.stabilizer (MulAut V) c →* Equiv.Perm (V ⧸ C) :=
    { toFun := fun T => (QuotientGroup.congr C C T.1 (hmap T.1 T.2)).toEquiv
      map_one' := Equiv.ext fun x => by
        induction x using QuotientGroup.induction_on with
        | H x => exact QuotientGroup.congr_mk _ _ _ _ x
      map_mul' := fun T₁ T₂ => Equiv.ext fun x => by
        induction x using QuotientGroup.induction_on with
        | H x =>
          change QuotientGroup.congr C C (T₁ * T₂).1 (hmap _ (T₁ * T₂).2) (x : V ⧸ C) =
            QuotientGroup.congr C C T₁.1 (hmap _ T₁.2)
              (QuotientGroup.congr C C T₂.1 (hmap _ T₂.2) (x : V ⧸ C))
          rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
          rfl }
  have hkerfix : ∀ T : σ.ker, ∀ x : V, x⁻¹ * (T : MulAut V) x ∈ C := by
    intro T x
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.1 T.2) (x : V ⧸ C)
    change QuotientGroup.congr C C (T : MulAction.stabilizer (MulAut V) c).1
      (hmap _ (T : MulAction.stabilizer (MulAut V) c).2) (x : V ⧸ C) = (x : V ⧸ C) at h
    rw [QuotientGroup.congr_mk] at h
    have := inv_mem (QuotientGroup.eq.1 h)
    rwa [mul_inv_rev, inv_inv] at this
  have hfixC : ∀ T : σ.ker, ∀ d ∈ C, (T : MulAut V) d = d := by
    intro T d hd
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [map_zpow]
    exact congrArg (· ^ n) (T : MulAction.stabilizer (MulAut V) c).2
  have hkercomm : ∀ T₁ T₂ : σ.ker, T₁ * T₂ = T₂ * T₁ := by
    intro T₁ T₂
    refine Subtype.ext (Subtype.ext (MulEquiv.ext fun x => ?_))
    obtain ⟨d₁, hd₁, e₁⟩ : ∃ d ∈ C, (T₁ : MulAut V) x = x * d := ⟨_, hkerfix T₁ x, by group⟩
    obtain ⟨d₂, hd₂, e₂⟩ : ∃ d ∈ C, (T₂ : MulAut V) x = x * d := ⟨_, hkerfix T₂ x, by group⟩
    change (T₁ : MulAut V) ((T₂ : MulAut V) x) = (T₂ : MulAut V) ((T₁ : MulAut V) x)
    rw [e₂, map_mul, e₁, hfixC T₁ d₂ hd₂, map_mul, e₂, hfixC T₂ d₁ hd₁, mul_assoc, mul_assoc,
      hcomm d₁ d₂]
  have : Group.IsSolvable σ.ker := Group.isSolvable_of_comm hkercomm
  have hcardC : Nat.card C = 2 := by
    have := Fact.mk Nat.prime_two
    rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1]
  have hcardQ : Nat.card (V ⧸ C) = 4 := by
    have h := Subgroup.card_mul_index C
    rw [hcardC, hcard] at h
    change 2 * Nat.card (V ⧸ C) = 8 at h
    omega
  have : Group.IsSolvable (Equiv.Perm (V ⧸ C)) := Equiv.Perm.isSolvable (by rw [hcardQ])
  exact Group.isSolvable_of_ker_le_range σ.ker.subtype σ fun T hT => ⟨⟨T, hT⟩, rfl⟩

theorem characteristic_Frattini_coset_automorphisms {S : Type*} [Group S] [Finite S]
    (hS : IsPGroup 2 S) (Q : Subgroup S) [Q.Characteristic] {k : ℕ}
    (helem : IsElementaryAbelian 2 (S ⧸ commutator S))
    (hcard : Nat.card (S ⧸ commutator S) = 8)
    (huniq : ∃! c : S ⧸ commutator S, c ≠ 1 ∧
      ∀ y : S, (y : S ⧸ commutator S) = c → orderOf (y : S ⧸ Q) = k) :
    Group.IsSolvable (MulAut S) := by
  classical
  obtain ⟨c, ⟨hc1, hck⟩, hcuniq⟩ := huniq
  have hcommV : ∀ x y : S ⧸ commutator S, x * y = y * x :=
    fun x y => helem.toIsMulCommutative.is_comm.comm x y
  have hc2 : c ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 helem.exponent_dvd_p c
  let ρ := quotientAutomorphism (commutator S)
  have hρc : ∀ α : MulAut S, ρ α c = c := by
    intro α
    refine hcuniq _ ⟨fun h => hc1 ((ρ α).injective (h.trans (map_one (ρ α)).symm)), ?_⟩
    intro y hy
    have hx : ((α.symm y : S) : S ⧸ commutator S) = c := by
      apply (ρ α).injective
      rw [← hy]
      exact (quotientAutomorphism_apply (commutator S) α (α.symm y)).trans
        (congrArg _ (α.apply_symm_apply y))
    rw [← hck _ hx]
    have e := quotientAutomorphism_apply Q α (α.symm y)
    rw [MulEquiv.apply_symm_apply] at e
    change orderOf (QuotientGroup.mk' Q y) = orderOf (QuotientGroup.mk' Q (α.symm y))
    rw [← e]
    exact MulEquiv.orderOf_eq _ _
  let St := MulAction.stabilizer (MulAut (S ⧸ commutator S)) c
  let ρ' : MulAut S →* St := ρ.codRestrict St hρc
  have hSt : Group.IsSolvable St := isSolvable_stabilizer_of_card_eight hcommV hcard hc1 hc2
  have hle : ρ'.ker ≤ (quotientAutomorphism (frattini S)).ker := by
    intro α hα
    have hα' : ρ α = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hα)
    rw [← MonoidHom.mem_ker, mem_quotientAutomorphism_kernel] at hα'
    rw [mem_quotientAutomorphism_kernel]
    intro x
    have h := QuotientGroup.eq.1 (hα' x)
    exact QuotientGroup.eq.2
      (CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini 2 hS h)
  have hfin : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hP : IsPGroup 2 ρ'.ker :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hS).2.to_le hle
  have : Group.IsNilpotent ρ'.ker := hP.isNilpotent
  exact Group.isSolvable_of_ker_le_range ρ'.ker.subtype ρ' fun α hα => ⟨⟨α, hα⟩, rfl⟩

end CFSG.Sporadic.SchreierLemmas
