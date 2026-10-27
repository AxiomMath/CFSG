module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
import CFSG.Holt.H78.Sec4LemmaD
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
import Mathlib.GroupTheory.NoncommPiCoprod
import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
import CFSG.Holt.H78.Schur
import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki SemidirectProduct Equiv
open scoped commutatorElement

namespace SetupQ

universe u

section Coordinates

variable {f n : ℕ}

@[expose] noncomputable def coordHom (f n : ℕ) (i : Fin n) : PSL2Model f →* L2Wreath f n :=
  SemidirectProduct.inl.comp (MonoidHom.mulSingle (fun _ : Fin n => PSL2Model f) i)

theorem coordHom_apply (i : Fin n) (x : PSL2Model f) :
    coordHom f n i x = SemidirectProduct.inl (Pi.mulSingle i x) := rfl

theorem coordHom_injective (i : Fin n) : Function.Injective (coordHom f n i) :=
  SemidirectProduct.inl_injective.comp
    (Pi.mulSingle_injective (M := fun _ : Fin n => PSL2Model f) i)

theorem coordHom_commute {i j : Fin n} (hij : i ≠ j) (x y : PSL2Model f) :
    Commute (coordHom f n i x) (coordHom f n j y) :=
  Commute.map (Pi.mulSingle_commute (f := fun _ : Fin n => PSL2Model f) hij x y)
    SemidirectProduct.inl

theorem conj_coordHom (σ : Perm (Fin n)) (i : Fin n) (x : PSL2Model f) :
    (inr σ : L2Wreath f n) * coordHom f n i x * (inr σ)⁻¹ = coordHom f n (σ i) x := by
  rw [coordHom_apply, coordHom_apply, ← WreathAct.permAct_mulSingle, inl_aut, map_inv]

theorem l2WreathBase_eq_iSup : l2WreathBase f n = ⨆ i, (coordHom f n i).range := by
  have hcomm : Pairwise fun i j => ∀ x y, Commute (coordHom f n i x) (coordHom f n j y) :=
    fun i j hij x y => coordHom_commute hij x y
  have h : MonoidHom.noncommPiCoprod (coordHom f n) hcomm =
      (SemidirectProduct.inl : (Fin n → PSL2Model f) →* L2Wreath f n) := by
    refine MonoidHom.pi_ext fun i x => ?_
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    rfl
  rw [l2WreathBase, ← h, MonoidHom.noncommPiCoprod_range]

theorem isPerfect_psl2Model (hf : 2 ≤ f) : Group.IsPerfect (PSL2Model f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (PSL2Model f) :=
    IsBenderGroup.isSimpleGroup (IsBenderGroup.isPSL2 f hf (MulEquiv.refl _))
  have : Nontrivial (PSL2Model f) := IsSimpleGroup.toNontrivial
  rw [Group.isPerfect_def]
  rcases (inferInstance : (commutator (PSL2Model f)).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    have hc : IsMulCommutative (PSL2Model f) := (commutator_eq_bot_iff (PSL2Model f)).1 h
    obtain ⟨x, hx⟩ := exists_ne (1 : PSL2Model f)
    have hxz : x ∈ Subgroup.center (PSL2Model f) :=
      Subgroup.mem_center_iff.2 fun g => hc.is_comm.comm g x
    rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hxz
    exact hx hxz
  · exact h

end Coordinates

section Central

variable {H : Type*} [Group H]

theorem commutatorElement_mul_of_mem_center {u : H} (hu : u ∈ Subgroup.center H) (s t : H) :
    ⁅u * s, t⁆ = ⁅s, t⁆ := by
  have hu' : ∀ g : H, u * g = g * u := fun g => (Subgroup.mem_center_iff.1 hu g).symm
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_eq_one_iff_mul_comm.2 (hu' t),
    mul_one, hu', mul_inv_cancel_right]

theorem commutatorElement_mul_of_mem_center' {v : H} (hv : v ∈ Subgroup.center H) (s t : H) :
    ⁅s, v * t⁆ = ⁅s, t⁆ := by
  have hv' : ∀ g : H, v * g = g * v := fun g => (Subgroup.mem_center_iff.1 hv g).symm
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.2 (hv' s).symm, one_mul, hv', mul_inv_cancel_right]

theorem commutator_le_of_central_decomp {P R : Subgroup H}
    (h : ∀ x ∈ P, ∃ u ∈ Subgroup.center H, ∃ a ∈ R, x = u * a) : ⁅P, P⁆ ≤ ⁅R, R⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨u, hu, a, ha, rfl⟩ := h x hx
  obtain ⟨v, hv, b, hb, rfl⟩ := h y hy
  rw [commutatorElement_mul_of_mem_center hu, commutatorElement_mul_of_mem_center' hv]
  exact Subgroup.commutator_mem_commutator ha hb

end Central

section Cover

variable {f n : ℕ} {H : Type*} [Group H]

@[expose] noncomputable def coordPre (π : H →* L2Wreath f n) (i : Fin n) : Subgroup H :=
  (coordHom f n i).range.comap π

@[expose] noncomputable def coordComm (π : H →* L2Wreath f n) (i : Fin n) : Subgroup H :=
  ⁅coordPre π i, coordPre π i⁆

variable (π : H →* L2Wreath f n)

theorem map_coordPre (hπ : Function.Surjective π) (i : Fin n) :
    (coordPre π i).map π = (coordHom f n i).range :=
  Subgroup.map_comap_eq_self_of_surjective hπ _

theorem coordComm_le_coordPre (i : Fin n) : coordComm π i ≤ coordPre π i :=
  Subgroup.commutator_le_self _

theorem map_coordComm (hπ : Function.Surjective π) (hf : 2 ≤ f) (i : Fin n) :
    (coordComm π i).map π = (coordHom f n i).range := by
  have := isPerfect_psl2Model hf
  have : Group.IsPerfect (coordHom f n i).range := Group.IsPerfect.range _
  rw [coordComm, Subgroup.map_commutator, map_coordPre π hπ, Subgroup.commutator_eq_self]

theorem exists_central_mul_coordComm (hπ : Function.Surjective π) (hf : 2 ≤ f)
    (hker : π.ker = Subgroup.center H) (i : Fin n) {x : H} (hx : x ∈ coordPre π i) :
    ∃ u ∈ Subgroup.center H, ∃ a ∈ coordComm π i, x = u * a := by
  have hmem : π x ∈ (coordComm π i).map π := by
    rw [map_coordComm π hπ hf i]
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hax⟩ := hmem
  refine ⟨x * a⁻¹, ?_, a, ha, by group⟩
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel]

theorem commutator_coordComm (hπ : Function.Surjective π) (hf : 2 ≤ f)
    (hker : π.ker = Subgroup.center H) (i : Fin n) :
    ⁅coordComm π i, coordComm π i⁆ = coordComm π i :=
  le_antisymm (Subgroup.commutator_le_self _)
    (commutator_le_of_central_decomp fun _ hx => exists_central_mul_coordComm π hπ hf hker i hx)

theorem commutator_coordPre_le_ker {i j : Fin n} (hij : i ≠ j) :
    ⁅coordPre π i, coordPre π j⁆ ≤ π.ker := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw [MonoidHom.mem_ker, map_commutatorElement, ← ha, ← hb]
  exact (coordHom_commute hij a b).commutator_eq

theorem commutator_coordComm_coordPre (hker : π.ker = Subgroup.center H) {i j : Fin n}
    (hij : i ≠ j) : ⁅coordComm π i, coordPre π j⁆ = ⊥ := by
  have h1 : ⁅coordPre π i, coordPre π j⁆ ≤ Subgroup.center H :=
    hker ▸ commutator_coordPre_le_ker π hij
  have h2 : ⁅coordPre π j, coordPre π i⁆ ≤ Subgroup.center H :=
    hker ▸ commutator_coordPre_le_ker π hij.symm
  refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
  · exact eq_bot_iff.2
      ((Subgroup.commutator_mono_left h1).trans (Subgroup.commutator_center_left _).le)
  · exact eq_bot_iff.2
      ((Subgroup.commutator_mono_left h2).trans (Subgroup.commutator_center_left _).le)

theorem commute_of_mem_coordComm (hker : π.ker = Subgroup.center H) {i j : Fin n} (hij : i ≠ j)
    {x y : H} (hx : x ∈ coordComm π i) (hy : y ∈ coordComm π j) : Commute x y := by
  have h := Subgroup.commutator_mem_commutator hx (coordComm_le_coordPre π j hy)
  rw [commutator_coordComm_coordPre π hker hij, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_commute.1 h

theorem mem_center_of_commute (hπ : Function.Surjective π) (hf : 2 ≤ f)
    (hker : π.ker = Subgroup.center H) {i : Fin n} {z : H} (hz : z ∈ coordComm π i)
    (hc : ∀ x ∈ coordComm π i, Commute x z) : z ∈ Subgroup.center H := by
  obtain ⟨c, hcz⟩ := coordComm_le_coordPre π i hz
  have hcc : c ∈ Subgroup.center (PSL2Model f) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : coordHom f n i y ∈ (coordComm π i).map π := by
      rw [map_coordComm π hπ hf]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    have h := congrArg π (hc x hx).eq
    rw [map_mul, map_mul, hxy, ← hcz, ← map_mul, ← map_mul] at h
    exact coordHom_injective i h
  rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hcc
  rw [← hker, MonoidHom.mem_ker, ← hcz, hcc, map_one]

theorem exists_conj_coordComm_le (hπ : Function.Surjective π) (i i₀ : Fin n) :
    ∃ g : H, ∀ x ∈ coordComm π i, g * x * g⁻¹ ∈ coordComm π i₀ := by
  obtain ⟨g, hg⟩ := hπ (inr (swap i i₀))
  have hT : ∀ x ∈ coordPre π i, g * x * g⁻¹ ∈ coordPre π i₀ := by
    rintro x ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, ← ha, conj_coordHom, swap_apply_left]
  refine ⟨g, fun x hx => ?_⟩
  have hmap : (coordPre π i).map (MulAut.conj g).toMonoidHom ≤ coordPre π i₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hT x hx
  have hc : (coordComm π i).map (MulAut.conj g).toMonoidHom ≤ coordComm π i₀ := by
    rw [coordComm, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact hc ⟨x, hx, rfl⟩

theorem center_le_iSup_coordComm (hπ : Function.Surjective π) (hf : 2 ≤ f)
    (hker : π.ker = Subgroup.center H)
    (hperf : ⁅(l2WreathBase f n).comap π, (l2WreathBase f n).comap π⁆ =
      (l2WreathBase f n).comap π) : Subgroup.center H ≤ ⨆ i, coordComm π i := by
  set S : Subgroup H := ⨆ i, coordComm π i with hS
  have hdec : ∀ x ∈ (l2WreathBase f n).comap π, ∃ u ∈ Subgroup.center H, ∃ a ∈ S, x = u * a := by
    intro x hx
    have hmem : π x ∈ S.map π := by
      rw [hS, Subgroup.map_iSup]
      simp_rw [map_coordComm π hπ hf]
      rw [← l2WreathBase_eq_iSup]
      exact hx
    obtain ⟨a, ha, hax⟩ := hmem
    refine ⟨x * a⁻¹, ?_, a, ha, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel]
  intro m hm
  have hmL : m ∈ (l2WreathBase f n).comap π := by
    rw [← hker, MonoidHom.mem_ker] at hm
    rw [Subgroup.mem_comap, hm]
    exact Subgroup.one_mem _
  rw [← hperf] at hmL
  exact Subgroup.commutator_le_self _ (commutator_le_of_central_decomp hdec hmL)

end Cover

section KrullSchmidt

variable {H : Type*} [Group H] {ι : Type*} [Fintype ι]

theorem le_of_le_iSup (A : ι → Subgroup H) (i₀ : ι)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y)
    (hZ : ∀ i, ∀ z ∈ A i, (∀ x ∈ A i, Commute x z) → z ∈ Subgroup.center H)
    (hconj : ∀ i, ∃ g : H, ∀ x ∈ A i, g * x * g⁻¹ ∈ A i₀)
    (hM : Subgroup.center H ≤ ⨆ i, A i) : Subgroup.center H ≤ A i₀ := by
  classical
  have hcomm' : Pairwise fun i j : ι => ∀ x y : H, x ∈ A i → y ∈ A j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  intro m hm
  have hrange : m ∈ (Subgroup.noncommPiCoprod hcomm').range := by
    rw [Subgroup.noncommPiCoprod_range]
    exact hM hm
  obtain ⟨a, rfl⟩ := hrange
  rw [Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  have hai : (a i : H) ∈ Subgroup.center H := by
    refine hZ i _ (a i).2 fun x hx => ?_
    set c := (Finset.univ.erase i).noncommProd (fun j => (a j : H)) (fun j _ k _ hjk =>
      hcomm' hjk _ _ (a j).2 (a k).2)
    have hmc : (a i : H) * c = Subgroup.noncommPiCoprod hcomm' a := by
      rw [Subgroup.noncommPiCoprod_apply]
      exact Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) (fun j => (a j : H)) _ _
    have hxc : Commute x c := by
      refine Finset.noncommProd_commute _ _ _ _ fun j hj => ?_
      exact hcomm i j (Finset.ne_of_mem_erase hj).symm x hx _ (a j).2
    have h1 : x * ((a i : H) * c) = ((a i : H) * c) * x := by
      rw [hmc]
      exact Subgroup.mem_center_iff.1 hm x
    have h2 : (x * a i) * c = (a i * x) * c := by
      calc (x * a i) * c = x * (a i * c) := by rw [mul_assoc]
        _ = (a i * c) * x := h1
        _ = a i * (c * x) := by rw [mul_assoc]
        _ = a i * (x * c) := by rw [hxc.eq]
        _ = (a i * x) * c := by rw [mul_assoc]
    exact mul_right_cancel h2
  obtain ⟨g, hg⟩ := hconj i
  have h3 : g * (a i : H) * g⁻¹ = a i := by
    rw [Subgroup.mem_center_iff.1 hai g, mul_inv_cancel_right]
  have := hg _ (a i).2
  rwa [h3] at this

end KrullSchmidt

section Multiplier

variable {X : Type u} [Group X]

@[expose] def oddPart (K : Subgroup X) (hK : K ≤ Subgroup.center X) : Subgroup X where
  carrier := {x | x ∈ K ∧ Odd (orderOf x)}
  one_mem' := ⟨K.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxK, hx⟩ ⟨hyK, hy⟩
    refine ⟨K.mul_mem hxK hyK, ?_⟩
    have hc : Commute x y := Subgroup.mem_center_iff.1 (hK hyK) x
    exact (hx.mul hy).of_dvd_nat (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  inv_mem' := by
    rintro x ⟨hxK, hx⟩
    exact ⟨K.inv_mem hxK, by rwa [orderOf_inv]⟩

theorem eq_one_of_odd_of_isPGroup {Q : Subgroup X} (hQ : IsPGroup 2 Q) {z : X} (hz : z ∈ Q)
    (hodd : Odd (orderOf z)) : z = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨z, hz⟩
  have hdvd : orderOf z ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra h
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

theorem card_le_of_multiplier {Y : Type*} [Group Y] [Finite X] [Group.IsPerfect X] (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hc : ρ.ker ≤ Subgroup.center X) {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) (hQk : Q ≤ ρ.ker) (c : ℕ)
    (hmult : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* Y),
      Function.Surjective η → η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker →
        Nat.card η.ker ≤ c) : Nat.card Q ≤ c := by
  set N := oddPart ρ.ker hc
  have hNk : N ≤ ρ.ker := fun x hx => hx.1
  have : N.Normal := Subgroup.normal_of_le_center (hNk.trans hc)
  let η : X ⧸ N →* Y := QuotientGroup.lift N ρ hNk
  have hηmk : ∀ x : X, η (QuotientGroup.mk x) = ρ x := fun x => rfl
  have hη : Function.Surjective η := by
    intro y
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hηc : η.ker ≤ Subgroup.center (X ⧸ N) := by
    intro e he
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
    have hx : x ∈ ρ.ker := he
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hc hx) g]
  have hηp : IsPGroup 2 η.ker := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e : X ⧸ N)
    have hxk : x ∈ ρ.ker := by
      have := e.2
      rw [← hx] at this
      exact this
    obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨s, Subtype.ext ?_⟩
    have hmem : x ^ 2 ^ s ∈ N := by
      refine ⟨ρ.ker.pow_mem hxk _, ?_⟩
      rw [orderOf_pow_of_dvd (by positivity) ⟨t, hst⟩, hst, Nat.mul_div_cancel_left _
        (by positivity)]
      exact ht
    rw [Subgroup.coe_pow, ← hx, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  have hle : Nat.card η.ker ≤ c := hmult _ η hη hηc hηp
  let φ : Q → η.ker := fun q => ⟨QuotientGroup.mk (q : X), by
    rw [MonoidHom.mem_ker, hηmk]
    exact hQk q.2⟩
  have hφ : Function.Injective φ := by
    intro q q' h
    have h1 : (QuotientGroup.mk (q : X) : X ⧸ N) = QuotientGroup.mk (q' : X) :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h1
    have hz : (q : X)⁻¹ * q' = 1 :=
      eq_one_of_odd_of_isPGroup hQ (Q.mul_mem (Q.inv_mem q.2) q'.2) h1.2
    exact Subtype.ext (inv_mul_eq_one.1 hz)
  exact (Nat.card_le_card_of_injective φ hφ).trans hle

end Multiplier

section Bound

variable {f n : ℕ} {H : Type u} [Group H] [Finite H]

theorem card_le_of_equiv_multiplier [NeZero n] (hf : 2 ≤ f) (π : H →* L2Wreath f n)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center H)
    (hperf : ⁅(l2WreathBase f n).comap π, (l2WreathBase f n).comap π⁆ =
      (l2WreathBase f n).comap π)
    {Q : Subgroup H} (hQ : IsPGroup 2 Q) (hQc : Q ≤ Subgroup.center H)
    {Y : Type*} [Group Y] (ε : PSL2Model f ≃* Y) (c : ℕ)
    (hmult : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* Y),
      Function.Surjective η → η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker →
        Nat.card η.ker ≤ c) : Nat.card Q ≤ c := by
  have hMA : Subgroup.center H ≤ coordComm π 0 :=
    le_of_le_iSup (coordComm π) 0
      (fun i j hij x hx y hy => commute_of_mem_coordComm π hker hij hx hy)
      (fun i z hz hc => mem_center_of_commute π hπ hf hker hz hc)
      (fun i => exists_conj_coordComm_le π hπ i 0)
      (center_le_iSup_coordComm π hπ hf hker hperf)
  have hQA : Q ≤ coordComm π 0 := hQc.trans hMA
  have : Group.IsPerfect (coordComm π 0) :=
    Subgroup.isPerfect_iff.2 (commutator_coordComm π hπ hf hker 0)
  have hinj := coordHom_injective (f := f) (n := n) 0
  let ρ : coordComm π 0 →* PSL2Model f :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
      ((π.comp (coordComm π 0).subtype).codRestrict (coordHom f n 0).range
        fun x => coordComm_le_coordPre π 0 x.2)
  have hρ : ∀ x : coordComm π 0, coordHom f n 0 (ρ x) = π x := fun x =>
    MonoidHom.apply_ofInjective_symm hinj _
  have hρs : Function.Surjective ρ := by
    intro y
    have hy : coordHom f n 0 y ∈ (coordComm π 0).map π := by
      rw [map_coordComm π hπ hf]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, coordHom_injective 0 (by rw [hρ]; exact hxy)⟩
  have hπ1 : ∀ x : coordComm π 0, ρ x = 1 ↔ (x : H) ∈ Subgroup.center H := by
    intro x
    rw [← hker, MonoidHom.mem_ker, ← (coordHom_injective (f := f) (n := n) 0).eq_iff, hρ,
      map_one]
  have hρk : ρ.ker ≤ Subgroup.center (coordComm π 0) := by
    intro x hx
    have h2 := (hπ1 x).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 g)
  let ρ' : coordComm π 0 →* Y := ε.toMonoidHom.comp ρ
  have hker' : ρ'.ker = ρ.ker := by
    ext x
    simp [ρ', MonoidHom.mem_ker]
  have hQ' : IsPGroup 2 (Q.subgroupOf (coordComm π 0)) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm
  have hQ'k : Q.subgroupOf (coordComm π 0) ≤ ρ'.ker := by
    intro x hx
    rw [hker', MonoidHom.mem_ker, hπ1]
    exact hQc hx
  have hle := card_le_of_multiplier ρ' (ε.surjective.comp hρs) (hker' ▸ hρk) hQ' hQ'k c hmult
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv] at hle

theorem two_part_bound [NeZero n] (hf : 2 ≤ f) (π : H →* L2Wreath f n)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center H)
    (hperf : ⁅(l2WreathBase f n).comap π, (l2WreathBase f n).comap π⁆ =
      (l2WreathBase f n).comap π)
    {Q : Subgroup H} (hQ : IsPGroup 2 Q) (hQc : Q ≤ Subgroup.center H) :
    (3 ≤ f → Q = ⊥) ∧ (f = 2 → Nat.card Q ≤ 2) := by
  refine ⟨fun hf3 => ?_, fun hf2 => ?_⟩
  · refine Subgroup.eq_bot_of_card_le Q (card_le_of_equiv_multiplier hf π hπ hker hperf hQ hQc
      CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL 1 ?_)
    intro E _ _ _ η hη hηc hηp
    rw [CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot f hf3
      (GaloisField.card 2 f (by omega)) η hη hηc hηp]
    simp
  · subst hf2
    obtain ⟨κ⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
    refine card_le_of_equiv_multiplier hf π hπ hker hperf hQ hQc
      (CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL.trans κ) 2 ?_
    intro E _ _ _ η hη hηc hηp
    exact CFSG.Holt.H78.card_ker_le_two_of_alternatingGroup (by simp) η hη hηc hηp

end Bound

end SetupQ

theorem tenSetupQ_of_perfect (hP : TenSetupPerfect) : TenSetupQ := by
  intro G _ _ D hC f n hH
  obtain ⟨e⟩ := hH.iso
  set H := Halpha D hC.alpha
  let π : H →* L2Wreath f n := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center H := by
    ext x
    rw [MonoidHom.mem_ker]
    exact (e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff x))
  have hperf : ⁅(l2WreathBase f n).comap π, (l2WreathBase f n).comap π⁆ =
      (l2WreathBase f n).comap π := by
    refine Subgroup.map_injective H.subtype_injective ?_
    rw [Subgroup.map_commutator]
    exact hP G D hC f n hH e
  have : NeZero n := ⟨by have := hH.five_le; omega⟩
  have hQc : CFSG.pCore 2 H ≤ Subgroup.center H :=
    (CFSG.pCore_le_solvableRadical 2 H).trans hH.radH.le
  obtain ⟨h3, h2⟩ := SetupQ.two_part_bound hH.two_le π hπ hker hperf CFSG.pCore_isPGroup hQc
  by_cases hf2 : f = 2
  · have hle := h2 hf2
    have hpos : 0 < Nat.card (CFSG.pCore 2 H) := Nat.card_pos
    rcases (by omega : Nat.card (CFSG.pCore 2 H) = 1 ∨ Nat.card (CFSG.pCore 2 H) = 2) with h | h
    · exact Or.inl (Subgroup.eq_bot_of_card_le _ h.le)
    · exact Or.inr ⟨hf2, h⟩
  · exact Or.inl (h3 (by have := hH.two_le; omega))

end CFSG.OddTranspositions.PartThree

end
