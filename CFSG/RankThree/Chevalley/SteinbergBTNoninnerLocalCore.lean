module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank

theorem exists_mul_mod_eq_one {p j : ℕ} (hp : p.Prime) (hj0 : 0 < j) (hjp : j < p) :
    ∃ r : ℕ, r * j % p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hjZ : (j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hj0 hjp
  refine ⟨((j : ZMod p)⁻¹).val, ?_⟩
  have h : (((((j : ZMod p)⁻¹).val * j : ℕ)) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hjZ, Nat.cast_one]
  rw [(ZMod.natCast_eq_natCast_iff' _ _ _).1 h, Nat.mod_eq_of_lt hp.one_lt]

theorem pow_eq_self_of_mod_eq_one {G : Type*} [Monoid G] {g : G} {p n : ℕ} (hg : orderOf g = p)
    (hn : n % p = 1) : g ^ n = g := by
  rw [← pow_mod_orderOf, hg, hn, pow_one]

theorem aschbacherSolvableCore_centralizer_eq_bot_of_conj {A : Type*} [Group A]
    {B : Subgroup A} [Finite B] {p : ℕ} (hp : p.Prime) (a : B) (hap : orderOf a = p) (ψ : A)
    (N : Subgroup A) (hNB : ∀ n ∈ N, ψ⁻¹ * n * ψ ∈ B)
    (hNa : N ≤ Subgroup.centralizer {ψ * (a : A) * ψ⁻¹})
    (hNnormal : (N.subgroupOf (Subgroup.centralizer {ψ * (a : A) * ψ⁻¹})).Normal)
    (hsimple : IsSimpleGroup N) (hnc : ¬∀ x y : N, x * y = y * x)
    (hcent : Subgroup.centralizer {ψ * (a : A) * ψ⁻¹} ⊓ Subgroup.centralizer (N : Set A) ≤
      Subgroup.zpowers (ψ * (a : A) * ψ⁻¹)) :
    aschbacherSolvableCore p (Subgroup.centralizer {a} : Subgroup B) = ⊥ := by
  classical
  set H := (Subgroup.centralizer {a} : Subgroup B) with hH
  set a' : A := ψ * (a : A) * ψ⁻¹ with ha'
  let κ : H →* A := (MulAut.conj ψ).toMonoidHom.comp (B.subtype.comp H.subtype)
  have hκ : ∀ h : H, κ h = ψ * ((h : B) : A) * ψ⁻¹ := fun h => rfl
  have hκinj : Function.Injective κ := fun h₁ h₂ e => by
    rw [hκ, hκ] at e
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel e)))
  have hκa : ∀ h : H, κ h ∈ Subgroup.centralizer {a'} := by
    intro h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ((h : B) : A) * (a : A) = (a : A) * ((h : B) : A) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 h.2)
    rw [hκ, ha']
    calc ψ * ((h : B) : A) * ψ⁻¹ * (ψ * (a : A) * ψ⁻¹) = ψ * (((h : B) : A) * a) * ψ⁻¹ := by
          group
      _ = ψ * ((a : A) * ((h : B) : A)) * ψ⁻¹ := by rw [h2]
      _ = ψ * (a : A) * ψ⁻¹ * (ψ * ((h : B) : A) * ψ⁻¹) := by group
  have hsurj : ∀ n ∈ N, ∃ h : H, κ h = n := by
    intro n hn
    have h1 : n * a' = a' * n := Subgroup.mem_centralizer_singleton_iff.1 (hNa hn)
    refine ⟨⟨⟨ψ⁻¹ * n * ψ, hNB n hn⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext ?_)⟩, ?_⟩
    · change ψ⁻¹ * n * ψ * (a : A) = (a : A) * (ψ⁻¹ * n * ψ)
      calc ψ⁻¹ * n * ψ * (a : A) = ψ⁻¹ * (n * a') * ψ := by rw [ha']; group
        _ = ψ⁻¹ * (a' * n) * ψ := by rw [h1]
        _ = (a : A) * (ψ⁻¹ * n * ψ) := by rw [ha']; group
    · change ψ * (ψ⁻¹ * n * ψ) * ψ⁻¹ = n
      group
  set NH : Subgroup H := N.comap κ with hNH
  have hNHnormal : NH.Normal := by
    refine ⟨fun n hn h => ?_⟩
    have hn' : κ n ∈ N := hn
    have h1 := hNnormal.conj_mem ⟨κ n, hNa hn'⟩ (Subgroup.mem_subgroupOf.2 hn') ⟨κ h, hκa h⟩
    rw [Subgroup.mem_subgroupOf] at h1
    change κ (h * n * h⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact h1
  let eN : NH ≃* N := MulEquiv.ofBijective ((κ.comp NH.subtype).codRestrict N fun h => h.2)
    ⟨fun h₁ h₂ e => Subtype.ext (hκinj (congrArg Subtype.val e)), fun n => by
      obtain ⟨h, hh⟩ := hsurj n n.2
      exact ⟨⟨h, show κ h ∈ N by rw [hh]; exact n.2⟩, Subtype.ext hh⟩⟩
  have : IsSimpleGroup N := hsimple
  have : IsSimpleGroup NH := eN.isSimpleGroup
  have hncNH : ¬∀ x y : NH, x * y = y * x := fun h => hnc fun x y => by
    have e := congrArg eN (h (eN.symm x) (eN.symm y))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at e
  have : Finite H := Subtype.finite
  obtain ⟨hsolv, hchar, hpd, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set D := aschbacherSolvableCore p H with hD
  have hDnormal : D.Normal := Subgroup.normal_of_characteristic D
  have hDN : D ⊓ NH = ⊥ := by
    have : (D.subgroupOf NH).Normal := hDnormal.subgroupOf NH
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.subgroupOf NH) with h | h
    · exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    · exfalso
      have hle : NH ≤ D := Subgroup.subgroupOf_eq_top.1 h
      have : Group.IsSolvable D := hsolv
      have : Group.IsSolvable NH :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      exact hncNH (IsSimpleGroup.comm_iff_isSolvable.2 this)
  have hcomm : ∀ d ∈ D, ∀ n ∈ NH, d * n = n * d := by
    have hle : ⁅D, NH⁆ ≤ D ⊓ NH := Subgroup.commutator_le_inf D NH
    rw [hDN, le_bot_iff] at hle
    intro d hd n hn
    have h1 := Subgroup.commutator_mem_commutator hd hn
    rwa [hle, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hDa : D.map κ ≤ Subgroup.zpowers a' := by
    rintro _ ⟨d, hd, rfl⟩
    refine hcent (Subgroup.mem_inf.2 ⟨hκa d, Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩)
    obtain ⟨h, rfl⟩ := hsurj n hn
    have h1 := hcomm d hd h hn
    rw [← map_mul, ← map_mul, h1]
  have hcard : Nat.card D ∣ p := by
    have h1 := Subgroup.card_dvd_of_le hDa
    rwa [Subgroup.card_map_of_injective hκinj, Nat.card_zpowers, ha',
      show ψ * (a : A) * ψ⁻¹ = MulAut.conj ψ (a : A) from rfl, MulEquiv.orderOf_eq,
      Subgroup.orderOf_coe, hap] at h1
  rcases (Nat.dvd_prime hp).1 hcard with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd (h1 ▸ dvd_refl p) hpd

theorem aschbacherSolvableCore_centralizer_eq_bot_of_inner {M : Type*} [Group M]
    {C J : Subgroup M} [Finite C] {p : ℕ} (hp : p.Prime) (hJC : J ≤ C)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (α : B)
    (hαp : orderOf α = p) (ψ δ : MulAut C) (hψ : ψ * (α : MulAut C) * ψ⁻¹ = δ)
    (hsimple : IsSimpleGroup J) (hnc : ¬∀ a b : J, a * b = b * a)
    (ι : ↥(J.subgroupOf C) ≃* ↥((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)))
    (hNδ : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {δ})
    (hnormal : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {δ})).Normal)
    (hcent : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers δ) :
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  have : Finite (MulAut C) := Finite.of_injective (fun β : MulAut C => (β : C → C))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite B := Subtype.finite
  set N := (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) with hN
  have e : N ≃* J := ι.symm.trans (Subgroup.subgroupOfEquivOfLe hJC)
  have : IsSimpleGroup J := hsimple
  refine aschbacherSolvableCore_centralizer_eq_bot_of_conj hp α hαp ψ N ?_ (hψ ▸ hNδ)
    (hψ ▸ hnormal) e.isSimpleGroup ?_ (hψ ▸ hcent.le)
  · rintro _ ⟨j, -, rfl⟩
    have h := mulAut_mul_conj_mul_inv ψ⁻¹ j
    rw [inv_inv] at h
    change ψ⁻¹ * MulAut.conj j * ψ ∈ B
    rw [h]
    exact hB ⟨_, rfl⟩
  · intro h
    exact hnc fun x y => by
      have e' := congrArg e (h (e.symm x) (e.symm y))
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at e'

end CFSG.RankThree.Chevalley
