module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext (IsInternalDirect IsDirectSumMod NatL2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x (natI natC natIi)

namespace P2251e

section Proj

variable {X : Type} [Group X] {m : ℕ} {H : Subgroup X} {Nb : Fin m → Subgroup X}

@[expose] def proj (hd : IsInternalDirect H Nb) (j : Fin m) (A : Subgroup X) : Subgroup X :=
  ((A.comap (P22y.piMul hd)).map (Pi.evalMonoidHom (fun k => ↥(Nb k)) j)).map (Nb j).subtype

theorem mem_proj (hd : IsInternalDirect H Nb) (j : Fin m) {A : Subgroup X} {b : X} :
    b ∈ proj hd j A ↔ ∃ f : ∀ k, ↥(Nb k), P22y.piMul hd f ∈ A ∧ ((f j : ↥(Nb j)) : X) = b := by
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩

theorem proj_le (hd : IsInternalDirect H Nb) (j : Fin m) (A : Subgroup X) : proj hd j A ≤ Nb j := by
  rintro _ ⟨_, _, rfl⟩
  exact Subtype.property _

theorem exists_piMul (hd : IsInternalDirect H Nb) {a : X} (ha : a ∈ H) :
    ∃ f : ∀ k, ↥(Nb k), P22y.piMul hd f = a := by
  rw [← P22y.piMul_range hd] at ha
  exact ha

theorem isPGroup_proj (hd : IsInternalDirect H Nb) (j : Fin m) {A : Subgroup X} {p : ℕ}
    (hA : IsPGroup p A) : IsPGroup p (proj hd j A) := by
  rintro ⟨b, hb⟩
  obtain ⟨f, hfA, rfl⟩ := (mem_proj hd j).1 hb
  obtain ⟨k, hk⟩ := hA ⟨P22y.piMul hd f, hfA⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : P22y.piMul hd (f ^ p ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 : f ^ p ^ k = 1 := P22y.piMul_injective hd (h1.trans (map_one _).symm)
  simpa using congrArg Subtype.val (congrFun h2 j)

theorem card_proj_eq_two [Finite X] (hd : IsInternalDirect H Nb) {j : Fin m} (h6 : Nat.card ↥(Nb j) = 6)
    {A : Subgroup X} (hA : IsPGroup 2 A) (hne : proj hd j A ≠ ⊥) : Nat.card ↥(proj hd j A) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_proj hd j hA)
  have hdvd : 2 ^ k ∣ 6 := by
    rw [← hk, ← h6]
    exact Subgroup.card_dvd_of_le (proj_le hd j A)
  have hk2 : k < 2 := by
    by_contra hk2
    have h4 : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (not_lt.1 hk2)).trans hdvd
    norm_num at h4
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.1 (by rw [hk, pow_zero])) hne
  · rw [hk, pow_one]

end Proj

section Module

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure NatDecAt (ρ : Representation (ZMod 2) X V) (Nbar : Subgroup X) {m : ℕ} (Nb : Fin m → Subgroup X)
    (j : Fin m) : Prop where
  direct : IsInternalDirect Nbar Nb
  sum : IsDirectSumMod (natI ρ Nbar) (natC ρ Nbar) (fun k => natIi ρ Nbar (Nb k))
  nat : ∃ n : ℕ, 1 ≤ n ∧
    NatL2 ρ (Nb j) (natIi ρ Nbar (Nb j)) (natIi ρ Nbar (Nb j) ⊓ natC ρ Nbar) n

variable {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem inv_I {g : X} (hg : g ∈ Nbar) : ∀ u ∈ natI ρ Nbar, ρ g u ∈ natI ρ Nbar :=
  P22x.commOn_invariant (A := Nbar) (U := ⊤) (g := g)
    (fun a ha => Nbar.mul_mem (Nbar.mul_mem hg ha) (Nbar.inv_mem hg)) fun _ _ => trivial

theorem inv_Ii (hd : IsInternalDirect Nbar Nb) {g : X} (hg : g ∈ Nbar) (k : Fin m) :
    ∀ u ∈ natIi ρ Nbar (Nb k), ρ g u ∈ natIi ρ Nbar (Nb k) :=
  P22x.commOn_invariant (A := Nb k) (U := natI ρ Nbar) (g := g)
    (fun a ha => (mem_normalizer_iff.1 (P22w.le_normalizer_of_isInternalDirect hd k hg) a).1 ha)
    (inv_I hg)

theorem Ii_le_I (hd : IsInternalDirect Nbar Nb) (k : Fin m) : natIi ρ Nbar (Nb k) ≤ natI ρ Nbar :=
  P22x.commOn_le_of_invariant fun a ha u hu => inv_I (P22w.le_of_isInternalDirect hd k ha) u hu

theorem NatDecAt.step1 {j : Fin m} (d : NatDecAt ρ Nbar Nb j) {k : Fin m} (hkj : k ≠ j) {g : X}
    (hg : g ∈ Nb k) {x : V} (hx : x ∈ natIi ρ Nbar (Nb j)) : ρ g x - x ∈ natC ρ Nbar := by
  have h1 : ρ g x - x ∈ natIi ρ Nbar (Nb k) := P22x.sub_mem_commOn hg (Ii_le_I d.direct j hx)
  have h2 : ρ g x - x ∈ natIi ρ Nbar (Nb j) :=
    (natIi ρ Nbar (Nb j)).sub_mem
      (inv_Ii d.direct (P22w.le_of_isInternalDirect d.direct k hg) j x hx) hx
  exact d.sum.2 j ⟨Submodule.mem_sup_left h2,
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hkj h1))⟩

theorem NatDecAt.exists_comm {j : Fin m} (d : NatDecAt ρ Nbar Nb j) :
    ∀ x ∈ natIi ρ Nbar (Nb j), ∃ x' ∈ commOn ρ (Nb j) (natIi ρ Nbar (Nb j)), x - x' ∈ natC ρ Nbar := by
  intro x hx
  obtain ⟨n, -, F, _, _, -, -, -, -, φ, ψ, -, hψA, hψs, hψφ⟩ := d.nat
  obtain ⟨g₁, g₂, u₁, u₂, hy⟩ := P22x.sl2_exists_decomp (ψ x)
  obtain ⟨x₁, hx₁, hψ₁⟩ := hψs u₁
  obtain ⟨x₂, hx₂, hψ₂⟩ := hψs u₂
  set h₁ : ↥(Nb j) := φ.symm g₁
  set h₂ : ↥(Nb j) := φ.symm g₂
  have hcomm : (ρ (h₁ : X) x₁ - x₁) + (ρ (h₂ : X) x₂ - x₂) ∈
      commOn ρ (Nb j) (natIi ρ Nbar (Nb j)) :=
    Submodule.add_mem _ (P22x.sub_mem_commOn h₁.2 hx₁) (P22x.sub_mem_commOn h₂.2 hx₂)
  have hAle : commOn ρ (Nb j) (natIi ρ Nbar (Nb j)) ≤ natIi ρ Nbar (Nb j) :=
    P22x.commOn_le_of_invariant fun a ha u hu =>
      inv_Ii d.direct (P22w.le_of_isInternalDirect d.direct j ha) j u hu
  refine ⟨_, hcomm, ?_⟩
  have hker : ψ (x - ((ρ (h₁ : X) x₁ - x₁) + (ρ (h₂ : X) x₂ - x₂))) = 0 := by
    rw [map_sub, map_add, map_sub, map_sub, hψφ h₁ x₁ hx₁, hψφ h₂ x₂ hx₂, hψ₁, hψ₂]
    simp only [h₁, h₂, MulEquiv.apply_symm_apply]
    rw [hy]
    abel
  exact (hψA _ ((natIi ρ Nbar (Nb j)).sub_mem hx (hAle hcomm)) hker).2

theorem NatDecAt.lemma21 {j : Fin m} (d : NatDecAt ρ Nbar Nb j) {k : Fin m} (hkj : k ≠ j) {g : X}
    (hg : g ∈ Nb k) {x : V} (hx : x ∈ natIi ρ Nbar (Nb j)) : ρ g x = x := by
  obtain ⟨x', hx'm, hxx'⟩ := d.exists_comm x hx
  have hcfix : ρ g (x - x') = x - x' :=
    P22x.natC_fix (P22w.le_of_isInternalDirect d.direct k hg) hxx'
  have hx'fix : ρ g x' = x' := by
    have hle : commOn ρ (Nb j) (natIi ρ Nbar (Nb j)) ≤ LinearMap.eqLocus (ρ g) LinearMap.id := by
      rw [P22x.commOn_le_iff]
      intro h hh u hu
      have hδ : ρ g u - u ∈ natC ρ Nbar := d.step1 hkj hg hu
      have hfixh : ρ h (ρ g u - u) = ρ g u - u :=
        P22x.natC_fix (P22w.le_of_isInternalDirect d.direct j hh) hδ
      have hcomm : ρ g (ρ h u) = ρ h (ρ g u) := by
        rw [← Module.End.mul_apply, ← map_mul, d.direct.2.1 k j hkj g hg h hh, map_mul,
          Module.End.mul_apply]
      show ρ g (ρ h u - u) = ρ h u - u
      rw [map_sub, hcomm]
      rw [map_sub] at hfixh
      exact sub_eq_sub_iff_sub_eq_sub.1 hfixh
    exact hle hx'm
  have h1 : ρ g (x - x') = ρ g x - ρ g x' := map_sub _ _ _
  rw [hx'fix] at h1
  have h2 : ρ g x - x' = x - x' := by rw [← h1]; exact hcfix
  exact sub_left_inj.1 h2

theorem NatDecAt.pi_act {j : Fin m} (d : NatDecAt ρ Nbar Nb j) (f : ∀ k, ↥(Nb k)) {x : V}
    (hx : x ∈ natIi ρ Nbar (Nb j)) : ρ (P22y.piMul d.direct f) x = ρ ((f j : ↥(Nb j)) : X) x := by
  classical
  let S : Subgroup (∀ k, ↥(Nb k)) :=
    { carrier := {f | ∀ x ∈ natIi ρ Nbar (Nb j),
        ρ (P22y.piMul d.direct f) x = ρ ((f j : ↥(Nb j)) : X) x}
      one_mem' := by
        intro x _
        simp
      mul_mem' := by
        intro f g hf hg x hx
        have hgx : ρ ((g j : ↥(Nb j)) : X) x ∈ natIi ρ Nbar (Nb j) :=
          inv_Ii d.direct (P22w.le_of_isInternalDirect d.direct j (g j).2) j x hx
        rw [map_mul, map_mul, Module.End.mul_apply, hg x hx, hf _ hgx, Pi.mul_apply,
          Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      inv_mem' := by
        intro f hf x hx
        have hy : ρ (((f j : ↥(Nb j)) : X)⁻¹) x ∈ natIi ρ Nbar (Nb j) :=
          inv_Ii d.direct (Nbar.inv_mem (P22w.le_of_isInternalDirect d.direct j (f j).2)) j x hx
        have h1 : ρ (P22y.piMul d.direct f) (ρ (((f j : ↥(Nb j)) : X)⁻¹) x) = x := by
          rw [hf _ hy, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        have h2 : ρ (P22y.piMul d.direct f⁻¹) x = ρ (((f j : ↥(Nb j)) : X)⁻¹) x := by
          calc ρ (P22y.piMul d.direct f⁻¹) x
              = ρ ((P22y.piMul d.direct f)⁻¹)
                  (ρ (P22y.piMul d.direct f) (ρ (((f j : ↥(Nb j)) : X)⁻¹) x)) := by
                rw [h1, map_inv]
            _ = ρ (((f j : ↥(Nb j)) : X)⁻¹) x := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
                rfl
        rw [h2]
        simp }
  have hsingle : ∀ (k : Fin m) (y : ↥(Nb k)), (Pi.mulSingle k y : ∀ k, ↥(Nb k)) ∈ S := by
    intro k y x hx
    rw [P22y.piMul_mulSingle d.direct k y]
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [Pi.mulSingle_eq_of_ne hjk]
      simpa using d.lemma21 (Ne.symm hjk) y.2 hx
  have hS : ∀ f : (∀ k, ↥(Nb k)), f ∈ S := by
    intro f
    rw [← Finset.noncommProd_mulSingle f]
    exact Subgroup.noncommProd_mem S _ fun k _ => hsingle k (f k)
  exact hS f x hx

theorem NatDecAt.exists_not_mem {j : Fin m} (d : NatDecAt ρ Nbar Nb j) {b : X} (hb : b ∈ Nb j)
    (hb1 : b ≠ 1) : ∃ y ∈ natIi ρ Nbar (Nb j), ρ b y - y ∉ natC ρ Nbar := by
  obtain ⟨n, -, F, _, _, -, -, -, -, φ, ψ, hψB, -, hψs, hψφ⟩ := d.nat
  by_contra hcon
  push Not at hcon
  have hφ : φ ⟨b, hb⟩ = 1 := by
    refine P22x.sl2_eq_one_of_fix fun u => ?_
    obtain ⟨y, hy, rfl⟩ := hψs u
    have hyb : ρ b y ∈ natIi ρ Nbar (Nb j) :=
      inv_Ii d.direct (P22w.le_of_isInternalDirect d.direct j hb) j y hy
    have h0 := hψB _ ⟨(natIi ρ Nbar (Nb j)).sub_mem hyb hy, hcon y hy⟩
    rw [map_sub, sub_eq_zero] at h0
    rw [← hψφ ⟨b, hb⟩ y hy]
    exact h0
  exact hb1 (congrArg Subtype.val (φ.injective (hφ.trans (map_one φ).symm)))

theorem NatDecAt.exists_fixed {j : Fin m} (d : NatDecAt ρ Nbar Nb j) {Q : Subgroup X} (hQ : Q ≤ Nbar)
    (h2 : Nat.card ↥(proj d.direct j Q) = 2) :
    ∃ v ∈ natIi ρ Nbar (Nb j), v ∉ natC ρ Nbar ∧ ∀ a ∈ Q, ρ a v = v := by
  obtain ⟨t, ht1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(proj d.direct j Q))).1 h2
  have hcases : ∀ b ∈ proj d.direct j Q, b = 1 ∨ b = (t : X) := by
    intro b hb
    by_cases hb1 : (⟨b, hb⟩ : ↥(proj d.direct j Q)) = 1
    · exact Or.inl (congrArg Subtype.val hb1)
    · exact Or.inr (congrArg Subtype.val (huniq _ hb1))
  have htt : (t : X) * (t : X) = 1 := by
    have h := pow_card_eq_one' (x := t)
    rw [h2, pow_two] at h
    exact congrArg Subtype.val h
  have htN : (t : X) ∈ Nb j := proj_le d.direct j Q t.2
  obtain ⟨y, hy, hyC⟩ := d.exists_not_mem htN fun h => ht1 (Subtype.ext h)
  have hv : ρ (t : X) y - y ∈ natIi ρ Nbar (Nb j) :=
    (natIi ρ Nbar (Nb j)).sub_mem
      (inv_Ii d.direct (P22w.le_of_isInternalDirect d.direct j htN) j y hy) hy
  refine ⟨_, hv, hyC, fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_piMul d.direct (hQ ha)
  rw [d.pi_act f hv]
  rcases hcases _ ((mem_proj d.direct j).2 ⟨f, ha, rfl⟩) with h | h
  · rw [h, map_one, Module.End.one_apply]
  · rw [h, map_sub, ← Module.End.mul_apply, ← map_mul, htt, map_one, Module.End.one_apply, ← neg_sub,
      neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

end Module

section Data

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_proofE (D : Data G) : D.U ⊓ centralizer (jOf D.T : Set G) ≤ proofE D := by
  rintro u ⟨huU, huc⟩
  exact uc22p22e_mem_omegaZJ'.2 ⟨P22x.uc22p22xf_UleT D huU, fun x hx => mem_centralizer_iff.1 huc x hx,
    (P22x.uc22p22xf_hel D).2 u huU⟩

theorem natDecAt_of_data (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {Umod : Type}
    [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ) {j : Fin m} {n : ℕ}
    (hj : IsL2Ev ↥(Nb j) n) : NatDecAt ρ (mbarImage D.M D.U (proofN D)) Nb j := by
  obtain ⟨hsum, hsh⟩ := h3 hH c m Nb hNb Umod e ρ hc
  exact ⟨hNb.1, hsum, P22x.natL2_of_shape148 ρ (Nb j) _ _ hj (hsh j)⟩

theorem proj_jOf_ne_bot (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hd : IsInternalDirect (mbarImage D.M D.U (proofN D)) Nb) {j : Fin m} (hj : Nb j ≠ ⊥) :
    proj hd j (mbarImage D.M D.U (jOf D.T)) ≠ ⊥ := by
  intro hbot
  set K : Subgroup (MBar D.M D.U) := (Pi.evalMonoidHom (fun k => ↥(Nb k)) j).ker.map (P22y.piMul hd)
  have hJK : mbarImage D.M D.U (jOf D.T) ≤ K := by
    intro a ha
    obtain ⟨f, rfl⟩ := exists_piMul hd (P22x.mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM) ha)
    have hfj : ((f j : ↥(Nb j)) : MBar D.M D.U) ∈ proj hd j (mbarImage D.M D.U (jOf D.T)) :=
      (mem_proj hd j).2 ⟨f, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hfj
    exact ⟨f, MonoidHom.mem_ker.2 (Subtype.ext hfj), rfl⟩
  have hKn : ∀ n ∈ mbarImage D.M D.U (proofN D), ∀ r ∈ K, n * r * n⁻¹ ∈ K := by
    rintro n hn _ ⟨f, hf, rfl⟩
    obtain ⟨g, rfl⟩ := exists_piMul hd hn
    refine ⟨g * f * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show g * f * g⁻¹ ∈ (Pi.evalMonoidHom (fun k => ↥(Nb k)) j).ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hf, mul_one, mul_inv_cancel]
  set R : Subgroup G := (K.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype
  have hTR : jOf D.T ≤ R := fun x hx => by
    have hxM : x ∈ D.M := D.sylowM.le (uc22p22e_jOf_le_self D.T hx)
    exact ⟨⟨x, hxM⟩, hJK ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩
  have hRn : ∀ n ∈ proofN D, ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
    rintro n hn _ ⟨z, hz, rfl⟩
    have hnM : n ∈ D.M := uc22p22e_jOf_le_self D.M hn
    refine ⟨⟨n, hnM⟩ * z * ⟨n, hnM⟩⁻¹, Subgroup.mem_comap.2 ?_, by simp⟩
    rw [map_mul, map_mul, map_inv]
    exact hKn _ ⟨⟨n, hnM⟩, hn, rfl⟩ _ hz
  have hNR := P22x.jOf_M_le_of_normalized D hTR hRn
  apply hj
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨z, hz, rfl⟩ := P22w.le_of_isInternalDirect hd j hb
  obtain ⟨w, hw, hwz⟩ := hNR hz
  have hwz' : w = z := Subtype.ext hwz
  subst hwz'
  obtain ⟨f, hf, hfw⟩ := hw
  have hf' : f j = 1 := MonoidHom.mem_ker.1 hf
  have h1 : P22y.piMul hd (Pi.mulSingle j ⟨_, hb⟩) = P22y.piMul hd f := by
    rw [P22y.piMul_mulSingle, hfw]
  have h2 := congrFun (P22y.piMul_injective hd h1) j
  rw [Pi.mulSingle_eq_same, hf'] at h2
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)

theorem card_proj_jOf (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hd : IsInternalDirect (mbarImage D.M D.U (proofN D)) Nb) {j : Fin m} (h6 : Nat.card ↥(Nb j) = 6) :
    Nat.card ↥(proj hd j (mbarImage D.M D.U (jOf D.T))) = 2 := by
  have hJ : IsPGroup 2 (mbarImage D.M D.U (jOf D.T)) :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  have hne : Nb j ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h6
    norm_num at h6
  exact card_proj_eq_two hd h6 hJ (proj_jOf_ne_bot D hd hne)

end Data

end P2251e

open P2251e

theorem uc22p2251e_exists_fixed {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G)
    (h3 : S22_3_3 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]
    (e : ↥D.U ≃* Multiplicative Umod) (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod)
    (hc : ConjModule D.M D.U e ρ) {j : Fin m} (hj : IsL2Ev ↥(Nb j) 1) :
    ∃ v ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb j), v ∉ natC ρ (mbarImage D.M D.U (proofN D)) ∧
      (∀ a ∈ mbarImage D.M D.U (jOf D.T), ρ a v = v) ∧ P22x.iota e v ∈ proofE D := by
  have d := natDecAt_of_data D Ch h3 hH c hNb e ρ hc hj
  have h6 : Nat.card ↥(Nb j) = 6 := by
    rw [P22x.card_of_isL2Ev hj]
    norm_num
  obtain ⟨v, hv, hvC, hfix⟩ := d.exists_fixed
    (P22x.mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)) (card_proj_jOf D d.direct h6)
  refine ⟨v, hv, hvC, hfix, inf_centralizer_le_proofE D ⟨P22x.iota_mem e v, ?_⟩⟩
  have hvfix : v ∈ fixSub ρ (mbarImage D.M D.U (jOf D.T)) := hfix
  rw [P22x.fixSub_mbarImage (P22x.uc22p22xf_hV D) e ρ hc
    ((uc22p22e_jOf_le_self D.T).trans D.sylowM.le)] at hvfix
  exact P22x.mem_bsub.1 hvfix

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
