module

public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.SmithB42Alt6Norm
public import CFSG.Quasithin.Background.HB82Base

public section

namespace CFSG.Quasithin.H.LU

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.ZTrans CFSG.Quasithin.S143
  CFSG.Quasithin.B42Alt6
open scoped commutatorElement

theorem mulAut_comm_of_isCyclic {Z : Type*} [Group Z] [IsCyclic Z] (φ ψ : MulAut Z) :
    φ * ψ = ψ * φ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ.toMonoidHom
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic ψ.toMonoidHom
  refine MulEquiv.ext fun x => ?_
  have hm' : ∀ g, φ g = g ^ m := hm
  have hn' : ∀ g, ψ g = g ^ n := hn
  rw [MulAut.mul_apply, MulAut.mul_apply, hm', hn', hm', hn', ← zpow_mul, ← zpow_mul, mul_comm]

theorem le_center_of_normal_of_card_three {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    (Z : Subgroup Q) [Z.Normal] (hZ : Nat.card ↥Z = 3) : Z ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic ↥Z := isCyclic_of_prime_card hZ
  have hker : commutator Q ≤ (MulAut.conjNormal (H := Z)).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_comm_of_isCyclic _ _
  rw [hQ] at hker
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro q
  have h1 : MulAut.conjNormal (H := Z) q = 1 := hker (Subgroup.mem_top q)
  have h2 := congrArg (fun φ : MulAut ↥Z => ((φ ⟨z, hz⟩ : ↥Z) : Q)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc q * z = q * z * q⁻¹ * q := by group
    _ = z * q := by rw [h2]

theorem card_eq_map_mul_inf {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G) :
    Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.card_mul_index (f.domRestrict H).ker
  rw [Subgroup.index_ker] at h
  have h1 : (f.domRestrict H).range = H.map f := by
    ext b
    simp [Subgroup.mem_map]
  have h3 : Nat.card ↥(f.domRestrict H).ker = Nat.card ↥(H ⊓ f.ker) := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h3] at h
  rw [← h, mul_comm]

theorem isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem isQuasisimple_quot_pCore_of_three {G S : Type*} [Group G] [Group S] [Finite G]
    (hG : commutator G = ⊤) (f : G →* S) (hf : Function.Surjective f) [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (K : Subgroup G) [K.Normal] (hK : IsPGroup 2 ↥K)
    (hKf : K ≤ f.ker) (hcard : Nat.card ↥f.ker = 3 * Nat.card ↥K) :
    CFSG.IsQuasisimple (G ⧸ CFSG.pCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective f hf
  have hle : CFSG.pCore 2 G ≤ f.ker := by
    have hN : ((CFSG.pCore 2 G).map f).Normal := CFSG.pCore_normal.map f hf
    rcases hN.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hp : IsPGroup 2 S := by
        have h1 : IsPGroup 2 ((CFSG.pCore 2 G).map f) := CFSG.pCore_isPGroup.map f
        rw [h] at h1
        exact h1.of_equiv Subgroup.topEquiv
      have : Nontrivial S := ⟨⟨a * b, b * a, hab⟩⟩
      have hZ : Subgroup.center S ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot _).1 hp.center_nontrivial
      rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h2 | h2
      · exact hZ h2
      · exact hab ((Subgroup.mem_center_iff.1 (h2 ▸ Subgroup.mem_top b)) a)
  have hKle : K ≤ CFSG.pCore 2 G := le_sSup ⟨inferInstance, hK⟩
  have hpk : CFSG.pCore 2 G = K := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 (CFSG.pCore_isPGroup (p := 2) (G := G))
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 hK
    have h1 : Nat.card ↥(CFSG.pCore 2 G) ∣ Nat.card ↥f.ker := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [ha, hcard, hb] at h1
    have h2 : 2 ^ a ∣ 2 ^ b :=
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left _ (by norm_num)) h1)
    have h3 : Nat.card ↥(CFSG.pCore 2 G) ≤ Nat.card ↥K := by
      rw [ha, hb]
      exact Nat.le_of_dvd (by positivity) h2
    exact (Subgroup.eq_of_le_of_card_ge hKle h3).symm
  set Q := G ⧸ K
  have hQ : commutator Q = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K),
      ← Subgroup.map_commutator, ← commutator_def, hG]
  set f' : Q →* S := QuotientGroup.lift K f hKf
  have hf' : Function.Surjective f' := by
    intro s
    obtain ⟨g, rfl⟩ := hf s
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hker : f'.ker = f.ker.map (QuotientGroup.mk' K) := QuotientGroup.ker_lift K f hKf
  have hZ3 : Nat.card ↥f'.ker = 3 := by
    have h1 := card_eq_map_mul_inf (QuotientGroup.mk' K) f.ker
    rw [QuotientGroup.ker_mk', inf_eq_right.2 hKf, hcard, ← hker] at h1
    have hK0 : 0 < Nat.card ↥K := Nat.card_pos
    nlinarith
  have hZc : f'.ker ≤ Subgroup.center Q := le_center_of_normal_of_card_three hQ f'.ker hZ3
  have hcZ : Subgroup.center Q ≤ f'.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hfz : f' z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hf' y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) x]
    have hS : Subgroup.center S = ⊥ := by
      obtain ⟨a, b, hab⟩ := hnc
      rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
      · exact h
      · exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
    rw [hS] at hfz
    exact hfz
  have hcen : Subgroup.center Q = f'.ker := le_antisymm hcZ hZc
  let e₁ : Q ⧸ Subgroup.center Q ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective f' hf')
  have hQq : CFSG.IsQuasisimple Q := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨⟨hQ⟩, e₁.isSimpleGroup, e₁.symm a, e₁.symm b, fun h => hab (e₁.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  let e₂ : G ⧸ CFSG.pCore 2 G ≃* Q := QuotientGroup.quotientMulEquivOfEq hpk
  exact isQuasisimple_of_equiv e₂.symm hQq

theorem isQuasisimple_quot_of_map {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    {P : Subgroup (MulAut V)} {P' : Subgroup (MulAut W)} (hP : P.map (congrHom e) = P')
    (h : CFSG.IsQuasisimple (↥P' ⧸ CFSG.pCore 2 ↥P')) :
    CFSG.IsQuasisimple (↥P ⧸ CFSG.pCore 2 ↥P) := by
  let φ : ↥P ≃* ↥P' :=
    (P.equivMapOfInjective _ (congrHom_injective e)).trans (MulEquiv.subgroupCongr hP)
  have hc := CFSG.pCore_map_iso 2 φ
  exact isQuasisimple_of_equiv (QuotientGroup.congr _ _ φ hc).symm h

theorem commutator_eq_top_of_perfect {G : Type*} [Group G] {P : Subgroup G} (h : ⁅P, P⁆ = P) :
    commutator ↥P = ⊤ := by
  apply Subgroup.map_injective P.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

theorem a6_noncomm : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := by
  refine ⟨⟨c[0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
    ⟨c[0, 1, 3], by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, fun h => ?_⟩
  have h1 := congrArg Subtype.val h
  revert h1
  decide +kernel

theorem lu_A6_of_std {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W] (e : V ≃* W)
    {H X : Subgroup (MulAut V)} {P' : Subgroup (MulAut W)} {U' : Subgroup W}
    (hP : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = P')
    (hU : fixV (X.map (congrHom e)) = U') (Θ : ↥U' ≃* N6)
    (hρ : (alternatingGroup (Fin 6)).map (rhoOf Θ) = autSub P' U') (hperf : ⁅P', P'⁆ = P')
    {K : Subgroup (MulAut W)} (hKP : K ≤ P') (hKn : P' ≤ Subgroup.normalizer (K : Set (MulAut W)))
    (hK2 : IsPGroup 2 ↥K) (hKC : K ≤ centSub U')
    (hCK : Nat.card ↥(P' ⊓ centSub U') = 3 * Nat.card ↥K) :
    CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      AlternatingNatural (V := ↥(fixV X)) (autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X))
        ⊤ ⊥ 6 := by
  have : Finite (MulAut W) := finite_mulAut_z (V := W)
  set P := perfectCore (H ⊓ stabSub (fixV X))
  have hUe : ∀ v, v ∈ fixV X ↔ e v ∈ U' := fun v => by
    rw [← hU, fixV_map_congrHom]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hPU' : P' ≤ stabSub U' := by
    rw [← hP, ← hU, ← perfectCore_map_congrHom e, map_inf_stab_congrHom]
    exact (perfectCore_le _).trans inf_le_right
  let M : N6Model (autSub P' U') := ⟨Θ, rhoOf Θ, rhoOf_injective Θ, rhoOf_apply Θ, hρ⟩
  refine ⟨?_, realizes_autSub_of_map (FFModel.altDn 6) e P hUe (hP ▸ M.alternatingNatural)⟩
  refine isQuasisimple_quot_of_map e hP ?_
  let ι : ↥(alternatingGroup (Fin 6)) ≃* ↥(autSub P' U') :=
    ((alternatingGroup (Fin 6)).equivMapOfInjective _ (rhoOf_injective Θ)).trans
      (MulEquiv.subgroupCongr hρ)
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(autSub P' U') := ι.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(autSub P' U'), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := a6_noncomm
    exact ⟨ι a, ι b, fun h => hab (ι.injective (by rw [map_mul, map_mul, h]))⟩
  have hKn' : (K.subgroupOf P').Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2 hKn
  have hK2' : IsPGroup 2 ↥(K.subgroupOf P') :=
    hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKP).symm
  have hker : (resP hPU').ker = (P' ⊓ centSub U').subgroupOf P' := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨p.2, fun u hu => ?_⟩
      have h1 := congrArg (fun φ : ↥(autSub P' U') => (((φ : MulAut ↥U') ⟨u, hu⟩ : ↥U') : W)) h
      exact h1
    · rintro ⟨-, hc⟩
      refine Subtype.ext (MulEquiv.ext fun u => Subtype.ext ?_)
      exact hc u u.2
  refine isQuasisimple_quot_pCore_of_three (commutator_eq_top_of_perfect hperf) (resP hPU')
    (resP_surjective hPU') hnc (K.subgroupOf P') hK2' (fun k hk => ?_) ?_
  · rw [hker, Subgroup.mem_subgroupOf]
    exact ⟨k.2, hKC (Subgroup.mem_subgroupOf.1 hk)⟩
  · rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hCK,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv]

theorem lu_L32_of_std {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W] (e : V ≃* W)
    {H X : Subgroup (MulAut V)} {P' : Subgroup (MulAut W)} {U' : Subgroup W}
    (hP : (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) = P')
    (hU : fixV (X.map (congrHom e)) = U') (htop : autSub P' U' = ⊤)
    (hS : IsSimpleGroup ↥(autSub P' U')) (hnc : ∃ a b : ↥(autSub P' U'), a * b ≠ b * a)
    (hC : IsPGroup 2 ↥(P' ⊓ centSub U')) :
    CFSG.IsQuasisimple (↥(perfectCore (H ⊓ stabSub (fixV X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabSub (fixV X)))) ∧
      autSub (perfectCore (H ⊓ stabSub (fixV X))) (fixV X) = ⊤ := by
  have : Finite (MulAut W) := finite_mulAut_z (V := W)
  set P := perfectCore (H ⊓ stabSub (fixV X))
  have hUe : ∀ v, v ∈ fixV X ↔ e v ∈ U' := fun v => by
    rw [← hU, fixV_map_congrHom]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hPU' : P' ≤ stabSub U' := by
    rw [← hP, ← hU, ← perfectCore_map_congrHom e, map_inf_stab_congrHom]
    exact (perfectCore_le _).trans inf_le_right
  subst hP
  refine ⟨isQuasisimple_quot_of_map e rfl ?_, autSub_eq_top_of_map e P hUe htop⟩
  exact isQuasisimple_of_autSub hPU' hnc hC

end CFSG.Quasithin.H.LU
