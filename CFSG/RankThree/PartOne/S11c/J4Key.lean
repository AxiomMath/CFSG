module

public import CFSG.RankThree.PartOne.S11c.J4Dim
public import CFSG.RankThree.PartOne.S11c.J4MultFree
public import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialPlaneSelfDual

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra Module Subgroup
open CFSG.RankThree.GroupTheory.SteinbergBM
  (extraspecial_cyclotomic_minimal_module_abelian_plane_self_dual)
open scoped commutatorElement

section Orth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {G : Type*} [Group G]

omit [FiniteDimensional (ZMod 2) V] in
theorem separatingLeft_on_centralImage (ρ : Representation (ZMod 2) G V) (g : G)
    (hUW : IsCompl (centralFixed ρ g) (centralImage ρ g))
    {b : LinearMap.BilinForm (ZMod 2) V} (hb : b.Nondegenerate)
    (hbg : ∀ x y, b (ρ g x) (ρ g y) = b x y) :
    ∀ v ∈ centralImage ρ g, (∀ w ∈ centralImage ρ g, b v w = 0) → v = 0 := by
  intro v hv hvw
  have hvu : ∀ u ∈ centralFixed ρ g, b v u = 0 := by
    intro u hu
    obtain ⟨t, rfl⟩ := hv
    have hu' : ρ g u = u := by
      simpa [centralFixed, sub_eq_zero] using hu
    have h1 := hbg t u
    rw [hu'] at h1
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [LinearMap.BilinForm.sub_left, h1, sub_self]
  refine hb.1 v fun x => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hUW.codisjoint.eq_top ▸
    Submodule.mem_top (x := x))
  rw [map_add, hvu u hu, hvw w hw, add_zero]

end Orth

section Key

variable {J : Type*} [Group J] [Finite J] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

@[expose] noncomputable def repEquiv (ρ : Representation (ZMod 2) J V) : J →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom

omit [Finite J] [FiniteDimensional (ZMod 2) V] in
theorem repEquiv_apply (ρ : Representation (ZMod 2) J V) (g : J) (v : V) :
    repEquiv ρ g v = ρ g v := rfl

theorem centralizer_two_subgroup_eq_bot (ρ : Representation (ZMod 2) J V)
    (hV : finrank (ZMod 2) V = 112) {b : LinearMap.BilinForm (ZMod 2) V} (hb : b.Nondegenerate)
    (hbρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (Q : Subgroup J)
    (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11) {x y z : Q}
    (hz : z = ⁅x, y⁆) (hcard : Nat.card Q = 11 ^ 3) (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤)
    (hρz : ρ (z : J) ≠ 1)
    (hrank : ∀ g : J, g ≠ 1 → IsPGroup 2 (Subgroup.zpowers g) →
      finrank (ZMod 2) (centralFixed ρ g) ≤ 99)
    (E : Subgroup Q) (hE : Nat.card E = 11 ^ 2) (U : Subgroup J) (hU : IsPGroup 2 U)
    (hEU : ∀ e ∈ E, ∀ u ∈ U, (e : J) * u * (e : J)⁻¹ ∈ U) {β : Q} (hβE : β ∈ E) (hβ : β ≠ 1) :
    U ⊓ Subgroup.centralizer ({(β : J)} : Set J) = ⊥ := by
  classical
  set ρQ : Representation (ZMod 2) Q V := ρ.comp Q.subtype with hρQ
  have hρQapply : ∀ (q : Q) (v : V), ρQ q v = ρ (q : J) v := fun q v => rfl
  have hρz' : ρQ z ≠ 1 := hρz
  obtain ⟨hzc, hexp', hyx⟩ := extraspecial_eleven_facts hQ hexp hz
  have hz1 : z ≠ 1 := fun h => hρz' (by rw [h, map_one])
  have hzgen := center_eq_zpowers hQ hexp hz hz1
  have hU2 := finrank_centralFixed_center_eq_two hQ hexp hz ρQ hρz' hV
  have hVdim : finrank (ZMod 2) V = 11 * (11 - 1) + 2 := by omega
  have hUtriv := trivial_on_centralFixed hQ hexp hz ρQ hcard hgen hρz' hV
  obtain ⟨M, hM, hind, hsup, hMdim, hirr, hne, hdual⟩ :=
    extraspecial_cyclotomic_minimal_module_abelian_plane_self_dual (p := 11) (by norm_num)
      orderOf_two_zmod_eleven hQ hcard hexp hzgen ρQ hVdim hU2 E hE
  have hEcomm : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hE).is_comm.comm
      ⟨a, ha⟩ ⟨c, hc⟩)
  have hcommβ : ∀ e ∈ E, ρQ e * ρQ β = ρQ β * ρQ e := fun e he => by
    rw [← map_mul, ← map_mul, hEcomm e he β hβE]
  have hρQ_E : ∀ e ∈ E, ∀ v : V, ρQ e (ρQ β v) = ρQ β (ρQ e v) := fun e he v => by
    rw [← Module.End.mul_apply, hcommβ e he, Module.End.mul_apply]
  have hTpβ : ρQ β ^ 11 = 1 := by rw [← map_pow, hexp', map_one]
  have hUWβ := isCompl_centralFixed_centralImage (p := 11) (by norm_num) hTpβ
  set V' : Submodule (ZMod 2) V := centralImage ρQ β with hV'
  have hV'dim : 100 ≤ finrank (ZMod 2) V' :=
    finrank_centralImage_ge hQ hexp hz ρQ hcard hgen hρz' hV hβ
  have hV'inv : ∀ e ∈ E, ∀ v ∈ V', ρQ e v ∈ V' := fun e he v hv => by
    obtain ⟨t, rfl⟩ := hv
    refine ⟨ρQ e t, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [hρQ_E e he]
  have hbβ : ∀ x y, b (ρQ β x) (ρQ β y) = b x y := fun x y => hbρ (β : J) x y
  have hbV' := separatingLeft_on_centralImage ρQ β hUWβ hb hbβ
  have hMβ : ∀ i, ∀ m ∈ M i, (ρQ β - 1) m ∈ M i := fun i m hm => by
    simpa using sub_mem (hM i β hβE m hm) hm
  have hdich : ∀ i, (M i).map (ρQ β - 1) = ⊥ ∨ (M i).map (ρQ β - 1) = M i := by
    intro i
    refine hirr i _ ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact hMβ i m hm
    · rintro e he _ ⟨m, hm, rfl⟩
      refine ⟨ρQ e m, hM i e he m hm, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [hρQ_E e he]
  let ι := {i : Fin 11 // (M i).map (ρQ β - 1) ≠ ⊥}
  have hMι : ∀ i : ι, (M i.1).map (ρQ β - 1) = M i.1 := fun i =>
    (hdich i.1).resolve_left i.2
  have hMV' : ∀ i : ι, M i.1 ≤ V' := fun i m hm => by
    have : m ∈ (M i.1).map (ρQ β - 1) := by rw [hMι i]; exact hm
    obtain ⟨t, -, rfl⟩ := this
    exact ⟨t, rfl⟩
  have hsupι : ⨆ i : ι, M i.1 = V' := by
    have hUW := isCompl_centralFixed_centralImage (p := 11) (by norm_num)
      (show ρQ z ^ 11 = 1 by rw [← map_pow, hexp', map_one])
    have htop : centralFixed ρQ z ⊔ centralImage ρQ z = ⊤ := hUW.sup_eq_top
    have hV'map : V' = (centralFixed ρQ z ⊔ centralImage ρQ z).map (ρQ β - 1) := by
      rw [htop, hV', centralImage, Submodule.map_top]
    have hUmap : (centralFixed ρQ z).map (ρQ β - 1) = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_bot]
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hUtriv β u hu
    have hWmap : (centralImage ρQ z).map (ρQ β - 1) = ⨆ i, (M i).map (ρQ β - 1) := by
      rw [← hsup, Submodule.map_iSup]
    rw [hV'map, Submodule.map_sup, hUmap, bot_sup_eq, hWmap]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      calc M i.1 = (M i.1).map (ρQ β - 1) := (hMι i).symm
        _ ≤ ⨆ j, (M j).map (ρQ β - 1) := le_iSup (fun j => (M j).map (ρQ β - 1)) i.1
    · refine iSup_le fun i => ?_
      rcases hdich i with h | h
      · rw [h]; exact bot_le
      · have hne0 : (M i).map (ρQ β - 1) ≠ ⊥ := by
          rw [h]
          intro h0
          have := hMdim i
          rw [h0, finrank_bot] at this
          omega
        rw [h]
        exact le_iSup (fun j : ι => M j.1) ⟨i, hne0⟩
  let ρE : Representation (ZMod 2) E V := ρQ.comp E.subtype
  have hρE : ∀ (e : E) (v : V), ρE e v = ρ ((e : Q) : J) v := fun e v => rfl
  have hMinv : ∀ i : ι, ∀ (a : E), ∀ m ∈ M i.1, ρE a m ∈ M i.1 := fun i a m hm =>
    hM i.1 a a.2 m hm
  set K : Subgroup J := U ⊓ Subgroup.centralizer ({(β : J)} : Set J) with hK
  set R : Subgroup (V ≃ₗ[ZMod 2] V) := K.map (repEquiv ρ) with hR
  have hKcomm : ∀ g ∈ K, Commute g (β : J) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have hRb : ∀ r ∈ R, ∀ x y, b (r x) (r y) = b x y := by
    rintro _ ⟨g, hg, rfl⟩ x y
    exact hbρ g x y
  have hRp : IsPGroup 2 R := by
    intro r
    obtain ⟨g, hg, hgr⟩ := r.2
    obtain ⟨k, hk⟩ := hU ⟨g, hg.1⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    change (r : V ≃ₗ[ZMod 2] V) ^ 2 ^ k = 1
    rw [← hgr, ← map_pow, this, map_one]
  have hRV' : ∀ r ∈ R, ∀ v ∈ V', r v ∈ V' := by
    rintro _ ⟨g, hg, rfl⟩ v ⟨t, rfl⟩
    refine ⟨ρ g t, ?_⟩
    have hgβ : ρ g * ρ (β : J) = ρ (β : J) * ρ g := by
      rw [← map_mul, ← map_mul, (hKcomm g hg).eq]
    have h1 : ρ g (ρ (β : J) t) = ρ (β : J) (ρ g t) := by
      rw [← Module.End.mul_apply, hgβ, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, repEquiv_apply, hρQapply, h1]
  have hRA : ∀ (a : E), ∀ r ∈ R, ∃ r' ∈ R, ∀ v : V, r' v = ρE a (r (ρE a⁻¹ v)) := by
    rintro a _ ⟨g, hg, rfl⟩
    obtain ⟨a', ha'⟩ : ∃ a' : J, a' = (((a : E) : Q) : J) := ⟨_, rfl⟩
    have haβ : Commute a' (β : J) := by
      rw [ha']
      exact congrArg (fun q : Q => (q : J)) (hEcomm ((a : E) : Q) a.2 β hβE)
    have hmem : a' * g * a'⁻¹ ∈ K := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      · rw [ha']
        exact hEU ((a : E) : Q) a.2 g hg.1
      · exact (((haβ.mul_left (hKcomm g hg)).mul_left haβ.inv_left)).eq
    refine ⟨repEquiv ρ (a' * g * a'⁻¹), ⟨_, hmem, rfl⟩, fun v => ?_⟩
    have ha1 : ρE a = ρ a' := by
      ext w
      rw [hρE, ha']
    have ha2 : ρE a⁻¹ = ρ a'⁻¹ := by
      ext w
      rw [hρE]
      simp [ha']
    rw [repEquiv_apply, repEquiv_apply, ha1, ha2, map_mul, map_mul]
    rfl
  have hmain := multiplicity_free_trivial_on_subspace (b := b) ρE
    (fun a x y => hbρ (((a : E) : Q) : J) x y) V' (fun a v hv => hV'inv a a.2 v hv) hbV'
    (ι := ι) (fun i => M i.1) hMV' hMinv (hind.comp Subtype.val_injective) hsupι
    (fun i S hS hinv => hirr i.1 S hS (fun e he s hs => hinv ⟨e, he⟩ s hs))
    (fun i j hij φ h => hne i.1 j.1 (fun e => hij (Subtype.ext e)) φ
      (fun e he m => h ⟨e, he⟩ m))
    (fun i => by
      obtain ⟨B, h1, h2, h3⟩ := hdual i.1
      exact ⟨B, h1, h2, fun e x y => h3 e e.2 x y⟩)
    R hRb hRp hRV' hRA
  refine eq_bot_iff.mpr fun g hg => ?_
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hfix : ∀ v ∈ V', ρ g v = v := fun v hv => hmain (repEquiv ρ g) ⟨g, hg, rfl⟩ v hv
  have hle : V' ≤ centralFixed ρ g := fun v hv => by
    simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    exact hfix v hv
  have hpg : IsPGroup 2 (Subgroup.zpowers g) :=
    hU.to_le (Subgroup.zpowers_le.mpr hg.1)
  have h1 := hrank g hg1 hpg
  have h2 := Submodule.finrank_mono hle
  omega

end Key

end CFSG.RankThree.PartOne
