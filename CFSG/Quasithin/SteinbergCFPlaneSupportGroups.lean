module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin.SteinbergCF

open Module CFSG.QuasithinUnique.Setup.Offender

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ι : Type*}

@[expose] def submoduleStab (U : Submodule k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {g | U.map (g : V →ₗ[k] V) = U}
  one_mem' := by
    show U.map ((1 : V ≃ₗ[k] V) : V →ₗ[k] V) = U
    exact Submodule.map_id U
  mul_mem' := by
    intro g h hg hh
    show U.map ((g * h : V ≃ₗ[k] V) : V →ₗ[k] V) = U
    have e : ((g * h : V ≃ₗ[k] V) : V →ₗ[k] V) = (g : V →ₗ[k] V) ∘ₗ (h : V →ₗ[k] V) := rfl
    rw [e, Submodule.map_comp, show U.map (h : V →ₗ[k] V) = U from hh, hg]
  inv_mem' := by
    intro g hg
    have hg' : U.map (g : V →ₗ[k] V) = U := hg
    show U.map ((g⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) = U
    conv_lhs => rw [← hg']
    rw [← Submodule.map_comp]
    have e : ((g⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ (g : V →ₗ[k] V) = LinearMap.id := by
      ext v
      exact g.symm_apply_apply v
    rw [e, Submodule.map_id]

theorem mem_submoduleStab {U : Submodule k V} {g : V ≃ₗ[k] V} :
    g ∈ submoduleStab U ↔ U.map (g : V →ₗ[k] V) = U := Iff.rfl

theorem apply_mem_of_mem_submoduleStab {U : Submodule k V} {g : V ≃ₗ[k] V}
    (hg : g ∈ submoduleStab U) {u : V} (hu : u ∈ U) : g u ∈ U := by
  rw [← mem_submoduleStab.mp hg]
  exact ⟨u, hu, rfl⟩

@[expose] def planeSupport (I : ι → Submodule k V) (V₀ : Submodule k V) (i : ι) :
    Subgroup (V ≃ₗ[k] V) where
  carrier := {g | (I i).map (g : V →ₗ[k] V) = I i ∧ (∀ v ∈ V₀, g v = v) ∧
    ∀ j, j ≠ i → ∀ v ∈ I j, g v = v}
  one_mem' := ⟨(submoduleStab (I i)).one_mem, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨(submoduleStab (I i)).mul_mem hg1 hh1, fun v hv => ?_, fun j hj v hv => ?_⟩
    · rw [LinearEquiv.mul_apply, hh2 v hv, hg2 v hv]
    · rw [LinearEquiv.mul_apply, hh3 j hj v hv, hg3 j hj v hv]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    refine ⟨(submoduleStab (I i)).inv_mem hg1, fun v hv => ?_, fun j hj v hv => ?_⟩
    · exact (LinearEquiv.symm_apply_eq _).mpr (hg2 v hv).symm
    · exact (LinearEquiv.symm_apply_eq _).mpr (hg3 j hj v hv).symm

@[expose] def planeComplement (I : ι → Submodule k V) (V₀ : Submodule k V) (i : ι) :
    Submodule k V :=
  V₀ ⊔ ⨆ (j) (_ : j ≠ i), I j

variable {I : ι → Submodule k V} {V₀ : Submodule k V}

theorem fix_planeComplement {i : ι} {g : V ≃ₗ[k] V} (hg : g ∈ planeSupport I V₀ i) {u : V}
    (hu : u ∈ planeComplement I V₀ i) : g u = u := by
  have hle : planeComplement I V₀ i ≤ LinearMap.eqLocus (g : V →ₗ[k] V) LinearMap.id := by
    refine sup_le (fun v hv => hg.2.1 v hv) (iSup₂_le fun j hj v hv => hg.2.2 j hj v hv)
  exact hle hu

theorem linearEquiv_ext_of_planes (hspan : (⨆ j, I j) ⊔ V₀ = ⊤) {f g : V ≃ₗ[k] V}
    (h0 : ∀ v ∈ V₀, f v = g v) (hI : ∀ j, ∀ v ∈ I j, f v = g v) : f = g := by
  have hle : (⨆ j, I j) ⊔ V₀ ≤ LinearMap.eqLocus (f : V →ₗ[k] V) (g : V →ₗ[k] V) :=
    sup_le (iSup_le fun j v hv => hI j v hv) (fun v hv => h0 v hv)
  rw [hspan] at hle
  exact LinearEquiv.ext fun v => hle Submodule.mem_top

theorem eq_one_of_mem_planeSupport (hspan : (⨆ j, I j) ⊔ V₀ = ⊤) {i : ι} {g : V ≃ₗ[k] V}
    (hg : g ∈ planeSupport I V₀ i) (hfix : ∀ v ∈ I i, g v = v) : g = 1 := by
  refine linearEquiv_ext_of_planes hspan (fun v hv => hg.2.1 v hv) fun j v hv => ?_
  by_cases hj : j = i
  · subst hj
    exact hfix v hv
  · exact hg.2.2 j hj v hv

theorem planeSupport_commute (hspan : (⨆ j, I j) ⊔ V₀ = ⊤) {i j : ι} (hij : i ≠ j)
    {s t : V ≃ₗ[k] V} (hs : s ∈ planeSupport I V₀ i) (ht : t ∈ planeSupport I V₀ j) :
    s * t = t * s := by
  refine linearEquiv_ext_of_planes hspan (fun v hv => ?_) fun l v hv => ?_
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht.2.1 v hv, hs.2.1 v hv, ht.2.1 v hv]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    by_cases hli : l = i
    · subst hli
      have h1 : s v ∈ I l := apply_mem_of_mem_submoduleStab hs.1 hv
      rw [ht.2.2 l hij v hv, ht.2.2 l hij (s v) h1]
    · by_cases hlj : l = j
      · subst hlj
        have h1 : t v ∈ I l := apply_mem_of_mem_submoduleStab ht.1 hv
        rw [hs.2.2 l (Ne.symm hij) (t v) h1, hs.2.2 l (Ne.symm hij) v hv]
      · rw [ht.2.2 l hlj v hv, hs.2.2 l hli v hv, ht.2.2 l hlj v hv]

theorem iSupIndep_planeSupport (hspan : (⨆ j, I j) ⊔ V₀ = ⊤) :
    iSupIndep (planeSupport I V₀) := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  rintro g ⟨hg, hg'⟩
  have hle : (⨆ (j) (_ : j ≠ i), planeSupport I V₀ j) ≤
      centSub (MonoidHom.id (V ≃ₗ[k] V)) (I i) :=
    iSup₂_le fun j hj h hh v hv => hh.2.2 i (Ne.symm hj) v hv
  exact eq_one_of_mem_planeSupport hspan hg fun v hv => hle hg' v hv

theorem isCompl_plane_planeComplement (hI : iSupIndep I) (hc : IsCompl (⨆ j, I j) V₀)
    (i : ι) : IsCompl (I i) (planeComplement I V₀ i) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxU
    obtain ⟨v₀, hv₀, y, hy, rfl⟩ := Submodule.mem_sup.mp hxU
    have hy' : y ∈ ⨆ j, I j :=
      (iSup₂_le fun j _ => le_iSup I j : (⨆ (j) (_ : j ≠ i), I j) ≤ ⨆ j, I j) hy
    have hx' : v₀ + y ∈ ⨆ j, I j := le_iSup I i hx
    have hv₀' : v₀ ∈ ⨆ j, I j := by
      have := (⨆ j, I j).sub_mem hx' hy'
      rwa [add_sub_cancel_right] at this
    have h0 : v₀ = 0 := (Submodule.disjoint_def.mp hc.1) v₀ hv₀' hv₀
    rw [h0, zero_add] at hx ⊢
    exact (Submodule.disjoint_def.mp (hI i)) y hx hy
  · rw [codisjoint_iff, eq_top_iff, ← hc.2.eq_top]
    show (⨆ j, I j) ⊔ V₀ ≤ I i ⊔ (V₀ ⊔ ⨆ (j) (_ : j ≠ i), I j)
    have h1 : V₀ ≤ I i ⊔ (V₀ ⊔ ⨆ (j) (_ : j ≠ i), I j) :=
      le_sup_left.trans le_sup_right
    have h2 : (⨆ (j) (_ : j ≠ i), I j) ≤ I i ⊔ (V₀ ⊔ ⨆ (j) (_ : j ≠ i), I j) :=
      le_sup_right.trans le_sup_right
    refine sup_le (iSup_le fun j => ?_) h1
    by_cases hj : j = i
    · subst hj
      exact le_sup_left
    · exact (le_iSup₂_of_le (f := fun (j : ι) (_ : j ≠ i) => I j) j hj le_rfl).trans h2

theorem finrank_inf_ker_sub_one_eq_one [CharP k 2] {p : Submodule k V} [FiniteDimensional k p]
    (hp : finrank k p = 2) {a : V →ₗ[k] V} (ha : a * a = 1) (hap : ∀ v ∈ p, a v ∈ p)
    (hne : ∃ v ∈ p, a v ≠ v) : finrank k ↥(p ⊓ LinearMap.ker (a - 1)) = 1 := by
  set f : V →ₗ[k] V := a - 1 with hf
  have hfp : ∀ v ∈ p, f v ∈ p := fun v hv => p.sub_mem (hap v hv) hv
  set g : p →ₗ[k] p := f.restrict hfp with hg
  have hgg : g ∘ₗ g = 0 := by
    ext v
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    have haa : a (a v) = v := by
      have := congrArg (fun m : V →ₗ[k] V => m v) ha
      simpa using this
    simp only [LinearMap.comp_apply, hg, LinearMap.restrict_apply, LinearMap.zero_apply,
      Submodule.coe_zero, hf, LinearMap.sub_apply, Module.End.one_apply, map_sub, haa]
    have : (v : V) - a v - (a v - v) = (2 : k) • ((v : V) - a v) := by
      rw [two_smul]
      abel
    rw [this, h2, zero_smul]
  have hg0 : g ≠ 0 := by
    obtain ⟨v, hv, hav⟩ := hne
    intro h
    apply hav
    have := congrArg (fun m : p →ₗ[k] p => ((m ⟨v, hv⟩ : p) : V)) h
    simp only [hg, LinearMap.restrict_apply, LinearMap.zero_apply, Submodule.coe_zero, hf,
      LinearMap.sub_apply, Module.End.one_apply] at this
    exact sub_eq_zero.mp this
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [hp] at hrk
  have hle : LinearMap.range g ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.mpr hgg
  have h1 : finrank k (LinearMap.range g) ≤ finrank k (LinearMap.ker g) :=
    Submodule.finrank_mono hle
  have h2 : finrank k (LinearMap.range g) ≠ 0 := by
    intro h
    apply hg0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    exact h
  have hker : finrank k (LinearMap.ker g) = 1 := by omega
  have hmap : (LinearMap.ker g).map p.subtype = p ⊓ LinearMap.ker f := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hw)
      simpa [hg] using this
    · rintro ⟨hvp, hvf⟩
      refine ⟨⟨v, hvp⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      apply Subtype.ext
      simpa [hg] using LinearMap.mem_ker.mp hvf
  rw [← hmap, Submodule.finrank_map_subtype_eq]
  exact hker

theorem fixGL_sup (B C : Subgroup (V ≃ₗ[k] V)) : fixGL (B ⊔ C) = fixGL B ⊓ fixGL C := by
  apply le_antisymm
  · exact le_inf (fixSub_anti _ le_sup_left) (fixSub_anti _ le_sup_right)
  · intro v hv
    have hle : B ⊔ C ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) (fixGL B ⊓ fixGL C) :=
      sup_le (fun b hb u hu => hu.1 b hb) (fun c hc u hu => hu.2 c hc)
    exact fun g hg => hle hg v hv

theorem card_sup_and_card_fixGL_sup [CharP k 2] [FiniteDimensional k V] [Finite V]
    (hI : iSupIndep I) (hc : IsCompl (⨆ j, I j) V₀) {i : ι} (hdim : finrank k (I i) = 2)
    (hk : Nat.card k = 2) {A E₀ : Subgroup (V ≃ₗ[k] V)} (hAS : A ≤ planeSupport I V₀ i)
    (hA2 : Nat.card A = 2) (hE₀I : ∀ e ∈ E₀, ∀ v ∈ I i, e v = v)
    (hcomm : ∀ a ∈ A, ∀ e ∈ E₀, a * e = e * a) :
    Nat.card ↥(A ⊔ E₀) = 2 * Nat.card E₀ ∧
      Nat.card (fixGL (A ⊔ E₀)) * 2 = Nat.card (fixGL E₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    have hbot : A = ⊥ := eq_bot_iff.mpr fun b hb => by
      by_contra hb1
      exact h ⟨b, hb, hb1⟩
    rw [hbot, Subgroup.card_bot] at hA2
    exact absurd hA2 (by norm_num)
  have ha2 : a ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := ⟨a, haA⟩)
    rw [hA2] at this
    exact congrArg Subtype.val this
  have hAz : A = Subgroup.zpowers a := by
    have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA)
    rw [Nat.card_zpowers, hord, hA2]
  have hinf : A ⊓ E₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hbA, hbE⟩
    exact eq_one_of_mem_planeSupport hspan (hAS hbA) (hE₀I b hbE)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A E₀ hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, hA2] at hcard
  refine ⟨hcard, ?_⟩
  set X := fixGL E₀ with hX
  set U := planeComplement I V₀ i with hU
  have hIX : I i ≤ X := fun v hv e he => hE₀I e he v hv
  have hcompl := isCompl_plane_planeComplement hI hc i
  have hXdec : I i ⊔ U ⊓ X = X := by
    rw [← sup_inf_assoc_of_le U hIX, codisjoint_iff.mp hcompl.2, top_inf_eq]
  have hfixA : ∀ v, v ∈ fixGL A ↔ a v = v := by
    intro v
    constructor
    · intro hv
      exact hv a haA
    · intro hv b hb
      rw [hAz] at hb
      have hst : a ∈ MulAction.stabilizer (V ≃ₗ[k] V) v :=
        MulAction.mem_stabilizer_iff.mpr (by rw [LinearEquiv.smul_def]; exact hv)
      have := MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hst) hb)
      rwa [LinearEquiv.smul_def] at this
  have hfixeq : fixGL (A ⊔ E₀) = (I i ⊓ fixGL A) ⊔ U ⊓ X := by
    rw [fixGL_sup]
    apply le_antisymm
    · rintro v ⟨hvA, hvX⟩
      have hv : v ∈ I i ⊔ U ⊓ X := hXdec.symm ▸ hvX
      obtain ⟨x, hx, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      have hau : a u = u := fix_planeComplement (hAS haA) hu.1
      have hax : a x = x := by
        have := (hfixA _).mp hvA
        rw [map_add, hau] at this
        exact add_right_cancel this
      exact Submodule.add_mem_sup ⟨hx, (hfixA x).mpr hax⟩ hu
    · refine sup_le (fun v hv => ⟨hv.2, hIX hv.1⟩) (fun v hv => ⟨?_, hv.2⟩)
      exact (hfixA v).mpr (fix_planeComplement (hAS haA) hv.1)
  have hd1 : I i ⊓ (U ⊓ X) = ⊥ := disjoint_iff.mp (hcompl.1.mono_right inf_le_left)
  have hd2 : (I i ⊓ fixGL A) ⊓ (U ⊓ X) = ⊥ :=
    disjoint_iff.mp ((hcompl.1.mono_left inf_le_left).mono_right inf_le_left)
  have hX1 := Submodule.finrank_sup_add_finrank_inf_eq (I i) (U ⊓ X)
  rw [hXdec, hd1, finrank_bot, add_zero, hdim] at hX1
  have hY1 := Submodule.finrank_sup_add_finrank_inf_eq (I i ⊓ fixGL A) (U ⊓ X)
  rw [← hfixeq, hd2, finrank_bot, add_zero] at hY1
  have hker : fixGL A = LinearMap.ker ((a : V →ₗ[k] V) - 1) := by
    ext v
    rw [hfixA, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rfl
  have hline : finrank k ↥(I i ⊓ fixGL A) = 1 := by
    rw [hker]
    refine finrank_inf_ker_sub_one_eq_one hdim ?_ (fun v hv =>
      apply_mem_of_mem_submoduleStab (hAS haA).1 hv) ?_
    · refine LinearMap.ext fun v => ?_
      have h := congrArg (fun g : V ≃ₗ[k] V => g v) ha2
      simpa [pow_two] using h
    · by_contra h
      apply ha1
      refine eq_one_of_mem_planeSupport hspan (hAS haA) fun v hv => ?_
      by_contra hv'
      exact h ⟨v, hv, hv'⟩
  rw [hline] at hY1
  rw [Module.natCard_eq_pow_finrank (K := k) (V := ↥(fixGL (A ⊔ E₀))),
    Module.natCard_eq_pow_finrank (K := k) (V := ↥X), hk, hY1, hX1]
  ring

theorem card_and_weight_coordProduct [CharP k 2] [FiniteDimensional k V] [Finite V]
    [DecidableEq ι] (hI : iSupIndep I) (hc : IsCompl (⨆ j, I j) V₀)
    (hdim : ∀ i, finrank k (I i) = 2) (hk : Nat.card k = 2) (a : ι → Subgroup (V ≃ₗ[k] V))
    (J : Finset ι) (ha : ∀ i ∈ J, a i ≤ planeSupport I V₀ i ∧ Nat.card (a i) = 2) :
    Nat.card ↥(⨆ i ∈ J, a i) = 2 ^ J.card ∧
      weight (MonoidHom.id (V ≃ₗ[k] V)) (⨆ i ∈ J, a i) = Nat.card V := by
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot, Subgroup.card_bot,
      Finset.card_empty, pow_zero, true_and]
    unfold weight
    rw [Subgroup.card_bot, one_mul]
    have htop : fixSub (MonoidHom.id (V ≃ₗ[k] V)) ⊥ = ⊤ := by
      ext v
      simp only [mem_fixSub, Subgroup.mem_bot, Submodule.mem_top, iff_true]
      rintro b rfl
      rfl
    rw [htop]
    exact Nat.card_congr (Equiv.Set.univ V)
  | insert i J hiJ ih =>
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨hai, hai2⟩ := ha i (Finset.mem_insert_self i J)
    have hne : ∀ j ∈ J, j ≠ i := fun j hj h => hiJ (h ▸ hj)
    rw [Finset.iSup_insert]
    have hE₀I : ∀ e ∈ ⨆ j ∈ J, a j, ∀ v ∈ I i, e v = v := by
      have hle : (⨆ j ∈ J, a j) ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) (I i) :=
        iSup₂_le fun j hj g hg v hv =>
          ((ha j (Finset.mem_insert_of_mem hj)).1 hg).2.2 i (Ne.symm (hne j hj)) v hv
      exact fun e he v hv => hle he v hv
    have hcomm : ∀ x ∈ a i, ∀ e ∈ ⨆ j ∈ J, a j, x * e = e * x := by
      have hle : (⨆ j ∈ J, a j) ≤ Subgroup.centralizer (a i : Set (V ≃ₗ[k] V)) :=
        iSup₂_le fun j hj g hg => Subgroup.mem_centralizer_iff.mpr fun x hx =>
          planeSupport_commute hspan (Ne.symm (hne j hj)) (hai hx)
            ((ha j (Finset.mem_insert_of_mem hj)).1 hg)
      exact fun x hx e he => Subgroup.mem_centralizer_iff.mp (hle he) x hx
    obtain ⟨h1, h2⟩ := card_sup_and_card_fixGL_sup hI hc (hdim i) hk hai hai2 hE₀I hcomm
    refine ⟨?_, ?_⟩
    · rw [h1, ih'.1, Finset.card_insert_of_notMem hiJ, pow_succ]
      ring
    · have hw := ih'.2
      unfold weight at hw ⊢
      rw [h1, ← hw, ← h2]
      ring

theorem isElementaryAbelian_coordProduct (hspan : (⨆ j, I j) ⊔ V₀ = ⊤)
    (a : ι → Subgroup (V ≃ₗ[k] V)) (J : Finset ι)
    (ha : ∀ i ∈ J, a i ≤ planeSupport I V₀ i ∧ Nat.card (a i) = 2) :
    IsElementaryAbelian 2 ↥(⨆ i ∈ J, a i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : ∀ i ∈ J, a i ≤ Subgroup.centralizer (a i : Set (V ≃ₗ[k] V)) := fun i hi => by
    have : IsCyclic ↥(a i) := isCyclic_of_prime_card (ha i hi).2
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
  have hcomm : (⨆ i ∈ J, a i) ≤ Subgroup.centralizer ((⨆ i ∈ J, a i : Subgroup _) : Set _) := by
    refine iSup₂_le fun i hi => Subgroup.le_centralizer_iff.mpr (iSup₂_le fun j hj => ?_)
    by_cases hij : j = i
    · subst hij
      exact hab j hj
    · intro g hg
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        planeSupport_commute hspan (Ne.symm hij) ((ha i hi).1 hx) ((ha j hj).1 hg)
  have hc : IsMulCommutative ↥(⨆ i ∈ J, a i) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp hcomm
  have hsq : ∀ x ∈ (⨆ i ∈ J, a i), x ^ 2 = 1 := by
    intro x hx
    rw [iSup_subtype'] at hx
    have h := Subgroup.iSup_induction (fun i : ↥J => a i)
      (C := fun x => x ∈ (⨆ i ∈ J, a i) ∧ x ^ 2 = 1) hx
      (fun i y hy => ⟨le_iSup₂_of_le (f := fun j (_ : j ∈ J) => a j) i i.2 le_rfl hy, by
        have := pow_card_eq_one' (G := ↥(a i)) (x := ⟨y, hy⟩)
        rw [(ha i i.2).2] at this
        exact congrArg Subtype.val this⟩) ⟨one_mem _, one_pow 2⟩
      (fun y z hy hz => ⟨mul_mem hy.1 hz.1, by
        have hyz : Commute y z :=
          Subgroup.mem_centralizer_iff.mp (hcomm hz.1) y hy.1
        rw [hyz.mul_pow, hy.2, hz.2, one_mul]⟩)
    exact h.2
  exact
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hsq x x.2) }

end CFSG.Quasithin.SteinbergCF
