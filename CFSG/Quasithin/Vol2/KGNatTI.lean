module

public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conjAct_coe (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

theorem exists_coord_autOn {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {D : FFModel} {K M : Type} [Field K]
    [AddCommGroup M] [Module K M] (LM : LinModel D K M) {Z : Subgroup ↥V}
    {π : D.Gam →* ↥(autOn L V)} (h : D.RealizesVia (V := ↥V) (autOn L V) ⊤ Z π) :
    ∃ f : ↥V → M, (∀ u u' : ↥V, f (u * u') = f u + f u') ∧ (∀ u : ↥V, f u = 0 ↔ u ∈ Z) ∧
      Function.Surjective f ∧
      ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v) := by
  obtain ⟨f, hmul, hker, hsurj, hact⟩ := exists_coord LM h
  refine ⟨f, fun u u' => hmul u trivial u' trivial, fun u => hker u trivial,
    fun m => (hsurj m).imp fun u hu => hu.2, fun l hl => ?_⟩
  obtain ⟨γ, hγ⟩ := h.1 ⟨conjAct V ⟨l, hLV hl⟩,
    Subgroup.mem_map.2 ⟨⟨l, hLV hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩⟩
  refine ⟨LM.lin γ, fun v w hw => ?_⟩
  have hw' : w = ((π γ : ↥(autOn L V)) : MulAut ↥V) v := by
    rw [hγ]
    apply Subtype.ext
    rw [hw]
    exact (conjAct_coe V ⟨l, hLV hl⟩ v).symm
  rw [hw', hact γ v trivial]

section Scalar

variable {V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M] [Module K M] {f : ↥V → M}

theorem map_one_of_add (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') : f 1 = 0 := by
  have h := hmul 1 1
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)

@[expose] noncomputable def scalarHom (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u')
    (hbij : Function.Bijective f) (c : K) : ↥V →* ↥V where
  toFun v := (Equiv.ofBijective f hbij).symm (c • f v)
  map_one' := by
    rw [map_one_of_add hmul, smul_zero, Equiv.symm_apply_eq]
    exact (map_one_of_add hmul).symm
  map_mul' u u' := by
    rw [Equiv.symm_apply_eq]
    change c • f (u * u') = f (_ * _)
    rw [hmul, hmul, Equiv.ofBijective_apply_symm_apply f hbij,
      Equiv.ofBijective_apply_symm_apply f hbij, smul_add]

theorem f_scalarHom (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u')
    (hbij : Function.Bijective f) (c : K) (v : ↥V) : f (scalarHom hmul hbij c v) = c • f v :=
  Equiv.ofBijective_apply_symm_apply f hbij _

theorem injective_of_ker (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u')
    (hker : ∀ u : ↥V, f u = 0 → u = 1) : Function.Injective f := by
  intro u u' h
  have h1 : f (u * u'⁻¹) = 0 := by
    have := hmul (u * u'⁻¹) u'
    rw [inv_mul_cancel_right, h] at this
    exact add_eq_right.mp this.symm
  exact mul_inv_eq_one.mp (hker _ h1)

end Scalar

section Point

variable {L V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M] [Module K M] {f : ↥V → M}

@[expose] noncomputable def imgSub (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') (hbij : Function.Bijective f)
    (hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v))
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {U : Subgroup G}
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U) : Submodule K M where
  carrier := {m | ∃ u : ↥V, (u : G) ∈ U ∧ f u = m}
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u * u', U.mul_mem hu hu', hmul u u'⟩
  zero_mem' := ⟨1, U.one_mem, map_one_of_add hmul⟩
  smul_mem' := by
    rintro c _ ⟨u, hu, rfl⟩
    refine ⟨scalarHom hmul hbij c u, hU _ ?_ ?_ u hu, f_scalarHom hmul hbij c u⟩
    · intro x hx
      rw [hC, Subgroup.mem_bot] at hx ⊢
      rw [show x = 1 from Subtype.ext hx, map_one]
      rfl
    · intro l hl v w hw
      obtain ⟨A, hA⟩ := hlin l hl
      have hmem : l * ((scalarHom hmul hbij c v : ↥V) : G) * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (scalarHom hmul hbij c v).2
      have key : scalarHom hmul hbij c w =
          ⟨l * ((scalarHom hmul hbij c v : ↥V) : G) * l⁻¹, hmem⟩ := by
        apply hbij.1
        rw [f_scalarHom hmul hbij c w, hA v w hw,
          hA (scalarHom hmul hbij c v) ⟨_, hmem⟩ rfl, f_scalarHom hmul hbij c v,
          LinearMap.map_smul]
      rw [key, mul_inv_cancel]
      exact Subgroup.one_mem _

theorem eq_span_of_card {P : Submodule K M} [Finite P] (hP : Nat.card P = Nat.card K) {m : M}
    (hm : m ∈ P) (hm0 : m ≠ 0) : P = K ∙ m := by
  have hle : K ∙ m ≤ P := (Submodule.span_singleton_le_iff_mem m P).mpr hm
  have hcard : Nat.card (K ∙ m) = Nat.card K :=
    Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K M m hm0).toEquiv.symm
  symm
  apply Submodule.toAddSubgroup_injective
  apply AddSubgroup.eq_of_le_of_card_ge hle
  change Nat.card P ≤ Nat.card (K ∙ m)
  rw [hcard, hP]

theorem conj_eq_of_inf_ne_bot [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') (hbij : Function.Bijective f)
    (hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v))
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G} (hV₁ : V₁ ≤ V)
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₁)
    (hcard : Nat.card V₁ = Nat.card K) {l : G} (hl : l ∈ L)
    (hne : V₁ ⊓ conjSubgroup V₁ l ≠ ⊥) : conjSubgroup V₁ l = V₁ := by
  have : Finite M := Finite.of_surjective f hbij.2
  set S := imgSub hLV hmul hbij hlin hC hU with hS
  have hSc : Nat.card S = Nat.card K := by
    rw [← hcard]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun u : ↥V₁ => (⟨f ⟨u, hV₁ u.2⟩, ⟨_, u.2, rfl⟩⟩ : S)) ⟨?_, ?_⟩)).symm
    · intro u u' h
      have h2 := hbij.1 (congrArg Subtype.val h)
      apply Subtype.ext
      exact congrArg (fun w : ↥V => (w : G)) h2
    · rintro ⟨_, ⟨u, hu, rfl⟩⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx₁ : x ∈ V₁ := (Subgroup.mem_inf.mp hx).1
  have hx₂ : l * x * l⁻¹ ∈ V₁ := mem_conjSubgroup_iff.mp (Subgroup.mem_inf.mp hx).2
  have hxV : x ∈ V := hV₁ hx₁
  have hm0 : f ⟨x, hxV⟩ ≠ 0 := by
    intro h0
    apply hx1
    have h1 := congrArg Subtype.val (hbij.1 (h0.trans (map_one_of_add hmul).symm))
    exact Subtype.ext h1
  have hSm : S = K ∙ f ⟨x, hxV⟩ := eq_span_of_card hSc ⟨⟨x, hxV⟩, hx₁, rfl⟩ hm0
  obtain ⟨A, hA⟩ := hlin l⁻¹ (L.inv_mem hl)
  have hconjV : ∀ y ∈ V, l⁻¹ * y * l⁻¹⁻¹ ∈ V := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hl)) y).mp hy
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m' hm'
    obtain ⟨v, rfl⟩ := hbij.2 m'
    have h1 := hA v ⟨_, hconjV v v.2⟩ rfl
    rw [hm', ← map_one_of_add hmul] at h1
    have h3 : (v : G) = 1 := by
      have h2 := congrArg Subtype.val (hbij.1 h1)
      simp only [OneMemClass.coe_one, inv_inv] at h2
      have h4 : (v : G) = l * (l⁻¹ * v * l) * l⁻¹ := by group
      rw [h4, h2, mul_one, mul_inv_cancel]
    rw [show v = 1 from Subtype.ext h3]
    exact map_one_of_add hmul
  have hTc : Nat.card (S.map A) = Nat.card K := by
    rw [← hSc]
    exact Nat.card_congr (Submodule.equivMapOfInjective A hAinj S).toEquiv.symm
  have hmT : f ⟨x, hxV⟩ ∈ S.map A :=
    ⟨f ⟨_, hV₁ hx₂⟩, ⟨⟨_, hV₁ hx₂⟩, hx₂, rfl⟩, (hA _ ⟨x, hxV⟩ (by group)).symm⟩
  have hST : S.map A = S := (eq_span_of_card hTc hmT hm0).trans hSm.symm
  ext z
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hz
    have hzV : z ∈ V := by
      have h1 := hconjV _ (hV₁ hz)
      rwa [show l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z by group] at h1
    have hfz : f ⟨z, hzV⟩ ∈ S := by
      rw [← hST]
      exact ⟨f ⟨_, hV₁ hz⟩, ⟨⟨_, hV₁ hz⟩, hz, rfl⟩, (hA _ ⟨z, hzV⟩ (by group)).symm⟩
    obtain ⟨u, hu, hfu⟩ := hfz
    rw [← show (u : G) = z from congrArg Subtype.val (hbij.1 hfu)]
    exact hu
  · intro hz
    have hfz : f ⟨z, hV₁ hz⟩ ∈ S.map A := by
      rw [hST]
      exact ⟨_, hz, rfl⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hAu⟩ := hfz
    rw [← hA u ⟨_, hconjV u u.2⟩ rfl] at hAu
    have h1 := congrArg Subtype.val (hbij.1 hAu)
    simp only at h1
    rw [← h1, show l * (l⁻¹ * (u : G) * l⁻¹⁻¹) * l⁻¹ = u by group]
    exact hu

end Point

theorem pointsTIFact_holds : Ch11.SecD.PointsTIFact := by
  intro G _ _ T L I n V₁ hS hV₁ l hl hne
  obtain ⟨⟨-, hV₁V, hst, hidx, -⟩, -⟩ := hV₁
  have hC := hS.cV
  have hcard : Nat.card V₁ = 2 ^ n := by
    rw [hC, Subgroup.relIndex_bot_left, mul_one] at hidx
    exact hidx
  have hLV := hS.le_normalizer
  have hker1 : ∀ u : ↥(fsuV T I),
      u ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) → u = 1 := by
    intro u hu
    have h1 : (u : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨u.2, Subgroup.mem_subgroupOf.mp hu⟩
    rw [hC] at h1
    exact Subtype.ext h1
  obtain ⟨hcomm, hnat⟩ := hS.nat
  rcases hnat with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
    ⟨_, _, _, -, -, K, _, _, hK, π, hπ⟩
  · obtain ⟨f, hmul, hker, hsurj, hlin⟩ := exists_coord_autOn hLV (linModelNat _) hπ
    exact conj_eq_of_inf_ne_bot hLV hmul
      ⟨injective_of_ker hmul fun u hu => hker1 u ((hker u).mp hu), hsurj⟩ hlin hC hV₁V hst
      (hcard.trans hK.symm) hl hne
  · obtain ⟨f, hmul, hker, hsurj, hlin⟩ := exists_coord_autOn hLV (linModelNat _) hπ
    exact conj_eq_of_inf_ne_bot hLV hmul
      ⟨injective_of_ker hmul fun u hu => hker1 u ((hker u).mp hu), hsurj⟩ hlin hC hV₁V hst
      (hcard.trans hK.symm) hl hne
  · have : CharP K 2 := charP_two_of_card (by have := hS.one_lt; omega) hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K := by
      rw [← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
      refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
        (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
    obtain ⟨f, hmul, hker, hsurj, hlin⟩ := exists_coord_autOn hLV (linModelZorn _ hle) hπ
    exact conj_eq_of_inf_ne_bot hLV hmul
      ⟨injective_of_ker hmul fun u hu => hker1 u ((hker u).mp hu), hsurj⟩ hlin hC hV₁V hst
      (hcard.trans hK.symm) hl hne

end CFSG.Quasithin.Vol2.KGNat
