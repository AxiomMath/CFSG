module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xb
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

namespace P22x

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Matrix

section NatDecSection

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem sub_mem_commOn {ρ : Representation (ZMod 2) X V} {A : Subgroup X} {U : Submodule (ZMod 2) V}
    {a : X} (ha : a ∈ A) {u : V} (hu : u ∈ U) : ρ a u - u ∈ commOn ρ A U :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem commOn_le_iff {ρ : Representation (ZMod 2) X V} {A : Subgroup X} {U W : Submodule (ZMod 2) V} :
    commOn ρ A U ≤ W ↔ ∀ a ∈ A, ∀ u ∈ U, ρ a u - u ∈ W := by
  refine ⟨fun h a ha u hu => h (sub_mem_commOn ha hu), fun h => Submodule.span_le.2 ?_⟩
  rintro _ ⟨a, ha, u, hu, rfl⟩
  exact h a ha u hu

theorem commOn_mono {ρ : Representation (ZMod 2) X V} {A A' : Subgroup X}
    {U U' : Submodule (ZMod 2) V} (hA : A ≤ A') (hU : U ≤ U') : commOn ρ A U ≤ commOn ρ A' U' :=
  commOn_le_iff.2 fun a ha u hu => sub_mem_commOn (hA ha) (hU hu)

theorem commOn_le_of_invariant {ρ : Representation (ZMod 2) X V} {A : Subgroup X}
    {U : Submodule (ZMod 2) V} (hU : ∀ a ∈ A, ∀ u ∈ U, ρ a u ∈ U) : commOn ρ A U ≤ U :=
  commOn_le_iff.2 fun a ha u hu => U.sub_mem (hU a ha u hu) hu

theorem commOn_invariant {ρ : Representation (ZMod 2) X V} {A : Subgroup X}
    {U : Submodule (ZMod 2) V} {g : X} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hgU : ∀ u ∈ U, ρ g u ∈ U) : ∀ w ∈ commOn ρ A U, ρ g w ∈ commOn ρ A U := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hw
    have h1 : ρ g (ρ a u - u) = ρ (g * a * g⁻¹) (ρ g u) - ρ g u := by
      rw [map_sub, show ρ (g * a * g⁻¹) (ρ g u) = ρ g (ρ a u) from ?_]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        show ρ g⁻¹ (ρ g u) = u from ?_]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1]
    exact sub_mem_commOn (hgA a ha) (hgU u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

variable (ρ : Representation (ZMod 2) X V)

@[expose] def natI (Nbar : Subgroup X) : Submodule (ZMod 2) V := commOn ρ Nbar ⊤

@[expose] def natC (Nbar : Subgroup X) : Submodule (ZMod 2) V := natI ρ Nbar ⊓ fixSub ρ Nbar

@[expose] def natIi (Nbar H : Subgroup X) : Submodule (ZMod 2) V := commOn ρ H (natI ρ Nbar)

structure NatDec (Nbar : Subgroup X) {m : ℕ} (Nb : Fin m → Subgroup X) : Prop where
  direct : IsInternalDirect Nbar Nb
  sum : IsDirectSumMod (natI ρ Nbar) (natC ρ Nbar) (fun i => natIi ρ Nbar (Nb i))
  nat : ∀ i, ∃ n : ℕ, 1 ≤ n ∧
    NatL2 ρ (Nb i) (natIi ρ Nbar (Nb i)) (natIi ρ Nbar (Nb i) ⊓ natC ρ Nbar) n

variable {ρ} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.le (d : NatDec ρ Nbar Nb) (i : Fin m) : Nb i ≤ Nbar :=
  (le_iSup Nb i).trans d.direct.1.le

theorem NatDec.comm (d : NatDec ρ Nbar Nb) {i j : Fin m} (hij : i ≠ j) {x y : X} (hx : x ∈ Nb i)
    (hy : y ∈ Nb j) : x * y = y * x :=
  d.direct.2.1 i j hij x hx y hy

theorem NatDec.conj_mem (d : NatDec ρ Nbar Nb) {g : X} (hg : g ∈ Nbar) (i : Fin m) {h : X}
    (hh : h ∈ Nb i) : g * h * g⁻¹ ∈ Nb i := by
  have hg' : g ∈ ⨆ j, Nb j := d.direct.1 ▸ hg
  refine Subgroup.iSup_induction (C := fun g => ∀ h ∈ Nb i, g * h * g⁻¹ ∈ Nb i) Nb hg'
    (fun j g hgj h hh => ?_) (fun h hh => by simpa using hh) (fun a b ha hb h hh => ?_) h hh
  · by_cases hji : j = i
    · subst hji
      exact (Nb j).mul_mem ((Nb j).mul_mem hgj hh) ((Nb j).inv_mem hgj)
    · rw [d.comm hji hgj hh]
      simpa using hh
  · have : a * b * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ := by group
    rw [this]
    exact ha _ (hb h hh)

theorem NatDec.inv_I (_d : NatDec ρ Nbar Nb) {g : X} (hg : g ∈ Nbar) :
    ∀ u ∈ natI ρ Nbar, ρ g u ∈ natI ρ Nbar :=
  commOn_invariant (A := Nbar) (U := ⊤) (g := g)
    (fun a ha => Nbar.mul_mem (Nbar.mul_mem hg ha) (Nbar.inv_mem hg)) (fun u _ => trivial)

theorem NatDec.Ii_le_I (d : NatDec ρ Nbar Nb) (i : Fin m) : natIi ρ Nbar (Nb i) ≤ natI ρ Nbar :=
  commOn_le_of_invariant fun a ha u hu => d.inv_I (d.le i ha) u hu

theorem NatDec.inv_Ii (d : NatDec ρ Nbar Nb) {g : X} (hg : g ∈ Nbar) (i : Fin m) :
    ∀ u ∈ natIi ρ Nbar (Nb i), ρ g u ∈ natIi ρ Nbar (Nb i) :=
  commOn_invariant (A := Nb i) (U := natI ρ Nbar) (g := g) (fun a ha => d.conj_mem hg i ha)
    (d.inv_I hg)

theorem natC_fix {g : X} (hg : g ∈ Nbar) {c : V} (hc : c ∈ natC ρ Nbar) : ρ g c = c :=
  hc.2 g hg

theorem NatDec.step1 (d : NatDec ρ Nbar Nb) {i j : Fin m} (hji : j ≠ i) {g : X} (hg : g ∈ Nb j)
    {x : V} (hx : x ∈ natIi ρ Nbar (Nb i)) : ρ g x - x ∈ natC ρ Nbar := by
  have hxI : x ∈ natI ρ Nbar := d.Ii_le_I i hx
  have h1 : ρ g x - x ∈ natIi ρ Nbar (Nb j) := sub_mem_commOn hg hxI
  have h2 : ρ g x - x ∈ natIi ρ Nbar (Nb i) :=
    (natIi ρ Nbar (Nb i)).sub_mem (d.inv_Ii (d.le j hg) i x hx) hx
  exact d.sum.2 i ⟨Submodule.mem_sup_left h2,
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji h1))⟩

theorem NatDec.exists_comm (d : NatDec ρ Nbar Nb) (i : Fin m) :
    ∀ x ∈ natIi ρ Nbar (Nb i), ∃ x' ∈ commOn ρ (Nb i) (natIi ρ Nbar (Nb i)),
      x - x' ∈ natC ρ Nbar := by
  intro x hx
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  obtain ⟨g₁, g₂, u₁, u₂, hy⟩ := sl2_exists_decomp (ψ x)
  obtain ⟨x₁, hx₁, hψ₁⟩ := hψs u₁
  obtain ⟨x₂, hx₂, hψ₂⟩ := hψs u₂
  set h₁ : ↥(Nb i) := φ.symm g₁
  set h₂ : ↥(Nb i) := φ.symm g₂
  have hcomm : (ρ (h₁ : X) x₁ - x₁) + (ρ (h₂ : X) x₂ - x₂) ∈ commOn ρ (Nb i) (natIi ρ Nbar (Nb i)) :=
    Submodule.add_mem _ (sub_mem_commOn h₁.2 hx₁) (sub_mem_commOn h₂.2 hx₂)
  have hAle : commOn ρ (Nb i) (natIi ρ Nbar (Nb i)) ≤ natIi ρ Nbar (Nb i) :=
    commOn_le_of_invariant fun a ha u hu => d.inv_Ii (d.le i ha) i u hu
  refine ⟨_, hcomm, ?_⟩
  have hker : ψ (x - ((ρ (h₁ : X) x₁ - x₁) + (ρ (h₂ : X) x₂ - x₂))) = 0 := by
    rw [map_sub, map_add, map_sub, map_sub, hψφ h₁ x₁ hx₁, hψφ h₂ x₂ hx₂, hψ₁, hψ₂]
    simp only [h₁, h₂, MulEquiv.apply_symm_apply]
    rw [hy]
    abel
  exact (hψA _ ((natIi ρ Nbar (Nb i)).sub_mem hx (hAle hcomm)) hker).2

theorem NatDec.lemma21 (d : NatDec ρ Nbar Nb) {i j : Fin m} (hji : j ≠ i) {g : X} (hg : g ∈ Nb j)
    {x : V} (hx : x ∈ natIi ρ Nbar (Nb i)) : ρ g x = x := by
  obtain ⟨x', hx'm, hxx'⟩ := d.exists_comm i x hx
  have hcfix : ρ g (x - x') = x - x' := natC_fix (d.le j hg) hxx'
  have hx'fix : ρ g x' = x' := by
    have hle : commOn ρ (Nb i) (natIi ρ Nbar (Nb i)) ≤ LinearMap.eqLocus (ρ g) LinearMap.id := by
      rw [commOn_le_iff]
      intro h hh u hu
      have hδ : ρ g u - u ∈ natC ρ Nbar := d.step1 hji hg hu
      have hfixh : ρ h (ρ g u - u) = ρ g u - u := natC_fix (d.le i hh) hδ
      have hcomm : ρ g (ρ h u) = ρ h (ρ g u) := by
        rw [← Module.End.mul_apply, ← map_mul, d.comm hji hg hh, map_mul, Module.End.mul_apply]
      show ρ g (ρ h u - u) = ρ h u - u
      rw [map_sub, hcomm]
      rw [map_sub] at hfixh
      exact sub_eq_sub_iff_sub_eq_sub.1 hfixh
    exact hle hx'm
  have h1 : ρ g (x - x') = ρ g x - ρ g x' := map_sub _ _ _
  rw [hx'fix] at h1
  have h2 : ρ g x - x' = x - x' := by rw [← h1]; exact hcfix
  exact sub_left_inj.1 h2

theorem NatDec.pairwise_comm (d : NatDec ρ Nbar Nb) :
    Pairwise fun i j : Fin m => ∀ x y : X, x ∈ Nb i → y ∈ Nb j → Commute x y :=
  fun _ _ hij x y hx hy => d.comm hij hx hy

@[expose] def NatDec.natPi (d : NatDec ρ Nbar Nb) : (∀ i, ↥(Nb i)) →* X :=
  Subgroup.noncommPiCoprod (H := Nb) d.pairwise_comm

theorem NatDec.indep (d : NatDec ρ Nbar Nb) : iSupIndep Nb :=
  fun i => disjoint_iff.2 (d.direct.2.2 i)

theorem NatDec.natPi_injective (d : NatDec ρ Nbar Nb) : Function.Injective d.natPi :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep d.indep

theorem NatDec.natPi_range (d : NatDec ρ Nbar Nb) : d.natPi.range = Nbar := by
  rw [NatDec.natPi, Subgroup.noncommPiCoprod_range]
  exact d.direct.1

theorem NatDec.natPi_mulSingle (d : NatDec ρ Nbar Nb) (k : Fin m) (y : ↥(Nb k)) :
    d.natPi (Pi.mulSingle k y) = (y : X) :=
  Subgroup.noncommPiCoprod_mulSingle k y

theorem NatDec.natPi_mem (d : NatDec ρ Nbar Nb) (f : ∀ i, ↥(Nb i)) : d.natPi f ∈ Nbar := by
  have h : d.natPi f ∈ d.natPi.range := ⟨f, rfl⟩
  rwa [d.natPi_range] at h

theorem NatDec.exists_natPi (d : NatDec ρ Nbar Nb) {a : X} (ha : a ∈ Nbar) :
    ∃ f : ∀ i, ↥(Nb i), d.natPi f = a := by
  have h : a ∈ d.natPi.range := by rwa [d.natPi_range]
  exact h

theorem NatDec.pi_act (d : NatDec ρ Nbar Nb) (f : ∀ i, ↥(Nb i)) (i : Fin m) {x : V}
    (hx : x ∈ natIi ρ Nbar (Nb i)) : ρ (d.natPi f) x = ρ ((f i : ↥(Nb i)) : X) x := by
  classical
  let S : Subgroup (∀ i, ↥(Nb i)) :=
    { carrier := {f | ∀ i, ∀ x ∈ natIi ρ Nbar (Nb i),
        ρ (d.natPi f) x = ρ ((f i : ↥(Nb i)) : X) x}
      one_mem' := by
        intro i x _
        simp
      mul_mem' := by
        intro f g hf hg i x hx
        have hgx : ρ ((g i : ↥(Nb i)) : X) x ∈ natIi ρ Nbar (Nb i) :=
          d.inv_Ii (d.le i (g i).2) i x hx
        rw [map_mul, map_mul, Module.End.mul_apply, hg i x hx, hf i _ hgx, Pi.mul_apply,
          Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      inv_mem' := by
        intro f hf i x hx
        have hy : ρ (((f i : ↥(Nb i)) : X)⁻¹) x ∈ natIi ρ Nbar (Nb i) :=
          d.inv_Ii (Nbar.inv_mem (d.le i (f i).2)) i x hx
        have h1 : ρ (d.natPi f) (ρ (((f i : ↥(Nb i)) : X)⁻¹) x) = x := by
          rw [hf i _ hy, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        have h2 : ρ (d.natPi f⁻¹) x = ρ (((f i : ↥(Nb i)) : X)⁻¹) x := by
          calc ρ (d.natPi f⁻¹) x
              = ρ ((d.natPi f)⁻¹) (ρ (d.natPi f) (ρ (((f i : ↥(Nb i)) : X)⁻¹) x)) := by
                rw [h1, map_inv]
            _ = ρ (((f i : ↥(Nb i)) : X)⁻¹) x := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
                rfl
        rw [h2]
        simp }
  have hsingle : ∀ (k : Fin m) (y : ↥(Nb k)), (Pi.mulSingle k y : ∀ i, ↥(Nb i)) ∈ S := by
    intro k y i x hx
    rw [d.natPi_mulSingle k y]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Pi.mulSingle_eq_of_ne hik]
      simpa using d.lemma21 (Ne.symm hik) y.2 hx
  have hS : ∀ f : (∀ i, ↥(Nb i)), f ∈ S := by
    intro f
    rw [← Finset.noncommProd_mulSingle f]
    exact Subgroup.noncommProd_mem S _ fun k _ => hsingle k (f k)
  exact hS f i x hx

theorem NatDec.faithful (d : NatDec ρ Nbar Nb) (i : Fin m) {b : X} (hb : b ∈ Nb i)
    (h : ∀ x ∈ natIi ρ Nbar (Nb i), ρ b x = x) : b = 1 := by
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  have hφ : φ ⟨b, hb⟩ = 1 := by
    apply sl2_eq_one_of_fix
    intro y
    obtain ⟨x, hx, rfl⟩ := hψs y
    have := hψφ ⟨b, hb⟩ x hx
    rw [← this]
    exact congrArg ψ (h x hx)
  have := φ.injective (hφ.trans (map_one φ).symm)
  exact congrArg Subtype.val this

@[expose] def NatDec.proj (d : NatDec ρ Nbar Nb) (i : Fin m) (A : Subgroup X) : Subgroup X :=
  ((A.comap d.natPi).map (Pi.evalMonoidHom (fun j => ↥(Nb j)) i)).map (Nb i).subtype

theorem NatDec.mem_proj (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X} {b : X} :
    b ∈ d.proj i A ↔ ∃ f : ∀ j, ↥(Nb j), d.natPi f ∈ A ∧ ((f i : ↥(Nb i)) : X) = b := by
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩

theorem NatDec.proj_le (d : NatDec ρ Nbar Nb) (i : Fin m) (A : Subgroup X) : d.proj i A ≤ Nb i := by
  rintro _ ⟨_, _, rfl⟩
  exact Subtype.property _

theorem NatDec.isPGroup_proj (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X}
    (hA : IsPGroup 2 A) : IsPGroup 2 (d.proj i A) := by
  rintro ⟨b, hb⟩
  obtain ⟨f, hfA, rfl⟩ := (d.mem_proj i).1 hb
  obtain ⟨k, hk⟩ := hA ⟨d.natPi f, hfA⟩
  refine ⟨k, ?_⟩
  have h1 : d.natPi (f ^ (2 ^ k)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 : f ^ (2 ^ k) = 1 := d.natPi_injective (h1.trans (map_one _).symm)
  apply Subtype.ext
  have := congrFun h2 i
  simpa using congrArg Subtype.val this

theorem NatDec.card_le_prod_proj [Finite X] (d : NatDec ρ Nbar Nb) {A : Subgroup X} (hA : A ≤ Nbar) :
    Nat.card A ≤ ∏ i, Nat.card (d.proj i A) := by
  classical
  have hex : ∀ a : A, ∃ f : ∀ j, ↥(Nb j), d.natPi f = (a : X) := fun a => d.exists_natPi (hA a.2)
  choose g hg using hex
  let G : A → ∀ i, ↥(d.proj i A) := fun a i =>
    ⟨((g a i : ↥(Nb i)) : X), (d.mem_proj i).2 ⟨g a, by rw [hg a]; exact a.2, rfl⟩⟩
  have hinj : Function.Injective G := by
    intro a b hab
    have : g a = g b := by
      funext i
      apply Subtype.ext
      exact congrArg (fun z : ↥(d.proj i A) => (z : X)) (congrFun hab i)
    apply Subtype.ext
    rw [← hg a, ← hg b, this]
  calc Nat.card A ≤ Nat.card (∀ i, ↥(d.proj i A)) := Nat.card_le_card_of_injective G hinj
    _ = ∏ i, Nat.card (d.proj i A) := Nat.card_pi

theorem NatDec.exists_proj_act (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X} (hA : A ≤ Nbar)
    {a : X} (ha : a ∈ A) {x : V} (hx : x ∈ natIi ρ Nbar (Nb i)) :
    ∃ b ∈ d.proj i A, ρ a x = ρ b x := by
  obtain ⟨f, rfl⟩ := d.exists_natPi (hA ha)
  exact ⟨((f i : ↥(Nb i)) : X), (d.mem_proj i).2 ⟨f, ha, rfl⟩, d.pi_act f i hx⟩

theorem NatDec.exists_act_of_proj (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X} {b : X}
    (hb : b ∈ d.proj i A) {x : V} (hx : x ∈ natIi ρ Nbar (Nb i)) : ∃ a ∈ A, ρ a x = ρ b x := by
  obtain ⟨f, hfA, rfl⟩ := (d.mem_proj i).1 hb
  exact ⟨d.natPi f, hfA, d.pi_act f i hx⟩

end NatDecSection

section Counting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_sup_directSum {ι : Type*} [DecidableEq ι] (Y : ι → Submodule (ZMod 2) V)
    (C : Submodule (ZMod 2) V)
    (hY : ∀ i, (Y i ⊔ C) ⊓ ((⨆ j ∈ {j | j ≠ i}, Y j) ⊔ C) ≤ C) (s : Finset ι) :
    Nat.card ↥(s.sup Y ⊔ C) * ∏ i ∈ s, Nat.card ↥(Y i ⊓ C) =
      Nat.card ↥C * ∏ i ∈ s, Nat.card ↥(Y i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hle : s.sup Y ≤ ⨆ j ∈ {j | j ≠ k}, Y j :=
      Finset.sup_le fun j hj =>
        le_iSup₂_of_le j (show j ≠ k from fun h => hk (h ▸ hj)) le_rfl
    have hinf : (s.sup Y ⊔ C) ⊓ Y k = Y k ⊓ C := by
      apply le_antisymm
      · intro x hx
        refine ⟨hx.2, hY k ⟨Submodule.mem_sup_left hx.2, ?_⟩⟩
        exact (sup_le_sup_right hle C) hx.1
      · exact fun x hx => ⟨Submodule.mem_sup_right hx.2, hx.1⟩
    have hsup : (insert k s).sup Y ⊔ C = (s.sup Y ⊔ C) ⊔ Y k := by
      rw [Finset.sup_insert, sup_comm (Y k), sup_assoc, sup_comm (Y k) C, ← sup_assoc]
    have hcard := card_inf_mul_card_sup (s.sup Y ⊔ C) (Y k)
    rw [hinf] at hcard
    rw [hsup, Finset.prod_insert hk, Finset.prod_insert hk]
    calc Nat.card ↥((s.sup Y ⊔ C) ⊔ Y k) *
          (Nat.card ↥(Y k ⊓ C) * ∏ i ∈ s, Nat.card ↥(Y i ⊓ C))
        = (Nat.card ↥(Y k ⊓ C) * Nat.card ↥((s.sup Y ⊔ C) ⊔ Y k)) *
            ∏ i ∈ s, Nat.card ↥(Y i ⊓ C) := by ring
      _ = Nat.card ↥(Y k) * (Nat.card ↥(s.sup Y ⊔ C) * ∏ i ∈ s, Nat.card ↥(Y i ⊓ C)) := by
          rw [hcard]; ring
      _ = Nat.card ↥C * (Nat.card ↥(Y k) * ∏ i ∈ s, Nat.card ↥(Y i)) := by
          rw [ih]; ring

theorem card_comap_eq_mul {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G]
    (f : G →+ H) (hf : Function.Surjective f) (S : AddSubgroup H) :
    Nat.card (S.comap f) = Nat.card f.ker * Nat.card S := by
  haveI : Finite H := Finite.of_surjective f hf
  have h1 := AddSubgroup.index_comap_of_surjective S hf
  have h2 := AddSubgroup.card_mul_index (S.comap f)
  have h3 := AddSubgroup.card_mul_index S
  have h4 := AddSubgroup.card_ker_mul_card_of_surjective hf
  have hpos : 0 < S.index := Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite
  rw [h1] at h2
  have : Nat.card (S.comap f) * S.index = (Nat.card f.ker * Nat.card S) * S.index := by
    rw [h2, ← h4, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Counting

section Local

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def modFix (ρ : Representation (ZMod 2) X V) (C : Submodule (ZMod 2) V) (P : Subgroup X) :
    Submodule (ZMod 2) V where
  carrier := {v | ∀ a ∈ P, ρ a v - v ∈ C}
  add_mem' {v w} hv hw a ha := by
    have : ρ a (v + w) - (v + w) = (ρ a v - v) + (ρ a w - w) := by
      rw [map_add]; abel
    rw [this]
    exact C.add_mem (hv a ha) (hw a ha)
  zero_mem' a _ := by simp
  smul_mem' c v hv a ha := by
    have : ρ a (c • v) - c • v = c • (ρ a v - v) := by
      rw [map_smul, smul_sub]
    rw [this]
    exact C.smul_mem c (hv a ha)

theorem mem_modFix {ρ : Representation (ZMod 2) X V} {C : Submodule (ZMod 2) V} {P : Subgroup X}
    {v : V} : v ∈ modFix ρ C P ↔ ∀ a ∈ P, ρ a v - v ∈ C := Iff.rfl

variable {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.local_bound [Finite V] (d : NatDec ρ Nbar Nb) (i : Fin m) {P : Subgroup X} (hP : P ≤ Nb i)
    (hP2 : IsPGroup 2 P) :
    Nat.card P * Nat.card ↥(natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) P) ≤
        Nat.card ↥(natIi ρ Nbar (Nb i)) ∧
      (Nat.card P * Nat.card ↥(natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) P) =
          Nat.card ↥(natIi ρ Nbar (Nb i)) → P = ⊥ ∨ ¬ 2 ∣ P.relIndex (Nb i)) := by
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  set A : Submodule (ZMod 2) V := natIi ρ Nbar (Nb i) with hAdef
  set Q : Subgroup ↥(StatedSL 2 F) := (P.subgroupOf (Nb i)).map φ.toMonoidHom with hQdef
  have hPsub : Nat.card (P.subgroupOf (Nb i)) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have hQcard : Nat.card Q = Nat.card P := by
    rw [hQdef, Subgroup.card_map_of_injective φ.injective, hPsub]
  have hQp : IsPGroup 2 Q := (hP2.comap_subtype).map _
  have hrel : ∀ x ∈ A, x ∈ modFix ρ (natC ρ Nbar) P ↔ ψ x ∈ sl2Fix Q := by
    intro x hx
    constructor
    · intro hxP g hg
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
      have hbP : (b : X) ∈ P := hb
      have h1 : ρ (b : X) x - x ∈ natC ρ Nbar := hxP _ hbP
      have h2 : ρ (b : X) x - x ∈ A := A.sub_mem (d.inv_Ii (d.le i b.2) i x hx) hx
      have h3 : ψ (ρ (b : X) x - x) = 0 := hψB _ ⟨h2, h1⟩
      rw [map_sub, hψφ b x hx] at h3
      exact sub_eq_zero.1 h3
    · intro hx' a ha
      have hb : (⟨a, hP ha⟩ : ↥(Nb i)) ∈ P.subgroupOf (Nb i) := ha
      have h1 := hx' (φ ⟨a, hP ha⟩) (Subgroup.mem_map_of_mem _ hb)
      have h2 : ρ a x - x ∈ A := A.sub_mem (d.inv_Ii (d.le i (hP ha)) i x hx) hx
      have h3 : ψ (ρ a x - x) = 0 := by
        have := hψφ ⟨a, hP ha⟩ x hx
        rw [map_sub]
        exact sub_eq_zero.2 (this.trans h1)
      exact (hψA _ h2 h3).2
  set f : ↥A →+ (Fin 2 → F) := ψ.comp A.subtype.toAddMonoidHom with hf
  have hfs : Function.Surjective f := fun y => by
    obtain ⟨x, hx, hxy⟩ := hψs y
    exact ⟨⟨x, hx⟩, hxy⟩
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ natC ρ Nbar) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, hψA _ y.1.2 y.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, hψB _ v.2⟩
        left_inv := fun y => rfl
        right_inv := fun v => rfl }
  have hc1 : Nat.card ↥A = Nat.card f.ker * Nat.card F ^ 2 := by
    have := card_comap_eq_mul f hfs ⊤
    rw [AddSubgroup.comap_top, AddSubgroup.card_top, AddSubgroup.card_top, card_vec2] at this
    exact this
  set S : AddSubgroup (Fin 2 → F) := (sl2Fix Q).toAddSubgroup with hS
  have hc2 : Nat.card ↥(A ⊓ modFix ρ (natC ρ Nbar) P) =
      Nat.card f.ker * Nat.card (sl2Fix Q) := by
    have h := card_comap_eq_mul f hfs S
    have h' : Nat.card ↥(A ⊓ modFix ρ (natC ρ Nbar) P) = Nat.card ↥(S.comap f) :=
      Nat.card_congr
        { toFun := fun v => ⟨⟨v.1, v.2.1⟩, (hrel v.1 v.2.1).1 v.2.2⟩
          invFun := fun y => ⟨y.1.1, y.1.2, (hrel y.1.1 y.1.2).2 y.2⟩
          left_inv := fun v => rfl
          right_inv := fun y => rfl }
    rw [h', h]
    rfl
  have hker_pos : 0 < Nat.card f.ker := Nat.card_pos
  have hmain := sl2_card_mul_fix_le hF Q hQp
  rw [hQcard] at hmain
  have hq0 : 0 < Nat.card F := Nat.card_pos
  refine ⟨?_, fun heq => ?_⟩
  · rw [hc1, hc2]
    calc Nat.card P * (Nat.card f.ker * Nat.card (sl2Fix Q))
        = Nat.card f.ker * (Nat.card P * Nat.card (sl2Fix Q)) := by ring
      _ ≤ Nat.card f.ker * Nat.card F ^ 2 := Nat.mul_le_mul_left _ hmain
  · rw [hc1, hc2] at heq
    have hee : Nat.card P * Nat.card (sl2Fix Q) = Nat.card F ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hker_pos
      rw [← heq]
      ring
    by_cases hP1 : P = ⊥
    · exact Or.inl hP1
    · right
      have hQ1 : Q ≠ ⊥ := by
        intro h
        apply hP1
        have h1 : Nat.card Q = 1 := by rw [h]; exact Subgroup.card_bot
        rw [hQcard] at h1
        exact Subgroup.card_eq_one.1 h1
      obtain ⟨h1, h2⟩ := sl2_card_le hF Q hQp
      rw [hQcard] at h1
      have h2 := h2 hQ1
      have hPq : Nat.card P = Nat.card F := by
        apply le_antisymm h1
        by_contra hlt
        push_neg at hlt
        have h3 : Nat.card P * Nat.card (sl2Fix Q) ≤ Nat.card P * Nat.card F :=
          Nat.mul_le_mul_left _ h2
        have h4 : Nat.card P * Nat.card F < Nat.card F * Nat.card F :=
          Nat.mul_lt_mul_of_pos_right hlt hq0
        have h5 : Nat.card F ^ 2 = Nat.card F * Nat.card F := sq _
        omega
      have hNb : Nat.card ↥(Nb i) = Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [Nat.card_congr φ.toEquiv, card_statedSL_two]
      have hrelmul := Subgroup.relIndex_mul_card (H := P) (K := Nb i)
      rw [inf_of_le_left hP, hPq, hNb] at hrelmul
      have hrel1 : P.relIndex (Nb i) = Nat.card F ^ 2 - 1 :=
        Nat.eq_of_mul_eq_mul_right hq0 (by rw [hrelmul]; ring)
      rw [hrel1]
      exact (odd_card_sq_sub_one hF).not_two_dvd_nat

@[expose] def natF (ρ : Representation (ZMod 2) X V) (Nbar A : Subgroup X) : Submodule (ZMod 2) V :=
  natI ρ Nbar ⊓ modFix ρ (natC ρ Nbar) A

theorem NatDec.inf_modFix_proj (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X} (hA : A ≤ Nbar) :
    natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) (d.proj i A) =
      natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) A := by
  ext x
  constructor
  · rintro ⟨hx, hxf⟩
    refine ⟨hx, fun a ha => ?_⟩
    obtain ⟨b, hb, hab⟩ := d.exists_proj_act i hA ha hx
    rw [hab]
    exact hxf b hb
  · rintro ⟨hx, hxf⟩
    refine ⟨hx, fun b hb => ?_⟩
    obtain ⟨a, ha, hab⟩ := d.exists_act_of_proj i hb hx
    rw [← hab]
    exact hxf a ha

theorem NatDec.split (d : NatDec ρ Nbar Nb) {A : Subgroup X} (hA : A ≤ Nbar) (s : Finset (Fin m)) :
    ∀ v ∈ s.sup (fun i => natIi ρ Nbar (Nb i)) ⊔ natC ρ Nbar, v ∈ modFix ρ (natC ρ Nbar) A →
      v ∈ s.sup (fun i => natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) A) ⊔ natC ρ Nbar := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv _
    simpa using hv
  | insert k s hk ih =>
    intro v hv hvf
    rw [Finset.sup_insert] at hv ⊢
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    have hsupinv : ∀ a ∈ A, ∀ u ∈ s.sup (fun i => natIi ρ Nbar (Nb i)),
        ρ a u ∈ s.sup (fun i => natIi ρ Nbar (Nb i)) := by
      intro a ha u hu
      have hle : s.sup (fun i => natIi ρ Nbar (Nb i)) ≤
          (s.sup (fun i => natIi ρ Nbar (Nb i))).comap (ρ a) :=
        Finset.sup_le fun j hj u hu =>
          Submodule.mem_comap.2 (Finset.le_sup (f := fun i => natIi ρ Nbar (Nb i)) hj
            (d.inv_Ii (hA ha) j u hu))
      exact Submodule.mem_comap.1 (hle hu)
    have hsle : s.sup (fun i => natIi ρ Nbar (Nb i)) ≤
        ⨆ j ∈ {j | j ≠ k}, natIi ρ Nbar (Nb j) :=
      Finset.sup_le fun j hj =>
        le_iSup₂_of_le j (show j ≠ k from fun h => hk (h ▸ hj)) le_rfl
    have hfz : ∀ a ∈ A, ρ a z - z ∈ natC ρ Nbar ∧ ρ a y - y ∈ natC ρ Nbar := by
      intro a ha
      have h0 := hvf a ha
      have hc' : ρ a c = c := natC_fix (hA ha) hc
      have h1 : ρ a z - z ∈ natIi ρ Nbar (Nb k) :=
        (natIi ρ Nbar (Nb k)).sub_mem (d.inv_Ii (hA ha) k z hz) hz
      have h2 : ρ a y - y ∈ s.sup (fun i => natIi ρ Nbar (Nb i)) :=
        (s.sup (fun i => natIi ρ Nbar (Nb i))).sub_mem (hsupinv a ha y hy) hy
      have h3 : (ρ a z - z) + (ρ a y - y) ∈ natC ρ Nbar := by
        have : ρ a (z + y + c) - (z + y + c) = (ρ a z - z) + (ρ a y - y) := by
          rw [map_add, map_add, hc']; abel
        rw [← this]
        exact h0
      have h4 : ρ a z - z ∈ natC ρ Nbar := by
        refine d.sum.2 k ⟨Submodule.mem_sup_left h1, ?_⟩
        have h5 := ((⨆ j ∈ {j | j ≠ k}, natIi ρ Nbar (Nb j)) ⊔ natC ρ Nbar).sub_mem
          (Submodule.mem_sup_right h3) (Submodule.mem_sup_left (hsle h2))
        rwa [add_sub_cancel_right] at h5
      refine ⟨h4, ?_⟩
      have h5 := (natC ρ Nbar).sub_mem h3 h4
      rwa [add_sub_cancel_left] at h5
    have hzf : z ∈ natIi ρ Nbar (Nb k) ⊓ modFix ρ (natC ρ Nbar) A :=
      ⟨hz, fun a ha => (hfz a ha).1⟩
    have hyf : y ∈ modFix ρ (natC ρ Nbar) A := fun a ha => (hfz a ha).2
    have hy' := ih y (Submodule.mem_sup_left hy) hyf
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.mem_sup_right hc)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hzf)
    · have hle : s.sup (fun i => natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) A) ⊔ natC ρ Nbar ≤
          (natIi ρ Nbar (Nb k) ⊓ modFix ρ (natC ρ Nbar) A ⊔
            s.sup (fun i => natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) A)) ⊔ natC ρ Nbar :=
        sup_le_sup_right le_sup_right _
      exact hle hy'

theorem NatDec.offender_bound [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) {A : Subgroup X}
    (hA : A ≤ Nbar) (hA2 : IsPGroup 2 A) :
    Nat.card A * Nat.card ↥(natF ρ Nbar A) ≤ Nat.card ↥(natI ρ Nbar) ∧
      (Nat.card A * Nat.card ↥(natF ρ Nbar A) = Nat.card ↥(natI ρ Nbar) →
        ∀ i, d.proj i A = ⊥ ∨ ¬ 2 ∣ (d.proj i A).relIndex (Nb i)) := by
  classical
  set Y : Fin m → Submodule (ZMod 2) V := fun i => natIi ρ Nbar (Nb i) with hY
  set Fi : Fin m → Submodule (ZMod 2) V := fun i => Y i ⊓ modFix ρ (natC ρ Nbar) A with hFi
  set C := natC ρ Nbar with hC
  have hdir : ∀ i, (Y i ⊔ C) ⊓ ((⨆ j ∈ {j | j ≠ i}, Y j) ⊔ C) ≤ C := d.sum.2
  have hdirF : ∀ i, (Fi i ⊔ C) ⊓ ((⨆ j ∈ {j | j ≠ i}, Fi j) ⊔ C) ≤ C := fun i =>
    le_trans (inf_le_inf (sup_le_sup_right inf_le_left _)
      (sup_le_sup_right (iSup₂_mono fun j _ => inf_le_left) _)) (hdir i)
  have hIeq : Finset.univ.sup Y ⊔ C = natI ρ Nbar := by
    rw [Finset.sup_univ_eq_iSup]
    exact d.sum.1
  have hCfix : ∀ c ∈ C, ∀ a ∈ A, ρ a c - c ∈ C := fun c hc a ha => by
    rw [natC_fix (hA ha) hc, sub_self]
    exact C.zero_mem
  have hFeq : Finset.univ.sup Fi ⊔ C = natF ρ Nbar A := by
    apply le_antisymm
    · refine sup_le (Finset.sup_le fun i _ => ?_) ?_
      · exact inf_le_inf (d.Ii_le_I i) le_rfl
      · exact le_inf inf_le_left (hCfix)
    · intro v hv
      exact d.split hA Finset.univ v (by rw [hIeq]; exact hv.1) hv.2
  have hDS1 := card_sup_directSum Y C hdir Finset.univ
  have hDS2 := card_sup_directSum Fi C hdirF Finset.univ
  rw [hIeq] at hDS1
  rw [hFeq] at hDS2
  have hFiC : ∀ i, Fi i ⊓ C = Y i ⊓ C := fun i => by
    apply le_antisymm (inf_le_inf inf_le_left le_rfl)
    exact le_inf (le_inf inf_le_left fun c hc a ha => hCfix c hc.2 a ha) inf_le_right
  have hkp : ∏ i, Nat.card ↥(Fi i ⊓ C) = ∏ i, Nat.card ↥(Y i ⊓ C) :=
    Finset.prod_congr rfl fun i _ => by rw [hFiC i]
  rw [hkp] at hDS2
  have hkp_pos : 0 < ∏ i, Nat.card ↥(Y i ⊓ C) := Finset.prod_pos fun i _ => Nat.card_pos
  have hC_pos : 0 < Nat.card ↥C := Nat.card_pos
  have hloc : ∀ i, Nat.card (d.proj i A) * Nat.card ↥(Fi i) ≤ Nat.card ↥(Y i) ∧
      (Nat.card (d.proj i A) * Nat.card ↥(Fi i) = Nat.card ↥(Y i) →
        d.proj i A = ⊥ ∨ ¬ 2 ∣ (d.proj i A).relIndex (Nb i)) := by
    intro i
    have h := d.local_bound i (d.proj_le i A) (d.isPGroup_proj i hA2)
    rw [d.inf_modFix_proj i hA] at h
    exact h
  have hprod : Nat.card A * ∏ i, Nat.card ↥(Fi i) ≤ ∏ i, Nat.card ↥(Y i) := by
    calc Nat.card A * ∏ i, Nat.card ↥(Fi i)
        ≤ (∏ i, Nat.card (d.proj i A)) * ∏ i, Nat.card ↥(Fi i) :=
          Nat.mul_le_mul_right _ (d.card_le_prod_proj hA)
      _ = ∏ i, (Nat.card (d.proj i A) * Nat.card ↥(Fi i)) := (Finset.prod_mul_distrib).symm
      _ ≤ ∏ i, Nat.card ↥(Y i) := Finset.prod_le_prod' fun i _ => (hloc i).1
  refine ⟨?_, fun heq i => ?_⟩
  · refine Nat.le_of_mul_le_mul_right ?_ hkp_pos
    calc Nat.card A * Nat.card ↥(natF ρ Nbar A) * ∏ i, Nat.card ↥(Y i ⊓ C)
        = Nat.card A * (Nat.card ↥(natF ρ Nbar A) * ∏ i, Nat.card ↥(Y i ⊓ C)) := by ring
      _ = Nat.card ↥C * (Nat.card A * ∏ i, Nat.card ↥(Fi i)) := by rw [hDS2]; ring
      _ ≤ Nat.card ↥C * ∏ i, Nat.card ↥(Y i) := Nat.mul_le_mul_left _ hprod
      _ = Nat.card ↥(natI ρ Nbar) * ∏ i, Nat.card ↥(Y i ⊓ C) := hDS1.symm
  · have h1 : Nat.card ↥C * (Nat.card A * ∏ i, Nat.card ↥(Fi i)) =
        Nat.card ↥C * ∏ i, Nat.card ↥(Y i) := by
      calc Nat.card ↥C * (Nat.card A * ∏ i, Nat.card ↥(Fi i))
          = Nat.card A * (Nat.card ↥(natF ρ Nbar A) * ∏ i, Nat.card ↥(Y i ⊓ C)) := by
            rw [hDS2]; ring
        _ = Nat.card ↥(natI ρ Nbar) * ∏ i, Nat.card ↥(Y i ⊓ C) := by rw [← heq]; ring
        _ = Nat.card ↥C * ∏ i, Nat.card ↥(Y i) := hDS1
    have h2 : Nat.card A * ∏ i, Nat.card ↥(Fi i) = ∏ i, Nat.card ↥(Y i) :=
      Nat.eq_of_mul_eq_mul_left hC_pos h1
    have h3 : ∏ i, (Nat.card (d.proj i A) * Nat.card ↥(Fi i)) = ∏ i, Nat.card ↥(Y i) := by
      apply le_antisymm (Finset.prod_le_prod' fun i _ => (hloc i).1)
      calc ∏ i, Nat.card ↥(Y i) = Nat.card A * ∏ i, Nat.card ↥(Fi i) := h2.symm
        _ ≤ (∏ i, Nat.card (d.proj i A)) * ∏ i, Nat.card ↥(Fi i) :=
          Nat.mul_le_mul_right _ (d.card_le_prod_proj hA)
        _ = ∏ i, (Nat.card (d.proj i A) * Nat.card ↥(Fi i)) := (Finset.prod_mul_distrib).symm
    apply (hloc i).2
    by_contra hne
    have hlt : Nat.card (d.proj i A) * Nat.card ↥(Fi i) < Nat.card ↥(Y i) :=
      lt_of_le_of_ne (hloc i).1 hne
    have hpos : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        0 < Nat.card (d.proj j A) * Nat.card ↥(Fi j) := fun j _ =>
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have := Finset.prod_lt_prod₀ hpos (fun j _ => (hloc j).1) ⟨i, Finset.mem_univ i, hlt⟩
    omega

theorem natI_inf_fixSub_le_natF (ρ : Representation (ZMod 2) X V) (Nbar A : Subgroup X) :
    natI ρ Nbar ⊓ fixSub ρ A ≤ natF ρ Nbar A := fun v hv =>
  ⟨hv.1, fun a ha => by rw [hv.2 a ha, sub_self]; exact (natC ρ Nbar).zero_mem⟩

theorem NatDec.chain [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) {A : Subgroup X} (hA : A ≤ Nbar)
    (hA2 : IsPGroup 2 A) :
    Nat.card A * Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card ↥(fixSub ρ A) ≤
      Nat.card A * Nat.card ↥(natF ρ Nbar A) * Nat.card ↥(fixSub ρ A) ∧
    Nat.card A * Nat.card ↥(natF ρ Nbar A) * Nat.card ↥(fixSub ρ A) ≤
      Nat.card ↥(natI ρ Nbar) * Nat.card ↥(fixSub ρ A) ∧
    Nat.card ↥(natI ρ Nbar) * Nat.card ↥(fixSub ρ A) ≤
      Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card V := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.card_mono (Set.toFinite _) (natI_inf_fixSub_le_natF ρ Nbar A)))
  · exact Nat.mul_le_mul_right _ (d.offender_bound hA hA2).1
  · have h1 := card_inf_mul_card_sup (natI ρ Nbar) (fixSub ρ A)
    have h2 : Nat.card ↥(natI ρ Nbar ⊔ fixSub ρ A) ≤ Nat.card V :=
      Nat.card_le_card_of_injective _ (Submodule.injective_subtype _)
    calc Nat.card ↥(natI ρ Nbar) * Nat.card ↥(fixSub ρ A)
        = Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card ↥(natI ρ Nbar ⊔ fixSub ρ A) := h1.symm
      _ ≤ Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card V := Nat.mul_le_mul_left _ h2

theorem NatDec.not_strict_offender [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) {A : Subgroup X}
    (hA : A ≤ Nbar) (hA2 : IsPGroup 2 A) :
    Nat.card A * Nat.card ↥(fixSub ρ A) ≤ Nat.card V := by
  obtain ⟨h1, h2, h3⟩ := d.chain hA hA2
  have hc : 0 < Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hc
  calc Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * (Nat.card A * Nat.card ↥(fixSub ρ A))
      = Nat.card A * Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card ↥(fixSub ρ A) := by ring
    _ ≤ Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card V := h1.trans (h2.trans h3)

theorem NatDec.offender_eq [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) {A : Subgroup X}
    (hA : A ≤ Nbar) (hA2 : IsPGroup 2 A)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixSub ρ A)) :
    natF ρ Nbar A = natI ρ Nbar ⊓ fixSub ρ A ∧
      ∀ i, d.proj i A = ⊥ ∨ ¬ 2 ∣ (d.proj i A).relIndex (Nb i) := by
  obtain ⟨h1, h2, h3⟩ := d.chain hA hA2
  have hso := d.not_strict_offender hA hA2
  have heqv : Nat.card A * Nat.card ↥(fixSub ρ A) = Nat.card V := le_antisymm hso hoff
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have hx : 0 < Nat.card ↥(fixSub ρ A) := Nat.card_pos
  have hcu : Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card V =
      Nat.card A * Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card ↥(fixSub ρ A) := by
    rw [← heqv]; ring
  have e1 : Nat.card A * Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) * Nat.card ↥(fixSub ρ A) =
      Nat.card A * Nat.card ↥(natF ρ Nbar A) * Nat.card ↥(fixSub ρ A) :=
    le_antisymm h1 (h2.trans (h3.trans hcu.le))
  have e2 : Nat.card A * Nat.card ↥(natF ρ Nbar A) * Nat.card ↥(fixSub ρ A) =
      Nat.card ↥(natI ρ Nbar) * Nat.card ↥(fixSub ρ A) :=
    le_antisymm h2 (h3.trans (hcu.le.trans e1.le))
  have e1' : Nat.card ↥(natI ρ Nbar ⊓ fixSub ρ A) = Nat.card ↥(natF ρ Nbar A) :=
    Nat.eq_of_mul_eq_mul_left hA0 (Nat.eq_of_mul_eq_mul_right hx e1)
  have e2' : Nat.card A * Nat.card ↥(natF ρ Nbar A) = Nat.card ↥(natI ρ Nbar) :=
    Nat.eq_of_mul_eq_mul_right hx e2
  refine ⟨?_, (d.offender_bound hA hA2).2 e2'⟩
  have hle : natI ρ Nbar ⊓ fixSub ρ A ≤ natF ρ Nbar A := natI_inf_fixSub_le_natF ρ Nbar A
  have := AddSubgroup.eq_of_le_of_card_ge (H := (natI ρ Nbar ⊓ fixSub ρ A).toAddSubgroup)
    (K := (natF ρ Nbar A).toAddSubgroup) hle e1'.ge
  exact (Submodule.toAddSubgroup_injective this).symm

end Local

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
