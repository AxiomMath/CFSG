module

public import CFSG.LocalAnalysis.SteinbergCEMixedIrreducibleHead
public import CFSG.Quasithin.H13.NQTermInvertedDetector
public import CFSG.Quasithin.H13.NQTermTensorEquality
public import CFSG.LinearAlgebra.SteinbergBQDihedralNaturalS3

public section

namespace CFSG.Quasithin.H13.NQBlock

open Module CFSG.LocalAnalysis

variable {D : Type*} [AddCommGroup D] [Module (ZMod 2) D]

section Sect

variable (U N : Submodule (ZMod 2) D)

@[expose] noncomputable def secEnd (g : Module.End (ZMod 2) D) (hU : ∀ u ∈ U, g u ∈ U)
    (hN : ∀ n ∈ N, g n ∈ N) : Module.End (ZMod 2) (U ⧸ N.comap U.subtype) :=
  (N.comap U.subtype).mapQ (N.comap U.subtype) (g.restrict hU) fun _ hx => hN _ hx

theorem secEnd_mk (g : Module.End (ZMod 2) D) (hU : ∀ u ∈ U, g u ∈ U)
    (hN : ∀ n ∈ N, g n ∈ N) (u : U) :
    secEnd U N g hU hN (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨g u, hU u u.2⟩ :=
  rfl

theorem secEnd_one :
    secEnd U N 1 (fun _ hu => hu) (fun _ hn => hn) = 1 := by
  ext u
  rfl

theorem secEnd_mul (g h : Module.End (ZMod 2) D) (hgU : ∀ u ∈ U, g u ∈ U)
    (hgN : ∀ n ∈ N, g n ∈ N) (hhU : ∀ u ∈ U, h u ∈ U) (hhN : ∀ n ∈ N, h n ∈ N) :
    secEnd U N (g * h) (fun u hu => hgU _ (hhU u hu)) (fun n hn => hgN _ (hhN n hn)) =
      secEnd U N g hgU hgN * secEnd U N h hhU hhN := by
  ext u
  rfl


theorem secEnd_comm (g h : Module.End (ZMod 2) D) (hgU : ∀ u ∈ U, g u ∈ U)
    (hgN : ∀ n ∈ N, g n ∈ N) (hhU : ∀ u ∈ U, h u ∈ U) (hhN : ∀ n ∈ N, h n ∈ N)
    (hgh : g * h = h * g) :
    secEnd U N g hgU hgN * secEnd U N h hhU hhN =
      secEnd U N h hhU hhN * secEnd U N g hgU hgN := by
  rw [← secEnd_mul, ← secEnd_mul]
  congr 1

@[expose] noncomputable def secHom (H : Subgroup (Module.End (ZMod 2) D)ˣ)
    (hU : ∀ h ∈ H, ∀ u ∈ U, (h : Module.End (ZMod 2) D) u ∈ U)
    (hN : ∀ h ∈ H, ∀ n ∈ N, (h : Module.End (ZMod 2) D) n ∈ N) :
    ↥H →* (Module.End (ZMod 2) (U ⧸ N.comap U.subtype))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun h => secEnd U N ((h : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
        (hU h h.2) (hN h h.2)
      map_one' := secEnd_one U N
      map_mul' := fun g h => secEnd_mul U N _ _ (hU g g.2) (hN g g.2) (hU h h.2) (hN h h.2) }

theorem secHom_apply (H : Subgroup (Module.End (ZMod 2) D)ˣ)
    (hU : ∀ h ∈ H, ∀ u ∈ U, (h : Module.End (ZMod 2) D) u ∈ U)
    (hN : ∀ h ∈ H, ∀ n ∈ N, (h : Module.End (ZMod 2) D) n ∈ N) (h : H) :
    ((secHom U N H hU hN h : (Module.End (ZMod 2) (U ⧸ N.comap U.subtype))ˣ) :
      Module.End (ZMod 2) (U ⧸ N.comap U.subtype)) =
      secEnd U N ((h : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) (hU h h.2) (hN h h.2) :=
  rfl

theorem secHom_eq_one_iff (H : Subgroup (Module.End (ZMod 2) D)ˣ)
    (hU : ∀ h ∈ H, ∀ u ∈ U, (h : Module.End (ZMod 2) D) u ∈ U)
    (hN : ∀ h ∈ H, ∀ n ∈ N, (h : Module.End (ZMod 2) D) n ∈ N) (h : H) :
    secHom U N H hU hN h = 1 ↔
      ∀ u ∈ U, ((h : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u - u ∈ N := by
  constructor
  · intro h1 u hu
    have h2 := congrArg (fun f : (Module.End (ZMod 2) (U ⧸ N.comap U.subtype))ˣ =>
      (f : Module.End (ZMod 2) (U ⧸ N.comap U.subtype)) (Submodule.Quotient.mk ⟨u, hu⟩)) h1
    simp only [secHom_apply, secEnd_mk, Units.val_one, Module.End.one_apply] at h2
    rw [Submodule.Quotient.eq] at h2
    exact h2
  · intro h1
    apply Units.ext
    rw [secHom_apply, Units.val_one]
    ext u
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk u
    rw [Submodule.Quotient.eq]
    exact h1 u u.2


abbrev Sec := ↥U ⧸ N.comap U.subtype

@[expose] def stabUN : Subgroup (Module.End (ZMod 2) D)ˣ where
  carrier := {g | (∀ u ∈ U, (g : Module.End (ZMod 2) D) u ∈ U) ∧
    (∀ n ∈ N, (g : Module.End (ZMod 2) D) n ∈ N) ∧
    (∀ u ∈ U, ((g⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u ∈ U) ∧
    ∀ n ∈ N, ((g⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) n ∈ N}
  mul_mem' {g h} hg hh := by
    refine ⟨fun u hu => hg.1 _ (hh.1 u hu), fun n hn => hg.2.1 _ (hh.2.1 n hn),
      fun u hu => ?_, fun n hn => ?_⟩
    · rw [mul_inv_rev]
      exact hh.2.2.1 _ (hg.2.2.1 u hu)
    · rw [mul_inv_rev]
      exact hh.2.2.2 _ (hg.2.2.2 n hn)
  one_mem' := ⟨fun u hu => hu, fun n hn => hn, fun u hu => by simpa using hu,
    fun n hn => by simpa using hn⟩
  inv_mem' {g} hg := ⟨hg.2.2.1, hg.2.2.2, fun u hu => by rw [inv_inv]; exact hg.1 u hu,
    fun n hn => by rw [inv_inv]; exact hg.2.1 n hn⟩

theorem mem_stabUN {g : (Module.End (ZMod 2) D)ˣ} :
    g ∈ stabUN U N ↔ (∀ u ∈ U, (g : Module.End (ZMod 2) D) u ∈ U) ∧
      (∀ n ∈ N, (g : Module.End (ZMod 2) D) n ∈ N) ∧
      (∀ u ∈ U, ((g⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u ∈ U) ∧
      ∀ n ∈ N, ((g⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) n ∈ N :=
  Iff.rfl

end Sect

section Irred

theorem sec_irreducible {X Y A : Subgroup (Module.End (ZMod 2) D)ˣ} {U N : Submodule (ZMod 2) D}
    (hmax : CFSG.LocalAnalysis.IsMaxInvariantIn X Y A U N)
    (hXU : CFSG.LocalAnalysis.IsInvariantBy X U) (hYU : CFSG.LocalAnalysis.IsInvariantBy Y U)
    (hAU : CFSG.LocalAnalysis.IsInvariantBy A U)
    (M : Submodule (ZMod 2) (U ⧸ N.comap U.subtype))
    (hMX : ∀ x (hx : x ∈ X), ∀ m ∈ M, secEnd U N (x : Module.End (ZMod 2) D) (hXU x hx)
      (hmax.2.2.1 x hx) m ∈ M)
    (hMY : ∀ y (hy : y ∈ Y), ∀ m ∈ M, secEnd U N (y : Module.End (ZMod 2) D) (hYU y hy)
      (hmax.2.2.2.1 y hy) m ∈ M)
    (hMA : ∀ a (ha : a ∈ A), ∀ m ∈ M, secEnd U N (a : Module.End (ZMod 2) D) (hAU a ha)
      (hmax.2.2.2.2.1 a ha) m ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  have hNU := hmax.1
  have hNX := hmax.2.2.1
  have hNY := hmax.2.2.2.1
  have hNA := hmax.2.2.2.2.1
  have hmaxN := hmax.2.2.2.2.2
  set M₁ : Submodule (ZMod 2) D := (M.comap (N.comap U.subtype).mkQ).map U.subtype with hM₁
  have hNM₁ : N ≤ M₁ := by
    intro n hn
    refine ⟨⟨n, hNU hn⟩, ?_, rfl⟩
    change (N.comap U.subtype).mkQ ⟨n, hNU hn⟩ ∈ M
    rw [Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (show (⟨n, hNU hn⟩ : U) ∈ N.comap U.subtype from hn)]
    exact M.zero_mem
  have hM₁U : M₁ ≤ U := Submodule.map_subtype_le _ _
  have hinv : ∀ (H : Subgroup (Module.End (ZMod 2) D)ˣ) (hHU : ∀ h ∈ H, ∀ u ∈ U,
      (h : Module.End (ZMod 2) D) u ∈ U) (hHN : ∀ h ∈ H, ∀ n ∈ N,
      (h : Module.End (ZMod 2) D) n ∈ N),
      (∀ h (hh : h ∈ H), ∀ m ∈ M, secEnd U N (h : Module.End (ZMod 2) D) (hHU h hh)
        (hHN h hh) m ∈ M) →
      CFSG.LocalAnalysis.IsInvariantBy H M₁ := by
    intro H hHU hHN hHM h hh v hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨⟨(h : Module.End (ZMod 2) D) u, hHU h hh u u.2⟩, ?_, rfl⟩
    have h1 := hHM h hh _ hu
    rwa [Submodule.mkQ_apply, secEnd_mk] at h1
  rcases hmaxN M₁ hNM₁ hM₁U (hinv X hXU hNX hMX) (hinv Y hYU hNY hMY) (hinv A hAU hNA hMA) with
    h0 | h1
  · left
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hu : (u : D) ∈ M₁ := ⟨u, hm, rfl⟩
    rw [h0] at hu
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hu
  · right
    rw [eq_top_iff]
    intro m _
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hu : (u : D) ∈ M₁ := by
      rw [h1]
      exact u.2
    obtain ⟨u', hu', he⟩ := hu
    rw [show u = u' from Subtype.ext he.symm]
    exact hu'

end Irred


@[expose] noncomputable def restrictUnitsHom (V : Submodule (ZMod 2) D)
    (H : Subgroup (Module.End (ZMod 2) D)ˣ)
    (hV : ∀ h ∈ H, ∀ v ∈ V, ((h : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ∈ V) :
    ↥H →* (Module.End (ZMod 2) V)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun h => ((h : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D).restrict
        (hV h h.2)
      map_one' := by
        ext
        rfl
      map_mul' := fun _ _ => by
        ext
        rfl }

theorem sec_trivial_of_commute [FiniteDimensional (ZMod 2) D]
    {X Y A B : Subgroup (Module.End (ZMod 2) D)ˣ} {U N : Submodule (ZMod 2) D}
    (hmax : CFSG.LocalAnalysis.IsMaxInvariantIn X Y A U N)
    (hXU : CFSG.LocalAnalysis.IsInvariantBy X U) (hYU : CFSG.LocalAnalysis.IsInvariantBy Y U)
    (hAU : CFSG.LocalAnalysis.IsInvariantBy A U) (hBU : CFSG.LocalAnalysis.IsInvariantBy B U)
    (hBN : CFSG.LocalAnalysis.IsInvariantBy B N) (hB2 : IsPGroup 2 B)
    (hBX : ∀ b ∈ B, ∀ x ∈ X, b * x = x * b) (hBY : ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) :
    ∀ b ∈ B, ∀ u ∈ U, (b : Module.End (ZMod 2) D) u - u ∈ N := by
  classical
  have hS : Nontrivial (Sec U N) := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    apply hmax.2.1
    refine le_antisymm hmax.1 fun u hu => ?_
    have : (⟨u, hu⟩ : ↥U) ∈ N.comap U.subtype := by
      rw [htop]
      exact Submodule.mem_top
    exact this
  have : Finite D := Module.finite_of_finite (ZMod 2)
  have : Finite (Sec U N) := Module.finite_of_finite (ZMod 2)
  set F := CFSG.LocalAnalysis.CommutingFactor.fixedSub (secHom U N B hBU hBN).range with hF
  have hFinv : ∀ (g : (Module.End (ZMod 2) D)ˣ)
      (hgU : ∀ u ∈ U, (g : Module.End (ZMod 2) D) u ∈ U)
      (hgN : ∀ n ∈ N, (g : Module.End (ZMod 2) D) n ∈ N), (∀ b ∈ B, b * g = g * b) →
      ∀ m ∈ F, secEnd U N (g : Module.End (ZMod 2) D) hgU hgN m ∈ F := by
    intro g hgU hgN hg m hm
    rw [CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub] at hm ⊢
    rintro _ ⟨b, rfl⟩
    have h1 := secEnd_comm U N _ _ (hBU b b.2) (hBN b b.2) hgU hgN
      (by rw [← Units.val_mul, hg b b.2, Units.val_mul])
    have h2 := hm (secHom U N B hBU hBN b) ⟨b, rfl⟩
    calc ((secHom U N B hBU hBN b : (Module.End (ZMod 2) (Sec U N))ˣ) :
          Module.End (ZMod 2) (Sec U N)) (secEnd U N (g : Module.End (ZMod 2) D) hgU hgN m)
        = secEnd U N (g : Module.End (ZMod 2) D) hgU hgN
            (((secHom U N B hBU hBN b : (Module.End (ZMod 2) (Sec U N))ˣ) :
              Module.End (ZMod 2) (Sec U N)) m) := LinearMap.congr_fun h1 m
      _ = secEnd U N (g : Module.End (ZMod 2) D) hgU hgN m := by rw [h2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s₀, hs₀, hs₀B⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero
    ((Units.coeHom (Module.End (ZMod 2) (Sec U N))).comp (secHom U N B hBU hBN)) 2 ⊤
    (hB2.to_subgroup ⊤)
  have hs₀F : s₀ ∈ F := by
    rw [CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub]
    rintro _ ⟨b, rfl⟩
    exact hs₀B b (Subgroup.mem_top b)
  have hF0 : F ≠ ⊥ := fun h => hs₀ (by rw [h] at hs₀F; exact (Submodule.mem_bot _).mp hs₀F)
  have hFtop : F = ⊤ := by
    refine (sec_irreducible hmax hXU hYU hAU F (fun x hx => ?_) (fun y hy => ?_)
      (fun a ha => ?_)).resolve_left hF0
    · exact hFinv x (hXU x hx) (hmax.2.2.1 x hx) fun b hb => hBX b hb x hx
    · exact hFinv y (hYU y hy) (hmax.2.2.2.1 y hy) fun b hb => hBY b hb y hy
    · exact hFinv a (hAU a ha) (hmax.2.2.2.2.1 a ha) fun b hb => hBA b hb a ha
  intro b hb u hu
  have hs : (Submodule.Quotient.mk ⟨u, hu⟩ : Sec U N) ∈ F := by
    rw [hFtop]
    exact Submodule.mem_top
  have h1 : (Submodule.Quotient.mk ⟨(b : Module.End (ZMod 2) D) u, hBU b hb u hu⟩ : Sec U N) =
      Submodule.Quotient.mk ⟨u, hu⟩ :=
    (CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.mp hs) (secHom U N B hBU hBN ⟨b, hb⟩)
      ⟨⟨b, hb⟩, rfl⟩
  have h2 := (Submodule.Quotient.eq (N.comap U.subtype)).mp h1
  exact h2

theorem sec_codim_le [FiniteDimensional (ZMod 2) D] {A : Subgroup (Module.End (ZMod 2) D)ˣ}
    {U N : Submodule (ZMod 2) D} (hUA : CFSG.LocalAnalysis.IsInvariantBy A U)
    (hNA : CFSG.LocalAnalysis.IsInvariantBy A N) {T : Subgroup (Module.End (ZMod 2) (Sec U N))ˣ}
    (hT : ∀ s : Sec U N, (∀ g ∈ T, (g : Module.End (ZMod 2) (Sec U N)) s = s) ↔
      ∀ a (ha : a ∈ A), secEnd U N (a : Module.End (ZMod 2) D) (hUA a ha) (hNA a ha) s = s) :
    finrank (ZMod 2) (Sec U N) -
        finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub T) ≤
      finrank (ZMod 2) D - finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A) := by
  let ρA : Representation (ZMod 2) ↥A D := (Units.coeHom (Module.End (ZMod 2) D)).comp A.subtype
  let E₁ : Subrepresentation ρA :=
    { toSubmodule := U
      apply_mem_toSubmodule := by
        intro a v hv
        exact hUA a a.2 v hv }
  let E₂ : Subrepresentation E₁.toRepresentation :=
    { toSubmodule := N.comap U.subtype
      apply_mem_toSubmodule := by
        intro a v hv
        exact hNA a a.2 v hv }
  have h := CFSG.LocalAnalysis.codim_section_le_codim E₁ E₂
  have e1 : ρA.invariants = CFSG.LocalAnalysis.CommutingFactor.fixedSub A := by
    ext v
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩
  have e2 : E₂.quotient.invariants = CFSG.LocalAnalysis.CommutingFactor.fixedSub T := by
    ext s
    rw [CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub, hT]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩
  rw [e1, e2] at h
  exact h

theorem dihedral_irreducible_commutant {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {cS tS : (Module.End (ZMod 2) S)ˣ} (hcS : orderOf cS = p) (htS : orderOf tS = 2)
    (htz : tS * cS * tS = cS⁻¹) {I : Submodule (ZMod 2) S}
    (hDI : ∀ d ∈ Subgroup.closure {cS, tS}, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I)
    (hI0 : I ≠ ⊥)
    (hIirr : ∀ W ≤ I, (∀ d ∈ Subgroup.closure {cS, tS}, ∀ v ∈ W,
      (d : Module.End (ZMod 2) S) v ∈ W) → W = ⊥ ∨ W = I)
    (hfaith : ∀ d ∈ Subgroup.closure {cS, tS},
      (∀ v ∈ I, (d : Module.End (ZMod 2) S) v = v) → d = 1)
    {T : Subgroup (Module.End (ZMod 2) S)ˣ} (htT : tS ∈ T) (hT : ∀ g ∈ T, g = 1 ∨ g = tS)
    (hdim : finrank (ZMod 2) I -
      finrank (ZMod 2) ↥(I ⊓ CFSG.LocalAnalysis.CommutingFactor.fixedSub T) = 1) :
    p = 3 ∧ Nat.card (CFSG.LocalAnalysis.CommutingFactor.commutantD hDI) = 2 := by
  classical
  set DS := Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) S)ˣ) with hDSdef
  have hcSD : cS ∈ DS := Subgroup.subset_closure (Set.mem_insert _ _)
  have htSD : tS ∈ DS := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set zH : ↥DS := ⟨cS, hcSD⟩ with hzH
  set tH : ↥DS := ⟨tS, htSD⟩ with htH
  have hzHord : orderOf zH = p := by rw [hzH, Subgroup.orderOf_mk, hcS]
  have htHord : orderOf tH = 2 := by rw [htH, Subgroup.orderOf_mk, htS]
  have htzH : tH * zH * tH = zH⁻¹ := Subtype.ext htz
  have hgen : Subgroup.closure ({zH, tH} : Set ↥DS) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage
      (k := ({cS, tS} : Set (Module.End (ZMod 2) S)ˣ))
    have e : ((↑) : ↥DS → (Module.End (ZMod 2) S)ˣ) ⁻¹' {cS, tS} = {zH, tH} := by
      ext g
      simp [hzH, htH, Subtype.ext_iff]
    rw [← e]
    exact h
  let ρI : ↥DS →* Module.End (ZMod 2) ↥I :=
    { toFun := CFSG.LocalAnalysis.CommutingFactor.resD hDI
      map_one' := by
        ext v
        rfl
      map_mul' := fun _ _ => by
        ext v
        rfl }
  have hρIinj : Function.Injective ρI := by
    rw [injective_iff_map_eq_one]
    intro d hd
    apply Subtype.ext
    apply hfaith d d.2
    intro v hv
    exact congrArg (fun f : Module.End (ZMod 2) ↥I => ((f ⟨v, hv⟩ : ↥I) : S)) hd
  have hirrI : ∀ U' : Submodule (ZMod 2) ↥I, (∀ h, ∀ u ∈ U', ρI h u ∈ U') →
      U' = ⊥ ∨ U' = ⊤ := by
    intro U' hU'
    have hW := hIirr (U'.map I.subtype) (Submodule.map_subtype_le _ _) (by
      rintro d hd _ ⟨u, hu, rfl⟩
      exact ⟨ρI ⟨d, hd⟩ u, hU' _ u hu, rfl⟩)
    rcases hW with h | h
    · left
      exact Submodule.map_injective_of_injective I.injective_subtype
        (h.trans (Submodule.map_bot _).symm)
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : S) ∈ U'.map I.subtype := by
        rw [h]
        exact u.2
      obtain ⟨u', hu', he⟩ := hu
      rw [show u = u' from Subtype.ext he.symm]
      exact hu'
  have hker : (LinearMap.ker (ρI tH - 1)).map I.subtype =
      I ⊓ CFSG.LocalAnalysis.CommutingFactor.fixedSub T := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] at hu
      have hu' : (tS : Module.End (ZMod 2) S) u = u := congrArg Subtype.val hu
      refine ⟨u.2, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.mpr fun g hg => ?_⟩
      rcases hT g hg with h | h <;> rw [h]
      · rfl
      · exact hu'
    · rintro ⟨hsI, hsF⟩
      refine ⟨⟨s, hsI⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero]
      exact Subtype.ext ((CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.mp hsF) tS htT)
  have hdim' : finrank (ZMod 2) (↥I ⧸ LinearMap.ker (ρI tH - 1)) = 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (ρI tH - 1))
    have h2 := Submodule.finrank_map_subtype_eq I (LinearMap.ker (ρI tH - 1))
    rw [hker] at h2
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial ↥I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  obtain ⟨hp3, -, -, hscal⟩ :=
    CFSG.LinearAlgebra.binary_rank_one_dihedral_action_is_the_natural_S3_module hp2 hzHord
      htHord htzH hgen ρI hρIinj hirrI hdim'
  refine ⟨hp3, ?_⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨0, 1, fun h => zero_ne_one (α := Module.End (ZMod 2) ↥I) (congrArg Subtype.val h), ?_⟩
  ext f
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  obtain ⟨e, he⟩ := hscal f.1 fun h =>
    ((CFSG.LocalAnalysis.CommutingFactor.mem_commutantD hDI).mp f.2 h).symm
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) e with rfl | rfl
  · left
    rw [zero_smul] at he
    exact Subtype.ext he
  · right
    rw [one_smul] at he
    exact Subtype.ext he

theorem dihedral_head_false {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] [Nontrivial S] {XS T : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hXSne : XS ≠ ⊥) (hXSperf : Group.IsPerfect XS) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {cS tS : (Module.End (ZMod 2) S)ˣ} (hcS : orderOf cS = p) (htS2 : tS ^ 2 = 1)
    (htz : tS * cS * tS = cS⁻¹) (hXc : ∀ x ∈ XS, x * cS = cS * x)
    (hXt : ∀ x ∈ XS, x * tS = tS * x)
    (hirr : ∀ W : Submodule (ZMod 2) S, (∀ g ∈ XS ⊔ Subgroup.closure {cS, tS}, ∀ v ∈ W,
      (g : Module.End (ZMod 2) S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htT : tS ∈ T) (hT : ∀ g ∈ T, g = 1 ∨ g = tS) {m : ℕ}
    (hcod : finrank (ZMod 2) S -
      finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub T) ≤ m)
    (hm : m ≤ 3) (h3 : p = 3 → m ≤ 2) : False := by
  classical
  set DS := Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) S)ˣ) with hDSdef
  have htS1 : tS ≠ 1 := by
    intro h1
    rw [h1, one_mul, mul_one] at htz
    have h2 : cS ^ 2 = 1 := by
      rw [pow_two]
      calc cS * cS = cS⁻¹ * cS := by rw [← htz]
        _ = 1 := inv_mul_cancel cS
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hcS] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have htS : orderOf tS = 2 := orderOf_eq_prime htS2 htS1
  have hXD : ∀ x ∈ XS, ∀ d ∈ DS, x * d = d * x := by
    intro x hx d hd
    have hle : DS ≤ Subgroup.centralizer {x} := by
      rw [hDSdef, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg <;> rw [hg]
      · exact hXc x hx
      · exact hXt x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hd) _ (Set.mem_singleton _)
  have hTD : T ≤ DS := fun g hg => by
    rcases hT g hg with h | h <;> rw [h]
    · exact DS.one_mem
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨I, hDI, hI0, hIirr⟩ := NQTerm.exists_irreducible_invariant DS
  obtain ⟨r, -, -, -, hIfaith, -, -, -, -, hcodI, hr2, hr3, -⟩ :=
    CommutingFactor.commuting_factor_irreducible_modules_have_isotypic_multiplicity
      hXD hirr hDI hI0 hIirr
  have hcodS := hcodI T hTD
  have hr2' := hr2 hXSne hXSperf
  set cI := finrank (ZMod 2) I -
    finrank (ZMod 2) ↥(I ⊓ CFSG.LocalAnalysis.CommutingFactor.fixedSub T) with hcI
  have hrc : r * cI ≤ m := by
    rw [← hcodS]
    exact hcod
  have hcI1 : cI ≤ 1 := by
    by_contra h
    have := Nat.mul_le_mul hr2' (show 2 ≤ cI by omega)
    omega
  have hcI0 : cI ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcodS
    have hle := Submodule.finrank_le (CFSG.LocalAnalysis.CommutingFactor.fixedSub T)
    have htop : CFSG.LocalAnalysis.CommutingFactor.fixedSub T = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by omega)
    apply htS1
    apply Units.ext
    apply LinearMap.ext
    intro s
    have hs : s ∈ CFSG.LocalAnalysis.CommutingFactor.fixedSub T := by
      rw [htop]
      exact Submodule.mem_top
    exact (CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.mp hs) tS htT
  have hcI' : cI = 1 := by omega
  obtain ⟨hp3, hcomm2⟩ := dihedral_irreducible_commutant hp hp2 hcS htS htz hDI hI0 hIirr
    hIfaith htT hT hcI'
  have hr3' := hr3 (Nat.card_zmod 2) hcomm2 hXSne hXSperf
  have := h3 hp3
  rw [hcI', mul_one] at hrc
  omega

theorem mixed_head_false [FiniteDimensional (ZMod 2) D]
    {X C A : Subgroup (Module.End (ZMod 2) D)ˣ} {U N : Submodule (ZMod 2) D}
    (hX : ⁅X, X⁆ = X) (hXC : ∀ x ∈ X, ∀ y ∈ C, x * y = y * x)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a = a * x)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c₀ : (Module.End (ZMod 2) D)ˣ} (hc₀C : c₀ ∈ C)
    (hc₀ : orderOf c₀ = p) (hCgen : ∀ y ∈ C, ∃ k : ℤ, y = c₀ ^ k)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {B : Subgroup ↥A} (hBidx : B.index = 2) {a₀ : ↥A} (ha₀B : a₀ ∉ B)
    (hcB : ∀ b ∈ B, (b : (Module.End (ZMod 2) D)ˣ) * c₀ = c₀ * b)
    (hca₀ : (a₀ : (Module.End (ZMod 2) D)ˣ) * c₀ * (a₀ : (Module.End (ZMod 2) D)ˣ)⁻¹ = c₀⁻¹)
    {n j : ℕ} (hAcard : Nat.card A = 2 ^ n) (hn : n ≤ 2) (hj : j ≤ 1) (h3 : p = 3 → n = 1)
    (hcodim : 2 ^ (finrank (ZMod 2) D -
      finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) ≤ 2 ^ j * Nat.card A)
    (hN : CFSG.LocalAnalysis.IsMaxInvariantIn X C A U N)
    (hUX : CFSG.LocalAnalysis.IsInvariantBy X U) (hUC : CFSG.LocalAnalysis.IsInvariantBy C U)
    (hUA : CFSG.LocalAnalysis.IsInvariantBy A U)
    (hXnt : ∃ x ∈ X, ∃ u ∈ U, (x : Module.End (ZMod 2) D) u - u ∉ N)
    (hCfaith : ∀ y ∈ C, (∀ u ∈ U, (y : Module.End (ZMod 2) D) u - u ∈ N) → y = 1) : False := by
  classical
  have hNX : CFSG.LocalAnalysis.IsInvariantBy X N := hN.2.2.1
  have hNC : CFSG.LocalAnalysis.IsInvariantBy C N := hN.2.2.2.1
  have hNA : CFSG.LocalAnalysis.IsInvariantBy A N := hN.2.2.2.2.1
  have hSnt : Nontrivial (Sec U N) := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    apply hN.2.1
    refine le_antisymm hN.1 fun u hu => ?_
    have : (⟨u, hu⟩ : ↥U) ∈ N.comap U.subtype := by
      rw [htop]
      exact Submodule.mem_top
    exact this
  have hBC : ∀ b ∈ B, ∀ y ∈ C, (b : (Module.End (ZMod 2) D)ˣ) * y = y * b := by
    intro b hb y hy
    obtain ⟨k, rfl⟩ := hCgen y hy
    exact Commute.zpow_right (hcB b hb) k
  have hB'A : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
  have hBtriv := sec_trivial_of_commute (B := B.map A.subtype) hN hUX hUC hUA
    (fun g hg => hUA g (hB'A hg)) (fun g hg => hNA g (hB'A hg))
    (fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ (hB'A g.2))⟩)
    (fun g hg x hx => (hXA x hx g (hB'A hg)).symm)
    (fun g hg y hy => by
      obtain ⟨b, hb, rfl⟩ := hg
      exact hBC b hb y hy)
    (fun g hg a ha => hAc g (hB'A hg) a ha)
  have hK : ∀ H : Subgroup (Module.End (ZMod 2) D)ˣ, CFSG.LocalAnalysis.IsInvariantBy H U →
      CFSG.LocalAnalysis.IsInvariantBy H N → H ≤ stabUN U N :=
    fun H hHU hHN h hh => ⟨hHU h hh, hHN h hh, hHU _ (H.inv_mem hh), hHN _ (H.inv_mem hh)⟩
  have hKU : ∀ g ∈ stabUN U N, ∀ u ∈ U, (g : Module.End (ZMod 2) D) u ∈ U :=
    fun _ hg => ((mem_stabUN U N).mp hg).1
  have hKN : ∀ g ∈ stabUN U N, ∀ n ∈ N, (g : Module.End (ZMod 2) D) n ∈ N :=
    fun _ hg => ((mem_stabUN U N).mp hg).2.1
  have hXK := hK X hUX hNX
  have hCK := hK C hUC hNC
  have hAK := hK A hUA hNA
  set σ := secHom U N (stabUN U N) hKU hKN with hσdef
  set σX := σ.comp (Subgroup.inclusion hXK) with hσXdef
  set σA := σ.comp (Subgroup.inclusion hAK) with hσAdef
  set cS := σ ⟨c₀, hCK hc₀C⟩ with hcSdef
  set tS := σA a₀ with htSdef
  have hσB : ∀ b ∈ B, σA b = 1 := fun b hb =>
    (secHom_eq_one_iff U N (stabUN U N) hKU hKN (Subgroup.inclusion hAK b)).mpr
      (hBtriv _ ⟨b, hb, rfl⟩)
  have hσA2 : ∀ a : ↥A, σA a = 1 ∨ σA a = tS := by
    intro a
    by_cases ha : a ∈ B
    · exact Or.inl (hσB a ha)
    · right
      have h1 : a₀⁻¹ * a ∈ B := by
        rw [Subgroup.mul_mem_iff_of_index_two hBidx, Subgroup.inv_mem_iff]
        exact iff_of_false ha₀B ha
      calc σA a = σA (a₀ * (a₀⁻¹ * a)) := by rw [mul_inv_cancel_left]
        _ = tS := by rw [htSdef, map_mul, hσB _ h1, mul_one]
  have hσCinj : Function.Injective (σ.comp (Subgroup.inclusion hCK)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    exact hCfaith y y.2
      ((secHom_eq_one_iff U N (stabUN U N) hKU hKN (Subgroup.inclusion hCK y)).mp hy)
  have hcSord : orderOf cS = p := by
    have h1 := orderOf_injective _ hσCinj ⟨c₀, hc₀C⟩
    rw [Subgroup.orderOf_mk, hc₀] at h1
    exact h1
  have ha₀2 : a₀ ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ a₀.2)
  have htS2 : tS ^ 2 = 1 := by rw [htSdef, ← map_pow, ha₀2, map_one]
  have htSinv : tS⁻¹ = tS := inv_eq_of_mul_eq_one_right (by rw [← pow_two, htS2])
  have hrelK : Subgroup.inclusion hAK a₀ * ⟨c₀, hCK hc₀C⟩ * (Subgroup.inclusion hAK a₀)⁻¹ =
      (⟨c₀, hCK hc₀C⟩ : ↥(stabUN U N))⁻¹ := Subtype.ext hca₀
  have htz : tS * cS * tS = cS⁻¹ := by
    have h2 := congrArg σ hrelK
    simp only [map_mul, map_inv] at h2
    calc tS * cS * tS = tS * cS * tS⁻¹ := by rw [htSinv]
      _ = cS⁻¹ := h2
  have hXcS : ∀ x ∈ σX.range, x * cS = cS * x := by
    rintro _ ⟨x, rfl⟩
    have h1 : Subgroup.inclusion hXK x * ⟨c₀, hCK hc₀C⟩ =
        ⟨c₀, hCK hc₀C⟩ * Subgroup.inclusion hXK x :=
      Subtype.ext (hXC x x.2 c₀ hc₀C)
    have h2 := congrArg σ h1
    rwa [map_mul, map_mul] at h2
  have hXtS : ∀ x ∈ σX.range, x * tS = tS * x := by
    rintro _ ⟨x, rfl⟩
    have h1 : Subgroup.inclusion hXK x * Subgroup.inclusion hAK a₀ =
        Subgroup.inclusion hAK a₀ * Subgroup.inclusion hXK x :=
      Subtype.ext (hXA x x.2 _ a₀.2)
    have h2 := congrArg σ h1
    rwa [map_mul, map_mul] at h2
  have hcSD : cS ∈ Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) (Sec U N))ˣ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have htSD : tS ∈ Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) (Sec U N))ˣ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hCD : ∀ y (hy : y ∈ C), σ ⟨y, hCK hy⟩ ∈
      Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) (Sec U N))ˣ) := by
    intro y hy
    obtain ⟨k, rfl⟩ := hCgen y hy
    have h1 : (⟨c₀ ^ k, hCK hy⟩ : ↥(stabUN U N)) = ⟨c₀, hCK hc₀C⟩ ^ k := Subtype.ext rfl
    rw [h1, map_zpow]
    exact zpow_mem hcSD k
  have hAD : ∀ a : ↥A, σA a ∈
      Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) (Sec U N))ˣ) := by
    intro a
    rcases hσA2 a with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact htSD
  have hirr : ∀ W : Submodule (ZMod 2) (Sec U N), (∀ g ∈ σX.range ⊔
      Subgroup.closure ({cS, tS} : Set (Module.End (ZMod 2) (Sec U N))ˣ), ∀ v ∈ W,
      (g : Module.End (ZMod 2) (Sec U N)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    exact sec_irreducible hN hUX hUC hUA W
      (fun x hx m hm => hW (σX ⟨x, hx⟩) (Subgroup.mem_sup_left ⟨⟨x, hx⟩, rfl⟩) m hm)
      (fun y hy m hm => hW (σ ⟨y, hCK hy⟩) (Subgroup.mem_sup_right (hCD y hy)) m hm)
      (fun a ha m hm => hW (σA ⟨a, ha⟩) (Subgroup.mem_sup_right (hAD ⟨a, ha⟩)) m hm)
  have hTiff : ∀ s : Sec U N, (∀ g ∈ σA.range, (g : Module.End (ZMod 2) (Sec U N)) s = s) ↔
      ∀ a (ha : a ∈ A), secEnd U N (a : Module.End (ZMod 2) D) (hUA a ha) (hNA a ha) s = s := by
    intro s
    constructor
    · intro h a ha
      exact h (σA ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    · rintro h _ ⟨a, rfl⟩
      exact h a a.2
  have hsec := sec_codim_le hUA hNA hTiff
  have hcD : finrank (ZMod 2) D -
      finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A) ≤ j + n := by
    have h1 : 2 ^ (finrank (ZMod 2) D -
        finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) ≤ 2 ^ (j + n) := by
      rw [pow_add, ← hAcard]
      exact hcodim
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hXSne : σX.range ≠ ⊥ := by
    obtain ⟨x, hx, u, hu, hxu⟩ := hXnt
    intro h
    have h1 : σX ⟨x, hx⟩ ∈ σX.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hxu ((secHom_eq_one_iff U N (stabUN U N) hKU hKN ⟨x, hXK hx⟩).mp h1 u hu)
  have hXSperf : Group.IsPerfect ↥σX.range := by
    have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
    exact Group.IsPerfect.range σX
  exact dihedral_head_false (T := σA.range) hXSne hXSperf hp hp2 hcSord htS2 htz hXcS hXtS hirr
    ⟨a₀, rfl⟩ (by rintro _ ⟨a, rfl⟩; exact hσA2 a) (hsec.trans hcD) (by omega)
    (fun h => by have := h3 h; omega)

theorem solvable_source_linear_core [FiniteDimensional (ZMod 2) D]
    {X P A : Subgroup (Module.End (ZMod 2) D)ˣ} (hX : ⁅X, X⁆ = X)
    (hXP : ∀ x ∈ X, ∀ y ∈ P, x * y = y * x)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a = a * x)
    (hAP : A ≤ Subgroup.normalizer (P : Set (Module.End (ZMod 2) D)ˣ))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p P) (hPexp : ∀ y ∈ P, y ^ p = 1)
    (hPrank : CFSG.pRank p P ≤ 2)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1)
    (h3 : p = 3 → IsCyclic P ∧ Nat.card P = 3) {j : ℕ} (hj : j ≤ 1)
    (hcodim : 2 ^ (finrank (ZMod 2) D -
      finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) ≤ 2 ^ j * Nat.card A)
    (hV : ∃ g ∈ ⁅P, A⁆, ∃ v ∈ CFSG.LocalAnalysis.commSpace ⊤ X,
      ((g : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ≠ v) : False := by
  classical
  have : Finite D := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) D) :=
    Finite.of_injective (fun f : D →ₗ[ZMod 2] D => (f : D → D)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod 2) D)ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) D)ˣ => (u : Module.End (ZMod 2) D))
      Units.val_injective
  set V := CFSG.LocalAnalysis.commSpace ⊤ X with hVdef
  have hVP : ∀ y ∈ P, ∀ v ∈ V, ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ∈ V :=
    fun y hy v hv => CFSG.LocalAnalysis.isInvariantBy_commSpace_of_commute
      (fun a ha b hb => (hXP b hb a ha).symm) (fun _ _ _ _ => Submodule.mem_top) y hy v hv
  have hAX : A ≤ Subgroup.normalizer (X : Set (Module.End (ZMod 2) D)ˣ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hXA x hx a ha, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 : a * x * a⁻¹ * a = a * (a * x * a⁻¹) := hXA _ hx a ha
      have h2 : x = a * x * a⁻¹ :=
        calc x = a⁻¹ * (a * x * a⁻¹ * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [h1]
          _ = a * x * a⁻¹ := by group
      rw [h2]
      exact hx
  have hVA : ∀ a ∈ A, ∀ v ∈ V, ((a : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ∈ V :=
    fun a ha v hv => CFSG.LocalAnalysis.isInvariantBy_commSpace_of_normalizer hAX
      (fun _ _ _ _ => Submodule.mem_top) a ha v hv
  let φ : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  have hφ_apply : ∀ (a : ↥A) (y : ↥P), ((φ a y : ↥P) : (Module.End (ZMod 2) D)ˣ) =
      (a : (Module.End (ZMod 2) D)ˣ) * y * (a : (Module.End (ZMod 2) D)ˣ)⁻¹ := fun _ _ => rfl
  let fP := restrictUnitsHom V P hVP
  let fA := restrictUnitsHom V A hVA
  have hcompat : ∀ a : ↥A, fP.comp (φ a).toMonoidHom =
      (MulAut.conj (fA a)).toMonoidHom.comp fP := by
    intro a
    ext y v
    rfl
  let ρ0 := SemidirectProduct.lift fP fA hcompat
  let ρ : Representation (ZMod 2) (↥P ⋊[φ] ↥A) ↥V := (Units.coeHom _).comp ρ0
  have hρinl : ∀ (y : ↥P) (v : ↥V), ((ρ (SemidirectProduct.inl y) v : ↥V) : D) =
      ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v := fun _ _ => by
    simp [ρ, ρ0, fP, restrictUnitsHom]
  obtain ⟨g, hg, v, hv, hgv⟩ := hV
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hgv rfl
  have hPA : ⁅P, A⁆ ≤ (CFSG.RankThree.CentralExtension.autCommutator φ.range).map P.subtype := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨y, hy, a, ha, rfl⟩
    refine ⟨(⟨y, hy⟩ : ↥P)⁻¹⁻¹ * φ ⟨a, ha⟩ (⟨y, hy⟩ : ↥P)⁻¹,
      CFSG.RankThree.CentralExtension.inv_mul_apply_mem_autCommutator _ ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.coe_mul, hφ_apply]
    simp [commutatorElement_def, mul_assoc]
  obtain ⟨g', hg', rfl⟩ := hPA hg
  have hPnt : Nontrivial ↥P := ⟨⟨g', 1, fun h => hg1 (by rw [h]; rfl)⟩⟩
  have hAnt : Nontrivial ↥A := by
    by_contra hA
    rw [not_nontrivial_iff_subsingleton] at hA
    apply hg1
    have hle : ⁅P, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have : (⟨a, ha⟩ : ↥A) = 1 := Subsingleton.elim _ _
      have h1 : a = 1 := congrArg Subtype.val this
      rw [h1, one_mul, mul_one]
    have := hle ▸ hg
    exact (Subgroup.mem_bot.mp this)
  have hAel : CFSG.IsElementaryAbelian 2 ↥A :=
    { is_comm := ⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hA2 a a.2) }
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply hfaith a a.2
    intro y hy
    have h1 := congrArg (fun f : MulAut ↥P => ((f ⟨y, hy⟩ : ↥P) : (Module.End (ZMod 2) D)ˣ)) ha
    simp only [hφ_apply, MulAut.one_apply] at h1
    calc (a : (Module.End (ZMod 2) D)ˣ) * y = (a : (Module.End (ZMod 2) D)ˣ) * y *
        (a : (Module.End (ZMod 2) D)ˣ)⁻¹ * a := by group
      _ = y * a := by rw [h1]
  have hPexp' : ∀ x : ↥P, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp x x.2)
  have hVdet : ∃ g ∈ CFSG.RankThree.CentralExtension.autCommutator φ.range, ∃ v : ↥V,
      ρ (SemidirectProduct.inl g) v ≠ v := by
    refine ⟨g', hg', ⟨v, hv⟩, fun h => hgv ?_⟩
    have h1 := congrArg Subtype.val h
    rw [hρinl] at h1
    exact h1
  obtain ⟨⟨n, hacard, ha2⟩, ⟨B, hBidx, a₀, ha₀B, x, hxB, -, hccard, hcB, hca₀, hcA, c', hc',
      v', hv'⟩, h3A⟩ :=
    NQTerm.rank_two_exponent_prime_action_has_inverted_cyclic_detector hp hp2 hPp hPexp'
      hPrank φ hφinj ρ hVdet
  set c : ↥P := x⁻¹ * φ a₀ x with hcdef
  set C : Subgroup (Module.End (ZMod 2) D)ˣ := (Subgroup.zpowers c).map P.subtype with hCdef
  have hCP : C ≤ P := Subgroup.map_subtype_le _
  have hXC : ∀ x ∈ X, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hXP x hx y (hCP hy)
  have hCcard : Nat.card C = p := by
    rw [hCdef, Subgroup.card_map_of_injective P.subtype_injective, hccard]
  have hCodd : Odd (Nat.card C) := hCcard ▸ hp.odd_of_ne_two hp2
  have hAC : A ≤ Subgroup.normalizer (C : Set (Module.End (ZMod 2) D)ˣ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hCdef, Subgroup.map_map]
    have h2 := congrArg (Subgroup.map P.subtype) (hcA ⟨b, hb⟩)
    rw [Subgroup.map_map] at h2
    rw [← h2]
    congr 1
  have hCC : ∀ W : Submodule (ZMod 2) D, CFSG.LocalAnalysis.commSpace W C ≤
      CFSG.LocalAnalysis.commSpace (CFSG.LocalAnalysis.commSpace W C) C := fun W =>
    CFSG.LocalAnalysis.commSpace_le_commSpace_commSpace_of_card
      (ZMod.natCast_eq_zero_iff_even.not.mpr (Nat.not_even_iff_odd.mpr hCodd))
  have hVX : CFSG.LocalAnalysis.IsInvariantBy X V := CFSG.LocalAnalysis.isInvariantBy_commSpace
  have hVXX : CFSG.LocalAnalysis.commSpace V X = V :=
    le_antisymm (CFSG.LocalAnalysis.commSpace_le_of_isInvariantBy hVX)
      (CFSG.LocalAnalysis.commSpace_le_commSpace_commSpace_of_perfect hX)
  have hhead := CFSG.LocalAnalysis.isMixedHead_commSpace hXC hCC hAC hVX hVA hVXX
  set U := CFSG.LocalAnalysis.commSpace V C with hUdef
  obtain ⟨hUX, hUC, hUA, -, -, hNex, hNall⟩ := hhead
  have hUne : U ≠ ⊥ := by
    intro h0
    apply hv'
    have h1 := CFSG.LocalAnalysis.sub_mem_commSpace (W := V) (H := C)
      (Subgroup.mem_map_of_mem P.subtype hc') v'.2
    rw [← hUdef, h0, Submodule.mem_bot, sub_eq_zero] at h1
    apply Subtype.ext
    rw [hρinl]
    exact h1
  obtain ⟨N, hN⟩ := hNex hUne
  obtain ⟨hXnt, -, -, hCfaith⟩ := hNall N hN
  have hCsimple : IsSimpleGroup ↥C := by
    have : Fact p.Prime := ⟨hp⟩
    exact isSimpleGroup_of_prime_card hCcard
  have hc₀C : (c : (Module.End (ZMod 2) D)ˣ) ∈ C := ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hc₀ : orderOf (c : (Module.End (ZMod 2) D)ˣ) = p := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hccard
  have hCgen : ∀ y ∈ C, ∃ k : ℤ, y = (c : (Module.End (ZMod 2) D)ˣ) ^ k := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨k, map_zpow P.subtype c k⟩
  have hcB' : ∀ b ∈ B, (b : (Module.End (ZMod 2) D)ˣ) * c = c * b := by
    intro b hb
    have h2 : (b : (Module.End (ZMod 2) D)ˣ) * (c : (Module.End (ZMod 2) D)ˣ) *
        (b : (Module.End (ZMod 2) D)ˣ)⁻¹ = c := by
      rw [← hφ_apply, hcB b hb]
    calc (b : (Module.End (ZMod 2) D)ˣ) * (c : (Module.End (ZMod 2) D)ˣ) =
        (b : (Module.End (ZMod 2) D)ˣ) * (c : (Module.End (ZMod 2) D)ˣ) *
          (b : (Module.End (ZMod 2) D)ˣ)⁻¹ * b := by group
      _ = c * b := by rw [h2]
  have hca₀' : (a₀ : (Module.End (ZMod 2) D)ˣ) * (c : (Module.End (ZMod 2) D)ˣ) *
      (a₀ : (Module.End (ZMod 2) D)ˣ)⁻¹ = (c : (Module.End (ZMod 2) D)ˣ)⁻¹ := by
    rw [← hφ_apply, hca₀, Subgroup.coe_inv]
  have h3' : p = 3 → n = 1 := by
    intro hp3
    obtain ⟨hPcyc, hP3⟩ := h3 hp3
    have h1 : 2 ^ n = 2 ^ 1 := by rw [← hacard, h3A hPcyc hP3, pow_one]
    exact Nat.pow_right_injective le_rfl h1
  exact mixed_head_false hX hXC hXA hp hp2 hc₀C hc₀ hCgen hA2 hAc hBidx ha₀B hcB' hca₀' hacard
    ha2 hj h3' hcodim hN hUX hUC hUA hXnt (hCfaith hCsimple)

end CFSG.Quasithin.H13.NQBlock
