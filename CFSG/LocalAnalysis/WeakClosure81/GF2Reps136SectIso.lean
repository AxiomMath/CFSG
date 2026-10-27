module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectTransfer
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

section Split

variable {G H : Type*} [CommGroup G] [CommGroup H]

noncomputable def w1369_splitOfSurj (hG : ∀ x : G, x ^ 2 = 1) (hH : ∀ x : H, x ^ 2 = 1)
    (π : G →* H) (hπ : Function.Surjective π) : { s : H →* G // ∀ h, π (s h) = h } := by
  classical
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hG x.toMul
  letI : Module (ZMod 2) (Additive H) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hH x.toMul
  let πa : Additive G →+ Additive H :=
    { toFun := fun x => Additive.ofMul (π x.toMul)
      map_zero' := by
        show Additive.ofMul (π (0 : Additive G).toMul) = (0 : Additive H)
        rw [toMul_zero, map_one, ofMul_one]
      map_add' := fun x y => by
        apply Additive.ofMul.injective
        simp [toMul_add] }
  let π' : Additive G →ₗ[ZMod 2] Additive H := πa.toZModLinearMap 2
  have hπ' : Function.Surjective π' := fun y => by
    obtain ⟨x, hx⟩ := hπ y.toMul
    exact ⟨Additive.ofMul x, by simpa [π', πa] using congrArg Additive.ofMul hx⟩
  have hex : ∃ g : Additive H →ₗ[ZMod 2] Additive G, π' ∘ₗ g = LinearMap.id :=
    π'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ')
  let s : Additive H →ₗ[ZMod 2] Additive G := Classical.choose hex
  have hs : π' ∘ₗ s = LinearMap.id := Classical.choose_spec hex
  have hsmul : ∀ y : H, π ((s (Additive.ofMul y)).toMul) = y := fun y =>
    Additive.ofMul.injective (by
      have h1 := DFunLike.congr_fun hs (Additive.ofMul y)
      simpa [π', πa] using h1)
  let s' : H →* G :=
    { toFun := fun y => (s (Additive.ofMul y)).toMul
      map_one' := by
        show (s (Additive.ofMul (1 : H))).toMul = 1
        rw [show Additive.ofMul (1 : H) = 0 from rfl, map_zero]
        rfl
      map_mul' := fun a b => by
        show (s (Additive.ofMul (a * b))).toMul = (s (Additive.ofMul a)).toMul *
          (s (Additive.ofMul b)).toMul
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add,
          toMul_add] }
  exact ⟨s', hsmul⟩

end Split

private noncomputable def w1369q_mkHom (U C M : Subgroup W) (hM : M ≤ U) :
    ↥M →* ↥(w1369_im U C M) where
  toFun m :=
    ⟨QuotientGroup.mk ⟨(m : W), hM m.2⟩, by
      rw [w1369_im, Subgroup.mem_map]
      exact ⟨⟨(m : W), hM m.2⟩, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' m n := Subtype.ext rfl

private theorem w1369q_mkHom_coe (U C M : Subgroup W) (hM : M ≤ U) (m : ↥M) :
    ((w1369q_mkHom U C M hM m : ↥(w1369_im U C M)) : Sect U C) =
      QuotientGroup.mk ⟨(m : W), hM m.2⟩ := rfl

private theorem w1369q_mkHom_surj (U C M : Subgroup W) (hM : M ≤ U) :
    Function.Surjective (w1369q_mkHom U C M hM) := by
  intro y
  have hy : (y : Sect U C) ∈ w1369_im U C M := y.2
  unfold w1369_im at hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨u, hu, huy⟩ := hy
  refine ⟨⟨(u : W), Subgroup.mem_subgroupOf.mp hu⟩, Subtype.ext ?_⟩
  rw [w1369q_mkHom_coe]
  simpa using huy

private theorem w1369q_mkHom_ker (U C M : Subgroup W) (hM : M ≤ U) (m : ↥M) :
    w1369q_mkHom U C M hM m = 1 ↔ (m : W) ∈ C := by
  have hcoe : ((w1369q_mkHom U C M hM m : ↥(w1369_im U C M)) : Sect U C) =
      (QuotientGroup.mk ⟨(m : W), hM m.2⟩ : Sect U C) := rfl
  constructor
  · intro h
    have h1 : (QuotientGroup.mk ⟨(m : W), hM m.2⟩ : Sect U C) = 1 := by
      rw [← hcoe, h]
      rfl
    have h2 : (⟨(m : W), hM m.2⟩ : ↥U) ∈ C.subgroupOf U :=
      (QuotientGroup.eq_one_iff (⟨(m : W), hM m.2⟩ : ↥U)).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  · intro hm
    apply Subtype.ext
    rw [hcoe]
    change (QuotientGroup.mk ⟨(m : W), hM m.2⟩ : Sect U C) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hm

private theorem w1369q_mkHom_mem_bot_iff (U C M : Subgroup W) (hM : M ≤ U) (m : ↥M) :
    ((w1369q_mkHom U C M hM m : ↥(w1369_im U C M)) : Sect U C) ∈
      (⊥ : Subgroup (Sect U C)) ↔ (m : W) ∈ C := by
  rw [Subgroup.mem_bot]
  constructor
  · intro h
    exact (w1369q_mkHom_ker U C M hM m).mp (Subtype.ext h)
  · intro h
    rw [show w1369q_mkHom U C M hM m = 1 from
      (w1369q_mkHom_ker U C M hM m).mpr h]
    rfl

private theorem w1369q_mem_im_iff {U C M : Subgroup W} (hM : M ≤ U) {x : Sect U C} :
    x ∈ w1369_im U C M ↔
      ∃ m : ↥M, (QuotientGroup.mk ⟨(m : W), hM m.2⟩ : Sect U C) = x := by
  unfold w1369_im
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hux⟩
    exact ⟨⟨(u : W), Subgroup.mem_subgroupOf.mp hu⟩, by simpa using hux⟩
  · rintro ⟨m, rfl⟩
    exact ⟨⟨(m : W), hM m.2⟩, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩

private theorem w1369q_mk_mem_bot_iff {U C : Subgroup W} {u : ↥U} :
    (QuotientGroup.mk u : Sect U C) ∈ (⊥ : Subgroup (Sect U C)) ↔ (u : W) ∈ C := by
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  constructor
  · intro h; exact Subgroup.mem_subgroupOf.mp h
  · intro h; exact Subgroup.mem_subgroupOf.mpr h

private theorem w1369q_mk_mul_inv_mem_bot_iff {U C : Subgroup W} (u v : ↥U) :
    (QuotientGroup.mk u : Sect U C) * (QuotientGroup.mk v)⁻¹ ∈
        (⊥ : Subgroup (Sect U C)) ↔ (u : W) * (v : W)⁻¹ ∈ C := by
  rw [Subgroup.mem_bot, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_one_iff]
  constructor
  · intro h
    simpa using Subgroup.mem_subgroupOf.mp h
  · intro h
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h)

private theorem w1369q_beta_congr {A C : Subgroup W} {β : ↥A →* W}
    (hβC : ∀ a : ↥A, β a ∈ C ↔ (a : W) ∈ C) {a a' : ↥A}
    (h : (a : W) * (a' : W)⁻¹ ∈ C) : β a * (β a')⁻¹ ∈ C := by
  have hz : a * a'⁻¹ ∈ C.subgroupOf A := Subgroup.mem_subgroupOf.mpr h
  have h1 : β (a * a'⁻¹) ∈ C := (hβC (a * a'⁻¹)).mpr (Subgroup.mem_subgroupOf.mp hz)
  simpa using h1

private theorem w1369q_stable_bot {V : Type*} [CommGroup V] (X : Subgroup (MulAut V)) :
    StableUnder X (⊥ : Subgroup V) := by
  intro γ _ x hx
  rw [Subgroup.mem_bot] at hx ⊢
  rw [hx, map_one]

theorem w1369_secIsoOn_im_iff (hw2 : ∀ w : W, w ^ 2 = 1) {U C : Subgroup W}
    {Λ : Subgroup (MulAut W)} (hΛ : StabPair Λ U C) {A B : Subgroup W} (hCA : C ≤ A)
    (hAU : A ≤ U) (hCB : C ≤ B) (hBU : B ≤ U) :
    SecIsoOn (secSub U C Λ) (w1369_im U C A) ⊥ (w1369_im U C B) ⊥ ↔ SecIsoOn Λ A C B C := by
  have hCU : C ≤ U := hCA.trans hAU
  constructor
  · intro h
    obtain ⟨βbar, hβbarB, hβbarC, hβbarSurj, hβbarEquiv⟩ := h.2.2.2.2.2.2
    have hAstab : StableUnder Λ A := by
      rw [← w1369_pre_im hCA hAU]
      exact w1369_stable_pre hΛ h.2.2.1
    have hBstab : StableUnder Λ B := by
      rw [← w1369_pre_im hCB hBU]
      exact w1369_stable_pre hΛ h.2.2.2.2.1
    let ρB : ↥B →* ↥(w1369_im U C B) := w1369q_mkHom U C B hBU
    have hρB : Function.Surjective ρB := w1369q_mkHom_surj U C B hBU
    have hBexp : ∀ x : ↥B, x ^ 2 = 1 := fun x => by
      apply Subtype.ext
      simpa using hw2 (x : W)
    have hImBexp : ∀ x : ↥(w1369_im U C B), x ^ 2 = 1 := fun x => by
      apply Subtype.ext
      exact sect_exp_two hw2 U C (x : Sect U C)
    obtain ⟨sB, hsB⟩ := w1369_splitOfSurj hBexp hImBexp ρB hρB
    let βbarB : ↥(w1369_im U C A) →* ↥(w1369_im U C B) :=
      βbar.codRestrict _ hβbarB
    let fA : ↥A →* ↥(w1369_im U C A) := w1369q_mkHom U C A hAU
    let β : ↥A →* W := (Subgroup.subtype B).comp (sB.comp (βbarB.comp fA))
    have hβB : ∀ a : ↥A, β a ∈ B := fun a => (sB (βbarB (fA a))).2
    have hβcoe : ∀ a : ↥A,
        (QuotientGroup.mk (⟨β a, hBU (hβB a)⟩ : ↥U) : Sect U C) = βbar (fA a) := by
      intro a
      have h1 := hsB (βbarB (fA a))
      have h2 := congrArg (fun y : ↥(w1369_im U C B) => (y : Sect U C)) h1
      simpa [ρB, βbarB, β, w1369q_mkHom_coe] using h2
    have hβC : ∀ a : ↥A, β a ∈ C ↔ (a : W) ∈ C := by
      intro a
      rw [← w1369q_mk_mem_bot_iff (u := ⟨β a, hBU (hβB a)⟩), hβcoe a,
        hβbarC (fA a), w1369q_mkHom_mem_bot_iff U C A hAU a]
    have hβsurj : ∀ b ∈ B, ∃ a : ↥A, β a * b⁻¹ ∈ C := by
      intro b hb
      obtain ⟨x, hx⟩ := hβbarSurj (ρB ⟨b, hb⟩) (ρB ⟨b, hb⟩).2
      obtain ⟨a, rfl⟩ := w1369q_mkHom_surj U C A hAU x
      refine ⟨a, ?_⟩
      have hEq : βbar (fA a) = ((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C) := by
        have h1 : βbar (fA a) *
            (((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C))⁻¹ = 1 :=
          Subgroup.mem_bot.mp hx
        calc βbar (fA a) =
            (βbar (fA a) * (((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C))⁻¹) *
              ((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C) := by group
          _ = 1 * ((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C) := by rw [h1]
          _ = ((ρB ⟨b, hb⟩ : ↥(w1369_im U C B)) : Sect U C) := by simp
      have hmk : (QuotientGroup.mk (⟨β a, hBU (hβB a)⟩ : ↥U) : Sect U C) =
          (QuotientGroup.mk (⟨b, hBU hb⟩ : ↥U) : Sect U C) := by
        rw [hβcoe a, hEq]
        rfl
      have hdiv := QuotientGroup.eq_iff_div_mem.mp hmk
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hdiv
    have hβequiv : ∀ g ∈ Λ, ∀ a a' : ↥A, (a' : W) = g (a : W) →
        β a' * (g (β a))⁻¹ ∈ C := by
      intro g hg a a' ha'
      have hx : secAut U C g (hΛ g hg).1 (hΛ g hg).2 ∈ secSub U C Λ :=
        w1369_secAut_mem_secSub hΛ hg
      have hcond : ((fA a' : ↥(w1369_im U C A)) : Sect U C) =
          secAut U C g (hΛ g hg).1 (hΛ g hg).2
            ((fA a : ↥(w1369_im U C A)) : Sect U C) := by
        rw [w1369q_mkHom_coe, w1369q_mkHom_coe, secAut_mk]
        have hsub : (⟨(a' : W), hAU a'.2⟩ : ↥U) =
            ⟨g (a : W), (hΛ g hg).1 (a : W) (hAU a.2)⟩ := by
          apply Subtype.ext
          exact ha'
        rw [hsub]
      have hres := hβbarEquiv (secAut U C g (hΛ g hg).1 (hΛ g hg).2) hx (fA a) (fA a') hcond
      have hres' : (QuotientGroup.mk (⟨β a', hBU (hβB a')⟩ : ↥U) : Sect U C) *
          ((QuotientGroup.mk
            (⟨g (β a), (hΛ g hg).1 (β a) (hBU (hβB a))⟩ : ↥U) : Sect U C))⁻¹ ∈
          (⊥ : Subgroup (Sect U C)) := by
        rw [← hβcoe a', ← hβcoe a] at hres
        rw [secAut_mk] at hres
        exact hres
      exact (w1369q_mk_mul_inv_mem_bot_iff _ _).mp hres'
    exact ⟨hCA, hCB, hAstab, fun a ha z hz => (hΛ a ha).2 z hz, hBstab,
      fun a ha z hz => (hΛ a ha).2 z hz, β, hβB, hβC, hβsurj, hβequiv⟩
  · intro h
    obtain ⟨β, hβB, hβC, hβsurj, hβequiv⟩ := h.2.2.2.2.2.2
    let fA : ↥A →* ↥(w1369_im U C A) := w1369q_mkHom U C A hAU
    have hfA : Function.Surjective fA := w1369q_mkHom_surj U C A hAU
    let φ : ↥A →* Sect U C :=
      (QuotientGroup.mk' (C.subgroupOf U)).comp
        ((Subgroup.inclusion hBU).comp (β.codRestrict B hβB))
    have hφmk : ∀ a : ↥A,
        (QuotientGroup.mk (⟨β a, hBU (hβB a)⟩ : ↥U) : Sect U C) = φ a :=
      fun a => rfl
    have hkerφ : fA.ker ≤ φ.ker := by
      intro a ha
      rw [MonoidHom.mem_ker] at ha ⊢
      have haC : (a : W) ∈ C := (w1369q_mkHom_ker U C A hAU a).mp ha
      have hβaC : β a ∈ C := (hβC a).mpr haC
      rw [← hφmk a]
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hβaC
    let βbar : ↥(w1369_im U C A) →* Sect U C :=
      fA.liftOfRightInverse (Function.surjInv hfA) (Function.rightInverse_surjInv hfA)
        ⟨φ, hkerφ⟩
    have hβbar : ∀ a : ↥A, βbar (fA a) = φ a := fun a =>
      fA.liftOfRightInverse_comp_apply (Function.surjInv hfA)
        (Function.rightInverse_surjInv hfA) ⟨φ, hkerφ⟩ a
    refine ⟨bot_le, bot_le, w1369_stable_im hΛ h.2.2.1, w1369q_stable_bot _,
      w1369_stable_im hΛ h.2.2.2.2.1, w1369q_stable_bot _, βbar, ?_, ?_, ?_, ?_⟩
    · intro x
      obtain ⟨a, rfl⟩ := hfA x
      rw [hβbar a, ← hφmk a]
      exact (w1369q_mem_im_iff hBU).mpr ⟨⟨β a, hβB a⟩, rfl⟩
    · intro x
      obtain ⟨a, rfl⟩ := hfA x
      rw [hβbar a]
      have hleft : φ a ∈ (⊥ : Subgroup (Sect U C)) ↔ β a ∈ C := by
        rw [← hφmk a, w1369q_mk_mem_bot_iff]
      have hright : (fA a : Sect U C) ∈ (⊥ : Subgroup (Sect U C)) ↔ (a : W) ∈ C :=
        w1369q_mkHom_mem_bot_iff U C A hAU a
      rw [hleft, hright]
      exact hβC a
    · intro b hb
      obtain ⟨b0, hb0⟩ := (w1369q_mem_im_iff hBU).mp hb
      obtain ⟨a, ha⟩ := hβsurj b0 b0.2
      refine ⟨fA a, ?_⟩
      rw [hβbar a, ← hφmk a, ← hb0]
      exact (w1369q_mk_mul_inv_mem_bot_iff _ _).mpr ha
    · intro x hx a a' ha'
      obtain ⟨a0, rfl⟩ := hfA a
      obtain ⟨a0', rfl⟩ := hfA a'
      rw [w1369_mem_secSub_iff hΛ] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      have ha'' : (QuotientGroup.mk ⟨(a0' : W), hAU a0'.2⟩ : Sect U C) =
          secAut U C g (hΛ g hg).1 (hΛ g hg).2
            (QuotientGroup.mk ⟨(a0 : W), hAU a0.2⟩) := by
        rw [← w1369q_mkHom_coe U C A hAU a0', ← w1369q_mkHom_coe U C A hAU a0]
        exact ha'
      rw [secAut_mk] at ha''
      have hcong : (a0' : W) * (g (a0 : W))⁻¹ ∈ C := by
        have h1 := (QuotientGroup.eq_iff_div_mem.mp ha'')
        simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp h1
      let a1 : ↥A := ⟨g (a0 : W), h.2.2.1 g hg (a0 : W) a0.2⟩
      have hβa1 : β a1 * (g (β a0))⁻¹ ∈ C := by
        have h := hβequiv g hg a0 a1 rfl
        simpa [a1] using h
      have hβa0' : β a0' * (β a1)⁻¹ ∈ C := by
        apply w1369q_beta_congr hβC
        simpa [a1] using hcong
      have hfin : β a0' * (g (β a0))⁻¹ ∈ C := by
        have heq : β a0' * (g (β a0))⁻¹ =
            (β a0' * (β a1)⁻¹) * (β a1 * (g (β a0))⁻¹) := by group
        rw [heq]
        exact C.mul_mem hβa0' hβa1
      rw [hβbar a0', hβbar a0, ← hφmk a0', ← hφmk a0, secAut_mk]
      exact (w1369q_mk_mul_inv_mem_bot_iff _ _).mpr hfin

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
