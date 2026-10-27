module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.F918R1

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

private theorem exists_coordR2 {V : Type} [CommGroup V] {D : FFModel} (hsec : D.sec = ⊤)
    (hker : D.ker = ⊥) {H : Subgroup (MulAut V)} {J : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H J ⊥ π) :
    ∃ c : ↥J →* D.Amb, Function.Bijective c ∧
      ∀ (γ : D.Gam) (x : ↥J) (hx : ((π γ : ↥H) : MulAut V) (x : V) ∈ J),
        c ⟨((π γ : ↥H) : MulAut V) (x : V), hx⟩ = D.act γ (c x) := by
  obtain ⟨-, -, -, -, -, hs, -, β, hβs, hβk, hβe⟩ := h
  let q : ↥D.sec ⧸ D.ker.subgroupOf D.sec →* D.Amb :=
    QuotientGroup.lift (D.ker.subgroupOf D.sec) D.sec.subtype (fun x hx => by
      have hx' : (x : D.Amb) ∈ D.ker := hx
      rw [hker, Subgroup.mem_bot] at hx'
      exact hx')
  refine ⟨q.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β x)
    have hmx : m = 1 := by
      have h1 : q (β x) = 1 := hx
      rw [← hm] at h1
      exact Subtype.ext h1
    have hβx : β x = 1 := by
      rw [← hm, hmx]
      rfl
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk x).1 hβx))
  · intro m
    have hm : m ∈ D.sec := by
      rw [hsec]
      exact Subgroup.mem_top m
    obtain ⟨x, hx⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    refine ⟨x, ?_⟩
    show q (β x) = m
    rw [hx]
    rfl
  · intro γ x hx
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β x)
    have h1 := hβe γ x m hx (hs γ m m.2) hm.symm
    show q (β _) = D.act γ (q (β x))
    rw [h1, ← hm]
    rfl

private theorem exists_vecR2 {Y : Type} [CommGroup Y] {d : ℕ} {F : Type} [Field F]
    {K : Subgroup (MulAut Y)} {π : ↥(StatedSL d F) →* ↥K} {I : Subgroup Y}
    (hI : (FFModel.nat (StatedSL d F)).RealizesVia K I ⊥ π ∨
      (FFModel.dualNat (StatedSL d F)).RealizesVia K I ⊥ π) :
    ∃ (b : Bool) (f : ↥I → Fin d → F), Function.Bijective f ∧ f 1 = 0 ∧
      (∀ k : ↥K, ∀ y ∈ I, (k : MulAut Y) y ∈ I) ∧
      ∀ (γ : ↥(StatedSL d F)) (x : ↥I) (hx : ((π γ : ↥K) : MulAut Y) (x : Y) ∈ I),
        f ⟨((π γ : ↥K) : MulAut Y) (x : Y), hx⟩ = modActR b (γ : GL (Fin d) F) (f x) := by
  rcases hI with h | h
  · obtain ⟨c, hc, hce⟩ : ∃ c : ↥I →* Multiplicative (Fin d → F), Function.Bijective c ∧
        ∀ (γ : ↥(StatedSL d F)) (x : ↥I) (hx : ((π γ : ↥K) : MulAut Y) (x : Y) ∈ I),
          c ⟨((π γ : ↥K) : MulAut Y) (x : Y), hx⟩ = natAct (StatedSL d F) γ (c x) :=
      exists_coordR2 (D := FFModel.nat (StatedSL d F)) rfl rfl h
    refine ⟨true, fun x => Multiplicative.toAdd (c x), Multiplicative.toAdd.bijective.comp hc, ?_,
      h.2.2.2.1, fun γ x hx => ?_⟩
    · show Multiplicative.toAdd (c 1) = 0
      rw [map_one, toAdd_one]
    · show Multiplicative.toAdd (c _) = _
      rw [hce γ x hx, modActR_true]
      rfl
  · obtain ⟨c, hc, hce⟩ : ∃ c : ↥I →* Multiplicative (Fin d → F), Function.Bijective c ∧
        ∀ (γ : ↥(StatedSL d F)) (x : ↥I) (hx : ((π γ : ↥K) : MulAut Y) (x : Y) ∈ I),
          c ⟨((π γ : ↥K) : MulAut Y) (x : Y), hx⟩ = dualNatAct (StatedSL d F) γ (c x) :=
      exists_coordR2 (D := FFModel.dualNat (StatedSL d F)) rfl rfl h
    refine ⟨false, fun x => Multiplicative.toAdd (c x), Multiplicative.toAdd.bijective.comp hc, ?_,
      h.2.2.2.1, fun γ x hx => ?_⟩
    · show Multiplicative.toAdd (c 1) = 0
      rw [map_one, toAdd_one]
    · show Multiplicative.toAdd (c _) = _
      rw [hce γ x hx, modActR_false]
      rfl

private theorem eq_one_of_modActR_fixR2 {d : ℕ} {F : Type} [Field F] (b : Bool) {γ : GL (Fin d) F}
    (h : ∀ x : Fin d → F, modActR b γ x = x) : γ = 1 := by
  have key : ∀ M : Matrix (Fin d) (Fin d) F, (∀ x, M *ᵥ x = x) → M = 1 := fun M hM =>
    Matrix.ext_iff_mulVec.mpr fun x => by rw [hM, Matrix.one_mulVec]
  cases b with
  | true => exact Units.ext (key _ fun x => (modActR_true γ x).symm.trans (h x))
  | false =>
    have h1 : ((γ⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ = 1 :=
      key _ fun x => (modActR_false γ x).symm.trans (h x)
    exact inv_eq_one.mp (Units.ext (Matrix.transpose_eq_one.mp h1))

theorem pi_injective_of_realizes {Y : Type} [CommGroup Y] {d : ℕ} (hd : 2 ≤ d) {F : Type} [Field F]
    {K : Subgroup (MulAut Y)} (π : ↥(StatedSL d F) →* ↥K) {I : Subgroup Y}
    (hI : (FFModel.nat (StatedSL d F)).RealizesVia K I ⊥ π ∨
      (FFModel.dualNat (StatedSL d F)).RealizesVia K I ⊥ π) : Function.Injective π := by
  have _ := hd
  obtain ⟨b, f, hf, -, -, hfe⟩ := exists_vecR2 hI
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine Subtype.ext (eq_one_of_modActR_fixR2 b fun v => ?_)
  obtain ⟨x, rfl⟩ := hf.2 v
  have hx : ((π γ : ↥K) : MulAut Y) (x : Y) ∈ I := by
    rw [hγ]
    exact x.2
  have h1 := hfe γ x hx
  have h2 : (⟨((π γ : ↥K) : MulAut Y) (x : Y), hx⟩ : ↥I) = x := by
    apply Subtype.ext
    show ((π γ : ↥K) : MulAut Y) (x : Y) = x
    rw [hγ]
    rfl
  rw [h2] at h1
  exact h1.symm

private theorem exists_componentsR2 {Y : Type} [CommGroup Y] {ι : Type} [Fintype ι] (I : ι → Subgroup Y)
    (hsup : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ ⨆ (j : ι) (_ : j ≠ i), I j = ⊥) :
    ∃ c : Y → ∀ i, ↥(I i), (∀ y, ∏ i, (c y i : Y) = y) ∧ (∀ y y', c y = c y' → y = y') ∧
      ∀ g : MulAut Y, (∀ j, ∀ x ∈ I j, g x ∈ I j) → ∀ y, g y = y →
        ∀ j, g (c y j : Y) = (c y j : Y) := by
  classical
  have hpair : Pairwise fun i j : ι => ∀ x y : Y, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => Commute.all x y
  have hPapp : ∀ c : ∀ i, ↥(I i), Subgroup.noncommPiCoprod hpair c = ∏ i, (c i : Y) := fun c => by
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hPinj : Function.Injective (Subgroup.noncommPiCoprod hpair) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep fun i => disjoint_iff.mpr (hind i)
  have hPsurj : Function.Surjective (Subgroup.noncommPiCoprod hpair) := by
    intro y
    have hy : y ∈ (Subgroup.noncommPiCoprod hpair).range := by
      rw [Subgroup.noncommPiCoprod_range, hsup]
      exact Subgroup.mem_top y
    exact hy
  refine ⟨Function.surjInv hPsurj, fun y => ?_, fun y y' h => ?_, fun g hg y hy j => ?_⟩
  · rw [← hPapp]
    exact Function.surjInv_eq hPsurj y
  · rw [← Function.surjInv_eq hPsurj y, ← Function.surjInv_eq hPsurj y', h]
  · have h1 : (fun j => (⟨g (Function.surjInv hPsurj y j : Y),
        hg j _ (Function.surjInv hPsurj y j).2⟩ : ↥(I j))) = Function.surjInv hPsurj y := by
      apply hPinj
      rw [hPapp, hPapp, ← map_prod g, ← hPapp, Function.surjInv_eq hPsurj y, hy]
    exact congrArg Subtype.val (congrFun h1 j)

theorem d35Two_card_le {Y : Type} [CommGroup Y] [Finite Y] {ι : Type} [Fintype ι] {d : ℕ}
    (hd : 3 ≤ d) {F : Type} [Field F] [Finite F] {K K' : Subgroup (MulAut Y)}
    (π : ↥(StatedSL d F) →* ↥K) (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (I : ι → Subgroup Y) (hsup : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ ⨆ (j : ι) (_ : j ≠ i), I j = ⊥)
    (hreal : ∀ i, (FFModel.nat (StatedSL d F)).RealizesVia K (I i) ⊥ π ∨
      (FFModel.dualNat (StatedSL d F)).RealizesVia K (I i) ⊥ π) :
    Nat.card ↥K' ≤ Nat.card F ^ (Fintype.card ι * Fintype.card ι) := by
  choose b f hf hf1 hinv hfe using fun i => exists_vecR2 (hreal i)
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin d → F, w ≠ 0 := ⟨Pi.single ⟨0, by omega⟩ 1, by simp⟩
  choose u hu using fun i => (hf i).2 w₀
  have hstab : ∀ i (γ : ↥(StatedSL d F)), modActR (b i) (γ : GL (Fin d) F) w₀ = w₀ →
      ((π γ : ↥K) : MulAut Y) (u i : Y) = (u i : Y) := by
    intro i γ hγ
    have h1 := hfe i γ (u i) (hinv i (π γ) (u i) (u i).2)
    rw [hu i, hγ, ← hu i] at h1
    exact congrArg Subtype.val ((hf i).1 h1)
  have htrans : ∀ i, ∀ y ∈ I i,
      y = 1 ∨ ∃ γ : ↥(StatedSL d F), ((π γ : ↥K) : MulAut Y) (u i : Y) = y := by
    intro i y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    right
    have hfy : f i ⟨y, hy⟩ ≠ 0 := by
      intro h0
      rw [← hf1 i] at h0
      exact hy1 (congrArg Subtype.val ((hf i).1 h0))
    obtain ⟨γ, hγ, hγw⟩ := exists_modActR_eq (by omega) (b i) hw₀ hfy
    refine ⟨⟨γ, hγ⟩, ?_⟩
    have h1 := hfe i ⟨γ, hγ⟩ (u i) (hinv i (π ⟨γ, hγ⟩) (u i) (u i).2)
    rw [hu i] at h1
    exact congrArg Subtype.val ((hf i).1 (h1.trans hγw))
  have hφπ : ∀ φ ∈ K', ∀ (γ : ↥(StatedSL d F)) (y : Y),
      φ (((π γ : ↥K) : MulAut Y) y) = ((π γ : ↥K) : MulAut Y) (φ y) := by
    intro φ hφ γ y
    have h1 := congrArg (fun g : MulAut Y => g y) (hcomm _ (π γ).2 φ hφ)
    simp only [MulAut.mul_apply] at h1
    exact h1.symm
  have hdet : ∀ φ ∈ K', ∀ ψ ∈ K', (∀ i, φ (u i : Y) = ψ (u i : Y)) → φ = ψ := by
    intro φ hφ ψ hψ h
    have hle : ⨆ i, I i ≤ MonoidHom.eqLocus φ.toMonoidHom ψ.toMonoidHom := by
      refine iSup_le fun i y hy => ?_
      show φ y = ψ y
      rcases htrans i y hy with rfl | ⟨γ, rfl⟩
      · rw [map_one, map_one]
      · rw [hφπ φ hφ, hφπ ψ hψ, h i]
    rw [hsup] at hle
    exact MulEquiv.ext fun y => hle (Subgroup.mem_top y)
  obtain ⟨c, -, hcinj, hcfix⟩ := exists_componentsR2 I hsup hind
  have hfix : ∀ φ ∈ K', ∀ i j, ∀ γ ∈ StatedSL d F, modActR (b i) γ w₀ = w₀ →
      modActR (b j) γ (f j (c (φ (u i : Y)) j)) = f j (c (φ (u i : Y)) j) := by
    intro φ hφ i j γ hγ hγw
    have h1 : ((π ⟨γ, hγ⟩ : ↥K) : MulAut Y) (φ (u i : Y)) = φ (u i : Y) := by
      rw [← hφπ φ hφ, hstab i ⟨γ, hγ⟩ hγw]
    have h2 := hcfix _ (fun j x hx => hinv j (π ⟨γ, hγ⟩) x hx) _ h1 j
    have hmem := hinv j (π ⟨γ, hγ⟩) _ (c (φ (u i : Y)) j).2
    have h3 := hfe j ⟨γ, hγ⟩ (c (φ (u i : Y)) j) hmem
    have h4 : (⟨((π ⟨γ, hγ⟩ : ↥K) : MulAut Y) (c (φ (u i : Y)) j : Y), hmem⟩ : ↥(I j)) =
        c (φ (u i : Y)) j := Subtype.ext h2
    rw [h4] at h3
    exact h3.symm
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥K' → ∀ p : ι × ι, {x : Fin d → F // ∀ γ ∈ StatedSL d F,
      modActR (b p.1) γ w₀ = w₀ → modActR (b p.2) γ x = x}, Function.Injective Ψ := by
    refine ⟨fun φ p => ⟨f p.2 (c ((φ : MulAut Y) (u p.1 : Y)) p.2), hfix φ φ.2 p.1 p.2⟩, ?_⟩
    intro φ ψ hφψ
    refine Subtype.ext (hdet φ φ.2 ψ ψ.2 fun i => hcinj _ _ (funext fun j => ?_))
    exact (hf j).1 (congrArg Subtype.val (congrFun hφψ (i, j)))
  calc Nat.card ↥K' ≤ Nat.card (∀ p : ι × ι, {x : Fin d → F // ∀ γ ∈ StatedSL d F,
        modActR (b p.1) γ w₀ = w₀ → modActR (b p.2) γ x = x}) :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = ∏ p : ι × ι, Nat.card {x : Fin d → F // ∀ γ ∈ StatedSL d F,
        modActR (b p.1) γ w₀ = w₀ → modActR (b p.2) γ x = x} := Nat.card_pi
    _ ≤ ∏ _p : ι × ι, Nat.card F :=
        Finset.prod_le_prod fun p _ => fix_card_le_modActR hd (b p.1) (b p.2) hw₀
    _ = Nat.card F ^ (Fintype.card ι * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod]

end CFSG.Quasithin
