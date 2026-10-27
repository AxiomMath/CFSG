module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16c13beta_ker_card_elemAbelianOfRank {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16c13beta_ker_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private noncomputable def s16c13beta_ker_permFun {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) : ι :=
  Classical.choose (hperm (g : MulAut T) g.2 i)

private theorem s16c13beta_ker_permFun_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16c13beta_ker_permFun hperm g i) :=
  Classical.choose_spec (hperm (g : MulAut T) g.2 i)

private theorem s16c13beta_ker_permFun_injective {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) :
    Function.Injective (s16c13beta_ker_permFun hperm g) := by
  intro i j hij
  apply hinj
  have hi := s16c13beta_ker_permFun_spec hperm g i
  have hj := s16c13beta_ker_permFun_spec hperm g j
  rw [hij] at hi
  exact Subgroup.map_injective (g : MulAut T).injective (hi.trans hj.symm)

private noncomputable def s16c13beta_ker_perm {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) : Equiv.Perm ι :=
  Equiv.ofBijective (s16c13beta_ker_permFun hperm g)
    ⟨s16c13beta_ker_permFun_injective hinj hperm g,
      (Finite.injective_iff_surjective).1 (s16c13beta_ker_permFun_injective hinj hperm g)⟩

private theorem s16c13beta_ker_perm_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16c13beta_ker_perm hinj hperm g i) :=
  s16c13beta_ker_permFun_spec hperm g i

private theorem s16c13beta_ker_perm_mul {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g h : ↥X) :
    s16c13beta_ker_perm hinj hperm (g * h) =
      s16c13beta_ker_perm hinj hperm g * s16c13beta_ker_perm hinj hperm h := by
  ext i
  apply hinj
  rw [← s16c13beta_ker_perm_spec hinj hperm (g * h) i, Equiv.Perm.mul_apply,
    ← s16c13beta_ker_perm_spec hinj hperm g (s16c13beta_ker_perm hinj hperm h i),
    ← s16c13beta_ker_perm_spec hinj hperm h i]
  rw [Subgroup.map_map]
  rfl

private noncomputable def s16c13beta_ker_rho {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) : ↥X →* Equiv.Perm ι :=
  MonoidHom.mk' (s16c13beta_ker_perm hinj hperm) (s16c13beta_ker_perm_mul hinj hperm)

private theorem s16c13beta_ker_rho_spec {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16c13beta_ker_rho hinj hperm g i) :=
  s16c13beta_ker_perm_spec hinj hperm g i

private theorem s16c13beta_ker_rho_surjective {T : Type} [CommGroup T]
    {X : Subgroup (MulAut T)} {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)) :
    Function.Surjective (s16c13beta_ker_rho hinj hperm) := by
  intro π
  obtain ⟨g, hg, hgπ⟩ := hsurj π
  refine ⟨⟨g, hg⟩, ?_⟩
  ext i
  apply hinj
  exact (s16c13beta_ker_rho_spec hinj hperm ⟨g, hg⟩ i).symm.trans (hgπ i)

theorem s16c13beta_pcore_data {T : Type} [CommGroup T] [Finite T] {X : Subgroup (MulAut T)}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i))
    (hι : 4 ≤ Fintype.card ι) :
    pCoreOf p X ≤ X ∧ IsPGroup p ↥(pCoreOf p X) ∧
      (∀ φ ∈ X, (pCoreOf p X).map (MulAut.conj φ).toMonoidHom = pCoreOf p X) ∧
      ∀ a ∈ pCoreOf p X, ∀ i, (Y i).map a.toMonoidHom = Y i := by
  classical
  let ρ : ↥X →* Equiv.Perm ι := s16c13beta_ker_rho hinj hperm
  have hρsurj : Function.Surjective ρ := s16c13beta_ker_rho_surjective hinj hperm hsurj
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact (CFSG.pCore_isPGroup (p := p) (G := ↥X)).map X.subtype
  · intro φ hφ
    let α : MulAut ↥X := X.normalizerMonoidHom ⟨φ, X.le_normalizer hφ⟩
    have hcomp : X.subtype.comp α.toMonoidHom =
        (MulAut.conj φ).toMonoidHom.comp X.subtype := by
      ext y
      simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    calc (pCoreOf p X).map (MulAut.conj φ).toMonoidHom
        = ((CFSG.pCore p ↥X).map X.subtype).map (MulAut.conj φ).toMonoidHom := rfl
      _ = (CFSG.pCore p ↥X).map ((MulAut.conj φ).toMonoidHom.comp X.subtype) := by
            rw [Subgroup.map_map]
      _ = (CFSG.pCore p ↥X).map (X.subtype.comp α.toMonoidHom) := by rw [hcomp]
      _ = ((CFSG.pCore p ↥X).map α.toMonoidHom).map X.subtype := by rw [Subgroup.map_map]
      _ = (CFSG.pCore p ↥X).map X.subtype := by
            rw [Subgroup.characteristic_iff_map_eq.mp
              (inferInstance : (CFSG.pCore p ↥X).Characteristic) α]
      _ = pCoreOf p X := rfl
  · intro a ha i
    have hQtriv_big : ∀ q : ↥X, q ∈ CFSG.pCore p ↥X → ρ q = 1 := by
      intro q hq
      have hNnorm : ((CFSG.pCore p ↥X).map ρ).Normal :=
        (inferInstance : (CFSG.pCore p ↥X).Normal).map ρ hρsurj
      have hNp : IsPGroup p ↥((CFSG.pCore p ↥X).map ρ) :=
        (CFSG.pCore_isPGroup (p := p) (G := ↥X)).map ρ
      have hbot : (CFSG.pCore p ↥X).map ρ = ⊥ :=
        s16n9b_case4_perm_normal hp hp2 hι hNnorm hNp
      have hmem : ρ q ∈ (CFSG.pCore p ↥X).map ρ := Subgroup.mem_map.2 ⟨q, hq, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.1 ha
    have h1 : (Y i).map a.toMonoidHom = Y (ρ q i) := by
      rw [← hqval]
      exact s16c13beta_ker_rho_spec hinj hperm q i
    rw [hQtriv_big q hq] at h1
    simpa using h1

theorem s16c13beta_family_data {G : Type} [Group G] [Finite G] (D : Data G)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) {p r : ℕ}
    (hp : p = 3 ∨ p = 7) (hr : 3 < r) (h4 : Case168_4At D V₀ V hV L p r) :
    ∃ (ι : Type) (_ : Fintype ι) (Y : ι → Subgroup (Vtil V₀ V hV)), iSupIndep Y ∧
      Function.Injective Y ∧ ⨆ i, Y i = ⊤ ∧ Fintype.card ι = r + 1 ∧
      (∀ i, rk ↥(Y i) = dParam p) ∧
      (∀ g ∈ Mbar D.M V₀ V hV, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) ∧
      lBar V₀ V hV L ≤ Mbar D.M V₀ V hV ∧ IsElemAbelian p (lBar V₀ V hV L) ∧
      p ^ r ≤ Nat.card ↥(lBar V₀ V hV L) ∧
      (∀ f ∈ lBar V₀ V hV L, ∀ i, (Y i).map f.toMonoidHom = Y i) ∧
      (p = 7 → ∃ Q : Subgroup (MulAut (Vtil V₀ V hV)), lBar V₀ V hV L ≤ Q ∧
        Q ≤ Mbar D.M V₀ V hV ∧ IsPGroup 7 ↥Q ∧
        (∀ φ ∈ Mbar D.M V₀ V hV, Q.map (MulAut.conj φ).toMonoidHom = Q) ∧
        ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i) := by
  classical
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ :=
    s16n9b_case4_data (X := Mbar D.M V₀ V hV) h4.2.1
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hAP : lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) :=
    s16n9b_case4_pcore D hV hc hpp (by omega) h4.1
  have hI4 : 4 ≤ Fintype.card ι := by rw [hcard]; omega
  obtain ⟨hQX, hQp, hQnorm, hQY⟩ :=
    s16c13beta_pcore_data (X := Mbar D.M V₀ V hV) hpp hp2 hinj hperm hsurj hI4
  have hLel : IsElemAbelian p (lBar V₀ V hV L) := by
    have hcp := s16c13beta_ker_rank_comm_pow h4.1
    refine ⟨isMulCommutative_iff.2 hcp.1, fun x hx => ?_⟩
    simpa using congrArg Subtype.val (hcp.2 ⟨x, hx⟩)
  have hLcard : Nat.card ↥(lBar V₀ V hV L) = p ^ r :=
    s16c13beta_ker_card_elemAbelianOfRank h4.1
  have hFY : ∀ f ∈ lBar V₀ V hV L, ∀ i, (Y i).map f.toMonoidHom = Y i :=
    fun f hf i => hQY f (hAP hf) i
  refine ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hAP.trans hQX, hLel, hLcard.ge,
    hFY, ?_⟩
  intro hp7
  subst hp7
  exact ⟨pCoreOf 7 (Mbar D.M V₀ V hV), hAP, hQX, hQp, hQnorm, hQY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
