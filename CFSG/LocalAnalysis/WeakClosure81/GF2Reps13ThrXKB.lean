module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement BigOperators

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_card_supp_compSet {A X Q : Subgroup (MulAut W)}
    (c : (s13SuppGraph A X Q).ConnectedComponent) :
    Nat.card ↥c.supp = (s13CompSet A X Q c).ncard := by
  rw [Nat.card_coe_set_eq, s13CompSet]
  exact (Set.ncard_image_of_injective c.supp Subtype.val_injective).symm

private theorem w16g_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ZMod 3) :
    y = ∑ V, y V • (Pi.single V (1 : ZMod 3) : ι → ZMod 3) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

private theorem w16g_linear_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ZMod 3) →ₗ[ZMod 3] ZMod 3) (y : ι → ZMod 3) :
    F y = ∑ V, y V * F (Pi.single V 1) := by
  conv_lhs => rw [w16g_sum_single y]
  simp [map_sum, map_smul]

theorem w16g_case_one_hyperplane (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 2)
    (c : (s13SuppGraph A X Q).ConnectedComponent) [Fintype ↥c.supp]
    (hQc : Q ≤ s13XSupp X (s13CompSet A X Q c))
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam) :
    ∃ f : ↥c.supp → ZMod 3, (∀ V, f V ≠ 0) ∧
      ∀ y : ↥c.supp → ZMod 3, ((∑ V, f V * y V) = 0 ↔
        ∃ x : ↥(s13XSupp X (s13CompSet A X Q c)),
          ∀ V, lam V.1 (Additive.ofMul (Subgroup.inclusion s13XSupp_le x)) = y V) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have h2 : ∀ a ∈ A, (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 2 := by
    intro a ha
    have hconj := s13Supp_conj (X := X) (L := Q) (g := a)
      (h.hXA a ha) (by simpa using h.hXA a⁻¹ (A.inv_mem ha))
    rw [hconj, Set.ncard_image_of_injective _ (Subgroup.map_injective a.injective)]
    exact he
  obtain ⟨-, -, -, hcomp⟩ := s13_graph_decomp h hQ3 h2
  let C : Set (Subgroup W) := s13CompSet A X Q c
  let L : Subgroup (MulAut W) := s13XSupp X C
  have hCsub : C ⊆ s13IsoComps X := by
    rintro U ⟨W', hW', rfl⟩
    exact W'.2
  have hCne : C.Nonempty := by
    have hsub : s13Supp X Q ⊆ C :=
      (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mp hQc
    have hne : (s13Supp X Q).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at he
      simp at he
    exact hne.mono hsub
  have hLle : L ≤ X := s13XSupp_le
  have hLlt : Nat.card ↥L < 3 ^ C.ncard :=
    s13_card_XSupp_lt h.hW hp3 hp32 h.hXe hH0 hCsub hCne
  have hLpgroup : IsPGroup 3 ↥L := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (h.hXe.2 x.1 (hLle x.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hLpgroup
  obtain ⟨-, hlow, -⟩ := hcomp c
  have hk_le : C.ncard - 1 ≤ k := by
    rw [hk] at hlow
    exact (Nat.pow_le_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hlow
  have hk_lt : k < C.ncard := by
    rw [hk] at hLlt
    exact (Nat.pow_lt_pow_iff_right (show (1:ℕ) < 3 by norm_num)).mp hLlt
  have hk_eq : k = C.ncard - 1 := by omega
  have hLcard : Nat.card ↥L = 3 ^ (C.ncard - 1) := by rw [hk, hk_eq]
  let inc : ↥L →* ↥X := Subgroup.inclusion hLle
  let φ : ↥L → (↥c.supp → ZMod 3) := fun x V => lam V.1 (Additive.ofMul (inc x))
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hcoord : ∀ U : s13IsoComps X,
        lam U (Additive.ofMul (inc x)) = lam U (Additive.ofMul (inc y)) := by
      intro U
      by_cases hU : (U : Subgroup W) ∈ C
      · obtain ⟨k', hk', hkU⟩ := hU
        have hUk : U = k' := Subtype.ext hkU.symm
        rw [hUk]
        exact congrFun hxy ⟨k', hk'⟩
      · have hx0 : lam U (Additive.ofMul (inc x)) = 0 :=
          ((hl U).2 (inc x)).mpr ((mem_s13XSupp.mp x.2).2 U.1 U.2 hU)
        have hy0 : lam U (Additive.ofMul (inc y)) = 0 :=
          ((hl U).2 (inc y)).mpr ((mem_s13XSupp.mp y.2).2 U.1 U.2 hU)
        rw [hx0, hy0]
    have hxyX : inc x = inc y :=
      coord_injective h.hW hp3 hp32 h.hXe hl hcoord
    exact Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W)) hxyX)
  let Tadd : AddSubgroup (↥c.supp → ZMod 3) :=
    { carrier := Set.range φ
      zero_mem' := ⟨1, by funext V; simp [φ]⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x * y, by funext V; simp [φ, map_mul, ofMul_mul]⟩
      neg_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x⁻¹, by funext V; simp [φ, map_inv, ofMul_inv]⟩ }
  let T : Submodule (ZMod 3) (↥c.supp → ZMod 3) := Tadd.toZModSubmodule 3
  have hT_card : Nat.card ↥T = 3 ^ (C.ncard - 1) := by
    have h1 : Nat.card ↥T = Nat.card ↥L := by
      rw [show Nat.card ↥T = Nat.card (Set.range φ) from rfl]
      exact (Nat.card_congr (Equiv.ofInjective φ hφ_inj)).symm
    rw [h1, hLcard]
  have htop_card : Nat.card (↥c.supp → ZMod 3) = 3 ^ C.ncard := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      show Fintype.card ↥c.supp = Nat.card ↥c.supp from Nat.card_eq_fintype_card.symm,
      w16g_card_supp_compSet]
  have hTlt : T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hcard_eq : Nat.card ↥T = 3 ^ C.ncard := by
      rw [htop]
      rw [show Nat.card ↥(⊤ : Submodule (ZMod 3) (↥c.supp → ZMod 3)) =
          Nat.card (↥c.supp → ZMod 3) from
        Nat.card_congr (Submodule.topEquiv (R := ZMod 3) (M := (↥c.supp → ZMod 3))).toEquiv]
      exact htop_card
    have hpow : 3 ^ (C.ncard - 1) = 3 ^ C.ncard := by rw [← hT_card, hcard_eq]
    have heq : C.ncard - 1 = C.ncard :=
      Nat.pow_right_injective (show 2 ≤ 3 by norm_num) hpow
    have hCpos : 0 < C.ncard := hCne.ncard_pos
    omega
  obtain ⟨F, hFne, hTF⟩ := Submodule.exists_le_ker_of_lt_top T hTlt
  have hT_finrank : Module.finrank (ZMod 3) T = C.ncard - 1 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 3) (V := T)
    rw [ZMod.card,
      show Fintype.card T = Nat.card ↥T from Nat.card_eq_fintype_card.symm, hT_card] at h1
    exact (Nat.pow_right_injective (show 2 ≤ 3 by norm_num) h1).symm
  have hker_finrank : Module.finrank (ZMod 3) (LinearMap.ker F) = C.ncard - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker F
    have hcardι : Fintype.card ↥c.supp = C.ncard := by
      rw [show Fintype.card ↥c.supp = Nat.card ↥c.supp from Nat.card_eq_fintype_card.symm,
        w16g_card_supp_compSet]
    have htop : Module.finrank (ZMod 3) (↥c.supp → ZMod 3) = C.ncard := by
      rw [Module.finrank_fintype_fun_eq_card, hcardι]
    have hFrange : Module.finrank (ZMod 3) (LinearMap.range F) = 1 := by
      have hle : Module.finrank (ZMod 3) (LinearMap.range F) ≤ 1 := by
        have h := Submodule.finrank_mono (le_top : LinearMap.range F ≤ ⊤)
        rwa [finrank_top, Module.finrank_self] at h
      have hpos : 1 ≤ Module.finrank (ZMod 3) (LinearMap.range F) := by
        rw [Submodule.one_le_finrank_iff]
        intro hbot
        exact hFne (LinearMap.range_eq_bot.mp hbot)
      omega
    rw [htop, hFrange] at hsum
    omega
  have hker_eq : T = LinearMap.ker F :=
    Submodule.eq_of_le_of_finrank_le hTF (by rw [hker_finrank, hT_finrank])
  let f : ↥c.supp → ZMod 3 := fun V => F (Pi.single V 1)
  refine ⟨f, ?_, ?_⟩
  · intro V hV0
    have hsingle : (Pi.single V (1 : ZMod 3)) ∈ T := by
      rw [hker_eq]
      exact LinearMap.mem_ker.mpr (by rw [show F (Pi.single V 1) = f V from rfl, hV0])
    obtain ⟨x, hx⟩ := hsingle
    have hxV : lam V.1 (Additive.ofMul (inc x)) = 1 := by
      have h := congrFun hx V
      simpa [φ] using h
    have hxW : ∀ W' : ↥c.supp, W' ≠ V → lam W'.1 (Additive.ofMul (inc x)) = 0 := by
      intro W' hWV
      have h := congrFun hx W'
      simpa [φ, Pi.single_eq_of_ne hWV] using h
    have hz1 : (inc x : MulAut W) ≠ 1 := by
      intro h1
      have h0 : lam V.1 (Additive.ofMul (inc x)) = 0 := by
        rw [show (inc x : ↥X) = 1 from Subtype.ext h1]
        simp
      rw [hxV] at h0
      exact one_ne_zero h0
    have hsupp : s13Supp X (Subgroup.zpowers (inc x : MulAut W)) = {V.1.1} := by
      ext U
      rw [Set.mem_singleton_iff]
      constructor
      · intro hU
        by_contra hne
        have hUmem : U ∈ s13IsoComps X := hU.1
        have hcoord : lam ⟨U, hUmem⟩ (Additive.ofMul (inc x)) ≠ 0 :=
          (coord_ne_zero_iff hl (inc x) ⟨U, hUmem⟩).mpr hU.2
        by_cases hUC : U ∈ C
        · obtain ⟨k', hk', hkU⟩ := hUC
          have hk'V : (⟨k', hk'⟩ : ↥c.supp) ≠ V := by
            intro hkV
            apply hne
            have hk_eq : k' = V.1 :=
              congrArg (fun w : ↥c.supp => (w.1 : ↥(s13IsoComps X))) hkV
            exact hkU.symm.trans
              (congrArg (fun w : ↥(s13IsoComps X) => (w.1 : Subgroup W)) hk_eq)
          have hzero : lam ⟨U, hUmem⟩ (Additive.ofMul (inc x)) = 0 := by
            have hUk : (⟨U, hUmem⟩ : s13IsoComps X) = k' := Subtype.ext hkU.symm
            rw [hUk]
            exact hxW ⟨k', hk'⟩ hk'V
          exact hcoord hzero
        · have hzero : lam ⟨U, hUmem⟩ (Additive.ofMul (inc x)) = 0 :=
            ((hl ⟨U, hUmem⟩).2 _).mpr ((mem_s13XSupp.mp x.2).2 U hUmem hUC)
          exact hcoord hzero
      · intro hU
        rw [hU]
        refine ⟨V.1.2, ?_⟩
        rw [← coord_ne_zero_iff hl (inc x) V.1, hxV]
        exact one_ne_zero
    exact hH0 (inc x : MulAut W) (inc x).2 hz1 (by rw [hsupp, Set.ncard_singleton])
  · intro y
    constructor
    · intro hy
      have hFy : F y = 0 := by
        rw [w16g_linear_eq_sum]
        rw [show (∑ V, y V * F (Pi.single V 1)) = ∑ V, f V * y V from
          Finset.sum_congr rfl fun V _ => by rw [show F (Pi.single V 1) = f V from rfl, mul_comm]]
        exact hy
      have hmem : y ∈ T := by
        rw [hker_eq]
        exact LinearMap.mem_ker.mpr hFy
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, fun V => congrFun hx V⟩
    · rintro ⟨x, hx⟩
      have hmem : φ x ∈ LinearMap.ker F := by
        rw [← hker_eq]
        exact ⟨x, rfl⟩
      have hF0 : F (φ x) = 0 := LinearMap.mem_ker.mp hmem
      have h3 : F (φ x) = ∑ V, (φ x) V * f V := w16g_linear_eq_sum F (φ x)
      have h4 : (∑ V, (φ x) V * f V) = ∑ V, f V * y V :=
        Finset.sum_congr rfl fun V _ => by
          rw [show (φ x) V = y V from hx V, mul_comm]
      rw [h3, h4] at hF0
      exact hF0

end CFSG.LocalAnalysis.WeakClosure81
