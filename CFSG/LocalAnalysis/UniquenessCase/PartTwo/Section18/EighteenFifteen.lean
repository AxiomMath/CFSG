module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem p_mem_piSet_of_bar (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (x : IntMod V h.hyp125.isElemAbelian) (hx0 : x.val ∉ V₀)
    (hpd : p ∣ Nat.card (ptCent (Mbar D.M V₀ V h.hyp125.isElemAbelian)
      (mkTil V₀ V h.hyp125.isElemAbelian x))) :
    p ∈ piSet (D.M ⊓ centralizer ({x.val} : Set G)) := by
  classical
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hpp : p.Prime := h.p_prime
  have hp2 : p ≠ 2 := h.p_ne_two
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have := (mSub_le_one_iff hP.elemAbelian₀).1 h.small
    omega
  obtain ⟨n, -, hn⟩ : ∃ n ≤ 2, (D.M ⊓ centralizer ({x.val} : Set G)).relIndex
      (F11.CElt D.M V₀ x.val) = 2 ^ n := by
    rcases hcase with rfl | hc
    · exact ⟨0, by norm_num, by simpa using ElevenThree.relIndex_cElt_bot D.M x.val⟩
    · exact ElevenThree.relIndex_cElt_eq_pow_two hc h4 x.val_mem hx0
  have hCs : F11.CElt D.M V₀ x.val ≤ stabTil V₀ V := fun c hc => ⟨hP.le_normalizer hc.1, hc.2.1⟩
  let f : ↥(F11.CElt D.M V₀ x.val) →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hCs)
  have hfmem : ∀ c : ↥(F11.CElt D.M V₀ x.val),
      f c ∈ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨actTil_mem_barSub V₀ V hV c.2.1 (hCs c.2), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    show actTil V₀ V hV ⟨c, hCs c.2⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact c.2.2.2
  let g : ↥(F11.CElt D.M V₀ x.val) →* ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) :=
    f.codRestrict _ hfmem
  have hg : Function.Surjective g := by
    rintro ⟨φ, hφ⟩
    obtain ⟨hφM, hφst⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
    have hfix : actTil V₀ V hV m (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      MulAction.mem_stabilizer_iff.1 hφst
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    exact ⟨⟨(m : G), hmM, stabTil_le_normalizer₀ V₀ V m.2, hfix⟩, Subtype.ext rfl⟩
  have hdC : p ∣ Nat.card (F11.CElt D.M V₀ x.val) :=
    hpd.trans (Subgroup.card_dvd_of_surjective hg)
  have hmul := Subgroup.relIndex_mul_card (D.M ⊓ centralizer ({x.val} : Set G))
    (F11.CElt D.M V₀ x.val)
  rw [hn] at hmul
  have hcop : Nat.Coprime p (2 ^ n) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp Nat.prime_two).2 hp2)
  have hd1 : p ∣ Nat.card ↥((D.M ⊓ centralizer ({x.val} : Set G)) ⊓ F11.CElt D.M V₀ x.val) := by
    rw [← hmul] at hdC
    exact hcop.dvd_of_dvd_mul_left hdC
  exact ⟨hpp, hd1.trans (Subgroup.card_dvd_of_le inf_le_left)⟩

theorem p_mem_piSet_of_mem_V₀ (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {v : G} (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    p ∈ piSet (D.M ⊓ centralizer ({v} : Set G)) := by
  classical
  have hP := h.hyp125.pairFacts
  have h2 : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hP.elemAbelian₀).1 h.small
  have heq : ∀ a ∈ V₀, a ≠ 1 → a = v := by
    intro a ha ha1
    by_contra hav
    set s : Finset G := {1, a, v} with hs
    have hscard : s.card = 3 := by
      rw [hs, Finset.card_insert_of_notMem, Finset.card_pair hav]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hv1⟩
    have hsub : (s : Set G) ⊆ (V₀ : Set G) := by
      intro z hz
      simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      exacts [one_mem V₀, ha, hv]
    have hle : (s : Set G).ncard ≤ (V₀ : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hscard, ← Nat.card_coe_set_eq] at hle
    change 3 ≤ Nat.card V₀ at hle
    omega
  have hLC : L ≤ D.M ⊓ centralizer ({v} : Set G) := by
    intro l hl
    have hlM : l ∈ D.M := h.L_le_M hl
    refine Subgroup.mem_inf.2 ⟨hlM, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : l * v * l⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 (hP.le_normalizer₀ hlM) v).1 hv
    have hne : l * v * l⁻¹ ≠ 1 := by
      intro h1
      apply hv1
      have e : v = l⁻¹ * (l * v * l⁻¹) * l := by group
      rw [e, h1]
      group
    have e := heq _ hconj hne
    have : l * v = v * l := by
      calc l * v = l * v * l⁻¹ * l := by group
        _ = v * l := by rw [e]
    exact this
  exact ⟨h.p_prime, h.p_dvd_card_L.trans (Subgroup.card_dvd_of_le hLC)⟩

theorem r18_15_of_bar (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hbar : ∀ x : IntMod V h.hyp125.isElemAbelian, x.val ∉ V₀ →
      p ∣ Nat.card (ptCent (Mbar D.M V₀ V h.hyp125.isElemAbelian)
        (mkTil V₀ V h.hyp125.isElemAbelian x))) :
    R18_15At D V₀ V p L := by
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact p_mem_piSet_of_mem_V₀ D h hv0 hv1
  · refine p_mem_piSet_of_bar D h (IntMod.mk h.hyp125.isElemAbelian ⟨v, hv⟩) ?_ ?_
    · exact hv0
    · exact hbar (IntMod.mk h.hyp125.isElemAbelian ⟨v, hv⟩) hv0

theorem r18_15_of_case2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h142 : R18_14_2At D V₀ V p L h) {s f : ℕ}
    (hs : P18_13_2 D V₀ V p L h s) (hf : 2 ≤ f)
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f) :
    R18_15At D V₀ V p L := by
  refine r18_15_of_bar D h fun x hx0 => ?_
  have h1 := (h142 ⟨s, hs⟩ f hf hO).1 x.val x.val_mem hx0
  have hle : Opp p (centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
      (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem)) ≤
      ptCent (Mbar D.M V₀ V h.hyp125.isElemAbelian) (mkTil V₀ V h.hyp125.isElemAbelian x) := by
    intro e he
    have he' : e ∈ centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
        (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem) :=
      (show Opp p (centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
          (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem)) ≤
          centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
            (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem) from
        (Subgroup.closure_le _).mpr fun _ hy => hy.1) he
    obtain ⟨he1, he2⟩ := he'
    exact ⟨barSub_mono V₀ V h.hyp125.isElemAbelian h.X_le_M he1, he2⟩
  exact h1.2.trans (Subgroup.card_dvd_of_le hle)

theorem exists_natCoords_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hN : NatSUn H ⊤ ⊥ 4 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      ∃ (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
        (ψ : W ≃* Multiplicative (Fin 4 → F)), NatCoordsSU4 H n F ε ψ := by
  classical
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := hN
  letI := hK
  haveI : Finite K := hKf
  have hinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  let πe : ↥(StatedSU 4 (2 ^ n) K) ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨β, hβsurj, hβker, hβe⟩ :=
    (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro a a' hab
    have h1 : β (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * a'⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβker (a * a'⁻¹)).1 h1
    have h3 : a * a'⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let eβ : ↥(⊤ : Subgroup W) ≃* Multiplicative (Fin 4 → K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  let up : W ≃* ↥(⊤ : Subgroup W) := Subgroup.topEquiv.symm
  let ψ : W ≃* Multiplicative (Fin 4 → K) := up.trans eβ
  refine ⟨K, hK, hKf, hK2, πe.symm, ψ, ?_⟩
  intro l s
  obtain ⟨γ, rfl⟩ : ∃ γ, πe γ = l := πe.surjective l
  rw [MulEquiv.symm_apply_apply]
  have hψ : ∀ x : W, ψ x = β ⟨x, Subgroup.mem_top x⟩ := fun x => rfl
  have hπe : ∀ γ : ↥(StatedSU 4 (2 ^ n) K), πe γ = π γ :=
    fun γ => MulEquiv.ofBijective_apply π ⟨hinj, hπ.1⟩ γ
  rw [hψ, hψ, hπe]
  exact hβe γ ⟨s, Subgroup.mem_top s⟩ (Subgroup.mem_top _)

section Certified


theorem r18_15_of_case1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h) (hs : P18_13_1 D V₀ V p L h) :
    R18_15At D V₀ V p L := by
  obtain ⟨n, hSUn, hNat⟩ := hs
  obtain ⟨-, -, hn1, -⟩ := isU4_barSub_cong h h1742 (isU4_of_isSUn_four hSUn)
  have hn2 : 2 ≤ n := by omega
  obtain ⟨F, hF, hFfin, hFcard, ε, ψ, hcoords⟩ := exists_natCoords_of_natSUn hNat
  letI : Field F := hF
  haveI : Finite F := hFfin
  refine r18_15_of_bar D h fun x hx0 => ?_
  have h1 := h141 n hn2 hSUn F hFcard ε ψ hcoords x.val x.val_mem hx0
  let C : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian)) :=
    Opp p (centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
      (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem))
  have hpow : 1 < 2 ^ n * (2 ^ (2 * n) - 1) := by
    have h2 : 1 ≤ 2 ^ (2 * n) - 1 := by
      have h3 : 2 ^ 1 ≤ 2 ^ (2 * n) :=
        Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
      omega
    have h4 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : 1 < 2)
      (h4.trans (Nat.le_mul_of_pos_right _ (by omega)))
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hcardC : Nat.card C = 1 := by rw [hbot]; simp
    have hdvd : Nat.card (Bar2 C) ∣ Nat.card C := Subgroup.card_quotient_dvd_card _
    rw [hcardC] at hdvd
    have hle : Nat.card (Bar2 C) ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    by_cases hsum : (∑ i, (Multiplicative.toAdd
        (ψ (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem))) i ^ (2 ^ n + 1)) = 0
    · have hL2 : IsL2 (Bar2 C) n := h1.2 hsum
      rw [S17.card_of_isL2 hL2] at hle
      omega
    · have hSU3 : IsSU3 (Bar2 C) n := h1.1 hsum
      haveI : Nontrivial (Bar2 C ⧸ Subgroup.center (Bar2 C)) := hSU3.1.2.1
      have hq : 1 < Nat.card (Bar2 C ⧸ Subgroup.center (Bar2 C)) := Finite.one_lt_card
      have hd2 : Nat.card (Bar2 C ⧸ Subgroup.center (Bar2 C)) ∣ Nat.card (Bar2 C) :=
        Subgroup.card_quotient_dvd_card _
      haveI : Nontrivial (Bar2 C) :=
        Finite.one_lt_card_iff_nontrivial.mp
          (lt_of_lt_of_le hq (Nat.le_of_dvd Nat.card_pos hd2))
      have hgt : 1 < Nat.card (Bar2 C) := Finite.one_lt_card
      omega
  have hpC : p ∣ Nat.card C := by
    obtain ⟨s, hs, hso⟩ := s13_exists_orderOf_of_pElementSubgroup_ne_bot h.p_prime
      (by simpa [C, Opp] using hCne)
    have h := Subgroup.orderOf_dvd_natCard C (x := s) (by simpa [C, Opp] using hs)
    rwa [hso] at h
  refine hpC.trans (Subgroup.card_dvd_of_le ?_)
  intro e he
  have he0 : e ∈ Subgroup.closure {y : MulAut (Vtil V₀ V h.hyp125.isElemAbelian) |
      y ∈ centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
        (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem) ∧
      ∃ k : ℕ, orderOf y = p ^ k} := by
    simpa [C, Opp, CFSG.RankThree.PartOne.pElementSubgroup] using he
  have he' : e ∈ centVec (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
      (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem) :=
    (Subgroup.closure_le _).mpr (fun y hy => hy.1) he0
  obtain ⟨he1, he2⟩ := (centVec.mem_centVec).1 he'
  exact ⟨barSub_mono V₀ V h.hyp125.isElemAbelian h.X_le_M he1, he2⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
