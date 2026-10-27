module

import CFSG.RankThree.PartTwo.Sec5.Tools
import TauCeti.GroupTheory.PGroup
import CFSG.RankThree.PartTwo.Sec4.StepsBender
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nGlue1
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nFinal
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nGlue2
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
open CFSG.RankThree.PartTwo.Sec8.HeringU3n CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)

@[expose] def U3nPure : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (X : Type) [Group X] [Finite X], IsUnitaryTwo X (3 * n) →
    ∀ s : X, s ≠ 1 → s ^ 2 = 1 →
      Odd (Nat.card (Subgroup.center X)) ∧
      (∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E = 2 ^ (3 * n) → s ∈ E →
        (∀ u ∈ qOf s, ∀ x ∈ E, u * x = x * u) ∧ (∀ u ∈ qOf s, u ^ 2 = 1 → u ∈ E)) ∧
      (∀ F : Subgroup (MulAut X), IsPGroup 2 F → (∀ f ∈ F, f s = s) →
        (∀ x ∈ Subgroup.centralizer ({s} : Set X), ∀ f ∈ F,
          MulAut.conj x * f * (MulAut.conj x)⁻¹ ∈ F) →
        ∀ f ∈ F, ∃ u ∈ qOf s, f = MulAut.conj u)


theorem isUnitaryTwo_three_mul_of_isGammaIndex {G : Type} [Group G] [Finite G]
    {A X : Subgroup G} {c : G} {n m : ℕ} (h : IsGammaIndex A X c n)
    (hU : IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) :
    IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) (3 * n) := by
  have hn1 : 1 ≤ n := one_le_of_isGammaIndex h
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases h
  rcases hcases with ⟨hRee, -⟩ | ⟨htype, -⟩
  · obtain ⟨k, hk, hkn, he⟩ := hRee
    exact ((sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩).false_of_isUnitaryTwo hn1 hU).elim
  · rcases htype with hD | ⟨q, hp, hq, hG⟩ | hU' | hS | hSp
    · exact (not_isUnitaryTwo_of_isList86 hn1 (Or.inl hD) m hU).elim
    · exact (not_isUnitaryTwo_of_isList86 hn1
        (Or.inr (Or.inl (Item8KFactsProof.isoGTwoEven_of_isoGTwo hp hq hG))) m hU).elim
    · exact Or.inl hU'
    · exact Or.inr hS
    · exact (not_isUnitaryTwo_of_isList86 hn1 (Or.inr (Or.inr hSp)) m hU).elim

theorem isPGroup_rOf {G : Type} [Group G] [Finite G] (e s : G) : IsPGroup 2 (rOf e s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.pCore_isPGroup.map _

theorem rOf_le_centralizer {G : Type} [Group G] (e s : G) :
    rOf e s ≤ Subgroup.centralizer ({e, s} : Set G) :=
  Subgroup.map_subtype_le _

theorem centralizer_le_normalizer_rOf {G : Type} [Group G] [Finite G] (e s : G) :
    Subgroup.centralizer ({e, s} : Set G) ≤ Subgroup.normalizer (rOf e s : Set G) :=
  Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 (Subgroup.centralizer ({e, s} : Set G))))

theorem local_of_pure (hPure : U3nPure) (h45 : Sec4.Item4_5) (hPU : Pair84PartnerU)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    {S : Subgroup G} {s e : G} {Le : Subgroup G}
    (hset : Pair86LocalSetting G A c L a d n S s e Le) :
    rOf e s ≤ Subgroup.centralizer (S : Set G) ∧ ∀ x ∈ rOf e s, x ^ 2 = 1 → x ∈ S := by
  classical
  obtain ⟨h, hLU3, ⟨hSK, hSe, hScard, hES, hsS, hs1, hEs⟩, he, hLe⟩ := hset
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hInd : KF83Indep := kF83Indep_of kF83IndepGTwo_holds
  have hd := h.data83
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcK : ∀ k ∈ K, c * k = k * c := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL (hKL hk))).symm
  have hdK : ∀ k ∈ K, d * k = k * d := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKd hk)).symm
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hBK : B ≤ Subgroup.centralizer (K : Set G) := by
    rw [hBdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (hcK k hk).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (hdK k hk).symm
  have hsK : s ∈ K := hSK hsS
  have hs2 : s ^ 2 = 1 := hSe.2 s hsS
  obtain ⟨heB, he1, hY, hKY, hLe3⟩ : e ∈ B ∧ e ≠ 1 ∧ Le ∈ thetaComponentsAt 3 e ∧ K ≤ Le ∧
      IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) (3 * n) := by
    rcases hLe with ⟨hec, hLeL⟩ | ⟨hrel, m, hm⟩
    · subst hec
      subst hLeL
      exact ⟨Subgroup.subset_closure (by simp), h.ne_one, h.mem_thetaComponentsAt, hKL, hLU3⟩
    · obtain ⟨m', hm'⟩ := hrel.2.1
      have hecn : e ∉ Subgroup.zpowers c :=
        not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hm'
      have hec : e ≠ c := fun hh => hecn (hh ▸ Subgroup.mem_zpowers c)
      obtain ⟨heB, he1, -⟩ := he.resolve_left hec
      have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hBK heB) k hk)
      have hKres : K ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) :=
        KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
          (le_inf hKL hKe)
      have hΓ := ((hPU G A c L a d n h e Le heB hrel).2 ⟨m, hm⟩).1
      exact ⟨heB, he1, hrel.2.2.1, hKres.trans hrel.2.2.2.1,
        isUnitaryTwo_three_mul_of_isGammaIndex hΓ hm⟩
  obtain ⟨hAY, hR1, hR2, hR3⟩ := local_facts h45 hInd hO hR h heB he1 hY hKY hsK hs1 hs2
  set Y := Le with hYdef
  have hYH : Y ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have hsY : s ∈ Y := hKY hsK
  have hSY : S ≤ Y := hSK.trans hKY
  set θG : Subgroup G := inSubgroup (aschbacherSolvableCore 3) Y with hθG
  have hθGle : θG ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({e} : Set G)) := by
    rw [hθG, Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY]
    exact inf_le_right
  have hθGodd : Odd (Nat.card θG) := Odd.of_dvd_nat hR3 (Subgroup.card_dvd_of_le hθGle)
  have hθYodd : Odd (Nat.card (aschbacherSolvableCore 3 Y)) := by
    have : Nat.card θG = Nat.card (aschbacherSolvableCore 3 Y) := by
      rw [hθG, inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
    rwa [← this]
  set φ : Y →* Y ⧸ aschbacherSolvableCore 3 Y :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hφ
  have hφN : ∀ x : Y, φ x = 1 ↔ (x : G) ∈ θG := by
    intro x
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hS2g : IsPGroup 2 S := Sec5.isPGroup_of_isElemAbelian hSe
  have hSθ : S ⊓ θG = ⊥ := by
    have hθG2 : ¬ 2 ∣ Nat.card θG := by
      have := Nat.odd_iff.mp hθGodd
      omega
    rw [inf_comm]
    exact disjoint_iff.mp (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hθG2 hS2g)
  set Sb : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y) := img φ S with hSb
  have hSbcard : Nat.card Sb = 2 ^ (3 * n) := by
    rw [hSb, card_img φ hφN hθGodd hSY hS2g, hScard]
  have hSbelem : CFSG.Assembly.IsElemAbelian 2 Sb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨za, hza, hza'⟩ := (mem_img φ).mp a.2
      obtain ⟨zb, hzb, hzb'⟩ := (mem_img φ).mp b.2
      apply Subtype.ext
      change (a : Y ⧸ aschbacherSolvableCore 3 Y) * b = b * a
      rw [← hza', ← hzb', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hScomm _ hza _ hzb)
    · obtain ⟨z, hz, hz'⟩ := (mem_img φ).mp hx
      rw [← hz', ← map_pow]
      have : z ^ 2 = 1 := Subtype.ext (by simpa using hSe.2 _ hz)
      rw [this, map_one]
  set sY : Y := ⟨s, hsY⟩ with hsYdef
  have hsb : φ sY ∈ Sb := (mem_img φ).mpr ⟨sY, hsS, rfl⟩
  have hsb1 : φ sY ≠ 1 := by
    intro h1
    have hmem : s ∈ S ⊓ θG := ⟨hsS, (hφN sY).mp h1⟩
    rw [hSθ, Subgroup.mem_bot] at hmem
    exact hs1 hmem
  have hsb2 : φ sY ^ 2 = 1 := by
    rw [← map_pow]
    have : sY ^ 2 = 1 := Subtype.ext (by simpa using hs2)
    rw [this, map_one]
  obtain ⟨hZodd, hi, hii⟩ := hPure n hd.odd (Y ⧸ aschbacherSolvableCore 3 Y) hLe3 (φ sY) hsb1 hsb2
  obtain ⟨hic, hio⟩ := hi Sb hSbelem hSbcard hsb
  set R := rOf e s with hRdef
  have hR2g : IsPGroup 2 R := isPGroup_rOf e s
  have hRC : R ≤ Subgroup.centralizer ({e, s} : Set G) := rOf_le_centralizer e s
  have hRs : R ≤ Subgroup.centralizer ({s} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp (hRC hr) y (by simp)
  have hRH : R ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp (hRC hr) y (by simp)
  have hCR : ∀ g ∈ Subgroup.centralizer ({e} : Set G), g * s = s * g →
      g ∈ Subgroup.centralizer ({e, s} : Set G) := by
    intro g hg hgs
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    · exact hgs.symm
  have hRnorm : ∀ g ∈ Subgroup.centralizer ({e} : Set G), g * s = s * g →
      ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg hgs r hr =>
    (Subgroup.mem_normalizer_iff.mp (centralizer_le_normalizer_rOf e s (hCR g hg hgs)) r).mp hr
  set ρ : Subgroup.normalizer (Y : Set G) →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (thetaQuotMulAut Y).comp (compAction Y) with hρ
  have hρapply : ∀ (r : G) (hr : r ∈ Subgroup.normalizer (Y : Set G)) (l : Y),
      ρ ⟨r, hr⟩ (φ l) = φ ⟨r * l * r⁻¹, (Subgroup.mem_normalizer_iff.mp hr l).mp l.2⟩ :=
    fun r hr l => rfl
  have hρconj : ∀ (x : G) (hx : x ∈ Y),
      ρ ⟨x, Subgroup.le_normalizer hx⟩ = MulAut.conj (φ ⟨x, hx⟩) :=
    fun x hx => KFacts.thetaQuotMulAut_compAction_eq_conj hx (Subgroup.le_normalizer hx)
  set F : Subgroup (MulAut (Y ⧸ aschbacherSolvableCore 3 Y)) :=
    (R.subgroupOf (Subgroup.normalizer (Y : Set G))).map ρ with hFdef
  have hF2 : IsPGroup 2 F := hR2g.comap_subtype.map ρ
  have hFmem : ∀ r (hr : r ∈ R), ρ ⟨r, hR1 hr⟩ ∈ F := fun r hr =>
    ⟨⟨r, hR1 hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hFs : ∀ f ∈ F, f (φ sY) = φ sY := by
    rintro f ⟨⟨r, hrN⟩, hrR, rfl⟩
    have hrR' : r ∈ R := Subgroup.mem_subgroupOf.mp hrR
    have hrs : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.mp (hRs hrR')
    change ρ ⟨r, hrN⟩ (φ sY) = φ sY
    rw [hρapply]
    congr 1
    apply Subtype.ext
    change r * s * r⁻¹ = s
    rw [hrs, mul_inv_cancel_right]
  have hFnorm : ∀ xb ∈ Subgroup.centralizer ({φ sY} : Set (Y ⧸ aschbacherSolvableCore 3 Y)),
      ∀ f ∈ F, MulAut.conj xb * f * (MulAut.conj xb)⁻¹ ∈ F := by
    intro xb hxb f hf
    obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := hf
    have hrR' : r ∈ R := Subgroup.mem_subgroupOf.mp hrR
    have hcomm' : Commute (φ sY) xb := (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm
    have hsY2 : sY ^ 2 = 1 := Subtype.ext (by simpa using hs2)
    have hsY1 : sY ≠ 1 := fun h1 => hs1 (congrArg Subtype.val h1)
    have hzY : IsPGroup 2 (Subgroup.zpowers sY) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hsY2 hsY1, pow_one])
    have hkerY : ¬ 2 ∣ Nat.card φ.ker := by
      rw [hφ, QuotientGroup.ker_mk']
      have := Nat.odd_iff.mp hθYodd
      omega
    have hxbY : xb ∈ Subgroup.centralizer (((Subgroup.zpowers sY).map φ : Subgroup _) : Set _) := by
      rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact (hcomm'.zpow_left k).eq
    obtain ⟨x, hxc, hxφ⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel 2
      Nat.prime_two φ (QuotientGroup.mk'_surjective _) hkerY _ hzY xb hxbY
    have hxs : x * sY = sY * x :=
      (Subgroup.mem_centralizer_iff.mp hxc sY (Subgroup.mem_zpowers sY)).symm
    have hxs' : (x : G) * s = s * (x : G) := congrArg Subtype.val hxs
    have hxN : (x : G) ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer x.2
    have hxH : (x : G) ∈ Subgroup.centralizer ({e} : Set G) := hYH x.2
    have hxr : (x : G) * r * (x : G)⁻¹ ∈ R := hRnorm x hxH hxs' r hrR'
    have hxb' : MulAut.conj xb = ρ ⟨x, hxN⟩ := by
      rw [hρconj x x.2]
      congr 1
      exact hxφ.symm
    rw [hxb']
    have : ρ ⟨x, hxN⟩ * ρ ⟨r, hrN⟩ * (ρ ⟨x, hxN⟩)⁻¹ =
        ρ ⟨x * r * x⁻¹, hR1 hxr⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [this]
    exact hFmem _ hxr
  have hconjF : ∀ r (hr : r ∈ R), ∃ u ∈ qOf (φ sY), ρ ⟨r, hR1 hr⟩ = MulAut.conj u :=
    fun r hr => hii F hF2 hFs hFnorm _ (hFmem r hr)
  have hcent : ∀ r ∈ R, ∀ x ∈ S, r * x = x * r := by
    intro r hr x hx
    obtain ⟨u, hu, hρu⟩ := hconjF r hr
    have hxY : x ∈ Y := hSY hx
    have hxb : φ ⟨x, hxY⟩ ∈ Sb := (mem_img φ).mpr ⟨⟨x, hxY⟩, hx, rfl⟩
    have h1 : ρ ⟨r, hR1 hr⟩ (φ ⟨x, hxY⟩) = φ ⟨x, hxY⟩ := by
      rw [hρu, MulAut.conj_apply, hic u hu _ hxb]
      group
    rw [hρapply] at h1
    have h2 := (QuotientGroup.eq (s := aschbacherSolvableCore 3 Y)).mp
      (h1.symm : ((⟨x, hxY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = _)
    have h3 : x⁻¹ * (r * x * r⁻¹) ∈ θG := ⟨_, h2, rfl⟩
    have hw : r * x * r⁻¹ * x⁻¹ ∈ θG := by
      have h4 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y hxY) _).mp h3
      have h5 : x * (x⁻¹ * (r * x * r⁻¹)) * x⁻¹ = r * x * r⁻¹ * x⁻¹ := by group
      rwa [h5] at h4
    have hxs : x * s = s * x := hScomm x hx s hsS
    have h6 := commutator_eq_one_of_normal_two_group
      (H := Subgroup.centralizer ({e} : Set G))
      (Θ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)))
      (R := R) (s := s) (r := r) (x := x)
      (fun g hg => Sec6.le_normalizer_theta _ hg) (Subgroup.map_subtype_le _) hR3 hR2g hRH hRs
      hRnorm hr (hYH hxY) hxs (hθGle hw)
    calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
      _ = x * r := by rw [h6, one_mul]
  have hA : A ≤ Subgroup.centralizer ({e} : Set G) := by
    have hBA : B ≤ A := by
      rw [hBdef, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact h.mem_A
      · exact hd.d_mem
    have heA : e ∈ A := hBA heB
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx e heA)
  have hEA : Subgroup.closure ({c, a, d} : Set G) ≤ A := closure_le_of_sec8Std h
  have hom : ∀ x ∈ R, x ^ 2 = 1 → x ∈ S := by
    intro x hxR hx2
    obtain ⟨u, hu, hρu⟩ := hconjF x hxR
    have hρ2 : (ρ ⟨x, hR1 hxR⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨x, hR1 hxR⟩ : Subgroup.normalizer (Y : Set G)) ^ 2 = 1 :=
        Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    rw [hρu, ← map_pow] at hρ2
    have hu2c : u ^ 2 ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h7 := congrArg (fun f : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) => f g) hρ2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h7
      calc g * u ^ 2 = (u ^ 2 * g * (u ^ 2)⁻¹) * u ^ 2 := by rw [h7]
        _ = u ^ 2 * g := by group
    have hu2 : u ^ 2 = 1 := by
      obtain ⟨j, hj⟩ := (isPGroup_qOf (φ sY)) ⟨u, hu⟩
      have hj' : u ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      have : (u ^ 2) ^ (2 ^ j) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hj', one_pow]
      have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) := by
        have := Nat.odd_iff.mp hZodd
        omega
      exact Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_two hZ2 hu2c this
    have huS : u ∈ Sb := hio u hu hu2
    obtain ⟨z, hz, hzu⟩ := (mem_img φ).mp huS
    have hu'Y : (z : G) ∈ Y := z.2
    have hx'N : x * (z : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.mul_mem _ (hR1 hxR) (Subgroup.inv_mem _ (Subgroup.le_normalizer hu'Y))
    have hρx' : ρ ⟨x * (z : G)⁻¹, hx'N⟩ = 1 := by
      have e1 : (⟨x * (z : G)⁻¹, hx'N⟩ : Subgroup.normalizer (Y : Set G)) =
          ⟨x, hR1 hxR⟩ * (⟨(z : G), Subgroup.le_normalizer hu'Y⟩ :
            Subgroup.normalizer (Y : Set G))⁻¹ := rfl
      rw [e1, map_mul, map_inv, hρu, hρconj (z : G) hu'Y]
      have e2 : φ ⟨(z : G), hu'Y⟩ = u := hzu
      rw [e2]
      group
    have hSnormR : S ≤ Subgroup.normalizer (R : Set G) := fun g hg =>
      centralizer_le_normalizer_rOf e s (hCR g (hYH (hSY hg)) (hScomm g hg s hsS))
    have hRS2 : IsPGroup 2 (R ⊔ S : Subgroup G) := by
      have h1 := card_sup_dvd_mul_of_le_normalizer R S hSnormR
      obtain ⟨a', ha⟩ := hR2g.exists_card_eq
      obtain ⟨b', hb⟩ := hS2g.exists_card_eq
      rw [ha, hb, ← pow_add] at h1
      obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      exact IsPGroup.of_card hi'
    have hEC : Subgroup.closure ({c, a, d} : Set G) ≤
        Subgroup.normalizer (((R ⊔ S) ⊓ thetaQuotCentralizer Y : Subgroup G) : Set G) := by
      intro g hg
      have hgR : g ∈ Subgroup.normalizer (R : Set G) :=
        centralizer_le_normalizer_rOf e s
          (hCR g (hA (hEA hg)) (Subgroup.mem_centralizer_singleton_iff.mp (hEs hg)))
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨mem_normalizer_sup hgR (hES hg),
          Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y (hAY (hEA hg))⟩
    have hCbot := hR2 ((R ⊔ S) ⊓ thetaQuotCentralizer Y) (hRS2.to_le inf_le_left) inf_le_right hEC
    have hx'C : x * (z : G)⁻¹ ∈ (R ⊔ S) ⊓ thetaQuotCentralizer Y :=
      ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hxR)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right hz)),
        ⟨⟨x * (z : G)⁻¹, hx'N⟩, MonoidHom.mem_ker.mpr hρx', rfl⟩⟩
    rw [hCbot, Subgroup.mem_bot] at hx'C
    have hxz : x = (z : G) := mul_inv_eq_one.mp hx'C
    rw [hxz]
    exact hz
  exact ⟨fun r hr => Subgroup.mem_centralizer_iff.mpr fun y hy => (hcent r hr y hy).symm, hom⟩

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
