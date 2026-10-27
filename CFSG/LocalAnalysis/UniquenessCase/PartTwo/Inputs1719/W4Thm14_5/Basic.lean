module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Subnormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.GH74.GLS.C3.Layer1.U1aPU1
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.StatedPSLTwo
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

theorem isBasicModule_of_isIrrOn {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Y ≠ ⊥) (hirr : IsIrrOn Y ⊤ ⊥) : IsBasicModule Y := by
  refine ⟨fun U₁ U₂ h₁ h₂ hsup => ?_, fun U hU hfaith => ?_⟩
  · rcases hirr.2.2.2 U₁ h₁ bot_le le_top with h | h
    · right
      rw [← hsup, h, bot_sup_eq]
    · exact Or.inl h
  · rcases hirr.2.2.2 U hU bot_le le_top with h | h
    · refine absurd (eq_bot_iff.mpr fun y hy => ?_) hY
      rw [Subgroup.mem_bot]
      refine hfaith y hy fun u hu => ?_
      rw [h, Subgroup.mem_bot] at hu
      rw [hu, map_one]
    · exact h

theorem iSup_map_conj_eq_self_iff {A : Type*} [Group A] {L Y : Subgroup A} (hLY : L ≤ Y) :
    (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) = L ↔ (L.subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLY]
  constructor
  · intro h y hy
    have hle : ∀ g ∈ Y, L.map (MulAut.conj g).toMonoidHom ≤ L := fun g hg =>
      (le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => L.map (MulAut.conj g).toMonoidHom) g hg
        le_rfl).trans h.le
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hmem := hle y hy (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx)
      simpa [MulAut.conj_apply] using hmem
    · intro hx
      have hmem := hle y⁻¹ (Y.inv_mem hy)
        (Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom hx)
      simpa [MulAut.conj_apply, mul_assoc] using hmem
  · intro h
    refine le_antisymm (iSup₂_le fun g hg => ?_) (le_iSup₂_of_le 1 Y.one_mem fun x hx => ?_)
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp (h hg) x).mp hx
    · exact ⟨x, hx, by simp⟩

private theorem commutator_eq_self {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

private theorem exists_ne_of_isQuasisimple {X : Type*} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : ∃ a b : X, a * b ≠ b * a := by
  have := MinDegLow.nontrivial_of_isQuasisimple hX
  by_contra h
  push Not at h
  have hcomm : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact h y x
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hxt : x ∈ commutator X := hX.1 ▸ Subgroup.mem_top x
  rw [hcomm, Subgroup.mem_bot] at hxt
  exact hx hxt

private theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hX
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

private theorem pCore_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (CFSG.pCore_normal (p := 2) (G := X)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 X :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).of_equiv
        ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
    have : Nontrivial X := IsSimpleGroup.toNontrivial
    have hnt := hP.center_nontrivial
    rw [center_eq_bot_of_isSimpleGroup hX] at hnt
    obtain ⟨a, b, hab⟩ := hnt
    exact hab (Subsingleton.elim a b)

private theorem nonempty_bar2_equiv {G : Type} [Group G] {L : Subgroup G}
    (h : CFSG.pCore 2 ↥L = ⊥) : Nonempty (Bar2 L ≃* ↥L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

private theorem pCore_eq_bot_of_o2Trivial {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hL : CFSG.Open.IsSubnormal L Y) :
    CFSG.pCore 2 ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hY : pCoreOf 2 Y = ⊥ :=
    hO2 _ hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hLle : pCoreOf 2 L ≤ pCoreOf 2 Y := A4.pCoreOf_le_of_subnormal 2 hL
  rw [hY, le_bot_iff, pCoreOf] at hLle
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hLle

private theorem hinf_eq_bot_of_isSolvable {G : Type} [Group G] {H : Subgroup G}
    (h : Group.IsSolvable ↥H) : Hinf H = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := ↥H)
  unfold Hinf CFSG.inSubgroup
  rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective, ← le_bot_iff]
  exact (iInf_le (fun k => derivedSeries ↥H k) n).trans hn.le

theorem hinf_eq_self {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) : Hinf L = L :=
  le_antisymm (uc22p21c_Hinf_le L) (uc22p21c_le_Hinf le_rfl (commutator_eq_self hL))

private theorem le_normalizer_sup {G : Type*} [Group G] {A B X : Subgroup G}
    (hA : X ≤ normalizer (A : Set G)) (hB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y ∈ X, ∀ z ∈ A ⊔ B, y * z * y⁻¹ ∈ A ⊔ B := by
    intro y hy z hz
    have hmap : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp (hA hy) a).mp ha
      · rintro _ ⟨b, hb, rfl⟩
        simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp (hB hy) b).mp hb
    simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem _ hz)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key x hx z, fun h => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ h
  simpa [mul_assoc] using this

private theorem le_normalizer_inf {G : Type*} [Group G] {A B X : Subgroup G}
    (hA : X ≤ normalizer (A : Set G)) (hB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hx) z,
    Subgroup.mem_normalizer_iff.mp (hB hx) z]

private theorem shape_bar2 {G : Type} [Group G] [Finite G] {L : Subgroup G} {e : ℕ}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hO : CFSG.pCore 2 ↥L = ⊥)
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e) :
    IsSz (Bar2 L) e ∨ IsL2 (Bar2 L) e ∨ IsSU3 (Bar2 L) e := by
  obtain ⟨φ⟩ := nonempty_bar2_equiv hO
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := CFSG.Open.IsQuasisimple.of_mulEquiv φ hL
  let ψ : Bar2 L ⧸ center (Bar2 L) ≃* ↥L ⧸ center ↥L :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  rcases hshape with h | h | h | h
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv φ.symm h))
  · exact Or.inl (LieModel.of_mulEquiv φ.symm h)
  · have := uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) h
    have hZ : center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup (exists_ne_of_isQuasisimple hL)
    let χ : ↥L ⧸ center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact Or.inr (Or.inr ⟨hq, LieModel.of_mulEquiv (ψ.trans χ).symm h⟩)
  · exact Or.inr (Or.inr ⟨hq, LieModel.of_mulEquiv ψ.symm h.2⟩)

theorem eq_of_rankOne {W : Type} [CommGroup W] [Finite W] {Y L T P : Subgroup (MulAut W)}
    {e : ℕ} (hO2 : O2Trivial Y) (hL : IsComponentOf L Y) (hT : IsSylowIn 2 T Y)
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e)
    (hPL : P ≤ L) (hinf : Hinf P ≠ ⊥)
    (hnorm : normIn T L ≤ normalizer (P : Set (MulAut W))) : P = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hO : CFSG.pCore 2 ↥L = ⊥ := pCore_eq_bot_of_o2Trivial hO2 hL.2.1
  have hTL : IsSylowIn 2 (T ⊓ L) L := F6.isSylowIn_inf_of_isSubnormal hL.2.1 hT
  have hT'L : normIn T L ⊓ L = T ⊓ L := by
    rw [normIn, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
  have hTLT' : T ⊓ L ≤ normIn T L := fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hT'TL : normIn T L ≤ normalizer ((T ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer) inf_le_right
  have hdich := kRankOneBorel_holds (normIn T L) L (P ⊔ (T ⊓ L))
    (hT.isPGroup.to_le inf_le_left) inf_le_right (hT'L ▸ hTL) (commutator_eq_self hq)
    (Or.inl ⟨e, shape_bar2 hq hO hshape⟩) (hT'L ▸ le_sup_right) (sup_le hPL inf_le_right)
    (le_normalizer_sup hnorm hT'TL)
  rcases hdich with hJN | hJL
  ·
    exfalso
    apply hinf
    apply hinf_eq_bot_of_isSolvable
    rw [hT'L] at hJN
    let S : Sylow 2 ↥L := hTL.toSylow
    have hPS : P.subgroupOf L ≤ normalizer ((S : Subgroup ↥L) : Set ↥L) := by
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hpN := Subgroup.mem_normalizer_iff.mp (hJN (le_sup_left (a := P) hp)) z
      simp only [S, IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hpN
    have := CFSG.GH74.GLS.C3.Layer1.U1a.isSolvable_normalizer_sylow_two S
    have : Group.IsSolvable ↥(P.subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPS)
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPL).surjective
  ·
    have hLN : L ≤ normalizer (P : Set (MulAut W)) := by
      rw [← hJL]
      exact sup_le Subgroup.le_normalizer (hTLT'.trans hnorm)
    have hPn : (P.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).mpr hLN
    have hsub : CFSG.Open.IsSubnormal (P.subgroupOf L) ⊤ :=
      CFSG.Open.IsSubnormal.step le_top
        ((Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ => hPn.conj_mem x hx k)
        (CFSG.Open.IsSubnormal.refl ⊤)
    rcases MinDegLow.le_center_or_eq_top_of_isSubnormal (Or.inr hq) hsub with hcen | htop
    · exfalso
      apply hinf
      apply hinf_eq_bot_of_isSolvable
      have hcomm : ∀ a b : ↥(P.subgroupOf L), a * b = b * a := fun a b =>
        Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2) (b : ↥L)).symm)
      have : Group.IsSolvable ↥(P.subgroupOf L) := Group.isSolvable_of_comm hcomm
      exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPL).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPL).surjective
    · refine le_antisymm hPL fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact this

theorem isL2_param_unique {X : Type} [Group X] [Finite X] {e f : ℕ} (he : IsL2 X e)
    (hf : IsL2 X f) : e = f := by
  have h1 := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) he
  have h2 := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hf
  have he1 : 1 ≤ e := (CFSG.Blueprint.LieModel.admissible he).2.1
  have hf1 : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible hf).2.1
  have p1 := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl he1
  have p2 := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl hf1
  have heq : ordA 1 (2 ^ e) = ordA 1 (2 ^ f) := h1.symm.trans h2
  rw [heq] at p1
  have := (p1.transfer p2).1
  simpa using this

private theorem eq_of_mem_calC {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hK : K ∈ calC L) : K = L := by
  have hKL : K ≤ L := hK.1.le
  have hsub : CFSG.Open.IsSubnormal (K.subgroupOf L) ⊤ := by
    have h := CFSG.Open.IsSubnormal.comap (f := L.subtype) hK.1
    simpa [Subgroup.subgroupOf_self] using h
  rcases MinDegLow.le_center_or_eq_top_of_isSubnormal (Or.inr hL) hsub with hcen | htop
  · exfalso
    have hperf : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL]
      exact hK.2.1
    have hbot := MinDegLow.eq_bot_of_le_center hcen hperf
    have hK0 : K = ⊥ := by
      rw [← inf_eq_left.mpr hKL, ← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
    have hq := hK.2.2
    subst hK0
    have := MinDegLow.nontrivial_of_isQuasisimple hq
    have : Subsingleton (Bar2 (⊥ : Subgroup G)) :=
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(⊥ : Subgroup G))).subsingleton
    exact not_nontrivial (Bar2 (⊥ : Subgroup G)) ‹_›
  · refine le_antisymm hKL fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact this

theorem nParam_eq_of_isL2
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {e n : ℕ}
    (hL : CFSG.Open.IsQuasisimple ↥L) (he : IsL2 ↥L e) (hn : NParam L n) : n = e := by
  classical
  have : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two he
  have hab := exists_ne_of_isQuasisimple hL
  have hZ : center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup hab
  obtain ⟨φ⟩ := nonempty_bar2_equiv (pCore_eq_bot_of_isSimpleGroup hab)
  let ψ : Bar2 L ⧸ center (Bar2 L) ≃* ↥L :=
    (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have he1 : 1 ≤ e := (CFSG.Blueprint.LieModel.admissible he).2.1
  have hcard : Nat.card ↥L = ordA 1 (2 ^ e) :=
    CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) he
  have hpA := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl he1
  rw [← hcard] at hpA
  rcases hn with hs | ⟨L₁, L₂, h₁, h₂, -, hne, -⟩
  · rcases hs with hSz' | hL2 | ⟨-, hU⟩ | ⟨-, hL3⟩ | hSp4
    ·
      have hadm := CFSG.Blueprint.LieModel.admissible hSz'
      obtain ⟨-, hn1, -, -, hodd, -⟩ := hadm
      have hc : Nat.card ↥L = CFSG.Open.ordSuzuki (2 ^ n) :=
        (Nat.card_congr φ.toEquiv).symm.trans (hSz _ n hSz')
      have hpS := CFSG.Timmesfeld.Orders.profile_ordSuzuki hn1
      rw [← hc] at hpS
      exfalso
      have h2 := ((hpA.transfer hpS).2 2 le_rfl (by norm_num)).mp
        ⟨2, by simp, ⟨e, by ring⟩⟩
      rcases h2 with ⟨-, h⟩ | h
      · exact h ⟨n, by ring⟩
      · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    · exact (isL2_param_unique he (LieModel.of_mulEquiv φ hL2)).symm
    ·
      have hU' : IsU3 ↥L n := LieModel.of_mulEquiv ψ hU
      have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hU').2.1
      have hc : Nat.card ↥L = ordTwistedA 2 (2 ^ n) :=
        CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hU'
      have hpU := CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl hn1
      rw [← hc] at hpU
      have htr := hpA.transfer hpU
      have he3 : e = 3 * n := by
        have := htr.1
        norm_num at this
        omega
      exfalso
      by_cases h2 : n = 2
      · subst h2
        have h3 := (htr.2 3 (by norm_num) (by norm_num)).mp ⟨2, by simp, ⟨4, by omega⟩⟩
        revert h3
        unfold CFSG.Timmesfeld.Orders.zU
        decide
      · have h3 := (htr.2 (3 * n) (by omega) (by omega)).mp
          ⟨2, by simp, ⟨2, by omega⟩⟩
        obtain ⟨i, hi, h⟩ := h3
        rw [Finset.mem_Icc] at hi
        obtain ⟨hi1, hi2⟩ := hi
        interval_cases i
        · rcases h with ⟨-, hd⟩ | ⟨ho, -⟩
          · have := Nat.le_of_dvd (by omega) hd
            omega
          · exact absurd ho (by decide)
        · rcases h with ⟨hev, -⟩ | ⟨-, -, hnd⟩
          · exact absurd hev (by decide)
          · exact hnd ⟨1, by ring⟩
    ·
      have hL3' : IsL3 ↥L n := LieModel.of_mulEquiv ψ hL3
      have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hL3').2.1
      have hc : Nat.card ↥L = ordA 2 (2 ^ n) :=
        CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hL3'
      have hpL3 := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hn1
      rw [← hc] at hpL3
      have htr := hpA.transfer hpL3
      have he3 : e = 3 * n := by
        have := htr.1
        norm_num at this
        omega
      exfalso
      by_cases h1 : n = 1
      · subst h1
        have he' : e = 3 := by omega
        subst he'
        have h168 : ordA 1 (2 ^ 3) = ordA 2 (2 ^ 1) := hcard.symm.trans hc
        revert h168
        decide
      · have h6 := (htr.2 (6 * n) (by omega) (by omega)).mp
          ⟨2, by simp, ⟨1, by omega⟩⟩
        obtain ⟨i, hi, hd⟩ := h6
        rw [Finset.mem_Icc] at hi
        have := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd
        nlinarith
    ·
      have hSp' : IsSp4 ↥L n := LieModel.of_mulEquiv φ hSp4
      have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hSp').2.1
      have hc : Nat.card ↥L = ordBC 2 (2 ^ n) :=
        CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hSp'
      have hpB := CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hn1
      rw [← hc] at hpB
      have htr := hpA.transfer hpB
      have he4 : e = 4 * n := by
        have := htr.1
        norm_num at this
        omega
      exfalso
      have h8 := (htr.2 (8 * n) (by omega) (by omega)).mp
        ⟨2, by simp, ⟨1, by omega⟩⟩
      obtain ⟨i, hi, hd⟩ := h8
      rw [Finset.mem_Icc] at hi
      have := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd
      nlinarith
  · exact absurd ((eq_of_mem_calC hL h₁).trans (eq_of_mem_calC hL h₂).symm) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
