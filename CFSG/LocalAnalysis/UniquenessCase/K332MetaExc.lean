module

public import CFSG.LocalAnalysis.UniquenessCase.K332MetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Exc
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.Sporadic.J2
public import CFSG.RankThree.Coprime.SmallPrimeTorsionQuotient
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBFaithfulData
public import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
public import Certificates.Certificate3139
public import Certificates.Certificate8020
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThree.PartTwo.Sec4 (IsoGTwoPrime)

theorem sylowCenterLeOmegaComm_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SylowCenterLeOmegaComm X) : SylowCenterLeOmegaComm Y := by
  intro T x hxc hx3
  let T' : Sylow 3 X := T.comapOfInjective e.toMonoidHom e.injective
    fun y _ => ⟨e.symm y, e.apply_symm_apply y⟩
  let ψ : ↥(T' : Subgroup X) →* ↥(T : Subgroup Y) :=
    e.toMonoidHom.subgroupComap (T : Subgroup Y)
  let x' : ↥(T' : Subgroup X) := ⟨e.symm (x : Y), by
    show e (e.symm (x : Y)) ∈ (T : Subgroup Y)
    rw [e.apply_symm_apply]
    exact x.2⟩
  have hψx' : ψ x' = x := Subtype.ext (e.apply_symm_apply (x : Y))
  have hx'c : x' ∈ Subgroup.center ↥(T' : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : e (g : X) * (x : Y) = (x : Y) * e (g : X) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc (ψ g))
    apply Subtype.ext
    apply e.injective
    show e ((g : X) * e.symm (x : Y)) = e (e.symm (x : Y) * (g : X))
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h1
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    show (e.symm (x : Y)) ^ 3 = 1
    rw [← map_pow, show (x : Y) ^ 3 = 1 from congrArg Subtype.val hx3, map_one]
  have hmem := h T' x' hx'c hx'3
  have hΩ : (CFSG.omega₁ (G := ↥(T' : Subgroup X)) (p := 3)).map ψ ≤
      CFSG.omega₁ (G := ↥(T : Subgroup Y)) (p := 3) :=
    CFSG.RankThree.Coprime.map_omega₁_le ψ
  have hle : (⁅CFSG.omega₁ (G := ↥(T' : Subgroup X)) (p := 3),
      CFSG.omega₁ (G := ↥(T' : Subgroup X)) (p := 3)⁆).map ψ ≤
      ⁅CFSG.omega₁ (G := ↥(T : Subgroup Y)) (p := 3),
        CFSG.omega₁ (G := ↥(T : Subgroup Y)) (p := 3)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hΩ hΩ
  exact hle ⟨x', hmem, hψx'⟩

theorem sylowCenterLeOmegaComm_J2 :
    SylowCenterLeOmegaComm CFSG.Blueprint.NativeSporadic.J2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx3, hy3, -, -, -, hcardP, -, -, -⟩ :=
    CFSG.SectionRank.J2_sylow3_cubic_witness
  let P : Subgroup CFSG.Blueprint.NativeSporadic.J2 :=
    Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2)
  have hPcard : Nat.card P = 3 ^ 3 := hcardP
  have hPp : IsPGroup 3 P := IsPGroup.of_card hPcard
  obtain ⟨T₀, hPT₀⟩ := hPp.exists_le_sylow
  have hcardT₀ : Nat.card (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) = 3 ^ 3 := by
    have h0 : (604800 : ℕ) ≠ 0 := by norm_num
    have hfac : (604800 : ℕ).factorization 3 = 3 := by
      have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1
        (by norm_num : 3 ^ 3 ∣ 604800)
      have h2 : ¬ 4 ≤ (604800 : ℕ).factorization 3 := fun h => by
        have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
        norm_num at this
      omega
    rw [Sylow.card_eq_multiplicity T₀, CFSG.Sporadic.J2.card_J2, hfac]
  have hPT₀eq : P = (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
    Subgroup.eq_of_le_of_card_ge hPT₀ (by rw [hcardT₀, hPcard])
  have hxT₀ : x ∈ (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) := by
    rw [← hPT₀eq]
    exact Subgroup.subset_closure (by simp)
  have hyT₀ : y ∈ (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) := by
    rw [← hPT₀eq]
    exact Subgroup.subset_closure (by simp)
  intro T z hzc hz3
  let eT : ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2) ≃*
      ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2) := Sylow.equiv T₀ T
  let xT : ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2) := eT ⟨x, hxT₀⟩
  let yT : ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2) := eT ⟨y, hyT₀⟩
  have hT₀cl : Subgroup.closure
      ({⟨x, hxT₀⟩, ⟨y, hyT₀⟩} : Set ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2)) =
      ⊤ := by
    apply Subgroup.map_injective
      (f := (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2).subtype)
      (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2).subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have himage : (T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2).subtype ''
        ({⟨x, hxT₀⟩, ⟨y, hyT₀⟩} : Set ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2)) =
        ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with rfl | rfl
        · exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      · intro hz
        rcases hz with hzx | hzy
        · subst z
          exact ⟨⟨x, hxT₀⟩, Set.mem_insert_iff.mpr (Or.inl rfl), rfl⟩
        · subst z
          exact ⟨⟨y, hyT₀⟩, Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)),
            rfl⟩
    rw [himage, ← hPT₀eq]
  have hxT3 : xT ^ 3 = 1 := by
    show eT ⟨x, hxT₀⟩ ^ 3 = 1
    rw [← map_pow, show (⟨x, hxT₀⟩ : ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2)) ^ 3 =
      1 from Subtype.ext hx3, map_one]
  have hyT3 : yT ^ 3 = 1 := by
    show eT ⟨y, hyT₀⟩ ^ 3 = 1
    rw [← map_pow, show (⟨y, hyT₀⟩ : ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2)) ^ 3 =
      1 from Subtype.ext hy3, map_one]
  have hgen : Subgroup.closure
      ({xT, yT} : Set ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2)) = ⊤ := by
    rw [eq_top_iff]
    intro t ht
    clear ht
    obtain ⟨s, rfl⟩ := eT.surjective t
    have hs : s ∈ Subgroup.closure
        ({⟨x, hxT₀⟩, ⟨y, hyT₀⟩} : Set ↥(T₀ : Subgroup CFSG.Blueprint.NativeSporadic.J2)) := by
      rw [hT₀cl]
      exact Subgroup.mem_top s
    induction hs using Subgroup.closure_induction with
    | mem u hu =>
        rcases hu with hux | huy
        · subst u
          exact Subgroup.subset_closure (by simp [xT])
        · subst u
          exact Subgroup.subset_closure (by simp [yT])
    | one => simpa using Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
        rw [map_mul]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [map_inv]
        exact Subgroup.inv_mem _ iha
  have hΩT : CFSG.omega₁ (G := ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2))
      (p := 3) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine (Subgroup.closure_le (K := CFSG.omega₁
      (G := ↥(T : Subgroup CFSG.Blueprint.NativeSporadic.J2)) (p := 3))).2 ?_
    intro w hw
    rcases hw with hwx | hwy
    · subst w
      exact Subgroup.subset_closure (by simpa using hxT3)
    · subst w
      exact Subgroup.subset_closure (by simpa using hyT3)
  have hcomm := sylowCenterLeCommutator_J2 T z hzc hz3
  simpa [hΩT, commutator_def] using hcomm

variable {G : Type} [Group G] [Finite G]

theorem false_of_sylowCenterLeOmegaComm {S Z H : Subgroup G} [H.Normal]
    (hS : IsSylowOf 3 S ⊤) (hZS : Z ≤ S) (hZH : Z ≤ H) (hZ : Nat.card Z = 3)
    (hwc : IsWeaklyClosedIn Z S) {Q : Type} [Group Q] (hQ : CFSG.IsMetacyclic Q)
    (φ : ↥S →* Q) (hd : Disjoint (Z.subgroupOf S) φ.ker)
    (h : SylowCenterLeOmegaComm ↥H) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSH : IsSylowOf 3 (S ⊓ H) H :=
    hS.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top (H := H)).ge
  obtain ⟨T, hT⟩ := hSH.exists_sylow_eq_subgroupOf
  have hZne : Z ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨x, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
  have hxne : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hx3 : x ^ 3 = 1 := by
    have h1 : orderOf x ∣ 3 := hZ ▸ Subgroup.orderOf_dvd_natCard Z hxZ
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hxS : x ∈ S := hZS hxZ
  have hxH : x ∈ H := hZH hxZ
  have hcent : S ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosedPrimeCentralized.centralizes
      (p := 3) (P := S) (P₀ := Z) Nat.prime_three hS.isPGroup hZS hZ hwc
  have hTS : ∀ t : ↥(T : Subgroup ↥H), ((t : ↥H) : G) ∈ S := fun t => by
    have ht : (t : ↥H) ∈ (S ⊓ H).subgroupOf H := by rw [← hT]; exact t.2
    exact (Subgroup.mem_subgroupOf.mp ht).1
  let f : ↥(T : Subgroup ↥H) →* ↥S :=
    ((H.subtype).comp (T : Subgroup ↥H).subtype).codRestrict S hTS
  have hxT : (⟨x, hxH⟩ : ↥H) ∈ (T : Subgroup ↥H) := by
    rw [hT]
    exact Subgroup.mem_subgroupOf.mpr ⟨hxS, hxH⟩
  let xT : ↥(T : Subgroup ↥H) := ⟨⟨x, hxH⟩, hxT⟩
  have hxc : xT ∈ Subgroup.center ↥(T : Subgroup ↥H) := by
    rw [Subgroup.mem_center_iff]
    intro t
    exact Subtype.ext (Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcent (hTS t)) _ hxZ).symm)
  have hxT3 : xT ^ 3 = 1 := Subtype.ext (Subtype.ext hx3)
  let g : ↥(T : Subgroup ↥H) →* Q := φ.comp f
  have hker : ⁅CFSG.omega₁ (G := ↥(T : Subgroup ↥H)) (p := 3),
      CFSG.omega₁ (G := ↥(T : Subgroup ↥H)) (p := 3)⁆ ≤ g.ker := by
    haveI : Finite ↥(T : Subgroup ↥H) := Subtype.finite
    haveI : Finite ↥(g.range) := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
    letI : IsPGroup 3 ↥(T : Subgroup ↥H) := T.isPGroup'
    let E : Set ↥(T : Subgroup ↥H) := {u | u ^ 3 = 1}
    have hRpg : IsPGroup 3 ↥(g.range) :=
      IsPGroup.of_surjective (p := 3) T.isPGroup' g.rangeRestrict
        g.rangeRestrict_surjective
    have hRmeta : CFSG.IsMetacyclic ↥(g.range) :=
      (CFSG.GroupTheory.SteinbergBK.isMetacyclic_subgroup hQ g.range).1
    have hpair : (g '' E).Pairwise Commute := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
      have hc := commute_of_pow_three_of_isMetacyclic (R := ↥(g.range))
        (x := ⟨g a, ⟨a, rfl⟩⟩) (y := ⟨g b, ⟨b, rfl⟩⟩) hRpg hRmeta
        (by apply Subtype.ext; show (g a) ^ 3 = 1; rw [← map_pow g a, ha, map_one])
        (by apply Subtype.ext; show (g b) ^ 3 = 1; rw [← map_pow g b, hb, map_one])
      rw [commute_iff_eq]
      simpa using congrArg Subtype.val hc
    have hcommImg : IsMulCommutative
        ↥((CFSG.omega₁ (G := ↥(T : Subgroup ↥H)) (p := 3)).map g) := by
      rw [show (CFSG.omega₁ (G := ↥(T : Subgroup ↥H)) (p := 3)).map g =
          Subgroup.closure (g '' E) by
        simp [E, CFSG.omega₁, CFSG.omega, MonoidHom.map_closure]]
      exact Subgroup.isMulCommutative_closure hpair
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hcommab : Commute (g a) (g b) :=
      congrArg Subtype.val (hcommImg.is_comm.comm
        ⟨g a, Subgroup.mem_map_of_mem g ha⟩ ⟨g b, Subgroup.mem_map_of_mem g hb⟩)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcommab
  have hxker : xT ∈ g.ker := hker (h T xT hxc hxT3)
  have hgx : g xT = φ ⟨x, hxS⟩ := rfl
  have hφx : φ ⟨x, hxS⟩ = 1 := by
    rw [← hgx]
    exact MonoidHom.mem_ker.mp hxker
  have hmemZ : (⟨x, hxS⟩ : ↥S) ∈ Z.subgroupOf S := Subgroup.mem_subgroupOf.mpr hxZ
  have hmemK : (⟨x, hxS⟩ : ↥S) ∈ φ.ker := MonoidHom.mem_ker.mpr hφx
  have hone : (⟨x, hxS⟩ : ↥S) = 1 := Subgroup.disjoint_def.1 hd hmemZ hmemK
  exact hxne (congrArg Subtype.val hone)

theorem k332ExclusionMeta_of_sylowG2
    (hG2 : ∀ (X : Type) [Group X] [Finite X], IsoGTwoPrime X → SylowCenterLeOmegaComm X) :
    K332ExclusionMeta := by
  intro G _ _ S hS Z hZS hZ3 hwc Q _ hQ φ hd
  refine ⟨fun hiso => ?_, fun ⟨e⟩ => ?_⟩
  · exact false_of_sylowCenterLeOmegaComm hS hZS Subgroup.le_normalClosure hZ3 hwc hQ φ hd
      (hG2 _ hiso)
  · exact false_of_sylowCenterLeOmegaComm hS hZS Subgroup.le_normalClosure hZ3 hwc hQ φ hd
      (sylowCenterLeOmegaComm_of_mulEquiv e.symm sylowCenterLeOmegaComm_J2)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
