module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylowParameter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26RelIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26ComponentTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.DihedralCentralizerInvolutionConjugator
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise
open scoped commutatorElement
open scoped IsMulCommutative

namespace CFSG.GorensteinWalter

universe u

private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer_t26
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem S_le_normalizer_of_odd_centralized_inverted_t26
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    {X : Subgroup G} (hXO : X ≤ oddCoreOf c.Hhat)
    {s2 : G} (hs2I : IsInvolution s2) (hs2S : s2 ∈ (c.S : Subgroup G))
    (hs2E : s2 ∉ d.E)
    (hs2maps : ∀ x : G, x ∈ X → s2 * x * s2⁻¹ ∈ X) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have hEcentX : d.E ≤ Subgroup.normalizer (X : Set G) := by
    have hEcent : d.E ≤ Subgroup.centralizer (oddCoreOf c.Hhat : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
        (E_commutator_oddCore_eq_bot_t26 d)
    have hC : Subgroup.centralizer (oddCoreOf c.Hhat : Set G) ≤
        Subgroup.centralizer (X : Set G) :=
      Subgroup.centralizer_le hXO
    exact (hEcent.trans hC).trans (Subgroup.centralizer_le_normalizer _)
  have hs2N : s2 ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hs2maps x
    · intro hx
      have hs2inv' : s2⁻¹ = s2 :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2I.2)
      have hxback : s2 * (s2 * x * s2⁻¹) * s2⁻¹ = x := by
        rw [hs2inv']
        calc
          s2 * (s2 * x * s2) * s2 = (s2 * s2) * x * (s2 * s2) := by
            group
          _ = x := by
            have hsq : s2 * s2 = 1 := by simpa [pow_two] using hs2I.2
            rw [hsq]
            simp
      simpa [hxback] using hs2maps (s2 * x * s2⁻¹) hx
  let A : Subgroup G := (c.S : Subgroup G) ⊓ d.E
  have hA_le_E : A ≤ d.E := inf_le_right
  have hA_N : A ≤ Subgroup.normalizer (X : Set G) := hA_le_E.trans hEcentX
  have hB_le : Subgroup.zpowers s2 ≤ (c.S : Subgroup G) :=
    Subgroup.zpowers_le.mpr hs2S
  have hS_eq : A ⊔ Subgroup.zpowers s2 = (c.S : Subgroup G) := by
    let B : Subgroup G := Subgroup.zpowers s2
    have hle : A ⊔ Subgroup.zpowers s2 ≤ (c.S : Subgroup G) :=
      sup_le inf_le_left hB_le
    have hrel : d.E.relIndex (c.S : Subgroup G) = 2 :=
      S_relIndex_E_eq_two_t26 d K hK L hLnormal hLindex e
    have hrelA : A.relIndex (c.S : Subgroup G) = 2 := by
      dsimp [A]
      rw [Subgroup.inf_relIndex_left]
      exact hrel
    have hs2_not_A : s2 ∉ A := by
      intro h
      exact hs2E h.2
    apply le_antisymm hle
    obtain ⟨a, haS, haA, haAll⟩ :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and'
        (H := A) (K := (c.S : Subgroup G))).mp hrelA
    have has2 : a * s2 ∈ A := (haAll s2 hs2S).resolve_right hs2_not_A
    have haB : s2 ∈ B := by
      dsimp [B]
      exact Subgroup.mem_zpowers s2
    have haAB : a ∈ A ⊔ B := by
      have hstep : (a * s2) * s2⁻¹ = a := by group
      rw [← hstep]
      exact (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) has2)
        ((le_sup_right : B ≤ A ⊔ B) (B.inv_mem haB))
    intro b hbS
    rcases haAll b hbS with hbA | hbA
    · have hb' : a * b ∈ A := hbA
      have hstep : a⁻¹ * (a * b) = b := by group
      rw [← hstep]
      exact (A ⊔ B).mul_mem ((A ⊔ B).inv_mem haAB) ((le_sup_left : A ≤ A ⊔ B) hb')
    · exact (le_sup_left : A ≤ A ⊔ B) hbA
  -- `c.S = A ⊔ ⟨s2⟩` and both summands normalize `X`.
  rw [← hS_eq]
  exact sup_le hA_N (Subgroup.zpowers_le.mpr hs2N)

/-- Conjugating a reflected commutator subgroup by `y` (`t^y = s`) gives a
subgroup which the outer involution `s` maps into itself.  This is the
generator-level half of the dihedral normalization input; no commutativity
of the reflected subgroup is required. -/
private theorem reflected_R_conj_reflects_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (E : Subgroup G)
    {s y : G} (hsI : IsInvolution s) (hyI : IsInvolution y)
    (hyts : y * c.t * y⁻¹ = s) (htE : c.t ∈ E)
    (hts : Commute c.t s) :
    let CEs : Subgroup G := Subgroup.centralizer ({s} : Set G) ⊓ E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    let X : Subgroup G := R.map (MulAut.conj y).toMonoidHom
    ∀ z : G, z ∈ X → s * z * s⁻¹ ∈ X := by
  classical
  intro CEs R X
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hss : s * s = 1 := by simpa [pow_two] using hsI.2
  let f : G →* G := (MulAut.conj s).toMonoidHom
  let CEsy : Subgroup G := CEs.map (MulAut.conj y).toMonoidHom
  have hmapR : R.map (MulAut.conj y).toMonoidHom =
      ⁅Subgroup.zpowers s, CEsy⁆ := by
    dsimp [R, CEs, CEsy]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hyts]
  let Pre : Subgroup G := Subgroup.comap f X
  have hσa : ∀ a : G, a ∈ Subgroup.zpowers s → f a ∈ Subgroup.zpowers s := by
    intro a ha
    have hs_norm : s ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers (s * s * s⁻¹) = Subgroup.zpowers s
      rw [show s⁻¹ = s by
        exact inv_eq_of_mul_eq_one_right hss]
      simp [hss]
    exact (Subgroup.mem_normalizer_iff.mp hs_norm a).1 ha
  have hσb : ∀ b : G, b ∈ CEsy → f b ∈ CEsy := by
    intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨c0, hc, hbc⟩
    have hcC : c0 ∈ Subgroup.centralizer ({s} : Set G) :=
      (inf_le_left : CEs ≤ Subgroup.centralizer ({s} : Set G)) hc
    have hcE : c0 ∈ E := (inf_le_right : CEs ≤ E) hc
    have hcs : c0 * s = s * c0 := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hctC : c.t * c0 * c.t⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (c.t * c0 * c.t⁻¹) * s = c.t * c0 * (c.t⁻¹ * s) := by group
        _ = c.t * c0 * (s * c.t⁻¹) := by
          rw [(Commute.inv_left hts).eq]
        _ = c.t * (c0 * s) * c.t⁻¹ := by group
        _ = c.t * (s * c0) * c.t⁻¹ := by rw [hcs]
        _ = s * (c.t * c0 * c.t⁻¹) := by
          calc
            c.t * (s * c0) * c.t⁻¹ = (c.t * s) * c0 * c.t⁻¹ := by group
            _ = (s * c.t) * c0 * c.t⁻¹ := by rw [hts.eq]
            _ = s * (c.t * c0 * c.t⁻¹) := by group
    have hctE : c.t * c0 * c.t⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem htE hcE) (E.inv_mem htE)
    have hctCs : c.t * c0 * c.t⁻¹ ∈ CEs := ⟨hctC, hctE⟩
    have hbval : b = y * c0 * y⁻¹ := by
      simpa [MulAut.conj_apply] using hbc.symm
    have hfb : f b = y * (c.t * c0 * c.t⁻¹) * y⁻¹ := by
      rw [hbval]
      dsimp [f]
      change s * (y * c0 * y⁻¹) * s⁻¹ = y * (c.t * c0 * c.t⁻¹) * y⁻¹
      calc
        s * (y * c0 * y⁻¹) * s⁻¹
            = (y * c.t * y⁻¹) * (y * c0 * y⁻¹) * (y * c.t * y⁻¹)⁻¹ := by
              rw [← hyts]
        _ = y * (c.t * c0 * c.t⁻¹) * y⁻¹ := by group
    exact Subgroup.mem_map.mpr ⟨c.t * c0 * c.t⁻¹, hctCs, hfb.symm⟩
  have hgen : ∀ a : G, a ∈ Subgroup.zpowers s → ∀ b : G, b ∈ CEsy →
      ⁅a,b⁆ ∈ Pre := by
    intro a ha b hb
    rw [Subgroup.mem_comap]
    change f ⁅a,b⁆ ∈ X
    have hfcomm : f ⁅a,b⁆ = ⁅f a, f b⁆ := by
      dsimp [f, commutatorElement_def]
      change s * (a * b * a⁻¹ * b⁻¹) * s⁻¹ =
        (s * a * s⁻¹) * (s * b * s⁻¹) * (s * a * s⁻¹)⁻¹ *
          (s * b * s⁻¹)⁻¹
      group
    rw [hfcomm]
    have hmem : ⁅f a, f b⁆ ∈ ⁅Subgroup.zpowers s, CEsy⁆ :=
      Subgroup.commutator_mem_commutator (hσa a ha) (hσb b hb)
    simpa [X, hmapR] using hmem
  have hX_le_Pre : X ≤ Pre := by
    change R.map (MulAut.conj y).toMonoidHom ≤ Pre
    rw [hmapR]
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    exact hgen a ha b hb
  intro z hz
  exact Subgroup.mem_comap.mp (hX_le_Pre hz)

/-- If a Sylow `p`-subgroup of `G` lies in a subgroup `C`, then the
`p`-factor of `|C|` agrees with the Sylow order. -/
private lemma sylow_card_factorization_eq_of_le_t26
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (C : Subgroup G) (P : Sylow p G) (hPC : (P : Subgroup G) ≤ C) :
    (Nat.card C).factorization p = (Nat.card (P : Subgroup G)).factorization p := by
  apply le_antisymm
  · have hC_G : Nat.card C ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card C
    have hCle : (Nat.card C).factorization p ≤ (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd (Nat.card_pos (α := C)).ne'
        (Nat.card_pos (α := G)).ne').2 hC_G p
    have hPfacG : (Nat.card (P : Subgroup G)).factorization p =
        (Nat.card G).factorization p := by
      rw [P.card_eq_multiplicity, Nat.factorization_pow_self Fact.out]
    rw [← hPfacG] at hCle
    exact hCle
  · have hP_C : Nat.card (P : Subgroup G) ∣ Nat.card C :=
      Subgroup.card_dvd_of_le hPC
    exact (Nat.factorization_le_iff_dvd (Nat.card_pos (α := P)).ne'
      (Nat.card_pos (α := C)).ne').2 hP_C p

private lemma mem_conjugateSubgroup_iff_t26 {G : Type u} [Group G]
    (H : Subgroup G) (g x : G) :
    x ∈ conjugateSubgroup H g ↔ ∃ h ∈ H, x = g * h * g⁻¹ := by
  rw [conjugateSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

private lemma natCard_conjugateSubgroup_t26 {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    Nat.card (conjugateSubgroup H g) = Nat.card H := by
  rw [conjugateSubgroup, Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- An element of `H` which centralizes `z` and normalizes `E` also
normalizes `C_E(z)`. -/
private lemma mem_normalizer_inf_centralizer_E_of_mem_Hhat_commute_t26
    {G : Type u} [Group G] (E H : Subgroup G)
    (hEamb : ∀ {h x : G}, h ∈ H → x ∈ E → h * x * h⁻¹ ∈ E)
    {z h : G} (hh : h ∈ H)
    (hz : h ∈ Subgroup.centralizer ({z} : Set G)) :
    h ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({z} : Set G) ⊓ E : Subgroup G) : Set G) := by
  let Cz : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let C : Subgroup G := Cz ⊓ E
  have hconj (a : G) (ha : a ∈ H) (haz : a ∈ Cz) :
      ∀ y : G, y ∈ C → a * y * a⁻¹ ∈ C := by
    intro y hy
    rcases hy with ⟨hyC, hyE⟩
    constructor
    · change a * y * a⁻¹ ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hazcomm : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haz
      have hycomm : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hazinv : a⁻¹ * z = z * a⁻¹ := by
        have h : a * (a⁻¹ * z) = a * (z * a⁻¹) := by
          calc
            a * (a⁻¹ * z) = z := by group
            _ = (z * a) * a⁻¹ := by group
            _ = (a * z) * a⁻¹ := by rw [← hazcomm]
            _ = a * (z * a⁻¹) := by group
        exact mul_left_cancel h
      calc
        (a * y * a⁻¹) * z = a * y * (a⁻¹ * z) := by group
        _ = a * y * (z * a⁻¹) := by rw [hazinv]
        _ = a * (y * z) * a⁻¹ := by group
        _ = a * (z * y) * a⁻¹ := by rw [hycomm]
        _ = (a * z) * y * a⁻¹ := by group
        _ = (z * a) * y * a⁻¹ := by rw [hazcomm]
        _ = z * (a * y * a⁻¹) := by group
    · exact hEamb ha hyE
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj h hh hz x
  · intro hx
    have hx' : h⁻¹ * (h * x * h⁻¹) * h ∈ C := by
      simpa using hconj h⁻¹ (H.inv_mem hh) (Cz.inv_mem hz) (h * x * h⁻¹) hx
    have hx'' : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    simpa [hx'', C] using hx'

/-- Given a Sylow subgroup of `G` inside `N ∩ C`, extend a `p`-subgroup `V`
of that intersection to a Sylow subgroup of `C` which still lies in `N`. -/
private theorem exists_sylow_in_normalizer_containing_t26
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N C : Subgroup G) (P : Sylow p G)
    (hPC : (P : Subgroup G) ≤ C) (hPN : (P : Subgroup G) ≤ N)
    (V : Subgroup G) (hVN : V ≤ N) (hVC : V ≤ C) (hVp : IsPGroup p V) :
    ∃ Q : Sylow p C,
      ((Q : Subgroup C).map C.subtype) ≤ N ∧
        V ≤ ((Q : Subgroup C).map C.subtype) := by
  classical
  let M : Subgroup G := N ⊓ C
  have hVleM : V ≤ M := le_inf hVN hVC
  let VM : Subgroup M := V.subgroupOf M
  have hVMp : IsPGroup p VM :=
    IsPGroup.of_equiv hVp (Subgroup.subgroupOfEquivOfLe hVleM).symm
  obtain ⟨QM, hVleQM⟩ := hVMp.exists_le_sylow (G := M)
  let QG : Subgroup G := (QM : Subgroup M).map M.subtype
  have hQGM : QG ≤ M := Subgroup.map_subtype_le (QM : Subgroup M)
  have hQGC : QG ≤ C := hQGM.trans (inf_le_right : M ≤ C)
  have hQGN : QG ≤ N := hQGM.trans (inf_le_left : M ≤ N)
  have hMfacC : (Nat.card M).factorization p = (Nat.card C).factorization p := by
    have hPM : (P : Subgroup G) ≤ M := le_inf hPN hPC
    exact (sylow_card_factorization_eq_of_le_t26 M P hPM).trans
      (sylow_card_factorization_eq_of_le_t26 C P hPC).symm
  have hQGcard : Nat.card QG = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    rw [QM.card_eq_multiplicity, hMfacC]
  let Q0 : Subgroup C := QG.subgroupOf C
  have hQ0card : Nat.card Q0 = p ^ (Nat.card C).factorization p := by
    rw [← hQGcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQGC).toEquiv
  let Q : Sylow p C := Sylow.ofCard Q0 hQ0card
  have hQmap : ((Q : Subgroup C).map C.subtype) = QG := by
    simp [Q, Q0, Subgroup.map_subgroupOf_eq_of_le hQGC]
  refine ⟨Q, ?_, ?_⟩
  · rw [hQmap]
    exact hQGN
  · rw [hQmap]
    intro v hv
    have hvM : v ∈ M := hVleM hv
    have hvVM : (⟨v, hvM⟩ : M) ∈ VM := Subgroup.mem_subgroupOf.mpr hv
    have hvQM : (⟨v, hvM⟩ : M) ∈ (QM : Subgroup M) := hVleQM hvVM
    exact Subgroup.mem_map.mpr ⟨⟨v, hvM⟩, hvQM, rfl⟩

/-- The `C_G(ts)`-conjugator can be chosen inside any prescribed Sylow
subgroup of `C_G(ts)` which contains the Klein four `⟨t,s⟩`. -/
private theorem exists_theorem26_product_centralizer_conjugator_in_sylow_t26
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hm2 : 2 ≤ c.m)
    (s : G) (hsI : IsInvolution s)
    (hts : Commute c.t s) (htsne : c.t ≠ s)
    (Q : Sylow 2 (Subgroup.centralizer ({c.t * s} : Set G)))
    (hV : (Subgroup.zpowers c.t ⊔ Subgroup.zpowers s).subgroupOf
      (Subgroup.centralizer ({c.t * s} : Set G)) ≤
      (Q : Subgroup (Subgroup.centralizer ({c.t * s} : Set G)))) :
    ∃ y : G, IsInvolution y ∧
      y * c.t * y⁻¹ = s ∧
      y ∈ ((Q : Subgroup (Subgroup.centralizer ({c.t * s} : Set G))).map
        (Subgroup.centralizer ({c.t * s} : Set G)).subtype) := by
  classical
  have htt : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
  have hss : s * s = 1 := by simpa [pow_two] using hsI.2
  have hprodSq : (c.t * s) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (c.t * s) * (c.t * s) = c.t * (s * c.t) * s := by group
      _ = c.t * (c.t * s) * s := by rw [← hts.eq]
      _ = (c.t * c.t) * (s * s) := by group
      _ = 1 := by rw [htt, hss]; simp
  have hprodNe : c.t * s ≠ 1 := by
    intro hprod
    apply htsne
    calc
      c.t = c.t * 1 := by simp
      _ = c.t * (s * s) := by rw [hss]
      _ = (c.t * s) * s := by group
      _ = 1 * s := by rw [hprod]
      _ = s := by simp
  have hprodI : IsInvolution (c.t * s) := ⟨hprodNe, hprodSq⟩
  obtain ⟨a, ha⟩ :=
    fact_2_preamble_involutions_conjugate_proved
      hmin (c.t * s) c.t hprodI c.t_involution
  let Sa : Subgroup G := conjugateSubgroup (c.S : Subgroup G) a⁻¹
  have hSaC : Sa ≤ Subgroup.centralizer ({c.t * s} : Set G) := by
    intro x hx
    rcases (mem_conjugateSubgroup_iff_t26 (c.S : Subgroup G) a⁻¹ x).mp hx with
      ⟨q, hqS, rfl⟩
    have hqC : q ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact S_le_H c hqS
    have hqcomm : q * c.t = c.t * q :=
      Subgroup.mem_centralizer_singleton_iff.mp hqC
    have hback : c.t * s = a⁻¹ * c.t * a := by
      calc
        c.t * s = a⁻¹ * (a * (c.t * s) * a⁻¹) * a := by group
        _ = a⁻¹ * c.t * a := by rw [ha]
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [inv_inv]
    rw [hback]
    calc
      (a⁻¹ * q * a) * (a⁻¹ * c.t * a) =
          a⁻¹ * (q * c.t) * a := by group
      _ = a⁻¹ * (c.t * q) * a := by rw [hqcomm]
      _ = (a⁻¹ * c.t * a) * (a⁻¹ * q * a) := by group
  obtain ⟨eS⟩ := c.dihedralEquiv
  have hScard : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m :=
    (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have h8S : 8 ∣ Nat.card (↥(c.S : Subgroup G)) := by
    rw [hScard]
    have hpow : 2 ^ 3 ∣ 2 ^ (c.m + 1) :=
      pow_dvd_pow 2 (by omega)
    simpa [pow_succ'] using hpow
  have h8C : 8 ∣ Nat.card
      (Subgroup.centralizer ({c.t * s} : Set G)) := by
    have hdvd := Subgroup.card_dvd_of_le hSaC
    rw [natCard_conjugateSubgroup_t26] at hdvd
    exact h8S.trans hdvd
  exact
    exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow_in_sylow
      c.S eS c.t s c.t_involution hsI hts htsne h8C Q hV

/-- Conjugating the fixed Sylow back from `C_G(t)` gives a Sylow subgroup
inside `C_G(s)` when `t^g = s`. -/
private lemma conjugate_sylow_le_centralizer_of_conj_ts_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {g s : G} (hgI : IsInvolution g)
    (hgt : g * c.t * g⁻¹ = s) :
    conjugateSubgroup (c.S : Subgroup G) g⁻¹ ≤
      Subgroup.centralizer ({s} : Set G) := by
  have hSleCt : (c.S : Subgroup G) ≤ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact S_le_H c
  have hg2 : g * g = 1 := by simpa [pow_two] using hgI.2
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hsval : s = g * c.t * g := by
    calc
      s = g * c.t * g⁻¹ := hgt.symm
      _ = g * c.t * g := by rw [hginv]
  intro u hu
  rcases (mem_conjugateSubgroup_iff_t26 (c.S : Subgroup G) g⁻¹ u).mp hu with
    ⟨x, hxS, rfl⟩
  simp only [inv_inv]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxCt : x ∈ Subgroup.centralizer ({c.t} : Set G) := hSleCt hxS
  have hxcomm : x * c.t = c.t * x := Subgroup.mem_centralizer_singleton_iff.mp hxCt
  calc
    (g⁻¹ * x * g) * s = (g⁻¹ * x * g) * (g * c.t * g) := by rw [hsval]
    _ = (g * x * g) * (g * c.t * g) := by rw [hginv]
    _ = g * x * (g * g) * c.t * g := by group
    _ = g * x * c.t * g := by rw [hg2]; simp
    _ = g * (x * c.t) * g := by group
    _ = g * (c.t * x) * g := by rw [hxcomm]
    _ = (g * c.t * g) * (g * x * g) := by
      calc
        g * (c.t * x) * g = g * c.t * x * g := by group
        _ = g * c.t * 1 * x * g := by simp
        _ = g * c.t * (g * g) * x * g := by rw [← hg2]
        _ = (g * c.t * g) * (g * x * g) := by group
    _ = s * (g⁻¹ * x * g) := by rw [hsval, hginv]

/-- If `S` normalizes `R^g`, then `S^(g⁻¹)` normalizes `R`. -/
private lemma conjugate_sylow_le_normalizer_of_normalizes_conjugate_t26
    {G : Type u} [Group G] [Finite G]
    (S R : Subgroup G) {g : G} (hgI : IsInvolution g)
    (hSN : S ≤ Subgroup.normalizer
      (R.map (MulAut.conj g).toMonoidHom : Set G)) :
    conjugateSubgroup S g⁻¹ ≤ Subgroup.normalizer (R : Set G) := by
  intro u hu
  rcases (mem_conjugateSubgroup_iff_t26 S g⁻¹ u).mp hu with
    ⟨s, hsS, rfl⟩
  simp only [inv_inv]
  have hsN : s ∈ Subgroup.normalizer (R.map (MulAut.conj g).toMonoidHom : Set G) :=
    hSN hsS
  let u : G := g⁻¹ * s * g
  have hforward (a : G) (ha : a ∈ S) :
      ∀ x : G, x ∈ R → (g⁻¹ * a * g) * x * (g⁻¹ * a * g)⁻¹ ∈ R := by
    intro x hx
    have haN : a ∈ Subgroup.normalizer
        (R.map (MulAut.conj g).toMonoidHom : Set G) := hSN ha
    have hxgmem : g * x * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxg : a * (g * x * g⁻¹) * a⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      (Subgroup.mem_normalizer_iff.mp haN (g * x * g⁻¹)).1 hxgmem
    rcases Subgroup.mem_map.mp hxg with ⟨r, hrR, hrval⟩
    have hrval' : g * r * g⁻¹ = a * (g * x * g⁻¹) * a⁻¹ := by
      simpa [MulAut.conj_apply] using hrval
    have hgoal : (g⁻¹ * a * g) * x * (g⁻¹ * a * g)⁻¹ = r := by
      calc
        (g⁻¹ * a * g) * x * (g⁻¹ * a * g)⁻¹ =
            g⁻¹ * (a * (g * x * g⁻¹) * a⁻¹) * g := by group
        _ = g⁻¹ * (g * r * g⁻¹) * g := by rw [← hrval']
        _ = r := by group
    exact hgoal ▸ hrR
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward s hsS x
  · intro hx
    have hx' : (g⁻¹ * s⁻¹ * g) * (u * x * u⁻¹) * (g⁻¹ * s⁻¹ * g)⁻¹ ∈ R :=
      hforward s⁻¹ (S.inv_mem hsS) (u * x * u⁻¹) hx
    have hx'' : (g⁻¹ * s⁻¹ * g) * (u * x * u⁻¹) * (g⁻¹ * s⁻¹ * g)⁻¹ = x := by
      dsimp [u]
      group
    exact hx'' ▸ hx'

/-- The subgroup generated by two commuting involutions is a 2-group. -/
private theorem isPGroup_sup_zpowers_of_commute_involutions_t26
    {G : Type u} [Group G] [Finite G] {t s : G}
    (ht : IsInvolution t) (hs : IsInvolution s) (hts : Commute t s) :
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s
    IsPGroup 2 V := by
  intro V
  have htord : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  have hAp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, htord]
  have hBp : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, hsord]
  have hsNt : s ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (s * t * s⁻¹) = Subgroup.zpowers t
    have hss : s * s = 1 := by simpa [pow_two] using hs.2
    have hconj : s * t * s⁻¹ = t := by
      rw [show s⁻¹ = s by exact inv_eq_of_mul_eq_one_right hss]
      calc
        s * t * s = t * (s * s) := by rw [← hts.eq]; group
        _ = t := by rw [hss, mul_one]
    rw [hconj]
  have hBnormA : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
    Subgroup.zpowers_le.mpr hsNt
  exact IsPGroup.to_sup_of_normal_left' hAp hBp hBnormA

/-- The ambient reflected torus `R = [⟨t⟩, C_E(s)]` has the model half
`|U|/2` as its cardinality. -/
private theorem natCard_reflected_R_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y : G} (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = ld.s) :
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    Nat.card R = Nat.card ld.T.U / 2 := by
  classical
  intro CEs R
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let n : ℕ := Nat.card ld.T.U / 2
  have hn : n = (Nat.card K - 1) / 2 ∨ n = (Nat.card K + 1) / 2 := by
    dsimp [n]
    rcases ld.T.U_card with hU | hU
    · left
      rw [hU]
    · right
      rw [hU]
  have hnodd : Odd n := by simpa [n] using ld.T.U_half_odd
  have hRtr := reflected_R_image_outer_torus_t26 c d K hK L hLnormal hLindex e
    ld hyI hyts hn hnodd
  dsimp at hRtr
  rcases hRtr with ⟨hRbarL, _hR0cyc, hR0card_eq, _hR0eq, hRinterO⟩
  have hRleH : R ≤ c.Hhat :=
    (reflected_R_le_inter_of_conjugator_t26 c d.E
      (d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e).2.1
      d.isComponent.1 ld.hsS hyts (by simpa [pow_two] using hyI.2)).2.1
  let RH : Subgroup c.Hhat := R.subgroupOf c.Hhat
  let Rbar : Subgroup (c.Hhat ⧸ O) := RH.map q
  let R0 : Subgroup (PGL2 K) := (Rbar.subgroupOf L).map e.toMonoidHom
  have hqinj : Function.Injective (q.comp RH.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff (q.comp RH.subtype)).mp
    apply le_antisymm
    · intro x hx
      have hx1G : (x : G) = 1 := by
        have hq1 : q (x : c.Hhat) = 1 := by
          simpa [MonoidHom.mem_ker] using hx
        have hxO : (x : c.Hhat) ∈ O :=
          (QuotientGroup.eq_one_iff (N := O) (x : c.Hhat)).mp hq1
        exact hRinterO (x : G) x.2 (Subgroup.mem_map.mpr ⟨x, hxO, rfl⟩)
      have hx1H : (x : c.Hhat) = 1 := by
        apply Subtype.ext
        simpa using hx1G
      exact Subtype.ext hx1H
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp hx
      simp [hx1]
  have hcard : Nat.card R = Nat.card R0 := by
    calc
      Nat.card R = Nat.card RH :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH).toEquiv).symm
      _ = Nat.card Rbar := by
        have hmap : (⊤ : Subgroup RH).map (q.comp RH.subtype) = RH.map q := by
          ext x
          constructor
          · rintro ⟨y, _hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨(y : c.Hhat), y.2, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, trivial, rfl⟩
        change Nat.card ↥RH = Nat.card ↥(RH.map q)
        rw [← hmap]
        calc
          Nat.card ↥RH = Nat.card ↥(⊤ : Subgroup RH) :=
            (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
          _ = Nat.card ↥((⊤ : Subgroup RH).map (q.comp RH.subtype)) :=
            (Subgroup.card_map_of_injective (K := (⊤ : Subgroup RH))
              (f := q.comp RH.subtype) hqinj).symm
      _ = Nat.card (Rbar.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRbarL).toEquiv).symm
      _ = Nat.card R0 := by
        simpa [R0] using
          (Nat.card_congr (Subgroup.equivMapOfInjective (Rbar.subgroupOf L)
            e.toMonoidHom e.injective).toEquiv)
  rw [hcard]
  simpa [R0, Rbar, RH, n] using hR0card_eq

/-- The ambient join of the two reflected tori and the inner reflector has
order divisible by four: it maps onto the conjugated `PGL₂(K)` model join,
whose order is divisible by four. -/
private theorem four_dvd_card_ambient_join_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y g : G} (hyI : IsInvolution y)
    (hyts : y * c.t * y⁻¹ = ld.s)
    (hgI : IsInvolution g)
    (hgt : g * c.t * g⁻¹ = c.t * ld.s) :
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    let CEsts : Subgroup G := Subgroup.centralizer ({c.t * ld.s} : Set G) ⊓ d.E
    let Rstar : Subgroup G := ⁅Subgroup.zpowers c.t, CEsts⁆
    let Mamb : Subgroup G := (R ⊔ Subgroup.zpowers c.t) ⊔ Rstar
    4 ∣ Nat.card Mamb := by
  classical
  intro CEs R CEsts Rstar Mamb
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hg2 : g * g = 1 := by simpa [pow_two] using hgI.2
  obtain ⟨ld2, hs2, hld2s, hld2g, hld2t, hld2R, hld2Rstar⟩ :=
    exists_theorem26_outer_lift_data_swap d K hK L hLnormal hLindex e ld
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let n : ℕ := Nat.card ld.T.U / 2
  have hn : n = (Nat.card K - 1) / 2 ∨ n = (Nat.card K + 1) / 2 := by
    dsimp [n]
    rcases ld.T.U_card with hU | hU
    · left
      rw [hU]
    · right
      rw [hU]
  have hnodd : Odd n := by simpa [n] using ld.T.U_half_odd
  have hcomp := d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  dsimp at hcomp
  have hcard : 3 < Nat.card K := hcomp.1
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  dsimp at hend
  rcases hend with ⟨_hEnormal, htE, _hfuse, _hcent⟩
  have hRleH : R ≤ c.Hhat :=
    (reflected_R_le_inter_of_conjugator_t26 c d.E htE d.isComponent.1 ld.hsS
      hyts hy2).2.1
  have htsS : c.t * ld.s ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem (c.S0_le_S c.t_mem_S0) ld.hsS
  have hRstarH : Rstar ≤ c.Hhat :=
    (reflected_R_le_inter_of_conjugator_t26 c d.E htE d.isComponent.1 htsS
      hgt hg2).2.1
  have htH : c.t ∈ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat (c.S0_le_S c.t_mem_S0)
  have hMleH : Mamb ≤ c.Hhat := by
    dsimp [Mamb]
    apply sup_le
    · apply sup_le
      · exact hRleH
      · exact Subgroup.zpowers_le.mpr htH
    · exact hRstarH
  let M : Subgroup c.Hhat := Mamb.subgroupOf c.Hhat
  have hM_eq : M =
      (R.subgroupOf c.Hhat ⊔ (Subgroup.zpowers c.t).subgroupOf c.Hhat) ⊔
        Rstar.subgroupOf c.Hhat := by
    dsimp [M, Mamb]
    rw [Subgroup.subgroupOf_sup (A := R ⊔ Subgroup.zpowers c.t)
      (A' := Rstar) (B := c.Hhat)
      (hA := sup_le hRleH (Subgroup.zpowers_le.mpr htH)) (hA' := hRstarH)]
    rw [Subgroup.subgroupOf_sup (A := R) (A' := Subgroup.zpowers c.t)
      (B := c.Hhat) (hA := hRleH) (hA' := Subgroup.zpowers_le.mpr htH)]
  have hRtr := reflected_R_image_outer_torus_t26 c d K hK L hLnormal hLindex e
    ld hyI hyts hn hnodd
  dsimp at hRtr
  rcases hRtr with ⟨hRbarL, _hR0cyc, _hR0card, hR0eqC1, _hRinterO⟩
  have hRtr2 := reflected_R_image_outer_torus_t26 c d K hK L hLnormal hLindex e
    ld2 hgI (by simpa [hs2] using hgt) hn hnodd
  dsimp at hRtr2
  rcases hRtr2 with ⟨hRstarbarL, _hRstar0cyc, _hRstar0card, hRstar0eqC1,
    _hRstarinterO⟩
  have hRstarbarL' : (Rstar.subgroupOf c.Hhat).map q ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ (⁅Subgroup.zpowers c.t,
        Subgroup.centralizer ({ld2.s} : Set G) ⊓ d.E⁆).subgroupOf c.Hhat := by
      simpa [CEsts, Rstar, hs2] using hy
    exact hRstarbarL (Subgroup.mem_map.mpr ⟨y, hy', rfl⟩)
  let Rbar : Subgroup (c.Hhat ⧸ O) := (R.subgroupOf c.Hhat).map q
  let R0 : Subgroup (PGL2 K) := (Rbar.subgroupOf L).map e.toMonoidHom
  let Rstarbar : Subgroup (c.Hhat ⧸ O) := (Rstar.subgroupOf c.Hhat).map q
  let Rstar0 : Subgroup (PGL2 K) := (Rstarbar.subgroupOf L).map e.toMonoidHom
  let t0 : PGL2 K := ld.T.g * ld.T.t * ld.T.g⁻¹
  let M0 : Subgroup (PGL2 K) := (R0 ⊔ Subgroup.zpowers t0) ⊔ Rstar0
  have hR0eq : R0 = ld.T.R.map (MulAut.conj ld.T.g).toMonoidHom := by
    dsimp [R0, Rbar, R]
    rw [hR0eqC1]
    exact pgl2_reflected_outer_commutator_eq_conj_R hK hcard ld.Pmodel ld.eP ld.T
      (s0 := ld.T.g * ld.T.s * ld.T.g⁻¹) (t0 := ld.T.g * ld.T.t * ld.T.g⁻¹)
      (hs0 := rfl) (ht0 := rfl)
  have hRstar0eq : Rstar0 =
      ld.T.Rstar.map (MulAut.conj ld.T.g).toMonoidHom := by
    dsimp [Rstar0, Rstarbar, Rstar, CEsts]
    rw [← hs2]
    rw [hRstar0eqC1]
    rw [hld2g, hld2t, hld2s]
    exact pgl2_reflected_outer_commutator_eq_conj_Rstar hK hcard ld.Pmodel
      ld.eP ld.T
  let hSleG : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSleG
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  have htqL : q ⟨c.t, htH⟩ ∈ L :=
    hPqL (Subgroup.mem_map.mpr
      ⟨⟨c.t, htH⟩, c.S0_le_S c.t_mem_S0, rfl⟩)
  have hRcomap : R.subgroupOf c.Hhat ≤ Subgroup.comap q L := by
    intro x hx
    change q x ∈ L
    exact hRbarL (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hRstarcomap : Rstar.subgroupOf c.Hhat ≤ Subgroup.comap q L := by
    intro x hx
    change q x ∈ L
    have hx' : x ∈ (⁅Subgroup.zpowers c.t,
        Subgroup.centralizer ({ld2.s} : Set G) ⊓ d.E⁆).subgroupOf c.Hhat := by
      simpa [CEsts, Rstar, hs2] using hx
    exact hRstarbarL (Subgroup.mem_map.mpr ⟨x, hx', rfl⟩)
  have hTcomap : (Subgroup.zpowers c.t).subgroupOf c.Hhat ≤
      Subgroup.comap q L := by
    intro x hx
    change q x ∈ L
    rcases (Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)) with
      ⟨k, hk⟩
    have hxeq : x = (⟨c.t, htH⟩ : c.Hhat) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [hxeq]
    change q ((⟨c.t, htH⟩ : c.Hhat) ^ k) ∈ L
    have htP : (⟨c.t, htH⟩ : c.Hhat) ∈ (P : Subgroup c.Hhat) :=
      c.S0_le_S c.t_mem_S0
    exact hPqL (Subgroup.mem_map.mpr
      ⟨(⟨c.t, htH⟩ : c.Hhat) ^ k,
        (P : Subgroup c.Hhat).zpow_mem htP k, rfl⟩)
  have hMle_comap : M ≤ Subgroup.comap q L := by
    rw [hM_eq]
    exact sup_le (sup_le hRcomap hTcomap) hRstarcomap
  have hMambqL : ∀ x : Mamb, q (Subgroup.inclusion hMleH x) ∈ L := by
    intro x
    let xH : c.Hhat := Subgroup.inclusion hMleH x
    have hxMprop : xH ∈ M := Subgroup.mem_subgroupOf.mpr x.2
    exact Subgroup.mem_comap.mp (hMle_comap hxMprop)
  let f : Mamb →* PGL2 K :=
    e.toMonoidHom.comp ((q.comp (Subgroup.inclusion hMleH)).codRestrict L
      (fun x => hMambqL x))
  have hRleMamb : R ≤ Mamb := by
    dsimp [Mamb]
    exact le_trans le_sup_left le_sup_left
  have hRstarleMamb : Rstar ≤ Mamb := by
    dsimp [Mamb]
    exact le_sup_right
  have hTleMamb : Subgroup.zpowers c.t ≤ Mamb := by
    dsimp [Mamb]
    exact le_trans le_sup_right le_sup_left
  have hR_im : ∀ a : Mamb, (a : G) ∈ R → f a ∈ R0 := by
    intro a ha
    let aH : c.Hhat := Subgroup.inclusion hMleH a
    have haRH : aH ∈ R.subgroupOf c.Hhat := Subgroup.mem_subgroupOf.mpr ha
    have hqR : q aH ∈ Rbar := Subgroup.mem_map.mpr ⟨aH, haRH, rfl⟩
    have hL : q aH ∈ L := hRbarL hqR
    have hmemL : (⟨q aH, hL⟩ : L) ∈ Rbar.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hqR
    have hf : f a = e ⟨q aH, hL⟩ := by
      dsimp [f]
      rfl
    rw [hf]
    exact Subgroup.mem_map.mpr ⟨⟨q aH, hL⟩, hmemL, rfl⟩
  have hRstar_im : ∀ a : Mamb, (a : G) ∈ Rstar → f a ∈ Rstar0 := by
    intro a ha
    let aH : c.Hhat := Subgroup.inclusion hMleH a
    have haRH : aH ∈ Rstar.subgroupOf c.Hhat := Subgroup.mem_subgroupOf.mpr ha
    have hqR : q aH ∈ Rstarbar := Subgroup.mem_map.mpr ⟨aH, haRH, rfl⟩
    have hL : q aH ∈ L := hRstarbarL' hqR
    have hmemL : (⟨q aH, hL⟩ : L) ∈ Rstarbar.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hqR
    have hf : f a = e ⟨q aH, hL⟩ := by
      dsimp [f]
      rfl
    rw [hf]
    exact Subgroup.mem_map.mpr ⟨⟨q aH, hL⟩, hmemL, rfl⟩
  have hf_t0 : e ⟨q ⟨c.t, htH⟩, htqL⟩ = t0 := by
    have hLeq : (⟨q ⟨c.t, htH⟩, htqL⟩ : L) = ld.tL := by
      apply Subtype.ext
      exact ld.htL.symm
    rw [hLeq]
    exact ld.ht0eq
  have hT_im : ∀ a : Mamb, (a : G) ∈ Subgroup.zpowers c.t →
      f a ∈ Subgroup.zpowers t0 := by
    intro a ha
    let aH : c.Hhat := Subgroup.inclusion hMleH a
    have haTH : aH ∈ (Subgroup.zpowers c.t).subgroupOf c.Hhat :=
      Subgroup.mem_subgroupOf.mpr ha
    rcases (Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp haTH)) with
      ⟨k, hk⟩
    have hq : q aH = q ((⟨c.t, htH⟩ : c.Hhat) ^ k) := by
      congr 1
      apply Subtype.ext
      simpa using hk.symm
    have hLtk : q ((⟨c.t, htH⟩ : c.Hhat) ^ k) ∈ L := by
      have htP : (⟨c.t, htH⟩ : c.Hhat) ∈ (P : Subgroup c.Hhat) :=
        c.S0_le_S c.t_mem_S0
      exact hPqL (Subgroup.mem_map.mpr
        ⟨(⟨c.t, htH⟩ : c.Hhat) ^ k,
          (P : Subgroup c.Hhat).zpow_mem htP k, rfl⟩)
    have hf : f a = e ⟨q ((⟨c.t, htH⟩ : c.Hhat) ^ k), hLtk⟩ := by
      apply congrArg e
      apply Subtype.ext
      simpa [aH] using hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    calc
      t0 ^ k = (e ⟨q ⟨c.t, htH⟩, htqL⟩) ^ k := by rw [hf_t0]
      _ = e ⟨q ((⟨c.t, htH⟩ : c.Hhat) ^ k), hLtk⟩ := by
        rw [← map_zpow e (⟨q ⟨c.t, htH⟩, htqL⟩ : L) k]
        congr 1
      _ = f a := hf.symm
  have hRT_im : ∀ a : Mamb, (a : G) ∈ R ⊔ Subgroup.zpowers c.t →
      f a ∈ R0 ⊔ Subgroup.zpowers t0 := by
    intro a ha
    rw [Subgroup.sup_eq_closure] at ha
    refine Subgroup.closure_induction
      (k := ((R : Set G) ∪ (Subgroup.zpowers c.t : Set G)))
      (p := fun y hy => f ⟨y,
        (le_sup_left : R ⊔ Subgroup.zpowers c.t ≤ Mamb)
          (by simpa [← Subgroup.sup_eq_closure] using hy)⟩ ∈
        R0 ⊔ Subgroup.zpowers t0) ?_ ?_ ?_ ?_ ha
    · intro y hy
      rcases hy with hyR | hyT
      · exact Subgroup.mem_sup_left (hR_im ⟨y, hRleMamb hyR⟩ hyR)
      · exact Subgroup.mem_sup_right (hT_im ⟨y, hTleMamb hyT⟩ hyT)
    · change f (1 : Mamb) ∈ R0 ⊔ Subgroup.zpowers t0
      rw [map_one]
      exact (R0 ⊔ Subgroup.zpowers t0).one_mem
    · intro y z _hy _hz hyP hzP
      have hyM : y ∈ Mamb :=
        (le_sup_left : R ⊔ Subgroup.zpowers c.t ≤ Mamb)
          (by simpa [← Subgroup.sup_eq_closure] using _hy)
      have hzM : z ∈ Mamb :=
        (le_sup_left : R ⊔ Subgroup.zpowers c.t ≤ Mamb)
          (by simpa [← Subgroup.sup_eq_closure] using _hz)
      have heq : (⟨y * z, Mamb.mul_mem hyM hzM⟩ : Mamb) =
          (⟨y, hyM⟩ : Mamb) * (⟨z, hzM⟩ : Mamb) := by
        apply Subtype.ext
        rfl
      have hmul : f ⟨y * z, Mamb.mul_mem hyM hzM⟩ =
          f ⟨y, hyM⟩ * f ⟨z, hzM⟩ := by
        rw [heq, map_mul]
      rw [hmul]
      exact (R0 ⊔ Subgroup.zpowers t0).mul_mem hyP hzP
    · intro y _hy hyP
      have hyM : y ∈ Mamb :=
        (le_sup_left : R ⊔ Subgroup.zpowers c.t ≤ Mamb)
          (by simpa [← Subgroup.sup_eq_closure] using _hy)
      have heq : (⟨y⁻¹, Mamb.inv_mem hyM⟩ : Mamb) =
          (⟨y, hyM⟩ : Mamb)⁻¹ := by
        apply Subtype.ext
        rfl
      have hinv : f ⟨y⁻¹, Mamb.inv_mem hyM⟩ = (f ⟨y, hyM⟩)⁻¹ := by
        rw [heq, map_inv]
      rw [hinv]
      exact (R0 ⊔ Subgroup.zpowers t0).inv_mem hyP
  have hMamb_mem_le : ∀ a : Mamb, f a ∈ M0 := by
    intro a
    have haM : (a : G) ∈ (R ⊔ Subgroup.zpowers c.t) ⊔ Rstar := by
      simpa [Mamb] using a.2
    rw [Subgroup.sup_eq_closure] at haM
    let k : Set G :=
      ((R ⊔ Subgroup.zpowers c.t : Subgroup G) : Set G) ∪ (Rstar : Set G)
    change (a : G) ∈ Subgroup.closure k at haM
    have hmemM : ∀ y : G, y ∈ Subgroup.closure
        k →
        y ∈ Mamb := by
      intro y hy
      change y ∈ (R ⊔ Subgroup.zpowers c.t) ⊔ Rstar
      rw [Subgroup.sup_eq_closure]
      exact hy
    refine Subgroup.closure_induction
      (k := k)
      (p := fun y hy => f ⟨y, hmemM y hy⟩ ∈ M0)
      ?_ ?_ ?_ ?_ haM
    · intro y hy
      rcases hy with hyA | hyRstar
      · have hyM : y ∈ Mamb :=
          (le_sup_left : R ⊔ Subgroup.zpowers c.t ≤ Mamb) hyA
        exact (Subgroup.mem_sup_left (hRT_im ⟨y, hyM⟩ hyA))
      · have hyM : y ∈ Mamb := (le_sup_right : Rstar ≤ Mamb) hyRstar
        exact (Subgroup.mem_sup_right (hRstar_im ⟨y, hyM⟩ hyRstar))
    · change f (1 : Mamb) ∈ M0
      rw [map_one]
      exact M0.one_mem
    · intro y z _hy _hz hyP hzP
      have hyM : y ∈ Mamb := hmemM y _hy
      have hzM : z ∈ Mamb := hmemM z _hz
      have heq : (⟨y * z, Mamb.mul_mem hyM hzM⟩ : Mamb) =
          (⟨y, hyM⟩ : Mamb) * (⟨z, hzM⟩ : Mamb) := by
        apply Subtype.ext
        rfl
      have hmul : f ⟨y * z, Mamb.mul_mem hyM hzM⟩ =
          f ⟨y, hyM⟩ * f ⟨z, hzM⟩ := by
        rw [heq, map_mul]
      rw [hmul]
      exact M0.mul_mem hyP hzP
    · intro y _hy hyP
      have hyM : y ∈ Mamb := hmemM y _hy
      have heq : (⟨y⁻¹, Mamb.inv_mem hyM⟩ : Mamb) =
          (⟨y, hyM⟩ : Mamb)⁻¹ := by
        apply Subtype.ext
        rfl
      have hinv : f ⟨y⁻¹, Mamb.inv_mem hyM⟩ = (f ⟨y, hyM⟩)⁻¹ := by
        rw [heq, map_inv]
      rw [hinv]
      exact M0.inv_mem hyP
  have hRange_le : f.range ≤ M0 := by
    rw [MonoidHom.range_eq_map]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact hMamb_mem_le a
  have hR0_le : R0 ≤ f.range := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨yL, hyL, rfl⟩
    have hyRbar : (yL : c.Hhat ⧸ O) ∈ Rbar := Subgroup.mem_subgroupOf.mp hyL
    rcases Subgroup.mem_map.mp hyRbar with ⟨rH, hrRH, hrq⟩
    have hrRamb : (rH : G) ∈ R := Subgroup.mem_subgroupOf.mp hrRH
    let ar : Mamb := ⟨(rH : G), hRleMamb hrRamb⟩
    have hf : f ar = e yL := by
      apply congrArg e
      apply Subtype.ext
      have hincl : Subgroup.inclusion hMleH ar = rH := by
        apply Subtype.ext
        rfl
      change q (Subgroup.inclusion hMleH ar) = (yL : c.Hhat ⧸ O)
      rw [hincl]
      exact hrq
    exact MonoidHom.mem_range.mpr ⟨ar, hf⟩
  have hRstar0_le : Rstar0 ≤ f.range := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨yL, hyL, rfl⟩
    have hyRbar : (yL : c.Hhat ⧸ O) ∈ Rstarbar :=
      Subgroup.mem_subgroupOf.mp hyL
    rcases Subgroup.mem_map.mp hyRbar with ⟨rH, hrRH, hrq⟩
    have hrRamb : (rH : G) ∈ Rstar := Subgroup.mem_subgroupOf.mp hrRH
    let ar : Mamb := ⟨(rH : G), hRstarleMamb hrRamb⟩
    have hf : f ar = e yL := by
      apply congrArg e
      apply Subtype.ext
      have hincl : Subgroup.inclusion hMleH ar = rH := by
        apply Subtype.ext
        rfl
      change q (Subgroup.inclusion hMleH ar) = (yL : c.Hhat ⧸ O)
      rw [hincl]
      exact hrq
    exact MonoidHom.mem_range.mpr ⟨ar, hf⟩
  have ht0_range : t0 ∈ f.range := by
    let aT : Mamb := ⟨c.t, hTleMamb (Subgroup.mem_zpowers c.t)⟩
    have hf : f aT = t0 := by
      calc
        f aT = e ⟨q ⟨c.t, htH⟩, htqL⟩ := by
          apply congrArg e
          apply Subtype.ext
          rfl
        _ = t0 := hf_t0
    exact MonoidHom.mem_range.mpr ⟨aT, hf⟩
  have hM0_le : M0 ≤ f.range := by
    apply sup_le
    · apply sup_le
      · exact hR0_le
      · exact Subgroup.zpowers_le.mpr ht0_range
    · exact hRstar0_le
  have hRange_eq : f.range = M0 := le_antisymm hRange_le hM0_le
  let cg : PGL2 K ≃* PGL2 K := MulAut.conj ld.T.g
  have hcg_t : cg ld.T.t = t0 := rfl
  have hTmap : (Subgroup.zpowers ld.T.t).map cg.toMonoidHom =
      Subgroup.zpowers t0 := by
    rw [← hcg_t]
    simpa using (MonoidHom.map_zpowers cg.toMonoidHom ld.T.t)
  have hM0eq : M0 =
      ((ld.T.R ⊔ Subgroup.zpowers ld.T.t) ⊔ ld.T.Rstar).map
        cg.toMonoidHom := by
    dsimp [M0, t0]
    rw [hR0eq, hRstar0eq]
    rw [← hTmap]
    rw [← Subgroup.map_sup (H := ld.T.R)
      (K := Subgroup.zpowers ld.T.t) (f := cg.toMonoidHom)]
    rw [← Subgroup.map_sup (H := ld.T.R ⊔ Subgroup.zpowers ld.T.t)
      (K := ld.T.Rstar) (f := cg.toMonoidHom)]
    rfl
  have hM0card : Nat.card ↥M0 =
      Nat.card ↥((ld.T.R ⊔ Subgroup.zpowers ld.T.t) ⊔ ld.T.Rstar) := by
    rw [hM0eq]
    exact (Subgroup.card_map_of_injective
      (K := (ld.T.R ⊔ Subgroup.zpowers ld.T.t) ⊔ ld.T.Rstar)
      (f := cg.toMonoidHom) cg.injective)
  have hfour0 : 4 ∣ Nat.card ↥M0 := by
    rw [hM0card]
    exact ld.T.four_dvd_card
  have hcardM : Nat.card ↥Mamb = Nat.card ↥f.ker * Nat.card ↥M0 := by
    have hmul := f.ker.card_mul_index
    have hindex : f.ker.index = Nat.card f.range := Subgroup.index_ker f
    rw [hindex, hRange_eq] at hmul
    exact hmul.symm
  rw [hcardM]
  exact dvd_mul_of_dvd_right hfour0 (Nat.card f.ker)

/-- The final `PGL₂(K)` model contradiction for the component branch.

The body is the only remaining source-faithful work: the reflected-torus
transport and the normalizer transfer.  It is developed here in isolation;
at landing it is wired back through
`componentLayerOf_eq_bot_of_pgl2_model_impossible`. -/
public theorem pgl2_model_impossible_t26
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ld⟩ := exists_theorem26_outer_lift_data d K hK L hLnormal hLindex e
  have hm2 : 2 ≤ c.m := pgl2_dihedral_sylow_parameter_ge_two K hK ld.Pmodel ld.eP
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  dsimp at hend
  rcases hend with ⟨hEnormal, htE, _hfuse, hcent⟩
  have hEamb : ∀ {h x : G}, h ∈ c.Hhat → x ∈ d.E → h * x * h⁻¹ ∈ d.E := by
    intro h x hh hx
    let hH : c.Hhat := ⟨h, hh⟩
    let xH : c.Hhat := ⟨x, d.isComponent.1 hx⟩
    have hxEi : xH ∈ d.E.subgroupOf c.Hhat := Subgroup.mem_subgroupOf.mpr hx
    have hconj : hH * xH * hH⁻¹ ∈ d.E.subgroupOf c.Hhat :=
      hEnormal.conj_mem xH hxEi hH
    exact Subgroup.mem_subgroupOf.mp hconj
  have htsne1 : c.t ≠ ld.s := by
    intro h
    exact ld.hsE (by simpa [h] using htE)
  obtain ⟨y, hyI, hyts, _hyC⟩ :=
    exists_theorem26_product_centralizer_conjugator hmin c hm2 ld.s ld.hsI
      ld.hcomm htsne1
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
  let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
  let X : Subgroup G := R.map (MulAut.conj y).toMonoidHom
  have hRyO : X ≤ oddCoreOf c.Hhat := by
    simpa [X, CEs, R] using
      (reflected_R_conj_le_oddCore_t26 c d K hK L hLnormal hLindex e ld hyI hyts)
  have hs2maps : ∀ x : G, x ∈ X → ld.s * x * ld.s⁻¹ ∈ X := by
    simpa [X, CEs, R] using
      (reflected_R_conj_reflects_t26 c d.E ld.hsI hyI hyts htE ld.hcomm)
  have hSNX : (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) :=
    S_le_normalizer_of_odd_centralized_inverted_t26 d K hK L hLnormal hLindex e
      hRyO ld.hsI ld.hsS ld.hsE hs2maps
  have hRinter := reflected_R_le_inter_of_conjugator_t26 c d.E htE d.isComponent.1
    ld.hsS hyts hy2
  have hRleE : R ≤ d.E := by simpa [R, CEs] using hRinter.1
  have hRleH : R ≤ c.Hhat := by simpa [R, CEs] using hRinter.2.1
  have hRleHy : R ≤ conjugateSubgroup c.Hhat y := by
    simpa [R, CEs] using hRinter.2.2
  obtain ⟨ld2, hs2eq, hld2s, hld2g, hld2t, hld2R, hld2Rstar⟩ :=
    exists_theorem26_outer_lift_data_swap d K hK L hLnormal hLindex e ld
  have htsne2 : c.t ≠ ld2.s := by
    intro h
    exact ld2.hsE (by simpa [h] using htE)
  obtain ⟨g, hgI, hgt, _hgC⟩ :=
    exists_theorem26_product_centralizer_conjugator hmin c hm2 ld2.s ld2.hsI
      ld2.hcomm htsne2
  have hg2 : g * g = 1 := by simpa [pow_two] using hgI.2
  let CEsts : Subgroup G := Subgroup.centralizer ({ld2.s} : Set G) ⊓ d.E
  let Rstar : Subgroup G := ⁅Subgroup.zpowers c.t, CEsts⁆
  let X2 : Subgroup G := Rstar.map (MulAut.conj g).toMonoidHom
  have hRgO : X2 ≤ oddCoreOf c.Hhat := by
    simpa [X2, CEsts, Rstar, hs2eq] using
      (reflected_Rstar_conj_le_oddCore_t26 c d K hK L hLnormal hLindex e ld
        hgI (by simpa [hs2eq] using hgt))
  have hmaps2 : ∀ x : G, x ∈ X2 → ld2.s * x * ld2.s⁻¹ ∈ X2 := by
    simpa [X2, CEsts, Rstar] using
      (reflected_R_conj_reflects_t26 c d.E ld2.hsI hgI hgt htE ld2.hcomm)
  have hSNX2 : (c.S : Subgroup G) ≤ Subgroup.normalizer (X2 : Set G) :=
    S_le_normalizer_of_odd_centralized_inverted_t26 d K hK L hLnormal hLindex e
      hRgO ld2.hsI ld2.hsS ld2.hsE hmaps2
  have hRstarInter := reflected_R_le_inter_of_conjugator_t26 c d.E htE d.isComponent.1
    ld2.hsS hgt hg2
  have hRstarE : Rstar ≤ d.E := by simpa [Rstar, CEsts] using hRstarInter.1
  have hRstarH : Rstar ≤ c.Hhat := by simpa [Rstar, CEsts] using hRstarInter.2.1
  let C : Subgroup G := Subgroup.centralizer ({c.t * ld.s} : Set G)
  let N : Subgroup G := Subgroup.normalizer (Rstar : Set G)
  let P0S : Sylow 2 G := g⁻¹ • c.S
  have hP0def : (P0S : Subgroup G) = conjugateSubgroup (c.S : Subgroup G) g⁻¹ := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hP0C : (P0S : Subgroup G) ≤ C := by
    rw [hP0def]
    change conjugateSubgroup (c.S : Subgroup G) g⁻¹ ≤
      Subgroup.centralizer ({c.t * ld.s} : Set G)
    simpa [hs2eq] using conjugate_sylow_le_centralizer_of_conj_ts_t26 c hgI hgt
  have hP0N : (P0S : Subgroup G) ≤ N := by
    rw [hP0def]
    exact conjugate_sylow_le_normalizer_of_normalizes_conjugate_t26
      (c.S : Subgroup G) Rstar hgI hSNX2
  let V : Subgroup G := Subgroup.zpowers c.t ⊔ Subgroup.zpowers ld.s
  have htC : c.t ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      c.t * (c.t * ld.s) = ld.s := by
        rw [← mul_assoc]
        simpa [pow_two] using congrArg (fun x : G => x * ld.s) c.t_involution.2
      _ = (c.t * ld.s) * c.t := by
        rw [mul_assoc, ← ld.hcomm.eq, ← mul_assoc]
        rw [show c.t * c.t = 1 by simpa [pow_two] using c.t_involution.2, one_mul]
  have hsC : ld.s ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      ld.s * (c.t * ld.s) = c.t := by
        rw [← mul_assoc, ← ld.hcomm.eq, mul_assoc]
        rw [show ld.s * ld.s = 1 by simpa [pow_two] using ld.hsI.2, mul_one]
      _ = (c.t * ld.s) * ld.s := by
        rw [mul_assoc]
        rw [show ld.s * ld.s = 1 by simpa [pow_two] using ld.hsI.2, mul_one]
  have hVC : V ≤ C := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr htC
    · exact Subgroup.zpowers_le.mpr hsC
  have htH : c.t ∈ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat (c.S0_le_S c.t_mem_S0)
  have hsH : ld.s ∈ c.Hhat := (S_le_H c).trans c.H_le_Hhat ld.hsS
  have htC2 : c.t ∈ Subgroup.centralizer ({ld2.s} : Set G) := by
    simpa [hs2eq] using htC
  have hsC2 : ld.s ∈ Subgroup.centralizer ({ld2.s} : Set G) := by
    simpa [hs2eq] using hsC
  have htNCE : c.t ∈ Subgroup.normalizer (CEsts : Set G) :=
    mem_normalizer_inf_centralizer_E_of_mem_Hhat_commute_t26 d.E c.Hhat hEamb htH htC2
  have hsNCE : ld.s ∈ Subgroup.normalizer (CEsts : Set G) :=
    mem_normalizer_inf_centralizer_E_of_mem_Hhat_commute_t26 d.E c.Hhat hEamb hsH hsC2
  have hsNt : ld.s ∈ Subgroup.normalizer (Subgroup.zpowers c.t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (ld.s * c.t * ld.s⁻¹) = Subgroup.zpowers c.t
    have hss : ld.s * ld.s = 1 := by simpa [pow_two] using ld.hsI.2
    have hconj : ld.s * c.t * ld.s⁻¹ = c.t := by
      rw [show ld.s⁻¹ = ld.s by exact inv_eq_of_mul_eq_one_right hss]
      calc
        ld.s * c.t * ld.s = c.t * (ld.s * ld.s) := by rw [← ld.hcomm.eq]; group
        _ = c.t := by rw [hss, mul_one]
    rw [hconj]
  have hV_le_z : V ≤ Subgroup.normalizer (Subgroup.zpowers c.t : Set G) := by
    apply sup_le
    · exact Subgroup.le_normalizer
    · exact Subgroup.zpowers_le.mpr hsNt
  have hV_le_CEsts : V ≤ Subgroup.normalizer (CEsts : Set G) := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr htNCE
    · exact Subgroup.zpowers_le.mpr hsNCE
  have hVN : V ≤ N := by
    have h := le_normalizer_commutator_of_le_normalizer V
      (Subgroup.zpowers c.t) CEsts hV_le_z hV_le_CEsts
    simpa [V, Rstar, CEsts, N] using h
  have hVp : IsPGroup 2 V := by
    simpa [V] using isPGroup_sup_zpowers_of_commute_involutions_t26
      c.t_involution ld.hsI ld.hcomm
  obtain ⟨Q, hQN, hQV⟩ :=
    exists_sylow_in_normalizer_containing_t26 N C P0S hP0C hP0N V hVN hVC hVp
  have hVQ : V.subgroupOf C ≤ (Q : Subgroup C) := by
    intro v hv
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have hvm : (v : G) ∈ (Q : Subgroup C).map C.subtype := hQV hvV
    rcases Subgroup.mem_map.mp hvm with ⟨c0, hc0Q, hcv⟩
    have hc0v : c0 = v := Subtype.ext hcv
    simpa [hc0v] using hc0Q
  obtain ⟨y', hyI', hyts', hyMemQ⟩ :=
    exists_theorem26_product_centralizer_conjugator_in_sylow_t26 hmin c hm2 ld.s
      ld.hsI ld.hcomm htsne1 Q hVQ
  have hy'C : y' ∈ C := Subgroup.map_subtype_le (Q : Subgroup C) hyMemQ
  have hy'N : y' ∈ N := hQN hyMemQ
  have hy'2 : y' * y' = 1 := by simpa [pow_two] using hyI'.2
  have hRstar_le_Hy' : Rstar ≤ conjugateSubgroup c.Hhat y' := by
    have hRstar_map : Rstar.map (MulAut.conj y').toMonoidHom ≤ c.Hhat := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨r, hrR, rfl⟩
      have hconj : y' * r * y'⁻¹ ∈ Rstar :=
        (Subgroup.mem_normalizer_iff.mp hy'N r).1 hrR
      exact hRstarH hconj
    exact (map_conj_le_iff_le_conjugate_t26 c.Hhat y' Rstar hy'2).mp hRstar_map
  have h8 : 8 ∣ Nat.card ↥(c.Hhat ⊓ conjugateSubgroup c.Hhat y') := by
    let B : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y'
    let Mamb : Subgroup G := (R ⊔ Subgroup.zpowers c.t) ⊔ Rstar
    let Zs : Subgroup G := Subgroup.zpowers ld.s
    have hRleHy' : R ≤ conjugateSubgroup c.Hhat y' := by
      have hRy'O : R.map (MulAut.conj y').toMonoidHom ≤ oddCoreOf c.Hhat := by
        simpa [R, CEs] using
          (reflected_R_conj_le_oddCore_t26 c d K hK L hLnormal hLindex e ld
            hyI' hyts')
      have hOleH : oddCoreOf c.Hhat ≤ c.Hhat := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact y.2
      exact (map_conj_le_iff_le_conjugate_t26 c.Hhat y' R hy'2).mp
        (hRy'O.trans hOleH)
    have hy'inv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'2
    have hts' : c.t = y' * ld.s * y'⁻¹ := by
      calc
        c.t = y'⁻¹ * (y' * c.t * y'⁻¹) * y' := by group
        _ = y'⁻¹ * ld.s * y' := by rw [hyts']
        _ = y' * ld.s * y'⁻¹ := by rw [hy'inv]
    have htm : c.t ∈ conjugateSubgroup c.Hhat y' := by
      rw [conjugateSubgroup, Subgroup.mem_map]
      refine ⟨ld.s, hsH, ?_⟩
      change y' * ld.s * y'⁻¹ = c.t
      exact hts'.symm
    have hsm : ld.s ∈ conjugateSubgroup c.Hhat y' := by
      rw [conjugateSubgroup, Subgroup.mem_map]
      refine ⟨c.t, htH, ?_⟩
      change y' * c.t * y'⁻¹ = ld.s
      exact hyts'
    have hsB : ld.s ∈ B := by
      dsimp [B]
      exact Subgroup.mem_inf.mpr ⟨hsH, hsm⟩
    have hMambE : Mamb ≤ d.E := by
      dsimp [Mamb]
      apply sup_le
      · apply sup_le
        · exact hRleE
        · exact Subgroup.zpowers_le.mpr htE
      · exact hRstarE
    have hMamb_le_B : Mamb ≤ B := by
      dsimp [Mamb, B]
      apply sup_le
      · apply sup_le
        · exact le_inf hRleH hRleHy'
        · exact le_inf (Subgroup.zpowers_le.mpr htH)
            (Subgroup.zpowers_le.mpr htm)
      · exact le_inf hRstarH hRstar_le_Hy'
    have h4amb : 4 ∣ Nat.card ↥Mamb := by
      dsimp [Mamb]
      have hgt' : g * c.t * g⁻¹ = c.t * ld.s := by
        simpa [hs2eq] using hgt
      simpa [Mamb, R, Rstar, CEs, CEsts, hs2eq] using
        (four_dvd_card_ambient_join_t26 c d K hK L hLnormal hLindex e ld
          hyI hyts hgI hgt')
    have hsCself : ld.s ∈ Subgroup.centralizer ({ld.s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hsNCEs : ld.s ∈ Subgroup.normalizer (CEs : Set G) :=
      mem_normalizer_inf_centralizer_E_of_mem_Hhat_commute_t26 d.E c.Hhat
        hEamb hsH hsCself
    have hsNZ : Zs ≤ Subgroup.normalizer (Subgroup.zpowers c.t : Set G) :=
      Subgroup.zpowers_le.mpr hsNt
    have hsNCEsZ : Zs ≤ Subgroup.normalizer (CEs : Set G) :=
      Subgroup.zpowers_le.mpr hsNCEs
    have hsNCEstsZ : Zs ≤ Subgroup.normalizer (CEsts : Set G) :=
      Subgroup.zpowers_le.mpr hsNCE
    have hsNR : Zs ≤ Subgroup.normalizer (R : Set G) :=
      le_normalizer_commutator_of_le_normalizer Zs (Subgroup.zpowers c.t) CEs
        hsNZ hsNCEsZ
    have hsNRstar : Zs ≤ Subgroup.normalizer (Rstar : Set G) :=
      le_normalizer_commutator_of_le_normalizer Zs (Subgroup.zpowers c.t) CEsts
        hsNZ hsNCEstsZ
    have hRmap_s : R.map (MulAut.conj ld.s).toMonoidHom = R :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hsNR (Subgroup.mem_zpowers ld.s)))
    have hTmap_s : (Subgroup.zpowers c.t).map (MulAut.conj ld.s).toMonoidHom =
        Subgroup.zpowers c.t :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hsNZ (Subgroup.mem_zpowers ld.s)))
    have hRstarmap_s : Rstar.map (MulAut.conj ld.s).toMonoidHom = Rstar :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hsNRstar (Subgroup.mem_zpowers ld.s)))
    have hMmap_s : Mamb.map (MulAut.conj ld.s).toMonoidHom = Mamb := by
      dsimp [Mamb]
      rw [Subgroup.map_sup, Subgroup.map_sup]
      change R.map (MulAut.conj ld.s).toMonoidHom ⊔
          (Subgroup.zpowers c.t).map (MulAut.conj ld.s).toMonoidHom ⊔
          Rstar.map (MulAut.conj ld.s).toMonoidHom =
          R ⊔ Subgroup.zpowers c.t ⊔ Rstar
      rw [hRmap_s, hTmap_s, hRstarmap_s]
    have hsNM : ld.s ∈ Subgroup.normalizer (Mamb : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap_s
    have hsNMamb : Zs ≤ Subgroup.normalizer (Mamb : Set G) :=
      Subgroup.zpowers_le.mpr hsNM
    have hsZ : ld.s ∈ Zs := by
      dsimp [Zs]
      exact Subgroup.mem_zpowers ld.s
    have hsZne : (⟨ld.s, hsZ⟩ : Zs) ≠ 1 := by
      intro hs1
      exact ld.hsI.1 (congrArg Subtype.val hs1)
    have hsOrder : orderOf ld.s = 2 := orderOf_eq_prime ld.hsI.2 ld.hsI.1
    have hZscard : Nat.card Zs = 2 := by
      dsimp [Zs]
      simp [Nat.card_zpowers, hsOrder]
    have hZeq : ∀ z : Zs, z = 1 ∨ z = ⟨ld.s, hsZ⟩ := by
      intro z
      by_cases hz : z = 1
      · exact Or.inl hz
      · rcases (Nat.card_eq_two_iff' (1 : Zs)).mp hZscard with
          ⟨z0, _hz0ne, hz0uniq⟩
        exact Or.inr ((hz0uniq z hz).trans (hz0uniq ⟨ld.s, hsZ⟩ hsZne).symm)
    have hdisjoint : Disjoint Mamb Zs := by
      rw [Subgroup.disjoint_def]
      intro x hxM hxZ
      rcases hZeq ⟨x, hxZ⟩ with hx1 | hxs
      · exact congrArg Subtype.val hx1
      · exfalso
        apply ld.hsE
        have hxsG : x = ld.s := congrArg Subtype.val hxs
        exact hMambE (hxsG ▸ hxM)
    have hMs_le_B : Mamb ⊔ Zs ≤ B := by
      exact sup_le hMamb_le_B (Subgroup.zpowers_le.mpr hsB)
    have hcardMs : Nat.card (Mamb ⊔ Zs : Subgroup G) =
        Nat.card Mamb * Nat.card Zs :=
      card_sup_eq_mul_of_disjoint_of_le_normalizer_t26 Mamb Zs hsNMamb hdisjoint
    have hcardMs' : Nat.card (Mamb ⊔ Zs : Subgroup G) =
        2 * Nat.card Mamb := by
      rw [hcardMs, hZscard]
      omega
    have h8Ms : 8 ∣ Nat.card (Mamb ⊔ Zs : Subgroup G) := by
      rw [hcardMs']
      have h8eq : 8 = 2 * 4 := by norm_num
      rw [h8eq]
      exact Nat.mul_dvd_mul_left 2 h4amb
    exact h8Ms.trans (Subgroup.card_dvd_of_le hMs_le_B)
  exact component_branch_final_contradiction_t26 (c := c) (E := d.E) (s := ld.s)
    (y := y') hm2 htE ld.hsE hEamb hcent hyI' hyts' h8

/-- Split-out proof of `theorem_2_6_component_trivial`: the component layer
is trivial once the surviving `PGL₂(K)` model is ruled out. -/
public theorem theorem_2_6_component_trivial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat = ⊥) :
    componentLayerOf c.Hhat = ⊥ := by
  by_contra hE
  exact hE (componentLayerOf_eq_bot_of_pgl2_model_impossible hmin c hO2
    (pgl2_model_impossible_t26 hmin c))

end CFSG.GorensteinWalter
