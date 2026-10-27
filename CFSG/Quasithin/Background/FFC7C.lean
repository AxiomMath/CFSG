module

public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.FFC6E
public import CFSG.Quasithin.Background.FFC6P
public import CFSG.Quasithin.Background.FFC7A

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5
open scoped commutatorElement

namespace B510

section Transfer

variable {V : Type} [CommGroup V]

theorem faithful_of_binaryNatural {L : Subgroup (MulAut V)} {U Z : Subgroup V} {d n : ℕ}
    (h : BinaryNaturalSL L U Z d n) : ∀ g ∈ L, (∀ u ∈ U, g u = u) → g = 1 := by
  obtain ⟨K, hK, hfin, hc, π, hπ⟩ := h
  intro g hg hgU
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨g, hg⟩
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
  have hγ1 : γ = 1 := by
    refine FFModel.nat_faithful _ γ fun m _ => ?_
    obtain ⟨u, hu⟩ := hfs m
    have hgu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hπ.2.2.2.1 (π γ) u u.2
    have h1 := hfe γ u hgu
    have h2 : (⟨((π γ : ↥L) : MulAut V) (u : V), hgu⟩ : ↥U) = u := by
      apply Subtype.ext
      show ((π γ : ↥L) : MulAut V) (u : V) = u
      rw [hγ]
      exact hgU u u.2
    have h3 : f u = natAct _ γ (f u) := (congrArg f h2.symm).trans h1
    rw [hu] at h3
    have h4 : (FFModel.nat (Assembly.LowTwoRank.StatedSL d K)).act γ m = m := h3.symm
    show (FFModel.nat (Assembly.LowTwoRank.StatedSL d K)).act γ m * m⁻¹ ∈
      (FFModel.nat (Assembly.LowTwoRank.StatedSL d K)).ker
    rw [h4, mul_inv_cancel]
    exact Subgroup.one_mem _
  have : (π γ : ↥L) = 1 := by rw [hγ1, map_one]
  rw [hγ1, map_one] at hγ
  exact congrArg Subtype.val hγ.symm

end Transfer

section Aut

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem irr_autSub {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : L ≤ stabSub W)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → fixV L ⊓ W ≤ J → J ≤ W →
      J = fixV L ⊓ W ∨ J = W) :
    ∀ J : Subgroup ↥W, (∀ x ∈ autSub L W, ∀ w ∈ J, x w ∈ J) → fixV (autSub L W) ⊓ ⊤ ≤ J →
      J ≤ ⊤ → J = fixV (autSub L W) ⊓ ⊤ ∨ J = ⊤ := by
  intro J hJ hfJ _
  have hmap : (fixV (autSub L W)).map W.subtype = W ⊓ fixV L := map_subtype_fixV_autSub hLW
  have hinj : Function.Injective W.subtype := W.subtype_injective
  have hJ' : ∀ x ∈ L, ∀ w ∈ J.map W.subtype, x w ∈ J.map W.subtype := by
    rintro x hx _ ⟨u, hu, rfl⟩
    exact ⟨(resHom W ⟨x, hLW hx⟩) u, hJ _ (mem_autSub.2 ⟨⟨x, hLW hx⟩, hx, rfl⟩) u hu, rfl⟩
  have hle : fixV L ⊓ W ≤ J.map W.subtype := by
    intro v hv
    have hv' : v ∈ (fixV (autSub L W)).map W.subtype := by
      rw [hmap]
      exact ⟨hv.2, hv.1⟩
    obtain ⟨u, hu, rfl⟩ := hv'
    exact ⟨u, hfJ ⟨hu, trivial⟩, rfl⟩
  have hJW : J.map W.subtype ≤ W := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  rcases hirr _ hJ' hle hJW with h | h
  · left
    have h' : J.map W.subtype = (fixV (autSub L W)).map W.subtype := by
      rw [h, hmap, inf_comm]
    rw [inf_top_eq]
    exact Subgroup.map_injective hinj h'
  · right
    have h' : J.map W.subtype = (⊤ : Subgroup ↥W).map W.subtype := by
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective hinj h'

omit [Finite V] in
theorem commV_autSub_eq_top {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : L ≤ stabSub W)
    (hcomm : commSub W L = W) : commV (autSub L W) = ⊤ := by
  apply Subgroup.map_injective W.subtype_injective
  rw [B59.map_commV_aut hLW, hcomm, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite V] in
theorem commSub_top_autSub {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : L ≤ stabSub W)
    (hcomm : commSub W L = W) : commSub (⊤ : Subgroup ↥W) (autSub L W) = ⊤ := by
  rw [← commV_eq_commSub]
  exact commV_autSub_eq_top hLW hcomm

omit [Finite V] in
theorem natural_autSub {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) (hcomm : commSub W L = W) {d n : ℕ}
    (h : BinaryNaturalSL L W (fixV L ⊓ W) d n) :
    BinaryNaturalSL (autSub L W) (commV (autSub L W)) (fixV (autSub L W) ⊓ commV (autSub L W)) d n := by
  obtain ⟨K, hK, hfin, hc, hr⟩ := h
  refine ⟨K, hK, hfin, hc, ?_⟩
  have h1 := B59.realizes_comap hLW hf hr
  have hC : (fixV L ⊓ W).comap W.subtype = fixV (autSub L W) := by
    rw [inf_comm, ← map_subtype_fixV_autSub hLW]
    exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
  rw [hC] at h1
  rw [commV_autSub_eq_top hLW hcomm, inf_top_eq]
  exact h1

theorem pCore_eq_bot_aut {M : Type} [CommGroup M] [Finite M] (hM : ∀ v : M, v ^ 2 = 1)
    {X K : Subgroup (MulAut M)} (hKq : CFSG.Open.IsQuasisimple ↥K) (hKX : K ≤ X)
    (hn : ∀ y ∈ X, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hcomm : commSub (⊤ : Subgroup M) K = ⊤)
    (hirr : ∀ J : Subgroup M, (∀ x ∈ K, ∀ w ∈ J, x w ∈ J) → fixV K ⊓ ⊤ ≤ J → J ≤ ⊤ →
      J = fixV K ⊓ ⊤ ∨ J = ⊤) : pCoreOf 2 X = ⊥ := by
  refine eq_bot_iff.2 fun q hq => ?_
  rw [Subgroup.mem_bot]
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hKperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
  have hKnt : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hKq
  have hcommQ : ∀ n ∈ pCoreOf 2 X, ∀ l ∈ K, n * l = l * n :=
    B1Red.commute_of_normal_not_le hKq (fun n hn' l hl => hn n (hQX hn') l hl)
      (fun l hl n hn' => B1Red.conj_mem_pCoreOf (hKX hl) hn')
      (fun hle => Group.IsPerfect.not_isNilpotent ↥K (hQ2.to_le hle).isNilpotent)
  have key : ∀ n : ℕ, ∀ p ∈ pCoreOf 2 X, p ^ (2 ^ n) = 1 → p = 1 := by
    intro n
    induction n with
    | zero =>
      intro p _ hp
      simpa using hp
    | succ n ih =>
      intro p hp hp2
      have hp' : p ^ 2 ∈ pCoreOf 2 X := (pCoreOf 2 X).pow_mem hp 2
      have h1 : (p ^ 2) ^ (2 ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ']
        exact hp2
      have h2 : p ^ 2 = 1 := ih _ hp' h1
      have h3 : ∀ w ∈ (⊤ : Subgroup M), p (p w) = w := by
        intro w _
        have := congrArg (fun g : MulAut M => g w) h2
        simpa [pow_two, MulAut.mul_apply] using this
      have h4 := schur_nilp hM (L := K) (W := ⊤) (fun _ _ _ _ => trivial) hcomm hirr
        (q := p) (fun x hx => hcommQ p hp x hx) (fun _ _ => trivial) h3
      exact MulEquiv.ext fun w => h4 w trivial
  obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
  exact key k q hq (by simpa using congrArg Subtype.val hk)

end Aut

end B510

end FFC

end CFSG.Quasithin
