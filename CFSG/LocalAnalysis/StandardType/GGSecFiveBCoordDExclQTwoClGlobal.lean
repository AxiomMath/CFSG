module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem swapEquiv_mul_swapEquiv_pow_three {t : ℕ} {i j k : Fin t}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) ^ 3 = 1 := by
  have hperm : (Equiv.swap j k * Equiv.swap i j) ^ 3 = 1 := by
    have h3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := j) (b := k) (c := i)
      hjk (Ne.symm hij) (Ne.symm hik)
    rw [Equiv.swap_comm j i] at h3
    rw [← h3.orderOf, pow_orderOf_eq_one]
  have hpt : ∀ x : Fin t,
      Equiv.swap j k (Equiv.swap i j (Equiv.swap j k (Equiv.swap i j
        (Equiv.swap j k (Equiv.swap i j x))))) = x := by
    intro x
    have hx := congrFun (congrArg (fun e : Equiv.Perm (Fin t) => (e : Fin t → Fin t)) hperm) x
    simpa only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, id_eq] using hx
  have hcube : (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) ^ 3 =
      (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) *
        ((PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) *
          (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k)) := by
    rw [pow_succ, pow_succ, pow_one, mul_assoc]
  refine LinearEquiv.ext fun v => ?_
  funext l
  rw [hcube]
  simp only [LinearEquiv.mul_apply, PlaneRaw.swapEquiv_apply]
  rw [hpt l]
  rfl

private theorem swapEquiv_mul_swapEquiv_apply_single {t : ℕ} {i j k : Fin t} (hik : i ≠ k) :
    (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k)
      (Pi.single i (1 : PlaneRaw.F)) i = 0 := by
  rw [LinearEquiv.mul_apply, PlaneRaw.swapEquiv_apply, PlaneRaw.swapEquiv_apply]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  rw [Pi.single_eq_of_ne (Ne.symm hik)]

private theorem swapEquiv_mul_negEquiv_mul_swapEquiv {t : ℕ} {i j : Fin t} (hij : i ≠ j) :
    PlaneRaw.swapEquiv t i j * PlaneRaw.negEquiv t i * PlaneRaw.swapEquiv t i j =
      PlaneRaw.negEquiv t j := by
  ext v k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, PlaneRaw.swapEquiv_apply,
    PlaneRaw.negEquiv_apply, PlaneRaw.swapEquiv_apply, PlaneRaw.negEquiv_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · have hne : Equiv.swap i j k ≠ i := by
      intro h
      exact hk (by
        have := congrArg (Equiv.swap i j) h
        simpa using this)
    rw [if_neg hne, if_neg hk, Equiv.swap_apply_self]

private theorem sgnAut_eq_inv_of_coord_eq_one {n : ℕ} (i0 : Fin n)
    {f : Fin n → Multiplicative (ZMod 3)} (h : ∀ k, k ≠ i0 → f k = 1) :
    SpCoord.sgnAut i0 f = f⁻¹ := by
  funext k
  by_cases hk : k = i0
  · subst hk
    simp [SpCoord.sgnAut_apply]
  · simp [SpCoord.sgnAut_apply, Function.update_of_ne hk, h k hk]

omit [Finite G] in
private theorem qTwoCl_swap_mem {n t : ℕ} {Bs : Subgroup G}
    (ht : 3 ≤ t) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (Ψ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →*
      MulAut (Fin n → Multiplicative (ZMod 3)))
    (Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs)
    (hΨ : ∀ w, Ψ w = MulAut.congr eta (Φ w)) (hΦinj : Function.Injective Φ)
    (hsq : ∀ i j, i ≠ j → (Ψ (PlaneRaw.swapEquiv t i j)) ^ 2 = 1)
    (hfixed : ∀ i j, i ≠ j → Nat.card {f : Fin n → Multiplicative (ZMod 3) //
      Ψ (PlaneRaw.swapEquiv t i j) f = f} * 3 =
        Nat.card (Fin n → Multiplicative (ZMod 3)))
    (hmem : ∀ i j, Ψ (PlaneRaw.swapEquiv t i j) ∈ bSignedFull n 3) :
    ∀ i j, i ≠ j → Ψ (PlaneRaw.swapEquiv t i j) ∈ coordProdStab n 3 := by
  let u : Fin t → Fin t → MulAut (Fin n → Multiplicative (ZMod 3)) :=
    fun i j => Ψ (PlaneRaw.swapEquiv t i j)
  intro i j hij
  by_contra hnot
  have hex : ∃ a, u i j = SpCoord.sgnAut a := by
    by_contra h
    push Not at h
    exact hnot (mem_coordProdStab_of_isRefl_of_ne_sgnAut Nat.prime_three (by decide) (hmem i j)
      (hsq i j hij) (hfixed i j hij) h)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin t, k ≠ i ∧ k ≠ j := by
    have hlt : ({i, j} : Finset (Fin t)).card < (Finset.univ : Finset (Fin t)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have h2 : ({i, j} : Finset (Fin t)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact ⟨k, hk⟩
  have hsp : SpCoord.IsSignedPerm ⇑(u j k) := by
    have h := hmem j k
    rw [bSignedFull_eq_signedPermSubgroup] at h
    exact h
  have h4 : (u i j * u j k) ^ 4 = 1 := by
    rw [ha]
    exact pow_four_sgnAut_mul_of_isSignedPerm hsp (hsq j k (Ne.symm hkj)) a
  have h3 : (u i j * u j k) ^ 3 = 1 := by
    change (Ψ (PlaneRaw.swapEquiv t i j) * Ψ (PlaneRaw.swapEquiv t j k)) ^ 3 = 1
    rw [← map_mul, ← map_pow,
      swapEquiv_mul_swapEquiv_pow_three hij (Ne.symm hkj) (Ne.symm hki), map_one]
  have h1 : u i j * u j k = 1 := by
    have h := pow_succ (u i j * u j k) 3
    rw [h4, h3, one_mul] at h
    exact h.symm
  have hw : PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k = 1 := by
    have hc : Ψ (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) = 1 := by
      rw [map_mul]
      exact h1
    have hΦ1 : Φ (PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t j k) = 1 := by
      apply (MulAut.congr eta).injective
      rw [map_one, ← hΨ]
      exact hc
    exact hΦinj (by rw [hΦ1, map_one])
  have heval := swapEquiv_mul_swapEquiv_apply_single (j := j) (Ne.symm hki)
  rw [hw] at heval
  simp at heval

omit [Finite G] in
private theorem qTwoCl_sign_not_mem {n t : ℕ} {Bs K : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (Ψ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →*
      MulAut (Fin n → Multiplicative (ZMod 3)))
    (Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs)
    (hΨ : ∀ w, Ψ w = MulAut.congr eta (Φ w))
    (hAK : ggAutomizer K Bs = (PlaneRaw.signedPermGroup t).map Φ)
    (hu_all : ∀ i j, i ≠ j → Ψ (PlaneRaw.swapEquiv t i j) ∈ coordProdStab n 3)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs) {i : Fin n}
    (hri : MulAut.congr eta r = SpCoord.sgnAut i) :
    ∀ j, Ψ (PlaneRaw.negEquiv t j) ∉ coordProdStab n 3 := by
  have hex : ∃ j₀, Ψ (PlaneRaw.negEquiv t j₀) ∉ coordProdStab n 3 := by
    by_contra hall
    push Not at hall
    have hle : (PlaneRaw.signedPermGroup t).map Ψ ≤ coordProdStab n 3 := by
      rw [PlaneRaw.signedPermGroup, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, (⟨a, b, rfl⟩ | ⟨a, rfl⟩), rfl⟩
      · by_cases hab : a = b
        · subst hab
          rw [PlaneRaw.swapEquiv_self, map_one]
          exact Subgroup.one_mem _
        · exact hu_all a b hab
      · exact hall a
    rw [hAK] at hr
    obtain ⟨g, hg, hgr⟩ := Subgroup.mem_map.mp hr
    have hmem : Ψ g ∈ coordProdStab n 3 := hle (Subgroup.mem_map_of_mem Ψ hg)
    have hval : Ψ g = SpCoord.sgnAut i := by
      rw [hΨ, hgr, hri]
    rw [hval] at hmem
    exact sgnAut_not_mem_coordProdStab Nat.prime_three (by decide) i hmem
  obtain ⟨j₀, hj₀⟩ := hex
  intro j hmemj
  by_cases hj : j = j₀
  · subst hj
    exact hj₀ hmemj
  · apply hj₀
    rw [← swapEquiv_mul_negEquiv_mul_swapEquiv hj, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hu_all j j₀ hj) hmemj) (hu_all j j₀ hj)

omit [Finite G] in
private theorem qTwoCl_generator_facts {n t : ℕ} {Bs K L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (ht : 3 ≤ t)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs)
    (hΦinj : Function.Injective Φ) (hKmem : K ∈ 𝒦)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hAK : ggAutomizer K Bs = (PlaneRaw.signedPermGroup t).map Φ)
    (hneg : ∀ i, GGIsReflection 3 (Φ (PlaneRaw.negEquiv t i)))
    (hswap : ∀ i j, i ≠ j → GGIsReflection 3 (Φ (PlaneRaw.swapEquiv t i j)))
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs) {i : Fin n}
    (hri : MulAut.congr eta r = SpCoord.sgnAut i) :
    (∀ i j, i ≠ j → MulAut.congr eta (Φ (PlaneRaw.swapEquiv t i j)) ∈ coordProdStab n 3) ∧
      (∀ j, MulAut.congr eta (Φ (PlaneRaw.negEquiv t j)) ∉ coordProdStab n 3) ∧
        (∀ j, ∃ a, MulAut.congr eta (Φ (PlaneRaw.negEquiv t j)) = SpCoord.sgnAut a) := by
  let Ψ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →*
      MulAut (Fin n → Multiplicative (ZMod 3)) := (MulAut.congr eta).toMonoidHom.comp Φ
  have hΨ : ∀ w, Ψ w = MulAut.congr eta (Φ w) := fun w => rfl
  have hgen : ∀ g ∈ PlaneRaw.signedPermGroup t, Φ g ∈ ggAutomizerJoin L Bs 𝒦 := by
    intro g hg
    refine Subgroup.mem_sup_right
      (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hKmem ?_))
    rw [hAK]
    exact Subgroup.mem_map_of_mem Φ hg
  have hmemall : ∀ g ∈ PlaneRaw.signedPermGroup t, Ψ g ∈ bSignedFull n 3 := by
    intro g hg
    rw [← hK]
    exact Subgroup.mem_map_of_mem _ (hgen g hg)
  have hswap_sq : ∀ i j, i ≠ j → (Ψ (PlaneRaw.swapEquiv t i j)) ^ 2 = 1 := by
    intro i j hij
    rw [hΨ, ← map_pow, (hswap i j hij).1, map_one]
  have hswap_fix : ∀ i j, i ≠ j → Nat.card {f : Fin n → Multiplicative (ZMod 3) //
      Ψ (PlaneRaw.swapEquiv t i j) f = f} * 3 =
        Nat.card (Fin n → Multiplicative (ZMod 3)) := by
    intro i j hij
    rw [hΨ, card_fixed_congr eta (Φ (PlaneRaw.swapEquiv t i j)), (hswap i j hij).2,
      Nat.card_congr eta.toEquiv]
  have hswap_mem : ∀ i j, Ψ (PlaneRaw.swapEquiv t i j) ∈ bSignedFull n 3 := fun i j =>
    hmemall _ (Subgroup.subset_closure (Or.inl ⟨i, j, rfl⟩))
  have hu_all : ∀ i j, i ≠ j → Ψ (PlaneRaw.swapEquiv t i j) ∈ coordProdStab n 3 :=
    qTwoCl_swap_mem ht eta Ψ Φ hΨ hΦinj hswap_sq hswap_fix hswap_mem
  have hneg_sq : ∀ j, (Ψ (PlaneRaw.negEquiv t j)) ^ 2 = 1 := by
    intro j
    rw [hΨ, ← map_pow, (hneg j).1, map_one]
  have hneg_fix : ∀ j, Nat.card {f : Fin n → Multiplicative (ZMod 3) //
      Ψ (PlaneRaw.negEquiv t j) f = f} * 3 =
        Nat.card (Fin n → Multiplicative (ZMod 3)) := by
    intro j
    rw [hΨ, card_fixed_congr eta (Φ (PlaneRaw.negEquiv t j)), (hneg j).2,
      Nat.card_congr eta.toEquiv]
  have hnn_not : ∀ j, Ψ (PlaneRaw.negEquiv t j) ∉ coordProdStab n 3 :=
    qTwoCl_sign_not_mem eta Ψ Φ hΨ hAK hu_all hr hri
  refine ⟨hu_all, hnn_not, fun j => ?_⟩
  by_contra h
  push Not at h
  exact hnn_not j (mem_coordProdStab_of_isRefl_of_ne_sgnAut Nat.prime_three (by decide)
    (hmemall _ (Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)))
    (hneg_sq j) (hneg_fix j) h)

private theorem exists_negEquiv_inverts_x {n t : ℕ} {B Bs D J : Subgroup G} {x y : G}
    {K : Subgroup G} {i0 : Fin n} (hxBs : x ∈ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hnb : GGNbr 3 B x D J y K)
    (hxcoords : ∀ k : Fin n, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1)
    {Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs}
    (hfix : ∀ v : ↥Bs, (∀ i, Φ (PlaneRaw.negEquiv t i) v = v) →
      (v : G) ∈ Subgroup.centralizer (K : Set G))
    (hsgn : ∀ j, ∃ a, MulAut.congr eta (Φ (PlaneRaw.negEquiv t j)) = SpCoord.sgnAut a) :
    ∃ j₁, Φ (PlaneRaw.negEquiv t j₁) ⟨x, hxBs⟩ = (⟨x, hxBs⟩ : ↥Bs)⁻¹ ∧
      (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
  have hxne : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
    intro h1
    apply not_mem_centralizer_of_nbr hnb
    have hx1 : x = 1 := by
      have h := congrArg (fun b : ↥Bs => (b : G)) h1
      simpa using h
    rw [hx1]
    exact Subgroup.one_mem _
  have hmove : ∃ j₁, Φ (PlaneRaw.negEquiv t j₁) ⟨x, hxBs⟩ ≠ ⟨x, hxBs⟩ := by
    by_contra h
    push Not at h
    exact not_mem_centralizer_of_nbr hnb (hfix ⟨x, hxBs⟩ h)
  obtain ⟨j₁, hj₁⟩ := hmove
  obtain ⟨σ, hσ⟩ := hsgn j₁
  have hσi : σ = i0 := by
    by_contra hne
    apply hj₁
    apply eta.injective
    rw [← congr_apply_tau eta (Φ (PlaneRaw.negEquiv t j₁)) ⟨x, hxBs⟩, hσ,
      sgnAut_apply_of_coord_eq_one (hxcoords σ hne)]
  subst σ
  refine ⟨j₁, ?_, hxne⟩
  apply eta.injective
  rw [← congr_apply_tau eta (Φ (PlaneRaw.negEquiv t j₁)) ⟨x, hxBs⟩, hσ, map_inv,
    sgnAut_eq_inv_of_coord_eq_one i0 hxcoords]

theorem GGSecFiveRouteCfg.ne_dCoordinateBlock_of_qTwoClLocal (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hn : 3 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    {y : G} {K : Subgroup G} (hKmem : K ∈ 𝒦) (hnb : GGNbr 3 B x D J y K)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs) {i : Fin n}
    (hri : MulAut.congr eta r = SpCoord.sgnAut i) (hloc : GGQTwoClLocal Bs K) :
    (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≠ dCoordinateBlock n 3 i0 := by
  intro hLD
  obtain ⟨t, Φ, ht, hΦinj, hAK, hneg, hswap, hfix, hcomp⟩ := hloc
  obtain ⟨-, -, hxBs, hLx, -⟩ := hR.1.1.tableB_facts
  obtain ⟨hu_all, hnn_not, hnn_sgnAut⟩ :=
    qTwoCl_generator_facts ht eta Φ hΦinj hKmem hK hAK hneg hswap hr hri
  have hxcoords := coords_eq_one_of_map_eq_dCoordinateBlock hR hxBs hLx hn eta i0 hLD
  obtain ⟨j₁, hinv, hxne⟩ :=
    exists_negEquiv_inverts_x hxBs eta hnb hxcoords hfix hnn_sgnAut
  have hJK : J ≤ K :=
    le_of_ggNbr hLB hR.1.1.1 hR.1.1.2.2 (hP G 3 B x L D J hR.1.1.1 hR.1.1.2.2) hnb
  have hcompJ := ggIsComponentOf_inf_centralizer_nbr hR.1.1 hnb hJK
  have hJL : J ≤ L := le_of_stdSub_left hR.1.1.2.2
  have hle : (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n 3 := by
    have h1 : (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom ≤
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom :=
      Subgroup.map_mono (ggAutomizer_mono Bs hJL)
    rw [hLD] at h1
    exact h1.trans (dCoordinateBlock_le_coordProdStab i0)
  rcases hcomp ⟨x, hxBs⟩ j₁ hxne hinv J hcompJ with ⟨i₂, hi₂⟩ | ⟨i₂, j₂, hij₂, hrot⟩
  · exact hnn_not i₂ (hle (Subgroup.mem_map_of_mem _ hi₂))
  · have hprod : MulAut.congr eta (Φ (PlaneRaw.swapEquiv t i₂ j₂)) *
        MulAut.congr eta (Φ (PlaneRaw.negEquiv t j₂)) ∈ coordProdStab n 3 := by
      have h := hle (Subgroup.mem_map_of_mem _ hrot)
      change MulAut.congr eta (Φ (PlaneRaw.rotEquiv t i₂ j₂)) ∈ coordProdStab n 3 at h
      rw [PlaneRaw.rotEquiv, map_mul, map_mul] at h
      exact h
    exact hnn_not j₂ (by
      have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hu_all i₂ j₂ hij₂)) hprod
      simpa [inv_mul_cancel_left] using h)

end CFSG.StandardType

end
