module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  UCoord SpCoord


theorem ggUdPermModel {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hdn : (d, n) ≠ (6, 1)) (hd : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    ∃ (φ : ↥(unitarySU 2 n K d) →* L'), Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      (∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t) ∧
      ∃ (S : Subgroup (Fin d → Multiplicative (ZMod p))) (Θ : ↥S →* ↥A),
        (S = ⊤ ∨ S = sumZero d p) ∧ Function.Surjective Θ ∧
        (∀ f : ↥S, Θ f = 1 ↔
          ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) ∧
        (∀ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
            (g : Fin d → Multiplicative (ZMod p)) =
              permAut π (f : Fin d → Multiplicative (ZMod p)) →
              ggConjAut A hm (Θ f) = Θ g) ∧
        (∀ (hK' : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d))
          (hm : MulAut.conj (φ (LineU.permSU hK' σ)) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ∀ f g : ↥S, (g : Fin d → Multiplicative (ZMod p)) =
              permAut σ (f : Fin d → Multiplicative (ZMod p)) →
              ggConjAut A hm (Θ f) = Θ g) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  have hUF : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK hn hd hp hpq hpd
      (LineU.unitaryUniversalCover_holds n d K hK hd hdn) hψ hker hperf hA hAI hcard
  obtain ⟨u, hord, huq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hUF hp hpq
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hζu : IsPrimitiveRoot (u : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hord ▸ IsPrimitiveRoot.orderOf u)
  let S := ggKGTum_S φ A u hu
  let Θ := ggKGTum_Θ (φ := φ) (A := A) (u := u) (hu := hu) hφs hd0
  have hsurj : Function.Surjective Θ :=
    ggKGTum_Θ_surjective hUF (by omega) hφs hφker hA.2 hdiag hζu hd0
  have hkerΘ : ∀ f : ↥S, Θ f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c :=
    fun f => ggKGTum_Θ_eq_one_iff hUF (by omega) hφs hφker hord hd0 f
  have hSge : p ^ (d - 1) ≤ Nat.card ↥S := by
    have hVle : UCoord.sumZero d p ≤ S := ggKGTum_sumZero_le_S hUF hsc hdiag huq hord
    calc p ^ (d - 1) = Nat.card ↥(UCoord.sumZero d p) :=
          (ggKGTum_card_sumZero hp ⟨(u : K), hζu⟩ (by omega)).symm
      _ ≤ Nat.card ↥S := Nat.card_mono (Set.toFinite _) hVle
  have hS_or : S = ⊤ ∨ S = sumZero d p :=
    ggKGTum_S_eq_top_or_sumZero hp hd hord ⟨u, hζu⟩
      (fun σ {f} hf => ggKGTum_permAut_mem_S hUF hpq (by omega) hφs hφker hA.2 hsc hdiag σ hf)
      hSge
  refine ⟨φ, hφs, hφker, hdiag, S, Θ, hS_or, hsurj, hkerΘ, ?_, ?_⟩
  · intro m hm
    obtain ⟨π, hπ⟩ := ggKGTum_ggConjAut_eq hp hpq hd hd0 hUF hφs hφker hA hsc hdiag hm
    exact ⟨π, hπ⟩
  · intro hK' σ hm f g hfg
    exact ggKGTum_ggConjAut_eq_of_conj_eq hK' hpq (by omega) hd0 hφs hφker hA.2 hsc hdiag
      hm (fun _ _ => rfl) f g hfg

private def frameUdM_root {d p : ℕ} (i j : Fin d) : Fin d → Multiplicative (ZMod p) :=
  (UCoord.rootV (p := p) i j : Fin d → Multiplicative (ZMod p))

private theorem frameUdM_root_apply {d p : ℕ} (i j k : Fin d) :
    frameUdM_root (p := p) i j k =
      Multiplicative.ofAdd ((if k = i then (1 : ZMod p) else 0) -
        (if k = j then 1 else 0)) :=
  rfl

private theorem frameUdM_root_mem_sumZero {d p : ℕ} (i j : Fin d) :
    frameUdM_root (p := p) i j ∈ UCoord.sumZero d p :=
  (UCoord.rootV i j).2

private theorem frameUdM_root_self {d p : ℕ} {i j : Fin d} (hij : i ≠ j) :
    frameUdM_root (p := p) i j i = Multiplicative.ofAdd (1 : ZMod p) := by
  rw [frameUdM_root_apply, if_pos rfl, if_neg hij, sub_zero]

private theorem frameUdM_root_of_ne {d p : ℕ} {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) :
    frameUdM_root (p := p) i j k = 1 := by
  rw [frameUdM_root_apply, if_neg hki, if_neg hkj, sub_self]
  rfl

private theorem frameUdM_exists_notMem_four {d : ℕ} (hd : 5 ≤ d) (a b c e : Fin d) :
    ∃ k : Fin d, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ e := by
  have hcard : ({a, b, c, e} : Finset (Fin d)).card ≤ 4 := by
    have h1 : ({a, b, c, e} : Finset (Fin d)).card ≤
        ({b, c, e} : Finset (Fin d)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({b, c, e} : Finset (Fin d)).card ≤
        ({c, e} : Finset (Fin d)).card + 1 := Finset.card_insert_le _ _
    have h3 : ({c, e} : Finset (Fin d)).card ≤ ({e} : Finset (Fin d)).card + 1 :=
      Finset.card_insert_le _ _
    have h4 : ({e} : Finset (Fin d)).card = 1 := Finset.card_singleton e
    omega
  have hlt : ({a, b, c, e} : Finset (Fin d)).card <
      (Finset.univ : Finset (Fin d)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk⟩

private theorem frameUdM_eq_one_of_notMem {d p : ℕ} {σ : Equiv.Perm (Fin d)} {i j k : Fin d}
    {c : Multiplicative (ZMod p)}
    (hσi : k ≠ σ i) (hσj : k ≠ σ j) (hi : k ≠ i) (hj : k ≠ j)
    (hc : permAut (p := p) σ (frameUdM_root (p := p) i j) *
      (frameUdM_root (p := p) i j)⁻¹ = fun _ => c) : c = 1 := by
  have hk' := congrFun hc k
  rw [Pi.mul_apply, Pi.inv_apply] at hk'
  have hki : σ⁻¹ k ≠ i := by
    intro hh
    apply hσi
    calc k = σ (σ⁻¹ k) := by simp
      _ = σ i := by rw [hh]
  have hkj : σ⁻¹ k ≠ j := by
    intro hh
    apply hσj
    calc k = σ (σ⁻¹ k) := by simp
      _ = σ j := by rw [hh]
  have h1 : permAut (p := p) σ (frameUdM_root (p := p) i j) k = 1 := by
    rw [permAut_apply, Function.comp_apply, frameUdM_root_of_ne hki hkj]
  have h2 : frameUdM_root (p := p) i j k = 1 := frameUdM_root_of_ne hi hj
  rw [h1, h2, inv_one, mul_one] at hk'
  exact hk'.symm

private theorem frameUdM_apply_eq_self {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : Equiv.Perm (Fin d)} {i j : Fin d} (hij : i ≠ j) {c : Multiplicative (ZMod p)}
    (hc1 : c = 1)
    (hc : permAut (p := p) σ (frameUdM_root (p := p) i j) *
      (frameUdM_root (p := p) i j)⁻¹ = fun _ => c) : σ i = i := by
  have hk' := congrFun hc (σ i)
  rw [hc1, Pi.mul_apply, Pi.inv_apply] at hk'
  have h1 : permAut (p := p) σ (frameUdM_root (p := p) i j) (σ i) =
      frameUdM_root (p := p) i j i := by
    rw [permAut_apply, Function.comp_apply]
    simp
  rw [h1, frameUdM_root_self hij, frameUdM_root_apply] at hk'
  have hx : ((if σ i = i then (1 : ZMod p) else 0) - (if σ i = j then 1 else 0)) = 1 := by
    have h' := congrArg Multiplicative.toAdd hk'
    simp only [toAdd_mul, toAdd_inv, toAdd_one, toAdd_ofAdd] at h'
    have h'' : (1 : ZMod p) -
        ((if σ i = i then (1 : ZMod p) else 0) - (if σ i = j then 1 else 0)) = 0 := by
      simpa [sub_eq_add_neg] using h'
    exact (sub_eq_zero.mp h'').symm
  by_cases hii : σ i = i
  · simpa using hii
  · exfalso
    by_cases hjj : σ i = j
    · rw [if_neg hii, if_pos hjj] at hx
      have h2 : (2 : ZMod p) = 0 := by
        have h3 : (-1 : ZMod p) = 1 := by simpa using hx
        linear_combination -h3
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hpge : 2 ≤ p := hp.two_le
      omega
    · rw [if_neg hii, if_neg hjj] at hx
      have h1 : ((1 : ℕ) : ZMod p) = 0 := by simpa using hx.symm
      have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h1
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
      have hpge : 2 ≤ p := hp.two_le
      omega

private theorem frameUdM_permAut_eq_one_of_root {d p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 5 ≤ d)
    {σ : Equiv.Perm (Fin d)}
    (h : ∀ i j : Fin d, i ≠ j → ∃ c : Multiplicative (ZMod p),
      permAut (p := p) σ (frameUdM_root (p := p) i j) *
        (frameUdM_root (p := p) i j)⁻¹ = fun _ => c) :
    σ = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji⟩ : ∃ j : Fin d, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  have hij : i ≠ j := hji.symm
  obtain ⟨c, hc⟩ := h i j hij
  obtain ⟨k, hk⟩ := frameUdM_exists_notMem_four hd (σ i) (σ j) i j
  have hc1 : c = 1 :=
    frameUdM_eq_one_of_notMem hk.1 hk.2.1 hk.2.2.1 hk.2.2.2 hc
  have hsi : σ i = i := frameUdM_apply_eq_self hp hp2 hij hc1 hc
  simpa using hsi

theorem exists_udPermHom {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hdn : (d, n) ≠ (6, 1)) (hd : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    ∃ (S : Subgroup (Fin d → Multiplicative (ZMod p))) (Θ : ↥S →* ↥A)
      (Φ : Equiv.Perm (Fin d) →* MulAut ↥A),
      (S = ⊤ ∨ S = sumZero d p) ∧ Function.Surjective Θ ∧
      (∀ f : ↥S, Θ f = 1 ↔
        ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) ∧
      Function.Injective Φ ∧
      Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
      (∀ (σ : Equiv.Perm (Fin d)) (f g : ↥S),
        (g : Fin d → Multiplicative (ZMod p)) = permAut σ (f : Fin d → Multiplicative (ZMod p)) →
          Φ σ (Θ f) = Θ g) ∧
      ∀ σ : Equiv.Perm (Fin d), ∃ (w : L')
        (hw : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGTorusWeylElt p A w ∧ Φ σ = ggConjAut A hw := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hK' : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  obtain ⟨φ, hφs, hφker, hdiag, S, Θ, hS_or, hΘs, hΘker, hnorm, hperm⟩ :=
    ggUdPermModel hK hn hdn hd hp hpq hpd hψ hker hperf hA hAI hcard hsc
  have hmem : ∀ (σ : Equiv.Perm (Fin d)) {f : Fin d →
      Multiplicative (ZMod p)}, f ∈ S → permAut σ f ∈ S := by
    intro σ f hf
    rcases hS_or with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · rw [h] at hf ⊢
      exact UCoord.permAut_mem_sumZero σ hf
  have hroot_mem : ∀ i j : Fin d, frameUdM_root (p := p) i j ∈ S := by
    intro i j
    rcases hS_or with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · rw [h]
      exact frameUdM_root_mem_sumZero i j
  let mk : Equiv.Perm (Fin d) → ↥S → ↥S := fun σ f =>
    ⟨permAut σ (f : Fin d → Multiplicative (ZMod p)), hmem σ f.2⟩
  let rootS : (i j : Fin d) → ↥S := fun i j => ⟨frameUdM_root (p := p) i j, hroot_mem i j⟩
  let hn : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ (LineU.permSU hK' σ)) ∈
        Subgroup.normalizer (A : Set (MulAut L')) := fun σ =>
    SuDvdRootGen.conj_permSU_mem_normalizer hK' hpq hd3 hφs hφker hdiag hAp hsc σ
  let Φf : Equiv.Perm (Fin d) → MulAut ↥A := fun σ => ggConjAut A (hn σ)
  have hΦ_apply : ∀ (σ : Equiv.Perm (Fin d)) (f : ↥S),
      Φf σ (Θ f) = Θ (mk σ f) := fun σ f => hperm hK' σ (hn σ) f (mk σ f) rfl
  have hΦ_mul : ∀ σ τ : Equiv.Perm (Fin d), Φf σ * Φf τ = Φf (σ * τ) := by
    intro σ τ
    refine MulEquiv.ext fun b => ?_
    obtain ⟨f, rfl⟩ := hΘs b
    rw [MulAut.mul_apply, hΦ_apply τ f, hΦ_apply σ (mk τ f), hΦ_apply (σ * τ) f]
    congr 1
  have hΦ_one : Φf 1 = 1 := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨f, rfl⟩ := hΘs b
    rw [hΦ_apply]
    have h1 : mk 1 f = f := by
      refine Subtype.ext ?_
      show permAut (1 : Equiv.Perm (Fin d))
          (f : Fin d → Multiplicative (ZMod p)) =
        (f : Fin d → Multiplicative (ZMod p))
      funext k
      simp [permAut_apply]
    rw [h1]
    rfl
  let Φ : Equiv.Perm (Fin d) →* MulAut ↥A :=
    { toFun := Φf, map_one' := hΦ_one, map_mul' := fun σ τ => (hΦ_mul σ τ).symm }
  have hΦ_apply' : ∀ (σ : Equiv.Perm (Fin d)) (f : ↥S),
      Φ σ (Θ f) = Θ (mk σ f) := hΦ_apply
  have hrange : Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨σ, rfl⟩
      exact ggConjAut_mem_ggAutomizer
        (MonoidHom.mem_range.mpr ⟨φ (LineU.permSU hK' σ), rfl⟩) (hn σ)
    · intro v hv
      obtain ⟨g, hg, hgN, hgv⟩ := mem_ggAutomizer_iff.mp hv
      obtain ⟨mm, rfl⟩ := MonoidHom.mem_range.mp hg
      have hveq : v = ggConjAut A hgN :=
        MulEquiv.ext fun b => Subtype.ext ((hgv b).trans (ggConjAut_apply A hgN b).symm)
      obtain ⟨π, hπ⟩ := hnorm mm hgN
      refine MonoidHom.mem_range.mpr ⟨π, ?_⟩
      rw [hveq]
      refine MulEquiv.ext fun b => ?_
      obtain ⟨f, rfl⟩ := hΘs b
      rw [hΦ_apply']
      exact (hπ f (mk π f) rfl).symm
  have hkerΦ : ∀ σ : Equiv.Perm (Fin d), Φ σ = 1 → σ = 1 := by
    intro σ hσ
    apply frameUdM_permAut_eq_one_of_root hp hp2 hd
    intro i j hij
    have h1 : Θ (mk σ (rootS i j)) = Θ (rootS i j) := by
      rw [← hΦ_apply']
      have h' := congrArg (fun x : MulAut ↥A => x (Θ (rootS i j))) hσ
      simpa only [MulAut.one_apply] using h'
    have h2 : Θ (mk σ (rootS i j) * (rootS i j)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      simp
    obtain ⟨c, hc⟩ := (hΘker _).mp h2
    exact ⟨c, hc⟩
  have hΦ_inj : Function.Injective Φ := by
    intro σ τ hστ
    have h1 : Φ (σ * τ⁻¹) = 1 := by
      rw [map_mul, hστ, map_inv, mul_inv_cancel]
    have h2 := hkerΦ (σ * τ⁻¹) h1
    rwa [mul_inv_eq_one] at h2
  refine ⟨S, Θ, Φ, hS_or, hΘs, hΘker, hΦ_inj, hrange, ?_, ?_⟩
  · intro σ f g hg
    exact hperm hK' σ (hn σ) f g hg
  · intro σ
    exact ⟨φ (LineU.permSU hK' σ), hn σ,
      SuDvdRootGen.ggTorusWeylElt_permSU hK' hd3 hφker hdiag hAp σ, rfl⟩

end CFSG.StandardType

end
