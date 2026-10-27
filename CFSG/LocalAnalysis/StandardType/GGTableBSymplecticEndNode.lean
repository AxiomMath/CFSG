module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

section Layer

variable {G : Type*} [Group G]

theorem largeEvenLayer_eq_of_commutator_mem {H D : Subgroup G} (hDH : D ≤ H)
    (hcomm : ∀ g ∈ H, ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ D) (hD : CFSG.IsQuasisimple D) :
    LargeEvenLayer H = D ∧ IsComponentOf D H := by
  have hcompD : IsComponentOf D H := by
    refine ⟨hDH, IsSubnormal.step hDH ?_ (IsSubnormal.refl H), (isQuasisimple_iff _).mpr hD⟩
    rw [Subgroup.normal_subgroupOf_iff hDH]
    intro d g hd hg
    have h1 := hcomm g hg d (hDH hd)
    have e : g * d * g⁻¹ = (g * d * g⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact D.mul_mem h1 hd
  have hle : ∀ K' : Subgroup G, IsComponentOf K' H → K' ≤ D := by
    intro K' hK'
    have hK'q : CFSG.IsQuasisimple K' := (isQuasisimple_iff _).mp hK'.2.2
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    rw [← hK'perf, Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact hcomm g (hK'.1 hg) h (hK'.1 hh)
  exact ⟨le_antisymm (sSup_le fun K' hK' => hle K' hK') (le_sSup hcompD), hcompD⟩

end Layer

section SpLevel

open CFSG.SeitzReduction.SymplecticPilot CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n p : ℕ} {ζ : Kˣ}

@[expose] noncomputable def spTorusSt (hζ : ζ ^ p = 1) :
    (Fin n → Multiplicative (ZMod p)) →* StatedSp n K :=
  spTorusSp hζ

theorem coe_spTorusSt (hζ : ζ ^ p = 1) (f : Fin n → Multiplicative (ZMod p)) :
    ((spTorusSt hζ f : StatedSp n K) : GL (Fin n ⊕ Fin n) K) = spTorusGL hζ f :=
  rfl

theorem spTorusSt_eq_diagSp (hζ : ζ ^ p = 1) (f : Fin n → Multiplicative (ZMod p)) :
    spTorusSt (K := K) hζ f = diagSp K n (fun i => zmodPowHom hζ (f i)) := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [mat_diagSp, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_spTorusSt,
    spTorusGL_apply, TauCeti.diagGL_coe]
  congr 1
  funext x
  rcases x with i | i <;> rfl

theorem spTorusSt_mulSingle (hζ : ζ ^ p = 1) (i₀ : Fin n) :
    spTorusSt (K := K) hζ (Pi.mulSingle i₀ (Multiplicative.ofAdd 1)) = rootTorusHom K n i₀ ζ := by
  rw [spTorusSt_eq_diagSp, rootTorusHom_apply]
  congr 1
  funext i
  by_cases hi : i = i₀
  · subst hi
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    have := zmodPowHom_natCast hζ 1
    rwa [Nat.cast_one, pow_one] at this
  · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, map_one]

theorem spTorusSt_mulSingle_pow (hζ : ζ ^ p = 1) [NeZero p] (i₀ : Fin n)
    (a : Multiplicative (ZMod p)) :
    spTorusSt (K := K) hζ (Pi.mulSingle i₀ (Multiplicative.ofAdd 1)) ^
        (Multiplicative.toAdd a).val = spTorusSt hζ (Pi.mulSingle i₀ a) := by
  rw [← map_pow, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem mem_zpowers_of_commute_complSp [CharP K 2] (hK : 4 ≤ Nat.card K) (hζ : ζ ^ p = 1)
    [NeZero p] (hζo : orderOf ζ = p) (f : Fin (n + 1) → Multiplicative (ZMod p))
    (hf : ∀ j ∈ complSp K (0 : Fin (n + 1)), j * spTorusSt hζ f = spTorusSt hζ f * j) :
    spTorusSt (K := K) hζ f ∈
      Subgroup.zpowers
        (spTorusSt hζ (Pi.mulSingle (0 : Fin (n + 1)) (Multiplicative.ofAdd 1))) := by
  have hx1 : spTorusSt (K := K) hζ f ∈
      Subgroup.centralizer (rootTorusSp K (0 : Fin (n + 1)) : Set (StatedSp (n + 1) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    rw [spTorusSt_eq_diagSp, rootTorusHom_apply, ← map_mul, ← map_mul, mul_comm]
  have hx2 : spTorusSt (K := K) hζ f ∈
      Subgroup.centralizer (complSp K (0 : Fin (n + 1)) : Set (StatedSp (n + 1) K)) :=
    Subgroup.mem_centralizer_iff.mpr hf
  have hx3 : spTorusSt (K := K) hζ f ∈ rootTorusSp K (0 : Fin (n + 1)) := by
    rw [← centralizer_rootTorusSp_inf_centralizer_complSp hK (0 : Fin (n + 1))]
    exact ⟨hx1, hx2⟩
  obtain ⟨u, hu⟩ := hx3
  rw [spTorusSt_eq_diagSp, rootTorusHom_apply] at hu
  have hu' := diagSp_injective hu
  have hfi : ∀ i, i ≠ 0 → f i = 1 := by
    intro i hi
    have := congrFun hu' i
    rw [Pi.mulSingle_eq_of_ne hi] at this
    exact (zmodPowHom_eq_one_iff hζ hζo).mp this.symm
  have hf0 : f = Pi.mulSingle (0 : Fin (n + 1)) (f 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, hfi i hi]
  refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd (f 0)).val : ℤ), ?_⟩
  rw [zpow_natCast, spTorusSt_mulSingle_pow, ← hf0]

end SpLevel

section EndNode

open CFSG.SeitzReduction.SymplecticPilot CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    show e z * e x = e x * e z
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy]

theorem four_le_card_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : 4 ≤ Nat.card K := by
  have h3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.le_of_dvd (by omega) hpq
  omega

theorem ggEndNodeElt_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) :
    GGEndNodeElt p m (LargeEvenProj (LargeEvenSpGroup K m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  intro A hA hr _
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hK4 := four_le_card_of_dvd hp hp2 hpq
  have hκ : ζ * ζ ≠ 1 := by
    intro h
    have h2 : ζ ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  set e := spProjEquivSp (K := K) (m := n + 1) with he
  set A₁ : Subgroup (GL (Fin (n + 1) ⊕ Fin (n + 1)) K) :=
    (A.map e.toMonoidHom).map (LargeEvenSpGroup K (n + 1)).subtype with hA₁
  have hA₁e : IsElemAbelian p A₁ := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard₁ : Nat.card A₁ = Nat.card A := by
    rw [hA₁, ← Nat.card_congr ((A.map e.toMonoidHom).equivMapOfInjective
      _ (LargeEvenSpGroup K (n + 1)).subtype_injective).toEquiv,
      ← Nat.card_congr (A.equivMapOfInjective _ e.injective).toEquiv]
  obtain ⟨P, hP, hconj⟩ := exists_conj_eq_range_spTorusGL hp2 (natCast_ne_zero_of_charTwo hp hp2)
    hζo hζ (Subgroup.map_subtype_le _) hA₁e (hcard₁ ▸ hr)
  set Pg : LargeEvenSpGroup K (n + 1) := ⟨P, hP⟩ with hPg
  set Φ : LargeEvenProj (LargeEvenSpGroup K (n + 1)) ≃* StatedSp (n + 1) K :=
    e.trans (MulAut.conj Pg⁻¹) with hΦ
  have hΦapp : ∀ x, ((Φ x : StatedSp (n + 1) K) : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) =
      P⁻¹ * (e x : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) * P := by
    intro x
    show ((Pg⁻¹ * e x * Pg⁻¹⁻¹ : LargeEvenSpGroup K (n + 1)) :
      GL (Fin (n + 1) ⊕ Fin (n + 1)) K) = _
    rw [inv_inv]
    rfl
  have hM2 : ∀ s ∈ A, ∃ f, Φ s = spTorusSt hζ f := by
    intro s hs
    have hmem : P⁻¹ * (e s : GL (Fin (n + 1) ⊕ Fin (n + 1)) K) * P ∈
        (spTorusGL (m := n + 1) hζ).range := by
      rw [← hconj]
      refine ⟨(e s : GL (Fin (n + 1) ⊕ Fin (n + 1)) K), ⟨e s, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, Subtype.ext (by rw [hΦapp, coe_spTorusSt, hf])⟩
  set f₀ : Fin (n + 1) → Multiplicative (ZMod p) :=
    Pi.mulSingle 0 (Multiplicative.ofAdd 1) with hf₀
  set t₁ : StatedSp (n + 1) K := spTorusSt hζ f₀ with ht₁
  obtain ⟨a, ha, hΦa⟩ : ∃ a ∈ A, Φ a = t₁ := by
    have hmem : spTorusGL (m := n + 1) hζ f₀ ∈ A₁.map (MulAut.conj P⁻¹).toMonoidHom := by
      rw [hconj]
      exact ⟨f₀, rfl⟩
    obtain ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hq⟩ := hmem
    refine ⟨a, ha, Subtype.ext ?_⟩
    rw [hΦapp, ht₁, coe_spTorusSt, ← hq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  have ht₁root : t₁ = rootTorusHom K (n + 1) 0 ζ := spTorusSt_mulSingle hζ 0
  have hcentr : ∀ g : StatedSp (n + 1) K, g ∈ Subgroup.centralizer ({t₁} : Set _) →
      g ∈ Subgroup.centralizer ((Subgroup.zpowers t₁ : Subgroup _) : Set (StatedSp (n + 1) K)) := by
    intro g hg
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hg
  obtain ⟨hlay, hcompS⟩ := largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer ({t₁} : Set (StatedSp (n + 1) K)))
    (D := complSp K (0 : Fin (n + 1)))
    (by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff, ht₁root]
      exact ((Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_rootTorusSp 0 hj)) _
        ⟨ζ, rfl⟩).symm)
    (fun g hg h hh => commutator_mem_complSp_of_mem_centralizer hκ (X := Subgroup.zpowers t₁)
      (by rw [← ht₁root]; exact Subgroup.mem_zpowers _) (hcentr g hg) (hcentr h hh))
    (isQuasisimple_complSp hK4 hn 0)
  have hCa : Subgroup.centralizer ({a} : Set (LargeEvenProj (LargeEvenSpGroup K (n + 1)))) =
      (Subgroup.centralizer ({t₁} : Set (StatedSp (n + 1) K))).map Φ.symm.toMonoidHom := by
    rw [map_centralizer_singleton, ← hΦa, MulEquiv.symm_apply_apply]
  have hLa : LargeEvenLayer (Subgroup.centralizer ({a} : Set (LargeEvenProj (LargeEvenSpGroup K
      (n + 1))))) = (complSp K (0 : Fin (n + 1))).map Φ.symm.toMonoidHom := by
    rw [hCa, largeEvenLayer_map_of_injective _ Φ.symm.injective, hlay]
  refine ⟨a, ha, fun h1 => ?_, ?_, fun s hs => ?_⟩
  · have h2 : Φ a = 1 := by rw [h1, map_one]
    rw [hΦa, ht₁root, ← map_one (rootTorusHom K (n + 1) 0)] at h2
    have h3 := rootTorusHom_injective (K := K) (n := n + 1) 0 h2
    rw [h3, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  · rw [hLa, hCa]
    exact isComponentOf_map_of_injective _ Φ.symm.injective hcompS
  · rw [hLa]
    constructor
    · intro hcomm
      obtain ⟨f, hf⟩ := hM2 s hs
      have hf' : ∀ j ∈ complSp K (0 : Fin (n + 1)), j * spTorusSt hζ f = spTorusSt hζ f * j := by
        intro j hj
        have h1 := hcomm (Φ.symm j) ⟨j, hj, rfl⟩
        have h2 := congrArg Φ h1
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hf] at h2
        exact h2.symm
      obtain ⟨k, hk⟩ :=
        Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_commute_complSp hK4 hζ hζo f hf')
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective ?_⟩
      rw [map_zpow, hΦa, hf]
      exact hk
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      obtain ⟨j', hj', rfl⟩ := hj
      apply Φ.injective
      have hroot : t₁ ^ k ∈ rootTorusSp K (0 : Fin (n + 1)) := by
        rw [ht₁root]
        exact Subgroup.zpow_mem _ (rootTorusHom_mem_rootTorusSp 0 ζ) k
      have h1 :=
        (Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_rootTorusSp 0 hj')) _ hroot
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_zpow, MulEquiv.apply_symm_apply, hΦa]
      exact h1

theorem ggEndNode_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) :
    GGEndNode p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggEndNode_of_elt sp_I_subset_inn center_spProj_eq_bot
    (ggEndNodeElt_symplectic hp hp2 hpq hm)

end EndNode

end TableBSymp

end CFSG.StandardType
