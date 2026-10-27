module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68
  CFSG.QuasithinUnique.Vol2Native.L239

section S8

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G}

theorem center_eq_bot_of_simple_quasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hs : IsSimpleGroup X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have hcomm : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).2 h1
    have htop : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
    have hbt : (⊥ : Subgroup X) = ⊤ := hcomm.symm.trans htop
    have hs' := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    exact hx (by simpa using (show x ∈ (⊥ : Subgroup X) by rw [hbt]; trivial))

theorem nonempty_quot_perm_eight (hQ2 : IsPGroup 2 Q) (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple ↥L) (hs : IsSimpleGroup ↥L) (e : ↥L ≃* alternatingGroup (Fin 8))
    (hout : ∃ s ∈ Q, InducesOuter s L) :
    Nonempty ((↥(L ⊔ Q) ⧸ CFSG.pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  have hXN : L ⊔ Q ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hQN
  let ρ : ↥(L ⊔ Q) →* MulAut ↥L := actHom L (L ⊔ Q) hXN
  let c : Equiv.Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 8))
  have hc : Function.Bijective c :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num)
  let κ : MulAut ↥L ≃* Equiv.Perm (Fin 8) :=
    (MulAut.congr e).trans (MulEquiv.ofBijective c hc).symm
  let φ : ↥(L ⊔ Q) →* Equiv.Perm (Fin 8) := κ.toMonoidHom.comp ρ
  have hκconj : ∀ l : ↥L, κ (MulAut.conj l) = ((e l : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)) := by
    intro l
    show (MulEquiv.ofBijective c hc).symm (MulAut.congr e (MulAut.conj l)) = _
    rw [MulEquiv.symm_apply_eq]
    ext y
    simp [c, MulAut.conjNormal_apply, MulAut.congr_apply, MulAut.conj_apply]
  have hρL : ∀ (l : G) (hl : l ∈ L), ρ ⟨l, Subgroup.mem_sup_left hl⟩ =
      MulAut.conj (⟨l, hl⟩ : ↥L) := fun l hl =>
    conjOn_of_mem L ⟨l, hl⟩ (hXN (Subgroup.mem_sup_left hl))
  have hφL : ∀ l : ↥L, φ ⟨(l : G), Subgroup.mem_sup_left l.2⟩ =
      ((e l : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) := fun l => by
    show κ (ρ ⟨(l : G), Subgroup.mem_sup_left l.2⟩) = _
    rw [hρL (l : G) l.2]
    exact hκconj l
  have hkerφ : ∀ x : ↥(L ⊔ Q), φ x = 1 ↔ ρ x = 1 := fun x => map_eq_one_iff κ κ.injective
  obtain ⟨s, hsQ, hsN, hsin⟩ := hout
  let sX : ↥(L ⊔ Q) := ⟨s, Subgroup.mem_sup_right hsQ⟩
  have hsodd : Equiv.Perm.sign (φ sX) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φ sX)) with h1 | h1
    · exfalso
      apply hsin
      have hmem : φ sX ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 h1
      set l0 : ↥L := e.symm ⟨φ sX, hmem⟩ with hl0
      have h2 : ρ sX = MulAut.conj l0 := by
        apply κ.injective
        rw [hκconj l0, hl0, MulEquiv.apply_symm_apply]
        rfl
      have h3 : ∀ w : ↥L, s * (w : G) * s⁻¹ = (l0 : G) * (w : G) * (l0 : G)⁻¹ := fun w => by
        have := congrArg (fun γ : MulAut ↥L => ((γ w : ↥L) : G)) h2
        simpa [ρ, actHom_apply, conjOn_coe, MulAut.conj_apply] using this
      refine ⟨(l0 : G), l0.2, fun x hx => ?_⟩
      have hy : s⁻¹ * x * s ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) x).mp hx
        simpa using this
      have h4 := h3 ⟨s⁻¹ * x * s, hy⟩
      calc s⁻¹ * x * s = (l0 : G)⁻¹ * ((l0 : G) * (s⁻¹ * x * s) * (l0 : G)⁻¹) * (l0 : G) := by
            group
        _ = (l0 : G)⁻¹ * (s * (s⁻¹ * x * s) * s⁻¹) * (l0 : G) := by rw [← h4]
        _ = (l0 : G)⁻¹ * x * (l0 : G) := by group
    · exact h1
  have key : ∀ τ : Equiv.Perm (Fin 8), τ ∈ alternatingGroup (Fin 8) → ∃ x, φ x = τ := by
    intro τ hτ
    refine ⟨⟨((e.symm ⟨τ, hτ⟩ : ↥L) : G), Subgroup.mem_sup_left (e.symm ⟨τ, hτ⟩).2⟩, ?_⟩
    rw [hφL]
    simp
  have hsurj : Function.Surjective φ := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · exact key σ (Equiv.Perm.mem_alternatingGroup.2 h1)
    · have hev : σ * (φ sX)⁻¹ ∈ alternatingGroup (Fin 8) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, h1, hsodd]
        decide
      obtain ⟨x, hx⟩ := key _ hev
      exact ⟨x * sX, by rw [map_mul, hx]; group⟩
  have h_le1 : φ.ker ≤ CFSG.pCore 2 ↥(L ⊔ Q) := by
    have hKn : φ.ker.Normal := MonoidHom.normal_ker φ
    have hKp : IsPGroup 2 ↥φ.ker := by
      intro k
      have hkc : ((k : ↥(L ⊔ Q)) : G) ∈ Subgroup.centralizer (L : Set G) :=
        (conjOn_eq_one_iff L (hXN (k : ↥(L ⊔ Q)).2)).1 ((hkerφ _).1 k.2)
      obtain ⟨m, hm⟩ := exists_pow_mem_of_mem_sup hQ2 hQN (k : ↥(L ⊔ Q)).2
      refine ⟨m, ?_⟩
      have hmc : ((k : ↥(L ⊔ Q)) : G) ^ 2 ^ m ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.pow_mem _ hkc _
      have h1 : (⟨((k : ↥(L ⊔ Q)) : G) ^ 2 ^ m, hm⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hmc g g.2)
      rw [hZ, Subgroup.mem_bot] at h1
      have h2 : ((k : ↥(L ⊔ Q)) : G) ^ 2 ^ m = 1 := congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext h2)
    exact le_sSup (show φ.ker ∈ {K : Subgroup ↥(L ⊔ Q) | K.Normal ∧ IsPGroup 2 K} from
      ⟨hKn, hKp⟩)
  have h_le2 : CFSG.pCore 2 ↥(L ⊔ Q) ≤ φ.ker := by
    intro n hn
    refine (hkerφ n).2 ((conjOn_eq_one_iff L (hXN n.2)).2
      (Subgroup.mem_centralizer_iff.2 fun l hl => ?_))
    have hPn : (CFSG.pCore 2 ↥(L ⊔ Q)).Normal := CFSG.pCore_normal
    let ι : ↥L →* ↥(L ⊔ Q) := (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Q))
    let D : Subgroup ↥L := (CFSG.pCore 2 ↥(L ⊔ Q)).comap ι
    have hDn : D.Normal := Subgroup.normal_comap ι
    have hD : D = ⊥ := by
      have : D.Normal := hDn
      rcases hs.eq_bot_or_eq_top_of_normal D with hD | hD
      · exact hD
      · exfalso
        have hp : IsPGroup 2 ↥L := by
          intro l'
          have hl' : l' ∈ D := by rw [hD]; trivial
          obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(L ⊔ Q))) ⟨ι l', hl'⟩
          refine ⟨m, Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ Q) ?_⟩
          have h2 : (ι l') ^ 2 ^ m = 1 := congrArg Subtype.val hm
          show ι (l' ^ 2 ^ m) = ι 1
          rw [map_pow, map_one]
          exact h2
        have : Group.IsPerfect ↥L := hq.1
        have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
        exact Group.IsPerfect.not_isNilpotent ↥L hp.isNilpotent
    have hlL : l ∈ L := hl
    have hnN : (n : G) ∈ Subgroup.normalizer (L : Set G) := hXN n.2
    have hcL : (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hnN l).mp hlL) (L.inv_mem hlL)
    have hcP : n * ι ⟨l, hlL⟩ * n⁻¹ * (ι ⟨l, hlL⟩)⁻¹ ∈ CFSG.pCore 2 ↥(L ⊔ Q) := by
      have e1 : n * ι ⟨l, hlL⟩ * n⁻¹ * (ι ⟨l, hlL⟩)⁻¹ =
          n * (ι ⟨l, hlL⟩ * n⁻¹ * (ι ⟨l, hlL⟩)⁻¹) := by group
      rw [e1]
      exact (CFSG.pCore 2 ↥(L ⊔ Q)).mul_mem hn
        (hPn.conj_mem n⁻¹ ((CFSG.pCore 2 ↥(L ⊔ Q)).inv_mem hn) (ι ⟨l, hlL⟩))
    have hcD : (⟨(n : G) * l * (n : G)⁻¹ * l⁻¹, hcL⟩ : ↥L) ∈ D := hcP
    rw [hD, Subgroup.mem_bot] at hcD
    have h1 : (n : G) * l * (n : G)⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hcD
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hker : CFSG.pCore 2 ↥(L ⊔ Q) = φ.ker := le_antisymm h_le2 h_le1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

end S8

end E68Proof

end E6

end CFSG.Quasithin
