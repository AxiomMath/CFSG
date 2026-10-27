module

public import CFSG.Quasithin.SteinbergBTCoprimeQuotientSylowTransport
public import CFSG.Quasithin.SteinbergCDCommutingSupportsLinePair
public import CFSG.Quasithin.SteinbergBQTriangularPrimeLine
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open CFSG.Quasithin.SteinbergCC (coreQuotConj)
open scoped Pointwise MatrixGroups

section Bridge

variable {L : Type*} [Group L]

theorem normal_map_pCore (p : ℕ) (X : Subgroup L) [X.Normal] :
    ((CFSG.pCore p X).map X.subtype).Normal :=
  ConjAct.normal_of_characteristic_of_normal

theorem exists_coreQuot_mulEquiv_map (X : Subgroup L) [X.Normal] (A : Subgroup L) [A.Normal]
    (hA : A = (CFSG.pCore 2 X).map X.subtype) :
    ∃ ι : (X ⧸ CFSG.pCore 2 X) ≃* X.map (QuotientGroup.mk' A),
      (∀ x : X, (ι x : L ⧸ A) = ((x : L) : L ⧸ A)) ∧
      ∀ (l : L) (w : X ⧸ CFSG.pCore 2 X),
        (ι (coreQuotConj X l w) : L ⧸ A) = (l : L ⧸ A) * ι w * (l : L ⧸ A)⁻¹ := by
  set f : X →* L ⧸ A := (QuotientGroup.mk' A).comp X.subtype with hf
  have hker : f.ker = CFSG.pCore 2 X := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hA]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hrange : f.range = X.map (QuotientGroup.mk' A) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  let ι : (X ⧸ CFSG.pCore 2 X) ≃* X.map (QuotientGroup.mk' A) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  have hι : ∀ x : X, (ι x : L ⧸ A) = ((x : L) : L ⧸ A) := fun _ => rfl
  refine ⟨ι, hι, fun l w => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  rw [SteinbergCC.coreQuotConj_mk, hι, hι]
  change (((l * x * l⁻¹ : L)) : L ⧸ A) = _
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem map_mk_facts_of_coreQuot {p : ℕ} (X : Subgroup L) [X.Normal] (A : Subgroup L) [A.Normal]
    (hA : A = (CFSG.pCore 2 X).map X.subtype)
    (hXe : CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X))
    (hirr : ∀ U : Subgroup (X ⧸ CFSG.pCore 2 X),
      (∀ l : L, ∀ u ∈ U, coreQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤) :
    CFSG.IsElementaryAbelian p (X.map (QuotientGroup.mk' A)) ∧
      Nat.card (X.map (QuotientGroup.mk' A)) = Nat.card (X ⧸ CFSG.pCore 2 X) ∧
      ∀ W : Subgroup (L ⧸ A), W ≤ X.map (QuotientGroup.mk' A) →
        (∀ g : L, ∀ w ∈ W, (g : L ⧸ A) * w * (g : L ⧸ A)⁻¹ ∈ W) →
        W = ⊥ ∨ W = X.map (QuotientGroup.mk' A) := by
  obtain ⟨ι, -, hιc⟩ := exists_coreQuot_mulEquiv_map X A hA
  refine ⟨?_, Nat.card_congr ι.toEquiv.symm, fun W hWX hWinv => ?_⟩
  · have : IsMulCommutative (X.map (QuotientGroup.mk' A)) := ⟨⟨fun a b => ι.symm.injective (by
      rw [map_mul, map_mul]
      exact hXe.toIsMulCommutative.is_comm.comm _ _)⟩⟩
    refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ι.symm.injective ?_⟩
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hXe.exponent_dvd_p _
  set U : Subgroup (X ⧸ CFSG.pCore 2 X) :=
    (W.subgroupOf (X.map (QuotientGroup.mk' A))).comap ι.toMonoidHom with hU
  have hmemU : ∀ u, u ∈ U ↔ ((ι u : L ⧸ A) ∈ W) := fun _ => Iff.rfl
  have hUinv : ∀ l : L, ∀ u ∈ U, coreQuotConj X l u ∈ U := by
    intro l u hu
    rw [hmemU, hιc]
    exact hWinv l _ ((hmemU u).mp hu)
  rcases hirr U hUinv with h | h
  · left
    refine eq_bot_iff.mpr fun w hw => ?_
    obtain ⟨u, hu⟩ : ∃ u, ι u = ⟨w, hWX hw⟩ := ⟨ι.symm ⟨w, hWX hw⟩, ι.apply_symm_apply _⟩
    have huU : u ∈ U := by
      rw [hmemU, hu]
      exact hw
    rw [h, Subgroup.mem_bot] at huU
    rw [huU, map_one] at hu
    rw [Subgroup.mem_bot]
    exact (congrArg Subtype.val hu).symm
  · right
    refine le_antisymm hWX fun y hy => ?_
    have huU : ι.symm ⟨y, hy⟩ ∈ U := by
      rw [h]
      exact Subgroup.mem_top _
    rw [hmemU, ι.apply_symm_apply] at huU
    exact huU

end Bridge

theorem perfect_odd_plane_excludes_terminal_support_models {L : Type*} [Group L] [Finite L]
    (hL : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup L} [X.Normal]
    (hXe : CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X))
    (hXc : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2)
    (hirr : ∀ U : Subgroup (X ⧸ CFSG.pCore 2 X),
      (∀ l : L, ∀ u ∈ U, coreQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (¬ ∃ P P₁ P₂ A₁ A₂ : Subgroup L, CFSG.ABGLocalTools.IsSylowOf p P X ∧
        P₁ ≤ P ∧ P₂ ≤ P ∧ Nat.card P₁ = p ∧ Nat.card P₂ = p ∧
        P₁ ⊔ P₂ = P ∧ P₁ ⊓ P₂ = ⊥ ∧ ⁅P₁, P₂⁆ = ⊥ ∧
        A₁ ≤ (CFSG.pCore 2 X).map X.subtype ∧ A₂ ≤ (CFSG.pCore 2 X).map X.subtype ∧
        P ≤ normalizer (A₁ : Set L) ∧ P ≤ normalizer (A₂ : Set L) ∧
        (((CFSG.pCore 2 X).map X.subtype : Subgroup L) : Set L) = (A₁ : Set L) * (A₂ : Set L) ∧
        ⁅A₁, A₂⁆ = ⊥ ∧ ⁅A₁, P₂⁆ = ⊥ ∧ ⁅A₂, P₁⁆ = ⊥ ∧ ⁅A₁, P₁⁆ ≠ ⊥ ∧ ⁅A₂, P₂⁆ ≠ ⊥) ∧
      ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (l : kˣ), orderOf l = p →
        ∀ (C : Subgroup SL(3, k)) [C.Normal],
          (∀ c ∈ C, ∃ a : kˣ, a ^ 3 = 1 ∧ (c : Matrix (Fin 3) (Fin 3) k) = (a : k) • 1) →
          IsEmpty (X ≃* ((SteinbergBQ.triX (Subgroup.zpowers l)).map (QuotientGroup.mk' C))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : p ≠ p ^ 2 := by
    intro h
    have : p ^ 1 = p ^ 2 := by rw [pow_one]; exact h
    have := Nat.pow_right_injective hp.two_le this
    omega
  refine ⟨?_, ?_⟩
  ·
    rintro ⟨P, P₁, P₂, A₁, A₂, hP, hP₁P, hP₂P, hP₁, hP₂, hPsup, hPinf, hPcomm, -, -, hinv₁,
      hinv₂, hAeq, -, hc₁, hc₂, hn₁, hn₂⟩
    set A := (CFSG.pCore 2 X).map X.subtype with hAdef
    have : A.Normal := normal_map_pCore 2 X
    obtain ⟨hXe', hXc', hirr'⟩ := map_mk_facts_of_coreQuot X A rfl hXe hirr
    have hpA : ¬ p ∣ Nat.card A := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ((CFSG.pCore_isPGroup (p := 2) (G := X)).map
        X.subtype) : ∃ n, Nat.card A = 2 ^ n)
      rw [hn]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
      omega
    have hno := (SteinbergBT.coprime_abelian_quotient_Sylow_action_transport hp A X
      (Subgroup.map_subtype_le _) hpA hXe' (hXc'.trans hXc) P hP).2.2.2.2 hL hirr'
    obtain ⟨-, -, hpair⟩ := SteinbergCD.commuting_supports_detect_intrinsic_prime_line_pair hp
      hpA hPsup hPinf hPcomm hP₁ hP₂ hinv₁ hinv₂ hAeq hc₁ hc₂ hn₁ hn₂
    apply hno
    refine ⟨{P₁, P₂}, ⟨P₁, Finset.mem_insert_self _ _⟩, Finset.card_le_two, ?_, ?_⟩
    · intro Q hQ
      have hne : ∀ {R S : Subgroup L}, Nat.card R = p → Nat.card S = p → R ⊓ S = ⊥ → S ≤ R →
          False := by
        intro R S hR hS hRS hSR
        rw [inf_eq_right.mpr hSR] at hRS
        rw [hRS, Subgroup.card_bot] at hS
        exact hp.one_lt.ne hS
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · refine ⟨hP₁P, fun h => ?_, fun h => ?_⟩
        · rw [h, Subgroup.card_bot] at hP₁
          exact hp.one_lt.ne hP₁
        · exact hne hP₁ hP₂ hPinf (h ▸ hP₂P)
      · rw [Finset.mem_singleton] at hQ
        subst hQ
        refine ⟨hP₂P, fun h => ?_, fun h => ?_⟩
        · rw [h, Subgroup.card_bot] at hP₂
          exact hp.one_lt.ne hP₂
        · exact hne hP₂ hP₁ (inf_comm P₁ Q ▸ hPinf) (h ▸ hP₁P)
    · intro n hn Q hQ
      have hn' : n⁻¹ ∈ normalizer (A : Set L) ⊓ normalizer (P : Set L) := by
        refine Subgroup.mem_inf.mpr ⟨?_, inv_mem hn⟩
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      have hset := hpair n⁻¹ hn'
      have hconj : ∀ R : Subgroup L, R.map (MulAut.conj n).toMonoidHom = CFSG.conjugate R n⁻¹ :=
        fun R => by rw [CFSG.conjugate, inv_inv]
      have hmem : Q.map (MulAut.conj n).toMonoidHom ∈
          ({CFSG.conjugate P₁ n⁻¹, CFSG.conjugate P₂ n⁻¹} : Set (Subgroup L)) := by
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact Or.inl (hconj _)
        · rw [Finset.mem_singleton] at hQ
          subst hQ
          exact Or.inr (hconj _)
      rw [hset] at hmem
      rcases hmem with h | h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  ·
    intro k _ _ _ l hl C _ hC
    refine ⟨fun e => ?_⟩
    set μ := Subgroup.zpowers l with hμ
    set π : SL(3, k) →* SL(3, k) ⧸ C := QuotientGroup.mk' C with hπdef
    set Xb := (SteinbergBQ.triX μ).map π with hXb
    have hπ : ∀ g ∈ π.ker, ∃ c : kˣ, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • 1 := by
      intro g hg
      rw [hπdef, QuotientGroup.ker_mk'] at hg
      exact hC g hg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hline, hinv⟩ :=
      SteinbergBQ.triangular_three_space_characteristic_prime_line hp5 hl hμ π hπ hXb rfl rfl
    set ℓ := ((Xb ⊓ Subgroup.centralizer ((Subgroup.center ((SteinbergBQ.triA k).map π)).map
      ((SteinbergBQ.triA k).map π).subtype : Set (SL(3, k) ⧸ C))).subgroupOf Xb).map
      (QuotientGroup.mk' (CFSG.pCore 2 Xb)) with hℓ
    have hpc : (CFSG.pCore 2 X).map (e : X →* Xb) = CFSG.pCore 2 Xb := CFSG.pCore_map_iso 2 e
    let ē : (X ⧸ CFSG.pCore 2 X) ≃* (Xb ⧸ CFSG.pCore 2 Xb) :=
      QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 Xb) e hpc
    set U := ℓ.map ē.symm.toMonoidHom with hU
    have hmemU : ∀ u, u ∈ U ↔ ē u ∈ ℓ := fun u => by
      rw [hU, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    have hUc : Nat.card U = p := by
      rw [hU, Subgroup.card_map_of_injective (f := ē.symm.toMonoidHom) ē.symm.injective]
      exact hline
    have hUinv : ∀ l' : L, ∀ u ∈ U, coreQuotConj X l' u ∈ U := by
      intro l' u hu
      set σ : MulAut Xb := (e.symm.trans (MulAut.conjNormal l')).trans e with hσ
      obtain ⟨hσc, hσℓ⟩ := hinv σ
      have hcomm : ē (coreQuotConj X l' u) =
          (QuotientGroup.congr _ _ σ hσc : Xb ⧸ CFSG.pCore 2 Xb →* Xb ⧸ CFSG.pCore 2 Xb)
            (ē u) := by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
        rw [SteinbergCC.coreQuotConj_mk]
        change ((e (MulAut.conjNormal l' x) : Xb) : Xb ⧸ CFSG.pCore 2 Xb) =
          ((σ (e x) : Xb) : Xb ⧸ CFSG.pCore 2 Xb)
        rw [hσ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hmemU, hcomm, ← hσℓ]
      exact Subgroup.mem_map_of_mem _ ((hmemU u).mp hu)
    rcases hirr U hUinv with h | h
    · rw [h, Subgroup.card_bot] at hUc
      exact hp.one_lt.ne hUc
    · rw [h, Subgroup.card_top, hXc] at hUc
      exact hp1 hUc.symm

end CFSG.Quasithin.H13.NQTerm
