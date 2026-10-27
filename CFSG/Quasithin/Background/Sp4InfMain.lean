module

public import CFSG.Quasithin.Background.Sp4InfTwist
public import CFSG.Quasithin.Background.Sp4InfData
public import CFSG.Quasithin.Background.B69SL3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (proj_surjective)
open CFSG.QuasithinUnique.Lin2.Five (tauSp projEquiv)
open B6

namespace B69

theorem false_of_twist_sp4_gen {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hAs : rAV A < 1)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (r : ↥L →* ↥(StatedSp 2 K))
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (e₁ : Sec W₁ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₁ : ∀ (hLW : L ≤ stabSub W₁) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₁ (fixV L)),
      e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s))
    (t : MulAut V) (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L)
    (htw : ∃ (A' : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K), ∀ l l' : ↥L,
      (l' : MulAut V) = t * l * t⁻¹ →
        (((r l' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
            (((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) K,
      (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) K),
        Φ (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x) =
          matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (Φ x)) → False)
    (hnorm : ∀ x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K), x ∈ pairSub (Fin 2 ⊕ Fin 2) K →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x * pairHom (StatedSp 2 K) tauSp γ * x⁻¹ = pairHom (StatedSp 2 K) tauSp δ) →
      (∀ γ ∈ r.range, ∃ δ ∈ r.range,
        x⁻¹ * pairHom (StatedSp 2 K) tauSp γ * x = pairHom (StatedSp 2 K) tauSp δ) →
      x ∈ Sp4.pairNormSp K) : False := by
  classical
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hLperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := mem_normalizer_of_forall_mem ht ht'
  set W₂ : Subgroup V := W₁.map (t⁻¹ : MulAut V).toMonoidHom with hW₂
  have hW₂irr : W₂ ∈ IrrPlus L (⊤ : Subgroup V) :=
    irrPlus_map (g := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht' x hx)
      (fun x hx => by rw [inv_inv]; exact ht x hx) hW₁
  have hmemW₂ : ∀ w, w ∈ W₂ ↔ t w ∈ W₁ := fun w => by
    rw [hW₂, mem_map_aut_iff, inv_inv]
  have hLW₁ : L ≤ stabSub W₁ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₁).1
  have hLW₂ : L ≤ stabSub W₂ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₂irr).1
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  have hA₁ := a_stab_irr hV hA hL hLA hW₁
  have hA₂ := a_stab_irr hV hA hL hLA hW₂irr
  have hAW₁ : A ≤ stabSub W₁ := B1.le_stabSub_of_invariant hA₁
  have hAW₂ : A ≤ stabSub W₂ := B1.le_stabSub_of_invariant hA₂
  have hAU : A ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant fun a ha w hw =>
    mem_fixV_of_conj (fun x hx => by simpa using hAn a⁻¹ (A.inv_mem ha) x hx) hw
  let eT : ↥W₂ ≃* ↥W₁ :=
    { toFun := fun w => ⟨t (w : V), (hmemW₂ w).1 w.2⟩
      invFun := fun w => ⟨t⁻¹ (w : V), (hmemW₂ _).2 (by simp)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hfixt : ∀ w ∈ fixV L, t w ∈ fixV L := fun w hw => mem_fixV_of_conj ht' hw
  have hfixt' : ∀ w ∈ fixV L, t⁻¹ w ∈ fixV L := fun w hw =>
    mem_fixV_of_conj (t := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht x hx) hw
  have hmapC : ((fixV L).subgroupOf W₂).map eT.toMonoidHom = (fixV L).subgroupOf W₁ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfixt _ hx
    · intro hy
      exact ⟨eT.symm y, hfixt' _ hy, eT.apply_symm_apply y⟩
  let τ : Sec W₂ (fixV L) ≃* Sec W₁ (fixV L) := QuotientGroup.congr _ _ eT hmapC
  let c : MulAut ↥L := indAut L t
  have hc : ∀ l : ↥L, ((c l : ↥L) : MulAut V) = t * l * t⁻¹ := fun l => coe_indAut_apply htN l
  have hτ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      τ (B5.secHom L hLW₂ hLU l s) = B5.secHom L hLW₁ hLU (c l) (τ s) := by
    intro l s
    induction s using QuotientGroup.induction_on with
    | H w =>
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show t ((l : MulAut V) (w : V)) = ((c l : ↥L) : MulAut V) (t (w : V))
      rw [hc]
      simp [MulAut.mul_apply]
  let e₂₀ : Sec W₂ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K := τ.trans e₁
  have he₂₀ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      e₂₀ (B5.secHom L hLW₂ hLU l s) =
        matAut ((r (c l) : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₂₀ s) := by
    intro l s
    show e₁ (τ (B5.secHom L hLW₂ hLU l s)) = matAut _ (e₁ (τ s))
    rw [hτ]
    exact he₁ hLW₁ hLU (c l) (τ s)
  obtain ⟨A', σ, hmat⟩ := htw
  obtain ⟨e₂', he₂'⟩ := exists_tau_coord_of_mat (K := K) (B5.secHom L hLW₂ hLU) r
    (r.comp c.toMonoidHom) A' σ (fun l => hmat l (c l) (hc l)) e₂₀ he₂₀
  have hB : ¬ A ≤ centSec W₁ (fixV L) := by
    intro hle
    apply commSub_ne_bot_of_irr hLA hW₁
    rw [commSub_eq_bot_iff]
    intro w hw a ha
    exact sec_triv_imp_triv hL hAn hW₁ hA₁ ha (hle ha).2 w hw
  have hne : W₁ ≠ W₂ := ne_of_tau' r hLW₁ hLW₂ hLU e₁ e₂' (he₁ hLW₁ hLU) he₂' hniso
  have hGT := card_le_of_tau hn hK hA.1.2.2.1 hAn hAW₁ hAW₂ hAU hLW₁ hLW₂ hLU r hnorm e₁ e₂'
    (he₁ hLW₁ hLU) he₂' hB
  exact false_of_two_sections₁ hV hA hAs hL hLA hW₁ hW₂irr hne hGT


theorem false_of_twist_sp4 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hAs : rAV A < 1)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (r : ↥L →* ↥(StatedSp 2 K)) (hr : Function.Surjective r)
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (e₁ : Sec W₁ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₁ : ∀ (hLW : L ≤ stabSub W₁) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₁ (fixV L)),
      e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s))
    (t : MulAut V) (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L)
    (thb : MulAut (StatedProj (StatedSp 2 K)))
    (hthb : ∀ l l' : ↥L, (l' : MulAut V) = t * l * t⁻¹ →
      thb (proj 2 K (r l)) = proj 2 K (r l'))
    (hnot : ¬ TypePresSp thb) : False := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  obtain ⟨A', σ, h⟩ := exists_tau_mat thb hnot
  refine false_of_twist_sp4_gen hV hA hAs hL hLA hn hK r hW₁ e₁ he₁ t ht ht'
    ⟨A', σ, fun l l' hl' => ?_⟩ (fun Φ hΦ => not_exists_tau_iso Φ fun γ x => ?_)
    (hnorm_of_surjective r hr)
  · rw [← h (r l)]
    have : (projEquiv K).symm (thb (projEquiv K (r l))) = r l' := by
      rw [MulEquiv.symm_apply_eq]
      exact hthb l l' hl'
    rw [this]
  · obtain ⟨l, rfl⟩ := hr γ
    exact hΦ l x

@[expose] def AsB69NoStrongSp4One : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X) (A L : Subgroup (MulAut V)),
      StrongComponent V X S M A L →
      ¬ SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G _ =>
        BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1 ∧ qOf G = ((2 / 3 : ℚ) : WithTop ℚ))

theorem noStrongSp4_of_one (hone : AsB69NoStrongSp4One) : AsB69NoStrongSp4 := by
  intro V _ _ hV X S M A L hdata hcase
  obtain ⟨I, hI, ⟨n, hn, hHL⟩, hq⟩ := hcase
  by_cases hn1 : n = 1
  · subst hn1
    exact hone V hV X S M A L hdata ⟨I, hI, hn, hq⟩
  obtain ⟨-, hmp, -, hA, hAs, hL, hLA⟩ := hdata
  obtain ⟨K, hKf, hKfin, hK, hreal⟩ := hn
  have hn0 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have hn2 : 1 < n := by omega
  have hHL' : ffJ (secGroup L A I) = secL L A I := hHL hn2
  have hn' : BinaryNaturalSp4 (secL L A I) ⊤ ⊥ n := by
    rw [← hHL']
    exact ⟨K, hKf, hKfin, hK, hreal⟩
  clear hK hreal hKf hKfin K
  obtain ⟨K, hKf, hKfin, hK, r, hr, e₁, he₁⟩ := exists_natural_data_sp4 hI hn'
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn0 hK
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have hW₁ := B1Red.mem_irrPlus_of_autSub (le_stabSub_redU L A) hI
  have : Finite (MulAut V) := MulEquiv.finite_left
  let π₀ : ↥L →* StatedProj (StatedSp 2 K) := (proj 2 K).comp r
  have hπ₀ : Function.Surjective π₀ := proj_surjective.comp hr
  have : Nontrivial (StatedProj (StatedSp 2 K)) := by
    have h := even_natCard_statedProj_sp (K := K)
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hpos : 0 < Nat.card (StatedProj (StatedSp 2 K)) := Nat.card_pos
    obtain ⟨m, hm⟩ := h
    omega
  have hker₀ : π₀.ker = Subgroup.center ↥L :=
    ker_eq_center_of_surj hLq (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (F := K))
      π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* StatedProj (StatedSp 2 K) := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2
      (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (F := K)) πh hπh
  obtain ⟨t, -, htN, hall⟩ := exists_swap swapGeo_sp4 even_natCard_statedProj_sp hmp hLhat πh hπh
    hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ TypePresSp thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  exact false_of_twist_sp4 hV hA hAs hLq hLA hn0 hK r hr hW₁ e₁ he₁ (t : MulAut V) ht ht' thb
    (fun l l' hl' => by
      have := hthb l
      rw [hind l l' hl'] at this
      exact this) hnot

end B69

end CFSG.Quasithin
