module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Avg
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace FFL

theorem toAdd_permAct_mul_inv {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : G6.PermMod m) (i : Fin m) :
    Multiplicative.toAdd (G6.permAct m σ x * x⁻¹) i =
      Multiplicative.toAdd x (σ⁻¹ i) - Multiplicative.toAdd x i := by
  rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
  exact (sub_eq_add_neg _ _).symm

theorem altDn_mem_ker_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (hm : 0 < m) {x : G6.PermMod m}
    (hx : x ∈ G6.coreMod m) :
    G6.permAct m σ x * x⁻¹ ∈ Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m ↔
      F420.HeartFixed σ (Multiplicative.toAdd x) := by
  constructor
  · rintro ⟨⟨k, hk⟩, -⟩ i j
    have hi := congrFun (congrArg Multiplicative.toAdd hk) i
    have hj := congrFun (congrArg Multiplicative.toAdd hk) j
    rw [toAdd_permAct_mul_inv] at hi hj
    rw [← hi, ← hj]
    simp [G6.allOnes]
  · intro h
    refine ⟨?_, (G6.coreMod m).mul_mem (G6.permAct_mem_coreMod _ hx) ((G6.coreMod m).inv_mem hx)⟩
    set c := Multiplicative.toAdd x (σ⁻¹ ⟨0, hm⟩) - Multiplicative.toAdd x ⟨0, hm⟩ with hc
    refine ⟨(c.val : ℤ), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_permAct_mul_inv, h i ⟨0, hm⟩, ← hc]
    simp [G6.allOnes]

theorem exists_fixesFixed_altDn {m : ℕ} (h5 : 5 ≤ m) (h8 : m ≤ 8) :
    ∃ T₀ : Subgroup ↥(alternatingGroup (Fin m)), IsPGroup 2 T₀ ∧
      ∃ γ : ↥(alternatingGroup (Fin m)), orderOf γ = 3 ∧ FixesFixed (FFModel.altDn m) T₀ γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥(alternatingGroup (Fin m)) := default
  have hS : CFSG.Open.quasithinIsSylowTwo (P : Subgroup ↥(alternatingGroup (Fin m))) :=
    ⟨P.isPGroup', P.not_dvd_index⟩
  obtain ⟨g, hg3, hfix⟩ := F420.exists_orderOf_eq_three_heart m h5 h8 P hS
  have hm : 0 < m := by omega
  refine ⟨P, P.isPGroup', g, hg3, fun x hx hT => (altDn_mem_ker_iff (g : Equiv.Perm (Fin m)) hm
    hx).mpr ?_⟩
  have h := hfix ⟨Multiplicative.toAdd x, hx⟩ fun s hs =>
    (F420.mem_constWeight_iff _ _).mpr
      ((altDn_mem_ker_iff (s : Equiv.Perm (Fin m)) hm hx).mp (hT s hs))
  exact (F420.mem_constWeight_iff _ _).mp h

variable {V : Type} [CommGroup V] [Finite V]

theorem fix_or_lin2_of_b42
    (hV : ∀ v : V, v * v = 1)
    {L S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L)
    (hN : Nat.card L ≠ 360 ∧ Nat.card L ≠ 2520 ∧ Nat.card L ≠ 6048)
    (hZ : Subgroup.center ↥L = ⊥) (hB : B42ModulePair L (commV L) (fixV L ⊓ commV L)) :
    (∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v) ∨
      ∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n := by
  rcases hB with ⟨n, hn⟩ | ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ |
    ⟨m, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhat, -, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact Or.inr ⟨n, hn⟩
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS le_rfl hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_sp4 hV hS hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_g2 hV hS hπ)
  ·
    exfalso
    have := charP_two_of_card hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have h1 := card_eq_of_realizesVia (zornQ_faithful hle) hπ
    change Nat.card ↥L = Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ at h1
    rw [card_commutator_quasithinG2 (by simpa using hK)] at h1
    exact hN.2.2 h1
  ·
    left
    obtain ⟨T₀, hT₀, γ, hγ3, hD⟩ := exists_fixesFixed_altDn (m := 5) le_rfl (by norm_num)
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful le_rfl) hπ
    have hγ3' : γ ^ 3 = 1 := by rw [← hγ3, pow_orderOf_eq_one]
    refine exists_fix_of_realizesVia hV hS hπ hT₀ hγ3' ?_ hD
    intro h
    have h1 : γ = 1 := hinj (h.trans (map_one π).symm)
    rw [h1, orderOf_one] at hγ3
    omega
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hN.1 (by rw [h1]; decide)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hN.2.1 (by rw [h1]; decide)
  · exfalso
    have h1 := card_eq_of_realizesVia (G64.a7Four_faithful α) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [card_alt (by norm_num)] at h1
    exact hN.2.1 (by rw [h1]; decide)
  ·
    exfalso
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ, hπ.1⟩
    have h1 := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hhat.2.1, hZ, Subgroup.card_bot] at h1
    omega
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS (by norm_num) hπ)
  · have := charP_two_of_card hK
    exact Or.inl (fix_of_nat hV hS (by norm_num) hπ)
  · exact Or.inl (fix_of_extSq4 hV hS hπ)
  · exact Or.inl (fix_of_extSq5 hV hS hπ)

theorem fix_or_lin2_of_b51
    (hV : ∀ v : V, v * v = 1)
    {G L S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L)
    (hN : Nat.card L ≠ 360 ∧ Nat.card L ≠ 2520 ∧ Nat.card L ≠ 6048)
    (hZ : Subgroup.center ↥L = ⊥) (h : B51Part1 G L) :
    (∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v) ∨
      ∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, ⟨hU, hU0⟩, h₁, h₂⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, hind, hsup, hreal⟩
  · exact fix_or_lin2_of_b42 hV hS hN hZ hB
  ·
    left
    have := charP_two_of_card hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0)
    refine fix_of_sum hS le_rfl hinj fun v hv hT => ?_
    rw [← hsup] at hv
    refine fix_of_iSup I (fun i => disjoint_iff.mp (hind i)) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw
  ·
    left
    have hn4 : 4 ≤ n := by omega
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) h₁
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hU] at hv
    refine fix_of_sup hU0 (fun t ht w hw => ?_) (fun t ht w hw => ?_)
      (fix_nat_summand h₁ _ (by simp) (by simp))
      (fix_dualNat_summand h₂ _ (by simp; omega) (by simp; omega)) v hv hT
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₁.2.2.2.1 (π τ) w hw
    · obtain ⟨τ, -, rfl⟩ := ht
      exact h₂.2.2.2.1 (π τ) w hw
  ·
    left
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _)
      (hreal ⟨0, hk1⟩)
    refine fix_of_sum hS (by omega) hinj fun v hv hT => ?_
    rw [← hsup, bot_sup_eq] at hv
    refine fix_of_iSup I (fun i => by simpa using hind i) (fun t ht i w hw => ?_)
      (fun i => fix_nat_summand (hreal i) _ (by simp) (by simp)) v hv hT
    obtain ⟨τ, -, rfl⟩ := ht
    exact (hreal i).2.2.2.1 (π τ) w hw

theorem b51Part1_of_b56 (h56 : AsB56) (hV : ∀ v : V, v * v = 1) {Γ L : Subgroup (MulAut V)}
    (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hLΓ : L ≤ Γ) (hn : (L.subgroupOf Γ).Normal)
    (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥) (hq : CFSG.IsQuasisimple ↥L)
    (h6 : 6 < Nat.card L) (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    B51Part1 (ffJ Γ) L := by
  have hZ := center_eq_bot hLΓ hC
  obtain ⟨hLG, hB53⟩ := b53Hyp_ffJ hQ hq hZ hC hLΓ hn hoff
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hG1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLG))
  have hΓL := le_normalizer_of_normal hLΓ hn
  have hdich : ∀ H ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (H : Set (MulAut V)) →
      L ≤ H ∨ H = ⊥ := fun H hH hGH =>
    le_or_eq_bot hq hZ hC (hH.trans (ffJ_le Γ)) (hLG.trans hGH) ((hH.trans (ffJ_le Γ)).trans hΓL)
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  rcases h56 V hV2 (ffJ Γ) hG1 hB53 with ⟨hqF, ⟨h1, -⟩, -⟩ | h2 | h3 | h4 | h5
  ·
    have hFL : quasithinGenFitting (ffJ Γ) = L := by
      have hF := quasithinGenFitting_le (ffJ Γ)
      have hGF : ffJ Γ ≤ Subgroup.normalizer (quasithinGenFitting (ffJ Γ) : Set (MulAut V)) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_quasithinGenFitting _)
      rcases hdich _ hF hGF with hLF | hb
      · exact eq_of_isQuasisimple hq hqF hLF ((hF.trans (ffJ_le Γ)).trans hΓL)
      · exfalso
        have := nontrivial_of_isQuasisimple hqF
        rw [hb] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
    rw [hFL] at h1
    exact h1
  · exact (false_of_case2 hLG h6 h2).elim
  · exact (false_of_case3 hL1 hdich h3).elim
  · exact (false_of_case4 h6 hdich h4).elim
  · exact (false_of_case5 hL1 hdich h5).elim

theorem fix_or_lin2_of_b56
    (h56 : AsB56) (hV : ∀ v : V, v * v = 1)
    {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (hq : CFSG.IsQuasisimple ↥L) (h6 : 6 < Nat.card L)
    (hN : Nat.card L ≠ 360 ∧ Nat.card L ≠ 2520 ∧ Nat.card L ≠ 6048)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) {S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) :
    (∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v) ∨
      ∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n :=
  fix_or_lin2_of_b51 hV hS hN (center_eq_bot hLΓ hC)
    (b51Part1_of_b56 h56 hV hQ hLΓ hn hC hq h6 hoff)

omit [Finite V] in
theorem mem_of_fix_nat_two {L : Subgroup (MulAut V)} {U Z : Subgroup V} {K : Type} [Field K]
    [CharP K 2] {π : (FFModel.nat (StatedSL 2 K)).Gam →* ↥L}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z π) {ℓ : ↥L} (hℓ3 : ℓ ^ 3 = 1)
    (hℓ1 : ℓ ≠ 1) {u : V} (hu : u ∈ U) (hfix : (ℓ : MulAut V) u = u) : u ∈ Z := by
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  obtain ⟨γ, hγ⟩ := hπ.1 ℓ
  have hγ3 : γ ^ 3 = 1 := hinj (by rw [map_pow, hγ, hℓ3, map_one])
  have hγ1 : γ ≠ 1 := fun h => hℓ1 (by rw [← hγ, h, map_one])
  have hfix' : ((π γ : ↥L) : MulAut V) u = u :=
    (congrArg (fun l : ↥L => (l : MulAut V) u) hγ).trans hfix
  obtain ⟨-, -, -, hinvI, -, hsec, -, β, -, hβk, hβe⟩ := hπ
  set u' : ↥U := ⟨u, hu⟩ with hu'
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β u')
  have h1 := hβe γ u' m₀ (hinvI _ u hu) (hsec γ _ m₀.2) hm₀.symm
  have h2 : u' = ⟨((π γ : ↥L) : MulAut V) (u' : V), hinvI _ u hu⟩ := Subtype.ext hfix'.symm
  have h3 := QuotientGroup.eq.mp (hm₀.trans ((congrArg β h2).trans h1))
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 : (FFModel.nat (StatedSL 2 K)).act γ (m₀ : (FFModel.nat (StatedSL 2 K)).Amb) =
      (m₀ : (FFModel.nat (StatedSL 2 K)).Amb) :=
    (inv_mul_eq_one.mp (Subgroup.mem_bot.mp h3)).symm
  have h5 : (slMat γ).mulVec (Multiplicative.toAdd
      ((m₀ : (FFModel.nat (StatedSL 2 K)).Amb) : Multiplicative (Fin 2 → K))) =
      Multiplicative.toAdd ((m₀ : (FFModel.nat (StatedSL 2 K)).Amb) :
        Multiplicative (Fin 2 → K)) :=
    congrArg Multiplicative.toAdd h4
  set e := specialLinearGroupEquivStatedSL 2 K
  have hg3 : (e.symm γ) ^ 3 = 1 :=
    (map_pow e.symm γ 3).symm.trans ((congrArg e.symm hγ3).trans (map_one _))
  have hg1 : e.symm γ ≠ 1 := fun h => hγ1 (by rw [← e.apply_symm_apply γ, h, map_one]; rfl)
  have hmat : ((e.symm γ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      slMat γ :=
    (specialLinearGroupEquivStatedSL_coe 2 K (e.symm γ)).symm.trans
      (congrArg slMat (e.apply_symm_apply γ))
  have h5' : ((e.symm γ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd
        ((m₀ : (FFModel.nat (StatedSL 2 K)).Amb) : Multiplicative (Fin 2 → K))) =
      Multiplicative.toAdd ((m₀ : (FFModel.nat (StatedSL 2 K)).Amb) :
        Multiplicative (Fin 2 → K)) := by
    rw [hmat]
    exact h5
  have h6 := L15420.eq_zero_of_mulVec_eq_self CharTwo.two_eq_zero hg3 hg1 h5'
  have hm1 : m₀ = 1 := Subtype.ext (Multiplicative.toAdd.injective h6)
  have hβ : β u' = 1 := by rw [← hm₀, hm1]; rfl
  exact (hβk u').mp hβ

end FFL

end CFSG.Quasithin.EmptyFaithfulMultiple
